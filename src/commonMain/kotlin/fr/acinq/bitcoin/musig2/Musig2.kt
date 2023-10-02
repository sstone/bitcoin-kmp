package fr.acinq.bitcoin.musig2

import fr.acinq.bitcoin.*
import fr.acinq.secp256k1.Hex

public data class KeyAggCtx(val Q: PublicKey, val gacc: PrivateKey, val tacc: PrivateKey) {
    public fun tweak(tweak: PrivateKey, isXonly: Boolean): KeyAggCtx {
        return if (isXonly && !Q.isEven()) {
            KeyAggCtx(-Q + tweak.publicKey(), -gacc, tweak - tacc)
        } else {
            KeyAggCtx(Q + tweak.publicKey(), gacc, tweak + tacc)
        }
    }
}

public data class PrivateNonce(val p1: PrivateKey, val p2: PrivateKey, val pk: PublicKey) {
    public fun publicNonce(): PublicNonce = PublicNonce(p1.publicKey(), p2.publicKey())

    public companion object {
        public fun fromValidHex(hex: String): PrivateNonce {
            return fromBin(Hex.decode(hex))
        }

        public fun fromBin(bin: ByteArray): PrivateNonce {
            require(bin.size == 32 + 32 + 33)
            return PrivateNonce(
                PrivateKey(bin.copyOfRange(0, 32)),
                PrivateKey(bin.copyOfRange(32, 64)),
                PublicKey(bin.copyOfRange(64, 97))
            )
        }
    }
}

public data class PublicNonce(val P1: PublicKey, val P2: PublicKey) {
    public companion object {
        public fun fromValidHex(hex: String): PublicNonce {
            return fromBin(Hex.decode(hex))
        }

        public fun fromBin(bin: ByteArray): PublicNonce {
            require(bin.size == 33 + 33)
            return PublicNonce(PublicKey(bin.copyOfRange(0, 33)), PublicKey(bin.copyOfRange(33, 66)))
        }
    }
}

public data class SessionCtx(val aggnonce: PublicNonce, val pubkeys: List<PublicKey>, val tweaks: List<Pair<PrivateKey, Boolean>>, val message: ByteVector) {
    public fun build(): SessionValues {
        val keyAggCtx0 = keyAgg(pubkeys)
        val keyAggCtx = tweaks.fold(keyAggCtx0) { ctx, tweak -> ctx.tweak(tweak.first, tweak.second) }
        val (Q, gacc, tacc) = keyAggCtx
        val b = PrivateKey(Crypto.taggedHash((aggnonce.P1.value + aggnonce.P2.value + Q.xOnly().value + message).toByteArray(), "MuSig/noncecoef"))
        val R = runCatching { aggnonce.P1 + aggnonce.P2 * b }.getOrDefault(PublicKey.Generator)
        val e = PrivateKey(Crypto.taggedHash((R.xOnly().value + Q.xOnly().value + message).toByteArray(), "BIP0340/challenge"))
        return SessionValues(Q, gacc, tacc, b, R, e)
    }

    public fun getSessionKeyAggCoef(P: PublicKey): PrivateKey {
        require(pubkeys.contains(P)) { "signer's pubkey is not present" }
        return PrivateKey(keyAggCoeff(pubkeys, P))
    }

    public fun sign(secnonce: PrivateNonce, sk: PrivateKey): ByteVector32 {
        val (Q, gacc, _, b, R, e) = build()
        val (k1, k2) = if (R.isEven()) Pair(secnonce.p1, secnonce.p2) else Pair(-secnonce.p1, -secnonce.p2)
        val P = sk.publicKey()
        require(P == secnonce.pk)
        val a = getSessionKeyAggCoef(P)
        val d = if (Q.isEven()) gacc * sk else -gacc * sk
        val s = k1 + b * k2 + e * a * d
        require(partialSigVerify(s.value, secnonce.publicNonce(), sk.publicKey())) { "partial signature verification failed" }
        return s.value
    }

    public fun partialSigVerify(psig: ByteVector32, pubnonce: PublicNonce, pk: PublicKey): Boolean {
        val (Q, gacc, _, b, R, e) = build()
        val Rstar = pubnonce.P1 + pubnonce.P2 * b
        val Re = if (R.isEven()) Rstar else -Rstar
        val a = getSessionKeyAggCoef(pk)
        val gprime = if (Q.isEven()) gacc else -gacc
        return PrivateKey(psig).publicKey() == Re + pk * (e * a * gprime)
    }

    public fun partialSigAgg(psigs: List<ByteVector32>): PartialSigAggResult {
        val (Q, _, tacc, _, R, e) = build()
        for (i in psigs.indices) {
            if (!PrivateKey(psigs[i]).isValid()) return PartialSigAggResult.Failure.InvalidPartialSignature(i)
        }
        val s = psigs.map { PrivateKey(it) }.reduce { a, b -> a + b }
        val s1 = if (Q.isEven()) s + e * tacc else s - e * tacc
        val sig = ByteVector64(R.xOnly().value + s1.value)
        return PartialSigAggResult.Success(sig)
    }
}

public sealed class PartialSigAggResult {
    public abstract val result: ByteVector64?
    public fun isSuccess(): Boolean = result != null
    public fun isFailure(): Boolean = !isSuccess()

    public data class Success(val psig: ByteVector64) : PartialSigAggResult() {
        override val result: ByteVector64 = psig
    }

    public sealed class Failure : PartialSigAggResult() {
        override val result: ByteVector64? = null


        public data class InvalidPartialSignature(val index: Int) : Failure() {
            override fun toString(): String = "partial signature at index $index is not valid"
        }

        public data class GenericError(val t: Throwable) : Failure() {
            override fun toString(): String = "generic failure: ${t.message}"
        }
    }
}

public data class SessionValues(val Q: PublicKey, val gacc: PrivateKey, val tacc: PrivateKey, val b: PrivateKey, val R: PublicKey, val e: PrivateKey)

public fun keySort(pubkeys: List<PublicKey>): List<PublicKey> = pubkeys.sortedWith { a, b -> LexicographicalOrdering.compare(a, b) }

internal fun getSecondKey(pubkeys: List<PublicKey>): PublicKey {
    return pubkeys.drop(1).find { it != pubkeys[0] } ?: PublicKey(ByteArray(33))
}

internal fun hashKeys(pubkeys: List<PublicKey>): ByteVector32 {
    val concat = pubkeys.map { it.value }.reduce { a, b -> a + b }
    return Crypto.taggedHash(concat.toByteArray(), "KeyAgg list")
}

internal fun keyAggCoeffInternal(pubkeys: List<PublicKey>, pk: PublicKey, pk2: PublicKey): ByteVector32 {
    return if (pk == pk2) {
        ByteVector32.One.reversed()
    } else {
        Crypto.taggedHash(hashKeys(pubkeys).toByteArray() + pk.value.toByteArray(), "KeyAgg coefficient")
    }
}

internal fun keyAggCoeff(pubkeys: List<PublicKey>, pk: PublicKey): ByteVector32 {
    return keyAggCoeffInternal(pubkeys, pk, getSecondKey(pubkeys))
}

internal fun keyAgg(pubkeys: List<PublicKey>): KeyAggCtx {
    val pk2 = getSecondKey(pubkeys)
    val a = pubkeys.map { keyAggCoeffInternal(pubkeys, it, pk2) }
    val Q = pubkeys.zip(a).map { it.first.times(PrivateKey(it.second)) }.reduce { p1, p2 -> p1 + p2 }
    return KeyAggCtx(Q, PrivateKey(ByteVector32.One.reversed()), PrivateKey(ByteVector32.Zeroes))
}

internal fun nonceAgg(nonces: List<PublicNonce>): PublicNonce {
    val R1 = runCatching { nonces.map { it.P1 }.reduce { a, b -> a + b } }.getOrDefault(PublicKey(ByteArray(33)))
    val R2 = runCatching { nonces.map { it.P2 }.reduce { a, b -> a + b } }.getOrDefault(PublicKey(ByteArray(33)))
    return PublicNonce(R1, R2)
}
