/*
 * Copyright 2020 ACINQ SAS
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package fr.acinq.bitcoin

import kotlinx.serialization.InternalSerializationApi
import kotlin.test.Test

@ExperimentalUnsignedTypes
@InternalSerializationApi
@ExperimentalStdlibApi
class PuzzleTestsCommon {
    @Test
    fun `handle puzzle a59012de71dafa1510fd57d339ff488d50da4808c9fd4c001d6de8874d8aa26d`() {
        val tx = Transaction.read("010000000298a4782ee3399a79f2b6a7c70f9f810986a42e819c14340fa35e813aac9681ae000000006e4830450220087ede38729e6d35e4f515505018e659222031273b7366920f393ee3ab17bc1e022100ca43164b757d1a6d1235f13200d4b5f76dd8fda4ec9fc28546b2df5b1211e8df03210275983913e60093b767e85597ca9397fb2f418e57f998d6afbbc536116085b1cb02ac91ffffffffa939fd811ba1c70a3ec3d955717418fe4a24dd5e597f7a47230674c853b7f360000000006d4830450220087ede38729e6d35e4f515505018e659222031273b7366920f393ee3ab17bc1e022100ca43164b757d1a6d1235f13200d4b5f76dd8fda4ec9fc28546b2df5b1211e8df03210275983913e60093b767e85597ca9397fb2f418e57f998d6afbbc536116085b1cb01acffffffff01a08601000000000017a9146c21ac707cb37c90794294acda011060ef0fc0118700000000")
        val inputs = listOf(
            Transaction.read("01000000015a7005f8a0792562bd20b9eff51c09f3e9e6522174c04098762eab1be1afc057000000006b4830450221009c290467721372d171f0d888bb193b70e6c07b116112ef23483ecbe030938636022075ce1f6be389288a4ed7c81725836a2700b539db85aeb757160c950a78fa29c6012103bc9d9e9b50db4fc3f1eb93b9a3e2cc22e179dab4df22179a34413f86078444a6ffffffff02a08601000000000017a914827fe37ec405346ad4e995323cea83559537b89e87f8e03500000000001976a914f21d36cb22c671a4b022bc953890bb9c45820a1c88ac00000000"),
            Transaction.read("0100000001ae9e6387e20d0fc30aa043ed735e33e805200d65e9d33ab503913f7436001e6b000000006b483045022100b5e73e71be331971d57ad6d804020a70a88c5617d72584d2ec76f327316da8b3022014c0d150d67847cc9c3731390691309f0465e46f4c20ee17aafc13794f8d5152012103de3d3c06403ba70b3efd5b139eb09aff8b8260bfe838a831a44666a794f5e84dffffffff02a08601000000000017a91417be79cf51aa88feebb0a25e9d6a153ead585e5987583c3900000000001976a914285fb1890240afe00b852d1b6eab49a767bc462288ac00000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle 61d47409a240a4b67ce75ec4dffa30e1863485f8fe64a6334410347692f9e60e`() {
        val tx = Transaction.read("01000000012edfb7a1a41b61e46eae1032c38d8792eacb79f7a6599dd24372f4a3e88a31700000000006030000800191ffffffff010000000000000000016a00000000")
        val inputs = listOf(
            Transaction.read("010000000192cad3c8e41d1e2f1baf6f8a991c3db6bf67a60c49e963beb44f8e41a78073dd010000008b48304502203b4cb2c60cd688129ec89da31464ce9ce07da56125425afdf9fd67559e708b3c0221008174b7a26787a8eb30460a699f584518351a741bc37775dc702d7f14e8f53e340141043a58cccd11db5dfc34e1433eef0b2b3bf6b947113d5e45562a095781663c919dda444017ab9a7c0e458478e7ef3edf5233eb476c1cb62ecfbb03bc4e22e40333ffffffff0250c300000000000017a914bb89dd62e80d1801df9aa570769b012f246c4f6d8730ee9a00000000001976a91463e8c29bfd51ee98778481c920bb6d288a220f9188ac00000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle eb3b82c0884e3efa6d8b0be55b4915eb20be124c9766245bcc7f34fdac32bccb`() {
        val tx = Transaction.read("01000000024de8b0c4c2582db95fa6b3567a989b664484c7ad6672c85a3da413773e63fdb8000000006b48304502205b282fbc9b064f3bc823a23edcc0048cbb174754e7aa742e3c9f483ebe02911c022100e4b0b3a117d36cab5a67404dddbf43db7bea3c1530e0fe128ebc15621bd69a3b0121035aa98d5f77cd9a2d88710e6fc66212aff820026f0dad8f32d1f7ce87457dde50ffffffff4de8b0c4c2582db95fa6b3567a989b664484c7ad6672c85a3da413773e63fdb8010000006f004730440220276d6dad3defa37b5f81add3992d510d2f44a317fd85e04f93a1e2daea64660202200f862a0da684249322ceb8ed842fb8c859c0cb94c81e1c5308b4868157a428ee01ab51210232abdc893e7f0631364d7fd01cb33d24da45329a00357b3a7886211ab414d55a51aeffffffff02e0fd1c00000000001976a914380cb3c594de4e7e9b8e18db182987bebb5a4f7088acc0c62d000000000017142a9bc5447d664c1d0141392a842d23dba45c4f13b17500000000")
        val inputs = listOf(
            Transaction.read("01000000017ea56cd68c74b4cd1a2f478f361b8a67c15a6629d73d95ef21d96ae213eb5b2d010000006a4730440220228e4deb3bc5b47fc526e2a7f5e9434a52616f8353b55dbc820ccb69d5fbded502206a2874f7f84b20015614694fe25c4d76f10e31571f03c240e3e4bbf1f9985be201210232abdc893e7f0631364d7fd01cb33d24da45329a00357b3a7886211ab414d55affffffff0230c11d00000000001976a914709dcb44da534c550dacf4296f75cba1ba3b317788acc0c62d000000000017142a9bc5447d664c1d0141392a842d23dba45c4f13b17500000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle 6d36bc17e947ce00bb6f12f8e7a56a1585c5a36188ffa2b05e10b4743273a74b`() {
        val tx = Transaction.read("010000000237b17d763851cd1ab04a424463d413c4ee5cf61304c7fd76977bea7fce075705000000006a473044022002dbe4b5a2fbb521e4dc5fbec75fd960651a2754b03d0871b8c965469be50fa702206d97421fb7ea9359b63e48c2108223284b9a71560bd8182469b9039228d7b3d701210295bf727111acdeab8778284f02b768d1e21acbcbae42090cc49aaa3cc6d19cdaffffffff37b17d763851cd1ab04a424463d413c4ee5cf61304c7fd76977bea7fce0757050100000070004830450220106a3e4ef0b51b764a28872262ffef55846514dacbdcbbdd652c849d395b4384022100e03ae554c3cbb40600d31dd46fc33f25e47bf8525b1fe07282e3b6ecb5f3bb2801ab51210232abdc893e7f0631364d7fd01cb33d24da45329a00357b3a7886211ab414d55a51aeffffffff01003e4900000000001976a9140d7713649f9a0678f4e880b40f86b93289d1bb2788ac00000000")
        val inputs = listOf(
            Transaction.read("0100000002cbbc32acfd347fcc5b2466974c12be20eb15495be50b8b6dfa3e4e88c0823beb000000006a47304402205e9e74f93f6aa1b095bbe124be0be95aeca52ebe91f214c86febe512b26c827c0220379ee83416df7c2adc753b5eefe61e7aef10ec208b549a249b6006e8009a0e210121031dd6da443782f1099b0ed98060b9ee1b81cd2392e938d23015749625c7dd0470ffffffffcbbc32acfd347fcc5b2466974c12be20eb15495be50b8b6dfa3e4e88c0823beb010000007000483045022013187aed1aeaaca0ca8a7c0e4f6362070208e68a5230c7a3cf65d922da19964802210082ac0719fd2be6c40b550791a96449e6bf1f70ed9492f88e825416c099d36b2601ab51210232abdc893e7f0631364d7fd01cb33d24da45329a00357b3a7886211ab414d55a51aeffffffff02903a1c00000000001976a914f7d46c08dd53bc6bbb52178d60b3fc99a9c1fb8788acc0c62d000000000017142a9bc5447d664c1d0141392a842d23dba45c4f13b17500000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle bc179baab547b7d7c1d5d8d6f8b0cc6318eaa4b0dd0a093ad6ac7f5a1cb6b3ba`() {
        val tx = Transaction.read("010000000290c5e425bfba62bd5b294af0414d8fa3ed580c5ca6f351ccc23e360b14ff7f470100000091004730440220739d9ab2c3e7089e7bd311f267a65dc0ea00f49619cb61ec016a5038016ed71202201b88257809b623d471e429787c36e0a9bcd2a058fc0c75fd9c25f905657e3b9e01ab512103c86390eb5230237f31de1f02e70ce61e77f6dbfefa7d0e4ed4f6b3f78f85d8ec2103193f28067b502b34cac9eae39f74dba4815e1278bab31516efb29bd8de2c1bea52aeffffffffdd7f3ce640a2fb04dbe24630aa06e4299fbb1d3fe585fe4f80be4a96b5ff0a0d01000000b400483045022100a28d2ace2f1cb4b2a58d26a5f1a2cc15cdd4cf1c65cee8e4521971c7dc60021c0220476a5ad62bfa7c18f9174d9e5e29bc0062df543e2c336ae2c77507e462bbf95701ab512103c86390eb5230237f31de1f02e70ce61e77f6dbfefa7d0e4ed4f6b3f78f85d8ec2103193f28067b502b34cac9eae39f74dba4815e1278bab31516efb29bd8de2c1bea21032462c60ebc21f4d38b3c4ccb33be77b57ae72762be12887252db18fd6225befb53aeffffffff02e0fd1c00000000001976a9148501106ab5492387998252403d70857acfa1586488ac50c3000000000000171499050637f553f03cc0f82bbfe98dc99f10526311b17500000000")
        val inputs = listOf(
            Transaction.read("0100000001eae7c33c5a3ad25316a4a1a0220343693077d7a35c6d242ed731d9f26c9f8b45010000006b48304502205b910ff27919bb4b81847e17e19848a8148373b5d84856e8a0798395c1a4df6e022100a9300a11b37b52997726dab17851914151bd647ca053d60a013b8e0ad42d1c6e012102b2e1e38d1b15170212a852f68045979d790814a139ed57bffba3763f75e18808ffffffff02b0453c00000000001976a914c39c8d989dfdd7fde0ee80be36113c5abcefcb9c88ac40420f0000000000171464d63d835705618da2111ca3194f22d067187cf2b17500000000"),
            Transaction.read("010000000190c5e425bfba62bd5b294af0414d8fa3ed580c5ca6f351ccc23e360b14ff7f47000000006b4830450220668828280473923647f2fb99450578a18f81e92358d94c933b7033b4370448b8022100cfbce6723163c907b3b86777f0698cc29ea5f89d0fce657a3894afcb1c717da50121033be10bdc7ff38235cf469449147636c4e0e49aacdd0a25af4109cbebd361e0d2ffffffff0220402c00000000001976a9142758fcf332b5df477ec6d877d3b72526b827202b88ac40420f0000000000171451c387bb5c66d1e9d4d054fd96d0844eecf3b664b17500000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle 0157f2eec7bf856d66714856182a146998910dc6fa576bec200a9fa8039459e7`() {
        val tx = Transaction.read("01000000071f2819c45d3c1c995c4190513a80b5c77cb7011bd5ea76c0959317fa70dff4d0010000006f00473044022067903de9b17bf94cceb00bc29909b9ffd051fe06bf9fe8746db8ad9ff35850f60220466dc2a589316895dc377fd0e9089b6fc0b4aa3425d5ebf341b9a3b42bcd915001ab51210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a5451aeffffffff24239a8d1905a7a8fc55fcf6ade3629a642e3ea9d5db8131d2aa39b3a16d04920100000071004930460221009b57994fb091a05615f5fcb91c9dc0dc4055db104f6ce8233714a06401dbe2bb022100d3ddc25d4aedd8743f6a763e6a3eb0cbcb5f28369aadf12dd09f01d35df297d001ab51210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a5451aeffffffffeb710f552a89aef18a67cd65f310816a833e48ffbd2a0fea568cc203eb501f1c010000007000483045022047ffa8737bf505a9c09c9872ba59e7247c201e584babfbc0b92a522d5fdf625402210087c51b1940c948c4210f1eb3a95bea78a1d28f3674681f16247ad20595b2b98401ab51210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a5451aefffffffffd209beaeca7ce7fef18abae226f599d004bb9367c1023cb898d790c8fd75094010000006f0047304402204a82ca145282d3e454824c3bd805b3a3bc07397a67c68ccafe1ce1c65dc5ee90022065c3284d38b1176304cb441ed4b13b43d2d0c2c465afb6d60fd46430cb92ee7001ab51210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a5451aeffffffff828166ba93d9cb2d0a7c526f031802d534d1f3bcba99cdf38319709740502d1701000000700048304502206edc0fb9e8bb6e1a87a67faa98c0a2fd6f0a9870378e6eb5de4eb41bdd435b2a022100ae153e3f5881b62e7e615144c1c2a1ba1245fdd642a42fe931a790b9d41035cc01ab51210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a5451aeffffffffbde46a81e9c5e1b3bc8cffaf7344d8fa4597226212d3af75abcc12c0295f606d000000006b483045022100f33e760d098042d0797c80186a86c75490493213bdab2211a147e802c9f5d1e90220316723b23d9f76919ef950a7b326f371f24ccec6757da6b4f3c1563a94110882012102b6e409986f883995148c0ef9753c7d2468c382396a398c68d81c8a039be7f5edffffffff212b733844fe67a47d316b46001fbb153efcb2d43920646da1f8e574d4cc5673010000007100493046022100c327dbabd61403d65ddac5da2419692c91e710eab10ca36f03f75d57a83a6f0f022100a025adc0347fe2279a3a45bf27a56bd168e3c9aa2eed238bec56c3443a989f7101ab51210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a5451aeffffffff0150c30000000000001976a914c3c99e4f74ef8103ee24d7eb980ac5216a9218cd88ac00000000")
        val inputs = listOf(
            Transaction.read("0100000001212b733844fe67a47d316b46001fbb153efcb2d43920646da1f8e574d4cc5673000000006b483045022100afeffe723016ef5658fbaf76cae68dae4071491d3e17001d187d68431531bac8022064ac86756ce7bfe8f7a7ba95b30e9f484c6b9acb59b6301c39e53446b68bd16e0121029f3366d06900fd515e4ca324f5ab8812aac719e7f63494b364961ae8ddf00ec4ffffffff0268b29400000000001976a914bd236e620d132a9392ec745f15f6f180068800ef88ace8030000000000001714e41346a0f116a7d04984c2780a396b18b0e47ea7b17500000000"),
            Transaction.read("0100000001eb710f552a89aef18a67cd65f310816a833e48ffbd2a0fea568cc203eb501f1c000000006b483045022100bbf8d9416e4e3c716611d20edc669e67b452ae018382aff006f19d5d2fadaffd02202a3e651ff4a42401140041e1443eb980475279316590368a612636fcde957baf01210384187dc0c26227923a54f875139dce3234973fe152cef865637040d45666f1e7ffffffff0210089700000000001976a914839d17fe240ebc6336a30490734833e39bbd054b88ace8030000000000001714e41346a0f116a7d04984c2780a396b18b0e47ea7b17500000000"),
            Transaction.read("0100000001c5b9f89aeebb94f6838d9e8b0c0876dd7b62249a14f7c3acd466a4a6682c2530010000006b483045022068d7ba61ae4670fe857ca4617413e2a8f666c7a30dbee9ad52a77406f62fd4bb0221009ed0034c8005b17b8e85e5b5d9cd35a79914665863c1ea85201ff0b42ec1f48b01210291b3da73ea3ce05d942315135d10532b58175568092116da909da0cb42006a54ffffffff0248cf9700000000001976a91452b5f62ff6a34dc0937baa262314649b22caebec88ace8030000000000001714e41346a0f116a7d04984c2780a396b18b0e47ea7b17500000000"),
            Transaction.read("01000000011f2819c45d3c1c995c4190513a80b5c77cb7011bd5ea76c0959317fa70dff4d0000000006b483045022100b565856a139eb7a597dfa627bdbbb0d08ef28fd107faedaebe5793049878761102200385513557125ae17131c201d68916753a4cdec55c55b60fd49de3fbc39e43500121020164c85c193480442fcae6b2bbd96808ef57f77808cca1ba37362be3b50a5f5bffffffff0230eb9300000000001976a914c8caa5cc2b05f0c826955a55d18936a825173e7888ace8030000000000001714e41346a0f116a7d04984c2780a396b18b0e47ea7b17500000000"),
            Transaction.read("010000000124239a8d1905a7a8fc55fcf6ade3629a642e3ea9d5db8131d2aa39b3a16d0492000000006a473044022100f53409c8bfcd9f7dfec5c3ce5a6ba5fd2b06eb7a293ec1c6e88350c0a11eb088021f762d32280e86009fe2d78188b4354fefcdc0569e2bea4f084fe1fc8b7b44ce01210223a531fe288ff114636866ddc13b95539be0113fe9f3da7440ffe654f8c7d8f4ffffffff02d8409600000000001976a914b7067b0c168f2dbbfc691b00b75d5953e824677b88ace8030000000000001714e41346a0f116a7d04984c2780a396b18b0e47ea7b17500000000"),
            Transaction.read("0100000001fd209beaeca7ce7fef18abae226f599d004bb9367c1023cb898d790c8fd75094000000006b48304502203829272181ea61672c4f10610eb9fb8496e1f9126e756076656da6f89a5f12a7022100ff03dae114c74733f926d88bb4e7b4e66b8c2e3fa1e0cd4ac499c8c6b31c6e050121037f3f33a6a65658c78df034bc76b80ebda489184dfe985e1c79aca0205775f6beffffffff02e0ab0000000000001976a91436bb470a763a7e9b24978a0fefffed5fd240434d88ac007c9200000000001976a914c3c99e4f74ef8103ee24d7eb980ac5216a9218cd88ac00000000"),
            Transaction.read("0100000001828166ba93d9cb2d0a7c526f031802d534d1f3bcba99cdf38319709740502d17000000006b4830450221008dd2137e3828da3640e09f75b3c90f657a35894bcbb9e651e2d2807859d093060220511d0aabd30c7bac562bc4003fef284bab5512ed379e10f48d824771ce2c033a01210326f02d77f36875b22553bab6dc6f85d3f780a7deaf9703dbc6a44b10a712461dffffffff02a0799500000000001976a9148594be676909c1d2d5de7052825cb9350a72187888ace8030000000000001714e41346a0f116a7d04984c2780a396b18b0e47ea7b17500000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle 4d932e00d5e20e31211136651f1665309a11908e438bb4c30799154d26812491`() {
        val tx = Transaction.read("0100000002bab3b61c5a7facd63a090addb0a4ea1863ccb0f8d6d8d5c1d7b747b5aa9b17bc01000000fdfe000048304502210089666e61b0486a71f2103414315aa4c418dc65815f8b8bfcfab1037c3c2a66210220428b8162874cfc97e05dee6f901dae03820d11011fa7828ecb8fbca45be2188d01493046022100c6c19d75b6d5c911813b2b64cee07c6338f54bca0395264e53c3b3d8ca8e4f8e022100bbcb8d32960e62f26e3e5bdeca605a8b49f1a42cedd20bad507a1bc23c565faf01ab522103c86390eb5230237f31de1f02e70ce61e77f6dbfefa7d0e4ed4f6b3f78f85d8ec2103193f28067b502b34cac9eae39f74dba4815e1278bab31516efb29bd8de2c1bea21032462c60ebc21f4d38b3c4ccb33be77b57ae72762be12887252db18fd6225befb53aeffffffffb1678d9af66c4b8cde45d0d445749322746ab900e546d3900cf30f436e73428a01000000fd470100483045022100a7af036203a1e6b2e833b0d6b402958d58f9ffaaff4969539f213634f17600ee0220192594a5c60f70e5a97dc48fec06df0d3b17c44850162d3d552c7d8653d159a001483045022072020e687ce937828827e85bc916716a9099a510e7fbd96a2836617afa370108022100ce737ad7b46c249cda2b09cb065ea16078b9a3a31f6fc6b63385f645abfdafdf01493046022100c30c5f6e943a78d502216e019821545b940b940784e83051945d89c92ec245f0022100b5c76266878ee8f29f65401fb0af6ba3941641740d846cb551059c0ad25b798c01ab532103c86390eb5230237f31de1f02e70ce61e77f6dbfefa7d0e4ed4f6b3f78f85d8ec2103193f28067b502b34cac9eae39f74dba4815e1278bab31516efb29bd8de2c1bea21032462c60ebc21f4d38b3c4ccb33be77b57ae72762be12887252db18fd6225befb53aeffffffff0150c300000000000017142c68bb496b123d39920fcfdc206daa08bbe58506b17500000000")
        val inputs = listOf(
            Transaction.read("010000000290c5e425bfba62bd5b294af0414d8fa3ed580c5ca6f351ccc23e360b14ff7f470100000091004730440220739d9ab2c3e7089e7bd311f267a65dc0ea00f49619cb61ec016a5038016ed71202201b88257809b623d471e429787c36e0a9bcd2a058fc0c75fd9c25f905657e3b9e01ab512103c86390eb5230237f31de1f02e70ce61e77f6dbfefa7d0e4ed4f6b3f78f85d8ec2103193f28067b502b34cac9eae39f74dba4815e1278bab31516efb29bd8de2c1bea52aeffffffffdd7f3ce640a2fb04dbe24630aa06e4299fbb1d3fe585fe4f80be4a96b5ff0a0d01000000b400483045022100a28d2ace2f1cb4b2a58d26a5f1a2cc15cdd4cf1c65cee8e4521971c7dc60021c0220476a5ad62bfa7c18f9174d9e5e29bc0062df543e2c336ae2c77507e462bbf95701ab512103c86390eb5230237f31de1f02e70ce61e77f6dbfefa7d0e4ed4f6b3f78f85d8ec2103193f28067b502b34cac9eae39f74dba4815e1278bab31516efb29bd8de2c1bea21032462c60ebc21f4d38b3c4ccb33be77b57ae72762be12887252db18fd6225befb53aeffffffff02e0fd1c00000000001976a9148501106ab5492387998252403d70857acfa1586488ac50c3000000000000171499050637f553f03cc0f82bbfe98dc99f10526311b17500000000"),
            Transaction.read("0100000001bab3b61c5a7facd63a090addb0a4ea1863ccb0f8d6d8d5c1d7b747b5aa9b17bc000000006b483045022056eaab9d21789a762c7aefdf84d90daf35f7d98bc917c83a1ae6fa24d44f2b94022100a8e1d45d4bc51ad3a192b1b9d582a4711971b0e957012a303950b83eda3d306c01210375228faaa97a02433f4f126ba8d5a295b92466608acf8d13740130d5bbf9cdb4ffffffff0240771b00000000001976a914bb05d829af3b31730e69b7eeb83c1c0d21d362eb88ac50c3000000000000171452cf84e83d1dc919ef4ada30c44cf4349ee55af9b17500000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle f7fdd091fa6d8f5e7a8c2458f5c38faffff2d3f1406b6e4fe2c99dcc0d2d1cbb`() {
        val tx = Transaction.read("01000000023d6cf972d4dff9c519eff407ea800361dd0a121de1da8b6f4138a2f25de864b4000000008a4730440220ffda47bfc776bcd269da4832626ac332adfca6dd835e8ecd83cd1ebe7d709b0e022049cffa1cdc102a0b56e0e04913606c70af702a1149dc3b305ab9439288fee090014104266abb36d66eb4218a6dd31f09bb92cf3cfa803c7ea72c1fc80a50f919273e613f895b855fb7465ccbc8919ad1bd4a306c783f22cd3227327694c4fa4c1c439affffffff21ebc9ba20594737864352e95b727f1a565756f9d365083eb1a8596ec98c97b7010000008a4730440220503ff10e9f1e0de731407a4a245531c9ff17676eda461f8ceeb8c06049fa2c810220c008ac34694510298fa60b3f000df01caa244f165b727d4896eb84f81e46bcc4014104266abb36d66eb4218a6dd31f09bb92cf3cfa803c7ea72c1fc80a50f919273e613f895b855fb7465ccbc8919ad1bd4a306c783f22cd3227327694c4fa4c1c439affffffff01f0da5200000000001976a914857ccd42dded6df32949d4646dfa10a92458cfaa88ac00000000")
        val inputs = listOf(
            Transaction.read("01000000013133cd7b91c1c5bc7778e66d22522237c6466179d6e14531728c14e01bdb278c000000008a47304402202c5994ecaa115838a020c2365b1eab31cf0090763ec7d05863b6170b73e999b602202cd391c828f3581dc89436b882b0f231e81e0694bba5e9ced8fc552d96fcf19f014104422ac7b5032ef300eb7ef6ee86c189027ba6988053aa532aaa57ed09f229233b0f8cf39bc752df6ff65f455bc2d0a83d99717472ccd74de4e46ad2d25f1ccf30ffffffff01404b4c00000000001976a914bef80ecf3a44500fda1bc92176e442891662aed288ac00000000"),
            Transaction.read("0100000001e1b5ae18ae1ff567523858011be62508110adc3ac687fad221570f96abece329070000008a473044022032c4bfd84ab7428370205ca48a481ab21908ed0aa0ac400bcd2f5bfb094e4d9d0220a9f62e9fe8fe9165c53d667f5c54704d36c3815faa5653d0caa3280ec505f901014104266abb36d66eb4218a6dd31f09bb92cf3cfa803c7ea72c1fc80a50f919273e613f895b855fb7465ccbc8919ad1bd4a306c783f22cd3227327694c4fa4c1c439affffffff02204e0000000000001976a914857ccd42dded6df32949d4646dfa10a92458cfaa88acb08f0600000000001976a914bef80ecf3a44500fda1bc92176e442891662aed288ac00000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }

    @Test
    fun `handle puzzle 23b397edccd3740a74adb603c9756370fafcde9bcc4483eb271ecad09a94dd63`() {
        val tx = Transaction.read("0100000001b14bdcbc3e01bdaad36cc08e81e69c82e1060bc14e518db2b49aa43ad90ba26000000000490047304402203f16c6f40162ab686621ef3000b04e75418a0c0cb2d8aebeac894ae360ac1e780220ddc15ecdfc3507ac48e1681a33eb60996631bf6bf5bc0a0682c4db743ce7ca2b01ffffffff0140420f00000000001976a914660d4ef3a743e3e696ad990364e555c271ad504b88ac00000000")
        val inputs = listOf(
            Transaction.read("01000000013133cd7b91c1c5bc7778e66d22522237c6466179d6e14531728c14e01bdb278c000000008a47304402202c5994ecaa115838a020c2365b1eab31cf0090763ec7d05863b6170b73e999b602202cd391c828f3581dc89436b882b0f231e81e0694bba5e9ced8fc552d96fcf19f014104422ac7b5032ef300eb7ef6ee86c189027ba6988053aa532aaa57ed09f229233b0f8cf39bc752df6ff65f455bc2d0a83d99717472ccd74de4e46ad2d25f1ccf30ffffffff01404b4c00000000001976a914bef80ecf3a44500fda1bc92176e442891662aed288ac00000000"),
            Transaction.read("010000000337bd40a022eea1edd40a678cddabe200b131afd5797b232ac21861d8e97eb367020000008a4730440220e8343f8ac7e96582d92a450ce314668db4f7a0e2c94a97aa6df026f93ebee2290220866b5728d4247688d91b4a30144762bc8bfd7f385de7f7d326d665ff5e3e900301410461cbdcc5409fb4b4d42b51d33381354d80e550078cb532a34bfa2fcfdeb7d76519aecc62770f5b0e4ef8551946d8a540911abe3e7854a26f39f58b25c15342afffffffff96420befb14a9357181e5da089824a3e6ea5a95856ff74c06c7d5ea98d633cf9020000008a4730440220b7227a8f816f3810f97057102edf8be4434c1e00f48b4440976bcc478f1431030220af3cba150afdd44618de4369cdc65fea73e447d7b5fbe135d2f08f86d82aa85f01410461cbdcc5409fb4b4d42b51d33381354d80e550078cb532a34bfa2fcfdeb7d76519aecc62770f5b0e4ef8551946d8a540911abe3e7854a26f39f58b25c15342afffffffff96420befb14a9357181e5da089824a3e6ea5a95856ff74c06c7d5ea98d633cf9010000008a47304402207d689e1a61e06440eab18d961517a97c49219a91f2c59d9630e902fcb2f4ea8b0220dcd274349ca264d8bd2bee5135664a92899e94a319a349d6d6e3660d04b564ad0141047a4c5d104002ebc203bef5cab6f13ff57ab624bb5f9f1186beb64c83a396da0d912e11a18ea15a2c784a62fed2bbd8258c3413c18bf4c3f2ba28f3d5565e328bffffffff0340420f000000000087514104cc71eb30d653c0c3163990c47b976f3fb3f37cccdcbedb169a1dfef58bbfbfaff7d8a473e7e2e6d317b87bafe8bde97e3cf8f065dec022b51d11fcdd0d348ac4410461cbdcc5409fb4b4d42b51d33381354d80e550078cb532a34bfa2fcfdeb7d76519aecc62770f5b0e4ef8551946d8a540911abe3e7854a26f39f58b25c15342af52ae50cec402000000001976a914c812a297b8e0e778d7a22bb2cd6d23c3e789472b88ac20a10700000000001976a914641ad5051edd97029a003fe9efb29359fcee409d88ac00000000")
        )
        Transaction.correctlySpends(tx, inputs, ScriptFlags.MANDATORY_SCRIPT_VERIFY_FLAGS)
    }
}