proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <=u 9223372036854775808@64, a1_0 <=u 9223372036854775808@64, a2_0 <=u 9223372036854775808@64, a3_0 <=u 9223372036854775808@64, a4_0 <=u 9223372036854775808@64] }
split x27_1 tmp_to_use_1 a4_0 48;
and t428_1@uint64 a4_0 281474976710655@uint64;
assume t428_1 = tmp_to_use_1 && true;
mul v29_1 x27_1 4294968273@uint64;
add t030_1 a0_0 v29_1;
split v31_1 tmp_to_use_2 t030_1 52;
add t132_1 a1_0 v31_1;
and t033_1@uint64 t030_1 4503599627370495@uint64;
assume t033_1 = tmp_to_use_2 && true;
split v34_1 tmp_to_use_3 t132_1 52;
add t235_1 a2_0 v34_1;
and t136_1@uint64 t132_1 4503599627370495@uint64;
assume t136_1 = tmp_to_use_3 && true;
split v37_1 tmp_to_use_4 t235_1 52;
add t338_1 a3_0 v37_1;
and t239_1@uint64 t235_1 4503599627370495@uint64;
assume t239_1 = tmp_to_use_4 && true;
split v40_1 tmp_to_use_5 t338_1 52;
sub v46_1 1125899906842620@uint64 t428_1;
and t342_1@uint64 t338_1 4503599627370495@uint64;
assume t342_1 = tmp_to_use_5 && true;
sub v8_1 18014381329608892@uint64 t033_1;
sub v10_1 18014398509481980@uint64 t136_1;
sub v12_1 18014398509481980@uint64 t239_1;
sub v14_1 18014398509481980@uint64 t342_1;
sub v16_1 v46_1 v40_1;
{ v8_1 + (v10_1 * 4503599627370496) + (v12_1 * 20282409603651670423947251286016) + (v14_1 * 91343852333181432387730302044767688728495783936) + (v16_1 * 411376139330301510538742295639337626245683966408394965837152256) = 0 - (a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256)) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && and [t428_1 = tmp_to_use_1, t033_1 = tmp_to_use_2, t136_1 = tmp_to_use_3, t239_1 = tmp_to_use_4, t342_1 = tmp_to_use_5] }