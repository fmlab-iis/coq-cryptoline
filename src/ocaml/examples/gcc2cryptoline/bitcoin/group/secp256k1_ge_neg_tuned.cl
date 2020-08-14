(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=32G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=32G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_ge_neg_tuned.cl

Results of checking CNF formulas:       [OK]            0.954023 seconds
Finding polynomial coefficients         [OK]            0.082517 seconds
Verification result:                    [OK]            1.242628 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <=u 9223372036854775808@64, a1_0 <=u 9223372036854775808@64, a2_0 <=u 9223372036854775808@64, a3_0 <=u 9223372036854775808@64, a4_0 <=u 9223372036854775808@64] }
mov r3_40_1 a0_0;
mov r3_48_1 a1_0;
mov r3_56_1 a2_0;
mov r3_64_1 a3_0;
mov r3_72_1 a4_0;
mov t022_1 r3_40_1;
mov t123_1 r3_48_1;
mov t224_1 r3_56_1;
mov t325_1 r3_64_1;
mov t426_1 r3_72_1;
split x27_1 tmp_to_use_1 t426_1 48;
and t428_1@uint64 t426_1 281474976710655@uint64;
assume t428_1 = tmp_to_use_1 && true;
mul v29_1 x27_1 4294968273@uint64;
add t030_1 t022_1 v29_1;
split v31_1 tmp_to_use_2 t030_1 52;
add t132_1 t123_1 v31_1;
and t033_1@uint64 t030_1 4503599627370495@uint64;
assume t033_1 = tmp_to_use_2 && true;
split v34_1 tmp_to_use_3 t132_1 52;
add t235_1 t224_1 v34_1;
and t136_1@uint64 t132_1 4503599627370495@uint64;
assume t136_1 = tmp_to_use_3 && true;
split v37_1 tmp_to_use_4 t235_1 52;
add t338_1 t325_1 v37_1;
and t239_1@uint64 t235_1 4503599627370495@uint64;
assume t239_1 = tmp_to_use_4 && true;
split v40_1 tmp_to_use_5 t338_1 52;
sub v46_1 1125899906842620@uint64 t428_1;
and t342_1@uint64 t338_1 4503599627370495@uint64;
assume t342_1 = tmp_to_use_5 && true;
sub v8_1 18014381329608892@uint64 t033_1;
mov r3_40_2 v8_1;
sub v10_1 18014398509481980@uint64 t136_1;
mov r3_48_2 v10_1;
sub v12_1 18014398509481980@uint64 t239_1;
mov r3_56_2 v12_1;
sub v14_1 18014398509481980@uint64 t342_1;
mov r3_64_2 v14_1;
sub v16_1 v46_1 v40_1;
mov r3_72_2 v16_1;
mov c0_1 r3_40_2;
mov c1_1 r3_48_2;
mov c2_1 r3_56_2;
mov c3_1 r3_64_2;
mov c4_1 r3_72_2;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = 0 - (a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256)) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && and [t428_1 = tmp_to_use_1, t033_1 = tmp_to_use_2, t136_1 = tmp_to_use_3, t239_1 = tmp_to_use_4, t342_1 = tmp_to_use_5] }
