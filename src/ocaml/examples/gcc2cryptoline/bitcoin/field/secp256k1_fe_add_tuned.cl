(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_add_tuned.cl

Results of checking CNF formulas:       [OK]            0.171485 seconds
Finding polynomial coefficients         [OK]            0.026007 seconds
Verification result:                    [OK]            0.213735 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, uint64 b0_0, uint64 b1_0, uint64 b2_0, uint64 b3_0, uint64 b4_0) =
{ true && and [a0_0 <u 9223372036854775808@64, a1_0 <u 9223372036854775808@64, a2_0 <u 9223372036854775808@64, a3_0 <u 9223372036854775808@64, a4_0 <u 562949953421312@64, b0_0 <u 9223372036854775808@64, b1_0 <u 9223372036854775808@64, b2_0 <u 9223372036854775808@64, b3_0 <u 9223372036854775808@64, b4_0 <u 562949953421312@64] }
mov a18_0_1 a0_0;
mov a18_8_1 a1_0;
mov a18_16_1 a2_0;
mov a18_24_1 a3_0;
mov a18_32_1 a4_0;
mov r17_0_1 b0_0;
mov r17_8_1 b1_0;
mov r17_16_1 b2_0;
mov r17_24_1 b3_0;
mov r17_32_1 b4_0;
mov vect__142024_0_1 r17_0_1;
mov vect__142024_1_1 r17_8_1;
mov vect__142127_0_1 r17_16_1;
mov vect__142127_1_1 r17_24_1;
mov vect__242430_0_1 a18_0_1;
mov vect__242430_1_1 a18_8_1;
mov vect__242532_0_1 a18_16_1;
mov vect__242532_1_1 a18_24_1;
add vect__342634_0_1 vect__142024_0_1 vect__242430_0_1;
add vect__342634_1_1 vect__142024_1_1 vect__242430_1_1;
add vect__342635_0_1 vect__142127_0_1 vect__242532_0_1;
add vect__342635_1_1 vect__142127_1_1 vect__242532_1_1;
mov r17_0_2 vect__342634_0_1;
mov r17_8_2 vect__342634_1_1;
mov r17_16_2 vect__342635_0_1;
mov r17_24_2 vect__342635_1_1;
mov v13_1 r17_32_1;
mov v14_1 a18_32_1;
add v15_1 v13_1 v14_1;
mov r17_32_2 v15_1;
mov c0_1 r17_0_2;
mov c1_1 r17_8_2;
mov c2_1 r17_16_2;
mov c3_1 r17_24_2;
mov c4_1 r17_32_2;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256) + b0_0 + (b1_0 * 4503599627370496) + (b2_0 * 20282409603651670423947251286016) + (b3_0 * 91343852333181432387730302044767688728495783936) + (b4_0 * 411376139330301510538742295639337626245683966408394965837152256) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && true }