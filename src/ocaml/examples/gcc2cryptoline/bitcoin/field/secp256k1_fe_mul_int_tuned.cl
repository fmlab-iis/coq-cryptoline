(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_mul_int_tuned.cl

Results of checking CNF formulas:       [OK]            1.741403 seconds
Finding polynomial coefficients         [OK]            0.067307 seconds
Verification result:                    [OK]            2.572041 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, int32 a14_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <u 9007199254740992@64, a1_0 <u 9007199254740992@64, a2_0 <u 9007199254740992@64, a3_0 <u 9007199254740992@64, a4_0 <u 562949953421312@64, a14_0 <u 9@32] }
mov r13_0_1 a0_0;
mov r13_8_1 a1_0;
mov r13_16_1 a2_0;
mov r13_24_1 a3_0;
mov r13_32_1 a4_0;
mov v1_1 r13_0_1;
vpc v2_1@uint64 a14_0;
mul v3_1 v1_1 v2_1;
mov r13_0_2 v3_1;
mov v4_1 r13_8_1;
mul v5_1 v2_1 v4_1;
mov r13_8_2 v5_1;
mov v6_1 r13_16_1;
mul v7_1 v2_1 v6_1;
mov r13_16_2 v7_1;
mov v8_1 r13_24_1;
mul v9_1 v2_1 v8_1;
mov r13_24_2 v9_1;
mov v10_1 r13_32_1;
mul v11_1 v2_1 v10_1;
mov r13_32_2 v11_1;
mov c0_1 r13_0_2;
mov c1_1 r13_8_2;
mov c2_1 r13_16_2;
mov c3_1 r13_24_2;
mov c4_1 r13_32_2;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = (a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256)) * a14_0 (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && true }
