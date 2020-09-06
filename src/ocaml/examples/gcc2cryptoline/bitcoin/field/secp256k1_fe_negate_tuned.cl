(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_negate_tuned.cl

Results of checking CNF formulas:       [OK]            0.775225 seconds
Finding polynomial coefficients         [OK]            0.042868 seconds
Verification result:                    [OK]            1.041497 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, int32 a14_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <u 9007199254740992@64, a1_0 <u 9007199254740992@64, a2_0 <u 9007199254740992@64, a3_0 <u 9007199254740992@64, a4_0 <u 562949953421312@64] }
mov a18_0_1 a0_0;
mov a18_8_1 a1_0;
mov a18_16_1 a2_0;
mov a18_24_1 a3_0;
mov a18_32_1 a4_0;
mov m16_1 1@int32;
add v1_1 m16_1 1@int32;
vpc v2_1@uint64 v1_1;
mul v3_1 v2_1 9007190664804446@uint64;
mov v4_1 a18_0_1;
sub v5_1 v3_1 v4_1;
mov r19_0_1 v5_1;
mul v6_1 v2_1 9007199254740990@uint64;
mov v7_1 a18_8_1;
sub v8_1 v6_1 v7_1;
mov r19_8_1 v8_1;
mov v9_1 a18_16_1;
sub v10_1 v6_1 v9_1;
mov r19_16_1 v10_1;
mov v11_1 a18_24_1;
sub v12_1 v6_1 v11_1;
mov r19_24_1 v12_1;
mul v13_1 v2_1 562949953421310@uint64;
mov v14_1 a18_32_1;
sub v15_1 v13_1 v14_1;
mov r19_32_1 v15_1;
mov c0_1 r19_0_1;
mov c1_1 r19_8_1;
mov c2_1 r19_16_1;
mov c3_1 r19_24_1;
mov c4_1 r19_32_1;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = 0 - (a0_0 + (a1_0 * 4503599627370496) + (a2_0 * 20282409603651670423947251286016) + (a3_0 * 91343852333181432387730302044767688728495783936) + (a4_0 * 411376139330301510538742295639337626245683966408394965837152256)) (mod 115792089237316195423570985008687907853269984665640564039457584007908834671663) && true }