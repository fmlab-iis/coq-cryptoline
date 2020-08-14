(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_from_storage_tuned.cl

Results of checking CNF formulas:       [OK]            0.258574 seconds
Finding polynomial coefficients         [OK]            0.030908 seconds
Verification result:                    [OK]            0.412062 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0) =
{ true && true }
mov a20_0_1 a0_0;
mov a20_8_1 a1_0;
mov a20_16_1 a2_0;
mov a20_24_1 a3_0;
mov v1_1 a20_0_1;
and v2_1@uint64 v1_1 4503599627370495@uint64;
mov r21_0_1 v2_1;
split v3_1 tmp_to_use_1 v1_1 52;
assume tmp_to_use_1 = v2_1 && true;
mov v4_1 a20_8_1;
split tmp1_1 tmp2_1 v4_1 52;
shl v5_1 tmp2_1 12;
and v6_1@uint64 v5_1 4503599627370495@uint64;
or v7_1@uint64 v3_1 v6_1;
assume v7_1 = v3_1 + v6_1 && true;
mov r21_8_1 v7_1;
split v8_1 tmp_to_use_2 v4_1 40;
assume v6_1 = tmp_to_use_2 * 4096 && true;
mov v9_1 a20_16_1;
split tmp1_2 tmp2_2 v9_1 40;
shl v10_1 tmp2_2 24;
and v11_1@uint64 v10_1 4503599627370495@uint64;
or v12_1@uint64 v8_1 v11_1;
assume v12_1 = v8_1 + v11_1 && true;
mov r21_16_1 v12_1;
split v13_1 tmp_to_use_3 v9_1 28;
assume v11_1 = tmp_to_use_3 * 16777216 && true;
mov v14_1 a20_24_1;
split tmp1_3 tmp2_3 v14_1 28;
shl v15_1 tmp2_3 36;
and v16_1@uint64 v15_1 4503599627370495@uint64;
or v17_1@uint64 v13_1 v16_1;
assume v17_1 = v13_1 + v16_1 && true;
mov r21_24_1 v17_1;
split v18_1 tmp_to_use_4 v14_1 16;
assume v16_1 = tmp_to_use_4 * 68719476736 && true;
mov r21_32_1 v18_1;
mov c0_1 r21_0_1;
mov c1_1 r21_8_1;
mov c2_1 r21_16_1;
mov c3_1 r21_24_1;
mov c4_1 r21_32_1;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896) && and [tmp_to_use_1 = v2_1, v7_1 = add (v3_1) (v6_1), v6_1 = mul (tmp_to_use_2) (4096@64), v12_1 = add (v8_1) (v11_1), v11_1 = mul (tmp_to_use_3) (16777216@64), v17_1 = add (v13_1) (v16_1), v16_1 = mul (tmp_to_use_4) (68719476736@64)] }
