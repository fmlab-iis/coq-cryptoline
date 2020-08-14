(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=32G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=32G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_ge_from_storage_tuned.cl

Results of checking CNF formulas:       [OK]            1.122157 seconds
Finding polynomial coefficients         [OK]            0.087690 seconds
Finding polynomial coefficients         [OK]            0.092577 seconds
Verification result:                    [OK]            1.751593 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, uint64 a5_0, uint64 a6_0, uint64 a7_0) =
{ true && true }
mov a5_0_1 a0_0;
mov a5_8_1 a1_0;
mov a5_16_1 a2_0;
mov a5_24_1 a3_0;
mov a5_32_1 a4_0;
mov a5_40_1 a5_0;
mov a5_48_1 a6_0;
mov a5_56_1 a7_0;
mov v29_1 a5_0_1;
and v30_1@uint64 v29_1 4503599627370495@uint64;
mov r6_0_1 v30_1;
split v31_1 tmp_to_use_1 v29_1 52;
assume tmp_to_use_1 = v30_1 && true;
mov v32_1 a5_8_1;
split tmp1_1 tmp2_1 v32_1 52;
shl v33_1 tmp2_1 12;
and v34_1@uint64 v33_1 4503599627370495@uint64;
or v35_1@uint64 v31_1 v34_1;
assume v35_1 = v31_1 + v34_1 && true;
mov r6_8_1 v35_1;
split v36_1 tmp_to_use_2 v32_1 40;
assume v34_1 = tmp_to_use_2 * 4096 && true;
mov v37_1 a5_16_1;
split tmp1_2 tmp2_2 v37_1 40;
shl v38_1 tmp2_2 24;
and v39_1@uint64 v38_1 4503599627370495@uint64;
or v40_1@uint64 v36_1 v39_1;
assume v40_1 = v36_1 + v39_1 && true;
mov r6_16_1 v40_1;
split v41_1 tmp_to_use_3 v37_1 28;
assume v39_1 = tmp_to_use_3 * 16777216 && true;
mov v42_1 a5_24_1;
split tmp1_3 tmp2_3 v42_1 28;
shl v43_1 tmp2_3 36;
and v44_1@uint64 v43_1 4503599627370495@uint64;
or v45_1@uint64 v41_1 v44_1;
assume v45_1 = v41_1 + v44_1 && true;
mov r6_24_1 v45_1;
split v46_1 tmp_to_use_4 v42_1 16;
assume v44_1 = tmp_to_use_4 * 68719476736 && true;
mov r6_32_1 v46_1;
mov v11_1 a5_32_1;
and v12_1@uint64 v11_1 4503599627370495@uint64;
mov r6_40_1 v12_1;
split v13_1 tmp_to_use_5 v11_1 52;
assume v12_1 = tmp_to_use_5 && true;
mov v14_1 a5_40_1;
split tmp1_4 tmp2_4 v14_1 52;
shl v15_1 tmp2_4 12;
and v16_1@uint64 v15_1 4503599627370495@uint64;
or v17_1@uint64 v13_1 v16_1;
assume v17_1 = v13_1 + v16_1 && true;
mov r6_48_1 v17_1;
split v18_1 tmp_to_use_6 v14_1 40;
assume v16_1 = tmp_to_use_6 * 4096 && true;
mov v19_1 a5_48_1;
split tmp1_5 tmp2_5 v19_1 40;
shl v20_1 tmp2_5 24;
and v21_1@uint64 v20_1 4503599627370495@uint64;
or v22_1@uint64 v18_1 v21_1;
assume v22_1 = v18_1 + v21_1 && true;
mov r6_56_1 v22_1;
split v23_1 tmp_to_use_7 v19_1 28;
assume v21_1 = tmp_to_use_7 * 16777216 && true;
mov v24_1 a5_56_1;
split tmp1_6 tmp2_6 v24_1 28;
shl v25_1 tmp2_6 36;
and v26_1@uint64 v25_1 4503599627370495@uint64;
or v27_1@uint64 v23_1 v26_1;
assume v27_1 = v23_1 + v26_1 && true;
mov r6_64_1 v27_1;
split v28_1 tmp_to_use_8 v24_1 16;
assume v26_1 = tmp_to_use_8 * 68719476736 && true;
mov r6_72_1 v28_1;
mov r6_80_1 0@int32;
mov c0_1 r6_0_1;
mov c1_1 r6_8_1;
mov c2_1 r6_16_1;
mov c3_1 r6_24_1;
mov c4_1 r6_32_1;
mov c5_1 r6_40_1;
mov c6_1 r6_48_1;
mov c7_1 r6_56_1;
mov c8_1 r6_64_1;
mov c9_1 r6_72_1;
mov c10_1 r6_80_1;
{ c0_1 + (c1_1 * 4503599627370496) + (c2_1 * 20282409603651670423947251286016) + (c3_1 * 91343852333181432387730302044767688728495783936) + (c4_1 * 411376139330301510538742295639337626245683966408394965837152256) = a0_0 + (a1_0 * 18446744073709551616) + (a2_0 * 340282366920938463463374607431768211456) + (a3_0 * 6277101735386680763835789423207666416102355444464034512896) /\ c5_1 + (c6_1 * 4503599627370496) + (c7_1 * 20282409603651670423947251286016) + (c8_1 * 91343852333181432387730302044767688728495783936) + (c9_1 * 411376139330301510538742295639337626245683966408394965837152256) = a4_0 + (a5_0 * 18446744073709551616) + (a6_0 * 340282366920938463463374607431768211456) + (a7_0 * 6277101735386680763835789423207666416102355444464034512896) && and [tmp_to_use_1 = v30_1, v35_1 = add (v31_1) (v34_1), v34_1 = mul (tmp_to_use_2) (4096@64), v40_1 = add (v36_1) (v39_1), v39_1 = mul (tmp_to_use_3) (16777216@64), v45_1 = add (v41_1) (v44_1), v44_1 = mul (tmp_to_use_4) (68719476736@64), v12_1 = tmp_to_use_5, v17_1 = add (v13_1) (v16_1), v16_1 = mul (tmp_to_use_6) (4096@64), v22_1 = add (v18_1) (v21_1), v21_1 = mul (tmp_to_use_7) (16777216@64), v27_1 = add (v23_1) (v26_1), v26_1 = mul (tmp_to_use_8) (68719476736@64)] }
