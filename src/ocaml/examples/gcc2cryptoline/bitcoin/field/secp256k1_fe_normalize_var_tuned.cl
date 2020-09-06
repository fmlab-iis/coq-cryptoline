(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_normalize_var_tuned.cl

Results of checking CNF formulas:       [OK]            2.119597 seconds
Verification result:                    [OK]            24.320307 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <=u 9223372036854775808@64, a1_0 <=u 9223372036854775808@64, a2_0 <=u 9223372036854775808@64, a3_0 <=u 9223372036854775808@64, a4_0 <=u 9223372036854775808@64] }
mov p0_1 4503595332402223@uint64;
mov p1_1 4503599627370495@uint64;
mov p2_1 4503599627370495@uint64;
mov p3_1 4503599627370495@uint64;
mov p4_1 281474976710655@uint64;
mov r23_0_1 a0_0;
mov r23_8_1 a1_0;
mov r23_16_1 a2_0;
mov r23_24_1 a3_0;
mov r23_32_1 a4_0;
mov t024_1 r23_0_1;
mov t125_1 r23_8_1;
mov t226_1 r23_16_1;
mov t327_1 r23_24_1;
mov t428_1 r23_32_1;
split x29_1 t430_1 t428_1 48;
mul v1_1 x29_1 4294968273@uint64;
add t031_1 v1_1 t024_1;
split v2_1 t033_1 t031_1 52;
add t132_1 v2_1 t125_1;
split v3_1 t135_1 t132_1 52;
add t234_1 v3_1 t226_1;
split v4_1 t237_1 t234_1 52;
add t336_1 v4_1 t327_1;
and m38_1@uint64 t135_1 t237_1;
split v5_1 t340_1 t336_1 52;
add t439_1 v5_1 t430_1;
and m41_1@uint64 m38_1 t340_1;
split v7_1 tmp_to_use_1 t439_1 48;
subc lt_value_1 dontcare_1 t439_1 281474976710655@uint64;
subc gt_value_1 dontcare_2 281474976710655@uint64 t439_1;
or v8_1@uint1 lt_value_1 gt_value_1;
not v8_2@uint1 v8_1;
subc lt_value_2 dontcare_3 m41_1 4503599627370495@uint64;
subc gt_value_2 dontcare_4 4503599627370495@uint64 m41_1;
or v9_1@uint1 lt_value_2 gt_value_2;
not v9_2@uint1 v9_1;
and v10_1@uint1 v8_2 v9_2;
subc v11_1 dontcare_5 4503595332402222@uint64 t033_1;
and v6_1@uint1 v10_1 v11_1;
vpc v12_1@uint64 v6_1;
vpc v7_2@uint64 v7_1;
or x42_1@uint64 v7_2 v12_1;
subc flag_1 dontcare_6 x42_1 1@uint64;
add t043_1 t033_1 4294968273@uint64;
split v13_1 t045_1 t043_1 52;
add t144_1 v13_1 t135_1;
split v14_1 t147_1 t144_1 52;
add t246_1 v14_1 t237_1;
split v15_1 t249_1 t246_1 52;
add t348_1 v15_1 t340_1;
split v16_1 t351_1 t348_1 52;
add t450_1 v16_1 t439_1;
split tmp_and_1 t452_1 t450_1 48;
cmov t017_1 flag_1 t045_1 t033_1;
cmov t118_1 flag_1 t147_1 t135_1;
cmov t219_1 flag_1 t249_1 t237_1;
cmov t320_1 flag_1 t351_1 t340_1;
cmov t421_1 flag_1 t452_1 t439_1;
mov v58_0_1 t219_1;
mov v58_1_1 t320_1;
mov v60_0_1 t017_1;
mov v60_1_1 t118_1;
mov r23_0_2 v60_0_1;
mov r23_8_2 v60_1_1;
mov r23_16_2 v58_0_1;
mov r23_24_2 v58_1_1;
mov r23_32_2 t421_1;
mov c0_1 r23_0_2;
mov c1_1 r23_8_2;
mov c2_1 r23_16_2;
mov c3_1 r23_24_2;
mov c4_1 r23_32_2;
{ true && and [umod (add (mul (uext c0_1 208) (1@272)) (add (mul (uext c1_1 208) (4503599627370496@272)) (add (mul (uext c2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext c3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext c4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) = umod (add (mul (uext a0_0 208) (1@272)) (add (mul (uext a1_0 208) (4503599627370496@272)) (add (mul (uext a2_0 208) (20282409603651670423947251286016@272)) (add (mul (uext a3_0 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext a4_0 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))), c0_1 <u 4503599627370496@64, c1_1 <u 4503599627370496@64, c2_1 <u 4503599627370496@64, c3_1 <u 4503599627370496@64, c4_1 <u 4503599627370496@64] }