(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_normalize_tuned.cl

Results of checking CNF formulas:       [OK]            584.862541 seconds
Verification result:                    [OK]            606.925396 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <=u 9223372036854775808@64, a1_0 <=u 9223372036854775808@64, a2_0 <=u 9223372036854775808@64, a3_0 <=u 9223372036854775808@64, a4_0 <=u 9223372036854775808@64] }
mov p0_1 4503595332402223@uint64;
mov p1_1 4503599627370495@uint64;
mov p2_1 4503599627370495@uint64;
mov p3_1 4503599627370495@uint64;
mov p4_1 281474976710655@uint64;
mov r19_0_1 a0_0;
mov r19_8_1 a1_0;
mov r19_16_1 a2_0;
mov r19_24_1 a3_0;
mov r19_32_1 a4_0;
mov t020_1 r19_0_1;
mov t121_1 r19_8_1;
mov t222_1 r19_16_1;
mov t323_1 r19_24_1;
mov t424_1 r19_32_1;
split x25_1 t426_1 t424_1 48;
mul v1_1 x25_1 4294968273@uint64;
add t027_1 v1_1 t020_1;
split v2_1 t029_1 t027_1 52;
add t128_1 v2_1 t121_1;
split v3_1 t131_1 t128_1 52;
add t230_1 v3_1 t222_1;
split v4_1 t233_1 t230_1 52;
add t332_1 v4_1 t323_1;
and m34_1@uint64 t131_1 t233_1;
split v5_1 t336_1 t332_1 52;
add t435_1 v5_1 t426_1;
and m37_1@uint64 m34_1 t336_1;
split v7_1 tmp_to_use_1 t435_1 48;
subb lt_value_1 dontcare_1 t435_1 281474976710655@uint64;
subb gt_value_1 dontcare_2 281474976710655@uint64 t435_1;
or v8_1@uint1 lt_value_1 gt_value_1;
not v8_2@uint1 v8_1;
subb lt_value_2 dontcare_3 m37_1 4503599627370495@uint64;
subb gt_value_2 dontcare_4 4503599627370495@uint64 m37_1;
or v9_1@uint1 lt_value_2 gt_value_2;
not v9_2@uint1 v9_1;
and v10_1@uint1 v8_2 v9_2;
subb v11_1 dontcare_5 4503595332402222@uint64 t029_1;
and v6_1@uint1 v10_1 v11_1;
vpc v12_1@uint64 v6_1;
or x38_1@uint64 v7_1 v12_1;
mul v13_1 x38_1 4294968273@uint64;
add t039_1 v13_1 t029_1;
split v14_1 t041_1 t039_1 52;
add t140_1 v14_1 t131_1;
split v15_1 t143_1 t140_1 52;
add t242_1 v15_1 t233_1;
split v16_1 t245_1 t242_1 52;
add t344_1 v16_1 t336_1;
split v17_1 t347_1 t344_1 52;
add t446_1 v17_1 t435_1;
split tmp_and_1 t448_1 t446_1 48;
mov r19_0_2 t041_1;
mov r19_8_2 t143_1;
mov r19_16_2 t245_1;
mov r19_24_2 t347_1;
mov r19_32_2 t448_1;
mov c0_1 r19_0_2;
mov c1_1 r19_8_2;
mov c2_1 r19_16_2;
mov c3_1 r19_24_2;
mov c4_1 r19_32_2;
{ true && and [umod (add (mul (uext c0_1 208) (1@272)) (add (mul (uext c1_1 208) (4503599627370496@272)) (add (mul (uext c2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext c3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext c4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) = umod (add (mul (uext a0_0 208) (1@272)) (add (mul (uext a1_0 208) (4503599627370496@272)) (add (mul (uext a2_0 208) (20282409603651670423947251286016@272)) (add (mul (uext a3_0 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext a4_0 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))), c0_1 <u 4503599627370496@64, c1_1 <u 4503599627370496@64, c2_1 <u 4503599627370496@64, c3_1 <u 4503599627370496@64, c4_1 <u 4503599627370496@64] }
