(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_normalizes_to_zero_tuned.cl

Results of checking CNF formulas:       [OK]            114.443286 seconds
Verification result:                    [OK]            136.895555 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0) =
{ true && and [a0_0 <=u 9223372036854775808@64, a1_0 <=u 9223372036854775808@64, a2_0 <=u 9223372036854775808@64, a3_0 <=u 9223372036854775808@64, a4_0 <=u 9223372036854775808@64] }
mov p0_1 4503595332402223@uint64;
mov p1_1 4503599627370495@uint64;
mov p2_1 4503599627370495@uint64;
mov p3_1 4503599627370495@uint64;
mov p4_1 281474976710655@uint64;
mov r12_0_1 a0_0;
mov r12_8_1 a1_0;
mov r12_16_1 a2_0;
mov r12_24_1 a3_0;
mov r12_32_1 a4_0;
mov t013_1 r12_0_1;
mov t114_1 r12_8_1;
mov t215_1 r12_16_1;
mov t316_1 r12_24_1;
mov t417_1 r12_32_1;
split x18_1 tmp_to_use_1 t417_1 48;
and t419_1@uint64 t417_1 281474976710655@uint64;
mul v1_1 x18_1 4294968273@uint64;
add t020_1 v1_1 t013_1;
split v2_1 tmp_to_use_2 t020_1 52;
add t121_1 v2_1 t114_1;
and t022_1@uint64 t020_1 4503599627370495@uint64;
not nt022_1@uint64 t022_1;
not nvalue_1@uint64 4294968272@uint64;
and vn_1@uint64 t022_1 nvalue_1;
and nv_1@uint64 nt022_1 4294968272@uint64;
or z123_1@uint64 vn_1 nv_1;
split v3_1 tmp_to_use_3 t121_1 52;
add t224_1 v3_1 t215_1;
or v7_1@uint64 t020_1 t121_1;
split v4_1 tmp_to_use_4 t224_1 52;
add t327_1 v4_1 t316_1;
or v37_1@uint64 v7_1 t224_1;
and v35_1@uint64 t121_1 z123_1;
split v5_1 tmp_to_use_5 t327_1 52;
add t430_1 v5_1 t419_1;
or v38_1@uint64 t327_1 v37_1;
and z032_1@uint64 v38_1 4503599627370495@uint64;
or z034_1@uint64 t430_1 z032_1;
not nt430_1@uint64 t430_1;
not nvalue_2@uint64 4222124650659840@uint64;
and vn_2@uint64 t430_1 nvalue_2;
and nv_2@uint64 nt430_1 4222124650659840@uint64;
or v6_1@uint64 vn_2 nv_2;
and v25_1@uint64 t224_1 v35_1;
and v26_1@uint64 v25_1 t327_1;
and v44_1@uint64 v6_1 v26_1;
subb lt_value_1 dontcare_1 z034_1 0@uint64;
subb gt_value_1 dontcare_2 0@uint64 z034_1;
or v8_1@uint1 lt_value_1 gt_value_1;
not v8_2@uint1 v8_1;
vpc v8_3@uint8 v8_2;
subb lt_value_2 dontcare_3 v44_1 4503599627370495@uint64;
subb gt_value_2 dontcare_4 4503599627370495@uint64 v44_1;
or v9_1@uint1 lt_value_2 gt_value_2;
not v9_2@uint1 v9_1;
vpc v9_3@uint8 v9_2;
or v10_1@uint8 v8_3 v9_3;
cast v36_1@int32 v10_1;
mov is_zero_1 v36_1;
{ true && is_zero_1 = 1@32 /\ umod (add (mul (uext 0@64 208) (1@272)) (add (mul (uext 0@64 208) (4503599627370496@272)) (add (mul (uext 0@64 208) (20282409603651670423947251286016@272)) (add (mul (uext 0@64 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext 0@64 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) = umod (add (mul (uext a0_0 208) (1@272)) (add (mul (uext a1_0 208) (4503599627370496@272)) (add (mul (uext a2_0 208) (20282409603651670423947251286016@272)) (add (mul (uext a3_0 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext a4_0 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) \/ is_zero_1 = 0@32 /\ ~ (add (mul (uext 0@64 208) (1@272)) (add (mul (uext 0@64 208) (4503599627370496@272)) (add (mul (uext 0@64 208) (20282409603651670423947251286016@272)) (add (mul (uext 0@64 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext 0@64 208) (411376139330301510538742295639337626245683966408394965837152256@272))))) = umod (add (mul (uext a0_0 208) (1@272)) (add (mul (uext a1_0 208) (4503599627370496@272)) (add (mul (uext a2_0 208) (20282409603651670423947251286016@272)) (add (mul (uext a3_0 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext a4_0 208) (411376139330301510538742295639337626245683966408394965837152256@272)))))) (add (mul (uext p0_1 208) (1@272)) (add (mul (uext p1_1 208) (4503599627370496@272)) (add (mul (uext p2_1 208) (20282409603651670423947251286016@272)) (add (mul (uext p3_1 208) (91343852333181432387730302044767688728495783936@272)) (mul (uext p4_1 208) (411376139330301510538742295639337626245683966408394965837152256@272))))))) }
