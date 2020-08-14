(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_scalar_eq_tuned.cl

Results of checking CNF formulas:       [OK]            0.879218 seconds
Verification result:                    [OK]            0.936492 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 b0_0, uint64 b1_0, uint64 b2_0, uint64 b3_0) =
{ true && true }
mov a18_0_1 a0_0;
mov a18_8_1 a1_0;
mov a18_16_1 a2_0;
mov a18_24_1 a3_0;
mov b19_0_1 b0_0;
mov b19_8_1 b1_0;
mov b19_16_1 b2_0;
mov b19_24_1 b3_0;
mov v1_1 a18_0_1;
mov v2_1 b19_0_1;
not nv1_1@uint64 v1_1;
not nv2_1@uint64 v2_1;
and v1nv2_1@uint64 v1_1 nv2_1;
and nv1v2_1@uint64 nv1_1 v2_1;
or v3_1@uint64 v1nv2_1 nv1v2_1;
mov v4_1 a18_8_1;
mov v5_1 b19_8_1;
not nv4_1@uint64 v4_1;
not nv5_1@uint64 v5_1;
and v4nv5_1@uint64 v4_1 nv5_1;
and nv4v5_1@uint64 nv4_1 v5_1;
or v6_1@uint64 v4nv5_1 nv4v5_1;
or v7_1@uint64 v3_1 v6_1;
mov v8_1 a18_16_1;
mov v9_1 b19_16_1;
not nv8_1@uint64 v8_1;
not nv9_1@uint64 v9_1;
and v8nv9_1@uint64 v8_1 nv9_1;
and nv8v9_1@uint64 nv8_1 v9_1;
or v10_1@uint64 v8nv9_1 nv8v9_1;
or v11_1@uint64 v7_1 v10_1;
mov v12_1 a18_24_1;
mov v13_1 b19_24_1;
not nv12_1@uint64 v12_1;
not nv13_1@uint64 v13_1;
and v12nv13_1@uint64 v12_1 nv13_1;
and nv12v13_1@uint64 nv12_1 v13_1;
or v14_1@uint64 v12nv13_1 nv12v13_1;
or v15_1@uint64 v11_1 v14_1;
subb gt_value_1 dontcare_1 0@uint64 v15_1;
mov v16_1 gt_value_1;
not v16_2@uint1 v16_1;
vpc v16_3@uint8 v16_2;
cast v20_1@int32 v16_3;
mov c_1 v20_1;
{ true && or [c_1 >u 0@32 /\ add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))) = add (mul (uext b0_0 192) (1@256)) (add (mul (uext b1_0 192) (18446744073709551616@256)) (add (mul (uext b2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext b3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))), c_1 = 0@32 /\ add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))) >u add (mul (uext b0_0 192) (1@256)) (add (mul (uext b1_0 192) (18446744073709551616@256)) (add (mul (uext b2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext b3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))), c_1 = 0@32 /\ add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))) <u add (mul (uext b0_0 192) (1@256)) (add (mul (uext b1_0 192) (18446744073709551616@256)) (add (mul (uext b2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext b3_0 192) (6277101735386680763835789423207666416102355444464034512896@256))))] }
