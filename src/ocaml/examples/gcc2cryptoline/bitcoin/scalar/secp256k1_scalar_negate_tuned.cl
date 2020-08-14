(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_scalar_negate_tuned.cl

Results of checking CNF formulas:       [OK]            39.621084 seconds
Verification result:                    [OK]            58.358856 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0) =
{ true && add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))) <u add (mul (uext 13822214165235122497@64 192) (1@256)) (add (mul (uext 13451932020343611451@64 192) (18446744073709551616@256)) (add (mul (uext 18446744073709551614@64 192) (340282366920938463463374607431768211456@256)) (mul (uext 18446744073709551615@64 192) (6277101735386680763835789423207666416102355444464034512896@256)))) }
mov a23_0_1 a0_0;
mov a23_8_1 a1_0;
mov a23_16_1 a2_0;
mov a23_24_1 a3_0;
mov v24_1 a23_0_1;
mov v38_1 a23_8_1;
or v39_1@uint64 v24_1 v38_1;
mov v40_1 a23_16_1;
or v41_1@uint64 v39_1 v40_1;
mov v42_1 a23_24_1;
or v43_1@uint64 v41_1 v42_1;
subb gt_value_1 dontcare_1 0@uint64 v43_1;
mov v1_1 gt_value_1;
vpc v1_2@uint8 v1_1;
vpc v2_1@uint64 v1_2;
subb carry_1 nonzero25_1 0@uint64 v2_1;
not v3_1@uint64 v24_1;
vpc v4_1@uint128 v3_1;
mov value_lo_1 13822214165235122498@uint64;
mov value_hi_1 0@uint64;
join value_1 value_hi_1 value_lo_1;
add t26_1 v4_1 value_1;
adds dontcare_2 v5_1 v3_1 13822214165235122498@uint64;
and v6_1@uint64 v5_1 nonzero25_1;
mov r27_0_1 v6_1;
split t29_1 tmp_to_use_1 t26_1 64;
not v7_1@uint64 v38_1;
vpc v8_1@uint128 v7_1;
mov value_lo_2 13451932020343611451@uint64;
mov value_hi_2 0@uint64;
join value_2 value_hi_2 value_lo_2;
add v46_1 v8_1 value_2;
add t30_1 t29_1 v46_1;
cast v10_1@uint64 t30_1;
and v11_1@uint64 v10_1 nonzero25_1;
mov r27_8_1 v11_1;
split t32_1 tmp_to_use_2 t30_1 64;
not v12_1@uint64 v40_1;
vpc v13_1@uint128 v12_1;
mov value_lo_3 18446744073709551614@uint64;
mov value_hi_3 0@uint64;
join value_3 value_hi_3 value_lo_3;
add v44_1 v13_1 value_3;
add t33_1 t32_1 v44_1;
cast v15_1@uint64 t33_1;
and v16_1@uint64 v15_1 nonzero25_1;
mov r27_16_1 v16_1;
split t35_1 tmp_to_use_3 t33_1 64;
not v17_1@uint64 v42_1;
vpc v18_1@uint128 v17_1;
mov value_lo_4 18446744073709551615@uint64;
mov value_hi_4 0@uint64;
join value_4 value_hi_4 value_lo_4;
add v45_1 v18_1 value_4;
add t36_1 t35_1 v45_1;
cast v20_1@uint64 t36_1;
and v21_1@uint64 v20_1 nonzero25_1;
mov r27_24_1 v21_1;
mov c0_1 r27_0_1;
mov c1_1 r27_8_1;
mov c2_1 r27_16_1;
mov c3_1 r27_24_1;
{ true && (nonzero25_1 = 0@64 /\ add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))) = add (mul (uext 0@64 192) (1@256)) (add (mul (uext 0@64 192) (18446744073709551616@256)) (add (mul (uext 0@64 192) (340282366920938463463374607431768211456@256)) (mul (uext 0@64 192) (6277101735386680763835789423207666416102355444464034512896@256)))) \/ nonzero25_1 = 18446744073709551615@64 /\ add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256)))) >u add (mul (uext 0@64 192) (1@256)) (add (mul (uext 0@64 192) (18446744073709551616@256)) (add (mul (uext 0@64 192) (340282366920938463463374607431768211456@256)) (mul (uext 0@64 192) (6277101735386680763835789423207666416102355444464034512896@256))))) /\ umod (add (mul (uext 0@64 192) (1@256)) (add (mul (uext 0@64 192) (18446744073709551616@256)) (add (mul (uext 0@64 192) (340282366920938463463374607431768211456@256)) (mul (uext 0@64 192) (6277101735386680763835789423207666416102355444464034512896@256))))) (add (mul (uext 13822214165235122497@64 192) (1@256)) (add (mul (uext 13451932020343611451@64 192) (18446744073709551616@256)) (add (mul (uext 18446744073709551614@64 192) (340282366920938463463374607431768211456@256)) (mul (uext 18446744073709551615@64 192) (6277101735386680763835789423207666416102355444464034512896@256))))) = umod (add (add (mul (uext a0_0 192) (1@256)) (add (mul (uext a1_0 192) (18446744073709551616@256)) (add (mul (uext a2_0 192) (340282366920938463463374607431768211456@256)) (mul (uext a3_0 192) (6277101735386680763835789423207666416102355444464034512896@256))))) (add (mul (uext c0_1 192) (1@256)) (add (mul (uext c1_1 192) (18446744073709551616@256)) (add (mul (uext c2_1 192) (340282366920938463463374607431768211456@256)) (mul (uext c3_1 192) (6277101735386680763835789423207666416102355444464034512896@256)))))) (add (mul (uext 13822214165235122497@64 192) (1@256)) (add (mul (uext 13451932020343611451@64 192) (18446744073709551616@256)) (add (mul (uext 18446744073709551614@64 192) (340282366920938463463374607431768211456@256)) (mul (uext 18446744073709551615@64 192) (6277101735386680763835789423207666416102355444464034512896@256))))) }
