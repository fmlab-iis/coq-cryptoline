(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=8G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=8G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  secp256k1_fe_cmov_tuned.cl

Results of checking CNF formulas:       [OK]            1.720699 seconds
Finding polynomial coefficients         [OK]            0.085343 seconds
Finding polynomial coefficients         [OK]            0.086131 seconds
Finding polynomial coefficients         [OK]            0.085879 seconds
Finding polynomial coefficients         [OK]            0.087602 seconds
Finding polynomial coefficients         [OK]            0.083021 seconds
Verification result:                    [OK]            3.196219 seconds
*)

proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, int32 flag_0, uint64 r0_0, uint64 r1_0, uint64 r2_0, uint64 r3_0, uint64 r4_0) =
{ true && and [a0_0 <u 72057594037927928@64, a1_0 <u 72057594037927928@64, a2_0 <u 72057594037927928@64, a3_0 <u 72057594037927928@64, a4_0 <u 4503599627370488@64, r0_0 <u 72057594037927928@64, r1_0 <u 72057594037927928@64, r2_0 <u 72057594037927928@64, r3_0 <u 72057594037927928@64, r4_0 <u 4503599627370488@64, flag_0 <=u 1@32, flag_0 >=u 0@32] }
mov a31_0_1 a0_0;
mov a31_8_1 a1_0;
mov a31_16_1 a2_0;
mov a31_24_1 a3_0;
mov a31_32_1 a4_0;
mov flag27_1 flag_0;
mov r30_0_1 r0_0;
mov r30_8_1 r1_0;
mov r30_16_1 r2_0;
mov r30_24_1 r3_0;
mov r30_32_1 r4_0;
vpc flag27_bit_1@uint1 flag27_1;
vpc flag27_p_1@uint64 flag27_1;
mov v43_0_1 flag27_p_1;
mov v43_1_1 flag27_p_1;
mov v43_2_1 flag27_p_1;
mov v43_3_1 flag27_p_1;
mov vect__143345_0_1 v43_0_1;
mov vect__143345_1_1 v43_1_1;
mov vect__143346_0_1 v43_2_1;
mov vect__143346_1_1 v43_3_1;
vpc v1_1@uint64 flag27_1;
adds carry_0_1 vect_mask0_2843449_0_1 vect__143345_0_1 18446744073709551615@uint64;
adds carry_1_1 vect_mask0_2843449_1_1 vect__143345_1_1 18446744073709551615@uint64;
assume carry_0_1 = flag27_bit_1 && true;
assume carry_1_1 = flag27_bit_1 && true;
adds carry_0_2 vect_mask0_2843450_0_1 vect__143346_0_1 18446744073709551615@uint64;
adds carry_1_2 vect_mask0_2843450_1_1 vect__143346_1_1 18446744073709551615@uint64;
assume carry_0_2 = flag27_bit_1 && true;
assume carry_1_2 = flag27_bit_1 && true;
adds carry_1 mask028_1 v1_1 18446744073709551615@uint64;
subb carry_0_3 vect__3744058_0_1 0@uint64 vect__143345_0_1;
subb carry_1_3 vect__3744058_1_1 0@uint64 vect__143345_1_1;
assume carry_0_3 = flag27_bit_1 && true;
assume carry_1_3 = flag27_bit_1 && true;
subb carry_0_4 vect__3744059_0_1 0@uint64 vect__143346_0_1;
subb carry_1_4 vect__3744059_1_1 0@uint64 vect__143346_1_1;
assume carry_0_4 = flag27_bit_1 && true;
assume carry_1_4 = flag27_bit_1 && true;
subb carry_2 v37_1 0@uint64 v1_1;
assume carry_2 = flag27_bit_1 && true;
mov vect__243138_0_1 r30_0_1;
mov vect__243138_1_1 r30_8_1;
mov vect__243241_0_1 r30_16_1;
mov vect__243241_1_1 r30_24_1;
and vect__343551_0_1@uint64 vect__243138_0_1 vect_mask0_2843449_0_1;
and vect__343551_1_1@uint64 vect__243138_1_1 vect_mask0_2843449_1_1;
and vect__343552_0_1@uint64 vect__243241_0_1 vect_mask0_2843450_0_1;
and vect__343552_1_1@uint64 vect__243241_1_1 vect_mask0_2843450_1_1;
mov vect__443854_0_1 a31_0_1;
mov vect__443854_1_1 a31_8_1;
mov vect__443956_0_1 a31_16_1;
mov vect__443956_1_1 a31_24_1;
and vect__544160_0_1@uint64 vect__443854_0_1 vect__3744058_0_1;
and vect__544160_1_1@uint64 vect__443854_1_1 vect__3744058_1_1;
and vect__544161_0_1@uint64 vect__443956_0_1 vect__3744059_0_1;
and vect__544161_1_1@uint64 vect__443956_1_1 vect__3744059_1_1;
or vect__644262_0_1@uint64 vect__343551_0_1 vect__544160_0_1;
or vect__644262_1_1@uint64 vect__343551_1_1 vect__544160_1_1;
or vect__644263_0_1@uint64 vect__343552_0_1 vect__544161_0_1;
or vect__644263_1_1@uint64 vect__343552_1_1 vect__544161_1_1;
mov r30_0_2 vect__644262_0_1;
mov r30_8_2 vect__644262_1_1;
mov r30_16_2 vect__644263_0_1;
mov r30_24_2 vect__644263_1_1;
mov v22_1 r30_32_1;
and v23_1@uint64 v22_1 mask028_1;
mov v24_1 a31_32_1;
and v25_1@uint64 v24_1 v37_1;
or v26_1@uint64 v23_1 v25_1;
mov r30_32_2 v26_1;
assume r30_0_2 = ((1 - flag27_p_1) * r0_0) + (flag27_p_1 * a0_0) && true;
assume r30_8_2 = ((1 - flag27_p_1) * r1_0) + (flag27_p_1 * a1_0) && true;
assume r30_16_2 = ((1 - flag27_p_1) * r2_0) + (flag27_p_1 * a2_0) && true;
assume r30_24_2 = ((1 - flag27_p_1) * r3_0) + (flag27_p_1 * a3_0) && true;
assume r30_32_2 = ((1 - flag27_p_1) * r4_0) + (flag27_p_1 * a4_0) && true;
mov c0_1 r30_0_2;
mov c1_1 r30_8_2;
mov c2_1 r30_16_2;
mov c3_1 r30_24_2;
mov c4_1 r30_32_2;
{ and [c0_1 = ((1 - flag27_1) * r0_0) + (flag27_1 * a0_0), c1_1 = ((1 - flag27_1) * r1_0) + (flag27_1 * a1_0), c2_1 = ((1 - flag27_1) * r2_0) + (flag27_1 * a2_0), c3_1 = ((1 - flag27_1) * r3_0) + (flag27_1 * a3_0), c4_1 = ((1 - flag27_1) * r4_0) + (flag27_1 * a4_0)] && and [carry_0_1 = flag27_bit_1, carry_1_1 = flag27_bit_1, carry_0_2 = flag27_bit_1, carry_1_2 = flag27_bit_1, carry_0_3 = flag27_bit_1, carry_1_3 = flag27_bit_1, carry_0_4 = flag27_bit_1, carry_1_4 = flag27_bit_1, carry_2 = flag27_bit_1, r30_0_2 = add (mul (sub (1@64) (flag27_p_1)) (r0_0)) (mul (flag27_p_1) (a0_0)), r30_8_2 = add (mul (sub (1@64) (flag27_p_1)) (r1_0)) (mul (flag27_p_1) (a1_0)), r30_16_2 = add (mul (sub (1@64) (flag27_p_1)) (r2_0)) (mul (flag27_p_1) (a2_0)), r30_24_2 = add (mul (sub (1@64) (flag27_p_1)) (r3_0)) (mul (flag27_p_1) (a3_0)), r30_32_2 = add (mul (sub (1@64) (flag27_p_1)) (r4_0)) (mul (flag27_p_1) (a4_0))] }
