proc main(uint64 a0_0, uint64 a1_0, uint64 a2_0, uint64 a3_0, uint64 a4_0, int32 flag_0, uint64 r0_0, uint64 r1_0, uint64 r2_0, uint64 r3_0, uint64 r4_0) =
{ true && and [a0_0 <u 72057594037927928@64, a1_0 <u 72057594037927928@64, a2_0 <u 72057594037927928@64, a3_0 <u 72057594037927928@64, a4_0 <u 4503599627370488@64, r0_0 <u 72057594037927928@64, r1_0 <u 72057594037927928@64, r2_0 <u 72057594037927928@64, r3_0 <u 72057594037927928@64, r4_0 <u 4503599627370488@64, flag_0 <=u 1@32, flag_0 >=u 0@32] }
vpc flag27_bit_1@uint1 flag_0;
vpc flag27_p_1@uint64 flag_0;
vpc v1_1@uint64 flag_0;
adds carry_0_1 vect_mask0_2843449_0_1 flag27_p_1 18446744073709551615@uint64;
adds carry_1_1 vect_mask0_2843449_1_1 flag27_p_1 18446744073709551615@uint64;
assume carry_0_1 = flag27_bit_1 && true;
assume carry_1_1 = flag27_bit_1 && true;
adds carry_0_2 vect_mask0_2843450_0_1 flag27_p_1 18446744073709551615@uint64;
adds carry_1_2 vect_mask0_2843450_1_1 flag27_p_1 18446744073709551615@uint64;
assume carry_0_2 = flag27_bit_1 && true;
assume carry_1_2 = flag27_bit_1 && true;
adds carry_1 mask028_1 v1_1 18446744073709551615@uint64;
subb carry_0_3 vect__3744058_0_1 0@uint64 flag27_p_1;
subb carry_1_3 vect__3744058_1_1 0@uint64 flag27_p_1;
assume carry_0_3 = flag27_bit_1 && true;
assume carry_1_3 = flag27_bit_1 && true;
subb carry_0_4 vect__3744059_0_1 0@uint64 flag27_p_1;
subb carry_1_4 vect__3744059_1_1 0@uint64 flag27_p_1;
assume carry_0_4 = flag27_bit_1 && true;
assume carry_1_4 = flag27_bit_1 && true;
subb carry_2 v37_1 0@uint64 v1_1;
assume carry_2 = flag27_bit_1 && true;
and vect__343551_0_1@uint64 r0_0 vect_mask0_2843449_0_1;
and vect__343551_1_1@uint64 r1_0 vect_mask0_2843449_1_1;
and vect__343552_0_1@uint64 r2_0 vect_mask0_2843450_0_1;
and vect__343552_1_1@uint64 r3_0 vect_mask0_2843450_1_1;
and vect__544160_0_1@uint64 a0_0 vect__3744058_0_1;
and vect__544160_1_1@uint64 a1_0 vect__3744058_1_1;
and vect__544161_0_1@uint64 a2_0 vect__3744059_0_1;
and vect__544161_1_1@uint64 a3_0 vect__3744059_1_1;
or vect__644262_0_1@uint64 vect__343551_0_1 vect__544160_0_1;
or vect__644262_1_1@uint64 vect__343551_1_1 vect__544160_1_1;
or vect__644263_0_1@uint64 vect__343552_0_1 vect__544161_0_1;
or vect__644263_1_1@uint64 vect__343552_1_1 vect__544161_1_1;
and v23_1@uint64 r4_0 mask028_1;
and v25_1@uint64 a4_0 v37_1;
or v26_1@uint64 v23_1 v25_1;
assume vect__644262_0_1 = ((1 - flag27_p_1) * r0_0) + (flag27_p_1 * a0_0) && true;
assume vect__644262_1_1 = ((1 - flag27_p_1) * r1_0) + (flag27_p_1 * a1_0) && true;
assume vect__644263_0_1 = ((1 - flag27_p_1) * r2_0) + (flag27_p_1 * a2_0) && true;
assume vect__644263_1_1 = ((1 - flag27_p_1) * r3_0) + (flag27_p_1 * a3_0) && true;
assume v26_1 = ((1 - flag27_p_1) * r4_0) + (flag27_p_1 * a4_0) && true;
{ and [vect__644262_0_1 = ((1 - flag_0) * r0_0) + (flag_0 * a0_0), vect__644262_1_1 = ((1 - flag_0) * r1_0) + (flag_0 * a1_0), vect__644263_0_1 = ((1 - flag_0) * r2_0) + (flag_0 * a2_0), vect__644263_1_1 = ((1 - flag_0) * r3_0) + (flag_0 * a3_0), v26_1 = ((1 - flag_0) * r4_0) + (flag_0 * a4_0)] && and [carry_0_1 = flag27_bit_1, carry_1_1 = flag27_bit_1, carry_0_2 = flag27_bit_1, carry_1_2 = flag27_bit_1, carry_0_3 = flag27_bit_1, carry_1_3 = flag27_bit_1, carry_0_4 = flag27_bit_1, carry_1_4 = flag27_bit_1, carry_2 = flag27_bit_1, vect__644262_0_1 = add (mul (sub (1@64) (flag27_p_1)) (r0_0)) (mul (flag27_p_1) (a0_0)), vect__644262_1_1 = add (mul (sub (1@64) (flag27_p_1)) (r1_0)) (mul (flag27_p_1) (a1_0)), vect__644263_0_1 = add (mul (sub (1@64) (flag27_p_1)) (r2_0)) (mul (flag27_p_1) (a2_0)), vect__644263_1_1 = add (mul (sub (1@64) (flag27_p_1)) (r3_0)) (mul (flag27_p_1) (a3_0)), v26_1 = add (mul (sub (1@64) (flag27_p_1)) (r4_0)) (mul (flag27_p_1) (a4_0))] }