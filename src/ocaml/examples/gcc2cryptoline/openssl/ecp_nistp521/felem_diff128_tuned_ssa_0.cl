proc main(uint128 a0_0, uint128 a1_0, uint128 a2_0, uint128 a3_0, uint128 a4_0, uint128 a5_0, uint128 a6_0, uint128 a7_0, uint128 a8_0, uint128 b0_0, uint128 b1_0, uint128 b2_0, uint128 b3_0, uint128 b4_0, uint128 b5_0, uint128 b6_0, uint128 b7_0, uint128 b8_0) =
{ true && and [a0_0 <u 85070591730234615865843651857942052864@128, a1_0 <u 85070591730234615865843651857942052864@128, a2_0 <u 85070591730234615865843651857942052864@128, a3_0 <u 85070591730234615865843651857942052864@128, a4_0 <u 85070591730234615865843651857942052864@128, a5_0 <u 85070591730234615865843651857942052864@128, a6_0 <u 85070591730234615865843651857942052864@128, a7_0 <u 85070591730234615865843651857942052864@128, a8_0 <u 85070591730234615865843651857942052864@128, b0_0 <u 85070591730234615865843651857942052864@128, b1_0 <u 85070591730234615865843651857942052864@128, b2_0 <u 85070591730234615865843651857942052864@128, b3_0 <u 85070591730234615865843651857942052864@128, b4_0 <u 85070591730234615865843651857942052864@128, b5_0 <u 85070591730234615865843651857942052864@128, b6_0 <u 85070591730234615865843651857942052864@128, b7_0 <u 85070591730234615865843651857942052864@128, b8_0 <u 85070591730234615865843651857942052864@128] }
subb carry_1 v3_1 a0_0 b0_0;
join value_1 9223372036854775744@uint64 0@uint64;
adds carry1_1 v4_1 v3_1 value_1;
assume carry_1 = carry1_1 && true;
subb carry_2 v7_1 a1_0 b1_0;
join value_2 9223372036854775776@uint64 0@uint64;
adds carry1_2 v8_1 v7_1 value_2;
assume carry_2 = carry1_2 && true;
subb carry_3 v11_1 a2_0 b2_0;
join value_3 9223372036854775776@uint64 0@uint64;
adds carry1_3 v12_1 v11_1 value_3;
assume carry_3 = carry1_3 && true;
subb carry_4 v15_1 a3_0 b3_0;
join value_4 9223372036854775776@uint64 0@uint64;
adds carry1_4 v16_1 v15_1 value_4;
assume carry_4 = carry1_4 && true;
subb carry_5 v19_1 a4_0 b4_0;
join value_5 9223372036854775776@uint64 0@uint64;
adds carry1_5 v20_1 v19_1 value_5;
assume carry_5 = carry1_5 && true;
subb carry_6 v23_1 a5_0 b5_0;
join value_6 9223372036854775776@uint64 0@uint64;
adds carry1_6 v24_1 v23_1 value_6;
assume carry_6 = carry1_6 && true;
subb carry_7 v27_1 a6_0 b6_0;
join value_7 9223372036854775776@uint64 0@uint64;
adds carry1_7 v28_1 v27_1 value_7;
assume carry_7 = carry1_7 && true;
subb carry_8 v31_1 a7_0 b7_0;
join value_8 9223372036854775776@uint64 0@uint64;
adds carry1_8 v32_1 v31_1 value_8;
assume carry_8 = carry1_8 && true;
subb carry_9 v35_1 a8_0 b8_0;
join value_9 9223372036854775776@uint64 0@uint64;
adds carry1_9 v36_1 v35_1 value_9;
assume carry_9 = carry1_9 && true;
{ v4_1 + (v8_1 * 288230376151711744) + (v12_1 * 83076749736557242056487941267521536) + (v16_1 * 23945242826029513411849172299223580994042798784118784) + (v20_1 * 6901746346790563787434755862277025452451108972170386555162524223799296) + (v24_1 * 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) + (v28_1 * 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656) + (v32_1 * 165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064) + (v36_1 * 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616) = a0_0 + (a1_0 * 288230376151711744) + (a2_0 * 83076749736557242056487941267521536) + (a3_0 * 23945242826029513411849172299223580994042798784118784) + (a4_0 * 6901746346790563787434755862277025452451108972170386555162524223799296) + (a5_0 * 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) + (a6_0 * 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656) + (a7_0 * 165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064) + (a8_0 * 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616) - (b0_0 + (b1_0 * 288230376151711744) + (b2_0 * 83076749736557242056487941267521536) + (b3_0 * 23945242826029513411849172299223580994042798784118784) + (b4_0 * 6901746346790563787434755862277025452451108972170386555162524223799296) + (b5_0 * 1989292945639146568621528992587283360401824603189390869761855907572637988050133502132224) + (b6_0 * 573374653997517877902705223825521735199141247292070280934397209846730719022121202017504638277531421638656) + (b7_0 * 165263992197562149737978827008192759957101170741070304821162198818601447809077836456297302609928821211897803006255839576064) + (b8_0 * 47634102635436893179040485073748265163400240214004076398607741693502376385799646303105256699577209032590132615988260237052123652332890095616)) (mod 6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057152 - 1) && and [carry_1 = carry1_1, carry_2 = carry1_2, carry_3 = carry1_3, carry_4 = carry1_4, carry_5 = carry1_5, carry_6 = carry1_6, carry_7 = carry1_7, carry_8 = carry1_8, carry_9 = carry1_9, v4_1 <=u add (a0_0) (170141183460469231141391493357178454016@128), v8_1 <=u add (a1_0) (170141183460469231141391493357178454016@128), v12_1 <=u add (a2_0) (170141183460469231141391493357178454016@128), v16_1 <=u add (a3_0) (170141183460469231141391493357178454016@128), v20_1 <=u add (a4_0) (170141183460469231141391493357178454016@128), v24_1 <=u add (a5_0) (170141183460469231141391493357178454016@128), v28_1 <=u add (a6_0) (170141183460469231141391493357178454016@128), v32_1 <=u add (a7_0) (170141183460469231141391493357178454016@128), v36_1 <=u add (a8_0) (170141183460469231141391493357178454016@128)] }