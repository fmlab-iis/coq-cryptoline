proc main(uint64 mem0_0_0, uint64 mem0_16_0, uint64 mem0_24_0, uint64 mem0_32_0, uint64 mem0_8_0, uint64 mem1_0_0, uint64 mem1_16_0, uint64 mem1_24_0, uint64 mem1_32_0, uint64 mem1_8_0) =
{ true && and [mem0_0_0 <=u 2251799813685247@64, mem0_8_0 <=u 4503599627370494@64, mem0_16_0 <=u 2251799813685247@64, mem0_24_0 <=u 2251799813685247@64, mem0_32_0 <=u 2251799813685247@64, mem1_0_0 <=u 2251799813685247@64, mem1_8_0 <=u 4503599627370494@64, mem1_16_0 <=u 2251799813685247@64, mem1_24_0 <=u 2251799813685247@64, mem1_32_0 <=u 2251799813685247@64] }
add v10_0_1 mem0_0_0 18014398509481832@uint64;
add v10_1_1 mem0_8_0 18014398509481976@uint64;
sub v11_0_1 v10_0_1 mem1_0_0;
sub v11_1_1 v10_1_1 mem1_8_0;
add v13_0_1 mem0_16_0 18014398509481976@uint64;
add v13_1_1 mem0_24_0 18014398509481976@uint64;
sub v14_0_1 v13_0_1 mem1_16_0;
sub v14_1_1 v13_1_1 mem1_24_0;
add v_add20_1 mem0_32_0 18014398509481976@uint64;
sub v_sub21_1 v_add20_1 mem1_32_0;
{ v11_0_1 + (v11_1_1 * 2251799813685248) + (v14_0_1 * 5070602400912917605986812821504) + (v14_1_1 * 11417981541647679048466287755595961091061972992) + (v_sub21_1 * 25711008708143844408671393477458601640355247900524685364822016) = mem0_0_0 + (mem0_8_0 * 2251799813685248) + (mem0_16_0 * 5070602400912917605986812821504) + (mem0_24_0 * 11417981541647679048466287755595961091061972992) + (mem0_32_0 * 25711008708143844408671393477458601640355247900524685364822016) - (mem1_0_0 + (mem1_8_0 * 2251799813685248) + (mem1_16_0 * 5070602400912917605986812821504) + (mem1_24_0 * 11417981541647679048466287755595961091061972992) + (mem1_32_0 * 25711008708143844408671393477458601640355247900524685364822016)) (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [v11_0_1 <=u 20266198323167223@64, v11_1_1 <=u 22517998136852470@64, v14_0_1 <=u 20266198323167223@64, v14_1_1 <=u 20266198323167223@64, v_sub21_1 <=u 20266198323167223@64] }