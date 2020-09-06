(* @frege
===== Verification =====
Prefix: OCAMLRUNPARAM=s=32G
Options: -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .
Command: OCAMLRUNPARAM=s=32G ./coqcryptoline.exe -v -jobs 16 -fork -cadical /home/mht208/Sources/cadical/cadical-rel-1.3.0/build/cadical  -sat_cert grat  -gratchk /home/mht208/Sources/grat/gratchk/code/gratchk  -gratgen /home/mht208/Sources/grat/gratgen/gratgen  -no_carry_constraint -tmpdir .  Hacl_Curve25519_51_basic_fsub0_tuned.cl

Results of checking CNF formulas:       [OK]            0.702746 seconds
Finding polynomial coefficients         [OK]            0.068287 seconds
Verification result:                    [OK]            0.835735 seconds
*)

proc main(uint64 mem0_0_0, uint64 mem0_16_0, uint64 mem0_24_0, uint64 mem0_32_0, uint64 mem0_8_0, uint64 mem1_0_0, uint64 mem1_16_0, uint64 mem1_24_0, uint64 mem1_32_0, uint64 mem1_8_0) =
{ true && and [mem0_0_0 <=u 2251799813685247@64, mem0_8_0 <=u 4503599627370494@64, mem0_16_0 <=u 2251799813685247@64, mem0_24_0 <=u 2251799813685247@64, mem0_32_0 <=u 2251799813685247@64, mem1_0_0 <=u 2251799813685247@64, mem1_8_0 <=u 4503599627370494@64, mem1_16_0 <=u 2251799813685247@64, mem1_24_0 <=u 2251799813685247@64, mem1_32_0 <=u 2251799813685247@64] }
mov v1_0_1 mem0_0_0;
mov v1_1_1 mem0_8_0;
mov v3_0_1 mem1_0_0;
mov v3_1_1 mem1_8_0;
mov v5_0_1 mem0_16_0;
mov v5_1_1 mem0_24_0;
mov v7_0_1 mem1_16_0;
mov v7_1_1 mem1_24_0;
mov v8_1 mem0_32_0;
mov v9_1 mem1_32_0;
add v10_0_1 v1_0_1 18014398509481832@uint64;
add v10_1_1 v1_1_1 18014398509481976@uint64;
sub v11_0_1 v10_0_1 v3_0_1;
sub v11_1_1 v10_1_1 v3_1_1;
mov mem2_0_1 v11_0_1;
mov mem2_8_1 v11_1_1;
add v13_0_1 v5_0_1 18014398509481976@uint64;
add v13_1_1 v5_1_1 18014398509481976@uint64;
sub v14_0_1 v13_0_1 v7_0_1;
sub v14_1_1 v13_1_1 v7_1_1;
mov mem2_16_1 v14_0_1;
mov mem2_24_1 v14_1_1;
add v_add20_1 v8_1 18014398509481976@uint64;
sub v_sub21_1 v_add20_1 v9_1;
mov mem2_32_1 v_sub21_1;
{ mem2_0_1 + (mem2_8_1 * 2251799813685248) + (mem2_16_1 * 5070602400912917605986812821504) + (mem2_24_1 * 11417981541647679048466287755595961091061972992) + (mem2_32_1 * 25711008708143844408671393477458601640355247900524685364822016) = mem0_0_0 + (mem0_8_0 * 2251799813685248) + (mem0_16_0 * 5070602400912917605986812821504) + (mem0_24_0 * 11417981541647679048466287755595961091061972992) + (mem0_32_0 * 25711008708143844408671393477458601640355247900524685364822016) - (mem1_0_0 + (mem1_8_0 * 2251799813685248) + (mem1_16_0 * 5070602400912917605986812821504) + (mem1_24_0 * 11417981541647679048466287755595961091061972992) + (mem1_32_0 * 25711008708143844408671393477458601640355247900524685364822016)) (mod 57896044618658097711785492504343953926634992332820282019728792003956564819968 - 19) && and [mem2_0_1 <=u 20266198323167223@64, mem2_8_1 <=u 22517998136852470@64, mem2_16_1 <=u 20266198323167223@64, mem2_24_1 <=u 20266198323167223@64, mem2_32_1 <=u 20266198323167223@64] }
