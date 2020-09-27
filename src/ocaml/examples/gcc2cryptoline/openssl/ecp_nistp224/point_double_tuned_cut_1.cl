proc felem_reduce (uint128 a0, uint128 a1, uint128 a2, uint128 a3, uint128 a4, uint128 a5, uint128 a6;uint64 c0, uint64 c1, uint64 c2, uint64 c3) = 
{
  true
  &&
  and [
    a0 <u (2**126)@128,
    a1 <u (2**126)@128,
    a2 <u (2**126)@128,
    a3 <u (2**126)@128,
    a4 <u (2**126)@128,
    a5 <u (2**126)@128,
    a6 <u (2**126)@128
  ]
}


(* Start with undefined rhs *)
mov in54_0@uint128 a0;
mov in54_16@uint128 a1;
mov in54_32@uint128 a2;
mov in54_48@uint128 a3;
mov in54_64@uint128 a4;
mov in54_80@uint128 a5;
mov in54_96@uint128 a6;
(* End with undefined rhs *)



(* BB's index is 2 *)

(* _1 = *in_54(D); *)
mov v1 in54_0;
(* _2 = _1 + 0x80000000000000000000000000008000; *)
mov value_lo 0x8000@uint64;
mov value_hi 0x8000000000000000@uint64;
join value value_hi value_lo;
uadd v2 v1 value;
(* _3 = MEM[(const widelimb * )in_54(D) + 16B]; *)
mov v3 in54_16;
(* _4 = _3 + 0x7fffffffffffff7fff80000000000000; *)
mov value_lo 0xff80000000000000@uint64;
mov value_hi 0x7fffffffffffff7f@uint64;
join value value_hi value_lo;
uadd v4 v3 value;
(* _5 = MEM[(const widelimb * )in_54(D) + 32B]; *)
mov v5 in54_32;
(* _6 = _5 + 0x7fffffffffffff800000000000000000; *)
mov value_lo 0x0@uint64;
mov value_hi 0x7fffffffffffff80@uint64;
join value value_hi value_lo;
uadd v6 v5 value;
(* _7 = MEM[(const widelimb * )in_54(D) + 48B]; *)
mov v7 in54_48;
(* _8 = MEM[(const widelimb * )in_54(D) + 64B]; *)
mov v8 in54_64;
(* _9 = MEM[(const widelimb * )in_54(D) + 96B]; *)
mov v9 in54_96;
(* _10 = _9 >> 16; *)
usplit v10 tmp_to_use v9 16;
(* _11 = _8 + _10; *)
uadd v11 v8 v10;
(* _12 = _9 << 40; *)
usplit tmp1 tmp2 v9 88;
shl v12 tmp2 40;
(* TODO: check tmp1 heuristic *)
(* assert true && tmp1 = 0@128; *)
(* assume tmp1 = 0 && true; *)
(* _13 = _12 & 72056494526300160; *)
(* Note: high part 0x0@uint64 = 0x00000000000000 *)
(* Note: high part 0x0@uint64 = 0b00000000000000000000000000000000000000000000000000000000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0xffff0000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0b00000011111111111111110000000000000000000000000000000000000000 *)
mov value_lo 0xffff0000000000@uint64;
mov value_hi 0x0@uint64;
join value value_hi value_lo;
and uint128 v13 v12 value;

assert true && v13 = tmp_to_use * (2**40)@128;
assume v13 = tmp_to_use * (2**40) && true;

(* _15 = _6 - _9; *)
usub v15 v6 v9;
(* _16 = MEM[(const widelimb * )in_54(D) + 80B]; *)
mov v16 in54_80;
(* _17 = _16 >> 16; *)
usplit v17 tmp_to_use v16 16;
(* _64 = _7 + _17; *)
uadd v64 v7 v17;
(* _18 = _13 + _64; *)
uadd v18 v13 v64;
(* _19 = _16 << 40; *)
usplit tmp1 tmp2 v16 88;
shl v19 tmp2 40;
(* TODO: check tmp1 heuristic *)
(* assert true && tmp1 = 0@128; *)
(* assume tmp1 = 0 && true; *)
(* _20 = _19 & 72056494526300160; *)
(* Note: high part 0x0@uint64 = 0x00000000000000 *)
(* Note: high part 0x0@uint64 = 0b00000000000000000000000000000000000000000000000000000000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0xffff0000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0b00000011111111111111110000000000000000000000000000000000000000 *)
mov value_lo 0xffff0000000000@uint64;
mov value_hi 0x0@uint64;
join value value_hi value_lo;
and uint128 v20 v19 value;

assert true && v20 = tmp_to_use * (2**40)@128;
assume v20 = tmp_to_use * (2**40) && true;

(* _21 = _15 + _20; *)
uadd v21 v15 v20;
(* _22 = _4 - _16; *)
usub v22 v4 v16;
(* _23 = _11 >> 16; *)
usplit v23 tmp_to_use v11 16;
(* _24 = _21 + _23; *)
uadd v24 v21 v23;
(* _25 = _11 << 40; *)
usplit tmp1 tmp2 v11 88;
shl v25 tmp2 40;
(* TODO: check tmp1 heuristic *)
(* assert true && tmp1 = 0@128; *)
(* assume tmp1 = 0 && true; *)
(* _26 = _25 & 72056494526300160; *)
(* Note: high part 0x0@uint64 = 0x00000000000000 *)
(* Note: high part 0x0@uint64 = 0b00000000000000000000000000000000000000000000000000000000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0xffff0000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0b00000011111111111111110000000000000000000000000000000000000000 *)
mov value_lo 0xffff0000000000@uint64;
mov value_hi 0x0@uint64;
join value value_hi value_lo;
and uint128 v26 v25 value;

assert true && v26 = tmp_to_use * (2**40)@128;
assume v26 = tmp_to_use * (2**40) && true;

(* _27 = _22 + _26; *)
uadd v27 v22 v26;
(* _28 = _2 - _11; *)
usub v28 v2 v11;
(* _29 = _24 >> 56; *)
usplit v29 tmp_to_use v24 56;
(* _30 = _18 + _29; *)
uadd v30 v18 v29;
(* _31 = _24 & 72057594037927935; *)
(* Note: high part 0x0@uint64 = 0x00000000000000 *)
(* Note: high part 0x0@uint64 = 0b00000000000000000000000000000000000000000000000000000000000000 *)
(* Note: low part 0xffffffffffffff@uint64 = 0xffffffffffffff *)
(* Note: low part 0xffffffffffffff@uint64 = 0b00000011111111111111111111111111111111111111111111111111111111 *)
mov value_lo 0xffffffffffffff@uint64;
mov value_hi 0x0@uint64;
join value value_hi value_lo;
and uint128 v31 v24 value;

assert true && v31 = tmp_to_use ;
assume v31 = tmp_to_use &&  true ;

(* _32 = _30 >> 56; *)
usplit v32 tmp_to_use v30 56;
(* _33 = _30 & 72057594037927935; *)
(* Note: high part 0x0@uint64 = 0x00000000000000 *)
(* Note: high part 0x0@uint64 = 0b00000000000000000000000000000000000000000000000000000000000000 *)
(* Note: low part 0xffffffffffffff@uint64 = 0xffffffffffffff *)
(* Note: low part 0xffffffffffffff@uint64 = 0b00000011111111111111111111111111111111111111111111111111111111 *)
mov value_lo 0xffffffffffffff@uint64;
mov value_hi 0x0@uint64;
join value value_hi value_lo;
and uint128 v33 v30 value;

assert true && v33 = tmp_to_use ;
assume v33 = tmp_to_use && true;

(* _34 = _30 >> 72; *)
usplit v34 tmp_to_use v30 72;
(* _35 = _31 + _34; *)
uadd v35 v31 v34;
(* _36 = _32 << 40; *)
usplit tmp1 tmp2 v32 88;
shl v36 tmp2 40;
(* TODO: check tmp1 heuristic *)
(* assert true && tmp1 = 0@128; *)
(* assume tmp1 = 0 && true; *)
(* _37 = _36 & 72056494526300160; *)
(* Note: high part 0x0@uint64 = 0x00000000000000 *)
(* Note: high part 0x0@uint64 = 0b00000000000000000000000000000000000000000000000000000000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0xffff0000000000 *)
(* Note: low part 0xffff0000000000@uint64 = 0b00000011111111111111110000000000000000000000000000000000000000 *)
mov value_lo 0xffff0000000000@uint64;
mov value_hi 0x0@uint64;
join value value_hi value_lo;
and uint128 v37 v36 value;

(* NOTE: the following assertion is required for verifying algebraic specification *)

assert 
    true 
    &&
    (
        v37 
        +
        ((v34 * (2**40)@128) * (2**16)@128)
    )
    =
    (v32 * (2**40)@128);
assume
    (
        v37 
        +
        ((v34 * 2**40) * 2**16)
    )
    =
    (v32 * (2**40))
    &&
    true;


(* _38 = _27 + _37; *)
uadd v38 v27 v37;
(* _39 = _28 - _32; *)
usub v39 v28 v32;
(* _40 = _39 >> 56; *)
usplit v40 tmp_to_use v39 56;
(* _41 = _38 + _40; *)
uadd v41 v38 v40;
(* _42 = (long unsigned int) _39; *)
cast v42@uint64 v39@uint128;
(* _43 = _42 & 72057594037927935; *)
(* Note: 0xffffffffffffff@uint64 = 0xffffffffffffff *)
(* Note: 0xffffffffffffff@uint64 = 0b00000011111111111111111111111111111111111111111111111111111111 *)
and uint64 v43 v42 0xffffffffffffff@uint64;

vpc tmp_to_use_p@uint64 tmp_to_use;
assert true && v43 = tmp_to_use_p ;
assume v43 = tmp_to_use && true;

(* *out_55(D) = _43; *)
mov out55_0 v43;
(* _44 = _41 >> 56; *)
usplit v44 tmp_to_use v41 56;
(* _45 = _35 + _44; *)
uadd v45 v35 v44;
(* _46 = (long unsigned int) _41; *)
cast v46@uint64 v41@uint128;
(* _47 = _46 & 72057594037927935; *)
(* Note: 0xffffffffffffff@uint64 = 0xffffffffffffff *)
(* Note: 0xffffffffffffff@uint64 = 0b00000011111111111111111111111111111111111111111111111111111111 *)
and uint64 v47 v46 0xffffffffffffff@uint64;

vpc tmp_to_use_p@uint64 tmp_to_use;
assert true && v47 = tmp_to_use_p ;
assume v47 = tmp_to_use && true;

(* MEM[(limb * )out_55(D) + 8B] = _47; *)
mov out55_8 v47;
(* _48 = _45 >> 56; *)
usplit v48 tmp_to_use v45 56;
(* _49 = _33 + _48; *)
uadd v49 v33 v48;
(* _50 = (long unsigned int) _45; *)
cast v50@uint64 v45@uint128;
(* _51 = _50 & 72057594037927935; *)
(* Note: 0xffffffffffffff@uint64 = 0xffffffffffffff *)
(* Note: 0xffffffffffffff@uint64 = 0b00000011111111111111111111111111111111111111111111111111111111 *)
and uint64 v51 v50 0xffffffffffffff@uint64;

vpc tmp_to_use_p@uint64 tmp_to_use;
assert true && v51 = tmp_to_use_p;
assume v51 = tmp_to_use && true;

(* MEM[(limb * )out_55(D) + 16B] = _51; *)
mov out55_16 v51;
(* _52 = (long unsigned int) _49; *)
vpc v52@uint64 v49@uint128;
(* MEM[(limb * )out_55(D) + 24B] = _52; *)
mov out55_24 v52;
(* return; *)


(* Start with unused lhs *)
mov c0 out55_0@uint64;
mov c1 out55_8@uint64;
mov c2 out55_16@uint64;
mov c3 out55_24@uint64;
(* End with unsed lhs *)


{
  (limbs 56 [c0, c1 , c2, c3])
  =
  (limbs 56 [a0, a1, a2, a3, a4, a5, a6])
  (mod (2**224 - 2**96 + 1))
  &&
 and 
  [
      c0 <u (2**56)@64,
      c1 <u (2**56)@64,
      c2 <u (2**56)@64,
      c3 <u (2**56 + 2**16)@64
  ]
}

proc main (uint64 x0, uint64 x1, uint64 x2, uint64 x3, uint64 y0, uint64 y1,uint64 y2,uint64 y3,uint64 z0, uint64 z1,uint64 z2, uint64 z3) = 
{
  true
  &&
  and [
    x0 <u (2**58)@64,
    x1 <u (2**58)@64,
    x2 <u (2**58)@64,
    x3 <u (2**58)@64,
    y0 <u (2**58)@64,
    y1 <u (2**58)@64,
    y2 <u (2**58)@64,
    y3 <u (2**58)@64,
    z0 <u (2**58)@64,
    z1 <u (2**58)@64,
    z2 <u (2**58)@64,
    z3 <u (2**58)@64
  ]
}


(* Start with undefined rhs *)
mov x_in2_0@uint64 x0;
mov x_in2_8@uint64 x1;
mov x_in2_16@uint64 x2;
mov x_in2_24@uint64 x3;
mov y_in6_0@uint64 y0;
mov y_in6_8@uint64 y1;
mov y_in6_16@uint64 y2;
mov y_in6_24@uint64 y3;
mov z_in3_0@uint64 z0;
mov z_in3_8@uint64 z1;
mov z_in3_16@uint64 z2;
mov z_in3_24@uint64 z3;
(* End with undefined rhs *)



(* BB's index is 2 *)

(* _162 = *x_in_2(D); *)
mov v162 x_in2_0;
(* _163 = MEM[(const limb * )x_in_2(D) + 8B]; *)
mov v163 x_in2_8;
(* _164 = MEM[(const limb * )x_in_2(D) + 16B]; *)
mov v164 x_in2_16;
(* _165 = MEM[(const limb * )x_in_2(D) + 24B]; *)
mov v165 x_in2_24;
(* _472 = *z_in_3(D); *)
mov v472 z_in3_0;
(* tmp0_473 = _472 * 2; *)
umul tmp0473 v472 0x2@uint64;
(* _474 = MEM[(const limb * )z_in_3(D) + 8B]; *)
mov v474 z_in3_8;
(* tmp1_475 = _474 * 2; *)
umul tmp1475 v474 0x2@uint64;
(* _476 = MEM[(const limb * )z_in_3(D) + 16B]; *)
mov v476 z_in3_16;
(* tmp2_477 = _476 * 2; *)
umul tmp2477 v476 0x2@uint64;
(* _479 = _472 w* _472; *)
umulj v479 v472 v472;
(* MEM[(widelimb * )&tmp] = _479; *)
mov tmp_0 v479;
(* _481 = _472 w* tmp1_475; *)
umulj v481 v472 tmp1475;
(* MEM[(widelimb * )&tmp + 16B] = _481; *)
mov tmp_16 v481;
(* _483 = _472 w* tmp2_477; *)
umulj v483 v472 tmp2477;
(* _485 = _474 w* _474; *)
umulj v485 v474 v474;
(* _486 = _483 + _485; *)
uadd v486 v483 v485;
(* MEM[(widelimb * )&tmp + 32B] = _486; *)
mov tmp_32 v486;
(* _487 = MEM[(const limb * )z_in_3(D) + 24B]; *)
mov v487 z_in3_24;
(* _490 = _487 w* tmp0_473; *)
umulj v490 v487 tmp0473;
(* _491 = tmp2_477 w* _474; *)
umulj v491 tmp2477 v474;
(* _492 = _490 + _491; *)
uadd v492 v490 v491;
(* MEM[(widelimb * )&tmp + 48B] = _492; *)
mov tmp_48 v492;
(* _493 = tmp1_475 w* _487; *)
umulj v493 tmp1475 v487;
(* _495 = _476 w* _476; *)
umulj v495 v476 v476;
(* _496 = _493 + _495; *)
uadd v496 v493 v495;
(* MEM[(widelimb * )&tmp + 64B] = _496; *)
mov tmp_64 v496;
(* _497 = tmp2_477 w* _487; *)
umulj v497 tmp2477 v487;
(* MEM[(widelimb * )&tmp + 80B] = _497; *)
mov tmp_80 v497;
(* _498 = _487 w* _487; *)
umulj v498 v487 v487;
(* MEM[(widelimb * )&tmp + 96B] = _498; *)
mov tmp_96 v498;
(* felem_reduce (&delta, &tmp); *)
(* TODO: skipped, GIMPLE_CALL doesn't use internal or builtin function, inline function or self translte *)
call felem_reduce(tmp_0, tmp_16, tmp_32, tmp_48, tmp_64, tmp_80, tmp_96, delta_0, delta_8, delta_16, delta_24);

mov delta0_0 delta_0;
mov delta0_1 delta_8;
mov delta0_2 delta_16;
mov delta0_3 delta_24;

(* _445 = *y_in_6(D); *)
mov v445 y_in6_0;
(* tmp0_446 = _445 * 2; *)
umul tmp0446 v445 0x2@uint64;
(* _447 = MEM[(const limb * )y_in_6(D) + 8B]; *)
mov v447 y_in6_8;
(* tmp1_448 = _447 * 2; *)
umul tmp1448 v447 0x2@uint64;
(* _449 = MEM[(const limb * )y_in_6(D) + 16B]; *)
mov v449 y_in6_16;
(* tmp2_450 = _449 * 2; *)
umul tmp2450 v449 0x2@uint64;
(* _452 = _445 w* _445; *)
umulj v452 v445 v445;
(* MEM[(widelimb * )&tmp] = _452; *)
mov tmp_0 v452;
(* _454 = _445 w* tmp1_448; *)
umulj v454 v445 tmp1448;
(* MEM[(widelimb * )&tmp + 16B] = _454; *)
mov tmp_16 v454;
(* _456 = _445 w* tmp2_450; *)
umulj v456 v445 tmp2450;
(* _458 = _447 w* _447; *)
umulj v458 v447 v447;
(* _459 = _456 + _458; *)
uadd v459 v456 v458;
(* MEM[(widelimb * )&tmp + 32B] = _459; *)
mov tmp_32 v459;
(* _460 = MEM[(const limb * )y_in_6(D) + 24B]; *)
mov v460 y_in6_24;
(* _463 = _460 w* tmp0_446; *)
umulj v463 v460 tmp0446;
(* _464 = tmp2_450 w* _447; *)
umulj v464 tmp2450 v447;
(* _465 = _463 + _464; *)
uadd v465 v463 v464;
(* MEM[(widelimb * )&tmp + 48B] = _465; *)
mov tmp_48 v465;
(* _466 = tmp1_448 w* _460; *)
umulj v466 tmp1448 v460;
(* _468 = _449 w* _449; *)
umulj v468 v449 v449;
(* _469 = _466 + _468; *)
uadd v469 v466 v468;
(* MEM[(widelimb * )&tmp + 64B] = _469; *)
mov tmp_64 v469;
(* _470 = tmp2_450 w* _460; *)
umulj v470 tmp2450 v460;
(* MEM[(widelimb * )&tmp + 80B] = _470; *)
mov tmp_80 v470;
(* _471 = _460 w* _460; *)
umulj v471 v460 v460;
(* MEM[(widelimb * )&tmp + 96B] = _471; *)
mov tmp_96 v471;
(* felem_reduce (&gamma, &tmp); *)
(* TODO: skipped, GIMPLE_CALL doesn't use internal or builtin function, inline function or self translte *)
call felem_reduce(tmp_0, tmp_16, tmp_32, tmp_48, tmp_64, tmp_80, tmp_96, gamma_0, gamma_8, gamma_16, gamma_24);

mov gamma0_0 gamma_0;
mov gamma0_1 gamma_8;
mov gamma0_2 gamma_16;
mov gamma0_3 gamma_24;

(* _404 = *x_in_2(D); *)
mov v404 x_in2_0;
(* _406 = MEM[(const limb * )&gamma]; *)
mov v406 gamma_0;
(* _408 = _404 w* _406; *)
umulj v408 v404 v406;
(* MEM[(widelimb * )&tmp] = _408; *)
mov tmp_0 v408;
(* _409 = MEM[(const limb * )&gamma + 8B]; *)
mov v409 gamma_8;
(* _411 = _404 w* _409; *)
umulj v411 v404 v409;
(* _412 = MEM[(const limb * )x_in_2(D) + 8B]; *)
mov v412 x_in2_8;
(* _414 = _406 w* _412; *)
umulj v414 v406 v412;
(* _415 = _411 + _414; *)
uadd v415 v411 v414;
(* MEM[(widelimb * )&tmp + 16B] = _415; *)
mov tmp_16 v415;
(* _416 = MEM[(const limb * )&gamma + 16B]; *)
mov v416 gamma_16;
(* _418 = _404 w* _416; *)
umulj v418 v404 v416;
(* _419 = _409 w* _412; *)
umulj v419 v409 v412;
(* _420 = _418 + _419; *)
uadd v420 v418 v419;
(* _421 = MEM[(const limb * )x_in_2(D) + 16B]; *)
mov v421 x_in2_16;
(* _423 = _406 w* _421; *)
umulj v423 v406 v421;
(* _424 = _420 + _423; *)
uadd v424 v420 v423;
(* MEM[(widelimb * )&tmp + 32B] = _424; *)
mov tmp_32 v424;
(* _425 = MEM[(const limb * )&gamma + 24B]; *)
mov v425 gamma_24;
(* _427 = _404 w* _425; *)
umulj v427 v404 v425;
(* _428 = _412 w* _416; *)
umulj v428 v412 v416;
(* _211 = _427 + _428; *)
uadd v211 v427 v428;
(* _430 = MEM[(const limb * )x_in_2(D) + 24B]; *)
mov v430 x_in2_24;
(* _432 = _406 w* _430; *)
umulj v432 v406 v430;
(* _433 = _409 w* _421; *)
umulj v433 v409 v421;
(* _212 = _211 + _432; *)
uadd v212 v211 v432;
(* _435 = _212 + _433; *)
uadd v435 v212 v433;
(* MEM[(widelimb * )&tmp + 48B] = _435; *)
mov tmp_48 v435;
(* _436 = _412 w* _425; *)
umulj v436 v412 v425;
(* _437 = _416 w* _421; *)
umulj v437 v416 v421;
(* _438 = _436 + _437; *)
uadd v438 v436 v437;
(* _439 = _409 w* _430; *)
umulj v439 v409 v430;
(* _440 = _438 + _439; *)
uadd v440 v438 v439;
(* MEM[(widelimb * )&tmp + 64B] = _440; *)
mov tmp_64 v440;
(* _441 = _421 w* _425; *)
umulj v441 v421 v425;
(* _442 = _416 w* _430; *)
umulj v442 v416 v430;
(* _443 = _441 + _442; *)
uadd v443 v441 v442;
(* MEM[(widelimb * )&tmp + 80B] = _443; *)
mov tmp_80 v443;
(* _444 = _425 w* _430; *)
umulj v444 v425 v430;
(* MEM[(widelimb * )&tmp + 96B] = _444; *)
mov tmp_96 v444;
(* felem_reduce (&beta, &tmp); *)
(* TODO: skipped, GIMPLE_CALL doesn't use internal or builtin function, inline function or self translte *)
call felem_reduce(tmp_0, tmp_16, tmp_32, tmp_48, tmp_64, tmp_80, tmp_96, beta_0, beta_8, beta_16, beta_24);

mov beta0_0 beta_0;
mov beta0_1 beta_8;
mov beta0_2 beta_16;
mov beta0_3 beta_24;

(* _154 = MEM[(const limb * )&delta]; *)
mov v154 delta_0;
(* _209 = 288230376151711748 - _154; *)
usub v209 0x400000000000004@uint64 v154;
(* _155 = _162 + _209; *)
uadd v155 v162 v209;
(* _156 = MEM[(const limb * )&delta + 8B]; *)
mov v156 delta_8;
(* _208 = 288225978105200636 - _156; *)
usub v208 0x3fffbfffffffffc@uint64 v156;
(* _157 = _163 + _208; *)
uadd v157 v163 v208;
(* _158 = MEM[(const limb * )&delta + 16B]; *)
mov v158 delta_16;
(* _207 = 288230376151711740 - _158; *)
usub v207 0x3fffffffffffffc@uint64 v158;
(* _159 = _164 + _207; *)
uadd v159 v164 v207;
(* _160 = MEM[(const limb * )&delta + 24B]; *)
mov v160 delta_24;
(* _206 = 288230376151711740 - _160; *)
usub v206 0x3fffffffffffffc@uint64 v160;
(* _161 = _165 + _206; *)
uadd v161 v165 v206;
(* _139 = _154 + _162; *)
uadd v139 v154 v162;
(* _141 = _156 + _163; *)
uadd v141 v156 v163;
(* _143 = _158 + _164; *)
uadd v143 v158 v164;
(* _145 = _160 + _165; *)
uadd v145 v160 v165;
(* _134 = _139 * 3; *)
umul v134 v139 0x3@uint64;
(* _135 = _141 * 3; *)
umul v135 v141 0x3@uint64;
(* _136 = _143 * 3; *)
umul v136 v143 0x3@uint64;
(* _137 = _145 * 3; *)
umul v137 v145 0x3@uint64;
(* _367 = _155 w* _134; *)
umulj v367 v155 v134;
(* MEM[(widelimb * )&tmp] = _367; *)
mov tmp_0 v367;
(* _370 = _155 w* _135; *)
umulj v370 v155 v135;
(* _373 = _134 w* _157; *)
umulj v373 v134 v157;
(* _374 = _370 + _373; *)
uadd v374 v370 v373;
(* MEM[(widelimb * )&tmp + 16B] = _374; *)
mov tmp_16 v374;
(* _377 = _155 w* _136; *)
umulj v377 v155 v136;
(* _378 = _135 w* _157; *)
umulj v378 v135 v157;
(* _379 = _377 + _378; *)
uadd v379 v377 v378;
(* _382 = _134 w* _159; *)
umulj v382 v134 v159;
(* _383 = _379 + _382; *)
uadd v383 v379 v382;
(* MEM[(widelimb * )&tmp + 32B] = _383; *)
mov tmp_32 v383;
(* _386 = _155 w* _137; *)
umulj v386 v155 v137;
(* _387 = _157 w* _136; *)
umulj v387 v157 v136;
(* _553 = _386 + _387; *)
uadd v553 v386 v387;
(* _391 = _134 w* _161; *)
umulj v391 v134 v161;
(* _392 = _135 w* _159; *)
umulj v392 v135 v159;
(* _554 = _391 + _553; *)
uadd v554 v391 v553;
(* _394 = _392 + _554; *)
uadd v394 v392 v554;
(* MEM[(widelimb * )&tmp + 48B] = _394; *)
mov tmp_48 v394;
(* _395 = _157 w* _137; *)
umulj v395 v157 v137;
(* _396 = _136 w* _159; *)
umulj v396 v136 v159;
(* _397 = _395 + _396; *)
uadd v397 v395 v396;
(* _398 = _135 w* _161; *)
umulj v398 v135 v161;
(* _399 = _397 + _398; *)
uadd v399 v397 v398;
(* MEM[(widelimb * )&tmp + 64B] = _399; *)
mov tmp_64 v399;
(* _400 = _159 w* _137; *)
umulj v400 v159 v137;
(* _401 = _136 w* _161; *)
umulj v401 v136 v161;
(* _402 = _400 + _401; *)
uadd v402 v400 v401;
(* MEM[(widelimb * )&tmp + 80B] = _402; *)
mov tmp_80 v402;
(* _403 = _137 w* _161; *)
umulj v403 v137 v161;
(* MEM[(widelimb * )&tmp + 96B] = _403; *)
mov tmp_96 v403;
(* felem_reduce (&alpha, &tmp); *)
(* TODO: skipped, GIMPLE_CALL doesn't use internal or builtin function, inline function or self translte *)
call felem_reduce(tmp_0, tmp_16, tmp_32, tmp_48, tmp_64, tmp_80, tmp_96, alpha_0, alpha_8, alpha_16, alpha_24);

mov alpha0_0 alpha_0;
mov alpha0_1 alpha_8;
mov alpha0_2 alpha_16;
mov alpha0_3 alpha_24;

{
  and [
    (* delta = z^2 *)
    (limbs 56 [delta0_0, delta0_1, delta0_2, delta0_3])
    =
    ((limbs 56 [z0, z1, z2, z3]) ** 2)
    (mod (2**224 - 2**96 + 1))
    ,
    (* gamma = y^2 *)
    (limbs 56 [gamma0_0, gamma0_1, gamma0_2, gamma0_3])
    =
    ((limbs 56 [y0, y1, y2, y3]) ** 2)
    (mod (2**224 - 2**96 + 1))
    ,
    (* beta = x * gamma *)
    (limbs 56 [beta0_0, beta0_1, beta0_2, beta0_3])
    =
    ((limbs 56 [x0, x1, x2, x3]) * (limbs 56 [gamma0_0, gamma0_1, gamma0_2, gamma0_3]))
    (mod (2**224 - 2**96 + 1))
    ,
    (* alpha = 3 * (x - delta) * (x + delta) *)
    (limbs 56 [alpha0_0, alpha0_1, alpha0_2, alpha0_3])
    =
    (
      3 *
      ((limbs 56 [x0, x1, x2, x3]) - (limbs 56 [delta0_0, delta0_1, delta0_2, delta0_3])) *
      ((limbs 56 [x0, x1, x2, x3]) + (limbs 56 [delta0_0, delta0_1, delta0_2, delta0_3]))
    )
    (mod (2**224 - 2**96 + 1))
  ]
  &&
  true
}

