(*
@szu
Command : OCAMLRUNPARAM=s=100G _build/default/coqcryptoline.exe -v -jobs 20 -sat_solver cadical -sat_cert grat -no_carry_constraint -tmpdir . ntt_PQCLEAN_KYBER512_CLEAN_ntt_k1_ugly.cl

Results of checking CNF formulas:       [OK]		2074.180622 seconds
Verification result:                    [OK]            149858.432068 seconds
*)

proc PQCLEAN_KYBER512_CLEAN_montgomery_reduce (sint32 v_a, sint16 ret) =
{ true
  && and [ (-3329)@32 * (2**15)@32 <=s v_a, v_a <s 3329@32 * (2**15)@32 ]
}

assume eqmod (ret * (2**16)) v_a 3329
    && and [ (-3329)@16 <s ret, ret <s 3329@16 ];

{ true && true }

proc main (  sint16 a_0,   sint16 a_2,   sint16 a_4,   sint16 a_6,
             sint16 a_8,  sint16 a_10,  sint16 a_12,  sint16 a_14,
            sint16 a_16,  sint16 a_18,  sint16 a_20,  sint16 a_22,
            sint16 a_24,  sint16 a_26,  sint16 a_28,  sint16 a_30,
            sint16 a_32,  sint16 a_34,  sint16 a_36,  sint16 a_38,
            sint16 a_40,  sint16 a_42,  sint16 a_44,  sint16 a_46,
            sint16 a_48,  sint16 a_50,  sint16 a_52,  sint16 a_54,
            sint16 a_56,  sint16 a_58,  sint16 a_60,  sint16 a_62,
            sint16 a_64,  sint16 a_66,  sint16 a_68,  sint16 a_70,
            sint16 a_72,  sint16 a_74,  sint16 a_76,  sint16 a_78,
            sint16 a_80,  sint16 a_82,  sint16 a_84,  sint16 a_86,
            sint16 a_88,  sint16 a_90,  sint16 a_92,  sint16 a_94,
            sint16 a_96,  sint16 a_98, sint16 a_100, sint16 a_102,
           sint16 a_104, sint16 a_106, sint16 a_108, sint16 a_110,
           sint16 a_112, sint16 a_114, sint16 a_116, sint16 a_118,
           sint16 a_120, sint16 a_122, sint16 a_124, sint16 a_126,
           sint16 a_128, sint16 a_130, sint16 a_132, sint16 a_134,
           sint16 a_136, sint16 a_138, sint16 a_140, sint16 a_142,
           sint16 a_144, sint16 a_146, sint16 a_148, sint16 a_150,
           sint16 a_152, sint16 a_154, sint16 a_156, sint16 a_158,
           sint16 a_160, sint16 a_162, sint16 a_164, sint16 a_166,
           sint16 a_168, sint16 a_170, sint16 a_172, sint16 a_174,
           sint16 a_176, sint16 a_178, sint16 a_180, sint16 a_182,
           sint16 a_184, sint16 a_186, sint16 a_188, sint16 a_190,
           sint16 a_192, sint16 a_194, sint16 a_196, sint16 a_198,
           sint16 a_200, sint16 a_202, sint16 a_204, sint16 a_206,
           sint16 a_208, sint16 a_210, sint16 a_212, sint16 a_214,
           sint16 a_216, sint16 a_218, sint16 a_220, sint16 a_222,
           sint16 a_224, sint16 a_226, sint16 a_228, sint16 a_230,
           sint16 a_232, sint16 a_234, sint16 a_236, sint16 a_238,
           sint16 a_240, sint16 a_242, sint16 a_244, sint16 a_246,
           sint16 a_248, sint16 a_250, sint16 a_252, sint16 a_254,
           sint16 a_256, sint16 a_258, sint16 a_260, sint16 a_262,
           sint16 a_264, sint16 a_266, sint16 a_268, sint16 a_270,
           sint16 a_272, sint16 a_274, sint16 a_276, sint16 a_278,
           sint16 a_280, sint16 a_282, sint16 a_284, sint16 a_286,
           sint16 a_288, sint16 a_290, sint16 a_292, sint16 a_294,
           sint16 a_296, sint16 a_298, sint16 a_300, sint16 a_302,
           sint16 a_304, sint16 a_306, sint16 a_308, sint16 a_310,
           sint16 a_312, sint16 a_314, sint16 a_316, sint16 a_318,
           sint16 a_320, sint16 a_322, sint16 a_324, sint16 a_326,
           sint16 a_328, sint16 a_330, sint16 a_332, sint16 a_334,
           sint16 a_336, sint16 a_338, sint16 a_340, sint16 a_342,
           sint16 a_344, sint16 a_346, sint16 a_348, sint16 a_350,
           sint16 a_352, sint16 a_354, sint16 a_356, sint16 a_358,
           sint16 a_360, sint16 a_362, sint16 a_364, sint16 a_366,
           sint16 a_368, sint16 a_370, sint16 a_372, sint16 a_374,
           sint16 a_376, sint16 a_378, sint16 a_380, sint16 a_382,
           sint16 a_384, sint16 a_386, sint16 a_388, sint16 a_390,
           sint16 a_392, sint16 a_394, sint16 a_396, sint16 a_398,
           sint16 a_400, sint16 a_402, sint16 a_404, sint16 a_406,
           sint16 a_408, sint16 a_410, sint16 a_412, sint16 a_414,
           sint16 a_416, sint16 a_418, sint16 a_420, sint16 a_422,
           sint16 a_424, sint16 a_426, sint16 a_428, sint16 a_430,
           sint16 a_432, sint16 a_434, sint16 a_436, sint16 a_438,
           sint16 a_440, sint16 a_442, sint16 a_444, sint16 a_446,
           sint16 a_448, sint16 a_450, sint16 a_452, sint16 a_454,
           sint16 a_456, sint16 a_458, sint16 a_460, sint16 a_462,
           sint16 a_464, sint16 a_466, sint16 a_468, sint16 a_470,
           sint16 a_472, sint16 a_474, sint16 a_476, sint16 a_478,
           sint16 a_480, sint16 a_482, sint16 a_484, sint16 a_486,
           sint16 a_488, sint16 a_490, sint16 a_492, sint16 a_494,
           sint16 a_496, sint16 a_498, sint16 a_500, sint16 a_502,
           sint16 a_504, sint16 a_506, sint16 a_508, sint16 a_510) =
{
  true
&&
   and [
(-3329)@16 <s   a_0,   a_0 <s 3329@16, (-3329)@16 <s   a_2,   a_2 <s 3329@16, 
(-3329)@16 <s   a_4,   a_4 <s 3329@16, (-3329)@16 <s   a_6,   a_6 <s 3329@16, 
(-3329)@16 <s   a_8,   a_8 <s 3329@16, (-3329)@16 <s  a_10,  a_10 <s 3329@16, 
(-3329)@16 <s  a_12,  a_12 <s 3329@16, (-3329)@16 <s  a_14,  a_14 <s 3329@16, 
(-3329)@16 <s  a_16,  a_16 <s 3329@16, (-3329)@16 <s  a_18,  a_18 <s 3329@16, 
(-3329)@16 <s  a_20,  a_20 <s 3329@16, (-3329)@16 <s  a_22,  a_22 <s 3329@16, 
(-3329)@16 <s  a_24,  a_24 <s 3329@16, (-3329)@16 <s  a_26,  a_26 <s 3329@16, 
(-3329)@16 <s  a_28,  a_28 <s 3329@16, (-3329)@16 <s  a_30,  a_30 <s 3329@16, 
(-3329)@16 <s  a_32,  a_32 <s 3329@16, (-3329)@16 <s  a_34,  a_34 <s 3329@16, 
(-3329)@16 <s  a_36,  a_36 <s 3329@16, (-3329)@16 <s  a_38,  a_38 <s 3329@16, 
(-3329)@16 <s  a_40,  a_40 <s 3329@16, (-3329)@16 <s  a_42,  a_42 <s 3329@16, 
(-3329)@16 <s  a_44,  a_44 <s 3329@16, (-3329)@16 <s  a_46,  a_46 <s 3329@16, 
(-3329)@16 <s  a_48,  a_48 <s 3329@16, (-3329)@16 <s  a_50,  a_50 <s 3329@16, 
(-3329)@16 <s  a_52,  a_52 <s 3329@16, (-3329)@16 <s  a_54,  a_54 <s 3329@16, 
(-3329)@16 <s  a_56,  a_56 <s 3329@16, (-3329)@16 <s  a_58,  a_58 <s 3329@16, 
(-3329)@16 <s  a_60,  a_60 <s 3329@16, (-3329)@16 <s  a_62,  a_62 <s 3329@16, 
(-3329)@16 <s  a_64,  a_64 <s 3329@16, (-3329)@16 <s  a_66,  a_66 <s 3329@16, 
(-3329)@16 <s  a_68,  a_68 <s 3329@16, (-3329)@16 <s  a_70,  a_70 <s 3329@16, 
(-3329)@16 <s  a_72,  a_72 <s 3329@16, (-3329)@16 <s  a_74,  a_74 <s 3329@16, 
(-3329)@16 <s  a_76,  a_76 <s 3329@16, (-3329)@16 <s  a_78,  a_78 <s 3329@16, 
(-3329)@16 <s  a_80,  a_80 <s 3329@16, (-3329)@16 <s  a_82,  a_82 <s 3329@16, 
(-3329)@16 <s  a_84,  a_84 <s 3329@16, (-3329)@16 <s  a_86,  a_86 <s 3329@16, 
(-3329)@16 <s  a_88,  a_88 <s 3329@16, (-3329)@16 <s  a_90,  a_90 <s 3329@16, 
(-3329)@16 <s  a_92,  a_92 <s 3329@16, (-3329)@16 <s  a_94,  a_94 <s 3329@16, 
(-3329)@16 <s  a_96,  a_96 <s 3329@16, (-3329)@16 <s  a_98,  a_98 <s 3329@16, 
(-3329)@16 <s a_100, a_100 <s 3329@16, (-3329)@16 <s a_102, a_102 <s 3329@16, 
(-3329)@16 <s a_104, a_104 <s 3329@16, (-3329)@16 <s a_106, a_106 <s 3329@16, 
(-3329)@16 <s a_108, a_108 <s 3329@16, (-3329)@16 <s a_110, a_110 <s 3329@16, 
(-3329)@16 <s a_112, a_112 <s 3329@16, (-3329)@16 <s a_114, a_114 <s 3329@16, 
(-3329)@16 <s a_116, a_116 <s 3329@16, (-3329)@16 <s a_118, a_118 <s 3329@16, 
(-3329)@16 <s a_120, a_120 <s 3329@16, (-3329)@16 <s a_122, a_122 <s 3329@16, 
(-3329)@16 <s a_124, a_124 <s 3329@16, (-3329)@16 <s a_126, a_126 <s 3329@16, 
(-3329)@16 <s a_128, a_128 <s 3329@16, (-3329)@16 <s a_130, a_130 <s 3329@16, 
(-3329)@16 <s a_132, a_132 <s 3329@16, (-3329)@16 <s a_134, a_134 <s 3329@16, 
(-3329)@16 <s a_136, a_136 <s 3329@16, (-3329)@16 <s a_138, a_138 <s 3329@16, 
(-3329)@16 <s a_140, a_140 <s 3329@16, (-3329)@16 <s a_142, a_142 <s 3329@16, 
(-3329)@16 <s a_144, a_144 <s 3329@16, (-3329)@16 <s a_146, a_146 <s 3329@16, 
(-3329)@16 <s a_148, a_148 <s 3329@16, (-3329)@16 <s a_150, a_150 <s 3329@16, 
(-3329)@16 <s a_152, a_152 <s 3329@16, (-3329)@16 <s a_154, a_154 <s 3329@16, 
(-3329)@16 <s a_156, a_156 <s 3329@16, (-3329)@16 <s a_158, a_158 <s 3329@16, 
(-3329)@16 <s a_160, a_160 <s 3329@16, (-3329)@16 <s a_162, a_162 <s 3329@16, 
(-3329)@16 <s a_164, a_164 <s 3329@16, (-3329)@16 <s a_166, a_166 <s 3329@16, 
(-3329)@16 <s a_168, a_168 <s 3329@16, (-3329)@16 <s a_170, a_170 <s 3329@16, 
(-3329)@16 <s a_172, a_172 <s 3329@16, (-3329)@16 <s a_174, a_174 <s 3329@16, 
(-3329)@16 <s a_176, a_176 <s 3329@16, (-3329)@16 <s a_178, a_178 <s 3329@16, 
(-3329)@16 <s a_180, a_180 <s 3329@16, (-3329)@16 <s a_182, a_182 <s 3329@16, 
(-3329)@16 <s a_184, a_184 <s 3329@16, (-3329)@16 <s a_186, a_186 <s 3329@16, 
(-3329)@16 <s a_188, a_188 <s 3329@16, (-3329)@16 <s a_190, a_190 <s 3329@16, 
(-3329)@16 <s a_192, a_192 <s 3329@16, (-3329)@16 <s a_194, a_194 <s 3329@16, 
(-3329)@16 <s a_196, a_196 <s 3329@16, (-3329)@16 <s a_198, a_198 <s 3329@16, 
(-3329)@16 <s a_200, a_200 <s 3329@16, (-3329)@16 <s a_202, a_202 <s 3329@16, 
(-3329)@16 <s a_204, a_204 <s 3329@16, (-3329)@16 <s a_206, a_206 <s 3329@16, 
(-3329)@16 <s a_208, a_208 <s 3329@16, (-3329)@16 <s a_210, a_210 <s 3329@16, 
(-3329)@16 <s a_212, a_212 <s 3329@16, (-3329)@16 <s a_214, a_214 <s 3329@16, 
(-3329)@16 <s a_216, a_216 <s 3329@16, (-3329)@16 <s a_218, a_218 <s 3329@16, 
(-3329)@16 <s a_220, a_220 <s 3329@16, (-3329)@16 <s a_222, a_222 <s 3329@16, 
(-3329)@16 <s a_224, a_224 <s 3329@16, (-3329)@16 <s a_226, a_226 <s 3329@16, 
(-3329)@16 <s a_228, a_228 <s 3329@16, (-3329)@16 <s a_230, a_230 <s 3329@16, 
(-3329)@16 <s a_232, a_232 <s 3329@16, (-3329)@16 <s a_234, a_234 <s 3329@16, 
(-3329)@16 <s a_236, a_236 <s 3329@16, (-3329)@16 <s a_238, a_238 <s 3329@16, 
(-3329)@16 <s a_240, a_240 <s 3329@16, (-3329)@16 <s a_242, a_242 <s 3329@16, 
(-3329)@16 <s a_244, a_244 <s 3329@16, (-3329)@16 <s a_246, a_246 <s 3329@16, 
(-3329)@16 <s a_248, a_248 <s 3329@16, (-3329)@16 <s a_250, a_250 <s 3329@16, 
(-3329)@16 <s a_252, a_252 <s 3329@16, (-3329)@16 <s a_254, a_254 <s 3329@16, 
(-3329)@16 <s a_256, a_256 <s 3329@16, (-3329)@16 <s a_258, a_258 <s 3329@16, 
(-3329)@16 <s a_260, a_260 <s 3329@16, (-3329)@16 <s a_262, a_262 <s 3329@16, 
(-3329)@16 <s a_264, a_264 <s 3329@16, (-3329)@16 <s a_266, a_266 <s 3329@16, 
(-3329)@16 <s a_268, a_268 <s 3329@16, (-3329)@16 <s a_270, a_270 <s 3329@16, 
(-3329)@16 <s a_272, a_272 <s 3329@16, (-3329)@16 <s a_274, a_274 <s 3329@16, 
(-3329)@16 <s a_276, a_276 <s 3329@16, (-3329)@16 <s a_278, a_278 <s 3329@16, 
(-3329)@16 <s a_280, a_280 <s 3329@16, (-3329)@16 <s a_282, a_282 <s 3329@16, 
(-3329)@16 <s a_284, a_284 <s 3329@16, (-3329)@16 <s a_286, a_286 <s 3329@16, 
(-3329)@16 <s a_288, a_288 <s 3329@16, (-3329)@16 <s a_290, a_290 <s 3329@16, 
(-3329)@16 <s a_292, a_292 <s 3329@16, (-3329)@16 <s a_294, a_294 <s 3329@16, 
(-3329)@16 <s a_296, a_296 <s 3329@16, (-3329)@16 <s a_298, a_298 <s 3329@16, 
(-3329)@16 <s a_300, a_300 <s 3329@16, (-3329)@16 <s a_302, a_302 <s 3329@16, 
(-3329)@16 <s a_304, a_304 <s 3329@16, (-3329)@16 <s a_306, a_306 <s 3329@16, 
(-3329)@16 <s a_308, a_308 <s 3329@16, (-3329)@16 <s a_310, a_310 <s 3329@16, 
(-3329)@16 <s a_312, a_312 <s 3329@16, (-3329)@16 <s a_314, a_314 <s 3329@16, 
(-3329)@16 <s a_316, a_316 <s 3329@16, (-3329)@16 <s a_318, a_318 <s 3329@16, 
(-3329)@16 <s a_320, a_320 <s 3329@16, (-3329)@16 <s a_322, a_322 <s 3329@16, 
(-3329)@16 <s a_324, a_324 <s 3329@16, (-3329)@16 <s a_326, a_326 <s 3329@16, 
(-3329)@16 <s a_328, a_328 <s 3329@16, (-3329)@16 <s a_330, a_330 <s 3329@16, 
(-3329)@16 <s a_332, a_332 <s 3329@16, (-3329)@16 <s a_334, a_334 <s 3329@16, 
(-3329)@16 <s a_336, a_336 <s 3329@16, (-3329)@16 <s a_338, a_338 <s 3329@16, 
(-3329)@16 <s a_340, a_340 <s 3329@16, (-3329)@16 <s a_342, a_342 <s 3329@16, 
(-3329)@16 <s a_344, a_344 <s 3329@16, (-3329)@16 <s a_346, a_346 <s 3329@16, 
(-3329)@16 <s a_348, a_348 <s 3329@16, (-3329)@16 <s a_350, a_350 <s 3329@16, 
(-3329)@16 <s a_352, a_352 <s 3329@16, (-3329)@16 <s a_354, a_354 <s 3329@16, 
(-3329)@16 <s a_356, a_356 <s 3329@16, (-3329)@16 <s a_358, a_358 <s 3329@16, 
(-3329)@16 <s a_360, a_360 <s 3329@16, (-3329)@16 <s a_362, a_362 <s 3329@16, 
(-3329)@16 <s a_364, a_364 <s 3329@16, (-3329)@16 <s a_366, a_366 <s 3329@16, 
(-3329)@16 <s a_368, a_368 <s 3329@16, (-3329)@16 <s a_370, a_370 <s 3329@16, 
(-3329)@16 <s a_372, a_372 <s 3329@16, (-3329)@16 <s a_374, a_374 <s 3329@16, 
(-3329)@16 <s a_376, a_376 <s 3329@16, (-3329)@16 <s a_378, a_378 <s 3329@16, 
(-3329)@16 <s a_380, a_380 <s 3329@16, (-3329)@16 <s a_382, a_382 <s 3329@16, 
(-3329)@16 <s a_384, a_384 <s 3329@16, (-3329)@16 <s a_386, a_386 <s 3329@16, 
(-3329)@16 <s a_388, a_388 <s 3329@16, (-3329)@16 <s a_390, a_390 <s 3329@16, 
(-3329)@16 <s a_392, a_392 <s 3329@16, (-3329)@16 <s a_394, a_394 <s 3329@16, 
(-3329)@16 <s a_396, a_396 <s 3329@16, (-3329)@16 <s a_398, a_398 <s 3329@16, 
(-3329)@16 <s a_400, a_400 <s 3329@16, (-3329)@16 <s a_402, a_402 <s 3329@16, 
(-3329)@16 <s a_404, a_404 <s 3329@16, (-3329)@16 <s a_406, a_406 <s 3329@16, 
(-3329)@16 <s a_408, a_408 <s 3329@16, (-3329)@16 <s a_410, a_410 <s 3329@16, 
(-3329)@16 <s a_412, a_412 <s 3329@16, (-3329)@16 <s a_414, a_414 <s 3329@16, 
(-3329)@16 <s a_416, a_416 <s 3329@16, (-3329)@16 <s a_418, a_418 <s 3329@16, 
(-3329)@16 <s a_420, a_420 <s 3329@16, (-3329)@16 <s a_422, a_422 <s 3329@16, 
(-3329)@16 <s a_424, a_424 <s 3329@16, (-3329)@16 <s a_426, a_426 <s 3329@16, 
(-3329)@16 <s a_428, a_428 <s 3329@16, (-3329)@16 <s a_430, a_430 <s 3329@16, 
(-3329)@16 <s a_432, a_432 <s 3329@16, (-3329)@16 <s a_434, a_434 <s 3329@16, 
(-3329)@16 <s a_436, a_436 <s 3329@16, (-3329)@16 <s a_438, a_438 <s 3329@16, 
(-3329)@16 <s a_440, a_440 <s 3329@16, (-3329)@16 <s a_442, a_442 <s 3329@16, 
(-3329)@16 <s a_444, a_444 <s 3329@16, (-3329)@16 <s a_446, a_446 <s 3329@16, 
(-3329)@16 <s a_448, a_448 <s 3329@16, (-3329)@16 <s a_450, a_450 <s 3329@16, 
(-3329)@16 <s a_452, a_452 <s 3329@16, (-3329)@16 <s a_454, a_454 <s 3329@16, 
(-3329)@16 <s a_456, a_456 <s 3329@16, (-3329)@16 <s a_458, a_458 <s 3329@16, 
(-3329)@16 <s a_460, a_460 <s 3329@16, (-3329)@16 <s a_462, a_462 <s 3329@16, 
(-3329)@16 <s a_464, a_464 <s 3329@16, (-3329)@16 <s a_466, a_466 <s 3329@16, 
(-3329)@16 <s a_468, a_468 <s 3329@16, (-3329)@16 <s a_470, a_470 <s 3329@16, 
(-3329)@16 <s a_472, a_472 <s 3329@16, (-3329)@16 <s a_474, a_474 <s 3329@16, 
(-3329)@16 <s a_476, a_476 <s 3329@16, (-3329)@16 <s a_478, a_478 <s 3329@16, 
(-3329)@16 <s a_480, a_480 <s 3329@16, (-3329)@16 <s a_482, a_482 <s 3329@16, 
(-3329)@16 <s a_484, a_484 <s 3329@16, (-3329)@16 <s a_486, a_486 <s 3329@16, 
(-3329)@16 <s a_488, a_488 <s 3329@16, (-3329)@16 <s a_490, a_490 <s 3329@16, 
(-3329)@16 <s a_492, a_492 <s 3329@16, (-3329)@16 <s a_494, a_494 <s 3329@16, 
(-3329)@16 <s a_496, a_496 <s 3329@16, (-3329)@16 <s a_498, a_498 <s 3329@16, 
(-3329)@16 <s a_500, a_500 <s 3329@16, (-3329)@16 <s a_502, a_502 <s 3329@16, 
(-3329)@16 <s a_504, a_504 <s 3329@16, (-3329)@16 <s a_506, a_506 <s 3329@16, 
(-3329)@16 <s a_508, a_508 <s 3329@16, (-3329)@16 <s a_510, a_510 <s 3329@16]

}

mov mem0_0 a_0; mov mem0_2 a_2; mov mem0_4 a_4; 
mov mem0_6 a_6; mov mem0_8 a_8; mov mem0_10 a_10; 
mov mem0_12 a_12; mov mem0_14 a_14; mov mem0_16 a_16; 
mov mem0_18 a_18; mov mem0_20 a_20; mov mem0_22 a_22; 
mov mem0_24 a_24; mov mem0_26 a_26; mov mem0_28 a_28; 
mov mem0_30 a_30; mov mem0_32 a_32; mov mem0_34 a_34; 
mov mem0_36 a_36; mov mem0_38 a_38; mov mem0_40 a_40; 
mov mem0_42 a_42; mov mem0_44 a_44; mov mem0_46 a_46; 
mov mem0_48 a_48; mov mem0_50 a_50; mov mem0_52 a_52; 
mov mem0_54 a_54; mov mem0_56 a_56; mov mem0_58 a_58; 
mov mem0_60 a_60; mov mem0_62 a_62; mov mem0_64 a_64; 
mov mem0_66 a_66; mov mem0_68 a_68; mov mem0_70 a_70; 
mov mem0_72 a_72; mov mem0_74 a_74; mov mem0_76 a_76; 
mov mem0_78 a_78; mov mem0_80 a_80; mov mem0_82 a_82; 
mov mem0_84 a_84; mov mem0_86 a_86; mov mem0_88 a_88; 
mov mem0_90 a_90; mov mem0_92 a_92; mov mem0_94 a_94; 
mov mem0_96 a_96; mov mem0_98 a_98; mov mem0_100 a_100; 
mov mem0_102 a_102; mov mem0_104 a_104; mov mem0_106 a_106; 
mov mem0_108 a_108; mov mem0_110 a_110; mov mem0_112 a_112; 
mov mem0_114 a_114; mov mem0_116 a_116; mov mem0_118 a_118; 
mov mem0_120 a_120; mov mem0_122 a_122; mov mem0_124 a_124; 
mov mem0_126 a_126; mov mem0_128 a_128; mov mem0_130 a_130; 
mov mem0_132 a_132; mov mem0_134 a_134; mov mem0_136 a_136; 
mov mem0_138 a_138; mov mem0_140 a_140; mov mem0_142 a_142; 
mov mem0_144 a_144; mov mem0_146 a_146; mov mem0_148 a_148; 
mov mem0_150 a_150; mov mem0_152 a_152; mov mem0_154 a_154; 
mov mem0_156 a_156; mov mem0_158 a_158; mov mem0_160 a_160; 
mov mem0_162 a_162; mov mem0_164 a_164; mov mem0_166 a_166; 
mov mem0_168 a_168; mov mem0_170 a_170; mov mem0_172 a_172; 
mov mem0_174 a_174; mov mem0_176 a_176; mov mem0_178 a_178; 
mov mem0_180 a_180; mov mem0_182 a_182; mov mem0_184 a_184; 
mov mem0_186 a_186; mov mem0_188 a_188; mov mem0_190 a_190; 
mov mem0_192 a_192; mov mem0_194 a_194; mov mem0_196 a_196; 
mov mem0_198 a_198; mov mem0_200 a_200; mov mem0_202 a_202; 
mov mem0_204 a_204; mov mem0_206 a_206; mov mem0_208 a_208; 
mov mem0_210 a_210; mov mem0_212 a_212; mov mem0_214 a_214; 
mov mem0_216 a_216; mov mem0_218 a_218; mov mem0_220 a_220; 
mov mem0_222 a_222; mov mem0_224 a_224; mov mem0_226 a_226; 
mov mem0_228 a_228; mov mem0_230 a_230; mov mem0_232 a_232; 
mov mem0_234 a_234; mov mem0_236 a_236; mov mem0_238 a_238; 
mov mem0_240 a_240; mov mem0_242 a_242; mov mem0_244 a_244; 
mov mem0_246 a_246; mov mem0_248 a_248; mov mem0_250 a_250; 
mov mem0_252 a_252; mov mem0_254 a_254; mov mem0_256 a_256; 
mov mem0_258 a_258; mov mem0_260 a_260; mov mem0_262 a_262; 
mov mem0_264 a_264; mov mem0_266 a_266; mov mem0_268 a_268; 
mov mem0_270 a_270; mov mem0_272 a_272; mov mem0_274 a_274; 
mov mem0_276 a_276; mov mem0_278 a_278; mov mem0_280 a_280; 
mov mem0_282 a_282; mov mem0_284 a_284; mov mem0_286 a_286; 
mov mem0_288 a_288; mov mem0_290 a_290; mov mem0_292 a_292; 
mov mem0_294 a_294; mov mem0_296 a_296; mov mem0_298 a_298; 
mov mem0_300 a_300; mov mem0_302 a_302; mov mem0_304 a_304; 
mov mem0_306 a_306; mov mem0_308 a_308; mov mem0_310 a_310; 
mov mem0_312 a_312; mov mem0_314 a_314; mov mem0_316 a_316; 
mov mem0_318 a_318; mov mem0_320 a_320; mov mem0_322 a_322; 
mov mem0_324 a_324; mov mem0_326 a_326; mov mem0_328 a_328; 
mov mem0_330 a_330; mov mem0_332 a_332; mov mem0_334 a_334; 
mov mem0_336 a_336; mov mem0_338 a_338; mov mem0_340 a_340; 
mov mem0_342 a_342; mov mem0_344 a_344; mov mem0_346 a_346; 
mov mem0_348 a_348; mov mem0_350 a_350; mov mem0_352 a_352; 
mov mem0_354 a_354; mov mem0_356 a_356; mov mem0_358 a_358; 
mov mem0_360 a_360; mov mem0_362 a_362; mov mem0_364 a_364; 
mov mem0_366 a_366; mov mem0_368 a_368; mov mem0_370 a_370; 
mov mem0_372 a_372; mov mem0_374 a_374; mov mem0_376 a_376; 
mov mem0_378 a_378; mov mem0_380 a_380; mov mem0_382 a_382; 
mov mem0_384 a_384; mov mem0_386 a_386; mov mem0_388 a_388; 
mov mem0_390 a_390; mov mem0_392 a_392; mov mem0_394 a_394; 
mov mem0_396 a_396; mov mem0_398 a_398; mov mem0_400 a_400; 
mov mem0_402 a_402; mov mem0_404 a_404; mov mem0_406 a_406; 
mov mem0_408 a_408; mov mem0_410 a_410; mov mem0_412 a_412; 
mov mem0_414 a_414; mov mem0_416 a_416; mov mem0_418 a_418; 
mov mem0_420 a_420; mov mem0_422 a_422; mov mem0_424 a_424; 
mov mem0_426 a_426; mov mem0_428 a_428; mov mem0_430 a_430; 
mov mem0_432 a_432; mov mem0_434 a_434; mov mem0_436 a_436; 
mov mem0_438 a_438; mov mem0_440 a_440; mov mem0_442 a_442; 
mov mem0_444 a_444; mov mem0_446 a_446; mov mem0_448 a_448; 
mov mem0_450 a_450; mov mem0_452 a_452; mov mem0_454 a_454; 
mov mem0_456 a_456; mov mem0_458 a_458; mov mem0_460 a_460; 
mov mem0_462 a_462; mov mem0_464 a_464; mov mem0_466 a_466; 
mov mem0_468 a_468; mov mem0_470 a_470; mov mem0_472 a_472; 
mov mem0_474 a_474; mov mem0_476 a_476; mov mem0_478 a_478; 
mov mem0_480 a_480; mov mem0_482 a_482; mov mem0_484 a_484; 
mov mem0_486 a_486; mov mem0_488 a_488; mov mem0_490 a_490; 
mov mem0_492 a_492; mov mem0_494 a_494; mov mem0_496 a_496; 
mov mem0_498 a_498; mov mem0_500 a_500; mov mem0_502 a_502; 
mov mem0_504 a_504; mov mem0_506 a_506; mov mem0_508 a_508; 
mov mem0_510 a_510; 

nondet v_call_i@sint16;
nondet v_call_i_1289@sint16;
nondet v_call_i_2296@sint16;
nondet v_call_i_3303@sint16;
nondet v_call_i_4310@sint16;
nondet v_call_i_5317@sint16;
nondet v_call_i_6324@sint16;
nondet v_call_i_7@sint16;
nondet v_call_i_8@sint16;
nondet v_call_i_9@sint16;
nondet v_call_i_10@sint16;
nondet v_call_i_11@sint16;
nondet v_call_i_12@sint16;
nondet v_call_i_13@sint16;
nondet v_call_i_14@sint16;
nondet v_call_i_15@sint16;
nondet v_call_i_16@sint16;
nondet v_call_i_17@sint16;
nondet v_call_i_18@sint16;
nondet v_call_i_19@sint16;
nondet v_call_i_20@sint16;
nondet v_call_i_21@sint16;
nondet v_call_i_22@sint16;
nondet v_call_i_23@sint16;
nondet v_call_i_24@sint16;
nondet v_call_i_25@sint16;
nondet v_call_i_26@sint16;
nondet v_call_i_27@sint16;
nondet v_call_i_28@sint16;
nondet v_call_i_29@sint16;
nondet v_call_i_30@sint16;
nondet v_call_i_31@sint16;
nondet v_call_i_32@sint16;
nondet v_call_i_33@sint16;
nondet v_call_i_34@sint16;
nondet v_call_i_35@sint16;
nondet v_call_i_36@sint16;
nondet v_call_i_37@sint16;
nondet v_call_i_38@sint16;
nondet v_call_i_39@sint16;
nondet v_call_i_40@sint16;
nondet v_call_i_41@sint16;
nondet v_call_i_42@sint16;
nondet v_call_i_43@sint16;
nondet v_call_i_44@sint16;
nondet v_call_i_45@sint16;
nondet v_call_i_46@sint16;
nondet v_call_i_47@sint16;
nondet v_call_i_48@sint16;
nondet v_call_i_49@sint16;
nondet v_call_i_50@sint16;
nondet v_call_i_51@sint16;
nondet v_call_i_52@sint16;
nondet v_call_i_53@sint16;
nondet v_call_i_54@sint16;
nondet v_call_i_55@sint16;
nondet v_call_i_56@sint16;
nondet v_call_i_57@sint16;
nondet v_call_i_58@sint16;
nondet v_call_i_59@sint16;
nondet v_call_i_60@sint16;
nondet v_call_i_61@sint16;
nondet v_call_i_62@sint16;
nondet v_call_i_63@sint16;
nondet v_call_i_64@sint16;
nondet v_call_i_65@sint16;
nondet v_call_i_66@sint16;
nondet v_call_i_67@sint16;
nondet v_call_i_68@sint16;
nondet v_call_i_69@sint16;
nondet v_call_i_70@sint16;
nondet v_call_i_71@sint16;
nondet v_call_i_72@sint16;
nondet v_call_i_73@sint16;
nondet v_call_i_74@sint16;
nondet v_call_i_75@sint16;
nondet v_call_i_76@sint16;
nondet v_call_i_77@sint16;
nondet v_call_i_78@sint16;
nondet v_call_i_79@sint16;
nondet v_call_i_80@sint16;
nondet v_call_i_81@sint16;
nondet v_call_i_82@sint16;
nondet v_call_i_83@sint16;
nondet v_call_i_84@sint16;
nondet v_call_i_85@sint16;
nondet v_call_i_86@sint16;
nondet v_call_i_87@sint16;
nondet v_call_i_88@sint16;
nondet v_call_i_89@sint16;
nondet v_call_i_90@sint16;
nondet v_call_i_91@sint16;
nondet v_call_i_92@sint16;
nondet v_call_i_93@sint16;
nondet v_call_i_94@sint16;
nondet v_call_i_95@sint16;
nondet v_call_i_96@sint16;
nondet v_call_i_97@sint16;
nondet v_call_i_98@sint16;
nondet v_call_i_99@sint16;
nondet v_call_i_100@sint16;
nondet v_call_i_101@sint16;
nondet v_call_i_102@sint16;
nondet v_call_i_103@sint16;
nondet v_call_i_104@sint16;
nondet v_call_i_105@sint16;
nondet v_call_i_106@sint16;
nondet v_call_i_107@sint16;
nondet v_call_i_108@sint16;
nondet v_call_i_109@sint16;
nondet v_call_i_110@sint16;
nondet v_call_i_111@sint16;
nondet v_call_i_112@sint16;
nondet v_call_i_113@sint16;
nondet v_call_i_114@sint16;
nondet v_call_i_115@sint16;
nondet v_call_i_116@sint16;
nondet v_call_i_117@sint16;
nondet v_call_i_118@sint16;
nondet v_call_i_119@sint16;
nondet v_call_i_120@sint16;
nondet v_call_i_121@sint16;
nondet v_call_i_122@sint16;
nondet v_call_i_123@sint16;
nondet v_call_i_124@sint16;
nondet v_call_i_125@sint16;
nondet v_call_i_126@sint16;
nondet v_call_i_127@sint16;
nondet v_call_i_1@sint16;
nondet v_call_i_1_1@sint16;
nondet v_call_i_1_2@sint16;
nondet v_call_i_1_3@sint16;
nondet v_call_i_1_4@sint16;
nondet v_call_i_1_5@sint16;
nondet v_call_i_1_6@sint16;
nondet v_call_i_1_7@sint16;
nondet v_call_i_1_8@sint16;
nondet v_call_i_1_9@sint16;
nondet v_call_i_1_10@sint16;
nondet v_call_i_1_11@sint16;
nondet v_call_i_1_12@sint16;
nondet v_call_i_1_13@sint16;
nondet v_call_i_1_14@sint16;
nondet v_call_i_1_15@sint16;
nondet v_call_i_1_16@sint16;
nondet v_call_i_1_17@sint16;
nondet v_call_i_1_18@sint16;
nondet v_call_i_1_19@sint16;
nondet v_call_i_1_20@sint16;
nondet v_call_i_1_21@sint16;
nondet v_call_i_1_22@sint16;
nondet v_call_i_1_23@sint16;
nondet v_call_i_1_24@sint16;
nondet v_call_i_1_25@sint16;
nondet v_call_i_1_26@sint16;
nondet v_call_i_1_27@sint16;
nondet v_call_i_1_28@sint16;
nondet v_call_i_1_29@sint16;
nondet v_call_i_1_30@sint16;
nondet v_call_i_1_31@sint16;
nondet v_call_i_1_32@sint16;
nondet v_call_i_1_33@sint16;
nondet v_call_i_1_34@sint16;
nondet v_call_i_1_35@sint16;
nondet v_call_i_1_36@sint16;
nondet v_call_i_1_37@sint16;
nondet v_call_i_1_38@sint16;
nondet v_call_i_1_39@sint16;
nondet v_call_i_1_40@sint16;
nondet v_call_i_1_41@sint16;
nondet v_call_i_1_42@sint16;
nondet v_call_i_1_43@sint16;
nondet v_call_i_1_44@sint16;
nondet v_call_i_1_45@sint16;
nondet v_call_i_1_46@sint16;
nondet v_call_i_1_47@sint16;
nondet v_call_i_1_48@sint16;
nondet v_call_i_1_49@sint16;
nondet v_call_i_1_50@sint16;
nondet v_call_i_1_51@sint16;
nondet v_call_i_1_52@sint16;
nondet v_call_i_1_53@sint16;
nondet v_call_i_1_54@sint16;
nondet v_call_i_1_55@sint16;
nondet v_call_i_1_56@sint16;
nondet v_call_i_1_57@sint16;
nondet v_call_i_1_58@sint16;
nondet v_call_i_1_59@sint16;
nondet v_call_i_1_60@sint16;
nondet v_call_i_1_61@sint16;
nondet v_call_i_1_62@sint16;
nondet v_call_i_1_63@sint16;
nondet v_call_i_1_1281@sint16;
nondet v_call_i_1_1_1@sint16;
nondet v_call_i_1_2_1@sint16;
nondet v_call_i_1_3_1@sint16;
nondet v_call_i_1_4_1@sint16;
nondet v_call_i_1_5_1@sint16;
nondet v_call_i_1_6_1@sint16;
nondet v_call_i_1_7_1@sint16;
nondet v_call_i_1_8_1@sint16;
nondet v_call_i_1_9_1@sint16;
nondet v_call_i_1_10_1@sint16;
nondet v_call_i_1_11_1@sint16;
nondet v_call_i_1_12_1@sint16;
nondet v_call_i_1_13_1@sint16;
nondet v_call_i_1_14_1@sint16;
nondet v_call_i_1_15_1@sint16;
nondet v_call_i_1_16_1@sint16;
nondet v_call_i_1_17_1@sint16;
nondet v_call_i_1_18_1@sint16;
nondet v_call_i_1_19_1@sint16;
nondet v_call_i_1_20_1@sint16;
nondet v_call_i_1_21_1@sint16;
nondet v_call_i_1_22_1@sint16;
nondet v_call_i_1_23_1@sint16;
nondet v_call_i_1_24_1@sint16;
nondet v_call_i_1_25_1@sint16;
nondet v_call_i_1_26_1@sint16;
nondet v_call_i_1_27_1@sint16;
nondet v_call_i_1_28_1@sint16;
nondet v_call_i_1_29_1@sint16;
nondet v_call_i_1_30_1@sint16;
nondet v_call_i_1_31_1@sint16;
nondet v_call_i_1_32_1@sint16;
nondet v_call_i_1_33_1@sint16;
nondet v_call_i_1_34_1@sint16;
nondet v_call_i_1_35_1@sint16;
nondet v_call_i_1_36_1@sint16;
nondet v_call_i_1_37_1@sint16;
nondet v_call_i_1_38_1@sint16;
nondet v_call_i_1_39_1@sint16;
nondet v_call_i_1_40_1@sint16;
nondet v_call_i_1_41_1@sint16;
nondet v_call_i_1_42_1@sint16;
nondet v_call_i_1_43_1@sint16;
nondet v_call_i_1_44_1@sint16;
nondet v_call_i_1_45_1@sint16;
nondet v_call_i_1_46_1@sint16;
nondet v_call_i_1_47_1@sint16;
nondet v_call_i_1_48_1@sint16;
nondet v_call_i_1_49_1@sint16;
nondet v_call_i_1_50_1@sint16;
nondet v_call_i_1_51_1@sint16;
nondet v_call_i_1_52_1@sint16;
nondet v_call_i_1_53_1@sint16;
nondet v_call_i_1_54_1@sint16;
nondet v_call_i_1_55_1@sint16;
nondet v_call_i_1_56_1@sint16;
nondet v_call_i_1_57_1@sint16;
nondet v_call_i_1_58_1@sint16;
nondet v_call_i_1_59_1@sint16;
nondet v_call_i_1_60_1@sint16;
nondet v_call_i_1_61_1@sint16;
nondet v_call_i_1_62_1@sint16;
nondet v_call_i_1_63_1@sint16;
nondet v_call_i_2@sint16;
nondet v_call_i_2_1@sint16;
nondet v_call_i_2_2@sint16;
nondet v_call_i_2_3@sint16;
nondet v_call_i_2_4@sint16;
nondet v_call_i_2_5@sint16;
nondet v_call_i_2_6@sint16;
nondet v_call_i_2_7@sint16;
nondet v_call_i_2_8@sint16;
nondet v_call_i_2_9@sint16;
nondet v_call_i_2_10@sint16;
nondet v_call_i_2_11@sint16;
nondet v_call_i_2_12@sint16;
nondet v_call_i_2_13@sint16;
nondet v_call_i_2_14@sint16;
nondet v_call_i_2_15@sint16;
nondet v_call_i_2_16@sint16;
nondet v_call_i_2_17@sint16;
nondet v_call_i_2_18@sint16;
nondet v_call_i_2_19@sint16;
nondet v_call_i_2_20@sint16;
nondet v_call_i_2_21@sint16;
nondet v_call_i_2_22@sint16;
nondet v_call_i_2_23@sint16;
nondet v_call_i_2_24@sint16;
nondet v_call_i_2_25@sint16;
nondet v_call_i_2_26@sint16;
nondet v_call_i_2_27@sint16;
nondet v_call_i_2_28@sint16;
nondet v_call_i_2_29@sint16;
nondet v_call_i_2_30@sint16;
nondet v_call_i_2_31@sint16;
nondet v_call_i_2_1251@sint16;
nondet v_call_i_2_1_1@sint16;
nondet v_call_i_2_2_1@sint16;
nondet v_call_i_2_3_1@sint16;
nondet v_call_i_2_4_1@sint16;
nondet v_call_i_2_5_1@sint16;
nondet v_call_i_2_6_1@sint16;
nondet v_call_i_2_7_1@sint16;
nondet v_call_i_2_8_1@sint16;
nondet v_call_i_2_9_1@sint16;
nondet v_call_i_2_10_1@sint16;
nondet v_call_i_2_11_1@sint16;
nondet v_call_i_2_12_1@sint16;
nondet v_call_i_2_13_1@sint16;
nondet v_call_i_2_14_1@sint16;
nondet v_call_i_2_15_1@sint16;
nondet v_call_i_2_16_1@sint16;
nondet v_call_i_2_17_1@sint16;
nondet v_call_i_2_18_1@sint16;
nondet v_call_i_2_19_1@sint16;
nondet v_call_i_2_20_1@sint16;
nondet v_call_i_2_21_1@sint16;
nondet v_call_i_2_22_1@sint16;
nondet v_call_i_2_23_1@sint16;
nondet v_call_i_2_24_1@sint16;
nondet v_call_i_2_25_1@sint16;
nondet v_call_i_2_26_1@sint16;
nondet v_call_i_2_27_1@sint16;
nondet v_call_i_2_28_1@sint16;
nondet v_call_i_2_29_1@sint16;
nondet v_call_i_2_30_1@sint16;
nondet v_call_i_2_31_1@sint16;
nondet v_call_i_2_2261@sint16;
nondet v_call_i_2_1_2@sint16;
nondet v_call_i_2_2_2@sint16;
nondet v_call_i_2_3_2@sint16;
nondet v_call_i_2_4_2@sint16;
nondet v_call_i_2_5_2@sint16;
nondet v_call_i_2_6_2@sint16;
nondet v_call_i_2_7_2@sint16;
nondet v_call_i_2_8_2@sint16;
nondet v_call_i_2_9_2@sint16;
nondet v_call_i_2_10_2@sint16;
nondet v_call_i_2_11_2@sint16;
nondet v_call_i_2_12_2@sint16;
nondet v_call_i_2_13_2@sint16;
nondet v_call_i_2_14_2@sint16;
nondet v_call_i_2_15_2@sint16;
nondet v_call_i_2_16_2@sint16;
nondet v_call_i_2_17_2@sint16;
nondet v_call_i_2_18_2@sint16;
nondet v_call_i_2_19_2@sint16;
nondet v_call_i_2_20_2@sint16;
nondet v_call_i_2_21_2@sint16;
nondet v_call_i_2_22_2@sint16;
nondet v_call_i_2_23_2@sint16;
nondet v_call_i_2_24_2@sint16;
nondet v_call_i_2_25_2@sint16;
nondet v_call_i_2_26_2@sint16;
nondet v_call_i_2_27_2@sint16;
nondet v_call_i_2_28_2@sint16;
nondet v_call_i_2_29_2@sint16;
nondet v_call_i_2_30_2@sint16;
nondet v_call_i_2_31_2@sint16;
nondet v_call_i_2_3271@sint16;
nondet v_call_i_2_1_3@sint16;
nondet v_call_i_2_2_3@sint16;
nondet v_call_i_2_3_3@sint16;
nondet v_call_i_2_4_3@sint16;
nondet v_call_i_2_5_3@sint16;
nondet v_call_i_2_6_3@sint16;
nondet v_call_i_2_7_3@sint16;
nondet v_call_i_2_8_3@sint16;
nondet v_call_i_2_9_3@sint16;
nondet v_call_i_2_10_3@sint16;
nondet v_call_i_2_11_3@sint16;
nondet v_call_i_2_12_3@sint16;
nondet v_call_i_2_13_3@sint16;
nondet v_call_i_2_14_3@sint16;
nondet v_call_i_2_15_3@sint16;
nondet v_call_i_2_16_3@sint16;
nondet v_call_i_2_17_3@sint16;
nondet v_call_i_2_18_3@sint16;
nondet v_call_i_2_19_3@sint16;
nondet v_call_i_2_20_3@sint16;
nondet v_call_i_2_21_3@sint16;
nondet v_call_i_2_22_3@sint16;
nondet v_call_i_2_23_3@sint16;
nondet v_call_i_2_24_3@sint16;
nondet v_call_i_2_25_3@sint16;
nondet v_call_i_2_26_3@sint16;
nondet v_call_i_2_27_3@sint16;
nondet v_call_i_2_28_3@sint16;
nondet v_call_i_2_29_3@sint16;
nondet v_call_i_2_30_3@sint16;
nondet v_call_i_2_31_3@sint16;
nondet v_call_i_3@sint16;
nondet v_call_i_3_1@sint16;
nondet v_call_i_3_2@sint16;
nondet v_call_i_3_3@sint16;
nondet v_call_i_3_4@sint16;
nondet v_call_i_3_5@sint16;
nondet v_call_i_3_6@sint16;
nondet v_call_i_3_7@sint16;
nondet v_call_i_3_8@sint16;
nondet v_call_i_3_9@sint16;
nondet v_call_i_3_10@sint16;
nondet v_call_i_3_11@sint16;
nondet v_call_i_3_12@sint16;
nondet v_call_i_3_13@sint16;
nondet v_call_i_3_14@sint16;
nondet v_call_i_3_15@sint16;
nondet v_call_i_3_1181@sint16;
nondet v_call_i_3_1_1@sint16;
nondet v_call_i_3_2_1@sint16;
nondet v_call_i_3_3_1@sint16;
nondet v_call_i_3_4_1@sint16;
nondet v_call_i_3_5_1@sint16;
nondet v_call_i_3_6_1@sint16;
nondet v_call_i_3_7_1@sint16;
nondet v_call_i_3_8_1@sint16;
nondet v_call_i_3_9_1@sint16;
nondet v_call_i_3_10_1@sint16;
nondet v_call_i_3_11_1@sint16;
nondet v_call_i_3_12_1@sint16;
nondet v_call_i_3_13_1@sint16;
nondet v_call_i_3_14_1@sint16;
nondet v_call_i_3_15_1@sint16;
nondet v_call_i_3_2191@sint16;
nondet v_call_i_3_1_2@sint16;
nondet v_call_i_3_2_2@sint16;
nondet v_call_i_3_3_2@sint16;
nondet v_call_i_3_4_2@sint16;
nondet v_call_i_3_5_2@sint16;
nondet v_call_i_3_6_2@sint16;
nondet v_call_i_3_7_2@sint16;
nondet v_call_i_3_8_2@sint16;
nondet v_call_i_3_9_2@sint16;
nondet v_call_i_3_10_2@sint16;
nondet v_call_i_3_11_2@sint16;
nondet v_call_i_3_12_2@sint16;
nondet v_call_i_3_13_2@sint16;
nondet v_call_i_3_14_2@sint16;
nondet v_call_i_3_15_2@sint16;
nondet v_call_i_3_3201@sint16;
nondet v_call_i_3_1_3@sint16;
nondet v_call_i_3_2_3@sint16;
nondet v_call_i_3_3_3@sint16;
nondet v_call_i_3_4_3@sint16;
nondet v_call_i_3_5_3@sint16;
nondet v_call_i_3_6_3@sint16;
nondet v_call_i_3_7_3@sint16;
nondet v_call_i_3_8_3@sint16;
nondet v_call_i_3_9_3@sint16;
nondet v_call_i_3_10_3@sint16;
nondet v_call_i_3_11_3@sint16;
nondet v_call_i_3_12_3@sint16;
nondet v_call_i_3_13_3@sint16;
nondet v_call_i_3_14_3@sint16;
nondet v_call_i_3_15_3@sint16;
nondet v_call_i_3_4211@sint16;
nondet v_call_i_3_1_4@sint16;
nondet v_call_i_3_2_4@sint16;
nondet v_call_i_3_3_4@sint16;
nondet v_call_i_3_4_4@sint16;
nondet v_call_i_3_5_4@sint16;
nondet v_call_i_3_6_4@sint16;
nondet v_call_i_3_7_4@sint16;
nondet v_call_i_3_8_4@sint16;
nondet v_call_i_3_9_4@sint16;
nondet v_call_i_3_10_4@sint16;
nondet v_call_i_3_11_4@sint16;
nondet v_call_i_3_12_4@sint16;
nondet v_call_i_3_13_4@sint16;
nondet v_call_i_3_14_4@sint16;
nondet v_call_i_3_15_4@sint16;
nondet v_call_i_3_5221@sint16;
nondet v_call_i_3_1_5@sint16;
nondet v_call_i_3_2_5@sint16;
nondet v_call_i_3_3_5@sint16;
nondet v_call_i_3_4_5@sint16;
nondet v_call_i_3_5_5@sint16;
nondet v_call_i_3_6_5@sint16;
nondet v_call_i_3_7_5@sint16;
nondet v_call_i_3_8_5@sint16;
nondet v_call_i_3_9_5@sint16;
nondet v_call_i_3_10_5@sint16;
nondet v_call_i_3_11_5@sint16;
nondet v_call_i_3_12_5@sint16;
nondet v_call_i_3_13_5@sint16;
nondet v_call_i_3_14_5@sint16;
nondet v_call_i_3_15_5@sint16;
nondet v_call_i_3_6231@sint16;
nondet v_call_i_3_1_6@sint16;
nondet v_call_i_3_2_6@sint16;
nondet v_call_i_3_3_6@sint16;
nondet v_call_i_3_4_6@sint16;
nondet v_call_i_3_5_6@sint16;
nondet v_call_i_3_6_6@sint16;
nondet v_call_i_3_7_6@sint16;
nondet v_call_i_3_8_6@sint16;
nondet v_call_i_3_9_6@sint16;
nondet v_call_i_3_10_6@sint16;
nondet v_call_i_3_11_6@sint16;
nondet v_call_i_3_12_6@sint16;
nondet v_call_i_3_13_6@sint16;
nondet v_call_i_3_14_6@sint16;
nondet v_call_i_3_15_6@sint16;
nondet v_call_i_3_7241@sint16;
nondet v_call_i_3_1_7@sint16;
nondet v_call_i_3_2_7@sint16;
nondet v_call_i_3_3_7@sint16;
nondet v_call_i_3_4_7@sint16;
nondet v_call_i_3_5_7@sint16;
nondet v_call_i_3_6_7@sint16;
nondet v_call_i_3_7_7@sint16;
nondet v_call_i_3_8_7@sint16;
nondet v_call_i_3_9_7@sint16;
nondet v_call_i_3_10_7@sint16;
nondet v_call_i_3_11_7@sint16;
nondet v_call_i_3_12_7@sint16;
nondet v_call_i_3_13_7@sint16;
nondet v_call_i_3_14_7@sint16;
nondet v_call_i_3_15_7@sint16;
nondet v_call_i_4@sint16;
nondet v_call_i_4_1@sint16;
nondet v_call_i_4_2@sint16;
nondet v_call_i_4_3@sint16;
nondet v_call_i_4_4@sint16;
nondet v_call_i_4_5@sint16;
nondet v_call_i_4_6@sint16;
nondet v_call_i_4_7@sint16;
nondet v_call_i_4_1111@sint16;
nondet v_call_i_4_1_1@sint16;
nondet v_call_i_4_2_1@sint16;
nondet v_call_i_4_3_1@sint16;
nondet v_call_i_4_4_1@sint16;
nondet v_call_i_4_5_1@sint16;
nondet v_call_i_4_6_1@sint16;
nondet v_call_i_4_7_1@sint16;
nondet v_call_i_4_2121@sint16;
nondet v_call_i_4_1_2@sint16;
nondet v_call_i_4_2_2@sint16;
nondet v_call_i_4_3_2@sint16;
nondet v_call_i_4_4_2@sint16;
nondet v_call_i_4_5_2@sint16;
nondet v_call_i_4_6_2@sint16;
nondet v_call_i_4_7_2@sint16;
nondet v_call_i_4_3131@sint16;
nondet v_call_i_4_1_3@sint16;
nondet v_call_i_4_2_3@sint16;
nondet v_call_i_4_3_3@sint16;
nondet v_call_i_4_4_3@sint16;
nondet v_call_i_4_5_3@sint16;
nondet v_call_i_4_6_3@sint16;
nondet v_call_i_4_7_3@sint16;
nondet v_call_i_4_4141@sint16;
nondet v_call_i_4_1_4@sint16;
nondet v_call_i_4_2_4@sint16;
nondet v_call_i_4_3_4@sint16;
nondet v_call_i_4_4_4@sint16;
nondet v_call_i_4_5_4@sint16;
nondet v_call_i_4_6_4@sint16;
nondet v_call_i_4_7_4@sint16;
nondet v_call_i_4_5151@sint16;
nondet v_call_i_4_1_5@sint16;
nondet v_call_i_4_2_5@sint16;
nondet v_call_i_4_3_5@sint16;
nondet v_call_i_4_4_5@sint16;
nondet v_call_i_4_5_5@sint16;
nondet v_call_i_4_6_5@sint16;
nondet v_call_i_4_7_5@sint16;
nondet v_call_i_4_6161@sint16;
nondet v_call_i_4_1_6@sint16;
nondet v_call_i_4_2_6@sint16;
nondet v_call_i_4_3_6@sint16;
nondet v_call_i_4_4_6@sint16;
nondet v_call_i_4_5_6@sint16;
nondet v_call_i_4_6_6@sint16;
nondet v_call_i_4_7_6@sint16;
nondet v_call_i_4_7171@sint16;
nondet v_call_i_4_1_7@sint16;
nondet v_call_i_4_2_7@sint16;
nondet v_call_i_4_3_7@sint16;
nondet v_call_i_4_4_7@sint16;
nondet v_call_i_4_5_7@sint16;
nondet v_call_i_4_6_7@sint16;
nondet v_call_i_4_7_7@sint16;
nondet v_call_i_4_8@sint16;
nondet v_call_i_4_1_8@sint16;
nondet v_call_i_4_2_8@sint16;
nondet v_call_i_4_3_8@sint16;
nondet v_call_i_4_4_8@sint16;
nondet v_call_i_4_5_8@sint16;
nondet v_call_i_4_6_8@sint16;
nondet v_call_i_4_7_8@sint16;
nondet v_call_i_4_9@sint16;
nondet v_call_i_4_1_9@sint16;
nondet v_call_i_4_2_9@sint16;
nondet v_call_i_4_3_9@sint16;
nondet v_call_i_4_4_9@sint16;
nondet v_call_i_4_5_9@sint16;
nondet v_call_i_4_6_9@sint16;
nondet v_call_i_4_7_9@sint16;
nondet v_call_i_4_10@sint16;
nondet v_call_i_4_1_10@sint16;
nondet v_call_i_4_2_10@sint16;
nondet v_call_i_4_3_10@sint16;
nondet v_call_i_4_4_10@sint16;
nondet v_call_i_4_5_10@sint16;
nondet v_call_i_4_6_10@sint16;
nondet v_call_i_4_7_10@sint16;
nondet v_call_i_4_11@sint16;
nondet v_call_i_4_1_11@sint16;
nondet v_call_i_4_2_11@sint16;
nondet v_call_i_4_3_11@sint16;
nondet v_call_i_4_4_11@sint16;
nondet v_call_i_4_5_11@sint16;
nondet v_call_i_4_6_11@sint16;
nondet v_call_i_4_7_11@sint16;
nondet v_call_i_4_12@sint16;
nondet v_call_i_4_1_12@sint16;
nondet v_call_i_4_2_12@sint16;
nondet v_call_i_4_3_12@sint16;
nondet v_call_i_4_4_12@sint16;
nondet v_call_i_4_5_12@sint16;
nondet v_call_i_4_6_12@sint16;
nondet v_call_i_4_7_12@sint16;
nondet v_call_i_4_13@sint16;
nondet v_call_i_4_1_13@sint16;
nondet v_call_i_4_2_13@sint16;
nondet v_call_i_4_3_13@sint16;
nondet v_call_i_4_4_13@sint16;
nondet v_call_i_4_5_13@sint16;
nondet v_call_i_4_6_13@sint16;
nondet v_call_i_4_7_13@sint16;
nondet v_call_i_4_14@sint16;
nondet v_call_i_4_1_14@sint16;
nondet v_call_i_4_2_14@sint16;
nondet v_call_i_4_3_14@sint16;
nondet v_call_i_4_4_14@sint16;
nondet v_call_i_4_5_14@sint16;
nondet v_call_i_4_6_14@sint16;
nondet v_call_i_4_7_14@sint16;
nondet v_call_i_4_15@sint16;
nondet v_call_i_4_1_15@sint16;
nondet v_call_i_4_2_15@sint16;
nondet v_call_i_4_3_15@sint16;
nondet v_call_i_4_4_15@sint16;
nondet v_call_i_4_5_15@sint16;
nondet v_call_i_4_6_15@sint16;
nondet v_call_i_4_7_15@sint16;
nondet v_call_i_5@sint16;
nondet v_call_i_5_1@sint16;
nondet v_call_i_5_2@sint16;
nondet v_call_i_5_3@sint16;
nondet v_call_i_5_181@sint16;
nondet v_call_i_5_1_1@sint16;
nondet v_call_i_5_2_1@sint16;
nondet v_call_i_5_3_1@sint16;
nondet v_call_i_5_291@sint16;
nondet v_call_i_5_1_2@sint16;
nondet v_call_i_5_2_2@sint16;
nondet v_call_i_5_3_2@sint16;
nondet v_call_i_5_3101@sint16;
nondet v_call_i_5_1_3@sint16;
nondet v_call_i_5_2_3@sint16;
nondet v_call_i_5_3_3@sint16;
nondet v_call_i_5_4@sint16;
nondet v_call_i_5_1_4@sint16;
nondet v_call_i_5_2_4@sint16;
nondet v_call_i_5_3_4@sint16;
nondet v_call_i_5_5@sint16;
nondet v_call_i_5_1_5@sint16;
nondet v_call_i_5_2_5@sint16;
nondet v_call_i_5_3_5@sint16;
nondet v_call_i_5_6@sint16;
nondet v_call_i_5_1_6@sint16;
nondet v_call_i_5_2_6@sint16;
nondet v_call_i_5_3_6@sint16;
nondet v_call_i_5_7@sint16;
nondet v_call_i_5_1_7@sint16;
nondet v_call_i_5_2_7@sint16;
nondet v_call_i_5_3_7@sint16;
nondet v_call_i_5_8@sint16;
nondet v_call_i_5_1_8@sint16;
nondet v_call_i_5_2_8@sint16;
nondet v_call_i_5_3_8@sint16;
nondet v_call_i_5_9@sint16;
nondet v_call_i_5_1_9@sint16;
nondet v_call_i_5_2_9@sint16;
nondet v_call_i_5_3_9@sint16;
nondet v_call_i_5_10@sint16;
nondet v_call_i_5_1_10@sint16;
nondet v_call_i_5_2_10@sint16;
nondet v_call_i_5_3_10@sint16;
nondet v_call_i_5_11@sint16;
nondet v_call_i_5_1_11@sint16;
nondet v_call_i_5_2_11@sint16;
nondet v_call_i_5_3_11@sint16;
nondet v_call_i_5_12@sint16;
nondet v_call_i_5_1_12@sint16;
nondet v_call_i_5_2_12@sint16;
nondet v_call_i_5_3_12@sint16;
nondet v_call_i_5_13@sint16;
nondet v_call_i_5_1_13@sint16;
nondet v_call_i_5_2_13@sint16;
nondet v_call_i_5_3_13@sint16;
nondet v_call_i_5_14@sint16;
nondet v_call_i_5_1_14@sint16;
nondet v_call_i_5_2_14@sint16;
nondet v_call_i_5_3_14@sint16;
nondet v_call_i_5_15@sint16;
nondet v_call_i_5_1_15@sint16;
nondet v_call_i_5_2_15@sint16;
nondet v_call_i_5_3_15@sint16;
nondet v_call_i_5_16@sint16;
nondet v_call_i_5_1_16@sint16;
nondet v_call_i_5_2_16@sint16;
nondet v_call_i_5_3_16@sint16;
nondet v_call_i_5_17@sint16;
nondet v_call_i_5_1_17@sint16;
nondet v_call_i_5_2_17@sint16;
nondet v_call_i_5_3_17@sint16;
nondet v_call_i_5_18@sint16;
nondet v_call_i_5_1_18@sint16;
nondet v_call_i_5_2_18@sint16;
nondet v_call_i_5_3_18@sint16;
nondet v_call_i_5_19@sint16;
nondet v_call_i_5_1_19@sint16;
nondet v_call_i_5_2_19@sint16;
nondet v_call_i_5_3_19@sint16;
nondet v_call_i_5_20@sint16;
nondet v_call_i_5_1_20@sint16;
nondet v_call_i_5_2_20@sint16;
nondet v_call_i_5_3_20@sint16;
nondet v_call_i_5_21@sint16;
nondet v_call_i_5_1_21@sint16;
nondet v_call_i_5_2_21@sint16;
nondet v_call_i_5_3_21@sint16;
nondet v_call_i_5_22@sint16;
nondet v_call_i_5_1_22@sint16;
nondet v_call_i_5_2_22@sint16;
nondet v_call_i_5_3_22@sint16;
nondet v_call_i_5_23@sint16;
nondet v_call_i_5_1_23@sint16;
nondet v_call_i_5_2_23@sint16;
nondet v_call_i_5_3_23@sint16;
nondet v_call_i_5_24@sint16;
nondet v_call_i_5_1_24@sint16;
nondet v_call_i_5_2_24@sint16;
nondet v_call_i_5_3_24@sint16;
nondet v_call_i_5_25@sint16;
nondet v_call_i_5_1_25@sint16;
nondet v_call_i_5_2_25@sint16;
nondet v_call_i_5_3_25@sint16;
nondet v_call_i_5_26@sint16;
nondet v_call_i_5_1_26@sint16;
nondet v_call_i_5_2_26@sint16;
nondet v_call_i_5_3_26@sint16;
nondet v_call_i_5_27@sint16;
nondet v_call_i_5_1_27@sint16;
nondet v_call_i_5_2_27@sint16;
nondet v_call_i_5_3_27@sint16;
nondet v_call_i_5_28@sint16;
nondet v_call_i_5_1_28@sint16;
nondet v_call_i_5_2_28@sint16;
nondet v_call_i_5_3_28@sint16;
nondet v_call_i_5_29@sint16;
nondet v_call_i_5_1_29@sint16;
nondet v_call_i_5_2_29@sint16;
nondet v_call_i_5_3_29@sint16;
nondet v_call_i_5_30@sint16;
nondet v_call_i_5_1_30@sint16;
nondet v_call_i_5_2_30@sint16;
nondet v_call_i_5_3_30@sint16;
nondet v_call_i_5_31@sint16;
nondet v_call_i_5_1_31@sint16;
nondet v_call_i_5_2_31@sint16;
nondet v_call_i_5_3_31@sint16;
nondet v_call_i_6@sint16;
nondet v_call_i_6_1@sint16;
nondet v_call_i_6_171@sint16;
nondet v_call_i_6_1_1@sint16;
nondet v_call_i_6_2@sint16;
nondet v_call_i_6_1_2@sint16;
nondet v_call_i_6_3@sint16;
nondet v_call_i_6_1_3@sint16;
nondet v_call_i_6_4@sint16;
nondet v_call_i_6_1_4@sint16;
nondet v_call_i_6_5@sint16;
nondet v_call_i_6_1_5@sint16;
nondet v_call_i_6_6@sint16;
nondet v_call_i_6_1_6@sint16;
nondet v_call_i_6_7@sint16;
nondet v_call_i_6_1_7@sint16;
nondet v_call_i_6_8@sint16;
nondet v_call_i_6_1_8@sint16;
nondet v_call_i_6_9@sint16;
nondet v_call_i_6_1_9@sint16;
nondet v_call_i_6_10@sint16;
nondet v_call_i_6_1_10@sint16;
nondet v_call_i_6_11@sint16;
nondet v_call_i_6_1_11@sint16;
nondet v_call_i_6_12@sint16;
nondet v_call_i_6_1_12@sint16;
nondet v_call_i_6_13@sint16;
nondet v_call_i_6_1_13@sint16;
nondet v_call_i_6_14@sint16;
nondet v_call_i_6_1_14@sint16;
nondet v_call_i_6_15@sint16;
nondet v_call_i_6_1_15@sint16;
nondet v_call_i_6_16@sint16;
nondet v_call_i_6_1_16@sint16;
nondet v_call_i_6_17@sint16;
nondet v_call_i_6_1_17@sint16;
nondet v_call_i_6_18@sint16;
nondet v_call_i_6_1_18@sint16;
nondet v_call_i_6_19@sint16;
nondet v_call_i_6_1_19@sint16;
nondet v_call_i_6_20@sint16;
nondet v_call_i_6_1_20@sint16;
nondet v_call_i_6_21@sint16;
nondet v_call_i_6_1_21@sint16;
nondet v_call_i_6_22@sint16;
nondet v_call_i_6_1_22@sint16;
nondet v_call_i_6_23@sint16;
nondet v_call_i_6_1_23@sint16;
nondet v_call_i_6_24@sint16;
nondet v_call_i_6_1_24@sint16;
nondet v_call_i_6_25@sint16;
nondet v_call_i_6_1_25@sint16;
nondet v_call_i_6_26@sint16;
nondet v_call_i_6_1_26@sint16;
nondet v_call_i_6_27@sint16;
nondet v_call_i_6_1_27@sint16;
nondet v_call_i_6_28@sint16;
nondet v_call_i_6_1_28@sint16;
nondet v_call_i_6_29@sint16;
nondet v_call_i_6_1_29@sint16;
nondet v_call_i_6_30@sint16;
nondet v_call_i_6_1_30@sint16;
nondet v_call_i_6_31@sint16;
nondet v_call_i_6_1_31@sint16;
nondet v_call_i_6_32@sint16;
nondet v_call_i_6_1_32@sint16;
nondet v_call_i_6_33@sint16;
nondet v_call_i_6_1_33@sint16;
nondet v_call_i_6_34@sint16;
nondet v_call_i_6_1_34@sint16;
nondet v_call_i_6_35@sint16;
nondet v_call_i_6_1_35@sint16;
nondet v_call_i_6_36@sint16;
nondet v_call_i_6_1_36@sint16;
nondet v_call_i_6_37@sint16;
nondet v_call_i_6_1_37@sint16;
nondet v_call_i_6_38@sint16;
nondet v_call_i_6_1_38@sint16;
nondet v_call_i_6_39@sint16;
nondet v_call_i_6_1_39@sint16;
nondet v_call_i_6_40@sint16;
nondet v_call_i_6_1_40@sint16;
nondet v_call_i_6_41@sint16;
nondet v_call_i_6_1_41@sint16;
nondet v_call_i_6_42@sint16;
nondet v_call_i_6_1_42@sint16;
nondet v_call_i_6_43@sint16;
nondet v_call_i_6_1_43@sint16;
nondet v_call_i_6_44@sint16;
nondet v_call_i_6_1_44@sint16;
nondet v_call_i_6_45@sint16;
nondet v_call_i_6_1_45@sint16;
nondet v_call_i_6_46@sint16;
nondet v_call_i_6_1_46@sint16;
nondet v_call_i_6_47@sint16;
nondet v_call_i_6_1_47@sint16;
nondet v_call_i_6_48@sint16;
nondet v_call_i_6_1_48@sint16;
nondet v_call_i_6_49@sint16;
nondet v_call_i_6_1_49@sint16;
nondet v_call_i_6_50@sint16;
nondet v_call_i_6_1_50@sint16;
nondet v_call_i_6_51@sint16;
nondet v_call_i_6_1_51@sint16;
nondet v_call_i_6_52@sint16;
nondet v_call_i_6_1_52@sint16;
nondet v_call_i_6_53@sint16;
nondet v_call_i_6_1_53@sint16;
nondet v_call_i_6_54@sint16;
nondet v_call_i_6_1_54@sint16;
nondet v_call_i_6_55@sint16;
nondet v_call_i_6_1_55@sint16;
nondet v_call_i_6_56@sint16;
nondet v_call_i_6_1_56@sint16;
nondet v_call_i_6_57@sint16;
nondet v_call_i_6_1_57@sint16;
nondet v_call_i_6_58@sint16;
nondet v_call_i_6_1_58@sint16;
nondet v_call_i_6_59@sint16;
nondet v_call_i_6_1_59@sint16;
nondet v_call_i_6_60@sint16;
nondet v_call_i_6_1_60@sint16;
nondet v_call_i_6_61@sint16;
nondet v_call_i_6_1_61@sint16;
nondet v_call_i_6_62@sint16;
nondet v_call_i_6_1_62@sint16;
nondet v_call_i_6_63@sint16;
nondet v_call_i_6_1_63@sint16;

(*   %arrayidx9 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %0 = load i16, i16* %arrayidx9, align 2, !tbaa !3 *)
mov v0 mem0_256;
(*   %conv1.i = sext i16 %0 to i32 *)
cast v_conv1_i@sint32 v0@sint16;
(*   %mul.i = mul nsw i32 %conv1.i, -758 *)
mul v_mul_i v_conv1_i (-758)@sint32;
(*   %call.i = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i, v_call_i);
(*   %1 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v1 mem0_0;
(*   %sub = sub i16 %1, %call.i *)
sub v_sub v1 v_call_i;
(*   store i16 %sub, i16* %arrayidx9, align 2, !tbaa !3 *)
mov mem0_256 v_sub;
(*   %add21 = add i16 %1, %call.i *)
add v_add21 v1 v_call_i;
(*   store i16 %add21, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21;

(*   %arrayidx9.1286 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %2 = load i16, i16* %arrayidx9.1286, align 2, !tbaa !3 *)
mov v2 mem0_258;
(*   %conv1.i.1287 = sext i16 %2 to i32 *)
cast v_conv1_i_1287@sint32 v2@sint16;
(*   %mul.i.1288 = mul nsw i32 %conv1.i.1287, -758 *)
mul v_mul_i_1288 v_conv1_i_1287 (-758)@sint32;
(*   %call.i.1289 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.1288) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_1288, v_call_i_1289);
(*   %arrayidx11.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %3 = load i16, i16* %arrayidx11.1, align 2, !tbaa !3 *)
mov v3 mem0_2;
(*   %sub.1290 = sub i16 %3, %call.i.1289 *)
sub v_sub_1290 v3 v_call_i_1289;
(*   store i16 %sub.1290, i16* %arrayidx9.1286, align 2, !tbaa !3 *)
mov mem0_258 v_sub_1290;
(*   %add21.1291 = add i16 %3, %call.i.1289 *)
add v_add21_1291 v3 v_call_i_1289;
(*   store i16 %add21.1291, i16* %arrayidx11.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_1291;

(*   %arrayidx9.2293 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %4 = load i16, i16* %arrayidx9.2293, align 2, !tbaa !3 *)
mov v4 mem0_260;
(*   %conv1.i.2294 = sext i16 %4 to i32 *)
cast v_conv1_i_2294@sint32 v4@sint16;
(*   %mul.i.2295 = mul nsw i32 %conv1.i.2294, -758 *)
mul v_mul_i_2295 v_conv1_i_2294 (-758)@sint32;
(*   %call.i.2296 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2295) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2295, v_call_i_2296);
(*   %arrayidx11.2 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %5 = load i16, i16* %arrayidx11.2, align 2, !tbaa !3 *)
mov v5 mem0_4;
(*   %sub.2297 = sub i16 %5, %call.i.2296 *)
sub v_sub_2297 v5 v_call_i_2296;
(*   store i16 %sub.2297, i16* %arrayidx9.2293, align 2, !tbaa !3 *)
mov mem0_260 v_sub_2297;
(*   %add21.2298 = add i16 %5, %call.i.2296 *)
add v_add21_2298 v5 v_call_i_2296;
(*   store i16 %add21.2298, i16* %arrayidx11.2, align 2, !tbaa !3 *)
mov mem0_4 v_add21_2298;

(*   %arrayidx9.3300 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %6 = load i16, i16* %arrayidx9.3300, align 2, !tbaa !3 *)
mov v6 mem0_262;
(*   %conv1.i.3301 = sext i16 %6 to i32 *)
cast v_conv1_i_3301@sint32 v6@sint16;
(*   %mul.i.3302 = mul nsw i32 %conv1.i.3301, -758 *)
mul v_mul_i_3302 v_conv1_i_3301 (-758)@sint32;
(*   %call.i.3303 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.3302) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_3302, v_call_i_3303);
(*   %arrayidx11.3 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %7 = load i16, i16* %arrayidx11.3, align 2, !tbaa !3 *)
mov v7 mem0_6;
(*   %sub.3304 = sub i16 %7, %call.i.3303 *)
sub v_sub_3304 v7 v_call_i_3303;
(*   store i16 %sub.3304, i16* %arrayidx9.3300, align 2, !tbaa !3 *)
mov mem0_262 v_sub_3304;
(*   %add21.3305 = add i16 %7, %call.i.3303 *)
add v_add21_3305 v7 v_call_i_3303;
(*   store i16 %add21.3305, i16* %arrayidx11.3, align 2, !tbaa !3 *)
mov mem0_6 v_add21_3305;

(*   %arrayidx9.4307 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %8 = load i16, i16* %arrayidx9.4307, align 2, !tbaa !3 *)
mov v8 mem0_264;
(*   %conv1.i.4308 = sext i16 %8 to i32 *)
cast v_conv1_i_4308@sint32 v8@sint16;
(*   %mul.i.4309 = mul nsw i32 %conv1.i.4308, -758 *)
mul v_mul_i_4309 v_conv1_i_4308 (-758)@sint32;
(*   %call.i.4310 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.4309) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_4309, v_call_i_4310);
(*   %arrayidx11.4 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %9 = load i16, i16* %arrayidx11.4, align 2, !tbaa !3 *)
mov v9 mem0_8;
(*   %sub.4311 = sub i16 %9, %call.i.4310 *)
sub v_sub_4311 v9 v_call_i_4310;
(*   store i16 %sub.4311, i16* %arrayidx9.4307, align 2, !tbaa !3 *)
mov mem0_264 v_sub_4311;
(*   %add21.4312 = add i16 %9, %call.i.4310 *)
add v_add21_4312 v9 v_call_i_4310;
(*   store i16 %add21.4312, i16* %arrayidx11.4, align 2, !tbaa !3 *)
mov mem0_8 v_add21_4312;

(*   %arrayidx9.5314 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %10 = load i16, i16* %arrayidx9.5314, align 2, !tbaa !3 *)
mov v10 mem0_266;
(*   %conv1.i.5315 = sext i16 %10 to i32 *)
cast v_conv1_i_5315@sint32 v10@sint16;
(*   %mul.i.5316 = mul nsw i32 %conv1.i.5315, -758 *)
mul v_mul_i_5316 v_conv1_i_5315 (-758)@sint32;
(*   %call.i.5317 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.5316) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_5316, v_call_i_5317);
(*   %arrayidx11.5 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %11 = load i16, i16* %arrayidx11.5, align 2, !tbaa !3 *)
mov v11 mem0_10;
(*   %sub.5318 = sub i16 %11, %call.i.5317 *)
sub v_sub_5318 v11 v_call_i_5317;
(*   store i16 %sub.5318, i16* %arrayidx9.5314, align 2, !tbaa !3 *)
mov mem0_266 v_sub_5318;
(*   %add21.5319 = add i16 %11, %call.i.5317 *)
add v_add21_5319 v11 v_call_i_5317;
(*   store i16 %add21.5319, i16* %arrayidx11.5, align 2, !tbaa !3 *)
mov mem0_10 v_add21_5319;

(*   %arrayidx9.6321 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %12 = load i16, i16* %arrayidx9.6321, align 2, !tbaa !3 *)
mov v12 mem0_268;
(*   %conv1.i.6322 = sext i16 %12 to i32 *)
cast v_conv1_i_6322@sint32 v12@sint16;
(*   %mul.i.6323 = mul nsw i32 %conv1.i.6322, -758 *)
mul v_mul_i_6323 v_conv1_i_6322 (-758)@sint32;
(*   %call.i.6324 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6323) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6323, v_call_i_6324);
(*   %arrayidx11.6 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %13 = load i16, i16* %arrayidx11.6, align 2, !tbaa !3 *)
mov v13 mem0_12;
(*   %sub.6325 = sub i16 %13, %call.i.6324 *)
sub v_sub_6325 v13 v_call_i_6324;
(*   store i16 %sub.6325, i16* %arrayidx9.6321, align 2, !tbaa !3 *)
mov mem0_268 v_sub_6325;
(*   %add21.6326 = add i16 %13, %call.i.6324 *)
add v_add21_6326 v13 v_call_i_6324;
(*   store i16 %add21.6326, i16* %arrayidx11.6, align 2, !tbaa !3 *)
mov mem0_12 v_add21_6326;

(*   %arrayidx9.7 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %14 = load i16, i16* %arrayidx9.7, align 2, !tbaa !3 *)
mov v14 mem0_270;
(*   %conv1.i.7 = sext i16 %14 to i32 *)
cast v_conv1_i_7@sint32 v14@sint16;
(*   %mul.i.7 = mul nsw i32 %conv1.i.7, -758 *)
mul v_mul_i_7 v_conv1_i_7 (-758)@sint32;
(*   %call.i.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_7, v_call_i_7);
(*   %arrayidx11.7 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %15 = load i16, i16* %arrayidx11.7, align 2, !tbaa !3 *)
mov v15 mem0_14;
(*   %sub.7 = sub i16 %15, %call.i.7 *)
sub v_sub_7 v15 v_call_i_7;
(*   store i16 %sub.7, i16* %arrayidx9.7, align 2, !tbaa !3 *)
mov mem0_270 v_sub_7;
(*   %add21.7 = add i16 %15, %call.i.7 *)
add v_add21_7 v15 v_call_i_7;
(*   store i16 %add21.7, i16* %arrayidx11.7, align 2, !tbaa !3 *)
mov mem0_14 v_add21_7;

(*   %arrayidx9.8 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %16 = load i16, i16* %arrayidx9.8, align 2, !tbaa !3 *)
mov v16 mem0_272;
(*   %conv1.i.8 = sext i16 %16 to i32 *)
cast v_conv1_i_8@sint32 v16@sint16;
(*   %mul.i.8 = mul nsw i32 %conv1.i.8, -758 *)
mul v_mul_i_8 v_conv1_i_8 (-758)@sint32;
(*   %call.i.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_8, v_call_i_8);
(*   %arrayidx11.8 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %17 = load i16, i16* %arrayidx11.8, align 2, !tbaa !3 *)
mov v17 mem0_16;
(*   %sub.8 = sub i16 %17, %call.i.8 *)
sub v_sub_8 v17 v_call_i_8;
(*   store i16 %sub.8, i16* %arrayidx9.8, align 2, !tbaa !3 *)
mov mem0_272 v_sub_8;
(*   %add21.8 = add i16 %17, %call.i.8 *)
add v_add21_8 v17 v_call_i_8;
(*   store i16 %add21.8, i16* %arrayidx11.8, align 2, !tbaa !3 *)
mov mem0_16 v_add21_8;

(*   %arrayidx9.9 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %18 = load i16, i16* %arrayidx9.9, align 2, !tbaa !3 *)
mov v18 mem0_274;
(*   %conv1.i.9 = sext i16 %18 to i32 *)
cast v_conv1_i_9@sint32 v18@sint16;
(*   %mul.i.9 = mul nsw i32 %conv1.i.9, -758 *)
mul v_mul_i_9 v_conv1_i_9 (-758)@sint32;
(*   %call.i.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_9, v_call_i_9);
(*   %arrayidx11.9 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %19 = load i16, i16* %arrayidx11.9, align 2, !tbaa !3 *)
mov v19 mem0_18;
(*   %sub.9 = sub i16 %19, %call.i.9 *)
sub v_sub_9 v19 v_call_i_9;
(*   store i16 %sub.9, i16* %arrayidx9.9, align 2, !tbaa !3 *)
mov mem0_274 v_sub_9;
(*   %add21.9 = add i16 %19, %call.i.9 *)
add v_add21_9 v19 v_call_i_9;
(*   store i16 %add21.9, i16* %arrayidx11.9, align 2, !tbaa !3 *)
mov mem0_18 v_add21_9;

(*   %arrayidx9.10 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %20 = load i16, i16* %arrayidx9.10, align 2, !tbaa !3 *)
mov v20 mem0_276;
(*   %conv1.i.10 = sext i16 %20 to i32 *)
cast v_conv1_i_10@sint32 v20@sint16;
(*   %mul.i.10 = mul nsw i32 %conv1.i.10, -758 *)
mul v_mul_i_10 v_conv1_i_10 (-758)@sint32;
(*   %call.i.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_10, v_call_i_10);
(*   %arrayidx11.10 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %21 = load i16, i16* %arrayidx11.10, align 2, !tbaa !3 *)
mov v21 mem0_20;
(*   %sub.10 = sub i16 %21, %call.i.10 *)
sub v_sub_10 v21 v_call_i_10;
(*   store i16 %sub.10, i16* %arrayidx9.10, align 2, !tbaa !3 *)
mov mem0_276 v_sub_10;
(*   %add21.10 = add i16 %21, %call.i.10 *)
add v_add21_10 v21 v_call_i_10;
(*   store i16 %add21.10, i16* %arrayidx11.10, align 2, !tbaa !3 *)
mov mem0_20 v_add21_10;
(*   %arrayidx9.11 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %22 = load i16, i16* %arrayidx9.11, align 2, !tbaa !3 *)
mov v22 mem0_278;
(*   %conv1.i.11 = sext i16 %22 to i32 *)
cast v_conv1_i_11@sint32 v22@sint16;
(*   %mul.i.11 = mul nsw i32 %conv1.i.11, -758 *)
mul v_mul_i_11 v_conv1_i_11 (-758)@sint32;
(*   %call.i.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_11, v_call_i_11);
(*   %arrayidx11.11 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %23 = load i16, i16* %arrayidx11.11, align 2, !tbaa !3 *)
mov v23 mem0_22;
(*   %sub.11 = sub i16 %23, %call.i.11 *)
sub v_sub_11 v23 v_call_i_11;
(*   store i16 %sub.11, i16* %arrayidx9.11, align 2, !tbaa !3 *)
mov mem0_278 v_sub_11;
(*   %add21.11 = add i16 %23, %call.i.11 *)
add v_add21_11 v23 v_call_i_11;
(*   store i16 %add21.11, i16* %arrayidx11.11, align 2, !tbaa !3 *)
mov mem0_22 v_add21_11;
(*   %arrayidx9.12 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %24 = load i16, i16* %arrayidx9.12, align 2, !tbaa !3 *)
mov v24 mem0_280;
(*   %conv1.i.12 = sext i16 %24 to i32 *)
cast v_conv1_i_12@sint32 v24@sint16;
(*   %mul.i.12 = mul nsw i32 %conv1.i.12, -758 *)
mul v_mul_i_12 v_conv1_i_12 (-758)@sint32;
(*   %call.i.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_12, v_call_i_12);
(*   %arrayidx11.12 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %25 = load i16, i16* %arrayidx11.12, align 2, !tbaa !3 *)
mov v25 mem0_24;
(*   %sub.12 = sub i16 %25, %call.i.12 *)
sub v_sub_12 v25 v_call_i_12;
(*   store i16 %sub.12, i16* %arrayidx9.12, align 2, !tbaa !3 *)
mov mem0_280 v_sub_12;
(*   %add21.12 = add i16 %25, %call.i.12 *)
add v_add21_12 v25 v_call_i_12;
(*   store i16 %add21.12, i16* %arrayidx11.12, align 2, !tbaa !3 *)
mov mem0_24 v_add21_12;
(*   %arrayidx9.13 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %26 = load i16, i16* %arrayidx9.13, align 2, !tbaa !3 *)
mov v26 mem0_282;
(*   %conv1.i.13 = sext i16 %26 to i32 *)
cast v_conv1_i_13@sint32 v26@sint16;
(*   %mul.i.13 = mul nsw i32 %conv1.i.13, -758 *)
mul v_mul_i_13 v_conv1_i_13 (-758)@sint32;
(*   %call.i.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_13, v_call_i_13);
(*   %arrayidx11.13 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %27 = load i16, i16* %arrayidx11.13, align 2, !tbaa !3 *)
mov v27 mem0_26;
(*   %sub.13 = sub i16 %27, %call.i.13 *)
sub v_sub_13 v27 v_call_i_13;
(*   store i16 %sub.13, i16* %arrayidx9.13, align 2, !tbaa !3 *)
mov mem0_282 v_sub_13;
(*   %add21.13 = add i16 %27, %call.i.13 *)
add v_add21_13 v27 v_call_i_13;
(*   store i16 %add21.13, i16* %arrayidx11.13, align 2, !tbaa !3 *)
mov mem0_26 v_add21_13;
(*   %arrayidx9.14 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %28 = load i16, i16* %arrayidx9.14, align 2, !tbaa !3 *)
mov v28 mem0_284;
(*   %conv1.i.14 = sext i16 %28 to i32 *)
cast v_conv1_i_14@sint32 v28@sint16;
(*   %mul.i.14 = mul nsw i32 %conv1.i.14, -758 *)
mul v_mul_i_14 v_conv1_i_14 (-758)@sint32;
(*   %call.i.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_14, v_call_i_14);
(*   %arrayidx11.14 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %29 = load i16, i16* %arrayidx11.14, align 2, !tbaa !3 *)
mov v29 mem0_28;
(*   %sub.14 = sub i16 %29, %call.i.14 *)
sub v_sub_14 v29 v_call_i_14;
(*   store i16 %sub.14, i16* %arrayidx9.14, align 2, !tbaa !3 *)
mov mem0_284 v_sub_14;
(*   %add21.14 = add i16 %29, %call.i.14 *)
add v_add21_14 v29 v_call_i_14;
(*   store i16 %add21.14, i16* %arrayidx11.14, align 2, !tbaa !3 *)
mov mem0_28 v_add21_14;
(*   %arrayidx9.15 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %30 = load i16, i16* %arrayidx9.15, align 2, !tbaa !3 *)
mov v30 mem0_286;
(*   %conv1.i.15 = sext i16 %30 to i32 *)
cast v_conv1_i_15@sint32 v30@sint16;
(*   %mul.i.15 = mul nsw i32 %conv1.i.15, -758 *)
mul v_mul_i_15 v_conv1_i_15 (-758)@sint32;
(*   %call.i.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_15, v_call_i_15);
(*   %arrayidx11.15 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %31 = load i16, i16* %arrayidx11.15, align 2, !tbaa !3 *)
mov v31 mem0_30;
(*   %sub.15 = sub i16 %31, %call.i.15 *)
sub v_sub_15 v31 v_call_i_15;
(*   store i16 %sub.15, i16* %arrayidx9.15, align 2, !tbaa !3 *)
mov mem0_286 v_sub_15;
(*   %add21.15 = add i16 %31, %call.i.15 *)
add v_add21_15 v31 v_call_i_15;
(*   store i16 %add21.15, i16* %arrayidx11.15, align 2, !tbaa !3 *)
mov mem0_30 v_add21_15;
(*   %arrayidx9.16 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %32 = load i16, i16* %arrayidx9.16, align 2, !tbaa !3 *)
mov v32 mem0_288;
(*   %conv1.i.16 = sext i16 %32 to i32 *)
cast v_conv1_i_16@sint32 v32@sint16;
(*   %mul.i.16 = mul nsw i32 %conv1.i.16, -758 *)
mul v_mul_i_16 v_conv1_i_16 (-758)@sint32;
(*   %call.i.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_16, v_call_i_16);
(*   %arrayidx11.16 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %33 = load i16, i16* %arrayidx11.16, align 2, !tbaa !3 *)
mov v33 mem0_32;
(*   %sub.16 = sub i16 %33, %call.i.16 *)
sub v_sub_16 v33 v_call_i_16;
(*   store i16 %sub.16, i16* %arrayidx9.16, align 2, !tbaa !3 *)
mov mem0_288 v_sub_16;
(*   %add21.16 = add i16 %33, %call.i.16 *)
add v_add21_16 v33 v_call_i_16;
(*   store i16 %add21.16, i16* %arrayidx11.16, align 2, !tbaa !3 *)
mov mem0_32 v_add21_16;
(*   %arrayidx9.17 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %34 = load i16, i16* %arrayidx9.17, align 2, !tbaa !3 *)
mov v34 mem0_290;
(*   %conv1.i.17 = sext i16 %34 to i32 *)
cast v_conv1_i_17@sint32 v34@sint16;
(*   %mul.i.17 = mul nsw i32 %conv1.i.17, -758 *)
mul v_mul_i_17 v_conv1_i_17 (-758)@sint32;
(*   %call.i.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_17, v_call_i_17);
(*   %arrayidx11.17 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %35 = load i16, i16* %arrayidx11.17, align 2, !tbaa !3 *)
mov v35 mem0_34;
(*   %sub.17 = sub i16 %35, %call.i.17 *)
sub v_sub_17 v35 v_call_i_17;
(*   store i16 %sub.17, i16* %arrayidx9.17, align 2, !tbaa !3 *)
mov mem0_290 v_sub_17;
(*   %add21.17 = add i16 %35, %call.i.17 *)
add v_add21_17 v35 v_call_i_17;
(*   store i16 %add21.17, i16* %arrayidx11.17, align 2, !tbaa !3 *)
mov mem0_34 v_add21_17;
(*   %arrayidx9.18 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %36 = load i16, i16* %arrayidx9.18, align 2, !tbaa !3 *)
mov v36 mem0_292;
(*   %conv1.i.18 = sext i16 %36 to i32 *)
cast v_conv1_i_18@sint32 v36@sint16;
(*   %mul.i.18 = mul nsw i32 %conv1.i.18, -758 *)
mul v_mul_i_18 v_conv1_i_18 (-758)@sint32;
(*   %call.i.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_18, v_call_i_18);
(*   %arrayidx11.18 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %37 = load i16, i16* %arrayidx11.18, align 2, !tbaa !3 *)
mov v37 mem0_36;
(*   %sub.18 = sub i16 %37, %call.i.18 *)
sub v_sub_18 v37 v_call_i_18;
(*   store i16 %sub.18, i16* %arrayidx9.18, align 2, !tbaa !3 *)
mov mem0_292 v_sub_18;
(*   %add21.18 = add i16 %37, %call.i.18 *)
add v_add21_18 v37 v_call_i_18;
(*   store i16 %add21.18, i16* %arrayidx11.18, align 2, !tbaa !3 *)
mov mem0_36 v_add21_18;
(*   %arrayidx9.19 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %38 = load i16, i16* %arrayidx9.19, align 2, !tbaa !3 *)
mov v38 mem0_294;
(*   %conv1.i.19 = sext i16 %38 to i32 *)
cast v_conv1_i_19@sint32 v38@sint16;
(*   %mul.i.19 = mul nsw i32 %conv1.i.19, -758 *)
mul v_mul_i_19 v_conv1_i_19 (-758)@sint32;
(*   %call.i.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_19, v_call_i_19);
(*   %arrayidx11.19 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %39 = load i16, i16* %arrayidx11.19, align 2, !tbaa !3 *)
mov v39 mem0_38;
(*   %sub.19 = sub i16 %39, %call.i.19 *)
sub v_sub_19 v39 v_call_i_19;
(*   store i16 %sub.19, i16* %arrayidx9.19, align 2, !tbaa !3 *)
mov mem0_294 v_sub_19;
(*   %add21.19 = add i16 %39, %call.i.19 *)
add v_add21_19 v39 v_call_i_19;
(*   store i16 %add21.19, i16* %arrayidx11.19, align 2, !tbaa !3 *)
mov mem0_38 v_add21_19;
(*   %arrayidx9.20 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %40 = load i16, i16* %arrayidx9.20, align 2, !tbaa !3 *)
mov v40 mem0_296;
(*   %conv1.i.20 = sext i16 %40 to i32 *)
cast v_conv1_i_20@sint32 v40@sint16;
(*   %mul.i.20 = mul nsw i32 %conv1.i.20, -758 *)
mul v_mul_i_20 v_conv1_i_20 (-758)@sint32;
(*   %call.i.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_20, v_call_i_20);
(*   %arrayidx11.20 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %41 = load i16, i16* %arrayidx11.20, align 2, !tbaa !3 *)
mov v41 mem0_40;
(*   %sub.20 = sub i16 %41, %call.i.20 *)
sub v_sub_20 v41 v_call_i_20;
(*   store i16 %sub.20, i16* %arrayidx9.20, align 2, !tbaa !3 *)
mov mem0_296 v_sub_20;
(*   %add21.20 = add i16 %41, %call.i.20 *)
add v_add21_20 v41 v_call_i_20;
(*   store i16 %add21.20, i16* %arrayidx11.20, align 2, !tbaa !3 *)
mov mem0_40 v_add21_20;
(*   %arrayidx9.21 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %42 = load i16, i16* %arrayidx9.21, align 2, !tbaa !3 *)
mov v42 mem0_298;
(*   %conv1.i.21 = sext i16 %42 to i32 *)
cast v_conv1_i_21@sint32 v42@sint16;
(*   %mul.i.21 = mul nsw i32 %conv1.i.21, -758 *)
mul v_mul_i_21 v_conv1_i_21 (-758)@sint32;
(*   %call.i.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_21, v_call_i_21);
(*   %arrayidx11.21 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %43 = load i16, i16* %arrayidx11.21, align 2, !tbaa !3 *)
mov v43 mem0_42;
(*   %sub.21 = sub i16 %43, %call.i.21 *)
sub v_sub_21 v43 v_call_i_21;
(*   store i16 %sub.21, i16* %arrayidx9.21, align 2, !tbaa !3 *)
mov mem0_298 v_sub_21;
(*   %add21.21 = add i16 %43, %call.i.21 *)
add v_add21_21 v43 v_call_i_21;
(*   store i16 %add21.21, i16* %arrayidx11.21, align 2, !tbaa !3 *)
mov mem0_42 v_add21_21;
(*   %arrayidx9.22 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %44 = load i16, i16* %arrayidx9.22, align 2, !tbaa !3 *)
mov v44 mem0_300;
(*   %conv1.i.22 = sext i16 %44 to i32 *)
cast v_conv1_i_22@sint32 v44@sint16;
(*   %mul.i.22 = mul nsw i32 %conv1.i.22, -758 *)
mul v_mul_i_22 v_conv1_i_22 (-758)@sint32;
(*   %call.i.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_22, v_call_i_22);
(*   %arrayidx11.22 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %45 = load i16, i16* %arrayidx11.22, align 2, !tbaa !3 *)
mov v45 mem0_44;
(*   %sub.22 = sub i16 %45, %call.i.22 *)
sub v_sub_22 v45 v_call_i_22;
(*   store i16 %sub.22, i16* %arrayidx9.22, align 2, !tbaa !3 *)
mov mem0_300 v_sub_22;
(*   %add21.22 = add i16 %45, %call.i.22 *)
add v_add21_22 v45 v_call_i_22;
(*   store i16 %add21.22, i16* %arrayidx11.22, align 2, !tbaa !3 *)
mov mem0_44 v_add21_22;
(*   %arrayidx9.23 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %46 = load i16, i16* %arrayidx9.23, align 2, !tbaa !3 *)
mov v46 mem0_302;
(*   %conv1.i.23 = sext i16 %46 to i32 *)
cast v_conv1_i_23@sint32 v46@sint16;
(*   %mul.i.23 = mul nsw i32 %conv1.i.23, -758 *)
mul v_mul_i_23 v_conv1_i_23 (-758)@sint32;
(*   %call.i.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_23, v_call_i_23);
(*   %arrayidx11.23 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %47 = load i16, i16* %arrayidx11.23, align 2, !tbaa !3 *)
mov v47 mem0_46;
(*   %sub.23 = sub i16 %47, %call.i.23 *)
sub v_sub_23 v47 v_call_i_23;
(*   store i16 %sub.23, i16* %arrayidx9.23, align 2, !tbaa !3 *)
mov mem0_302 v_sub_23;
(*   %add21.23 = add i16 %47, %call.i.23 *)
add v_add21_23 v47 v_call_i_23;
(*   store i16 %add21.23, i16* %arrayidx11.23, align 2, !tbaa !3 *)
mov mem0_46 v_add21_23;
(*   %arrayidx9.24 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %48 = load i16, i16* %arrayidx9.24, align 2, !tbaa !3 *)
mov v48 mem0_304;
(*   %conv1.i.24 = sext i16 %48 to i32 *)
cast v_conv1_i_24@sint32 v48@sint16;
(*   %mul.i.24 = mul nsw i32 %conv1.i.24, -758 *)
mul v_mul_i_24 v_conv1_i_24 (-758)@sint32;
(*   %call.i.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_24, v_call_i_24);
(*   %arrayidx11.24 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %49 = load i16, i16* %arrayidx11.24, align 2, !tbaa !3 *)
mov v49 mem0_48;
(*   %sub.24 = sub i16 %49, %call.i.24 *)
sub v_sub_24 v49 v_call_i_24;
(*   store i16 %sub.24, i16* %arrayidx9.24, align 2, !tbaa !3 *)
mov mem0_304 v_sub_24;
(*   %add21.24 = add i16 %49, %call.i.24 *)
add v_add21_24 v49 v_call_i_24;
(*   store i16 %add21.24, i16* %arrayidx11.24, align 2, !tbaa !3 *)
mov mem0_48 v_add21_24;
(*   %arrayidx9.25 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %50 = load i16, i16* %arrayidx9.25, align 2, !tbaa !3 *)
mov v50 mem0_306;
(*   %conv1.i.25 = sext i16 %50 to i32 *)
cast v_conv1_i_25@sint32 v50@sint16;
(*   %mul.i.25 = mul nsw i32 %conv1.i.25, -758 *)
mul v_mul_i_25 v_conv1_i_25 (-758)@sint32;
(*   %call.i.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_25, v_call_i_25);
(*   %arrayidx11.25 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %51 = load i16, i16* %arrayidx11.25, align 2, !tbaa !3 *)
mov v51 mem0_50;
(*   %sub.25 = sub i16 %51, %call.i.25 *)
sub v_sub_25 v51 v_call_i_25;
(*   store i16 %sub.25, i16* %arrayidx9.25, align 2, !tbaa !3 *)
mov mem0_306 v_sub_25;
(*   %add21.25 = add i16 %51, %call.i.25 *)
add v_add21_25 v51 v_call_i_25;
(*   store i16 %add21.25, i16* %arrayidx11.25, align 2, !tbaa !3 *)
mov mem0_50 v_add21_25;
(*   %arrayidx9.26 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %52 = load i16, i16* %arrayidx9.26, align 2, !tbaa !3 *)
mov v52 mem0_308;
(*   %conv1.i.26 = sext i16 %52 to i32 *)
cast v_conv1_i_26@sint32 v52@sint16;
(*   %mul.i.26 = mul nsw i32 %conv1.i.26, -758 *)
mul v_mul_i_26 v_conv1_i_26 (-758)@sint32;
(*   %call.i.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_26, v_call_i_26);
(*   %arrayidx11.26 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %53 = load i16, i16* %arrayidx11.26, align 2, !tbaa !3 *)
mov v53 mem0_52;
(*   %sub.26 = sub i16 %53, %call.i.26 *)
sub v_sub_26 v53 v_call_i_26;
(*   store i16 %sub.26, i16* %arrayidx9.26, align 2, !tbaa !3 *)
mov mem0_308 v_sub_26;
(*   %add21.26 = add i16 %53, %call.i.26 *)
add v_add21_26 v53 v_call_i_26;
(*   store i16 %add21.26, i16* %arrayidx11.26, align 2, !tbaa !3 *)
mov mem0_52 v_add21_26;
(*   %arrayidx9.27 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %54 = load i16, i16* %arrayidx9.27, align 2, !tbaa !3 *)
mov v54 mem0_310;
(*   %conv1.i.27 = sext i16 %54 to i32 *)
cast v_conv1_i_27@sint32 v54@sint16;
(*   %mul.i.27 = mul nsw i32 %conv1.i.27, -758 *)
mul v_mul_i_27 v_conv1_i_27 (-758)@sint32;
(*   %call.i.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_27, v_call_i_27);
(*   %arrayidx11.27 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %55 = load i16, i16* %arrayidx11.27, align 2, !tbaa !3 *)
mov v55 mem0_54;
(*   %sub.27 = sub i16 %55, %call.i.27 *)
sub v_sub_27 v55 v_call_i_27;
(*   store i16 %sub.27, i16* %arrayidx9.27, align 2, !tbaa !3 *)
mov mem0_310 v_sub_27;
(*   %add21.27 = add i16 %55, %call.i.27 *)
add v_add21_27 v55 v_call_i_27;
(*   store i16 %add21.27, i16* %arrayidx11.27, align 2, !tbaa !3 *)
mov mem0_54 v_add21_27;
(*   %arrayidx9.28 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %56 = load i16, i16* %arrayidx9.28, align 2, !tbaa !3 *)
mov v56 mem0_312;
(*   %conv1.i.28 = sext i16 %56 to i32 *)
cast v_conv1_i_28@sint32 v56@sint16;
(*   %mul.i.28 = mul nsw i32 %conv1.i.28, -758 *)
mul v_mul_i_28 v_conv1_i_28 (-758)@sint32;
(*   %call.i.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_28, v_call_i_28);
(*   %arrayidx11.28 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %57 = load i16, i16* %arrayidx11.28, align 2, !tbaa !3 *)
mov v57 mem0_56;
(*   %sub.28 = sub i16 %57, %call.i.28 *)
sub v_sub_28 v57 v_call_i_28;
(*   store i16 %sub.28, i16* %arrayidx9.28, align 2, !tbaa !3 *)
mov mem0_312 v_sub_28;
(*   %add21.28 = add i16 %57, %call.i.28 *)
add v_add21_28 v57 v_call_i_28;
(*   store i16 %add21.28, i16* %arrayidx11.28, align 2, !tbaa !3 *)
mov mem0_56 v_add21_28;
(*   %arrayidx9.29 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %58 = load i16, i16* %arrayidx9.29, align 2, !tbaa !3 *)
mov v58 mem0_314;
(*   %conv1.i.29 = sext i16 %58 to i32 *)
cast v_conv1_i_29@sint32 v58@sint16;
(*   %mul.i.29 = mul nsw i32 %conv1.i.29, -758 *)
mul v_mul_i_29 v_conv1_i_29 (-758)@sint32;
(*   %call.i.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_29, v_call_i_29);
(*   %arrayidx11.29 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %59 = load i16, i16* %arrayidx11.29, align 2, !tbaa !3 *)
mov v59 mem0_58;
(*   %sub.29 = sub i16 %59, %call.i.29 *)
sub v_sub_29 v59 v_call_i_29;
(*   store i16 %sub.29, i16* %arrayidx9.29, align 2, !tbaa !3 *)
mov mem0_314 v_sub_29;
(*   %add21.29 = add i16 %59, %call.i.29 *)
add v_add21_29 v59 v_call_i_29;
(*   store i16 %add21.29, i16* %arrayidx11.29, align 2, !tbaa !3 *)
mov mem0_58 v_add21_29;
(*   %arrayidx9.30 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %60 = load i16, i16* %arrayidx9.30, align 2, !tbaa !3 *)
mov v60 mem0_316;
(*   %conv1.i.30 = sext i16 %60 to i32 *)
cast v_conv1_i_30@sint32 v60@sint16;
(*   %mul.i.30 = mul nsw i32 %conv1.i.30, -758 *)
mul v_mul_i_30 v_conv1_i_30 (-758)@sint32;
(*   %call.i.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_30, v_call_i_30);
(*   %arrayidx11.30 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %61 = load i16, i16* %arrayidx11.30, align 2, !tbaa !3 *)
mov v61 mem0_60;
(*   %sub.30 = sub i16 %61, %call.i.30 *)
sub v_sub_30 v61 v_call_i_30;
(*   store i16 %sub.30, i16* %arrayidx9.30, align 2, !tbaa !3 *)
mov mem0_316 v_sub_30;
(*   %add21.30 = add i16 %61, %call.i.30 *)
add v_add21_30 v61 v_call_i_30;
(*   store i16 %add21.30, i16* %arrayidx11.30, align 2, !tbaa !3 *)
mov mem0_60 v_add21_30;
(*   %arrayidx9.31 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %62 = load i16, i16* %arrayidx9.31, align 2, !tbaa !3 *)
mov v62 mem0_318;
(*   %conv1.i.31 = sext i16 %62 to i32 *)
cast v_conv1_i_31@sint32 v62@sint16;
(*   %mul.i.31 = mul nsw i32 %conv1.i.31, -758 *)
mul v_mul_i_31 v_conv1_i_31 (-758)@sint32;
(*   %call.i.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_31, v_call_i_31);
(*   %arrayidx11.31 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %63 = load i16, i16* %arrayidx11.31, align 2, !tbaa !3 *)
mov v63 mem0_62;
(*   %sub.31 = sub i16 %63, %call.i.31 *)
sub v_sub_31 v63 v_call_i_31;
(*   store i16 %sub.31, i16* %arrayidx9.31, align 2, !tbaa !3 *)
mov mem0_318 v_sub_31;
(*   %add21.31 = add i16 %63, %call.i.31 *)
add v_add21_31 v63 v_call_i_31;
(*   store i16 %add21.31, i16* %arrayidx11.31, align 2, !tbaa !3 *)
mov mem0_62 v_add21_31;
(*   %arrayidx9.32 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %64 = load i16, i16* %arrayidx9.32, align 2, !tbaa !3 *)
mov v64 mem0_320;
(*   %conv1.i.32 = sext i16 %64 to i32 *)
cast v_conv1_i_32@sint32 v64@sint16;
(*   %mul.i.32 = mul nsw i32 %conv1.i.32, -758 *)
mul v_mul_i_32 v_conv1_i_32 (-758)@sint32;
(*   %call.i.32 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.32) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_32, v_call_i_32);
(*   %arrayidx11.32 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %65 = load i16, i16* %arrayidx11.32, align 2, !tbaa !3 *)
mov v65 mem0_64;
(*   %sub.32 = sub i16 %65, %call.i.32 *)
sub v_sub_32 v65 v_call_i_32;
(*   store i16 %sub.32, i16* %arrayidx9.32, align 2, !tbaa !3 *)
mov mem0_320 v_sub_32;
(*   %add21.32 = add i16 %65, %call.i.32 *)
add v_add21_32 v65 v_call_i_32;
(*   store i16 %add21.32, i16* %arrayidx11.32, align 2, !tbaa !3 *)
mov mem0_64 v_add21_32;
(*   %arrayidx9.33 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %66 = load i16, i16* %arrayidx9.33, align 2, !tbaa !3 *)
mov v66 mem0_322;
(*   %conv1.i.33 = sext i16 %66 to i32 *)
cast v_conv1_i_33@sint32 v66@sint16;
(*   %mul.i.33 = mul nsw i32 %conv1.i.33, -758 *)
mul v_mul_i_33 v_conv1_i_33 (-758)@sint32;
(*   %call.i.33 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.33) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_33, v_call_i_33);
(*   %arrayidx11.33 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %67 = load i16, i16* %arrayidx11.33, align 2, !tbaa !3 *)
mov v67 mem0_66;
(*   %sub.33 = sub i16 %67, %call.i.33 *)
sub v_sub_33 v67 v_call_i_33;
(*   store i16 %sub.33, i16* %arrayidx9.33, align 2, !tbaa !3 *)
mov mem0_322 v_sub_33;
(*   %add21.33 = add i16 %67, %call.i.33 *)
add v_add21_33 v67 v_call_i_33;
(*   store i16 %add21.33, i16* %arrayidx11.33, align 2, !tbaa !3 *)
mov mem0_66 v_add21_33;
(*   %arrayidx9.34 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %68 = load i16, i16* %arrayidx9.34, align 2, !tbaa !3 *)
mov v68 mem0_324;
(*   %conv1.i.34 = sext i16 %68 to i32 *)
cast v_conv1_i_34@sint32 v68@sint16;
(*   %mul.i.34 = mul nsw i32 %conv1.i.34, -758 *)
mul v_mul_i_34 v_conv1_i_34 (-758)@sint32;
(*   %call.i.34 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.34) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_34, v_call_i_34);
(*   %arrayidx11.34 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %69 = load i16, i16* %arrayidx11.34, align 2, !tbaa !3 *)
mov v69 mem0_68;
(*   %sub.34 = sub i16 %69, %call.i.34 *)
sub v_sub_34 v69 v_call_i_34;
(*   store i16 %sub.34, i16* %arrayidx9.34, align 2, !tbaa !3 *)
mov mem0_324 v_sub_34;
(*   %add21.34 = add i16 %69, %call.i.34 *)
add v_add21_34 v69 v_call_i_34;
(*   store i16 %add21.34, i16* %arrayidx11.34, align 2, !tbaa !3 *)
mov mem0_68 v_add21_34;
(*   %arrayidx9.35 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %70 = load i16, i16* %arrayidx9.35, align 2, !tbaa !3 *)
mov v70 mem0_326;
(*   %conv1.i.35 = sext i16 %70 to i32 *)
cast v_conv1_i_35@sint32 v70@sint16;
(*   %mul.i.35 = mul nsw i32 %conv1.i.35, -758 *)
mul v_mul_i_35 v_conv1_i_35 (-758)@sint32;
(*   %call.i.35 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.35) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_35, v_call_i_35);
(*   %arrayidx11.35 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %71 = load i16, i16* %arrayidx11.35, align 2, !tbaa !3 *)
mov v71 mem0_70;
(*   %sub.35 = sub i16 %71, %call.i.35 *)
sub v_sub_35 v71 v_call_i_35;
(*   store i16 %sub.35, i16* %arrayidx9.35, align 2, !tbaa !3 *)
mov mem0_326 v_sub_35;
(*   %add21.35 = add i16 %71, %call.i.35 *)
add v_add21_35 v71 v_call_i_35;
(*   store i16 %add21.35, i16* %arrayidx11.35, align 2, !tbaa !3 *)
mov mem0_70 v_add21_35;
(*   %arrayidx9.36 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %72 = load i16, i16* %arrayidx9.36, align 2, !tbaa !3 *)
mov v72 mem0_328;
(*   %conv1.i.36 = sext i16 %72 to i32 *)
cast v_conv1_i_36@sint32 v72@sint16;
(*   %mul.i.36 = mul nsw i32 %conv1.i.36, -758 *)
mul v_mul_i_36 v_conv1_i_36 (-758)@sint32;
(*   %call.i.36 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.36) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_36, v_call_i_36);
(*   %arrayidx11.36 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %73 = load i16, i16* %arrayidx11.36, align 2, !tbaa !3 *)
mov v73 mem0_72;
(*   %sub.36 = sub i16 %73, %call.i.36 *)
sub v_sub_36 v73 v_call_i_36;
(*   store i16 %sub.36, i16* %arrayidx9.36, align 2, !tbaa !3 *)
mov mem0_328 v_sub_36;
(*   %add21.36 = add i16 %73, %call.i.36 *)
add v_add21_36 v73 v_call_i_36;
(*   store i16 %add21.36, i16* %arrayidx11.36, align 2, !tbaa !3 *)
mov mem0_72 v_add21_36;
(*   %arrayidx9.37 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %74 = load i16, i16* %arrayidx9.37, align 2, !tbaa !3 *)
mov v74 mem0_330;
(*   %conv1.i.37 = sext i16 %74 to i32 *)
cast v_conv1_i_37@sint32 v74@sint16;
(*   %mul.i.37 = mul nsw i32 %conv1.i.37, -758 *)
mul v_mul_i_37 v_conv1_i_37 (-758)@sint32;
(*   %call.i.37 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.37) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_37, v_call_i_37);
(*   %arrayidx11.37 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %75 = load i16, i16* %arrayidx11.37, align 2, !tbaa !3 *)
mov v75 mem0_74;
(*   %sub.37 = sub i16 %75, %call.i.37 *)
sub v_sub_37 v75 v_call_i_37;
(*   store i16 %sub.37, i16* %arrayidx9.37, align 2, !tbaa !3 *)
mov mem0_330 v_sub_37;
(*   %add21.37 = add i16 %75, %call.i.37 *)
add v_add21_37 v75 v_call_i_37;
(*   store i16 %add21.37, i16* %arrayidx11.37, align 2, !tbaa !3 *)
mov mem0_74 v_add21_37;
(*   %arrayidx9.38 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %76 = load i16, i16* %arrayidx9.38, align 2, !tbaa !3 *)
mov v76 mem0_332;
(*   %conv1.i.38 = sext i16 %76 to i32 *)
cast v_conv1_i_38@sint32 v76@sint16;
(*   %mul.i.38 = mul nsw i32 %conv1.i.38, -758 *)
mul v_mul_i_38 v_conv1_i_38 (-758)@sint32;
(*   %call.i.38 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.38) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_38, v_call_i_38);
(*   %arrayidx11.38 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %77 = load i16, i16* %arrayidx11.38, align 2, !tbaa !3 *)
mov v77 mem0_76;
(*   %sub.38 = sub i16 %77, %call.i.38 *)
sub v_sub_38 v77 v_call_i_38;
(*   store i16 %sub.38, i16* %arrayidx9.38, align 2, !tbaa !3 *)
mov mem0_332 v_sub_38;
(*   %add21.38 = add i16 %77, %call.i.38 *)
add v_add21_38 v77 v_call_i_38;
(*   store i16 %add21.38, i16* %arrayidx11.38, align 2, !tbaa !3 *)
mov mem0_76 v_add21_38;
(*   %arrayidx9.39 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %78 = load i16, i16* %arrayidx9.39, align 2, !tbaa !3 *)
mov v78 mem0_334;
(*   %conv1.i.39 = sext i16 %78 to i32 *)
cast v_conv1_i_39@sint32 v78@sint16;
(*   %mul.i.39 = mul nsw i32 %conv1.i.39, -758 *)
mul v_mul_i_39 v_conv1_i_39 (-758)@sint32;
(*   %call.i.39 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.39) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_39, v_call_i_39);
(*   %arrayidx11.39 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %79 = load i16, i16* %arrayidx11.39, align 2, !tbaa !3 *)
mov v79 mem0_78;
(*   %sub.39 = sub i16 %79, %call.i.39 *)
sub v_sub_39 v79 v_call_i_39;
(*   store i16 %sub.39, i16* %arrayidx9.39, align 2, !tbaa !3 *)
mov mem0_334 v_sub_39;
(*   %add21.39 = add i16 %79, %call.i.39 *)
add v_add21_39 v79 v_call_i_39;
(*   store i16 %add21.39, i16* %arrayidx11.39, align 2, !tbaa !3 *)
mov mem0_78 v_add21_39;
(*   %arrayidx9.40 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %80 = load i16, i16* %arrayidx9.40, align 2, !tbaa !3 *)
mov v80 mem0_336;
(*   %conv1.i.40 = sext i16 %80 to i32 *)
cast v_conv1_i_40@sint32 v80@sint16;
(*   %mul.i.40 = mul nsw i32 %conv1.i.40, -758 *)
mul v_mul_i_40 v_conv1_i_40 (-758)@sint32;
(*   %call.i.40 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.40) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_40, v_call_i_40);
(*   %arrayidx11.40 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %81 = load i16, i16* %arrayidx11.40, align 2, !tbaa !3 *)
mov v81 mem0_80;
(*   %sub.40 = sub i16 %81, %call.i.40 *)
sub v_sub_40 v81 v_call_i_40;
(*   store i16 %sub.40, i16* %arrayidx9.40, align 2, !tbaa !3 *)
mov mem0_336 v_sub_40;
(*   %add21.40 = add i16 %81, %call.i.40 *)
add v_add21_40 v81 v_call_i_40;
(*   store i16 %add21.40, i16* %arrayidx11.40, align 2, !tbaa !3 *)
mov mem0_80 v_add21_40;
(*   %arrayidx9.41 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %82 = load i16, i16* %arrayidx9.41, align 2, !tbaa !3 *)
mov v82 mem0_338;
(*   %conv1.i.41 = sext i16 %82 to i32 *)
cast v_conv1_i_41@sint32 v82@sint16;
(*   %mul.i.41 = mul nsw i32 %conv1.i.41, -758 *)
mul v_mul_i_41 v_conv1_i_41 (-758)@sint32;
(*   %call.i.41 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.41) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_41, v_call_i_41);
(*   %arrayidx11.41 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %83 = load i16, i16* %arrayidx11.41, align 2, !tbaa !3 *)
mov v83 mem0_82;
(*   %sub.41 = sub i16 %83, %call.i.41 *)
sub v_sub_41 v83 v_call_i_41;
(*   store i16 %sub.41, i16* %arrayidx9.41, align 2, !tbaa !3 *)
mov mem0_338 v_sub_41;
(*   %add21.41 = add i16 %83, %call.i.41 *)
add v_add21_41 v83 v_call_i_41;
(*   store i16 %add21.41, i16* %arrayidx11.41, align 2, !tbaa !3 *)
mov mem0_82 v_add21_41;
(*   %arrayidx9.42 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %84 = load i16, i16* %arrayidx9.42, align 2, !tbaa !3 *)
mov v84 mem0_340;
(*   %conv1.i.42 = sext i16 %84 to i32 *)
cast v_conv1_i_42@sint32 v84@sint16;
(*   %mul.i.42 = mul nsw i32 %conv1.i.42, -758 *)
mul v_mul_i_42 v_conv1_i_42 (-758)@sint32;
(*   %call.i.42 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.42) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_42, v_call_i_42);
(*   %arrayidx11.42 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %85 = load i16, i16* %arrayidx11.42, align 2, !tbaa !3 *)
mov v85 mem0_84;
(*   %sub.42 = sub i16 %85, %call.i.42 *)
sub v_sub_42 v85 v_call_i_42;
(*   store i16 %sub.42, i16* %arrayidx9.42, align 2, !tbaa !3 *)
mov mem0_340 v_sub_42;
(*   %add21.42 = add i16 %85, %call.i.42 *)
add v_add21_42 v85 v_call_i_42;
(*   store i16 %add21.42, i16* %arrayidx11.42, align 2, !tbaa !3 *)
mov mem0_84 v_add21_42;
(*   %arrayidx9.43 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %86 = load i16, i16* %arrayidx9.43, align 2, !tbaa !3 *)
mov v86 mem0_342;
(*   %conv1.i.43 = sext i16 %86 to i32 *)
cast v_conv1_i_43@sint32 v86@sint16;
(*   %mul.i.43 = mul nsw i32 %conv1.i.43, -758 *)
mul v_mul_i_43 v_conv1_i_43 (-758)@sint32;
(*   %call.i.43 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.43) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_43, v_call_i_43);
(*   %arrayidx11.43 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %87 = load i16, i16* %arrayidx11.43, align 2, !tbaa !3 *)
mov v87 mem0_86;
(*   %sub.43 = sub i16 %87, %call.i.43 *)
sub v_sub_43 v87 v_call_i_43;
(*   store i16 %sub.43, i16* %arrayidx9.43, align 2, !tbaa !3 *)
mov mem0_342 v_sub_43;
(*   %add21.43 = add i16 %87, %call.i.43 *)
add v_add21_43 v87 v_call_i_43;
(*   store i16 %add21.43, i16* %arrayidx11.43, align 2, !tbaa !3 *)
mov mem0_86 v_add21_43;
(*   %arrayidx9.44 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %88 = load i16, i16* %arrayidx9.44, align 2, !tbaa !3 *)
mov v88 mem0_344;
(*   %conv1.i.44 = sext i16 %88 to i32 *)
cast v_conv1_i_44@sint32 v88@sint16;
(*   %mul.i.44 = mul nsw i32 %conv1.i.44, -758 *)
mul v_mul_i_44 v_conv1_i_44 (-758)@sint32;
(*   %call.i.44 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.44) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_44, v_call_i_44);
(*   %arrayidx11.44 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %89 = load i16, i16* %arrayidx11.44, align 2, !tbaa !3 *)
mov v89 mem0_88;
(*   %sub.44 = sub i16 %89, %call.i.44 *)
sub v_sub_44 v89 v_call_i_44;
(*   store i16 %sub.44, i16* %arrayidx9.44, align 2, !tbaa !3 *)
mov mem0_344 v_sub_44;
(*   %add21.44 = add i16 %89, %call.i.44 *)
add v_add21_44 v89 v_call_i_44;
(*   store i16 %add21.44, i16* %arrayidx11.44, align 2, !tbaa !3 *)
mov mem0_88 v_add21_44;
(*   %arrayidx9.45 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %90 = load i16, i16* %arrayidx9.45, align 2, !tbaa !3 *)
mov v90 mem0_346;
(*   %conv1.i.45 = sext i16 %90 to i32 *)
cast v_conv1_i_45@sint32 v90@sint16;
(*   %mul.i.45 = mul nsw i32 %conv1.i.45, -758 *)
mul v_mul_i_45 v_conv1_i_45 (-758)@sint32;
(*   %call.i.45 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.45) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_45, v_call_i_45);
(*   %arrayidx11.45 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %91 = load i16, i16* %arrayidx11.45, align 2, !tbaa !3 *)
mov v91 mem0_90;
(*   %sub.45 = sub i16 %91, %call.i.45 *)
sub v_sub_45 v91 v_call_i_45;
(*   store i16 %sub.45, i16* %arrayidx9.45, align 2, !tbaa !3 *)
mov mem0_346 v_sub_45;
(*   %add21.45 = add i16 %91, %call.i.45 *)
add v_add21_45 v91 v_call_i_45;
(*   store i16 %add21.45, i16* %arrayidx11.45, align 2, !tbaa !3 *)
mov mem0_90 v_add21_45;
(*   %arrayidx9.46 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %92 = load i16, i16* %arrayidx9.46, align 2, !tbaa !3 *)
mov v92 mem0_348;
(*   %conv1.i.46 = sext i16 %92 to i32 *)
cast v_conv1_i_46@sint32 v92@sint16;
(*   %mul.i.46 = mul nsw i32 %conv1.i.46, -758 *)
mul v_mul_i_46 v_conv1_i_46 (-758)@sint32;
(*   %call.i.46 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.46) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_46, v_call_i_46);
(*   %arrayidx11.46 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %93 = load i16, i16* %arrayidx11.46, align 2, !tbaa !3 *)
mov v93 mem0_92;
(*   %sub.46 = sub i16 %93, %call.i.46 *)
sub v_sub_46 v93 v_call_i_46;
(*   store i16 %sub.46, i16* %arrayidx9.46, align 2, !tbaa !3 *)
mov mem0_348 v_sub_46;
(*   %add21.46 = add i16 %93, %call.i.46 *)
add v_add21_46 v93 v_call_i_46;
(*   store i16 %add21.46, i16* %arrayidx11.46, align 2, !tbaa !3 *)
mov mem0_92 v_add21_46;
(*   %arrayidx9.47 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %94 = load i16, i16* %arrayidx9.47, align 2, !tbaa !3 *)
mov v94 mem0_350;
(*   %conv1.i.47 = sext i16 %94 to i32 *)
cast v_conv1_i_47@sint32 v94@sint16;
(*   %mul.i.47 = mul nsw i32 %conv1.i.47, -758 *)
mul v_mul_i_47 v_conv1_i_47 (-758)@sint32;
(*   %call.i.47 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.47) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_47, v_call_i_47);
(*   %arrayidx11.47 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %95 = load i16, i16* %arrayidx11.47, align 2, !tbaa !3 *)
mov v95 mem0_94;
(*   %sub.47 = sub i16 %95, %call.i.47 *)
sub v_sub_47 v95 v_call_i_47;
(*   store i16 %sub.47, i16* %arrayidx9.47, align 2, !tbaa !3 *)
mov mem0_350 v_sub_47;
(*   %add21.47 = add i16 %95, %call.i.47 *)
add v_add21_47 v95 v_call_i_47;
(*   store i16 %add21.47, i16* %arrayidx11.47, align 2, !tbaa !3 *)
mov mem0_94 v_add21_47;
(*   %arrayidx9.48 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %96 = load i16, i16* %arrayidx9.48, align 2, !tbaa !3 *)
mov v96 mem0_352;
(*   %conv1.i.48 = sext i16 %96 to i32 *)
cast v_conv1_i_48@sint32 v96@sint16;
(*   %mul.i.48 = mul nsw i32 %conv1.i.48, -758 *)
mul v_mul_i_48 v_conv1_i_48 (-758)@sint32;
(*   %call.i.48 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.48) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_48, v_call_i_48);
(*   %arrayidx11.48 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %97 = load i16, i16* %arrayidx11.48, align 2, !tbaa !3 *)
mov v97 mem0_96;
(*   %sub.48 = sub i16 %97, %call.i.48 *)
sub v_sub_48 v97 v_call_i_48;
(*   store i16 %sub.48, i16* %arrayidx9.48, align 2, !tbaa !3 *)
mov mem0_352 v_sub_48;
(*   %add21.48 = add i16 %97, %call.i.48 *)
add v_add21_48 v97 v_call_i_48;
(*   store i16 %add21.48, i16* %arrayidx11.48, align 2, !tbaa !3 *)
mov mem0_96 v_add21_48;
(*   %arrayidx9.49 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %98 = load i16, i16* %arrayidx9.49, align 2, !tbaa !3 *)
mov v98 mem0_354;
(*   %conv1.i.49 = sext i16 %98 to i32 *)
cast v_conv1_i_49@sint32 v98@sint16;
(*   %mul.i.49 = mul nsw i32 %conv1.i.49, -758 *)
mul v_mul_i_49 v_conv1_i_49 (-758)@sint32;
(*   %call.i.49 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.49) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_49, v_call_i_49);
(*   %arrayidx11.49 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %99 = load i16, i16* %arrayidx11.49, align 2, !tbaa !3 *)
mov v99 mem0_98;
(*   %sub.49 = sub i16 %99, %call.i.49 *)
sub v_sub_49 v99 v_call_i_49;
(*   store i16 %sub.49, i16* %arrayidx9.49, align 2, !tbaa !3 *)
mov mem0_354 v_sub_49;
(*   %add21.49 = add i16 %99, %call.i.49 *)
add v_add21_49 v99 v_call_i_49;
(*   store i16 %add21.49, i16* %arrayidx11.49, align 2, !tbaa !3 *)
mov mem0_98 v_add21_49;
(*   %arrayidx9.50 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %100 = load i16, i16* %arrayidx9.50, align 2, !tbaa !3 *)
mov v100 mem0_356;
(*   %conv1.i.50 = sext i16 %100 to i32 *)
cast v_conv1_i_50@sint32 v100@sint16;
(*   %mul.i.50 = mul nsw i32 %conv1.i.50, -758 *)
mul v_mul_i_50 v_conv1_i_50 (-758)@sint32;
(*   %call.i.50 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.50) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_50, v_call_i_50);
(*   %arrayidx11.50 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %101 = load i16, i16* %arrayidx11.50, align 2, !tbaa !3 *)
mov v101 mem0_100;
(*   %sub.50 = sub i16 %101, %call.i.50 *)
sub v_sub_50 v101 v_call_i_50;
(*   store i16 %sub.50, i16* %arrayidx9.50, align 2, !tbaa !3 *)
mov mem0_356 v_sub_50;
(*   %add21.50 = add i16 %101, %call.i.50 *)
add v_add21_50 v101 v_call_i_50;
(*   store i16 %add21.50, i16* %arrayidx11.50, align 2, !tbaa !3 *)
mov mem0_100 v_add21_50;
(*   %arrayidx9.51 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %102 = load i16, i16* %arrayidx9.51, align 2, !tbaa !3 *)
mov v102 mem0_358;
(*   %conv1.i.51 = sext i16 %102 to i32 *)
cast v_conv1_i_51@sint32 v102@sint16;
(*   %mul.i.51 = mul nsw i32 %conv1.i.51, -758 *)
mul v_mul_i_51 v_conv1_i_51 (-758)@sint32;
(*   %call.i.51 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.51) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_51, v_call_i_51);
(*   %arrayidx11.51 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %103 = load i16, i16* %arrayidx11.51, align 2, !tbaa !3 *)
mov v103 mem0_102;
(*   %sub.51 = sub i16 %103, %call.i.51 *)
sub v_sub_51 v103 v_call_i_51;
(*   store i16 %sub.51, i16* %arrayidx9.51, align 2, !tbaa !3 *)
mov mem0_358 v_sub_51;
(*   %add21.51 = add i16 %103, %call.i.51 *)
add v_add21_51 v103 v_call_i_51;
(*   store i16 %add21.51, i16* %arrayidx11.51, align 2, !tbaa !3 *)
mov mem0_102 v_add21_51;
(*   %arrayidx9.52 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %104 = load i16, i16* %arrayidx9.52, align 2, !tbaa !3 *)
mov v104 mem0_360;
(*   %conv1.i.52 = sext i16 %104 to i32 *)
cast v_conv1_i_52@sint32 v104@sint16;
(*   %mul.i.52 = mul nsw i32 %conv1.i.52, -758 *)
mul v_mul_i_52 v_conv1_i_52 (-758)@sint32;
(*   %call.i.52 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.52) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_52, v_call_i_52);
(*   %arrayidx11.52 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %105 = load i16, i16* %arrayidx11.52, align 2, !tbaa !3 *)
mov v105 mem0_104;
(*   %sub.52 = sub i16 %105, %call.i.52 *)
sub v_sub_52 v105 v_call_i_52;
(*   store i16 %sub.52, i16* %arrayidx9.52, align 2, !tbaa !3 *)
mov mem0_360 v_sub_52;
(*   %add21.52 = add i16 %105, %call.i.52 *)
add v_add21_52 v105 v_call_i_52;
(*   store i16 %add21.52, i16* %arrayidx11.52, align 2, !tbaa !3 *)
mov mem0_104 v_add21_52;
(*   %arrayidx9.53 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %106 = load i16, i16* %arrayidx9.53, align 2, !tbaa !3 *)
mov v106 mem0_362;
(*   %conv1.i.53 = sext i16 %106 to i32 *)
cast v_conv1_i_53@sint32 v106@sint16;
(*   %mul.i.53 = mul nsw i32 %conv1.i.53, -758 *)
mul v_mul_i_53 v_conv1_i_53 (-758)@sint32;
(*   %call.i.53 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.53) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_53, v_call_i_53);
(*   %arrayidx11.53 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %107 = load i16, i16* %arrayidx11.53, align 2, !tbaa !3 *)
mov v107 mem0_106;
(*   %sub.53 = sub i16 %107, %call.i.53 *)
sub v_sub_53 v107 v_call_i_53;
(*   store i16 %sub.53, i16* %arrayidx9.53, align 2, !tbaa !3 *)
mov mem0_362 v_sub_53;
(*   %add21.53 = add i16 %107, %call.i.53 *)
add v_add21_53 v107 v_call_i_53;
(*   store i16 %add21.53, i16* %arrayidx11.53, align 2, !tbaa !3 *)
mov mem0_106 v_add21_53;
(*   %arrayidx9.54 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %108 = load i16, i16* %arrayidx9.54, align 2, !tbaa !3 *)
mov v108 mem0_364;
(*   %conv1.i.54 = sext i16 %108 to i32 *)
cast v_conv1_i_54@sint32 v108@sint16;
(*   %mul.i.54 = mul nsw i32 %conv1.i.54, -758 *)
mul v_mul_i_54 v_conv1_i_54 (-758)@sint32;
(*   %call.i.54 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.54) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_54, v_call_i_54);
(*   %arrayidx11.54 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %109 = load i16, i16* %arrayidx11.54, align 2, !tbaa !3 *)
mov v109 mem0_108;
(*   %sub.54 = sub i16 %109, %call.i.54 *)
sub v_sub_54 v109 v_call_i_54;
(*   store i16 %sub.54, i16* %arrayidx9.54, align 2, !tbaa !3 *)
mov mem0_364 v_sub_54;
(*   %add21.54 = add i16 %109, %call.i.54 *)
add v_add21_54 v109 v_call_i_54;
(*   store i16 %add21.54, i16* %arrayidx11.54, align 2, !tbaa !3 *)
mov mem0_108 v_add21_54;
(*   %arrayidx9.55 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %110 = load i16, i16* %arrayidx9.55, align 2, !tbaa !3 *)
mov v110 mem0_366;
(*   %conv1.i.55 = sext i16 %110 to i32 *)
cast v_conv1_i_55@sint32 v110@sint16;
(*   %mul.i.55 = mul nsw i32 %conv1.i.55, -758 *)
mul v_mul_i_55 v_conv1_i_55 (-758)@sint32;
(*   %call.i.55 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.55) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_55, v_call_i_55);
(*   %arrayidx11.55 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %111 = load i16, i16* %arrayidx11.55, align 2, !tbaa !3 *)
mov v111 mem0_110;
(*   %sub.55 = sub i16 %111, %call.i.55 *)
sub v_sub_55 v111 v_call_i_55;
(*   store i16 %sub.55, i16* %arrayidx9.55, align 2, !tbaa !3 *)
mov mem0_366 v_sub_55;
(*   %add21.55 = add i16 %111, %call.i.55 *)
add v_add21_55 v111 v_call_i_55;
(*   store i16 %add21.55, i16* %arrayidx11.55, align 2, !tbaa !3 *)
mov mem0_110 v_add21_55;
(*   %arrayidx9.56 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %112 = load i16, i16* %arrayidx9.56, align 2, !tbaa !3 *)
mov v112 mem0_368;
(*   %conv1.i.56 = sext i16 %112 to i32 *)
cast v_conv1_i_56@sint32 v112@sint16;
(*   %mul.i.56 = mul nsw i32 %conv1.i.56, -758 *)
mul v_mul_i_56 v_conv1_i_56 (-758)@sint32;
(*   %call.i.56 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.56) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_56, v_call_i_56);
(*   %arrayidx11.56 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %113 = load i16, i16* %arrayidx11.56, align 2, !tbaa !3 *)
mov v113 mem0_112;
(*   %sub.56 = sub i16 %113, %call.i.56 *)
sub v_sub_56 v113 v_call_i_56;
(*   store i16 %sub.56, i16* %arrayidx9.56, align 2, !tbaa !3 *)
mov mem0_368 v_sub_56;
(*   %add21.56 = add i16 %113, %call.i.56 *)
add v_add21_56 v113 v_call_i_56;
(*   store i16 %add21.56, i16* %arrayidx11.56, align 2, !tbaa !3 *)
mov mem0_112 v_add21_56;
(*   %arrayidx9.57 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %114 = load i16, i16* %arrayidx9.57, align 2, !tbaa !3 *)
mov v114 mem0_370;
(*   %conv1.i.57 = sext i16 %114 to i32 *)
cast v_conv1_i_57@sint32 v114@sint16;
(*   %mul.i.57 = mul nsw i32 %conv1.i.57, -758 *)
mul v_mul_i_57 v_conv1_i_57 (-758)@sint32;
(*   %call.i.57 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.57) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_57, v_call_i_57);
(*   %arrayidx11.57 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %115 = load i16, i16* %arrayidx11.57, align 2, !tbaa !3 *)
mov v115 mem0_114;
(*   %sub.57 = sub i16 %115, %call.i.57 *)
sub v_sub_57 v115 v_call_i_57;
(*   store i16 %sub.57, i16* %arrayidx9.57, align 2, !tbaa !3 *)
mov mem0_370 v_sub_57;
(*   %add21.57 = add i16 %115, %call.i.57 *)
add v_add21_57 v115 v_call_i_57;
(*   store i16 %add21.57, i16* %arrayidx11.57, align 2, !tbaa !3 *)
mov mem0_114 v_add21_57;
(*   %arrayidx9.58 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %116 = load i16, i16* %arrayidx9.58, align 2, !tbaa !3 *)
mov v116 mem0_372;
(*   %conv1.i.58 = sext i16 %116 to i32 *)
cast v_conv1_i_58@sint32 v116@sint16;
(*   %mul.i.58 = mul nsw i32 %conv1.i.58, -758 *)
mul v_mul_i_58 v_conv1_i_58 (-758)@sint32;
(*   %call.i.58 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.58) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_58, v_call_i_58);
(*   %arrayidx11.58 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %117 = load i16, i16* %arrayidx11.58, align 2, !tbaa !3 *)
mov v117 mem0_116;
(*   %sub.58 = sub i16 %117, %call.i.58 *)
sub v_sub_58 v117 v_call_i_58;
(*   store i16 %sub.58, i16* %arrayidx9.58, align 2, !tbaa !3 *)
mov mem0_372 v_sub_58;
(*   %add21.58 = add i16 %117, %call.i.58 *)
add v_add21_58 v117 v_call_i_58;
(*   store i16 %add21.58, i16* %arrayidx11.58, align 2, !tbaa !3 *)
mov mem0_116 v_add21_58;
(*   %arrayidx9.59 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %118 = load i16, i16* %arrayidx9.59, align 2, !tbaa !3 *)
mov v118 mem0_374;
(*   %conv1.i.59 = sext i16 %118 to i32 *)
cast v_conv1_i_59@sint32 v118@sint16;
(*   %mul.i.59 = mul nsw i32 %conv1.i.59, -758 *)
mul v_mul_i_59 v_conv1_i_59 (-758)@sint32;
(*   %call.i.59 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.59) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_59, v_call_i_59);
(*   %arrayidx11.59 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %119 = load i16, i16* %arrayidx11.59, align 2, !tbaa !3 *)
mov v119 mem0_118;
(*   %sub.59 = sub i16 %119, %call.i.59 *)
sub v_sub_59 v119 v_call_i_59;
(*   store i16 %sub.59, i16* %arrayidx9.59, align 2, !tbaa !3 *)
mov mem0_374 v_sub_59;
(*   %add21.59 = add i16 %119, %call.i.59 *)
add v_add21_59 v119 v_call_i_59;
(*   store i16 %add21.59, i16* %arrayidx11.59, align 2, !tbaa !3 *)
mov mem0_118 v_add21_59;
(*   %arrayidx9.60 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %120 = load i16, i16* %arrayidx9.60, align 2, !tbaa !3 *)
mov v120 mem0_376;
(*   %conv1.i.60 = sext i16 %120 to i32 *)
cast v_conv1_i_60@sint32 v120@sint16;
(*   %mul.i.60 = mul nsw i32 %conv1.i.60, -758 *)
mul v_mul_i_60 v_conv1_i_60 (-758)@sint32;
(*   %call.i.60 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.60) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_60, v_call_i_60);
(*   %arrayidx11.60 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %121 = load i16, i16* %arrayidx11.60, align 2, !tbaa !3 *)
mov v121 mem0_120;
(*   %sub.60 = sub i16 %121, %call.i.60 *)
sub v_sub_60 v121 v_call_i_60;
(*   store i16 %sub.60, i16* %arrayidx9.60, align 2, !tbaa !3 *)
mov mem0_376 v_sub_60;
(*   %add21.60 = add i16 %121, %call.i.60 *)
add v_add21_60 v121 v_call_i_60;
(*   store i16 %add21.60, i16* %arrayidx11.60, align 2, !tbaa !3 *)
mov mem0_120 v_add21_60;
(*   %arrayidx9.61 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %122 = load i16, i16* %arrayidx9.61, align 2, !tbaa !3 *)
mov v122 mem0_378;
(*   %conv1.i.61 = sext i16 %122 to i32 *)
cast v_conv1_i_61@sint32 v122@sint16;
(*   %mul.i.61 = mul nsw i32 %conv1.i.61, -758 *)
mul v_mul_i_61 v_conv1_i_61 (-758)@sint32;
(*   %call.i.61 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.61) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_61, v_call_i_61);
(*   %arrayidx11.61 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %123 = load i16, i16* %arrayidx11.61, align 2, !tbaa !3 *)
mov v123 mem0_122;
(*   %sub.61 = sub i16 %123, %call.i.61 *)
sub v_sub_61 v123 v_call_i_61;
(*   store i16 %sub.61, i16* %arrayidx9.61, align 2, !tbaa !3 *)
mov mem0_378 v_sub_61;
(*   %add21.61 = add i16 %123, %call.i.61 *)
add v_add21_61 v123 v_call_i_61;
(*   store i16 %add21.61, i16* %arrayidx11.61, align 2, !tbaa !3 *)
mov mem0_122 v_add21_61;
(*   %arrayidx9.62 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %124 = load i16, i16* %arrayidx9.62, align 2, !tbaa !3 *)
mov v124 mem0_380;
(*   %conv1.i.62 = sext i16 %124 to i32 *)
cast v_conv1_i_62@sint32 v124@sint16;
(*   %mul.i.62 = mul nsw i32 %conv1.i.62, -758 *)
mul v_mul_i_62 v_conv1_i_62 (-758)@sint32;
(*   %call.i.62 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.62) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_62, v_call_i_62);
(*   %arrayidx11.62 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %125 = load i16, i16* %arrayidx11.62, align 2, !tbaa !3 *)
mov v125 mem0_124;
(*   %sub.62 = sub i16 %125, %call.i.62 *)
sub v_sub_62 v125 v_call_i_62;
(*   store i16 %sub.62, i16* %arrayidx9.62, align 2, !tbaa !3 *)
mov mem0_380 v_sub_62;
(*   %add21.62 = add i16 %125, %call.i.62 *)
add v_add21_62 v125 v_call_i_62;
(*   store i16 %add21.62, i16* %arrayidx11.62, align 2, !tbaa !3 *)
mov mem0_124 v_add21_62;
(*   %arrayidx9.63 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %126 = load i16, i16* %arrayidx9.63, align 2, !tbaa !3 *)
mov v126 mem0_382;
(*   %conv1.i.63 = sext i16 %126 to i32 *)
cast v_conv1_i_63@sint32 v126@sint16;
(*   %mul.i.63 = mul nsw i32 %conv1.i.63, -758 *)
mul v_mul_i_63 v_conv1_i_63 (-758)@sint32;
(*   %call.i.63 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.63) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_63, v_call_i_63);
(*   %arrayidx11.63 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %127 = load i16, i16* %arrayidx11.63, align 2, !tbaa !3 *)
mov v127 mem0_126;
(*   %sub.63 = sub i16 %127, %call.i.63 *)
sub v_sub_63 v127 v_call_i_63;
(*   store i16 %sub.63, i16* %arrayidx9.63, align 2, !tbaa !3 *)
mov mem0_382 v_sub_63;
(*   %add21.63 = add i16 %127, %call.i.63 *)
add v_add21_63 v127 v_call_i_63;
(*   store i16 %add21.63, i16* %arrayidx11.63, align 2, !tbaa !3 *)
mov mem0_126 v_add21_63;

(*   %arrayidx9.64 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %128 = load i16, i16* %arrayidx9.64, align 2, !tbaa !3 *)
mov v128 mem0_384;
(*   %conv1.i.64 = sext i16 %128 to i32 *)
cast v_conv1_i_64@sint32 v128@sint16;
(*   %mul.i.64 = mul nsw i32 %conv1.i.64, -758 *)
mul v_mul_i_64 v_conv1_i_64 (-758)@sint32;
(*   %call.i.64 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.64) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_64, v_call_i_64);
(*   %arrayidx11.64 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %129 = load i16, i16* %arrayidx11.64, align 2, !tbaa !3 *)
mov v129 mem0_128;
(*   %sub.64 = sub i16 %129, %call.i.64 *)
sub v_sub_64 v129 v_call_i_64;
(*   store i16 %sub.64, i16* %arrayidx9.64, align 2, !tbaa !3 *)
mov mem0_384 v_sub_64;
(*   %add21.64 = add i16 %129, %call.i.64 *)
add v_add21_64 v129 v_call_i_64;
(*   store i16 %add21.64, i16* %arrayidx11.64, align 2, !tbaa !3 *)
mov mem0_128 v_add21_64;

(*   %arrayidx9.65 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %130 = load i16, i16* %arrayidx9.65, align 2, !tbaa !3 *)
mov v130 mem0_386;
(*   %conv1.i.65 = sext i16 %130 to i32 *)
cast v_conv1_i_65@sint32 v130@sint16;
(*   %mul.i.65 = mul nsw i32 %conv1.i.65, -758 *)
mul v_mul_i_65 v_conv1_i_65 (-758)@sint32;
(*   %call.i.65 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.65) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_65, v_call_i_65);
(*   %arrayidx11.65 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %131 = load i16, i16* %arrayidx11.65, align 2, !tbaa !3 *)
mov v131 mem0_130;
(*   %sub.65 = sub i16 %131, %call.i.65 *)
sub v_sub_65 v131 v_call_i_65;
(*   store i16 %sub.65, i16* %arrayidx9.65, align 2, !tbaa !3 *)
mov mem0_386 v_sub_65;
(*   %add21.65 = add i16 %131, %call.i.65 *)
add v_add21_65 v131 v_call_i_65;
(*   store i16 %add21.65, i16* %arrayidx11.65, align 2, !tbaa !3 *)
mov mem0_130 v_add21_65;
(*   %arrayidx9.66 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %132 = load i16, i16* %arrayidx9.66, align 2, !tbaa !3 *)
mov v132 mem0_388;
(*   %conv1.i.66 = sext i16 %132 to i32 *)
cast v_conv1_i_66@sint32 v132@sint16;
(*   %mul.i.66 = mul nsw i32 %conv1.i.66, -758 *)
mul v_mul_i_66 v_conv1_i_66 (-758)@sint32;
(*   %call.i.66 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.66) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_66, v_call_i_66);
(*   %arrayidx11.66 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %133 = load i16, i16* %arrayidx11.66, align 2, !tbaa !3 *)
mov v133 mem0_132;
(*   %sub.66 = sub i16 %133, %call.i.66 *)
sub v_sub_66 v133 v_call_i_66;
(*   store i16 %sub.66, i16* %arrayidx9.66, align 2, !tbaa !3 *)
mov mem0_388 v_sub_66;
(*   %add21.66 = add i16 %133, %call.i.66 *)
add v_add21_66 v133 v_call_i_66;
(*   store i16 %add21.66, i16* %arrayidx11.66, align 2, !tbaa !3 *)
mov mem0_132 v_add21_66;
(*   %arrayidx9.67 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %134 = load i16, i16* %arrayidx9.67, align 2, !tbaa !3 *)
mov v134 mem0_390;
(*   %conv1.i.67 = sext i16 %134 to i32 *)
cast v_conv1_i_67@sint32 v134@sint16;
(*   %mul.i.67 = mul nsw i32 %conv1.i.67, -758 *)
mul v_mul_i_67 v_conv1_i_67 (-758)@sint32;
(*   %call.i.67 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.67) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_67, v_call_i_67);
(*   %arrayidx11.67 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %135 = load i16, i16* %arrayidx11.67, align 2, !tbaa !3 *)
mov v135 mem0_134;
(*   %sub.67 = sub i16 %135, %call.i.67 *)
sub v_sub_67 v135 v_call_i_67;
(*   store i16 %sub.67, i16* %arrayidx9.67, align 2, !tbaa !3 *)
mov mem0_390 v_sub_67;
(*   %add21.67 = add i16 %135, %call.i.67 *)
add v_add21_67 v135 v_call_i_67;
(*   store i16 %add21.67, i16* %arrayidx11.67, align 2, !tbaa !3 *)
mov mem0_134 v_add21_67;
(*   %arrayidx9.68 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %136 = load i16, i16* %arrayidx9.68, align 2, !tbaa !3 *)
mov v136 mem0_392;
(*   %conv1.i.68 = sext i16 %136 to i32 *)
cast v_conv1_i_68@sint32 v136@sint16;
(*   %mul.i.68 = mul nsw i32 %conv1.i.68, -758 *)
mul v_mul_i_68 v_conv1_i_68 (-758)@sint32;
(*   %call.i.68 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.68) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_68, v_call_i_68);
(*   %arrayidx11.68 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %137 = load i16, i16* %arrayidx11.68, align 2, !tbaa !3 *)
mov v137 mem0_136;
(*   %sub.68 = sub i16 %137, %call.i.68 *)
sub v_sub_68 v137 v_call_i_68;
(*   store i16 %sub.68, i16* %arrayidx9.68, align 2, !tbaa !3 *)
mov mem0_392 v_sub_68;
(*   %add21.68 = add i16 %137, %call.i.68 *)
add v_add21_68 v137 v_call_i_68;
(*   store i16 %add21.68, i16* %arrayidx11.68, align 2, !tbaa !3 *)
mov mem0_136 v_add21_68;
(*   %arrayidx9.69 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %138 = load i16, i16* %arrayidx9.69, align 2, !tbaa !3 *)
mov v138 mem0_394;
(*   %conv1.i.69 = sext i16 %138 to i32 *)
cast v_conv1_i_69@sint32 v138@sint16;
(*   %mul.i.69 = mul nsw i32 %conv1.i.69, -758 *)
mul v_mul_i_69 v_conv1_i_69 (-758)@sint32;
(*   %call.i.69 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.69) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_69, v_call_i_69);
(*   %arrayidx11.69 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %139 = load i16, i16* %arrayidx11.69, align 2, !tbaa !3 *)
mov v139 mem0_138;
(*   %sub.69 = sub i16 %139, %call.i.69 *)
sub v_sub_69 v139 v_call_i_69;
(*   store i16 %sub.69, i16* %arrayidx9.69, align 2, !tbaa !3 *)
mov mem0_394 v_sub_69;
(*   %add21.69 = add i16 %139, %call.i.69 *)
add v_add21_69 v139 v_call_i_69;
(*   store i16 %add21.69, i16* %arrayidx11.69, align 2, !tbaa !3 *)
mov mem0_138 v_add21_69;
(*   %arrayidx9.70 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %140 = load i16, i16* %arrayidx9.70, align 2, !tbaa !3 *)
mov v140 mem0_396;
(*   %conv1.i.70 = sext i16 %140 to i32 *)
cast v_conv1_i_70@sint32 v140@sint16;
(*   %mul.i.70 = mul nsw i32 %conv1.i.70, -758 *)
mul v_mul_i_70 v_conv1_i_70 (-758)@sint32;
(*   %call.i.70 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.70) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_70, v_call_i_70);
(*   %arrayidx11.70 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %141 = load i16, i16* %arrayidx11.70, align 2, !tbaa !3 *)
mov v141 mem0_140;
(*   %sub.70 = sub i16 %141, %call.i.70 *)
sub v_sub_70 v141 v_call_i_70;
(*   store i16 %sub.70, i16* %arrayidx9.70, align 2, !tbaa !3 *)
mov mem0_396 v_sub_70;
(*   %add21.70 = add i16 %141, %call.i.70 *)
add v_add21_70 v141 v_call_i_70;
(*   store i16 %add21.70, i16* %arrayidx11.70, align 2, !tbaa !3 *)
mov mem0_140 v_add21_70;
(*   %arrayidx9.71 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %142 = load i16, i16* %arrayidx9.71, align 2, !tbaa !3 *)
mov v142 mem0_398;
(*   %conv1.i.71 = sext i16 %142 to i32 *)
cast v_conv1_i_71@sint32 v142@sint16;
(*   %mul.i.71 = mul nsw i32 %conv1.i.71, -758 *)
mul v_mul_i_71 v_conv1_i_71 (-758)@sint32;
(*   %call.i.71 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.71) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_71, v_call_i_71);
(*   %arrayidx11.71 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %143 = load i16, i16* %arrayidx11.71, align 2, !tbaa !3 *)
mov v143 mem0_142;
(*   %sub.71 = sub i16 %143, %call.i.71 *)
sub v_sub_71 v143 v_call_i_71;
(*   store i16 %sub.71, i16* %arrayidx9.71, align 2, !tbaa !3 *)
mov mem0_398 v_sub_71;
(*   %add21.71 = add i16 %143, %call.i.71 *)
add v_add21_71 v143 v_call_i_71;
(*   store i16 %add21.71, i16* %arrayidx11.71, align 2, !tbaa !3 *)
mov mem0_142 v_add21_71;
(*   %arrayidx9.72 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %144 = load i16, i16* %arrayidx9.72, align 2, !tbaa !3 *)
mov v144 mem0_400;
(*   %conv1.i.72 = sext i16 %144 to i32 *)
cast v_conv1_i_72@sint32 v144@sint16;
(*   %mul.i.72 = mul nsw i32 %conv1.i.72, -758 *)
mul v_mul_i_72 v_conv1_i_72 (-758)@sint32;
(*   %call.i.72 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.72) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_72, v_call_i_72);
(*   %arrayidx11.72 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %145 = load i16, i16* %arrayidx11.72, align 2, !tbaa !3 *)
mov v145 mem0_144;
(*   %sub.72 = sub i16 %145, %call.i.72 *)
sub v_sub_72 v145 v_call_i_72;
(*   store i16 %sub.72, i16* %arrayidx9.72, align 2, !tbaa !3 *)
mov mem0_400 v_sub_72;
(*   %add21.72 = add i16 %145, %call.i.72 *)
add v_add21_72 v145 v_call_i_72;
(*   store i16 %add21.72, i16* %arrayidx11.72, align 2, !tbaa !3 *)
mov mem0_144 v_add21_72;
(*   %arrayidx9.73 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %146 = load i16, i16* %arrayidx9.73, align 2, !tbaa !3 *)
mov v146 mem0_402;
(*   %conv1.i.73 = sext i16 %146 to i32 *)
cast v_conv1_i_73@sint32 v146@sint16;
(*   %mul.i.73 = mul nsw i32 %conv1.i.73, -758 *)
mul v_mul_i_73 v_conv1_i_73 (-758)@sint32;
(*   %call.i.73 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.73) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_73, v_call_i_73);
(*   %arrayidx11.73 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %147 = load i16, i16* %arrayidx11.73, align 2, !tbaa !3 *)
mov v147 mem0_146;
(*   %sub.73 = sub i16 %147, %call.i.73 *)
sub v_sub_73 v147 v_call_i_73;
(*   store i16 %sub.73, i16* %arrayidx9.73, align 2, !tbaa !3 *)
mov mem0_402 v_sub_73;
(*   %add21.73 = add i16 %147, %call.i.73 *)
add v_add21_73 v147 v_call_i_73;
(*   store i16 %add21.73, i16* %arrayidx11.73, align 2, !tbaa !3 *)
mov mem0_146 v_add21_73;
(*   %arrayidx9.74 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %148 = load i16, i16* %arrayidx9.74, align 2, !tbaa !3 *)
mov v148 mem0_404;
(*   %conv1.i.74 = sext i16 %148 to i32 *)
cast v_conv1_i_74@sint32 v148@sint16;
(*   %mul.i.74 = mul nsw i32 %conv1.i.74, -758 *)
mul v_mul_i_74 v_conv1_i_74 (-758)@sint32;
(*   %call.i.74 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.74) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_74, v_call_i_74);
(*   %arrayidx11.74 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %149 = load i16, i16* %arrayidx11.74, align 2, !tbaa !3 *)
mov v149 mem0_148;
(*   %sub.74 = sub i16 %149, %call.i.74 *)
sub v_sub_74 v149 v_call_i_74;
(*   store i16 %sub.74, i16* %arrayidx9.74, align 2, !tbaa !3 *)
mov mem0_404 v_sub_74;
(*   %add21.74 = add i16 %149, %call.i.74 *)
add v_add21_74 v149 v_call_i_74;
(*   store i16 %add21.74, i16* %arrayidx11.74, align 2, !tbaa !3 *)
mov mem0_148 v_add21_74;
(*   %arrayidx9.75 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %150 = load i16, i16* %arrayidx9.75, align 2, !tbaa !3 *)
mov v150 mem0_406;
(*   %conv1.i.75 = sext i16 %150 to i32 *)
cast v_conv1_i_75@sint32 v150@sint16;
(*   %mul.i.75 = mul nsw i32 %conv1.i.75, -758 *)
mul v_mul_i_75 v_conv1_i_75 (-758)@sint32;
(*   %call.i.75 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.75) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_75, v_call_i_75);
(*   %arrayidx11.75 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %151 = load i16, i16* %arrayidx11.75, align 2, !tbaa !3 *)
mov v151 mem0_150;
(*   %sub.75 = sub i16 %151, %call.i.75 *)
sub v_sub_75 v151 v_call_i_75;
(*   store i16 %sub.75, i16* %arrayidx9.75, align 2, !tbaa !3 *)
mov mem0_406 v_sub_75;
(*   %add21.75 = add i16 %151, %call.i.75 *)
add v_add21_75 v151 v_call_i_75;
(*   store i16 %add21.75, i16* %arrayidx11.75, align 2, !tbaa !3 *)
mov mem0_150 v_add21_75;
(*   %arrayidx9.76 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %152 = load i16, i16* %arrayidx9.76, align 2, !tbaa !3 *)
mov v152 mem0_408;
(*   %conv1.i.76 = sext i16 %152 to i32 *)
cast v_conv1_i_76@sint32 v152@sint16;
(*   %mul.i.76 = mul nsw i32 %conv1.i.76, -758 *)
mul v_mul_i_76 v_conv1_i_76 (-758)@sint32;
(*   %call.i.76 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.76) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_76, v_call_i_76);
(*   %arrayidx11.76 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %153 = load i16, i16* %arrayidx11.76, align 2, !tbaa !3 *)
mov v153 mem0_152;
(*   %sub.76 = sub i16 %153, %call.i.76 *)
sub v_sub_76 v153 v_call_i_76;
(*   store i16 %sub.76, i16* %arrayidx9.76, align 2, !tbaa !3 *)
mov mem0_408 v_sub_76;
(*   %add21.76 = add i16 %153, %call.i.76 *)
add v_add21_76 v153 v_call_i_76;
(*   store i16 %add21.76, i16* %arrayidx11.76, align 2, !tbaa !3 *)
mov mem0_152 v_add21_76;
(*   %arrayidx9.77 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %154 = load i16, i16* %arrayidx9.77, align 2, !tbaa !3 *)
mov v154 mem0_410;
(*   %conv1.i.77 = sext i16 %154 to i32 *)
cast v_conv1_i_77@sint32 v154@sint16;
(*   %mul.i.77 = mul nsw i32 %conv1.i.77, -758 *)
mul v_mul_i_77 v_conv1_i_77 (-758)@sint32;
(*   %call.i.77 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.77) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_77, v_call_i_77);
(*   %arrayidx11.77 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %155 = load i16, i16* %arrayidx11.77, align 2, !tbaa !3 *)
mov v155 mem0_154;
(*   %sub.77 = sub i16 %155, %call.i.77 *)
sub v_sub_77 v155 v_call_i_77;
(*   store i16 %sub.77, i16* %arrayidx9.77, align 2, !tbaa !3 *)
mov mem0_410 v_sub_77;
(*   %add21.77 = add i16 %155, %call.i.77 *)
add v_add21_77 v155 v_call_i_77;
(*   store i16 %add21.77, i16* %arrayidx11.77, align 2, !tbaa !3 *)
mov mem0_154 v_add21_77;
(*   %arrayidx9.78 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %156 = load i16, i16* %arrayidx9.78, align 2, !tbaa !3 *)
mov v156 mem0_412;
(*   %conv1.i.78 = sext i16 %156 to i32 *)
cast v_conv1_i_78@sint32 v156@sint16;
(*   %mul.i.78 = mul nsw i32 %conv1.i.78, -758 *)
mul v_mul_i_78 v_conv1_i_78 (-758)@sint32;
(*   %call.i.78 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.78) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_78, v_call_i_78);
(*   %arrayidx11.78 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %157 = load i16, i16* %arrayidx11.78, align 2, !tbaa !3 *)
mov v157 mem0_156;
(*   %sub.78 = sub i16 %157, %call.i.78 *)
sub v_sub_78 v157 v_call_i_78;
(*   store i16 %sub.78, i16* %arrayidx9.78, align 2, !tbaa !3 *)
mov mem0_412 v_sub_78;
(*   %add21.78 = add i16 %157, %call.i.78 *)
add v_add21_78 v157 v_call_i_78;
(*   store i16 %add21.78, i16* %arrayidx11.78, align 2, !tbaa !3 *)
mov mem0_156 v_add21_78;
(*   %arrayidx9.79 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %158 = load i16, i16* %arrayidx9.79, align 2, !tbaa !3 *)
mov v158 mem0_414;
(*   %conv1.i.79 = sext i16 %158 to i32 *)
cast v_conv1_i_79@sint32 v158@sint16;
(*   %mul.i.79 = mul nsw i32 %conv1.i.79, -758 *)
mul v_mul_i_79 v_conv1_i_79 (-758)@sint32;
(*   %call.i.79 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.79) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_79, v_call_i_79);
(*   %arrayidx11.79 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %159 = load i16, i16* %arrayidx11.79, align 2, !tbaa !3 *)
mov v159 mem0_158;
(*   %sub.79 = sub i16 %159, %call.i.79 *)
sub v_sub_79 v159 v_call_i_79;
(*   store i16 %sub.79, i16* %arrayidx9.79, align 2, !tbaa !3 *)
mov mem0_414 v_sub_79;
(*   %add21.79 = add i16 %159, %call.i.79 *)
add v_add21_79 v159 v_call_i_79;
(*   store i16 %add21.79, i16* %arrayidx11.79, align 2, !tbaa !3 *)
mov mem0_158 v_add21_79;
(*   %arrayidx9.80 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %160 = load i16, i16* %arrayidx9.80, align 2, !tbaa !3 *)
mov v160 mem0_416;
(*   %conv1.i.80 = sext i16 %160 to i32 *)
cast v_conv1_i_80@sint32 v160@sint16;
(*   %mul.i.80 = mul nsw i32 %conv1.i.80, -758 *)
mul v_mul_i_80 v_conv1_i_80 (-758)@sint32;
(*   %call.i.80 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.80) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_80, v_call_i_80);
(*   %arrayidx11.80 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %161 = load i16, i16* %arrayidx11.80, align 2, !tbaa !3 *)
mov v161 mem0_160;
(*   %sub.80 = sub i16 %161, %call.i.80 *)
sub v_sub_80 v161 v_call_i_80;
(*   store i16 %sub.80, i16* %arrayidx9.80, align 2, !tbaa !3 *)
mov mem0_416 v_sub_80;
(*   %add21.80 = add i16 %161, %call.i.80 *)
add v_add21_80 v161 v_call_i_80;
(*   store i16 %add21.80, i16* %arrayidx11.80, align 2, !tbaa !3 *)
mov mem0_160 v_add21_80;
(*   %arrayidx9.81 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %162 = load i16, i16* %arrayidx9.81, align 2, !tbaa !3 *)
mov v162 mem0_418;
(*   %conv1.i.81 = sext i16 %162 to i32 *)
cast v_conv1_i_81@sint32 v162@sint16;
(*   %mul.i.81 = mul nsw i32 %conv1.i.81, -758 *)
mul v_mul_i_81 v_conv1_i_81 (-758)@sint32;
(*   %call.i.81 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.81) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_81, v_call_i_81);
(*   %arrayidx11.81 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %163 = load i16, i16* %arrayidx11.81, align 2, !tbaa !3 *)
mov v163 mem0_162;
(*   %sub.81 = sub i16 %163, %call.i.81 *)
sub v_sub_81 v163 v_call_i_81;
(*   store i16 %sub.81, i16* %arrayidx9.81, align 2, !tbaa !3 *)
mov mem0_418 v_sub_81;
(*   %add21.81 = add i16 %163, %call.i.81 *)
add v_add21_81 v163 v_call_i_81;
(*   store i16 %add21.81, i16* %arrayidx11.81, align 2, !tbaa !3 *)
mov mem0_162 v_add21_81;
(*   %arrayidx9.82 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %164 = load i16, i16* %arrayidx9.82, align 2, !tbaa !3 *)
mov v164 mem0_420;
(*   %conv1.i.82 = sext i16 %164 to i32 *)
cast v_conv1_i_82@sint32 v164@sint16;
(*   %mul.i.82 = mul nsw i32 %conv1.i.82, -758 *)
mul v_mul_i_82 v_conv1_i_82 (-758)@sint32;
(*   %call.i.82 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.82) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_82, v_call_i_82);
(*   %arrayidx11.82 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %165 = load i16, i16* %arrayidx11.82, align 2, !tbaa !3 *)
mov v165 mem0_164;
(*   %sub.82 = sub i16 %165, %call.i.82 *)
sub v_sub_82 v165 v_call_i_82;
(*   store i16 %sub.82, i16* %arrayidx9.82, align 2, !tbaa !3 *)
mov mem0_420 v_sub_82;
(*   %add21.82 = add i16 %165, %call.i.82 *)
add v_add21_82 v165 v_call_i_82;
(*   store i16 %add21.82, i16* %arrayidx11.82, align 2, !tbaa !3 *)
mov mem0_164 v_add21_82;
(*   %arrayidx9.83 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %166 = load i16, i16* %arrayidx9.83, align 2, !tbaa !3 *)
mov v166 mem0_422;
(*   %conv1.i.83 = sext i16 %166 to i32 *)
cast v_conv1_i_83@sint32 v166@sint16;
(*   %mul.i.83 = mul nsw i32 %conv1.i.83, -758 *)
mul v_mul_i_83 v_conv1_i_83 (-758)@sint32;
(*   %call.i.83 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.83) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_83, v_call_i_83);
(*   %arrayidx11.83 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %167 = load i16, i16* %arrayidx11.83, align 2, !tbaa !3 *)
mov v167 mem0_166;
(*   %sub.83 = sub i16 %167, %call.i.83 *)
sub v_sub_83 v167 v_call_i_83;
(*   store i16 %sub.83, i16* %arrayidx9.83, align 2, !tbaa !3 *)
mov mem0_422 v_sub_83;
(*   %add21.83 = add i16 %167, %call.i.83 *)
add v_add21_83 v167 v_call_i_83;
(*   store i16 %add21.83, i16* %arrayidx11.83, align 2, !tbaa !3 *)
mov mem0_166 v_add21_83;
(*   %arrayidx9.84 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %168 = load i16, i16* %arrayidx9.84, align 2, !tbaa !3 *)
mov v168 mem0_424;
(*   %conv1.i.84 = sext i16 %168 to i32 *)
cast v_conv1_i_84@sint32 v168@sint16;
(*   %mul.i.84 = mul nsw i32 %conv1.i.84, -758 *)
mul v_mul_i_84 v_conv1_i_84 (-758)@sint32;
(*   %call.i.84 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.84) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_84, v_call_i_84);
(*   %arrayidx11.84 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %169 = load i16, i16* %arrayidx11.84, align 2, !tbaa !3 *)
mov v169 mem0_168;
(*   %sub.84 = sub i16 %169, %call.i.84 *)
sub v_sub_84 v169 v_call_i_84;
(*   store i16 %sub.84, i16* %arrayidx9.84, align 2, !tbaa !3 *)
mov mem0_424 v_sub_84;
(*   %add21.84 = add i16 %169, %call.i.84 *)
add v_add21_84 v169 v_call_i_84;
(*   store i16 %add21.84, i16* %arrayidx11.84, align 2, !tbaa !3 *)
mov mem0_168 v_add21_84;
(*   %arrayidx9.85 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %170 = load i16, i16* %arrayidx9.85, align 2, !tbaa !3 *)
mov v170 mem0_426;
(*   %conv1.i.85 = sext i16 %170 to i32 *)
cast v_conv1_i_85@sint32 v170@sint16;
(*   %mul.i.85 = mul nsw i32 %conv1.i.85, -758 *)
mul v_mul_i_85 v_conv1_i_85 (-758)@sint32;
(*   %call.i.85 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.85) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_85, v_call_i_85);
(*   %arrayidx11.85 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %171 = load i16, i16* %arrayidx11.85, align 2, !tbaa !3 *)
mov v171 mem0_170;
(*   %sub.85 = sub i16 %171, %call.i.85 *)
sub v_sub_85 v171 v_call_i_85;
(*   store i16 %sub.85, i16* %arrayidx9.85, align 2, !tbaa !3 *)
mov mem0_426 v_sub_85;
(*   %add21.85 = add i16 %171, %call.i.85 *)
add v_add21_85 v171 v_call_i_85;
(*   store i16 %add21.85, i16* %arrayidx11.85, align 2, !tbaa !3 *)
mov mem0_170 v_add21_85;
(*   %arrayidx9.86 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %172 = load i16, i16* %arrayidx9.86, align 2, !tbaa !3 *)
mov v172 mem0_428;
(*   %conv1.i.86 = sext i16 %172 to i32 *)
cast v_conv1_i_86@sint32 v172@sint16;
(*   %mul.i.86 = mul nsw i32 %conv1.i.86, -758 *)
mul v_mul_i_86 v_conv1_i_86 (-758)@sint32;
(*   %call.i.86 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.86) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_86, v_call_i_86);
(*   %arrayidx11.86 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %173 = load i16, i16* %arrayidx11.86, align 2, !tbaa !3 *)
mov v173 mem0_172;
(*   %sub.86 = sub i16 %173, %call.i.86 *)
sub v_sub_86 v173 v_call_i_86;
(*   store i16 %sub.86, i16* %arrayidx9.86, align 2, !tbaa !3 *)
mov mem0_428 v_sub_86;
(*   %add21.86 = add i16 %173, %call.i.86 *)
add v_add21_86 v173 v_call_i_86;
(*   store i16 %add21.86, i16* %arrayidx11.86, align 2, !tbaa !3 *)
mov mem0_172 v_add21_86;
(*   %arrayidx9.87 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %174 = load i16, i16* %arrayidx9.87, align 2, !tbaa !3 *)
mov v174 mem0_430;
(*   %conv1.i.87 = sext i16 %174 to i32 *)
cast v_conv1_i_87@sint32 v174@sint16;
(*   %mul.i.87 = mul nsw i32 %conv1.i.87, -758 *)
mul v_mul_i_87 v_conv1_i_87 (-758)@sint32;
(*   %call.i.87 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.87) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_87, v_call_i_87);
(*   %arrayidx11.87 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %175 = load i16, i16* %arrayidx11.87, align 2, !tbaa !3 *)
mov v175 mem0_174;
(*   %sub.87 = sub i16 %175, %call.i.87 *)
sub v_sub_87 v175 v_call_i_87;
(*   store i16 %sub.87, i16* %arrayidx9.87, align 2, !tbaa !3 *)
mov mem0_430 v_sub_87;
(*   %add21.87 = add i16 %175, %call.i.87 *)
add v_add21_87 v175 v_call_i_87;
(*   store i16 %add21.87, i16* %arrayidx11.87, align 2, !tbaa !3 *)
mov mem0_174 v_add21_87;
(*   %arrayidx9.88 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %176 = load i16, i16* %arrayidx9.88, align 2, !tbaa !3 *)
mov v176 mem0_432;
(*   %conv1.i.88 = sext i16 %176 to i32 *)
cast v_conv1_i_88@sint32 v176@sint16;
(*   %mul.i.88 = mul nsw i32 %conv1.i.88, -758 *)
mul v_mul_i_88 v_conv1_i_88 (-758)@sint32;
(*   %call.i.88 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.88) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_88, v_call_i_88);
(*   %arrayidx11.88 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %177 = load i16, i16* %arrayidx11.88, align 2, !tbaa !3 *)
mov v177 mem0_176;
(*   %sub.88 = sub i16 %177, %call.i.88 *)
sub v_sub_88 v177 v_call_i_88;
(*   store i16 %sub.88, i16* %arrayidx9.88, align 2, !tbaa !3 *)
mov mem0_432 v_sub_88;
(*   %add21.88 = add i16 %177, %call.i.88 *)
add v_add21_88 v177 v_call_i_88;
(*   store i16 %add21.88, i16* %arrayidx11.88, align 2, !tbaa !3 *)
mov mem0_176 v_add21_88;
(*   %arrayidx9.89 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %178 = load i16, i16* %arrayidx9.89, align 2, !tbaa !3 *)
mov v178 mem0_434;
(*   %conv1.i.89 = sext i16 %178 to i32 *)
cast v_conv1_i_89@sint32 v178@sint16;
(*   %mul.i.89 = mul nsw i32 %conv1.i.89, -758 *)
mul v_mul_i_89 v_conv1_i_89 (-758)@sint32;
(*   %call.i.89 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.89) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_89, v_call_i_89);
(*   %arrayidx11.89 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %179 = load i16, i16* %arrayidx11.89, align 2, !tbaa !3 *)
mov v179 mem0_178;
(*   %sub.89 = sub i16 %179, %call.i.89 *)
sub v_sub_89 v179 v_call_i_89;
(*   store i16 %sub.89, i16* %arrayidx9.89, align 2, !tbaa !3 *)
mov mem0_434 v_sub_89;
(*   %add21.89 = add i16 %179, %call.i.89 *)
add v_add21_89 v179 v_call_i_89;
(*   store i16 %add21.89, i16* %arrayidx11.89, align 2, !tbaa !3 *)
mov mem0_178 v_add21_89;
(*   %arrayidx9.90 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %180 = load i16, i16* %arrayidx9.90, align 2, !tbaa !3 *)
mov v180 mem0_436;
(*   %conv1.i.90 = sext i16 %180 to i32 *)
cast v_conv1_i_90@sint32 v180@sint16;
(*   %mul.i.90 = mul nsw i32 %conv1.i.90, -758 *)
mul v_mul_i_90 v_conv1_i_90 (-758)@sint32;
(*   %call.i.90 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.90) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_90, v_call_i_90);
(*   %arrayidx11.90 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %181 = load i16, i16* %arrayidx11.90, align 2, !tbaa !3 *)
mov v181 mem0_180;
(*   %sub.90 = sub i16 %181, %call.i.90 *)
sub v_sub_90 v181 v_call_i_90;
(*   store i16 %sub.90, i16* %arrayidx9.90, align 2, !tbaa !3 *)
mov mem0_436 v_sub_90;
(*   %add21.90 = add i16 %181, %call.i.90 *)
add v_add21_90 v181 v_call_i_90;
(*   store i16 %add21.90, i16* %arrayidx11.90, align 2, !tbaa !3 *)
mov mem0_180 v_add21_90;
(*   %arrayidx9.91 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %182 = load i16, i16* %arrayidx9.91, align 2, !tbaa !3 *)
mov v182 mem0_438;
(*   %conv1.i.91 = sext i16 %182 to i32 *)
cast v_conv1_i_91@sint32 v182@sint16;
(*   %mul.i.91 = mul nsw i32 %conv1.i.91, -758 *)
mul v_mul_i_91 v_conv1_i_91 (-758)@sint32;
(*   %call.i.91 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.91) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_91, v_call_i_91);
(*   %arrayidx11.91 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %183 = load i16, i16* %arrayidx11.91, align 2, !tbaa !3 *)
mov v183 mem0_182;
(*   %sub.91 = sub i16 %183, %call.i.91 *)
sub v_sub_91 v183 v_call_i_91;
(*   store i16 %sub.91, i16* %arrayidx9.91, align 2, !tbaa !3 *)
mov mem0_438 v_sub_91;
(*   %add21.91 = add i16 %183, %call.i.91 *)
add v_add21_91 v183 v_call_i_91;
(*   store i16 %add21.91, i16* %arrayidx11.91, align 2, !tbaa !3 *)
mov mem0_182 v_add21_91;
(*   %arrayidx9.92 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %184 = load i16, i16* %arrayidx9.92, align 2, !tbaa !3 *)
mov v184 mem0_440;
(*   %conv1.i.92 = sext i16 %184 to i32 *)
cast v_conv1_i_92@sint32 v184@sint16;
(*   %mul.i.92 = mul nsw i32 %conv1.i.92, -758 *)
mul v_mul_i_92 v_conv1_i_92 (-758)@sint32;
(*   %call.i.92 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.92) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_92, v_call_i_92);
(*   %arrayidx11.92 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %185 = load i16, i16* %arrayidx11.92, align 2, !tbaa !3 *)
mov v185 mem0_184;
(*   %sub.92 = sub i16 %185, %call.i.92 *)
sub v_sub_92 v185 v_call_i_92;
(*   store i16 %sub.92, i16* %arrayidx9.92, align 2, !tbaa !3 *)
mov mem0_440 v_sub_92;
(*   %add21.92 = add i16 %185, %call.i.92 *)
add v_add21_92 v185 v_call_i_92;
(*   store i16 %add21.92, i16* %arrayidx11.92, align 2, !tbaa !3 *)
mov mem0_184 v_add21_92;
(*   %arrayidx9.93 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %186 = load i16, i16* %arrayidx9.93, align 2, !tbaa !3 *)
mov v186 mem0_442;
(*   %conv1.i.93 = sext i16 %186 to i32 *)
cast v_conv1_i_93@sint32 v186@sint16;
(*   %mul.i.93 = mul nsw i32 %conv1.i.93, -758 *)
mul v_mul_i_93 v_conv1_i_93 (-758)@sint32;
(*   %call.i.93 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.93) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_93, v_call_i_93);
(*   %arrayidx11.93 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %187 = load i16, i16* %arrayidx11.93, align 2, !tbaa !3 *)
mov v187 mem0_186;
(*   %sub.93 = sub i16 %187, %call.i.93 *)
sub v_sub_93 v187 v_call_i_93;
(*   store i16 %sub.93, i16* %arrayidx9.93, align 2, !tbaa !3 *)
mov mem0_442 v_sub_93;
(*   %add21.93 = add i16 %187, %call.i.93 *)
add v_add21_93 v187 v_call_i_93;
(*   store i16 %add21.93, i16* %arrayidx11.93, align 2, !tbaa !3 *)
mov mem0_186 v_add21_93;
(*   %arrayidx9.94 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %188 = load i16, i16* %arrayidx9.94, align 2, !tbaa !3 *)
mov v188 mem0_444;
(*   %conv1.i.94 = sext i16 %188 to i32 *)
cast v_conv1_i_94@sint32 v188@sint16;
(*   %mul.i.94 = mul nsw i32 %conv1.i.94, -758 *)
mul v_mul_i_94 v_conv1_i_94 (-758)@sint32;
(*   %call.i.94 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.94) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_94, v_call_i_94);
(*   %arrayidx11.94 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %189 = load i16, i16* %arrayidx11.94, align 2, !tbaa !3 *)
mov v189 mem0_188;
(*   %sub.94 = sub i16 %189, %call.i.94 *)
sub v_sub_94 v189 v_call_i_94;
(*   store i16 %sub.94, i16* %arrayidx9.94, align 2, !tbaa !3 *)
mov mem0_444 v_sub_94;
(*   %add21.94 = add i16 %189, %call.i.94 *)
add v_add21_94 v189 v_call_i_94;
(*   store i16 %add21.94, i16* %arrayidx11.94, align 2, !tbaa !3 *)
mov mem0_188 v_add21_94;
(*   %arrayidx9.95 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %190 = load i16, i16* %arrayidx9.95, align 2, !tbaa !3 *)
mov v190 mem0_446;
(*   %conv1.i.95 = sext i16 %190 to i32 *)
cast v_conv1_i_95@sint32 v190@sint16;
(*   %mul.i.95 = mul nsw i32 %conv1.i.95, -758 *)
mul v_mul_i_95 v_conv1_i_95 (-758)@sint32;
(*   %call.i.95 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.95) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_95, v_call_i_95);
(*   %arrayidx11.95 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %191 = load i16, i16* %arrayidx11.95, align 2, !tbaa !3 *)
mov v191 mem0_190;
(*   %sub.95 = sub i16 %191, %call.i.95 *)
sub v_sub_95 v191 v_call_i_95;
(*   store i16 %sub.95, i16* %arrayidx9.95, align 2, !tbaa !3 *)
mov mem0_446 v_sub_95;
(*   %add21.95 = add i16 %191, %call.i.95 *)
add v_add21_95 v191 v_call_i_95;
(*   store i16 %add21.95, i16* %arrayidx11.95, align 2, !tbaa !3 *)
mov mem0_190 v_add21_95;
(*   %arrayidx9.96 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %192 = load i16, i16* %arrayidx9.96, align 2, !tbaa !3 *)
mov v192 mem0_448;
(*   %conv1.i.96 = sext i16 %192 to i32 *)
cast v_conv1_i_96@sint32 v192@sint16;
(*   %mul.i.96 = mul nsw i32 %conv1.i.96, -758 *)
mul v_mul_i_96 v_conv1_i_96 (-758)@sint32;
(*   %call.i.96 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.96) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_96, v_call_i_96);
(*   %arrayidx11.96 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %193 = load i16, i16* %arrayidx11.96, align 2, !tbaa !3 *)
mov v193 mem0_192;
(*   %sub.96 = sub i16 %193, %call.i.96 *)
sub v_sub_96 v193 v_call_i_96;
(*   store i16 %sub.96, i16* %arrayidx9.96, align 2, !tbaa !3 *)
mov mem0_448 v_sub_96;
(*   %add21.96 = add i16 %193, %call.i.96 *)
add v_add21_96 v193 v_call_i_96;
(*   store i16 %add21.96, i16* %arrayidx11.96, align 2, !tbaa !3 *)
mov mem0_192 v_add21_96;
(*   %arrayidx9.97 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %194 = load i16, i16* %arrayidx9.97, align 2, !tbaa !3 *)
mov v194 mem0_450;
(*   %conv1.i.97 = sext i16 %194 to i32 *)
cast v_conv1_i_97@sint32 v194@sint16;
(*   %mul.i.97 = mul nsw i32 %conv1.i.97, -758 *)
mul v_mul_i_97 v_conv1_i_97 (-758)@sint32;
(*   %call.i.97 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.97) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_97, v_call_i_97);
(*   %arrayidx11.97 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %195 = load i16, i16* %arrayidx11.97, align 2, !tbaa !3 *)
mov v195 mem0_194;
(*   %sub.97 = sub i16 %195, %call.i.97 *)
sub v_sub_97 v195 v_call_i_97;
(*   store i16 %sub.97, i16* %arrayidx9.97, align 2, !tbaa !3 *)
mov mem0_450 v_sub_97;
(*   %add21.97 = add i16 %195, %call.i.97 *)
add v_add21_97 v195 v_call_i_97;
(*   store i16 %add21.97, i16* %arrayidx11.97, align 2, !tbaa !3 *)
mov mem0_194 v_add21_97;
(*   %arrayidx9.98 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %196 = load i16, i16* %arrayidx9.98, align 2, !tbaa !3 *)
mov v196 mem0_452;
(*   %conv1.i.98 = sext i16 %196 to i32 *)
cast v_conv1_i_98@sint32 v196@sint16;
(*   %mul.i.98 = mul nsw i32 %conv1.i.98, -758 *)
mul v_mul_i_98 v_conv1_i_98 (-758)@sint32;
(*   %call.i.98 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.98) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_98, v_call_i_98);
(*   %arrayidx11.98 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %197 = load i16, i16* %arrayidx11.98, align 2, !tbaa !3 *)
mov v197 mem0_196;
(*   %sub.98 = sub i16 %197, %call.i.98 *)
sub v_sub_98 v197 v_call_i_98;
(*   store i16 %sub.98, i16* %arrayidx9.98, align 2, !tbaa !3 *)
mov mem0_452 v_sub_98;
(*   %add21.98 = add i16 %197, %call.i.98 *)
add v_add21_98 v197 v_call_i_98;
(*   store i16 %add21.98, i16* %arrayidx11.98, align 2, !tbaa !3 *)
mov mem0_196 v_add21_98;
(*   %arrayidx9.99 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %198 = load i16, i16* %arrayidx9.99, align 2, !tbaa !3 *)
mov v198 mem0_454;
(*   %conv1.i.99 = sext i16 %198 to i32 *)
cast v_conv1_i_99@sint32 v198@sint16;
(*   %mul.i.99 = mul nsw i32 %conv1.i.99, -758 *)
mul v_mul_i_99 v_conv1_i_99 (-758)@sint32;
(*   %call.i.99 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.99) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_99, v_call_i_99);
(*   %arrayidx11.99 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %199 = load i16, i16* %arrayidx11.99, align 2, !tbaa !3 *)
mov v199 mem0_198;
(*   %sub.99 = sub i16 %199, %call.i.99 *)
sub v_sub_99 v199 v_call_i_99;
(*   store i16 %sub.99, i16* %arrayidx9.99, align 2, !tbaa !3 *)
mov mem0_454 v_sub_99;
(*   %add21.99 = add i16 %199, %call.i.99 *)
add v_add21_99 v199 v_call_i_99;
(*   store i16 %add21.99, i16* %arrayidx11.99, align 2, !tbaa !3 *)
mov mem0_198 v_add21_99;
(*   %arrayidx9.100 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %200 = load i16, i16* %arrayidx9.100, align 2, !tbaa !3 *)
mov v200 mem0_456;
(*   %conv1.i.100 = sext i16 %200 to i32 *)
cast v_conv1_i_100@sint32 v200@sint16;
(*   %mul.i.100 = mul nsw i32 %conv1.i.100, -758 *)
mul v_mul_i_100 v_conv1_i_100 (-758)@sint32;
(*   %call.i.100 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.100) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_100, v_call_i_100);
(*   %arrayidx11.100 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %201 = load i16, i16* %arrayidx11.100, align 2, !tbaa !3 *)
mov v201 mem0_200;
(*   %sub.100 = sub i16 %201, %call.i.100 *)
sub v_sub_100 v201 v_call_i_100;
(*   store i16 %sub.100, i16* %arrayidx9.100, align 2, !tbaa !3 *)
mov mem0_456 v_sub_100;
(*   %add21.100 = add i16 %201, %call.i.100 *)
add v_add21_100 v201 v_call_i_100;
(*   store i16 %add21.100, i16* %arrayidx11.100, align 2, !tbaa !3 *)
mov mem0_200 v_add21_100;
(*   %arrayidx9.101 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %202 = load i16, i16* %arrayidx9.101, align 2, !tbaa !3 *)
mov v202 mem0_458;
(*   %conv1.i.101 = sext i16 %202 to i32 *)
cast v_conv1_i_101@sint32 v202@sint16;
(*   %mul.i.101 = mul nsw i32 %conv1.i.101, -758 *)
mul v_mul_i_101 v_conv1_i_101 (-758)@sint32;
(*   %call.i.101 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.101) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_101, v_call_i_101);
(*   %arrayidx11.101 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %203 = load i16, i16* %arrayidx11.101, align 2, !tbaa !3 *)
mov v203 mem0_202;
(*   %sub.101 = sub i16 %203, %call.i.101 *)
sub v_sub_101 v203 v_call_i_101;
(*   store i16 %sub.101, i16* %arrayidx9.101, align 2, !tbaa !3 *)
mov mem0_458 v_sub_101;
(*   %add21.101 = add i16 %203, %call.i.101 *)
add v_add21_101 v203 v_call_i_101;
(*   store i16 %add21.101, i16* %arrayidx11.101, align 2, !tbaa !3 *)
mov mem0_202 v_add21_101;
(*   %arrayidx9.102 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %204 = load i16, i16* %arrayidx9.102, align 2, !tbaa !3 *)
mov v204 mem0_460;
(*   %conv1.i.102 = sext i16 %204 to i32 *)
cast v_conv1_i_102@sint32 v204@sint16;
(*   %mul.i.102 = mul nsw i32 %conv1.i.102, -758 *)
mul v_mul_i_102 v_conv1_i_102 (-758)@sint32;
(*   %call.i.102 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.102) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_102, v_call_i_102);
(*   %arrayidx11.102 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %205 = load i16, i16* %arrayidx11.102, align 2, !tbaa !3 *)
mov v205 mem0_204;
(*   %sub.102 = sub i16 %205, %call.i.102 *)
sub v_sub_102 v205 v_call_i_102;
(*   store i16 %sub.102, i16* %arrayidx9.102, align 2, !tbaa !3 *)
mov mem0_460 v_sub_102;
(*   %add21.102 = add i16 %205, %call.i.102 *)
add v_add21_102 v205 v_call_i_102;
(*   store i16 %add21.102, i16* %arrayidx11.102, align 2, !tbaa !3 *)
mov mem0_204 v_add21_102;
(*   %arrayidx9.103 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %206 = load i16, i16* %arrayidx9.103, align 2, !tbaa !3 *)
mov v206 mem0_462;
(*   %conv1.i.103 = sext i16 %206 to i32 *)
cast v_conv1_i_103@sint32 v206@sint16;
(*   %mul.i.103 = mul nsw i32 %conv1.i.103, -758 *)
mul v_mul_i_103 v_conv1_i_103 (-758)@sint32;
(*   %call.i.103 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.103) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_103, v_call_i_103);
(*   %arrayidx11.103 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %207 = load i16, i16* %arrayidx11.103, align 2, !tbaa !3 *)
mov v207 mem0_206;
(*   %sub.103 = sub i16 %207, %call.i.103 *)
sub v_sub_103 v207 v_call_i_103;
(*   store i16 %sub.103, i16* %arrayidx9.103, align 2, !tbaa !3 *)
mov mem0_462 v_sub_103;
(*   %add21.103 = add i16 %207, %call.i.103 *)
add v_add21_103 v207 v_call_i_103;
(*   store i16 %add21.103, i16* %arrayidx11.103, align 2, !tbaa !3 *)
mov mem0_206 v_add21_103;
(*   %arrayidx9.104 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %208 = load i16, i16* %arrayidx9.104, align 2, !tbaa !3 *)
mov v208 mem0_464;
(*   %conv1.i.104 = sext i16 %208 to i32 *)
cast v_conv1_i_104@sint32 v208@sint16;
(*   %mul.i.104 = mul nsw i32 %conv1.i.104, -758 *)
mul v_mul_i_104 v_conv1_i_104 (-758)@sint32;
(*   %call.i.104 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.104) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_104, v_call_i_104);
(*   %arrayidx11.104 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %209 = load i16, i16* %arrayidx11.104, align 2, !tbaa !3 *)
mov v209 mem0_208;
(*   %sub.104 = sub i16 %209, %call.i.104 *)
sub v_sub_104 v209 v_call_i_104;
(*   store i16 %sub.104, i16* %arrayidx9.104, align 2, !tbaa !3 *)
mov mem0_464 v_sub_104;
(*   %add21.104 = add i16 %209, %call.i.104 *)
add v_add21_104 v209 v_call_i_104;
(*   store i16 %add21.104, i16* %arrayidx11.104, align 2, !tbaa !3 *)
mov mem0_208 v_add21_104;
(*   %arrayidx9.105 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %210 = load i16, i16* %arrayidx9.105, align 2, !tbaa !3 *)
mov v210 mem0_466;
(*   %conv1.i.105 = sext i16 %210 to i32 *)
cast v_conv1_i_105@sint32 v210@sint16;
(*   %mul.i.105 = mul nsw i32 %conv1.i.105, -758 *)
mul v_mul_i_105 v_conv1_i_105 (-758)@sint32;
(*   %call.i.105 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.105) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_105, v_call_i_105);
(*   %arrayidx11.105 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %211 = load i16, i16* %arrayidx11.105, align 2, !tbaa !3 *)
mov v211 mem0_210;
(*   %sub.105 = sub i16 %211, %call.i.105 *)
sub v_sub_105 v211 v_call_i_105;
(*   store i16 %sub.105, i16* %arrayidx9.105, align 2, !tbaa !3 *)
mov mem0_466 v_sub_105;
(*   %add21.105 = add i16 %211, %call.i.105 *)
add v_add21_105 v211 v_call_i_105;
(*   store i16 %add21.105, i16* %arrayidx11.105, align 2, !tbaa !3 *)
mov mem0_210 v_add21_105;
(*   %arrayidx9.106 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %212 = load i16, i16* %arrayidx9.106, align 2, !tbaa !3 *)
mov v212 mem0_468;
(*   %conv1.i.106 = sext i16 %212 to i32 *)
cast v_conv1_i_106@sint32 v212@sint16;
(*   %mul.i.106 = mul nsw i32 %conv1.i.106, -758 *)
mul v_mul_i_106 v_conv1_i_106 (-758)@sint32;
(*   %call.i.106 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.106) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_106, v_call_i_106);
(*   %arrayidx11.106 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %213 = load i16, i16* %arrayidx11.106, align 2, !tbaa !3 *)
mov v213 mem0_212;
(*   %sub.106 = sub i16 %213, %call.i.106 *)
sub v_sub_106 v213 v_call_i_106;
(*   store i16 %sub.106, i16* %arrayidx9.106, align 2, !tbaa !3 *)
mov mem0_468 v_sub_106;
(*   %add21.106 = add i16 %213, %call.i.106 *)
add v_add21_106 v213 v_call_i_106;
(*   store i16 %add21.106, i16* %arrayidx11.106, align 2, !tbaa !3 *)
mov mem0_212 v_add21_106;
(*   %arrayidx9.107 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %214 = load i16, i16* %arrayidx9.107, align 2, !tbaa !3 *)
mov v214 mem0_470;
(*   %conv1.i.107 = sext i16 %214 to i32 *)
cast v_conv1_i_107@sint32 v214@sint16;
(*   %mul.i.107 = mul nsw i32 %conv1.i.107, -758 *)
mul v_mul_i_107 v_conv1_i_107 (-758)@sint32;
(*   %call.i.107 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.107) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_107, v_call_i_107);
(*   %arrayidx11.107 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %215 = load i16, i16* %arrayidx11.107, align 2, !tbaa !3 *)
mov v215 mem0_214;
(*   %sub.107 = sub i16 %215, %call.i.107 *)
sub v_sub_107 v215 v_call_i_107;
(*   store i16 %sub.107, i16* %arrayidx9.107, align 2, !tbaa !3 *)
mov mem0_470 v_sub_107;
(*   %add21.107 = add i16 %215, %call.i.107 *)
add v_add21_107 v215 v_call_i_107;
(*   store i16 %add21.107, i16* %arrayidx11.107, align 2, !tbaa !3 *)
mov mem0_214 v_add21_107;
(*   %arrayidx9.108 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %216 = load i16, i16* %arrayidx9.108, align 2, !tbaa !3 *)
mov v216 mem0_472;
(*   %conv1.i.108 = sext i16 %216 to i32 *)
cast v_conv1_i_108@sint32 v216@sint16;
(*   %mul.i.108 = mul nsw i32 %conv1.i.108, -758 *)
mul v_mul_i_108 v_conv1_i_108 (-758)@sint32;
(*   %call.i.108 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.108) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_108, v_call_i_108);
(*   %arrayidx11.108 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %217 = load i16, i16* %arrayidx11.108, align 2, !tbaa !3 *)
mov v217 mem0_216;
(*   %sub.108 = sub i16 %217, %call.i.108 *)
sub v_sub_108 v217 v_call_i_108;
(*   store i16 %sub.108, i16* %arrayidx9.108, align 2, !tbaa !3 *)
mov mem0_472 v_sub_108;
(*   %add21.108 = add i16 %217, %call.i.108 *)
add v_add21_108 v217 v_call_i_108;
(*   store i16 %add21.108, i16* %arrayidx11.108, align 2, !tbaa !3 *)
mov mem0_216 v_add21_108;
(*   %arrayidx9.109 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %218 = load i16, i16* %arrayidx9.109, align 2, !tbaa !3 *)
mov v218 mem0_474;
(*   %conv1.i.109 = sext i16 %218 to i32 *)
cast v_conv1_i_109@sint32 v218@sint16;
(*   %mul.i.109 = mul nsw i32 %conv1.i.109, -758 *)
mul v_mul_i_109 v_conv1_i_109 (-758)@sint32;
(*   %call.i.109 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.109) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_109, v_call_i_109);
(*   %arrayidx11.109 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %219 = load i16, i16* %arrayidx11.109, align 2, !tbaa !3 *)
mov v219 mem0_218;
(*   %sub.109 = sub i16 %219, %call.i.109 *)
sub v_sub_109 v219 v_call_i_109;
(*   store i16 %sub.109, i16* %arrayidx9.109, align 2, !tbaa !3 *)
mov mem0_474 v_sub_109;
(*   %add21.109 = add i16 %219, %call.i.109 *)
add v_add21_109 v219 v_call_i_109;
(*   store i16 %add21.109, i16* %arrayidx11.109, align 2, !tbaa !3 *)
mov mem0_218 v_add21_109;
(*   %arrayidx9.110 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %220 = load i16, i16* %arrayidx9.110, align 2, !tbaa !3 *)
mov v220 mem0_476;
(*   %conv1.i.110 = sext i16 %220 to i32 *)
cast v_conv1_i_110@sint32 v220@sint16;
(*   %mul.i.110 = mul nsw i32 %conv1.i.110, -758 *)
mul v_mul_i_110 v_conv1_i_110 (-758)@sint32;
(*   %call.i.110 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.110) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_110, v_call_i_110);
(*   %arrayidx11.110 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %221 = load i16, i16* %arrayidx11.110, align 2, !tbaa !3 *)
mov v221 mem0_220;
(*   %sub.110 = sub i16 %221, %call.i.110 *)
sub v_sub_110 v221 v_call_i_110;
(*   store i16 %sub.110, i16* %arrayidx9.110, align 2, !tbaa !3 *)
mov mem0_476 v_sub_110;
(*   %add21.110 = add i16 %221, %call.i.110 *)
add v_add21_110 v221 v_call_i_110;
(*   store i16 %add21.110, i16* %arrayidx11.110, align 2, !tbaa !3 *)
mov mem0_220 v_add21_110;
(*   %arrayidx9.111 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %222 = load i16, i16* %arrayidx9.111, align 2, !tbaa !3 *)
mov v222 mem0_478;
(*   %conv1.i.111 = sext i16 %222 to i32 *)
cast v_conv1_i_111@sint32 v222@sint16;
(*   %mul.i.111 = mul nsw i32 %conv1.i.111, -758 *)
mul v_mul_i_111 v_conv1_i_111 (-758)@sint32;
(*   %call.i.111 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.111) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_111, v_call_i_111);
(*   %arrayidx11.111 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %223 = load i16, i16* %arrayidx11.111, align 2, !tbaa !3 *)
mov v223 mem0_222;
(*   %sub.111 = sub i16 %223, %call.i.111 *)
sub v_sub_111 v223 v_call_i_111;
(*   store i16 %sub.111, i16* %arrayidx9.111, align 2, !tbaa !3 *)
mov mem0_478 v_sub_111;
(*   %add21.111 = add i16 %223, %call.i.111 *)
add v_add21_111 v223 v_call_i_111;
(*   store i16 %add21.111, i16* %arrayidx11.111, align 2, !tbaa !3 *)
mov mem0_222 v_add21_111;
(*   %arrayidx9.112 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %224 = load i16, i16* %arrayidx9.112, align 2, !tbaa !3 *)
mov v224 mem0_480;
(*   %conv1.i.112 = sext i16 %224 to i32 *)
cast v_conv1_i_112@sint32 v224@sint16;
(*   %mul.i.112 = mul nsw i32 %conv1.i.112, -758 *)
mul v_mul_i_112 v_conv1_i_112 (-758)@sint32;
(*   %call.i.112 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.112) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_112, v_call_i_112);
(*   %arrayidx11.112 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %225 = load i16, i16* %arrayidx11.112, align 2, !tbaa !3 *)
mov v225 mem0_224;
(*   %sub.112 = sub i16 %225, %call.i.112 *)
sub v_sub_112 v225 v_call_i_112;
(*   store i16 %sub.112, i16* %arrayidx9.112, align 2, !tbaa !3 *)
mov mem0_480 v_sub_112;
(*   %add21.112 = add i16 %225, %call.i.112 *)
add v_add21_112 v225 v_call_i_112;
(*   store i16 %add21.112, i16* %arrayidx11.112, align 2, !tbaa !3 *)
mov mem0_224 v_add21_112;
(*   %arrayidx9.113 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %226 = load i16, i16* %arrayidx9.113, align 2, !tbaa !3 *)
mov v226 mem0_482;
(*   %conv1.i.113 = sext i16 %226 to i32 *)
cast v_conv1_i_113@sint32 v226@sint16;
(*   %mul.i.113 = mul nsw i32 %conv1.i.113, -758 *)
mul v_mul_i_113 v_conv1_i_113 (-758)@sint32;
(*   %call.i.113 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.113) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_113, v_call_i_113);
(*   %arrayidx11.113 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %227 = load i16, i16* %arrayidx11.113, align 2, !tbaa !3 *)
mov v227 mem0_226;
(*   %sub.113 = sub i16 %227, %call.i.113 *)
sub v_sub_113 v227 v_call_i_113;
(*   store i16 %sub.113, i16* %arrayidx9.113, align 2, !tbaa !3 *)
mov mem0_482 v_sub_113;
(*   %add21.113 = add i16 %227, %call.i.113 *)
add v_add21_113 v227 v_call_i_113;
(*   store i16 %add21.113, i16* %arrayidx11.113, align 2, !tbaa !3 *)
mov mem0_226 v_add21_113;
(*   %arrayidx9.114 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %228 = load i16, i16* %arrayidx9.114, align 2, !tbaa !3 *)
mov v228 mem0_484;
(*   %conv1.i.114 = sext i16 %228 to i32 *)
cast v_conv1_i_114@sint32 v228@sint16;
(*   %mul.i.114 = mul nsw i32 %conv1.i.114, -758 *)
mul v_mul_i_114 v_conv1_i_114 (-758)@sint32;
(*   %call.i.114 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.114) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_114, v_call_i_114);
(*   %arrayidx11.114 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %229 = load i16, i16* %arrayidx11.114, align 2, !tbaa !3 *)
mov v229 mem0_228;
(*   %sub.114 = sub i16 %229, %call.i.114 *)
sub v_sub_114 v229 v_call_i_114;
(*   store i16 %sub.114, i16* %arrayidx9.114, align 2, !tbaa !3 *)
mov mem0_484 v_sub_114;
(*   %add21.114 = add i16 %229, %call.i.114 *)
add v_add21_114 v229 v_call_i_114;
(*   store i16 %add21.114, i16* %arrayidx11.114, align 2, !tbaa !3 *)
mov mem0_228 v_add21_114;
(*   %arrayidx9.115 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %230 = load i16, i16* %arrayidx9.115, align 2, !tbaa !3 *)
mov v230 mem0_486;
(*   %conv1.i.115 = sext i16 %230 to i32 *)
cast v_conv1_i_115@sint32 v230@sint16;
(*   %mul.i.115 = mul nsw i32 %conv1.i.115, -758 *)
mul v_mul_i_115 v_conv1_i_115 (-758)@sint32;
(*   %call.i.115 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.115) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_115, v_call_i_115);
(*   %arrayidx11.115 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %231 = load i16, i16* %arrayidx11.115, align 2, !tbaa !3 *)
mov v231 mem0_230;
(*   %sub.115 = sub i16 %231, %call.i.115 *)
sub v_sub_115 v231 v_call_i_115;
(*   store i16 %sub.115, i16* %arrayidx9.115, align 2, !tbaa !3 *)
mov mem0_486 v_sub_115;
(*   %add21.115 = add i16 %231, %call.i.115 *)
add v_add21_115 v231 v_call_i_115;
(*   store i16 %add21.115, i16* %arrayidx11.115, align 2, !tbaa !3 *)
mov mem0_230 v_add21_115;
(*   %arrayidx9.116 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %232 = load i16, i16* %arrayidx9.116, align 2, !tbaa !3 *)
mov v232 mem0_488;
(*   %conv1.i.116 = sext i16 %232 to i32 *)
cast v_conv1_i_116@sint32 v232@sint16;
(*   %mul.i.116 = mul nsw i32 %conv1.i.116, -758 *)
mul v_mul_i_116 v_conv1_i_116 (-758)@sint32;
(*   %call.i.116 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.116) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_116, v_call_i_116);
(*   %arrayidx11.116 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %233 = load i16, i16* %arrayidx11.116, align 2, !tbaa !3 *)
mov v233 mem0_232;
(*   %sub.116 = sub i16 %233, %call.i.116 *)
sub v_sub_116 v233 v_call_i_116;
(*   store i16 %sub.116, i16* %arrayidx9.116, align 2, !tbaa !3 *)
mov mem0_488 v_sub_116;
(*   %add21.116 = add i16 %233, %call.i.116 *)
add v_add21_116 v233 v_call_i_116;
(*   store i16 %add21.116, i16* %arrayidx11.116, align 2, !tbaa !3 *)
mov mem0_232 v_add21_116;
(*   %arrayidx9.117 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %234 = load i16, i16* %arrayidx9.117, align 2, !tbaa !3 *)
mov v234 mem0_490;
(*   %conv1.i.117 = sext i16 %234 to i32 *)
cast v_conv1_i_117@sint32 v234@sint16;
(*   %mul.i.117 = mul nsw i32 %conv1.i.117, -758 *)
mul v_mul_i_117 v_conv1_i_117 (-758)@sint32;
(*   %call.i.117 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.117) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_117, v_call_i_117);
(*   %arrayidx11.117 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %235 = load i16, i16* %arrayidx11.117, align 2, !tbaa !3 *)
mov v235 mem0_234;
(*   %sub.117 = sub i16 %235, %call.i.117 *)
sub v_sub_117 v235 v_call_i_117;
(*   store i16 %sub.117, i16* %arrayidx9.117, align 2, !tbaa !3 *)
mov mem0_490 v_sub_117;
(*   %add21.117 = add i16 %235, %call.i.117 *)
add v_add21_117 v235 v_call_i_117;
(*   store i16 %add21.117, i16* %arrayidx11.117, align 2, !tbaa !3 *)
mov mem0_234 v_add21_117;
(*   %arrayidx9.118 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %236 = load i16, i16* %arrayidx9.118, align 2, !tbaa !3 *)
mov v236 mem0_492;
(*   %conv1.i.118 = sext i16 %236 to i32 *)
cast v_conv1_i_118@sint32 v236@sint16;
(*   %mul.i.118 = mul nsw i32 %conv1.i.118, -758 *)
mul v_mul_i_118 v_conv1_i_118 (-758)@sint32;
(*   %call.i.118 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.118) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_118, v_call_i_118);
(*   %arrayidx11.118 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %237 = load i16, i16* %arrayidx11.118, align 2, !tbaa !3 *)
mov v237 mem0_236;
(*   %sub.118 = sub i16 %237, %call.i.118 *)
sub v_sub_118 v237 v_call_i_118;
(*   store i16 %sub.118, i16* %arrayidx9.118, align 2, !tbaa !3 *)
mov mem0_492 v_sub_118;
(*   %add21.118 = add i16 %237, %call.i.118 *)
add v_add21_118 v237 v_call_i_118;
(*   store i16 %add21.118, i16* %arrayidx11.118, align 2, !tbaa !3 *)
mov mem0_236 v_add21_118;
(*   %arrayidx9.119 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %238 = load i16, i16* %arrayidx9.119, align 2, !tbaa !3 *)
mov v238 mem0_494;
(*   %conv1.i.119 = sext i16 %238 to i32 *)
cast v_conv1_i_119@sint32 v238@sint16;
(*   %mul.i.119 = mul nsw i32 %conv1.i.119, -758 *)
mul v_mul_i_119 v_conv1_i_119 (-758)@sint32;
(*   %call.i.119 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.119) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_119, v_call_i_119);
(*   %arrayidx11.119 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %239 = load i16, i16* %arrayidx11.119, align 2, !tbaa !3 *)
mov v239 mem0_238;
(*   %sub.119 = sub i16 %239, %call.i.119 *)
sub v_sub_119 v239 v_call_i_119;
(*   store i16 %sub.119, i16* %arrayidx9.119, align 2, !tbaa !3 *)
mov mem0_494 v_sub_119;
(*   %add21.119 = add i16 %239, %call.i.119 *)
add v_add21_119 v239 v_call_i_119;
(*   store i16 %add21.119, i16* %arrayidx11.119, align 2, !tbaa !3 *)
mov mem0_238 v_add21_119;
(*   %arrayidx9.120 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %240 = load i16, i16* %arrayidx9.120, align 2, !tbaa !3 *)
mov v240 mem0_496;
(*   %conv1.i.120 = sext i16 %240 to i32 *)
cast v_conv1_i_120@sint32 v240@sint16;
(*   %mul.i.120 = mul nsw i32 %conv1.i.120, -758 *)
mul v_mul_i_120 v_conv1_i_120 (-758)@sint32;
(*   %call.i.120 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.120) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_120, v_call_i_120);
(*   %arrayidx11.120 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %241 = load i16, i16* %arrayidx11.120, align 2, !tbaa !3 *)
mov v241 mem0_240;
(*   %sub.120 = sub i16 %241, %call.i.120 *)
sub v_sub_120 v241 v_call_i_120;
(*   store i16 %sub.120, i16* %arrayidx9.120, align 2, !tbaa !3 *)
mov mem0_496 v_sub_120;
(*   %add21.120 = add i16 %241, %call.i.120 *)
add v_add21_120 v241 v_call_i_120;
(*   store i16 %add21.120, i16* %arrayidx11.120, align 2, !tbaa !3 *)
mov mem0_240 v_add21_120;
(*   %arrayidx9.121 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %242 = load i16, i16* %arrayidx9.121, align 2, !tbaa !3 *)
mov v242 mem0_498;
(*   %conv1.i.121 = sext i16 %242 to i32 *)
cast v_conv1_i_121@sint32 v242@sint16;
(*   %mul.i.121 = mul nsw i32 %conv1.i.121, -758 *)
mul v_mul_i_121 v_conv1_i_121 (-758)@sint32;
(*   %call.i.121 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.121) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_121, v_call_i_121);
(*   %arrayidx11.121 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %243 = load i16, i16* %arrayidx11.121, align 2, !tbaa !3 *)
mov v243 mem0_242;
(*   %sub.121 = sub i16 %243, %call.i.121 *)
sub v_sub_121 v243 v_call_i_121;
(*   store i16 %sub.121, i16* %arrayidx9.121, align 2, !tbaa !3 *)
mov mem0_498 v_sub_121;
(*   %add21.121 = add i16 %243, %call.i.121 *)
add v_add21_121 v243 v_call_i_121;
(*   store i16 %add21.121, i16* %arrayidx11.121, align 2, !tbaa !3 *)
mov mem0_242 v_add21_121;
(*   %arrayidx9.122 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %244 = load i16, i16* %arrayidx9.122, align 2, !tbaa !3 *)
mov v244 mem0_500;
(*   %conv1.i.122 = sext i16 %244 to i32 *)
cast v_conv1_i_122@sint32 v244@sint16;
(*   %mul.i.122 = mul nsw i32 %conv1.i.122, -758 *)
mul v_mul_i_122 v_conv1_i_122 (-758)@sint32;
(*   %call.i.122 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.122) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_122, v_call_i_122);
(*   %arrayidx11.122 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %245 = load i16, i16* %arrayidx11.122, align 2, !tbaa !3 *)
mov v245 mem0_244;
(*   %sub.122 = sub i16 %245, %call.i.122 *)
sub v_sub_122 v245 v_call_i_122;
(*   store i16 %sub.122, i16* %arrayidx9.122, align 2, !tbaa !3 *)
mov mem0_500 v_sub_122;
(*   %add21.122 = add i16 %245, %call.i.122 *)
add v_add21_122 v245 v_call_i_122;
(*   store i16 %add21.122, i16* %arrayidx11.122, align 2, !tbaa !3 *)
mov mem0_244 v_add21_122;
(*   %arrayidx9.123 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %246 = load i16, i16* %arrayidx9.123, align 2, !tbaa !3 *)
mov v246 mem0_502;
(*   %conv1.i.123 = sext i16 %246 to i32 *)
cast v_conv1_i_123@sint32 v246@sint16;
(*   %mul.i.123 = mul nsw i32 %conv1.i.123, -758 *)
mul v_mul_i_123 v_conv1_i_123 (-758)@sint32;
(*   %call.i.123 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.123) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_123, v_call_i_123);
(*   %arrayidx11.123 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %247 = load i16, i16* %arrayidx11.123, align 2, !tbaa !3 *)
mov v247 mem0_246;
(*   %sub.123 = sub i16 %247, %call.i.123 *)
sub v_sub_123 v247 v_call_i_123;
(*   store i16 %sub.123, i16* %arrayidx9.123, align 2, !tbaa !3 *)
mov mem0_502 v_sub_123;
(*   %add21.123 = add i16 %247, %call.i.123 *)
add v_add21_123 v247 v_call_i_123;
(*   store i16 %add21.123, i16* %arrayidx11.123, align 2, !tbaa !3 *)
mov mem0_246 v_add21_123;
(*   %arrayidx9.124 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %248 = load i16, i16* %arrayidx9.124, align 2, !tbaa !3 *)
mov v248 mem0_504;
(*   %conv1.i.124 = sext i16 %248 to i32 *)
cast v_conv1_i_124@sint32 v248@sint16;
(*   %mul.i.124 = mul nsw i32 %conv1.i.124, -758 *)
mul v_mul_i_124 v_conv1_i_124 (-758)@sint32;
(*   %call.i.124 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.124) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_124, v_call_i_124);
(*   %arrayidx11.124 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %249 = load i16, i16* %arrayidx11.124, align 2, !tbaa !3 *)
mov v249 mem0_248;
(*   %sub.124 = sub i16 %249, %call.i.124 *)
sub v_sub_124 v249 v_call_i_124;
(*   store i16 %sub.124, i16* %arrayidx9.124, align 2, !tbaa !3 *)
mov mem0_504 v_sub_124;
(*   %add21.124 = add i16 %249, %call.i.124 *)
add v_add21_124 v249 v_call_i_124;
(*   store i16 %add21.124, i16* %arrayidx11.124, align 2, !tbaa !3 *)
mov mem0_248 v_add21_124;
(*   %arrayidx9.125 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %250 = load i16, i16* %arrayidx9.125, align 2, !tbaa !3 *)
mov v250 mem0_506;
(*   %conv1.i.125 = sext i16 %250 to i32 *)
cast v_conv1_i_125@sint32 v250@sint16;
(*   %mul.i.125 = mul nsw i32 %conv1.i.125, -758 *)
mul v_mul_i_125 v_conv1_i_125 (-758)@sint32;
(*   %call.i.125 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.125) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_125, v_call_i_125);
(*   %arrayidx11.125 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %251 = load i16, i16* %arrayidx11.125, align 2, !tbaa !3 *)
mov v251 mem0_250;
(*   %sub.125 = sub i16 %251, %call.i.125 *)
sub v_sub_125 v251 v_call_i_125;
(*   store i16 %sub.125, i16* %arrayidx9.125, align 2, !tbaa !3 *)
mov mem0_506 v_sub_125;
(*   %add21.125 = add i16 %251, %call.i.125 *)
add v_add21_125 v251 v_call_i_125;
(*   store i16 %add21.125, i16* %arrayidx11.125, align 2, !tbaa !3 *)
mov mem0_250 v_add21_125;
(*   %arrayidx9.126 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %252 = load i16, i16* %arrayidx9.126, align 2, !tbaa !3 *)
mov v252 mem0_508;
(*   %conv1.i.126 = sext i16 %252 to i32 *)
cast v_conv1_i_126@sint32 v252@sint16;
(*   %mul.i.126 = mul nsw i32 %conv1.i.126, -758 *)
mul v_mul_i_126 v_conv1_i_126 (-758)@sint32;
(*   %call.i.126 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.126) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_126, v_call_i_126);
(*   %arrayidx11.126 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %253 = load i16, i16* %arrayidx11.126, align 2, !tbaa !3 *)
mov v253 mem0_252;
(*   %sub.126 = sub i16 %253, %call.i.126 *)
sub v_sub_126 v253 v_call_i_126;
(*   store i16 %sub.126, i16* %arrayidx9.126, align 2, !tbaa !3 *)
mov mem0_508 v_sub_126;
(*   %add21.126 = add i16 %253, %call.i.126 *)
add v_add21_126 v253 v_call_i_126;
(*   store i16 %add21.126, i16* %arrayidx11.126, align 2, !tbaa !3 *)
mov mem0_252 v_add21_126;
(*   %arrayidx9.127 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %254 = load i16, i16* %arrayidx9.127, align 2, !tbaa !3 *)
mov v254 mem0_510;
(*   %conv1.i.127 = sext i16 %254 to i32 *)
cast v_conv1_i_127@sint32 v254@sint16;
(*   %mul.i.127 = mul nsw i32 %conv1.i.127, -758 *)
mul v_mul_i_127 v_conv1_i_127 (-758)@sint32;
(*   %call.i.127 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.127) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_127, v_call_i_127);
(*   %arrayidx11.127 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %255 = load i16, i16* %arrayidx11.127, align 2, !tbaa !3 *)
mov v255 mem0_254;
(*   %sub.127 = sub i16 %255, %call.i.127 *)
sub v_sub_127 v255 v_call_i_127;
(*   store i16 %sub.127, i16* %arrayidx9.127, align 2, !tbaa !3 *)
mov mem0_510 v_sub_127;
(*   %add21.127 = add i16 %255, %call.i.127 *)
add v_add21_127 v255 v_call_i_127;
(*   store i16 %add21.127, i16* %arrayidx11.127, align 2, !tbaa !3 *)
mov mem0_254 v_add21_127;

mov mem0_0_k1 mem0_0;
mov mem0_2_k1 mem0_2;
mov mem0_4_k1 mem0_4;
mov mem0_6_k1 mem0_6;
mov mem0_8_k1 mem0_8;
mov mem0_10_k1 mem0_10;
mov mem0_12_k1 mem0_12;
mov mem0_14_k1 mem0_14;
mov mem0_16_k1 mem0_16;
mov mem0_18_k1 mem0_18;
mov mem0_20_k1 mem0_20;
mov mem0_22_k1 mem0_22;
mov mem0_24_k1 mem0_24;
mov mem0_26_k1 mem0_26;
mov mem0_28_k1 mem0_28;
mov mem0_30_k1 mem0_30;
mov mem0_32_k1 mem0_32;
mov mem0_34_k1 mem0_34;
mov mem0_36_k1 mem0_36;
mov mem0_38_k1 mem0_38;
mov mem0_40_k1 mem0_40;
mov mem0_42_k1 mem0_42;
mov mem0_44_k1 mem0_44;
mov mem0_46_k1 mem0_46;
mov mem0_48_k1 mem0_48;
mov mem0_50_k1 mem0_50;
mov mem0_52_k1 mem0_52;
mov mem0_54_k1 mem0_54;
mov mem0_56_k1 mem0_56;
mov mem0_58_k1 mem0_58;
mov mem0_60_k1 mem0_60;
mov mem0_62_k1 mem0_62;
mov mem0_64_k1 mem0_64;
mov mem0_66_k1 mem0_66;
mov mem0_68_k1 mem0_68;
mov mem0_70_k1 mem0_70;
mov mem0_72_k1 mem0_72;
mov mem0_74_k1 mem0_74;
mov mem0_76_k1 mem0_76;
mov mem0_78_k1 mem0_78;
mov mem0_80_k1 mem0_80;
mov mem0_82_k1 mem0_82;
mov mem0_84_k1 mem0_84;
mov mem0_86_k1 mem0_86;
mov mem0_88_k1 mem0_88;
mov mem0_90_k1 mem0_90;
mov mem0_92_k1 mem0_92;
mov mem0_94_k1 mem0_94;
mov mem0_96_k1 mem0_96;
mov mem0_98_k1 mem0_98;
mov mem0_100_k1 mem0_100;
mov mem0_102_k1 mem0_102;
mov mem0_104_k1 mem0_104;
mov mem0_106_k1 mem0_106;
mov mem0_108_k1 mem0_108;
mov mem0_110_k1 mem0_110;
mov mem0_112_k1 mem0_112;
mov mem0_114_k1 mem0_114;
mov mem0_116_k1 mem0_116;
mov mem0_118_k1 mem0_118;
mov mem0_120_k1 mem0_120;
mov mem0_122_k1 mem0_122;
mov mem0_124_k1 mem0_124;
mov mem0_126_k1 mem0_126;
mov mem0_128_k1 mem0_128;
mov mem0_130_k1 mem0_130;
mov mem0_132_k1 mem0_132;
mov mem0_134_k1 mem0_134;
mov mem0_136_k1 mem0_136;
mov mem0_138_k1 mem0_138;
mov mem0_140_k1 mem0_140;
mov mem0_142_k1 mem0_142;
mov mem0_144_k1 mem0_144;
mov mem0_146_k1 mem0_146;
mov mem0_148_k1 mem0_148;
mov mem0_150_k1 mem0_150;
mov mem0_152_k1 mem0_152;
mov mem0_154_k1 mem0_154;
mov mem0_156_k1 mem0_156;
mov mem0_158_k1 mem0_158;
mov mem0_160_k1 mem0_160;
mov mem0_162_k1 mem0_162;
mov mem0_164_k1 mem0_164;
mov mem0_166_k1 mem0_166;
mov mem0_168_k1 mem0_168;
mov mem0_170_k1 mem0_170;
mov mem0_172_k1 mem0_172;
mov mem0_174_k1 mem0_174;
mov mem0_176_k1 mem0_176;
mov mem0_178_k1 mem0_178;
mov mem0_180_k1 mem0_180;
mov mem0_182_k1 mem0_182;
mov mem0_184_k1 mem0_184;
mov mem0_186_k1 mem0_186;
mov mem0_188_k1 mem0_188;
mov mem0_190_k1 mem0_190;
mov mem0_192_k1 mem0_192;
mov mem0_194_k1 mem0_194;
mov mem0_196_k1 mem0_196;
mov mem0_198_k1 mem0_198;
mov mem0_200_k1 mem0_200;
mov mem0_202_k1 mem0_202;
mov mem0_204_k1 mem0_204;
mov mem0_206_k1 mem0_206;
mov mem0_208_k1 mem0_208;
mov mem0_210_k1 mem0_210;
mov mem0_212_k1 mem0_212;
mov mem0_214_k1 mem0_214;
mov mem0_216_k1 mem0_216;
mov mem0_218_k1 mem0_218;
mov mem0_220_k1 mem0_220;
mov mem0_222_k1 mem0_222;
mov mem0_224_k1 mem0_224;
mov mem0_226_k1 mem0_226;
mov mem0_228_k1 mem0_228;
mov mem0_230_k1 mem0_230;
mov mem0_232_k1 mem0_232;
mov mem0_234_k1 mem0_234;
mov mem0_236_k1 mem0_236;
mov mem0_238_k1 mem0_238;
mov mem0_240_k1 mem0_240;
mov mem0_242_k1 mem0_242;
mov mem0_244_k1 mem0_244;
mov mem0_246_k1 mem0_246;
mov mem0_248_k1 mem0_248;
mov mem0_250_k1 mem0_250;
mov mem0_252_k1 mem0_252;
mov mem0_254_k1 mem0_254;
mov mem0_256_k1 mem0_256;
mov mem0_258_k1 mem0_258;
mov mem0_260_k1 mem0_260;
mov mem0_262_k1 mem0_262;
mov mem0_264_k1 mem0_264;
mov mem0_266_k1 mem0_266;
mov mem0_268_k1 mem0_268;
mov mem0_270_k1 mem0_270;
mov mem0_272_k1 mem0_272;
mov mem0_274_k1 mem0_274;
mov mem0_276_k1 mem0_276;
mov mem0_278_k1 mem0_278;
mov mem0_280_k1 mem0_280;
mov mem0_282_k1 mem0_282;
mov mem0_284_k1 mem0_284;
mov mem0_286_k1 mem0_286;
mov mem0_288_k1 mem0_288;
mov mem0_290_k1 mem0_290;
mov mem0_292_k1 mem0_292;
mov mem0_294_k1 mem0_294;
mov mem0_296_k1 mem0_296;
mov mem0_298_k1 mem0_298;
mov mem0_300_k1 mem0_300;
mov mem0_302_k1 mem0_302;
mov mem0_304_k1 mem0_304;
mov mem0_306_k1 mem0_306;
mov mem0_308_k1 mem0_308;
mov mem0_310_k1 mem0_310;
mov mem0_312_k1 mem0_312;
mov mem0_314_k1 mem0_314;
mov mem0_316_k1 mem0_316;
mov mem0_318_k1 mem0_318;
mov mem0_320_k1 mem0_320;
mov mem0_322_k1 mem0_322;
mov mem0_324_k1 mem0_324;
mov mem0_326_k1 mem0_326;
mov mem0_328_k1 mem0_328;
mov mem0_330_k1 mem0_330;
mov mem0_332_k1 mem0_332;
mov mem0_334_k1 mem0_334;
mov mem0_336_k1 mem0_336;
mov mem0_338_k1 mem0_338;
mov mem0_340_k1 mem0_340;
mov mem0_342_k1 mem0_342;
mov mem0_344_k1 mem0_344;
mov mem0_346_k1 mem0_346;
mov mem0_348_k1 mem0_348;
mov mem0_350_k1 mem0_350;
mov mem0_352_k1 mem0_352;
mov mem0_354_k1 mem0_354;
mov mem0_356_k1 mem0_356;
mov mem0_358_k1 mem0_358;
mov mem0_360_k1 mem0_360;
mov mem0_362_k1 mem0_362;
mov mem0_364_k1 mem0_364;
mov mem0_366_k1 mem0_366;
mov mem0_368_k1 mem0_368;
mov mem0_370_k1 mem0_370;
mov mem0_372_k1 mem0_372;
mov mem0_374_k1 mem0_374;
mov mem0_376_k1 mem0_376;
mov mem0_378_k1 mem0_378;
mov mem0_380_k1 mem0_380;
mov mem0_382_k1 mem0_382;
mov mem0_384_k1 mem0_384;
mov mem0_386_k1 mem0_386;
mov mem0_388_k1 mem0_388;
mov mem0_390_k1 mem0_390;
mov mem0_392_k1 mem0_392;
mov mem0_394_k1 mem0_394;
mov mem0_396_k1 mem0_396;
mov mem0_398_k1 mem0_398;
mov mem0_400_k1 mem0_400;
mov mem0_402_k1 mem0_402;
mov mem0_404_k1 mem0_404;
mov mem0_406_k1 mem0_406;
mov mem0_408_k1 mem0_408;
mov mem0_410_k1 mem0_410;
mov mem0_412_k1 mem0_412;
mov mem0_414_k1 mem0_414;
mov mem0_416_k1 mem0_416;
mov mem0_418_k1 mem0_418;
mov mem0_420_k1 mem0_420;
mov mem0_422_k1 mem0_422;
mov mem0_424_k1 mem0_424;
mov mem0_426_k1 mem0_426;
mov mem0_428_k1 mem0_428;
mov mem0_430_k1 mem0_430;
mov mem0_432_k1 mem0_432;
mov mem0_434_k1 mem0_434;
mov mem0_436_k1 mem0_436;
mov mem0_438_k1 mem0_438;
mov mem0_440_k1 mem0_440;
mov mem0_442_k1 mem0_442;
mov mem0_444_k1 mem0_444;
mov mem0_446_k1 mem0_446;
mov mem0_448_k1 mem0_448;
mov mem0_450_k1 mem0_450;
mov mem0_452_k1 mem0_452;
mov mem0_454_k1 mem0_454;
mov mem0_456_k1 mem0_456;
mov mem0_458_k1 mem0_458;
mov mem0_460_k1 mem0_460;
mov mem0_462_k1 mem0_462;
mov mem0_464_k1 mem0_464;
mov mem0_466_k1 mem0_466;
mov mem0_468_k1 mem0_468;
mov mem0_470_k1 mem0_470;
mov mem0_472_k1 mem0_472;
mov mem0_474_k1 mem0_474;
mov mem0_476_k1 mem0_476;
mov mem0_478_k1 mem0_478;
mov mem0_480_k1 mem0_480;
mov mem0_482_k1 mem0_482;
mov mem0_484_k1 mem0_484;
mov mem0_486_k1 mem0_486;
mov mem0_488_k1 mem0_488;
mov mem0_490_k1 mem0_490;
mov mem0_492_k1 mem0_492;
mov mem0_494_k1 mem0_494;
mov mem0_496_k1 mem0_496;
mov mem0_498_k1 mem0_498;
mov mem0_500_k1 mem0_500;
mov mem0_502_k1 mem0_502;
mov mem0_504_k1 mem0_504;
mov mem0_506_k1 mem0_506;
mov mem0_508_k1 mem0_508;
mov mem0_510_k1 mem0_510;

{

and [

eqmod mem0_256_k1*(2**16) a_0*(2**16)-a_256*(-758) 3329,
eqmod mem0_0_k1*(2**16) a_0*(2**16)+a_256*(-758) 3329,
eqmod mem0_258_k1*(2**16) a_2*(2**16)-a_258*(-758) 3329,
eqmod mem0_2_k1*(2**16) a_2*(2**16)+a_258*(-758) 3329,
eqmod mem0_260_k1*(2**16) a_4*(2**16)-a_260*(-758) 3329,
eqmod mem0_4_k1*(2**16) a_4*(2**16)+a_260*(-758) 3329,
eqmod mem0_262_k1*(2**16) a_6*(2**16)-a_262*(-758) 3329,
eqmod mem0_6_k1*(2**16) a_6*(2**16)+a_262*(-758) 3329,
eqmod mem0_264_k1*(2**16) a_8*(2**16)-a_264*(-758) 3329,
eqmod mem0_8_k1*(2**16) a_8*(2**16)+a_264*(-758) 3329,
eqmod mem0_266_k1*(2**16) a_10*(2**16)-a_266*(-758) 3329,
eqmod mem0_10_k1*(2**16) a_10*(2**16)+a_266*(-758) 3329,
eqmod mem0_268_k1*(2**16) a_12*(2**16)-a_268*(-758) 3329,
eqmod mem0_12_k1*(2**16) a_12*(2**16)+a_268*(-758) 3329,
eqmod mem0_270_k1*(2**16) a_14*(2**16)-a_270*(-758) 3329,
eqmod mem0_14_k1*(2**16) a_14*(2**16)+a_270*(-758) 3329,
eqmod mem0_272_k1*(2**16) a_16*(2**16)-a_272*(-758) 3329,
eqmod mem0_16_k1*(2**16) a_16*(2**16)+a_272*(-758) 3329,
eqmod mem0_274_k1*(2**16) a_18*(2**16)-a_274*(-758) 3329,
eqmod mem0_18_k1*(2**16) a_18*(2**16)+a_274*(-758) 3329,
eqmod mem0_276_k1*(2**16) a_20*(2**16)-a_276*(-758) 3329,
eqmod mem0_20_k1*(2**16) a_20*(2**16)+a_276*(-758) 3329,
eqmod mem0_278_k1*(2**16) a_22*(2**16)-a_278*(-758) 3329,
eqmod mem0_22_k1*(2**16) a_22*(2**16)+a_278*(-758) 3329,
eqmod mem0_280_k1*(2**16) a_24*(2**16)-a_280*(-758) 3329,
eqmod mem0_24_k1*(2**16) a_24*(2**16)+a_280*(-758) 3329,
eqmod mem0_282_k1*(2**16) a_26*(2**16)-a_282*(-758) 3329,
eqmod mem0_26_k1*(2**16) a_26*(2**16)+a_282*(-758) 3329,
eqmod mem0_284_k1*(2**16) a_28*(2**16)-a_284*(-758) 3329,
eqmod mem0_28_k1*(2**16) a_28*(2**16)+a_284*(-758) 3329,
eqmod mem0_286_k1*(2**16) a_30*(2**16)-a_286*(-758) 3329,
eqmod mem0_30_k1*(2**16) a_30*(2**16)+a_286*(-758) 3329,
eqmod mem0_288_k1*(2**16) a_32*(2**16)-a_288*(-758) 3329,
eqmod mem0_32_k1*(2**16) a_32*(2**16)+a_288*(-758) 3329,
eqmod mem0_290_k1*(2**16) a_34*(2**16)-a_290*(-758) 3329,
eqmod mem0_34_k1*(2**16) a_34*(2**16)+a_290*(-758) 3329,
eqmod mem0_292_k1*(2**16) a_36*(2**16)-a_292*(-758) 3329,
eqmod mem0_36_k1*(2**16) a_36*(2**16)+a_292*(-758) 3329,
eqmod mem0_294_k1*(2**16) a_38*(2**16)-a_294*(-758) 3329,
eqmod mem0_38_k1*(2**16) a_38*(2**16)+a_294*(-758) 3329,
eqmod mem0_296_k1*(2**16) a_40*(2**16)-a_296*(-758) 3329,
eqmod mem0_40_k1*(2**16) a_40*(2**16)+a_296*(-758) 3329,
eqmod mem0_298_k1*(2**16) a_42*(2**16)-a_298*(-758) 3329,
eqmod mem0_42_k1*(2**16) a_42*(2**16)+a_298*(-758) 3329,
eqmod mem0_300_k1*(2**16) a_44*(2**16)-a_300*(-758) 3329,
eqmod mem0_44_k1*(2**16) a_44*(2**16)+a_300*(-758) 3329,
eqmod mem0_302_k1*(2**16) a_46*(2**16)-a_302*(-758) 3329,
eqmod mem0_46_k1*(2**16) a_46*(2**16)+a_302*(-758) 3329,
eqmod mem0_304_k1*(2**16) a_48*(2**16)-a_304*(-758) 3329,
eqmod mem0_48_k1*(2**16) a_48*(2**16)+a_304*(-758) 3329,
eqmod mem0_306_k1*(2**16) a_50*(2**16)-a_306*(-758) 3329,
eqmod mem0_50_k1*(2**16) a_50*(2**16)+a_306*(-758) 3329,
eqmod mem0_308_k1*(2**16) a_52*(2**16)-a_308*(-758) 3329,
eqmod mem0_52_k1*(2**16) a_52*(2**16)+a_308*(-758) 3329,
eqmod mem0_310_k1*(2**16) a_54*(2**16)-a_310*(-758) 3329,
eqmod mem0_54_k1*(2**16) a_54*(2**16)+a_310*(-758) 3329,
eqmod mem0_312_k1*(2**16) a_56*(2**16)-a_312*(-758) 3329,
eqmod mem0_56_k1*(2**16) a_56*(2**16)+a_312*(-758) 3329,
eqmod mem0_314_k1*(2**16) a_58*(2**16)-a_314*(-758) 3329,
eqmod mem0_58_k1*(2**16) a_58*(2**16)+a_314*(-758) 3329,
eqmod mem0_316_k1*(2**16) a_60*(2**16)-a_316*(-758) 3329,
eqmod mem0_60_k1*(2**16) a_60*(2**16)+a_316*(-758) 3329,
eqmod mem0_318_k1*(2**16) a_62*(2**16)-a_318*(-758) 3329,
eqmod mem0_62_k1*(2**16) a_62*(2**16)+a_318*(-758) 3329,
eqmod mem0_320_k1*(2**16) a_64*(2**16)-a_320*(-758) 3329,
eqmod mem0_64_k1*(2**16) a_64*(2**16)+a_320*(-758) 3329,
eqmod mem0_322_k1*(2**16) a_66*(2**16)-a_322*(-758) 3329,
eqmod mem0_66_k1*(2**16) a_66*(2**16)+a_322*(-758) 3329,
eqmod mem0_324_k1*(2**16) a_68*(2**16)-a_324*(-758) 3329,
eqmod mem0_68_k1*(2**16) a_68*(2**16)+a_324*(-758) 3329,
eqmod mem0_326_k1*(2**16) a_70*(2**16)-a_326*(-758) 3329,
eqmod mem0_70_k1*(2**16) a_70*(2**16)+a_326*(-758) 3329,
eqmod mem0_328_k1*(2**16) a_72*(2**16)-a_328*(-758) 3329,
eqmod mem0_72_k1*(2**16) a_72*(2**16)+a_328*(-758) 3329,
eqmod mem0_330_k1*(2**16) a_74*(2**16)-a_330*(-758) 3329,
eqmod mem0_74_k1*(2**16) a_74*(2**16)+a_330*(-758) 3329,
eqmod mem0_332_k1*(2**16) a_76*(2**16)-a_332*(-758) 3329,
eqmod mem0_76_k1*(2**16) a_76*(2**16)+a_332*(-758) 3329,
eqmod mem0_334_k1*(2**16) a_78*(2**16)-a_334*(-758) 3329,
eqmod mem0_78_k1*(2**16) a_78*(2**16)+a_334*(-758) 3329,
eqmod mem0_336_k1*(2**16) a_80*(2**16)-a_336*(-758) 3329,
eqmod mem0_80_k1*(2**16) a_80*(2**16)+a_336*(-758) 3329,
eqmod mem0_338_k1*(2**16) a_82*(2**16)-a_338*(-758) 3329,
eqmod mem0_82_k1*(2**16) a_82*(2**16)+a_338*(-758) 3329,
eqmod mem0_340_k1*(2**16) a_84*(2**16)-a_340*(-758) 3329,
eqmod mem0_84_k1*(2**16) a_84*(2**16)+a_340*(-758) 3329,
eqmod mem0_342_k1*(2**16) a_86*(2**16)-a_342*(-758) 3329,
eqmod mem0_86_k1*(2**16) a_86*(2**16)+a_342*(-758) 3329,
eqmod mem0_344_k1*(2**16) a_88*(2**16)-a_344*(-758) 3329,
eqmod mem0_88_k1*(2**16) a_88*(2**16)+a_344*(-758) 3329,
eqmod mem0_346_k1*(2**16) a_90*(2**16)-a_346*(-758) 3329,
eqmod mem0_90_k1*(2**16) a_90*(2**16)+a_346*(-758) 3329,
eqmod mem0_348_k1*(2**16) a_92*(2**16)-a_348*(-758) 3329,
eqmod mem0_92_k1*(2**16) a_92*(2**16)+a_348*(-758) 3329,
eqmod mem0_350_k1*(2**16) a_94*(2**16)-a_350*(-758) 3329,
eqmod mem0_94_k1*(2**16) a_94*(2**16)+a_350*(-758) 3329,
eqmod mem0_352_k1*(2**16) a_96*(2**16)-a_352*(-758) 3329,
eqmod mem0_96_k1*(2**16) a_96*(2**16)+a_352*(-758) 3329,
eqmod mem0_354_k1*(2**16) a_98*(2**16)-a_354*(-758) 3329,
eqmod mem0_98_k1*(2**16) a_98*(2**16)+a_354*(-758) 3329,
eqmod mem0_356_k1*(2**16) a_100*(2**16)-a_356*(-758) 3329,
eqmod mem0_100_k1*(2**16) a_100*(2**16)+a_356*(-758) 3329,
eqmod mem0_358_k1*(2**16) a_102*(2**16)-a_358*(-758) 3329,
eqmod mem0_102_k1*(2**16) a_102*(2**16)+a_358*(-758) 3329,
eqmod mem0_360_k1*(2**16) a_104*(2**16)-a_360*(-758) 3329,
eqmod mem0_104_k1*(2**16) a_104*(2**16)+a_360*(-758) 3329,
eqmod mem0_362_k1*(2**16) a_106*(2**16)-a_362*(-758) 3329,
eqmod mem0_106_k1*(2**16) a_106*(2**16)+a_362*(-758) 3329,
eqmod mem0_364_k1*(2**16) a_108*(2**16)-a_364*(-758) 3329,
eqmod mem0_108_k1*(2**16) a_108*(2**16)+a_364*(-758) 3329,
eqmod mem0_366_k1*(2**16) a_110*(2**16)-a_366*(-758) 3329,
eqmod mem0_110_k1*(2**16) a_110*(2**16)+a_366*(-758) 3329,
eqmod mem0_368_k1*(2**16) a_112*(2**16)-a_368*(-758) 3329,
eqmod mem0_112_k1*(2**16) a_112*(2**16)+a_368*(-758) 3329,
eqmod mem0_370_k1*(2**16) a_114*(2**16)-a_370*(-758) 3329,
eqmod mem0_114_k1*(2**16) a_114*(2**16)+a_370*(-758) 3329,
eqmod mem0_372_k1*(2**16) a_116*(2**16)-a_372*(-758) 3329,
eqmod mem0_116_k1*(2**16) a_116*(2**16)+a_372*(-758) 3329,
eqmod mem0_374_k1*(2**16) a_118*(2**16)-a_374*(-758) 3329,
eqmod mem0_118_k1*(2**16) a_118*(2**16)+a_374*(-758) 3329,
eqmod mem0_376_k1*(2**16) a_120*(2**16)-a_376*(-758) 3329,
eqmod mem0_120_k1*(2**16) a_120*(2**16)+a_376*(-758) 3329,
eqmod mem0_378_k1*(2**16) a_122*(2**16)-a_378*(-758) 3329,
eqmod mem0_122_k1*(2**16) a_122*(2**16)+a_378*(-758) 3329,
eqmod mem0_380_k1*(2**16) a_124*(2**16)-a_380*(-758) 3329,
eqmod mem0_124_k1*(2**16) a_124*(2**16)+a_380*(-758) 3329,
eqmod mem0_382_k1*(2**16) a_126*(2**16)-a_382*(-758) 3329,
eqmod mem0_126_k1*(2**16) a_126*(2**16)+a_382*(-758) 3329,
eqmod mem0_384_k1*(2**16) a_128*(2**16)-a_384*(-758) 3329,
eqmod mem0_128_k1*(2**16) a_128*(2**16)+a_384*(-758) 3329,
eqmod mem0_386_k1*(2**16) a_130*(2**16)-a_386*(-758) 3329,
eqmod mem0_130_k1*(2**16) a_130*(2**16)+a_386*(-758) 3329,
eqmod mem0_388_k1*(2**16) a_132*(2**16)-a_388*(-758) 3329,
eqmod mem0_132_k1*(2**16) a_132*(2**16)+a_388*(-758) 3329,
eqmod mem0_390_k1*(2**16) a_134*(2**16)-a_390*(-758) 3329,
eqmod mem0_134_k1*(2**16) a_134*(2**16)+a_390*(-758) 3329,
eqmod mem0_392_k1*(2**16) a_136*(2**16)-a_392*(-758) 3329,
eqmod mem0_136_k1*(2**16) a_136*(2**16)+a_392*(-758) 3329,
eqmod mem0_394_k1*(2**16) a_138*(2**16)-a_394*(-758) 3329,
eqmod mem0_138_k1*(2**16) a_138*(2**16)+a_394*(-758) 3329,
eqmod mem0_396_k1*(2**16) a_140*(2**16)-a_396*(-758) 3329,
eqmod mem0_140_k1*(2**16) a_140*(2**16)+a_396*(-758) 3329,
eqmod mem0_398_k1*(2**16) a_142*(2**16)-a_398*(-758) 3329,
eqmod mem0_142_k1*(2**16) a_142*(2**16)+a_398*(-758) 3329,
eqmod mem0_400_k1*(2**16) a_144*(2**16)-a_400*(-758) 3329,
eqmod mem0_144_k1*(2**16) a_144*(2**16)+a_400*(-758) 3329,
eqmod mem0_402_k1*(2**16) a_146*(2**16)-a_402*(-758) 3329,
eqmod mem0_146_k1*(2**16) a_146*(2**16)+a_402*(-758) 3329,
eqmod mem0_404_k1*(2**16) a_148*(2**16)-a_404*(-758) 3329,
eqmod mem0_148_k1*(2**16) a_148*(2**16)+a_404*(-758) 3329,
eqmod mem0_406_k1*(2**16) a_150*(2**16)-a_406*(-758) 3329,
eqmod mem0_150_k1*(2**16) a_150*(2**16)+a_406*(-758) 3329,
eqmod mem0_408_k1*(2**16) a_152*(2**16)-a_408*(-758) 3329,
eqmod mem0_152_k1*(2**16) a_152*(2**16)+a_408*(-758) 3329,
eqmod mem0_410_k1*(2**16) a_154*(2**16)-a_410*(-758) 3329,
eqmod mem0_154_k1*(2**16) a_154*(2**16)+a_410*(-758) 3329,
eqmod mem0_412_k1*(2**16) a_156*(2**16)-a_412*(-758) 3329,
eqmod mem0_156_k1*(2**16) a_156*(2**16)+a_412*(-758) 3329,
eqmod mem0_414_k1*(2**16) a_158*(2**16)-a_414*(-758) 3329,
eqmod mem0_158_k1*(2**16) a_158*(2**16)+a_414*(-758) 3329,
eqmod mem0_416_k1*(2**16) a_160*(2**16)-a_416*(-758) 3329,
eqmod mem0_160_k1*(2**16) a_160*(2**16)+a_416*(-758) 3329,
eqmod mem0_418_k1*(2**16) a_162*(2**16)-a_418*(-758) 3329,
eqmod mem0_162_k1*(2**16) a_162*(2**16)+a_418*(-758) 3329,
eqmod mem0_420_k1*(2**16) a_164*(2**16)-a_420*(-758) 3329,
eqmod mem0_164_k1*(2**16) a_164*(2**16)+a_420*(-758) 3329,
eqmod mem0_422_k1*(2**16) a_166*(2**16)-a_422*(-758) 3329,
eqmod mem0_166_k1*(2**16) a_166*(2**16)+a_422*(-758) 3329,
eqmod mem0_424_k1*(2**16) a_168*(2**16)-a_424*(-758) 3329,
eqmod mem0_168_k1*(2**16) a_168*(2**16)+a_424*(-758) 3329,
eqmod mem0_426_k1*(2**16) a_170*(2**16)-a_426*(-758) 3329,
eqmod mem0_170_k1*(2**16) a_170*(2**16)+a_426*(-758) 3329,
eqmod mem0_428_k1*(2**16) a_172*(2**16)-a_428*(-758) 3329,
eqmod mem0_172_k1*(2**16) a_172*(2**16)+a_428*(-758) 3329,
eqmod mem0_430_k1*(2**16) a_174*(2**16)-a_430*(-758) 3329,
eqmod mem0_174_k1*(2**16) a_174*(2**16)+a_430*(-758) 3329,
eqmod mem0_432_k1*(2**16) a_176*(2**16)-a_432*(-758) 3329,
eqmod mem0_176_k1*(2**16) a_176*(2**16)+a_432*(-758) 3329,
eqmod mem0_434_k1*(2**16) a_178*(2**16)-a_434*(-758) 3329,
eqmod mem0_178_k1*(2**16) a_178*(2**16)+a_434*(-758) 3329,
eqmod mem0_436_k1*(2**16) a_180*(2**16)-a_436*(-758) 3329,
eqmod mem0_180_k1*(2**16) a_180*(2**16)+a_436*(-758) 3329,
eqmod mem0_438_k1*(2**16) a_182*(2**16)-a_438*(-758) 3329,
eqmod mem0_182_k1*(2**16) a_182*(2**16)+a_438*(-758) 3329,
eqmod mem0_440_k1*(2**16) a_184*(2**16)-a_440*(-758) 3329,
eqmod mem0_184_k1*(2**16) a_184*(2**16)+a_440*(-758) 3329,
eqmod mem0_442_k1*(2**16) a_186*(2**16)-a_442*(-758) 3329,
eqmod mem0_186_k1*(2**16) a_186*(2**16)+a_442*(-758) 3329,
eqmod mem0_444_k1*(2**16) a_188*(2**16)-a_444*(-758) 3329,
eqmod mem0_188_k1*(2**16) a_188*(2**16)+a_444*(-758) 3329,
eqmod mem0_446_k1*(2**16) a_190*(2**16)-a_446*(-758) 3329,
eqmod mem0_190_k1*(2**16) a_190*(2**16)+a_446*(-758) 3329,
eqmod mem0_448_k1*(2**16) a_192*(2**16)-a_448*(-758) 3329,
eqmod mem0_192_k1*(2**16) a_192*(2**16)+a_448*(-758) 3329,
eqmod mem0_450_k1*(2**16) a_194*(2**16)-a_450*(-758) 3329,
eqmod mem0_194_k1*(2**16) a_194*(2**16)+a_450*(-758) 3329,
eqmod mem0_452_k1*(2**16) a_196*(2**16)-a_452*(-758) 3329,
eqmod mem0_196_k1*(2**16) a_196*(2**16)+a_452*(-758) 3329,
eqmod mem0_454_k1*(2**16) a_198*(2**16)-a_454*(-758) 3329,
eqmod mem0_198_k1*(2**16) a_198*(2**16)+a_454*(-758) 3329,
eqmod mem0_456_k1*(2**16) a_200*(2**16)-a_456*(-758) 3329,
eqmod mem0_200_k1*(2**16) a_200*(2**16)+a_456*(-758) 3329,
eqmod mem0_458_k1*(2**16) a_202*(2**16)-a_458*(-758) 3329,
eqmod mem0_202_k1*(2**16) a_202*(2**16)+a_458*(-758) 3329,
eqmod mem0_460_k1*(2**16) a_204*(2**16)-a_460*(-758) 3329,
eqmod mem0_204_k1*(2**16) a_204*(2**16)+a_460*(-758) 3329,
eqmod mem0_462_k1*(2**16) a_206*(2**16)-a_462*(-758) 3329,
eqmod mem0_206_k1*(2**16) a_206*(2**16)+a_462*(-758) 3329,
eqmod mem0_464_k1*(2**16) a_208*(2**16)-a_464*(-758) 3329,
eqmod mem0_208_k1*(2**16) a_208*(2**16)+a_464*(-758) 3329,
eqmod mem0_466_k1*(2**16) a_210*(2**16)-a_466*(-758) 3329,
eqmod mem0_210_k1*(2**16) a_210*(2**16)+a_466*(-758) 3329,
eqmod mem0_468_k1*(2**16) a_212*(2**16)-a_468*(-758) 3329,
eqmod mem0_212_k1*(2**16) a_212*(2**16)+a_468*(-758) 3329,
eqmod mem0_470_k1*(2**16) a_214*(2**16)-a_470*(-758) 3329,
eqmod mem0_214_k1*(2**16) a_214*(2**16)+a_470*(-758) 3329,
eqmod mem0_472_k1*(2**16) a_216*(2**16)-a_472*(-758) 3329,
eqmod mem0_216_k1*(2**16) a_216*(2**16)+a_472*(-758) 3329,
eqmod mem0_474_k1*(2**16) a_218*(2**16)-a_474*(-758) 3329,
eqmod mem0_218_k1*(2**16) a_218*(2**16)+a_474*(-758) 3329,
eqmod mem0_476_k1*(2**16) a_220*(2**16)-a_476*(-758) 3329,
eqmod mem0_220_k1*(2**16) a_220*(2**16)+a_476*(-758) 3329,
eqmod mem0_478_k1*(2**16) a_222*(2**16)-a_478*(-758) 3329,
eqmod mem0_222_k1*(2**16) a_222*(2**16)+a_478*(-758) 3329,
eqmod mem0_480_k1*(2**16) a_224*(2**16)-a_480*(-758) 3329,
eqmod mem0_224_k1*(2**16) a_224*(2**16)+a_480*(-758) 3329,
eqmod mem0_482_k1*(2**16) a_226*(2**16)-a_482*(-758) 3329,
eqmod mem0_226_k1*(2**16) a_226*(2**16)+a_482*(-758) 3329,
eqmod mem0_484_k1*(2**16) a_228*(2**16)-a_484*(-758) 3329,
eqmod mem0_228_k1*(2**16) a_228*(2**16)+a_484*(-758) 3329,
eqmod mem0_486_k1*(2**16) a_230*(2**16)-a_486*(-758) 3329,
eqmod mem0_230_k1*(2**16) a_230*(2**16)+a_486*(-758) 3329,
eqmod mem0_488_k1*(2**16) a_232*(2**16)-a_488*(-758) 3329,
eqmod mem0_232_k1*(2**16) a_232*(2**16)+a_488*(-758) 3329,
eqmod mem0_490_k1*(2**16) a_234*(2**16)-a_490*(-758) 3329,
eqmod mem0_234_k1*(2**16) a_234*(2**16)+a_490*(-758) 3329,
eqmod mem0_492_k1*(2**16) a_236*(2**16)-a_492*(-758) 3329,
eqmod mem0_236_k1*(2**16) a_236*(2**16)+a_492*(-758) 3329,
eqmod mem0_494_k1*(2**16) a_238*(2**16)-a_494*(-758) 3329,
eqmod mem0_238_k1*(2**16) a_238*(2**16)+a_494*(-758) 3329,
eqmod mem0_496_k1*(2**16) a_240*(2**16)-a_496*(-758) 3329,
eqmod mem0_240_k1*(2**16) a_240*(2**16)+a_496*(-758) 3329,
eqmod mem0_498_k1*(2**16) a_242*(2**16)-a_498*(-758) 3329,
eqmod mem0_242_k1*(2**16) a_242*(2**16)+a_498*(-758) 3329,
eqmod mem0_500_k1*(2**16) a_244*(2**16)-a_500*(-758) 3329,
eqmod mem0_244_k1*(2**16) a_244*(2**16)+a_500*(-758) 3329,
eqmod mem0_502_k1*(2**16) a_246*(2**16)-a_502*(-758) 3329,
eqmod mem0_246_k1*(2**16) a_246*(2**16)+a_502*(-758) 3329,
eqmod mem0_504_k1*(2**16) a_248*(2**16)-a_504*(-758) 3329,
eqmod mem0_248_k1*(2**16) a_248*(2**16)+a_504*(-758) 3329,
eqmod mem0_506_k1*(2**16) a_250*(2**16)-a_506*(-758) 3329,
eqmod mem0_250_k1*(2**16) a_250*(2**16)+a_506*(-758) 3329,
eqmod mem0_508_k1*(2**16) a_252*(2**16)-a_508*(-758) 3329,
eqmod mem0_252_k1*(2**16) a_252*(2**16)+a_508*(-758) 3329,
eqmod mem0_510_k1*(2**16) a_254*(2**16)-a_510*(-758) 3329,
eqmod mem0_254_k1*(2**16) a_254*(2**16)+a_510*(-758) 3329

] && and [

    (-3)@16 * 3329@16 <s mem0_0, mem0_0 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_2, mem0_2 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_4, mem0_4 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_6, mem0_6 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_8, mem0_8 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_10, mem0_10 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_12, mem0_12 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_14, mem0_14 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_16, mem0_16 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_18, mem0_18 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_20, mem0_20 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_22, mem0_22 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_24, mem0_24 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_26, mem0_26 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_28, mem0_28 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_30, mem0_30 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_32, mem0_32 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_34, mem0_34 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_36, mem0_36 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_38, mem0_38 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_40, mem0_40 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_42, mem0_42 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_44, mem0_44 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_46, mem0_46 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_48, mem0_48 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_50, mem0_50 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_52, mem0_52 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_54, mem0_54 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_56, mem0_56 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_58, mem0_58 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_60, mem0_60 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_62, mem0_62 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_64, mem0_64 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_66, mem0_66 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_68, mem0_68 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_70, mem0_70 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_72, mem0_72 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_74, mem0_74 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_76, mem0_76 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_78, mem0_78 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_80, mem0_80 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_82, mem0_82 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_84, mem0_84 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_86, mem0_86 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_88, mem0_88 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_90, mem0_90 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_92, mem0_92 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_94, mem0_94 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_96, mem0_96 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_98, mem0_98 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_100, mem0_100 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_102, mem0_102 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_104, mem0_104 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_106, mem0_106 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_108, mem0_108 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_110, mem0_110 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_112, mem0_112 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_114, mem0_114 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_116, mem0_116 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_118, mem0_118 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_120, mem0_120 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_122, mem0_122 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_124, mem0_124 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_126, mem0_126 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_128, mem0_128 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_130, mem0_130 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_132, mem0_132 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_134, mem0_134 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_136, mem0_136 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_138, mem0_138 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_140, mem0_140 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_142, mem0_142 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_144, mem0_144 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_146, mem0_146 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_148, mem0_148 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_150, mem0_150 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_152, mem0_152 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_154, mem0_154 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_156, mem0_156 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_158, mem0_158 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_160, mem0_160 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_162, mem0_162 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_164, mem0_164 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_166, mem0_166 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_168, mem0_168 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_170, mem0_170 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_172, mem0_172 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_174, mem0_174 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_176, mem0_176 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_178, mem0_178 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_180, mem0_180 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_182, mem0_182 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_184, mem0_184 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_186, mem0_186 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_188, mem0_188 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_190, mem0_190 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_192, mem0_192 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_194, mem0_194 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_196, mem0_196 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_198, mem0_198 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_200, mem0_200 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_202, mem0_202 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_204, mem0_204 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_206, mem0_206 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_208, mem0_208 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_210, mem0_210 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_212, mem0_212 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_214, mem0_214 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_216, mem0_216 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_218, mem0_218 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_220, mem0_220 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_222, mem0_222 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_224, mem0_224 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_226, mem0_226 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_228, mem0_228 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_230, mem0_230 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_232, mem0_232 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_234, mem0_234 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_236, mem0_236 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_238, mem0_238 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_240, mem0_240 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_242, mem0_242 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_244, mem0_244 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_246, mem0_246 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_248, mem0_248 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_250, mem0_250 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_252, mem0_252 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_254, mem0_254 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_256, mem0_256 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_258, mem0_258 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_260, mem0_260 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_262, mem0_262 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_264, mem0_264 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_266, mem0_266 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_268, mem0_268 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_270, mem0_270 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_272, mem0_272 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_274, mem0_274 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_276, mem0_276 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_278, mem0_278 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_280, mem0_280 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_282, mem0_282 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_284, mem0_284 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_286, mem0_286 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_288, mem0_288 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_290, mem0_290 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_292, mem0_292 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_294, mem0_294 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_296, mem0_296 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_298, mem0_298 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_300, mem0_300 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_302, mem0_302 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_304, mem0_304 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_306, mem0_306 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_308, mem0_308 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_310, mem0_310 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_312, mem0_312 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_314, mem0_314 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_316, mem0_316 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_318, mem0_318 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_320, mem0_320 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_322, mem0_322 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_324, mem0_324 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_326, mem0_326 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_328, mem0_328 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_330, mem0_330 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_332, mem0_332 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_334, mem0_334 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_336, mem0_336 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_338, mem0_338 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_340, mem0_340 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_342, mem0_342 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_344, mem0_344 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_346, mem0_346 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_348, mem0_348 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_350, mem0_350 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_352, mem0_352 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_354, mem0_354 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_356, mem0_356 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_358, mem0_358 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_360, mem0_360 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_362, mem0_362 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_364, mem0_364 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_366, mem0_366 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_368, mem0_368 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_370, mem0_370 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_372, mem0_372 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_374, mem0_374 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_376, mem0_376 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_378, mem0_378 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_380, mem0_380 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_382, mem0_382 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_384, mem0_384 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_386, mem0_386 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_388, mem0_388 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_390, mem0_390 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_392, mem0_392 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_394, mem0_394 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_396, mem0_396 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_398, mem0_398 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_400, mem0_400 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_402, mem0_402 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_404, mem0_404 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_406, mem0_406 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_408, mem0_408 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_410, mem0_410 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_412, mem0_412 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_414, mem0_414 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_416, mem0_416 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_418, mem0_418 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_420, mem0_420 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_422, mem0_422 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_424, mem0_424 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_426, mem0_426 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_428, mem0_428 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_430, mem0_430 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_432, mem0_432 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_434, mem0_434 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_436, mem0_436 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_438, mem0_438 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_440, mem0_440 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_442, mem0_442 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_444, mem0_444 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_446, mem0_446 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_448, mem0_448 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_450, mem0_450 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_452, mem0_452 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_454, mem0_454 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_456, mem0_456 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_458, mem0_458 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_460, mem0_460 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_462, mem0_462 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_464, mem0_464 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_466, mem0_466 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_468, mem0_468 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_470, mem0_470 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_472, mem0_472 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_474, mem0_474 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_476, mem0_476 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_478, mem0_478 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_480, mem0_480 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_482, mem0_482 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_484, mem0_484 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_486, mem0_486 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_488, mem0_488 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_490, mem0_490 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_492, mem0_492 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_494, mem0_494 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_496, mem0_496 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_498, mem0_498 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_500, mem0_500 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_502, mem0_502 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_504, mem0_504 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_506, mem0_506 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_508, mem0_508 <s 3@16 * 3329@16,
    (-3)@16 * 3329@16 <s mem0_510, mem0_510 <s 3@16 * 3329@16

]
}

