(*_build/default/coqcryptoline.exe -v -jobs 16 -sat_solver cadical -sat_cert grat -no_carry_constraint ~/tmp/coqcv_ntt_k64_separated.cl
Parsing Cryptoline file:                [OK]            0.272112 seconds
*)

proc PQCLEAN_KYBER512_CLEAN_montgomery_reduce (sint32 v_a, sint16 ret) =
{ true
  && and [ (-3329)@32 * (2**15)@32 <=s v_a, v_a <s 3329@32 * (2**15)@32 ]
}

assume eqmod (ret * (2**16)) v_a 3329
    && and [ (-3329)@16 <s ret, ret <s 3329@16 ];

{ true && true }

proc main (  
	     sint16 mem0_0,   sint16 mem0_2,   sint16 mem0_4,   sint16 mem0_6,
             sint16 mem0_8,  sint16 mem0_10,  sint16 mem0_12,  sint16 mem0_14,
            sint16 mem0_16,  sint16 mem0_18,  sint16 mem0_20,  sint16 mem0_22,
            sint16 mem0_24,  sint16 mem0_26,  sint16 mem0_28,  sint16 mem0_30,
            sint16 mem0_32,  sint16 mem0_34,  sint16 mem0_36,  sint16 mem0_38,
            sint16 mem0_40,  sint16 mem0_42,  sint16 mem0_44,  sint16 mem0_46,
            sint16 mem0_48,  sint16 mem0_50,  sint16 mem0_52,  sint16 mem0_54,
            sint16 mem0_56,  sint16 mem0_58,  sint16 mem0_60,  sint16 mem0_62,
            sint16 mem0_64,  sint16 mem0_66,  sint16 mem0_68,  sint16 mem0_70,
            sint16 mem0_72,  sint16 mem0_74,  sint16 mem0_76,  sint16 mem0_78,
            sint16 mem0_80,  sint16 mem0_82,  sint16 mem0_84,  sint16 mem0_86,
            sint16 mem0_88,  sint16 mem0_90,  sint16 mem0_92,  sint16 mem0_94,
            sint16 mem0_96,  sint16 mem0_98, sint16 mem0_100, sint16 mem0_102,
           sint16 mem0_104, sint16 mem0_106, sint16 mem0_108, sint16 mem0_110,
           sint16 mem0_112, sint16 mem0_114, sint16 mem0_116, sint16 mem0_118,
           sint16 mem0_120, sint16 mem0_122, sint16 mem0_124, sint16 mem0_126,
           sint16 mem0_128, sint16 mem0_130, sint16 mem0_132, sint16 mem0_134,
           sint16 mem0_136, sint16 mem0_138, sint16 mem0_140, sint16 mem0_142,
           sint16 mem0_144, sint16 mem0_146, sint16 mem0_148, sint16 mem0_150,
           sint16 mem0_152, sint16 mem0_154, sint16 mem0_156, sint16 mem0_158,
           sint16 mem0_160, sint16 mem0_162, sint16 mem0_164, sint16 mem0_166,
           sint16 mem0_168, sint16 mem0_170, sint16 mem0_172, sint16 mem0_174,
           sint16 mem0_176, sint16 mem0_178, sint16 mem0_180, sint16 mem0_182,
           sint16 mem0_184, sint16 mem0_186, sint16 mem0_188, sint16 mem0_190,
           sint16 mem0_192, sint16 mem0_194, sint16 mem0_196, sint16 mem0_198,
           sint16 mem0_200, sint16 mem0_202, sint16 mem0_204, sint16 mem0_206,
           sint16 mem0_208, sint16 mem0_210, sint16 mem0_212, sint16 mem0_214,
           sint16 mem0_216, sint16 mem0_218, sint16 mem0_220, sint16 mem0_222,
           sint16 mem0_224, sint16 mem0_226, sint16 mem0_228, sint16 mem0_230,
           sint16 mem0_232, sint16 mem0_234, sint16 mem0_236, sint16 mem0_238,
           sint16 mem0_240, sint16 mem0_242, sint16 mem0_244, sint16 mem0_246,
           sint16 mem0_248, sint16 mem0_250, sint16 mem0_252, sint16 mem0_254,
           sint16 mem0_256, sint16 mem0_258, sint16 mem0_260, sint16 mem0_262,
           sint16 mem0_264, sint16 mem0_266, sint16 mem0_268, sint16 mem0_270,
           sint16 mem0_272, sint16 mem0_274, sint16 mem0_276, sint16 mem0_278,
           sint16 mem0_280, sint16 mem0_282, sint16 mem0_284, sint16 mem0_286,
           sint16 mem0_288, sint16 mem0_290, sint16 mem0_292, sint16 mem0_294,
           sint16 mem0_296, sint16 mem0_298, sint16 mem0_300, sint16 mem0_302,
           sint16 mem0_304, sint16 mem0_306, sint16 mem0_308, sint16 mem0_310,
           sint16 mem0_312, sint16 mem0_314, sint16 mem0_316, sint16 mem0_318,
           sint16 mem0_320, sint16 mem0_322, sint16 mem0_324, sint16 mem0_326,
           sint16 mem0_328, sint16 mem0_330, sint16 mem0_332, sint16 mem0_334,
           sint16 mem0_336, sint16 mem0_338, sint16 mem0_340, sint16 mem0_342,
           sint16 mem0_344, sint16 mem0_346, sint16 mem0_348, sint16 mem0_350,
           sint16 mem0_352, sint16 mem0_354, sint16 mem0_356, sint16 mem0_358,
           sint16 mem0_360, sint16 mem0_362, sint16 mem0_364, sint16 mem0_366,
           sint16 mem0_368, sint16 mem0_370, sint16 mem0_372, sint16 mem0_374,
           sint16 mem0_376, sint16 mem0_378, sint16 mem0_380, sint16 mem0_382,
           sint16 mem0_384, sint16 mem0_386, sint16 mem0_388, sint16 mem0_390,
           sint16 mem0_392, sint16 mem0_394, sint16 mem0_396, sint16 mem0_398,
           sint16 mem0_400, sint16 mem0_402, sint16 mem0_404, sint16 mem0_406,
           sint16 mem0_408, sint16 mem0_410, sint16 mem0_412, sint16 mem0_414,
           sint16 mem0_416, sint16 mem0_418, sint16 mem0_420, sint16 mem0_422,
           sint16 mem0_424, sint16 mem0_426, sint16 mem0_428, sint16 mem0_430,
           sint16 mem0_432, sint16 mem0_434, sint16 mem0_436, sint16 mem0_438,
           sint16 mem0_440, sint16 mem0_442, sint16 mem0_444, sint16 mem0_446,
           sint16 mem0_448, sint16 mem0_450, sint16 mem0_452, sint16 mem0_454,
           sint16 mem0_456, sint16 mem0_458, sint16 mem0_460, sint16 mem0_462,
           sint16 mem0_464, sint16 mem0_466, sint16 mem0_468, sint16 mem0_470,
           sint16 mem0_472, sint16 mem0_474, sint16 mem0_476, sint16 mem0_478,
           sint16 mem0_480, sint16 mem0_482, sint16 mem0_484, sint16 mem0_486,
           sint16 mem0_488, sint16 mem0_490, sint16 mem0_492, sint16 mem0_494,
           sint16 mem0_496, sint16 mem0_498, sint16 mem0_500, sint16 mem0_502,
           sint16 mem0_504, sint16 mem0_506, sint16 mem0_508, sint16 mem0_510, bit x) =

{
true
&& and [
    (-8)@16 * 3329@16 <s mem0_0, mem0_0 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_2, mem0_2 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_4, mem0_4 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_6, mem0_6 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_8, mem0_8 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_10, mem0_10 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_12, mem0_12 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_14, mem0_14 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_16, mem0_16 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_18, mem0_18 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_20, mem0_20 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_22, mem0_22 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_24, mem0_24 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_26, mem0_26 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_28, mem0_28 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_30, mem0_30 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_32, mem0_32 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_34, mem0_34 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_36, mem0_36 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_38, mem0_38 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_40, mem0_40 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_42, mem0_42 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_44, mem0_44 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_46, mem0_46 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_48, mem0_48 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_50, mem0_50 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_52, mem0_52 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_54, mem0_54 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_56, mem0_56 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_58, mem0_58 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_60, mem0_60 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_62, mem0_62 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_64, mem0_64 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_66, mem0_66 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_68, mem0_68 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_70, mem0_70 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_72, mem0_72 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_74, mem0_74 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_76, mem0_76 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_78, mem0_78 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_80, mem0_80 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_82, mem0_82 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_84, mem0_84 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_86, mem0_86 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_88, mem0_88 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_90, mem0_90 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_92, mem0_92 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_94, mem0_94 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_96, mem0_96 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_98, mem0_98 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_100, mem0_100 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_102, mem0_102 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_104, mem0_104 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_106, mem0_106 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_108, mem0_108 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_110, mem0_110 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_112, mem0_112 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_114, mem0_114 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_116, mem0_116 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_118, mem0_118 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_120, mem0_120 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_122, mem0_122 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_124, mem0_124 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_126, mem0_126 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_128, mem0_128 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_130, mem0_130 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_132, mem0_132 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_134, mem0_134 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_136, mem0_136 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_138, mem0_138 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_140, mem0_140 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_142, mem0_142 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_144, mem0_144 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_146, mem0_146 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_148, mem0_148 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_150, mem0_150 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_152, mem0_152 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_154, mem0_154 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_156, mem0_156 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_158, mem0_158 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_160, mem0_160 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_162, mem0_162 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_164, mem0_164 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_166, mem0_166 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_168, mem0_168 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_170, mem0_170 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_172, mem0_172 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_174, mem0_174 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_176, mem0_176 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_178, mem0_178 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_180, mem0_180 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_182, mem0_182 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_184, mem0_184 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_186, mem0_186 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_188, mem0_188 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_190, mem0_190 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_192, mem0_192 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_194, mem0_194 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_196, mem0_196 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_198, mem0_198 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_200, mem0_200 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_202, mem0_202 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_204, mem0_204 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_206, mem0_206 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_208, mem0_208 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_210, mem0_210 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_212, mem0_212 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_214, mem0_214 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_216, mem0_216 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_218, mem0_218 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_220, mem0_220 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_222, mem0_222 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_224, mem0_224 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_226, mem0_226 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_228, mem0_228 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_230, mem0_230 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_232, mem0_232 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_234, mem0_234 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_236, mem0_236 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_238, mem0_238 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_240, mem0_240 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_242, mem0_242 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_244, mem0_244 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_246, mem0_246 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_248, mem0_248 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_250, mem0_250 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_252, mem0_252 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_254, mem0_254 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_256, mem0_256 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_258, mem0_258 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_260, mem0_260 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_262, mem0_262 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_264, mem0_264 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_266, mem0_266 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_268, mem0_268 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_270, mem0_270 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_272, mem0_272 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_274, mem0_274 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_276, mem0_276 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_278, mem0_278 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_280, mem0_280 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_282, mem0_282 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_284, mem0_284 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_286, mem0_286 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_288, mem0_288 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_290, mem0_290 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_292, mem0_292 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_294, mem0_294 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_296, mem0_296 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_298, mem0_298 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_300, mem0_300 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_302, mem0_302 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_304, mem0_304 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_306, mem0_306 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_308, mem0_308 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_310, mem0_310 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_312, mem0_312 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_314, mem0_314 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_316, mem0_316 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_318, mem0_318 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_320, mem0_320 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_322, mem0_322 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_324, mem0_324 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_326, mem0_326 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_328, mem0_328 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_330, mem0_330 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_332, mem0_332 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_334, mem0_334 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_336, mem0_336 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_338, mem0_338 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_340, mem0_340 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_342, mem0_342 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_344, mem0_344 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_346, mem0_346 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_348, mem0_348 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_350, mem0_350 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_352, mem0_352 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_354, mem0_354 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_356, mem0_356 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_358, mem0_358 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_360, mem0_360 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_362, mem0_362 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_364, mem0_364 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_366, mem0_366 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_368, mem0_368 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_370, mem0_370 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_372, mem0_372 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_374, mem0_374 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_376, mem0_376 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_378, mem0_378 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_380, mem0_380 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_382, mem0_382 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_384, mem0_384 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_386, mem0_386 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_388, mem0_388 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_390, mem0_390 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_392, mem0_392 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_394, mem0_394 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_396, mem0_396 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_398, mem0_398 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_400, mem0_400 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_402, mem0_402 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_404, mem0_404 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_406, mem0_406 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_408, mem0_408 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_410, mem0_410 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_412, mem0_412 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_414, mem0_414 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_416, mem0_416 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_418, mem0_418 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_420, mem0_420 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_422, mem0_422 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_424, mem0_424 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_426, mem0_426 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_428, mem0_428 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_430, mem0_430 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_432, mem0_432 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_434, mem0_434 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_436, mem0_436 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_438, mem0_438 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_440, mem0_440 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_442, mem0_442 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_444, mem0_444 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_446, mem0_446 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_448, mem0_448 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_450, mem0_450 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_452, mem0_452 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_454, mem0_454 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_456, mem0_456 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_458, mem0_458 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_460, mem0_460 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_462, mem0_462 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_464, mem0_464 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_466, mem0_466 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_468, mem0_468 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_470, mem0_470 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_472, mem0_472 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_474, mem0_474 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_476, mem0_476 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_478, mem0_478 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_480, mem0_480 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_482, mem0_482 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_484, mem0_484 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_486, mem0_486 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_488, mem0_488 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_490, mem0_490 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_492, mem0_492 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_494, mem0_494 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_496, mem0_496 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_498, mem0_498 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_500, mem0_500 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_502, mem0_502 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_504, mem0_504 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_506, mem0_506 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_508, mem0_508 <s 8@16 * 3329@16,
    (-8)@16 * 3329@16 <s mem0_510, mem0_510 <s 8@16 * 3329@16
]
}

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

mov mem0_0_k63 mem0_0;
mov mem0_2_k63 mem0_2;
mov mem0_4_k63 mem0_4;
mov mem0_6_k63 mem0_6;
mov mem0_8_k63 mem0_8;
mov mem0_10_k63 mem0_10;
mov mem0_12_k63 mem0_12;
mov mem0_14_k63 mem0_14;
mov mem0_16_k63 mem0_16;
mov mem0_18_k63 mem0_18;
mov mem0_20_k63 mem0_20;
mov mem0_22_k63 mem0_22;
mov mem0_24_k63 mem0_24;
mov mem0_26_k63 mem0_26;
mov mem0_28_k63 mem0_28;
mov mem0_30_k63 mem0_30;
mov mem0_32_k63 mem0_32;
mov mem0_34_k63 mem0_34;
mov mem0_36_k63 mem0_36;
mov mem0_38_k63 mem0_38;
mov mem0_40_k63 mem0_40;
mov mem0_42_k63 mem0_42;
mov mem0_44_k63 mem0_44;
mov mem0_46_k63 mem0_46;
mov mem0_48_k63 mem0_48;
mov mem0_50_k63 mem0_50;
mov mem0_52_k63 mem0_52;
mov mem0_54_k63 mem0_54;
mov mem0_56_k63 mem0_56;
mov mem0_58_k63 mem0_58;
mov mem0_60_k63 mem0_60;
mov mem0_62_k63 mem0_62;
mov mem0_64_k63 mem0_64;
mov mem0_66_k63 mem0_66;
mov mem0_68_k63 mem0_68;
mov mem0_70_k63 mem0_70;
mov mem0_72_k63 mem0_72;
mov mem0_74_k63 mem0_74;
mov mem0_76_k63 mem0_76;
mov mem0_78_k63 mem0_78;
mov mem0_80_k63 mem0_80;
mov mem0_82_k63 mem0_82;
mov mem0_84_k63 mem0_84;
mov mem0_86_k63 mem0_86;
mov mem0_88_k63 mem0_88;
mov mem0_90_k63 mem0_90;
mov mem0_92_k63 mem0_92;
mov mem0_94_k63 mem0_94;
mov mem0_96_k63 mem0_96;
mov mem0_98_k63 mem0_98;
mov mem0_100_k63 mem0_100;
mov mem0_102_k63 mem0_102;
mov mem0_104_k63 mem0_104;
mov mem0_106_k63 mem0_106;
mov mem0_108_k63 mem0_108;
mov mem0_110_k63 mem0_110;
mov mem0_112_k63 mem0_112;
mov mem0_114_k63 mem0_114;
mov mem0_116_k63 mem0_116;
mov mem0_118_k63 mem0_118;
mov mem0_120_k63 mem0_120;
mov mem0_122_k63 mem0_122;
mov mem0_124_k63 mem0_124;
mov mem0_126_k63 mem0_126;
mov mem0_128_k63 mem0_128;
mov mem0_130_k63 mem0_130;
mov mem0_132_k63 mem0_132;
mov mem0_134_k63 mem0_134;
mov mem0_136_k63 mem0_136;
mov mem0_138_k63 mem0_138;
mov mem0_140_k63 mem0_140;
mov mem0_142_k63 mem0_142;
mov mem0_144_k63 mem0_144;
mov mem0_146_k63 mem0_146;
mov mem0_148_k63 mem0_148;
mov mem0_150_k63 mem0_150;
mov mem0_152_k63 mem0_152;
mov mem0_154_k63 mem0_154;
mov mem0_156_k63 mem0_156;
mov mem0_158_k63 mem0_158;
mov mem0_160_k63 mem0_160;
mov mem0_162_k63 mem0_162;
mov mem0_164_k63 mem0_164;
mov mem0_166_k63 mem0_166;
mov mem0_168_k63 mem0_168;
mov mem0_170_k63 mem0_170;
mov mem0_172_k63 mem0_172;
mov mem0_174_k63 mem0_174;
mov mem0_176_k63 mem0_176;
mov mem0_178_k63 mem0_178;
mov mem0_180_k63 mem0_180;
mov mem0_182_k63 mem0_182;
mov mem0_184_k63 mem0_184;
mov mem0_186_k63 mem0_186;
mov mem0_188_k63 mem0_188;
mov mem0_190_k63 mem0_190;
mov mem0_192_k63 mem0_192;
mov mem0_194_k63 mem0_194;
mov mem0_196_k63 mem0_196;
mov mem0_198_k63 mem0_198;
mov mem0_200_k63 mem0_200;
mov mem0_202_k63 mem0_202;
mov mem0_204_k63 mem0_204;
mov mem0_206_k63 mem0_206;
mov mem0_208_k63 mem0_208;
mov mem0_210_k63 mem0_210;
mov mem0_212_k63 mem0_212;
mov mem0_214_k63 mem0_214;
mov mem0_216_k63 mem0_216;
mov mem0_218_k63 mem0_218;
mov mem0_220_k63 mem0_220;
mov mem0_222_k63 mem0_222;
mov mem0_224_k63 mem0_224;
mov mem0_226_k63 mem0_226;
mov mem0_228_k63 mem0_228;
mov mem0_230_k63 mem0_230;
mov mem0_232_k63 mem0_232;
mov mem0_234_k63 mem0_234;
mov mem0_236_k63 mem0_236;
mov mem0_238_k63 mem0_238;
mov mem0_240_k63 mem0_240;
mov mem0_242_k63 mem0_242;
mov mem0_244_k63 mem0_244;
mov mem0_246_k63 mem0_246;
mov mem0_248_k63 mem0_248;
mov mem0_250_k63 mem0_250;
mov mem0_252_k63 mem0_252;
mov mem0_254_k63 mem0_254;
mov mem0_256_k63 mem0_256;
mov mem0_258_k63 mem0_258;
mov mem0_260_k63 mem0_260;
mov mem0_262_k63 mem0_262;
mov mem0_264_k63 mem0_264;
mov mem0_266_k63 mem0_266;
mov mem0_268_k63 mem0_268;
mov mem0_270_k63 mem0_270;
mov mem0_272_k63 mem0_272;
mov mem0_274_k63 mem0_274;
mov mem0_276_k63 mem0_276;
mov mem0_278_k63 mem0_278;
mov mem0_280_k63 mem0_280;
mov mem0_282_k63 mem0_282;
mov mem0_284_k63 mem0_284;
mov mem0_286_k63 mem0_286;
mov mem0_288_k63 mem0_288;
mov mem0_290_k63 mem0_290;
mov mem0_292_k63 mem0_292;
mov mem0_294_k63 mem0_294;
mov mem0_296_k63 mem0_296;
mov mem0_298_k63 mem0_298;
mov mem0_300_k63 mem0_300;
mov mem0_302_k63 mem0_302;
mov mem0_304_k63 mem0_304;
mov mem0_306_k63 mem0_306;
mov mem0_308_k63 mem0_308;
mov mem0_310_k63 mem0_310;
mov mem0_312_k63 mem0_312;
mov mem0_314_k63 mem0_314;
mov mem0_316_k63 mem0_316;
mov mem0_318_k63 mem0_318;
mov mem0_320_k63 mem0_320;
mov mem0_322_k63 mem0_322;
mov mem0_324_k63 mem0_324;
mov mem0_326_k63 mem0_326;
mov mem0_328_k63 mem0_328;
mov mem0_330_k63 mem0_330;
mov mem0_332_k63 mem0_332;
mov mem0_334_k63 mem0_334;
mov mem0_336_k63 mem0_336;
mov mem0_338_k63 mem0_338;
mov mem0_340_k63 mem0_340;
mov mem0_342_k63 mem0_342;
mov mem0_344_k63 mem0_344;
mov mem0_346_k63 mem0_346;
mov mem0_348_k63 mem0_348;
mov mem0_350_k63 mem0_350;
mov mem0_352_k63 mem0_352;
mov mem0_354_k63 mem0_354;
mov mem0_356_k63 mem0_356;
mov mem0_358_k63 mem0_358;
mov mem0_360_k63 mem0_360;
mov mem0_362_k63 mem0_362;
mov mem0_364_k63 mem0_364;
mov mem0_366_k63 mem0_366;
mov mem0_368_k63 mem0_368;
mov mem0_370_k63 mem0_370;
mov mem0_372_k63 mem0_372;
mov mem0_374_k63 mem0_374;
mov mem0_376_k63 mem0_376;
mov mem0_378_k63 mem0_378;
mov mem0_380_k63 mem0_380;
mov mem0_382_k63 mem0_382;
mov mem0_384_k63 mem0_384;
mov mem0_386_k63 mem0_386;
mov mem0_388_k63 mem0_388;
mov mem0_390_k63 mem0_390;
mov mem0_392_k63 mem0_392;
mov mem0_394_k63 mem0_394;
mov mem0_396_k63 mem0_396;
mov mem0_398_k63 mem0_398;
mov mem0_400_k63 mem0_400;
mov mem0_402_k63 mem0_402;
mov mem0_404_k63 mem0_404;
mov mem0_406_k63 mem0_406;
mov mem0_408_k63 mem0_408;
mov mem0_410_k63 mem0_410;
mov mem0_412_k63 mem0_412;
mov mem0_414_k63 mem0_414;
mov mem0_416_k63 mem0_416;
mov mem0_418_k63 mem0_418;
mov mem0_420_k63 mem0_420;
mov mem0_422_k63 mem0_422;
mov mem0_424_k63 mem0_424;
mov mem0_426_k63 mem0_426;
mov mem0_428_k63 mem0_428;
mov mem0_430_k63 mem0_430;
mov mem0_432_k63 mem0_432;
mov mem0_434_k63 mem0_434;
mov mem0_436_k63 mem0_436;
mov mem0_438_k63 mem0_438;
mov mem0_440_k63 mem0_440;
mov mem0_442_k63 mem0_442;
mov mem0_444_k63 mem0_444;
mov mem0_446_k63 mem0_446;
mov mem0_448_k63 mem0_448;
mov mem0_450_k63 mem0_450;
mov mem0_452_k63 mem0_452;
mov mem0_454_k63 mem0_454;
mov mem0_456_k63 mem0_456;
mov mem0_458_k63 mem0_458;
mov mem0_460_k63 mem0_460;
mov mem0_462_k63 mem0_462;
mov mem0_464_k63 mem0_464;
mov mem0_466_k63 mem0_466;
mov mem0_468_k63 mem0_468;
mov mem0_470_k63 mem0_470;
mov mem0_472_k63 mem0_472;
mov mem0_474_k63 mem0_474;
mov mem0_476_k63 mem0_476;
mov mem0_478_k63 mem0_478;
mov mem0_480_k63 mem0_480;
mov mem0_482_k63 mem0_482;
mov mem0_484_k63 mem0_484;
mov mem0_486_k63 mem0_486;
mov mem0_488_k63 mem0_488;
mov mem0_490_k63 mem0_490;
mov mem0_492_k63 mem0_492;
mov mem0_494_k63 mem0_494;
mov mem0_496_k63 mem0_496;
mov mem0_498_k63 mem0_498;
mov mem0_500_k63 mem0_500;
mov mem0_502_k63 mem0_502;
mov mem0_504_k63 mem0_504;
mov mem0_506_k63 mem0_506;
mov mem0_508_k63 mem0_508;
mov mem0_510_k63 mem0_510;

(* NOTE: k = 64 *)

(*   %arrayidx9.6 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %1536 = load i16, i16* %arrayidx9.6, align 2, !tbaa !3 *)
mov v1536 mem0_4;
(*   %conv1.i.6 = sext i16 %1536 to i32 *)
cast v_conv1_i_6@sint32 v1536@sint16;
(*   %mul.i.6 = mul nsw i32 %conv1.i.6, -1103 *)
mul v_mul_i_6 v_conv1_i_6 (-1103)@sint32;
(*   %call.i.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6, v_call_i_6);
(*   %1537 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v1537 mem0_0;
(*   %sub.6 = sub i16 %1537, %call.i.6 *)
sub v_sub_6 v1537 v_call_i_6;
(*   store i16 %sub.6, i16* %arrayidx9.6, align 2, !tbaa !3 *)
mov mem0_4 v_sub_6;
(*   %add21.6 = add i16 %1537, %call.i.6 *)
add v_add21_6 v1537 v_call_i_6;
(*   store i16 %add21.6, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21_6;
(*   %arrayidx9.6.1 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %1538 = load i16, i16* %arrayidx9.6.1, align 2, !tbaa !3 *)
mov v1538 mem0_6;
(*   %conv1.i.6.1 = sext i16 %1538 to i32 *)
cast v_conv1_i_6_1@sint32 v1538@sint16;
(*   %mul.i.6.1 = mul nsw i32 %conv1.i.6.1, -1103 *)
mul v_mul_i_6_1 v_conv1_i_6_1 (-1103)@sint32;
(*   %call.i.6.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1, v_call_i_6_1);
(*   %arrayidx11.6.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %1539 = load i16, i16* %arrayidx11.6.1, align 2, !tbaa !3 *)
mov v1539 mem0_2;
(*   %sub.6.1 = sub i16 %1539, %call.i.6.1 *)
sub v_sub_6_1 v1539 v_call_i_6_1;
(*   store i16 %sub.6.1, i16* %arrayidx9.6.1, align 2, !tbaa !3 *)
mov mem0_6 v_sub_6_1;
(*   %add21.6.1 = add i16 %1539, %call.i.6.1 *)
add v_add21_6_1 v1539 v_call_i_6_1;
(*   store i16 %add21.6.1, i16* %arrayidx11.6.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_6_1;

(* NOTE: k = 65 *)

(*   %arrayidx9.6.168 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %1540 = load i16, i16* %arrayidx9.6.168, align 2, !tbaa !3 *)
mov v1540 mem0_12;
(*   %conv1.i.6.169 = sext i16 %1540 to i32 *)
cast v_conv1_i_6_169@sint32 v1540@sint16;
(*   %mul.i.6.170 = mul nsw i32 %conv1.i.6.169, 430 *)
mul v_mul_i_6_170 v_conv1_i_6_169 (430)@sint32;
(*   %call.i.6.171 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.170) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_170, v_call_i_6_171);
(*   %arrayidx11.6.172 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %1541 = load i16, i16* %arrayidx11.6.172, align 2, !tbaa !3 *)
mov v1541 mem0_8;
(*   %sub.6.173 = sub i16 %1541, %call.i.6.171 *)
sub v_sub_6_173 v1541 v_call_i_6_171;
(*   store i16 %sub.6.173, i16* %arrayidx9.6.168, align 2, !tbaa !3 *)
mov mem0_12 v_sub_6_173;
(*   %add21.6.174 = add i16 %1541, %call.i.6.171 *)
add v_add21_6_174 v1541 v_call_i_6_171;
(*   store i16 %add21.6.174, i16* %arrayidx11.6.172, align 2, !tbaa !3 *)
mov mem0_8 v_add21_6_174;
(*   %arrayidx9.6.1.1 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %1542 = load i16, i16* %arrayidx9.6.1.1, align 2, !tbaa !3 *)
mov v1542 mem0_14;
(*   %conv1.i.6.1.1 = sext i16 %1542 to i32 *)
cast v_conv1_i_6_1_1@sint32 v1542@sint16;
(*   %mul.i.6.1.1 = mul nsw i32 %conv1.i.6.1.1, 430 *)
mul v_mul_i_6_1_1 v_conv1_i_6_1_1 (430)@sint32;
(*   %call.i.6.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_1, v_call_i_6_1_1);
(*   %arrayidx11.6.1.1 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %1543 = load i16, i16* %arrayidx11.6.1.1, align 2, !tbaa !3 *)
mov v1543 mem0_10;
(*   %sub.6.1.1 = sub i16 %1543, %call.i.6.1.1 *)
sub v_sub_6_1_1 v1543 v_call_i_6_1_1;
(*   store i16 %sub.6.1.1, i16* %arrayidx9.6.1.1, align 2, !tbaa !3 *)
mov mem0_14 v_sub_6_1_1;
(*   %add21.6.1.1 = add i16 %1543, %call.i.6.1.1 *)
add v_add21_6_1_1 v1543 v_call_i_6_1_1;
(*   store i16 %add21.6.1.1, i16* %arrayidx11.6.1.1, align 2, !tbaa !3 *)
mov mem0_10 v_add21_6_1_1;

(* NOTE: k = 66 *)

(*   %arrayidx9.6.2 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %1544 = load i16, i16* %arrayidx9.6.2, align 2, !tbaa !3 *)
mov v1544 mem0_20;
(*   %conv1.i.6.2 = sext i16 %1544 to i32 *)
cast v_conv1_i_6_2@sint32 v1544@sint16;
(*   %mul.i.6.2 = mul nsw i32 %conv1.i.6.2, 555 *)
mul v_mul_i_6_2 v_conv1_i_6_2 (555)@sint32;
(*   %call.i.6.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_2, v_call_i_6_2);
(*   %arrayidx11.6.2 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %1545 = load i16, i16* %arrayidx11.6.2, align 2, !tbaa !3 *)
mov v1545 mem0_16;
(*   %sub.6.2 = sub i16 %1545, %call.i.6.2 *)
sub v_sub_6_2 v1545 v_call_i_6_2;
(*   store i16 %sub.6.2, i16* %arrayidx9.6.2, align 2, !tbaa !3 *)
mov mem0_20 v_sub_6_2;
(*   %add21.6.2 = add i16 %1545, %call.i.6.2 *)
add v_add21_6_2 v1545 v_call_i_6_2;
(*   store i16 %add21.6.2, i16* %arrayidx11.6.2, align 2, !tbaa !3 *)
mov mem0_16 v_add21_6_2;
(*   %arrayidx9.6.1.2 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %1546 = load i16, i16* %arrayidx9.6.1.2, align 2, !tbaa !3 *)
mov v1546 mem0_22;
(*   %conv1.i.6.1.2 = sext i16 %1546 to i32 *)
cast v_conv1_i_6_1_2@sint32 v1546@sint16;
(*   %mul.i.6.1.2 = mul nsw i32 %conv1.i.6.1.2, 555 *)
mul v_mul_i_6_1_2 v_conv1_i_6_1_2 (555)@sint32;
(*   %call.i.6.1.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_2, v_call_i_6_1_2);
(*   %arrayidx11.6.1.2 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %1547 = load i16, i16* %arrayidx11.6.1.2, align 2, !tbaa !3 *)
mov v1547 mem0_18;
(*   %sub.6.1.2 = sub i16 %1547, %call.i.6.1.2 *)
sub v_sub_6_1_2 v1547 v_call_i_6_1_2;
(*   store i16 %sub.6.1.2, i16* %arrayidx9.6.1.2, align 2, !tbaa !3 *)
mov mem0_22 v_sub_6_1_2;
(*   %add21.6.1.2 = add i16 %1547, %call.i.6.1.2 *)
add v_add21_6_1_2 v1547 v_call_i_6_1_2;
(*   store i16 %add21.6.1.2, i16* %arrayidx11.6.1.2, align 2, !tbaa !3 *)
mov mem0_18 v_add21_6_1_2;

(* NOTE: k = 67 *)

(*   %arrayidx9.6.3 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %1548 = load i16, i16* %arrayidx9.6.3, align 2, !tbaa !3 *)
mov v1548 mem0_28;
(*   %conv1.i.6.3 = sext i16 %1548 to i32 *)
cast v_conv1_i_6_3@sint32 v1548@sint16;
(*   %mul.i.6.3 = mul nsw i32 %conv1.i.6.3, 843 *)
mul v_mul_i_6_3 v_conv1_i_6_3 (843)@sint32;
(*   %call.i.6.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_3, v_call_i_6_3);
(*   %arrayidx11.6.3 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %1549 = load i16, i16* %arrayidx11.6.3, align 2, !tbaa !3 *)
mov v1549 mem0_24;
(*   %sub.6.3 = sub i16 %1549, %call.i.6.3 *)
sub v_sub_6_3 v1549 v_call_i_6_3;
(*   store i16 %sub.6.3, i16* %arrayidx9.6.3, align 2, !tbaa !3 *)
mov mem0_28 v_sub_6_3;
(*   %add21.6.3 = add i16 %1549, %call.i.6.3 *)
add v_add21_6_3 v1549 v_call_i_6_3;
(*   store i16 %add21.6.3, i16* %arrayidx11.6.3, align 2, !tbaa !3 *)
mov mem0_24 v_add21_6_3;
(*   %arrayidx9.6.1.3 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %1550 = load i16, i16* %arrayidx9.6.1.3, align 2, !tbaa !3 *)
mov v1550 mem0_30;
(*   %conv1.i.6.1.3 = sext i16 %1550 to i32 *)
cast v_conv1_i_6_1_3@sint32 v1550@sint16;
(*   %mul.i.6.1.3 = mul nsw i32 %conv1.i.6.1.3, 843 *)
mul v_mul_i_6_1_3 v_conv1_i_6_1_3 (843)@sint32;
(*   %call.i.6.1.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_3, v_call_i_6_1_3);
(*   %arrayidx11.6.1.3 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %1551 = load i16, i16* %arrayidx11.6.1.3, align 2, !tbaa !3 *)
mov v1551 mem0_26;
(*   %sub.6.1.3 = sub i16 %1551, %call.i.6.1.3 *)
sub v_sub_6_1_3 v1551 v_call_i_6_1_3;
(*   store i16 %sub.6.1.3, i16* %arrayidx9.6.1.3, align 2, !tbaa !3 *)
mov mem0_30 v_sub_6_1_3;
(*   %add21.6.1.3 = add i16 %1551, %call.i.6.1.3 *)
add v_add21_6_1_3 v1551 v_call_i_6_1_3;
(*   store i16 %add21.6.1.3, i16* %arrayidx11.6.1.3, align 2, !tbaa !3 *)
mov mem0_26 v_add21_6_1_3;

(* NOTE: k = 68 *)

(*   %arrayidx9.6.4 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %1552 = load i16, i16* %arrayidx9.6.4, align 2, !tbaa !3 *)
mov v1552 mem0_36;
(*   %conv1.i.6.4 = sext i16 %1552 to i32 *)
cast v_conv1_i_6_4@sint32 v1552@sint16;
(*   %mul.i.6.4 = mul nsw i32 %conv1.i.6.4, -1251 *)
mul v_mul_i_6_4 v_conv1_i_6_4 (-1251)@sint32;
(*   %call.i.6.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_4, v_call_i_6_4);
(*   %arrayidx11.6.4 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %1553 = load i16, i16* %arrayidx11.6.4, align 2, !tbaa !3 *)
mov v1553 mem0_32;
(*   %sub.6.4 = sub i16 %1553, %call.i.6.4 *)
sub v_sub_6_4 v1553 v_call_i_6_4;
(*   store i16 %sub.6.4, i16* %arrayidx9.6.4, align 2, !tbaa !3 *)
mov mem0_36 v_sub_6_4;
(*   %add21.6.4 = add i16 %1553, %call.i.6.4 *)
add v_add21_6_4 v1553 v_call_i_6_4;
(*   store i16 %add21.6.4, i16* %arrayidx11.6.4, align 2, !tbaa !3 *)
mov mem0_32 v_add21_6_4;
(*   %arrayidx9.6.1.4 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %1554 = load i16, i16* %arrayidx9.6.1.4, align 2, !tbaa !3 *)
mov v1554 mem0_38;
(*   %conv1.i.6.1.4 = sext i16 %1554 to i32 *)
cast v_conv1_i_6_1_4@sint32 v1554@sint16;
(*   %mul.i.6.1.4 = mul nsw i32 %conv1.i.6.1.4, -1251 *)
mul v_mul_i_6_1_4 v_conv1_i_6_1_4 (-1251)@sint32;
(*   %call.i.6.1.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_4, v_call_i_6_1_4);
(*   %arrayidx11.6.1.4 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %1555 = load i16, i16* %arrayidx11.6.1.4, align 2, !tbaa !3 *)
mov v1555 mem0_34;
(*   %sub.6.1.4 = sub i16 %1555, %call.i.6.1.4 *)
sub v_sub_6_1_4 v1555 v_call_i_6_1_4;
(*   store i16 %sub.6.1.4, i16* %arrayidx9.6.1.4, align 2, !tbaa !3 *)
mov mem0_38 v_sub_6_1_4;
(*   %add21.6.1.4 = add i16 %1555, %call.i.6.1.4 *)
add v_add21_6_1_4 v1555 v_call_i_6_1_4;
(*   store i16 %add21.6.1.4, i16* %arrayidx11.6.1.4, align 2, !tbaa !3 *)
mov mem0_34 v_add21_6_1_4;

(* NOTE: k = 69 *)

(*   %arrayidx9.6.5 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %1556 = load i16, i16* %arrayidx9.6.5, align 2, !tbaa !3 *)
mov v1556 mem0_44;
(*   %conv1.i.6.5 = sext i16 %1556 to i32 *)
cast v_conv1_i_6_5@sint32 v1556@sint16;
(*   %mul.i.6.5 = mul nsw i32 %conv1.i.6.5, 871 *)
mul v_mul_i_6_5 v_conv1_i_6_5 (871)@sint32;
(*   %call.i.6.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_5, v_call_i_6_5);
(*   %arrayidx11.6.5 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %1557 = load i16, i16* %arrayidx11.6.5, align 2, !tbaa !3 *)
mov v1557 mem0_40;
(*   %sub.6.5 = sub i16 %1557, %call.i.6.5 *)
sub v_sub_6_5 v1557 v_call_i_6_5;
(*   store i16 %sub.6.5, i16* %arrayidx9.6.5, align 2, !tbaa !3 *)
mov mem0_44 v_sub_6_5;
(*   %add21.6.5 = add i16 %1557, %call.i.6.5 *)
add v_add21_6_5 v1557 v_call_i_6_5;
(*   store i16 %add21.6.5, i16* %arrayidx11.6.5, align 2, !tbaa !3 *)
mov mem0_40 v_add21_6_5;
(*   %arrayidx9.6.1.5 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %1558 = load i16, i16* %arrayidx9.6.1.5, align 2, !tbaa !3 *)
mov v1558 mem0_46;
(*   %conv1.i.6.1.5 = sext i16 %1558 to i32 *)
cast v_conv1_i_6_1_5@sint32 v1558@sint16;
(*   %mul.i.6.1.5 = mul nsw i32 %conv1.i.6.1.5, 871 *)
mul v_mul_i_6_1_5 v_conv1_i_6_1_5 (871)@sint32;
(*   %call.i.6.1.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_5, v_call_i_6_1_5);
(*   %arrayidx11.6.1.5 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %1559 = load i16, i16* %arrayidx11.6.1.5, align 2, !tbaa !3 *)
mov v1559 mem0_42;
(*   %sub.6.1.5 = sub i16 %1559, %call.i.6.1.5 *)
sub v_sub_6_1_5 v1559 v_call_i_6_1_5;
(*   store i16 %sub.6.1.5, i16* %arrayidx9.6.1.5, align 2, !tbaa !3 *)
mov mem0_46 v_sub_6_1_5;
(*   %add21.6.1.5 = add i16 %1559, %call.i.6.1.5 *)
add v_add21_6_1_5 v1559 v_call_i_6_1_5;
(*   store i16 %add21.6.1.5, i16* %arrayidx11.6.1.5, align 2, !tbaa !3 *)
mov mem0_42 v_add21_6_1_5;

(* NOTE: k = 70 *)

(*   %arrayidx9.6.6 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %1560 = load i16, i16* %arrayidx9.6.6, align 2, !tbaa !3 *)
mov v1560 mem0_52;
(*   %conv1.i.6.6 = sext i16 %1560 to i32 *)
cast v_conv1_i_6_6@sint32 v1560@sint16;
(*   %mul.i.6.6 = mul nsw i32 %conv1.i.6.6, 1550 *)
mul v_mul_i_6_6 v_conv1_i_6_6 (1550)@sint32;
(*   %call.i.6.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_6, v_call_i_6_6);
(*   %arrayidx11.6.6 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %1561 = load i16, i16* %arrayidx11.6.6, align 2, !tbaa !3 *)
mov v1561 mem0_48;
(*   %sub.6.6 = sub i16 %1561, %call.i.6.6 *)
sub v_sub_6_6 v1561 v_call_i_6_6;
(*   store i16 %sub.6.6, i16* %arrayidx9.6.6, align 2, !tbaa !3 *)
mov mem0_52 v_sub_6_6;
(*   %add21.6.6 = add i16 %1561, %call.i.6.6 *)
add v_add21_6_6 v1561 v_call_i_6_6;
(*   store i16 %add21.6.6, i16* %arrayidx11.6.6, align 2, !tbaa !3 *)
mov mem0_48 v_add21_6_6;
(*   %arrayidx9.6.1.6 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %1562 = load i16, i16* %arrayidx9.6.1.6, align 2, !tbaa !3 *)
mov v1562 mem0_54;
(*   %conv1.i.6.1.6 = sext i16 %1562 to i32 *)
cast v_conv1_i_6_1_6@sint32 v1562@sint16;
(*   %mul.i.6.1.6 = mul nsw i32 %conv1.i.6.1.6, 1550 *)
mul v_mul_i_6_1_6 v_conv1_i_6_1_6 (1550)@sint32;
(*   %call.i.6.1.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_6, v_call_i_6_1_6);
(*   %arrayidx11.6.1.6 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %1563 = load i16, i16* %arrayidx11.6.1.6, align 2, !tbaa !3 *)
mov v1563 mem0_50;
(*   %sub.6.1.6 = sub i16 %1563, %call.i.6.1.6 *)
sub v_sub_6_1_6 v1563 v_call_i_6_1_6;
(*   store i16 %sub.6.1.6, i16* %arrayidx9.6.1.6, align 2, !tbaa !3 *)
mov mem0_54 v_sub_6_1_6;
(*   %add21.6.1.6 = add i16 %1563, %call.i.6.1.6 *)
add v_add21_6_1_6 v1563 v_call_i_6_1_6;
(*   store i16 %add21.6.1.6, i16* %arrayidx11.6.1.6, align 2, !tbaa !3 *)
mov mem0_50 v_add21_6_1_6;

(* NOTE: k = 71 *)

(*   %arrayidx9.6.7 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %1564 = load i16, i16* %arrayidx9.6.7, align 2, !tbaa !3 *)
mov v1564 mem0_60;
(*   %conv1.i.6.7 = sext i16 %1564 to i32 *)
cast v_conv1_i_6_7@sint32 v1564@sint16;
(*   %mul.i.6.7 = mul nsw i32 %conv1.i.6.7, 105 *)
mul v_mul_i_6_7 v_conv1_i_6_7 (105)@sint32;
(*   %call.i.6.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_7, v_call_i_6_7);
(*   %arrayidx11.6.7 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %1565 = load i16, i16* %arrayidx11.6.7, align 2, !tbaa !3 *)
mov v1565 mem0_56;
(*   %sub.6.7 = sub i16 %1565, %call.i.6.7 *)
sub v_sub_6_7 v1565 v_call_i_6_7;
(*   store i16 %sub.6.7, i16* %arrayidx9.6.7, align 2, !tbaa !3 *)
mov mem0_60 v_sub_6_7;
(*   %add21.6.7 = add i16 %1565, %call.i.6.7 *)
add v_add21_6_7 v1565 v_call_i_6_7;
(*   store i16 %add21.6.7, i16* %arrayidx11.6.7, align 2, !tbaa !3 *)
mov mem0_56 v_add21_6_7;
(*   %arrayidx9.6.1.7 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %1566 = load i16, i16* %arrayidx9.6.1.7, align 2, !tbaa !3 *)
mov v1566 mem0_62;
(*   %conv1.i.6.1.7 = sext i16 %1566 to i32 *)
cast v_conv1_i_6_1_7@sint32 v1566@sint16;
(*   %mul.i.6.1.7 = mul nsw i32 %conv1.i.6.1.7, 105 *)
mul v_mul_i_6_1_7 v_conv1_i_6_1_7 (105)@sint32;
(*   %call.i.6.1.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_7, v_call_i_6_1_7);
(*   %arrayidx11.6.1.7 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %1567 = load i16, i16* %arrayidx11.6.1.7, align 2, !tbaa !3 *)
mov v1567 mem0_58;
(*   %sub.6.1.7 = sub i16 %1567, %call.i.6.1.7 *)
sub v_sub_6_1_7 v1567 v_call_i_6_1_7;
(*   store i16 %sub.6.1.7, i16* %arrayidx9.6.1.7, align 2, !tbaa !3 *)
mov mem0_62 v_sub_6_1_7;
(*   %add21.6.1.7 = add i16 %1567, %call.i.6.1.7 *)
add v_add21_6_1_7 v1567 v_call_i_6_1_7;
(*   store i16 %add21.6.1.7, i16* %arrayidx11.6.1.7, align 2, !tbaa !3 *)
mov mem0_58 v_add21_6_1_7;

(* NOTE: k = 72 *)

(*   %arrayidx9.6.8 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %1568 = load i16, i16* %arrayidx9.6.8, align 2, !tbaa !3 *)
mov v1568 mem0_68;
(*   %conv1.i.6.8 = sext i16 %1568 to i32 *)
cast v_conv1_i_6_8@sint32 v1568@sint16;
(*   %mul.i.6.8 = mul nsw i32 %conv1.i.6.8, 422 *)
mul v_mul_i_6_8 v_conv1_i_6_8 (422)@sint32;
(*   %call.i.6.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_8, v_call_i_6_8);
(*   %arrayidx11.6.8 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %1569 = load i16, i16* %arrayidx11.6.8, align 2, !tbaa !3 *)
mov v1569 mem0_64;
(*   %sub.6.8 = sub i16 %1569, %call.i.6.8 *)
sub v_sub_6_8 v1569 v_call_i_6_8;
(*   store i16 %sub.6.8, i16* %arrayidx9.6.8, align 2, !tbaa !3 *)
mov mem0_68 v_sub_6_8;
(*   %add21.6.8 = add i16 %1569, %call.i.6.8 *)
add v_add21_6_8 v1569 v_call_i_6_8;
(*   store i16 %add21.6.8, i16* %arrayidx11.6.8, align 2, !tbaa !3 *)
mov mem0_64 v_add21_6_8;
(*   %arrayidx9.6.1.8 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %1570 = load i16, i16* %arrayidx9.6.1.8, align 2, !tbaa !3 *)
mov v1570 mem0_70;
(*   %conv1.i.6.1.8 = sext i16 %1570 to i32 *)
cast v_conv1_i_6_1_8@sint32 v1570@sint16;
(*   %mul.i.6.1.8 = mul nsw i32 %conv1.i.6.1.8, 422 *)
mul v_mul_i_6_1_8 v_conv1_i_6_1_8 (422)@sint32;
(*   %call.i.6.1.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_8, v_call_i_6_1_8);
(*   %arrayidx11.6.1.8 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %1571 = load i16, i16* %arrayidx11.6.1.8, align 2, !tbaa !3 *)
mov v1571 mem0_66;
(*   %sub.6.1.8 = sub i16 %1571, %call.i.6.1.8 *)
sub v_sub_6_1_8 v1571 v_call_i_6_1_8;
(*   store i16 %sub.6.1.8, i16* %arrayidx9.6.1.8, align 2, !tbaa !3 *)
mov mem0_70 v_sub_6_1_8;
(*   %add21.6.1.8 = add i16 %1571, %call.i.6.1.8 *)
add v_add21_6_1_8 v1571 v_call_i_6_1_8;
(*   store i16 %add21.6.1.8, i16* %arrayidx11.6.1.8, align 2, !tbaa !3 *)
mov mem0_66 v_add21_6_1_8;

(* NOTE: k = 73 *)

(*   %arrayidx9.6.9 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %1572 = load i16, i16* %arrayidx9.6.9, align 2, !tbaa !3 *)
mov v1572 mem0_76;
(*   %conv1.i.6.9 = sext i16 %1572 to i32 *)
cast v_conv1_i_6_9@sint32 v1572@sint16;
(*   %mul.i.6.9 = mul nsw i32 %conv1.i.6.9, 587 *)
mul v_mul_i_6_9 v_conv1_i_6_9 (587)@sint32;
(*   %call.i.6.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_9, v_call_i_6_9);
(*   %arrayidx11.6.9 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %1573 = load i16, i16* %arrayidx11.6.9, align 2, !tbaa !3 *)
mov v1573 mem0_72;
(*   %sub.6.9 = sub i16 %1573, %call.i.6.9 *)
sub v_sub_6_9 v1573 v_call_i_6_9;
(*   store i16 %sub.6.9, i16* %arrayidx9.6.9, align 2, !tbaa !3 *)
mov mem0_76 v_sub_6_9;
(*   %add21.6.9 = add i16 %1573, %call.i.6.9 *)
add v_add21_6_9 v1573 v_call_i_6_9;
(*   store i16 %add21.6.9, i16* %arrayidx11.6.9, align 2, !tbaa !3 *)
mov mem0_72 v_add21_6_9;
(*   %arrayidx9.6.1.9 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %1574 = load i16, i16* %arrayidx9.6.1.9, align 2, !tbaa !3 *)
mov v1574 mem0_78;
(*   %conv1.i.6.1.9 = sext i16 %1574 to i32 *)
cast v_conv1_i_6_1_9@sint32 v1574@sint16;
(*   %mul.i.6.1.9 = mul nsw i32 %conv1.i.6.1.9, 587 *)
mul v_mul_i_6_1_9 v_conv1_i_6_1_9 (587)@sint32;
(*   %call.i.6.1.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_9, v_call_i_6_1_9);
(*   %arrayidx11.6.1.9 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %1575 = load i16, i16* %arrayidx11.6.1.9, align 2, !tbaa !3 *)
mov v1575 mem0_74;
(*   %sub.6.1.9 = sub i16 %1575, %call.i.6.1.9 *)
sub v_sub_6_1_9 v1575 v_call_i_6_1_9;
(*   store i16 %sub.6.1.9, i16* %arrayidx9.6.1.9, align 2, !tbaa !3 *)
mov mem0_78 v_sub_6_1_9;
(*   %add21.6.1.9 = add i16 %1575, %call.i.6.1.9 *)
add v_add21_6_1_9 v1575 v_call_i_6_1_9;
(*   store i16 %add21.6.1.9, i16* %arrayidx11.6.1.9, align 2, !tbaa !3 *)
mov mem0_74 v_add21_6_1_9;

(* NOTE: k = 74 *)

(*   %arrayidx9.6.10 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %1576 = load i16, i16* %arrayidx9.6.10, align 2, !tbaa !3 *)
mov v1576 mem0_84;
(*   %conv1.i.6.10 = sext i16 %1576 to i32 *)
cast v_conv1_i_6_10@sint32 v1576@sint16;
(*   %mul.i.6.10 = mul nsw i32 %conv1.i.6.10, 177 *)
mul v_mul_i_6_10 v_conv1_i_6_10 (177)@sint32;
(*   %call.i.6.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_10, v_call_i_6_10);
(*   %arrayidx11.6.10 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %1577 = load i16, i16* %arrayidx11.6.10, align 2, !tbaa !3 *)
mov v1577 mem0_80;
(*   %sub.6.10 = sub i16 %1577, %call.i.6.10 *)
sub v_sub_6_10 v1577 v_call_i_6_10;
(*   store i16 %sub.6.10, i16* %arrayidx9.6.10, align 2, !tbaa !3 *)
mov mem0_84 v_sub_6_10;
(*   %add21.6.10 = add i16 %1577, %call.i.6.10 *)
add v_add21_6_10 v1577 v_call_i_6_10;
(*   store i16 %add21.6.10, i16* %arrayidx11.6.10, align 2, !tbaa !3 *)
mov mem0_80 v_add21_6_10;
(*   %arrayidx9.6.1.10 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %1578 = load i16, i16* %arrayidx9.6.1.10, align 2, !tbaa !3 *)
mov v1578 mem0_86;
(*   %conv1.i.6.1.10 = sext i16 %1578 to i32 *)
cast v_conv1_i_6_1_10@sint32 v1578@sint16;
(*   %mul.i.6.1.10 = mul nsw i32 %conv1.i.6.1.10, 177 *)
mul v_mul_i_6_1_10 v_conv1_i_6_1_10 (177)@sint32;
(*   %call.i.6.1.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_10, v_call_i_6_1_10);
(*   %arrayidx11.6.1.10 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %1579 = load i16, i16* %arrayidx11.6.1.10, align 2, !tbaa !3 *)
mov v1579 mem0_82;
(*   %sub.6.1.10 = sub i16 %1579, %call.i.6.1.10 *)
sub v_sub_6_1_10 v1579 v_call_i_6_1_10;
(*   store i16 %sub.6.1.10, i16* %arrayidx9.6.1.10, align 2, !tbaa !3 *)
mov mem0_86 v_sub_6_1_10;
(*   %add21.6.1.10 = add i16 %1579, %call.i.6.1.10 *)
add v_add21_6_1_10 v1579 v_call_i_6_1_10;
(*   store i16 %add21.6.1.10, i16* %arrayidx11.6.1.10, align 2, !tbaa !3 *)
mov mem0_82 v_add21_6_1_10;

(* NOTE: k = 75 *)

(*   %arrayidx9.6.11 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %1580 = load i16, i16* %arrayidx9.6.11, align 2, !tbaa !3 *)
mov v1580 mem0_92;
(*   %conv1.i.6.11 = sext i16 %1580 to i32 *)
cast v_conv1_i_6_11@sint32 v1580@sint16;
(*   %mul.i.6.11 = mul nsw i32 %conv1.i.6.11, -235 *)
mul v_mul_i_6_11 v_conv1_i_6_11 (-235)@sint32;
(*   %call.i.6.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_11, v_call_i_6_11);
(*   %arrayidx11.6.11 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %1581 = load i16, i16* %arrayidx11.6.11, align 2, !tbaa !3 *)
mov v1581 mem0_88;
(*   %sub.6.11 = sub i16 %1581, %call.i.6.11 *)
sub v_sub_6_11 v1581 v_call_i_6_11;
(*   store i16 %sub.6.11, i16* %arrayidx9.6.11, align 2, !tbaa !3 *)
mov mem0_92 v_sub_6_11;
(*   %add21.6.11 = add i16 %1581, %call.i.6.11 *)
add v_add21_6_11 v1581 v_call_i_6_11;
(*   store i16 %add21.6.11, i16* %arrayidx11.6.11, align 2, !tbaa !3 *)
mov mem0_88 v_add21_6_11;
(*   %arrayidx9.6.1.11 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %1582 = load i16, i16* %arrayidx9.6.1.11, align 2, !tbaa !3 *)
mov v1582 mem0_94;
(*   %conv1.i.6.1.11 = sext i16 %1582 to i32 *)
cast v_conv1_i_6_1_11@sint32 v1582@sint16;
(*   %mul.i.6.1.11 = mul nsw i32 %conv1.i.6.1.11, -235 *)
mul v_mul_i_6_1_11 v_conv1_i_6_1_11 (-235)@sint32;
(*   %call.i.6.1.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_11, v_call_i_6_1_11);
(*   %arrayidx11.6.1.11 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %1583 = load i16, i16* %arrayidx11.6.1.11, align 2, !tbaa !3 *)
mov v1583 mem0_90;
(*   %sub.6.1.11 = sub i16 %1583, %call.i.6.1.11 *)
sub v_sub_6_1_11 v1583 v_call_i_6_1_11;
(*   store i16 %sub.6.1.11, i16* %arrayidx9.6.1.11, align 2, !tbaa !3 *)
mov mem0_94 v_sub_6_1_11;
(*   %add21.6.1.11 = add i16 %1583, %call.i.6.1.11 *)
add v_add21_6_1_11 v1583 v_call_i_6_1_11;
(*   store i16 %add21.6.1.11, i16* %arrayidx11.6.1.11, align 2, !tbaa !3 *)
mov mem0_90 v_add21_6_1_11;

(* NOTE: k = 76 *)

(*   %arrayidx9.6.12 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %1584 = load i16, i16* %arrayidx9.6.12, align 2, !tbaa !3 *)
mov v1584 mem0_100;
(*   %conv1.i.6.12 = sext i16 %1584 to i32 *)
cast v_conv1_i_6_12@sint32 v1584@sint16;
(*   %mul.i.6.12 = mul nsw i32 %conv1.i.6.12, -291 *)
mul v_mul_i_6_12 v_conv1_i_6_12 (-291)@sint32;
(*   %call.i.6.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_12, v_call_i_6_12);
(*   %arrayidx11.6.12 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %1585 = load i16, i16* %arrayidx11.6.12, align 2, !tbaa !3 *)
mov v1585 mem0_96;
(*   %sub.6.12 = sub i16 %1585, %call.i.6.12 *)
sub v_sub_6_12 v1585 v_call_i_6_12;
(*   store i16 %sub.6.12, i16* %arrayidx9.6.12, align 2, !tbaa !3 *)
mov mem0_100 v_sub_6_12;
(*   %add21.6.12 = add i16 %1585, %call.i.6.12 *)
add v_add21_6_12 v1585 v_call_i_6_12;
(*   store i16 %add21.6.12, i16* %arrayidx11.6.12, align 2, !tbaa !3 *)
mov mem0_96 v_add21_6_12;
(*   %arrayidx9.6.1.12 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %1586 = load i16, i16* %arrayidx9.6.1.12, align 2, !tbaa !3 *)
mov v1586 mem0_102;
(*   %conv1.i.6.1.12 = sext i16 %1586 to i32 *)
cast v_conv1_i_6_1_12@sint32 v1586@sint16;
(*   %mul.i.6.1.12 = mul nsw i32 %conv1.i.6.1.12, -291 *)
mul v_mul_i_6_1_12 v_conv1_i_6_1_12 (-291)@sint32;
(*   %call.i.6.1.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_12, v_call_i_6_1_12);
(*   %arrayidx11.6.1.12 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %1587 = load i16, i16* %arrayidx11.6.1.12, align 2, !tbaa !3 *)
mov v1587 mem0_98;
(*   %sub.6.1.12 = sub i16 %1587, %call.i.6.1.12 *)
sub v_sub_6_1_12 v1587 v_call_i_6_1_12;
(*   store i16 %sub.6.1.12, i16* %arrayidx9.6.1.12, align 2, !tbaa !3 *)
mov mem0_102 v_sub_6_1_12;
(*   %add21.6.1.12 = add i16 %1587, %call.i.6.1.12 *)
add v_add21_6_1_12 v1587 v_call_i_6_1_12;
(*   store i16 %add21.6.1.12, i16* %arrayidx11.6.1.12, align 2, !tbaa !3 *)
mov mem0_98 v_add21_6_1_12;

(* NOTE: k = 77 *)

(*   %arrayidx9.6.13 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %1588 = load i16, i16* %arrayidx9.6.13, align 2, !tbaa !3 *)
mov v1588 mem0_108;
(*   %conv1.i.6.13 = sext i16 %1588 to i32 *)
cast v_conv1_i_6_13@sint32 v1588@sint16;
(*   %mul.i.6.13 = mul nsw i32 %conv1.i.6.13, -460 *)
mul v_mul_i_6_13 v_conv1_i_6_13 (-460)@sint32;
(*   %call.i.6.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_13, v_call_i_6_13);
(*   %arrayidx11.6.13 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %1589 = load i16, i16* %arrayidx11.6.13, align 2, !tbaa !3 *)
mov v1589 mem0_104;
(*   %sub.6.13 = sub i16 %1589, %call.i.6.13 *)
sub v_sub_6_13 v1589 v_call_i_6_13;
(*   store i16 %sub.6.13, i16* %arrayidx9.6.13, align 2, !tbaa !3 *)
mov mem0_108 v_sub_6_13;
(*   %add21.6.13 = add i16 %1589, %call.i.6.13 *)
add v_add21_6_13 v1589 v_call_i_6_13;
(*   store i16 %add21.6.13, i16* %arrayidx11.6.13, align 2, !tbaa !3 *)
mov mem0_104 v_add21_6_13;
(*   %arrayidx9.6.1.13 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %1590 = load i16, i16* %arrayidx9.6.1.13, align 2, !tbaa !3 *)
mov v1590 mem0_110;
(*   %conv1.i.6.1.13 = sext i16 %1590 to i32 *)
cast v_conv1_i_6_1_13@sint32 v1590@sint16;
(*   %mul.i.6.1.13 = mul nsw i32 %conv1.i.6.1.13, -460 *)
mul v_mul_i_6_1_13 v_conv1_i_6_1_13 (-460)@sint32;
(*   %call.i.6.1.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_13, v_call_i_6_1_13);
(*   %arrayidx11.6.1.13 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %1591 = load i16, i16* %arrayidx11.6.1.13, align 2, !tbaa !3 *)
mov v1591 mem0_106;
(*   %sub.6.1.13 = sub i16 %1591, %call.i.6.1.13 *)
sub v_sub_6_1_13 v1591 v_call_i_6_1_13;
(*   store i16 %sub.6.1.13, i16* %arrayidx9.6.1.13, align 2, !tbaa !3 *)
mov mem0_110 v_sub_6_1_13;
(*   %add21.6.1.13 = add i16 %1591, %call.i.6.1.13 *)
add v_add21_6_1_13 v1591 v_call_i_6_1_13;
(*   store i16 %add21.6.1.13, i16* %arrayidx11.6.1.13, align 2, !tbaa !3 *)
mov mem0_106 v_add21_6_1_13;

(* NOTE: k = 78 *)

(*   %arrayidx9.6.14 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %1592 = load i16, i16* %arrayidx9.6.14, align 2, !tbaa !3 *)
mov v1592 mem0_116;
(*   %conv1.i.6.14 = sext i16 %1592 to i32 *)
cast v_conv1_i_6_14@sint32 v1592@sint16;
(*   %mul.i.6.14 = mul nsw i32 %conv1.i.6.14, 1574 *)
mul v_mul_i_6_14 v_conv1_i_6_14 (1574)@sint32;
(*   %call.i.6.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_14, v_call_i_6_14);
(*   %arrayidx11.6.14 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %1593 = load i16, i16* %arrayidx11.6.14, align 2, !tbaa !3 *)
mov v1593 mem0_112;
(*   %sub.6.14 = sub i16 %1593, %call.i.6.14 *)
sub v_sub_6_14 v1593 v_call_i_6_14;
(*   store i16 %sub.6.14, i16* %arrayidx9.6.14, align 2, !tbaa !3 *)
mov mem0_116 v_sub_6_14;
(*   %add21.6.14 = add i16 %1593, %call.i.6.14 *)
add v_add21_6_14 v1593 v_call_i_6_14;
(*   store i16 %add21.6.14, i16* %arrayidx11.6.14, align 2, !tbaa !3 *)
mov mem0_112 v_add21_6_14;
(*   %arrayidx9.6.1.14 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %1594 = load i16, i16* %arrayidx9.6.1.14, align 2, !tbaa !3 *)
mov v1594 mem0_118;
(*   %conv1.i.6.1.14 = sext i16 %1594 to i32 *)
cast v_conv1_i_6_1_14@sint32 v1594@sint16;
(*   %mul.i.6.1.14 = mul nsw i32 %conv1.i.6.1.14, 1574 *)
mul v_mul_i_6_1_14 v_conv1_i_6_1_14 (1574)@sint32;
(*   %call.i.6.1.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_14, v_call_i_6_1_14);
(*   %arrayidx11.6.1.14 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %1595 = load i16, i16* %arrayidx11.6.1.14, align 2, !tbaa !3 *)
mov v1595 mem0_114;
(*   %sub.6.1.14 = sub i16 %1595, %call.i.6.1.14 *)
sub v_sub_6_1_14 v1595 v_call_i_6_1_14;
(*   store i16 %sub.6.1.14, i16* %arrayidx9.6.1.14, align 2, !tbaa !3 *)
mov mem0_118 v_sub_6_1_14;
(*   %add21.6.1.14 = add i16 %1595, %call.i.6.1.14 *)
add v_add21_6_1_14 v1595 v_call_i_6_1_14;
(*   store i16 %add21.6.1.14, i16* %arrayidx11.6.1.14, align 2, !tbaa !3 *)
mov mem0_114 v_add21_6_1_14;

(* NOTE: k = 79 *)

(*   %arrayidx9.6.15 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %1596 = load i16, i16* %arrayidx9.6.15, align 2, !tbaa !3 *)
mov v1596 mem0_124;
(*   %conv1.i.6.15 = sext i16 %1596 to i32 *)
cast v_conv1_i_6_15@sint32 v1596@sint16;
(*   %mul.i.6.15 = mul nsw i32 %conv1.i.6.15, 1653 *)
mul v_mul_i_6_15 v_conv1_i_6_15 (1653)@sint32;
(*   %call.i.6.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_15, v_call_i_6_15);
(*   %arrayidx11.6.15 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %1597 = load i16, i16* %arrayidx11.6.15, align 2, !tbaa !3 *)
mov v1597 mem0_120;
(*   %sub.6.15 = sub i16 %1597, %call.i.6.15 *)
sub v_sub_6_15 v1597 v_call_i_6_15;
(*   store i16 %sub.6.15, i16* %arrayidx9.6.15, align 2, !tbaa !3 *)
mov mem0_124 v_sub_6_15;
(*   %add21.6.15 = add i16 %1597, %call.i.6.15 *)
add v_add21_6_15 v1597 v_call_i_6_15;
(*   store i16 %add21.6.15, i16* %arrayidx11.6.15, align 2, !tbaa !3 *)
mov mem0_120 v_add21_6_15;
(*   %arrayidx9.6.1.15 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %1598 = load i16, i16* %arrayidx9.6.1.15, align 2, !tbaa !3 *)
mov v1598 mem0_126;
(*   %conv1.i.6.1.15 = sext i16 %1598 to i32 *)
cast v_conv1_i_6_1_15@sint32 v1598@sint16;
(*   %mul.i.6.1.15 = mul nsw i32 %conv1.i.6.1.15, 1653 *)
mul v_mul_i_6_1_15 v_conv1_i_6_1_15 (1653)@sint32;
(*   %call.i.6.1.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_15, v_call_i_6_1_15);
(*   %arrayidx11.6.1.15 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %1599 = load i16, i16* %arrayidx11.6.1.15, align 2, !tbaa !3 *)
mov v1599 mem0_122;
(*   %sub.6.1.15 = sub i16 %1599, %call.i.6.1.15 *)
sub v_sub_6_1_15 v1599 v_call_i_6_1_15;
(*   store i16 %sub.6.1.15, i16* %arrayidx9.6.1.15, align 2, !tbaa !3 *)
mov mem0_126 v_sub_6_1_15;
(*   %add21.6.1.15 = add i16 %1599, %call.i.6.1.15 *)
add v_add21_6_1_15 v1599 v_call_i_6_1_15;
(*   store i16 %add21.6.1.15, i16* %arrayidx11.6.1.15, align 2, !tbaa !3 *)
mov mem0_122 v_add21_6_1_15;

(* NOTE: k = 80 *)

(*   %arrayidx9.6.16 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %1600 = load i16, i16* %arrayidx9.6.16, align 2, !tbaa !3 *)
mov v1600 mem0_132;
(*   %conv1.i.6.16 = sext i16 %1600 to i32 *)
cast v_conv1_i_6_16@sint32 v1600@sint16;
(*   %mul.i.6.16 = mul nsw i32 %conv1.i.6.16, -246 *)
mul v_mul_i_6_16 v_conv1_i_6_16 (-246)@sint32;
(*   %call.i.6.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_16, v_call_i_6_16);
(*   %arrayidx11.6.16 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %1601 = load i16, i16* %arrayidx11.6.16, align 2, !tbaa !3 *)
mov v1601 mem0_128;
(*   %sub.6.16 = sub i16 %1601, %call.i.6.16 *)
sub v_sub_6_16 v1601 v_call_i_6_16;
(*   store i16 %sub.6.16, i16* %arrayidx9.6.16, align 2, !tbaa !3 *)
mov mem0_132 v_sub_6_16;
(*   %add21.6.16 = add i16 %1601, %call.i.6.16 *)
add v_add21_6_16 v1601 v_call_i_6_16;
(*   store i16 %add21.6.16, i16* %arrayidx11.6.16, align 2, !tbaa !3 *)
mov mem0_128 v_add21_6_16;
(*   %arrayidx9.6.1.16 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %1602 = load i16, i16* %arrayidx9.6.1.16, align 2, !tbaa !3 *)
mov v1602 mem0_134;
(*   %conv1.i.6.1.16 = sext i16 %1602 to i32 *)
cast v_conv1_i_6_1_16@sint32 v1602@sint16;
(*   %mul.i.6.1.16 = mul nsw i32 %conv1.i.6.1.16, -246 *)
mul v_mul_i_6_1_16 v_conv1_i_6_1_16 (-246)@sint32;
(*   %call.i.6.1.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_16, v_call_i_6_1_16);
(*   %arrayidx11.6.1.16 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %1603 = load i16, i16* %arrayidx11.6.1.16, align 2, !tbaa !3 *)
mov v1603 mem0_130;
(*   %sub.6.1.16 = sub i16 %1603, %call.i.6.1.16 *)
sub v_sub_6_1_16 v1603 v_call_i_6_1_16;
(*   store i16 %sub.6.1.16, i16* %arrayidx9.6.1.16, align 2, !tbaa !3 *)
mov mem0_134 v_sub_6_1_16;
(*   %add21.6.1.16 = add i16 %1603, %call.i.6.1.16 *)
add v_add21_6_1_16 v1603 v_call_i_6_1_16;
(*   store i16 %add21.6.1.16, i16* %arrayidx11.6.1.16, align 2, !tbaa !3 *)
mov mem0_130 v_add21_6_1_16;

(* NOTE: k = 81 *)

(*   %arrayidx9.6.17 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %1604 = load i16, i16* %arrayidx9.6.17, align 2, !tbaa !3 *)
mov v1604 mem0_140;
(*   %conv1.i.6.17 = sext i16 %1604 to i32 *)
cast v_conv1_i_6_17@sint32 v1604@sint16;
(*   %mul.i.6.17 = mul nsw i32 %conv1.i.6.17, 778 *)
mul v_mul_i_6_17 v_conv1_i_6_17 (778)@sint32;
(*   %call.i.6.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_17, v_call_i_6_17);
(*   %arrayidx11.6.17 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %1605 = load i16, i16* %arrayidx11.6.17, align 2, !tbaa !3 *)
mov v1605 mem0_136;
(*   %sub.6.17 = sub i16 %1605, %call.i.6.17 *)
sub v_sub_6_17 v1605 v_call_i_6_17;
(*   store i16 %sub.6.17, i16* %arrayidx9.6.17, align 2, !tbaa !3 *)
mov mem0_140 v_sub_6_17;
(*   %add21.6.17 = add i16 %1605, %call.i.6.17 *)
add v_add21_6_17 v1605 v_call_i_6_17;
(*   store i16 %add21.6.17, i16* %arrayidx11.6.17, align 2, !tbaa !3 *)
mov mem0_136 v_add21_6_17;
(*   %arrayidx9.6.1.17 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %1606 = load i16, i16* %arrayidx9.6.1.17, align 2, !tbaa !3 *)
mov v1606 mem0_142;
(*   %conv1.i.6.1.17 = sext i16 %1606 to i32 *)
cast v_conv1_i_6_1_17@sint32 v1606@sint16;
(*   %mul.i.6.1.17 = mul nsw i32 %conv1.i.6.1.17, 778 *)
mul v_mul_i_6_1_17 v_conv1_i_6_1_17 (778)@sint32;
(*   %call.i.6.1.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_17, v_call_i_6_1_17);
(*   %arrayidx11.6.1.17 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %1607 = load i16, i16* %arrayidx11.6.1.17, align 2, !tbaa !3 *)
mov v1607 mem0_138;
(*   %sub.6.1.17 = sub i16 %1607, %call.i.6.1.17 *)
sub v_sub_6_1_17 v1607 v_call_i_6_1_17;
(*   store i16 %sub.6.1.17, i16* %arrayidx9.6.1.17, align 2, !tbaa !3 *)
mov mem0_142 v_sub_6_1_17;
(*   %add21.6.1.17 = add i16 %1607, %call.i.6.1.17 *)
add v_add21_6_1_17 v1607 v_call_i_6_1_17;
(*   store i16 %add21.6.1.17, i16* %arrayidx11.6.1.17, align 2, !tbaa !3 *)
mov mem0_138 v_add21_6_1_17;

(* NOTE: k = 82 *)

(*   %arrayidx9.6.18 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %1608 = load i16, i16* %arrayidx9.6.18, align 2, !tbaa !3 *)
mov v1608 mem0_148;
(*   %conv1.i.6.18 = sext i16 %1608 to i32 *)
cast v_conv1_i_6_18@sint32 v1608@sint16;
(*   %mul.i.6.18 = mul nsw i32 %conv1.i.6.18, 1159 *)
mul v_mul_i_6_18 v_conv1_i_6_18 (1159)@sint32;
(*   %call.i.6.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_18, v_call_i_6_18);
(*   %arrayidx11.6.18 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %1609 = load i16, i16* %arrayidx11.6.18, align 2, !tbaa !3 *)
mov v1609 mem0_144;
(*   %sub.6.18 = sub i16 %1609, %call.i.6.18 *)
sub v_sub_6_18 v1609 v_call_i_6_18;
(*   store i16 %sub.6.18, i16* %arrayidx9.6.18, align 2, !tbaa !3 *)
mov mem0_148 v_sub_6_18;
(*   %add21.6.18 = add i16 %1609, %call.i.6.18 *)
add v_add21_6_18 v1609 v_call_i_6_18;
(*   store i16 %add21.6.18, i16* %arrayidx11.6.18, align 2, !tbaa !3 *)
mov mem0_144 v_add21_6_18;
(*   %arrayidx9.6.1.18 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %1610 = load i16, i16* %arrayidx9.6.1.18, align 2, !tbaa !3 *)
mov v1610 mem0_150;
(*   %conv1.i.6.1.18 = sext i16 %1610 to i32 *)
cast v_conv1_i_6_1_18@sint32 v1610@sint16;
(*   %mul.i.6.1.18 = mul nsw i32 %conv1.i.6.1.18, 1159 *)
mul v_mul_i_6_1_18 v_conv1_i_6_1_18 (1159)@sint32;
(*   %call.i.6.1.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_18, v_call_i_6_1_18);
(*   %arrayidx11.6.1.18 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %1611 = load i16, i16* %arrayidx11.6.1.18, align 2, !tbaa !3 *)
mov v1611 mem0_146;
(*   %sub.6.1.18 = sub i16 %1611, %call.i.6.1.18 *)
sub v_sub_6_1_18 v1611 v_call_i_6_1_18;
(*   store i16 %sub.6.1.18, i16* %arrayidx9.6.1.18, align 2, !tbaa !3 *)
mov mem0_150 v_sub_6_1_18;
(*   %add21.6.1.18 = add i16 %1611, %call.i.6.1.18 *)
add v_add21_6_1_18 v1611 v_call_i_6_1_18;
(*   store i16 %add21.6.1.18, i16* %arrayidx11.6.1.18, align 2, !tbaa !3 *)
mov mem0_146 v_add21_6_1_18;

(* NOTE: k = 83 *)

(*   %arrayidx9.6.19 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %1612 = load i16, i16* %arrayidx9.6.19, align 2, !tbaa !3 *)
mov v1612 mem0_156;
(*   %conv1.i.6.19 = sext i16 %1612 to i32 *)
cast v_conv1_i_6_19@sint32 v1612@sint16;
(*   %mul.i.6.19 = mul nsw i32 %conv1.i.6.19, -147 *)
mul v_mul_i_6_19 v_conv1_i_6_19 (-147)@sint32;
(*   %call.i.6.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_19, v_call_i_6_19);
(*   %arrayidx11.6.19 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %1613 = load i16, i16* %arrayidx11.6.19, align 2, !tbaa !3 *)
mov v1613 mem0_152;
(*   %sub.6.19 = sub i16 %1613, %call.i.6.19 *)
sub v_sub_6_19 v1613 v_call_i_6_19;
(*   store i16 %sub.6.19, i16* %arrayidx9.6.19, align 2, !tbaa !3 *)
mov mem0_156 v_sub_6_19;
(*   %add21.6.19 = add i16 %1613, %call.i.6.19 *)
add v_add21_6_19 v1613 v_call_i_6_19;
(*   store i16 %add21.6.19, i16* %arrayidx11.6.19, align 2, !tbaa !3 *)
mov mem0_152 v_add21_6_19;
(*   %arrayidx9.6.1.19 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %1614 = load i16, i16* %arrayidx9.6.1.19, align 2, !tbaa !3 *)
mov v1614 mem0_158;
(*   %conv1.i.6.1.19 = sext i16 %1614 to i32 *)
cast v_conv1_i_6_1_19@sint32 v1614@sint16;
(*   %mul.i.6.1.19 = mul nsw i32 %conv1.i.6.1.19, -147 *)
mul v_mul_i_6_1_19 v_conv1_i_6_1_19 (-147)@sint32;
(*   %call.i.6.1.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_19, v_call_i_6_1_19);
(*   %arrayidx11.6.1.19 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %1615 = load i16, i16* %arrayidx11.6.1.19, align 2, !tbaa !3 *)
mov v1615 mem0_154;
(*   %sub.6.1.19 = sub i16 %1615, %call.i.6.1.19 *)
sub v_sub_6_1_19 v1615 v_call_i_6_1_19;
(*   store i16 %sub.6.1.19, i16* %arrayidx9.6.1.19, align 2, !tbaa !3 *)
mov mem0_158 v_sub_6_1_19;
(*   %add21.6.1.19 = add i16 %1615, %call.i.6.1.19 *)
add v_add21_6_1_19 v1615 v_call_i_6_1_19;
(*   store i16 %add21.6.1.19, i16* %arrayidx11.6.1.19, align 2, !tbaa !3 *)
mov mem0_154 v_add21_6_1_19;

(* NOTE: k = 84 *)

(*   %arrayidx9.6.20 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %1616 = load i16, i16* %arrayidx9.6.20, align 2, !tbaa !3 *)
mov v1616 mem0_164;
(*   %conv1.i.6.20 = sext i16 %1616 to i32 *)
cast v_conv1_i_6_20@sint32 v1616@sint16;
(*   %mul.i.6.20 = mul nsw i32 %conv1.i.6.20, -777 *)
mul v_mul_i_6_20 v_conv1_i_6_20 (-777)@sint32;
(*   %call.i.6.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_20, v_call_i_6_20);
(*   %arrayidx11.6.20 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %1617 = load i16, i16* %arrayidx11.6.20, align 2, !tbaa !3 *)
mov v1617 mem0_160;
(*   %sub.6.20 = sub i16 %1617, %call.i.6.20 *)
sub v_sub_6_20 v1617 v_call_i_6_20;
(*   store i16 %sub.6.20, i16* %arrayidx9.6.20, align 2, !tbaa !3 *)
mov mem0_164 v_sub_6_20;
(*   %add21.6.20 = add i16 %1617, %call.i.6.20 *)
add v_add21_6_20 v1617 v_call_i_6_20;
(*   store i16 %add21.6.20, i16* %arrayidx11.6.20, align 2, !tbaa !3 *)
mov mem0_160 v_add21_6_20;
(*   %arrayidx9.6.1.20 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %1618 = load i16, i16* %arrayidx9.6.1.20, align 2, !tbaa !3 *)
mov v1618 mem0_166;
(*   %conv1.i.6.1.20 = sext i16 %1618 to i32 *)
cast v_conv1_i_6_1_20@sint32 v1618@sint16;
(*   %mul.i.6.1.20 = mul nsw i32 %conv1.i.6.1.20, -777 *)
mul v_mul_i_6_1_20 v_conv1_i_6_1_20 (-777)@sint32;
(*   %call.i.6.1.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_20, v_call_i_6_1_20);
(*   %arrayidx11.6.1.20 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %1619 = load i16, i16* %arrayidx11.6.1.20, align 2, !tbaa !3 *)
mov v1619 mem0_162;
(*   %sub.6.1.20 = sub i16 %1619, %call.i.6.1.20 *)
sub v_sub_6_1_20 v1619 v_call_i_6_1_20;
(*   store i16 %sub.6.1.20, i16* %arrayidx9.6.1.20, align 2, !tbaa !3 *)
mov mem0_166 v_sub_6_1_20;
(*   %add21.6.1.20 = add i16 %1619, %call.i.6.1.20 *)
add v_add21_6_1_20 v1619 v_call_i_6_1_20;
(*   store i16 %add21.6.1.20, i16* %arrayidx11.6.1.20, align 2, !tbaa !3 *)
mov mem0_162 v_add21_6_1_20;

(* NOTE: k = 85 *)

(*   %arrayidx9.6.21 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %1620 = load i16, i16* %arrayidx9.6.21, align 2, !tbaa !3 *)
mov v1620 mem0_172;
(*   %conv1.i.6.21 = sext i16 %1620 to i32 *)
cast v_conv1_i_6_21@sint32 v1620@sint16;
(*   %mul.i.6.21 = mul nsw i32 %conv1.i.6.21, 1483 *)
mul v_mul_i_6_21 v_conv1_i_6_21 (1483)@sint32;
(*   %call.i.6.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_21, v_call_i_6_21);
(*   %arrayidx11.6.21 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %1621 = load i16, i16* %arrayidx11.6.21, align 2, !tbaa !3 *)
mov v1621 mem0_168;
(*   %sub.6.21 = sub i16 %1621, %call.i.6.21 *)
sub v_sub_6_21 v1621 v_call_i_6_21;
(*   store i16 %sub.6.21, i16* %arrayidx9.6.21, align 2, !tbaa !3 *)
mov mem0_172 v_sub_6_21;
(*   %add21.6.21 = add i16 %1621, %call.i.6.21 *)
add v_add21_6_21 v1621 v_call_i_6_21;
(*   store i16 %add21.6.21, i16* %arrayidx11.6.21, align 2, !tbaa !3 *)
mov mem0_168 v_add21_6_21;
(*   %arrayidx9.6.1.21 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %1622 = load i16, i16* %arrayidx9.6.1.21, align 2, !tbaa !3 *)
mov v1622 mem0_174;
(*   %conv1.i.6.1.21 = sext i16 %1622 to i32 *)
cast v_conv1_i_6_1_21@sint32 v1622@sint16;
(*   %mul.i.6.1.21 = mul nsw i32 %conv1.i.6.1.21, 1483 *)
mul v_mul_i_6_1_21 v_conv1_i_6_1_21 (1483)@sint32;
(*   %call.i.6.1.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_21, v_call_i_6_1_21);
(*   %arrayidx11.6.1.21 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %1623 = load i16, i16* %arrayidx11.6.1.21, align 2, !tbaa !3 *)
mov v1623 mem0_170;
(*   %sub.6.1.21 = sub i16 %1623, %call.i.6.1.21 *)
sub v_sub_6_1_21 v1623 v_call_i_6_1_21;
(*   store i16 %sub.6.1.21, i16* %arrayidx9.6.1.21, align 2, !tbaa !3 *)
mov mem0_174 v_sub_6_1_21;
(*   %add21.6.1.21 = add i16 %1623, %call.i.6.1.21 *)
add v_add21_6_1_21 v1623 v_call_i_6_1_21;
(*   store i16 %add21.6.1.21, i16* %arrayidx11.6.1.21, align 2, !tbaa !3 *)
mov mem0_170 v_add21_6_1_21;

(* NOTE: k = 86 *)

(*   %arrayidx9.6.22 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %1624 = load i16, i16* %arrayidx9.6.22, align 2, !tbaa !3 *)
mov v1624 mem0_180;
(*   %conv1.i.6.22 = sext i16 %1624 to i32 *)
cast v_conv1_i_6_22@sint32 v1624@sint16;
(*   %mul.i.6.22 = mul nsw i32 %conv1.i.6.22, -602 *)
mul v_mul_i_6_22 v_conv1_i_6_22 (-602)@sint32;
(*   %call.i.6.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_22, v_call_i_6_22);
(*   %arrayidx11.6.22 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %1625 = load i16, i16* %arrayidx11.6.22, align 2, !tbaa !3 *)
mov v1625 mem0_176;
(*   %sub.6.22 = sub i16 %1625, %call.i.6.22 *)
sub v_sub_6_22 v1625 v_call_i_6_22;
(*   store i16 %sub.6.22, i16* %arrayidx9.6.22, align 2, !tbaa !3 *)
mov mem0_180 v_sub_6_22;
(*   %add21.6.22 = add i16 %1625, %call.i.6.22 *)
add v_add21_6_22 v1625 v_call_i_6_22;
(*   store i16 %add21.6.22, i16* %arrayidx11.6.22, align 2, !tbaa !3 *)
mov mem0_176 v_add21_6_22;
(*   %arrayidx9.6.1.22 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %1626 = load i16, i16* %arrayidx9.6.1.22, align 2, !tbaa !3 *)
mov v1626 mem0_182;
(*   %conv1.i.6.1.22 = sext i16 %1626 to i32 *)
cast v_conv1_i_6_1_22@sint32 v1626@sint16;
(*   %mul.i.6.1.22 = mul nsw i32 %conv1.i.6.1.22, -602 *)
mul v_mul_i_6_1_22 v_conv1_i_6_1_22 (-602)@sint32;
(*   %call.i.6.1.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_22, v_call_i_6_1_22);
(*   %arrayidx11.6.1.22 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %1627 = load i16, i16* %arrayidx11.6.1.22, align 2, !tbaa !3 *)
mov v1627 mem0_178;
(*   %sub.6.1.22 = sub i16 %1627, %call.i.6.1.22 *)
sub v_sub_6_1_22 v1627 v_call_i_6_1_22;
(*   store i16 %sub.6.1.22, i16* %arrayidx9.6.1.22, align 2, !tbaa !3 *)
mov mem0_182 v_sub_6_1_22;
(*   %add21.6.1.22 = add i16 %1627, %call.i.6.1.22 *)
add v_add21_6_1_22 v1627 v_call_i_6_1_22;
(*   store i16 %add21.6.1.22, i16* %arrayidx11.6.1.22, align 2, !tbaa !3 *)
mov mem0_178 v_add21_6_1_22;

(* NOTE: k = 87 *)

(*   %arrayidx9.6.23 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %1628 = load i16, i16* %arrayidx9.6.23, align 2, !tbaa !3 *)
mov v1628 mem0_188;
(*   %conv1.i.6.23 = sext i16 %1628 to i32 *)
cast v_conv1_i_6_23@sint32 v1628@sint16;
(*   %mul.i.6.23 = mul nsw i32 %conv1.i.6.23, 1119 *)
mul v_mul_i_6_23 v_conv1_i_6_23 (1119)@sint32;
(*   %call.i.6.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_23, v_call_i_6_23);
(*   %arrayidx11.6.23 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %1629 = load i16, i16* %arrayidx11.6.23, align 2, !tbaa !3 *)
mov v1629 mem0_184;
(*   %sub.6.23 = sub i16 %1629, %call.i.6.23 *)
sub v_sub_6_23 v1629 v_call_i_6_23;
(*   store i16 %sub.6.23, i16* %arrayidx9.6.23, align 2, !tbaa !3 *)
mov mem0_188 v_sub_6_23;
(*   %add21.6.23 = add i16 %1629, %call.i.6.23 *)
add v_add21_6_23 v1629 v_call_i_6_23;
(*   store i16 %add21.6.23, i16* %arrayidx11.6.23, align 2, !tbaa !3 *)
mov mem0_184 v_add21_6_23;
(*   %arrayidx9.6.1.23 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %1630 = load i16, i16* %arrayidx9.6.1.23, align 2, !tbaa !3 *)
mov v1630 mem0_190;
(*   %conv1.i.6.1.23 = sext i16 %1630 to i32 *)
cast v_conv1_i_6_1_23@sint32 v1630@sint16;
(*   %mul.i.6.1.23 = mul nsw i32 %conv1.i.6.1.23, 1119 *)
mul v_mul_i_6_1_23 v_conv1_i_6_1_23 (1119)@sint32;
(*   %call.i.6.1.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_23, v_call_i_6_1_23);
(*   %arrayidx11.6.1.23 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %1631 = load i16, i16* %arrayidx11.6.1.23, align 2, !tbaa !3 *)
mov v1631 mem0_186;
(*   %sub.6.1.23 = sub i16 %1631, %call.i.6.1.23 *)
sub v_sub_6_1_23 v1631 v_call_i_6_1_23;
(*   store i16 %sub.6.1.23, i16* %arrayidx9.6.1.23, align 2, !tbaa !3 *)
mov mem0_190 v_sub_6_1_23;
(*   %add21.6.1.23 = add i16 %1631, %call.i.6.1.23 *)
add v_add21_6_1_23 v1631 v_call_i_6_1_23;
(*   store i16 %add21.6.1.23, i16* %arrayidx11.6.1.23, align 2, !tbaa !3 *)
mov mem0_186 v_add21_6_1_23;

(* NOTE: k = 88 *)

(*   %arrayidx9.6.24 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %1632 = load i16, i16* %arrayidx9.6.24, align 2, !tbaa !3 *)
mov v1632 mem0_196;
(*   %conv1.i.6.24 = sext i16 %1632 to i32 *)
cast v_conv1_i_6_24@sint32 v1632@sint16;
(*   %mul.i.6.24 = mul nsw i32 %conv1.i.6.24, -1590 *)
mul v_mul_i_6_24 v_conv1_i_6_24 (-1590)@sint32;
(*   %call.i.6.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_24, v_call_i_6_24);
(*   %arrayidx11.6.24 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %1633 = load i16, i16* %arrayidx11.6.24, align 2, !tbaa !3 *)
mov v1633 mem0_192;
(*   %sub.6.24 = sub i16 %1633, %call.i.6.24 *)
sub v_sub_6_24 v1633 v_call_i_6_24;
(*   store i16 %sub.6.24, i16* %arrayidx9.6.24, align 2, !tbaa !3 *)
mov mem0_196 v_sub_6_24;
(*   %add21.6.24 = add i16 %1633, %call.i.6.24 *)
add v_add21_6_24 v1633 v_call_i_6_24;
(*   store i16 %add21.6.24, i16* %arrayidx11.6.24, align 2, !tbaa !3 *)
mov mem0_192 v_add21_6_24;
(*   %arrayidx9.6.1.24 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %1634 = load i16, i16* %arrayidx9.6.1.24, align 2, !tbaa !3 *)
mov v1634 mem0_198;
(*   %conv1.i.6.1.24 = sext i16 %1634 to i32 *)
cast v_conv1_i_6_1_24@sint32 v1634@sint16;
(*   %mul.i.6.1.24 = mul nsw i32 %conv1.i.6.1.24, -1590 *)
mul v_mul_i_6_1_24 v_conv1_i_6_1_24 (-1590)@sint32;
(*   %call.i.6.1.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_24, v_call_i_6_1_24);
(*   %arrayidx11.6.1.24 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %1635 = load i16, i16* %arrayidx11.6.1.24, align 2, !tbaa !3 *)
mov v1635 mem0_194;
(*   %sub.6.1.24 = sub i16 %1635, %call.i.6.1.24 *)
sub v_sub_6_1_24 v1635 v_call_i_6_1_24;
(*   store i16 %sub.6.1.24, i16* %arrayidx9.6.1.24, align 2, !tbaa !3 *)
mov mem0_198 v_sub_6_1_24;
(*   %add21.6.1.24 = add i16 %1635, %call.i.6.1.24 *)
add v_add21_6_1_24 v1635 v_call_i_6_1_24;
(*   store i16 %add21.6.1.24, i16* %arrayidx11.6.1.24, align 2, !tbaa !3 *)
mov mem0_194 v_add21_6_1_24;

(* NOTE: k = 89 *)

(*   %arrayidx9.6.25 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %1636 = load i16, i16* %arrayidx9.6.25, align 2, !tbaa !3 *)
mov v1636 mem0_204;
(*   %conv1.i.6.25 = sext i16 %1636 to i32 *)
cast v_conv1_i_6_25@sint32 v1636@sint16;
(*   %mul.i.6.25 = mul nsw i32 %conv1.i.6.25, 644 *)
mul v_mul_i_6_25 v_conv1_i_6_25 (644)@sint32;
(*   %call.i.6.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_25, v_call_i_6_25);
(*   %arrayidx11.6.25 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %1637 = load i16, i16* %arrayidx11.6.25, align 2, !tbaa !3 *)
mov v1637 mem0_200;
(*   %sub.6.25 = sub i16 %1637, %call.i.6.25 *)
sub v_sub_6_25 v1637 v_call_i_6_25;
(*   store i16 %sub.6.25, i16* %arrayidx9.6.25, align 2, !tbaa !3 *)
mov mem0_204 v_sub_6_25;
(*   %add21.6.25 = add i16 %1637, %call.i.6.25 *)
add v_add21_6_25 v1637 v_call_i_6_25;
(*   store i16 %add21.6.25, i16* %arrayidx11.6.25, align 2, !tbaa !3 *)
mov mem0_200 v_add21_6_25;
(*   %arrayidx9.6.1.25 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %1638 = load i16, i16* %arrayidx9.6.1.25, align 2, !tbaa !3 *)
mov v1638 mem0_206;
(*   %conv1.i.6.1.25 = sext i16 %1638 to i32 *)
cast v_conv1_i_6_1_25@sint32 v1638@sint16;
(*   %mul.i.6.1.25 = mul nsw i32 %conv1.i.6.1.25, 644 *)
mul v_mul_i_6_1_25 v_conv1_i_6_1_25 (644)@sint32;
(*   %call.i.6.1.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_25, v_call_i_6_1_25);
(*   %arrayidx11.6.1.25 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %1639 = load i16, i16* %arrayidx11.6.1.25, align 2, !tbaa !3 *)
mov v1639 mem0_202;
(*   %sub.6.1.25 = sub i16 %1639, %call.i.6.1.25 *)
sub v_sub_6_1_25 v1639 v_call_i_6_1_25;
(*   store i16 %sub.6.1.25, i16* %arrayidx9.6.1.25, align 2, !tbaa !3 *)
mov mem0_206 v_sub_6_1_25;
(*   %add21.6.1.25 = add i16 %1639, %call.i.6.1.25 *)
add v_add21_6_1_25 v1639 v_call_i_6_1_25;
(*   store i16 %add21.6.1.25, i16* %arrayidx11.6.1.25, align 2, !tbaa !3 *)
mov mem0_202 v_add21_6_1_25;

(* NOTE: k = 90 *)

(*   %arrayidx9.6.26 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %1640 = load i16, i16* %arrayidx9.6.26, align 2, !tbaa !3 *)
mov v1640 mem0_212;
(*   %conv1.i.6.26 = sext i16 %1640 to i32 *)
cast v_conv1_i_6_26@sint32 v1640@sint16;
(*   %mul.i.6.26 = mul nsw i32 %conv1.i.6.26, -872 *)
mul v_mul_i_6_26 v_conv1_i_6_26 (-872)@sint32;
(*   %call.i.6.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_26, v_call_i_6_26);
(*   %arrayidx11.6.26 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %1641 = load i16, i16* %arrayidx11.6.26, align 2, !tbaa !3 *)
mov v1641 mem0_208;
(*   %sub.6.26 = sub i16 %1641, %call.i.6.26 *)
sub v_sub_6_26 v1641 v_call_i_6_26;
(*   store i16 %sub.6.26, i16* %arrayidx9.6.26, align 2, !tbaa !3 *)
mov mem0_212 v_sub_6_26;
(*   %add21.6.26 = add i16 %1641, %call.i.6.26 *)
add v_add21_6_26 v1641 v_call_i_6_26;
(*   store i16 %add21.6.26, i16* %arrayidx11.6.26, align 2, !tbaa !3 *)
mov mem0_208 v_add21_6_26;
(*   %arrayidx9.6.1.26 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %1642 = load i16, i16* %arrayidx9.6.1.26, align 2, !tbaa !3 *)
mov v1642 mem0_214;
(*   %conv1.i.6.1.26 = sext i16 %1642 to i32 *)
cast v_conv1_i_6_1_26@sint32 v1642@sint16;
(*   %mul.i.6.1.26 = mul nsw i32 %conv1.i.6.1.26, -872 *)
mul v_mul_i_6_1_26 v_conv1_i_6_1_26 (-872)@sint32;
(*   %call.i.6.1.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_26, v_call_i_6_1_26);
(*   %arrayidx11.6.1.26 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %1643 = load i16, i16* %arrayidx11.6.1.26, align 2, !tbaa !3 *)
mov v1643 mem0_210;
(*   %sub.6.1.26 = sub i16 %1643, %call.i.6.1.26 *)
sub v_sub_6_1_26 v1643 v_call_i_6_1_26;
(*   store i16 %sub.6.1.26, i16* %arrayidx9.6.1.26, align 2, !tbaa !3 *)
mov mem0_214 v_sub_6_1_26;
(*   %add21.6.1.26 = add i16 %1643, %call.i.6.1.26 *)
add v_add21_6_1_26 v1643 v_call_i_6_1_26;
(*   store i16 %add21.6.1.26, i16* %arrayidx11.6.1.26, align 2, !tbaa !3 *)
mov mem0_210 v_add21_6_1_26;

(* NOTE: k = 91 *)

(*   %arrayidx9.6.27 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %1644 = load i16, i16* %arrayidx9.6.27, align 2, !tbaa !3 *)
mov v1644 mem0_220;
(*   %conv1.i.6.27 = sext i16 %1644 to i32 *)
cast v_conv1_i_6_27@sint32 v1644@sint16;
(*   %mul.i.6.27 = mul nsw i32 %conv1.i.6.27, 349 *)
mul v_mul_i_6_27 v_conv1_i_6_27 (349)@sint32;
(*   %call.i.6.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_27, v_call_i_6_27);
(*   %arrayidx11.6.27 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %1645 = load i16, i16* %arrayidx11.6.27, align 2, !tbaa !3 *)
mov v1645 mem0_216;
(*   %sub.6.27 = sub i16 %1645, %call.i.6.27 *)
sub v_sub_6_27 v1645 v_call_i_6_27;
(*   store i16 %sub.6.27, i16* %arrayidx9.6.27, align 2, !tbaa !3 *)
mov mem0_220 v_sub_6_27;
(*   %add21.6.27 = add i16 %1645, %call.i.6.27 *)
add v_add21_6_27 v1645 v_call_i_6_27;
(*   store i16 %add21.6.27, i16* %arrayidx11.6.27, align 2, !tbaa !3 *)
mov mem0_216 v_add21_6_27;
(*   %arrayidx9.6.1.27 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %1646 = load i16, i16* %arrayidx9.6.1.27, align 2, !tbaa !3 *)
mov v1646 mem0_222;
(*   %conv1.i.6.1.27 = sext i16 %1646 to i32 *)
cast v_conv1_i_6_1_27@sint32 v1646@sint16;
(*   %mul.i.6.1.27 = mul nsw i32 %conv1.i.6.1.27, 349 *)
mul v_mul_i_6_1_27 v_conv1_i_6_1_27 (349)@sint32;
(*   %call.i.6.1.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_27, v_call_i_6_1_27);
(*   %arrayidx11.6.1.27 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %1647 = load i16, i16* %arrayidx11.6.1.27, align 2, !tbaa !3 *)
mov v1647 mem0_218;
(*   %sub.6.1.27 = sub i16 %1647, %call.i.6.1.27 *)
sub v_sub_6_1_27 v1647 v_call_i_6_1_27;
(*   store i16 %sub.6.1.27, i16* %arrayidx9.6.1.27, align 2, !tbaa !3 *)
mov mem0_222 v_sub_6_1_27;
(*   %add21.6.1.27 = add i16 %1647, %call.i.6.1.27 *)
add v_add21_6_1_27 v1647 v_call_i_6_1_27;
(*   store i16 %add21.6.1.27, i16* %arrayidx11.6.1.27, align 2, !tbaa !3 *)
mov mem0_218 v_add21_6_1_27;

(* NOTE: k = 92 *)

(*   %arrayidx9.6.28 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %1648 = load i16, i16* %arrayidx9.6.28, align 2, !tbaa !3 *)
mov v1648 mem0_228;
(*   %conv1.i.6.28 = sext i16 %1648 to i32 *)
cast v_conv1_i_6_28@sint32 v1648@sint16;
(*   %mul.i.6.28 = mul nsw i32 %conv1.i.6.28, 418 *)
mul v_mul_i_6_28 v_conv1_i_6_28 (418)@sint32;
(*   %call.i.6.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_28, v_call_i_6_28);
(*   %arrayidx11.6.28 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %1649 = load i16, i16* %arrayidx11.6.28, align 2, !tbaa !3 *)
mov v1649 mem0_224;
(*   %sub.6.28 = sub i16 %1649, %call.i.6.28 *)
sub v_sub_6_28 v1649 v_call_i_6_28;
(*   store i16 %sub.6.28, i16* %arrayidx9.6.28, align 2, !tbaa !3 *)
mov mem0_228 v_sub_6_28;
(*   %add21.6.28 = add i16 %1649, %call.i.6.28 *)
add v_add21_6_28 v1649 v_call_i_6_28;
(*   store i16 %add21.6.28, i16* %arrayidx11.6.28, align 2, !tbaa !3 *)
mov mem0_224 v_add21_6_28;
(*   %arrayidx9.6.1.28 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %1650 = load i16, i16* %arrayidx9.6.1.28, align 2, !tbaa !3 *)
mov v1650 mem0_230;
(*   %conv1.i.6.1.28 = sext i16 %1650 to i32 *)
cast v_conv1_i_6_1_28@sint32 v1650@sint16;
(*   %mul.i.6.1.28 = mul nsw i32 %conv1.i.6.1.28, 418 *)
mul v_mul_i_6_1_28 v_conv1_i_6_1_28 (418)@sint32;
(*   %call.i.6.1.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_28, v_call_i_6_1_28);
(*   %arrayidx11.6.1.28 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %1651 = load i16, i16* %arrayidx11.6.1.28, align 2, !tbaa !3 *)
mov v1651 mem0_226;
(*   %sub.6.1.28 = sub i16 %1651, %call.i.6.1.28 *)
sub v_sub_6_1_28 v1651 v_call_i_6_1_28;
(*   store i16 %sub.6.1.28, i16* %arrayidx9.6.1.28, align 2, !tbaa !3 *)
mov mem0_230 v_sub_6_1_28;
(*   %add21.6.1.28 = add i16 %1651, %call.i.6.1.28 *)
add v_add21_6_1_28 v1651 v_call_i_6_1_28;
(*   store i16 %add21.6.1.28, i16* %arrayidx11.6.1.28, align 2, !tbaa !3 *)
mov mem0_226 v_add21_6_1_28;

(* NOTE: k = 93 *)

(*   %arrayidx9.6.29 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %1652 = load i16, i16* %arrayidx9.6.29, align 2, !tbaa !3 *)
mov v1652 mem0_236;
(*   %conv1.i.6.29 = sext i16 %1652 to i32 *)
cast v_conv1_i_6_29@sint32 v1652@sint16;
(*   %mul.i.6.29 = mul nsw i32 %conv1.i.6.29, 329 *)
mul v_mul_i_6_29 v_conv1_i_6_29 (329)@sint32;
(*   %call.i.6.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_29, v_call_i_6_29);
(*   %arrayidx11.6.29 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %1653 = load i16, i16* %arrayidx11.6.29, align 2, !tbaa !3 *)
mov v1653 mem0_232;
(*   %sub.6.29 = sub i16 %1653, %call.i.6.29 *)
sub v_sub_6_29 v1653 v_call_i_6_29;
(*   store i16 %sub.6.29, i16* %arrayidx9.6.29, align 2, !tbaa !3 *)
mov mem0_236 v_sub_6_29;
(*   %add21.6.29 = add i16 %1653, %call.i.6.29 *)
add v_add21_6_29 v1653 v_call_i_6_29;
(*   store i16 %add21.6.29, i16* %arrayidx11.6.29, align 2, !tbaa !3 *)
mov mem0_232 v_add21_6_29;
(*   %arrayidx9.6.1.29 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %1654 = load i16, i16* %arrayidx9.6.1.29, align 2, !tbaa !3 *)
mov v1654 mem0_238;
(*   %conv1.i.6.1.29 = sext i16 %1654 to i32 *)
cast v_conv1_i_6_1_29@sint32 v1654@sint16;
(*   %mul.i.6.1.29 = mul nsw i32 %conv1.i.6.1.29, 329 *)
mul v_mul_i_6_1_29 v_conv1_i_6_1_29 (329)@sint32;
(*   %call.i.6.1.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_29, v_call_i_6_1_29);
(*   %arrayidx11.6.1.29 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %1655 = load i16, i16* %arrayidx11.6.1.29, align 2, !tbaa !3 *)
mov v1655 mem0_234;
(*   %sub.6.1.29 = sub i16 %1655, %call.i.6.1.29 *)
sub v_sub_6_1_29 v1655 v_call_i_6_1_29;
(*   store i16 %sub.6.1.29, i16* %arrayidx9.6.1.29, align 2, !tbaa !3 *)
mov mem0_238 v_sub_6_1_29;
(*   %add21.6.1.29 = add i16 %1655, %call.i.6.1.29 *)
add v_add21_6_1_29 v1655 v_call_i_6_1_29;
(*   store i16 %add21.6.1.29, i16* %arrayidx11.6.1.29, align 2, !tbaa !3 *)
mov mem0_234 v_add21_6_1_29;

(* NOTE: k = 94 *)

(*   %arrayidx9.6.30 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %1656 = load i16, i16* %arrayidx9.6.30, align 2, !tbaa !3 *)
mov v1656 mem0_244;
(*   %conv1.i.6.30 = sext i16 %1656 to i32 *)
cast v_conv1_i_6_30@sint32 v1656@sint16;
(*   %mul.i.6.30 = mul nsw i32 %conv1.i.6.30, -156 *)
mul v_mul_i_6_30 v_conv1_i_6_30 (-156)@sint32;
(*   %call.i.6.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_30, v_call_i_6_30);
(*   %arrayidx11.6.30 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %1657 = load i16, i16* %arrayidx11.6.30, align 2, !tbaa !3 *)
mov v1657 mem0_240;
(*   %sub.6.30 = sub i16 %1657, %call.i.6.30 *)
sub v_sub_6_30 v1657 v_call_i_6_30;
(*   store i16 %sub.6.30, i16* %arrayidx9.6.30, align 2, !tbaa !3 *)
mov mem0_244 v_sub_6_30;
(*   %add21.6.30 = add i16 %1657, %call.i.6.30 *)
add v_add21_6_30 v1657 v_call_i_6_30;
(*   store i16 %add21.6.30, i16* %arrayidx11.6.30, align 2, !tbaa !3 *)
mov mem0_240 v_add21_6_30;
(*   %arrayidx9.6.1.30 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %1658 = load i16, i16* %arrayidx9.6.1.30, align 2, !tbaa !3 *)
mov v1658 mem0_246;
(*   %conv1.i.6.1.30 = sext i16 %1658 to i32 *)
cast v_conv1_i_6_1_30@sint32 v1658@sint16;
(*   %mul.i.6.1.30 = mul nsw i32 %conv1.i.6.1.30, -156 *)
mul v_mul_i_6_1_30 v_conv1_i_6_1_30 (-156)@sint32;
(*   %call.i.6.1.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_30, v_call_i_6_1_30);
(*   %arrayidx11.6.1.30 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %1659 = load i16, i16* %arrayidx11.6.1.30, align 2, !tbaa !3 *)
mov v1659 mem0_242;
(*   %sub.6.1.30 = sub i16 %1659, %call.i.6.1.30 *)
sub v_sub_6_1_30 v1659 v_call_i_6_1_30;
(*   store i16 %sub.6.1.30, i16* %arrayidx9.6.1.30, align 2, !tbaa !3 *)
mov mem0_246 v_sub_6_1_30;
(*   %add21.6.1.30 = add i16 %1659, %call.i.6.1.30 *)
add v_add21_6_1_30 v1659 v_call_i_6_1_30;
(*   store i16 %add21.6.1.30, i16* %arrayidx11.6.1.30, align 2, !tbaa !3 *)
mov mem0_242 v_add21_6_1_30;

(* NOTE: k = 95 *)

(*   %arrayidx9.6.31 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %1660 = load i16, i16* %arrayidx9.6.31, align 2, !tbaa !3 *)
mov v1660 mem0_252;
(*   %conv1.i.6.31 = sext i16 %1660 to i32 *)
cast v_conv1_i_6_31@sint32 v1660@sint16;
(*   %mul.i.6.31 = mul nsw i32 %conv1.i.6.31, -75 *)
mul v_mul_i_6_31 v_conv1_i_6_31 (-75)@sint32;
(*   %call.i.6.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_31, v_call_i_6_31);
(*   %arrayidx11.6.31 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %1661 = load i16, i16* %arrayidx11.6.31, align 2, !tbaa !3 *)
mov v1661 mem0_248;
(*   %sub.6.31 = sub i16 %1661, %call.i.6.31 *)
sub v_sub_6_31 v1661 v_call_i_6_31;
(*   store i16 %sub.6.31, i16* %arrayidx9.6.31, align 2, !tbaa !3 *)
mov mem0_252 v_sub_6_31;
(*   %add21.6.31 = add i16 %1661, %call.i.6.31 *)
add v_add21_6_31 v1661 v_call_i_6_31;
(*   store i16 %add21.6.31, i16* %arrayidx11.6.31, align 2, !tbaa !3 *)
mov mem0_248 v_add21_6_31;
(*   %arrayidx9.6.1.31 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %1662 = load i16, i16* %arrayidx9.6.1.31, align 2, !tbaa !3 *)
mov v1662 mem0_254;
(*   %conv1.i.6.1.31 = sext i16 %1662 to i32 *)
cast v_conv1_i_6_1_31@sint32 v1662@sint16;
(*   %mul.i.6.1.31 = mul nsw i32 %conv1.i.6.1.31, -75 *)
mul v_mul_i_6_1_31 v_conv1_i_6_1_31 (-75)@sint32;
(*   %call.i.6.1.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_31, v_call_i_6_1_31);
(*   %arrayidx11.6.1.31 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %1663 = load i16, i16* %arrayidx11.6.1.31, align 2, !tbaa !3 *)
mov v1663 mem0_250;
(*   %sub.6.1.31 = sub i16 %1663, %call.i.6.1.31 *)
sub v_sub_6_1_31 v1663 v_call_i_6_1_31;
(*   store i16 %sub.6.1.31, i16* %arrayidx9.6.1.31, align 2, !tbaa !3 *)
mov mem0_254 v_sub_6_1_31;
(*   %add21.6.1.31 = add i16 %1663, %call.i.6.1.31 *)
add v_add21_6_1_31 v1663 v_call_i_6_1_31;
(*   store i16 %add21.6.1.31, i16* %arrayidx11.6.1.31, align 2, !tbaa !3 *)
mov mem0_250 v_add21_6_1_31;

(* NOTE: k = 96 *)

(*   %arrayidx9.6.32 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %1664 = load i16, i16* %arrayidx9.6.32, align 2, !tbaa !3 *)
mov v1664 mem0_260;
(*   %conv1.i.6.32 = sext i16 %1664 to i32 *)
cast v_conv1_i_6_32@sint32 v1664@sint16;
(*   %mul.i.6.32 = mul nsw i32 %conv1.i.6.32, 817 *)
mul v_mul_i_6_32 v_conv1_i_6_32 (817)@sint32;
(*   %call.i.6.32 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.32) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_32, v_call_i_6_32);
(*   %arrayidx11.6.32 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %1665 = load i16, i16* %arrayidx11.6.32, align 2, !tbaa !3 *)
mov v1665 mem0_256;
(*   %sub.6.32 = sub i16 %1665, %call.i.6.32 *)
sub v_sub_6_32 v1665 v_call_i_6_32;
(*   store i16 %sub.6.32, i16* %arrayidx9.6.32, align 2, !tbaa !3 *)
mov mem0_260 v_sub_6_32;
(*   %add21.6.32 = add i16 %1665, %call.i.6.32 *)
add v_add21_6_32 v1665 v_call_i_6_32;
(*   store i16 %add21.6.32, i16* %arrayidx11.6.32, align 2, !tbaa !3 *)
mov mem0_256 v_add21_6_32;
(*   %arrayidx9.6.1.32 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %1666 = load i16, i16* %arrayidx9.6.1.32, align 2, !tbaa !3 *)
mov v1666 mem0_262;
(*   %conv1.i.6.1.32 = sext i16 %1666 to i32 *)
cast v_conv1_i_6_1_32@sint32 v1666@sint16;
(*   %mul.i.6.1.32 = mul nsw i32 %conv1.i.6.1.32, 817 *)
mul v_mul_i_6_1_32 v_conv1_i_6_1_32 (817)@sint32;
(*   %call.i.6.1.32 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.32) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_32, v_call_i_6_1_32);
(*   %arrayidx11.6.1.32 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %1667 = load i16, i16* %arrayidx11.6.1.32, align 2, !tbaa !3 *)
mov v1667 mem0_258;
(*   %sub.6.1.32 = sub i16 %1667, %call.i.6.1.32 *)
sub v_sub_6_1_32 v1667 v_call_i_6_1_32;
(*   store i16 %sub.6.1.32, i16* %arrayidx9.6.1.32, align 2, !tbaa !3 *)
mov mem0_262 v_sub_6_1_32;
(*   %add21.6.1.32 = add i16 %1667, %call.i.6.1.32 *)
add v_add21_6_1_32 v1667 v_call_i_6_1_32;
(*   store i16 %add21.6.1.32, i16* %arrayidx11.6.1.32, align 2, !tbaa !3 *)
mov mem0_258 v_add21_6_1_32;

(* NOTE: k = 97 *)

(*   %arrayidx9.6.33 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %1668 = load i16, i16* %arrayidx9.6.33, align 2, !tbaa !3 *)
mov v1668 mem0_268;
(*   %conv1.i.6.33 = sext i16 %1668 to i32 *)
cast v_conv1_i_6_33@sint32 v1668@sint16;
(*   %mul.i.6.33 = mul nsw i32 %conv1.i.6.33, 1097 *)
mul v_mul_i_6_33 v_conv1_i_6_33 (1097)@sint32;
(*   %call.i.6.33 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.33) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_33, v_call_i_6_33);
(*   %arrayidx11.6.33 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %1669 = load i16, i16* %arrayidx11.6.33, align 2, !tbaa !3 *)
mov v1669 mem0_264;
(*   %sub.6.33 = sub i16 %1669, %call.i.6.33 *)
sub v_sub_6_33 v1669 v_call_i_6_33;
(*   store i16 %sub.6.33, i16* %arrayidx9.6.33, align 2, !tbaa !3 *)
mov mem0_268 v_sub_6_33;
(*   %add21.6.33 = add i16 %1669, %call.i.6.33 *)
add v_add21_6_33 v1669 v_call_i_6_33;
(*   store i16 %add21.6.33, i16* %arrayidx11.6.33, align 2, !tbaa !3 *)
mov mem0_264 v_add21_6_33;
(*   %arrayidx9.6.1.33 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %1670 = load i16, i16* %arrayidx9.6.1.33, align 2, !tbaa !3 *)
mov v1670 mem0_270;
(*   %conv1.i.6.1.33 = sext i16 %1670 to i32 *)
cast v_conv1_i_6_1_33@sint32 v1670@sint16;
(*   %mul.i.6.1.33 = mul nsw i32 %conv1.i.6.1.33, 1097 *)
mul v_mul_i_6_1_33 v_conv1_i_6_1_33 (1097)@sint32;
(*   %call.i.6.1.33 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.33) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_33, v_call_i_6_1_33);
(*   %arrayidx11.6.1.33 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %1671 = load i16, i16* %arrayidx11.6.1.33, align 2, !tbaa !3 *)
mov v1671 mem0_266;
(*   %sub.6.1.33 = sub i16 %1671, %call.i.6.1.33 *)
sub v_sub_6_1_33 v1671 v_call_i_6_1_33;
(*   store i16 %sub.6.1.33, i16* %arrayidx9.6.1.33, align 2, !tbaa !3 *)
mov mem0_270 v_sub_6_1_33;
(*   %add21.6.1.33 = add i16 %1671, %call.i.6.1.33 *)
add v_add21_6_1_33 v1671 v_call_i_6_1_33;
(*   store i16 %add21.6.1.33, i16* %arrayidx11.6.1.33, align 2, !tbaa !3 *)
mov mem0_266 v_add21_6_1_33;

(* NOTE: k = 98 *)

(*   %arrayidx9.6.34 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %1672 = load i16, i16* %arrayidx9.6.34, align 2, !tbaa !3 *)
mov v1672 mem0_276;
(*   %conv1.i.6.34 = sext i16 %1672 to i32 *)
cast v_conv1_i_6_34@sint32 v1672@sint16;
(*   %mul.i.6.34 = mul nsw i32 %conv1.i.6.34, 603 *)
mul v_mul_i_6_34 v_conv1_i_6_34 (603)@sint32;
(*   %call.i.6.34 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.34) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_34, v_call_i_6_34);
(*   %arrayidx11.6.34 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %1673 = load i16, i16* %arrayidx11.6.34, align 2, !tbaa !3 *)
mov v1673 mem0_272;
(*   %sub.6.34 = sub i16 %1673, %call.i.6.34 *)
sub v_sub_6_34 v1673 v_call_i_6_34;
(*   store i16 %sub.6.34, i16* %arrayidx9.6.34, align 2, !tbaa !3 *)
mov mem0_276 v_sub_6_34;
(*   %add21.6.34 = add i16 %1673, %call.i.6.34 *)
add v_add21_6_34 v1673 v_call_i_6_34;
(*   store i16 %add21.6.34, i16* %arrayidx11.6.34, align 2, !tbaa !3 *)
mov mem0_272 v_add21_6_34;
(*   %arrayidx9.6.1.34 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %1674 = load i16, i16* %arrayidx9.6.1.34, align 2, !tbaa !3 *)
mov v1674 mem0_278;
(*   %conv1.i.6.1.34 = sext i16 %1674 to i32 *)
cast v_conv1_i_6_1_34@sint32 v1674@sint16;
(*   %mul.i.6.1.34 = mul nsw i32 %conv1.i.6.1.34, 603 *)
mul v_mul_i_6_1_34 v_conv1_i_6_1_34 (603)@sint32;
(*   %call.i.6.1.34 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.34) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_34, v_call_i_6_1_34);
(*   %arrayidx11.6.1.34 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %1675 = load i16, i16* %arrayidx11.6.1.34, align 2, !tbaa !3 *)
mov v1675 mem0_274;
(*   %sub.6.1.34 = sub i16 %1675, %call.i.6.1.34 *)
sub v_sub_6_1_34 v1675 v_call_i_6_1_34;
(*   store i16 %sub.6.1.34, i16* %arrayidx9.6.1.34, align 2, !tbaa !3 *)
mov mem0_278 v_sub_6_1_34;
(*   %add21.6.1.34 = add i16 %1675, %call.i.6.1.34 *)
add v_add21_6_1_34 v1675 v_call_i_6_1_34;
(*   store i16 %add21.6.1.34, i16* %arrayidx11.6.1.34, align 2, !tbaa !3 *)
mov mem0_274 v_add21_6_1_34;

(* NOTE: k = 99 *)

(*   %arrayidx9.6.35 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %1676 = load i16, i16* %arrayidx9.6.35, align 2, !tbaa !3 *)
mov v1676 mem0_284;
(*   %conv1.i.6.35 = sext i16 %1676 to i32 *)
cast v_conv1_i_6_35@sint32 v1676@sint16;
(*   %mul.i.6.35 = mul nsw i32 %conv1.i.6.35, 610 *)
mul v_mul_i_6_35 v_conv1_i_6_35 (610)@sint32;
(*   %call.i.6.35 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.35) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_35, v_call_i_6_35);
(*   %arrayidx11.6.35 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %1677 = load i16, i16* %arrayidx11.6.35, align 2, !tbaa !3 *)
mov v1677 mem0_280;
(*   %sub.6.35 = sub i16 %1677, %call.i.6.35 *)
sub v_sub_6_35 v1677 v_call_i_6_35;
(*   store i16 %sub.6.35, i16* %arrayidx9.6.35, align 2, !tbaa !3 *)
mov mem0_284 v_sub_6_35;
(*   %add21.6.35 = add i16 %1677, %call.i.6.35 *)
add v_add21_6_35 v1677 v_call_i_6_35;
(*   store i16 %add21.6.35, i16* %arrayidx11.6.35, align 2, !tbaa !3 *)
mov mem0_280 v_add21_6_35;
(*   %arrayidx9.6.1.35 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %1678 = load i16, i16* %arrayidx9.6.1.35, align 2, !tbaa !3 *)
mov v1678 mem0_286;
(*   %conv1.i.6.1.35 = sext i16 %1678 to i32 *)
cast v_conv1_i_6_1_35@sint32 v1678@sint16;
(*   %mul.i.6.1.35 = mul nsw i32 %conv1.i.6.1.35, 610 *)
mul v_mul_i_6_1_35 v_conv1_i_6_1_35 (610)@sint32;
(*   %call.i.6.1.35 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.35) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_35, v_call_i_6_1_35);
(*   %arrayidx11.6.1.35 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %1679 = load i16, i16* %arrayidx11.6.1.35, align 2, !tbaa !3 *)
mov v1679 mem0_282;
(*   %sub.6.1.35 = sub i16 %1679, %call.i.6.1.35 *)
sub v_sub_6_1_35 v1679 v_call_i_6_1_35;
(*   store i16 %sub.6.1.35, i16* %arrayidx9.6.1.35, align 2, !tbaa !3 *)
mov mem0_286 v_sub_6_1_35;
(*   %add21.6.1.35 = add i16 %1679, %call.i.6.1.35 *)
add v_add21_6_1_35 v1679 v_call_i_6_1_35;
(*   store i16 %add21.6.1.35, i16* %arrayidx11.6.1.35, align 2, !tbaa !3 *)
mov mem0_282 v_add21_6_1_35;

(* NOTE: k = 100 *)

(*   %arrayidx9.6.36 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %1680 = load i16, i16* %arrayidx9.6.36, align 2, !tbaa !3 *)
mov v1680 mem0_292;
(*   %conv1.i.6.36 = sext i16 %1680 to i32 *)
cast v_conv1_i_6_36@sint32 v1680@sint16;
(*   %mul.i.6.36 = mul nsw i32 %conv1.i.6.36, 1322 *)
mul v_mul_i_6_36 v_conv1_i_6_36 (1322)@sint32;
(*   %call.i.6.36 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.36) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_36, v_call_i_6_36);
(*   %arrayidx11.6.36 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %1681 = load i16, i16* %arrayidx11.6.36, align 2, !tbaa !3 *)
mov v1681 mem0_288;
(*   %sub.6.36 = sub i16 %1681, %call.i.6.36 *)
sub v_sub_6_36 v1681 v_call_i_6_36;
(*   store i16 %sub.6.36, i16* %arrayidx9.6.36, align 2, !tbaa !3 *)
mov mem0_292 v_sub_6_36;
(*   %add21.6.36 = add i16 %1681, %call.i.6.36 *)
add v_add21_6_36 v1681 v_call_i_6_36;
(*   store i16 %add21.6.36, i16* %arrayidx11.6.36, align 2, !tbaa !3 *)
mov mem0_288 v_add21_6_36;
(*   %arrayidx9.6.1.36 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %1682 = load i16, i16* %arrayidx9.6.1.36, align 2, !tbaa !3 *)
mov v1682 mem0_294;
(*   %conv1.i.6.1.36 = sext i16 %1682 to i32 *)
cast v_conv1_i_6_1_36@sint32 v1682@sint16;
(*   %mul.i.6.1.36 = mul nsw i32 %conv1.i.6.1.36, 1322 *)
mul v_mul_i_6_1_36 v_conv1_i_6_1_36 (1322)@sint32;
(*   %call.i.6.1.36 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.36) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_36, v_call_i_6_1_36);
(*   %arrayidx11.6.1.36 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %1683 = load i16, i16* %arrayidx11.6.1.36, align 2, !tbaa !3 *)
mov v1683 mem0_290;
(*   %sub.6.1.36 = sub i16 %1683, %call.i.6.1.36 *)
sub v_sub_6_1_36 v1683 v_call_i_6_1_36;
(*   store i16 %sub.6.1.36, i16* %arrayidx9.6.1.36, align 2, !tbaa !3 *)
mov mem0_294 v_sub_6_1_36;
(*   %add21.6.1.36 = add i16 %1683, %call.i.6.1.36 *)
add v_add21_6_1_36 v1683 v_call_i_6_1_36;
(*   store i16 %add21.6.1.36, i16* %arrayidx11.6.1.36, align 2, !tbaa !3 *)
mov mem0_290 v_add21_6_1_36;

(* NOTE: k = 101 *)

(*   %arrayidx9.6.37 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %1684 = load i16, i16* %arrayidx9.6.37, align 2, !tbaa !3 *)
mov v1684 mem0_300;
(*   %conv1.i.6.37 = sext i16 %1684 to i32 *)
cast v_conv1_i_6_37@sint32 v1684@sint16;
(*   %mul.i.6.37 = mul nsw i32 %conv1.i.6.37, -1285 *)
mul v_mul_i_6_37 v_conv1_i_6_37 (-1285)@sint32;
(*   %call.i.6.37 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.37) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_37, v_call_i_6_37);
(*   %arrayidx11.6.37 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %1685 = load i16, i16* %arrayidx11.6.37, align 2, !tbaa !3 *)
mov v1685 mem0_296;
(*   %sub.6.37 = sub i16 %1685, %call.i.6.37 *)
sub v_sub_6_37 v1685 v_call_i_6_37;
(*   store i16 %sub.6.37, i16* %arrayidx9.6.37, align 2, !tbaa !3 *)
mov mem0_300 v_sub_6_37;
(*   %add21.6.37 = add i16 %1685, %call.i.6.37 *)
add v_add21_6_37 v1685 v_call_i_6_37;
(*   store i16 %add21.6.37, i16* %arrayidx11.6.37, align 2, !tbaa !3 *)
mov mem0_296 v_add21_6_37;
(*   %arrayidx9.6.1.37 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %1686 = load i16, i16* %arrayidx9.6.1.37, align 2, !tbaa !3 *)
mov v1686 mem0_302;
(*   %conv1.i.6.1.37 = sext i16 %1686 to i32 *)
cast v_conv1_i_6_1_37@sint32 v1686@sint16;
(*   %mul.i.6.1.37 = mul nsw i32 %conv1.i.6.1.37, -1285 *)
mul v_mul_i_6_1_37 v_conv1_i_6_1_37 (-1285)@sint32;
(*   %call.i.6.1.37 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.37) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_37, v_call_i_6_1_37);
(*   %arrayidx11.6.1.37 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %1687 = load i16, i16* %arrayidx11.6.1.37, align 2, !tbaa !3 *)
mov v1687 mem0_298;
(*   %sub.6.1.37 = sub i16 %1687, %call.i.6.1.37 *)
sub v_sub_6_1_37 v1687 v_call_i_6_1_37;
(*   store i16 %sub.6.1.37, i16* %arrayidx9.6.1.37, align 2, !tbaa !3 *)
mov mem0_302 v_sub_6_1_37;
(*   %add21.6.1.37 = add i16 %1687, %call.i.6.1.37 *)
add v_add21_6_1_37 v1687 v_call_i_6_1_37;
(*   store i16 %add21.6.1.37, i16* %arrayidx11.6.1.37, align 2, !tbaa !3 *)
mov mem0_298 v_add21_6_1_37;

(* NOTE: k = 102 *)

(*   %arrayidx9.6.38 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %1688 = load i16, i16* %arrayidx9.6.38, align 2, !tbaa !3 *)
mov v1688 mem0_308;
(*   %conv1.i.6.38 = sext i16 %1688 to i32 *)
cast v_conv1_i_6_38@sint32 v1688@sint16;
(*   %mul.i.6.38 = mul nsw i32 %conv1.i.6.38, -1465 *)
mul v_mul_i_6_38 v_conv1_i_6_38 (-1465)@sint32;
(*   %call.i.6.38 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.38) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_38, v_call_i_6_38);
(*   %arrayidx11.6.38 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %1689 = load i16, i16* %arrayidx11.6.38, align 2, !tbaa !3 *)
mov v1689 mem0_304;
(*   %sub.6.38 = sub i16 %1689, %call.i.6.38 *)
sub v_sub_6_38 v1689 v_call_i_6_38;
(*   store i16 %sub.6.38, i16* %arrayidx9.6.38, align 2, !tbaa !3 *)
mov mem0_308 v_sub_6_38;
(*   %add21.6.38 = add i16 %1689, %call.i.6.38 *)
add v_add21_6_38 v1689 v_call_i_6_38;
(*   store i16 %add21.6.38, i16* %arrayidx11.6.38, align 2, !tbaa !3 *)
mov mem0_304 v_add21_6_38;
(*   %arrayidx9.6.1.38 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %1690 = load i16, i16* %arrayidx9.6.1.38, align 2, !tbaa !3 *)
mov v1690 mem0_310;
(*   %conv1.i.6.1.38 = sext i16 %1690 to i32 *)
cast v_conv1_i_6_1_38@sint32 v1690@sint16;
(*   %mul.i.6.1.38 = mul nsw i32 %conv1.i.6.1.38, -1465 *)
mul v_mul_i_6_1_38 v_conv1_i_6_1_38 (-1465)@sint32;
(*   %call.i.6.1.38 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.38) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_38, v_call_i_6_1_38);
(*   %arrayidx11.6.1.38 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %1691 = load i16, i16* %arrayidx11.6.1.38, align 2, !tbaa !3 *)
mov v1691 mem0_306;
(*   %sub.6.1.38 = sub i16 %1691, %call.i.6.1.38 *)
sub v_sub_6_1_38 v1691 v_call_i_6_1_38;
(*   store i16 %sub.6.1.38, i16* %arrayidx9.6.1.38, align 2, !tbaa !3 *)
mov mem0_310 v_sub_6_1_38;
(*   %add21.6.1.38 = add i16 %1691, %call.i.6.1.38 *)
add v_add21_6_1_38 v1691 v_call_i_6_1_38;
(*   store i16 %add21.6.1.38, i16* %arrayidx11.6.1.38, align 2, !tbaa !3 *)
mov mem0_306 v_add21_6_1_38;

(* NOTE: k = 103 *)

(*   %arrayidx9.6.39 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %1692 = load i16, i16* %arrayidx9.6.39, align 2, !tbaa !3 *)
mov v1692 mem0_316;
(*   %conv1.i.6.39 = sext i16 %1692 to i32 *)
cast v_conv1_i_6_39@sint32 v1692@sint16;
(*   %mul.i.6.39 = mul nsw i32 %conv1.i.6.39, 384 *)
mul v_mul_i_6_39 v_conv1_i_6_39 (384)@sint32;
(*   %call.i.6.39 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.39) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_39, v_call_i_6_39);
(*   %arrayidx11.6.39 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %1693 = load i16, i16* %arrayidx11.6.39, align 2, !tbaa !3 *)
mov v1693 mem0_312;
(*   %sub.6.39 = sub i16 %1693, %call.i.6.39 *)
sub v_sub_6_39 v1693 v_call_i_6_39;
(*   store i16 %sub.6.39, i16* %arrayidx9.6.39, align 2, !tbaa !3 *)
mov mem0_316 v_sub_6_39;
(*   %add21.6.39 = add i16 %1693, %call.i.6.39 *)
add v_add21_6_39 v1693 v_call_i_6_39;
(*   store i16 %add21.6.39, i16* %arrayidx11.6.39, align 2, !tbaa !3 *)
mov mem0_312 v_add21_6_39;
(*   %arrayidx9.6.1.39 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %1694 = load i16, i16* %arrayidx9.6.1.39, align 2, !tbaa !3 *)
mov v1694 mem0_318;
(*   %conv1.i.6.1.39 = sext i16 %1694 to i32 *)
cast v_conv1_i_6_1_39@sint32 v1694@sint16;
(*   %mul.i.6.1.39 = mul nsw i32 %conv1.i.6.1.39, 384 *)
mul v_mul_i_6_1_39 v_conv1_i_6_1_39 (384)@sint32;
(*   %call.i.6.1.39 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.39) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_39, v_call_i_6_1_39);
(*   %arrayidx11.6.1.39 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %1695 = load i16, i16* %arrayidx11.6.1.39, align 2, !tbaa !3 *)
mov v1695 mem0_314;
(*   %sub.6.1.39 = sub i16 %1695, %call.i.6.1.39 *)
sub v_sub_6_1_39 v1695 v_call_i_6_1_39;
(*   store i16 %sub.6.1.39, i16* %arrayidx9.6.1.39, align 2, !tbaa !3 *)
mov mem0_318 v_sub_6_1_39;
(*   %add21.6.1.39 = add i16 %1695, %call.i.6.1.39 *)
add v_add21_6_1_39 v1695 v_call_i_6_1_39;
(*   store i16 %add21.6.1.39, i16* %arrayidx11.6.1.39, align 2, !tbaa !3 *)
mov mem0_314 v_add21_6_1_39;

(* NOTE: k = 104 *)

(*   %arrayidx9.6.40 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %1696 = load i16, i16* %arrayidx9.6.40, align 2, !tbaa !3 *)
mov v1696 mem0_324;
(*   %conv1.i.6.40 = sext i16 %1696 to i32 *)
cast v_conv1_i_6_40@sint32 v1696@sint16;
(*   %mul.i.6.40 = mul nsw i32 %conv1.i.6.40, -1215 *)
mul v_mul_i_6_40 v_conv1_i_6_40 (-1215)@sint32;
(*   %call.i.6.40 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.40) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_40, v_call_i_6_40);
(*   %arrayidx11.6.40 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %1697 = load i16, i16* %arrayidx11.6.40, align 2, !tbaa !3 *)
mov v1697 mem0_320;
(*   %sub.6.40 = sub i16 %1697, %call.i.6.40 *)
sub v_sub_6_40 v1697 v_call_i_6_40;
(*   store i16 %sub.6.40, i16* %arrayidx9.6.40, align 2, !tbaa !3 *)
mov mem0_324 v_sub_6_40;
(*   %add21.6.40 = add i16 %1697, %call.i.6.40 *)
add v_add21_6_40 v1697 v_call_i_6_40;
(*   store i16 %add21.6.40, i16* %arrayidx11.6.40, align 2, !tbaa !3 *)
mov mem0_320 v_add21_6_40;
(*   %arrayidx9.6.1.40 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %1698 = load i16, i16* %arrayidx9.6.1.40, align 2, !tbaa !3 *)
mov v1698 mem0_326;
(*   %conv1.i.6.1.40 = sext i16 %1698 to i32 *)
cast v_conv1_i_6_1_40@sint32 v1698@sint16;
(*   %mul.i.6.1.40 = mul nsw i32 %conv1.i.6.1.40, -1215 *)
mul v_mul_i_6_1_40 v_conv1_i_6_1_40 (-1215)@sint32;
(*   %call.i.6.1.40 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.40) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_40, v_call_i_6_1_40);
(*   %arrayidx11.6.1.40 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %1699 = load i16, i16* %arrayidx11.6.1.40, align 2, !tbaa !3 *)
mov v1699 mem0_322;
(*   %sub.6.1.40 = sub i16 %1699, %call.i.6.1.40 *)
sub v_sub_6_1_40 v1699 v_call_i_6_1_40;
(*   store i16 %sub.6.1.40, i16* %arrayidx9.6.1.40, align 2, !tbaa !3 *)
mov mem0_326 v_sub_6_1_40;
(*   %add21.6.1.40 = add i16 %1699, %call.i.6.1.40 *)
add v_add21_6_1_40 v1699 v_call_i_6_1_40;
(*   store i16 %add21.6.1.40, i16* %arrayidx11.6.1.40, align 2, !tbaa !3 *)
mov mem0_322 v_add21_6_1_40;

(* NOTE: k = 105 *)

(*   %arrayidx9.6.41 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %1700 = load i16, i16* %arrayidx9.6.41, align 2, !tbaa !3 *)
mov v1700 mem0_332;
(*   %conv1.i.6.41 = sext i16 %1700 to i32 *)
cast v_conv1_i_6_41@sint32 v1700@sint16;
(*   %mul.i.6.41 = mul nsw i32 %conv1.i.6.41, -136 *)
mul v_mul_i_6_41 v_conv1_i_6_41 (-136)@sint32;
(*   %call.i.6.41 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.41) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_41, v_call_i_6_41);
(*   %arrayidx11.6.41 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %1701 = load i16, i16* %arrayidx11.6.41, align 2, !tbaa !3 *)
mov v1701 mem0_328;
(*   %sub.6.41 = sub i16 %1701, %call.i.6.41 *)
sub v_sub_6_41 v1701 v_call_i_6_41;
(*   store i16 %sub.6.41, i16* %arrayidx9.6.41, align 2, !tbaa !3 *)
mov mem0_332 v_sub_6_41;
(*   %add21.6.41 = add i16 %1701, %call.i.6.41 *)
add v_add21_6_41 v1701 v_call_i_6_41;
(*   store i16 %add21.6.41, i16* %arrayidx11.6.41, align 2, !tbaa !3 *)
mov mem0_328 v_add21_6_41;
(*   %arrayidx9.6.1.41 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %1702 = load i16, i16* %arrayidx9.6.1.41, align 2, !tbaa !3 *)
mov v1702 mem0_334;
(*   %conv1.i.6.1.41 = sext i16 %1702 to i32 *)
cast v_conv1_i_6_1_41@sint32 v1702@sint16;
(*   %mul.i.6.1.41 = mul nsw i32 %conv1.i.6.1.41, -136 *)
mul v_mul_i_6_1_41 v_conv1_i_6_1_41 (-136)@sint32;
(*   %call.i.6.1.41 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.41) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_41, v_call_i_6_1_41);
(*   %arrayidx11.6.1.41 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %1703 = load i16, i16* %arrayidx11.6.1.41, align 2, !tbaa !3 *)
mov v1703 mem0_330;
(*   %sub.6.1.41 = sub i16 %1703, %call.i.6.1.41 *)
sub v_sub_6_1_41 v1703 v_call_i_6_1_41;
(*   store i16 %sub.6.1.41, i16* %arrayidx9.6.1.41, align 2, !tbaa !3 *)
mov mem0_334 v_sub_6_1_41;
(*   %add21.6.1.41 = add i16 %1703, %call.i.6.1.41 *)
add v_add21_6_1_41 v1703 v_call_i_6_1_41;
(*   store i16 %add21.6.1.41, i16* %arrayidx11.6.1.41, align 2, !tbaa !3 *)
mov mem0_330 v_add21_6_1_41;

(* NOTE: k = 106 *)

(*   %arrayidx9.6.42 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %1704 = load i16, i16* %arrayidx9.6.42, align 2, !tbaa !3 *)
mov v1704 mem0_340;
(*   %conv1.i.6.42 = sext i16 %1704 to i32 *)
cast v_conv1_i_6_42@sint32 v1704@sint16;
(*   %mul.i.6.42 = mul nsw i32 %conv1.i.6.42, 1218 *)
mul v_mul_i_6_42 v_conv1_i_6_42 (1218)@sint32;
(*   %call.i.6.42 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.42) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_42, v_call_i_6_42);
(*   %arrayidx11.6.42 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %1705 = load i16, i16* %arrayidx11.6.42, align 2, !tbaa !3 *)
mov v1705 mem0_336;
(*   %sub.6.42 = sub i16 %1705, %call.i.6.42 *)
sub v_sub_6_42 v1705 v_call_i_6_42;
(*   store i16 %sub.6.42, i16* %arrayidx9.6.42, align 2, !tbaa !3 *)
mov mem0_340 v_sub_6_42;
(*   %add21.6.42 = add i16 %1705, %call.i.6.42 *)
add v_add21_6_42 v1705 v_call_i_6_42;
(*   store i16 %add21.6.42, i16* %arrayidx11.6.42, align 2, !tbaa !3 *)
mov mem0_336 v_add21_6_42;
(*   %arrayidx9.6.1.42 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %1706 = load i16, i16* %arrayidx9.6.1.42, align 2, !tbaa !3 *)
mov v1706 mem0_342;
(*   %conv1.i.6.1.42 = sext i16 %1706 to i32 *)
cast v_conv1_i_6_1_42@sint32 v1706@sint16;
(*   %mul.i.6.1.42 = mul nsw i32 %conv1.i.6.1.42, 1218 *)
mul v_mul_i_6_1_42 v_conv1_i_6_1_42 (1218)@sint32;
(*   %call.i.6.1.42 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.42) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_42, v_call_i_6_1_42);
(*   %arrayidx11.6.1.42 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %1707 = load i16, i16* %arrayidx11.6.1.42, align 2, !tbaa !3 *)
mov v1707 mem0_338;
(*   %sub.6.1.42 = sub i16 %1707, %call.i.6.1.42 *)
sub v_sub_6_1_42 v1707 v_call_i_6_1_42;
(*   store i16 %sub.6.1.42, i16* %arrayidx9.6.1.42, align 2, !tbaa !3 *)
mov mem0_342 v_sub_6_1_42;
(*   %add21.6.1.42 = add i16 %1707, %call.i.6.1.42 *)
add v_add21_6_1_42 v1707 v_call_i_6_1_42;
(*   store i16 %add21.6.1.42, i16* %arrayidx11.6.1.42, align 2, !tbaa !3 *)
mov mem0_338 v_add21_6_1_42;

(* NOTE: k = 107 *)

(*   %arrayidx9.6.43 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %1708 = load i16, i16* %arrayidx9.6.43, align 2, !tbaa !3 *)
mov v1708 mem0_348;
(*   %conv1.i.6.43 = sext i16 %1708 to i32 *)
cast v_conv1_i_6_43@sint32 v1708@sint16;
(*   %mul.i.6.43 = mul nsw i32 %conv1.i.6.43, -1335 *)
mul v_mul_i_6_43 v_conv1_i_6_43 (-1335)@sint32;
(*   %call.i.6.43 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.43) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_43, v_call_i_6_43);
(*   %arrayidx11.6.43 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %1709 = load i16, i16* %arrayidx11.6.43, align 2, !tbaa !3 *)
mov v1709 mem0_344;
(*   %sub.6.43 = sub i16 %1709, %call.i.6.43 *)
sub v_sub_6_43 v1709 v_call_i_6_43;
(*   store i16 %sub.6.43, i16* %arrayidx9.6.43, align 2, !tbaa !3 *)
mov mem0_348 v_sub_6_43;
(*   %add21.6.43 = add i16 %1709, %call.i.6.43 *)
add v_add21_6_43 v1709 v_call_i_6_43;
(*   store i16 %add21.6.43, i16* %arrayidx11.6.43, align 2, !tbaa !3 *)
mov mem0_344 v_add21_6_43;
(*   %arrayidx9.6.1.43 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %1710 = load i16, i16* %arrayidx9.6.1.43, align 2, !tbaa !3 *)
mov v1710 mem0_350;
(*   %conv1.i.6.1.43 = sext i16 %1710 to i32 *)
cast v_conv1_i_6_1_43@sint32 v1710@sint16;
(*   %mul.i.6.1.43 = mul nsw i32 %conv1.i.6.1.43, -1335 *)
mul v_mul_i_6_1_43 v_conv1_i_6_1_43 (-1335)@sint32;
(*   %call.i.6.1.43 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.43) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_43, v_call_i_6_1_43);
(*   %arrayidx11.6.1.43 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %1711 = load i16, i16* %arrayidx11.6.1.43, align 2, !tbaa !3 *)
mov v1711 mem0_346;
(*   %sub.6.1.43 = sub i16 %1711, %call.i.6.1.43 *)
sub v_sub_6_1_43 v1711 v_call_i_6_1_43;
(*   store i16 %sub.6.1.43, i16* %arrayidx9.6.1.43, align 2, !tbaa !3 *)
mov mem0_350 v_sub_6_1_43;
(*   %add21.6.1.43 = add i16 %1711, %call.i.6.1.43 *)
add v_add21_6_1_43 v1711 v_call_i_6_1_43;
(*   store i16 %add21.6.1.43, i16* %arrayidx11.6.1.43, align 2, !tbaa !3 *)
mov mem0_346 v_add21_6_1_43;

(* NOTE: k = 108 *)

(*   %arrayidx9.6.44 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %1712 = load i16, i16* %arrayidx9.6.44, align 2, !tbaa !3 *)
mov v1712 mem0_356;
(*   %conv1.i.6.44 = sext i16 %1712 to i32 *)
cast v_conv1_i_6_44@sint32 v1712@sint16;
(*   %mul.i.6.44 = mul nsw i32 %conv1.i.6.44, -874 *)
mul v_mul_i_6_44 v_conv1_i_6_44 (-874)@sint32;
(*   %call.i.6.44 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.44) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_44, v_call_i_6_44);
(*   %arrayidx11.6.44 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %1713 = load i16, i16* %arrayidx11.6.44, align 2, !tbaa !3 *)
mov v1713 mem0_352;
(*   %sub.6.44 = sub i16 %1713, %call.i.6.44 *)
sub v_sub_6_44 v1713 v_call_i_6_44;
(*   store i16 %sub.6.44, i16* %arrayidx9.6.44, align 2, !tbaa !3 *)
mov mem0_356 v_sub_6_44;
(*   %add21.6.44 = add i16 %1713, %call.i.6.44 *)
add v_add21_6_44 v1713 v_call_i_6_44;
(*   store i16 %add21.6.44, i16* %arrayidx11.6.44, align 2, !tbaa !3 *)
mov mem0_352 v_add21_6_44;
(*   %arrayidx9.6.1.44 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %1714 = load i16, i16* %arrayidx9.6.1.44, align 2, !tbaa !3 *)
mov v1714 mem0_358;
(*   %conv1.i.6.1.44 = sext i16 %1714 to i32 *)
cast v_conv1_i_6_1_44@sint32 v1714@sint16;
(*   %mul.i.6.1.44 = mul nsw i32 %conv1.i.6.1.44, -874 *)
mul v_mul_i_6_1_44 v_conv1_i_6_1_44 (-874)@sint32;
(*   %call.i.6.1.44 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.44) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_44, v_call_i_6_1_44);
(*   %arrayidx11.6.1.44 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %1715 = load i16, i16* %arrayidx11.6.1.44, align 2, !tbaa !3 *)
mov v1715 mem0_354;
(*   %sub.6.1.44 = sub i16 %1715, %call.i.6.1.44 *)
sub v_sub_6_1_44 v1715 v_call_i_6_1_44;
(*   store i16 %sub.6.1.44, i16* %arrayidx9.6.1.44, align 2, !tbaa !3 *)
mov mem0_358 v_sub_6_1_44;
(*   %add21.6.1.44 = add i16 %1715, %call.i.6.1.44 *)
add v_add21_6_1_44 v1715 v_call_i_6_1_44;
(*   store i16 %add21.6.1.44, i16* %arrayidx11.6.1.44, align 2, !tbaa !3 *)
mov mem0_354 v_add21_6_1_44;

(* NOTE: k = 109 *)

(*   %arrayidx9.6.45 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %1716 = load i16, i16* %arrayidx9.6.45, align 2, !tbaa !3 *)
mov v1716 mem0_364;
(*   %conv1.i.6.45 = sext i16 %1716 to i32 *)
cast v_conv1_i_6_45@sint32 v1716@sint16;
(*   %mul.i.6.45 = mul nsw i32 %conv1.i.6.45, 220 *)
mul v_mul_i_6_45 v_conv1_i_6_45 (220)@sint32;
(*   %call.i.6.45 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.45) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_45, v_call_i_6_45);
(*   %arrayidx11.6.45 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %1717 = load i16, i16* %arrayidx11.6.45, align 2, !tbaa !3 *)
mov v1717 mem0_360;
(*   %sub.6.45 = sub i16 %1717, %call.i.6.45 *)
sub v_sub_6_45 v1717 v_call_i_6_45;
(*   store i16 %sub.6.45, i16* %arrayidx9.6.45, align 2, !tbaa !3 *)
mov mem0_364 v_sub_6_45;
(*   %add21.6.45 = add i16 %1717, %call.i.6.45 *)
add v_add21_6_45 v1717 v_call_i_6_45;
(*   store i16 %add21.6.45, i16* %arrayidx11.6.45, align 2, !tbaa !3 *)
mov mem0_360 v_add21_6_45;
(*   %arrayidx9.6.1.45 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %1718 = load i16, i16* %arrayidx9.6.1.45, align 2, !tbaa !3 *)
mov v1718 mem0_366;
(*   %conv1.i.6.1.45 = sext i16 %1718 to i32 *)
cast v_conv1_i_6_1_45@sint32 v1718@sint16;
(*   %mul.i.6.1.45 = mul nsw i32 %conv1.i.6.1.45, 220 *)
mul v_mul_i_6_1_45 v_conv1_i_6_1_45 (220)@sint32;
(*   %call.i.6.1.45 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.45) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_45, v_call_i_6_1_45);
(*   %arrayidx11.6.1.45 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %1719 = load i16, i16* %arrayidx11.6.1.45, align 2, !tbaa !3 *)
mov v1719 mem0_362;
(*   %sub.6.1.45 = sub i16 %1719, %call.i.6.1.45 *)
sub v_sub_6_1_45 v1719 v_call_i_6_1_45;
(*   store i16 %sub.6.1.45, i16* %arrayidx9.6.1.45, align 2, !tbaa !3 *)
mov mem0_366 v_sub_6_1_45;
(*   %add21.6.1.45 = add i16 %1719, %call.i.6.1.45 *)
add v_add21_6_1_45 v1719 v_call_i_6_1_45;
(*   store i16 %add21.6.1.45, i16* %arrayidx11.6.1.45, align 2, !tbaa !3 *)
mov mem0_362 v_add21_6_1_45;

(* NOTE: k = 110 *)

(*   %arrayidx9.6.46 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %1720 = load i16, i16* %arrayidx9.6.46, align 2, !tbaa !3 *)
mov v1720 mem0_372;
(*   %conv1.i.6.46 = sext i16 %1720 to i32 *)
cast v_conv1_i_6_46@sint32 v1720@sint16;
(*   %mul.i.6.46 = mul nsw i32 %conv1.i.6.46, -1187 *)
mul v_mul_i_6_46 v_conv1_i_6_46 (-1187)@sint32;
(*   %call.i.6.46 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.46) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_46, v_call_i_6_46);
(*   %arrayidx11.6.46 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %1721 = load i16, i16* %arrayidx11.6.46, align 2, !tbaa !3 *)
mov v1721 mem0_368;
(*   %sub.6.46 = sub i16 %1721, %call.i.6.46 *)
sub v_sub_6_46 v1721 v_call_i_6_46;
(*   store i16 %sub.6.46, i16* %arrayidx9.6.46, align 2, !tbaa !3 *)
mov mem0_372 v_sub_6_46;
(*   %add21.6.46 = add i16 %1721, %call.i.6.46 *)
add v_add21_6_46 v1721 v_call_i_6_46;
(*   store i16 %add21.6.46, i16* %arrayidx11.6.46, align 2, !tbaa !3 *)
mov mem0_368 v_add21_6_46;
(*   %arrayidx9.6.1.46 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %1722 = load i16, i16* %arrayidx9.6.1.46, align 2, !tbaa !3 *)
mov v1722 mem0_374;
(*   %conv1.i.6.1.46 = sext i16 %1722 to i32 *)
cast v_conv1_i_6_1_46@sint32 v1722@sint16;
(*   %mul.i.6.1.46 = mul nsw i32 %conv1.i.6.1.46, -1187 *)
mul v_mul_i_6_1_46 v_conv1_i_6_1_46 (-1187)@sint32;
(*   %call.i.6.1.46 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.46) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_46, v_call_i_6_1_46);
(*   %arrayidx11.6.1.46 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %1723 = load i16, i16* %arrayidx11.6.1.46, align 2, !tbaa !3 *)
mov v1723 mem0_370;
(*   %sub.6.1.46 = sub i16 %1723, %call.i.6.1.46 *)
sub v_sub_6_1_46 v1723 v_call_i_6_1_46;
(*   store i16 %sub.6.1.46, i16* %arrayidx9.6.1.46, align 2, !tbaa !3 *)
mov mem0_374 v_sub_6_1_46;
(*   %add21.6.1.46 = add i16 %1723, %call.i.6.1.46 *)
add v_add21_6_1_46 v1723 v_call_i_6_1_46;
(*   store i16 %add21.6.1.46, i16* %arrayidx11.6.1.46, align 2, !tbaa !3 *)
mov mem0_370 v_add21_6_1_46;

(* NOTE: k = 111 *)

(*   %arrayidx9.6.47 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %1724 = load i16, i16* %arrayidx9.6.47, align 2, !tbaa !3 *)
mov v1724 mem0_380;
(*   %conv1.i.6.47 = sext i16 %1724 to i32 *)
cast v_conv1_i_6_47@sint32 v1724@sint16;
(*   %mul.i.6.47 = mul nsw i32 %conv1.i.6.47, -1659 *)
mul v_mul_i_6_47 v_conv1_i_6_47 (-1659)@sint32;
(*   %call.i.6.47 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.47) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_47, v_call_i_6_47);
(*   %arrayidx11.6.47 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %1725 = load i16, i16* %arrayidx11.6.47, align 2, !tbaa !3 *)
mov v1725 mem0_376;
(*   %sub.6.47 = sub i16 %1725, %call.i.6.47 *)
sub v_sub_6_47 v1725 v_call_i_6_47;
(*   store i16 %sub.6.47, i16* %arrayidx9.6.47, align 2, !tbaa !3 *)
mov mem0_380 v_sub_6_47;
(*   %add21.6.47 = add i16 %1725, %call.i.6.47 *)
add v_add21_6_47 v1725 v_call_i_6_47;
(*   store i16 %add21.6.47, i16* %arrayidx11.6.47, align 2, !tbaa !3 *)
mov mem0_376 v_add21_6_47;
(*   %arrayidx9.6.1.47 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %1726 = load i16, i16* %arrayidx9.6.1.47, align 2, !tbaa !3 *)
mov v1726 mem0_382;
(*   %conv1.i.6.1.47 = sext i16 %1726 to i32 *)
cast v_conv1_i_6_1_47@sint32 v1726@sint16;
(*   %mul.i.6.1.47 = mul nsw i32 %conv1.i.6.1.47, -1659 *)
mul v_mul_i_6_1_47 v_conv1_i_6_1_47 (-1659)@sint32;
(*   %call.i.6.1.47 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.47) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_47, v_call_i_6_1_47);
(*   %arrayidx11.6.1.47 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %1727 = load i16, i16* %arrayidx11.6.1.47, align 2, !tbaa !3 *)
mov v1727 mem0_378;
(*   %sub.6.1.47 = sub i16 %1727, %call.i.6.1.47 *)
sub v_sub_6_1_47 v1727 v_call_i_6_1_47;
(*   store i16 %sub.6.1.47, i16* %arrayidx9.6.1.47, align 2, !tbaa !3 *)
mov mem0_382 v_sub_6_1_47;
(*   %add21.6.1.47 = add i16 %1727, %call.i.6.1.47 *)
add v_add21_6_1_47 v1727 v_call_i_6_1_47;
(*   store i16 %add21.6.1.47, i16* %arrayidx11.6.1.47, align 2, !tbaa !3 *)
mov mem0_378 v_add21_6_1_47;

(* NOTE: k = 112 *)

(*   %arrayidx9.6.48 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %1728 = load i16, i16* %arrayidx9.6.48, align 2, !tbaa !3 *)
mov v1728 mem0_388;
(*   %conv1.i.6.48 = sext i16 %1728 to i32 *)
cast v_conv1_i_6_48@sint32 v1728@sint16;
(*   %mul.i.6.48 = mul nsw i32 %conv1.i.6.48, -1185 *)
mul v_mul_i_6_48 v_conv1_i_6_48 (-1185)@sint32;
(*   %call.i.6.48 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.48) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_48, v_call_i_6_48);
(*   %arrayidx11.6.48 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %1729 = load i16, i16* %arrayidx11.6.48, align 2, !tbaa !3 *)
mov v1729 mem0_384;
(*   %sub.6.48 = sub i16 %1729, %call.i.6.48 *)
sub v_sub_6_48 v1729 v_call_i_6_48;
(*   store i16 %sub.6.48, i16* %arrayidx9.6.48, align 2, !tbaa !3 *)
mov mem0_388 v_sub_6_48;
(*   %add21.6.48 = add i16 %1729, %call.i.6.48 *)
add v_add21_6_48 v1729 v_call_i_6_48;
(*   store i16 %add21.6.48, i16* %arrayidx11.6.48, align 2, !tbaa !3 *)
mov mem0_384 v_add21_6_48;
(*   %arrayidx9.6.1.48 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %1730 = load i16, i16* %arrayidx9.6.1.48, align 2, !tbaa !3 *)
mov v1730 mem0_390;
(*   %conv1.i.6.1.48 = sext i16 %1730 to i32 *)
cast v_conv1_i_6_1_48@sint32 v1730@sint16;
(*   %mul.i.6.1.48 = mul nsw i32 %conv1.i.6.1.48, -1185 *)
mul v_mul_i_6_1_48 v_conv1_i_6_1_48 (-1185)@sint32;
(*   %call.i.6.1.48 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.48) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_48, v_call_i_6_1_48);
(*   %arrayidx11.6.1.48 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %1731 = load i16, i16* %arrayidx11.6.1.48, align 2, !tbaa !3 *)
mov v1731 mem0_386;
(*   %sub.6.1.48 = sub i16 %1731, %call.i.6.1.48 *)
sub v_sub_6_1_48 v1731 v_call_i_6_1_48;
(*   store i16 %sub.6.1.48, i16* %arrayidx9.6.1.48, align 2, !tbaa !3 *)
mov mem0_390 v_sub_6_1_48;
(*   %add21.6.1.48 = add i16 %1731, %call.i.6.1.48 *)
add v_add21_6_1_48 v1731 v_call_i_6_1_48;
(*   store i16 %add21.6.1.48, i16* %arrayidx11.6.1.48, align 2, !tbaa !3 *)
mov mem0_386 v_add21_6_1_48;

(* NOTE: k = 113 *)

(*   %arrayidx9.6.49 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %1732 = load i16, i16* %arrayidx9.6.49, align 2, !tbaa !3 *)
mov v1732 mem0_396;
(*   %conv1.i.6.49 = sext i16 %1732 to i32 *)
cast v_conv1_i_6_49@sint32 v1732@sint16;
(*   %mul.i.6.49 = mul nsw i32 %conv1.i.6.49, -1530 *)
mul v_mul_i_6_49 v_conv1_i_6_49 (-1530)@sint32;
(*   %call.i.6.49 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.49) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_49, v_call_i_6_49);
(*   %arrayidx11.6.49 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %1733 = load i16, i16* %arrayidx11.6.49, align 2, !tbaa !3 *)
mov v1733 mem0_392;
(*   %sub.6.49 = sub i16 %1733, %call.i.6.49 *)
sub v_sub_6_49 v1733 v_call_i_6_49;
(*   store i16 %sub.6.49, i16* %arrayidx9.6.49, align 2, !tbaa !3 *)
mov mem0_396 v_sub_6_49;
(*   %add21.6.49 = add i16 %1733, %call.i.6.49 *)
add v_add21_6_49 v1733 v_call_i_6_49;
(*   store i16 %add21.6.49, i16* %arrayidx11.6.49, align 2, !tbaa !3 *)
mov mem0_392 v_add21_6_49;
(*   %arrayidx9.6.1.49 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %1734 = load i16, i16* %arrayidx9.6.1.49, align 2, !tbaa !3 *)
mov v1734 mem0_398;
(*   %conv1.i.6.1.49 = sext i16 %1734 to i32 *)
cast v_conv1_i_6_1_49@sint32 v1734@sint16;
(*   %mul.i.6.1.49 = mul nsw i32 %conv1.i.6.1.49, -1530 *)
mul v_mul_i_6_1_49 v_conv1_i_6_1_49 (-1530)@sint32;
(*   %call.i.6.1.49 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.49) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_49, v_call_i_6_1_49);
(*   %arrayidx11.6.1.49 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %1735 = load i16, i16* %arrayidx11.6.1.49, align 2, !tbaa !3 *)
mov v1735 mem0_394;
(*   %sub.6.1.49 = sub i16 %1735, %call.i.6.1.49 *)
sub v_sub_6_1_49 v1735 v_call_i_6_1_49;
(*   store i16 %sub.6.1.49, i16* %arrayidx9.6.1.49, align 2, !tbaa !3 *)
mov mem0_398 v_sub_6_1_49;
(*   %add21.6.1.49 = add i16 %1735, %call.i.6.1.49 *)
add v_add21_6_1_49 v1735 v_call_i_6_1_49;
(*   store i16 %add21.6.1.49, i16* %arrayidx11.6.1.49, align 2, !tbaa !3 *)
mov mem0_394 v_add21_6_1_49;

(* NOTE: k = 114 *)

(*   %arrayidx9.6.50 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %1736 = load i16, i16* %arrayidx9.6.50, align 2, !tbaa !3 *)
mov v1736 mem0_404;
(*   %conv1.i.6.50 = sext i16 %1736 to i32 *)
cast v_conv1_i_6_50@sint32 v1736@sint16;
(*   %mul.i.6.50 = mul nsw i32 %conv1.i.6.50, -1278 *)
mul v_mul_i_6_50 v_conv1_i_6_50 (-1278)@sint32;
(*   %call.i.6.50 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.50) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_50, v_call_i_6_50);
(*   %arrayidx11.6.50 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %1737 = load i16, i16* %arrayidx11.6.50, align 2, !tbaa !3 *)
mov v1737 mem0_400;
(*   %sub.6.50 = sub i16 %1737, %call.i.6.50 *)
sub v_sub_6_50 v1737 v_call_i_6_50;
(*   store i16 %sub.6.50, i16* %arrayidx9.6.50, align 2, !tbaa !3 *)
mov mem0_404 v_sub_6_50;
(*   %add21.6.50 = add i16 %1737, %call.i.6.50 *)
add v_add21_6_50 v1737 v_call_i_6_50;
(*   store i16 %add21.6.50, i16* %arrayidx11.6.50, align 2, !tbaa !3 *)
mov mem0_400 v_add21_6_50;
(*   %arrayidx9.6.1.50 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %1738 = load i16, i16* %arrayidx9.6.1.50, align 2, !tbaa !3 *)
mov v1738 mem0_406;
(*   %conv1.i.6.1.50 = sext i16 %1738 to i32 *)
cast v_conv1_i_6_1_50@sint32 v1738@sint16;
(*   %mul.i.6.1.50 = mul nsw i32 %conv1.i.6.1.50, -1278 *)
mul v_mul_i_6_1_50 v_conv1_i_6_1_50 (-1278)@sint32;
(*   %call.i.6.1.50 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.50) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_50, v_call_i_6_1_50);
(*   %arrayidx11.6.1.50 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %1739 = load i16, i16* %arrayidx11.6.1.50, align 2, !tbaa !3 *)
mov v1739 mem0_402;
(*   %sub.6.1.50 = sub i16 %1739, %call.i.6.1.50 *)
sub v_sub_6_1_50 v1739 v_call_i_6_1_50;
(*   store i16 %sub.6.1.50, i16* %arrayidx9.6.1.50, align 2, !tbaa !3 *)
mov mem0_406 v_sub_6_1_50;
(*   %add21.6.1.50 = add i16 %1739, %call.i.6.1.50 *)
add v_add21_6_1_50 v1739 v_call_i_6_1_50;
(*   store i16 %add21.6.1.50, i16* %arrayidx11.6.1.50, align 2, !tbaa !3 *)
mov mem0_402 v_add21_6_1_50;

(* NOTE: k = 115 *)

(*   %arrayidx9.6.51 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %1740 = load i16, i16* %arrayidx9.6.51, align 2, !tbaa !3 *)
mov v1740 mem0_412;
(*   %conv1.i.6.51 = sext i16 %1740 to i32 *)
cast v_conv1_i_6_51@sint32 v1740@sint16;
(*   %mul.i.6.51 = mul nsw i32 %conv1.i.6.51, 794 *)
mul v_mul_i_6_51 v_conv1_i_6_51 (794)@sint32;
(*   %call.i.6.51 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.51) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_51, v_call_i_6_51);
(*   %arrayidx11.6.51 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %1741 = load i16, i16* %arrayidx11.6.51, align 2, !tbaa !3 *)
mov v1741 mem0_408;
(*   %sub.6.51 = sub i16 %1741, %call.i.6.51 *)
sub v_sub_6_51 v1741 v_call_i_6_51;
(*   store i16 %sub.6.51, i16* %arrayidx9.6.51, align 2, !tbaa !3 *)
mov mem0_412 v_sub_6_51;
(*   %add21.6.51 = add i16 %1741, %call.i.6.51 *)
add v_add21_6_51 v1741 v_call_i_6_51;
(*   store i16 %add21.6.51, i16* %arrayidx11.6.51, align 2, !tbaa !3 *)
mov mem0_408 v_add21_6_51;
(*   %arrayidx9.6.1.51 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %1742 = load i16, i16* %arrayidx9.6.1.51, align 2, !tbaa !3 *)
mov v1742 mem0_414;
(*   %conv1.i.6.1.51 = sext i16 %1742 to i32 *)
cast v_conv1_i_6_1_51@sint32 v1742@sint16;
(*   %mul.i.6.1.51 = mul nsw i32 %conv1.i.6.1.51, 794 *)
mul v_mul_i_6_1_51 v_conv1_i_6_1_51 (794)@sint32;
(*   %call.i.6.1.51 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.51) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_51, v_call_i_6_1_51);
(*   %arrayidx11.6.1.51 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %1743 = load i16, i16* %arrayidx11.6.1.51, align 2, !tbaa !3 *)
mov v1743 mem0_410;
(*   %sub.6.1.51 = sub i16 %1743, %call.i.6.1.51 *)
sub v_sub_6_1_51 v1743 v_call_i_6_1_51;
(*   store i16 %sub.6.1.51, i16* %arrayidx9.6.1.51, align 2, !tbaa !3 *)
mov mem0_414 v_sub_6_1_51;
(*   %add21.6.1.51 = add i16 %1743, %call.i.6.1.51 *)
add v_add21_6_1_51 v1743 v_call_i_6_1_51;
(*   store i16 %add21.6.1.51, i16* %arrayidx11.6.1.51, align 2, !tbaa !3 *)
mov mem0_410 v_add21_6_1_51;

(* NOTE: k = 116 *)

(*   %arrayidx9.6.52 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %1744 = load i16, i16* %arrayidx9.6.52, align 2, !tbaa !3 *)
mov v1744 mem0_420;
(*   %conv1.i.6.52 = sext i16 %1744 to i32 *)
cast v_conv1_i_6_52@sint32 v1744@sint16;
(*   %mul.i.6.52 = mul nsw i32 %conv1.i.6.52, -1510 *)
mul v_mul_i_6_52 v_conv1_i_6_52 (-1510)@sint32;
(*   %call.i.6.52 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.52) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_52, v_call_i_6_52);
(*   %arrayidx11.6.52 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %1745 = load i16, i16* %arrayidx11.6.52, align 2, !tbaa !3 *)
mov v1745 mem0_416;
(*   %sub.6.52 = sub i16 %1745, %call.i.6.52 *)
sub v_sub_6_52 v1745 v_call_i_6_52;
(*   store i16 %sub.6.52, i16* %arrayidx9.6.52, align 2, !tbaa !3 *)
mov mem0_420 v_sub_6_52;
(*   %add21.6.52 = add i16 %1745, %call.i.6.52 *)
add v_add21_6_52 v1745 v_call_i_6_52;
(*   store i16 %add21.6.52, i16* %arrayidx11.6.52, align 2, !tbaa !3 *)
mov mem0_416 v_add21_6_52;
(*   %arrayidx9.6.1.52 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %1746 = load i16, i16* %arrayidx9.6.1.52, align 2, !tbaa !3 *)
mov v1746 mem0_422;
(*   %conv1.i.6.1.52 = sext i16 %1746 to i32 *)
cast v_conv1_i_6_1_52@sint32 v1746@sint16;
(*   %mul.i.6.1.52 = mul nsw i32 %conv1.i.6.1.52, -1510 *)
mul v_mul_i_6_1_52 v_conv1_i_6_1_52 (-1510)@sint32;
(*   %call.i.6.1.52 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.52) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_52, v_call_i_6_1_52);
(*   %arrayidx11.6.1.52 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %1747 = load i16, i16* %arrayidx11.6.1.52, align 2, !tbaa !3 *)
mov v1747 mem0_418;
(*   %sub.6.1.52 = sub i16 %1747, %call.i.6.1.52 *)
sub v_sub_6_1_52 v1747 v_call_i_6_1_52;
(*   store i16 %sub.6.1.52, i16* %arrayidx9.6.1.52, align 2, !tbaa !3 *)
mov mem0_422 v_sub_6_1_52;
(*   %add21.6.1.52 = add i16 %1747, %call.i.6.1.52 *)
add v_add21_6_1_52 v1747 v_call_i_6_1_52;
(*   store i16 %add21.6.1.52, i16* %arrayidx11.6.1.52, align 2, !tbaa !3 *)
mov mem0_418 v_add21_6_1_52;

(* NOTE: k = 117 *)

(*   %arrayidx9.6.53 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %1748 = load i16, i16* %arrayidx9.6.53, align 2, !tbaa !3 *)
mov v1748 mem0_428;
(*   %conv1.i.6.53 = sext i16 %1748 to i32 *)
cast v_conv1_i_6_53@sint32 v1748@sint16;
(*   %mul.i.6.53 = mul nsw i32 %conv1.i.6.53, -854 *)
mul v_mul_i_6_53 v_conv1_i_6_53 (-854)@sint32;
(*   %call.i.6.53 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.53) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_53, v_call_i_6_53);
(*   %arrayidx11.6.53 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %1749 = load i16, i16* %arrayidx11.6.53, align 2, !tbaa !3 *)
mov v1749 mem0_424;
(*   %sub.6.53 = sub i16 %1749, %call.i.6.53 *)
sub v_sub_6_53 v1749 v_call_i_6_53;
(*   store i16 %sub.6.53, i16* %arrayidx9.6.53, align 2, !tbaa !3 *)
mov mem0_428 v_sub_6_53;
(*   %add21.6.53 = add i16 %1749, %call.i.6.53 *)
add v_add21_6_53 v1749 v_call_i_6_53;
(*   store i16 %add21.6.53, i16* %arrayidx11.6.53, align 2, !tbaa !3 *)
mov mem0_424 v_add21_6_53;
(*   %arrayidx9.6.1.53 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %1750 = load i16, i16* %arrayidx9.6.1.53, align 2, !tbaa !3 *)
mov v1750 mem0_430;
(*   %conv1.i.6.1.53 = sext i16 %1750 to i32 *)
cast v_conv1_i_6_1_53@sint32 v1750@sint16;
(*   %mul.i.6.1.53 = mul nsw i32 %conv1.i.6.1.53, -854 *)
mul v_mul_i_6_1_53 v_conv1_i_6_1_53 (-854)@sint32;
(*   %call.i.6.1.53 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.53) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_53, v_call_i_6_1_53);
(*   %arrayidx11.6.1.53 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %1751 = load i16, i16* %arrayidx11.6.1.53, align 2, !tbaa !3 *)
mov v1751 mem0_426;
(*   %sub.6.1.53 = sub i16 %1751, %call.i.6.1.53 *)
sub v_sub_6_1_53 v1751 v_call_i_6_1_53;
(*   store i16 %sub.6.1.53, i16* %arrayidx9.6.1.53, align 2, !tbaa !3 *)
mov mem0_430 v_sub_6_1_53;
(*   %add21.6.1.53 = add i16 %1751, %call.i.6.1.53 *)
add v_add21_6_1_53 v1751 v_call_i_6_1_53;
(*   store i16 %add21.6.1.53, i16* %arrayidx11.6.1.53, align 2, !tbaa !3 *)
mov mem0_426 v_add21_6_1_53;

(* NOTE: k = 118 *)

(*   %arrayidx9.6.54 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %1752 = load i16, i16* %arrayidx9.6.54, align 2, !tbaa !3 *)
mov v1752 mem0_436;
(*   %conv1.i.6.54 = sext i16 %1752 to i32 *)
cast v_conv1_i_6_54@sint32 v1752@sint16;
(*   %mul.i.6.54 = mul nsw i32 %conv1.i.6.54, -870 *)
mul v_mul_i_6_54 v_conv1_i_6_54 (-870)@sint32;
(*   %call.i.6.54 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.54) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_54, v_call_i_6_54);
(*   %arrayidx11.6.54 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %1753 = load i16, i16* %arrayidx11.6.54, align 2, !tbaa !3 *)
mov v1753 mem0_432;
(*   %sub.6.54 = sub i16 %1753, %call.i.6.54 *)
sub v_sub_6_54 v1753 v_call_i_6_54;
(*   store i16 %sub.6.54, i16* %arrayidx9.6.54, align 2, !tbaa !3 *)
mov mem0_436 v_sub_6_54;
(*   %add21.6.54 = add i16 %1753, %call.i.6.54 *)
add v_add21_6_54 v1753 v_call_i_6_54;
(*   store i16 %add21.6.54, i16* %arrayidx11.6.54, align 2, !tbaa !3 *)
mov mem0_432 v_add21_6_54;
(*   %arrayidx9.6.1.54 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %1754 = load i16, i16* %arrayidx9.6.1.54, align 2, !tbaa !3 *)
mov v1754 mem0_438;
(*   %conv1.i.6.1.54 = sext i16 %1754 to i32 *)
cast v_conv1_i_6_1_54@sint32 v1754@sint16;
(*   %mul.i.6.1.54 = mul nsw i32 %conv1.i.6.1.54, -870 *)
mul v_mul_i_6_1_54 v_conv1_i_6_1_54 (-870)@sint32;
(*   %call.i.6.1.54 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.54) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_54, v_call_i_6_1_54);
(*   %arrayidx11.6.1.54 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %1755 = load i16, i16* %arrayidx11.6.1.54, align 2, !tbaa !3 *)
mov v1755 mem0_434;
(*   %sub.6.1.54 = sub i16 %1755, %call.i.6.1.54 *)
sub v_sub_6_1_54 v1755 v_call_i_6_1_54;
(*   store i16 %sub.6.1.54, i16* %arrayidx9.6.1.54, align 2, !tbaa !3 *)
mov mem0_438 v_sub_6_1_54;
(*   %add21.6.1.54 = add i16 %1755, %call.i.6.1.54 *)
add v_add21_6_1_54 v1755 v_call_i_6_1_54;
(*   store i16 %add21.6.1.54, i16* %arrayidx11.6.1.54, align 2, !tbaa !3 *)
mov mem0_434 v_add21_6_1_54;

(* NOTE: k = 119 *)

(*   %arrayidx9.6.55 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %1756 = load i16, i16* %arrayidx9.6.55, align 2, !tbaa !3 *)
mov v1756 mem0_444;
(*   %conv1.i.6.55 = sext i16 %1756 to i32 *)
cast v_conv1_i_6_55@sint32 v1756@sint16;
(*   %mul.i.6.55 = mul nsw i32 %conv1.i.6.55, 478 *)
mul v_mul_i_6_55 v_conv1_i_6_55 (478)@sint32;
(*   %call.i.6.55 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.55) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_55, v_call_i_6_55);
(*   %arrayidx11.6.55 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %1757 = load i16, i16* %arrayidx11.6.55, align 2, !tbaa !3 *)
mov v1757 mem0_440;
(*   %sub.6.55 = sub i16 %1757, %call.i.6.55 *)
sub v_sub_6_55 v1757 v_call_i_6_55;
(*   store i16 %sub.6.55, i16* %arrayidx9.6.55, align 2, !tbaa !3 *)
mov mem0_444 v_sub_6_55;
(*   %add21.6.55 = add i16 %1757, %call.i.6.55 *)
add v_add21_6_55 v1757 v_call_i_6_55;
(*   store i16 %add21.6.55, i16* %arrayidx11.6.55, align 2, !tbaa !3 *)
mov mem0_440 v_add21_6_55;
(*   %arrayidx9.6.1.55 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %1758 = load i16, i16* %arrayidx9.6.1.55, align 2, !tbaa !3 *)
mov v1758 mem0_446;
(*   %conv1.i.6.1.55 = sext i16 %1758 to i32 *)
cast v_conv1_i_6_1_55@sint32 v1758@sint16;
(*   %mul.i.6.1.55 = mul nsw i32 %conv1.i.6.1.55, 478 *)
mul v_mul_i_6_1_55 v_conv1_i_6_1_55 (478)@sint32;
(*   %call.i.6.1.55 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.55) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_55, v_call_i_6_1_55);
(*   %arrayidx11.6.1.55 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %1759 = load i16, i16* %arrayidx11.6.1.55, align 2, !tbaa !3 *)
mov v1759 mem0_442;
(*   %sub.6.1.55 = sub i16 %1759, %call.i.6.1.55 *)
sub v_sub_6_1_55 v1759 v_call_i_6_1_55;
(*   store i16 %sub.6.1.55, i16* %arrayidx9.6.1.55, align 2, !tbaa !3 *)
mov mem0_446 v_sub_6_1_55;
(*   %add21.6.1.55 = add i16 %1759, %call.i.6.1.55 *)
add v_add21_6_1_55 v1759 v_call_i_6_1_55;
(*   store i16 %add21.6.1.55, i16* %arrayidx11.6.1.55, align 2, !tbaa !3 *)
mov mem0_442 v_add21_6_1_55;

(* NOTE: k = 120 *)

(*   %arrayidx9.6.56 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %1760 = load i16, i16* %arrayidx9.6.56, align 2, !tbaa !3 *)
mov v1760 mem0_452;
(*   %conv1.i.6.56 = sext i16 %1760 to i32 *)
cast v_conv1_i_6_56@sint32 v1760@sint16;
(*   %mul.i.6.56 = mul nsw i32 %conv1.i.6.56, -108 *)
mul v_mul_i_6_56 v_conv1_i_6_56 (-108)@sint32;
(*   %call.i.6.56 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.56) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_56, v_call_i_6_56);
(*   %arrayidx11.6.56 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %1761 = load i16, i16* %arrayidx11.6.56, align 2, !tbaa !3 *)
mov v1761 mem0_448;
(*   %sub.6.56 = sub i16 %1761, %call.i.6.56 *)
sub v_sub_6_56 v1761 v_call_i_6_56;
(*   store i16 %sub.6.56, i16* %arrayidx9.6.56, align 2, !tbaa !3 *)
mov mem0_452 v_sub_6_56;
(*   %add21.6.56 = add i16 %1761, %call.i.6.56 *)
add v_add21_6_56 v1761 v_call_i_6_56;
(*   store i16 %add21.6.56, i16* %arrayidx11.6.56, align 2, !tbaa !3 *)
mov mem0_448 v_add21_6_56;
(*   %arrayidx9.6.1.56 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %1762 = load i16, i16* %arrayidx9.6.1.56, align 2, !tbaa !3 *)
mov v1762 mem0_454;
(*   %conv1.i.6.1.56 = sext i16 %1762 to i32 *)
cast v_conv1_i_6_1_56@sint32 v1762@sint16;
(*   %mul.i.6.1.56 = mul nsw i32 %conv1.i.6.1.56, -108 *)
mul v_mul_i_6_1_56 v_conv1_i_6_1_56 (-108)@sint32;
(*   %call.i.6.1.56 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.56) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_56, v_call_i_6_1_56);
(*   %arrayidx11.6.1.56 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %1763 = load i16, i16* %arrayidx11.6.1.56, align 2, !tbaa !3 *)
mov v1763 mem0_450;
(*   %sub.6.1.56 = sub i16 %1763, %call.i.6.1.56 *)
sub v_sub_6_1_56 v1763 v_call_i_6_1_56;
(*   store i16 %sub.6.1.56, i16* %arrayidx9.6.1.56, align 2, !tbaa !3 *)
mov mem0_454 v_sub_6_1_56;
(*   %add21.6.1.56 = add i16 %1763, %call.i.6.1.56 *)
add v_add21_6_1_56 v1763 v_call_i_6_1_56;
(*   store i16 %add21.6.1.56, i16* %arrayidx11.6.1.56, align 2, !tbaa !3 *)
mov mem0_450 v_add21_6_1_56;

(* NOTE: k = 121 *)

(*   %arrayidx9.6.57 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %1764 = load i16, i16* %arrayidx9.6.57, align 2, !tbaa !3 *)
mov v1764 mem0_460;
(*   %conv1.i.6.57 = sext i16 %1764 to i32 *)
cast v_conv1_i_6_57@sint32 v1764@sint16;
(*   %mul.i.6.57 = mul nsw i32 %conv1.i.6.57, -308 *)
mul v_mul_i_6_57 v_conv1_i_6_57 (-308)@sint32;
(*   %call.i.6.57 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.57) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_57, v_call_i_6_57);
(*   %arrayidx11.6.57 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %1765 = load i16, i16* %arrayidx11.6.57, align 2, !tbaa !3 *)
mov v1765 mem0_456;
(*   %sub.6.57 = sub i16 %1765, %call.i.6.57 *)
sub v_sub_6_57 v1765 v_call_i_6_57;
(*   store i16 %sub.6.57, i16* %arrayidx9.6.57, align 2, !tbaa !3 *)
mov mem0_460 v_sub_6_57;
(*   %add21.6.57 = add i16 %1765, %call.i.6.57 *)
add v_add21_6_57 v1765 v_call_i_6_57;
(*   store i16 %add21.6.57, i16* %arrayidx11.6.57, align 2, !tbaa !3 *)
mov mem0_456 v_add21_6_57;
(*   %arrayidx9.6.1.57 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %1766 = load i16, i16* %arrayidx9.6.1.57, align 2, !tbaa !3 *)
mov v1766 mem0_462;
(*   %conv1.i.6.1.57 = sext i16 %1766 to i32 *)
cast v_conv1_i_6_1_57@sint32 v1766@sint16;
(*   %mul.i.6.1.57 = mul nsw i32 %conv1.i.6.1.57, -308 *)
mul v_mul_i_6_1_57 v_conv1_i_6_1_57 (-308)@sint32;
(*   %call.i.6.1.57 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.57) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_57, v_call_i_6_1_57);
(*   %arrayidx11.6.1.57 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %1767 = load i16, i16* %arrayidx11.6.1.57, align 2, !tbaa !3 *)
mov v1767 mem0_458;
(*   %sub.6.1.57 = sub i16 %1767, %call.i.6.1.57 *)
sub v_sub_6_1_57 v1767 v_call_i_6_1_57;
(*   store i16 %sub.6.1.57, i16* %arrayidx9.6.1.57, align 2, !tbaa !3 *)
mov mem0_462 v_sub_6_1_57;
(*   %add21.6.1.57 = add i16 %1767, %call.i.6.1.57 *)
add v_add21_6_1_57 v1767 v_call_i_6_1_57;
(*   store i16 %add21.6.1.57, i16* %arrayidx11.6.1.57, align 2, !tbaa !3 *)
mov mem0_458 v_add21_6_1_57;

(* NOTE: k = 122 *)

(*   %arrayidx9.6.58 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %1768 = load i16, i16* %arrayidx9.6.58, align 2, !tbaa !3 *)
mov v1768 mem0_468;
(*   %conv1.i.6.58 = sext i16 %1768 to i32 *)
cast v_conv1_i_6_58@sint32 v1768@sint16;
(*   %mul.i.6.58 = mul nsw i32 %conv1.i.6.58, 996 *)
mul v_mul_i_6_58 v_conv1_i_6_58 (996)@sint32;
(*   %call.i.6.58 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.58) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_58, v_call_i_6_58);
(*   %arrayidx11.6.58 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %1769 = load i16, i16* %arrayidx11.6.58, align 2, !tbaa !3 *)
mov v1769 mem0_464;
(*   %sub.6.58 = sub i16 %1769, %call.i.6.58 *)
sub v_sub_6_58 v1769 v_call_i_6_58;
(*   store i16 %sub.6.58, i16* %arrayidx9.6.58, align 2, !tbaa !3 *)
mov mem0_468 v_sub_6_58;
(*   %add21.6.58 = add i16 %1769, %call.i.6.58 *)
add v_add21_6_58 v1769 v_call_i_6_58;
(*   store i16 %add21.6.58, i16* %arrayidx11.6.58, align 2, !tbaa !3 *)
mov mem0_464 v_add21_6_58;
(*   %arrayidx9.6.1.58 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %1770 = load i16, i16* %arrayidx9.6.1.58, align 2, !tbaa !3 *)
mov v1770 mem0_470;
(*   %conv1.i.6.1.58 = sext i16 %1770 to i32 *)
cast v_conv1_i_6_1_58@sint32 v1770@sint16;
(*   %mul.i.6.1.58 = mul nsw i32 %conv1.i.6.1.58, 996 *)
mul v_mul_i_6_1_58 v_conv1_i_6_1_58 (996)@sint32;
(*   %call.i.6.1.58 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.58) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_58, v_call_i_6_1_58);
(*   %arrayidx11.6.1.58 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %1771 = load i16, i16* %arrayidx11.6.1.58, align 2, !tbaa !3 *)
mov v1771 mem0_466;
(*   %sub.6.1.58 = sub i16 %1771, %call.i.6.1.58 *)
sub v_sub_6_1_58 v1771 v_call_i_6_1_58;
(*   store i16 %sub.6.1.58, i16* %arrayidx9.6.1.58, align 2, !tbaa !3 *)
mov mem0_470 v_sub_6_1_58;
(*   %add21.6.1.58 = add i16 %1771, %call.i.6.1.58 *)
add v_add21_6_1_58 v1771 v_call_i_6_1_58;
(*   store i16 %add21.6.1.58, i16* %arrayidx11.6.1.58, align 2, !tbaa !3 *)
mov mem0_466 v_add21_6_1_58;

(* NOTE: k = 123 *)

(*   %arrayidx9.6.59 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %1772 = load i16, i16* %arrayidx9.6.59, align 2, !tbaa !3 *)
mov v1772 mem0_476;
(*   %conv1.i.6.59 = sext i16 %1772 to i32 *)
cast v_conv1_i_6_59@sint32 v1772@sint16;
(*   %mul.i.6.59 = mul nsw i32 %conv1.i.6.59, 991 *)
mul v_mul_i_6_59 v_conv1_i_6_59 (991)@sint32;
(*   %call.i.6.59 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.59) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_59, v_call_i_6_59);
(*   %arrayidx11.6.59 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %1773 = load i16, i16* %arrayidx11.6.59, align 2, !tbaa !3 *)
mov v1773 mem0_472;
(*   %sub.6.59 = sub i16 %1773, %call.i.6.59 *)
sub v_sub_6_59 v1773 v_call_i_6_59;
(*   store i16 %sub.6.59, i16* %arrayidx9.6.59, align 2, !tbaa !3 *)
mov mem0_476 v_sub_6_59;
(*   %add21.6.59 = add i16 %1773, %call.i.6.59 *)
add v_add21_6_59 v1773 v_call_i_6_59;
(*   store i16 %add21.6.59, i16* %arrayidx11.6.59, align 2, !tbaa !3 *)
mov mem0_472 v_add21_6_59;
(*   %arrayidx9.6.1.59 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %1774 = load i16, i16* %arrayidx9.6.1.59, align 2, !tbaa !3 *)
mov v1774 mem0_478;
(*   %conv1.i.6.1.59 = sext i16 %1774 to i32 *)
cast v_conv1_i_6_1_59@sint32 v1774@sint16;
(*   %mul.i.6.1.59 = mul nsw i32 %conv1.i.6.1.59, 991 *)
mul v_mul_i_6_1_59 v_conv1_i_6_1_59 (991)@sint32;
(*   %call.i.6.1.59 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.59) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_59, v_call_i_6_1_59);
(*   %arrayidx11.6.1.59 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %1775 = load i16, i16* %arrayidx11.6.1.59, align 2, !tbaa !3 *)
mov v1775 mem0_474;
(*   %sub.6.1.59 = sub i16 %1775, %call.i.6.1.59 *)
sub v_sub_6_1_59 v1775 v_call_i_6_1_59;
(*   store i16 %sub.6.1.59, i16* %arrayidx9.6.1.59, align 2, !tbaa !3 *)
mov mem0_478 v_sub_6_1_59;
(*   %add21.6.1.59 = add i16 %1775, %call.i.6.1.59 *)
add v_add21_6_1_59 v1775 v_call_i_6_1_59;
(*   store i16 %add21.6.1.59, i16* %arrayidx11.6.1.59, align 2, !tbaa !3 *)
mov mem0_474 v_add21_6_1_59;

(* NOTE: k = 124 *)

(*   %arrayidx9.6.60 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %1776 = load i16, i16* %arrayidx9.6.60, align 2, !tbaa !3 *)
mov v1776 mem0_484;
(*   %conv1.i.6.60 = sext i16 %1776 to i32 *)
cast v_conv1_i_6_60@sint32 v1776@sint16;
(*   %mul.i.6.60 = mul nsw i32 %conv1.i.6.60, 958 *)
mul v_mul_i_6_60 v_conv1_i_6_60 (958)@sint32;
(*   %call.i.6.60 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.60) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_60, v_call_i_6_60);
(*   %arrayidx11.6.60 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %1777 = load i16, i16* %arrayidx11.6.60, align 2, !tbaa !3 *)
mov v1777 mem0_480;
(*   %sub.6.60 = sub i16 %1777, %call.i.6.60 *)
sub v_sub_6_60 v1777 v_call_i_6_60;
(*   store i16 %sub.6.60, i16* %arrayidx9.6.60, align 2, !tbaa !3 *)
mov mem0_484 v_sub_6_60;
(*   %add21.6.60 = add i16 %1777, %call.i.6.60 *)
add v_add21_6_60 v1777 v_call_i_6_60;
(*   store i16 %add21.6.60, i16* %arrayidx11.6.60, align 2, !tbaa !3 *)
mov mem0_480 v_add21_6_60;
(*   %arrayidx9.6.1.60 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %1778 = load i16, i16* %arrayidx9.6.1.60, align 2, !tbaa !3 *)
mov v1778 mem0_486;
(*   %conv1.i.6.1.60 = sext i16 %1778 to i32 *)
cast v_conv1_i_6_1_60@sint32 v1778@sint16;
(*   %mul.i.6.1.60 = mul nsw i32 %conv1.i.6.1.60, 958 *)
mul v_mul_i_6_1_60 v_conv1_i_6_1_60 (958)@sint32;
(*   %call.i.6.1.60 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.60) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_60, v_call_i_6_1_60);
(*   %arrayidx11.6.1.60 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %1779 = load i16, i16* %arrayidx11.6.1.60, align 2, !tbaa !3 *)
mov v1779 mem0_482;
(*   %sub.6.1.60 = sub i16 %1779, %call.i.6.1.60 *)
sub v_sub_6_1_60 v1779 v_call_i_6_1_60;
(*   store i16 %sub.6.1.60, i16* %arrayidx9.6.1.60, align 2, !tbaa !3 *)
mov mem0_486 v_sub_6_1_60;
(*   %add21.6.1.60 = add i16 %1779, %call.i.6.1.60 *)
add v_add21_6_1_60 v1779 v_call_i_6_1_60;
(*   store i16 %add21.6.1.60, i16* %arrayidx11.6.1.60, align 2, !tbaa !3 *)
mov mem0_482 v_add21_6_1_60;

(* NOTE: k = 125 *)

(*   %arrayidx9.6.61 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %1780 = load i16, i16* %arrayidx9.6.61, align 2, !tbaa !3 *)
mov v1780 mem0_492;
(*   %conv1.i.6.61 = sext i16 %1780 to i32 *)
cast v_conv1_i_6_61@sint32 v1780@sint16;
(*   %mul.i.6.61 = mul nsw i32 %conv1.i.6.61, -1460 *)
mul v_mul_i_6_61 v_conv1_i_6_61 (-1460)@sint32;
(*   %call.i.6.61 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.61) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_61, v_call_i_6_61);
(*   %arrayidx11.6.61 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %1781 = load i16, i16* %arrayidx11.6.61, align 2, !tbaa !3 *)
mov v1781 mem0_488;
(*   %sub.6.61 = sub i16 %1781, %call.i.6.61 *)
sub v_sub_6_61 v1781 v_call_i_6_61;
(*   store i16 %sub.6.61, i16* %arrayidx9.6.61, align 2, !tbaa !3 *)
mov mem0_492 v_sub_6_61;
(*   %add21.6.61 = add i16 %1781, %call.i.6.61 *)
add v_add21_6_61 v1781 v_call_i_6_61;
(*   store i16 %add21.6.61, i16* %arrayidx11.6.61, align 2, !tbaa !3 *)
mov mem0_488 v_add21_6_61;
(*   %arrayidx9.6.1.61 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %1782 = load i16, i16* %arrayidx9.6.1.61, align 2, !tbaa !3 *)
mov v1782 mem0_494;
(*   %conv1.i.6.1.61 = sext i16 %1782 to i32 *)
cast v_conv1_i_6_1_61@sint32 v1782@sint16;
(*   %mul.i.6.1.61 = mul nsw i32 %conv1.i.6.1.61, -1460 *)
mul v_mul_i_6_1_61 v_conv1_i_6_1_61 (-1460)@sint32;
(*   %call.i.6.1.61 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.61) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_61, v_call_i_6_1_61);
(*   %arrayidx11.6.1.61 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %1783 = load i16, i16* %arrayidx11.6.1.61, align 2, !tbaa !3 *)
mov v1783 mem0_490;
(*   %sub.6.1.61 = sub i16 %1783, %call.i.6.1.61 *)
sub v_sub_6_1_61 v1783 v_call_i_6_1_61;
(*   store i16 %sub.6.1.61, i16* %arrayidx9.6.1.61, align 2, !tbaa !3 *)
mov mem0_494 v_sub_6_1_61;
(*   %add21.6.1.61 = add i16 %1783, %call.i.6.1.61 *)
add v_add21_6_1_61 v1783 v_call_i_6_1_61;
(*   store i16 %add21.6.1.61, i16* %arrayidx11.6.1.61, align 2, !tbaa !3 *)
mov mem0_490 v_add21_6_1_61;

(* NOTE: k = 126 *)

(*   %arrayidx9.6.62 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %1784 = load i16, i16* %arrayidx9.6.62, align 2, !tbaa !3 *)
mov v1784 mem0_500;
(*   %conv1.i.6.62 = sext i16 %1784 to i32 *)
cast v_conv1_i_6_62@sint32 v1784@sint16;
(*   %mul.i.6.62 = mul nsw i32 %conv1.i.6.62, 1522 *)
mul v_mul_i_6_62 v_conv1_i_6_62 (1522)@sint32;
(*   %call.i.6.62 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.62) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_62, v_call_i_6_62);
(*   %arrayidx11.6.62 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %1785 = load i16, i16* %arrayidx11.6.62, align 2, !tbaa !3 *)
mov v1785 mem0_496;
(*   %sub.6.62 = sub i16 %1785, %call.i.6.62 *)
sub v_sub_6_62 v1785 v_call_i_6_62;
(*   store i16 %sub.6.62, i16* %arrayidx9.6.62, align 2, !tbaa !3 *)
mov mem0_500 v_sub_6_62;
(*   %add21.6.62 = add i16 %1785, %call.i.6.62 *)
add v_add21_6_62 v1785 v_call_i_6_62;
(*   store i16 %add21.6.62, i16* %arrayidx11.6.62, align 2, !tbaa !3 *)
mov mem0_496 v_add21_6_62;
(*   %arrayidx9.6.1.62 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %1786 = load i16, i16* %arrayidx9.6.1.62, align 2, !tbaa !3 *)
mov v1786 mem0_502;
(*   %conv1.i.6.1.62 = sext i16 %1786 to i32 *)
cast v_conv1_i_6_1_62@sint32 v1786@sint16;
(*   %mul.i.6.1.62 = mul nsw i32 %conv1.i.6.1.62, 1522 *)
mul v_mul_i_6_1_62 v_conv1_i_6_1_62 (1522)@sint32;
(*   %call.i.6.1.62 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.62) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_62, v_call_i_6_1_62);
(*   %arrayidx11.6.1.62 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %1787 = load i16, i16* %arrayidx11.6.1.62, align 2, !tbaa !3 *)
mov v1787 mem0_498;
(*   %sub.6.1.62 = sub i16 %1787, %call.i.6.1.62 *)
sub v_sub_6_1_62 v1787 v_call_i_6_1_62;
(*   store i16 %sub.6.1.62, i16* %arrayidx9.6.1.62, align 2, !tbaa !3 *)
mov mem0_502 v_sub_6_1_62;
(*   %add21.6.1.62 = add i16 %1787, %call.i.6.1.62 *)
add v_add21_6_1_62 v1787 v_call_i_6_1_62;
(*   store i16 %add21.6.1.62, i16* %arrayidx11.6.1.62, align 2, !tbaa !3 *)
mov mem0_498 v_add21_6_1_62;

(* NOTE: k = 127 *)

(*   %arrayidx9.6.63 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %1788 = load i16, i16* %arrayidx9.6.63, align 2, !tbaa !3 *)
mov v1788 mem0_508;
(*   %conv1.i.6.63 = sext i16 %1788 to i32 *)
cast v_conv1_i_6_63@sint32 v1788@sint16;
(*   %mul.i.6.63 = mul nsw i32 %conv1.i.6.63, 1628 *)
mul v_mul_i_6_63 v_conv1_i_6_63 (1628)@sint32;
(*   %call.i.6.63 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.63) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_63, v_call_i_6_63);
(*   %arrayidx11.6.63 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %1789 = load i16, i16* %arrayidx11.6.63, align 2, !tbaa !3 *)
mov v1789 mem0_504;
(*   %sub.6.63 = sub i16 %1789, %call.i.6.63 *)
sub v_sub_6_63 v1789 v_call_i_6_63;
(*   store i16 %sub.6.63, i16* %arrayidx9.6.63, align 2, !tbaa !3 *)
mov mem0_508 v_sub_6_63;
(*   %add21.6.63 = add i16 %1789, %call.i.6.63 *)
add v_add21_6_63 v1789 v_call_i_6_63;
(*   store i16 %add21.6.63, i16* %arrayidx11.6.63, align 2, !tbaa !3 *)
mov mem0_504 v_add21_6_63;
(*   %arrayidx9.6.1.63 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %1790 = load i16, i16* %arrayidx9.6.1.63, align 2, !tbaa !3 *)
mov v1790 mem0_510;
(*   %conv1.i.6.1.63 = sext i16 %1790 to i32 *)
cast v_conv1_i_6_1_63@sint32 v1790@sint16;
(*   %mul.i.6.1.63 = mul nsw i32 %conv1.i.6.1.63, 1628 *)
mul v_mul_i_6_1_63 v_conv1_i_6_1_63 (1628)@sint32;
(*   %call.i.6.1.63 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.6.1.63) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_6_1_63, v_call_i_6_1_63);
(*   %arrayidx11.6.1.63 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %1791 = load i16, i16* %arrayidx11.6.1.63, align 2, !tbaa !3 *)
mov v1791 mem0_506;
(*   %sub.6.1.63 = sub i16 %1791, %call.i.6.1.63 *)
sub v_sub_6_1_63 v1791 v_call_i_6_1_63;
(*   store i16 %sub.6.1.63, i16* %arrayidx9.6.1.63, align 2, !tbaa !3 *)
mov mem0_510 v_sub_6_1_63;
(*   %add21.6.1.63 = add i16 %1791, %call.i.6.1.63 *)
add v_add21_6_1_63 v1791 v_call_i_6_1_63;
(*   store i16 %add21.6.1.63, i16* %arrayidx11.6.1.63, align 2, !tbaa !3 *)
mov mem0_506 v_add21_6_1_63;
(*   ret void *)


(* outputs *)



mov r_0 mem0_0@sint16; mov r_2 mem0_2@sint16;
mov r_4 mem0_4@sint16; mov r_6 mem0_6@sint16;
mov r_8 mem0_8@sint16; mov r_10 mem0_10@sint16;
mov r_12 mem0_12@sint16; mov r_14 mem0_14@sint16;
mov r_16 mem0_16@sint16; mov r_18 mem0_18@sint16;
mov r_20 mem0_20@sint16; mov r_22 mem0_22@sint16;
mov r_24 mem0_24@sint16; mov r_26 mem0_26@sint16;
mov r_28 mem0_28@sint16; mov r_30 mem0_30@sint16;
mov r_32 mem0_32@sint16; mov r_34 mem0_34@sint16;
mov r_36 mem0_36@sint16; mov r_38 mem0_38@sint16;
mov r_40 mem0_40@sint16; mov r_42 mem0_42@sint16;
mov r_44 mem0_44@sint16; mov r_46 mem0_46@sint16;
mov r_48 mem0_48@sint16; mov r_50 mem0_50@sint16;
mov r_52 mem0_52@sint16; mov r_54 mem0_54@sint16;
mov r_56 mem0_56@sint16; mov r_58 mem0_58@sint16;
mov r_60 mem0_60@sint16; mov r_62 mem0_62@sint16;
mov r_64 mem0_64@sint16; mov r_66 mem0_66@sint16;
mov r_68 mem0_68@sint16; mov r_70 mem0_70@sint16;
mov r_72 mem0_72@sint16; mov r_74 mem0_74@sint16;
mov r_76 mem0_76@sint16; mov r_78 mem0_78@sint16;
mov r_80 mem0_80@sint16; mov r_82 mem0_82@sint16;
mov r_84 mem0_84@sint16; mov r_86 mem0_86@sint16;
mov r_88 mem0_88@sint16; mov r_90 mem0_90@sint16;
mov r_92 mem0_92@sint16; mov r_94 mem0_94@sint16;
mov r_96 mem0_96@sint16; mov r_98 mem0_98@sint16;
mov r_100 mem0_100@sint16; mov r_102 mem0_102@sint16;
mov r_104 mem0_104@sint16; mov r_106 mem0_106@sint16;
mov r_108 mem0_108@sint16; mov r_110 mem0_110@sint16;
mov r_112 mem0_112@sint16; mov r_114 mem0_114@sint16;
mov r_116 mem0_116@sint16; mov r_118 mem0_118@sint16;
mov r_120 mem0_120@sint16; mov r_122 mem0_122@sint16;
mov r_124 mem0_124@sint16; mov r_126 mem0_126@sint16;
mov r_128 mem0_128@sint16; mov r_130 mem0_130@sint16;
mov r_132 mem0_132@sint16; mov r_134 mem0_134@sint16;
mov r_136 mem0_136@sint16; mov r_138 mem0_138@sint16;
mov r_140 mem0_140@sint16; mov r_142 mem0_142@sint16;
mov r_144 mem0_144@sint16; mov r_146 mem0_146@sint16;
mov r_148 mem0_148@sint16; mov r_150 mem0_150@sint16;
mov r_152 mem0_152@sint16; mov r_154 mem0_154@sint16;
mov r_156 mem0_156@sint16; mov r_158 mem0_158@sint16;
mov r_160 mem0_160@sint16; mov r_162 mem0_162@sint16;
mov r_164 mem0_164@sint16; mov r_166 mem0_166@sint16;
mov r_168 mem0_168@sint16; mov r_170 mem0_170@sint16;
mov r_172 mem0_172@sint16; mov r_174 mem0_174@sint16;
mov r_176 mem0_176@sint16; mov r_178 mem0_178@sint16;
mov r_180 mem0_180@sint16; mov r_182 mem0_182@sint16;
mov r_184 mem0_184@sint16; mov r_186 mem0_186@sint16;
mov r_188 mem0_188@sint16; mov r_190 mem0_190@sint16;
mov r_192 mem0_192@sint16; mov r_194 mem0_194@sint16;
mov r_196 mem0_196@sint16; mov r_198 mem0_198@sint16;
mov r_200 mem0_200@sint16; mov r_202 mem0_202@sint16;
mov r_204 mem0_204@sint16; mov r_206 mem0_206@sint16;
mov r_208 mem0_208@sint16; mov r_210 mem0_210@sint16;
mov r_212 mem0_212@sint16; mov r_214 mem0_214@sint16;
mov r_216 mem0_216@sint16; mov r_218 mem0_218@sint16;
mov r_220 mem0_220@sint16; mov r_222 mem0_222@sint16;
mov r_224 mem0_224@sint16; mov r_226 mem0_226@sint16;
mov r_228 mem0_228@sint16; mov r_230 mem0_230@sint16;
mov r_232 mem0_232@sint16; mov r_234 mem0_234@sint16;
mov r_236 mem0_236@sint16; mov r_238 mem0_238@sint16;
mov r_240 mem0_240@sint16; mov r_242 mem0_242@sint16;
mov r_244 mem0_244@sint16; mov r_246 mem0_246@sint16;
mov r_248 mem0_248@sint16; mov r_250 mem0_250@sint16;
mov r_252 mem0_252@sint16; mov r_254 mem0_254@sint16;
mov r_256 mem0_256@sint16; mov r_258 mem0_258@sint16;
mov r_260 mem0_260@sint16; mov r_262 mem0_262@sint16;
mov r_264 mem0_264@sint16; mov r_266 mem0_266@sint16;
mov r_268 mem0_268@sint16; mov r_270 mem0_270@sint16;
mov r_272 mem0_272@sint16; mov r_274 mem0_274@sint16;
mov r_276 mem0_276@sint16; mov r_278 mem0_278@sint16;
mov r_280 mem0_280@sint16; mov r_282 mem0_282@sint16;
mov r_284 mem0_284@sint16; mov r_286 mem0_286@sint16;
mov r_288 mem0_288@sint16; mov r_290 mem0_290@sint16;
mov r_292 mem0_292@sint16; mov r_294 mem0_294@sint16;
mov r_296 mem0_296@sint16; mov r_298 mem0_298@sint16;
mov r_300 mem0_300@sint16; mov r_302 mem0_302@sint16;
mov r_304 mem0_304@sint16; mov r_306 mem0_306@sint16;
mov r_308 mem0_308@sint16; mov r_310 mem0_310@sint16;
mov r_312 mem0_312@sint16; mov r_314 mem0_314@sint16;
mov r_316 mem0_316@sint16; mov r_318 mem0_318@sint16;
mov r_320 mem0_320@sint16; mov r_322 mem0_322@sint16;
mov r_324 mem0_324@sint16; mov r_326 mem0_326@sint16;
mov r_328 mem0_328@sint16; mov r_330 mem0_330@sint16;
mov r_332 mem0_332@sint16; mov r_334 mem0_334@sint16;
mov r_336 mem0_336@sint16; mov r_338 mem0_338@sint16;
mov r_340 mem0_340@sint16; mov r_342 mem0_342@sint16;
mov r_344 mem0_344@sint16; mov r_346 mem0_346@sint16;
mov r_348 mem0_348@sint16; mov r_350 mem0_350@sint16;
mov r_352 mem0_352@sint16; mov r_354 mem0_354@sint16;
mov r_356 mem0_356@sint16; mov r_358 mem0_358@sint16;
mov r_360 mem0_360@sint16; mov r_362 mem0_362@sint16;
mov r_364 mem0_364@sint16; mov r_366 mem0_366@sint16;
mov r_368 mem0_368@sint16; mov r_370 mem0_370@sint16;
mov r_372 mem0_372@sint16; mov r_374 mem0_374@sint16;
mov r_376 mem0_376@sint16; mov r_378 mem0_378@sint16;
mov r_380 mem0_380@sint16; mov r_382 mem0_382@sint16;
mov r_384 mem0_384@sint16; mov r_386 mem0_386@sint16;
mov r_388 mem0_388@sint16; mov r_390 mem0_390@sint16;
mov r_392 mem0_392@sint16; mov r_394 mem0_394@sint16;
mov r_396 mem0_396@sint16; mov r_398 mem0_398@sint16;
mov r_400 mem0_400@sint16; mov r_402 mem0_402@sint16;
mov r_404 mem0_404@sint16; mov r_406 mem0_406@sint16;
mov r_408 mem0_408@sint16; mov r_410 mem0_410@sint16;
mov r_412 mem0_412@sint16; mov r_414 mem0_414@sint16;
mov r_416 mem0_416@sint16; mov r_418 mem0_418@sint16;
mov r_420 mem0_420@sint16; mov r_422 mem0_422@sint16;
mov r_424 mem0_424@sint16; mov r_426 mem0_426@sint16;
mov r_428 mem0_428@sint16; mov r_430 mem0_430@sint16;
mov r_432 mem0_432@sint16; mov r_434 mem0_434@sint16;
mov r_436 mem0_436@sint16; mov r_438 mem0_438@sint16;
mov r_440 mem0_440@sint16; mov r_442 mem0_442@sint16;
mov r_444 mem0_444@sint16; mov r_446 mem0_446@sint16;
mov r_448 mem0_448@sint16; mov r_450 mem0_450@sint16;
mov r_452 mem0_452@sint16; mov r_454 mem0_454@sint16;
mov r_456 mem0_456@sint16; mov r_458 mem0_458@sint16;
mov r_460 mem0_460@sint16; mov r_462 mem0_462@sint16;
mov r_464 mem0_464@sint16; mov r_466 mem0_466@sint16;
mov r_468 mem0_468@sint16; mov r_470 mem0_470@sint16;
mov r_472 mem0_472@sint16; mov r_474 mem0_474@sint16;
mov r_476 mem0_476@sint16; mov r_478 mem0_478@sint16;
mov r_480 mem0_480@sint16; mov r_482 mem0_482@sint16;
mov r_484 mem0_484@sint16; mov r_486 mem0_486@sint16;
mov r_488 mem0_488@sint16; mov r_490 mem0_490@sint16;
mov r_492 mem0_492@sint16; mov r_494 mem0_494@sint16;
mov r_496 mem0_496@sint16; mov r_498 mem0_498@sint16;
mov r_500 mem0_500@sint16; mov r_502 mem0_502@sint16;
mov r_504 mem0_504@sint16; mov r_506 mem0_506@sint16;
mov r_508 mem0_508@sint16; mov r_510 mem0_510@sint16;

{
  and [ 
eqmod 
(
mem0_0_k63*(x**0) + mem0_2_k63*(x**1) + mem0_4_k63*(x**2) + mem0_6_k63*(x**3)
)
(
r_0*(x**0) + r_2*(x**1)
)
[3329, x**2 - 17],
eqmod 
(
mem0_0_k63*(x**0) + mem0_2_k63*(x**1) + mem0_4_k63*(x**2) + mem0_6_k63*(x**3)
)
(
r_4*(x**0) + r_6*(x**1)
)
[3329, x**2 - 3312],
eqmod 
(
mem0_8_k63*(x**0) + mem0_10_k63*(x**1) + mem0_12_k63*(x**2) + mem0_14_k63*(x**3)
)
(
r_8*(x**0) + r_10*(x**1)
)
[3329, x**2 - 2761],
eqmod 
(
mem0_8_k63*(x**0) + mem0_10_k63*(x**1) + mem0_12_k63*(x**2) + mem0_14_k63*(x**3)
)
(
r_12*(x**0) + r_14*(x**1)
)
[3329, x**2 - 568],
eqmod 
(
mem0_16_k63*(x**0) + mem0_18_k63*(x**1) + mem0_20_k63*(x**2) + mem0_22_k63*(x**3)
)
(
r_16*(x**0) + r_18*(x**1)
)
[3329, x**2 - 583],
eqmod 
(
mem0_16_k63*(x**0) + mem0_18_k63*(x**1) + mem0_20_k63*(x**2) + mem0_22_k63*(x**3)
)
(
r_20*(x**0) + r_22*(x**1)
)
[3329, x**2 - 2746],
eqmod 
(
mem0_24_k63*(x**0) + mem0_26_k63*(x**1) + mem0_28_k63*(x**2) + mem0_30_k63*(x**3)
)
(
r_24*(x**0) + r_26*(x**1)
)
[3329, x**2 - 2649],
eqmod 
(
mem0_24_k63*(x**0) + mem0_26_k63*(x**1) + mem0_28_k63*(x**2) + mem0_30_k63*(x**3)
)
(
r_28*(x**0) + r_30*(x**1)
)
[3329, x**2 - 680],
eqmod 
(
mem0_32_k63*(x**0) + mem0_34_k63*(x**1) + mem0_36_k63*(x**2) + mem0_38_k63*(x**3)
)
(
r_32*(x**0) + r_34*(x**1)
)
[3329, x**2 - 1637],
eqmod 
(
mem0_32_k63*(x**0) + mem0_34_k63*(x**1) + mem0_36_k63*(x**2) + mem0_38_k63*(x**3)
)
(
r_36*(x**0) + r_38*(x**1)
)
[3329, x**2 - 1692],
eqmod 
(
mem0_40_k63*(x**0) + mem0_42_k63*(x**1) + mem0_44_k63*(x**2) + mem0_46_k63*(x**3)
)
(
r_40*(x**0) + r_42*(x**1)
)
[3329, x**2 - 723],
eqmod 
(
mem0_40_k63*(x**0) + mem0_42_k63*(x**1) + mem0_44_k63*(x**2) + mem0_46_k63*(x**3)
)
(
r_44*(x**0) + r_46*(x**1)
)
[3329, x**2 - 2606],
eqmod 
(
mem0_48_k63*(x**0) + mem0_50_k63*(x**1) + mem0_52_k63*(x**2) + mem0_54_k63*(x**3)
)
(
r_48*(x**0) + r_50*(x**1)
)
[3329, x**2 - 2288],
eqmod 
(
mem0_48_k63*(x**0) + mem0_50_k63*(x**1) + mem0_52_k63*(x**2) + mem0_54_k63*(x**3)
)
(
r_52*(x**0) + r_54*(x**1)
)
[3329, x**2 - 1041],
eqmod 
(
mem0_56_k63*(x**0) + mem0_58_k63*(x**1) + mem0_60_k63*(x**2) + mem0_62_k63*(x**3)
)
(
r_56*(x**0) + r_58*(x**1)
)
[3329, x**2 - 1100],
eqmod 
(
mem0_56_k63*(x**0) + mem0_58_k63*(x**1) + mem0_60_k63*(x**2) + mem0_62_k63*(x**3)
)
(
r_60*(x**0) + r_62*(x**1)
)
[3329, x**2 - 2229],
eqmod 
(
mem0_64_k63*(x**0) + mem0_66_k63*(x**1) + mem0_68_k63*(x**2) + mem0_70_k63*(x**3)
)
(
r_64*(x**0) + r_66*(x**1)
)
[3329, x**2 - 1409],
eqmod 
(
mem0_64_k63*(x**0) + mem0_66_k63*(x**1) + mem0_68_k63*(x**2) + mem0_70_k63*(x**3)
)
(
r_68*(x**0) + r_70*(x**1)
)
[3329, x**2 - 1920],
eqmod 
(
mem0_72_k63*(x**0) + mem0_74_k63*(x**1) + mem0_76_k63*(x**2) + mem0_78_k63*(x**3)
)
(
r_72*(x**0) + r_74*(x**1)
)
[3329, x**2 - 2662],
eqmod 
(
mem0_72_k63*(x**0) + mem0_74_k63*(x**1) + mem0_76_k63*(x**2) + mem0_78_k63*(x**3)
)
(
r_76*(x**0) + r_78*(x**1)
)
[3329, x**2 - 667],
eqmod 
(
mem0_80_k63*(x**0) + mem0_82_k63*(x**1) + mem0_84_k63*(x**2) + mem0_86_k63*(x**3)
)
(
r_80*(x**0) + r_82*(x**1)
)
[3329, x**2 - 3281],
eqmod 
(
mem0_80_k63*(x**0) + mem0_82_k63*(x**1) + mem0_84_k63*(x**2) + mem0_86_k63*(x**3)
)
(
r_84*(x**0) + r_86*(x**1)
)
[3329, x**2 - 48],
eqmod 
(
mem0_88_k63*(x**0) + mem0_90_k63*(x**1) + mem0_92_k63*(x**2) + mem0_94_k63*(x**3)
)
(
r_88*(x**0) + r_90*(x**1)
)
[3329, x**2 - 233],
eqmod 
(
mem0_88_k63*(x**0) + mem0_90_k63*(x**1) + mem0_92_k63*(x**2) + mem0_94_k63*(x**3)
)
(
r_92*(x**0) + r_94*(x**1)
)
[3329, x**2 - 3096],
eqmod 
(
mem0_96_k63*(x**0) + mem0_98_k63*(x**1) + mem0_100_k63*(x**2) + mem0_102_k63*(x**3)
)
(
r_96*(x**0) + r_98*(x**1)
)
[3329, x**2 - 756],
eqmod 
(
mem0_96_k63*(x**0) + mem0_98_k63*(x**1) + mem0_100_k63*(x**2) + mem0_102_k63*(x**3)
)
(
r_100*(x**0) + r_102*(x**1)
)
[3329, x**2 - 2573],
eqmod 
(
mem0_104_k63*(x**0) + mem0_106_k63*(x**1) + mem0_108_k63*(x**2) + mem0_110_k63*(x**3)
)
(
r_104*(x**0) + r_106*(x**1)
)
[3329, x**2 - 2156],
eqmod 
(
mem0_104_k63*(x**0) + mem0_106_k63*(x**1) + mem0_108_k63*(x**2) + mem0_110_k63*(x**3)
)
(
r_108*(x**0) + r_110*(x**1)
)
[3329, x**2 - 1173],
eqmod 
(
mem0_112_k63*(x**0) + mem0_114_k63*(x**1) + mem0_116_k63*(x**2) + mem0_118_k63*(x**3)
)
(
r_112*(x**0) + r_114*(x**1)
)
[3329, x**2 - 3015],
eqmod 
(
mem0_112_k63*(x**0) + mem0_114_k63*(x**1) + mem0_116_k63*(x**2) + mem0_118_k63*(x**3)
)
(
r_116*(x**0) + r_118*(x**1)
)
[3329, x**2 - 314],
eqmod 
(
mem0_120_k63*(x**0) + mem0_122_k63*(x**1) + mem0_124_k63*(x**2) + mem0_126_k63*(x**3)
)
(
r_120*(x**0) + r_122*(x**1)
)
[3329, x**2 - 3050],
eqmod 
(
mem0_120_k63*(x**0) + mem0_122_k63*(x**1) + mem0_124_k63*(x**2) + mem0_126_k63*(x**3)
)
(
r_124*(x**0) + r_126*(x**1)
)
[3329, x**2 - 279],
eqmod 
(
mem0_128_k63*(x**0) + mem0_130_k63*(x**1) + mem0_132_k63*(x**2) + mem0_134_k63*(x**3)
)
(
r_128*(x**0) + r_130*(x**1)
)
[3329, x**2 - 1703],
eqmod 
(
mem0_128_k63*(x**0) + mem0_130_k63*(x**1) + mem0_132_k63*(x**2) + mem0_134_k63*(x**3)
)
(
r_132*(x**0) + r_134*(x**1)
)
[3329, x**2 - 1626],
eqmod 
(
mem0_136_k63*(x**0) + mem0_138_k63*(x**1) + mem0_140_k63*(x**2) + mem0_142_k63*(x**3)
)
(
r_136*(x**0) + r_138*(x**1)
)
[3329, x**2 - 1651],
eqmod 
(
mem0_136_k63*(x**0) + mem0_138_k63*(x**1) + mem0_140_k63*(x**2) + mem0_142_k63*(x**3)
)
(
r_140*(x**0) + r_142*(x**1)
)
[3329, x**2 - 1678],
eqmod 
(
mem0_144_k63*(x**0) + mem0_146_k63*(x**1) + mem0_148_k63*(x**2) + mem0_150_k63*(x**3)
)
(
r_144*(x**0) + r_146*(x**1)
)
[3329, x**2 - 2789],
eqmod 
(
mem0_144_k63*(x**0) + mem0_146_k63*(x**1) + mem0_148_k63*(x**2) + mem0_150_k63*(x**3)
)
(
r_148*(x**0) + r_150*(x**1)
)
[3329, x**2 - 540],
eqmod 
(
mem0_152_k63*(x**0) + mem0_154_k63*(x**1) + mem0_156_k63*(x**2) + mem0_158_k63*(x**3)
)
(
r_152*(x**0) + r_154*(x**1)
)
[3329, x**2 - 1789],
eqmod 
(
mem0_152_k63*(x**0) + mem0_154_k63*(x**1) + mem0_156_k63*(x**2) + mem0_158_k63*(x**3)
)
(
r_156*(x**0) + r_158*(x**1)
)
[3329, x**2 - 1540],
eqmod 
(
mem0_160_k63*(x**0) + mem0_162_k63*(x**1) + mem0_164_k63*(x**2) + mem0_166_k63*(x**3)
)
(
r_160*(x**0) + r_162*(x**1)
)
[3329, x**2 - 1847],
eqmod 
(
mem0_160_k63*(x**0) + mem0_162_k63*(x**1) + mem0_164_k63*(x**2) + mem0_166_k63*(x**3)
)
(
r_164*(x**0) + r_166*(x**1)
)
[3329, x**2 - 1482],
eqmod 
(
mem0_168_k63*(x**0) + mem0_170_k63*(x**1) + mem0_172_k63*(x**2) + mem0_174_k63*(x**3)
)
(
r_168*(x**0) + r_170*(x**1)
)
[3329, x**2 - 952],
eqmod 
(
mem0_168_k63*(x**0) + mem0_170_k63*(x**1) + mem0_172_k63*(x**2) + mem0_174_k63*(x**3)
)
(
r_172*(x**0) + r_174*(x**1)
)
[3329, x**2 - 2377],
eqmod 
(
mem0_176_k63*(x**0) + mem0_178_k63*(x**1) + mem0_180_k63*(x**2) + mem0_182_k63*(x**3)
)
(
r_176*(x**0) + r_178*(x**1)
)
[3329, x**2 - 1461],
eqmod 
(
mem0_176_k63*(x**0) + mem0_178_k63*(x**1) + mem0_180_k63*(x**2) + mem0_182_k63*(x**3)
)
(
r_180*(x**0) + r_182*(x**1)
)
[3329, x**2 - 1868],
eqmod 
(
mem0_184_k63*(x**0) + mem0_186_k63*(x**1) + mem0_188_k63*(x**2) + mem0_190_k63*(x**3)
)
(
r_184*(x**0) + r_186*(x**1)
)
[3329, x**2 - 2687],
eqmod 
(
mem0_184_k63*(x**0) + mem0_186_k63*(x**1) + mem0_188_k63*(x**2) + mem0_190_k63*(x**3)
)
(
r_188*(x**0) + r_190*(x**1)
)
[3329, x**2 - 642],
eqmod 
(
mem0_192_k63*(x**0) + mem0_194_k63*(x**1) + mem0_196_k63*(x**2) + mem0_198_k63*(x**3)
)
(
r_192*(x**0) + r_194*(x**1)
)
[3329, x**2 - 939],
eqmod 
(
mem0_192_k63*(x**0) + mem0_194_k63*(x**1) + mem0_196_k63*(x**2) + mem0_198_k63*(x**3)
)
(
r_196*(x**0) + r_198*(x**1)
)
[3329, x**2 - 2390],
eqmod 
(
mem0_200_k63*(x**0) + mem0_202_k63*(x**1) + mem0_204_k63*(x**2) + mem0_206_k63*(x**3)
)
(
r_200*(x**0) + r_202*(x**1)
)
[3329, x**2 - 2308],
eqmod 
(
mem0_200_k63*(x**0) + mem0_202_k63*(x**1) + mem0_204_k63*(x**2) + mem0_206_k63*(x**3)
)
(
r_204*(x**0) + r_206*(x**1)
)
[3329, x**2 - 1021],
eqmod 
(
mem0_208_k63*(x**0) + mem0_210_k63*(x**1) + mem0_212_k63*(x**2) + mem0_214_k63*(x**3)
)
(
r_208*(x**0) + r_210*(x**1)
)
[3329, x**2 - 2437],
eqmod 
(
mem0_208_k63*(x**0) + mem0_210_k63*(x**1) + mem0_212_k63*(x**2) + mem0_214_k63*(x**3)
)
(
r_212*(x**0) + r_214*(x**1)
)
[3329, x**2 - 892],
eqmod 
(
mem0_216_k63*(x**0) + mem0_218_k63*(x**1) + mem0_220_k63*(x**2) + mem0_222_k63*(x**3)
)
(
r_216*(x**0) + r_218*(x**1)
)
[3329, x**2 - 2388],
eqmod 
(
mem0_216_k63*(x**0) + mem0_218_k63*(x**1) + mem0_220_k63*(x**2) + mem0_222_k63*(x**3)
)
(
r_220*(x**0) + r_222*(x**1)
)
[3329, x**2 - 941],
eqmod 
(
mem0_224_k63*(x**0) + mem0_226_k63*(x**1) + mem0_228_k63*(x**2) + mem0_230_k63*(x**3)
)
(
r_224*(x**0) + r_226*(x**1)
)
[3329, x**2 - 733],
eqmod 
(
mem0_224_k63*(x**0) + mem0_226_k63*(x**1) + mem0_228_k63*(x**2) + mem0_230_k63*(x**3)
)
(
r_228*(x**0) + r_230*(x**1)
)
[3329, x**2 - 2596],
eqmod 
(
mem0_232_k63*(x**0) + mem0_234_k63*(x**1) + mem0_236_k63*(x**2) + mem0_238_k63*(x**3)
)
(
r_232*(x**0) + r_234*(x**1)
)
[3329, x**2 - 2337],
eqmod 
(
mem0_232_k63*(x**0) + mem0_234_k63*(x**1) + mem0_236_k63*(x**2) + mem0_238_k63*(x**3)
)
(
r_236*(x**0) + r_238*(x**1)
)
[3329, x**2 - 992],
eqmod 
(
mem0_240_k63*(x**0) + mem0_242_k63*(x**1) + mem0_244_k63*(x**2) + mem0_246_k63*(x**3)
)
(
r_240*(x**0) + r_242*(x**1)
)
[3329, x**2 - 268],
eqmod 
(
mem0_240_k63*(x**0) + mem0_242_k63*(x**1) + mem0_244_k63*(x**2) + mem0_246_k63*(x**3)
)
(
r_244*(x**0) + r_246*(x**1)
)
[3329, x**2 - 3061],
eqmod 
(
mem0_248_k63*(x**0) + mem0_250_k63*(x**1) + mem0_252_k63*(x**2) + mem0_254_k63*(x**3)
)
(
r_248*(x**0) + r_250*(x**1)
)
[3329, x**2 - 641],
eqmod 
(
mem0_248_k63*(x**0) + mem0_250_k63*(x**1) + mem0_252_k63*(x**2) + mem0_254_k63*(x**3)
)
(
r_252*(x**0) + r_254*(x**1)
)
[3329, x**2 - 2688],
eqmod 
(
mem0_256_k63*(x**0) + mem0_258_k63*(x**1) + mem0_260_k63*(x**2) + mem0_262_k63*(x**3)
)
(
r_256*(x**0) + r_258*(x**1)
)
[3329, x**2 - 1584],
eqmod 
(
mem0_256_k63*(x**0) + mem0_258_k63*(x**1) + mem0_260_k63*(x**2) + mem0_262_k63*(x**3)
)
(
r_260*(x**0) + r_262*(x**1)
)
[3329, x**2 - 1745],
eqmod 
(
mem0_264_k63*(x**0) + mem0_266_k63*(x**1) + mem0_268_k63*(x**2) + mem0_270_k63*(x**3)
)
(
r_264*(x**0) + r_266*(x**1)
)
[3329, x**2 - 2298],
eqmod 
(
mem0_264_k63*(x**0) + mem0_266_k63*(x**1) + mem0_268_k63*(x**2) + mem0_270_k63*(x**3)
)
(
r_268*(x**0) + r_270*(x**1)
)
[3329, x**2 - 1031],
eqmod 
(
mem0_272_k63*(x**0) + mem0_274_k63*(x**1) + mem0_276_k63*(x**2) + mem0_278_k63*(x**3)
)
(
r_272*(x**0) + r_274*(x**1)
)
[3329, x**2 - 2037],
eqmod 
(
mem0_272_k63*(x**0) + mem0_274_k63*(x**1) + mem0_276_k63*(x**2) + mem0_278_k63*(x**3)
)
(
r_276*(x**0) + r_278*(x**1)
)
[3329, x**2 - 1292],
eqmod 
(
mem0_280_k63*(x**0) + mem0_282_k63*(x**1) + mem0_284_k63*(x**2) + mem0_286_k63*(x**3)
)
(
r_280*(x**0) + r_282*(x**1)
)
[3329, x**2 - 3220],
eqmod 
(
mem0_280_k63*(x**0) + mem0_282_k63*(x**1) + mem0_284_k63*(x**2) + mem0_286_k63*(x**3)
)
(
r_284*(x**0) + r_286*(x**1)
)
[3329, x**2 - 109],
eqmod 
(
mem0_288_k63*(x**0) + mem0_290_k63*(x**1) + mem0_292_k63*(x**2) + mem0_294_k63*(x**3)
)
(
r_288*(x**0) + r_290*(x**1)
)
[3329, x**2 - 375],
eqmod 
(
mem0_288_k63*(x**0) + mem0_290_k63*(x**1) + mem0_292_k63*(x**2) + mem0_294_k63*(x**3)
)
(
r_292*(x**0) + r_294*(x**1)
)
[3329, x**2 - 2954],
eqmod 
(
mem0_296_k63*(x**0) + mem0_298_k63*(x**1) + mem0_300_k63*(x**2) + mem0_302_k63*(x**3)
)
(
r_296*(x**0) + r_298*(x**1)
)
[3329, x**2 - 2549],
eqmod 
(
mem0_296_k63*(x**0) + mem0_298_k63*(x**1) + mem0_300_k63*(x**2) + mem0_302_k63*(x**3)
)
(
r_300*(x**0) + r_302*(x**1)
)
[3329, x**2 - 780],
eqmod 
(
mem0_304_k63*(x**0) + mem0_306_k63*(x**1) + mem0_308_k63*(x**2) + mem0_310_k63*(x**3)
)
(
r_304*(x**0) + r_306*(x**1)
)
[3329, x**2 - 2090],
eqmod 
(
mem0_304_k63*(x**0) + mem0_306_k63*(x**1) + mem0_308_k63*(x**2) + mem0_310_k63*(x**3)
)
(
r_308*(x**0) + r_310*(x**1)
)
[3329, x**2 - 1239],
eqmod 
(
mem0_312_k63*(x**0) + mem0_314_k63*(x**1) + mem0_316_k63*(x**2) + mem0_318_k63*(x**3)
)
(
r_312*(x**0) + r_314*(x**1)
)
[3329, x**2 - 1645],
eqmod 
(
mem0_312_k63*(x**0) + mem0_314_k63*(x**1) + mem0_316_k63*(x**2) + mem0_318_k63*(x**3)
)
(
r_316*(x**0) + r_318*(x**1)
)
[3329, x**2 - 1684],
eqmod 
(
mem0_320_k63*(x**0) + mem0_322_k63*(x**1) + mem0_324_k63*(x**2) + mem0_326_k63*(x**3)
)
(
r_320*(x**0) + r_322*(x**1)
)
[3329, x**2 - 1063],
eqmod 
(
mem0_320_k63*(x**0) + mem0_322_k63*(x**1) + mem0_324_k63*(x**2) + mem0_326_k63*(x**3)
)
(
r_324*(x**0) + r_326*(x**1)
)
[3329, x**2 - 2266],
eqmod 
(
mem0_328_k63*(x**0) + mem0_330_k63*(x**1) + mem0_332_k63*(x**2) + mem0_334_k63*(x**3)
)
(
r_328*(x**0) + r_330*(x**1)
)
[3329, x**2 - 319],
eqmod 
(
mem0_328_k63*(x**0) + mem0_330_k63*(x**1) + mem0_332_k63*(x**2) + mem0_334_k63*(x**3)
)
(
r_332*(x**0) + r_334*(x**1)
)
[3329, x**2 - 3010],
eqmod 
(
mem0_336_k63*(x**0) + mem0_338_k63*(x**1) + mem0_340_k63*(x**2) + mem0_342_k63*(x**3)
)
(
r_336*(x**0) + r_338*(x**1)
)
[3329, x**2 - 2773],
eqmod 
(
mem0_336_k63*(x**0) + mem0_338_k63*(x**1) + mem0_340_k63*(x**2) + mem0_342_k63*(x**3)
)
(
r_340*(x**0) + r_342*(x**1)
)
[3329, x**2 - 556],
eqmod 
(
mem0_344_k63*(x**0) + mem0_346_k63*(x**1) + mem0_348_k63*(x**2) + mem0_350_k63*(x**3)
)
(
r_344*(x**0) + r_346*(x**1)
)
[3329, x**2 - 757],
eqmod 
(
mem0_344_k63*(x**0) + mem0_346_k63*(x**1) + mem0_348_k63*(x**2) + mem0_350_k63*(x**3)
)
(
r_348*(x**0) + r_350*(x**1)
)
[3329, x**2 - 2572],
eqmod 
(
mem0_352_k63*(x**0) + mem0_354_k63*(x**1) + mem0_356_k63*(x**2) + mem0_358_k63*(x**3)
)
(
r_352*(x**0) + r_354*(x**1)
)
[3329, x**2 - 2099],
eqmod 
(
mem0_352_k63*(x**0) + mem0_354_k63*(x**1) + mem0_356_k63*(x**2) + mem0_358_k63*(x**3)
)
(
r_356*(x**0) + r_358*(x**1)
)
[3329, x**2 - 1230],
eqmod 
(
mem0_360_k63*(x**0) + mem0_362_k63*(x**1) + mem0_364_k63*(x**2) + mem0_366_k63*(x**3)
)
(
r_360*(x**0) + r_362*(x**1)
)
[3329, x**2 - 561],
eqmod 
(
mem0_360_k63*(x**0) + mem0_362_k63*(x**1) + mem0_364_k63*(x**2) + mem0_366_k63*(x**3)
)
(
r_364*(x**0) + r_366*(x**1)
)
[3329, x**2 - 2768],
eqmod 
(
mem0_368_k63*(x**0) + mem0_370_k63*(x**1) + mem0_372_k63*(x**2) + mem0_374_k63*(x**3)
)
(
r_368*(x**0) + r_370*(x**1)
)
[3329, x**2 - 2466],
eqmod 
(
mem0_368_k63*(x**0) + mem0_370_k63*(x**1) + mem0_372_k63*(x**2) + mem0_374_k63*(x**3)
)
(
r_372*(x**0) + r_374*(x**1)
)
[3329, x**2 - 863],
eqmod 
(
mem0_376_k63*(x**0) + mem0_378_k63*(x**1) + mem0_380_k63*(x**2) + mem0_382_k63*(x**3)
)
(
r_376*(x**0) + r_378*(x**1)
)
[3329, x**2 - 2594],
eqmod 
(
mem0_376_k63*(x**0) + mem0_378_k63*(x**1) + mem0_380_k63*(x**2) + mem0_382_k63*(x**3)
)
(
r_380*(x**0) + r_382*(x**1)
)
[3329, x**2 - 735],
eqmod 
(
mem0_384_k63*(x**0) + mem0_386_k63*(x**1) + mem0_388_k63*(x**2) + mem0_390_k63*(x**3)
)
(
r_384*(x**0) + r_386*(x**1)
)
[3329, x**2 - 2804],
eqmod 
(
mem0_384_k63*(x**0) + mem0_386_k63*(x**1) + mem0_388_k63*(x**2) + mem0_390_k63*(x**3)
)
(
r_388*(x**0) + r_390*(x**1)
)
[3329, x**2 - 525],
eqmod 
(
mem0_392_k63*(x**0) + mem0_394_k63*(x**1) + mem0_396_k63*(x**2) + mem0_398_k63*(x**3)
)
(
r_392*(x**0) + r_394*(x**1)
)
[3329, x**2 - 1092],
eqmod 
(
mem0_392_k63*(x**0) + mem0_394_k63*(x**1) + mem0_396_k63*(x**2) + mem0_398_k63*(x**3)
)
(
r_396*(x**0) + r_398*(x**1)
)
[3329, x**2 - 2237],
eqmod 
(
mem0_400_k63*(x**0) + mem0_402_k63*(x**1) + mem0_404_k63*(x**2) + mem0_406_k63*(x**3)
)
(
r_400*(x**0) + r_402*(x**1)
)
[3329, x**2 - 403],
eqmod 
(
mem0_400_k63*(x**0) + mem0_402_k63*(x**1) + mem0_404_k63*(x**2) + mem0_406_k63*(x**3)
)
(
r_404*(x**0) + r_406*(x**1)
)
[3329, x**2 - 2926],
eqmod 
(
mem0_408_k63*(x**0) + mem0_410_k63*(x**1) + mem0_412_k63*(x**2) + mem0_414_k63*(x**3)
)
(
r_408*(x**0) + r_410*(x**1)
)
[3329, x**2 - 1026],
eqmod 
(
mem0_408_k63*(x**0) + mem0_410_k63*(x**1) + mem0_412_k63*(x**2) + mem0_414_k63*(x**3)
)
(
r_412*(x**0) + r_414*(x**1)
)
[3329, x**2 - 2303],
eqmod 
(
mem0_416_k63*(x**0) + mem0_418_k63*(x**1) + mem0_420_k63*(x**2) + mem0_422_k63*(x**3)
)
(
r_416*(x**0) + r_418*(x**1)
)
[3329, x**2 - 1143],
eqmod 
(
mem0_416_k63*(x**0) + mem0_418_k63*(x**1) + mem0_420_k63*(x**2) + mem0_422_k63*(x**3)
)
(
r_420*(x**0) + r_422*(x**1)
)
[3329, x**2 - 2186],
eqmod 
(
mem0_424_k63*(x**0) + mem0_426_k63*(x**1) + mem0_428_k63*(x**2) + mem0_430_k63*(x**3)
)
(
r_424*(x**0) + r_426*(x**1)
)
[3329, x**2 - 2150],
eqmod 
(
mem0_424_k63*(x**0) + mem0_426_k63*(x**1) + mem0_428_k63*(x**2) + mem0_430_k63*(x**3)
)
(
r_428*(x**0) + r_430*(x**1)
)
[3329, x**2 - 1179],
eqmod 
(
mem0_432_k63*(x**0) + mem0_434_k63*(x**1) + mem0_436_k63*(x**2) + mem0_438_k63*(x**3)
)
(
r_432*(x**0) + r_434*(x**1)
)
[3329, x**2 - 2775],
eqmod 
(
mem0_432_k63*(x**0) + mem0_434_k63*(x**1) + mem0_436_k63*(x**2) + mem0_438_k63*(x**3)
)
(
r_436*(x**0) + r_438*(x**1)
)
[3329, x**2 - 554],
eqmod 
(
mem0_440_k63*(x**0) + mem0_442_k63*(x**1) + mem0_444_k63*(x**2) + mem0_446_k63*(x**3)
)
(
r_440*(x**0) + r_442*(x**1)
)
[3329, x**2 - 886],
eqmod 
(
mem0_440_k63*(x**0) + mem0_442_k63*(x**1) + mem0_444_k63*(x**2) + mem0_446_k63*(x**3)
)
(
r_444*(x**0) + r_446*(x**1)
)
[3329, x**2 - 2443],
eqmod 
(
mem0_448_k63*(x**0) + mem0_450_k63*(x**1) + mem0_452_k63*(x**2) + mem0_454_k63*(x**3)
)
(
r_448*(x**0) + r_450*(x**1)
)
[3329, x**2 - 1722],
eqmod 
(
mem0_448_k63*(x**0) + mem0_450_k63*(x**1) + mem0_452_k63*(x**2) + mem0_454_k63*(x**3)
)
(
r_452*(x**0) + r_454*(x**1)
)
[3329, x**2 - 1607],
eqmod 
(
mem0_456_k63*(x**0) + mem0_458_k63*(x**1) + mem0_460_k63*(x**2) + mem0_462_k63*(x**3)
)
(
r_456*(x**0) + r_458*(x**1)
)
[3329, x**2 - 1212],
eqmod 
(
mem0_456_k63*(x**0) + mem0_458_k63*(x**1) + mem0_460_k63*(x**2) + mem0_462_k63*(x**3)
)
(
r_460*(x**0) + r_462*(x**1)
)
[3329, x**2 - 2117],
eqmod 
(
mem0_464_k63*(x**0) + mem0_466_k63*(x**1) + mem0_468_k63*(x**2) + mem0_470_k63*(x**3)
)
(
r_464*(x**0) + r_466*(x**1)
)
[3329, x**2 - 1874],
eqmod 
(
mem0_464_k63*(x**0) + mem0_466_k63*(x**1) + mem0_468_k63*(x**2) + mem0_470_k63*(x**3)
)
(
r_468*(x**0) + r_470*(x**1)
)
[3329, x**2 - 1455],
eqmod 
(
mem0_472_k63*(x**0) + mem0_474_k63*(x**1) + mem0_476_k63*(x**2) + mem0_478_k63*(x**3)
)
(
r_472*(x**0) + r_474*(x**1)
)
[3329, x**2 - 1029],
eqmod 
(
mem0_472_k63*(x**0) + mem0_474_k63*(x**1) + mem0_476_k63*(x**2) + mem0_478_k63*(x**3)
)
(
r_476*(x**0) + r_478*(x**1)
)
[3329, x**2 - 2300],
eqmod 
(
mem0_480_k63*(x**0) + mem0_482_k63*(x**1) + mem0_484_k63*(x**2) + mem0_486_k63*(x**3)
)
(
r_480*(x**0) + r_482*(x**1)
)
[3329, x**2 - 2110],
eqmod 
(
mem0_480_k63*(x**0) + mem0_482_k63*(x**1) + mem0_484_k63*(x**2) + mem0_486_k63*(x**3)
)
(
r_484*(x**0) + r_486*(x**1)
)
[3329, x**2 - 1219],
eqmod 
(
mem0_488_k63*(x**0) + mem0_490_k63*(x**1) + mem0_492_k63*(x**2) + mem0_494_k63*(x**3)
)
(
r_488*(x**0) + r_490*(x**1)
)
[3329, x**2 - 2935],
eqmod 
(
mem0_488_k63*(x**0) + mem0_490_k63*(x**1) + mem0_492_k63*(x**2) + mem0_494_k63*(x**3)
)
(
r_492*(x**0) + r_494*(x**1)
)
[3329, x**2 - 394],
eqmod 
(
mem0_496_k63*(x**0) + mem0_498_k63*(x**1) + mem0_500_k63*(x**2) + mem0_502_k63*(x**3)
)
(
r_496*(x**0) + r_498*(x**1)
)
[3329, x**2 - 885],
eqmod 
(
mem0_496_k63*(x**0) + mem0_498_k63*(x**1) + mem0_500_k63*(x**2) + mem0_502_k63*(x**3)
)
(
r_500*(x**0) + r_502*(x**1)
)
[3329, x**2 - 2444],
eqmod 
(
mem0_504_k63*(x**0) + mem0_506_k63*(x**1) + mem0_508_k63*(x**2) + mem0_510_k63*(x**3)
)
(
r_504*(x**0) + r_506*(x**1)
)
[3329, x**2 - 2154],
eqmod 
(
mem0_504_k63*(x**0) + mem0_506_k63*(x**1) + mem0_508_k63*(x**2) + mem0_510_k63*(x**3)
)
(
r_508*(x**0) + r_510*(x**1)
)
[3329, x**2 - 1175]
] && and [
   (-9)@16 * 3329@16 <s mem0_0, mem0_0 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_2, mem0_2 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_4, mem0_4 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_6, mem0_6 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_8, mem0_8 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_10, mem0_10 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_12, mem0_12 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_14, mem0_14 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_16, mem0_16 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_18, mem0_18 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_20, mem0_20 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_22, mem0_22 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_24, mem0_24 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_26, mem0_26 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_28, mem0_28 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_30, mem0_30 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_32, mem0_32 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_34, mem0_34 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_36, mem0_36 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_38, mem0_38 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_40, mem0_40 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_42, mem0_42 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_44, mem0_44 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_46, mem0_46 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_48, mem0_48 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_50, mem0_50 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_52, mem0_52 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_54, mem0_54 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_56, mem0_56 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_58, mem0_58 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_60, mem0_60 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_62, mem0_62 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_64, mem0_64 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_66, mem0_66 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_68, mem0_68 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_70, mem0_70 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_72, mem0_72 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_74, mem0_74 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_76, mem0_76 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_78, mem0_78 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_80, mem0_80 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_82, mem0_82 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_84, mem0_84 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_86, mem0_86 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_88, mem0_88 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_90, mem0_90 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_92, mem0_92 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_94, mem0_94 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_96, mem0_96 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_98, mem0_98 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_100, mem0_100 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_102, mem0_102 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_104, mem0_104 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_106, mem0_106 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_108, mem0_108 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_110, mem0_110 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_112, mem0_112 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_114, mem0_114 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_116, mem0_116 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_118, mem0_118 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_120, mem0_120 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_122, mem0_122 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_124, mem0_124 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_126, mem0_126 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_128, mem0_128 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_130, mem0_130 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_132, mem0_132 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_134, mem0_134 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_136, mem0_136 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_138, mem0_138 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_140, mem0_140 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_142, mem0_142 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_144, mem0_144 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_146, mem0_146 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_148, mem0_148 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_150, mem0_150 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_152, mem0_152 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_154, mem0_154 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_156, mem0_156 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_158, mem0_158 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_160, mem0_160 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_162, mem0_162 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_164, mem0_164 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_166, mem0_166 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_168, mem0_168 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_170, mem0_170 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_172, mem0_172 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_174, mem0_174 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_176, mem0_176 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_178, mem0_178 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_180, mem0_180 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_182, mem0_182 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_184, mem0_184 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_186, mem0_186 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_188, mem0_188 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_190, mem0_190 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_192, mem0_192 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_194, mem0_194 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_196, mem0_196 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_198, mem0_198 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_200, mem0_200 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_202, mem0_202 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_204, mem0_204 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_206, mem0_206 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_208, mem0_208 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_210, mem0_210 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_212, mem0_212 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_214, mem0_214 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_216, mem0_216 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_218, mem0_218 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_220, mem0_220 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_222, mem0_222 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_224, mem0_224 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_226, mem0_226 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_228, mem0_228 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_230, mem0_230 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_232, mem0_232 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_234, mem0_234 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_236, mem0_236 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_238, mem0_238 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_240, mem0_240 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_242, mem0_242 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_244, mem0_244 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_246, mem0_246 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_248, mem0_248 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_250, mem0_250 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_252, mem0_252 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_254, mem0_254 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_256, mem0_256 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_258, mem0_258 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_260, mem0_260 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_262, mem0_262 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_264, mem0_264 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_266, mem0_266 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_268, mem0_268 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_270, mem0_270 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_272, mem0_272 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_274, mem0_274 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_276, mem0_276 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_278, mem0_278 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_280, mem0_280 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_282, mem0_282 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_284, mem0_284 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_286, mem0_286 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_288, mem0_288 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_290, mem0_290 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_292, mem0_292 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_294, mem0_294 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_296, mem0_296 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_298, mem0_298 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_300, mem0_300 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_302, mem0_302 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_304, mem0_304 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_306, mem0_306 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_308, mem0_308 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_310, mem0_310 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_312, mem0_312 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_314, mem0_314 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_316, mem0_316 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_318, mem0_318 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_320, mem0_320 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_322, mem0_322 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_324, mem0_324 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_326, mem0_326 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_328, mem0_328 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_330, mem0_330 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_332, mem0_332 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_334, mem0_334 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_336, mem0_336 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_338, mem0_338 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_340, mem0_340 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_342, mem0_342 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_344, mem0_344 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_346, mem0_346 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_348, mem0_348 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_350, mem0_350 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_352, mem0_352 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_354, mem0_354 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_356, mem0_356 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_358, mem0_358 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_360, mem0_360 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_362, mem0_362 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_364, mem0_364 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_366, mem0_366 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_368, mem0_368 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_370, mem0_370 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_372, mem0_372 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_374, mem0_374 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_376, mem0_376 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_378, mem0_378 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_380, mem0_380 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_382, mem0_382 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_384, mem0_384 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_386, mem0_386 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_388, mem0_388 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_390, mem0_390 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_392, mem0_392 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_394, mem0_394 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_396, mem0_396 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_398, mem0_398 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_400, mem0_400 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_402, mem0_402 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_404, mem0_404 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_406, mem0_406 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_408, mem0_408 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_410, mem0_410 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_412, mem0_412 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_414, mem0_414 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_416, mem0_416 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_418, mem0_418 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_420, mem0_420 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_422, mem0_422 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_424, mem0_424 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_426, mem0_426 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_428, mem0_428 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_430, mem0_430 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_432, mem0_432 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_434, mem0_434 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_436, mem0_436 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_438, mem0_438 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_440, mem0_440 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_442, mem0_442 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_444, mem0_444 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_446, mem0_446 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_448, mem0_448 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_450, mem0_450 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_452, mem0_452 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_454, mem0_454 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_456, mem0_456 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_458, mem0_458 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_460, mem0_460 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_462, mem0_462 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_464, mem0_464 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_466, mem0_466 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_468, mem0_468 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_470, mem0_470 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_472, mem0_472 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_474, mem0_474 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_476, mem0_476 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_478, mem0_478 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_480, mem0_480 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_482, mem0_482 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_484, mem0_484 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_486, mem0_486 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_488, mem0_488 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_490, mem0_490 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_492, mem0_492 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_494, mem0_494 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_496, mem0_496 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_498, mem0_498 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_500, mem0_500 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_502, mem0_502 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_504, mem0_504 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_506, mem0_506 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_508, mem0_508 <s 9@16 * 3329@16,
   (-9)@16 * 3329@16 <s mem0_510, mem0_510 <s 9@16 * 3329@16
]
}
