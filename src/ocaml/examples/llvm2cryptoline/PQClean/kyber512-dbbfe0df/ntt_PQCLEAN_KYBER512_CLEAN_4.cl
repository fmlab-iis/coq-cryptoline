(*
~/git/cryptoline/_build/default/cv.exe -v -no_carry_constraint -o coqcryptoline.log ~/git/llvm2cryptoline-draft_examples/examples/PQClean/kyber512-dbbfe0df/coqcv_ntt_k4_separated.cl 
Parsing CryptoLine file:		[OK]		0.169314 seconds
Checking well-formedness:		[OK]		0.010295 seconds
Transforming to SSA form:		[OK]		0.001983 seconds
Normalizing specification:		[OK]		0.002566 seconds
Rewriting assignments:			[OK]		0.001583 seconds
Verifying program safety:		[OK]		41.005936 seconds
Verifying range specification:		[OK]		54.571912 seconds
Rewriting value-preserved casting:	[OK]		0.000270 seconds
Verifying algebraic specification:	[OK]		2.486562 seconds
Verification result:			[OK]		98.252873 seconds

_build/default/coqcryptoline.exe -v -jobs 16 -sat_solver cadical -sat_cert grat -no_carry_constraint ~/tmp/coqcv_ntt_k4_separated.cl 
Parsing Cryptoline file:                [OK]            0.246278 seconds
Results of checking CNF formulas:       [OK]            666.260963 seconds
Finding polynomial coefficients
         Polynomials #0:                [DONE]          873.344461 seconds
         Polynomials #4:                [DONE]          882.247782 seconds
         Polynomials #6:                [DONE]          888.279609 seconds
         Polynomials #3:                [DONE]          889.815861 seconds
         Polynomials #5:                [DONE]          892.532827 seconds
         Polynomials #7:                [DONE]          893.056222 seconds
         Polynomials #1:                [DONE]          901.951769 seconds
         Polynomials #2:                [DONE]          903.217729 seconds
Finished finding polynomial coefficients                903.420054 seconds
Verification result:                    [OK]            2080.719959 seconds
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
   (-4)@16 * 3329@16 <s mem0_0, mem0_0 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_2, mem0_2 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_4, mem0_4 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_6, mem0_6 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_8, mem0_8 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_10, mem0_10 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_12, mem0_12 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_14, mem0_14 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_16, mem0_16 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_18, mem0_18 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_20, mem0_20 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_22, mem0_22 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_24, mem0_24 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_26, mem0_26 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_28, mem0_28 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_30, mem0_30 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_32, mem0_32 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_34, mem0_34 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_36, mem0_36 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_38, mem0_38 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_40, mem0_40 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_42, mem0_42 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_44, mem0_44 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_46, mem0_46 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_48, mem0_48 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_50, mem0_50 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_52, mem0_52 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_54, mem0_54 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_56, mem0_56 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_58, mem0_58 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_60, mem0_60 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_62, mem0_62 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_64, mem0_64 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_66, mem0_66 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_68, mem0_68 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_70, mem0_70 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_72, mem0_72 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_74, mem0_74 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_76, mem0_76 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_78, mem0_78 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_80, mem0_80 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_82, mem0_82 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_84, mem0_84 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_86, mem0_86 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_88, mem0_88 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_90, mem0_90 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_92, mem0_92 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_94, mem0_94 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_96, mem0_96 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_98, mem0_98 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_100, mem0_100 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_102, mem0_102 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_104, mem0_104 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_106, mem0_106 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_108, mem0_108 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_110, mem0_110 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_112, mem0_112 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_114, mem0_114 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_116, mem0_116 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_118, mem0_118 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_120, mem0_120 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_122, mem0_122 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_124, mem0_124 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_126, mem0_126 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_128, mem0_128 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_130, mem0_130 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_132, mem0_132 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_134, mem0_134 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_136, mem0_136 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_138, mem0_138 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_140, mem0_140 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_142, mem0_142 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_144, mem0_144 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_146, mem0_146 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_148, mem0_148 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_150, mem0_150 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_152, mem0_152 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_154, mem0_154 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_156, mem0_156 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_158, mem0_158 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_160, mem0_160 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_162, mem0_162 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_164, mem0_164 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_166, mem0_166 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_168, mem0_168 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_170, mem0_170 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_172, mem0_172 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_174, mem0_174 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_176, mem0_176 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_178, mem0_178 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_180, mem0_180 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_182, mem0_182 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_184, mem0_184 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_186, mem0_186 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_188, mem0_188 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_190, mem0_190 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_192, mem0_192 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_194, mem0_194 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_196, mem0_196 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_198, mem0_198 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_200, mem0_200 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_202, mem0_202 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_204, mem0_204 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_206, mem0_206 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_208, mem0_208 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_210, mem0_210 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_212, mem0_212 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_214, mem0_214 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_216, mem0_216 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_218, mem0_218 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_220, mem0_220 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_222, mem0_222 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_224, mem0_224 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_226, mem0_226 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_228, mem0_228 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_230, mem0_230 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_232, mem0_232 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_234, mem0_234 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_236, mem0_236 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_238, mem0_238 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_240, mem0_240 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_242, mem0_242 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_244, mem0_244 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_246, mem0_246 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_248, mem0_248 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_250, mem0_250 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_252, mem0_252 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_254, mem0_254 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_256, mem0_256 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_258, mem0_258 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_260, mem0_260 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_262, mem0_262 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_264, mem0_264 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_266, mem0_266 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_268, mem0_268 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_270, mem0_270 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_272, mem0_272 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_274, mem0_274 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_276, mem0_276 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_278, mem0_278 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_280, mem0_280 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_282, mem0_282 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_284, mem0_284 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_286, mem0_286 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_288, mem0_288 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_290, mem0_290 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_292, mem0_292 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_294, mem0_294 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_296, mem0_296 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_298, mem0_298 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_300, mem0_300 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_302, mem0_302 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_304, mem0_304 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_306, mem0_306 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_308, mem0_308 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_310, mem0_310 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_312, mem0_312 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_314, mem0_314 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_316, mem0_316 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_318, mem0_318 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_320, mem0_320 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_322, mem0_322 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_324, mem0_324 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_326, mem0_326 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_328, mem0_328 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_330, mem0_330 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_332, mem0_332 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_334, mem0_334 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_336, mem0_336 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_338, mem0_338 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_340, mem0_340 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_342, mem0_342 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_344, mem0_344 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_346, mem0_346 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_348, mem0_348 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_350, mem0_350 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_352, mem0_352 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_354, mem0_354 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_356, mem0_356 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_358, mem0_358 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_360, mem0_360 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_362, mem0_362 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_364, mem0_364 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_366, mem0_366 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_368, mem0_368 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_370, mem0_370 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_372, mem0_372 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_374, mem0_374 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_376, mem0_376 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_378, mem0_378 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_380, mem0_380 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_382, mem0_382 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_384, mem0_384 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_386, mem0_386 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_388, mem0_388 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_390, mem0_390 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_392, mem0_392 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_394, mem0_394 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_396, mem0_396 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_398, mem0_398 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_400, mem0_400 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_402, mem0_402 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_404, mem0_404 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_406, mem0_406 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_408, mem0_408 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_410, mem0_410 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_412, mem0_412 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_414, mem0_414 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_416, mem0_416 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_418, mem0_418 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_420, mem0_420 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_422, mem0_422 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_424, mem0_424 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_426, mem0_426 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_428, mem0_428 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_430, mem0_430 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_432, mem0_432 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_434, mem0_434 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_436, mem0_436 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_438, mem0_438 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_440, mem0_440 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_442, mem0_442 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_444, mem0_444 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_446, mem0_446 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_448, mem0_448 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_450, mem0_450 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_452, mem0_452 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_454, mem0_454 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_456, mem0_456 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_458, mem0_458 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_460, mem0_460 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_462, mem0_462 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_464, mem0_464 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_466, mem0_466 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_468, mem0_468 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_470, mem0_470 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_472, mem0_472 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_474, mem0_474 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_476, mem0_476 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_478, mem0_478 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_480, mem0_480 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_482, mem0_482 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_484, mem0_484 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_486, mem0_486 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_488, mem0_488 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_490, mem0_490 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_492, mem0_492 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_494, mem0_494 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_496, mem0_496 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_498, mem0_498 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_500, mem0_500 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_502, mem0_502 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_504, mem0_504 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_506, mem0_506 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_508, mem0_508 <s 4@16 * 3329@16,
   (-4)@16 * 3329@16 <s mem0_510, mem0_510 <s 4@16 * 3329@16
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

mov mem0_0_k3 mem0_0;
mov mem0_2_k3 mem0_2;
mov mem0_4_k3 mem0_4;
mov mem0_6_k3 mem0_6;
mov mem0_8_k3 mem0_8;
mov mem0_10_k3 mem0_10;
mov mem0_12_k3 mem0_12;
mov mem0_14_k3 mem0_14;
mov mem0_16_k3 mem0_16;
mov mem0_18_k3 mem0_18;
mov mem0_20_k3 mem0_20;
mov mem0_22_k3 mem0_22;
mov mem0_24_k3 mem0_24;
mov mem0_26_k3 mem0_26;
mov mem0_28_k3 mem0_28;
mov mem0_30_k3 mem0_30;
mov mem0_32_k3 mem0_32;
mov mem0_34_k3 mem0_34;
mov mem0_36_k3 mem0_36;
mov mem0_38_k3 mem0_38;
mov mem0_40_k3 mem0_40;
mov mem0_42_k3 mem0_42;
mov mem0_44_k3 mem0_44;
mov mem0_46_k3 mem0_46;
mov mem0_48_k3 mem0_48;
mov mem0_50_k3 mem0_50;
mov mem0_52_k3 mem0_52;
mov mem0_54_k3 mem0_54;
mov mem0_56_k3 mem0_56;
mov mem0_58_k3 mem0_58;
mov mem0_60_k3 mem0_60;
mov mem0_62_k3 mem0_62;
mov mem0_64_k3 mem0_64;
mov mem0_66_k3 mem0_66;
mov mem0_68_k3 mem0_68;
mov mem0_70_k3 mem0_70;
mov mem0_72_k3 mem0_72;
mov mem0_74_k3 mem0_74;
mov mem0_76_k3 mem0_76;
mov mem0_78_k3 mem0_78;
mov mem0_80_k3 mem0_80;
mov mem0_82_k3 mem0_82;
mov mem0_84_k3 mem0_84;
mov mem0_86_k3 mem0_86;
mov mem0_88_k3 mem0_88;
mov mem0_90_k3 mem0_90;
mov mem0_92_k3 mem0_92;
mov mem0_94_k3 mem0_94;
mov mem0_96_k3 mem0_96;
mov mem0_98_k3 mem0_98;
mov mem0_100_k3 mem0_100;
mov mem0_102_k3 mem0_102;
mov mem0_104_k3 mem0_104;
mov mem0_106_k3 mem0_106;
mov mem0_108_k3 mem0_108;
mov mem0_110_k3 mem0_110;
mov mem0_112_k3 mem0_112;
mov mem0_114_k3 mem0_114;
mov mem0_116_k3 mem0_116;
mov mem0_118_k3 mem0_118;
mov mem0_120_k3 mem0_120;
mov mem0_122_k3 mem0_122;
mov mem0_124_k3 mem0_124;
mov mem0_126_k3 mem0_126;
mov mem0_128_k3 mem0_128;
mov mem0_130_k3 mem0_130;
mov mem0_132_k3 mem0_132;
mov mem0_134_k3 mem0_134;
mov mem0_136_k3 mem0_136;
mov mem0_138_k3 mem0_138;
mov mem0_140_k3 mem0_140;
mov mem0_142_k3 mem0_142;
mov mem0_144_k3 mem0_144;
mov mem0_146_k3 mem0_146;
mov mem0_148_k3 mem0_148;
mov mem0_150_k3 mem0_150;
mov mem0_152_k3 mem0_152;
mov mem0_154_k3 mem0_154;
mov mem0_156_k3 mem0_156;
mov mem0_158_k3 mem0_158;
mov mem0_160_k3 mem0_160;
mov mem0_162_k3 mem0_162;
mov mem0_164_k3 mem0_164;
mov mem0_166_k3 mem0_166;
mov mem0_168_k3 mem0_168;
mov mem0_170_k3 mem0_170;
mov mem0_172_k3 mem0_172;
mov mem0_174_k3 mem0_174;
mov mem0_176_k3 mem0_176;
mov mem0_178_k3 mem0_178;
mov mem0_180_k3 mem0_180;
mov mem0_182_k3 mem0_182;
mov mem0_184_k3 mem0_184;
mov mem0_186_k3 mem0_186;
mov mem0_188_k3 mem0_188;
mov mem0_190_k3 mem0_190;
mov mem0_192_k3 mem0_192;
mov mem0_194_k3 mem0_194;
mov mem0_196_k3 mem0_196;
mov mem0_198_k3 mem0_198;
mov mem0_200_k3 mem0_200;
mov mem0_202_k3 mem0_202;
mov mem0_204_k3 mem0_204;
mov mem0_206_k3 mem0_206;
mov mem0_208_k3 mem0_208;
mov mem0_210_k3 mem0_210;
mov mem0_212_k3 mem0_212;
mov mem0_214_k3 mem0_214;
mov mem0_216_k3 mem0_216;
mov mem0_218_k3 mem0_218;
mov mem0_220_k3 mem0_220;
mov mem0_222_k3 mem0_222;
mov mem0_224_k3 mem0_224;
mov mem0_226_k3 mem0_226;
mov mem0_228_k3 mem0_228;
mov mem0_230_k3 mem0_230;
mov mem0_232_k3 mem0_232;
mov mem0_234_k3 mem0_234;
mov mem0_236_k3 mem0_236;
mov mem0_238_k3 mem0_238;
mov mem0_240_k3 mem0_240;
mov mem0_242_k3 mem0_242;
mov mem0_244_k3 mem0_244;
mov mem0_246_k3 mem0_246;
mov mem0_248_k3 mem0_248;
mov mem0_250_k3 mem0_250;
mov mem0_252_k3 mem0_252;
mov mem0_254_k3 mem0_254;
mov mem0_256_k3 mem0_256;
mov mem0_258_k3 mem0_258;
mov mem0_260_k3 mem0_260;
mov mem0_262_k3 mem0_262;
mov mem0_264_k3 mem0_264;
mov mem0_266_k3 mem0_266;
mov mem0_268_k3 mem0_268;
mov mem0_270_k3 mem0_270;
mov mem0_272_k3 mem0_272;
mov mem0_274_k3 mem0_274;
mov mem0_276_k3 mem0_276;
mov mem0_278_k3 mem0_278;
mov mem0_280_k3 mem0_280;
mov mem0_282_k3 mem0_282;
mov mem0_284_k3 mem0_284;
mov mem0_286_k3 mem0_286;
mov mem0_288_k3 mem0_288;
mov mem0_290_k3 mem0_290;
mov mem0_292_k3 mem0_292;
mov mem0_294_k3 mem0_294;
mov mem0_296_k3 mem0_296;
mov mem0_298_k3 mem0_298;
mov mem0_300_k3 mem0_300;
mov mem0_302_k3 mem0_302;
mov mem0_304_k3 mem0_304;
mov mem0_306_k3 mem0_306;
mov mem0_308_k3 mem0_308;
mov mem0_310_k3 mem0_310;
mov mem0_312_k3 mem0_312;
mov mem0_314_k3 mem0_314;
mov mem0_316_k3 mem0_316;
mov mem0_318_k3 mem0_318;
mov mem0_320_k3 mem0_320;
mov mem0_322_k3 mem0_322;
mov mem0_324_k3 mem0_324;
mov mem0_326_k3 mem0_326;
mov mem0_328_k3 mem0_328;
mov mem0_330_k3 mem0_330;
mov mem0_332_k3 mem0_332;
mov mem0_334_k3 mem0_334;
mov mem0_336_k3 mem0_336;
mov mem0_338_k3 mem0_338;
mov mem0_340_k3 mem0_340;
mov mem0_342_k3 mem0_342;
mov mem0_344_k3 mem0_344;
mov mem0_346_k3 mem0_346;
mov mem0_348_k3 mem0_348;
mov mem0_350_k3 mem0_350;
mov mem0_352_k3 mem0_352;
mov mem0_354_k3 mem0_354;
mov mem0_356_k3 mem0_356;
mov mem0_358_k3 mem0_358;
mov mem0_360_k3 mem0_360;
mov mem0_362_k3 mem0_362;
mov mem0_364_k3 mem0_364;
mov mem0_366_k3 mem0_366;
mov mem0_368_k3 mem0_368;
mov mem0_370_k3 mem0_370;
mov mem0_372_k3 mem0_372;
mov mem0_374_k3 mem0_374;
mov mem0_376_k3 mem0_376;
mov mem0_378_k3 mem0_378;
mov mem0_380_k3 mem0_380;
mov mem0_382_k3 mem0_382;
mov mem0_384_k3 mem0_384;
mov mem0_386_k3 mem0_386;
mov mem0_388_k3 mem0_388;
mov mem0_390_k3 mem0_390;
mov mem0_392_k3 mem0_392;
mov mem0_394_k3 mem0_394;
mov mem0_396_k3 mem0_396;
mov mem0_398_k3 mem0_398;
mov mem0_400_k3 mem0_400;
mov mem0_402_k3 mem0_402;
mov mem0_404_k3 mem0_404;
mov mem0_406_k3 mem0_406;
mov mem0_408_k3 mem0_408;
mov mem0_410_k3 mem0_410;
mov mem0_412_k3 mem0_412;
mov mem0_414_k3 mem0_414;
mov mem0_416_k3 mem0_416;
mov mem0_418_k3 mem0_418;
mov mem0_420_k3 mem0_420;
mov mem0_422_k3 mem0_422;
mov mem0_424_k3 mem0_424;
mov mem0_426_k3 mem0_426;
mov mem0_428_k3 mem0_428;
mov mem0_430_k3 mem0_430;
mov mem0_432_k3 mem0_432;
mov mem0_434_k3 mem0_434;
mov mem0_436_k3 mem0_436;
mov mem0_438_k3 mem0_438;
mov mem0_440_k3 mem0_440;
mov mem0_442_k3 mem0_442;
mov mem0_444_k3 mem0_444;
mov mem0_446_k3 mem0_446;
mov mem0_448_k3 mem0_448;
mov mem0_450_k3 mem0_450;
mov mem0_452_k3 mem0_452;
mov mem0_454_k3 mem0_454;
mov mem0_456_k3 mem0_456;
mov mem0_458_k3 mem0_458;
mov mem0_460_k3 mem0_460;
mov mem0_462_k3 mem0_462;
mov mem0_464_k3 mem0_464;
mov mem0_466_k3 mem0_466;
mov mem0_468_k3 mem0_468;
mov mem0_470_k3 mem0_470;
mov mem0_472_k3 mem0_472;
mov mem0_474_k3 mem0_474;
mov mem0_476_k3 mem0_476;
mov mem0_478_k3 mem0_478;
mov mem0_480_k3 mem0_480;
mov mem0_482_k3 mem0_482;
mov mem0_484_k3 mem0_484;
mov mem0_486_k3 mem0_486;
mov mem0_488_k3 mem0_488;
mov mem0_490_k3 mem0_490;
mov mem0_492_k3 mem0_492;
mov mem0_494_k3 mem0_494;
mov mem0_496_k3 mem0_496;
mov mem0_498_k3 mem0_498;
mov mem0_500_k3 mem0_500;
mov mem0_502_k3 mem0_502;
mov mem0_504_k3 mem0_504;
mov mem0_506_k3 mem0_506;
mov mem0_508_k3 mem0_508;
mov mem0_510_k3 mem0_510;


(* NOTE: k = 4 *)

(*   %arrayidx9.2 = getelementptr inbounds i16, i16* %r, i64 32 *)
(*   %512 = load i16, i16* %arrayidx9.2, align 2, !tbaa !3 *)
mov v512 mem0_64;
(*   %conv1.i.2 = sext i16 %512 to i32 *)
cast v_conv1_i_2@sint32 v512@sint16;
(*   %mul.i.2 = mul nsw i32 %conv1.i.2, 1493 *)
mul v_mul_i_2 v_conv1_i_2 (1493)@sint32;
(*   %call.i.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2, v_call_i_2);
(*   %513 = load i16, i16* %r, align 2, !tbaa !3 *)
mov v513 mem0_0;
(*   %sub.2 = sub i16 %513, %call.i.2 *)
sub v_sub_2 v513 v_call_i_2;
(*   store i16 %sub.2, i16* %arrayidx9.2, align 2, !tbaa !3 *)
mov mem0_64 v_sub_2;
(*   %add21.2 = add i16 %513, %call.i.2 *)
add v_add21_2 v513 v_call_i_2;
(*   store i16 %add21.2, i16* %r, align 2, !tbaa !3 *)
mov mem0_0 v_add21_2;
(*   %arrayidx9.2.1 = getelementptr inbounds i16, i16* %r, i64 33 *)
(*   %514 = load i16, i16* %arrayidx9.2.1, align 2, !tbaa !3 *)
mov v514 mem0_66;
(*   %conv1.i.2.1 = sext i16 %514 to i32 *)
cast v_conv1_i_2_1@sint32 v514@sint16;
(*   %mul.i.2.1 = mul nsw i32 %conv1.i.2.1, 1493 *)
mul v_mul_i_2_1 v_conv1_i_2_1 (1493)@sint32;
(*   %call.i.2.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_1, v_call_i_2_1);
(*   %arrayidx11.2.1 = getelementptr inbounds i16, i16* %r, i64 1 *)
(*   %515 = load i16, i16* %arrayidx11.2.1, align 2, !tbaa !3 *)
mov v515 mem0_2;
(*   %sub.2.1 = sub i16 %515, %call.i.2.1 *)
sub v_sub_2_1 v515 v_call_i_2_1;
(*   store i16 %sub.2.1, i16* %arrayidx9.2.1, align 2, !tbaa !3 *)
mov mem0_66 v_sub_2_1;
(*   %add21.2.1 = add i16 %515, %call.i.2.1 *)
add v_add21_2_1 v515 v_call_i_2_1;
(*   store i16 %add21.2.1, i16* %arrayidx11.2.1, align 2, !tbaa !3 *)
mov mem0_2 v_add21_2_1;
(*   %arrayidx9.2.2 = getelementptr inbounds i16, i16* %r, i64 34 *)
(*   %516 = load i16, i16* %arrayidx9.2.2, align 2, !tbaa !3 *)
mov v516 mem0_68;
(*   %conv1.i.2.2 = sext i16 %516 to i32 *)
cast v_conv1_i_2_2@sint32 v516@sint16;
(*   %mul.i.2.2 = mul nsw i32 %conv1.i.2.2, 1493 *)
mul v_mul_i_2_2 v_conv1_i_2_2 (1493)@sint32;
(*   %call.i.2.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_2, v_call_i_2_2);
(*   %arrayidx11.2.2 = getelementptr inbounds i16, i16* %r, i64 2 *)
(*   %517 = load i16, i16* %arrayidx11.2.2, align 2, !tbaa !3 *)
mov v517 mem0_4;
(*   %sub.2.2 = sub i16 %517, %call.i.2.2 *)
sub v_sub_2_2 v517 v_call_i_2_2;
(*   store i16 %sub.2.2, i16* %arrayidx9.2.2, align 2, !tbaa !3 *)
mov mem0_68 v_sub_2_2;
(*   %add21.2.2 = add i16 %517, %call.i.2.2 *)
add v_add21_2_2 v517 v_call_i_2_2;
(*   store i16 %add21.2.2, i16* %arrayidx11.2.2, align 2, !tbaa !3 *)
mov mem0_4 v_add21_2_2;
(*   %arrayidx9.2.3 = getelementptr inbounds i16, i16* %r, i64 35 *)
(*   %518 = load i16, i16* %arrayidx9.2.3, align 2, !tbaa !3 *)
mov v518 mem0_70;
(*   %conv1.i.2.3 = sext i16 %518 to i32 *)
cast v_conv1_i_2_3@sint32 v518@sint16;
(*   %mul.i.2.3 = mul nsw i32 %conv1.i.2.3, 1493 *)
mul v_mul_i_2_3 v_conv1_i_2_3 (1493)@sint32;
(*   %call.i.2.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_3, v_call_i_2_3);
(*   %arrayidx11.2.3 = getelementptr inbounds i16, i16* %r, i64 3 *)
(*   %519 = load i16, i16* %arrayidx11.2.3, align 2, !tbaa !3 *)
mov v519 mem0_6;
(*   %sub.2.3 = sub i16 %519, %call.i.2.3 *)
sub v_sub_2_3 v519 v_call_i_2_3;
(*   store i16 %sub.2.3, i16* %arrayidx9.2.3, align 2, !tbaa !3 *)
mov mem0_70 v_sub_2_3;
(*   %add21.2.3 = add i16 %519, %call.i.2.3 *)
add v_add21_2_3 v519 v_call_i_2_3;
(*   store i16 %add21.2.3, i16* %arrayidx11.2.3, align 2, !tbaa !3 *)
mov mem0_6 v_add21_2_3;
(*   %arrayidx9.2.4 = getelementptr inbounds i16, i16* %r, i64 36 *)
(*   %520 = load i16, i16* %arrayidx9.2.4, align 2, !tbaa !3 *)
mov v520 mem0_72;
(*   %conv1.i.2.4 = sext i16 %520 to i32 *)
cast v_conv1_i_2_4@sint32 v520@sint16;
(*   %mul.i.2.4 = mul nsw i32 %conv1.i.2.4, 1493 *)
mul v_mul_i_2_4 v_conv1_i_2_4 (1493)@sint32;
(*   %call.i.2.4 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.4) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_4, v_call_i_2_4);
(*   %arrayidx11.2.4 = getelementptr inbounds i16, i16* %r, i64 4 *)
(*   %521 = load i16, i16* %arrayidx11.2.4, align 2, !tbaa !3 *)
mov v521 mem0_8;
(*   %sub.2.4 = sub i16 %521, %call.i.2.4 *)
sub v_sub_2_4 v521 v_call_i_2_4;
(*   store i16 %sub.2.4, i16* %arrayidx9.2.4, align 2, !tbaa !3 *)
mov mem0_72 v_sub_2_4;
(*   %add21.2.4 = add i16 %521, %call.i.2.4 *)
add v_add21_2_4 v521 v_call_i_2_4;
(*   store i16 %add21.2.4, i16* %arrayidx11.2.4, align 2, !tbaa !3 *)
mov mem0_8 v_add21_2_4;
(*   %arrayidx9.2.5 = getelementptr inbounds i16, i16* %r, i64 37 *)
(*   %522 = load i16, i16* %arrayidx9.2.5, align 2, !tbaa !3 *)
mov v522 mem0_74;
(*   %conv1.i.2.5 = sext i16 %522 to i32 *)
cast v_conv1_i_2_5@sint32 v522@sint16;
(*   %mul.i.2.5 = mul nsw i32 %conv1.i.2.5, 1493 *)
mul v_mul_i_2_5 v_conv1_i_2_5 (1493)@sint32;
(*   %call.i.2.5 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.5) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_5, v_call_i_2_5);
(*   %arrayidx11.2.5 = getelementptr inbounds i16, i16* %r, i64 5 *)
(*   %523 = load i16, i16* %arrayidx11.2.5, align 2, !tbaa !3 *)
mov v523 mem0_10;
(*   %sub.2.5 = sub i16 %523, %call.i.2.5 *)
sub v_sub_2_5 v523 v_call_i_2_5;
(*   store i16 %sub.2.5, i16* %arrayidx9.2.5, align 2, !tbaa !3 *)
mov mem0_74 v_sub_2_5;
(*   %add21.2.5 = add i16 %523, %call.i.2.5 *)
add v_add21_2_5 v523 v_call_i_2_5;
(*   store i16 %add21.2.5, i16* %arrayidx11.2.5, align 2, !tbaa !3 *)
mov mem0_10 v_add21_2_5;
(*   %arrayidx9.2.6 = getelementptr inbounds i16, i16* %r, i64 38 *)
(*   %524 = load i16, i16* %arrayidx9.2.6, align 2, !tbaa !3 *)
mov v524 mem0_76;
(*   %conv1.i.2.6 = sext i16 %524 to i32 *)
cast v_conv1_i_2_6@sint32 v524@sint16;
(*   %mul.i.2.6 = mul nsw i32 %conv1.i.2.6, 1493 *)
mul v_mul_i_2_6 v_conv1_i_2_6 (1493)@sint32;
(*   %call.i.2.6 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.6) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_6, v_call_i_2_6);
(*   %arrayidx11.2.6 = getelementptr inbounds i16, i16* %r, i64 6 *)
(*   %525 = load i16, i16* %arrayidx11.2.6, align 2, !tbaa !3 *)
mov v525 mem0_12;
(*   %sub.2.6 = sub i16 %525, %call.i.2.6 *)
sub v_sub_2_6 v525 v_call_i_2_6;
(*   store i16 %sub.2.6, i16* %arrayidx9.2.6, align 2, !tbaa !3 *)
mov mem0_76 v_sub_2_6;
(*   %add21.2.6 = add i16 %525, %call.i.2.6 *)
add v_add21_2_6 v525 v_call_i_2_6;
(*   store i16 %add21.2.6, i16* %arrayidx11.2.6, align 2, !tbaa !3 *)
mov mem0_12 v_add21_2_6;
(*   %arrayidx9.2.7 = getelementptr inbounds i16, i16* %r, i64 39 *)
(*   %526 = load i16, i16* %arrayidx9.2.7, align 2, !tbaa !3 *)
mov v526 mem0_78;
(*   %conv1.i.2.7 = sext i16 %526 to i32 *)
cast v_conv1_i_2_7@sint32 v526@sint16;
(*   %mul.i.2.7 = mul nsw i32 %conv1.i.2.7, 1493 *)
mul v_mul_i_2_7 v_conv1_i_2_7 (1493)@sint32;
(*   %call.i.2.7 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.7) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_7, v_call_i_2_7);
(*   %arrayidx11.2.7 = getelementptr inbounds i16, i16* %r, i64 7 *)
(*   %527 = load i16, i16* %arrayidx11.2.7, align 2, !tbaa !3 *)
mov v527 mem0_14;
(*   %sub.2.7 = sub i16 %527, %call.i.2.7 *)
sub v_sub_2_7 v527 v_call_i_2_7;
(*   store i16 %sub.2.7, i16* %arrayidx9.2.7, align 2, !tbaa !3 *)
mov mem0_78 v_sub_2_7;
(*   %add21.2.7 = add i16 %527, %call.i.2.7 *)
add v_add21_2_7 v527 v_call_i_2_7;
(*   store i16 %add21.2.7, i16* %arrayidx11.2.7, align 2, !tbaa !3 *)
mov mem0_14 v_add21_2_7;
(*   %arrayidx9.2.8 = getelementptr inbounds i16, i16* %r, i64 40 *)
(*   %528 = load i16, i16* %arrayidx9.2.8, align 2, !tbaa !3 *)
mov v528 mem0_80;
(*   %conv1.i.2.8 = sext i16 %528 to i32 *)
cast v_conv1_i_2_8@sint32 v528@sint16;
(*   %mul.i.2.8 = mul nsw i32 %conv1.i.2.8, 1493 *)
mul v_mul_i_2_8 v_conv1_i_2_8 (1493)@sint32;
(*   %call.i.2.8 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.8) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_8, v_call_i_2_8);
(*   %arrayidx11.2.8 = getelementptr inbounds i16, i16* %r, i64 8 *)
(*   %529 = load i16, i16* %arrayidx11.2.8, align 2, !tbaa !3 *)
mov v529 mem0_16;
(*   %sub.2.8 = sub i16 %529, %call.i.2.8 *)
sub v_sub_2_8 v529 v_call_i_2_8;
(*   store i16 %sub.2.8, i16* %arrayidx9.2.8, align 2, !tbaa !3 *)
mov mem0_80 v_sub_2_8;
(*   %add21.2.8 = add i16 %529, %call.i.2.8 *)
add v_add21_2_8 v529 v_call_i_2_8;
(*   store i16 %add21.2.8, i16* %arrayidx11.2.8, align 2, !tbaa !3 *)
mov mem0_16 v_add21_2_8;
(*   %arrayidx9.2.9 = getelementptr inbounds i16, i16* %r, i64 41 *)
(*   %530 = load i16, i16* %arrayidx9.2.9, align 2, !tbaa !3 *)
mov v530 mem0_82;
(*   %conv1.i.2.9 = sext i16 %530 to i32 *)
cast v_conv1_i_2_9@sint32 v530@sint16;
(*   %mul.i.2.9 = mul nsw i32 %conv1.i.2.9, 1493 *)
mul v_mul_i_2_9 v_conv1_i_2_9 (1493)@sint32;
(*   %call.i.2.9 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.9) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_9, v_call_i_2_9);
(*   %arrayidx11.2.9 = getelementptr inbounds i16, i16* %r, i64 9 *)
(*   %531 = load i16, i16* %arrayidx11.2.9, align 2, !tbaa !3 *)
mov v531 mem0_18;
(*   %sub.2.9 = sub i16 %531, %call.i.2.9 *)
sub v_sub_2_9 v531 v_call_i_2_9;
(*   store i16 %sub.2.9, i16* %arrayidx9.2.9, align 2, !tbaa !3 *)
mov mem0_82 v_sub_2_9;
(*   %add21.2.9 = add i16 %531, %call.i.2.9 *)
add v_add21_2_9 v531 v_call_i_2_9;
(*   store i16 %add21.2.9, i16* %arrayidx11.2.9, align 2, !tbaa !3 *)
mov mem0_18 v_add21_2_9;
(*   %arrayidx9.2.10 = getelementptr inbounds i16, i16* %r, i64 42 *)
(*   %532 = load i16, i16* %arrayidx9.2.10, align 2, !tbaa !3 *)
mov v532 mem0_84;
(*   %conv1.i.2.10 = sext i16 %532 to i32 *)
cast v_conv1_i_2_10@sint32 v532@sint16;
(*   %mul.i.2.10 = mul nsw i32 %conv1.i.2.10, 1493 *)
mul v_mul_i_2_10 v_conv1_i_2_10 (1493)@sint32;
(*   %call.i.2.10 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.10) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_10, v_call_i_2_10);
(*   %arrayidx11.2.10 = getelementptr inbounds i16, i16* %r, i64 10 *)
(*   %533 = load i16, i16* %arrayidx11.2.10, align 2, !tbaa !3 *)
mov v533 mem0_20;
(*   %sub.2.10 = sub i16 %533, %call.i.2.10 *)
sub v_sub_2_10 v533 v_call_i_2_10;
(*   store i16 %sub.2.10, i16* %arrayidx9.2.10, align 2, !tbaa !3 *)
mov mem0_84 v_sub_2_10;
(*   %add21.2.10 = add i16 %533, %call.i.2.10 *)
add v_add21_2_10 v533 v_call_i_2_10;
(*   store i16 %add21.2.10, i16* %arrayidx11.2.10, align 2, !tbaa !3 *)
mov mem0_20 v_add21_2_10;
(*   %arrayidx9.2.11 = getelementptr inbounds i16, i16* %r, i64 43 *)
(*   %534 = load i16, i16* %arrayidx9.2.11, align 2, !tbaa !3 *)
mov v534 mem0_86;
(*   %conv1.i.2.11 = sext i16 %534 to i32 *)
cast v_conv1_i_2_11@sint32 v534@sint16;
(*   %mul.i.2.11 = mul nsw i32 %conv1.i.2.11, 1493 *)
mul v_mul_i_2_11 v_conv1_i_2_11 (1493)@sint32;
(*   %call.i.2.11 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.11) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_11, v_call_i_2_11);
(*   %arrayidx11.2.11 = getelementptr inbounds i16, i16* %r, i64 11 *)
(*   %535 = load i16, i16* %arrayidx11.2.11, align 2, !tbaa !3 *)
mov v535 mem0_22;
(*   %sub.2.11 = sub i16 %535, %call.i.2.11 *)
sub v_sub_2_11 v535 v_call_i_2_11;
(*   store i16 %sub.2.11, i16* %arrayidx9.2.11, align 2, !tbaa !3 *)
mov mem0_86 v_sub_2_11;
(*   %add21.2.11 = add i16 %535, %call.i.2.11 *)
add v_add21_2_11 v535 v_call_i_2_11;
(*   store i16 %add21.2.11, i16* %arrayidx11.2.11, align 2, !tbaa !3 *)
mov mem0_22 v_add21_2_11;
(*   %arrayidx9.2.12 = getelementptr inbounds i16, i16* %r, i64 44 *)
(*   %536 = load i16, i16* %arrayidx9.2.12, align 2, !tbaa !3 *)
mov v536 mem0_88;
(*   %conv1.i.2.12 = sext i16 %536 to i32 *)
cast v_conv1_i_2_12@sint32 v536@sint16;
(*   %mul.i.2.12 = mul nsw i32 %conv1.i.2.12, 1493 *)
mul v_mul_i_2_12 v_conv1_i_2_12 (1493)@sint32;
(*   %call.i.2.12 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.12) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_12, v_call_i_2_12);
(*   %arrayidx11.2.12 = getelementptr inbounds i16, i16* %r, i64 12 *)
(*   %537 = load i16, i16* %arrayidx11.2.12, align 2, !tbaa !3 *)
mov v537 mem0_24;
(*   %sub.2.12 = sub i16 %537, %call.i.2.12 *)
sub v_sub_2_12 v537 v_call_i_2_12;
(*   store i16 %sub.2.12, i16* %arrayidx9.2.12, align 2, !tbaa !3 *)
mov mem0_88 v_sub_2_12;
(*   %add21.2.12 = add i16 %537, %call.i.2.12 *)
add v_add21_2_12 v537 v_call_i_2_12;
(*   store i16 %add21.2.12, i16* %arrayidx11.2.12, align 2, !tbaa !3 *)
mov mem0_24 v_add21_2_12;
(*   %arrayidx9.2.13 = getelementptr inbounds i16, i16* %r, i64 45 *)
(*   %538 = load i16, i16* %arrayidx9.2.13, align 2, !tbaa !3 *)
mov v538 mem0_90;
(*   %conv1.i.2.13 = sext i16 %538 to i32 *)
cast v_conv1_i_2_13@sint32 v538@sint16;
(*   %mul.i.2.13 = mul nsw i32 %conv1.i.2.13, 1493 *)
mul v_mul_i_2_13 v_conv1_i_2_13 (1493)@sint32;
(*   %call.i.2.13 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.13) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_13, v_call_i_2_13);
(*   %arrayidx11.2.13 = getelementptr inbounds i16, i16* %r, i64 13 *)
(*   %539 = load i16, i16* %arrayidx11.2.13, align 2, !tbaa !3 *)
mov v539 mem0_26;
(*   %sub.2.13 = sub i16 %539, %call.i.2.13 *)
sub v_sub_2_13 v539 v_call_i_2_13;
(*   store i16 %sub.2.13, i16* %arrayidx9.2.13, align 2, !tbaa !3 *)
mov mem0_90 v_sub_2_13;
(*   %add21.2.13 = add i16 %539, %call.i.2.13 *)
add v_add21_2_13 v539 v_call_i_2_13;
(*   store i16 %add21.2.13, i16* %arrayidx11.2.13, align 2, !tbaa !3 *)
mov mem0_26 v_add21_2_13;
(*   %arrayidx9.2.14 = getelementptr inbounds i16, i16* %r, i64 46 *)
(*   %540 = load i16, i16* %arrayidx9.2.14, align 2, !tbaa !3 *)
mov v540 mem0_92;
(*   %conv1.i.2.14 = sext i16 %540 to i32 *)
cast v_conv1_i_2_14@sint32 v540@sint16;
(*   %mul.i.2.14 = mul nsw i32 %conv1.i.2.14, 1493 *)
mul v_mul_i_2_14 v_conv1_i_2_14 (1493)@sint32;
(*   %call.i.2.14 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.14) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_14, v_call_i_2_14);
(*   %arrayidx11.2.14 = getelementptr inbounds i16, i16* %r, i64 14 *)
(*   %541 = load i16, i16* %arrayidx11.2.14, align 2, !tbaa !3 *)
mov v541 mem0_28;
(*   %sub.2.14 = sub i16 %541, %call.i.2.14 *)
sub v_sub_2_14 v541 v_call_i_2_14;
(*   store i16 %sub.2.14, i16* %arrayidx9.2.14, align 2, !tbaa !3 *)
mov mem0_92 v_sub_2_14;
(*   %add21.2.14 = add i16 %541, %call.i.2.14 *)
add v_add21_2_14 v541 v_call_i_2_14;
(*   store i16 %add21.2.14, i16* %arrayidx11.2.14, align 2, !tbaa !3 *)
mov mem0_28 v_add21_2_14;
(*   %arrayidx9.2.15 = getelementptr inbounds i16, i16* %r, i64 47 *)
(*   %542 = load i16, i16* %arrayidx9.2.15, align 2, !tbaa !3 *)
mov v542 mem0_94;
(*   %conv1.i.2.15 = sext i16 %542 to i32 *)
cast v_conv1_i_2_15@sint32 v542@sint16;
(*   %mul.i.2.15 = mul nsw i32 %conv1.i.2.15, 1493 *)
mul v_mul_i_2_15 v_conv1_i_2_15 (1493)@sint32;
(*   %call.i.2.15 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.15) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_15, v_call_i_2_15);
(*   %arrayidx11.2.15 = getelementptr inbounds i16, i16* %r, i64 15 *)
(*   %543 = load i16, i16* %arrayidx11.2.15, align 2, !tbaa !3 *)
mov v543 mem0_30;
(*   %sub.2.15 = sub i16 %543, %call.i.2.15 *)
sub v_sub_2_15 v543 v_call_i_2_15;
(*   store i16 %sub.2.15, i16* %arrayidx9.2.15, align 2, !tbaa !3 *)
mov mem0_94 v_sub_2_15;
(*   %add21.2.15 = add i16 %543, %call.i.2.15 *)
add v_add21_2_15 v543 v_call_i_2_15;
(*   store i16 %add21.2.15, i16* %arrayidx11.2.15, align 2, !tbaa !3 *)
mov mem0_30 v_add21_2_15;
(*   %arrayidx9.2.16 = getelementptr inbounds i16, i16* %r, i64 48 *)
(*   %544 = load i16, i16* %arrayidx9.2.16, align 2, !tbaa !3 *)
mov v544 mem0_96;
(*   %conv1.i.2.16 = sext i16 %544 to i32 *)
cast v_conv1_i_2_16@sint32 v544@sint16;
(*   %mul.i.2.16 = mul nsw i32 %conv1.i.2.16, 1493 *)
mul v_mul_i_2_16 v_conv1_i_2_16 (1493)@sint32;
(*   %call.i.2.16 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.16) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_16, v_call_i_2_16);
(*   %arrayidx11.2.16 = getelementptr inbounds i16, i16* %r, i64 16 *)
(*   %545 = load i16, i16* %arrayidx11.2.16, align 2, !tbaa !3 *)
mov v545 mem0_32;
(*   %sub.2.16 = sub i16 %545, %call.i.2.16 *)
sub v_sub_2_16 v545 v_call_i_2_16;
(*   store i16 %sub.2.16, i16* %arrayidx9.2.16, align 2, !tbaa !3 *)
mov mem0_96 v_sub_2_16;
(*   %add21.2.16 = add i16 %545, %call.i.2.16 *)
add v_add21_2_16 v545 v_call_i_2_16;
(*   store i16 %add21.2.16, i16* %arrayidx11.2.16, align 2, !tbaa !3 *)
mov mem0_32 v_add21_2_16;
(*   %arrayidx9.2.17 = getelementptr inbounds i16, i16* %r, i64 49 *)
(*   %546 = load i16, i16* %arrayidx9.2.17, align 2, !tbaa !3 *)
mov v546 mem0_98;
(*   %conv1.i.2.17 = sext i16 %546 to i32 *)
cast v_conv1_i_2_17@sint32 v546@sint16;
(*   %mul.i.2.17 = mul nsw i32 %conv1.i.2.17, 1493 *)
mul v_mul_i_2_17 v_conv1_i_2_17 (1493)@sint32;
(*   %call.i.2.17 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.17) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_17, v_call_i_2_17);
(*   %arrayidx11.2.17 = getelementptr inbounds i16, i16* %r, i64 17 *)
(*   %547 = load i16, i16* %arrayidx11.2.17, align 2, !tbaa !3 *)
mov v547 mem0_34;
(*   %sub.2.17 = sub i16 %547, %call.i.2.17 *)
sub v_sub_2_17 v547 v_call_i_2_17;
(*   store i16 %sub.2.17, i16* %arrayidx9.2.17, align 2, !tbaa !3 *)
mov mem0_98 v_sub_2_17;
(*   %add21.2.17 = add i16 %547, %call.i.2.17 *)
add v_add21_2_17 v547 v_call_i_2_17;
(*   store i16 %add21.2.17, i16* %arrayidx11.2.17, align 2, !tbaa !3 *)
mov mem0_34 v_add21_2_17;
(*   %arrayidx9.2.18 = getelementptr inbounds i16, i16* %r, i64 50 *)
(*   %548 = load i16, i16* %arrayidx9.2.18, align 2, !tbaa !3 *)
mov v548 mem0_100;
(*   %conv1.i.2.18 = sext i16 %548 to i32 *)
cast v_conv1_i_2_18@sint32 v548@sint16;
(*   %mul.i.2.18 = mul nsw i32 %conv1.i.2.18, 1493 *)
mul v_mul_i_2_18 v_conv1_i_2_18 (1493)@sint32;
(*   %call.i.2.18 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.18) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_18, v_call_i_2_18);
(*   %arrayidx11.2.18 = getelementptr inbounds i16, i16* %r, i64 18 *)
(*   %549 = load i16, i16* %arrayidx11.2.18, align 2, !tbaa !3 *)
mov v549 mem0_36;
(*   %sub.2.18 = sub i16 %549, %call.i.2.18 *)
sub v_sub_2_18 v549 v_call_i_2_18;
(*   store i16 %sub.2.18, i16* %arrayidx9.2.18, align 2, !tbaa !3 *)
mov mem0_100 v_sub_2_18;
(*   %add21.2.18 = add i16 %549, %call.i.2.18 *)
add v_add21_2_18 v549 v_call_i_2_18;
(*   store i16 %add21.2.18, i16* %arrayidx11.2.18, align 2, !tbaa !3 *)
mov mem0_36 v_add21_2_18;
(*   %arrayidx9.2.19 = getelementptr inbounds i16, i16* %r, i64 51 *)
(*   %550 = load i16, i16* %arrayidx9.2.19, align 2, !tbaa !3 *)
mov v550 mem0_102;
(*   %conv1.i.2.19 = sext i16 %550 to i32 *)
cast v_conv1_i_2_19@sint32 v550@sint16;
(*   %mul.i.2.19 = mul nsw i32 %conv1.i.2.19, 1493 *)
mul v_mul_i_2_19 v_conv1_i_2_19 (1493)@sint32;
(*   %call.i.2.19 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.19) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_19, v_call_i_2_19);
(*   %arrayidx11.2.19 = getelementptr inbounds i16, i16* %r, i64 19 *)
(*   %551 = load i16, i16* %arrayidx11.2.19, align 2, !tbaa !3 *)
mov v551 mem0_38;
(*   %sub.2.19 = sub i16 %551, %call.i.2.19 *)
sub v_sub_2_19 v551 v_call_i_2_19;
(*   store i16 %sub.2.19, i16* %arrayidx9.2.19, align 2, !tbaa !3 *)
mov mem0_102 v_sub_2_19;
(*   %add21.2.19 = add i16 %551, %call.i.2.19 *)
add v_add21_2_19 v551 v_call_i_2_19;
(*   store i16 %add21.2.19, i16* %arrayidx11.2.19, align 2, !tbaa !3 *)
mov mem0_38 v_add21_2_19;
(*   %arrayidx9.2.20 = getelementptr inbounds i16, i16* %r, i64 52 *)
(*   %552 = load i16, i16* %arrayidx9.2.20, align 2, !tbaa !3 *)
mov v552 mem0_104;
(*   %conv1.i.2.20 = sext i16 %552 to i32 *)
cast v_conv1_i_2_20@sint32 v552@sint16;
(*   %mul.i.2.20 = mul nsw i32 %conv1.i.2.20, 1493 *)
mul v_mul_i_2_20 v_conv1_i_2_20 (1493)@sint32;
(*   %call.i.2.20 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.20) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_20, v_call_i_2_20);
(*   %arrayidx11.2.20 = getelementptr inbounds i16, i16* %r, i64 20 *)
(*   %553 = load i16, i16* %arrayidx11.2.20, align 2, !tbaa !3 *)
mov v553 mem0_40;
(*   %sub.2.20 = sub i16 %553, %call.i.2.20 *)
sub v_sub_2_20 v553 v_call_i_2_20;
(*   store i16 %sub.2.20, i16* %arrayidx9.2.20, align 2, !tbaa !3 *)
mov mem0_104 v_sub_2_20;
(*   %add21.2.20 = add i16 %553, %call.i.2.20 *)
add v_add21_2_20 v553 v_call_i_2_20;
(*   store i16 %add21.2.20, i16* %arrayidx11.2.20, align 2, !tbaa !3 *)
mov mem0_40 v_add21_2_20;
(*   %arrayidx9.2.21 = getelementptr inbounds i16, i16* %r, i64 53 *)
(*   %554 = load i16, i16* %arrayidx9.2.21, align 2, !tbaa !3 *)
mov v554 mem0_106;
(*   %conv1.i.2.21 = sext i16 %554 to i32 *)
cast v_conv1_i_2_21@sint32 v554@sint16;
(*   %mul.i.2.21 = mul nsw i32 %conv1.i.2.21, 1493 *)
mul v_mul_i_2_21 v_conv1_i_2_21 (1493)@sint32;
(*   %call.i.2.21 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.21) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_21, v_call_i_2_21);
(*   %arrayidx11.2.21 = getelementptr inbounds i16, i16* %r, i64 21 *)
(*   %555 = load i16, i16* %arrayidx11.2.21, align 2, !tbaa !3 *)
mov v555 mem0_42;
(*   %sub.2.21 = sub i16 %555, %call.i.2.21 *)
sub v_sub_2_21 v555 v_call_i_2_21;
(*   store i16 %sub.2.21, i16* %arrayidx9.2.21, align 2, !tbaa !3 *)
mov mem0_106 v_sub_2_21;
(*   %add21.2.21 = add i16 %555, %call.i.2.21 *)
add v_add21_2_21 v555 v_call_i_2_21;
(*   store i16 %add21.2.21, i16* %arrayidx11.2.21, align 2, !tbaa !3 *)
mov mem0_42 v_add21_2_21;
(*   %arrayidx9.2.22 = getelementptr inbounds i16, i16* %r, i64 54 *)
(*   %556 = load i16, i16* %arrayidx9.2.22, align 2, !tbaa !3 *)
mov v556 mem0_108;
(*   %conv1.i.2.22 = sext i16 %556 to i32 *)
cast v_conv1_i_2_22@sint32 v556@sint16;
(*   %mul.i.2.22 = mul nsw i32 %conv1.i.2.22, 1493 *)
mul v_mul_i_2_22 v_conv1_i_2_22 (1493)@sint32;
(*   %call.i.2.22 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.22) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_22, v_call_i_2_22);
(*   %arrayidx11.2.22 = getelementptr inbounds i16, i16* %r, i64 22 *)
(*   %557 = load i16, i16* %arrayidx11.2.22, align 2, !tbaa !3 *)
mov v557 mem0_44;
(*   %sub.2.22 = sub i16 %557, %call.i.2.22 *)
sub v_sub_2_22 v557 v_call_i_2_22;
(*   store i16 %sub.2.22, i16* %arrayidx9.2.22, align 2, !tbaa !3 *)
mov mem0_108 v_sub_2_22;
(*   %add21.2.22 = add i16 %557, %call.i.2.22 *)
add v_add21_2_22 v557 v_call_i_2_22;
(*   store i16 %add21.2.22, i16* %arrayidx11.2.22, align 2, !tbaa !3 *)
mov mem0_44 v_add21_2_22;
(*   %arrayidx9.2.23 = getelementptr inbounds i16, i16* %r, i64 55 *)
(*   %558 = load i16, i16* %arrayidx9.2.23, align 2, !tbaa !3 *)
mov v558 mem0_110;
(*   %conv1.i.2.23 = sext i16 %558 to i32 *)
cast v_conv1_i_2_23@sint32 v558@sint16;
(*   %mul.i.2.23 = mul nsw i32 %conv1.i.2.23, 1493 *)
mul v_mul_i_2_23 v_conv1_i_2_23 (1493)@sint32;
(*   %call.i.2.23 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.23) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_23, v_call_i_2_23);
(*   %arrayidx11.2.23 = getelementptr inbounds i16, i16* %r, i64 23 *)
(*   %559 = load i16, i16* %arrayidx11.2.23, align 2, !tbaa !3 *)
mov v559 mem0_46;
(*   %sub.2.23 = sub i16 %559, %call.i.2.23 *)
sub v_sub_2_23 v559 v_call_i_2_23;
(*   store i16 %sub.2.23, i16* %arrayidx9.2.23, align 2, !tbaa !3 *)
mov mem0_110 v_sub_2_23;
(*   %add21.2.23 = add i16 %559, %call.i.2.23 *)
add v_add21_2_23 v559 v_call_i_2_23;
(*   store i16 %add21.2.23, i16* %arrayidx11.2.23, align 2, !tbaa !3 *)
mov mem0_46 v_add21_2_23;
(*   %arrayidx9.2.24 = getelementptr inbounds i16, i16* %r, i64 56 *)
(*   %560 = load i16, i16* %arrayidx9.2.24, align 2, !tbaa !3 *)
mov v560 mem0_112;
(*   %conv1.i.2.24 = sext i16 %560 to i32 *)
cast v_conv1_i_2_24@sint32 v560@sint16;
(*   %mul.i.2.24 = mul nsw i32 %conv1.i.2.24, 1493 *)
mul v_mul_i_2_24 v_conv1_i_2_24 (1493)@sint32;
(*   %call.i.2.24 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.24) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_24, v_call_i_2_24);
(*   %arrayidx11.2.24 = getelementptr inbounds i16, i16* %r, i64 24 *)
(*   %561 = load i16, i16* %arrayidx11.2.24, align 2, !tbaa !3 *)
mov v561 mem0_48;
(*   %sub.2.24 = sub i16 %561, %call.i.2.24 *)
sub v_sub_2_24 v561 v_call_i_2_24;
(*   store i16 %sub.2.24, i16* %arrayidx9.2.24, align 2, !tbaa !3 *)
mov mem0_112 v_sub_2_24;
(*   %add21.2.24 = add i16 %561, %call.i.2.24 *)
add v_add21_2_24 v561 v_call_i_2_24;
(*   store i16 %add21.2.24, i16* %arrayidx11.2.24, align 2, !tbaa !3 *)
mov mem0_48 v_add21_2_24;
(*   %arrayidx9.2.25 = getelementptr inbounds i16, i16* %r, i64 57 *)
(*   %562 = load i16, i16* %arrayidx9.2.25, align 2, !tbaa !3 *)
mov v562 mem0_114;
(*   %conv1.i.2.25 = sext i16 %562 to i32 *)
cast v_conv1_i_2_25@sint32 v562@sint16;
(*   %mul.i.2.25 = mul nsw i32 %conv1.i.2.25, 1493 *)
mul v_mul_i_2_25 v_conv1_i_2_25 (1493)@sint32;
(*   %call.i.2.25 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.25) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_25, v_call_i_2_25);
(*   %arrayidx11.2.25 = getelementptr inbounds i16, i16* %r, i64 25 *)
(*   %563 = load i16, i16* %arrayidx11.2.25, align 2, !tbaa !3 *)
mov v563 mem0_50;
(*   %sub.2.25 = sub i16 %563, %call.i.2.25 *)
sub v_sub_2_25 v563 v_call_i_2_25;
(*   store i16 %sub.2.25, i16* %arrayidx9.2.25, align 2, !tbaa !3 *)
mov mem0_114 v_sub_2_25;
(*   %add21.2.25 = add i16 %563, %call.i.2.25 *)
add v_add21_2_25 v563 v_call_i_2_25;
(*   store i16 %add21.2.25, i16* %arrayidx11.2.25, align 2, !tbaa !3 *)
mov mem0_50 v_add21_2_25;
(*   %arrayidx9.2.26 = getelementptr inbounds i16, i16* %r, i64 58 *)
(*   %564 = load i16, i16* %arrayidx9.2.26, align 2, !tbaa !3 *)
mov v564 mem0_116;
(*   %conv1.i.2.26 = sext i16 %564 to i32 *)
cast v_conv1_i_2_26@sint32 v564@sint16;
(*   %mul.i.2.26 = mul nsw i32 %conv1.i.2.26, 1493 *)
mul v_mul_i_2_26 v_conv1_i_2_26 (1493)@sint32;
(*   %call.i.2.26 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.26) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_26, v_call_i_2_26);
(*   %arrayidx11.2.26 = getelementptr inbounds i16, i16* %r, i64 26 *)
(*   %565 = load i16, i16* %arrayidx11.2.26, align 2, !tbaa !3 *)
mov v565 mem0_52;
(*   %sub.2.26 = sub i16 %565, %call.i.2.26 *)
sub v_sub_2_26 v565 v_call_i_2_26;
(*   store i16 %sub.2.26, i16* %arrayidx9.2.26, align 2, !tbaa !3 *)
mov mem0_116 v_sub_2_26;
(*   %add21.2.26 = add i16 %565, %call.i.2.26 *)
add v_add21_2_26 v565 v_call_i_2_26;
(*   store i16 %add21.2.26, i16* %arrayidx11.2.26, align 2, !tbaa !3 *)
mov mem0_52 v_add21_2_26;
(*   %arrayidx9.2.27 = getelementptr inbounds i16, i16* %r, i64 59 *)
(*   %566 = load i16, i16* %arrayidx9.2.27, align 2, !tbaa !3 *)
mov v566 mem0_118;
(*   %conv1.i.2.27 = sext i16 %566 to i32 *)
cast v_conv1_i_2_27@sint32 v566@sint16;
(*   %mul.i.2.27 = mul nsw i32 %conv1.i.2.27, 1493 *)
mul v_mul_i_2_27 v_conv1_i_2_27 (1493)@sint32;
(*   %call.i.2.27 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.27) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_27, v_call_i_2_27);
(*   %arrayidx11.2.27 = getelementptr inbounds i16, i16* %r, i64 27 *)
(*   %567 = load i16, i16* %arrayidx11.2.27, align 2, !tbaa !3 *)
mov v567 mem0_54;
(*   %sub.2.27 = sub i16 %567, %call.i.2.27 *)
sub v_sub_2_27 v567 v_call_i_2_27;
(*   store i16 %sub.2.27, i16* %arrayidx9.2.27, align 2, !tbaa !3 *)
mov mem0_118 v_sub_2_27;
(*   %add21.2.27 = add i16 %567, %call.i.2.27 *)
add v_add21_2_27 v567 v_call_i_2_27;
(*   store i16 %add21.2.27, i16* %arrayidx11.2.27, align 2, !tbaa !3 *)
mov mem0_54 v_add21_2_27;
(*   %arrayidx9.2.28 = getelementptr inbounds i16, i16* %r, i64 60 *)
(*   %568 = load i16, i16* %arrayidx9.2.28, align 2, !tbaa !3 *)
mov v568 mem0_120;
(*   %conv1.i.2.28 = sext i16 %568 to i32 *)
cast v_conv1_i_2_28@sint32 v568@sint16;
(*   %mul.i.2.28 = mul nsw i32 %conv1.i.2.28, 1493 *)
mul v_mul_i_2_28 v_conv1_i_2_28 (1493)@sint32;
(*   %call.i.2.28 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.28) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_28, v_call_i_2_28);
(*   %arrayidx11.2.28 = getelementptr inbounds i16, i16* %r, i64 28 *)
(*   %569 = load i16, i16* %arrayidx11.2.28, align 2, !tbaa !3 *)
mov v569 mem0_56;
(*   %sub.2.28 = sub i16 %569, %call.i.2.28 *)
sub v_sub_2_28 v569 v_call_i_2_28;
(*   store i16 %sub.2.28, i16* %arrayidx9.2.28, align 2, !tbaa !3 *)
mov mem0_120 v_sub_2_28;
(*   %add21.2.28 = add i16 %569, %call.i.2.28 *)
add v_add21_2_28 v569 v_call_i_2_28;
(*   store i16 %add21.2.28, i16* %arrayidx11.2.28, align 2, !tbaa !3 *)
mov mem0_56 v_add21_2_28;
(*   %arrayidx9.2.29 = getelementptr inbounds i16, i16* %r, i64 61 *)
(*   %570 = load i16, i16* %arrayidx9.2.29, align 2, !tbaa !3 *)
mov v570 mem0_122;
(*   %conv1.i.2.29 = sext i16 %570 to i32 *)
cast v_conv1_i_2_29@sint32 v570@sint16;
(*   %mul.i.2.29 = mul nsw i32 %conv1.i.2.29, 1493 *)
mul v_mul_i_2_29 v_conv1_i_2_29 (1493)@sint32;
(*   %call.i.2.29 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.29) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_29, v_call_i_2_29);
(*   %arrayidx11.2.29 = getelementptr inbounds i16, i16* %r, i64 29 *)
(*   %571 = load i16, i16* %arrayidx11.2.29, align 2, !tbaa !3 *)
mov v571 mem0_58;
(*   %sub.2.29 = sub i16 %571, %call.i.2.29 *)
sub v_sub_2_29 v571 v_call_i_2_29;
(*   store i16 %sub.2.29, i16* %arrayidx9.2.29, align 2, !tbaa !3 *)
mov mem0_122 v_sub_2_29;
(*   %add21.2.29 = add i16 %571, %call.i.2.29 *)
add v_add21_2_29 v571 v_call_i_2_29;
(*   store i16 %add21.2.29, i16* %arrayidx11.2.29, align 2, !tbaa !3 *)
mov mem0_58 v_add21_2_29;
(*   %arrayidx9.2.30 = getelementptr inbounds i16, i16* %r, i64 62 *)
(*   %572 = load i16, i16* %arrayidx9.2.30, align 2, !tbaa !3 *)
mov v572 mem0_124;
(*   %conv1.i.2.30 = sext i16 %572 to i32 *)
cast v_conv1_i_2_30@sint32 v572@sint16;
(*   %mul.i.2.30 = mul nsw i32 %conv1.i.2.30, 1493 *)
mul v_mul_i_2_30 v_conv1_i_2_30 (1493)@sint32;
(*   %call.i.2.30 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.30) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_30, v_call_i_2_30);
(*   %arrayidx11.2.30 = getelementptr inbounds i16, i16* %r, i64 30 *)
(*   %573 = load i16, i16* %arrayidx11.2.30, align 2, !tbaa !3 *)
mov v573 mem0_60;
(*   %sub.2.30 = sub i16 %573, %call.i.2.30 *)
sub v_sub_2_30 v573 v_call_i_2_30;
(*   store i16 %sub.2.30, i16* %arrayidx9.2.30, align 2, !tbaa !3 *)
mov mem0_124 v_sub_2_30;
(*   %add21.2.30 = add i16 %573, %call.i.2.30 *)
add v_add21_2_30 v573 v_call_i_2_30;
(*   store i16 %add21.2.30, i16* %arrayidx11.2.30, align 2, !tbaa !3 *)
mov mem0_60 v_add21_2_30;
(*   %arrayidx9.2.31 = getelementptr inbounds i16, i16* %r, i64 63 *)
(*   %574 = load i16, i16* %arrayidx9.2.31, align 2, !tbaa !3 *)
mov v574 mem0_126;
(*   %conv1.i.2.31 = sext i16 %574 to i32 *)
cast v_conv1_i_2_31@sint32 v574@sint16;
(*   %mul.i.2.31 = mul nsw i32 %conv1.i.2.31, 1493 *)
mul v_mul_i_2_31 v_conv1_i_2_31 (1493)@sint32;
(*   %call.i.2.31 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.31) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_31, v_call_i_2_31);
(*   %arrayidx11.2.31 = getelementptr inbounds i16, i16* %r, i64 31 *)
(*   %575 = load i16, i16* %arrayidx11.2.31, align 2, !tbaa !3 *)
mov v575 mem0_62;
(*   %sub.2.31 = sub i16 %575, %call.i.2.31 *)
sub v_sub_2_31 v575 v_call_i_2_31;
(*   store i16 %sub.2.31, i16* %arrayidx9.2.31, align 2, !tbaa !3 *)
mov mem0_126 v_sub_2_31;
(*   %add21.2.31 = add i16 %575, %call.i.2.31 *)
add v_add21_2_31 v575 v_call_i_2_31;
(*   store i16 %add21.2.31, i16* %arrayidx11.2.31, align 2, !tbaa !3 *)
mov mem0_62 v_add21_2_31;

(* NOTE: k = 5 *)

(*   %arrayidx9.2.1248 = getelementptr inbounds i16, i16* %r, i64 96 *)
(*   %576 = load i16, i16* %arrayidx9.2.1248, align 2, !tbaa !3 *)
mov v576 mem0_192;
(*   %conv1.i.2.1249 = sext i16 %576 to i32 *)
cast v_conv1_i_2_1249@sint32 v576@sint16;
(*   %mul.i.2.1250 = mul nsw i32 %conv1.i.2.1249, 1422 *)
mul v_mul_i_2_1250 v_conv1_i_2_1249 (1422)@sint32;
(*   %call.i.2.1251 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.1250) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_1250, v_call_i_2_1251);
(*   %arrayidx11.2.1252 = getelementptr inbounds i16, i16* %r, i64 64 *)
(*   %577 = load i16, i16* %arrayidx11.2.1252, align 2, !tbaa !3 *)
mov v577 mem0_128;
(*   %sub.2.1253 = sub i16 %577, %call.i.2.1251 *)
sub v_sub_2_1253 v577 v_call_i_2_1251;
(*   store i16 %sub.2.1253, i16* %arrayidx9.2.1248, align 2, !tbaa !3 *)
mov mem0_192 v_sub_2_1253;
(*   %add21.2.1254 = add i16 %577, %call.i.2.1251 *)
add v_add21_2_1254 v577 v_call_i_2_1251;
(*   store i16 %add21.2.1254, i16* %arrayidx11.2.1252, align 2, !tbaa !3 *)
mov mem0_128 v_add21_2_1254;
(*   %arrayidx9.2.1.1 = getelementptr inbounds i16, i16* %r, i64 97 *)
(*   %578 = load i16, i16* %arrayidx9.2.1.1, align 2, !tbaa !3 *)
mov v578 mem0_194;
(*   %conv1.i.2.1.1 = sext i16 %578 to i32 *)
cast v_conv1_i_2_1_1@sint32 v578@sint16;
(*   %mul.i.2.1.1 = mul nsw i32 %conv1.i.2.1.1, 1422 *)
mul v_mul_i_2_1_1 v_conv1_i_2_1_1 (1422)@sint32;
(*   %call.i.2.1.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.1.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_1_1, v_call_i_2_1_1);
(*   %arrayidx11.2.1.1 = getelementptr inbounds i16, i16* %r, i64 65 *)
(*   %579 = load i16, i16* %arrayidx11.2.1.1, align 2, !tbaa !3 *)
mov v579 mem0_130;
(*   %sub.2.1.1 = sub i16 %579, %call.i.2.1.1 *)
sub v_sub_2_1_1 v579 v_call_i_2_1_1;
(*   store i16 %sub.2.1.1, i16* %arrayidx9.2.1.1, align 2, !tbaa !3 *)
mov mem0_194 v_sub_2_1_1;
(*   %add21.2.1.1 = add i16 %579, %call.i.2.1.1 *)
add v_add21_2_1_1 v579 v_call_i_2_1_1;
(*   store i16 %add21.2.1.1, i16* %arrayidx11.2.1.1, align 2, !tbaa !3 *)
mov mem0_130 v_add21_2_1_1;
(*   %arrayidx9.2.2.1 = getelementptr inbounds i16, i16* %r, i64 98 *)
(*   %580 = load i16, i16* %arrayidx9.2.2.1, align 2, !tbaa !3 *)
mov v580 mem0_196;
(*   %conv1.i.2.2.1 = sext i16 %580 to i32 *)
cast v_conv1_i_2_2_1@sint32 v580@sint16;
(*   %mul.i.2.2.1 = mul nsw i32 %conv1.i.2.2.1, 1422 *)
mul v_mul_i_2_2_1 v_conv1_i_2_2_1 (1422)@sint32;
(*   %call.i.2.2.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.2.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_2_1, v_call_i_2_2_1);
(*   %arrayidx11.2.2.1 = getelementptr inbounds i16, i16* %r, i64 66 *)
(*   %581 = load i16, i16* %arrayidx11.2.2.1, align 2, !tbaa !3 *)
mov v581 mem0_132;
(*   %sub.2.2.1 = sub i16 %581, %call.i.2.2.1 *)
sub v_sub_2_2_1 v581 v_call_i_2_2_1;
(*   store i16 %sub.2.2.1, i16* %arrayidx9.2.2.1, align 2, !tbaa !3 *)
mov mem0_196 v_sub_2_2_1;
(*   %add21.2.2.1 = add i16 %581, %call.i.2.2.1 *)
add v_add21_2_2_1 v581 v_call_i_2_2_1;
(*   store i16 %add21.2.2.1, i16* %arrayidx11.2.2.1, align 2, !tbaa !3 *)
mov mem0_132 v_add21_2_2_1;
(*   %arrayidx9.2.3.1 = getelementptr inbounds i16, i16* %r, i64 99 *)
(*   %582 = load i16, i16* %arrayidx9.2.3.1, align 2, !tbaa !3 *)
mov v582 mem0_198;
(*   %conv1.i.2.3.1 = sext i16 %582 to i32 *)
cast v_conv1_i_2_3_1@sint32 v582@sint16;
(*   %mul.i.2.3.1 = mul nsw i32 %conv1.i.2.3.1, 1422 *)
mul v_mul_i_2_3_1 v_conv1_i_2_3_1 (1422)@sint32;
(*   %call.i.2.3.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.3.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_3_1, v_call_i_2_3_1);
(*   %arrayidx11.2.3.1 = getelementptr inbounds i16, i16* %r, i64 67 *)
(*   %583 = load i16, i16* %arrayidx11.2.3.1, align 2, !tbaa !3 *)
mov v583 mem0_134;
(*   %sub.2.3.1 = sub i16 %583, %call.i.2.3.1 *)
sub v_sub_2_3_1 v583 v_call_i_2_3_1;
(*   store i16 %sub.2.3.1, i16* %arrayidx9.2.3.1, align 2, !tbaa !3 *)
mov mem0_198 v_sub_2_3_1;
(*   %add21.2.3.1 = add i16 %583, %call.i.2.3.1 *)
add v_add21_2_3_1 v583 v_call_i_2_3_1;
(*   store i16 %add21.2.3.1, i16* %arrayidx11.2.3.1, align 2, !tbaa !3 *)
mov mem0_134 v_add21_2_3_1;
(*   %arrayidx9.2.4.1 = getelementptr inbounds i16, i16* %r, i64 100 *)
(*   %584 = load i16, i16* %arrayidx9.2.4.1, align 2, !tbaa !3 *)
mov v584 mem0_200;
(*   %conv1.i.2.4.1 = sext i16 %584 to i32 *)
cast v_conv1_i_2_4_1@sint32 v584@sint16;
(*   %mul.i.2.4.1 = mul nsw i32 %conv1.i.2.4.1, 1422 *)
mul v_mul_i_2_4_1 v_conv1_i_2_4_1 (1422)@sint32;
(*   %call.i.2.4.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.4.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_4_1, v_call_i_2_4_1);
(*   %arrayidx11.2.4.1 = getelementptr inbounds i16, i16* %r, i64 68 *)
(*   %585 = load i16, i16* %arrayidx11.2.4.1, align 2, !tbaa !3 *)
mov v585 mem0_136;
(*   %sub.2.4.1 = sub i16 %585, %call.i.2.4.1 *)
sub v_sub_2_4_1 v585 v_call_i_2_4_1;
(*   store i16 %sub.2.4.1, i16* %arrayidx9.2.4.1, align 2, !tbaa !3 *)
mov mem0_200 v_sub_2_4_1;
(*   %add21.2.4.1 = add i16 %585, %call.i.2.4.1 *)
add v_add21_2_4_1 v585 v_call_i_2_4_1;
(*   store i16 %add21.2.4.1, i16* %arrayidx11.2.4.1, align 2, !tbaa !3 *)
mov mem0_136 v_add21_2_4_1;
(*   %arrayidx9.2.5.1 = getelementptr inbounds i16, i16* %r, i64 101 *)
(*   %586 = load i16, i16* %arrayidx9.2.5.1, align 2, !tbaa !3 *)
mov v586 mem0_202;
(*   %conv1.i.2.5.1 = sext i16 %586 to i32 *)
cast v_conv1_i_2_5_1@sint32 v586@sint16;
(*   %mul.i.2.5.1 = mul nsw i32 %conv1.i.2.5.1, 1422 *)
mul v_mul_i_2_5_1 v_conv1_i_2_5_1 (1422)@sint32;
(*   %call.i.2.5.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.5.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_5_1, v_call_i_2_5_1);
(*   %arrayidx11.2.5.1 = getelementptr inbounds i16, i16* %r, i64 69 *)
(*   %587 = load i16, i16* %arrayidx11.2.5.1, align 2, !tbaa !3 *)
mov v587 mem0_138;
(*   %sub.2.5.1 = sub i16 %587, %call.i.2.5.1 *)
sub v_sub_2_5_1 v587 v_call_i_2_5_1;
(*   store i16 %sub.2.5.1, i16* %arrayidx9.2.5.1, align 2, !tbaa !3 *)
mov mem0_202 v_sub_2_5_1;
(*   %add21.2.5.1 = add i16 %587, %call.i.2.5.1 *)
add v_add21_2_5_1 v587 v_call_i_2_5_1;
(*   store i16 %add21.2.5.1, i16* %arrayidx11.2.5.1, align 2, !tbaa !3 *)
mov mem0_138 v_add21_2_5_1;
(*   %arrayidx9.2.6.1 = getelementptr inbounds i16, i16* %r, i64 102 *)
(*   %588 = load i16, i16* %arrayidx9.2.6.1, align 2, !tbaa !3 *)
mov v588 mem0_204;
(*   %conv1.i.2.6.1 = sext i16 %588 to i32 *)
cast v_conv1_i_2_6_1@sint32 v588@sint16;
(*   %mul.i.2.6.1 = mul nsw i32 %conv1.i.2.6.1, 1422 *)
mul v_mul_i_2_6_1 v_conv1_i_2_6_1 (1422)@sint32;
(*   %call.i.2.6.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.6.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_6_1, v_call_i_2_6_1);
(*   %arrayidx11.2.6.1 = getelementptr inbounds i16, i16* %r, i64 70 *)
(*   %589 = load i16, i16* %arrayidx11.2.6.1, align 2, !tbaa !3 *)
mov v589 mem0_140;
(*   %sub.2.6.1 = sub i16 %589, %call.i.2.6.1 *)
sub v_sub_2_6_1 v589 v_call_i_2_6_1;
(*   store i16 %sub.2.6.1, i16* %arrayidx9.2.6.1, align 2, !tbaa !3 *)
mov mem0_204 v_sub_2_6_1;
(*   %add21.2.6.1 = add i16 %589, %call.i.2.6.1 *)
add v_add21_2_6_1 v589 v_call_i_2_6_1;
(*   store i16 %add21.2.6.1, i16* %arrayidx11.2.6.1, align 2, !tbaa !3 *)
mov mem0_140 v_add21_2_6_1;
(*   %arrayidx9.2.7.1 = getelementptr inbounds i16, i16* %r, i64 103 *)
(*   %590 = load i16, i16* %arrayidx9.2.7.1, align 2, !tbaa !3 *)
mov v590 mem0_206;
(*   %conv1.i.2.7.1 = sext i16 %590 to i32 *)
cast v_conv1_i_2_7_1@sint32 v590@sint16;
(*   %mul.i.2.7.1 = mul nsw i32 %conv1.i.2.7.1, 1422 *)
mul v_mul_i_2_7_1 v_conv1_i_2_7_1 (1422)@sint32;
(*   %call.i.2.7.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.7.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_7_1, v_call_i_2_7_1);
(*   %arrayidx11.2.7.1 = getelementptr inbounds i16, i16* %r, i64 71 *)
(*   %591 = load i16, i16* %arrayidx11.2.7.1, align 2, !tbaa !3 *)
mov v591 mem0_142;
(*   %sub.2.7.1 = sub i16 %591, %call.i.2.7.1 *)
sub v_sub_2_7_1 v591 v_call_i_2_7_1;
(*   store i16 %sub.2.7.1, i16* %arrayidx9.2.7.1, align 2, !tbaa !3 *)
mov mem0_206 v_sub_2_7_1;
(*   %add21.2.7.1 = add i16 %591, %call.i.2.7.1 *)
add v_add21_2_7_1 v591 v_call_i_2_7_1;
(*   store i16 %add21.2.7.1, i16* %arrayidx11.2.7.1, align 2, !tbaa !3 *)
mov mem0_142 v_add21_2_7_1;
(*   %arrayidx9.2.8.1 = getelementptr inbounds i16, i16* %r, i64 104 *)
(*   %592 = load i16, i16* %arrayidx9.2.8.1, align 2, !tbaa !3 *)
mov v592 mem0_208;
(*   %conv1.i.2.8.1 = sext i16 %592 to i32 *)
cast v_conv1_i_2_8_1@sint32 v592@sint16;
(*   %mul.i.2.8.1 = mul nsw i32 %conv1.i.2.8.1, 1422 *)
mul v_mul_i_2_8_1 v_conv1_i_2_8_1 (1422)@sint32;
(*   %call.i.2.8.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.8.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_8_1, v_call_i_2_8_1);
(*   %arrayidx11.2.8.1 = getelementptr inbounds i16, i16* %r, i64 72 *)
(*   %593 = load i16, i16* %arrayidx11.2.8.1, align 2, !tbaa !3 *)
mov v593 mem0_144;
(*   %sub.2.8.1 = sub i16 %593, %call.i.2.8.1 *)
sub v_sub_2_8_1 v593 v_call_i_2_8_1;
(*   store i16 %sub.2.8.1, i16* %arrayidx9.2.8.1, align 2, !tbaa !3 *)
mov mem0_208 v_sub_2_8_1;
(*   %add21.2.8.1 = add i16 %593, %call.i.2.8.1 *)
add v_add21_2_8_1 v593 v_call_i_2_8_1;
(*   store i16 %add21.2.8.1, i16* %arrayidx11.2.8.1, align 2, !tbaa !3 *)
mov mem0_144 v_add21_2_8_1;
(*   %arrayidx9.2.9.1 = getelementptr inbounds i16, i16* %r, i64 105 *)
(*   %594 = load i16, i16* %arrayidx9.2.9.1, align 2, !tbaa !3 *)
mov v594 mem0_210;
(*   %conv1.i.2.9.1 = sext i16 %594 to i32 *)
cast v_conv1_i_2_9_1@sint32 v594@sint16;
(*   %mul.i.2.9.1 = mul nsw i32 %conv1.i.2.9.1, 1422 *)
mul v_mul_i_2_9_1 v_conv1_i_2_9_1 (1422)@sint32;
(*   %call.i.2.9.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.9.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_9_1, v_call_i_2_9_1);
(*   %arrayidx11.2.9.1 = getelementptr inbounds i16, i16* %r, i64 73 *)
(*   %595 = load i16, i16* %arrayidx11.2.9.1, align 2, !tbaa !3 *)
mov v595 mem0_146;
(*   %sub.2.9.1 = sub i16 %595, %call.i.2.9.1 *)
sub v_sub_2_9_1 v595 v_call_i_2_9_1;
(*   store i16 %sub.2.9.1, i16* %arrayidx9.2.9.1, align 2, !tbaa !3 *)
mov mem0_210 v_sub_2_9_1;
(*   %add21.2.9.1 = add i16 %595, %call.i.2.9.1 *)
add v_add21_2_9_1 v595 v_call_i_2_9_1;
(*   store i16 %add21.2.9.1, i16* %arrayidx11.2.9.1, align 2, !tbaa !3 *)
mov mem0_146 v_add21_2_9_1;
(*   %arrayidx9.2.10.1 = getelementptr inbounds i16, i16* %r, i64 106 *)
(*   %596 = load i16, i16* %arrayidx9.2.10.1, align 2, !tbaa !3 *)
mov v596 mem0_212;
(*   %conv1.i.2.10.1 = sext i16 %596 to i32 *)
cast v_conv1_i_2_10_1@sint32 v596@sint16;
(*   %mul.i.2.10.1 = mul nsw i32 %conv1.i.2.10.1, 1422 *)
mul v_mul_i_2_10_1 v_conv1_i_2_10_1 (1422)@sint32;
(*   %call.i.2.10.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.10.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_10_1, v_call_i_2_10_1);
(*   %arrayidx11.2.10.1 = getelementptr inbounds i16, i16* %r, i64 74 *)
(*   %597 = load i16, i16* %arrayidx11.2.10.1, align 2, !tbaa !3 *)
mov v597 mem0_148;
(*   %sub.2.10.1 = sub i16 %597, %call.i.2.10.1 *)
sub v_sub_2_10_1 v597 v_call_i_2_10_1;
(*   store i16 %sub.2.10.1, i16* %arrayidx9.2.10.1, align 2, !tbaa !3 *)
mov mem0_212 v_sub_2_10_1;
(*   %add21.2.10.1 = add i16 %597, %call.i.2.10.1 *)
add v_add21_2_10_1 v597 v_call_i_2_10_1;
(*   store i16 %add21.2.10.1, i16* %arrayidx11.2.10.1, align 2, !tbaa !3 *)
mov mem0_148 v_add21_2_10_1;
(*   %arrayidx9.2.11.1 = getelementptr inbounds i16, i16* %r, i64 107 *)
(*   %598 = load i16, i16* %arrayidx9.2.11.1, align 2, !tbaa !3 *)
mov v598 mem0_214;
(*   %conv1.i.2.11.1 = sext i16 %598 to i32 *)
cast v_conv1_i_2_11_1@sint32 v598@sint16;
(*   %mul.i.2.11.1 = mul nsw i32 %conv1.i.2.11.1, 1422 *)
mul v_mul_i_2_11_1 v_conv1_i_2_11_1 (1422)@sint32;
(*   %call.i.2.11.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.11.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_11_1, v_call_i_2_11_1);
(*   %arrayidx11.2.11.1 = getelementptr inbounds i16, i16* %r, i64 75 *)
(*   %599 = load i16, i16* %arrayidx11.2.11.1, align 2, !tbaa !3 *)
mov v599 mem0_150;
(*   %sub.2.11.1 = sub i16 %599, %call.i.2.11.1 *)
sub v_sub_2_11_1 v599 v_call_i_2_11_1;
(*   store i16 %sub.2.11.1, i16* %arrayidx9.2.11.1, align 2, !tbaa !3 *)
mov mem0_214 v_sub_2_11_1;
(*   %add21.2.11.1 = add i16 %599, %call.i.2.11.1 *)
add v_add21_2_11_1 v599 v_call_i_2_11_1;
(*   store i16 %add21.2.11.1, i16* %arrayidx11.2.11.1, align 2, !tbaa !3 *)
mov mem0_150 v_add21_2_11_1;
(*   %arrayidx9.2.12.1 = getelementptr inbounds i16, i16* %r, i64 108 *)
(*   %600 = load i16, i16* %arrayidx9.2.12.1, align 2, !tbaa !3 *)
mov v600 mem0_216;
(*   %conv1.i.2.12.1 = sext i16 %600 to i32 *)
cast v_conv1_i_2_12_1@sint32 v600@sint16;
(*   %mul.i.2.12.1 = mul nsw i32 %conv1.i.2.12.1, 1422 *)
mul v_mul_i_2_12_1 v_conv1_i_2_12_1 (1422)@sint32;
(*   %call.i.2.12.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.12.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_12_1, v_call_i_2_12_1);
(*   %arrayidx11.2.12.1 = getelementptr inbounds i16, i16* %r, i64 76 *)
(*   %601 = load i16, i16* %arrayidx11.2.12.1, align 2, !tbaa !3 *)
mov v601 mem0_152;
(*   %sub.2.12.1 = sub i16 %601, %call.i.2.12.1 *)
sub v_sub_2_12_1 v601 v_call_i_2_12_1;
(*   store i16 %sub.2.12.1, i16* %arrayidx9.2.12.1, align 2, !tbaa !3 *)
mov mem0_216 v_sub_2_12_1;
(*   %add21.2.12.1 = add i16 %601, %call.i.2.12.1 *)
add v_add21_2_12_1 v601 v_call_i_2_12_1;
(*   store i16 %add21.2.12.1, i16* %arrayidx11.2.12.1, align 2, !tbaa !3 *)
mov mem0_152 v_add21_2_12_1;
(*   %arrayidx9.2.13.1 = getelementptr inbounds i16, i16* %r, i64 109 *)
(*   %602 = load i16, i16* %arrayidx9.2.13.1, align 2, !tbaa !3 *)
mov v602 mem0_218;
(*   %conv1.i.2.13.1 = sext i16 %602 to i32 *)
cast v_conv1_i_2_13_1@sint32 v602@sint16;
(*   %mul.i.2.13.1 = mul nsw i32 %conv1.i.2.13.1, 1422 *)
mul v_mul_i_2_13_1 v_conv1_i_2_13_1 (1422)@sint32;
(*   %call.i.2.13.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.13.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_13_1, v_call_i_2_13_1);
(*   %arrayidx11.2.13.1 = getelementptr inbounds i16, i16* %r, i64 77 *)
(*   %603 = load i16, i16* %arrayidx11.2.13.1, align 2, !tbaa !3 *)
mov v603 mem0_154;
(*   %sub.2.13.1 = sub i16 %603, %call.i.2.13.1 *)
sub v_sub_2_13_1 v603 v_call_i_2_13_1;
(*   store i16 %sub.2.13.1, i16* %arrayidx9.2.13.1, align 2, !tbaa !3 *)
mov mem0_218 v_sub_2_13_1;
(*   %add21.2.13.1 = add i16 %603, %call.i.2.13.1 *)
add v_add21_2_13_1 v603 v_call_i_2_13_1;
(*   store i16 %add21.2.13.1, i16* %arrayidx11.2.13.1, align 2, !tbaa !3 *)
mov mem0_154 v_add21_2_13_1;
(*   %arrayidx9.2.14.1 = getelementptr inbounds i16, i16* %r, i64 110 *)
(*   %604 = load i16, i16* %arrayidx9.2.14.1, align 2, !tbaa !3 *)
mov v604 mem0_220;
(*   %conv1.i.2.14.1 = sext i16 %604 to i32 *)
cast v_conv1_i_2_14_1@sint32 v604@sint16;
(*   %mul.i.2.14.1 = mul nsw i32 %conv1.i.2.14.1, 1422 *)
mul v_mul_i_2_14_1 v_conv1_i_2_14_1 (1422)@sint32;
(*   %call.i.2.14.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.14.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_14_1, v_call_i_2_14_1);
(*   %arrayidx11.2.14.1 = getelementptr inbounds i16, i16* %r, i64 78 *)
(*   %605 = load i16, i16* %arrayidx11.2.14.1, align 2, !tbaa !3 *)
mov v605 mem0_156;
(*   %sub.2.14.1 = sub i16 %605, %call.i.2.14.1 *)
sub v_sub_2_14_1 v605 v_call_i_2_14_1;
(*   store i16 %sub.2.14.1, i16* %arrayidx9.2.14.1, align 2, !tbaa !3 *)
mov mem0_220 v_sub_2_14_1;
(*   %add21.2.14.1 = add i16 %605, %call.i.2.14.1 *)
add v_add21_2_14_1 v605 v_call_i_2_14_1;
(*   store i16 %add21.2.14.1, i16* %arrayidx11.2.14.1, align 2, !tbaa !3 *)
mov mem0_156 v_add21_2_14_1;
(*   %arrayidx9.2.15.1 = getelementptr inbounds i16, i16* %r, i64 111 *)
(*   %606 = load i16, i16* %arrayidx9.2.15.1, align 2, !tbaa !3 *)
mov v606 mem0_222;
(*   %conv1.i.2.15.1 = sext i16 %606 to i32 *)
cast v_conv1_i_2_15_1@sint32 v606@sint16;
(*   %mul.i.2.15.1 = mul nsw i32 %conv1.i.2.15.1, 1422 *)
mul v_mul_i_2_15_1 v_conv1_i_2_15_1 (1422)@sint32;
(*   %call.i.2.15.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.15.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_15_1, v_call_i_2_15_1);
(*   %arrayidx11.2.15.1 = getelementptr inbounds i16, i16* %r, i64 79 *)
(*   %607 = load i16, i16* %arrayidx11.2.15.1, align 2, !tbaa !3 *)
mov v607 mem0_158;
(*   %sub.2.15.1 = sub i16 %607, %call.i.2.15.1 *)
sub v_sub_2_15_1 v607 v_call_i_2_15_1;
(*   store i16 %sub.2.15.1, i16* %arrayidx9.2.15.1, align 2, !tbaa !3 *)
mov mem0_222 v_sub_2_15_1;
(*   %add21.2.15.1 = add i16 %607, %call.i.2.15.1 *)
add v_add21_2_15_1 v607 v_call_i_2_15_1;
(*   store i16 %add21.2.15.1, i16* %arrayidx11.2.15.1, align 2, !tbaa !3 *)
mov mem0_158 v_add21_2_15_1;
(*   %arrayidx9.2.16.1 = getelementptr inbounds i16, i16* %r, i64 112 *)
(*   %608 = load i16, i16* %arrayidx9.2.16.1, align 2, !tbaa !3 *)
mov v608 mem0_224;
(*   %conv1.i.2.16.1 = sext i16 %608 to i32 *)
cast v_conv1_i_2_16_1@sint32 v608@sint16;
(*   %mul.i.2.16.1 = mul nsw i32 %conv1.i.2.16.1, 1422 *)
mul v_mul_i_2_16_1 v_conv1_i_2_16_1 (1422)@sint32;
(*   %call.i.2.16.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.16.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_16_1, v_call_i_2_16_1);
(*   %arrayidx11.2.16.1 = getelementptr inbounds i16, i16* %r, i64 80 *)
(*   %609 = load i16, i16* %arrayidx11.2.16.1, align 2, !tbaa !3 *)
mov v609 mem0_160;
(*   %sub.2.16.1 = sub i16 %609, %call.i.2.16.1 *)
sub v_sub_2_16_1 v609 v_call_i_2_16_1;
(*   store i16 %sub.2.16.1, i16* %arrayidx9.2.16.1, align 2, !tbaa !3 *)
mov mem0_224 v_sub_2_16_1;
(*   %add21.2.16.1 = add i16 %609, %call.i.2.16.1 *)
add v_add21_2_16_1 v609 v_call_i_2_16_1;
(*   store i16 %add21.2.16.1, i16* %arrayidx11.2.16.1, align 2, !tbaa !3 *)
mov mem0_160 v_add21_2_16_1;
(*   %arrayidx9.2.17.1 = getelementptr inbounds i16, i16* %r, i64 113 *)
(*   %610 = load i16, i16* %arrayidx9.2.17.1, align 2, !tbaa !3 *)
mov v610 mem0_226;
(*   %conv1.i.2.17.1 = sext i16 %610 to i32 *)
cast v_conv1_i_2_17_1@sint32 v610@sint16;
(*   %mul.i.2.17.1 = mul nsw i32 %conv1.i.2.17.1, 1422 *)
mul v_mul_i_2_17_1 v_conv1_i_2_17_1 (1422)@sint32;
(*   %call.i.2.17.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.17.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_17_1, v_call_i_2_17_1);
(*   %arrayidx11.2.17.1 = getelementptr inbounds i16, i16* %r, i64 81 *)
(*   %611 = load i16, i16* %arrayidx11.2.17.1, align 2, !tbaa !3 *)
mov v611 mem0_162;
(*   %sub.2.17.1 = sub i16 %611, %call.i.2.17.1 *)
sub v_sub_2_17_1 v611 v_call_i_2_17_1;
(*   store i16 %sub.2.17.1, i16* %arrayidx9.2.17.1, align 2, !tbaa !3 *)
mov mem0_226 v_sub_2_17_1;
(*   %add21.2.17.1 = add i16 %611, %call.i.2.17.1 *)
add v_add21_2_17_1 v611 v_call_i_2_17_1;
(*   store i16 %add21.2.17.1, i16* %arrayidx11.2.17.1, align 2, !tbaa !3 *)
mov mem0_162 v_add21_2_17_1;
(*   %arrayidx9.2.18.1 = getelementptr inbounds i16, i16* %r, i64 114 *)
(*   %612 = load i16, i16* %arrayidx9.2.18.1, align 2, !tbaa !3 *)
mov v612 mem0_228;
(*   %conv1.i.2.18.1 = sext i16 %612 to i32 *)
cast v_conv1_i_2_18_1@sint32 v612@sint16;
(*   %mul.i.2.18.1 = mul nsw i32 %conv1.i.2.18.1, 1422 *)
mul v_mul_i_2_18_1 v_conv1_i_2_18_1 (1422)@sint32;
(*   %call.i.2.18.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.18.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_18_1, v_call_i_2_18_1);
(*   %arrayidx11.2.18.1 = getelementptr inbounds i16, i16* %r, i64 82 *)
(*   %613 = load i16, i16* %arrayidx11.2.18.1, align 2, !tbaa !3 *)
mov v613 mem0_164;
(*   %sub.2.18.1 = sub i16 %613, %call.i.2.18.1 *)
sub v_sub_2_18_1 v613 v_call_i_2_18_1;
(*   store i16 %sub.2.18.1, i16* %arrayidx9.2.18.1, align 2, !tbaa !3 *)
mov mem0_228 v_sub_2_18_1;
(*   %add21.2.18.1 = add i16 %613, %call.i.2.18.1 *)
add v_add21_2_18_1 v613 v_call_i_2_18_1;
(*   store i16 %add21.2.18.1, i16* %arrayidx11.2.18.1, align 2, !tbaa !3 *)
mov mem0_164 v_add21_2_18_1;
(*   %arrayidx9.2.19.1 = getelementptr inbounds i16, i16* %r, i64 115 *)
(*   %614 = load i16, i16* %arrayidx9.2.19.1, align 2, !tbaa !3 *)
mov v614 mem0_230;
(*   %conv1.i.2.19.1 = sext i16 %614 to i32 *)
cast v_conv1_i_2_19_1@sint32 v614@sint16;
(*   %mul.i.2.19.1 = mul nsw i32 %conv1.i.2.19.1, 1422 *)
mul v_mul_i_2_19_1 v_conv1_i_2_19_1 (1422)@sint32;
(*   %call.i.2.19.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.19.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_19_1, v_call_i_2_19_1);
(*   %arrayidx11.2.19.1 = getelementptr inbounds i16, i16* %r, i64 83 *)
(*   %615 = load i16, i16* %arrayidx11.2.19.1, align 2, !tbaa !3 *)
mov v615 mem0_166;
(*   %sub.2.19.1 = sub i16 %615, %call.i.2.19.1 *)
sub v_sub_2_19_1 v615 v_call_i_2_19_1;
(*   store i16 %sub.2.19.1, i16* %arrayidx9.2.19.1, align 2, !tbaa !3 *)
mov mem0_230 v_sub_2_19_1;
(*   %add21.2.19.1 = add i16 %615, %call.i.2.19.1 *)
add v_add21_2_19_1 v615 v_call_i_2_19_1;
(*   store i16 %add21.2.19.1, i16* %arrayidx11.2.19.1, align 2, !tbaa !3 *)
mov mem0_166 v_add21_2_19_1;
(*   %arrayidx9.2.20.1 = getelementptr inbounds i16, i16* %r, i64 116 *)
(*   %616 = load i16, i16* %arrayidx9.2.20.1, align 2, !tbaa !3 *)
mov v616 mem0_232;
(*   %conv1.i.2.20.1 = sext i16 %616 to i32 *)
cast v_conv1_i_2_20_1@sint32 v616@sint16;
(*   %mul.i.2.20.1 = mul nsw i32 %conv1.i.2.20.1, 1422 *)
mul v_mul_i_2_20_1 v_conv1_i_2_20_1 (1422)@sint32;
(*   %call.i.2.20.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.20.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_20_1, v_call_i_2_20_1);
(*   %arrayidx11.2.20.1 = getelementptr inbounds i16, i16* %r, i64 84 *)
(*   %617 = load i16, i16* %arrayidx11.2.20.1, align 2, !tbaa !3 *)
mov v617 mem0_168;
(*   %sub.2.20.1 = sub i16 %617, %call.i.2.20.1 *)
sub v_sub_2_20_1 v617 v_call_i_2_20_1;
(*   store i16 %sub.2.20.1, i16* %arrayidx9.2.20.1, align 2, !tbaa !3 *)
mov mem0_232 v_sub_2_20_1;
(*   %add21.2.20.1 = add i16 %617, %call.i.2.20.1 *)
add v_add21_2_20_1 v617 v_call_i_2_20_1;
(*   store i16 %add21.2.20.1, i16* %arrayidx11.2.20.1, align 2, !tbaa !3 *)
mov mem0_168 v_add21_2_20_1;
(*   %arrayidx9.2.21.1 = getelementptr inbounds i16, i16* %r, i64 117 *)
(*   %618 = load i16, i16* %arrayidx9.2.21.1, align 2, !tbaa !3 *)
mov v618 mem0_234;
(*   %conv1.i.2.21.1 = sext i16 %618 to i32 *)
cast v_conv1_i_2_21_1@sint32 v618@sint16;
(*   %mul.i.2.21.1 = mul nsw i32 %conv1.i.2.21.1, 1422 *)
mul v_mul_i_2_21_1 v_conv1_i_2_21_1 (1422)@sint32;
(*   %call.i.2.21.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.21.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_21_1, v_call_i_2_21_1);
(*   %arrayidx11.2.21.1 = getelementptr inbounds i16, i16* %r, i64 85 *)
(*   %619 = load i16, i16* %arrayidx11.2.21.1, align 2, !tbaa !3 *)
mov v619 mem0_170;
(*   %sub.2.21.1 = sub i16 %619, %call.i.2.21.1 *)
sub v_sub_2_21_1 v619 v_call_i_2_21_1;
(*   store i16 %sub.2.21.1, i16* %arrayidx9.2.21.1, align 2, !tbaa !3 *)
mov mem0_234 v_sub_2_21_1;
(*   %add21.2.21.1 = add i16 %619, %call.i.2.21.1 *)
add v_add21_2_21_1 v619 v_call_i_2_21_1;
(*   store i16 %add21.2.21.1, i16* %arrayidx11.2.21.1, align 2, !tbaa !3 *)
mov mem0_170 v_add21_2_21_1;
(*   %arrayidx9.2.22.1 = getelementptr inbounds i16, i16* %r, i64 118 *)
(*   %620 = load i16, i16* %arrayidx9.2.22.1, align 2, !tbaa !3 *)
mov v620 mem0_236;
(*   %conv1.i.2.22.1 = sext i16 %620 to i32 *)
cast v_conv1_i_2_22_1@sint32 v620@sint16;
(*   %mul.i.2.22.1 = mul nsw i32 %conv1.i.2.22.1, 1422 *)
mul v_mul_i_2_22_1 v_conv1_i_2_22_1 (1422)@sint32;
(*   %call.i.2.22.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.22.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_22_1, v_call_i_2_22_1);
(*   %arrayidx11.2.22.1 = getelementptr inbounds i16, i16* %r, i64 86 *)
(*   %621 = load i16, i16* %arrayidx11.2.22.1, align 2, !tbaa !3 *)
mov v621 mem0_172;
(*   %sub.2.22.1 = sub i16 %621, %call.i.2.22.1 *)
sub v_sub_2_22_1 v621 v_call_i_2_22_1;
(*   store i16 %sub.2.22.1, i16* %arrayidx9.2.22.1, align 2, !tbaa !3 *)
mov mem0_236 v_sub_2_22_1;
(*   %add21.2.22.1 = add i16 %621, %call.i.2.22.1 *)
add v_add21_2_22_1 v621 v_call_i_2_22_1;
(*   store i16 %add21.2.22.1, i16* %arrayidx11.2.22.1, align 2, !tbaa !3 *)
mov mem0_172 v_add21_2_22_1;
(*   %arrayidx9.2.23.1 = getelementptr inbounds i16, i16* %r, i64 119 *)
(*   %622 = load i16, i16* %arrayidx9.2.23.1, align 2, !tbaa !3 *)
mov v622 mem0_238;
(*   %conv1.i.2.23.1 = sext i16 %622 to i32 *)
cast v_conv1_i_2_23_1@sint32 v622@sint16;
(*   %mul.i.2.23.1 = mul nsw i32 %conv1.i.2.23.1, 1422 *)
mul v_mul_i_2_23_1 v_conv1_i_2_23_1 (1422)@sint32;
(*   %call.i.2.23.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.23.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_23_1, v_call_i_2_23_1);
(*   %arrayidx11.2.23.1 = getelementptr inbounds i16, i16* %r, i64 87 *)
(*   %623 = load i16, i16* %arrayidx11.2.23.1, align 2, !tbaa !3 *)
mov v623 mem0_174;
(*   %sub.2.23.1 = sub i16 %623, %call.i.2.23.1 *)
sub v_sub_2_23_1 v623 v_call_i_2_23_1;
(*   store i16 %sub.2.23.1, i16* %arrayidx9.2.23.1, align 2, !tbaa !3 *)
mov mem0_238 v_sub_2_23_1;
(*   %add21.2.23.1 = add i16 %623, %call.i.2.23.1 *)
add v_add21_2_23_1 v623 v_call_i_2_23_1;
(*   store i16 %add21.2.23.1, i16* %arrayidx11.2.23.1, align 2, !tbaa !3 *)
mov mem0_174 v_add21_2_23_1;
(*   %arrayidx9.2.24.1 = getelementptr inbounds i16, i16* %r, i64 120 *)
(*   %624 = load i16, i16* %arrayidx9.2.24.1, align 2, !tbaa !3 *)
mov v624 mem0_240;
(*   %conv1.i.2.24.1 = sext i16 %624 to i32 *)
cast v_conv1_i_2_24_1@sint32 v624@sint16;
(*   %mul.i.2.24.1 = mul nsw i32 %conv1.i.2.24.1, 1422 *)
mul v_mul_i_2_24_1 v_conv1_i_2_24_1 (1422)@sint32;
(*   %call.i.2.24.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.24.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_24_1, v_call_i_2_24_1);
(*   %arrayidx11.2.24.1 = getelementptr inbounds i16, i16* %r, i64 88 *)
(*   %625 = load i16, i16* %arrayidx11.2.24.1, align 2, !tbaa !3 *)
mov v625 mem0_176;
(*   %sub.2.24.1 = sub i16 %625, %call.i.2.24.1 *)
sub v_sub_2_24_1 v625 v_call_i_2_24_1;
(*   store i16 %sub.2.24.1, i16* %arrayidx9.2.24.1, align 2, !tbaa !3 *)
mov mem0_240 v_sub_2_24_1;
(*   %add21.2.24.1 = add i16 %625, %call.i.2.24.1 *)
add v_add21_2_24_1 v625 v_call_i_2_24_1;
(*   store i16 %add21.2.24.1, i16* %arrayidx11.2.24.1, align 2, !tbaa !3 *)
mov mem0_176 v_add21_2_24_1;
(*   %arrayidx9.2.25.1 = getelementptr inbounds i16, i16* %r, i64 121 *)
(*   %626 = load i16, i16* %arrayidx9.2.25.1, align 2, !tbaa !3 *)
mov v626 mem0_242;
(*   %conv1.i.2.25.1 = sext i16 %626 to i32 *)
cast v_conv1_i_2_25_1@sint32 v626@sint16;
(*   %mul.i.2.25.1 = mul nsw i32 %conv1.i.2.25.1, 1422 *)
mul v_mul_i_2_25_1 v_conv1_i_2_25_1 (1422)@sint32;
(*   %call.i.2.25.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.25.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_25_1, v_call_i_2_25_1);
(*   %arrayidx11.2.25.1 = getelementptr inbounds i16, i16* %r, i64 89 *)
(*   %627 = load i16, i16* %arrayidx11.2.25.1, align 2, !tbaa !3 *)
mov v627 mem0_178;
(*   %sub.2.25.1 = sub i16 %627, %call.i.2.25.1 *)
sub v_sub_2_25_1 v627 v_call_i_2_25_1;
(*   store i16 %sub.2.25.1, i16* %arrayidx9.2.25.1, align 2, !tbaa !3 *)
mov mem0_242 v_sub_2_25_1;
(*   %add21.2.25.1 = add i16 %627, %call.i.2.25.1 *)
add v_add21_2_25_1 v627 v_call_i_2_25_1;
(*   store i16 %add21.2.25.1, i16* %arrayidx11.2.25.1, align 2, !tbaa !3 *)
mov mem0_178 v_add21_2_25_1;
(*   %arrayidx9.2.26.1 = getelementptr inbounds i16, i16* %r, i64 122 *)
(*   %628 = load i16, i16* %arrayidx9.2.26.1, align 2, !tbaa !3 *)
mov v628 mem0_244;
(*   %conv1.i.2.26.1 = sext i16 %628 to i32 *)
cast v_conv1_i_2_26_1@sint32 v628@sint16;
(*   %mul.i.2.26.1 = mul nsw i32 %conv1.i.2.26.1, 1422 *)
mul v_mul_i_2_26_1 v_conv1_i_2_26_1 (1422)@sint32;
(*   %call.i.2.26.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.26.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_26_1, v_call_i_2_26_1);
(*   %arrayidx11.2.26.1 = getelementptr inbounds i16, i16* %r, i64 90 *)
(*   %629 = load i16, i16* %arrayidx11.2.26.1, align 2, !tbaa !3 *)
mov v629 mem0_180;
(*   %sub.2.26.1 = sub i16 %629, %call.i.2.26.1 *)
sub v_sub_2_26_1 v629 v_call_i_2_26_1;
(*   store i16 %sub.2.26.1, i16* %arrayidx9.2.26.1, align 2, !tbaa !3 *)
mov mem0_244 v_sub_2_26_1;
(*   %add21.2.26.1 = add i16 %629, %call.i.2.26.1 *)
add v_add21_2_26_1 v629 v_call_i_2_26_1;
(*   store i16 %add21.2.26.1, i16* %arrayidx11.2.26.1, align 2, !tbaa !3 *)
mov mem0_180 v_add21_2_26_1;
(*   %arrayidx9.2.27.1 = getelementptr inbounds i16, i16* %r, i64 123 *)
(*   %630 = load i16, i16* %arrayidx9.2.27.1, align 2, !tbaa !3 *)
mov v630 mem0_246;
(*   %conv1.i.2.27.1 = sext i16 %630 to i32 *)
cast v_conv1_i_2_27_1@sint32 v630@sint16;
(*   %mul.i.2.27.1 = mul nsw i32 %conv1.i.2.27.1, 1422 *)
mul v_mul_i_2_27_1 v_conv1_i_2_27_1 (1422)@sint32;
(*   %call.i.2.27.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.27.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_27_1, v_call_i_2_27_1);
(*   %arrayidx11.2.27.1 = getelementptr inbounds i16, i16* %r, i64 91 *)
(*   %631 = load i16, i16* %arrayidx11.2.27.1, align 2, !tbaa !3 *)
mov v631 mem0_182;
(*   %sub.2.27.1 = sub i16 %631, %call.i.2.27.1 *)
sub v_sub_2_27_1 v631 v_call_i_2_27_1;
(*   store i16 %sub.2.27.1, i16* %arrayidx9.2.27.1, align 2, !tbaa !3 *)
mov mem0_246 v_sub_2_27_1;
(*   %add21.2.27.1 = add i16 %631, %call.i.2.27.1 *)
add v_add21_2_27_1 v631 v_call_i_2_27_1;
(*   store i16 %add21.2.27.1, i16* %arrayidx11.2.27.1, align 2, !tbaa !3 *)
mov mem0_182 v_add21_2_27_1;
(*   %arrayidx9.2.28.1 = getelementptr inbounds i16, i16* %r, i64 124 *)
(*   %632 = load i16, i16* %arrayidx9.2.28.1, align 2, !tbaa !3 *)
mov v632 mem0_248;
(*   %conv1.i.2.28.1 = sext i16 %632 to i32 *)
cast v_conv1_i_2_28_1@sint32 v632@sint16;
(*   %mul.i.2.28.1 = mul nsw i32 %conv1.i.2.28.1, 1422 *)
mul v_mul_i_2_28_1 v_conv1_i_2_28_1 (1422)@sint32;
(*   %call.i.2.28.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.28.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_28_1, v_call_i_2_28_1);
(*   %arrayidx11.2.28.1 = getelementptr inbounds i16, i16* %r, i64 92 *)
(*   %633 = load i16, i16* %arrayidx11.2.28.1, align 2, !tbaa !3 *)
mov v633 mem0_184;
(*   %sub.2.28.1 = sub i16 %633, %call.i.2.28.1 *)
sub v_sub_2_28_1 v633 v_call_i_2_28_1;
(*   store i16 %sub.2.28.1, i16* %arrayidx9.2.28.1, align 2, !tbaa !3 *)
mov mem0_248 v_sub_2_28_1;
(*   %add21.2.28.1 = add i16 %633, %call.i.2.28.1 *)
add v_add21_2_28_1 v633 v_call_i_2_28_1;
(*   store i16 %add21.2.28.1, i16* %arrayidx11.2.28.1, align 2, !tbaa !3 *)
mov mem0_184 v_add21_2_28_1;
(*   %arrayidx9.2.29.1 = getelementptr inbounds i16, i16* %r, i64 125 *)
(*   %634 = load i16, i16* %arrayidx9.2.29.1, align 2, !tbaa !3 *)
mov v634 mem0_250;
(*   %conv1.i.2.29.1 = sext i16 %634 to i32 *)
cast v_conv1_i_2_29_1@sint32 v634@sint16;
(*   %mul.i.2.29.1 = mul nsw i32 %conv1.i.2.29.1, 1422 *)
mul v_mul_i_2_29_1 v_conv1_i_2_29_1 (1422)@sint32;
(*   %call.i.2.29.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.29.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_29_1, v_call_i_2_29_1);
(*   %arrayidx11.2.29.1 = getelementptr inbounds i16, i16* %r, i64 93 *)
(*   %635 = load i16, i16* %arrayidx11.2.29.1, align 2, !tbaa !3 *)
mov v635 mem0_186;
(*   %sub.2.29.1 = sub i16 %635, %call.i.2.29.1 *)
sub v_sub_2_29_1 v635 v_call_i_2_29_1;
(*   store i16 %sub.2.29.1, i16* %arrayidx9.2.29.1, align 2, !tbaa !3 *)
mov mem0_250 v_sub_2_29_1;
(*   %add21.2.29.1 = add i16 %635, %call.i.2.29.1 *)
add v_add21_2_29_1 v635 v_call_i_2_29_1;
(*   store i16 %add21.2.29.1, i16* %arrayidx11.2.29.1, align 2, !tbaa !3 *)
mov mem0_186 v_add21_2_29_1;
(*   %arrayidx9.2.30.1 = getelementptr inbounds i16, i16* %r, i64 126 *)
(*   %636 = load i16, i16* %arrayidx9.2.30.1, align 2, !tbaa !3 *)
mov v636 mem0_252;
(*   %conv1.i.2.30.1 = sext i16 %636 to i32 *)
cast v_conv1_i_2_30_1@sint32 v636@sint16;
(*   %mul.i.2.30.1 = mul nsw i32 %conv1.i.2.30.1, 1422 *)
mul v_mul_i_2_30_1 v_conv1_i_2_30_1 (1422)@sint32;
(*   %call.i.2.30.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.30.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_30_1, v_call_i_2_30_1);
(*   %arrayidx11.2.30.1 = getelementptr inbounds i16, i16* %r, i64 94 *)
(*   %637 = load i16, i16* %arrayidx11.2.30.1, align 2, !tbaa !3 *)
mov v637 mem0_188;
(*   %sub.2.30.1 = sub i16 %637, %call.i.2.30.1 *)
sub v_sub_2_30_1 v637 v_call_i_2_30_1;
(*   store i16 %sub.2.30.1, i16* %arrayidx9.2.30.1, align 2, !tbaa !3 *)
mov mem0_252 v_sub_2_30_1;
(*   %add21.2.30.1 = add i16 %637, %call.i.2.30.1 *)
add v_add21_2_30_1 v637 v_call_i_2_30_1;
(*   store i16 %add21.2.30.1, i16* %arrayidx11.2.30.1, align 2, !tbaa !3 *)
mov mem0_188 v_add21_2_30_1;
(*   %arrayidx9.2.31.1 = getelementptr inbounds i16, i16* %r, i64 127 *)
(*   %638 = load i16, i16* %arrayidx9.2.31.1, align 2, !tbaa !3 *)
mov v638 mem0_254;
(*   %conv1.i.2.31.1 = sext i16 %638 to i32 *)
cast v_conv1_i_2_31_1@sint32 v638@sint16;
(*   %mul.i.2.31.1 = mul nsw i32 %conv1.i.2.31.1, 1422 *)
mul v_mul_i_2_31_1 v_conv1_i_2_31_1 (1422)@sint32;
(*   %call.i.2.31.1 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.31.1) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_31_1, v_call_i_2_31_1);
(*   %arrayidx11.2.31.1 = getelementptr inbounds i16, i16* %r, i64 95 *)
(*   %639 = load i16, i16* %arrayidx11.2.31.1, align 2, !tbaa !3 *)
mov v639 mem0_190;
(*   %sub.2.31.1 = sub i16 %639, %call.i.2.31.1 *)
sub v_sub_2_31_1 v639 v_call_i_2_31_1;
(*   store i16 %sub.2.31.1, i16* %arrayidx9.2.31.1, align 2, !tbaa !3 *)
mov mem0_254 v_sub_2_31_1;
(*   %add21.2.31.1 = add i16 %639, %call.i.2.31.1 *)
add v_add21_2_31_1 v639 v_call_i_2_31_1;
(*   store i16 %add21.2.31.1, i16* %arrayidx11.2.31.1, align 2, !tbaa !3 *)
mov mem0_190 v_add21_2_31_1;

(* NOTE: k = 6 *)

(*   %arrayidx9.2.2258 = getelementptr inbounds i16, i16* %r, i64 160 *)
(*   %640 = load i16, i16* %arrayidx9.2.2258, align 2, !tbaa !3 *)
mov v640 mem0_320;
(*   %conv1.i.2.2259 = sext i16 %640 to i32 *)
cast v_conv1_i_2_2259@sint32 v640@sint16;
(*   %mul.i.2.2260 = mul nsw i32 %conv1.i.2.2259, 287 *)
mul v_mul_i_2_2260 v_conv1_i_2_2259 (287)@sint32;
(*   %call.i.2.2261 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.2260) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_2260, v_call_i_2_2261);
(*   %arrayidx11.2.2262 = getelementptr inbounds i16, i16* %r, i64 128 *)
(*   %641 = load i16, i16* %arrayidx11.2.2262, align 2, !tbaa !3 *)
mov v641 mem0_256;
(*   %sub.2.2263 = sub i16 %641, %call.i.2.2261 *)
sub v_sub_2_2263 v641 v_call_i_2_2261;
(*   store i16 %sub.2.2263, i16* %arrayidx9.2.2258, align 2, !tbaa !3 *)
mov mem0_320 v_sub_2_2263;
(*   %add21.2.2264 = add i16 %641, %call.i.2.2261 *)
add v_add21_2_2264 v641 v_call_i_2_2261;
(*   store i16 %add21.2.2264, i16* %arrayidx11.2.2262, align 2, !tbaa !3 *)
mov mem0_256 v_add21_2_2264;
(*   %arrayidx9.2.1.2 = getelementptr inbounds i16, i16* %r, i64 161 *)
(*   %642 = load i16, i16* %arrayidx9.2.1.2, align 2, !tbaa !3 *)
mov v642 mem0_322;
(*   %conv1.i.2.1.2 = sext i16 %642 to i32 *)
cast v_conv1_i_2_1_2@sint32 v642@sint16;
(*   %mul.i.2.1.2 = mul nsw i32 %conv1.i.2.1.2, 287 *)
mul v_mul_i_2_1_2 v_conv1_i_2_1_2 (287)@sint32;
(*   %call.i.2.1.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.1.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_1_2, v_call_i_2_1_2);
(*   %arrayidx11.2.1.2 = getelementptr inbounds i16, i16* %r, i64 129 *)
(*   %643 = load i16, i16* %arrayidx11.2.1.2, align 2, !tbaa !3 *)
mov v643 mem0_258;
(*   %sub.2.1.2 = sub i16 %643, %call.i.2.1.2 *)
sub v_sub_2_1_2 v643 v_call_i_2_1_2;
(*   store i16 %sub.2.1.2, i16* %arrayidx9.2.1.2, align 2, !tbaa !3 *)
mov mem0_322 v_sub_2_1_2;
(*   %add21.2.1.2 = add i16 %643, %call.i.2.1.2 *)
add v_add21_2_1_2 v643 v_call_i_2_1_2;
(*   store i16 %add21.2.1.2, i16* %arrayidx11.2.1.2, align 2, !tbaa !3 *)
mov mem0_258 v_add21_2_1_2;
(*   %arrayidx9.2.2.2 = getelementptr inbounds i16, i16* %r, i64 162 *)
(*   %644 = load i16, i16* %arrayidx9.2.2.2, align 2, !tbaa !3 *)
mov v644 mem0_324;
(*   %conv1.i.2.2.2 = sext i16 %644 to i32 *)
cast v_conv1_i_2_2_2@sint32 v644@sint16;
(*   %mul.i.2.2.2 = mul nsw i32 %conv1.i.2.2.2, 287 *)
mul v_mul_i_2_2_2 v_conv1_i_2_2_2 (287)@sint32;
(*   %call.i.2.2.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.2.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_2_2, v_call_i_2_2_2);
(*   %arrayidx11.2.2.2 = getelementptr inbounds i16, i16* %r, i64 130 *)
(*   %645 = load i16, i16* %arrayidx11.2.2.2, align 2, !tbaa !3 *)
mov v645 mem0_260;
(*   %sub.2.2.2 = sub i16 %645, %call.i.2.2.2 *)
sub v_sub_2_2_2 v645 v_call_i_2_2_2;
(*   store i16 %sub.2.2.2, i16* %arrayidx9.2.2.2, align 2, !tbaa !3 *)
mov mem0_324 v_sub_2_2_2;
(*   %add21.2.2.2 = add i16 %645, %call.i.2.2.2 *)
add v_add21_2_2_2 v645 v_call_i_2_2_2;
(*   store i16 %add21.2.2.2, i16* %arrayidx11.2.2.2, align 2, !tbaa !3 *)
mov mem0_260 v_add21_2_2_2;
(*   %arrayidx9.2.3.2 = getelementptr inbounds i16, i16* %r, i64 163 *)
(*   %646 = load i16, i16* %arrayidx9.2.3.2, align 2, !tbaa !3 *)
mov v646 mem0_326;
(*   %conv1.i.2.3.2 = sext i16 %646 to i32 *)
cast v_conv1_i_2_3_2@sint32 v646@sint16;
(*   %mul.i.2.3.2 = mul nsw i32 %conv1.i.2.3.2, 287 *)
mul v_mul_i_2_3_2 v_conv1_i_2_3_2 (287)@sint32;
(*   %call.i.2.3.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.3.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_3_2, v_call_i_2_3_2);
(*   %arrayidx11.2.3.2 = getelementptr inbounds i16, i16* %r, i64 131 *)
(*   %647 = load i16, i16* %arrayidx11.2.3.2, align 2, !tbaa !3 *)
mov v647 mem0_262;
(*   %sub.2.3.2 = sub i16 %647, %call.i.2.3.2 *)
sub v_sub_2_3_2 v647 v_call_i_2_3_2;
(*   store i16 %sub.2.3.2, i16* %arrayidx9.2.3.2, align 2, !tbaa !3 *)
mov mem0_326 v_sub_2_3_2;
(*   %add21.2.3.2 = add i16 %647, %call.i.2.3.2 *)
add v_add21_2_3_2 v647 v_call_i_2_3_2;
(*   store i16 %add21.2.3.2, i16* %arrayidx11.2.3.2, align 2, !tbaa !3 *)
mov mem0_262 v_add21_2_3_2;
(*   %arrayidx9.2.4.2 = getelementptr inbounds i16, i16* %r, i64 164 *)
(*   %648 = load i16, i16* %arrayidx9.2.4.2, align 2, !tbaa !3 *)
mov v648 mem0_328;
(*   %conv1.i.2.4.2 = sext i16 %648 to i32 *)
cast v_conv1_i_2_4_2@sint32 v648@sint16;
(*   %mul.i.2.4.2 = mul nsw i32 %conv1.i.2.4.2, 287 *)
mul v_mul_i_2_4_2 v_conv1_i_2_4_2 (287)@sint32;
(*   %call.i.2.4.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.4.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_4_2, v_call_i_2_4_2);
(*   %arrayidx11.2.4.2 = getelementptr inbounds i16, i16* %r, i64 132 *)
(*   %649 = load i16, i16* %arrayidx11.2.4.2, align 2, !tbaa !3 *)
mov v649 mem0_264;
(*   %sub.2.4.2 = sub i16 %649, %call.i.2.4.2 *)
sub v_sub_2_4_2 v649 v_call_i_2_4_2;
(*   store i16 %sub.2.4.2, i16* %arrayidx9.2.4.2, align 2, !tbaa !3 *)
mov mem0_328 v_sub_2_4_2;
(*   %add21.2.4.2 = add i16 %649, %call.i.2.4.2 *)
add v_add21_2_4_2 v649 v_call_i_2_4_2;
(*   store i16 %add21.2.4.2, i16* %arrayidx11.2.4.2, align 2, !tbaa !3 *)
mov mem0_264 v_add21_2_4_2;
(*   %arrayidx9.2.5.2 = getelementptr inbounds i16, i16* %r, i64 165 *)
(*   %650 = load i16, i16* %arrayidx9.2.5.2, align 2, !tbaa !3 *)
mov v650 mem0_330;
(*   %conv1.i.2.5.2 = sext i16 %650 to i32 *)
cast v_conv1_i_2_5_2@sint32 v650@sint16;
(*   %mul.i.2.5.2 = mul nsw i32 %conv1.i.2.5.2, 287 *)
mul v_mul_i_2_5_2 v_conv1_i_2_5_2 (287)@sint32;
(*   %call.i.2.5.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.5.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_5_2, v_call_i_2_5_2);
(*   %arrayidx11.2.5.2 = getelementptr inbounds i16, i16* %r, i64 133 *)
(*   %651 = load i16, i16* %arrayidx11.2.5.2, align 2, !tbaa !3 *)
mov v651 mem0_266;
(*   %sub.2.5.2 = sub i16 %651, %call.i.2.5.2 *)
sub v_sub_2_5_2 v651 v_call_i_2_5_2;
(*   store i16 %sub.2.5.2, i16* %arrayidx9.2.5.2, align 2, !tbaa !3 *)
mov mem0_330 v_sub_2_5_2;
(*   %add21.2.5.2 = add i16 %651, %call.i.2.5.2 *)
add v_add21_2_5_2 v651 v_call_i_2_5_2;
(*   store i16 %add21.2.5.2, i16* %arrayidx11.2.5.2, align 2, !tbaa !3 *)
mov mem0_266 v_add21_2_5_2;
(*   %arrayidx9.2.6.2 = getelementptr inbounds i16, i16* %r, i64 166 *)
(*   %652 = load i16, i16* %arrayidx9.2.6.2, align 2, !tbaa !3 *)
mov v652 mem0_332;
(*   %conv1.i.2.6.2 = sext i16 %652 to i32 *)
cast v_conv1_i_2_6_2@sint32 v652@sint16;
(*   %mul.i.2.6.2 = mul nsw i32 %conv1.i.2.6.2, 287 *)
mul v_mul_i_2_6_2 v_conv1_i_2_6_2 (287)@sint32;
(*   %call.i.2.6.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.6.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_6_2, v_call_i_2_6_2);
(*   %arrayidx11.2.6.2 = getelementptr inbounds i16, i16* %r, i64 134 *)
(*   %653 = load i16, i16* %arrayidx11.2.6.2, align 2, !tbaa !3 *)
mov v653 mem0_268;
(*   %sub.2.6.2 = sub i16 %653, %call.i.2.6.2 *)
sub v_sub_2_6_2 v653 v_call_i_2_6_2;
(*   store i16 %sub.2.6.2, i16* %arrayidx9.2.6.2, align 2, !tbaa !3 *)
mov mem0_332 v_sub_2_6_2;
(*   %add21.2.6.2 = add i16 %653, %call.i.2.6.2 *)
add v_add21_2_6_2 v653 v_call_i_2_6_2;
(*   store i16 %add21.2.6.2, i16* %arrayidx11.2.6.2, align 2, !tbaa !3 *)
mov mem0_268 v_add21_2_6_2;
(*   %arrayidx9.2.7.2 = getelementptr inbounds i16, i16* %r, i64 167 *)
(*   %654 = load i16, i16* %arrayidx9.2.7.2, align 2, !tbaa !3 *)
mov v654 mem0_334;
(*   %conv1.i.2.7.2 = sext i16 %654 to i32 *)
cast v_conv1_i_2_7_2@sint32 v654@sint16;
(*   %mul.i.2.7.2 = mul nsw i32 %conv1.i.2.7.2, 287 *)
mul v_mul_i_2_7_2 v_conv1_i_2_7_2 (287)@sint32;
(*   %call.i.2.7.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.7.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_7_2, v_call_i_2_7_2);
(*   %arrayidx11.2.7.2 = getelementptr inbounds i16, i16* %r, i64 135 *)
(*   %655 = load i16, i16* %arrayidx11.2.7.2, align 2, !tbaa !3 *)
mov v655 mem0_270;
(*   %sub.2.7.2 = sub i16 %655, %call.i.2.7.2 *)
sub v_sub_2_7_2 v655 v_call_i_2_7_2;
(*   store i16 %sub.2.7.2, i16* %arrayidx9.2.7.2, align 2, !tbaa !3 *)
mov mem0_334 v_sub_2_7_2;
(*   %add21.2.7.2 = add i16 %655, %call.i.2.7.2 *)
add v_add21_2_7_2 v655 v_call_i_2_7_2;
(*   store i16 %add21.2.7.2, i16* %arrayidx11.2.7.2, align 2, !tbaa !3 *)
mov mem0_270 v_add21_2_7_2;
(*   %arrayidx9.2.8.2 = getelementptr inbounds i16, i16* %r, i64 168 *)
(*   %656 = load i16, i16* %arrayidx9.2.8.2, align 2, !tbaa !3 *)
mov v656 mem0_336;
(*   %conv1.i.2.8.2 = sext i16 %656 to i32 *)
cast v_conv1_i_2_8_2@sint32 v656@sint16;
(*   %mul.i.2.8.2 = mul nsw i32 %conv1.i.2.8.2, 287 *)
mul v_mul_i_2_8_2 v_conv1_i_2_8_2 (287)@sint32;
(*   %call.i.2.8.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.8.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_8_2, v_call_i_2_8_2);
(*   %arrayidx11.2.8.2 = getelementptr inbounds i16, i16* %r, i64 136 *)
(*   %657 = load i16, i16* %arrayidx11.2.8.2, align 2, !tbaa !3 *)
mov v657 mem0_272;
(*   %sub.2.8.2 = sub i16 %657, %call.i.2.8.2 *)
sub v_sub_2_8_2 v657 v_call_i_2_8_2;
(*   store i16 %sub.2.8.2, i16* %arrayidx9.2.8.2, align 2, !tbaa !3 *)
mov mem0_336 v_sub_2_8_2;
(*   %add21.2.8.2 = add i16 %657, %call.i.2.8.2 *)
add v_add21_2_8_2 v657 v_call_i_2_8_2;
(*   store i16 %add21.2.8.2, i16* %arrayidx11.2.8.2, align 2, !tbaa !3 *)
mov mem0_272 v_add21_2_8_2;
(*   %arrayidx9.2.9.2 = getelementptr inbounds i16, i16* %r, i64 169 *)
(*   %658 = load i16, i16* %arrayidx9.2.9.2, align 2, !tbaa !3 *)
mov v658 mem0_338;
(*   %conv1.i.2.9.2 = sext i16 %658 to i32 *)
cast v_conv1_i_2_9_2@sint32 v658@sint16;
(*   %mul.i.2.9.2 = mul nsw i32 %conv1.i.2.9.2, 287 *)
mul v_mul_i_2_9_2 v_conv1_i_2_9_2 (287)@sint32;
(*   %call.i.2.9.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.9.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_9_2, v_call_i_2_9_2);
(*   %arrayidx11.2.9.2 = getelementptr inbounds i16, i16* %r, i64 137 *)
(*   %659 = load i16, i16* %arrayidx11.2.9.2, align 2, !tbaa !3 *)
mov v659 mem0_274;
(*   %sub.2.9.2 = sub i16 %659, %call.i.2.9.2 *)
sub v_sub_2_9_2 v659 v_call_i_2_9_2;
(*   store i16 %sub.2.9.2, i16* %arrayidx9.2.9.2, align 2, !tbaa !3 *)
mov mem0_338 v_sub_2_9_2;
(*   %add21.2.9.2 = add i16 %659, %call.i.2.9.2 *)
add v_add21_2_9_2 v659 v_call_i_2_9_2;
(*   store i16 %add21.2.9.2, i16* %arrayidx11.2.9.2, align 2, !tbaa !3 *)
mov mem0_274 v_add21_2_9_2;
(*   %arrayidx9.2.10.2 = getelementptr inbounds i16, i16* %r, i64 170 *)
(*   %660 = load i16, i16* %arrayidx9.2.10.2, align 2, !tbaa !3 *)
mov v660 mem0_340;
(*   %conv1.i.2.10.2 = sext i16 %660 to i32 *)
cast v_conv1_i_2_10_2@sint32 v660@sint16;
(*   %mul.i.2.10.2 = mul nsw i32 %conv1.i.2.10.2, 287 *)
mul v_mul_i_2_10_2 v_conv1_i_2_10_2 (287)@sint32;
(*   %call.i.2.10.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.10.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_10_2, v_call_i_2_10_2);
(*   %arrayidx11.2.10.2 = getelementptr inbounds i16, i16* %r, i64 138 *)
(*   %661 = load i16, i16* %arrayidx11.2.10.2, align 2, !tbaa !3 *)
mov v661 mem0_276;
(*   %sub.2.10.2 = sub i16 %661, %call.i.2.10.2 *)
sub v_sub_2_10_2 v661 v_call_i_2_10_2;
(*   store i16 %sub.2.10.2, i16* %arrayidx9.2.10.2, align 2, !tbaa !3 *)
mov mem0_340 v_sub_2_10_2;
(*   %add21.2.10.2 = add i16 %661, %call.i.2.10.2 *)
add v_add21_2_10_2 v661 v_call_i_2_10_2;
(*   store i16 %add21.2.10.2, i16* %arrayidx11.2.10.2, align 2, !tbaa !3 *)
mov mem0_276 v_add21_2_10_2;
(*   %arrayidx9.2.11.2 = getelementptr inbounds i16, i16* %r, i64 171 *)
(*   %662 = load i16, i16* %arrayidx9.2.11.2, align 2, !tbaa !3 *)
mov v662 mem0_342;
(*   %conv1.i.2.11.2 = sext i16 %662 to i32 *)
cast v_conv1_i_2_11_2@sint32 v662@sint16;
(*   %mul.i.2.11.2 = mul nsw i32 %conv1.i.2.11.2, 287 *)
mul v_mul_i_2_11_2 v_conv1_i_2_11_2 (287)@sint32;
(*   %call.i.2.11.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.11.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_11_2, v_call_i_2_11_2);
(*   %arrayidx11.2.11.2 = getelementptr inbounds i16, i16* %r, i64 139 *)
(*   %663 = load i16, i16* %arrayidx11.2.11.2, align 2, !tbaa !3 *)
mov v663 mem0_278;
(*   %sub.2.11.2 = sub i16 %663, %call.i.2.11.2 *)
sub v_sub_2_11_2 v663 v_call_i_2_11_2;
(*   store i16 %sub.2.11.2, i16* %arrayidx9.2.11.2, align 2, !tbaa !3 *)
mov mem0_342 v_sub_2_11_2;
(*   %add21.2.11.2 = add i16 %663, %call.i.2.11.2 *)
add v_add21_2_11_2 v663 v_call_i_2_11_2;
(*   store i16 %add21.2.11.2, i16* %arrayidx11.2.11.2, align 2, !tbaa !3 *)
mov mem0_278 v_add21_2_11_2;
(*   %arrayidx9.2.12.2 = getelementptr inbounds i16, i16* %r, i64 172 *)
(*   %664 = load i16, i16* %arrayidx9.2.12.2, align 2, !tbaa !3 *)
mov v664 mem0_344;
(*   %conv1.i.2.12.2 = sext i16 %664 to i32 *)
cast v_conv1_i_2_12_2@sint32 v664@sint16;
(*   %mul.i.2.12.2 = mul nsw i32 %conv1.i.2.12.2, 287 *)
mul v_mul_i_2_12_2 v_conv1_i_2_12_2 (287)@sint32;
(*   %call.i.2.12.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.12.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_12_2, v_call_i_2_12_2);
(*   %arrayidx11.2.12.2 = getelementptr inbounds i16, i16* %r, i64 140 *)
(*   %665 = load i16, i16* %arrayidx11.2.12.2, align 2, !tbaa !3 *)
mov v665 mem0_280;
(*   %sub.2.12.2 = sub i16 %665, %call.i.2.12.2 *)
sub v_sub_2_12_2 v665 v_call_i_2_12_2;
(*   store i16 %sub.2.12.2, i16* %arrayidx9.2.12.2, align 2, !tbaa !3 *)
mov mem0_344 v_sub_2_12_2;
(*   %add21.2.12.2 = add i16 %665, %call.i.2.12.2 *)
add v_add21_2_12_2 v665 v_call_i_2_12_2;
(*   store i16 %add21.2.12.2, i16* %arrayidx11.2.12.2, align 2, !tbaa !3 *)
mov mem0_280 v_add21_2_12_2;
(*   %arrayidx9.2.13.2 = getelementptr inbounds i16, i16* %r, i64 173 *)
(*   %666 = load i16, i16* %arrayidx9.2.13.2, align 2, !tbaa !3 *)
mov v666 mem0_346;
(*   %conv1.i.2.13.2 = sext i16 %666 to i32 *)
cast v_conv1_i_2_13_2@sint32 v666@sint16;
(*   %mul.i.2.13.2 = mul nsw i32 %conv1.i.2.13.2, 287 *)
mul v_mul_i_2_13_2 v_conv1_i_2_13_2 (287)@sint32;
(*   %call.i.2.13.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.13.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_13_2, v_call_i_2_13_2);
(*   %arrayidx11.2.13.2 = getelementptr inbounds i16, i16* %r, i64 141 *)
(*   %667 = load i16, i16* %arrayidx11.2.13.2, align 2, !tbaa !3 *)
mov v667 mem0_282;
(*   %sub.2.13.2 = sub i16 %667, %call.i.2.13.2 *)
sub v_sub_2_13_2 v667 v_call_i_2_13_2;
(*   store i16 %sub.2.13.2, i16* %arrayidx9.2.13.2, align 2, !tbaa !3 *)
mov mem0_346 v_sub_2_13_2;
(*   %add21.2.13.2 = add i16 %667, %call.i.2.13.2 *)
add v_add21_2_13_2 v667 v_call_i_2_13_2;
(*   store i16 %add21.2.13.2, i16* %arrayidx11.2.13.2, align 2, !tbaa !3 *)
mov mem0_282 v_add21_2_13_2;
(*   %arrayidx9.2.14.2 = getelementptr inbounds i16, i16* %r, i64 174 *)
(*   %668 = load i16, i16* %arrayidx9.2.14.2, align 2, !tbaa !3 *)
mov v668 mem0_348;
(*   %conv1.i.2.14.2 = sext i16 %668 to i32 *)
cast v_conv1_i_2_14_2@sint32 v668@sint16;
(*   %mul.i.2.14.2 = mul nsw i32 %conv1.i.2.14.2, 287 *)
mul v_mul_i_2_14_2 v_conv1_i_2_14_2 (287)@sint32;
(*   %call.i.2.14.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.14.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_14_2, v_call_i_2_14_2);
(*   %arrayidx11.2.14.2 = getelementptr inbounds i16, i16* %r, i64 142 *)
(*   %669 = load i16, i16* %arrayidx11.2.14.2, align 2, !tbaa !3 *)
mov v669 mem0_284;
(*   %sub.2.14.2 = sub i16 %669, %call.i.2.14.2 *)
sub v_sub_2_14_2 v669 v_call_i_2_14_2;
(*   store i16 %sub.2.14.2, i16* %arrayidx9.2.14.2, align 2, !tbaa !3 *)
mov mem0_348 v_sub_2_14_2;
(*   %add21.2.14.2 = add i16 %669, %call.i.2.14.2 *)
add v_add21_2_14_2 v669 v_call_i_2_14_2;
(*   store i16 %add21.2.14.2, i16* %arrayidx11.2.14.2, align 2, !tbaa !3 *)
mov mem0_284 v_add21_2_14_2;
(*   %arrayidx9.2.15.2 = getelementptr inbounds i16, i16* %r, i64 175 *)
(*   %670 = load i16, i16* %arrayidx9.2.15.2, align 2, !tbaa !3 *)
mov v670 mem0_350;
(*   %conv1.i.2.15.2 = sext i16 %670 to i32 *)
cast v_conv1_i_2_15_2@sint32 v670@sint16;
(*   %mul.i.2.15.2 = mul nsw i32 %conv1.i.2.15.2, 287 *)
mul v_mul_i_2_15_2 v_conv1_i_2_15_2 (287)@sint32;
(*   %call.i.2.15.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.15.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_15_2, v_call_i_2_15_2);
(*   %arrayidx11.2.15.2 = getelementptr inbounds i16, i16* %r, i64 143 *)
(*   %671 = load i16, i16* %arrayidx11.2.15.2, align 2, !tbaa !3 *)
mov v671 mem0_286;
(*   %sub.2.15.2 = sub i16 %671, %call.i.2.15.2 *)
sub v_sub_2_15_2 v671 v_call_i_2_15_2;
(*   store i16 %sub.2.15.2, i16* %arrayidx9.2.15.2, align 2, !tbaa !3 *)
mov mem0_350 v_sub_2_15_2;
(*   %add21.2.15.2 = add i16 %671, %call.i.2.15.2 *)
add v_add21_2_15_2 v671 v_call_i_2_15_2;
(*   store i16 %add21.2.15.2, i16* %arrayidx11.2.15.2, align 2, !tbaa !3 *)
mov mem0_286 v_add21_2_15_2;
(*   %arrayidx9.2.16.2 = getelementptr inbounds i16, i16* %r, i64 176 *)
(*   %672 = load i16, i16* %arrayidx9.2.16.2, align 2, !tbaa !3 *)
mov v672 mem0_352;
(*   %conv1.i.2.16.2 = sext i16 %672 to i32 *)
cast v_conv1_i_2_16_2@sint32 v672@sint16;
(*   %mul.i.2.16.2 = mul nsw i32 %conv1.i.2.16.2, 287 *)
mul v_mul_i_2_16_2 v_conv1_i_2_16_2 (287)@sint32;
(*   %call.i.2.16.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.16.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_16_2, v_call_i_2_16_2);
(*   %arrayidx11.2.16.2 = getelementptr inbounds i16, i16* %r, i64 144 *)
(*   %673 = load i16, i16* %arrayidx11.2.16.2, align 2, !tbaa !3 *)
mov v673 mem0_288;
(*   %sub.2.16.2 = sub i16 %673, %call.i.2.16.2 *)
sub v_sub_2_16_2 v673 v_call_i_2_16_2;
(*   store i16 %sub.2.16.2, i16* %arrayidx9.2.16.2, align 2, !tbaa !3 *)
mov mem0_352 v_sub_2_16_2;
(*   %add21.2.16.2 = add i16 %673, %call.i.2.16.2 *)
add v_add21_2_16_2 v673 v_call_i_2_16_2;
(*   store i16 %add21.2.16.2, i16* %arrayidx11.2.16.2, align 2, !tbaa !3 *)
mov mem0_288 v_add21_2_16_2;
(*   %arrayidx9.2.17.2 = getelementptr inbounds i16, i16* %r, i64 177 *)
(*   %674 = load i16, i16* %arrayidx9.2.17.2, align 2, !tbaa !3 *)
mov v674 mem0_354;
(*   %conv1.i.2.17.2 = sext i16 %674 to i32 *)
cast v_conv1_i_2_17_2@sint32 v674@sint16;
(*   %mul.i.2.17.2 = mul nsw i32 %conv1.i.2.17.2, 287 *)
mul v_mul_i_2_17_2 v_conv1_i_2_17_2 (287)@sint32;
(*   %call.i.2.17.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.17.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_17_2, v_call_i_2_17_2);
(*   %arrayidx11.2.17.2 = getelementptr inbounds i16, i16* %r, i64 145 *)
(*   %675 = load i16, i16* %arrayidx11.2.17.2, align 2, !tbaa !3 *)
mov v675 mem0_290;
(*   %sub.2.17.2 = sub i16 %675, %call.i.2.17.2 *)
sub v_sub_2_17_2 v675 v_call_i_2_17_2;
(*   store i16 %sub.2.17.2, i16* %arrayidx9.2.17.2, align 2, !tbaa !3 *)
mov mem0_354 v_sub_2_17_2;
(*   %add21.2.17.2 = add i16 %675, %call.i.2.17.2 *)
add v_add21_2_17_2 v675 v_call_i_2_17_2;
(*   store i16 %add21.2.17.2, i16* %arrayidx11.2.17.2, align 2, !tbaa !3 *)
mov mem0_290 v_add21_2_17_2;
(*   %arrayidx9.2.18.2 = getelementptr inbounds i16, i16* %r, i64 178 *)
(*   %676 = load i16, i16* %arrayidx9.2.18.2, align 2, !tbaa !3 *)
mov v676 mem0_356;
(*   %conv1.i.2.18.2 = sext i16 %676 to i32 *)
cast v_conv1_i_2_18_2@sint32 v676@sint16;
(*   %mul.i.2.18.2 = mul nsw i32 %conv1.i.2.18.2, 287 *)
mul v_mul_i_2_18_2 v_conv1_i_2_18_2 (287)@sint32;
(*   %call.i.2.18.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.18.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_18_2, v_call_i_2_18_2);
(*   %arrayidx11.2.18.2 = getelementptr inbounds i16, i16* %r, i64 146 *)
(*   %677 = load i16, i16* %arrayidx11.2.18.2, align 2, !tbaa !3 *)
mov v677 mem0_292;
(*   %sub.2.18.2 = sub i16 %677, %call.i.2.18.2 *)
sub v_sub_2_18_2 v677 v_call_i_2_18_2;
(*   store i16 %sub.2.18.2, i16* %arrayidx9.2.18.2, align 2, !tbaa !3 *)
mov mem0_356 v_sub_2_18_2;
(*   %add21.2.18.2 = add i16 %677, %call.i.2.18.2 *)
add v_add21_2_18_2 v677 v_call_i_2_18_2;
(*   store i16 %add21.2.18.2, i16* %arrayidx11.2.18.2, align 2, !tbaa !3 *)
mov mem0_292 v_add21_2_18_2;
(*   %arrayidx9.2.19.2 = getelementptr inbounds i16, i16* %r, i64 179 *)
(*   %678 = load i16, i16* %arrayidx9.2.19.2, align 2, !tbaa !3 *)
mov v678 mem0_358;
(*   %conv1.i.2.19.2 = sext i16 %678 to i32 *)
cast v_conv1_i_2_19_2@sint32 v678@sint16;
(*   %mul.i.2.19.2 = mul nsw i32 %conv1.i.2.19.2, 287 *)
mul v_mul_i_2_19_2 v_conv1_i_2_19_2 (287)@sint32;
(*   %call.i.2.19.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.19.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_19_2, v_call_i_2_19_2);
(*   %arrayidx11.2.19.2 = getelementptr inbounds i16, i16* %r, i64 147 *)
(*   %679 = load i16, i16* %arrayidx11.2.19.2, align 2, !tbaa !3 *)
mov v679 mem0_294;
(*   %sub.2.19.2 = sub i16 %679, %call.i.2.19.2 *)
sub v_sub_2_19_2 v679 v_call_i_2_19_2;
(*   store i16 %sub.2.19.2, i16* %arrayidx9.2.19.2, align 2, !tbaa !3 *)
mov mem0_358 v_sub_2_19_2;
(*   %add21.2.19.2 = add i16 %679, %call.i.2.19.2 *)
add v_add21_2_19_2 v679 v_call_i_2_19_2;
(*   store i16 %add21.2.19.2, i16* %arrayidx11.2.19.2, align 2, !tbaa !3 *)
mov mem0_294 v_add21_2_19_2;
(*   %arrayidx9.2.20.2 = getelementptr inbounds i16, i16* %r, i64 180 *)
(*   %680 = load i16, i16* %arrayidx9.2.20.2, align 2, !tbaa !3 *)
mov v680 mem0_360;
(*   %conv1.i.2.20.2 = sext i16 %680 to i32 *)
cast v_conv1_i_2_20_2@sint32 v680@sint16;
(*   %mul.i.2.20.2 = mul nsw i32 %conv1.i.2.20.2, 287 *)
mul v_mul_i_2_20_2 v_conv1_i_2_20_2 (287)@sint32;
(*   %call.i.2.20.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.20.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_20_2, v_call_i_2_20_2);
(*   %arrayidx11.2.20.2 = getelementptr inbounds i16, i16* %r, i64 148 *)
(*   %681 = load i16, i16* %arrayidx11.2.20.2, align 2, !tbaa !3 *)
mov v681 mem0_296;
(*   %sub.2.20.2 = sub i16 %681, %call.i.2.20.2 *)
sub v_sub_2_20_2 v681 v_call_i_2_20_2;
(*   store i16 %sub.2.20.2, i16* %arrayidx9.2.20.2, align 2, !tbaa !3 *)
mov mem0_360 v_sub_2_20_2;
(*   %add21.2.20.2 = add i16 %681, %call.i.2.20.2 *)
add v_add21_2_20_2 v681 v_call_i_2_20_2;
(*   store i16 %add21.2.20.2, i16* %arrayidx11.2.20.2, align 2, !tbaa !3 *)
mov mem0_296 v_add21_2_20_2;
(*   %arrayidx9.2.21.2 = getelementptr inbounds i16, i16* %r, i64 181 *)
(*   %682 = load i16, i16* %arrayidx9.2.21.2, align 2, !tbaa !3 *)
mov v682 mem0_362;
(*   %conv1.i.2.21.2 = sext i16 %682 to i32 *)
cast v_conv1_i_2_21_2@sint32 v682@sint16;
(*   %mul.i.2.21.2 = mul nsw i32 %conv1.i.2.21.2, 287 *)
mul v_mul_i_2_21_2 v_conv1_i_2_21_2 (287)@sint32;
(*   %call.i.2.21.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.21.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_21_2, v_call_i_2_21_2);
(*   %arrayidx11.2.21.2 = getelementptr inbounds i16, i16* %r, i64 149 *)
(*   %683 = load i16, i16* %arrayidx11.2.21.2, align 2, !tbaa !3 *)
mov v683 mem0_298;
(*   %sub.2.21.2 = sub i16 %683, %call.i.2.21.2 *)
sub v_sub_2_21_2 v683 v_call_i_2_21_2;
(*   store i16 %sub.2.21.2, i16* %arrayidx9.2.21.2, align 2, !tbaa !3 *)
mov mem0_362 v_sub_2_21_2;
(*   %add21.2.21.2 = add i16 %683, %call.i.2.21.2 *)
add v_add21_2_21_2 v683 v_call_i_2_21_2;
(*   store i16 %add21.2.21.2, i16* %arrayidx11.2.21.2, align 2, !tbaa !3 *)
mov mem0_298 v_add21_2_21_2;
(*   %arrayidx9.2.22.2 = getelementptr inbounds i16, i16* %r, i64 182 *)
(*   %684 = load i16, i16* %arrayidx9.2.22.2, align 2, !tbaa !3 *)
mov v684 mem0_364;
(*   %conv1.i.2.22.2 = sext i16 %684 to i32 *)
cast v_conv1_i_2_22_2@sint32 v684@sint16;
(*   %mul.i.2.22.2 = mul nsw i32 %conv1.i.2.22.2, 287 *)
mul v_mul_i_2_22_2 v_conv1_i_2_22_2 (287)@sint32;
(*   %call.i.2.22.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.22.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_22_2, v_call_i_2_22_2);
(*   %arrayidx11.2.22.2 = getelementptr inbounds i16, i16* %r, i64 150 *)
(*   %685 = load i16, i16* %arrayidx11.2.22.2, align 2, !tbaa !3 *)
mov v685 mem0_300;
(*   %sub.2.22.2 = sub i16 %685, %call.i.2.22.2 *)
sub v_sub_2_22_2 v685 v_call_i_2_22_2;
(*   store i16 %sub.2.22.2, i16* %arrayidx9.2.22.2, align 2, !tbaa !3 *)
mov mem0_364 v_sub_2_22_2;
(*   %add21.2.22.2 = add i16 %685, %call.i.2.22.2 *)
add v_add21_2_22_2 v685 v_call_i_2_22_2;
(*   store i16 %add21.2.22.2, i16* %arrayidx11.2.22.2, align 2, !tbaa !3 *)
mov mem0_300 v_add21_2_22_2;
(*   %arrayidx9.2.23.2 = getelementptr inbounds i16, i16* %r, i64 183 *)
(*   %686 = load i16, i16* %arrayidx9.2.23.2, align 2, !tbaa !3 *)
mov v686 mem0_366;
(*   %conv1.i.2.23.2 = sext i16 %686 to i32 *)
cast v_conv1_i_2_23_2@sint32 v686@sint16;
(*   %mul.i.2.23.2 = mul nsw i32 %conv1.i.2.23.2, 287 *)
mul v_mul_i_2_23_2 v_conv1_i_2_23_2 (287)@sint32;
(*   %call.i.2.23.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.23.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_23_2, v_call_i_2_23_2);
(*   %arrayidx11.2.23.2 = getelementptr inbounds i16, i16* %r, i64 151 *)
(*   %687 = load i16, i16* %arrayidx11.2.23.2, align 2, !tbaa !3 *)
mov v687 mem0_302;
(*   %sub.2.23.2 = sub i16 %687, %call.i.2.23.2 *)
sub v_sub_2_23_2 v687 v_call_i_2_23_2;
(*   store i16 %sub.2.23.2, i16* %arrayidx9.2.23.2, align 2, !tbaa !3 *)
mov mem0_366 v_sub_2_23_2;
(*   %add21.2.23.2 = add i16 %687, %call.i.2.23.2 *)
add v_add21_2_23_2 v687 v_call_i_2_23_2;
(*   store i16 %add21.2.23.2, i16* %arrayidx11.2.23.2, align 2, !tbaa !3 *)
mov mem0_302 v_add21_2_23_2;
(*   %arrayidx9.2.24.2 = getelementptr inbounds i16, i16* %r, i64 184 *)
(*   %688 = load i16, i16* %arrayidx9.2.24.2, align 2, !tbaa !3 *)
mov v688 mem0_368;
(*   %conv1.i.2.24.2 = sext i16 %688 to i32 *)
cast v_conv1_i_2_24_2@sint32 v688@sint16;
(*   %mul.i.2.24.2 = mul nsw i32 %conv1.i.2.24.2, 287 *)
mul v_mul_i_2_24_2 v_conv1_i_2_24_2 (287)@sint32;
(*   %call.i.2.24.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.24.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_24_2, v_call_i_2_24_2);
(*   %arrayidx11.2.24.2 = getelementptr inbounds i16, i16* %r, i64 152 *)
(*   %689 = load i16, i16* %arrayidx11.2.24.2, align 2, !tbaa !3 *)
mov v689 mem0_304;
(*   %sub.2.24.2 = sub i16 %689, %call.i.2.24.2 *)
sub v_sub_2_24_2 v689 v_call_i_2_24_2;
(*   store i16 %sub.2.24.2, i16* %arrayidx9.2.24.2, align 2, !tbaa !3 *)
mov mem0_368 v_sub_2_24_2;
(*   %add21.2.24.2 = add i16 %689, %call.i.2.24.2 *)
add v_add21_2_24_2 v689 v_call_i_2_24_2;
(*   store i16 %add21.2.24.2, i16* %arrayidx11.2.24.2, align 2, !tbaa !3 *)
mov mem0_304 v_add21_2_24_2;
(*   %arrayidx9.2.25.2 = getelementptr inbounds i16, i16* %r, i64 185 *)
(*   %690 = load i16, i16* %arrayidx9.2.25.2, align 2, !tbaa !3 *)
mov v690 mem0_370;
(*   %conv1.i.2.25.2 = sext i16 %690 to i32 *)
cast v_conv1_i_2_25_2@sint32 v690@sint16;
(*   %mul.i.2.25.2 = mul nsw i32 %conv1.i.2.25.2, 287 *)
mul v_mul_i_2_25_2 v_conv1_i_2_25_2 (287)@sint32;
(*   %call.i.2.25.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.25.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_25_2, v_call_i_2_25_2);
(*   %arrayidx11.2.25.2 = getelementptr inbounds i16, i16* %r, i64 153 *)
(*   %691 = load i16, i16* %arrayidx11.2.25.2, align 2, !tbaa !3 *)
mov v691 mem0_306;
(*   %sub.2.25.2 = sub i16 %691, %call.i.2.25.2 *)
sub v_sub_2_25_2 v691 v_call_i_2_25_2;
(*   store i16 %sub.2.25.2, i16* %arrayidx9.2.25.2, align 2, !tbaa !3 *)
mov mem0_370 v_sub_2_25_2;
(*   %add21.2.25.2 = add i16 %691, %call.i.2.25.2 *)
add v_add21_2_25_2 v691 v_call_i_2_25_2;
(*   store i16 %add21.2.25.2, i16* %arrayidx11.2.25.2, align 2, !tbaa !3 *)
mov mem0_306 v_add21_2_25_2;
(*   %arrayidx9.2.26.2 = getelementptr inbounds i16, i16* %r, i64 186 *)
(*   %692 = load i16, i16* %arrayidx9.2.26.2, align 2, !tbaa !3 *)
mov v692 mem0_372;
(*   %conv1.i.2.26.2 = sext i16 %692 to i32 *)
cast v_conv1_i_2_26_2@sint32 v692@sint16;
(*   %mul.i.2.26.2 = mul nsw i32 %conv1.i.2.26.2, 287 *)
mul v_mul_i_2_26_2 v_conv1_i_2_26_2 (287)@sint32;
(*   %call.i.2.26.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.26.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_26_2, v_call_i_2_26_2);
(*   %arrayidx11.2.26.2 = getelementptr inbounds i16, i16* %r, i64 154 *)
(*   %693 = load i16, i16* %arrayidx11.2.26.2, align 2, !tbaa !3 *)
mov v693 mem0_308;
(*   %sub.2.26.2 = sub i16 %693, %call.i.2.26.2 *)
sub v_sub_2_26_2 v693 v_call_i_2_26_2;
(*   store i16 %sub.2.26.2, i16* %arrayidx9.2.26.2, align 2, !tbaa !3 *)
mov mem0_372 v_sub_2_26_2;
(*   %add21.2.26.2 = add i16 %693, %call.i.2.26.2 *)
add v_add21_2_26_2 v693 v_call_i_2_26_2;
(*   store i16 %add21.2.26.2, i16* %arrayidx11.2.26.2, align 2, !tbaa !3 *)
mov mem0_308 v_add21_2_26_2;
(*   %arrayidx9.2.27.2 = getelementptr inbounds i16, i16* %r, i64 187 *)
(*   %694 = load i16, i16* %arrayidx9.2.27.2, align 2, !tbaa !3 *)
mov v694 mem0_374;
(*   %conv1.i.2.27.2 = sext i16 %694 to i32 *)
cast v_conv1_i_2_27_2@sint32 v694@sint16;
(*   %mul.i.2.27.2 = mul nsw i32 %conv1.i.2.27.2, 287 *)
mul v_mul_i_2_27_2 v_conv1_i_2_27_2 (287)@sint32;
(*   %call.i.2.27.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.27.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_27_2, v_call_i_2_27_2);
(*   %arrayidx11.2.27.2 = getelementptr inbounds i16, i16* %r, i64 155 *)
(*   %695 = load i16, i16* %arrayidx11.2.27.2, align 2, !tbaa !3 *)
mov v695 mem0_310;
(*   %sub.2.27.2 = sub i16 %695, %call.i.2.27.2 *)
sub v_sub_2_27_2 v695 v_call_i_2_27_2;
(*   store i16 %sub.2.27.2, i16* %arrayidx9.2.27.2, align 2, !tbaa !3 *)
mov mem0_374 v_sub_2_27_2;
(*   %add21.2.27.2 = add i16 %695, %call.i.2.27.2 *)
add v_add21_2_27_2 v695 v_call_i_2_27_2;
(*   store i16 %add21.2.27.2, i16* %arrayidx11.2.27.2, align 2, !tbaa !3 *)
mov mem0_310 v_add21_2_27_2;
(*   %arrayidx9.2.28.2 = getelementptr inbounds i16, i16* %r, i64 188 *)
(*   %696 = load i16, i16* %arrayidx9.2.28.2, align 2, !tbaa !3 *)
mov v696 mem0_376;
(*   %conv1.i.2.28.2 = sext i16 %696 to i32 *)
cast v_conv1_i_2_28_2@sint32 v696@sint16;
(*   %mul.i.2.28.2 = mul nsw i32 %conv1.i.2.28.2, 287 *)
mul v_mul_i_2_28_2 v_conv1_i_2_28_2 (287)@sint32;
(*   %call.i.2.28.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.28.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_28_2, v_call_i_2_28_2);
(*   %arrayidx11.2.28.2 = getelementptr inbounds i16, i16* %r, i64 156 *)
(*   %697 = load i16, i16* %arrayidx11.2.28.2, align 2, !tbaa !3 *)
mov v697 mem0_312;
(*   %sub.2.28.2 = sub i16 %697, %call.i.2.28.2 *)
sub v_sub_2_28_2 v697 v_call_i_2_28_2;
(*   store i16 %sub.2.28.2, i16* %arrayidx9.2.28.2, align 2, !tbaa !3 *)
mov mem0_376 v_sub_2_28_2;
(*   %add21.2.28.2 = add i16 %697, %call.i.2.28.2 *)
add v_add21_2_28_2 v697 v_call_i_2_28_2;
(*   store i16 %add21.2.28.2, i16* %arrayidx11.2.28.2, align 2, !tbaa !3 *)
mov mem0_312 v_add21_2_28_2;
(*   %arrayidx9.2.29.2 = getelementptr inbounds i16, i16* %r, i64 189 *)
(*   %698 = load i16, i16* %arrayidx9.2.29.2, align 2, !tbaa !3 *)
mov v698 mem0_378;
(*   %conv1.i.2.29.2 = sext i16 %698 to i32 *)
cast v_conv1_i_2_29_2@sint32 v698@sint16;
(*   %mul.i.2.29.2 = mul nsw i32 %conv1.i.2.29.2, 287 *)
mul v_mul_i_2_29_2 v_conv1_i_2_29_2 (287)@sint32;
(*   %call.i.2.29.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.29.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_29_2, v_call_i_2_29_2);
(*   %arrayidx11.2.29.2 = getelementptr inbounds i16, i16* %r, i64 157 *)
(*   %699 = load i16, i16* %arrayidx11.2.29.2, align 2, !tbaa !3 *)
mov v699 mem0_314;
(*   %sub.2.29.2 = sub i16 %699, %call.i.2.29.2 *)
sub v_sub_2_29_2 v699 v_call_i_2_29_2;
(*   store i16 %sub.2.29.2, i16* %arrayidx9.2.29.2, align 2, !tbaa !3 *)
mov mem0_378 v_sub_2_29_2;
(*   %add21.2.29.2 = add i16 %699, %call.i.2.29.2 *)
add v_add21_2_29_2 v699 v_call_i_2_29_2;
(*   store i16 %add21.2.29.2, i16* %arrayidx11.2.29.2, align 2, !tbaa !3 *)
mov mem0_314 v_add21_2_29_2;
(*   %arrayidx9.2.30.2 = getelementptr inbounds i16, i16* %r, i64 190 *)
(*   %700 = load i16, i16* %arrayidx9.2.30.2, align 2, !tbaa !3 *)
mov v700 mem0_380;
(*   %conv1.i.2.30.2 = sext i16 %700 to i32 *)
cast v_conv1_i_2_30_2@sint32 v700@sint16;
(*   %mul.i.2.30.2 = mul nsw i32 %conv1.i.2.30.2, 287 *)
mul v_mul_i_2_30_2 v_conv1_i_2_30_2 (287)@sint32;
(*   %call.i.2.30.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.30.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_30_2, v_call_i_2_30_2);
(*   %arrayidx11.2.30.2 = getelementptr inbounds i16, i16* %r, i64 158 *)
(*   %701 = load i16, i16* %arrayidx11.2.30.2, align 2, !tbaa !3 *)
mov v701 mem0_316;
(*   %sub.2.30.2 = sub i16 %701, %call.i.2.30.2 *)
sub v_sub_2_30_2 v701 v_call_i_2_30_2;
(*   store i16 %sub.2.30.2, i16* %arrayidx9.2.30.2, align 2, !tbaa !3 *)
mov mem0_380 v_sub_2_30_2;
(*   %add21.2.30.2 = add i16 %701, %call.i.2.30.2 *)
add v_add21_2_30_2 v701 v_call_i_2_30_2;
(*   store i16 %add21.2.30.2, i16* %arrayidx11.2.30.2, align 2, !tbaa !3 *)
mov mem0_316 v_add21_2_30_2;
(*   %arrayidx9.2.31.2 = getelementptr inbounds i16, i16* %r, i64 191 *)
(*   %702 = load i16, i16* %arrayidx9.2.31.2, align 2, !tbaa !3 *)
mov v702 mem0_382;
(*   %conv1.i.2.31.2 = sext i16 %702 to i32 *)
cast v_conv1_i_2_31_2@sint32 v702@sint16;
(*   %mul.i.2.31.2 = mul nsw i32 %conv1.i.2.31.2, 287 *)
mul v_mul_i_2_31_2 v_conv1_i_2_31_2 (287)@sint32;
(*   %call.i.2.31.2 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.31.2) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_31_2, v_call_i_2_31_2);
(*   %arrayidx11.2.31.2 = getelementptr inbounds i16, i16* %r, i64 159 *)
(*   %703 = load i16, i16* %arrayidx11.2.31.2, align 2, !tbaa !3 *)
mov v703 mem0_318;
(*   %sub.2.31.2 = sub i16 %703, %call.i.2.31.2 *)
sub v_sub_2_31_2 v703 v_call_i_2_31_2;
(*   store i16 %sub.2.31.2, i16* %arrayidx9.2.31.2, align 2, !tbaa !3 *)
mov mem0_382 v_sub_2_31_2;
(*   %add21.2.31.2 = add i16 %703, %call.i.2.31.2 *)
add v_add21_2_31_2 v703 v_call_i_2_31_2;
(*   store i16 %add21.2.31.2, i16* %arrayidx11.2.31.2, align 2, !tbaa !3 *)
mov mem0_318 v_add21_2_31_2;

(* NOTE: k = 7 *)

(*   %arrayidx9.2.3268 = getelementptr inbounds i16, i16* %r, i64 224 *)
(*   %704 = load i16, i16* %arrayidx9.2.3268, align 2, !tbaa !3 *)
mov v704 mem0_448;
(*   %conv1.i.2.3269 = sext i16 %704 to i32 *)
cast v_conv1_i_2_3269@sint32 v704@sint16;
(*   %mul.i.2.3270 = mul nsw i32 %conv1.i.2.3269, 202 *)
mul v_mul_i_2_3270 v_conv1_i_2_3269 (202)@sint32;
(*   %call.i.2.3271 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.3270) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_3270, v_call_i_2_3271);
(*   %arrayidx11.2.3272 = getelementptr inbounds i16, i16* %r, i64 192 *)
(*   %705 = load i16, i16* %arrayidx11.2.3272, align 2, !tbaa !3 *)
mov v705 mem0_384;
(*   %sub.2.3273 = sub i16 %705, %call.i.2.3271 *)
sub v_sub_2_3273 v705 v_call_i_2_3271;
(*   store i16 %sub.2.3273, i16* %arrayidx9.2.3268, align 2, !tbaa !3 *)
mov mem0_448 v_sub_2_3273;
(*   %add21.2.3274 = add i16 %705, %call.i.2.3271 *)
add v_add21_2_3274 v705 v_call_i_2_3271;
(*   store i16 %add21.2.3274, i16* %arrayidx11.2.3272, align 2, !tbaa !3 *)
mov mem0_384 v_add21_2_3274;
(*   %arrayidx9.2.1.3 = getelementptr inbounds i16, i16* %r, i64 225 *)
(*   %706 = load i16, i16* %arrayidx9.2.1.3, align 2, !tbaa !3 *)
mov v706 mem0_450;
(*   %conv1.i.2.1.3 = sext i16 %706 to i32 *)
cast v_conv1_i_2_1_3@sint32 v706@sint16;
(*   %mul.i.2.1.3 = mul nsw i32 %conv1.i.2.1.3, 202 *)
mul v_mul_i_2_1_3 v_conv1_i_2_1_3 (202)@sint32;
(*   %call.i.2.1.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.1.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_1_3, v_call_i_2_1_3);
(*   %arrayidx11.2.1.3 = getelementptr inbounds i16, i16* %r, i64 193 *)
(*   %707 = load i16, i16* %arrayidx11.2.1.3, align 2, !tbaa !3 *)
mov v707 mem0_386;
(*   %sub.2.1.3 = sub i16 %707, %call.i.2.1.3 *)
sub v_sub_2_1_3 v707 v_call_i_2_1_3;
(*   store i16 %sub.2.1.3, i16* %arrayidx9.2.1.3, align 2, !tbaa !3 *)
mov mem0_450 v_sub_2_1_3;
(*   %add21.2.1.3 = add i16 %707, %call.i.2.1.3 *)
add v_add21_2_1_3 v707 v_call_i_2_1_3;
(*   store i16 %add21.2.1.3, i16* %arrayidx11.2.1.3, align 2, !tbaa !3 *)
mov mem0_386 v_add21_2_1_3;
(*   %arrayidx9.2.2.3 = getelementptr inbounds i16, i16* %r, i64 226 *)
(*   %708 = load i16, i16* %arrayidx9.2.2.3, align 2, !tbaa !3 *)
mov v708 mem0_452;
(*   %conv1.i.2.2.3 = sext i16 %708 to i32 *)
cast v_conv1_i_2_2_3@sint32 v708@sint16;
(*   %mul.i.2.2.3 = mul nsw i32 %conv1.i.2.2.3, 202 *)
mul v_mul_i_2_2_3 v_conv1_i_2_2_3 (202)@sint32;
(*   %call.i.2.2.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.2.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_2_3, v_call_i_2_2_3);
(*   %arrayidx11.2.2.3 = getelementptr inbounds i16, i16* %r, i64 194 *)
(*   %709 = load i16, i16* %arrayidx11.2.2.3, align 2, !tbaa !3 *)
mov v709 mem0_388;
(*   %sub.2.2.3 = sub i16 %709, %call.i.2.2.3 *)
sub v_sub_2_2_3 v709 v_call_i_2_2_3;
(*   store i16 %sub.2.2.3, i16* %arrayidx9.2.2.3, align 2, !tbaa !3 *)
mov mem0_452 v_sub_2_2_3;
(*   %add21.2.2.3 = add i16 %709, %call.i.2.2.3 *)
add v_add21_2_2_3 v709 v_call_i_2_2_3;
(*   store i16 %add21.2.2.3, i16* %arrayidx11.2.2.3, align 2, !tbaa !3 *)
mov mem0_388 v_add21_2_2_3;
(*   %arrayidx9.2.3.3 = getelementptr inbounds i16, i16* %r, i64 227 *)
(*   %710 = load i16, i16* %arrayidx9.2.3.3, align 2, !tbaa !3 *)
mov v710 mem0_454;
(*   %conv1.i.2.3.3 = sext i16 %710 to i32 *)
cast v_conv1_i_2_3_3@sint32 v710@sint16;
(*   %mul.i.2.3.3 = mul nsw i32 %conv1.i.2.3.3, 202 *)
mul v_mul_i_2_3_3 v_conv1_i_2_3_3 (202)@sint32;
(*   %call.i.2.3.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.3.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_3_3, v_call_i_2_3_3);
(*   %arrayidx11.2.3.3 = getelementptr inbounds i16, i16* %r, i64 195 *)
(*   %711 = load i16, i16* %arrayidx11.2.3.3, align 2, !tbaa !3 *)
mov v711 mem0_390;
(*   %sub.2.3.3 = sub i16 %711, %call.i.2.3.3 *)
sub v_sub_2_3_3 v711 v_call_i_2_3_3;
(*   store i16 %sub.2.3.3, i16* %arrayidx9.2.3.3, align 2, !tbaa !3 *)
mov mem0_454 v_sub_2_3_3;
(*   %add21.2.3.3 = add i16 %711, %call.i.2.3.3 *)
add v_add21_2_3_3 v711 v_call_i_2_3_3;
(*   store i16 %add21.2.3.3, i16* %arrayidx11.2.3.3, align 2, !tbaa !3 *)
mov mem0_390 v_add21_2_3_3;
(*   %arrayidx9.2.4.3 = getelementptr inbounds i16, i16* %r, i64 228 *)
(*   %712 = load i16, i16* %arrayidx9.2.4.3, align 2, !tbaa !3 *)
mov v712 mem0_456;
(*   %conv1.i.2.4.3 = sext i16 %712 to i32 *)
cast v_conv1_i_2_4_3@sint32 v712@sint16;
(*   %mul.i.2.4.3 = mul nsw i32 %conv1.i.2.4.3, 202 *)
mul v_mul_i_2_4_3 v_conv1_i_2_4_3 (202)@sint32;
(*   %call.i.2.4.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.4.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_4_3, v_call_i_2_4_3);
(*   %arrayidx11.2.4.3 = getelementptr inbounds i16, i16* %r, i64 196 *)
(*   %713 = load i16, i16* %arrayidx11.2.4.3, align 2, !tbaa !3 *)
mov v713 mem0_392;
(*   %sub.2.4.3 = sub i16 %713, %call.i.2.4.3 *)
sub v_sub_2_4_3 v713 v_call_i_2_4_3;
(*   store i16 %sub.2.4.3, i16* %arrayidx9.2.4.3, align 2, !tbaa !3 *)
mov mem0_456 v_sub_2_4_3;
(*   %add21.2.4.3 = add i16 %713, %call.i.2.4.3 *)
add v_add21_2_4_3 v713 v_call_i_2_4_3;
(*   store i16 %add21.2.4.3, i16* %arrayidx11.2.4.3, align 2, !tbaa !3 *)
mov mem0_392 v_add21_2_4_3;
(*   %arrayidx9.2.5.3 = getelementptr inbounds i16, i16* %r, i64 229 *)
(*   %714 = load i16, i16* %arrayidx9.2.5.3, align 2, !tbaa !3 *)
mov v714 mem0_458;
(*   %conv1.i.2.5.3 = sext i16 %714 to i32 *)
cast v_conv1_i_2_5_3@sint32 v714@sint16;
(*   %mul.i.2.5.3 = mul nsw i32 %conv1.i.2.5.3, 202 *)
mul v_mul_i_2_5_3 v_conv1_i_2_5_3 (202)@sint32;
(*   %call.i.2.5.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.5.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_5_3, v_call_i_2_5_3);
(*   %arrayidx11.2.5.3 = getelementptr inbounds i16, i16* %r, i64 197 *)
(*   %715 = load i16, i16* %arrayidx11.2.5.3, align 2, !tbaa !3 *)
mov v715 mem0_394;
(*   %sub.2.5.3 = sub i16 %715, %call.i.2.5.3 *)
sub v_sub_2_5_3 v715 v_call_i_2_5_3;
(*   store i16 %sub.2.5.3, i16* %arrayidx9.2.5.3, align 2, !tbaa !3 *)
mov mem0_458 v_sub_2_5_3;
(*   %add21.2.5.3 = add i16 %715, %call.i.2.5.3 *)
add v_add21_2_5_3 v715 v_call_i_2_5_3;
(*   store i16 %add21.2.5.3, i16* %arrayidx11.2.5.3, align 2, !tbaa !3 *)
mov mem0_394 v_add21_2_5_3;
(*   %arrayidx9.2.6.3 = getelementptr inbounds i16, i16* %r, i64 230 *)
(*   %716 = load i16, i16* %arrayidx9.2.6.3, align 2, !tbaa !3 *)
mov v716 mem0_460;
(*   %conv1.i.2.6.3 = sext i16 %716 to i32 *)
cast v_conv1_i_2_6_3@sint32 v716@sint16;
(*   %mul.i.2.6.3 = mul nsw i32 %conv1.i.2.6.3, 202 *)
mul v_mul_i_2_6_3 v_conv1_i_2_6_3 (202)@sint32;
(*   %call.i.2.6.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.6.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_6_3, v_call_i_2_6_3);
(*   %arrayidx11.2.6.3 = getelementptr inbounds i16, i16* %r, i64 198 *)
(*   %717 = load i16, i16* %arrayidx11.2.6.3, align 2, !tbaa !3 *)
mov v717 mem0_396;
(*   %sub.2.6.3 = sub i16 %717, %call.i.2.6.3 *)
sub v_sub_2_6_3 v717 v_call_i_2_6_3;
(*   store i16 %sub.2.6.3, i16* %arrayidx9.2.6.3, align 2, !tbaa !3 *)
mov mem0_460 v_sub_2_6_3;
(*   %add21.2.6.3 = add i16 %717, %call.i.2.6.3 *)
add v_add21_2_6_3 v717 v_call_i_2_6_3;
(*   store i16 %add21.2.6.3, i16* %arrayidx11.2.6.3, align 2, !tbaa !3 *)
mov mem0_396 v_add21_2_6_3;
(*   %arrayidx9.2.7.3 = getelementptr inbounds i16, i16* %r, i64 231 *)
(*   %718 = load i16, i16* %arrayidx9.2.7.3, align 2, !tbaa !3 *)
mov v718 mem0_462;
(*   %conv1.i.2.7.3 = sext i16 %718 to i32 *)
cast v_conv1_i_2_7_3@sint32 v718@sint16;
(*   %mul.i.2.7.3 = mul nsw i32 %conv1.i.2.7.3, 202 *)
mul v_mul_i_2_7_3 v_conv1_i_2_7_3 (202)@sint32;
(*   %call.i.2.7.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.7.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_7_3, v_call_i_2_7_3);
(*   %arrayidx11.2.7.3 = getelementptr inbounds i16, i16* %r, i64 199 *)
(*   %719 = load i16, i16* %arrayidx11.2.7.3, align 2, !tbaa !3 *)
mov v719 mem0_398;
(*   %sub.2.7.3 = sub i16 %719, %call.i.2.7.3 *)
sub v_sub_2_7_3 v719 v_call_i_2_7_3;
(*   store i16 %sub.2.7.3, i16* %arrayidx9.2.7.3, align 2, !tbaa !3 *)
mov mem0_462 v_sub_2_7_3;
(*   %add21.2.7.3 = add i16 %719, %call.i.2.7.3 *)
add v_add21_2_7_3 v719 v_call_i_2_7_3;
(*   store i16 %add21.2.7.3, i16* %arrayidx11.2.7.3, align 2, !tbaa !3 *)
mov mem0_398 v_add21_2_7_3;
(*   %arrayidx9.2.8.3 = getelementptr inbounds i16, i16* %r, i64 232 *)
(*   %720 = load i16, i16* %arrayidx9.2.8.3, align 2, !tbaa !3 *)
mov v720 mem0_464;
(*   %conv1.i.2.8.3 = sext i16 %720 to i32 *)
cast v_conv1_i_2_8_3@sint32 v720@sint16;
(*   %mul.i.2.8.3 = mul nsw i32 %conv1.i.2.8.3, 202 *)
mul v_mul_i_2_8_3 v_conv1_i_2_8_3 (202)@sint32;
(*   %call.i.2.8.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.8.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_8_3, v_call_i_2_8_3);
(*   %arrayidx11.2.8.3 = getelementptr inbounds i16, i16* %r, i64 200 *)
(*   %721 = load i16, i16* %arrayidx11.2.8.3, align 2, !tbaa !3 *)
mov v721 mem0_400;
(*   %sub.2.8.3 = sub i16 %721, %call.i.2.8.3 *)
sub v_sub_2_8_3 v721 v_call_i_2_8_3;
(*   store i16 %sub.2.8.3, i16* %arrayidx9.2.8.3, align 2, !tbaa !3 *)
mov mem0_464 v_sub_2_8_3;
(*   %add21.2.8.3 = add i16 %721, %call.i.2.8.3 *)
add v_add21_2_8_3 v721 v_call_i_2_8_3;
(*   store i16 %add21.2.8.3, i16* %arrayidx11.2.8.3, align 2, !tbaa !3 *)
mov mem0_400 v_add21_2_8_3;
(*   %arrayidx9.2.9.3 = getelementptr inbounds i16, i16* %r, i64 233 *)
(*   %722 = load i16, i16* %arrayidx9.2.9.3, align 2, !tbaa !3 *)
mov v722 mem0_466;
(*   %conv1.i.2.9.3 = sext i16 %722 to i32 *)
cast v_conv1_i_2_9_3@sint32 v722@sint16;
(*   %mul.i.2.9.3 = mul nsw i32 %conv1.i.2.9.3, 202 *)
mul v_mul_i_2_9_3 v_conv1_i_2_9_3 (202)@sint32;
(*   %call.i.2.9.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.9.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_9_3, v_call_i_2_9_3);
(*   %arrayidx11.2.9.3 = getelementptr inbounds i16, i16* %r, i64 201 *)
(*   %723 = load i16, i16* %arrayidx11.2.9.3, align 2, !tbaa !3 *)
mov v723 mem0_402;
(*   %sub.2.9.3 = sub i16 %723, %call.i.2.9.3 *)
sub v_sub_2_9_3 v723 v_call_i_2_9_3;
(*   store i16 %sub.2.9.3, i16* %arrayidx9.2.9.3, align 2, !tbaa !3 *)
mov mem0_466 v_sub_2_9_3;
(*   %add21.2.9.3 = add i16 %723, %call.i.2.9.3 *)
add v_add21_2_9_3 v723 v_call_i_2_9_3;
(*   store i16 %add21.2.9.3, i16* %arrayidx11.2.9.3, align 2, !tbaa !3 *)
mov mem0_402 v_add21_2_9_3;
(*   %arrayidx9.2.10.3 = getelementptr inbounds i16, i16* %r, i64 234 *)
(*   %724 = load i16, i16* %arrayidx9.2.10.3, align 2, !tbaa !3 *)
mov v724 mem0_468;
(*   %conv1.i.2.10.3 = sext i16 %724 to i32 *)
cast v_conv1_i_2_10_3@sint32 v724@sint16;
(*   %mul.i.2.10.3 = mul nsw i32 %conv1.i.2.10.3, 202 *)
mul v_mul_i_2_10_3 v_conv1_i_2_10_3 (202)@sint32;
(*   %call.i.2.10.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.10.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_10_3, v_call_i_2_10_3);
(*   %arrayidx11.2.10.3 = getelementptr inbounds i16, i16* %r, i64 202 *)
(*   %725 = load i16, i16* %arrayidx11.2.10.3, align 2, !tbaa !3 *)
mov v725 mem0_404;
(*   %sub.2.10.3 = sub i16 %725, %call.i.2.10.3 *)
sub v_sub_2_10_3 v725 v_call_i_2_10_3;
(*   store i16 %sub.2.10.3, i16* %arrayidx9.2.10.3, align 2, !tbaa !3 *)
mov mem0_468 v_sub_2_10_3;
(*   %add21.2.10.3 = add i16 %725, %call.i.2.10.3 *)
add v_add21_2_10_3 v725 v_call_i_2_10_3;
(*   store i16 %add21.2.10.3, i16* %arrayidx11.2.10.3, align 2, !tbaa !3 *)
mov mem0_404 v_add21_2_10_3;
(*   %arrayidx9.2.11.3 = getelementptr inbounds i16, i16* %r, i64 235 *)
(*   %726 = load i16, i16* %arrayidx9.2.11.3, align 2, !tbaa !3 *)
mov v726 mem0_470;
(*   %conv1.i.2.11.3 = sext i16 %726 to i32 *)
cast v_conv1_i_2_11_3@sint32 v726@sint16;
(*   %mul.i.2.11.3 = mul nsw i32 %conv1.i.2.11.3, 202 *)
mul v_mul_i_2_11_3 v_conv1_i_2_11_3 (202)@sint32;
(*   %call.i.2.11.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.11.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_11_3, v_call_i_2_11_3);
(*   %arrayidx11.2.11.3 = getelementptr inbounds i16, i16* %r, i64 203 *)
(*   %727 = load i16, i16* %arrayidx11.2.11.3, align 2, !tbaa !3 *)
mov v727 mem0_406;
(*   %sub.2.11.3 = sub i16 %727, %call.i.2.11.3 *)
sub v_sub_2_11_3 v727 v_call_i_2_11_3;
(*   store i16 %sub.2.11.3, i16* %arrayidx9.2.11.3, align 2, !tbaa !3 *)
mov mem0_470 v_sub_2_11_3;
(*   %add21.2.11.3 = add i16 %727, %call.i.2.11.3 *)
add v_add21_2_11_3 v727 v_call_i_2_11_3;
(*   store i16 %add21.2.11.3, i16* %arrayidx11.2.11.3, align 2, !tbaa !3 *)
mov mem0_406 v_add21_2_11_3;
(*   %arrayidx9.2.12.3 = getelementptr inbounds i16, i16* %r, i64 236 *)
(*   %728 = load i16, i16* %arrayidx9.2.12.3, align 2, !tbaa !3 *)
mov v728 mem0_472;
(*   %conv1.i.2.12.3 = sext i16 %728 to i32 *)
cast v_conv1_i_2_12_3@sint32 v728@sint16;
(*   %mul.i.2.12.3 = mul nsw i32 %conv1.i.2.12.3, 202 *)
mul v_mul_i_2_12_3 v_conv1_i_2_12_3 (202)@sint32;
(*   %call.i.2.12.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.12.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_12_3, v_call_i_2_12_3);
(*   %arrayidx11.2.12.3 = getelementptr inbounds i16, i16* %r, i64 204 *)
(*   %729 = load i16, i16* %arrayidx11.2.12.3, align 2, !tbaa !3 *)
mov v729 mem0_408;
(*   %sub.2.12.3 = sub i16 %729, %call.i.2.12.3 *)
sub v_sub_2_12_3 v729 v_call_i_2_12_3;
(*   store i16 %sub.2.12.3, i16* %arrayidx9.2.12.3, align 2, !tbaa !3 *)
mov mem0_472 v_sub_2_12_3;
(*   %add21.2.12.3 = add i16 %729, %call.i.2.12.3 *)
add v_add21_2_12_3 v729 v_call_i_2_12_3;
(*   store i16 %add21.2.12.3, i16* %arrayidx11.2.12.3, align 2, !tbaa !3 *)
mov mem0_408 v_add21_2_12_3;
(*   %arrayidx9.2.13.3 = getelementptr inbounds i16, i16* %r, i64 237 *)
(*   %730 = load i16, i16* %arrayidx9.2.13.3, align 2, !tbaa !3 *)
mov v730 mem0_474;
(*   %conv1.i.2.13.3 = sext i16 %730 to i32 *)
cast v_conv1_i_2_13_3@sint32 v730@sint16;
(*   %mul.i.2.13.3 = mul nsw i32 %conv1.i.2.13.3, 202 *)
mul v_mul_i_2_13_3 v_conv1_i_2_13_3 (202)@sint32;
(*   %call.i.2.13.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.13.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_13_3, v_call_i_2_13_3);
(*   %arrayidx11.2.13.3 = getelementptr inbounds i16, i16* %r, i64 205 *)
(*   %731 = load i16, i16* %arrayidx11.2.13.3, align 2, !tbaa !3 *)
mov v731 mem0_410;
(*   %sub.2.13.3 = sub i16 %731, %call.i.2.13.3 *)
sub v_sub_2_13_3 v731 v_call_i_2_13_3;
(*   store i16 %sub.2.13.3, i16* %arrayidx9.2.13.3, align 2, !tbaa !3 *)
mov mem0_474 v_sub_2_13_3;
(*   %add21.2.13.3 = add i16 %731, %call.i.2.13.3 *)
add v_add21_2_13_3 v731 v_call_i_2_13_3;
(*   store i16 %add21.2.13.3, i16* %arrayidx11.2.13.3, align 2, !tbaa !3 *)
mov mem0_410 v_add21_2_13_3;
(*   %arrayidx9.2.14.3 = getelementptr inbounds i16, i16* %r, i64 238 *)
(*   %732 = load i16, i16* %arrayidx9.2.14.3, align 2, !tbaa !3 *)
mov v732 mem0_476;
(*   %conv1.i.2.14.3 = sext i16 %732 to i32 *)
cast v_conv1_i_2_14_3@sint32 v732@sint16;
(*   %mul.i.2.14.3 = mul nsw i32 %conv1.i.2.14.3, 202 *)
mul v_mul_i_2_14_3 v_conv1_i_2_14_3 (202)@sint32;
(*   %call.i.2.14.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.14.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_14_3, v_call_i_2_14_3);
(*   %arrayidx11.2.14.3 = getelementptr inbounds i16, i16* %r, i64 206 *)
(*   %733 = load i16, i16* %arrayidx11.2.14.3, align 2, !tbaa !3 *)
mov v733 mem0_412;
(*   %sub.2.14.3 = sub i16 %733, %call.i.2.14.3 *)
sub v_sub_2_14_3 v733 v_call_i_2_14_3;
(*   store i16 %sub.2.14.3, i16* %arrayidx9.2.14.3, align 2, !tbaa !3 *)
mov mem0_476 v_sub_2_14_3;
(*   %add21.2.14.3 = add i16 %733, %call.i.2.14.3 *)
add v_add21_2_14_3 v733 v_call_i_2_14_3;
(*   store i16 %add21.2.14.3, i16* %arrayidx11.2.14.3, align 2, !tbaa !3 *)
mov mem0_412 v_add21_2_14_3;
(*   %arrayidx9.2.15.3 = getelementptr inbounds i16, i16* %r, i64 239 *)
(*   %734 = load i16, i16* %arrayidx9.2.15.3, align 2, !tbaa !3 *)
mov v734 mem0_478;
(*   %conv1.i.2.15.3 = sext i16 %734 to i32 *)
cast v_conv1_i_2_15_3@sint32 v734@sint16;
(*   %mul.i.2.15.3 = mul nsw i32 %conv1.i.2.15.3, 202 *)
mul v_mul_i_2_15_3 v_conv1_i_2_15_3 (202)@sint32;
(*   %call.i.2.15.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.15.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_15_3, v_call_i_2_15_3);
(*   %arrayidx11.2.15.3 = getelementptr inbounds i16, i16* %r, i64 207 *)
(*   %735 = load i16, i16* %arrayidx11.2.15.3, align 2, !tbaa !3 *)
mov v735 mem0_414;
(*   %sub.2.15.3 = sub i16 %735, %call.i.2.15.3 *)
sub v_sub_2_15_3 v735 v_call_i_2_15_3;
(*   store i16 %sub.2.15.3, i16* %arrayidx9.2.15.3, align 2, !tbaa !3 *)
mov mem0_478 v_sub_2_15_3;
(*   %add21.2.15.3 = add i16 %735, %call.i.2.15.3 *)
add v_add21_2_15_3 v735 v_call_i_2_15_3;
(*   store i16 %add21.2.15.3, i16* %arrayidx11.2.15.3, align 2, !tbaa !3 *)
mov mem0_414 v_add21_2_15_3;
(*   %arrayidx9.2.16.3 = getelementptr inbounds i16, i16* %r, i64 240 *)
(*   %736 = load i16, i16* %arrayidx9.2.16.3, align 2, !tbaa !3 *)
mov v736 mem0_480;
(*   %conv1.i.2.16.3 = sext i16 %736 to i32 *)
cast v_conv1_i_2_16_3@sint32 v736@sint16;
(*   %mul.i.2.16.3 = mul nsw i32 %conv1.i.2.16.3, 202 *)
mul v_mul_i_2_16_3 v_conv1_i_2_16_3 (202)@sint32;
(*   %call.i.2.16.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.16.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_16_3, v_call_i_2_16_3);
(*   %arrayidx11.2.16.3 = getelementptr inbounds i16, i16* %r, i64 208 *)
(*   %737 = load i16, i16* %arrayidx11.2.16.3, align 2, !tbaa !3 *)
mov v737 mem0_416;
(*   %sub.2.16.3 = sub i16 %737, %call.i.2.16.3 *)
sub v_sub_2_16_3 v737 v_call_i_2_16_3;
(*   store i16 %sub.2.16.3, i16* %arrayidx9.2.16.3, align 2, !tbaa !3 *)
mov mem0_480 v_sub_2_16_3;
(*   %add21.2.16.3 = add i16 %737, %call.i.2.16.3 *)
add v_add21_2_16_3 v737 v_call_i_2_16_3;
(*   store i16 %add21.2.16.3, i16* %arrayidx11.2.16.3, align 2, !tbaa !3 *)
mov mem0_416 v_add21_2_16_3;
(*   %arrayidx9.2.17.3 = getelementptr inbounds i16, i16* %r, i64 241 *)
(*   %738 = load i16, i16* %arrayidx9.2.17.3, align 2, !tbaa !3 *)
mov v738 mem0_482;
(*   %conv1.i.2.17.3 = sext i16 %738 to i32 *)
cast v_conv1_i_2_17_3@sint32 v738@sint16;
(*   %mul.i.2.17.3 = mul nsw i32 %conv1.i.2.17.3, 202 *)
mul v_mul_i_2_17_3 v_conv1_i_2_17_3 (202)@sint32;
(*   %call.i.2.17.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.17.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_17_3, v_call_i_2_17_3);
(*   %arrayidx11.2.17.3 = getelementptr inbounds i16, i16* %r, i64 209 *)
(*   %739 = load i16, i16* %arrayidx11.2.17.3, align 2, !tbaa !3 *)
mov v739 mem0_418;
(*   %sub.2.17.3 = sub i16 %739, %call.i.2.17.3 *)
sub v_sub_2_17_3 v739 v_call_i_2_17_3;
(*   store i16 %sub.2.17.3, i16* %arrayidx9.2.17.3, align 2, !tbaa !3 *)
mov mem0_482 v_sub_2_17_3;
(*   %add21.2.17.3 = add i16 %739, %call.i.2.17.3 *)
add v_add21_2_17_3 v739 v_call_i_2_17_3;
(*   store i16 %add21.2.17.3, i16* %arrayidx11.2.17.3, align 2, !tbaa !3 *)
mov mem0_418 v_add21_2_17_3;
(*   %arrayidx9.2.18.3 = getelementptr inbounds i16, i16* %r, i64 242 *)
(*   %740 = load i16, i16* %arrayidx9.2.18.3, align 2, !tbaa !3 *)
mov v740 mem0_484;
(*   %conv1.i.2.18.3 = sext i16 %740 to i32 *)
cast v_conv1_i_2_18_3@sint32 v740@sint16;
(*   %mul.i.2.18.3 = mul nsw i32 %conv1.i.2.18.3, 202 *)
mul v_mul_i_2_18_3 v_conv1_i_2_18_3 (202)@sint32;
(*   %call.i.2.18.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.18.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_18_3, v_call_i_2_18_3);
(*   %arrayidx11.2.18.3 = getelementptr inbounds i16, i16* %r, i64 210 *)
(*   %741 = load i16, i16* %arrayidx11.2.18.3, align 2, !tbaa !3 *)
mov v741 mem0_420;
(*   %sub.2.18.3 = sub i16 %741, %call.i.2.18.3 *)
sub v_sub_2_18_3 v741 v_call_i_2_18_3;
(*   store i16 %sub.2.18.3, i16* %arrayidx9.2.18.3, align 2, !tbaa !3 *)
mov mem0_484 v_sub_2_18_3;
(*   %add21.2.18.3 = add i16 %741, %call.i.2.18.3 *)
add v_add21_2_18_3 v741 v_call_i_2_18_3;
(*   store i16 %add21.2.18.3, i16* %arrayidx11.2.18.3, align 2, !tbaa !3 *)
mov mem0_420 v_add21_2_18_3;
(*   %arrayidx9.2.19.3 = getelementptr inbounds i16, i16* %r, i64 243 *)
(*   %742 = load i16, i16* %arrayidx9.2.19.3, align 2, !tbaa !3 *)
mov v742 mem0_486;
(*   %conv1.i.2.19.3 = sext i16 %742 to i32 *)
cast v_conv1_i_2_19_3@sint32 v742@sint16;
(*   %mul.i.2.19.3 = mul nsw i32 %conv1.i.2.19.3, 202 *)
mul v_mul_i_2_19_3 v_conv1_i_2_19_3 (202)@sint32;
(*   %call.i.2.19.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.19.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_19_3, v_call_i_2_19_3);
(*   %arrayidx11.2.19.3 = getelementptr inbounds i16, i16* %r, i64 211 *)
(*   %743 = load i16, i16* %arrayidx11.2.19.3, align 2, !tbaa !3 *)
mov v743 mem0_422;
(*   %sub.2.19.3 = sub i16 %743, %call.i.2.19.3 *)
sub v_sub_2_19_3 v743 v_call_i_2_19_3;
(*   store i16 %sub.2.19.3, i16* %arrayidx9.2.19.3, align 2, !tbaa !3 *)
mov mem0_486 v_sub_2_19_3;
(*   %add21.2.19.3 = add i16 %743, %call.i.2.19.3 *)
add v_add21_2_19_3 v743 v_call_i_2_19_3;
(*   store i16 %add21.2.19.3, i16* %arrayidx11.2.19.3, align 2, !tbaa !3 *)
mov mem0_422 v_add21_2_19_3;
(*   %arrayidx9.2.20.3 = getelementptr inbounds i16, i16* %r, i64 244 *)
(*   %744 = load i16, i16* %arrayidx9.2.20.3, align 2, !tbaa !3 *)
mov v744 mem0_488;
(*   %conv1.i.2.20.3 = sext i16 %744 to i32 *)
cast v_conv1_i_2_20_3@sint32 v744@sint16;
(*   %mul.i.2.20.3 = mul nsw i32 %conv1.i.2.20.3, 202 *)
mul v_mul_i_2_20_3 v_conv1_i_2_20_3 (202)@sint32;
(*   %call.i.2.20.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.20.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_20_3, v_call_i_2_20_3);
(*   %arrayidx11.2.20.3 = getelementptr inbounds i16, i16* %r, i64 212 *)
(*   %745 = load i16, i16* %arrayidx11.2.20.3, align 2, !tbaa !3 *)
mov v745 mem0_424;
(*   %sub.2.20.3 = sub i16 %745, %call.i.2.20.3 *)
sub v_sub_2_20_3 v745 v_call_i_2_20_3;
(*   store i16 %sub.2.20.3, i16* %arrayidx9.2.20.3, align 2, !tbaa !3 *)
mov mem0_488 v_sub_2_20_3;
(*   %add21.2.20.3 = add i16 %745, %call.i.2.20.3 *)
add v_add21_2_20_3 v745 v_call_i_2_20_3;
(*   store i16 %add21.2.20.3, i16* %arrayidx11.2.20.3, align 2, !tbaa !3 *)
mov mem0_424 v_add21_2_20_3;
(*   %arrayidx9.2.21.3 = getelementptr inbounds i16, i16* %r, i64 245 *)
(*   %746 = load i16, i16* %arrayidx9.2.21.3, align 2, !tbaa !3 *)
mov v746 mem0_490;
(*   %conv1.i.2.21.3 = sext i16 %746 to i32 *)
cast v_conv1_i_2_21_3@sint32 v746@sint16;
(*   %mul.i.2.21.3 = mul nsw i32 %conv1.i.2.21.3, 202 *)
mul v_mul_i_2_21_3 v_conv1_i_2_21_3 (202)@sint32;
(*   %call.i.2.21.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.21.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_21_3, v_call_i_2_21_3);
(*   %arrayidx11.2.21.3 = getelementptr inbounds i16, i16* %r, i64 213 *)
(*   %747 = load i16, i16* %arrayidx11.2.21.3, align 2, !tbaa !3 *)
mov v747 mem0_426;
(*   %sub.2.21.3 = sub i16 %747, %call.i.2.21.3 *)
sub v_sub_2_21_3 v747 v_call_i_2_21_3;
(*   store i16 %sub.2.21.3, i16* %arrayidx9.2.21.3, align 2, !tbaa !3 *)
mov mem0_490 v_sub_2_21_3;
(*   %add21.2.21.3 = add i16 %747, %call.i.2.21.3 *)
add v_add21_2_21_3 v747 v_call_i_2_21_3;
(*   store i16 %add21.2.21.3, i16* %arrayidx11.2.21.3, align 2, !tbaa !3 *)
mov mem0_426 v_add21_2_21_3;
(*   %arrayidx9.2.22.3 = getelementptr inbounds i16, i16* %r, i64 246 *)
(*   %748 = load i16, i16* %arrayidx9.2.22.3, align 2, !tbaa !3 *)
mov v748 mem0_492;
(*   %conv1.i.2.22.3 = sext i16 %748 to i32 *)
cast v_conv1_i_2_22_3@sint32 v748@sint16;
(*   %mul.i.2.22.3 = mul nsw i32 %conv1.i.2.22.3, 202 *)
mul v_mul_i_2_22_3 v_conv1_i_2_22_3 (202)@sint32;
(*   %call.i.2.22.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.22.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_22_3, v_call_i_2_22_3);
(*   %arrayidx11.2.22.3 = getelementptr inbounds i16, i16* %r, i64 214 *)
(*   %749 = load i16, i16* %arrayidx11.2.22.3, align 2, !tbaa !3 *)
mov v749 mem0_428;
(*   %sub.2.22.3 = sub i16 %749, %call.i.2.22.3 *)
sub v_sub_2_22_3 v749 v_call_i_2_22_3;
(*   store i16 %sub.2.22.3, i16* %arrayidx9.2.22.3, align 2, !tbaa !3 *)
mov mem0_492 v_sub_2_22_3;
(*   %add21.2.22.3 = add i16 %749, %call.i.2.22.3 *)
add v_add21_2_22_3 v749 v_call_i_2_22_3;
(*   store i16 %add21.2.22.3, i16* %arrayidx11.2.22.3, align 2, !tbaa !3 *)
mov mem0_428 v_add21_2_22_3;
(*   %arrayidx9.2.23.3 = getelementptr inbounds i16, i16* %r, i64 247 *)
(*   %750 = load i16, i16* %arrayidx9.2.23.3, align 2, !tbaa !3 *)
mov v750 mem0_494;
(*   %conv1.i.2.23.3 = sext i16 %750 to i32 *)
cast v_conv1_i_2_23_3@sint32 v750@sint16;
(*   %mul.i.2.23.3 = mul nsw i32 %conv1.i.2.23.3, 202 *)
mul v_mul_i_2_23_3 v_conv1_i_2_23_3 (202)@sint32;
(*   %call.i.2.23.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.23.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_23_3, v_call_i_2_23_3);
(*   %arrayidx11.2.23.3 = getelementptr inbounds i16, i16* %r, i64 215 *)
(*   %751 = load i16, i16* %arrayidx11.2.23.3, align 2, !tbaa !3 *)
mov v751 mem0_430;
(*   %sub.2.23.3 = sub i16 %751, %call.i.2.23.3 *)
sub v_sub_2_23_3 v751 v_call_i_2_23_3;
(*   store i16 %sub.2.23.3, i16* %arrayidx9.2.23.3, align 2, !tbaa !3 *)
mov mem0_494 v_sub_2_23_3;
(*   %add21.2.23.3 = add i16 %751, %call.i.2.23.3 *)
add v_add21_2_23_3 v751 v_call_i_2_23_3;
(*   store i16 %add21.2.23.3, i16* %arrayidx11.2.23.3, align 2, !tbaa !3 *)
mov mem0_430 v_add21_2_23_3;
(*   %arrayidx9.2.24.3 = getelementptr inbounds i16, i16* %r, i64 248 *)
(*   %752 = load i16, i16* %arrayidx9.2.24.3, align 2, !tbaa !3 *)
mov v752 mem0_496;
(*   %conv1.i.2.24.3 = sext i16 %752 to i32 *)
cast v_conv1_i_2_24_3@sint32 v752@sint16;
(*   %mul.i.2.24.3 = mul nsw i32 %conv1.i.2.24.3, 202 *)
mul v_mul_i_2_24_3 v_conv1_i_2_24_3 (202)@sint32;
(*   %call.i.2.24.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.24.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_24_3, v_call_i_2_24_3);
(*   %arrayidx11.2.24.3 = getelementptr inbounds i16, i16* %r, i64 216 *)
(*   %753 = load i16, i16* %arrayidx11.2.24.3, align 2, !tbaa !3 *)
mov v753 mem0_432;
(*   %sub.2.24.3 = sub i16 %753, %call.i.2.24.3 *)
sub v_sub_2_24_3 v753 v_call_i_2_24_3;
(*   store i16 %sub.2.24.3, i16* %arrayidx9.2.24.3, align 2, !tbaa !3 *)
mov mem0_496 v_sub_2_24_3;
(*   %add21.2.24.3 = add i16 %753, %call.i.2.24.3 *)
add v_add21_2_24_3 v753 v_call_i_2_24_3;
(*   store i16 %add21.2.24.3, i16* %arrayidx11.2.24.3, align 2, !tbaa !3 *)
mov mem0_432 v_add21_2_24_3;
(*   %arrayidx9.2.25.3 = getelementptr inbounds i16, i16* %r, i64 249 *)
(*   %754 = load i16, i16* %arrayidx9.2.25.3, align 2, !tbaa !3 *)
mov v754 mem0_498;
(*   %conv1.i.2.25.3 = sext i16 %754 to i32 *)
cast v_conv1_i_2_25_3@sint32 v754@sint16;
(*   %mul.i.2.25.3 = mul nsw i32 %conv1.i.2.25.3, 202 *)
mul v_mul_i_2_25_3 v_conv1_i_2_25_3 (202)@sint32;
(*   %call.i.2.25.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.25.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_25_3, v_call_i_2_25_3);
(*   %arrayidx11.2.25.3 = getelementptr inbounds i16, i16* %r, i64 217 *)
(*   %755 = load i16, i16* %arrayidx11.2.25.3, align 2, !tbaa !3 *)
mov v755 mem0_434;
(*   %sub.2.25.3 = sub i16 %755, %call.i.2.25.3 *)
sub v_sub_2_25_3 v755 v_call_i_2_25_3;
(*   store i16 %sub.2.25.3, i16* %arrayidx9.2.25.3, align 2, !tbaa !3 *)
mov mem0_498 v_sub_2_25_3;
(*   %add21.2.25.3 = add i16 %755, %call.i.2.25.3 *)
add v_add21_2_25_3 v755 v_call_i_2_25_3;
(*   store i16 %add21.2.25.3, i16* %arrayidx11.2.25.3, align 2, !tbaa !3 *)
mov mem0_434 v_add21_2_25_3;
(*   %arrayidx9.2.26.3 = getelementptr inbounds i16, i16* %r, i64 250 *)
(*   %756 = load i16, i16* %arrayidx9.2.26.3, align 2, !tbaa !3 *)
mov v756 mem0_500;
(*   %conv1.i.2.26.3 = sext i16 %756 to i32 *)
cast v_conv1_i_2_26_3@sint32 v756@sint16;
(*   %mul.i.2.26.3 = mul nsw i32 %conv1.i.2.26.3, 202 *)
mul v_mul_i_2_26_3 v_conv1_i_2_26_3 (202)@sint32;
(*   %call.i.2.26.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.26.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_26_3, v_call_i_2_26_3);
(*   %arrayidx11.2.26.3 = getelementptr inbounds i16, i16* %r, i64 218 *)
(*   %757 = load i16, i16* %arrayidx11.2.26.3, align 2, !tbaa !3 *)
mov v757 mem0_436;
(*   %sub.2.26.3 = sub i16 %757, %call.i.2.26.3 *)
sub v_sub_2_26_3 v757 v_call_i_2_26_3;
(*   store i16 %sub.2.26.3, i16* %arrayidx9.2.26.3, align 2, !tbaa !3 *)
mov mem0_500 v_sub_2_26_3;
(*   %add21.2.26.3 = add i16 %757, %call.i.2.26.3 *)
add v_add21_2_26_3 v757 v_call_i_2_26_3;
(*   store i16 %add21.2.26.3, i16* %arrayidx11.2.26.3, align 2, !tbaa !3 *)
mov mem0_436 v_add21_2_26_3;
(*   %arrayidx9.2.27.3 = getelementptr inbounds i16, i16* %r, i64 251 *)
(*   %758 = load i16, i16* %arrayidx9.2.27.3, align 2, !tbaa !3 *)
mov v758 mem0_502;
(*   %conv1.i.2.27.3 = sext i16 %758 to i32 *)
cast v_conv1_i_2_27_3@sint32 v758@sint16;
(*   %mul.i.2.27.3 = mul nsw i32 %conv1.i.2.27.3, 202 *)
mul v_mul_i_2_27_3 v_conv1_i_2_27_3 (202)@sint32;
(*   %call.i.2.27.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.27.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_27_3, v_call_i_2_27_3);
(*   %arrayidx11.2.27.3 = getelementptr inbounds i16, i16* %r, i64 219 *)
(*   %759 = load i16, i16* %arrayidx11.2.27.3, align 2, !tbaa !3 *)
mov v759 mem0_438;
(*   %sub.2.27.3 = sub i16 %759, %call.i.2.27.3 *)
sub v_sub_2_27_3 v759 v_call_i_2_27_3;
(*   store i16 %sub.2.27.3, i16* %arrayidx9.2.27.3, align 2, !tbaa !3 *)
mov mem0_502 v_sub_2_27_3;
(*   %add21.2.27.3 = add i16 %759, %call.i.2.27.3 *)
add v_add21_2_27_3 v759 v_call_i_2_27_3;
(*   store i16 %add21.2.27.3, i16* %arrayidx11.2.27.3, align 2, !tbaa !3 *)
mov mem0_438 v_add21_2_27_3;
(*   %arrayidx9.2.28.3 = getelementptr inbounds i16, i16* %r, i64 252 *)
(*   %760 = load i16, i16* %arrayidx9.2.28.3, align 2, !tbaa !3 *)
mov v760 mem0_504;
(*   %conv1.i.2.28.3 = sext i16 %760 to i32 *)
cast v_conv1_i_2_28_3@sint32 v760@sint16;
(*   %mul.i.2.28.3 = mul nsw i32 %conv1.i.2.28.3, 202 *)
mul v_mul_i_2_28_3 v_conv1_i_2_28_3 (202)@sint32;
(*   %call.i.2.28.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.28.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_28_3, v_call_i_2_28_3);
(*   %arrayidx11.2.28.3 = getelementptr inbounds i16, i16* %r, i64 220 *)
(*   %761 = load i16, i16* %arrayidx11.2.28.3, align 2, !tbaa !3 *)
mov v761 mem0_440;
(*   %sub.2.28.3 = sub i16 %761, %call.i.2.28.3 *)
sub v_sub_2_28_3 v761 v_call_i_2_28_3;
(*   store i16 %sub.2.28.3, i16* %arrayidx9.2.28.3, align 2, !tbaa !3 *)
mov mem0_504 v_sub_2_28_3;
(*   %add21.2.28.3 = add i16 %761, %call.i.2.28.3 *)
add v_add21_2_28_3 v761 v_call_i_2_28_3;
(*   store i16 %add21.2.28.3, i16* %arrayidx11.2.28.3, align 2, !tbaa !3 *)
mov mem0_440 v_add21_2_28_3;
(*   %arrayidx9.2.29.3 = getelementptr inbounds i16, i16* %r, i64 253 *)
(*   %762 = load i16, i16* %arrayidx9.2.29.3, align 2, !tbaa !3 *)
mov v762 mem0_506;
(*   %conv1.i.2.29.3 = sext i16 %762 to i32 *)
cast v_conv1_i_2_29_3@sint32 v762@sint16;
(*   %mul.i.2.29.3 = mul nsw i32 %conv1.i.2.29.3, 202 *)
mul v_mul_i_2_29_3 v_conv1_i_2_29_3 (202)@sint32;
(*   %call.i.2.29.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.29.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_29_3, v_call_i_2_29_3);
(*   %arrayidx11.2.29.3 = getelementptr inbounds i16, i16* %r, i64 221 *)
(*   %763 = load i16, i16* %arrayidx11.2.29.3, align 2, !tbaa !3 *)
mov v763 mem0_442;
(*   %sub.2.29.3 = sub i16 %763, %call.i.2.29.3 *)
sub v_sub_2_29_3 v763 v_call_i_2_29_3;
(*   store i16 %sub.2.29.3, i16* %arrayidx9.2.29.3, align 2, !tbaa !3 *)
mov mem0_506 v_sub_2_29_3;
(*   %add21.2.29.3 = add i16 %763, %call.i.2.29.3 *)
add v_add21_2_29_3 v763 v_call_i_2_29_3;
(*   store i16 %add21.2.29.3, i16* %arrayidx11.2.29.3, align 2, !tbaa !3 *)
mov mem0_442 v_add21_2_29_3;
(*   %arrayidx9.2.30.3 = getelementptr inbounds i16, i16* %r, i64 254 *)
(*   %764 = load i16, i16* %arrayidx9.2.30.3, align 2, !tbaa !3 *)
mov v764 mem0_508;
(*   %conv1.i.2.30.3 = sext i16 %764 to i32 *)
cast v_conv1_i_2_30_3@sint32 v764@sint16;
(*   %mul.i.2.30.3 = mul nsw i32 %conv1.i.2.30.3, 202 *)
mul v_mul_i_2_30_3 v_conv1_i_2_30_3 (202)@sint32;
(*   %call.i.2.30.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.30.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_30_3, v_call_i_2_30_3);
(*   %arrayidx11.2.30.3 = getelementptr inbounds i16, i16* %r, i64 222 *)
(*   %765 = load i16, i16* %arrayidx11.2.30.3, align 2, !tbaa !3 *)
mov v765 mem0_444;
(*   %sub.2.30.3 = sub i16 %765, %call.i.2.30.3 *)
sub v_sub_2_30_3 v765 v_call_i_2_30_3;
(*   store i16 %sub.2.30.3, i16* %arrayidx9.2.30.3, align 2, !tbaa !3 *)
mov mem0_508 v_sub_2_30_3;
(*   %add21.2.30.3 = add i16 %765, %call.i.2.30.3 *)
add v_add21_2_30_3 v765 v_call_i_2_30_3;
(*   store i16 %add21.2.30.3, i16* %arrayidx11.2.30.3, align 2, !tbaa !3 *)
mov mem0_444 v_add21_2_30_3;
(*   %arrayidx9.2.31.3 = getelementptr inbounds i16, i16* %r, i64 255 *)
(*   %766 = load i16, i16* %arrayidx9.2.31.3, align 2, !tbaa !3 *)
mov v766 mem0_510;
(*   %conv1.i.2.31.3 = sext i16 %766 to i32 *)
cast v_conv1_i_2_31_3@sint32 v766@sint16;
(*   %mul.i.2.31.3 = mul nsw i32 %conv1.i.2.31.3, 202 *)
mul v_mul_i_2_31_3 v_conv1_i_2_31_3 (202)@sint32;
(*   %call.i.2.31.3 = tail call signext i16 @PQCLEAN_KYBER512_CLEAN_montgomery_reduce(i32 %mul.i.2.31.3) #2 *)
call PQCLEAN_KYBER512_CLEAN_montgomery_reduce(v_mul_i_2_31_3, v_call_i_2_31_3);
(*   %arrayidx11.2.31.3 = getelementptr inbounds i16, i16* %r, i64 223 *)
(*   %767 = load i16, i16* %arrayidx11.2.31.3, align 2, !tbaa !3 *)
mov v767 mem0_446;
(*   %sub.2.31.3 = sub i16 %767, %call.i.2.31.3 *)
sub v_sub_2_31_3 v767 v_call_i_2_31_3;
(*   store i16 %sub.2.31.3, i16* %arrayidx9.2.31.3, align 2, !tbaa !3 *)
mov mem0_510 v_sub_2_31_3;
(*   %add21.2.31.3 = add i16 %767, %call.i.2.31.3 *)
add v_add21_2_31_3 v767 v_call_i_2_31_3;
(*   store i16 %add21.2.31.3, i16* %arrayidx11.2.31.3, align 2, !tbaa !3 *)
mov mem0_446 v_add21_2_31_3;

{and [
eqmod 
(
mem0_0_k3*(x**0) + mem0_2_k3*(x**1) + mem0_4_k3*(x**2) + mem0_6_k3*(x**3) + 
mem0_8_k3*(x**4) + mem0_10_k3*(x**5) + mem0_12_k3*(x**6) + mem0_14_k3*(x**7) + 
mem0_16_k3*(x**8) + mem0_18_k3*(x**9) + mem0_20_k3*(x**10) + mem0_22_k3*(x**11) + 
mem0_24_k3*(x**12) + mem0_26_k3*(x**13) + mem0_28_k3*(x**14) + mem0_30_k3*(x**15) + 
mem0_32_k3*(x**16) + mem0_34_k3*(x**17) + mem0_36_k3*(x**18) + mem0_38_k3*(x**19) + 
mem0_40_k3*(x**20) + mem0_42_k3*(x**21) + mem0_44_k3*(x**22) + mem0_46_k3*(x**23) + 
mem0_48_k3*(x**24) + mem0_50_k3*(x**25) + mem0_52_k3*(x**26) + mem0_54_k3*(x**27) + 
mem0_56_k3*(x**28) + mem0_58_k3*(x**29) + mem0_60_k3*(x**30) + mem0_62_k3*(x**31) + 
mem0_64_k3*(x**32) + mem0_66_k3*(x**33) + mem0_68_k3*(x**34) + mem0_70_k3*(x**35) + 
mem0_72_k3*(x**36) + mem0_74_k3*(x**37) + mem0_76_k3*(x**38) + mem0_78_k3*(x**39) + 
mem0_80_k3*(x**40) + mem0_82_k3*(x**41) + mem0_84_k3*(x**42) + mem0_86_k3*(x**43) + 
mem0_88_k3*(x**44) + mem0_90_k3*(x**45) + mem0_92_k3*(x**46) + mem0_94_k3*(x**47) + 
mem0_96_k3*(x**48) + mem0_98_k3*(x**49) + mem0_100_k3*(x**50) + mem0_102_k3*(x**51) + 
mem0_104_k3*(x**52) + mem0_106_k3*(x**53) + mem0_108_k3*(x**54) + mem0_110_k3*(x**55) + 
mem0_112_k3*(x**56) + mem0_114_k3*(x**57) + mem0_116_k3*(x**58) + mem0_118_k3*(x**59) + 
mem0_120_k3*(x**60) + mem0_122_k3*(x**61) + mem0_124_k3*(x**62) + mem0_126_k3*(x**63)
)
(
mem0_0*(x**0) + mem0_2*(x**1) + mem0_4*(x**2) + mem0_6*(x**3) + 
mem0_8*(x**4) + mem0_10*(x**5) + mem0_12*(x**6) + mem0_14*(x**7) + 
mem0_16*(x**8) + mem0_18*(x**9) + mem0_20*(x**10) + mem0_22*(x**11) + 
mem0_24*(x**12) + mem0_26*(x**13) + mem0_28*(x**14) + mem0_30*(x**15) + 
mem0_32*(x**16) + mem0_34*(x**17) + mem0_36*(x**18) + mem0_38*(x**19) + 
mem0_40*(x**20) + mem0_42*(x**21) + mem0_44*(x**22) + mem0_46*(x**23) + 
mem0_48*(x**24) + mem0_50*(x**25) + mem0_52*(x**26) + mem0_54*(x**27) + 
mem0_56*(x**28) + mem0_58*(x**29) + mem0_60*(x**30) + mem0_62*(x**31)
)
[3329, x**32 - 2642],
eqmod 
(
mem0_0_k3*(x**0) + mem0_2_k3*(x**1) + mem0_4_k3*(x**2) + mem0_6_k3*(x**3) + 
mem0_8_k3*(x**4) + mem0_10_k3*(x**5) + mem0_12_k3*(x**6) + mem0_14_k3*(x**7) + 
mem0_16_k3*(x**8) + mem0_18_k3*(x**9) + mem0_20_k3*(x**10) + mem0_22_k3*(x**11) + 
mem0_24_k3*(x**12) + mem0_26_k3*(x**13) + mem0_28_k3*(x**14) + mem0_30_k3*(x**15) + 
mem0_32_k3*(x**16) + mem0_34_k3*(x**17) + mem0_36_k3*(x**18) + mem0_38_k3*(x**19) + 
mem0_40_k3*(x**20) + mem0_42_k3*(x**21) + mem0_44_k3*(x**22) + mem0_46_k3*(x**23) + 
mem0_48_k3*(x**24) + mem0_50_k3*(x**25) + mem0_52_k3*(x**26) + mem0_54_k3*(x**27) + 
mem0_56_k3*(x**28) + mem0_58_k3*(x**29) + mem0_60_k3*(x**30) + mem0_62_k3*(x**31) + 
mem0_64_k3*(x**32) + mem0_66_k3*(x**33) + mem0_68_k3*(x**34) + mem0_70_k3*(x**35) + 
mem0_72_k3*(x**36) + mem0_74_k3*(x**37) + mem0_76_k3*(x**38) + mem0_78_k3*(x**39) + 
mem0_80_k3*(x**40) + mem0_82_k3*(x**41) + mem0_84_k3*(x**42) + mem0_86_k3*(x**43) + 
mem0_88_k3*(x**44) + mem0_90_k3*(x**45) + mem0_92_k3*(x**46) + mem0_94_k3*(x**47) + 
mem0_96_k3*(x**48) + mem0_98_k3*(x**49) + mem0_100_k3*(x**50) + mem0_102_k3*(x**51) + 
mem0_104_k3*(x**52) + mem0_106_k3*(x**53) + mem0_108_k3*(x**54) + mem0_110_k3*(x**55) + 
mem0_112_k3*(x**56) + mem0_114_k3*(x**57) + mem0_116_k3*(x**58) + mem0_118_k3*(x**59) + 
mem0_120_k3*(x**60) + mem0_122_k3*(x**61) + mem0_124_k3*(x**62) + mem0_126_k3*(x**63)
)
(
mem0_64*(x**0) + mem0_66*(x**1) + mem0_68*(x**2) + mem0_70*(x**3) + 
mem0_72*(x**4) + mem0_74*(x**5) + mem0_76*(x**6) + mem0_78*(x**7) + 
mem0_80*(x**8) + mem0_82*(x**9) + mem0_84*(x**10) + mem0_86*(x**11) + 
mem0_88*(x**12) + mem0_90*(x**13) + mem0_92*(x**14) + mem0_94*(x**15) + 
mem0_96*(x**16) + mem0_98*(x**17) + mem0_100*(x**18) + mem0_102*(x**19) + 
mem0_104*(x**20) + mem0_106*(x**21) + mem0_108*(x**22) + mem0_110*(x**23) + 
mem0_112*(x**24) + mem0_114*(x**25) + mem0_116*(x**26) + mem0_118*(x**27) + 
mem0_120*(x**28) + mem0_122*(x**29) + mem0_124*(x**30) + mem0_126*(x**31)
)
[3329, x**32 - 687],
eqmod 
(
mem0_128_k3*(x**0) + mem0_130_k3*(x**1) + mem0_132_k3*(x**2) + mem0_134_k3*(x**3) + 
mem0_136_k3*(x**4) + mem0_138_k3*(x**5) + mem0_140_k3*(x**6) + mem0_142_k3*(x**7) + 
mem0_144_k3*(x**8) + mem0_146_k3*(x**9) + mem0_148_k3*(x**10) + mem0_150_k3*(x**11) + 
mem0_152_k3*(x**12) + mem0_154_k3*(x**13) + mem0_156_k3*(x**14) + mem0_158_k3*(x**15) + 
mem0_160_k3*(x**16) + mem0_162_k3*(x**17) + mem0_164_k3*(x**18) + mem0_166_k3*(x**19) + 
mem0_168_k3*(x**20) + mem0_170_k3*(x**21) + mem0_172_k3*(x**22) + mem0_174_k3*(x**23) + 
mem0_176_k3*(x**24) + mem0_178_k3*(x**25) + mem0_180_k3*(x**26) + mem0_182_k3*(x**27) + 
mem0_184_k3*(x**28) + mem0_186_k3*(x**29) + mem0_188_k3*(x**30) + mem0_190_k3*(x**31) + 
mem0_192_k3*(x**32) + mem0_194_k3*(x**33) + mem0_196_k3*(x**34) + mem0_198_k3*(x**35) + 
mem0_200_k3*(x**36) + mem0_202_k3*(x**37) + mem0_204_k3*(x**38) + mem0_206_k3*(x**39) + 
mem0_208_k3*(x**40) + mem0_210_k3*(x**41) + mem0_212_k3*(x**42) + mem0_214_k3*(x**43) + 
mem0_216_k3*(x**44) + mem0_218_k3*(x**45) + mem0_220_k3*(x**46) + mem0_222_k3*(x**47) + 
mem0_224_k3*(x**48) + mem0_226_k3*(x**49) + mem0_228_k3*(x**50) + mem0_230_k3*(x**51) + 
mem0_232_k3*(x**52) + mem0_234_k3*(x**53) + mem0_236_k3*(x**54) + mem0_238_k3*(x**55) + 
mem0_240_k3*(x**56) + mem0_242_k3*(x**57) + mem0_244_k3*(x**58) + mem0_246_k3*(x**59) + 
mem0_248_k3*(x**60) + mem0_250_k3*(x**61) + mem0_252_k3*(x**62) + mem0_254_k3*(x**63)
)
(
mem0_128*(x**0) + mem0_130*(x**1) + mem0_132*(x**2) + mem0_134*(x**3) + 
mem0_136*(x**4) + mem0_138*(x**5) + mem0_140*(x**6) + mem0_142*(x**7) + 
mem0_144*(x**8) + mem0_146*(x**9) + mem0_148*(x**10) + mem0_150*(x**11) + 
mem0_152*(x**12) + mem0_154*(x**13) + mem0_156*(x**14) + mem0_158*(x**15) + 
mem0_160*(x**16) + mem0_162*(x**17) + mem0_164*(x**18) + mem0_166*(x**19) + 
mem0_168*(x**20) + mem0_170*(x**21) + mem0_172*(x**22) + mem0_174*(x**23) + 
mem0_176*(x**24) + mem0_178*(x**25) + mem0_180*(x**26) + mem0_182*(x**27) + 
mem0_184*(x**28) + mem0_186*(x**29) + mem0_188*(x**30) + mem0_190*(x**31)
)
[3329, x**32 - 630],
eqmod 
(
mem0_128_k3*(x**0) + mem0_130_k3*(x**1) + mem0_132_k3*(x**2) + mem0_134_k3*(x**3) + 
mem0_136_k3*(x**4) + mem0_138_k3*(x**5) + mem0_140_k3*(x**6) + mem0_142_k3*(x**7) + 
mem0_144_k3*(x**8) + mem0_146_k3*(x**9) + mem0_148_k3*(x**10) + mem0_150_k3*(x**11) + 
mem0_152_k3*(x**12) + mem0_154_k3*(x**13) + mem0_156_k3*(x**14) + mem0_158_k3*(x**15) + 
mem0_160_k3*(x**16) + mem0_162_k3*(x**17) + mem0_164_k3*(x**18) + mem0_166_k3*(x**19) + 
mem0_168_k3*(x**20) + mem0_170_k3*(x**21) + mem0_172_k3*(x**22) + mem0_174_k3*(x**23) + 
mem0_176_k3*(x**24) + mem0_178_k3*(x**25) + mem0_180_k3*(x**26) + mem0_182_k3*(x**27) + 
mem0_184_k3*(x**28) + mem0_186_k3*(x**29) + mem0_188_k3*(x**30) + mem0_190_k3*(x**31) + 
mem0_192_k3*(x**32) + mem0_194_k3*(x**33) + mem0_196_k3*(x**34) + mem0_198_k3*(x**35) + 
mem0_200_k3*(x**36) + mem0_202_k3*(x**37) + mem0_204_k3*(x**38) + mem0_206_k3*(x**39) + 
mem0_208_k3*(x**40) + mem0_210_k3*(x**41) + mem0_212_k3*(x**42) + mem0_214_k3*(x**43) + 
mem0_216_k3*(x**44) + mem0_218_k3*(x**45) + mem0_220_k3*(x**46) + mem0_222_k3*(x**47) + 
mem0_224_k3*(x**48) + mem0_226_k3*(x**49) + mem0_228_k3*(x**50) + mem0_230_k3*(x**51) + 
mem0_232_k3*(x**52) + mem0_234_k3*(x**53) + mem0_236_k3*(x**54) + mem0_238_k3*(x**55) + 
mem0_240_k3*(x**56) + mem0_242_k3*(x**57) + mem0_244_k3*(x**58) + mem0_246_k3*(x**59) + 
mem0_248_k3*(x**60) + mem0_250_k3*(x**61) + mem0_252_k3*(x**62) + mem0_254_k3*(x**63)
)
(
mem0_192*(x**0) + mem0_194*(x**1) + mem0_196*(x**2) + mem0_198*(x**3) + 
mem0_200*(x**4) + mem0_202*(x**5) + mem0_204*(x**6) + mem0_206*(x**7) + 
mem0_208*(x**8) + mem0_210*(x**9) + mem0_212*(x**10) + mem0_214*(x**11) + 
mem0_216*(x**12) + mem0_218*(x**13) + mem0_220*(x**14) + mem0_222*(x**15) + 
mem0_224*(x**16) + mem0_226*(x**17) + mem0_228*(x**18) + mem0_230*(x**19) + 
mem0_232*(x**20) + mem0_234*(x**21) + mem0_236*(x**22) + mem0_238*(x**23) + 
mem0_240*(x**24) + mem0_242*(x**25) + mem0_244*(x**26) + mem0_246*(x**27) + 
mem0_248*(x**28) + mem0_250*(x**29) + mem0_252*(x**30) + mem0_254*(x**31)
)
[3329, x**32 - 2699],
eqmod 
(
mem0_256_k3*(x**0) + mem0_258_k3*(x**1) + mem0_260_k3*(x**2) + mem0_262_k3*(x**3) + 
mem0_264_k3*(x**4) + mem0_266_k3*(x**5) + mem0_268_k3*(x**6) + mem0_270_k3*(x**7) + 
mem0_272_k3*(x**8) + mem0_274_k3*(x**9) + mem0_276_k3*(x**10) + mem0_278_k3*(x**11) + 
mem0_280_k3*(x**12) + mem0_282_k3*(x**13) + mem0_284_k3*(x**14) + mem0_286_k3*(x**15) + 
mem0_288_k3*(x**16) + mem0_290_k3*(x**17) + mem0_292_k3*(x**18) + mem0_294_k3*(x**19) + 
mem0_296_k3*(x**20) + mem0_298_k3*(x**21) + mem0_300_k3*(x**22) + mem0_302_k3*(x**23) + 
mem0_304_k3*(x**24) + mem0_306_k3*(x**25) + mem0_308_k3*(x**26) + mem0_310_k3*(x**27) + 
mem0_312_k3*(x**28) + mem0_314_k3*(x**29) + mem0_316_k3*(x**30) + mem0_318_k3*(x**31) + 
mem0_320_k3*(x**32) + mem0_322_k3*(x**33) + mem0_324_k3*(x**34) + mem0_326_k3*(x**35) + 
mem0_328_k3*(x**36) + mem0_330_k3*(x**37) + mem0_332_k3*(x**38) + mem0_334_k3*(x**39) + 
mem0_336_k3*(x**40) + mem0_338_k3*(x**41) + mem0_340_k3*(x**42) + mem0_342_k3*(x**43) + 
mem0_344_k3*(x**44) + mem0_346_k3*(x**45) + mem0_348_k3*(x**46) + mem0_350_k3*(x**47) + 
mem0_352_k3*(x**48) + mem0_354_k3*(x**49) + mem0_356_k3*(x**50) + mem0_358_k3*(x**51) + 
mem0_360_k3*(x**52) + mem0_362_k3*(x**53) + mem0_364_k3*(x**54) + mem0_366_k3*(x**55) + 
mem0_368_k3*(x**56) + mem0_370_k3*(x**57) + mem0_372_k3*(x**58) + mem0_374_k3*(x**59) + 
mem0_376_k3*(x**60) + mem0_378_k3*(x**61) + mem0_380_k3*(x**62) + mem0_382_k3*(x**63)
)
(
mem0_256*(x**0) + mem0_258*(x**1) + mem0_260*(x**2) + mem0_262*(x**3) + 
mem0_264*(x**4) + mem0_266*(x**5) + mem0_268*(x**6) + mem0_270*(x**7) + 
mem0_272*(x**8) + mem0_274*(x**9) + mem0_276*(x**10) + mem0_278*(x**11) + 
mem0_280*(x**12) + mem0_282*(x**13) + mem0_284*(x**14) + mem0_286*(x**15) + 
mem0_288*(x**16) + mem0_290*(x**17) + mem0_292*(x**18) + mem0_294*(x**19) + 
mem0_296*(x**20) + mem0_298*(x**21) + mem0_300*(x**22) + mem0_302*(x**23) + 
mem0_304*(x**24) + mem0_306*(x**25) + mem0_308*(x**26) + mem0_310*(x**27) + 
mem0_312*(x**28) + mem0_314*(x**29) + mem0_316*(x**30) + mem0_318*(x**31)
)
[3329, x**32 - 1897],
eqmod 
(
mem0_256_k3*(x**0) + mem0_258_k3*(x**1) + mem0_260_k3*(x**2) + mem0_262_k3*(x**3) + 
mem0_264_k3*(x**4) + mem0_266_k3*(x**5) + mem0_268_k3*(x**6) + mem0_270_k3*(x**7) + 
mem0_272_k3*(x**8) + mem0_274_k3*(x**9) + mem0_276_k3*(x**10) + mem0_278_k3*(x**11) + 
mem0_280_k3*(x**12) + mem0_282_k3*(x**13) + mem0_284_k3*(x**14) + mem0_286_k3*(x**15) + 
mem0_288_k3*(x**16) + mem0_290_k3*(x**17) + mem0_292_k3*(x**18) + mem0_294_k3*(x**19) + 
mem0_296_k3*(x**20) + mem0_298_k3*(x**21) + mem0_300_k3*(x**22) + mem0_302_k3*(x**23) + 
mem0_304_k3*(x**24) + mem0_306_k3*(x**25) + mem0_308_k3*(x**26) + mem0_310_k3*(x**27) + 
mem0_312_k3*(x**28) + mem0_314_k3*(x**29) + mem0_316_k3*(x**30) + mem0_318_k3*(x**31) + 
mem0_320_k3*(x**32) + mem0_322_k3*(x**33) + mem0_324_k3*(x**34) + mem0_326_k3*(x**35) + 
mem0_328_k3*(x**36) + mem0_330_k3*(x**37) + mem0_332_k3*(x**38) + mem0_334_k3*(x**39) + 
mem0_336_k3*(x**40) + mem0_338_k3*(x**41) + mem0_340_k3*(x**42) + mem0_342_k3*(x**43) + 
mem0_344_k3*(x**44) + mem0_346_k3*(x**45) + mem0_348_k3*(x**46) + mem0_350_k3*(x**47) + 
mem0_352_k3*(x**48) + mem0_354_k3*(x**49) + mem0_356_k3*(x**50) + mem0_358_k3*(x**51) + 
mem0_360_k3*(x**52) + mem0_362_k3*(x**53) + mem0_364_k3*(x**54) + mem0_366_k3*(x**55) + 
mem0_368_k3*(x**56) + mem0_370_k3*(x**57) + mem0_372_k3*(x**58) + mem0_374_k3*(x**59) + 
mem0_376_k3*(x**60) + mem0_378_k3*(x**61) + mem0_380_k3*(x**62) + mem0_382_k3*(x**63)
)
(
mem0_320*(x**0) + mem0_322*(x**1) + mem0_324*(x**2) + mem0_326*(x**3) + 
mem0_328*(x**4) + mem0_330*(x**5) + mem0_332*(x**6) + mem0_334*(x**7) + 
mem0_336*(x**8) + mem0_338*(x**9) + mem0_340*(x**10) + mem0_342*(x**11) + 
mem0_344*(x**12) + mem0_346*(x**13) + mem0_348*(x**14) + mem0_350*(x**15) + 
mem0_352*(x**16) + mem0_354*(x**17) + mem0_356*(x**18) + mem0_358*(x**19) + 
mem0_360*(x**20) + mem0_362*(x**21) + mem0_364*(x**22) + mem0_366*(x**23) + 
mem0_368*(x**24) + mem0_370*(x**25) + mem0_372*(x**26) + mem0_374*(x**27) + 
mem0_376*(x**28) + mem0_378*(x**29) + mem0_380*(x**30) + mem0_382*(x**31)
)
[3329, x**32 - 1432],
eqmod 
(
mem0_384_k3*(x**0) + mem0_386_k3*(x**1) + mem0_388_k3*(x**2) + mem0_390_k3*(x**3) + 
mem0_392_k3*(x**4) + mem0_394_k3*(x**5) + mem0_396_k3*(x**6) + mem0_398_k3*(x**7) + 
mem0_400_k3*(x**8) + mem0_402_k3*(x**9) + mem0_404_k3*(x**10) + mem0_406_k3*(x**11) + 
mem0_408_k3*(x**12) + mem0_410_k3*(x**13) + mem0_412_k3*(x**14) + mem0_414_k3*(x**15) + 
mem0_416_k3*(x**16) + mem0_418_k3*(x**17) + mem0_420_k3*(x**18) + mem0_422_k3*(x**19) + 
mem0_424_k3*(x**20) + mem0_426_k3*(x**21) + mem0_428_k3*(x**22) + mem0_430_k3*(x**23) + 
mem0_432_k3*(x**24) + mem0_434_k3*(x**25) + mem0_436_k3*(x**26) + mem0_438_k3*(x**27) + 
mem0_440_k3*(x**28) + mem0_442_k3*(x**29) + mem0_444_k3*(x**30) + mem0_446_k3*(x**31) + 
mem0_448_k3*(x**32) + mem0_450_k3*(x**33) + mem0_452_k3*(x**34) + mem0_454_k3*(x**35) + 
mem0_456_k3*(x**36) + mem0_458_k3*(x**37) + mem0_460_k3*(x**38) + mem0_462_k3*(x**39) + 
mem0_464_k3*(x**40) + mem0_466_k3*(x**41) + mem0_468_k3*(x**42) + mem0_470_k3*(x**43) + 
mem0_472_k3*(x**44) + mem0_474_k3*(x**45) + mem0_476_k3*(x**46) + mem0_478_k3*(x**47) + 
mem0_480_k3*(x**48) + mem0_482_k3*(x**49) + mem0_484_k3*(x**50) + mem0_486_k3*(x**51) + 
mem0_488_k3*(x**52) + mem0_490_k3*(x**53) + mem0_492_k3*(x**54) + mem0_494_k3*(x**55) + 
mem0_496_k3*(x**56) + mem0_498_k3*(x**57) + mem0_500_k3*(x**58) + mem0_502_k3*(x**59) + 
mem0_504_k3*(x**60) + mem0_506_k3*(x**61) + mem0_508_k3*(x**62) + mem0_510_k3*(x**63)
)
(
mem0_384*(x**0) + mem0_386*(x**1) + mem0_388*(x**2) + mem0_390*(x**3) + 
mem0_392*(x**4) + mem0_394*(x**5) + mem0_396*(x**6) + mem0_398*(x**7) + 
mem0_400*(x**8) + mem0_402*(x**9) + mem0_404*(x**10) + mem0_406*(x**11) + 
mem0_408*(x**12) + mem0_410*(x**13) + mem0_412*(x**14) + mem0_414*(x**15) + 
mem0_416*(x**16) + mem0_418*(x**17) + mem0_420*(x**18) + mem0_422*(x**19) + 
mem0_424*(x**20) + mem0_426*(x**21) + mem0_428*(x**22) + mem0_430*(x**23) + 
mem0_432*(x**24) + mem0_434*(x**25) + mem0_436*(x**26) + mem0_438*(x**27) + 
mem0_440*(x**28) + mem0_442*(x**29) + mem0_444*(x**30) + mem0_446*(x**31)
)
[3329, x**32 - 848],
eqmod 
(
mem0_384_k3*(x**0) + mem0_386_k3*(x**1) + mem0_388_k3*(x**2) + mem0_390_k3*(x**3) + 
mem0_392_k3*(x**4) + mem0_394_k3*(x**5) + mem0_396_k3*(x**6) + mem0_398_k3*(x**7) + 
mem0_400_k3*(x**8) + mem0_402_k3*(x**9) + mem0_404_k3*(x**10) + mem0_406_k3*(x**11) + 
mem0_408_k3*(x**12) + mem0_410_k3*(x**13) + mem0_412_k3*(x**14) + mem0_414_k3*(x**15) + 
mem0_416_k3*(x**16) + mem0_418_k3*(x**17) + mem0_420_k3*(x**18) + mem0_422_k3*(x**19) + 
mem0_424_k3*(x**20) + mem0_426_k3*(x**21) + mem0_428_k3*(x**22) + mem0_430_k3*(x**23) + 
mem0_432_k3*(x**24) + mem0_434_k3*(x**25) + mem0_436_k3*(x**26) + mem0_438_k3*(x**27) + 
mem0_440_k3*(x**28) + mem0_442_k3*(x**29) + mem0_444_k3*(x**30) + mem0_446_k3*(x**31) + 
mem0_448_k3*(x**32) + mem0_450_k3*(x**33) + mem0_452_k3*(x**34) + mem0_454_k3*(x**35) + 
mem0_456_k3*(x**36) + mem0_458_k3*(x**37) + mem0_460_k3*(x**38) + mem0_462_k3*(x**39) + 
mem0_464_k3*(x**40) + mem0_466_k3*(x**41) + mem0_468_k3*(x**42) + mem0_470_k3*(x**43) + 
mem0_472_k3*(x**44) + mem0_474_k3*(x**45) + mem0_476_k3*(x**46) + mem0_478_k3*(x**47) + 
mem0_480_k3*(x**48) + mem0_482_k3*(x**49) + mem0_484_k3*(x**50) + mem0_486_k3*(x**51) + 
mem0_488_k3*(x**52) + mem0_490_k3*(x**53) + mem0_492_k3*(x**54) + mem0_494_k3*(x**55) + 
mem0_496_k3*(x**56) + mem0_498_k3*(x**57) + mem0_500_k3*(x**58) + mem0_502_k3*(x**59) + 
mem0_504_k3*(x**60) + mem0_506_k3*(x**61) + mem0_508_k3*(x**62) + mem0_510_k3*(x**63)
)
(
mem0_448*(x**0) + mem0_450*(x**1) + mem0_452*(x**2) + mem0_454*(x**3) + 
mem0_456*(x**4) + mem0_458*(x**5) + mem0_460*(x**6) + mem0_462*(x**7) + 
mem0_464*(x**8) + mem0_466*(x**9) + mem0_468*(x**10) + mem0_470*(x**11) + 
mem0_472*(x**12) + mem0_474*(x**13) + mem0_476*(x**14) + mem0_478*(x**15) + 
mem0_480*(x**16) + mem0_482*(x**17) + mem0_484*(x**18) + mem0_486*(x**19) + 
mem0_488*(x**20) + mem0_490*(x**21) + mem0_492*(x**22) + mem0_494*(x**23) + 
mem0_496*(x**24) + mem0_498*(x**25) + mem0_500*(x**26) + mem0_502*(x**27) + 
mem0_504*(x**28) + mem0_506*(x**29) + mem0_508*(x**30) + mem0_510*(x**31)
)
[3329, x**32 - 2481]
] && and [
   (-5)@16 * 3329@16 <s mem0_0, mem0_0 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_2, mem0_2 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_4, mem0_4 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_6, mem0_6 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_8, mem0_8 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_10, mem0_10 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_12, mem0_12 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_14, mem0_14 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_16, mem0_16 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_18, mem0_18 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_20, mem0_20 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_22, mem0_22 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_24, mem0_24 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_26, mem0_26 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_28, mem0_28 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_30, mem0_30 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_32, mem0_32 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_34, mem0_34 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_36, mem0_36 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_38, mem0_38 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_40, mem0_40 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_42, mem0_42 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_44, mem0_44 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_46, mem0_46 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_48, mem0_48 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_50, mem0_50 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_52, mem0_52 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_54, mem0_54 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_56, mem0_56 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_58, mem0_58 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_60, mem0_60 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_62, mem0_62 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_64, mem0_64 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_66, mem0_66 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_68, mem0_68 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_70, mem0_70 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_72, mem0_72 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_74, mem0_74 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_76, mem0_76 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_78, mem0_78 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_80, mem0_80 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_82, mem0_82 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_84, mem0_84 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_86, mem0_86 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_88, mem0_88 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_90, mem0_90 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_92, mem0_92 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_94, mem0_94 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_96, mem0_96 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_98, mem0_98 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_100, mem0_100 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_102, mem0_102 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_104, mem0_104 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_106, mem0_106 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_108, mem0_108 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_110, mem0_110 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_112, mem0_112 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_114, mem0_114 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_116, mem0_116 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_118, mem0_118 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_120, mem0_120 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_122, mem0_122 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_124, mem0_124 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_126, mem0_126 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_128, mem0_128 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_130, mem0_130 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_132, mem0_132 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_134, mem0_134 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_136, mem0_136 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_138, mem0_138 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_140, mem0_140 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_142, mem0_142 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_144, mem0_144 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_146, mem0_146 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_148, mem0_148 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_150, mem0_150 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_152, mem0_152 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_154, mem0_154 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_156, mem0_156 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_158, mem0_158 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_160, mem0_160 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_162, mem0_162 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_164, mem0_164 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_166, mem0_166 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_168, mem0_168 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_170, mem0_170 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_172, mem0_172 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_174, mem0_174 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_176, mem0_176 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_178, mem0_178 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_180, mem0_180 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_182, mem0_182 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_184, mem0_184 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_186, mem0_186 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_188, mem0_188 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_190, mem0_190 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_192, mem0_192 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_194, mem0_194 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_196, mem0_196 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_198, mem0_198 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_200, mem0_200 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_202, mem0_202 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_204, mem0_204 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_206, mem0_206 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_208, mem0_208 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_210, mem0_210 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_212, mem0_212 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_214, mem0_214 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_216, mem0_216 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_218, mem0_218 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_220, mem0_220 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_222, mem0_222 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_224, mem0_224 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_226, mem0_226 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_228, mem0_228 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_230, mem0_230 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_232, mem0_232 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_234, mem0_234 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_236, mem0_236 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_238, mem0_238 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_240, mem0_240 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_242, mem0_242 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_244, mem0_244 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_246, mem0_246 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_248, mem0_248 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_250, mem0_250 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_252, mem0_252 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_254, mem0_254 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_256, mem0_256 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_258, mem0_258 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_260, mem0_260 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_262, mem0_262 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_264, mem0_264 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_266, mem0_266 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_268, mem0_268 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_270, mem0_270 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_272, mem0_272 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_274, mem0_274 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_276, mem0_276 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_278, mem0_278 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_280, mem0_280 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_282, mem0_282 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_284, mem0_284 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_286, mem0_286 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_288, mem0_288 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_290, mem0_290 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_292, mem0_292 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_294, mem0_294 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_296, mem0_296 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_298, mem0_298 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_300, mem0_300 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_302, mem0_302 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_304, mem0_304 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_306, mem0_306 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_308, mem0_308 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_310, mem0_310 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_312, mem0_312 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_314, mem0_314 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_316, mem0_316 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_318, mem0_318 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_320, mem0_320 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_322, mem0_322 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_324, mem0_324 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_326, mem0_326 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_328, mem0_328 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_330, mem0_330 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_332, mem0_332 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_334, mem0_334 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_336, mem0_336 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_338, mem0_338 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_340, mem0_340 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_342, mem0_342 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_344, mem0_344 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_346, mem0_346 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_348, mem0_348 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_350, mem0_350 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_352, mem0_352 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_354, mem0_354 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_356, mem0_356 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_358, mem0_358 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_360, mem0_360 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_362, mem0_362 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_364, mem0_364 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_366, mem0_366 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_368, mem0_368 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_370, mem0_370 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_372, mem0_372 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_374, mem0_374 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_376, mem0_376 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_378, mem0_378 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_380, mem0_380 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_382, mem0_382 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_384, mem0_384 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_386, mem0_386 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_388, mem0_388 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_390, mem0_390 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_392, mem0_392 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_394, mem0_394 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_396, mem0_396 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_398, mem0_398 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_400, mem0_400 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_402, mem0_402 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_404, mem0_404 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_406, mem0_406 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_408, mem0_408 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_410, mem0_410 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_412, mem0_412 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_414, mem0_414 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_416, mem0_416 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_418, mem0_418 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_420, mem0_420 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_422, mem0_422 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_424, mem0_424 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_426, mem0_426 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_428, mem0_428 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_430, mem0_430 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_432, mem0_432 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_434, mem0_434 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_436, mem0_436 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_438, mem0_438 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_440, mem0_440 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_442, mem0_442 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_444, mem0_444 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_446, mem0_446 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_448, mem0_448 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_450, mem0_450 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_452, mem0_452 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_454, mem0_454 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_456, mem0_456 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_458, mem0_458 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_460, mem0_460 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_462, mem0_462 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_464, mem0_464 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_466, mem0_466 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_468, mem0_468 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_470, mem0_470 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_472, mem0_472 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_474, mem0_474 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_476, mem0_476 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_478, mem0_478 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_480, mem0_480 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_482, mem0_482 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_484, mem0_484 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_486, mem0_486 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_488, mem0_488 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_490, mem0_490 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_492, mem0_492 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_494, mem0_494 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_496, mem0_496 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_498, mem0_498 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_500, mem0_500 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_502, mem0_502 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_504, mem0_504 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_506, mem0_506 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_508, mem0_508 <s 5@16 * 3329@16,
   (-5)@16 * 3329@16 <s mem0_510, mem0_510 <s 5@16 * 3329@16
]
}
