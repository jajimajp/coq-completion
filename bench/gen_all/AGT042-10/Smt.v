(* Zenerated by tptp2coqp *)
Require Import SMTCoq.SMTCoq ZArith.
Local Open Scope Z_scope.

(* axioms *)
Variable a : Z.
Variable accept_city : Z -> Z -> Z.
Variable accept_leader : Z -> Z -> Z.
Variable accept_number : Z -> Z -> Z.
Variable accept_population : Z -> Z -> Z -> Z.
Variable accept_team : Z -> Z -> Z -> Z -> Z.
Variable any_agent_in_all_proposed_teams : Z -> Z -> Z -> Z.
Variable atheist : Z.
Variable b : Z.
Variable centrallakecity : Z.
Variable centraltown : Z.
Variable christian : Z.
Variable christiancountrychumanitarianorganization : Z.
Variable christiansufferterrahumanitarianorganization : Z.
Variable citya : Z.
Variable cityb : Z.
Variable coastvillage : Z.
Variable countryacivilorganization : Z.
Variable countryafirstaidorganization : Z.
Variable countryahumanitarianorganization : Z.
Variable countryamedicalorganization : Z.
Variable countrybcivilorganization : Z.
Variable countrybhumanitarianorganization : Z.
Variable countryccivilorganization : Z.
Variable countrycmedicalorganization : Z.
Variable ifeq : Z -> Z -> Z -> Z -> Z.
Variable ifeq2 : Z -> Z -> Z -> Z -> Z.
Variable ifeq3 : Z -> Z -> Z -> Z -> Z.
Variable less : Z -> Z -> Z.
Variable min_number_of_proposed_agents : Z -> Z -> Z.
Variable muslim : Z.
Variable muslimcountrybhumanitarianorganization : Z.
Variable n0 : Z.
Variable n1 : Z.
Variable n10 : Z.
Variable n100 : Z.
Variable n11 : Z.
Variable n12 : Z.
Variable n13 : Z.
Variable n15 : Z.
Variable n16 : Z.
Variable n2 : Z.
Variable n20 : Z.
Variable n23 : Z.
Variable n24 : Z.
Variable n25 : Z.
Variable n3 : Z.
Variable n30 : Z.
Variable n4 : Z.
Variable n5 : Z.
Variable n54 : Z.
Variable n6 : Z.
Variable n60 : Z.
Variable n65 : Z.
Variable n68 : Z.
Variable n7 : Z.
Variable n70 : Z.
Variable n75 : Z.
Variable n78 : Z.
Variable n8 : Z.
Variable n85 : Z.
Variable n9 : Z.
Variable native : Z.
Variable northport : Z.
Variable other : Z.
Variable stjosephburgh : Z.
Variable sufferterragovernment : Z.
Variable suffertown : Z.
Variable sunnysideport : Z.
Variable sunsetpoint : Z.
Variable the_agent_in_all_proposed_teams : Z -> Z -> Z -> Z.
Variable the_agent_not_in_any_proposed_teams : Z -> Z -> Z -> Z.
Variable towna : Z.
Variable townb : Z.
Variable townc : Z.
Variable true : Z.
Variable tuple : Z -> Z -> Z -> Z.
Axiom deduced_366 : (ifeq2 (accept_city muslimcountrybhumanitarianorganization towna) true a b) =? b.
Axiom deduced_82 : (ifeq2 (accept_leader christiansufferterrahumanitarianorganization sufferterragovernment) true a b) =? b.
Axiom deduced_62 : (ifeq2 (accept_number countryccivilorganization n6) true a b) =? b.
Axiom deduced_58 : (ifeq2 (accept_number countryccivilorganization n5) true a b) =? b.
Axiom deduced_13 : (ifeq2 (accept_city countryamedicalorganization coastvillage) true a b) =? b.
Axiom event_246 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrycmedicalorganization towna n6) true a b) =? b.
Axiom event_219 : (ifeq2 (accept_team countryccivilorganization countrycmedicalorganization towna n6) true a b) =? b.
Axiom event_218 : (ifeq2 (accept_team countryccivilorganization christiancountrychumanitarianorganization towna n6) true a b) =? b.
Axiom event_217 : (ifeq2 (accept_team countryccivilorganization countrybhumanitarianorganization towna n6) true a b) =? b.
Axiom event_216 : (ifeq2 (accept_team countryccivilorganization countrybcivilorganization towna n6) true a b) =? b.
Axiom event_213 : (ifeq2 (accept_team christiansufferterrahumanitarianorganization sufferterragovernment towna n6) true a b) =? b.
Axiom event_212 : (ifeq2 (accept_team christiansufferterrahumanitarianorganization sufferterragovernment towna n2) true a b) =? b.
Axiom event_187 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization towna n6) true a b) =? b.
Axiom event_186 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrybhumanitarianorganization towna n6) true a b) =? b.
Axiom event_185 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrybcivilorganization towna n6) true a b) =? b.
Axiom event_184 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countryccivilorganization towna n4) true a b) =? b.
Axiom event_182 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrybhumanitarianorganization towna n2) true a b) =? b.
Axiom event_181 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countryccivilorganization towna n3) true a b) =? b.
Axiom event_180 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrycmedicalorganization towna n3) true a b) =? b.
Axiom event_179 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization towna n3) true a b) =? b.
Axiom event_178 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrybcivilorganization towna n3) true a b) =? b.
Axiom event_177 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countryccivilorganization towna n2) true a b) =? b.
Axiom event_176 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization towna n2) true a b) =? b.
Axiom event_175 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrycmedicalorganization towna n2) true a b) =? b.
Axiom event_174 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrybcivilorganization towna n2) true a b) =? b.
Axiom event_144 : (ifeq2 (accept_team countryccivilorganization countrybhumanitarianorganization cityb n6) true a b) =? b.
Axiom event_143 : (ifeq2 (accept_team countryccivilorganization countrybhumanitarianorganization cityb n5) true a b) =? b.
Axiom event_119 : (ifeq2 (accept_team countryccivilorganization countrycmedicalorganization townc n6) true a b) =? b.
Axiom event_118 : (ifeq2 (accept_team countryccivilorganization christiancountrychumanitarianorganization townc n6) true a b) =? b.
Axiom event_117 : (ifeq2 (accept_team countryccivilorganization countrybhumanitarianorganization townc n6) true a b) =? b.
Axiom event_116 : (ifeq2 (accept_team countryccivilorganization countrybcivilorganization townc n6) true a b) =? b.
Axiom event_115 : (ifeq2 (accept_team countryccivilorganization muslimcountrybhumanitarianorganization townc n6) true a b) =? b.
Axiom event_72 : (ifeq2 (accept_team countryccivilorganization christiancountrychumanitarianorganization coastvillage n6) true a b) =? b.
Axiom event_71 : (ifeq2 (accept_team countryccivilorganization christiancountrychumanitarianorganization coastvillage n5) true a b) =? b.
Axiom event_40 : (ifeq2 (accept_team countryccivilorganization countrycmedicalorganization towna n5) true a b) =? b.
Axiom event_36 : (ifeq2 (accept_team countryamedicalorganization countryafirstaidorganization coastvillage n6) true a b) =? b.
Axiom event_35 : (ifeq2 (accept_team countryamedicalorganization countryacivilorganization coastvillage n6) true a b) =? b.
Axiom event_34 : (ifeq2 (accept_team countryamedicalorganization countryahumanitarianorganization coastvillage n6) true a b) =? b.
Axiom event_33 : (ifeq2 (accept_team countryamedicalorganization sufferterragovernment coastvillage n2) true a b) =? b.
Axiom event_32 : (ifeq2 (accept_team countryamedicalorganization christiansufferterrahumanitarianorganization coastvillage n2) true a b) =? b.
Axiom event_31 : (ifeq2 (accept_team countryamedicalorganization countryacivilorganization coastvillage n2) true a b) =? b.
Axiom event_30 : (ifeq2 (accept_team countryamedicalorganization countryafirstaidorganization coastvillage n2) true a b) =? b.
Axiom event_29 : (ifeq2 (accept_team countryamedicalorganization countryahumanitarianorganization coastvillage n2) true a b) =? b.
Axiom event_10 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrycmedicalorganization towna n5) true a b) =? b.
Axiom event_9 : (ifeq2 (accept_team muslimcountrybhumanitarianorganization countrycmedicalorganization towna n4) true a b) =? b.
Axiom a1_6 : forall A C L : Z, (ifeq (tuple (accept_city A C) (accept_leader A L) (the_agent_not_in_any_proposed_teams A L C)) (tuple true true true) a b) =? b.
Axiom deduced_367 : (accept_leader muslimcountrybhumanitarianorganization sufferterragovernment) =? true.
Axiom deduced_365 : (accept_number muslimcountrybhumanitarianorganization n6) =? true.
Axiom deduced_364 : (accept_number muslimcountrybhumanitarianorganization n1) =? true.
Axiom deduced_363 : (accept_number muslimcountrybhumanitarianorganization n2) =? true.
Axiom deduced_362 : (accept_number muslimcountrybhumanitarianorganization n3) =? true.
Axiom deduced_361 : (accept_number muslimcountrybhumanitarianorganization n4) =? true.
Axiom deduced_360 : (accept_number muslimcountrybhumanitarianorganization n5) =? true.
Axiom deduced_359 : (accept_number countrycmedicalorganization n6) =? true.
Axiom deduced_358 : (accept_number countrycmedicalorganization n1) =? true.
Axiom deduced_357 : (accept_number countrycmedicalorganization n2) =? true.
Axiom deduced_356 : (accept_number countrycmedicalorganization n3) =? true.
Axiom deduced_355 : (accept_number countrycmedicalorganization n4) =? true.
Axiom deduced_354 : (accept_number countrycmedicalorganization n5) =? true.
Axiom deduced_353 : (accept_leader christiancountrychumanitarianorganization sufferterragovernment) =? true.
Axiom deduced_352 : (accept_city christiancountrychumanitarianorganization towna) =? true.
Axiom deduced_351 : (accept_population christiancountrychumanitarianorganization atheist n75) =? true.
Axiom deduced_350 : (accept_population christiancountrychumanitarianorganization christian n24) =? true.
Axiom deduced_349 : (accept_population christiancountrychumanitarianorganization muslim n1) =? true.
Axiom deduced_348 : (accept_population christiancountrychumanitarianorganization native n0) =? true.
Axiom deduced_347 : (accept_population christiancountrychumanitarianorganization other n0) =? true.
Axiom deduced_346 : (accept_number christiancountrychumanitarianorganization n6) =? true.
Axiom deduced_345 : (accept_number christiancountrychumanitarianorganization n1) =? true.
Axiom deduced_344 : (accept_number christiancountrychumanitarianorganization n2) =? true.
Axiom deduced_343 : (accept_number christiancountrychumanitarianorganization n3) =? true.
Axiom deduced_342 : (accept_number christiancountrychumanitarianorganization n4) =? true.
Axiom deduced_341 : (accept_number christiancountrychumanitarianorganization n5) =? true.
Axiom deduced_340 : (accept_leader christiancountrychumanitarianorganization countrycmedicalorganization) =? true.
Axiom deduced_339 : (accept_leader christiancountrychumanitarianorganization countrybhumanitarianorganization) =? true.
Axiom deduced_338 : (accept_number countrybhumanitarianorganization n6) =? true.
Axiom deduced_337 : (accept_number countrybhumanitarianorganization n1) =? true.
Axiom deduced_336 : (accept_number countrybhumanitarianorganization n2) =? true.
Axiom deduced_335 : (accept_number countrybhumanitarianorganization n3) =? true.
Axiom deduced_334 : (accept_number countrybhumanitarianorganization n4) =? true.
Axiom deduced_333 : (accept_number countrybhumanitarianorganization n5) =? true.
Axiom deduced_332 : (accept_leader christiancountrychumanitarianorganization countrybcivilorganization) =? true.
Axiom deduced_331 : (accept_number countrybcivilorganization n6) =? true.
Axiom deduced_330 : (accept_number countrybcivilorganization n1) =? true.
Axiom deduced_329 : (accept_number countrybcivilorganization n2) =? true.
Axiom deduced_328 : (accept_number countrybcivilorganization n3) =? true.
Axiom deduced_327 : (accept_number countrybcivilorganization n4) =? true.
Axiom deduced_326 : (accept_number countrybcivilorganization n5) =? true.
Axiom deduced_325 : (accept_leader christiancountrychumanitarianorganization countryccivilorganization) =? true.
Axiom deduced_324 : (accept_number countryccivilorganization n4) =? true.
Axiom deduced_323 : (accept_number countryccivilorganization n1) =? true.
Axiom deduced_322 : (accept_number countryccivilorganization n2) =? true.
Axiom deduced_321 : (accept_number countryccivilorganization n3) =? true.
Axiom deduced_320 : (accept_city countryacivilorganization towna) =? true.
Axiom deduced_319 : (accept_leader countryacivilorganization sufferterragovernment) =? true.
Axiom deduced_318 : (accept_number countryacivilorganization n6) =? true.
Axiom deduced_317 : (accept_population countryacivilorganization atheist n75) =? true.
Axiom deduced_316 : (accept_population countryacivilorganization christian n24) =? true.
Axiom deduced_315 : (accept_population countryacivilorganization muslim n1) =? true.
Axiom deduced_314 : (accept_population countryacivilorganization native n0) =? true.
Axiom deduced_313 : (accept_population countryacivilorganization other n0) =? true.
Axiom deduced_312 : (accept_number countryacivilorganization n1) =? true.
Axiom deduced_311 : (accept_number countryacivilorganization n2) =? true.
Axiom deduced_310 : (accept_number countryacivilorganization n3) =? true.
Axiom deduced_309 : (accept_number countryacivilorganization n4) =? true.
Axiom deduced_308 : (accept_number countryacivilorganization n5) =? true.
Axiom deduced_307 : (accept_number sufferterragovernment n6) =? true.
Axiom deduced_306 : (accept_number sufferterragovernment n1) =? true.
Axiom deduced_305 : (accept_number sufferterragovernment n2) =? true.
Axiom deduced_304 : (accept_number sufferterragovernment n3) =? true.
Axiom deduced_303 : (accept_number sufferterragovernment n4) =? true.
Axiom deduced_302 : (accept_number sufferterragovernment n5) =? true.
Axiom deduced_301 : (accept_leader countrybcivilorganization sufferterragovernment) =? true.
Axiom deduced_300 : (accept_city countrybcivilorganization towna) =? true.
Axiom deduced_299 : (accept_population countrybcivilorganization atheist n75) =? true.
Axiom deduced_298 : (accept_population countrybcivilorganization christian n24) =? true.
Axiom deduced_297 : (accept_population countrybcivilorganization muslim n1) =? true.
Axiom deduced_296 : (accept_population countrybcivilorganization native n0) =? true.
Axiom deduced_295 : (accept_population countrybcivilorganization other n0) =? true.
Axiom deduced_294 : (accept_leader countrybcivilorganization countrycmedicalorganization) =? true.
Axiom deduced_293 : (accept_leader countrybcivilorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_292 : (accept_leader countrybcivilorganization countrybhumanitarianorganization) =? true.
Axiom deduced_291 : (accept_leader countrybcivilorganization countryccivilorganization) =? true.
Axiom deduced_290 : (accept_leader countrycmedicalorganization sufferterragovernment) =? true.
Axiom deduced_289 : (accept_city countrycmedicalorganization towna) =? true.
Axiom deduced_288 : (accept_population countrycmedicalorganization atheist n75) =? true.
Axiom deduced_287 : (accept_population countrycmedicalorganization christian n24) =? true.
Axiom deduced_286 : (accept_population countrycmedicalorganization muslim n1) =? true.
Axiom deduced_285 : (accept_population countrycmedicalorganization native n0) =? true.
Axiom deduced_284 : (accept_population countrycmedicalorganization other n0) =? true.
Axiom deduced_283 : (accept_leader countrycmedicalorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_282 : (accept_leader countrycmedicalorganization countrybhumanitarianorganization) =? true.
Axiom deduced_281 : (accept_leader countrycmedicalorganization countrybcivilorganization) =? true.
Axiom deduced_280 : (accept_leader countrycmedicalorganization countryccivilorganization) =? true.
Axiom deduced_279 : (accept_city countryafirstaidorganization towna) =? true.
Axiom deduced_278 : (accept_leader countryafirstaidorganization sufferterragovernment) =? true.
Axiom deduced_277 : (accept_number countryafirstaidorganization n6) =? true.
Axiom deduced_276 : (accept_population countryafirstaidorganization atheist n75) =? true.
Axiom deduced_275 : (accept_population countryafirstaidorganization christian n24) =? true.
Axiom deduced_274 : (accept_population countryafirstaidorganization muslim n1) =? true.
Axiom deduced_273 : (accept_population countryafirstaidorganization native n0) =? true.
Axiom deduced_272 : (accept_population countryafirstaidorganization other n0) =? true.
Axiom deduced_271 : (accept_number countryafirstaidorganization n1) =? true.
Axiom deduced_270 : (accept_number countryafirstaidorganization n2) =? true.
Axiom deduced_269 : (accept_number countryafirstaidorganization n3) =? true.
Axiom deduced_268 : (accept_number countryafirstaidorganization n4) =? true.
Axiom deduced_267 : (accept_number countryafirstaidorganization n5) =? true.
Axiom deduced_266 : (accept_leader countryccivilorganization sufferterragovernment) =? true.
Axiom deduced_265 : (accept_city countryccivilorganization towna) =? true.
Axiom deduced_264 : (accept_population countryccivilorganization atheist n75) =? true.
Axiom deduced_263 : (accept_population countryccivilorganization christian n24) =? true.
Axiom deduced_262 : (accept_population countryccivilorganization muslim n1) =? true.
Axiom deduced_261 : (accept_population countryccivilorganization native n0) =? true.
Axiom deduced_260 : (accept_population countryccivilorganization other n0) =? true.
Axiom deduced_259 : (accept_leader sufferterragovernment countrybhumanitarianorganization) =? true.
Axiom deduced_258 : (accept_city sufferterragovernment cityb) =? true.
Axiom deduced_257 : (accept_population sufferterragovernment atheist n78) =? true.
Axiom deduced_256 : (accept_population sufferterragovernment christian n20) =? true.
Axiom deduced_255 : (accept_population sufferterragovernment muslim n1) =? true.
Axiom deduced_254 : (accept_population sufferterragovernment native n0) =? true.
Axiom deduced_253 : (accept_population sufferterragovernment other n1) =? true.
Axiom deduced_252 : (accept_leader sufferterragovernment countryacivilorganization) =? true.
Axiom deduced_251 : (accept_city countryahumanitarianorganization towna) =? true.
Axiom deduced_250 : (accept_leader countryahumanitarianorganization sufferterragovernment) =? true.
Axiom deduced_249 : (accept_number countryahumanitarianorganization n6) =? true.
Axiom deduced_248 : (accept_population countryahumanitarianorganization atheist n75) =? true.
Axiom deduced_247 : (accept_population countryahumanitarianorganization christian n24) =? true.
Axiom deduced_246 : (accept_population countryahumanitarianorganization muslim n1) =? true.
Axiom deduced_245 : (accept_population countryahumanitarianorganization native n0) =? true.
Axiom deduced_244 : (accept_population countryahumanitarianorganization other n0) =? true.
Axiom deduced_243 : (accept_number countryahumanitarianorganization n1) =? true.
Axiom deduced_242 : (accept_number countryahumanitarianorganization n2) =? true.
Axiom deduced_241 : (accept_number countryahumanitarianorganization n3) =? true.
Axiom deduced_240 : (accept_number countryahumanitarianorganization n4) =? true.
Axiom deduced_239 : (accept_number countryahumanitarianorganization n5) =? true.
Axiom deduced_238 : (accept_leader countryahumanitarianorganization countrybhumanitarianorganization) =? true.
Axiom deduced_237 : (accept_city countryahumanitarianorganization cityb) =? true.
Axiom deduced_236 : (accept_population countryahumanitarianorganization atheist n78) =? true.
Axiom deduced_235 : (accept_population countryahumanitarianorganization christian n20) =? true.
Axiom deduced_234 : (accept_population countryahumanitarianorganization other n1) =? true.
Axiom deduced_233 : (accept_leader countryahumanitarianorganization countryacivilorganization) =? true.
Axiom deduced_232 : (accept_leader countryacivilorganization countrybhumanitarianorganization) =? true.
Axiom deduced_231 : (accept_city countryacivilorganization cityb) =? true.
Axiom deduced_230 : (accept_population countryacivilorganization atheist n78) =? true.
Axiom deduced_229 : (accept_population countryacivilorganization christian n20) =? true.
Axiom deduced_228 : (accept_population countryacivilorganization other n1) =? true.
Axiom deduced_227 : (accept_city countryamedicalorganization towna) =? true.
Axiom deduced_226 : (accept_leader countryamedicalorganization sufferterragovernment) =? true.
Axiom deduced_225 : (accept_number countryamedicalorganization n6) =? true.
Axiom deduced_224 : (accept_population countryamedicalorganization atheist n75) =? true.
Axiom deduced_223 : (accept_population countryamedicalorganization christian n24) =? true.
Axiom deduced_222 : (accept_population countryamedicalorganization muslim n1) =? true.
Axiom deduced_221 : (accept_population countryamedicalorganization native n0) =? true.
Axiom deduced_220 : (accept_population countryamedicalorganization other n0) =? true.
Axiom deduced_219 : (accept_number countryamedicalorganization n1) =? true.
Axiom deduced_218 : (accept_number countryamedicalorganization n2) =? true.
Axiom deduced_217 : (accept_number countryamedicalorganization n3) =? true.
Axiom deduced_216 : (accept_number countryamedicalorganization n4) =? true.
Axiom deduced_215 : (accept_number countryamedicalorganization n5) =? true.
Axiom deduced_214 : (accept_leader countryamedicalorganization countrybhumanitarianorganization) =? true.
Axiom deduced_213 : (accept_city countryamedicalorganization cityb) =? true.
Axiom deduced_212 : (accept_population countryamedicalorganization atheist n78) =? true.
Axiom deduced_211 : (accept_population countryamedicalorganization christian n20) =? true.
Axiom deduced_210 : (accept_population countryamedicalorganization other n1) =? true.
Axiom deduced_209 : (accept_leader countryamedicalorganization countryacivilorganization) =? true.
Axiom deduced_208 : (accept_city muslimcountrybhumanitarianorganization cityb) =? true.
Axiom deduced_207 : (accept_leader muslimcountrybhumanitarianorganization countrybhumanitarianorganization) =? true.
Axiom deduced_206 : (accept_population muslimcountrybhumanitarianorganization atheist n78) =? true.
Axiom deduced_205 : (accept_population muslimcountrybhumanitarianorganization christian n20) =? true.
Axiom deduced_204 : (accept_population muslimcountrybhumanitarianorganization muslim n1) =? true.
Axiom deduced_203 : (accept_population muslimcountrybhumanitarianorganization native n0) =? true.
Axiom deduced_202 : (accept_population muslimcountrybhumanitarianorganization other n1) =? true.
Axiom deduced_201 : (accept_leader muslimcountrybhumanitarianorganization countryahumanitarianorganization) =? true.
Axiom deduced_200 : (accept_city muslimcountrybhumanitarianorganization townc) =? true.
Axiom deduced_199 : (accept_population muslimcountrybhumanitarianorganization atheist n30) =? true.
Axiom deduced_198 : (accept_population muslimcountrybhumanitarianorganization christian n0) =? true.
Axiom deduced_197 : (accept_population muslimcountrybhumanitarianorganization muslim n65) =? true.
Axiom deduced_196 : (accept_population muslimcountrybhumanitarianorganization other n5) =? true.
Axiom deduced_195 : (accept_leader muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_194 : (accept_leader muslimcountrybhumanitarianorganization countrycmedicalorganization) =? true.
Axiom deduced_193 : (accept_city countrycmedicalorganization cityb) =? true.
Axiom deduced_192 : (accept_population countrycmedicalorganization atheist n78) =? true.
Axiom deduced_191 : (accept_population countrycmedicalorganization christian n20) =? true.
Axiom deduced_190 : (accept_population countrycmedicalorganization other n1) =? true.
Axiom deduced_189 : (accept_leader countrycmedicalorganization countryahumanitarianorganization) =? true.
Axiom deduced_188 : (accept_city countrycmedicalorganization townc) =? true.
Axiom deduced_187 : (accept_population countrycmedicalorganization atheist n30) =? true.
Axiom deduced_186 : (accept_population countrycmedicalorganization christian n0) =? true.
Axiom deduced_185 : (accept_population countrycmedicalorganization muslim n65) =? true.
Axiom deduced_184 : (accept_population countrycmedicalorganization other n5) =? true.
Axiom deduced_183 : (accept_leader countrycmedicalorganization muslimcountrybhumanitarianorganization) =? true.
Axiom deduced_182 : (accept_leader countryccivilorganization countryahumanitarianorganization) =? true.
Axiom deduced_181 : (accept_city countryccivilorganization townc) =? true.
Axiom deduced_180 : (accept_population countryccivilorganization atheist n30) =? true.
Axiom deduced_179 : (accept_population countryccivilorganization christian n0) =? true.
Axiom deduced_178 : (accept_population countryccivilorganization muslim n65) =? true.
Axiom deduced_177 : (accept_population countryccivilorganization other n5) =? true.
Axiom deduced_176 : (accept_leader christiansufferterrahumanitarianorganization countrybhumanitarianorganization) =? true.
Axiom deduced_175 : (accept_city christiansufferterrahumanitarianorganization cityb) =? true.
Axiom deduced_174 : (accept_population christiansufferterrahumanitarianorganization atheist n78) =? true.
Axiom deduced_173 : (accept_population christiansufferterrahumanitarianorganization christian n20) =? true.
Axiom deduced_172 : (accept_population christiansufferterrahumanitarianorganization muslim n1) =? true.
Axiom deduced_171 : (accept_population christiansufferterrahumanitarianorganization native n0) =? true.
Axiom deduced_170 : (accept_population christiansufferterrahumanitarianorganization other n1) =? true.
Axiom deduced_169 : (accept_number christiansufferterrahumanitarianorganization n6) =? true.
Axiom deduced_168 : (accept_number christiansufferterrahumanitarianorganization n1) =? true.
Axiom deduced_167 : (accept_number christiansufferterrahumanitarianorganization n2) =? true.
Axiom deduced_166 : (accept_number christiansufferterrahumanitarianorganization n3) =? true.
Axiom deduced_165 : (accept_number christiansufferterrahumanitarianorganization n4) =? true.
Axiom deduced_164 : (accept_number christiansufferterrahumanitarianorganization n5) =? true.
Axiom deduced_163 : (accept_leader christiansufferterrahumanitarianorganization countryacivilorganization) =? true.
Axiom deduced_162 : (accept_city christiansufferterrahumanitarianorganization townc) =? true.
Axiom deduced_161 : (accept_leader christiansufferterrahumanitarianorganization countryahumanitarianorganization) =? true.
Axiom deduced_160 : (accept_population christiansufferterrahumanitarianorganization atheist n30) =? true.
Axiom deduced_159 : (accept_population christiansufferterrahumanitarianorganization christian n0) =? true.
Axiom deduced_158 : (accept_population christiansufferterrahumanitarianorganization muslim n65) =? true.
Axiom deduced_157 : (accept_population christiansufferterrahumanitarianorganization other n5) =? true.
Axiom deduced_156 : (accept_leader muslimcountrybhumanitarianorganization countrybcivilorganization) =? true.
Axiom deduced_155 : (accept_leader muslimcountrybhumanitarianorganization countryccivilorganization) =? true.
Axiom deduced_154 : (accept_city sufferterragovernment townc) =? true.
Axiom deduced_153 : (accept_leader sufferterragovernment countryahumanitarianorganization) =? true.
Axiom deduced_152 : (accept_population sufferterragovernment atheist n30) =? true.
Axiom deduced_151 : (accept_population sufferterragovernment christian n0) =? true.
Axiom deduced_150 : (accept_population sufferterragovernment muslim n65) =? true.
Axiom deduced_149 : (accept_population sufferterragovernment other n5) =? true.
Axiom deduced_148 : (accept_leader sufferterragovernment christiancountrychumanitarianorganization) =? true.
Axiom deduced_147 : (accept_city sufferterragovernment coastvillage) =? true.
Axiom deduced_146 : (accept_population sufferterragovernment atheist n12) =? true.
Axiom deduced_145 : (accept_population sufferterragovernment christian n3) =? true.
Axiom deduced_144 : (accept_population sufferterragovernment muslim n0) =? true.
Axiom deduced_143 : (accept_population sufferterragovernment native n85) =? true.
Axiom deduced_142 : (accept_population sufferterragovernment other n0) =? true.
Axiom deduced_141 : (accept_leader sufferterragovernment countryafirstaidorganization) =? true.
Axiom deduced_140 : (accept_leader countrybhumanitarianorganization sufferterragovernment) =? true.
Axiom deduced_139 : (accept_city countrybhumanitarianorganization towna) =? true.
Axiom deduced_138 : (accept_population countrybhumanitarianorganization atheist n75) =? true.
Axiom deduced_137 : (accept_population countrybhumanitarianorganization christian n24) =? true.
Axiom deduced_136 : (accept_population countrybhumanitarianorganization muslim n1) =? true.
Axiom deduced_135 : (accept_population countrybhumanitarianorganization native n0) =? true.
Axiom deduced_134 : (accept_population countrybhumanitarianorganization other n0) =? true.
Axiom deduced_133 : (accept_leader countrybhumanitarianorganization countrycmedicalorganization) =? true.
Axiom deduced_132 : (accept_leader countrybhumanitarianorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_131 : (accept_leader countrybhumanitarianorganization countrybcivilorganization) =? true.
Axiom deduced_130 : (accept_leader countrybhumanitarianorganization countryccivilorganization) =? true.
Axiom deduced_129 : (accept_leader countrybhumanitarianorganization countryahumanitarianorganization) =? true.
Axiom deduced_128 : (accept_city countrybhumanitarianorganization townc) =? true.
Axiom deduced_127 : (accept_population countrybhumanitarianorganization atheist n30) =? true.
Axiom deduced_126 : (accept_population countrybhumanitarianorganization christian n0) =? true.
Axiom deduced_125 : (accept_population countrybhumanitarianorganization muslim n65) =? true.
Axiom deduced_124 : (accept_population countrybhumanitarianorganization other n5) =? true.
Axiom deduced_123 : (accept_leader countrybhumanitarianorganization muslimcountrybhumanitarianorganization) =? true.
Axiom deduced_122 : (accept_city countrybhumanitarianorganization coastvillage) =? true.
Axiom deduced_121 : (accept_population countrybhumanitarianorganization atheist n12) =? true.
Axiom deduced_120 : (accept_population countrybhumanitarianorganization christian n3) =? true.
Axiom deduced_119 : (accept_population countrybhumanitarianorganization muslim n0) =? true.
Axiom deduced_118 : (accept_population countrybhumanitarianorganization native n85) =? true.
Axiom deduced_117 : (accept_leader countrybhumanitarianorganization countryacivilorganization) =? true.
Axiom deduced_116 : (accept_leader countryafirstaidorganization countrybhumanitarianorganization) =? true.
Axiom deduced_115 : (accept_city countryafirstaidorganization cityb) =? true.
Axiom deduced_114 : (accept_population countryafirstaidorganization atheist n78) =? true.
Axiom deduced_113 : (accept_population countryafirstaidorganization christian n20) =? true.
Axiom deduced_112 : (accept_population countryafirstaidorganization other n1) =? true.
Axiom deduced_111 : (accept_leader countryafirstaidorganization countryacivilorganization) =? true.
Axiom deduced_110 : (accept_city countryafirstaidorganization townc) =? true.
Axiom deduced_109 : (accept_leader countryafirstaidorganization countryahumanitarianorganization) =? true.
Axiom deduced_108 : (accept_population countryafirstaidorganization atheist n30) =? true.
Axiom deduced_107 : (accept_population countryafirstaidorganization christian n0) =? true.
Axiom deduced_106 : (accept_population countryafirstaidorganization muslim n65) =? true.
Axiom deduced_105 : (accept_population countryafirstaidorganization other n5) =? true.
Axiom deduced_104 : (accept_leader countryafirstaidorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_103 : (accept_city countryafirstaidorganization coastvillage) =? true.
Axiom deduced_102 : (accept_population countryafirstaidorganization atheist n12) =? true.
Axiom deduced_101 : (accept_population countryafirstaidorganization christian n3) =? true.
Axiom deduced_100 : (accept_population countryafirstaidorganization muslim n0) =? true.
Axiom deduced_99 : (accept_population countryafirstaidorganization native n85) =? true.
Axiom deduced_98 : (accept_city muslimcountrybhumanitarianorganization coastvillage) =? true.
Axiom deduced_97 : (accept_population muslimcountrybhumanitarianorganization atheist n12) =? true.
Axiom deduced_96 : (accept_population muslimcountrybhumanitarianorganization christian n3) =? true.
Axiom deduced_95 : (accept_population muslimcountrybhumanitarianorganization muslim n0) =? true.
Axiom deduced_94 : (accept_population muslimcountrybhumanitarianorganization native n85) =? true.
Axiom deduced_93 : (accept_population muslimcountrybhumanitarianorganization other n0) =? true.
Axiom deduced_92 : (accept_leader muslimcountrybhumanitarianorganization countryacivilorganization) =? true.
Axiom deduced_91 : (accept_leader christiansufferterrahumanitarianorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_90 : (accept_city christiansufferterrahumanitarianorganization coastvillage) =? true.
Axiom deduced_89 : (accept_population christiansufferterrahumanitarianorganization atheist n12) =? true.
Axiom deduced_88 : (accept_population christiansufferterrahumanitarianorganization christian n3) =? true.
Axiom deduced_87 : (accept_population christiansufferterrahumanitarianorganization muslim n0) =? true.
Axiom deduced_86 : (accept_population christiansufferterrahumanitarianorganization native n85) =? true.
Axiom deduced_85 : (accept_population christiansufferterrahumanitarianorganization other n0) =? true.
Axiom deduced_84 : (accept_leader christiansufferterrahumanitarianorganization countryafirstaidorganization) =? true.
Axiom deduced_83 : (accept_city christiansufferterrahumanitarianorganization towna) =? true.
Axiom deduced_81 : (accept_population christiansufferterrahumanitarianorganization atheist n75) =? true.
Axiom deduced_80 : (accept_population christiansufferterrahumanitarianorganization christian n24) =? true.
Axiom deduced_79 : (accept_city countryacivilorganization townc) =? true.
Axiom deduced_78 : (accept_leader countryacivilorganization countryahumanitarianorganization) =? true.
Axiom deduced_77 : (accept_population countryacivilorganization atheist n30) =? true.
Axiom deduced_76 : (accept_population countryacivilorganization christian n0) =? true.
Axiom deduced_75 : (accept_population countryacivilorganization muslim n65) =? true.
Axiom deduced_74 : (accept_population countryacivilorganization other n5) =? true.
Axiom deduced_73 : (accept_leader countryacivilorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_72 : (accept_city countryacivilorganization coastvillage) =? true.
Axiom deduced_71 : (accept_population countryacivilorganization atheist n12) =? true.
Axiom deduced_70 : (accept_population countryacivilorganization christian n3) =? true.
Axiom deduced_69 : (accept_population countryacivilorganization muslim n0) =? true.
Axiom deduced_68 : (accept_population countryacivilorganization native n85) =? true.
Axiom deduced_67 : (accept_leader countryacivilorganization countryafirstaidorganization) =? true.
Axiom deduced_66 : (accept_leader countryacivilorganization countryamedicalorganization) =? true.
Axiom deduced_65 : (accept_leader countryccivilorganization countryacivilorganization) =? true.
Axiom deduced_64 : (accept_city countryccivilorganization cityb) =? true.
Axiom deduced_63 : (accept_leader countryccivilorganization countrybhumanitarianorganization) =? true.
Axiom deduced_61 : (accept_population countryccivilorganization atheist n78) =? true.
Axiom deduced_60 : (accept_population countryccivilorganization christian n20) =? true.
Axiom deduced_59 : (accept_population countryccivilorganization other n1) =? true.
Axiom deduced_57 : (accept_city sufferterragovernment towna) =? true.
Axiom deduced_56 : (accept_population sufferterragovernment atheist n75) =? true.
Axiom deduced_55 : (accept_population sufferterragovernment christian n24) =? true.
Axiom deduced_54 : (accept_leader sufferterragovernment countryamedicalorganization) =? true.
Axiom deduced_53 : (accept_city countrybcivilorganization cityb) =? true.
Axiom deduced_52 : (accept_population countrybcivilorganization atheist n78) =? true.
Axiom deduced_51 : (accept_population countrybcivilorganization christian n20) =? true.
Axiom deduced_50 : (accept_population countrybcivilorganization other n1) =? true.
Axiom deduced_49 : (accept_leader countrybcivilorganization countryahumanitarianorganization) =? true.
Axiom deduced_48 : (accept_city countrybcivilorganization townc) =? true.
Axiom deduced_47 : (accept_population countrybcivilorganization atheist n30) =? true.
Axiom deduced_46 : (accept_population countrybcivilorganization christian n0) =? true.
Axiom deduced_45 : (accept_population countrybcivilorganization muslim n65) =? true.
Axiom deduced_44 : (accept_population countrybcivilorganization other n5) =? true.
Axiom deduced_43 : (accept_leader countrybcivilorganization muslimcountrybhumanitarianorganization) =? true.
Axiom deduced_42 : (accept_city countrybcivilorganization coastvillage) =? true.
Axiom deduced_41 : (accept_population countrybcivilorganization atheist n12) =? true.
Axiom deduced_40 : (accept_population countrybcivilorganization christian n3) =? true.
Axiom deduced_39 : (accept_population countrybcivilorganization muslim n0) =? true.
Axiom deduced_38 : (accept_population countrybcivilorganization native n85) =? true.
Axiom deduced_37 : (accept_leader countrybcivilorganization countryacivilorganization) =? true.
Axiom deduced_36 : (accept_city countrycmedicalorganization coastvillage) =? true.
Axiom deduced_35 : (accept_population countrycmedicalorganization atheist n12) =? true.
Axiom deduced_34 : (accept_population countrycmedicalorganization christian n3) =? true.
Axiom deduced_33 : (accept_population countrycmedicalorganization muslim n0) =? true.
Axiom deduced_32 : (accept_population countrycmedicalorganization native n85) =? true.
Axiom deduced_31 : (accept_leader countrycmedicalorganization countryacivilorganization) =? true.
Axiom deduced_30 : (accept_leader christiansufferterrahumanitarianorganization countryamedicalorganization) =? true.
Axiom deduced_29 : (accept_leader countryafirstaidorganization countryamedicalorganization) =? true.
Axiom deduced_28 : (accept_leader countryahumanitarianorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_27 : (accept_city countryahumanitarianorganization coastvillage) =? true.
Axiom deduced_26 : (accept_population countryahumanitarianorganization atheist n12) =? true.
Axiom deduced_25 : (accept_population countryahumanitarianorganization christian n3) =? true.
Axiom deduced_24 : (accept_population countryahumanitarianorganization muslim n0) =? true.
Axiom deduced_23 : (accept_population countryahumanitarianorganization native n85) =? true.
Axiom deduced_22 : (accept_leader countryahumanitarianorganization countryafirstaidorganization) =? true.
Axiom deduced_21 : (accept_leader countryahumanitarianorganization countryamedicalorganization) =? true.
Axiom deduced_20 : (accept_city countryamedicalorganization townc) =? true.
Axiom deduced_19 : (accept_leader countryamedicalorganization countryahumanitarianorganization) =? true.
Axiom deduced_18 : (accept_population countryamedicalorganization atheist n30) =? true.
Axiom deduced_17 : (accept_population countryamedicalorganization christian n0) =? true.
Axiom deduced_16 : (accept_population countryamedicalorganization muslim n65) =? true.
Axiom deduced_15 : (accept_population countryamedicalorganization other n5) =? true.
Axiom deduced_14 : (accept_leader countryamedicalorganization christiancountrychumanitarianorganization) =? true.
Axiom deduced_12 : (accept_city christiancountrychumanitarianorganization cityb) =? true.
Axiom deduced_11 : (accept_population christiancountrychumanitarianorganization atheist n78) =? true.
Axiom deduced_10 : (accept_population christiancountrychumanitarianorganization christian n20) =? true.
Axiom deduced_9 : (accept_population christiancountrychumanitarianorganization other n1) =? true.
Axiom deduced_8 : (accept_leader christiancountrychumanitarianorganization countryahumanitarianorganization) =? true.
Axiom deduced_7 : (accept_city christiancountrychumanitarianorganization townc) =? true.
Axiom deduced_6 : (accept_population christiancountrychumanitarianorganization atheist n30) =? true.
Axiom deduced_5 : (accept_population christiancountrychumanitarianorganization christian n0) =? true.
Axiom deduced_4 : (accept_population christiancountrychumanitarianorganization muslim n65) =? true.
Axiom deduced_3 : (accept_population christiancountrychumanitarianorganization other n5) =? true.
Axiom deduced_2 : (accept_leader christiancountrychumanitarianorganization muslimcountrybhumanitarianorganization) =? true.
Axiom deduced_1 : (accept_leader christiancountrychumanitarianorganization countryacivilorganization) =? true.
Axiom event_249 : (any_agent_in_all_proposed_teams muslimcountrybhumanitarianorganization sufferterragovernment towna) =? true.
Axiom event_248 : (the_agent_not_in_any_proposed_teams muslimcountrybhumanitarianorganization sufferterragovernment towna) =? true.
Axiom event_247 : (accept_number muslimcountrybhumanitarianorganization n6) =? true.
Axiom event_245 : (accept_number countrycmedicalorganization n6) =? true.
Axiom event_244 : (any_agent_in_all_proposed_teams christiancountrychumanitarianorganization sufferterragovernment towna) =? true.
Axiom event_243 : (the_agent_in_all_proposed_teams christiancountrychumanitarianorganization sufferterragovernment towna) =? true.
Axiom event_242 : (accept_number christiancountrychumanitarianorganization n6) =? true.
Axiom event_241 : (accept_team christiancountrychumanitarianorganization countrycmedicalorganization towna n6) =? true.
Axiom event_240 : (accept_team christiancountrychumanitarianorganization countrybhumanitarianorganization towna n6) =? true.
Axiom event_239 : (accept_number countrybhumanitarianorganization n6) =? true.
Axiom event_238 : (accept_team christiancountrychumanitarianorganization countrybcivilorganization towna n6) =? true.
Axiom event_237 : (accept_number countrybcivilorganization n6) =? true.
Axiom event_236 : (accept_team christiancountrychumanitarianorganization countryccivilorganization towna n4) =? true.
Axiom event_235 : (accept_number countryccivilorganization n4) =? true.
Axiom event_234 : (accept_number christiancountrychumanitarianorganization n3) =? true.
Axiom event_233 : (any_agent_in_all_proposed_teams countrycmedicalorganization sufferterragovernment towna) =? true.
Axiom event_232 : (the_agent_in_all_proposed_teams countrycmedicalorganization sufferterragovernment towna) =? true.
Axiom event_231 : (accept_team countrycmedicalorganization christiancountrychumanitarianorganization towna n6) =? true.
Axiom event_230 : (accept_team countrycmedicalorganization countrybhumanitarianorganization towna n6) =? true.
Axiom event_229 : (accept_team countrycmedicalorganization countrybcivilorganization towna n6) =? true.
Axiom event_228 : (accept_team countrycmedicalorganization countryccivilorganization towna n4) =? true.
Axiom event_227 : (accept_number countrycmedicalorganization n3) =? true.
Axiom event_226 : (accept_number countrycmedicalorganization n2) =? true.
Axiom event_225 : (accept_team countryacivilorganization sufferterragovernment towna n6) =? true.
Axiom event_224 : (accept_number sufferterragovernment n6) =? true.
Axiom event_223 : (accept_team countryacivilorganization sufferterragovernment towna n5) =? true.
Axiom event_222 : (accept_number sufferterragovernment n5) =? true.
Axiom event_221 : (any_agent_in_all_proposed_teams countryccivilorganization sufferterragovernment towna) =? true.
Axiom event_220 : (the_agent_in_all_proposed_teams countryccivilorganization sufferterragovernment towna) =? true.
Axiom event_215 : (accept_number countryccivilorganization n3) =? true.
Axiom event_214 : (accept_number countryccivilorganization n2) =? true.
Axiom event_211 : (accept_number sufferterragovernment n2) =? true.
Axiom event_210 : (any_agent_in_all_proposed_teams countrybcivilorganization sufferterragovernment towna) =? true.
Axiom event_209 : (the_agent_in_all_proposed_teams countrybcivilorganization sufferterragovernment towna) =? true.
Axiom event_208 : (accept_team countrybcivilorganization countrycmedicalorganization towna n6) =? true.
Axiom event_207 : (accept_team countrybcivilorganization christiancountrychumanitarianorganization towna n6) =? true.
Axiom event_206 : (accept_team countrybcivilorganization countrybhumanitarianorganization towna n6) =? true.
Axiom event_205 : (accept_team countrybcivilorganization countryccivilorganization towna n4) =? true.
Axiom event_204 : (accept_number countrybcivilorganization n3) =? true.
Axiom event_203 : (accept_number countrybcivilorganization n2) =? true.
Axiom event_202 : (any_agent_in_all_proposed_teams countrybhumanitarianorganization sufferterragovernment towna) =? true.
Axiom event_201 : (the_agent_in_all_proposed_teams countrybhumanitarianorganization sufferterragovernment towna) =? true.
Axiom event_200 : (accept_team countrybhumanitarianorganization countrycmedicalorganization towna n6) =? true.
Axiom event_199 : (accept_team countrybhumanitarianorganization christiancountrychumanitarianorganization towna n6) =? true.
Axiom event_198 : (accept_team countrybhumanitarianorganization countrybcivilorganization towna n6) =? true.
Axiom event_197 : (accept_number countrybhumanitarianorganization n2) =? true.
Axiom event_196 : (accept_team countrybhumanitarianorganization countryccivilorganization towna n3) =? true.
Axiom event_195 : (accept_team countrybhumanitarianorganization countrycmedicalorganization towna n3) =? true.
Axiom event_194 : (accept_team countrybhumanitarianorganization christiancountrychumanitarianorganization towna n3) =? true.
Axiom event_193 : (accept_team countrybhumanitarianorganization countrybcivilorganization towna n3) =? true.
Axiom event_192 : (accept_number christiancountrychumanitarianorganization n2) =? true.
Axiom event_191 : (accept_team countryahumanitarianorganization sufferterragovernment towna n6) =? true.
Axiom event_190 : (accept_team countryahumanitarianorganization sufferterragovernment towna n5) =? true.
Axiom event_189 : (accept_team countryamedicalorganization sufferterragovernment towna n6) =? true.
Axiom event_188 : (accept_team countryamedicalorganization sufferterragovernment towna n5) =? true.
Axiom event_183 : (accept_number muslimcountrybhumanitarianorganization n2) =? true.
Axiom event_173 : (accept_team muslimcountrybhumanitarianorganization countrybhumanitarianorganization cityb n6) =? true.
Axiom event_172 : (accept_team muslimcountrybhumanitarianorganization countrybhumanitarianorganization cityb n5) =? true.
Axiom event_171 : (accept_number countrybhumanitarianorganization n5) =? true.
Axiom event_170 : (any_agent_in_all_proposed_teams countryacivilorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_169 : (the_agent_in_all_proposed_teams countryacivilorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_168 : (accept_number countryacivilorganization n6) =? true.
Axiom event_167 : (accept_team countryacivilorganization countryahumanitarianorganization cityb n6) =? true.
Axiom event_166 : (accept_number countryahumanitarianorganization n6) =? true.
Axiom event_165 : (any_agent_in_all_proposed_teams countryahumanitarianorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_164 : (the_agent_in_all_proposed_teams countryahumanitarianorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_163 : (accept_team christiancountrychumanitarianorganization countrybhumanitarianorganization cityb n6) =? true.
Axiom event_162 : (accept_team christiancountrychumanitarianorganization countrybhumanitarianorganization cityb n5) =? true.
Axiom event_161 : (accept_team countrybcivilorganization countrybhumanitarianorganization cityb n6) =? true.
Axiom event_160 : (accept_team countrybcivilorganization countrybhumanitarianorganization cityb n5) =? true.
Axiom event_159 : (any_agent_in_all_proposed_teams countryamedicalorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_158 : (the_agent_in_all_proposed_teams countryamedicalorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_157 : (accept_number countryamedicalorganization n6) =? true.
Axiom event_156 : (accept_team countryamedicalorganization countryahumanitarianorganization cityb n6) =? true.
Axiom event_155 : (accept_team countrycmedicalorganization countrybhumanitarianorganization cityb n6) =? true.
Axiom event_154 : (accept_team countrycmedicalorganization countrybhumanitarianorganization cityb n5) =? true.
Axiom event_153 : (accept_team countryafirstaidorganization sufferterragovernment towna n6) =? true.
Axiom event_152 : (accept_team countryafirstaidorganization sufferterragovernment towna n5) =? true.
Axiom event_151 : (any_agent_in_all_proposed_teams countryafirstaidorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_150 : (the_agent_in_all_proposed_teams countryafirstaidorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_149 : (accept_number countryafirstaidorganization n6) =? true.
Axiom event_148 : (accept_team countryafirstaidorganization countryahumanitarianorganization cityb n6) =? true.
Axiom event_147 : (any_agent_in_all_proposed_teams sufferterragovernment countrybhumanitarianorganization cityb) =? true.
Axiom event_146 : (the_agent_in_all_proposed_teams sufferterragovernment countrybhumanitarianorganization cityb) =? true.
Axiom event_145 : (accept_team sufferterragovernment countryahumanitarianorganization cityb n6) =? true.
Axiom event_142 : (any_agent_in_all_proposed_teams christiansufferterrahumanitarianorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_141 : (the_agent_in_all_proposed_teams christiansufferterrahumanitarianorganization countrybhumanitarianorganization cityb) =? true.
Axiom event_140 : (accept_number christiansufferterrahumanitarianorganization n6) =? true.
Axiom event_139 : (accept_team christiansufferterrahumanitarianorganization countryahumanitarianorganization cityb n6) =? true.
Axiom event_138 : (any_agent_in_all_proposed_teams countrybhumanitarianorganization countryahumanitarianorganization townc) =? true.
Axiom event_137 : (the_agent_in_all_proposed_teams countrybhumanitarianorganization countryahumanitarianorganization townc) =? true.
Axiom event_136 : (accept_team countrybhumanitarianorganization countrycmedicalorganization townc n6) =? true.
Axiom event_135 : (accept_team countrybhumanitarianorganization christiancountrychumanitarianorganization townc n6) =? true.
Axiom event_134 : (accept_team countrybhumanitarianorganization countrybcivilorganization townc n6) =? true.
Axiom event_133 : (any_agent_in_all_proposed_teams countrycmedicalorganization countryahumanitarianorganization townc) =? true.
Axiom event_132 : (the_agent_in_all_proposed_teams countrycmedicalorganization countryahumanitarianorganization townc) =? true.
Axiom event_131 : (accept_team countrycmedicalorganization christiancountrychumanitarianorganization townc n6) =? true.
Axiom event_130 : (accept_team countrycmedicalorganization countrybhumanitarianorganization townc n6) =? true.
Axiom event_129 : (accept_team countrycmedicalorganization countrybcivilorganization townc n6) =? true.
Axiom event_128 : (accept_team countrycmedicalorganization muslimcountrybhumanitarianorganization townc n6) =? true.
Axiom event_127 : (accept_team countrycmedicalorganization countryccivilorganization townc n4) =? true.
Axiom event_126 : (accept_team countryamedicalorganization countryahumanitarianorganization townc n6) =? true.
Axiom event_125 : (accept_team christiansufferterrahumanitarianorganization countryahumanitarianorganization townc n6) =? true.
Axiom event_124 : (accept_team sufferterragovernment countryahumanitarianorganization townc n6) =? true.
Axiom event_123 : (accept_team countrybhumanitarianorganization muslimcountrybhumanitarianorganization townc n6) =? true.
Axiom event_122 : (accept_team countrybhumanitarianorganization countrybcivilorganization townc n2) =? true.
Axiom event_121 : (any_agent_in_all_proposed_teams countryccivilorganization countryahumanitarianorganization townc) =? true.
Axiom event_120 : (the_agent_in_all_proposed_teams countryccivilorganization countryahumanitarianorganization townc) =? true.
Axiom event_114 : (any_agent_in_all_proposed_teams christiancountrychumanitarianorganization countryahumanitarianorganization townc) =? true.
Axiom event_113 : (the_agent_in_all_proposed_teams christiancountrychumanitarianorganization countryahumanitarianorganization townc) =? true.
Axiom event_112 : (accept_team christiancountrychumanitarianorganization countrycmedicalorganization townc n6) =? true.
Axiom event_111 : (accept_team christiancountrychumanitarianorganization countrybhumanitarianorganization townc n6) =? true.
Axiom event_110 : (accept_team christiancountrychumanitarianorganization countrybcivilorganization townc n6) =? true.
Axiom event_109 : (accept_team christiancountrychumanitarianorganization muslimcountrybhumanitarianorganization townc n6) =? true.
Axiom event_108 : (accept_team christiancountrychumanitarianorganization countryccivilorganization townc n4) =? true.
Axiom event_107 : (accept_team countryafirstaidorganization countryahumanitarianorganization townc n6) =? true.
Axiom event_106 : (accept_team countryacivilorganization countryahumanitarianorganization townc n6) =? true.
Axiom event_105 : (any_agent_in_all_proposed_teams muslimcountrybhumanitarianorganization countryahumanitarianorganization townc) =? true.
Axiom event_104 : (the_agent_in_all_proposed_teams muslimcountrybhumanitarianorganization countryahumanitarianorganization townc) =? true.
Axiom event_103 : (accept_team muslimcountrybhumanitarianorganization countrycmedicalorganization townc n6) =? true.
Axiom event_102 : (accept_team muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization townc n6) =? true.
Axiom event_101 : (accept_team muslimcountrybhumanitarianorganization countrybhumanitarianorganization townc n6) =? true.
Axiom event_100 : (accept_team muslimcountrybhumanitarianorganization countrybcivilorganization townc n6) =? true.
Axiom event_99 : (accept_team muslimcountrybhumanitarianorganization countryccivilorganization townc n4) =? true.
Axiom event_98 : (accept_number muslimcountrybhumanitarianorganization n3) =? true.
Axiom event_97 : (accept_team muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization coastvillage n6) =? true.
Axiom event_96 : (accept_team countrycmedicalorganization christiancountrychumanitarianorganization coastvillage n6) =? true.
Axiom event_95 : (any_agent_in_all_proposed_teams christiansufferterrahumanitarianorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_94 : (the_agent_in_all_proposed_teams christiansufferterrahumanitarianorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_93 : (accept_team christiansufferterrahumanitarianorganization countryafirstaidorganization coastvillage n6) =? true.
Axiom event_92 : (accept_team christiansufferterrahumanitarianorganization countryacivilorganization coastvillage n6) =? true.
Axiom event_91 : (accept_team christiansufferterrahumanitarianorganization countryahumanitarianorganization coastvillage n6) =? true.
Axiom event_90 : (accept_team christiansufferterrahumanitarianorganization countryahumanitarianorganization coastvillage n5) =? true.
Axiom event_89 : (accept_number countryahumanitarianorganization n5) =? true.
Axiom event_88 : (accept_number christiansufferterrahumanitarianorganization n2) =? true.
Axiom event_87 : (any_agent_in_all_proposed_teams sufferterragovernment christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_86 : (the_agent_in_all_proposed_teams sufferterragovernment christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_85 : (accept_team sufferterragovernment countryafirstaidorganization coastvillage n6) =? true.
Axiom event_84 : (accept_team sufferterragovernment countryacivilorganization coastvillage n6) =? true.
Axiom event_83 : (accept_team sufferterragovernment countryahumanitarianorganization coastvillage n6) =? true.
Axiom event_82 : (accept_team sufferterragovernment countryahumanitarianorganization coastvillage n5) =? true.
Axiom event_81 : (any_agent_in_all_proposed_teams countrybcivilorganization countryahumanitarianorganization townc) =? true.
Axiom event_80 : (the_agent_in_all_proposed_teams countrybcivilorganization countryahumanitarianorganization townc) =? true.
Axiom event_79 : (accept_team countrybcivilorganization countrycmedicalorganization townc n6) =? true.
Axiom event_78 : (accept_team countrybcivilorganization christiancountrychumanitarianorganization townc n6) =? true.
Axiom event_77 : (accept_team countrybcivilorganization countrybhumanitarianorganization townc n6) =? true.
Axiom event_76 : (accept_team countrybcivilorganization muslimcountrybhumanitarianorganization townc n6) =? true.
Axiom event_75 : (accept_team countrybcivilorganization christiancountrychumanitarianorganization coastvillage n6) =? true.
Axiom event_74 : (accept_team countrybcivilorganization christiancountrychumanitarianorganization coastvillage n5) =? true.
Axiom event_73 : (accept_number christiancountrychumanitarianorganization n5) =? true.
Axiom event_70 : (any_agent_in_all_proposed_teams countryafirstaidorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_69 : (the_agent_in_all_proposed_teams countryafirstaidorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_68 : (accept_team countryafirstaidorganization countryacivilorganization coastvillage n6) =? true.
Axiom event_67 : (accept_team countryafirstaidorganization countryahumanitarianorganization coastvillage n6) =? true.
Axiom event_66 : (accept_team countryafirstaidorganization countryahumanitarianorganization coastvillage n5) =? true.
Axiom event_65 : (accept_number countryafirstaidorganization n2) =? true.
Axiom event_64 : (any_agent_in_all_proposed_teams countryacivilorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_63 : (the_agent_in_all_proposed_teams countryacivilorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_62 : (accept_team countryacivilorganization countryafirstaidorganization coastvillage n6) =? true.
Axiom event_61 : (accept_team countryacivilorganization countryahumanitarianorganization coastvillage n6) =? true.
Axiom event_60 : (accept_team countryacivilorganization countryahumanitarianorganization coastvillage n5) =? true.
Axiom event_59 : (accept_number countryacivilorganization n2) =? true.
Axiom event_58 : (accept_team countryafirstaidorganization countryacivilorganization towna n6) =? true.
Axiom event_57 : (any_agent_in_all_proposed_teams christiancountrychumanitarianorganization countryacivilorganization towna) =? true.
Axiom event_56 : (the_agent_in_all_proposed_teams christiancountrychumanitarianorganization countryacivilorganization towna) =? true.
Axiom event_55 : (accept_team christiancountrychumanitarianorganization countrycmedicalorganization towna n5) =? true.
Axiom event_54 : (accept_number countrycmedicalorganization n5) =? true.
Axiom event_53 : (accept_team christiancountrychumanitarianorganization countrycmedicalorganization towna n4) =? true.
Axiom event_52 : (accept_number countrycmedicalorganization n4) =? true.
Axiom event_51 : (accept_team countrycmedicalorganization christiancountrychumanitarianorganization coastvillage n5) =? true.
Axiom event_50 : (any_agent_in_all_proposed_teams countrycmedicalorganization countryacivilorganization towna) =? true.
Axiom event_49 : (the_agent_in_all_proposed_teams countrycmedicalorganization countryacivilorganization towna) =? true.
Axiom event_48 : (accept_team sufferterragovernment countryacivilorganization towna n6) =? true.
Axiom event_47 : (any_agent_in_all_proposed_teams countrybcivilorganization countryacivilorganization towna) =? true.
Axiom event_46 : (the_agent_in_all_proposed_teams countrybcivilorganization countryacivilorganization towna) =? true.
Axiom event_45 : (accept_number countrybcivilorganization n5) =? true.
Axiom event_44 : (accept_team countrybcivilorganization countrycmedicalorganization towna n5) =? true.
Axiom event_43 : (accept_team countrybcivilorganization countrycmedicalorganization towna n4) =? true.
Axiom event_42 : (any_agent_in_all_proposed_teams countryccivilorganization countryacivilorganization towna) =? true.
Axiom event_41 : (the_agent_in_all_proposed_teams countryccivilorganization countryacivilorganization towna) =? true.
Axiom event_39 : (accept_team countryccivilorganization countrycmedicalorganization towna n4) =? true.
Axiom event_38 : (any_agent_in_all_proposed_teams countryamedicalorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_37 : (the_agent_not_in_any_proposed_teams countryamedicalorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_28 : (accept_number countryahumanitarianorganization n2) =? true.
Axiom event_27 : (accept_team countryamedicalorganization countryacivilorganization towna n6) =? true.
Axiom event_26 : (accept_team christiansufferterrahumanitarianorganization countryacivilorganization towna n6) =? true.
Axiom event_25 : (accept_team countrybhumanitarianorganization christiancountrychumanitarianorganization coastvillage n6) =? true.
Axiom event_24 : (accept_team countrybhumanitarianorganization christiancountrychumanitarianorganization coastvillage n5) =? true.
Axiom event_23 : (any_agent_in_all_proposed_teams countrybhumanitarianorganization countryacivilorganization towna) =? true.
Axiom event_22 : (the_agent_in_all_proposed_teams countrybhumanitarianorganization countryacivilorganization towna) =? true.
Axiom event_21 : (accept_number countrybhumanitarianorganization n1) =? true.
Axiom event_20 : (accept_team sufferterragovernment countryacivilorganization cityb n6) =? true.
Axiom event_19 : (accept_team christiansufferterrahumanitarianorganization countryacivilorganization cityb n6) =? true.
Axiom event_18 : (accept_team countrybcivilorganization countrybhumanitarianorganization cityb n4) =? true.
Axiom event_17 : (accept_number countrybhumanitarianorganization n4) =? true.
Axiom event_16 : (accept_team countryafirstaidorganization countryacivilorganization cityb n6) =? true.
Axiom event_15 : (accept_team christiancountrychumanitarianorganization countrybhumanitarianorganization cityb n4) =? true.
Axiom event_14 : (accept_team countryamedicalorganization countryacivilorganization cityb n6) =? true.
Axiom event_13 : (accept_team muslimcountrybhumanitarianorganization christiancountrychumanitarianorganization coastvillage n5) =? true.
Axiom event_12 : (any_agent_in_all_proposed_teams muslimcountrybhumanitarianorganization countryacivilorganization towna) =? true.
Axiom event_11 : (the_agent_not_in_any_proposed_teams muslimcountrybhumanitarianorganization countryacivilorganization towna) =? true.
Axiom event_8 : (accept_team muslimcountrybhumanitarianorganization countrybhumanitarianorganization cityb n4) =? true.
Axiom event_7 : (accept_team countryccivilorganization countrybhumanitarianorganization cityb n2) =? true.
Axiom event_6 : (any_agent_in_all_proposed_teams countryahumanitarianorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_5 : (the_agent_in_all_proposed_teams countryahumanitarianorganization christiancountrychumanitarianorganization coastvillage) =? true.
Axiom event_4 : (accept_team countryahumanitarianorganization countryafirstaidorganization coastvillage n6) =? true.
Axiom event_3 : (accept_team countryahumanitarianorganization countryacivilorganization coastvillage n6) =? true.
Axiom event_2 : (accept_team countryahumanitarianorganization countryacivilorganization towna n6) =? true.
Axiom event_1 : (accept_team countryahumanitarianorganization countryacivilorganization cityb n6) =? true.
Axiom a2_13 : forall A : Z, (ifeq3 (accept_city A townc) true (accept_population A christian n0) true) =? true.
Axiom a2_13_1 : forall A : Z, (ifeq3 (accept_city A townc) true (accept_population A atheist n30) true) =? true.
Axiom a2_13_2 : forall A : Z, (ifeq3 (accept_city A townc) true (accept_population A muslim n65) true) =? true.
Axiom a2_13_3 : forall A : Z, (ifeq3 (accept_city A townc) true (accept_population A native n0) true) =? true.
Axiom a2_13_4 : forall A : Z, (ifeq3 (accept_city A townc) true (accept_population A other n5) true) =? true.
Axiom a2_13_5 : forall A : Z, (ifeq3 (accept_population A other n5) true (ifeq3 (accept_population A native n0) true (ifeq3 (accept_population A muslim n65) true (ifeq3 (accept_population A atheist n30) true (ifeq3 (accept_population A christian n0) true (accept_city A townc) true) true) true) true) true) =? true.
Axiom a2_12 : forall A : Z, (ifeq3 (accept_city A cityb) true (accept_population A christian n20) true) =? true.
Axiom a2_12_1 : forall A : Z, (ifeq3 (accept_city A cityb) true (accept_population A atheist n78) true) =? true.
Axiom a2_12_2 : forall A : Z, (ifeq3 (accept_city A cityb) true (accept_population A muslim n1) true) =? true.
Axiom a2_12_3 : forall A : Z, (ifeq3 (accept_city A cityb) true (accept_population A native n0) true) =? true.
Axiom a2_12_4 : forall A : Z, (ifeq3 (accept_city A cityb) true (accept_population A other n1) true) =? true.
Axiom a2_12_5 : forall A : Z, (ifeq3 (accept_population A other n1) true (ifeq3 (accept_population A native n0) true (ifeq3 (accept_population A muslim n1) true (ifeq3 (accept_population A atheist n78) true (ifeq3 (accept_population A christian n20) true (accept_city A cityb) true) true) true) true) true) =? true.
Axiom a2_11 : forall A : Z, (ifeq3 (accept_city A townb) true (accept_population A christian n20) true) =? true.
Axiom a2_11_1 : forall A : Z, (ifeq3 (accept_city A townb) true (accept_population A atheist n70) true) =? true.
Axiom a2_11_2 : forall A : Z, (ifeq3 (accept_city A townb) true (accept_population A muslim n8) true) =? true.
Axiom a2_11_3 : forall A : Z, (ifeq3 (accept_city A townb) true (accept_population A native n0) true) =? true.
Axiom a2_11_4 : forall A : Z, (ifeq3 (accept_city A townb) true (accept_population A other n2) true) =? true.
Axiom a2_11_5 : forall A : Z, (ifeq3 (accept_population A other n2) true (ifeq3 (accept_population A native n0) true (ifeq3 (accept_population A muslim n8) true (ifeq3 (accept_population A atheist n70) true (ifeq3 (accept_population A christian n20) true (accept_city A townb) true) true) true) true) true) =? true.
Axiom a2_10 : forall A : Z, (ifeq3 (accept_city A citya) true (accept_population A christian n25) true) =? true.
Axiom a2_10_1 : forall A : Z, (ifeq3 (accept_city A citya) true (accept_population A atheist n75) true) =? true.
Axiom a2_10_2 : forall A : Z, (ifeq3 (accept_city A citya) true (accept_population A muslim n0) true) =? true.
Axiom a2_10_3 : forall A : Z, (ifeq3 (accept_city A citya) true (accept_population A native n0) true) =? true.
Axiom a2_10_4 : forall A : Z, (ifeq3 (accept_city A citya) true (accept_population A other n0) true) =? true.
Axiom a2_10_5 : forall A : Z, (ifeq3 (accept_population A other n0) true (ifeq3 (accept_population A native n0) true (ifeq3 (accept_population A muslim n0) true (ifeq3 (accept_population A atheist n75) true (ifeq3 (accept_population A christian n25) true (accept_city A citya) true) true) true) true) true) =? true.
Axiom a2_9 : forall A : Z, (ifeq3 (accept_city A towna) true (accept_population A christian n24) true) =? true.
Axiom a2_9_1 : forall A : Z, (ifeq3 (accept_city A towna) true (accept_population A atheist n75) true) =? true.
Axiom a2_9_2 : forall A : Z, (ifeq3 (accept_city A towna) true (accept_population A muslim n1) true) =? true.
Axiom a2_9_3 : forall A : Z, (ifeq3 (accept_city A towna) true (accept_population A native n0) true) =? true.
Axiom a2_9_4 : forall A : Z, (ifeq3 (accept_city A towna) true (accept_population A other n0) true) =? true.
Axiom a2_9_5 : forall A : Z, (ifeq3 (accept_population A other n0) true (ifeq3 (accept_population A native n0) true (ifeq3 (accept_population A muslim n1) true (ifeq3 (accept_population A atheist n75) true (ifeq3 (accept_population A christian n24) true (accept_city A towna) true) true) true) true) true) =? true.
Axiom a2_8 : forall A : Z, (ifeq3 (accept_city A sunsetpoint) true (accept_population A christian n0) true) =? true.
Axiom a2_8_1 : forall A : Z, (ifeq3 (accept_city A sunsetpoint) true (accept_population A atheist n0) true) =? true.
Axiom a2_8_2 : forall A : Z, (ifeq3 (accept_city A sunsetpoint) true (accept_population A muslim n0) true) =? true.
Axiom a2_8_3 : forall A : Z, (ifeq3 (accept_city A sunsetpoint) true (accept_population A native n100) true) =? true.
Axiom a2_8_4 : forall A : Z, (ifeq3 (accept_city A sunsetpoint) true (accept_population A other n0) true) =? true.
Axiom a2_8_5 : forall A : Z, (ifeq3 (accept_population A other n0) true (ifeq3 (accept_population A native n100) true (ifeq3 (accept_population A muslim n0) true (ifeq3 (accept_population A atheist n0) true (ifeq3 (accept_population A christian n0) true (accept_city A sunsetpoint) true) true) true) true) true) =? true.
Axiom a2_7 : forall A : Z, (ifeq3 (accept_city A coastvillage) true (accept_population A christian n3) true) =? true.
Axiom a2_7_1 : forall A : Z, (ifeq3 (accept_city A coastvillage) true (accept_population A atheist n12) true) =? true.
Axiom a2_7_2 : forall A : Z, (ifeq3 (accept_city A coastvillage) true (accept_population A muslim n0) true) =? true.
Axiom a2_7_3 : forall A : Z, (ifeq3 (accept_city A coastvillage) true (accept_population A native n85) true) =? true.
Axiom a2_7_4 : forall A : Z, (ifeq3 (accept_city A coastvillage) true (accept_population A other n0) true) =? true.
Axiom a2_7_5 : forall A : Z, (ifeq3 (accept_population A other n0) true (ifeq3 (accept_population A native n85) true (ifeq3 (accept_population A muslim n0) true (ifeq3 (accept_population A atheist n12) true (ifeq3 (accept_population A christian n3) true (accept_city A coastvillage) true) true) true) true) true) =? true.
Axiom a2_6 : forall A : Z, (ifeq3 (accept_city A northport) true (accept_population A christian n13) true) =? true.
Axiom a2_6_1 : forall A : Z, (ifeq3 (accept_city A northport) true (accept_population A atheist n70) true) =? true.
Axiom a2_6_2 : forall A : Z, (ifeq3 (accept_city A northport) true (accept_population A muslim n0) true) =? true.
Axiom a2_6_3 : forall A : Z, (ifeq3 (accept_city A northport) true (accept_population A native n15) true) =? true.
Axiom a2_6_4 : forall A : Z, (ifeq3 (accept_city A northport) true (accept_population A other n2) true) =? true.
Axiom a2_6_5 : forall A : Z, (ifeq3 (accept_population A other n2) true (ifeq3 (accept_population A native n15) true (ifeq3 (accept_population A muslim n0) true (ifeq3 (accept_population A atheist n70) true (ifeq3 (accept_population A christian n13) true (accept_city A northport) true) true) true) true) true) =? true.
Axiom a2_5 : forall A : Z, (ifeq3 (accept_city A stjosephburgh) true (accept_population A christian n16) true) =? true.
Axiom a2_5_1 : forall A : Z, (ifeq3 (accept_city A stjosephburgh) true (accept_population A atheist n68) true) =? true.
Axiom a2_5_2 : forall A : Z, (ifeq3 (accept_city A stjosephburgh) true (accept_population A muslim n1) true) =? true.
Axiom a2_5_3 : forall A : Z, (ifeq3 (accept_city A stjosephburgh) true (accept_population A native n11) true) =? true.
Axiom a2_5_4 : forall A : Z, (ifeq3 (accept_city A stjosephburgh) true (accept_population A other n4) true) =? true.
Axiom a2_5_5 : forall A : Z, (ifeq3 (accept_population A other n4) true (ifeq3 (accept_population A native n11) true (ifeq3 (accept_population A muslim n1) true (ifeq3 (accept_population A atheist n68) true (ifeq3 (accept_population A christian n16) true (accept_city A stjosephburgh) true) true) true) true) true) =? true.
Axiom a2_4 : forall A : Z, (ifeq3 (accept_city A centrallakecity) true (accept_population A christian n15) true) =? true.
Axiom a2_4_1 : forall A : Z, (ifeq3 (accept_city A centrallakecity) true (accept_population A atheist n70) true) =? true.
Axiom a2_4_2 : forall A : Z, (ifeq3 (accept_city A centrallakecity) true (accept_population A muslim n1) true) =? true.
Axiom a2_4_3 : forall A : Z, (ifeq3 (accept_city A centrallakecity) true (accept_population A native n10) true) =? true.
Axiom a2_4_4 : forall A : Z, (ifeq3 (accept_city A centrallakecity) true (accept_population A other n4) true) =? true.
Axiom a2_4_5 : forall A : Z, (ifeq3 (accept_population A other n4) true (ifeq3 (accept_population A native n10) true (ifeq3 (accept_population A muslim n1) true (ifeq3 (accept_population A atheist n70) true (ifeq3 (accept_population A christian n15) true (accept_city A centrallakecity) true) true) true) true) true) =? true.
Axiom a2_3 : forall A : Z, (ifeq3 (accept_city A sunnysideport) true (accept_population A christian n8) true) =? true.
Axiom a2_3_1 : forall A : Z, (ifeq3 (accept_city A sunnysideport) true (accept_population A atheist n30) true) =? true.
Axiom a2_3_2 : forall A : Z, (ifeq3 (accept_city A sunnysideport) true (accept_population A muslim n60) true) =? true.
Axiom a2_3_3 : forall A : Z, (ifeq3 (accept_city A sunnysideport) true (accept_population A native n1) true) =? true.
Axiom a2_3_4 : forall A : Z, (ifeq3 (accept_city A sunnysideport) true (accept_population A other n1) true) =? true.
Axiom a2_3_5 : forall A : Z, (ifeq3 (accept_population A other n1) true (ifeq3 (accept_population A native n1) true (ifeq3 (accept_population A muslim n60) true (ifeq3 (accept_population A atheist n30) true (ifeq3 (accept_population A christian n8) true (accept_city A sunnysideport) true) true) true) true) true) =? true.
Axiom a2_2 : forall A : Z, (ifeq3 (accept_city A centraltown) true (accept_population A christian n23) true) =? true.
Axiom a2_2_1 : forall A : Z, (ifeq3 (accept_city A centraltown) true (accept_population A atheist n54) true) =? true.
Axiom a2_2_2 : forall A : Z, (ifeq3 (accept_city A centraltown) true (accept_population A muslim n3) true) =? true.
Axiom a2_2_3 : forall A : Z, (ifeq3 (accept_city A centraltown) true (accept_population A native n1) true) =? true.
Axiom a2_2_4 : forall A : Z, (ifeq3 (accept_city A centraltown) true (accept_population A other n9) true) =? true.
Axiom a2_2_5 : forall A : Z, (ifeq3 (accept_population A other n9) true (ifeq3 (accept_population A native n1) true (ifeq3 (accept_population A muslim n3) true (ifeq3 (accept_population A atheist n54) true (ifeq3 (accept_population A christian n23) true (accept_city A centraltown) true) true) true) true) true) =? true.
Axiom a2_1 : forall A : Z, (ifeq3 (accept_city A suffertown) true (accept_population A christian n20) true) =? true.
Axiom a2_1_1 : forall A : Z, (ifeq3 (accept_city A suffertown) true (accept_population A atheist n65) true) =? true.
Axiom a2_1_2 : forall A : Z, (ifeq3 (accept_city A suffertown) true (accept_population A muslim n7) true) =? true.
Axiom a2_1_3 : forall A : Z, (ifeq3 (accept_city A suffertown) true (accept_population A native n4) true) =? true.
Axiom a2_1_4 : forall A : Z, (ifeq3 (accept_city A suffertown) true (accept_population A other n4) true) =? true.
Axiom a2_1_5 : forall A : Z, (ifeq3 (accept_population A other n4) true (ifeq3 (accept_population A native n4) true (ifeq3 (accept_population A muslim n7) true (ifeq3 (accept_population A atheist n65) true (ifeq3 (accept_population A christian n20) true (accept_city A suffertown) true) true) true) true) true) =? true.
Axiom a1_7 : forall A N : Z, (ifeq3 (min_number_of_proposed_agents A N) true (accept_number A N) true) =? true.
Axiom a1_5 : forall A C L : Z, (ifeq3 (any_agent_in_all_proposed_teams A L C) true (accept_leader A L) true) =? true.
Axiom a1_4 : forall A C L : Z, (ifeq3 (the_agent_in_all_proposed_teams A L C) true (accept_city A C) true) =? true.
Axiom a1_4_1 : forall A C L : Z, (ifeq3 (the_agent_in_all_proposed_teams A L C) true (accept_leader A L) true) =? true.
Axiom a1_3 : forall A M N P : Z, (ifeq3 (accept_population A P N) true (ifeq3 (less M N) true (accept_population A P M) true) true) =? true.
Axiom a1_2 : forall A M N : Z, (ifeq3 (less M N) true (ifeq3 (accept_number A N) true (accept_number A M) true) true) =? true.
Axiom a1_1 : forall A C L N : Z, (ifeq3 (accept_team A L C N) true (accept_city A C) true) =? true.
Axiom a1_1_1 : forall A C L N : Z, (ifeq3 (accept_team A L C N) true (accept_leader A L) true) =? true.
Axiom a1_1_2 : forall A C L N : Z, (ifeq3 (accept_team A L C N) true (accept_number A N) true) =? true.
Axiom a1_1_3 : forall A C L N : Z, (ifeq3 (accept_number A N) true (ifeq3 (accept_leader A L) true (ifeq3 (accept_city A C) true (accept_team A L C N) true) true) true) =? true.
Axiom ifeq_axiom_002 : forall A B C : Z, (ifeq A A B C) =? B.
Axiom ifeq_axiom_001 : forall A B C : Z, (ifeq2 A A B C) =? B.
Axiom ifeq_axiom : forall A B C : Z, (ifeq3 A A B C) =? B.

Add_lemmas deduced_366 deduced_82 deduced_62 deduced_58 deduced_13 event_246 event_219 event_218 event_217 event_216 event_213 event_212 event_187 event_186 event_185 event_184 event_182 event_181 event_180 event_179 event_178 event_177 event_176 event_175 event_174 event_144 event_143 event_119 event_118 event_117 event_116 event_115 event_72 event_71 event_40 event_36 event_35 event_34 event_33 event_32 event_31 event_30 event_29 event_10 event_9 a1_6 deduced_367 deduced_365 deduced_364 deduced_363 deduced_362 deduced_361 deduced_360 deduced_359 deduced_358 deduced_357 deduced_356 deduced_355 deduced_354 deduced_353 deduced_352 deduced_351 deduced_350 deduced_349 deduced_348 deduced_347 deduced_346 deduced_345 deduced_344 deduced_343 deduced_342 deduced_341 deduced_340 deduced_339 deduced_338 deduced_337 deduced_336 deduced_335 deduced_334 deduced_333 deduced_332 deduced_331 deduced_330 deduced_329 deduced_328 deduced_327 deduced_326 deduced_325 deduced_324 deduced_323 deduced_322 deduced_321 deduced_320 deduced_319 deduced_318 deduced_317 deduced_316 deduced_315 deduced_314 deduced_313 deduced_312 deduced_311 deduced_310 deduced_309 deduced_308 deduced_307 deduced_306 deduced_305 deduced_304 deduced_303 deduced_302 deduced_301 deduced_300 deduced_299 deduced_298 deduced_297 deduced_296 deduced_295 deduced_294 deduced_293 deduced_292 deduced_291 deduced_290 deduced_289 deduced_288 deduced_287 deduced_286 deduced_285 deduced_284 deduced_283 deduced_282 deduced_281 deduced_280 deduced_279 deduced_278 deduced_277 deduced_276 deduced_275 deduced_274 deduced_273 deduced_272 deduced_271 deduced_270 deduced_269 deduced_268 deduced_267 deduced_266 deduced_265 deduced_264 deduced_263 deduced_262 deduced_261 deduced_260 deduced_259 deduced_258 deduced_257 deduced_256 deduced_255 deduced_254 deduced_253 deduced_252 deduced_251 deduced_250 deduced_249 deduced_248 deduced_247 deduced_246 deduced_245 deduced_244 deduced_243 deduced_242 deduced_241 deduced_240 deduced_239 deduced_238 deduced_237 deduced_236 deduced_235 deduced_234 deduced_233 deduced_232 deduced_231 deduced_230 deduced_229 deduced_228 deduced_227 deduced_226 deduced_225 deduced_224 deduced_223 deduced_222 deduced_221 deduced_220 deduced_219 deduced_218 deduced_217 deduced_216 deduced_215 deduced_214 deduced_213 deduced_212 deduced_211 deduced_210 deduced_209 deduced_208 deduced_207 deduced_206 deduced_205 deduced_204 deduced_203 deduced_202 deduced_201 deduced_200 deduced_199 deduced_198 deduced_197 deduced_196 deduced_195 deduced_194 deduced_193 deduced_192 deduced_191 deduced_190 deduced_189 deduced_188 deduced_187 deduced_186 deduced_185 deduced_184 deduced_183 deduced_182 deduced_181 deduced_180 deduced_179 deduced_178 deduced_177 deduced_176 deduced_175 deduced_174 deduced_173 deduced_172 deduced_171 deduced_170 deduced_169 deduced_168 deduced_167 deduced_166 deduced_165 deduced_164 deduced_163 deduced_162 deduced_161 deduced_160 deduced_159 deduced_158 deduced_157 deduced_156 deduced_155 deduced_154 deduced_153 deduced_152 deduced_151 deduced_150 deduced_149 deduced_148 deduced_147 deduced_146 deduced_145 deduced_144 deduced_143 deduced_142 deduced_141 deduced_140 deduced_139 deduced_138 deduced_137 deduced_136 deduced_135 deduced_134 deduced_133 deduced_132 deduced_131 deduced_130 deduced_129 deduced_128 deduced_127 deduced_126 deduced_125 deduced_124 deduced_123 deduced_122 deduced_121 deduced_120 deduced_119 deduced_118 deduced_117 deduced_116 deduced_115 deduced_114 deduced_113 deduced_112 deduced_111 deduced_110 deduced_109 deduced_108 deduced_107 deduced_106 deduced_105 deduced_104 deduced_103 deduced_102 deduced_101 deduced_100 deduced_99 deduced_98 deduced_97 deduced_96 deduced_95 deduced_94 deduced_93 deduced_92 deduced_91 deduced_90 deduced_89 deduced_88 deduced_87 deduced_86 deduced_85 deduced_84 deduced_83 deduced_81 deduced_80 deduced_79 deduced_78 deduced_77 deduced_76 deduced_75 deduced_74 deduced_73 deduced_72 deduced_71 deduced_70 deduced_69 deduced_68 deduced_67 deduced_66 deduced_65 deduced_64 deduced_63 deduced_61 deduced_60 deduced_59 deduced_57 deduced_56 deduced_55 deduced_54 deduced_53 deduced_52 deduced_51 deduced_50 deduced_49 deduced_48 deduced_47 deduced_46 deduced_45 deduced_44 deduced_43 deduced_42 deduced_41 deduced_40 deduced_39 deduced_38 deduced_37 deduced_36 deduced_35 deduced_34 deduced_33 deduced_32 deduced_31 deduced_30 deduced_29 deduced_28 deduced_27 deduced_26 deduced_25 deduced_24 deduced_23 deduced_22 deduced_21 deduced_20 deduced_19 deduced_18 deduced_17 deduced_16 deduced_15 deduced_14 deduced_12 deduced_11 deduced_10 deduced_9 deduced_8 deduced_7 deduced_6 deduced_5 deduced_4 deduced_3 deduced_2 deduced_1 event_249 event_248 event_247 event_245 event_244 event_243 event_242 event_241 event_240 event_239 event_238 event_237 event_236 event_235 event_234 event_233 event_232 event_231 event_230 event_229 event_228 event_227 event_226 event_225 event_224 event_223 event_222 event_221 event_220 event_215 event_214 event_211 event_210 event_209 event_208 event_207 event_206 event_205 event_204 event_203 event_202 event_201 event_200 event_199 event_198 event_197 event_196 event_195 event_194 event_193 event_192 event_191 event_190 event_189 event_188 event_183 event_173 event_172 event_171 event_170 event_169 event_168 event_167 event_166 event_165 event_164 event_163 event_162 event_161 event_160 event_159 event_158 event_157 event_156 event_155 event_154 event_153 event_152 event_151 event_150 event_149 event_148 event_147 event_146 event_145 event_142 event_141 event_140 event_139 event_138 event_137 event_136 event_135 event_134 event_133 event_132 event_131 event_130 event_129 event_128 event_127 event_126 event_125 event_124 event_123 event_122 event_121 event_120 event_114 event_113 event_112 event_111 event_110 event_109 event_108 event_107 event_106 event_105 event_104 event_103 event_102 event_101 event_100 event_99 event_98 event_97 event_96 event_95 event_94 event_93 event_92 event_91 event_90 event_89 event_88 event_87 event_86 event_85 event_84 event_83 event_82 event_81 event_80 event_79 event_78 event_77 event_76 event_75 event_74 event_73 event_70 event_69 event_68 event_67 event_66 event_65 event_64 event_63 event_62 event_61 event_60 event_59 event_58 event_57 event_56 event_55 event_54 event_53 event_52 event_51 event_50 event_49 event_48 event_47 event_46 event_45 event_44 event_43 event_42 event_41 event_39 event_38 event_37 event_28 event_27 event_26 event_25 event_24 event_23 event_22 event_21 event_20 event_19 event_18 event_17 event_16 event_15 event_14 event_13 event_12 event_11 event_8 event_7 event_6 event_5 event_4 event_3 event_2 event_1 a2_13 a2_13_1 a2_13_2 a2_13_3 a2_13_4 a2_13_5 a2_12 a2_12_1 a2_12_2 a2_12_3 a2_12_4 a2_12_5 a2_11 a2_11_1 a2_11_2 a2_11_3 a2_11_4 a2_11_5 a2_10 a2_10_1 a2_10_2 a2_10_3 a2_10_4 a2_10_5 a2_9 a2_9_1 a2_9_2 a2_9_3 a2_9_4 a2_9_5 a2_8 a2_8_1 a2_8_2 a2_8_3 a2_8_4 a2_8_5 a2_7 a2_7_1 a2_7_2 a2_7_3 a2_7_4 a2_7_5 a2_6 a2_6_1 a2_6_2 a2_6_3 a2_6_4 a2_6_5 a2_5 a2_5_1 a2_5_2 a2_5_3 a2_5_4 a2_5_5 a2_4 a2_4_1 a2_4_2 a2_4_3 a2_4_4 a2_4_5 a2_3 a2_3_1 a2_3_2 a2_3_3 a2_3_4 a2_3_5 a2_2 a2_2_1 a2_2_2 a2_2_3 a2_2_4 a2_2_5 a2_1 a2_1_1 a2_1_2 a2_1_3 a2_1_4 a2_1_5 a1_7 a1_5 a1_4 a1_4_1 a1_3 a1_2 a1_1 a1_1_1 a1_1_2 a1_1_3 ifeq_axiom_002 ifeq_axiom_001 ifeq_axiom.

(* Zoal *)
Theorem check : a =? b.
Proof.
  smt.
Qed.

Check check.

