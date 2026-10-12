import Sq17Lean.OrbitCensus.Chunk0272
import Sq17Lean.OrbitCensus.Chunk0273
import Sq17Lean.OrbitCensus.Chunk0274
import Sq17Lean.OrbitCensus.Chunk0275
import Sq17Lean.OrbitCensus.Chunk0276
import Sq17Lean.OrbitCensus.Chunk0277
import Sq17Lean.OrbitCensus.Chunk0278
import Sq17Lean.OrbitCensus.Chunk0279
import Sq17Lean.OrbitCensus.Chunk0280
import Sq17Lean.OrbitCensus.Chunk0281
import Sq17Lean.OrbitCensus.Chunk0282
import Sq17Lean.OrbitCensus.Chunk0283
import Sq17Lean.OrbitCensus.Chunk0284
import Sq17Lean.OrbitCensus.Chunk0285
import Sq17Lean.OrbitCensus.Chunk0286
import Sq17Lean.OrbitCensus.Chunk0287

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_017_0 : List Row := rows0272 ++ rows0273
theorem goodCompose00_017_0 : GoodBlock representatives rowsCompose00_017_0 9044145 9115657 2048 :=
  good0272.append good0273 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_1 : List Row := rows0274 ++ rows0275
theorem goodCompose00_017_1 : GoodBlock representatives rowsCompose00_017_1 9115664 9224707 2048 :=
  good0274.append good0275 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_2 : List Row := rowsCompose00_017_0 ++ rowsCompose00_017_1
theorem goodCompose00_017_2 : GoodBlock representatives rowsCompose00_017_2 9044145 9224707 4096 :=
  goodCompose00_017_0.append goodCompose00_017_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_3 : List Row := rows0276 ++ rows0277
theorem goodCompose00_017_3 : GoodBlock representatives rowsCompose00_017_3 9224708 9440673 2048 :=
  good0276.append good0277 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_4 : List Row := rows0278 ++ rows0279
theorem goodCompose00_017_4 : GoodBlock representatives rowsCompose00_017_4 9440704 9462278 2048 :=
  good0278.append good0279 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_5 : List Row := rowsCompose00_017_3 ++ rowsCompose00_017_4
theorem goodCompose00_017_5 : GoodBlock representatives rowsCompose00_017_5 9224708 9462278 4096 :=
  goodCompose00_017_3.append goodCompose00_017_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_6 : List Row := rowsCompose00_017_2 ++ rowsCompose00_017_5
theorem goodCompose00_017_6 : GoodBlock representatives rowsCompose00_017_6 9044145 9462278 8192 :=
  goodCompose00_017_2.append goodCompose00_017_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_7 : List Row := rows0280 ++ rows0281
theorem goodCompose00_017_7 : GoodBlock representatives rowsCompose00_017_7 9462278 9506065 2048 :=
  good0280.append good0281 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_8 : List Row := rows0282 ++ rows0283
theorem goodCompose00_017_8 : GoodBlock representatives rowsCompose00_017_8 9506080 9575457 2048 :=
  good0282.append good0283 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_9 : List Row := rowsCompose00_017_7 ++ rowsCompose00_017_8
theorem goodCompose00_017_9 : GoodBlock representatives rowsCompose00_017_9 9462278 9575457 4096 :=
  goodCompose00_017_7.append goodCompose00_017_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_10 : List Row := rows0284 ++ rows0285
theorem goodCompose00_017_10 : GoodBlock representatives rowsCompose00_017_10 9575488 9701545 2048 :=
  good0284.append good0285 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_11 : List Row := rows0286 ++ rows0287
theorem goodCompose00_017_11 : GoodBlock representatives rowsCompose00_017_11 9701552 9830563 2048 :=
  good0286.append good0287 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_12 : List Row := rowsCompose00_017_10 ++ rowsCompose00_017_11
theorem goodCompose00_017_12 : GoodBlock representatives rowsCompose00_017_12 9575488 9830563 4096 :=
  goodCompose00_017_10.append goodCompose00_017_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_13 : List Row := rowsCompose00_017_9 ++ rowsCompose00_017_12
theorem goodCompose00_017_13 : GoodBlock representatives rowsCompose00_017_13 9462278 9830563 8192 :=
  goodCompose00_017_9.append goodCompose00_017_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_017_14 : List Row := rowsCompose00_017_6 ++ rowsCompose00_017_13
theorem goodCompose00_017_14 : GoodBlock representatives rowsCompose00_017_14 9044145 9830563 16384 :=
  goodCompose00_017_6.append goodCompose00_017_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_017_14
