import Sq17Lean.OrbitCensus.Chunk0304
import Sq17Lean.OrbitCensus.Chunk0305
import Sq17Lean.OrbitCensus.Chunk0306
import Sq17Lean.OrbitCensus.Chunk0307
import Sq17Lean.OrbitCensus.Chunk0308
import Sq17Lean.OrbitCensus.Chunk0309
import Sq17Lean.OrbitCensus.Chunk0310
import Sq17Lean.OrbitCensus.Chunk0311
import Sq17Lean.OrbitCensus.Chunk0312
import Sq17Lean.OrbitCensus.Chunk0313
import Sq17Lean.OrbitCensus.Chunk0314
import Sq17Lean.OrbitCensus.Chunk0315
import Sq17Lean.OrbitCensus.Chunk0316
import Sq17Lean.OrbitCensus.Chunk0317
import Sq17Lean.OrbitCensus.Chunk0318
import Sq17Lean.OrbitCensus.Chunk0319

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_019_0 : List Row := rows0304 ++ rows0305
theorem goodCompose00_019_0 : GoodBlock representatives rowsCompose00_019_0 11011206 11108433 2048 :=
  good0304.append good0305 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_1 : List Row := rows0306 ++ rows0307
theorem goodCompose00_019_1 : GoodBlock representatives rowsCompose00_019_1 11108448 11537475 2048 :=
  good0306.append good0307 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_2 : List Row := rowsCompose00_019_0 ++ rowsCompose00_019_1
theorem goodCompose00_019_2 : GoodBlock representatives rowsCompose00_019_2 11011206 11537475 4096 :=
  goodCompose00_019_0.append goodCompose00_019_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_3 : List Row := rows0308 ++ rows0309
theorem goodCompose00_019_3 : GoodBlock representatives rowsCompose00_019_3 11537476 11666481 2048 :=
  good0308.append good0309 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_4 : List Row := rows0310 ++ rows0311
theorem goodCompose00_019_4 : GoodBlock representatives rowsCompose00_019_4 11666497 12189714 2048 :=
  good0310.append good0311 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_5 : List Row := rowsCompose00_019_3 ++ rowsCompose00_019_4
theorem goodCompose00_019_5 : GoodBlock representatives rowsCompose00_019_5 11537476 12189714 4096 :=
  goodCompose00_019_3.append goodCompose00_019_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_6 : List Row := rowsCompose00_019_2 ++ rowsCompose00_019_5
theorem goodCompose00_019_6 : GoodBlock representatives rowsCompose00_019_6 11011206 12189714 8192 :=
  goodCompose00_019_2.append goodCompose00_019_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_7 : List Row := rows0312 ++ rows0313
theorem goodCompose00_019_7 : GoodBlock representatives rowsCompose00_019_7 12189714 12594434 2048 :=
  good0312.append good0313 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_8 : List Row := rows0314 ++ rows0315
theorem goodCompose00_019_8 : GoodBlock representatives rowsCompose00_019_8 12594434 12624419 2048 :=
  good0314.append good0315 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_9 : List Row := rowsCompose00_019_7 ++ rowsCompose00_019_8
theorem goodCompose00_019_9 : GoodBlock representatives rowsCompose00_019_9 12189714 12624419 4096 :=
  goodCompose00_019_7.append goodCompose00_019_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_10 : List Row := rows0316 ++ rows0317
theorem goodCompose00_019_10 : GoodBlock representatives rowsCompose00_019_10 12624420 12682261 2048 :=
  good0316.append good0317 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_11 : List Row := rows0318 ++ rows0319
theorem goodCompose00_019_11 : GoodBlock representatives rowsCompose00_019_11 12682264 12759057 2048 :=
  good0318.append good0319 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_12 : List Row := rowsCompose00_019_10 ++ rowsCompose00_019_11
theorem goodCompose00_019_12 : GoodBlock representatives rowsCompose00_019_12 12624420 12759057 4096 :=
  goodCompose00_019_10.append goodCompose00_019_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_13 : List Row := rowsCompose00_019_9 ++ rowsCompose00_019_12
theorem goodCompose00_019_13 : GoodBlock representatives rowsCompose00_019_13 12189714 12759057 8192 :=
  goodCompose00_019_9.append goodCompose00_019_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_019_14 : List Row := rowsCompose00_019_6 ++ rowsCompose00_019_13
theorem goodCompose00_019_14 : GoodBlock representatives rowsCompose00_019_14 11011206 12759057 16384 :=
  goodCompose00_019_6.append goodCompose00_019_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_019_14
