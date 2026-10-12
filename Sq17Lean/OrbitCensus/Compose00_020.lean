import Sq17Lean.OrbitCensus.Chunk0320
import Sq17Lean.OrbitCensus.Chunk0321
import Sq17Lean.OrbitCensus.Chunk0322
import Sq17Lean.OrbitCensus.Chunk0323
import Sq17Lean.OrbitCensus.Chunk0324
import Sq17Lean.OrbitCensus.Chunk0325
import Sq17Lean.OrbitCensus.Chunk0326
import Sq17Lean.OrbitCensus.Chunk0327
import Sq17Lean.OrbitCensus.Chunk0328
import Sq17Lean.OrbitCensus.Chunk0329
import Sq17Lean.OrbitCensus.Chunk0330
import Sq17Lean.OrbitCensus.Chunk0331
import Sq17Lean.OrbitCensus.Chunk0332
import Sq17Lean.OrbitCensus.Chunk0333
import Sq17Lean.OrbitCensus.Chunk0334
import Sq17Lean.OrbitCensus.Chunk0335

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_020_0 : List Row := rows0320 ++ rows0321
theorem goodCompose00_020_0 : GoodBlock representatives rowsCompose00_020_0 12759072 12877899 2048 :=
  good0320.append good0321 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_1 : List Row := rows0322 ++ rows0323
theorem goodCompose00_020_1 : GoodBlock representatives rowsCompose00_020_1 12877900 13109413 2048 :=
  good0322.append good0323 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_2 : List Row := rowsCompose00_020_0 ++ rowsCompose00_020_1
theorem goodCompose00_020_2 : GoodBlock representatives rowsCompose00_020_2 12759072 13109413 4096 :=
  goodCompose00_020_0.append goodCompose00_020_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_3 : List Row := rows0324 ++ rows0325
theorem goodCompose00_020_3 : GoodBlock representatives rowsCompose00_020_3 13109416 13238434 2048 :=
  good0324.append good0325 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_4 : List Row := rows0326 ++ rows0327
theorem goodCompose00_020_4 : GoodBlock representatives rowsCompose00_020_4 13238434 13636169 2048 :=
  good0326.append good0327 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_5 : List Row := rowsCompose00_020_3 ++ rowsCompose00_020_4
theorem goodCompose00_020_5 : GoodBlock representatives rowsCompose00_020_5 13109416 13636169 4096 :=
  goodCompose00_020_3.append goodCompose00_020_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_6 : List Row := rowsCompose00_020_2 ++ rowsCompose00_020_5
theorem goodCompose00_020_6 : GoodBlock representatives rowsCompose00_020_6 12759072 13636169 8192 :=
  goodCompose00_020_2.append goodCompose00_020_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_7 : List Row := rows0328 ++ rows0329
theorem goodCompose00_020_7 : GoodBlock representatives rowsCompose00_020_7 13636176 13767682 2048 :=
  good0328.append good0329 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_8 : List Row := rows0330 ++ rows0331
theorem goodCompose00_020_8 : GoodBlock representatives rowsCompose00_020_8 13767682 14417926 2048 :=
  good0330.append good0331 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_9 : List Row := rowsCompose00_020_7 ++ rowsCompose00_020_8
theorem goodCompose00_020_9 : GoodBlock representatives rowsCompose00_020_9 13636176 14417926 4096 :=
  goodCompose00_020_7.append goodCompose00_020_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_10 : List Row := rows0332 ++ rows0333
theorem goodCompose00_020_10 : GoodBlock representatives rowsCompose00_020_10 14417926 14745953 2048 :=
  good0332.append good0333 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_11 : List Row := rows0334 ++ rows0335
theorem goodCompose00_020_11 : GoodBlock representatives rowsCompose00_020_11 14745985 15204645 2048 :=
  good0334.append good0335 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_12 : List Row := rowsCompose00_020_10 ++ rowsCompose00_020_11
theorem goodCompose00_020_12 : GoodBlock representatives rowsCompose00_020_12 14417926 15204645 4096 :=
  goodCompose00_020_10.append goodCompose00_020_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_13 : List Row := rowsCompose00_020_9 ++ rowsCompose00_020_12
theorem goodCompose00_020_13 : GoodBlock representatives rowsCompose00_020_13 13636176 15204645 8192 :=
  goodCompose00_020_9.append goodCompose00_020_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_020_14 : List Row := rowsCompose00_020_6 ++ rowsCompose00_020_13
theorem goodCompose00_020_14 : GoodBlock representatives rowsCompose00_020_14 12759072 15204645 16384 :=
  goodCompose00_020_6.append goodCompose00_020_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_020_14
