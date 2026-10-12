import Sq17Lean.OrbitCensus.Chunk0288
import Sq17Lean.OrbitCensus.Chunk0289
import Sq17Lean.OrbitCensus.Chunk0290
import Sq17Lean.OrbitCensus.Chunk0291
import Sq17Lean.OrbitCensus.Chunk0292
import Sq17Lean.OrbitCensus.Chunk0293
import Sq17Lean.OrbitCensus.Chunk0294
import Sq17Lean.OrbitCensus.Chunk0295
import Sq17Lean.OrbitCensus.Chunk0296
import Sq17Lean.OrbitCensus.Chunk0297
import Sq17Lean.OrbitCensus.Chunk0298
import Sq17Lean.OrbitCensus.Chunk0299
import Sq17Lean.OrbitCensus.Chunk0300
import Sq17Lean.OrbitCensus.Chunk0301
import Sq17Lean.OrbitCensus.Chunk0302
import Sq17Lean.OrbitCensus.Chunk0303

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_018_0 : List Row := rows0288 ++ rows0289
theorem goodCompose00_018_0 : GoodBlock representatives rowsCompose00_018_0 9830564 9994417 2048 :=
  good0288.append good0289 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_1 : List Row := rows0290 ++ rows0291
theorem goodCompose00_018_1 : GoodBlock representatives rowsCompose00_018_1 9994433 10240517 2048 :=
  good0290.append good0291 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_2 : List Row := rowsCompose00_018_0 ++ rowsCompose00_018_1
theorem goodCompose00_018_2 : GoodBlock representatives rowsCompose00_018_2 9830564 10240517 4096 :=
  goodCompose00_018_0.append goodCompose00_018_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_3 : List Row := rows0292 ++ rows0293
theorem goodCompose00_018_3 : GoodBlock representatives rowsCompose00_018_3 10240520 10496051 2048 :=
  good0292.append good0293 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_4 : List Row := rows0294 ++ rows0295
theorem goodCompose00_018_4 : GoodBlock representatives rowsCompose00_018_4 10496052 10524753 2048 :=
  good0294.append good0295 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_5 : List Row := rowsCompose00_018_3 ++ rowsCompose00_018_4
theorem goodCompose00_018_5 : GoodBlock representatives rowsCompose00_018_5 10240520 10524753 4096 :=
  goodCompose00_018_3.append goodCompose00_018_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_6 : List Row := rowsCompose00_018_2 ++ rowsCompose00_018_5
theorem goodCompose00_018_6 : GoodBlock representatives rowsCompose00_018_6 9830564 10524753 8192 :=
  goodCompose00_018_2.append goodCompose00_018_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_7 : List Row := rows0296 ++ rows0297
theorem goodCompose00_018_7 : GoodBlock representatives rowsCompose00_018_7 10524768 10580481 2048 :=
  good0296.append good0297 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_8 : List Row := rows0298 ++ rows0299
theorem goodCompose00_018_8 : GoodBlock representatives rowsCompose00_018_8 10580992 10653709 2048 :=
  good0298.append good0299 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_9 : List Row := rowsCompose00_018_7 ++ rowsCompose00_018_8
theorem goodCompose00_018_9 : GoodBlock representatives rowsCompose00_018_9 10524768 10653709 4096 :=
  goodCompose00_018_7.append goodCompose00_018_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_10 : List Row := rows0300 ++ rows0301
theorem goodCompose00_018_10 : GoodBlock representatives rowsCompose00_018_10 10653713 10768899 2048 :=
  good0300.append good0301 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_11 : List Row := rows0302 ++ rows0303
theorem goodCompose00_018_11 : GoodBlock representatives rowsCompose00_018_11 10768900 11011206 2048 :=
  good0302.append good0303 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_12 : List Row := rowsCompose00_018_10 ++ rowsCompose00_018_11
theorem goodCompose00_018_12 : GoodBlock representatives rowsCompose00_018_12 10653713 11011206 4096 :=
  goodCompose00_018_10.append goodCompose00_018_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_13 : List Row := rowsCompose00_018_9 ++ rowsCompose00_018_12
theorem goodCompose00_018_13 : GoodBlock representatives rowsCompose00_018_13 10524768 11011206 8192 :=
  goodCompose00_018_9.append goodCompose00_018_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_018_14 : List Row := rowsCompose00_018_6 ++ rowsCompose00_018_13
theorem goodCompose00_018_14 : GoodBlock representatives rowsCompose00_018_14 9830564 11011206 16384 :=
  goodCompose00_018_6.append goodCompose00_018_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_018_14
