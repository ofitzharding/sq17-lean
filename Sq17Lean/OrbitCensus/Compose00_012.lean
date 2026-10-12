import Sq17Lean.OrbitCensus.Chunk0192
import Sq17Lean.OrbitCensus.Chunk0193
import Sq17Lean.OrbitCensus.Chunk0194
import Sq17Lean.OrbitCensus.Chunk0195
import Sq17Lean.OrbitCensus.Chunk0196
import Sq17Lean.OrbitCensus.Chunk0197
import Sq17Lean.OrbitCensus.Chunk0198
import Sq17Lean.OrbitCensus.Chunk0199
import Sq17Lean.OrbitCensus.Chunk0200
import Sq17Lean.OrbitCensus.Chunk0201
import Sq17Lean.OrbitCensus.Chunk0202
import Sq17Lean.OrbitCensus.Chunk0203
import Sq17Lean.OrbitCensus.Chunk0204
import Sq17Lean.OrbitCensus.Chunk0205
import Sq17Lean.OrbitCensus.Chunk0206
import Sq17Lean.OrbitCensus.Chunk0207

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_012_0 : List Row := rows0192 ++ rows0193
theorem goodCompose00_012_0 : GoodBlock representatives rowsCompose00_012_0 4612240 4723469 2048 :=
  good0192.append good0193 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_1 : List Row := rows0194 ++ rows0195
theorem goodCompose00_012_1 : GoodBlock representatives rowsCompose00_012_1 4723473 4751453 2048 :=
  good0194.append good0195 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_2 : List Row := rowsCompose00_012_0 ++ rowsCompose00_012_1
theorem goodCompose00_012_2 : GoodBlock representatives rowsCompose00_012_2 4612240 4751453 4096 :=
  goodCompose00_012_0.append goodCompose00_012_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_3 : List Row := rows0196 ++ rows0197
theorem goodCompose00_012_3 : GoodBlock representatives rowsCompose00_012_3 4751459 4791301 2048 :=
  good0196.append good0197 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_4 : List Row := rows0198 ++ rows0199
theorem goodCompose00_012_4 : GoodBlock representatives rowsCompose00_012_4 4791304 4861956 2048 :=
  good0198.append good0199 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_5 : List Row := rowsCompose00_012_3 ++ rowsCompose00_012_4
theorem goodCompose00_012_5 : GoodBlock representatives rowsCompose00_012_5 4751459 4861956 4096 :=
  goodCompose00_012_3.append goodCompose00_012_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_6 : List Row := rowsCompose00_012_2 ++ rowsCompose00_012_5
theorem goodCompose00_012_6 : GoodBlock representatives rowsCompose00_012_6 4612240 4861956 8192 :=
  goodCompose00_012_2.append goodCompose00_012_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_7 : List Row := rows0200 ++ rows0201
theorem goodCompose00_012_7 : GoodBlock representatives rowsCompose00_012_7 4861957 4985481 2048 :=
  good0200.append good0201 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_8 : List Row := rows0202 ++ rows0203
theorem goodCompose00_012_8 : GoodBlock representatives rowsCompose00_012_8 4985488 5116993 2048 :=
  good0202.append good0203 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_9 : List Row := rowsCompose00_012_7 ++ rowsCompose00_012_8
theorem goodCompose00_012_9 : GoodBlock representatives rowsCompose00_012_9 4861957 5116993 4096 :=
  goodCompose00_012_7.append goodCompose00_012_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_10 : List Row := rows0204 ++ rows0205
theorem goodCompose00_012_10 : GoodBlock representatives rowsCompose00_012_10 5117056 5253191 2048 :=
  good0204.append good0205 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_11 : List Row := rows0206 ++ rows0207
theorem goodCompose00_012_11 : GoodBlock representatives rowsCompose00_012_11 5253193 5281929 2048 :=
  good0206.append good0207 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_12 : List Row := rowsCompose00_012_10 ++ rowsCompose00_012_11
theorem goodCompose00_012_12 : GoodBlock representatives rowsCompose00_012_12 5117056 5281929 4096 :=
  goodCompose00_012_10.append goodCompose00_012_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_13 : List Row := rowsCompose00_012_9 ++ rowsCompose00_012_12
theorem goodCompose00_012_13 : GoodBlock representatives rowsCompose00_012_13 4861957 5281929 8192 :=
  goodCompose00_012_9.append goodCompose00_012_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_012_14 : List Row := rowsCompose00_012_6 ++ rowsCompose00_012_13
theorem goodCompose00_012_14 : GoodBlock representatives rowsCompose00_012_14 4612240 5281929 16384 :=
  goodCompose00_012_6.append goodCompose00_012_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_012_14
