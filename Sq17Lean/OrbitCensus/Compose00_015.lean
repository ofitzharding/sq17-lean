import Sq17Lean.OrbitCensus.Chunk0240
import Sq17Lean.OrbitCensus.Chunk0241
import Sq17Lean.OrbitCensus.Chunk0242
import Sq17Lean.OrbitCensus.Chunk0243
import Sq17Lean.OrbitCensus.Chunk0244
import Sq17Lean.OrbitCensus.Chunk0245
import Sq17Lean.OrbitCensus.Chunk0246
import Sq17Lean.OrbitCensus.Chunk0247
import Sq17Lean.OrbitCensus.Chunk0248
import Sq17Lean.OrbitCensus.Chunk0249
import Sq17Lean.OrbitCensus.Chunk0250
import Sq17Lean.OrbitCensus.Chunk0251
import Sq17Lean.OrbitCensus.Chunk0252
import Sq17Lean.OrbitCensus.Chunk0253
import Sq17Lean.OrbitCensus.Chunk0254
import Sq17Lean.OrbitCensus.Chunk0255

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_015_0 : List Row := rows0240 ++ rows0241
theorem goodCompose00_015_0 : GoodBlock representatives rowsCompose00_015_0 8391239 8401458 2048 :=
  good0240.append good0241 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_1 : List Row := rows0242 ++ rows0243
theorem goodCompose00_015_1 : GoodBlock representatives rowsCompose00_015_1 8401458 8415619 2048 :=
  good0242.append good0243 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_2 : List Row := rowsCompose00_015_0 ++ rowsCompose00_015_1
theorem goodCompose00_015_2 : GoodBlock representatives rowsCompose00_015_2 8391239 8415619 4096 :=
  goodCompose00_015_0.append goodCompose00_015_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_3 : List Row := rows0244 ++ rows0245
theorem goodCompose00_015_3 : GoodBlock representatives rowsCompose00_015_3 8415620 8432651 2048 :=
  good0244.append good0245 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_4 : List Row := rows0246 ++ rows0247
theorem goodCompose00_015_4 : GoodBlock representatives rowsCompose00_015_4 8432652 8457989 2048 :=
  good0246.append good0247 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_5 : List Row := rowsCompose00_015_3 ++ rowsCompose00_015_4
theorem goodCompose00_015_5 : GoodBlock representatives rowsCompose00_015_5 8415620 8457989 4096 :=
  goodCompose00_015_3.append goodCompose00_015_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_6 : List Row := rowsCompose00_015_2 ++ rowsCompose00_015_5
theorem goodCompose00_015_6 : GoodBlock representatives rowsCompose00_015_6 8391239 8457989 8192 :=
  goodCompose00_015_2.append goodCompose00_015_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_7 : List Row := rows0248 ++ rows0249
theorem goodCompose00_015_7 : GoodBlock representatives rowsCompose00_015_7 8457992 8479521 2048 :=
  good0248.append good0249 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_8 : List Row := rows0250 ++ rows0251
theorem goodCompose00_015_8 : GoodBlock representatives rowsCompose00_015_8 8479552 8521907 2048 :=
  good0250.append good0251 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_9 : List Row := rowsCompose00_015_7 ++ rowsCompose00_015_8
theorem goodCompose00_015_9 : GoodBlock representatives rowsCompose00_015_9 8457992 8521907 4096 :=
  goodCompose00_015_7.append goodCompose00_015_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_10 : List Row := rows0252 ++ rows0253
theorem goodCompose00_015_10 : GoodBlock representatives rowsCompose00_015_10 8521908 8540441 2048 :=
  good0252.append good0253 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_11 : List Row := rows0254 ++ rows0255
theorem goodCompose00_015_11 : GoodBlock representatives rowsCompose00_015_11 8540449 8586341 2048 :=
  good0254.append good0255 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_12 : List Row := rowsCompose00_015_10 ++ rowsCompose00_015_11
theorem goodCompose00_015_12 : GoodBlock representatives rowsCompose00_015_12 8521908 8586341 4096 :=
  goodCompose00_015_10.append goodCompose00_015_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_13 : List Row := rowsCompose00_015_9 ++ rowsCompose00_015_12
theorem goodCompose00_015_13 : GoodBlock representatives rowsCompose00_015_13 8457992 8586341 8192 :=
  goodCompose00_015_9.append goodCompose00_015_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_015_14 : List Row := rowsCompose00_015_6 ++ rowsCompose00_015_13
theorem goodCompose00_015_14 : GoodBlock representatives rowsCompose00_015_14 8391239 8586341 16384 :=
  goodCompose00_015_6.append goodCompose00_015_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_015_14
