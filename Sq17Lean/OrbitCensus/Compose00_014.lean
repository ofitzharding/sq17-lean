import Sq17Lean.OrbitCensus.Chunk0224
import Sq17Lean.OrbitCensus.Chunk0225
import Sq17Lean.OrbitCensus.Chunk0226
import Sq17Lean.OrbitCensus.Chunk0227
import Sq17Lean.OrbitCensus.Chunk0228
import Sq17Lean.OrbitCensus.Chunk0229
import Sq17Lean.OrbitCensus.Chunk0230
import Sq17Lean.OrbitCensus.Chunk0231
import Sq17Lean.OrbitCensus.Chunk0232
import Sq17Lean.OrbitCensus.Chunk0233
import Sq17Lean.OrbitCensus.Chunk0234
import Sq17Lean.OrbitCensus.Chunk0235
import Sq17Lean.OrbitCensus.Chunk0236
import Sq17Lean.OrbitCensus.Chunk0237
import Sq17Lean.OrbitCensus.Chunk0238
import Sq17Lean.OrbitCensus.Chunk0239

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_014_0 : List Row := rows0224 ++ rows0225
theorem goodCompose00_014_0 : GoodBlock representatives rowsCompose00_014_0 6357832 6425129 2048 :=
  good0224.append good0225 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_1 : List Row := rows0226 ++ rows0227
theorem goodCompose00_014_1 : GoodBlock representatives rowsCompose00_014_1 6425136 6553933 2048 :=
  good0226.append good0227 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_2 : List Row := rowsCompose00_014_0 ++ rowsCompose00_014_1
theorem goodCompose00_014_2 : GoodBlock representatives rowsCompose00_014_2 6357832 6553933 4096 :=
  goodCompose00_014_0.append goodCompose00_014_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_3 : List Row := rows0228 ++ rows0229
theorem goodCompose00_014_3 : GoodBlock representatives rowsCompose00_014_3 6553937 6627843 2048 :=
  good0228.append good0229 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_4 : List Row := rows0230 ++ rows0231
theorem goodCompose00_014_4 : GoodBlock representatives rowsCompose00_014_4 6627844 6833186 2048 :=
  good0230.append good0231 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_5 : List Row := rowsCompose00_014_3 ++ rowsCompose00_014_4
theorem goodCompose00_014_5 : GoodBlock representatives rowsCompose00_014_5 6553937 6833186 4096 :=
  goodCompose00_014_3.append goodCompose00_014_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_6 : List Row := rowsCompose00_014_2 ++ rowsCompose00_014_5
theorem goodCompose00_014_6 : GoodBlock representatives rowsCompose00_014_6 6357832 6833186 8192 :=
  goodCompose00_014_2.append goodCompose00_014_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_7 : List Row := rows0232 ++ rows0233
theorem goodCompose00_014_7 : GoodBlock representatives rowsCompose00_014_7 6833186 7078785 2048 :=
  good0232.append good0233 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_8 : List Row := rows0234 ++ rows0235
theorem goodCompose00_014_8 : GoodBlock representatives rowsCompose00_014_8 7078915 7367169 2048 :=
  good0234.append good0235 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_9 : List Row := rowsCompose00_014_7 ++ rowsCompose00_014_8
theorem goodCompose00_014_9 : GoodBlock representatives rowsCompose00_014_9 6833186 7367169 4096 :=
  goodCompose00_014_7.append goodCompose00_014_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_10 : List Row := rows0236 ++ rows0237
theorem goodCompose00_014_10 : GoodBlock representatives rowsCompose00_014_10 7367680 7611649 2048 :=
  good0236.append good0237 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_11 : List Row := rows0238 ++ rows0239
theorem goodCompose00_014_11 : GoodBlock representatives rowsCompose00_014_11 7611904 8391229 2048 :=
  good0238.append good0239 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_12 : List Row := rowsCompose00_014_10 ++ rowsCompose00_014_11
theorem goodCompose00_014_12 : GoodBlock representatives rowsCompose00_014_12 7367680 8391229 4096 :=
  goodCompose00_014_10.append goodCompose00_014_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_13 : List Row := rowsCompose00_014_9 ++ rowsCompose00_014_12
theorem goodCompose00_014_13 : GoodBlock representatives rowsCompose00_014_13 6833186 8391229 8192 :=
  goodCompose00_014_9.append goodCompose00_014_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_014_14 : List Row := rowsCompose00_014_6 ++ rowsCompose00_014_13
theorem goodCompose00_014_14 : GoodBlock representatives rowsCompose00_014_14 6357832 8391229 16384 :=
  goodCompose00_014_6.append goodCompose00_014_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_014_14
