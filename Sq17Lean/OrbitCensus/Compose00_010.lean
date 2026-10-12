import Sq17Lean.OrbitCensus.Chunk0160
import Sq17Lean.OrbitCensus.Chunk0161
import Sq17Lean.OrbitCensus.Chunk0162
import Sq17Lean.OrbitCensus.Chunk0163
import Sq17Lean.OrbitCensus.Chunk0164
import Sq17Lean.OrbitCensus.Chunk0165
import Sq17Lean.OrbitCensus.Chunk0166
import Sq17Lean.OrbitCensus.Chunk0167
import Sq17Lean.OrbitCensus.Chunk0168
import Sq17Lean.OrbitCensus.Chunk0169
import Sq17Lean.OrbitCensus.Chunk0170
import Sq17Lean.OrbitCensus.Chunk0171
import Sq17Lean.OrbitCensus.Chunk0172
import Sq17Lean.OrbitCensus.Chunk0173
import Sq17Lean.OrbitCensus.Chunk0174
import Sq17Lean.OrbitCensus.Chunk0175

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_010_0 : List Row := rows0160 ++ rows0161
theorem goodCompose00_010_0 : GoodBlock representatives rowsCompose00_010_0 3408966 3506187 2048 :=
  good0160.append good0161 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_1 : List Row := rows0162 ++ rows0163
theorem goodCompose00_010_1 : GoodBlock representatives rowsCompose00_010_1 3506188 3691523 2048 :=
  good0162.append good0163 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_2 : List Row := rowsCompose00_010_0 ++ rowsCompose00_010_1
theorem goodCompose00_010_2 : GoodBlock representatives rowsCompose00_010_2 3408966 3691523 4096 :=
  goodCompose00_010_0.append goodCompose00_010_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_3 : List Row := rows0164 ++ rows0165
theorem goodCompose00_010_3 : GoodBlock representatives rowsCompose00_010_3 3691524 3936641 2048 :=
  good0164.append good0165 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_4 : List Row := rows0166 ++ rows0167
theorem goodCompose00_010_4 : GoodBlock representatives rowsCompose00_010_4 3936769 4200803 2048 :=
  good0166.append good0167 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_5 : List Row := rowsCompose00_010_3 ++ rowsCompose00_010_4
theorem goodCompose00_010_5 : GoodBlock representatives rowsCompose00_010_5 3691524 4200803 4096 :=
  goodCompose00_010_3.append goodCompose00_010_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_6 : List Row := rowsCompose00_010_2 ++ rowsCompose00_010_5
theorem goodCompose00_010_6 : GoodBlock representatives rowsCompose00_010_6 3408966 4200803 8192 :=
  goodCompose00_010_2.append goodCompose00_010_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_7 : List Row := rows0168 ++ rows0169
theorem goodCompose00_010_7 : GoodBlock representatives rowsCompose00_010_7 4200804 4213000 2048 :=
  good0168.append good0169 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_8 : List Row := rows0170 ++ rows0171
theorem goodCompose00_010_8 : GoodBlock representatives rowsCompose00_010_8 4213003 4229539 2048 :=
  good0170.append good0171 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_9 : List Row := rowsCompose00_010_7 ++ rowsCompose00_010_8
theorem goodCompose00_010_9 : GoodBlock representatives rowsCompose00_010_9 4200804 4229539 4096 :=
  goodCompose00_010_7.append goodCompose00_010_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_10 : List Row := rows0172 ++ rows0173
theorem goodCompose00_010_10 : GoodBlock representatives rowsCompose00_010_10 4229540 4248601 2048 :=
  good0172.append good0173 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_11 : List Row := rows0174 ++ rows0175
theorem goodCompose00_010_11 : GoodBlock representatives rowsCompose00_010_11 4248609 4270289 2048 :=
  good0174.append good0175 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_12 : List Row := rowsCompose00_010_10 ++ rowsCompose00_010_11
theorem goodCompose00_010_12 : GoodBlock representatives rowsCompose00_010_12 4229540 4270289 4096 :=
  goodCompose00_010_10.append goodCompose00_010_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_13 : List Row := rowsCompose00_010_9 ++ rowsCompose00_010_12
theorem goodCompose00_010_13 : GoodBlock representatives rowsCompose00_010_13 4200804 4270289 8192 :=
  goodCompose00_010_9.append goodCompose00_010_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_010_14 : List Row := rowsCompose00_010_6 ++ rowsCompose00_010_13
theorem goodCompose00_010_14 : GoodBlock representatives rowsCompose00_010_14 3408966 4270289 16384 :=
  goodCompose00_010_6.append goodCompose00_010_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_010_14
