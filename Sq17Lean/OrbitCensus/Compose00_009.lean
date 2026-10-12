import Sq17Lean.OrbitCensus.Chunk0144
import Sq17Lean.OrbitCensus.Chunk0145
import Sq17Lean.OrbitCensus.Chunk0146
import Sq17Lean.OrbitCensus.Chunk0147
import Sq17Lean.OrbitCensus.Chunk0148
import Sq17Lean.OrbitCensus.Chunk0149
import Sq17Lean.OrbitCensus.Chunk0150
import Sq17Lean.OrbitCensus.Chunk0151
import Sq17Lean.OrbitCensus.Chunk0152
import Sq17Lean.OrbitCensus.Chunk0153
import Sq17Lean.OrbitCensus.Chunk0154
import Sq17Lean.OrbitCensus.Chunk0155
import Sq17Lean.OrbitCensus.Chunk0156
import Sq17Lean.OrbitCensus.Chunk0157
import Sq17Lean.OrbitCensus.Chunk0158
import Sq17Lean.OrbitCensus.Chunk0159

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_009_0 : List Row := rows0144 ++ rows0145
theorem goodCompose00_009_0 : GoodBlock representatives rowsCompose00_009_0 2670732 2732097 2048 :=
  good0144.append good0145 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_1 : List Row := rows0146 ++ rows0147
theorem goodCompose00_009_1 : GoodBlock representatives rowsCompose00_009_1 2732160 2819107 2048 :=
  good0146.append good0147 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_2 : List Row := rowsCompose00_009_0 ++ rowsCompose00_009_1
theorem goodCompose00_009_2 : GoodBlock representatives rowsCompose00_009_2 2670732 2819107 4096 :=
  goodCompose00_009_0.append goodCompose00_009_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_3 : List Row := rows0148 ++ rows0149
theorem goodCompose00_009_3 : GoodBlock representatives rowsCompose00_009_3 2819108 2920769 2048 :=
  good0148.append good0149 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_4 : List Row := rows0150 ++ rows0151
theorem goodCompose00_009_4 : GoodBlock representatives rowsCompose00_009_4 2920832 3148345 2048 :=
  good0150.append good0151 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_5 : List Row := rowsCompose00_009_3 ++ rowsCompose00_009_4
theorem goodCompose00_009_5 : GoodBlock representatives rowsCompose00_009_5 2819108 3148345 4096 :=
  goodCompose00_009_3.append goodCompose00_009_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_6 : List Row := rowsCompose00_009_2 ++ rowsCompose00_009_5
theorem goodCompose00_009_6 : GoodBlock representatives rowsCompose00_009_6 2670732 3148345 8192 :=
  goodCompose00_009_2.append goodCompose00_009_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_7 : List Row := rows0152 ++ rows0153
theorem goodCompose00_009_7 : GoodBlock representatives rowsCompose00_009_7 3148355 3167749 2048 :=
  good0152.append good0153 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_8 : List Row := rows0154 ++ rows0155
theorem goodCompose00_009_8 : GoodBlock representatives rowsCompose00_009_8 3167752 3213334 2048 :=
  good0154.append good0155 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_9 : List Row := rowsCompose00_009_7 ++ rowsCompose00_009_8
theorem goodCompose00_009_9 : GoodBlock representatives rowsCompose00_009_9 3148355 3213334 4096 :=
  goodCompose00_009_7.append goodCompose00_009_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_10 : List Row := rows0156 ++ rows0157
theorem goodCompose00_009_10 : GoodBlock representatives rowsCompose00_009_10 3213334 3281189 2048 :=
  good0156.append good0157 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_11 : List Row := rows0158 ++ rows0159
theorem goodCompose00_009_11 : GoodBlock representatives rowsCompose00_009_11 3281192 3408966 2048 :=
  good0158.append good0159 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_12 : List Row := rowsCompose00_009_10 ++ rowsCompose00_009_11
theorem goodCompose00_009_12 : GoodBlock representatives rowsCompose00_009_12 3213334 3408966 4096 :=
  goodCompose00_009_10.append goodCompose00_009_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_13 : List Row := rowsCompose00_009_9 ++ rowsCompose00_009_12
theorem goodCompose00_009_13 : GoodBlock representatives rowsCompose00_009_13 3148355 3408966 8192 :=
  goodCompose00_009_9.append goodCompose00_009_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_009_14 : List Row := rowsCompose00_009_6 ++ rowsCompose00_009_13
theorem goodCompose00_009_14 : GoodBlock representatives rowsCompose00_009_14 2670732 3408966 16384 :=
  goodCompose00_009_6.append goodCompose00_009_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_009_14
