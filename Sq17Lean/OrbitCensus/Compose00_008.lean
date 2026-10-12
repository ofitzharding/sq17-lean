import Sq17Lean.OrbitCensus.Chunk0128
import Sq17Lean.OrbitCensus.Chunk0129
import Sq17Lean.OrbitCensus.Chunk0130
import Sq17Lean.OrbitCensus.Chunk0131
import Sq17Lean.OrbitCensus.Chunk0132
import Sq17Lean.OrbitCensus.Chunk0133
import Sq17Lean.OrbitCensus.Chunk0134
import Sq17Lean.OrbitCensus.Chunk0135
import Sq17Lean.OrbitCensus.Chunk0136
import Sq17Lean.OrbitCensus.Chunk0137
import Sq17Lean.OrbitCensus.Chunk0138
import Sq17Lean.OrbitCensus.Chunk0139
import Sq17Lean.OrbitCensus.Chunk0140
import Sq17Lean.OrbitCensus.Chunk0141
import Sq17Lean.OrbitCensus.Chunk0142
import Sq17Lean.OrbitCensus.Chunk0143

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_008_0 : List Row := rows0128 ++ rows0129
theorem goodCompose00_008_0 : GoodBlock representatives rowsCompose00_008_0 2247171 2294093 2048 :=
  good0128.append good0129 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_1 : List Row := rows0130 ++ rows0131
theorem goodCompose00_008_1 : GoodBlock representatives rowsCompose00_008_1 2294097 2360588 2048 :=
  good0130.append good0131 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_2 : List Row := rowsCompose00_008_0 ++ rowsCompose00_008_1
theorem goodCompose00_008_2 : GoodBlock representatives rowsCompose00_008_2 2247171 2360588 4096 :=
  goodCompose00_008_0.append goodCompose00_008_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_3 : List Row := rows0132 ++ rows0133
theorem goodCompose00_008_3 : GoodBlock representatives rowsCompose00_008_3 2360589 2377867 2048 :=
  good0132.append good0133 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_4 : List Row := rows0134 ++ rows0135
theorem goodCompose00_008_4 : GoodBlock representatives rowsCompose00_008_4 2377868 2425010 2048 :=
  good0134.append good0135 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_5 : List Row := rowsCompose00_008_3 ++ rowsCompose00_008_4
theorem goodCompose00_008_5 : GoodBlock representatives rowsCompose00_008_5 2360589 2425010 4096 :=
  goodCompose00_008_3.append goodCompose00_008_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_6 : List Row := rowsCompose00_008_2 ++ rowsCompose00_008_5
theorem goodCompose00_008_6 : GoodBlock representatives rowsCompose00_008_6 2247171 2425010 8192 :=
  goodCompose00_008_2.append goodCompose00_008_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_7 : List Row := rows0136 ++ rows0137
theorem goodCompose00_008_7 : GoodBlock representatives rowsCompose00_008_7 2425010 2491689 2048 :=
  good0136.append good0137 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_8 : List Row := rows0138 ++ rows0139
theorem goodCompose00_008_8 : GoodBlock representatives rowsCompose00_008_8 2491696 2589825 2048 :=
  good0138.append good0139 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_9 : List Row := rowsCompose00_008_7 ++ rowsCompose00_008_8
theorem goodCompose00_008_9 : GoodBlock representatives rowsCompose00_008_9 2425010 2589825 4096 :=
  goodCompose00_008_7.append goodCompose00_008_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_10 : List Row := rows0140 ++ rows0141
theorem goodCompose00_008_10 : GoodBlock representatives rowsCompose00_008_10 2589952 2636809 2048 :=
  good0140.append good0141 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_11 : List Row := rows0142 ++ rows0143
theorem goodCompose00_008_11 : GoodBlock representatives rowsCompose00_008_11 2636816 2670731 2048 :=
  good0142.append good0143 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_12 : List Row := rowsCompose00_008_10 ++ rowsCompose00_008_11
theorem goodCompose00_008_12 : GoodBlock representatives rowsCompose00_008_12 2589952 2670731 4096 :=
  goodCompose00_008_10.append goodCompose00_008_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_13 : List Row := rowsCompose00_008_9 ++ rowsCompose00_008_12
theorem goodCompose00_008_13 : GoodBlock representatives rowsCompose00_008_13 2425010 2670731 8192 :=
  goodCompose00_008_9.append goodCompose00_008_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_008_14 : List Row := rowsCompose00_008_6 ++ rowsCompose00_008_13
theorem goodCompose00_008_14 : GoodBlock representatives rowsCompose00_008_14 2247171 2670731 16384 :=
  goodCompose00_008_6.append goodCompose00_008_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_008_14
