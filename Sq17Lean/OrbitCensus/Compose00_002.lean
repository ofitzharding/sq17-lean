import Sq17Lean.OrbitCensus.Chunk0032
import Sq17Lean.OrbitCensus.Chunk0033
import Sq17Lean.OrbitCensus.Chunk0034
import Sq17Lean.OrbitCensus.Chunk0035
import Sq17Lean.OrbitCensus.Chunk0036
import Sq17Lean.OrbitCensus.Chunk0037
import Sq17Lean.OrbitCensus.Chunk0038
import Sq17Lean.OrbitCensus.Chunk0039
import Sq17Lean.OrbitCensus.Chunk0040
import Sq17Lean.OrbitCensus.Chunk0041
import Sq17Lean.OrbitCensus.Chunk0042
import Sq17Lean.OrbitCensus.Chunk0043
import Sq17Lean.OrbitCensus.Chunk0044
import Sq17Lean.OrbitCensus.Chunk0045
import Sq17Lean.OrbitCensus.Chunk0046
import Sq17Lean.OrbitCensus.Chunk0047

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_002_0 : List Row := rows0032 ++ rows0033
theorem goodCompose00_002_0 : GoodBlock representatives rowsCompose00_002_0 266364 277793 2048 :=
  good0032.append good0033 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_1 : List Row := rows0034 ++ rows0035
theorem goodCompose00_002_1 : GoodBlock representatives rowsCompose00_002_1 277824 295099 2048 :=
  good0034.append good0035 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_2 : List Row := rowsCompose00_002_0 ++ rowsCompose00_002_1
theorem goodCompose00_002_2 : GoodBlock representatives rowsCompose00_002_2 266364 295099 4096 :=
  goodCompose00_002_0.append goodCompose00_002_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_3 : List Row := rows0036 ++ rows0037
theorem goodCompose00_002_3 : GoodBlock representatives rowsCompose00_002_3 295100 311588 2048 :=
  good0036.append good0037 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_4 : List Row := rows0038 ++ rows0039
theorem goodCompose00_002_4 : GoodBlock representatives rowsCompose00_002_4 311589 333846 2048 :=
  good0038.append good0039 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_5 : List Row := rowsCompose00_002_3 ++ rowsCompose00_002_4
theorem goodCompose00_002_5 : GoodBlock representatives rowsCompose00_002_5 295100 333846 4096 :=
  goodCompose00_002_3.append goodCompose00_002_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_6 : List Row := rowsCompose00_002_2 ++ rowsCompose00_002_5
theorem goodCompose00_002_6 : GoodBlock representatives rowsCompose00_002_6 266364 333846 8192 :=
  goodCompose00_002_2.append goodCompose00_002_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_7 : List Row := rows0040 ++ rows0041
theorem goodCompose00_002_7 : GoodBlock representatives rowsCompose00_002_7 333846 361123 2048 :=
  good0040.append good0041 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_8 : List Row := rows0042 ++ rows0043
theorem goodCompose00_002_8 : GoodBlock representatives rowsCompose00_002_8 361124 397525 2048 :=
  good0042.append good0043 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_9 : List Row := rowsCompose00_002_7 ++ rowsCompose00_002_8
theorem goodCompose00_002_9 : GoodBlock representatives rowsCompose00_002_9 333846 397525 4096 :=
  goodCompose00_002_7.append goodCompose00_002_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_10 : List Row := rows0044 ++ rows0045
theorem goodCompose00_002_10 : GoodBlock representatives rowsCompose00_002_10 397528 419970 2048 :=
  good0044.append good0045 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_11 : List Row := rows0046 ++ rows0047
theorem goodCompose00_002_11 : GoodBlock representatives rowsCompose00_002_11 419970 463371 2048 :=
  good0046.append good0047 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_12 : List Row := rowsCompose00_002_10 ++ rowsCompose00_002_11
theorem goodCompose00_002_12 : GoodBlock representatives rowsCompose00_002_12 397528 463371 4096 :=
  goodCompose00_002_10.append goodCompose00_002_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_13 : List Row := rowsCompose00_002_9 ++ rowsCompose00_002_12
theorem goodCompose00_002_13 : GoodBlock representatives rowsCompose00_002_13 333846 463371 8192 :=
  goodCompose00_002_9.append goodCompose00_002_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_002_14 : List Row := rowsCompose00_002_6 ++ rowsCompose00_002_13
theorem goodCompose00_002_14 : GoodBlock representatives rowsCompose00_002_14 266364 463371 16384 :=
  goodCompose00_002_6.append goodCompose00_002_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_002_14
