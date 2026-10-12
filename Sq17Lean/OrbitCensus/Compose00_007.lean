import Sq17Lean.OrbitCensus.Chunk0112
import Sq17Lean.OrbitCensus.Chunk0113
import Sq17Lean.OrbitCensus.Chunk0114
import Sq17Lean.OrbitCensus.Chunk0115
import Sq17Lean.OrbitCensus.Chunk0116
import Sq17Lean.OrbitCensus.Chunk0117
import Sq17Lean.OrbitCensus.Chunk0118
import Sq17Lean.OrbitCensus.Chunk0119
import Sq17Lean.OrbitCensus.Chunk0120
import Sq17Lean.OrbitCensus.Chunk0121
import Sq17Lean.OrbitCensus.Chunk0122
import Sq17Lean.OrbitCensus.Chunk0123
import Sq17Lean.OrbitCensus.Chunk0124
import Sq17Lean.OrbitCensus.Chunk0125
import Sq17Lean.OrbitCensus.Chunk0126
import Sq17Lean.OrbitCensus.Chunk0127

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_007_0 : List Row := rows0112 ++ rows0113
theorem goodCompose00_007_0 : GoodBlock representatives rowsCompose00_007_0 1868368 2099121 2048 :=
  good0112.append good0113 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_1 : List Row := rows0114 ++ rows0115
theorem goodCompose00_007_1 : GoodBlock representatives rowsCompose00_007_1 2099137 2109193 2048 :=
  good0114.append good0115 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_2 : List Row := rowsCompose00_007_0 ++ rowsCompose00_007_1
theorem goodCompose00_007_2 : GoodBlock representatives rowsCompose00_007_2 1868368 2109193 4096 :=
  goodCompose00_007_0.append goodCompose00_007_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_3 : List Row := rows0116 ++ rows0117
theorem goodCompose00_007_3 : GoodBlock representatives rowsCompose00_007_3 2109200 2122947 2048 :=
  good0116.append good0117 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_4 : List Row := rows0118 ++ rows0119
theorem goodCompose00_007_4 : GoodBlock representatives rowsCompose00_007_4 2122948 2139689 2048 :=
  good0118.append good0119 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_5 : List Row := rowsCompose00_007_3 ++ rowsCompose00_007_4
theorem goodCompose00_007_5 : GoodBlock representatives rowsCompose00_007_5 2109200 2139689 4096 :=
  goodCompose00_007_3.append goodCompose00_007_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_6 : List Row := rowsCompose00_007_2 ++ rowsCompose00_007_5
theorem goodCompose00_007_6 : GoodBlock representatives rowsCompose00_007_6 1868368 2139689 8192 :=
  goodCompose00_007_2.append goodCompose00_007_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_7 : List Row := rows0120 ++ rows0121
theorem goodCompose00_007_7 : GoodBlock representatives rowsCompose00_007_7 2139696 2165443 2048 :=
  good0120.append good0121 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_8 : List Row := rows0122 ++ rows0123
theorem goodCompose00_007_8 : GoodBlock representatives rowsCompose00_007_8 2165444 2185361 2048 :=
  good0122.append good0123 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_9 : List Row := rowsCompose00_007_7 ++ rowsCompose00_007_8
theorem goodCompose00_007_9 : GoodBlock representatives rowsCompose00_007_9 2139696 2185361 4096 :=
  goodCompose00_007_7.append goodCompose00_007_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_10 : List Row := rows0124 ++ rows0125
theorem goodCompose00_007_10 : GoodBlock representatives rowsCompose00_007_10 2185376 2229666 2048 :=
  good0124.append good0125 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_11 : List Row := rows0126 ++ rows0127
theorem goodCompose00_007_11 : GoodBlock representatives rowsCompose00_007_11 2229666 2247105 2048 :=
  good0126.append good0127 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_12 : List Row := rowsCompose00_007_10 ++ rowsCompose00_007_11
theorem goodCompose00_007_12 : GoodBlock representatives rowsCompose00_007_12 2185376 2247105 4096 :=
  goodCompose00_007_10.append goodCompose00_007_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_13 : List Row := rowsCompose00_007_9 ++ rowsCompose00_007_12
theorem goodCompose00_007_13 : GoodBlock representatives rowsCompose00_007_13 2139696 2247105 8192 :=
  goodCompose00_007_9.append goodCompose00_007_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_007_14 : List Row := rowsCompose00_007_6 ++ rowsCompose00_007_13
theorem goodCompose00_007_14 : GoodBlock representatives rowsCompose00_007_14 1868368 2247105 16384 :=
  goodCompose00_007_6.append goodCompose00_007_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_007_14
