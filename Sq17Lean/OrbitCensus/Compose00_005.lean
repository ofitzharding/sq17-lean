import Sq17Lean.OrbitCensus.Chunk0080
import Sq17Lean.OrbitCensus.Chunk0081
import Sq17Lean.OrbitCensus.Chunk0082
import Sq17Lean.OrbitCensus.Chunk0083
import Sq17Lean.OrbitCensus.Chunk0084
import Sq17Lean.OrbitCensus.Chunk0085
import Sq17Lean.OrbitCensus.Chunk0086
import Sq17Lean.OrbitCensus.Chunk0087
import Sq17Lean.OrbitCensus.Chunk0088
import Sq17Lean.OrbitCensus.Chunk0089
import Sq17Lean.OrbitCensus.Chunk0090
import Sq17Lean.OrbitCensus.Chunk0091
import Sq17Lean.OrbitCensus.Chunk0092
import Sq17Lean.OrbitCensus.Chunk0093
import Sq17Lean.OrbitCensus.Chunk0094
import Sq17Lean.OrbitCensus.Chunk0095

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_005_0 : List Row := rows0080 ++ rows0081
theorem goodCompose00_005_0 : GoodBlock representatives rowsCompose00_005_0 1073548 1090137 2048 :=
  good0080.append good0081 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_1 : List Row := rows0082 ++ rows0083
theorem goodCompose00_005_1 : GoodBlock representatives rowsCompose00_005_1 1090145 1116260 2048 :=
  good0082.append good0083 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_2 : List Row := rowsCompose00_005_0 ++ rowsCompose00_005_1
theorem goodCompose00_005_2 : GoodBlock representatives rowsCompose00_005_2 1073548 1116260 4096 :=
  goodCompose00_005_0.append goodCompose00_005_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_3 : List Row := rows0084 ++ rows0085
theorem goodCompose00_005_3 : GoodBlock representatives rowsCompose00_005_3 1116261 1134730 2048 :=
  good0084.append good0085 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_4 : List Row := rows0086 ++ rows0087
theorem goodCompose00_005_4 : GoodBlock representatives rowsCompose00_005_4 1134730 1180473 2048 :=
  good0086.append good0087 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_5 : List Row := rowsCompose00_005_3 ++ rowsCompose00_005_4
theorem goodCompose00_005_5 : GoodBlock representatives rowsCompose00_005_5 1116261 1180473 4096 :=
  goodCompose00_005_3.append goodCompose00_005_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_6 : List Row := rowsCompose00_005_2 ++ rowsCompose00_005_5
theorem goodCompose00_005_6 : GoodBlock representatives rowsCompose00_005_6 1073548 1180473 8192 :=
  goodCompose00_005_2.append goodCompose00_005_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_7 : List Row := rows0088 ++ rows0089
theorem goodCompose00_005_7 : GoodBlock representatives rowsCompose00_005_7 1180483 1197251 2048 :=
  good0088.append good0089 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_8 : List Row := rows0090 ++ rows0091
theorem goodCompose00_005_8 : GoodBlock representatives rowsCompose00_005_8 1197252 1237122 2048 :=
  good0090.append good0091 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_9 : List Row := rowsCompose00_005_7 ++ rowsCompose00_005_8
theorem goodCompose00_005_9 : GoodBlock representatives rowsCompose00_005_9 1180483 1237122 4096 :=
  goodCompose00_005_7.append goodCompose00_005_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_10 : List Row := rows0092 ++ rows0093
theorem goodCompose00_005_10 : GoodBlock representatives rowsCompose00_005_10 1237122 1311396 2048 :=
  good0092.append good0093 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_11 : List Row := rows0094 ++ rows0095
theorem goodCompose00_005_11 : GoodBlock representatives rowsCompose00_005_11 1311397 1328154 2048 :=
  good0094.append good0095 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_12 : List Row := rowsCompose00_005_10 ++ rowsCompose00_005_11
theorem goodCompose00_005_12 : GoodBlock representatives rowsCompose00_005_12 1237122 1328154 4096 :=
  goodCompose00_005_10.append goodCompose00_005_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_13 : List Row := rowsCompose00_005_9 ++ rowsCompose00_005_12
theorem goodCompose00_005_13 : GoodBlock representatives rowsCompose00_005_13 1180483 1328154 8192 :=
  goodCompose00_005_9.append goodCompose00_005_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_005_14 : List Row := rowsCompose00_005_6 ++ rowsCompose00_005_13
theorem goodCompose00_005_14 : GoodBlock representatives rowsCompose00_005_14 1073548 1328154 16384 :=
  goodCompose00_005_6.append goodCompose00_005_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_005_14
