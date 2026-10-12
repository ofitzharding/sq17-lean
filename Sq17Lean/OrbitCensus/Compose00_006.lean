import Sq17Lean.OrbitCensus.Chunk0096
import Sq17Lean.OrbitCensus.Chunk0097
import Sq17Lean.OrbitCensus.Chunk0098
import Sq17Lean.OrbitCensus.Chunk0099
import Sq17Lean.OrbitCensus.Chunk0100
import Sq17Lean.OrbitCensus.Chunk0101
import Sq17Lean.OrbitCensus.Chunk0102
import Sq17Lean.OrbitCensus.Chunk0103
import Sq17Lean.OrbitCensus.Chunk0104
import Sq17Lean.OrbitCensus.Chunk0105
import Sq17Lean.OrbitCensus.Chunk0106
import Sq17Lean.OrbitCensus.Chunk0107
import Sq17Lean.OrbitCensus.Chunk0108
import Sq17Lean.OrbitCensus.Chunk0109
import Sq17Lean.OrbitCensus.Chunk0110
import Sq17Lean.OrbitCensus.Chunk0111

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_006_0 : List Row := rows0096 ++ rows0097
theorem goodCompose00_006_0 : GoodBlock representatives rowsCompose00_006_0 1328154 1364609 2048 :=
  good0096.append good0097 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_1 : List Row := rows0098 ++ rows0099
theorem goodCompose00_006_1 : GoodBlock representatives rowsCompose00_006_1 1364736 1442316 2048 :=
  good0098.append good0099 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_2 : List Row := rowsCompose00_006_0 ++ rowsCompose00_006_1
theorem goodCompose00_006_2 : GoodBlock representatives rowsCompose00_006_2 1328154 1442316 4096 :=
  goodCompose00_006_0.append goodCompose00_006_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_3 : List Row := rows0100 ++ rows0101
theorem goodCompose00_006_3 : GoodBlock representatives rowsCompose00_006_3 1442317 1519625 2048 :=
  good0100.append good0101 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_4 : List Row := rows0102 ++ rows0103
theorem goodCompose00_006_4 : GoodBlock representatives rowsCompose00_006_4 1519632 1585421 2048 :=
  good0102.append good0103 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_5 : List Row := rowsCompose00_006_3 ++ rowsCompose00_006_4
theorem goodCompose00_006_5 : GoodBlock representatives rowsCompose00_006_5 1442317 1585421 4096 :=
  goodCompose00_006_3.append goodCompose00_006_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_6 : List Row := rowsCompose00_006_2 ++ rowsCompose00_006_5
theorem goodCompose00_006_6 : GoodBlock representatives rowsCompose00_006_6 1328154 1585421 8192 :=
  goodCompose00_006_2.append goodCompose00_006_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_7 : List Row := rows0104 ++ rows0105
theorem goodCompose00_006_7 : GoodBlock representatives rowsCompose00_006_7 1585425 1615893 2048 :=
  good0104.append good0105 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_8 : List Row := rows0106 ++ rows0107
theorem goodCompose00_006_8 : GoodBlock representatives rowsCompose00_006_8 1615896 1673761 2048 :=
  good0106.append good0107 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_9 : List Row := rowsCompose00_006_7 ++ rowsCompose00_006_8
theorem goodCompose00_006_9 : GoodBlock representatives rowsCompose00_006_9 1585425 1673761 4096 :=
  goodCompose00_006_7.append goodCompose00_006_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_10 : List Row := rows0108 ++ rows0109
theorem goodCompose00_006_10 : GoodBlock representatives rowsCompose00_006_10 1673792 1757201 2048 :=
  good0108.append good0109 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_11 : List Row := rows0110 ++ rows0111
theorem goodCompose00_006_11 : GoodBlock representatives rowsCompose00_006_11 1757216 1868361 2048 :=
  good0110.append good0111 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_12 : List Row := rowsCompose00_006_10 ++ rowsCompose00_006_11
theorem goodCompose00_006_12 : GoodBlock representatives rowsCompose00_006_12 1673792 1868361 4096 :=
  goodCompose00_006_10.append goodCompose00_006_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_13 : List Row := rowsCompose00_006_9 ++ rowsCompose00_006_12
theorem goodCompose00_006_13 : GoodBlock representatives rowsCompose00_006_13 1585425 1868361 8192 :=
  goodCompose00_006_9.append goodCompose00_006_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_006_14 : List Row := rowsCompose00_006_6 ++ rowsCompose00_006_13
theorem goodCompose00_006_14 : GoodBlock representatives rowsCompose00_006_14 1328154 1868361 16384 :=
  goodCompose00_006_6.append goodCompose00_006_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_006_14
