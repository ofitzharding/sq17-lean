import Sq17Lean.OrbitCensus.Chunk0064
import Sq17Lean.OrbitCensus.Chunk0065
import Sq17Lean.OrbitCensus.Chunk0066
import Sq17Lean.OrbitCensus.Chunk0067
import Sq17Lean.OrbitCensus.Chunk0068
import Sq17Lean.OrbitCensus.Chunk0069
import Sq17Lean.OrbitCensus.Chunk0070
import Sq17Lean.OrbitCensus.Chunk0071
import Sq17Lean.OrbitCensus.Chunk0072
import Sq17Lean.OrbitCensus.Chunk0073
import Sq17Lean.OrbitCensus.Chunk0074
import Sq17Lean.OrbitCensus.Chunk0075
import Sq17Lean.OrbitCensus.Chunk0076
import Sq17Lean.OrbitCensus.Chunk0077
import Sq17Lean.OrbitCensus.Chunk0078
import Sq17Lean.OrbitCensus.Chunk0079

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_004_0 : List Row := rows0064 ++ rows0065
theorem goodCompose00_004_0 : GoodBlock representatives rowsCompose00_004_0 680160 723974 2048 :=
  good0064.append good0065 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_1 : List Row := rows0066 ++ rows0067
theorem goodCompose00_004_1 : GoodBlock representatives rowsCompose00_004_1 723974 789530 2048 :=
  good0066.append good0067 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_2 : List Row := rowsCompose00_004_0 ++ rowsCompose00_004_1
theorem goodCompose00_004_2 : GoodBlock representatives rowsCompose00_004_2 680160 789530 4096 :=
  goodCompose00_004_0.append goodCompose00_004_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_3 : List Row := rows0068 ++ rows0069
theorem goodCompose00_004_3 : GoodBlock representatives rowsCompose00_004_3 789530 811044 2048 :=
  good0068.append good0069 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_4 : List Row := rows0070 ++ rows0071
theorem goodCompose00_004_4 : GoodBlock representatives rowsCompose00_004_4 811045 854402 2048 :=
  good0070.append good0071 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_5 : List Row := rowsCompose00_004_3 ++ rowsCompose00_004_4
theorem goodCompose00_004_5 : GoodBlock representatives rowsCompose00_004_5 789530 854402 4096 :=
  goodCompose00_004_3.append goodCompose00_004_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_6 : List Row := rowsCompose00_004_2 ++ rowsCompose00_004_5
theorem goodCompose00_004_6 : GoodBlock representatives rowsCompose00_004_6 680160 854402 8192 :=
  goodCompose00_004_2.append goodCompose00_004_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_7 : List Row := rows0072 ++ rows0073
theorem goodCompose00_004_7 : GoodBlock representatives rowsCompose00_004_7 854402 922721 2048 :=
  good0072.append good0073 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_8 : List Row := rows0074 ++ rows0075
theorem goodCompose00_004_8 : GoodBlock representatives rowsCompose00_004_8 922753 1049998 2048 :=
  good0074.append good0075 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_9 : List Row := rowsCompose00_004_7 ++ rowsCompose00_004_8
theorem goodCompose00_004_9 : GoodBlock representatives rowsCompose00_004_9 854402 1049998 4096 :=
  goodCompose00_004_7.append goodCompose00_004_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_10 : List Row := rows0076 ++ rows0077
theorem goodCompose00_004_10 : GoodBlock representatives rowsCompose00_004_10 1049998 1059493 2048 :=
  good0076.append good0077 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_11 : List Row := rows0078 ++ rows0079
theorem goodCompose00_004_11 : GoodBlock representatives rowsCompose00_004_11 1059496 1073547 2048 :=
  good0078.append good0079 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_12 : List Row := rowsCompose00_004_10 ++ rowsCompose00_004_11
theorem goodCompose00_004_12 : GoodBlock representatives rowsCompose00_004_12 1049998 1073547 4096 :=
  goodCompose00_004_10.append goodCompose00_004_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_13 : List Row := rowsCompose00_004_9 ++ rowsCompose00_004_12
theorem goodCompose00_004_13 : GoodBlock representatives rowsCompose00_004_13 854402 1073547 8192 :=
  goodCompose00_004_9.append goodCompose00_004_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_004_14 : List Row := rowsCompose00_004_6 ++ rowsCompose00_004_13
theorem goodCompose00_004_14 : GoodBlock representatives rowsCompose00_004_14 680160 1073547 16384 :=
  goodCompose00_004_6.append goodCompose00_004_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_004_14
