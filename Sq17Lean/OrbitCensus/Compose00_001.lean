import Sq17Lean.OrbitCensus.Chunk0016
import Sq17Lean.OrbitCensus.Chunk0017
import Sq17Lean.OrbitCensus.Chunk0018
import Sq17Lean.OrbitCensus.Chunk0019
import Sq17Lean.OrbitCensus.Chunk0020
import Sq17Lean.OrbitCensus.Chunk0021
import Sq17Lean.OrbitCensus.Chunk0022
import Sq17Lean.OrbitCensus.Chunk0023
import Sq17Lean.OrbitCensus.Chunk0024
import Sq17Lean.OrbitCensus.Chunk0025
import Sq17Lean.OrbitCensus.Chunk0026
import Sq17Lean.OrbitCensus.Chunk0027
import Sq17Lean.OrbitCensus.Chunk0028
import Sq17Lean.OrbitCensus.Chunk0029
import Sq17Lean.OrbitCensus.Chunk0030
import Sq17Lean.OrbitCensus.Chunk0031

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_001_0 : List Row := rows0016 ++ rows0017
theorem goodCompose00_001_0 : GoodBlock representatives rowsCompose00_001_0 95752 113161 2048 :=
  good0016.append good0017 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_1 : List Row := rows0018 ++ rows0019
theorem goodCompose00_001_1 : GoodBlock representatives rowsCompose00_001_1 113168 135602 2048 :=
  good0018.append good0019 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_2 : List Row := rowsCompose00_001_0 ++ rowsCompose00_001_1
theorem goodCompose00_001_2 : GoodBlock representatives rowsCompose00_001_2 95752 135602 4096 :=
  goodCompose00_001_0.append goodCompose00_001_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_3 : List Row := rows0020 ++ rows0021
theorem goodCompose00_001_3 : GoodBlock representatives rowsCompose00_001_3 135602 147798 2048 :=
  good0020.append good0021 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_4 : List Row := rows0022 ++ rows0023
theorem goodCompose00_001_4 : GoodBlock representatives rowsCompose00_001_4 147798 164323 2048 :=
  good0022.append good0023 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_5 : List Row := rowsCompose00_001_3 ++ rowsCompose00_001_4
theorem goodCompose00_001_5 : GoodBlock representatives rowsCompose00_001_5 135602 164323 4096 :=
  goodCompose00_001_3.append goodCompose00_001_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_6 : List Row := rowsCompose00_001_2 ++ rowsCompose00_001_5
theorem goodCompose00_001_6 : GoodBlock representatives rowsCompose00_001_6 95752 164323 8192 :=
  goodCompose00_001_2.append goodCompose00_001_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_7 : List Row := rows0024 ++ rows0025
theorem goodCompose00_001_7 : GoodBlock representatives rowsCompose00_001_7 164324 180883 2048 :=
  good0024.append good0025 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_8 : List Row := rows0026 ++ rows0027
theorem goodCompose00_001_8 : GoodBlock representatives rowsCompose00_001_8 180884 203289 2048 :=
  good0026.append good0027 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_9 : List Row := rowsCompose00_001_7 ++ rowsCompose00_001_8
theorem goodCompose00_001_9 : GoodBlock representatives rowsCompose00_001_9 164324 203289 4096 :=
  goodCompose00_001_7.append goodCompose00_001_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_10 : List Row := rows0028 ++ rows0029
theorem goodCompose00_001_10 : GoodBlock representatives rowsCompose00_001_10 203297 230594 2048 :=
  good0028.append good0029 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_11 : List Row := rows0030 ++ rows0031
theorem goodCompose00_001_11 : GoodBlock representatives rowsCompose00_001_11 230594 266363 2048 :=
  good0030.append good0031 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_12 : List Row := rowsCompose00_001_10 ++ rowsCompose00_001_11
theorem goodCompose00_001_12 : GoodBlock representatives rowsCompose00_001_12 203297 266363 4096 :=
  goodCompose00_001_10.append goodCompose00_001_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_13 : List Row := rowsCompose00_001_9 ++ rowsCompose00_001_12
theorem goodCompose00_001_13 : GoodBlock representatives rowsCompose00_001_13 164324 266363 8192 :=
  goodCompose00_001_9.append goodCompose00_001_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_001_14 : List Row := rowsCompose00_001_6 ++ rowsCompose00_001_13
theorem goodCompose00_001_14 : GoodBlock representatives rowsCompose00_001_14 95752 266363 16384 :=
  goodCompose00_001_6.append goodCompose00_001_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_001_14
