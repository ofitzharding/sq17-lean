import Sq17Lean.OrbitCensus.Compose00_000
import Sq17Lean.OrbitCensus.Compose00_001
import Sq17Lean.OrbitCensus.Compose00_002
import Sq17Lean.OrbitCensus.Compose00_003
import Sq17Lean.OrbitCensus.Compose00_004
import Sq17Lean.OrbitCensus.Compose00_005
import Sq17Lean.OrbitCensus.Compose00_006
import Sq17Lean.OrbitCensus.Compose00_007
import Sq17Lean.OrbitCensus.Compose00_008
import Sq17Lean.OrbitCensus.Compose00_009
import Sq17Lean.OrbitCensus.Compose00_010
import Sq17Lean.OrbitCensus.Compose00_011
import Sq17Lean.OrbitCensus.Compose00_012
import Sq17Lean.OrbitCensus.Compose00_013
import Sq17Lean.OrbitCensus.Compose00_014
import Sq17Lean.OrbitCensus.Compose00_015

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose01_000_0 : List Row := rowsCompose00_000_14 ++ rowsCompose00_001_14
theorem goodCompose01_000_0 : GoodBlock representatives rowsCompose01_000_0 127 266363 32768 :=
  goodCompose00_000_14.append goodCompose00_001_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_1 : List Row := rowsCompose00_002_14 ++ rowsCompose00_003_14
theorem goodCompose01_000_1 : GoodBlock representatives rowsCompose01_000_1 266364 680145 32768 :=
  goodCompose00_002_14.append goodCompose00_003_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_2 : List Row := rowsCompose01_000_0 ++ rowsCompose01_000_1
theorem goodCompose01_000_2 : GoodBlock representatives rowsCompose01_000_2 127 680145 65536 :=
  goodCompose01_000_0.append goodCompose01_000_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_3 : List Row := rowsCompose00_004_14 ++ rowsCompose00_005_14
theorem goodCompose01_000_3 : GoodBlock representatives rowsCompose01_000_3 680160 1328154 32768 :=
  goodCompose00_004_14.append goodCompose00_005_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_4 : List Row := rowsCompose00_006_14 ++ rowsCompose00_007_14
theorem goodCompose01_000_4 : GoodBlock representatives rowsCompose01_000_4 1328154 2247105 32768 :=
  goodCompose00_006_14.append goodCompose00_007_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_5 : List Row := rowsCompose01_000_3 ++ rowsCompose01_000_4
theorem goodCompose01_000_5 : GoodBlock representatives rowsCompose01_000_5 680160 2247105 65536 :=
  goodCompose01_000_3.append goodCompose01_000_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_6 : List Row := rowsCompose01_000_2 ++ rowsCompose01_000_5
theorem goodCompose01_000_6 : GoodBlock representatives rowsCompose01_000_6 127 2247105 131072 :=
  goodCompose01_000_2.append goodCompose01_000_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_7 : List Row := rowsCompose00_008_14 ++ rowsCompose00_009_14
theorem goodCompose01_000_7 : GoodBlock representatives rowsCompose01_000_7 2247171 3408966 32768 :=
  goodCompose00_008_14.append goodCompose00_009_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_8 : List Row := rowsCompose00_010_14 ++ rowsCompose00_011_14
theorem goodCompose01_000_8 : GoodBlock representatives rowsCompose01_000_8 3408966 4612233 32768 :=
  goodCompose00_010_14.append goodCompose00_011_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_9 : List Row := rowsCompose01_000_7 ++ rowsCompose01_000_8
theorem goodCompose01_000_9 : GoodBlock representatives rowsCompose01_000_9 2247171 4612233 65536 :=
  goodCompose01_000_7.append goodCompose01_000_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_10 : List Row := rowsCompose00_012_14 ++ rowsCompose00_013_14
theorem goodCompose01_000_10 : GoodBlock representatives rowsCompose01_000_10 4612240 6357829 32768 :=
  goodCompose00_012_14.append goodCompose00_013_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_11 : List Row := rowsCompose00_014_14 ++ rowsCompose00_015_14
theorem goodCompose01_000_11 : GoodBlock representatives rowsCompose01_000_11 6357832 8586341 32768 :=
  goodCompose00_014_14.append goodCompose00_015_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_12 : List Row := rowsCompose01_000_10 ++ rowsCompose01_000_11
theorem goodCompose01_000_12 : GoodBlock representatives rowsCompose01_000_12 4612240 8586341 65536 :=
  goodCompose01_000_10.append goodCompose01_000_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_13 : List Row := rowsCompose01_000_9 ++ rowsCompose01_000_12
theorem goodCompose01_000_13 : GoodBlock representatives rowsCompose01_000_13 2247171 8586341 131072 :=
  goodCompose01_000_9.append goodCompose01_000_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_000_14 : List Row := rowsCompose01_000_6 ++ rowsCompose01_000_13
theorem goodCompose01_000_14 : GoodBlock representatives rowsCompose01_000_14 127 8586341 262144 :=
  goodCompose01_000_6.append goodCompose01_000_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose01_000_14
