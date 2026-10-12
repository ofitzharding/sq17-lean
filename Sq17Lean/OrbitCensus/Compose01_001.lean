import Sq17Lean.OrbitCensus.Compose00_016
import Sq17Lean.OrbitCensus.Compose00_017
import Sq17Lean.OrbitCensus.Compose00_018
import Sq17Lean.OrbitCensus.Compose00_019
import Sq17Lean.OrbitCensus.Compose00_020
import Sq17Lean.OrbitCensus.Compose00_021

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose01_001_0 : List Row := rowsCompose00_017_14 ++ rowsCompose00_018_14
theorem goodCompose01_001_0 : GoodBlock representatives rowsCompose01_001_0 9044145 11011206 32768 :=
  goodCompose00_017_14.append goodCompose00_018_14 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_001_1 : List Row := rowsCompose00_016_14 ++ rowsCompose01_001_0
theorem goodCompose01_001_1 : GoodBlock representatives rowsCompose01_001_1 8586344 11011206 49152 :=
  goodCompose00_016_14.append goodCompose01_001_0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_001_2 : List Row := rowsCompose00_020_14 ++ rowsCompose00_021_0
theorem goodCompose01_001_2 : GoodBlock representatives rowsCompose01_001_2 12759072 16646145 18424 :=
  goodCompose00_020_14.append goodCompose00_021_0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_001_3 : List Row := rowsCompose00_019_14 ++ rowsCompose01_001_2
theorem goodCompose01_001_3 : GoodBlock representatives rowsCompose01_001_3 11011206 16646145 34808 :=
  goodCompose00_019_14.append goodCompose01_001_2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose01_001_4 : List Row := rowsCompose01_001_1 ++ rowsCompose01_001_3
theorem goodCompose01_001_4 : GoodBlock representatives rowsCompose01_001_4 8586344 16646145 83960 :=
  goodCompose01_001_1.append goodCompose01_001_3 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose01_001_4
