import Sq17Lean.OrbitCensus.Compose01_000
import Sq17Lean.OrbitCensus.Compose01_001

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose02_000_0 : List Row := rowsCompose01_000_14 ++ rowsCompose01_001_4
theorem goodCompose02_000_0 : GoodBlock representatives rowsCompose02_000_0 127 16646145 346104 :=
  goodCompose01_000_14.append goodCompose01_001_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose02_000_0
