import Sq17Lean.OrbitCensus.Compose02_000

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

theorem checked_rows : GoodBlock representatives rowsCompose02_000_0 127 16646145 346104 := goodCompose02_000_0

/-- Every 17-subset reaches a member of the exact source-bound table.
This is coverage, not a proof that all table entries represent different orbits. -/
theorem exhaustive (s : Finset (Fin 24)) (hs : s.card = 17) :
    Reaches representatives s := checked_rows.exhaustive s hs

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.checked_rows
#print axioms Sq17.OrbitCensus.exhaustive
