import Sq17Lean.OrbitCensus.Chunk0336
import Sq17Lean.OrbitCensus.Chunk0337

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_021_0 : List Row := rows0336 ++ rows0337
theorem goodCompose00_021_0 : GoodBlock representatives rowsCompose00_021_0 15204648 16646145 2040 :=
  good0336.append good0337 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_021_0
