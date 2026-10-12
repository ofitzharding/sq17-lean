import Sq17Lean.OrbitCensus.Chunk0000
import Sq17Lean.OrbitCensus.Chunk0001
import Sq17Lean.OrbitCensus.Chunk0002
import Sq17Lean.OrbitCensus.Chunk0003
import Sq17Lean.OrbitCensus.Chunk0004
import Sq17Lean.OrbitCensus.Chunk0005
import Sq17Lean.OrbitCensus.Chunk0006
import Sq17Lean.OrbitCensus.Chunk0007
import Sq17Lean.OrbitCensus.Chunk0008
import Sq17Lean.OrbitCensus.Chunk0009
import Sq17Lean.OrbitCensus.Chunk0010
import Sq17Lean.OrbitCensus.Chunk0011
import Sq17Lean.OrbitCensus.Chunk0012
import Sq17Lean.OrbitCensus.Chunk0013
import Sq17Lean.OrbitCensus.Chunk0014
import Sq17Lean.OrbitCensus.Chunk0015

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_000_0 : List Row := rows0000 ++ rows0001
theorem goodCompose00_000_0 : GoodBlock representatives rowsCompose00_000_0 127 9698 2048 :=
  good0000.append good0001 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_1 : List Row := rows0002 ++ rows0003
theorem goodCompose00_000_1 : GoodBlock representatives rowsCompose00_000_1 9698 19222 2048 :=
  good0002.append good0003 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_2 : List Row := rowsCompose00_000_0 ++ rowsCompose00_000_1
theorem goodCompose00_000_2 : GoodBlock representatives rowsCompose00_000_2 127 19222 4096 :=
  goodCompose00_000_0.append goodCompose00_000_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_3 : List Row := rows0004 ++ rows0005
theorem goodCompose00_000_3 : GoodBlock representatives rowsCompose00_000_3 19222 29570 2048 :=
  good0004.append good0005 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_4 : List Row := rows0006 ++ rows0007
theorem goodCompose00_000_4 : GoodBlock representatives rowsCompose00_000_4 29570 41172 2048 :=
  good0006.append good0007 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_5 : List Row := rowsCompose00_000_3 ++ rowsCompose00_000_4
theorem goodCompose00_000_5 : GoodBlock representatives rowsCompose00_000_5 19222 41172 4096 :=
  goodCompose00_000_3.append goodCompose00_000_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_6 : List Row := rowsCompose00_000_2 ++ rowsCompose00_000_5
theorem goodCompose00_000_6 : GoodBlock representatives rowsCompose00_000_6 127 41172 8192 :=
  goodCompose00_000_2.append goodCompose00_000_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_7 : List Row := rows0008 ++ rows0009
theorem goodCompose00_000_7 : GoodBlock representatives rowsCompose00_000_7 41173 53300 2048 :=
  good0008.append good0009 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_8 : List Row := rows0010 ++ rows0011
theorem goodCompose00_000_8 : GoodBlock representatives rowsCompose00_000_8 53301 69146 2048 :=
  good0010.append good0011 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_9 : List Row := rowsCompose00_000_7 ++ rowsCompose00_000_8
theorem goodCompose00_000_9 : GoodBlock representatives rowsCompose00_000_9 41173 69146 4096 :=
  goodCompose00_000_7.append goodCompose00_000_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_10 : List Row := rows0012 ++ rows0013
theorem goodCompose00_000_10 : GoodBlock representatives rowsCompose00_000_10 69146 80134 2048 :=
  good0012.append good0013 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_11 : List Row := rows0014 ++ rows0015
theorem goodCompose00_000_11 : GoodBlock representatives rowsCompose00_000_11 80134 95749 2048 :=
  good0014.append good0015 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_12 : List Row := rowsCompose00_000_10 ++ rowsCompose00_000_11
theorem goodCompose00_000_12 : GoodBlock representatives rowsCompose00_000_12 69146 95749 4096 :=
  goodCompose00_000_10.append goodCompose00_000_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_13 : List Row := rowsCompose00_000_9 ++ rowsCompose00_000_12
theorem goodCompose00_000_13 : GoodBlock representatives rowsCompose00_000_13 41173 95749 8192 :=
  goodCompose00_000_9.append goodCompose00_000_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_000_14 : List Row := rowsCompose00_000_6 ++ rowsCompose00_000_13
theorem goodCompose00_000_14 : GoodBlock representatives rowsCompose00_000_14 127 95749 16384 :=
  goodCompose00_000_6.append goodCompose00_000_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_000_14
