import Sq17Lean.OrbitCensus.Chunk0208
import Sq17Lean.OrbitCensus.Chunk0209
import Sq17Lean.OrbitCensus.Chunk0210
import Sq17Lean.OrbitCensus.Chunk0211
import Sq17Lean.OrbitCensus.Chunk0212
import Sq17Lean.OrbitCensus.Chunk0213
import Sq17Lean.OrbitCensus.Chunk0214
import Sq17Lean.OrbitCensus.Chunk0215
import Sq17Lean.OrbitCensus.Chunk0216
import Sq17Lean.OrbitCensus.Chunk0217
import Sq17Lean.OrbitCensus.Chunk0218
import Sq17Lean.OrbitCensus.Chunk0219
import Sq17Lean.OrbitCensus.Chunk0220
import Sq17Lean.OrbitCensus.Chunk0221
import Sq17Lean.OrbitCensus.Chunk0222
import Sq17Lean.OrbitCensus.Chunk0223

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_013_0 : List Row := rows0208 ++ rows0209
theorem goodCompose00_013_0 : GoodBlock representatives rowsCompose00_013_0 5281936 5341198 2048 :=
  good0208.append good0209 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_1 : List Row := rows0210 ++ rows0211
theorem goodCompose00_013_1 : GoodBlock representatives rowsCompose00_013_1 5341198 5410850 2048 :=
  good0210.append good0211 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_2 : List Row := rowsCompose00_013_0 ++ rowsCompose00_013_1
theorem goodCompose00_013_2 : GoodBlock representatives rowsCompose00_013_2 5281936 5410850 4096 :=
  goodCompose00_013_0.append goodCompose00_013_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_3 : List Row := rows0212 ++ rows0213
theorem goodCompose00_013_3 : GoodBlock representatives rowsCompose00_013_3 5410850 5526081 2048 :=
  good0212.append good0213 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_4 : List Row := rows0214 ++ rows0215
theorem goodCompose00_013_4 : GoodBlock representatives rowsCompose00_013_4 5526144 5768338 2048 :=
  good0214.append good0215 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_5 : List Row := rowsCompose00_013_3 ++ rowsCompose00_013_4
theorem goodCompose00_013_5 : GoodBlock representatives rowsCompose00_013_5 5410850 5768338 4096 :=
  goodCompose00_013_3.append goodCompose00_013_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_6 : List Row := rowsCompose00_013_2 ++ rowsCompose00_013_5
theorem goodCompose00_013_6 : GoodBlock representatives rowsCompose00_013_6 5281936 5768338 8192 :=
  goodCompose00_013_2.append goodCompose00_013_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_7 : List Row := rows0216 ++ rows0217
theorem goodCompose00_013_7 : GoodBlock representatives rowsCompose00_013_7 5768338 5865609 2048 :=
  good0216.append good0217 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_8 : List Row := rows0218 ++ rows0219
theorem goodCompose00_013_8 : GoodBlock representatives rowsCompose00_013_8 5865616 6293556 2048 :=
  good0218.append good0219 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_9 : List Row := rowsCompose00_013_7 ++ rowsCompose00_013_8
theorem goodCompose00_013_9 : GoodBlock representatives rowsCompose00_013_9 5768338 6293556 4096 :=
  goodCompose00_013_7.append goodCompose00_013_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_10 : List Row := rows0220 ++ rows0221
theorem goodCompose00_013_10 : GoodBlock representatives rowsCompose00_013_10 6293557 6312007 2048 :=
  good0220.append good0221 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_11 : List Row := rows0222 ++ rows0223
theorem goodCompose00_013_11 : GoodBlock representatives rowsCompose00_013_11 6312009 6357829 2048 :=
  good0222.append good0223 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_12 : List Row := rowsCompose00_013_10 ++ rowsCompose00_013_11
theorem goodCompose00_013_12 : GoodBlock representatives rowsCompose00_013_12 6293557 6357829 4096 :=
  goodCompose00_013_10.append goodCompose00_013_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_13 : List Row := rowsCompose00_013_9 ++ rowsCompose00_013_12
theorem goodCompose00_013_13 : GoodBlock representatives rowsCompose00_013_13 5768338 6357829 8192 :=
  goodCompose00_013_9.append goodCompose00_013_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_013_14 : List Row := rowsCompose00_013_6 ++ rowsCompose00_013_13
theorem goodCompose00_013_14 : GoodBlock representatives rowsCompose00_013_14 5281936 6357829 16384 :=
  goodCompose00_013_6.append goodCompose00_013_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_013_14
