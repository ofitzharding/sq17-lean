import Sq17Lean.OrbitCensus.Chunk0256
import Sq17Lean.OrbitCensus.Chunk0257
import Sq17Lean.OrbitCensus.Chunk0258
import Sq17Lean.OrbitCensus.Chunk0259
import Sq17Lean.OrbitCensus.Chunk0260
import Sq17Lean.OrbitCensus.Chunk0261
import Sq17Lean.OrbitCensus.Chunk0262
import Sq17Lean.OrbitCensus.Chunk0263
import Sq17Lean.OrbitCensus.Chunk0264
import Sq17Lean.OrbitCensus.Chunk0265
import Sq17Lean.OrbitCensus.Chunk0266
import Sq17Lean.OrbitCensus.Chunk0267
import Sq17Lean.OrbitCensus.Chunk0268
import Sq17Lean.OrbitCensus.Chunk0269
import Sq17Lean.OrbitCensus.Chunk0270
import Sq17Lean.OrbitCensus.Chunk0271

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_016_0 : List Row := rows0256 ++ rows0257
theorem goodCompose00_016_0 : GoodBlock representatives rowsCompose00_016_0 8586344 8652847 2048 :=
  good0256.append good0257 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_1 : List Row := rows0258 ++ rows0259
theorem goodCompose00_016_1 : GoodBlock representatives rowsCompose00_016_1 8652851 8671302 2048 :=
  good0258.append good0259 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_2 : List Row := rowsCompose00_016_0 ++ rowsCompose00_016_1
theorem goodCompose00_016_2 : GoodBlock representatives rowsCompose00_016_2 8586344 8671302 4096 :=
  goodCompose00_016_0.append goodCompose00_016_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_3 : List Row := rows0260 ++ rows0261
theorem goodCompose00_016_3 : GoodBlock representatives rowsCompose00_016_3 8671302 8717123 2048 :=
  good0260.append good0261 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_4 : List Row := rows0262 ++ rows0263
theorem goodCompose00_016_4 : GoodBlock representatives rowsCompose00_016_4 8717124 8784421 2048 :=
  good0262.append good0263 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_5 : List Row := rowsCompose00_016_3 ++ rowsCompose00_016_4
theorem goodCompose00_016_5 : GoodBlock representatives rowsCompose00_016_5 8671302 8784421 4096 :=
  goodCompose00_016_3.append goodCompose00_016_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_6 : List Row := rowsCompose00_016_2 ++ rowsCompose00_016_5
theorem goodCompose00_016_6 : GoodBlock representatives rowsCompose00_016_6 8586344 8784421 8192 :=
  goodCompose00_016_2.append goodCompose00_016_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_7 : List Row := rows0264 ++ rows0265
theorem goodCompose00_016_7 : GoodBlock representatives rowsCompose00_016_7 8784424 8913295 2048 :=
  good0264.append good0265 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_8 : List Row := rows0266 ++ rows0267
theorem goodCompose00_016_8 : GoodBlock representatives rowsCompose00_016_8 8913299 8929835 2048 :=
  good0266.append good0267 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_9 : List Row := rowsCompose00_016_7 ++ rowsCompose00_016_8
theorem goodCompose00_016_9 : GoodBlock representatives rowsCompose00_016_9 8784424 8929835 4096 :=
  goodCompose00_016_7.append goodCompose00_016_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_10 : List Row := rows0268 ++ rows0269
theorem goodCompose00_016_10 : GoodBlock representatives rowsCompose00_016_10 8929836 8964226 2048 :=
  good0268.append good0269 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_11 : List Row := rows0270 ++ rows0271
theorem goodCompose00_016_11 : GoodBlock representatives rowsCompose00_016_11 8964226 9044141 2048 :=
  good0270.append good0271 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_12 : List Row := rowsCompose00_016_10 ++ rowsCompose00_016_11
theorem goodCompose00_016_12 : GoodBlock representatives rowsCompose00_016_12 8929836 9044141 4096 :=
  goodCompose00_016_10.append goodCompose00_016_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_13 : List Row := rowsCompose00_016_9 ++ rowsCompose00_016_12
theorem goodCompose00_016_13 : GoodBlock representatives rowsCompose00_016_13 8784424 9044141 8192 :=
  goodCompose00_016_9.append goodCompose00_016_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_016_14 : List Row := rowsCompose00_016_6 ++ rowsCompose00_016_13
theorem goodCompose00_016_14 : GoodBlock representatives rowsCompose00_016_14 8586344 9044141 16384 :=
  goodCompose00_016_6.append goodCompose00_016_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_016_14
