import Sq17Lean.OrbitCensus.Chunk0176
import Sq17Lean.OrbitCensus.Chunk0177
import Sq17Lean.OrbitCensus.Chunk0178
import Sq17Lean.OrbitCensus.Chunk0179
import Sq17Lean.OrbitCensus.Chunk0180
import Sq17Lean.OrbitCensus.Chunk0181
import Sq17Lean.OrbitCensus.Chunk0182
import Sq17Lean.OrbitCensus.Chunk0183
import Sq17Lean.OrbitCensus.Chunk0184
import Sq17Lean.OrbitCensus.Chunk0185
import Sq17Lean.OrbitCensus.Chunk0186
import Sq17Lean.OrbitCensus.Chunk0187
import Sq17Lean.OrbitCensus.Chunk0188
import Sq17Lean.OrbitCensus.Chunk0189
import Sq17Lean.OrbitCensus.Chunk0190
import Sq17Lean.OrbitCensus.Chunk0191

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_011_0 : List Row := rows0176 ++ rows0177
theorem goodCompose00_011_0 : GoodBlock representatives rowsCompose00_011_0 4270304 4300812 2048 :=
  good0176.append good0177 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_1 : List Row := rows0178 ++ rows0179
theorem goodCompose00_011_1 : GoodBlock representatives rowsCompose00_011_1 4300813 4333971 2048 :=
  good0178.append good0179 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_2 : List Row := rowsCompose00_011_0 ++ rowsCompose00_011_1
theorem goodCompose00_011_2 : GoodBlock representatives rowsCompose00_011_2 4270304 4333971 4096 :=
  goodCompose00_011_0.append goodCompose00_011_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_3 : List Row := rows0180 ++ rows0181
theorem goodCompose00_011_3 : GoodBlock representatives rowsCompose00_011_3 4333972 4360965 2048 :=
  good0180.append good0181 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_4 : List Row := rows0182 ++ rows0183
theorem goodCompose00_011_4 : GoodBlock representatives rowsCompose00_011_4 4360968 4408338 2048 :=
  good0182.append good0183 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_5 : List Row := rowsCompose00_011_3 ++ rowsCompose00_011_4
theorem goodCompose00_011_5 : GoodBlock representatives rowsCompose00_011_5 4333972 4408338 4096 :=
  goodCompose00_011_3.append goodCompose00_011_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_6 : List Row := rowsCompose00_011_2 ++ rowsCompose00_011_5
theorem goodCompose00_011_6 : GoodBlock representatives rowsCompose00_011_6 4270304 4408338 8192 :=
  goodCompose00_011_2.append goodCompose00_011_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_7 : List Row := rows0184 ++ rows0185
theorem goodCompose00_011_7 : GoodBlock representatives rowsCompose00_011_7 4408338 4464873 2048 :=
  good0184.append good0185 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_8 : List Row := rows0186 ++ rows0187
theorem goodCompose00_011_8 : GoodBlock representatives rowsCompose00_011_8 4464880 4491569 2048 :=
  good0186.append good0187 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_9 : List Row := rowsCompose00_011_7 ++ rowsCompose00_011_8
theorem goodCompose00_011_9 : GoodBlock representatives rowsCompose00_011_9 4408338 4491569 4096 :=
  goodCompose00_011_7.append goodCompose00_011_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_10 : List Row := rows0188 ++ rows0189
theorem goodCompose00_011_10 : GoodBlock representatives rowsCompose00_011_10 4491585 4538785 2048 :=
  good0188.append good0189 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_11 : List Row := rows0190 ++ rows0191
theorem goodCompose00_011_11 : GoodBlock representatives rowsCompose00_011_11 4538816 4612233 2048 :=
  good0190.append good0191 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_12 : List Row := rowsCompose00_011_10 ++ rowsCompose00_011_11
theorem goodCompose00_011_12 : GoodBlock representatives rowsCompose00_011_12 4491585 4612233 4096 :=
  goodCompose00_011_10.append goodCompose00_011_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_13 : List Row := rowsCompose00_011_9 ++ rowsCompose00_011_12
theorem goodCompose00_011_13 : GoodBlock representatives rowsCompose00_011_13 4408338 4612233 8192 :=
  goodCompose00_011_9.append goodCompose00_011_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_011_14 : List Row := rowsCompose00_011_6 ++ rowsCompose00_011_13
theorem goodCompose00_011_14 : GoodBlock representatives rowsCompose00_011_14 4270304 4612233 16384 :=
  goodCompose00_011_6.append goodCompose00_011_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_011_14
