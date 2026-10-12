import Sq17Lean.OrbitCensus.Chunk0048
import Sq17Lean.OrbitCensus.Chunk0049
import Sq17Lean.OrbitCensus.Chunk0050
import Sq17Lean.OrbitCensus.Chunk0051
import Sq17Lean.OrbitCensus.Chunk0052
import Sq17Lean.OrbitCensus.Chunk0053
import Sq17Lean.OrbitCensus.Chunk0054
import Sq17Lean.OrbitCensus.Chunk0055
import Sq17Lean.OrbitCensus.Chunk0056
import Sq17Lean.OrbitCensus.Chunk0057
import Sq17Lean.OrbitCensus.Chunk0058
import Sq17Lean.OrbitCensus.Chunk0059
import Sq17Lean.OrbitCensus.Chunk0060
import Sq17Lean.OrbitCensus.Chunk0061
import Sq17Lean.OrbitCensus.Chunk0062
import Sq17Lean.OrbitCensus.Chunk0063

namespace Sq17.OrbitCensus
open Sq17.FiniteOrbitCover
open Sq17.OrbitFiniteData

noncomputable def rowsCompose00_003_0 : List Row := rows0048 ++ rows0049
theorem goodCompose00_003_0 : GoodBlock representatives rowsCompose00_003_0 463372 527699 2048 :=
  good0048.append good0049 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_1 : List Row := rows0050 ++ rows0051
theorem goodCompose00_003_1 : GoodBlock representatives rowsCompose00_003_1 527700 538694 2048 :=
  good0050.append good0051 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_2 : List Row := rowsCompose00_003_0 ++ rowsCompose00_003_1
theorem goodCompose00_003_2 : GoodBlock representatives rowsCompose00_003_2 463372 538694 4096 :=
  goodCompose00_003_0.append goodCompose00_003_1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_3 : List Row := rows0052 ++ rows0053
theorem goodCompose00_003_3 : GoodBlock representatives rowsCompose00_003_3 538694 553991 2048 :=
  good0052.append good0053 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_4 : List Row := rows0054 ++ rows0055
theorem goodCompose00_003_4 : GoodBlock representatives rowsCompose00_003_4 553993 571402 2048 :=
  good0054.append good0055 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_5 : List Row := rowsCompose00_003_3 ++ rowsCompose00_003_4
theorem goodCompose00_003_5 : GoodBlock representatives rowsCompose00_003_5 538694 571402 4096 :=
  goodCompose00_003_3.append goodCompose00_003_4 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_6 : List Row := rowsCompose00_003_2 ++ rowsCompose00_003_5
theorem goodCompose00_003_6 : GoodBlock representatives rowsCompose00_003_6 463372 571402 8192 :=
  goodCompose00_003_2.append goodCompose00_003_5 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_7 : List Row := rows0056 ++ rows0057
theorem goodCompose00_003_7 : GoodBlock representatives rowsCompose00_003_7 571402 594818 2048 :=
  good0056.append good0057 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_8 : List Row := rows0058 ++ rows0059
theorem goodCompose00_003_8 : GoodBlock representatives rowsCompose00_003_8 594818 622742 2048 :=
  good0058.append good0059 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_9 : List Row := rowsCompose00_003_7 ++ rowsCompose00_003_8
theorem goodCompose00_003_9 : GoodBlock representatives rowsCompose00_003_9 571402 622742 4096 :=
  goodCompose00_003_7.append goodCompose00_003_8 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_10 : List Row := rows0060 ++ rows0061
theorem goodCompose00_003_10 : GoodBlock representatives rowsCompose00_003_10 622742 658627 2048 :=
  good0060.append good0061 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_11 : List Row := rows0062 ++ rows0063
theorem goodCompose00_003_11 : GoodBlock representatives rowsCompose00_003_11 658628 680145 2048 :=
  good0062.append good0063 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_12 : List Row := rowsCompose00_003_10 ++ rowsCompose00_003_11
theorem goodCompose00_003_12 : GoodBlock representatives rowsCompose00_003_12 622742 680145 4096 :=
  goodCompose00_003_10.append goodCompose00_003_11 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_13 : List Row := rowsCompose00_003_9 ++ rowsCompose00_003_12
theorem goodCompose00_003_13 : GoodBlock representatives rowsCompose00_003_13 571402 680145 8192 :=
  goodCompose00_003_9.append goodCompose00_003_12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

noncomputable def rowsCompose00_003_14 : List Row := rowsCompose00_003_6 ++ rowsCompose00_003_13
theorem goodCompose00_003_14 : GoodBlock representatives rowsCompose00_003_14 463372 680145 16384 :=
  goodCompose00_003_6.append goodCompose00_003_13 (by decide +kernel) (by decide +kernel) (by decide +kernel)

end Sq17.OrbitCensus

#print axioms Sq17.OrbitCensus.goodCompose00_003_14
