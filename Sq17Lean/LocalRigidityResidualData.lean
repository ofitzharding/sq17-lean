import Sq17Lean.LocalResidual.Chunk000
import Sq17Lean.LocalResidual.Chunk001
import Sq17Lean.LocalResidual.Chunk002
import Sq17Lean.LocalResidual.Chunk003
import Sq17Lean.LocalResidual.Chunk004
import Sq17Lean.LocalResidual.Chunk005
import Sq17Lean.LocalResidual.Chunk006
import Sq17Lean.LocalResidual.Chunk007
import Sq17Lean.LocalResidual.Chunk008
import Sq17Lean.LocalResidual.Chunk009
import Sq17Lean.LocalResidual.Chunk010
import Sq17Lean.LocalResidual.Chunk011
import Sq17Lean.LocalResidual.Chunk012
import Sq17Lean.LocalResidual.Chunk013
import Sq17Lean.LocalResidual.Chunk014
import Sq17Lean.LocalResidual.Chunk015
import Sq17Lean.LocalResidual.Chunk016
import Sq17Lean.LocalResidual.Chunk017
import Sq17Lean.LocalResidual.Chunk018
import Sq17Lean.LocalResidual.Chunk019
import Sq17Lean.LocalResidual.Chunk020
import Sq17Lean.LocalResidual.Chunk021
import Sq17Lean.LocalResidual.Chunk022
import Sq17Lean.LocalResidual.Chunk023
import Sq17Lean.LocalResidual.Chunk024
import Sq17Lean.LocalResidual.Chunk025
import Sq17Lean.LocalResidual.Chunk026
import Sq17Lean.LocalResidual.Chunk027
import Sq17Lean.LocalResidual.Chunk028
import Sq17Lean.LocalResidual.Chunk029
import Sq17Lean.LocalResidual.Chunk030
import Sq17Lean.LocalResidual.Chunk031
import Sq17Lean.LocalResidual.Chunk032
import Sq17Lean.LocalResidual.Chunk033
import Sq17Lean.LocalResidual.Chunk034
import Sq17Lean.LocalResidual.Chunk035
import Sq17Lean.LocalResidual.Chunk036
import Sq17Lean.LocalResidual.Chunk037
import Sq17Lean.LocalResidual.Chunk038
import Sq17Lean.LocalResidual.Chunk039
import Sq17Lean.LocalResidual.Chunk040
import Sq17Lean.LocalResidual.Chunk041
import Sq17Lean.LocalResidual.Chunk042
import Sq17Lean.LocalResidual.Chunk043
import Sq17Lean.LocalResidual.Chunk044
import Sq17Lean.LocalResidual.Chunk045
import Sq17Lean.LocalResidual.Chunk046
import Sq17Lean.LocalResidual.Chunk047
import Sq17Lean.LocalResidual.Chunk048
import Sq17Lean.LocalResidual.Chunk049
import Sq17Lean.LocalResidual.Chunk050
import Sq17Lean.LocalResidual.Chunk051
import Sq17Lean.LocalResidual.Chunk052
import Sq17Lean.LocalResidual.Chunk053
import Sq17Lean.LocalResidual.Chunk054
import Sq17Lean.LocalResidual.Chunk055
import Sq17Lean.LocalResidual.Chunk056
import Sq17Lean.LocalResidual.Chunk057
import Sq17Lean.LocalResidual.Chunk058
import Sq17Lean.LocalResidual.Chunk059
import Sq17Lean.LocalResidual.Chunk060
import Sq17Lean.LocalResidual.Chunk061
import Sq17Lean.LocalResidual.Chunk062
import Sq17Lean.LocalResidual.Chunk063
import Sq17Lean.LocalResidual.Chunk064
import Sq17Lean.LocalResidual.Chunk065
import Sq17Lean.LocalResidual.Chunk066
import Sq17Lean.LocalResidual.Chunk067
import Sq17Lean.LocalResidual.Chunk068
import Sq17Lean.LocalResidual.Chunk069
import Sq17Lean.LocalResidual.Chunk070
import Sq17Lean.LocalResidual.Chunk071
import Sq17Lean.LocalResidual.Chunk072
import Sq17Lean.LocalResidual.Chunk073
import Sq17Lean.LocalResidual.Chunk074
import Sq17Lean.LocalResidual.Chunk075
import Sq17Lean.LocalResidual.Chunk076
import Sq17Lean.LocalResidual.Chunk077
import Sq17Lean.LocalResidual.Chunk078
import Sq17Lean.LocalResidual.Chunk079
import Sq17Lean.LocalResidual.Chunk080
import Sq17Lean.LocalResidual.Chunk081
import Sq17Lean.LocalResidual.Chunk082
import Sq17Lean.LocalResidual.Chunk083
import Sq17Lean.LocalResidual.Chunk084
import Sq17Lean.LocalResidual.Chunk085
import Sq17Lean.LocalResidual.Chunk086
import Sq17Lean.LocalResidual.Chunk087
import Sq17Lean.LocalResidual.Chunk088
import Sq17Lean.LocalResidual.Chunk089
import Sq17Lean.LocalResidual.Chunk090
import Sq17Lean.LocalResidual.Chunk091
import Sq17Lean.LocalResidual.Chunk092

namespace Sq17.LocalRigidity.ResidualData
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
theorem accepted (i : Fin 93) : sparseResidualCheck bounds support (WeightData.boxes i) (mid i) (target i) = true := by
  fin_cases i
  · exact accepted000
  · exact accepted001
  · exact accepted002
  · exact accepted003
  · exact accepted004
  · exact accepted005
  · exact accepted006
  · exact accepted007
  · exact accepted008
  · exact accepted009
  · exact accepted010
  · exact accepted011
  · exact accepted012
  · exact accepted013
  · exact accepted014
  · exact accepted015
  · exact accepted016
  · exact accepted017
  · exact accepted018
  · exact accepted019
  · exact accepted020
  · exact accepted021
  · exact accepted022
  · exact accepted023
  · exact accepted024
  · exact accepted025
  · exact accepted026
  · exact accepted027
  · exact accepted028
  · exact accepted029
  · exact accepted030
  · exact accepted031
  · exact accepted032
  · exact accepted033
  · exact accepted034
  · exact accepted035
  · exact accepted036
  · exact accepted037
  · exact accepted038
  · exact accepted039
  · exact accepted040
  · exact accepted041
  · exact accepted042
  · exact accepted043
  · exact accepted044
  · exact accepted045
  · exact accepted046
  · exact accepted047
  · exact accepted048
  · exact accepted049
  · exact accepted050
  · exact accepted051
  · exact accepted052
  · exact accepted053
  · exact accepted054
  · exact accepted055
  · exact accepted056
  · exact accepted057
  · exact accepted058
  · exact accepted059
  · exact accepted060
  · exact accepted061
  · exact accepted062
  · exact accepted063
  · exact accepted064
  · exact accepted065
  · exact accepted066
  · exact accepted067
  · exact accepted068
  · exact accepted069
  · exact accepted070
  · exact accepted071
  · exact accepted072
  · exact accepted073
  · exact accepted074
  · exact accepted075
  · exact accepted076
  · exact accepted077
  · exact accepted078
  · exact accepted079
  · exact accepted080
  · exact accepted081
  · exact accepted082
  · exact accepted083
  · exact accepted084
  · exact accepted085
  · exact accepted086
  · exact accepted087
  · exact accepted088
  · exact accepted089
  · exact accepted090
  · exact accepted091
  · exact accepted092
end Sq17.LocalRigidity.ResidualData
#print axioms Sq17.LocalRigidity.ResidualData.accepted
