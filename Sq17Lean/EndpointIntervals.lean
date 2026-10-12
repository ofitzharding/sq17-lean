import Sq17Lean.EndpointGeometry
import Sq17Lean.RationalExpression

namespace Sq17.EndpointIntervals
open Sq17.EndpointGeometry Sq17.RationalExpression
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def tRange : Interval := ⟨(362043893313323383453621978739944164218293243036741520638379/1000000000000000000000000000000000000000000000000000000000000),(362043893315323383453621978739944164218293243036741520638379/1000000000000000000000000000000000000000000000000000000000000)⟩
def betaRange : Interval := ⟨(330948674721739910429808533282915634174672003999685385633441/1000000000000000000000000000000000000000000000000000000000000),(330948674723739910429808533282915634174672003999685385633441/1000000000000000000000000000000000000000000000000000000000000)⟩
theorem t_holds : tRange.Holds t := by
  have h := abs_le.mp root_bounds.1
  norm_num [tRange,Interval.Holds,EndpointRoot.midpoint,EndpointRoot.radius] at *
  constructor <;> linarith
theorem beta_holds : betaRange.Holds beta := by
  have h := abs_le.mp root_bounds.2
  norm_num [betaRange,Interval.Holds,EndpointRoot.midpoint,EndpointRoot.radius] at *
  constructor <;> linarith

def cCert : Cert := (.mul ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.add ⟨(21723105482827/25000000000000),(43446210965727/50000000000000)⟩ (.constant 1) (.neg ⟨(-3276894517173/25000000000000),(-6553789034273/50000000000000)⟩ (.mul ⟨(6553789034273/50000000000000),(3276894517173/25000000000000)⟩ .x .x))) (.inv ⟨(88411405944231/100000000000000),(44205702972173/50000000000000)⟩ (.add ⟨(56553789034273/50000000000000),(28276894517173/25000000000000)⟩ (.mul ⟨(6553789034273/50000000000000),(3276894517173/25000000000000)⟩ .x .x) (.constant 1))))
theorem c_eval : cCert.eval t beta = c := by
  simp only [cCert,Cert.eval,c,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem c_checked : cCert.check tRange betaRange = true := by decide +kernel
theorem c_bounds : (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (c) := by
  have h := Cert.check_sound tRange betaRange cCert t beta t_holds beta_holds c_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (cCert.eval t beta) at h
  simpa only [c_eval] using h

def sCert : Cert := (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨(9051097332833/12500000000000),(14481755732613/20000000000000)⟩ .x (.constant 2)) (.inv ⟨(88411405944231/100000000000000),(44205702972173/50000000000000)⟩ (.add ⟨(56553789034273/50000000000000),(28276894517173/25000000000000)⟩ (.mul ⟨(6553789034273/50000000000000),(3276894517173/25000000000000)⟩ .x .x) (.constant 1))))
theorem s_eval : sCert.eval t beta = s := by
  simp only [sCert,Cert.eval,c_eval,s,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem s_checked : sCert.check tRange betaRange = true := by decide +kernel
theorem s_bounds : (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (s) := by
  have h := Cert.check_sound tRange betaRange sCert t beta t_holds beta_holds s_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (sCert.eval t beta) at h
  simpa only [s_eval] using h

def dCert : Cert := (.mul ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ (.add ⟨(4452364873493/5000000000000),(89047297469993/100000000000000)⟩ (.constant 1) (.neg ⟨(-547635126507/5000000000000),(-10952702530007/100000000000000)⟩ (.mul ⟨(10952702530007/100000000000000),(547635126507/5000000000000)⟩ .y .y))) (.inv ⟨(45064247070879/50000000000000),(90128494141867/100000000000000)⟩ (.add ⟨(110952702530007/100000000000000),(5547635126507/5000000000000)⟩ (.mul ⟨(10952702530007/100000000000000),(547635126507/5000000000000)⟩ .y .y) (.constant 1))))
theorem d_eval : dCert.eval t beta = d := by
  simp only [dCert,Cert.eval,c_eval,s_eval,d,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem d_checked : dCert.check tRange betaRange = true := by decide +kernel
theorem d_bounds : (⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ : Interval).Holds (d) := by
  have h := Cert.check_sound tRange betaRange dCert t beta t_holds beta_holds d_checked
  change (⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ : Interval).Holds (dCert.eval t beta) at h
  simpa only [d_eval] using h

def eCert : Cert := (.mul ⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ (.mul ⟨(66189734944347/100000000000000),(16547433736187/25000000000000)⟩ .y (.constant 2)) (.inv ⟨(45064247070879/50000000000000),(90128494141867/100000000000000)⟩ (.add ⟨(110952702530007/100000000000000),(5547635126507/5000000000000)⟩ (.mul ⟨(10952702530007/100000000000000),(547635126507/5000000000000)⟩ .y .y) (.constant 1))))
theorem e_eval : eCert.eval t beta = e := by
  simp only [eCert,Cert.eval,c_eval,s_eval,d_eval,e,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem e_checked : eCert.check tRange betaRange = true := by decide +kernel
theorem e_bounds : (⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ : Interval).Holds (e) := by
  have h := Cert.check_sound tRange betaRange eCert t beta t_holds beta_holds e_checked
  change (⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ : Interval).Holds (eCert.eval t beta) at h
  simpa only [e_eval] using h

def sideCert : Cert := (.mul ⟨(233776504679697/50000000000000),(233776504680757/50000000000000)⟩ (.add ⟨(744817557325329/100000000000000),(74481755732613/10000000000000)⟩ (.mul ⟨(144817557325329/100000000000000),(14481755732613/10000000000000)⟩ .x (.constant 4)) (.constant 6)) (.inv ⟨(31387082968237/50000000000000),(62774165936691/100000000000000)⟩ (.add ⟨(39825300148493/25000000000000),(159301200594519/100000000000000)⟩ (.add ⟨(21551097332833/12500000000000),(34481755732613/20000000000000)⟩ (.mul ⟨(9051097332833/12500000000000),(14481755732613/20000000000000)⟩ .x (.constant 2)) (.constant 1)) (.neg ⟨(-3276894517173/25000000000000),(-6553789034273/50000000000000)⟩ (.mul ⟨(6553789034273/50000000000000),(3276894517173/25000000000000)⟩ .x .x)))))
theorem side_eval : sideCert.eval t beta = side := by
  simp only [sideCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem side_checked : sideCert.check tRange betaRange = true := by decide +kernel
theorem side_bounds : (⟨(233776504679697/50000000000000),(233776504680757/50000000000000)⟩ : Interval).Holds (side) := by
  have h := Cert.check_sound tRange betaRange sideCert t beta t_holds beta_holds side_checked
  change (⟨(233776504679697/50000000000000),(233776504680757/50000000000000)⟩ : Interval).Holds (sideCert.eval t beta) at h
  simpa only [side_eval] using h

def hCert : Cert := (.mul ⟨(4401263472849/6250000000000),(70420215565919/100000000000000)⟩ (.add ⟨(140840431131169/100000000000000),(70420215565919/50000000000000)⟩ cCert sCert) (.inv ⟨(1/2),(1/2)⟩ (.constant 2)))
theorem h_eval : hCert.eval t beta = h := by
  simp only [hCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem h_checked : hCert.check tRange betaRange = true := by decide +kernel
theorem h_bounds : (⟨(4401263472849/6250000000000),(70420215565919/100000000000000)⟩ : Interval).Holds (h) := by
  have h := Cert.check_sound tRange betaRange hCert t beta t_holds beta_holds h_checked
  change (⟨(4401263472849/6250000000000),(70420215565919/100000000000000)⟩ : Interval).Holds (hCert.eval t beta) at h
  simpa only [h_eval] using h

def XCert : Cert := (.add ⟨(234732482647359/100000000000000),(2347324826547/1000000000000)⟩ (.mul ⟨(184732482647359/100000000000000),(1847324826547/1000000000000)⟩ (.add ⟨(35479171910373/25000000000000),(28383337529341/20000000000000)⟩ (.add ⟨(441232992934417/100000000000000),(22061649646811/5000000000000)⟩ (.add ⟨(31147516900787/12500000000000),(124590067603391/50000000000000)⟩ (.mul ⟨(6147516900787/12500000000000),(24590067603391/50000000000000)⟩ cCert sCert) (.constant 2)) (.mul ⟨(192052857728121/100000000000000),(96026428864719/50000000000000)⟩ sCert (.constant 3))) (.neg ⟨(-11972652211717/4000000000000),(-59863261057903/20000000000000)⟩ (.mul ⟨(59863261057903/20000000000000),(11972652211717/4000000000000)⟩ sCert sideCert))) (.inv ⟨(130169669062477/100000000000000),(32542417265717/25000000000000)⟩ cCert)) (.constant (1/2)))
theorem X_eval : XCert.eval t beta = X := by
  simp only [XCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem X_checked : XCert.check tRange betaRange = true := by decide +kernel
theorem X_bounds : (⟨(234732482647359/100000000000000),(2347324826547/1000000000000)⟩ : Interval).Holds (X) := by
  have h := Cert.check_sound tRange betaRange XCert t beta t_holds beta_holds X_checked
  change (⟨(234732482647359/100000000000000),(2347324826547/1000000000000)⟩ : Interval).Holds (XCert.eval t beta) at h
  simpa only [X_eval] using h

def YCert : Cert := (.add ⟨(261346013248223/100000000000000),(65336503313573/25000000000000)⟩ (.mul ⟨(111346013248223/100000000000000),(27836503313573/25000000000000)⟩ (.add ⟨(71281066803671/100000000000000),(35640533403533/50000000000000)⟩ (.add ⟨(215234217832693/50000000000000),(107617108916519/25000000000000)⟩ (.mul ⟨(115234217832693/50000000000000),(57617108916519/25000000000000)⟩ cCert (.constant 3)) (.constant 2)) (.neg ⟨(-71837473772343/20000000000000),(-35918736885901/10000000000000)⟩ (.mul ⟨(35918736885901/10000000000000),(71837473772343/20000000000000)⟩ cCert sideCert))) (.inv ⟨(156206996108663/100000000000000),(31241399221947/20000000000000)⟩ sCert)) (.constant (3/2)))
theorem Y_eval : YCert.eval t beta = Y := by
  simp only [YCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem Y_checked : YCert.check tRange betaRange = true := by decide +kernel
theorem Y_bounds : (⟨(261346013248223/100000000000000),(65336503313573/25000000000000)⟩ : Interval).Holds (Y) := by
  have h := Cert.check_sound tRange betaRange YCert t beta t_holds beta_holds Y_checked
  change (⟨(261346013248223/100000000000000),(65336503313573/25000000000000)⟩ : Interval).Holds (YCert.eval t beta) at h
  simpa only [Y_eval] using h

def ACert : Cert := (.add ⟨(7406373155421/12500000000000),(29625492626373/50000000000000)⟩ (.add ⟨(1156373155421/12500000000000),(4625492626373/50000000000000)⟩ (.mul ⟨(45703543047531/20000000000000),(28564714405521/12500000000000)⟩ dCert (.add ⟨(284732482647359/100000000000000),(2847324826547/1000000000000)⟩ XCert (.constant (1/2)))) (.neg ⟨(-219266729994287/100000000000000),(-109633364995711/50000000000000)⟩ (.mul ⟨(109633364995711/50000000000000),(219266729994287/100000000000000)⟩ eCert (.add ⟨(183776504679697/50000000000000),(183776504680757/50000000000000)⟩ sideCert (.neg ⟨-1,-1⟩ (.constant 1)))))) (.constant (1/2)))
theorem A_eval : ACert.eval t beta = A := by
  simp only [ACert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem A_checked : ACert.check tRange betaRange = true := by decide +kernel
theorem A_bounds : (⟨(7406373155421/12500000000000),(29625492626373/50000000000000)⟩ : Interval).Holds (A) := by
  have h := Cert.check_sound tRange betaRange ACert t beta t_holds beta_holds A_checked
  change (⟨(7406373155421/12500000000000),(29625492626373/50000000000000)⟩ : Interval).Holds (ACert.eval t beta) at h
  simpa only [A_eval] using h

def BCert : Cert := (.add ⟨(232126852824351/50000000000000),(464253705654069/100000000000000)⟩ (.mul ⟨(257126852824351/50000000000000),(514253705654069/100000000000000)⟩ (.add ⟨(34978199916319/25000000000000),(139912799665929/100000000000000)⟩ dCert eCert) (.add ⟨(183776504679697/50000000000000),(183776504680757/50000000000000)⟩ sideCert (.neg ⟨-1,-1⟩ (.constant 1)))) (.neg ⟨(-1/2),(-1/2)⟩ (.constant (1/2))))
theorem B_eval : BCert.eval t beta = B := by
  simp only [BCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem B_checked : BCert.check tRange betaRange = true := by decide +kernel
theorem B_bounds : (⟨(232126852824351/50000000000000),(464253705654069/100000000000000)⟩ : Interval).Holds (B) := by
  have h := Cert.check_sound tRange betaRange BCert t beta t_holds beta_holds B_checked
  change (⟨(232126852824351/50000000000000),(464253705654069/100000000000000)⟩ : Interval).Holds (BCert.eval t beta) at h
  simpa only [B_eval] using h

def u10Cert : Cert := (.add ⟨(32721537369171/10000000000000),(163607686846537/50000000000000)⟩ (.add ⟨(24897516900787/12500000000000),(99590067603391/50000000000000)⟩ (.mul ⟨(6147516900787/12500000000000),(24590067603391/50000000000000)⟩ cCert sCert) (.constant (3/2))) (.mul ⟨(64017619242707/50000000000000),(32008809621573/25000000000000)⟩ sCert (.constant 2)))
theorem u10_eval : u10Cert.eval t beta = u10 := by
  simp only [u10Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem u10_checked : u10Cert.check tRange betaRange = true := by decide +kernel
theorem u10_bounds : (⟨(32721537369171/10000000000000),(163607686846537/50000000000000)⟩ : Interval).Holds (u10) := by
  have h := Cert.check_sound tRange betaRange u10Cert t beta t_holds beta_holds u10_checked
  change (⟨(32721537369171/10000000000000),(163607686846537/50000000000000)⟩ : Interval).Holds (u10Cert.eval t beta) at h
  simpa only [u10_eval] using h

def v10Cert : Cert := (.add ⟨(84173468863701/50000000000000),(42086734432579/25000000000000)⟩ (.add ⟨(109173468863701/50000000000000),(54586734432579/25000000000000)⟩ (.mul ⟨(70591139242637/25000000000000),(282364556973023/100000000000000)⟩ cCert (.add ⟨(183776504679697/50000000000000),(183776504680757/50000000000000)⟩ sideCert (.neg ⟨-1,-1⟩ (.constant 1)))) (.neg ⟨(-32008809621573/50000000000000),(-64017619242707/100000000000000)⟩ sCert)) (.neg ⟨(-1/2),(-1/2)⟩ (.constant (1/2))))
theorem v10_eval : v10Cert.eval t beta = v10 := by
  simp only [v10Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem v10_checked : v10Cert.check tRange betaRange = true := by decide +kernel
theorem v10_bounds : (⟨(84173468863701/50000000000000),(42086734432579/25000000000000)⟩ : Interval).Holds (v10) := by
  have h := Cert.check_sound tRange betaRange v10Cert t beta t_holds beta_holds v10_checked
  change (⟨(84173468863701/50000000000000),(42086734432579/25000000000000)⟩ : Interval).Holds (v10Cert.eval t beta) at h
  simpa only [v10_eval] using h

def u11Cert : Cert := (.add ⟨(63714512593469/25000000000000),(31857256296873/12500000000000)⟩ (.add ⟨(51214512593469/25000000000000),(25607256296873/12500000000000)⟩ cCert (.mul ⟨(64017619242707/50000000000000),(32008809621573/25000000000000)⟩ sCert (.constant 2))) (.constant (1/2)))
theorem u11_eval : u11Cert.eval t beta = u11 := by
  simp only [u11Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem u11_checked : u11Cert.check tRange betaRange = true := by decide +kernel
theorem u11_bounds : (⟨(63714512593469/25000000000000),(31857256296873/12500000000000)⟩ : Interval).Holds (u11) := by
  have h := Cert.check_sound tRange betaRange u11Cert t beta t_holds beta_holds u11_checked
  change (⟨(63714512593469/25000000000000),(31857256296873/12500000000000)⟩ : Interval).Holds (u11Cert.eval t beta) at h
  simpa only [u11_eval] using h

def v11Cert : Cert := (.add ⟨(62663068041371/100000000000000),(6266306804229/10000000000000)⟩ (.add ⟨(162663068041371/100000000000000),(16266306804229/10000000000000)⟩ (.mul ⟨(38411405944231/25000000000000),(19205702972173/12500000000000)⟩ cCert (.constant 2)) (.mul ⟨(9017444264447/100000000000000),(4508722132453/50000000000000)⟩ (.add ⟨(3606977705779/20000000000000),(4508722132453/25000000000000)⟩ (.mul ⟨(118034888529/200000000000),(29508722132427/50000000000000)⟩ cCert cCert) (.neg ⟨(-8196511147121/20000000000000),(-20491277867521/50000000000000)⟩ (.mul ⟨(20491277867521/50000000000000),(8196511147121/20000000000000)⟩ sCert sCert))) (.inv ⟨(1/2),(1/2)⟩ (.constant 2)))) (.neg ⟨-1,-1⟩ (.constant 1)))
theorem v11_eval : v11Cert.eval t beta = v11 := by
  simp only [v11Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem v11_checked : v11Cert.check tRange betaRange = true := by decide +kernel
theorem v11_bounds : (⟨(62663068041371/100000000000000),(6266306804229/10000000000000)⟩ : Interval).Holds (v11) := by
  have h := Cert.check_sound tRange betaRange v11Cert t beta t_holds beta_holds v11_checked
  change (⟨(62663068041371/100000000000000),(6266306804229/10000000000000)⟩ : Interval).Holds (v11Cert.eval t beta) at h
  simpa only [v11_eval] using h

def u13Cert : Cert := (.add ⟨(267663243019631/100000000000000),(26766324302053/10000000000000)⟩ (.add ⟨(217663243019631/100000000000000),(21766324302053/10000000000000)⟩ (.mul ⟨(38411405944231/25000000000000),(19205702972173/12500000000000)⟩ cCert (.constant 2)) sCert) (.constant (1/2)))
theorem u13_eval : u13Cert.eval t beta = u13 := by
  simp only [u13Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem u13_checked : u13Cert.check tRange betaRange = true := by decide +kernel
theorem u13_bounds : (⟨(267663243019631/100000000000000),(26766324302053/10000000000000)⟩ : Interval).Holds (u13) := by
  have h := Cert.check_sound tRange betaRange u13Cert t beta t_holds beta_holds u13_checked
  change (⟨(267663243019631/100000000000000),(26766324302053/10000000000000)⟩ : Interval).Holds (u13Cert.eval t beta) at h
  simpa only [u13_eval] using h

def TCert : Cert := (.mul ⟨(7121322957709/100000000000000),(445082684971/6250000000000)⟩ cCert (.add ⟨(2317450631737/25000000000000),(4634901264649/50000000000000)⟩ (.add ⟨(238411405944231/50000000000000),(119205702972173/25000000000000)⟩ cCert (.constant 4)) (.neg ⟨(-233776504680757/50000000000000),(-233776504679697/50000000000000)⟩ sideCert)))
theorem T_eval : TCert.eval t beta = T := by
  simp only [TCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem T_checked : TCert.check tRange betaRange = true := by decide +kernel
theorem T_bounds : (⟨(7121322957709/100000000000000),(445082684971/6250000000000)⟩ : Interval).Holds (T) := by
  have h := Cert.check_sound tRange betaRange TCert t beta t_holds beta_holds T_checked
  change (⟨(7121322957709/100000000000000),(445082684971/6250000000000)⟩ : Interval).Holds (TCert.eval t beta) at h
  simpa only [T_eval] using h

def crossCert : Cert := (.add ⟨(23465444949327/100000000000000),(23465444950221/100000000000000)⟩ (.mul ⟨(6165567513639/10000000000000),(61655675136743/100000000000000)⟩ cCert dCert) (.neg ⟨(-38190230187063/100000000000000),(-19095115093261/50000000000000)⟩ (.mul ⟨(19095115093261/50000000000000),(38190230187063/100000000000000)⟩ sCert eCert)))
theorem cross_eval : crossCert.eval t beta = c*d-s*e := by
  simp only [crossCert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,div_eq_mul_inv]
  <;> norm_num
  <;> ring
  all_goals simp
theorem cross_checked : crossCert.check tRange betaRange = true := by decide +kernel
theorem cross_bounds : (⟨(23465444949327/100000000000000),(23465444950221/100000000000000)⟩ : Interval).Holds (c*d-s*e) := by
  have h := Cert.check_sound tRange betaRange crossCert t beta t_holds beta_holds cross_checked
  change (⟨(23465444949327/100000000000000),(23465444950221/100000000000000)⟩ : Interval).Holds (crossCert.eval t beta) at h
  simpa only [cross_eval] using h

theorem cross_positive : 0 < c*d-s*e := by
  have h := cross_bounds.1
  norm_num [Interval.Holds] at h
  linarith

end Sq17.EndpointIntervals
#print axioms Sq17.EndpointIntervals.T_bounds
#print axioms Sq17.EndpointIntervals.cross_positive
