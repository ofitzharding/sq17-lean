import Sq17Lean.LocalSliderUnwanted

namespace Sq17.LocalSlider
open Sq17.EndpointGeometry Sq17.EndpointIntervals Sq17.RationalExpression
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
noncomputable def cornerProjection (i j : Fin 17) (k : Fin 8) (second : Bool) : ℝ :=
  let n := optionNormal i j k
  let v := directions (optionOther i j k)
  if second then -n.1*v.2+n.2*v.1 else n.1*v.1+n.2*v.2

def contact_projection_3_0Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨0,0⟩ (.constant 0) cCert) (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.constant 1) sCert))
theorem contact_projection_3_0_eval : contact_projection_3_0Cert.eval t beta = cornerProjection 2 8 2 false := by
  simp only [contact_projection_3_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_3_0_checked : contact_projection_3_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_3_0_positive : 0 < cornerProjection 2 8 2 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_3_0Cert t beta t_holds beta_holds contact_projection_3_0_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_3_0Cert.eval t beta) at h
  rw [contact_projection_3_0_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_3_1Cert : Cert := (.add ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.mul ⟨0,0⟩ (.constant 0) (.neg ⟨(-32008809621573/50000000000000),(-64017619242707/100000000000000)⟩ sCert)) (.mul ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.constant 1) cCert))
theorem contact_projection_3_1_eval : contact_projection_3_1Cert.eval t beta = cornerProjection 2 8 2 true := by
  simp only [contact_projection_3_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_3_1_checked : contact_projection_3_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_3_1_positive : 0 < cornerProjection 2 8 2 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_3_1Cert t beta t_holds beta_holds contact_projection_3_1_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_3_1Cert.eval t beta) at h
  rw [contact_projection_3_1_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_3 (a b z : ℝ) : cornerGap a b z 2 8 2 true true = 0 := by
  have he : cornerGap a b z 2 8 2 true true = pairGap a b z 2 8 1 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_3_9]

def contact_projection_5_0Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ sCert (.constant 1)) (.mul ⟨0,0⟩ (.neg ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ cCert) (.constant 0)))
theorem contact_projection_5_0_eval : contact_projection_5_0Cert.eval t beta = cornerProjection 3 9 7 false := by
  simp only [contact_projection_5_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_5_0_checked : contact_projection_5_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_5_0_positive : 0 < cornerProjection 3 9 7 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_5_0Cert t beta t_holds beta_holds contact_projection_5_0_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_5_0Cert.eval t beta) at h
  rw [contact_projection_5_0_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_5_1Cert : Cert := (.neg ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.add ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ (.mul ⟨0,0⟩ sCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ (.neg ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ cCert) (.constant 1))))
theorem contact_projection_5_1_eval : contact_projection_5_1Cert.eval t beta = -(cornerProjection 3 9 7 true) := by
  simp only [contact_projection_5_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_5_1_checked : contact_projection_5_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_5_1_positive : 0 < -(cornerProjection 3 9 7 true) := by
  have h := Cert.check_sound tRange betaRange contact_projection_5_1Cert t beta t_holds beta_holds contact_projection_5_1_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_5_1Cert.eval t beta) at h
  rw [contact_projection_5_1_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_5 (a b z : ℝ) : cornerGap a b z 3 9 7 true false = 0 := by
  have he : cornerGap a b z 3 9 7 true false = pairGap a b z 3 9 3 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_4_10]

def contact_projection_6_0Cert : Cert := (.add ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.mul ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ cCert (.constant 1)) (.mul ⟨0,0⟩ sCert (.constant 0)))
theorem contact_projection_6_0_eval : contact_projection_6_0Cert.eval t beta = cornerProjection 2 10 4 false := by
  simp only [contact_projection_6_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_6_0_checked : contact_projection_6_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_6_0_positive : 0 < cornerProjection 2 10 4 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_6_0Cert t beta t_holds beta_holds contact_projection_6_0_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_6_0Cert.eval t beta) at h
  rw [contact_projection_6_0_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_6_1Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨0,0⟩ cCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ sCert (.constant 1)))
theorem contact_projection_6_1_eval : contact_projection_6_1Cert.eval t beta = cornerProjection 2 10 4 true := by
  simp only [contact_projection_6_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_6_1_checked : contact_projection_6_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_6_1_positive : 0 < cornerProjection 2 10 4 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_6_1Cert t beta t_holds beta_holds contact_projection_6_1_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_6_1Cert.eval t beta) at h
  rw [contact_projection_6_1_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_6 (a b z : ℝ) : cornerGap a b z 2 10 4 true true = 0 := by
  have he : cornerGap a b z 2 10 4 true true = pairGap a b z 2 10 2 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_3_11]

def contact_projection_9_0Cert : Cert := (.add ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.mul ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ cCert (.constant 1)) (.mul ⟨0,0⟩ sCert (.constant 0)))
theorem contact_projection_9_0_eval : contact_projection_9_0Cert.eval t beta = cornerProjection 1 12 4 false := by
  simp only [contact_projection_9_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_9_0_checked : contact_projection_9_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_9_0_positive : 0 < cornerProjection 1 12 4 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_9_0Cert t beta t_holds beta_holds contact_projection_9_0_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_9_0Cert.eval t beta) at h
  rw [contact_projection_9_0_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_9_1Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨0,0⟩ cCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ sCert (.constant 1)))
theorem contact_projection_9_1_eval : contact_projection_9_1Cert.eval t beta = cornerProjection 1 12 4 true := by
  simp only [contact_projection_9_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_9_1_checked : contact_projection_9_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_9_1_positive : 0 < cornerProjection 1 12 4 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_9_1Cert t beta t_holds beta_holds contact_projection_9_1_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_9_1Cert.eval t beta) at h
  rw [contact_projection_9_1_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_9 (a b z : ℝ) : cornerGap a b z 1 12 4 true true = 0 := by
  have he : cornerGap a b z 1 12 4 true true = pairGap a b z 1 12 2 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_2_13]

def contact_projection_12_0Cert : Cert := (.add ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.mul ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ cCert (.constant 1)) (.mul ⟨0,0⟩ sCert (.constant 0)))
theorem contact_projection_12_0_eval : contact_projection_12_0Cert.eval t beta = cornerProjection 9 14 0 false := by
  simp only [contact_projection_12_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_12_0_checked : contact_projection_12_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_12_0_positive : 0 < cornerProjection 9 14 0 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_12_0Cert t beta t_holds beta_holds contact_projection_12_0_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_12_0Cert.eval t beta) at h
  rw [contact_projection_12_0_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_12_1Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨0,0⟩ cCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ sCert (.constant 1)))
theorem contact_projection_12_1_eval : contact_projection_12_1Cert.eval t beta = cornerProjection 9 14 0 true := by
  simp only [contact_projection_12_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_12_1_checked : contact_projection_12_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_12_1_positive : 0 < cornerProjection 9 14 0 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_12_1Cert t beta t_holds beta_holds contact_projection_12_1_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_12_1Cert.eval t beta) at h
  rw [contact_projection_12_1_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_12 (a b z : ℝ) : cornerGap a b z 9 14 0 true true = 0 := by
  have he : cornerGap a b z 9 14 0 true true = pairGap a b z 9 14 2 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_10_15]

def contact_projection_13_0Cert : Cert := (.add ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.mul ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ cCert (.constant 1)) (.mul ⟨0,0⟩ sCert (.constant 0)))
theorem contact_projection_13_0_eval : contact_projection_13_0Cert.eval t beta = cornerProjection 13 16 0 false := by
  simp only [contact_projection_13_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_13_0_checked : contact_projection_13_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_13_0_positive : 0 < cornerProjection 13 16 0 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_13_0Cert t beta t_holds beta_holds contact_projection_13_0_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_13_0Cert.eval t beta) at h
  rw [contact_projection_13_0_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_13_1Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨0,0⟩ cCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ sCert (.constant 1)))
theorem contact_projection_13_1_eval : contact_projection_13_1Cert.eval t beta = cornerProjection 13 16 0 true := by
  simp only [contact_projection_13_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_13_1_checked : contact_projection_13_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_13_1_positive : 0 < cornerProjection 13 16 0 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_13_1Cert t beta t_holds beta_holds contact_projection_13_1_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_13_1Cert.eval t beta) at h
  rw [contact_projection_13_1_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_13 (a b z : ℝ) : cornerGap a b z 13 16 0 true true = 0 := by
  have he : cornerGap a b z 13 16 0 true true = pairGap a b z 13 16 2 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_14_17]

def contact_projection_14_0Cert : Cert := (.add ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ (.mul ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ dCert (.constant 1)) (.mul ⟨0,0⟩ (.neg ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ eCert) (.constant 0)))
theorem contact_projection_14_0_eval : contact_projection_14_0Cert.eval t beta = cornerProjection 14 15 4 false := by
  simp only [contact_projection_14_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_14_0_checked : contact_projection_14_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_14_0_positive : 0 < cornerProjection 14 15 4 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_14_0Cert t beta t_holds beta_holds contact_projection_14_0_checked
  change (⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ : Interval).Holds (contact_projection_14_0Cert.eval t beta) at h
  rw [contact_projection_14_0_eval] at h
  exact (show (0:ℝ) < ((20064247070879/25000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_14_1Cert : Cert := (.neg ⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ (.add ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ (.mul ⟨0,0⟩ dCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ (.neg ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ eCert) (.constant 1))))
theorem contact_projection_14_1_eval : contact_projection_14_1Cert.eval t beta = -(cornerProjection 14 15 4 true) := by
  simp only [contact_projection_14_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_14_1_checked : contact_projection_14_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_14_1_positive : 0 < -(cornerProjection 14 15 4 true) := by
  have h := Cert.check_sound tRange betaRange contact_projection_14_1Cert t beta t_holds beta_holds contact_projection_14_1_checked
  change (⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ : Interval).Holds (contact_projection_14_1Cert.eval t beta) at h
  rw [contact_projection_14_1_eval] at h
  exact (show (0:ℝ) < ((23303051321/39062500000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_14 (a b z : ℝ) : cornerGap a b z 14 15 4 true false = 0 := by
  have he : cornerGap a b z 14 15 4 true false = pairGap a b z 14 15 4 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_15_16]

def contact_projection_15_0Cert : Cert := (.add ⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ (.mul ⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ eCert (.constant 1)) (.mul ⟨0,0⟩ dCert (.constant 0)))
theorem contact_projection_15_0_eval : contact_projection_15_0Cert.eval t beta = cornerProjection 15 7 2 false := by
  simp only [contact_projection_15_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_15_0_checked : contact_projection_15_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_15_0_positive : 0 < cornerProjection 15 7 2 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_15_0Cert t beta t_holds beta_holds contact_projection_15_0_checked
  change (⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ : Interval).Holds (contact_projection_15_0Cert.eval t beta) at h
  rw [contact_projection_15_0_eval] at h
  exact (show (0:ℝ) < ((23303051321/39062500000):ℚ) by norm_num).trans_le h.1

def contact_projection_15_1Cert : Cert := (.add ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ (.mul ⟨0,0⟩ eCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ dCert (.constant 1)))
theorem contact_projection_15_1_eval : contact_projection_15_1Cert.eval t beta = cornerProjection 15 7 2 true := by
  simp only [contact_projection_15_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_15_1_checked : contact_projection_15_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_15_1_positive : 0 < cornerProjection 15 7 2 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_15_1Cert t beta t_holds beta_holds contact_projection_15_1_checked
  change (⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ : Interval).Holds (contact_projection_15_1Cert.eval t beta) at h
  rw [contact_projection_15_1_eval] at h
  exact (show (0:ℝ) < ((20064247070879/25000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_15 (a b z : ℝ) : cornerGap a b z 15 7 2 true true = 0 := by
  have he : cornerGap a b z 15 7 2 true true = pairGap a b z 15 7 5 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_16_8]

def contact_projection_16_0Cert : Cert := (.add ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ (.mul ⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ sCert (.constant 1)) (.mul ⟨0,0⟩ (.neg ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ cCert) (.constant 0)))
theorem contact_projection_16_0_eval : contact_projection_16_0Cert.eval t beta = cornerProjection 13 6 3 false := by
  simp only [contact_projection_16_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_16_0_checked : contact_projection_16_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_16_0_positive : 0 < cornerProjection 13 6 3 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_16_0Cert t beta t_holds beta_holds contact_projection_16_0_checked
  change (⟨(64017619242707/100000000000000),(32008809621573/50000000000000)⟩ : Interval).Holds (contact_projection_16_0Cert.eval t beta) at h
  rw [contact_projection_16_0_eval] at h
  exact (show (0:ℝ) < ((64017619242707/100000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_16_1Cert : Cert := (.neg ⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ (.add ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ (.mul ⟨0,0⟩ sCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ (.neg ⟨(-19205702972173/25000000000000),(-38411405944231/50000000000000)⟩ cCert) (.constant 1))))
theorem contact_projection_16_1_eval : contact_projection_16_1Cert.eval t beta = -(cornerProjection 13 6 3 true) := by
  simp only [contact_projection_16_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_16_1_checked : contact_projection_16_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_16_1_positive : 0 < -(cornerProjection 13 6 3 true) := by
  have h := Cert.check_sound tRange betaRange contact_projection_16_1Cert t beta t_holds beta_holds contact_projection_16_1_checked
  change (⟨(38411405944231/50000000000000),(19205702972173/25000000000000)⟩ : Interval).Holds (contact_projection_16_1Cert.eval t beta) at h
  rw [contact_projection_16_1_eval] at h
  exact (show (0:ℝ) < ((38411405944231/50000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_16 (a b z : ℝ) : cornerGap a b z 13 6 3 true false = 0 := by
  have he : cornerGap a b z 13 6 3 true false = pairGap a b z 13 6 3 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_14_7]

def contact_projection_17_0Cert : Cert := (.add ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ (.mul ⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ dCert (.constant 1)) (.mul ⟨0,0⟩ (.neg ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ eCert) (.constant 0)))
theorem contact_projection_17_0_eval : contact_projection_17_0Cert.eval t beta = cornerProjection 15 16 0 false := by
  simp only [contact_projection_17_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_17_0_checked : contact_projection_17_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_17_0_positive : 0 < cornerProjection 15 16 0 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_17_0Cert t beta t_holds beta_holds contact_projection_17_0_checked
  change (⟨(20064247070879/25000000000000),(40128494141867/50000000000000)⟩ : Interval).Holds (contact_projection_17_0Cert.eval t beta) at h
  rw [contact_projection_17_0_eval] at h
  exact (show (0:ℝ) < ((20064247070879/25000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_17_1Cert : Cert := (.neg ⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ (.add ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ (.mul ⟨0,0⟩ dCert (.neg ⟨0,0⟩ (.constant 0))) (.mul ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ (.neg ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ eCert) (.constant 1))))
theorem contact_projection_17_1_eval : contact_projection_17_1Cert.eval t beta = -(cornerProjection 15 16 0 true) := by
  simp only [contact_projection_17_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_17_1_checked : contact_projection_17_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_17_1_positive : 0 < -(cornerProjection 15 16 0 true) := by
  have h := Cert.check_sound tRange betaRange contact_projection_17_1Cert t beta t_holds beta_holds contact_projection_17_1_checked
  change (⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ : Interval).Holds (contact_projection_17_1Cert.eval t beta) at h
  rw [contact_projection_17_1_eval] at h
  exact (show (0:ℝ) < ((23303051321/39062500000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_17 (a b z : ℝ) : cornerGap a b z 15 16 0 true false = 0 := by
  have he : cornerGap a b z 15 16 0 true false = pairGap a b z 15 16 4 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_16_17]

def contact_projection_18_0Cert : Cert := (.add ⟨(23465444949327/100000000000000),(23465444950221/100000000000000)⟩ (.mul ⟨(6165567513639/10000000000000),(61655675136743/100000000000000)⟩ cCert dCert) (.mul ⟨(-38190230187063/100000000000000),(-19095115093261/50000000000000)⟩ sCert (.neg ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ eCert)))
theorem contact_projection_18_0_eval : contact_projection_18_0Cert.eval t beta = cornerProjection 11 15 0 false := by
  simp only [contact_projection_18_0Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_18_0_checked : contact_projection_18_0Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_18_0_positive : 0 < cornerProjection 11 15 0 false := by
  have h := Cert.check_sound tRange betaRange contact_projection_18_0Cert t beta t_holds beta_holds contact_projection_18_0_checked
  change (⟨(23465444949327/100000000000000),(23465444950221/100000000000000)⟩ : Interval).Holds (contact_projection_18_0Cert.eval t beta) at h
  rw [contact_projection_18_0_eval] at h
  exact (show (0:ℝ) < ((23465444949327/100000000000000):ℚ) by norm_num).trans_le h.1

def contact_projection_18_1Cert : Cert := (.add ⟨(1944157698667/2000000000000),(19441576986863/20000000000000)⟩ (.mul ⟨(9165854351669/20000000000000),(45829271758817/100000000000000)⟩ cCert (.neg ⟨(23303051321/39062500000),(11931162276439/20000000000000)⟩ (.neg ⟨(-11931162276439/20000000000000),(-23303051321/39062500000)⟩ eCert))) (.mul ⟨(10275722635001/20000000000000),(25689306587749/50000000000000)⟩ sCert dCert))
theorem contact_projection_18_1_eval : contact_projection_18_1Cert.eval t beta = cornerProjection 11 15 0 true := by
  simp only [contact_projection_18_1Cert,Cert.eval,c_eval,s_eval,d_eval,e_eval,side_eval,h_eval,X_eval,Y_eval,A_eval,B_eval,u10_eval,v10_eval,u11_eval,v11_eval,u13_eval,T_eval,cross_eval]
  <;> norm_num [cornerProjection,optionNormal,optionOther,optionOwner,directions]
  <;> ring
theorem contact_projection_18_1_checked : contact_projection_18_1Cert.check tRange betaRange = true := by decide +kernel
theorem contact_projection_18_1_positive : 0 < cornerProjection 11 15 0 true := by
  have h := Cert.check_sound tRange betaRange contact_projection_18_1Cert t beta t_holds beta_holds contact_projection_18_1_checked
  change (⟨(1944157698667/2000000000000),(19441576986863/20000000000000)⟩ : Interval).Holds (contact_projection_18_1Cert.eval t beta) at h
  rw [contact_projection_18_1_eval] at h
  exact (show (0:ℝ) < ((1944157698667/2000000000000):ℚ) by norm_num).trans_le h.1

theorem designated_corner_18 (a b z : ℝ) : cornerGap a b z 11 15 0 true true = 0 := by
  have he : cornerGap a b z 11 15 0 true true = pairGap a b z 11 15 2 := by
    norm_num [cornerGap,pairGap,optionNormal,optionOther,optionOwner,cornerSign,directions,axes,directionKind,axisKind,supportTable,crossSupport]
    <;> ring
  rw [he,pair_contact_12_16]

def nonparallelCorners : List (Fin 19 × Fin 8 × Bool × Bool) := [(3,2,true,true),(5,7,true,false),(6,4,true,true),(9,4,true,true),(12,0,true,true),(13,0,true,true),(14,4,true,false),(15,2,true,true),(16,3,true,false),(17,0,true,false),(18,0,true,true)]
theorem nonparallel_corner_tight (a b z : ℝ) : ∀ w ∈ nonparallelCorners,
    cornerGap a b z (contactPairs w.1).1 (contactPairs w.1).2.1 w.2.1 w.2.2.1 w.2.2.2 = 0 := by
  simp only [nonparallelCorners,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  exact ⟨designated_corner_3 a b z,designated_corner_5 a b z,designated_corner_6 a b z,designated_corner_9 a b z,designated_corner_12 a b z,designated_corner_13 a b z,designated_corner_14 a b z,designated_corner_15 a b z,designated_corner_16 a b z,designated_corner_17 a b z,designated_corner_18 a b z⟩
theorem nonparallel_corner_signs : ∀ w ∈ nonparallelCorners,
    0 < cornerSign w.2.2.1 * cornerProjection (contactPairs w.1).1 (contactPairs w.1).2.1 w.2.1 false ∧
    0 < cornerSign w.2.2.2 * cornerProjection (contactPairs w.1).1 (contactPairs w.1).2.1 w.2.1 true := by
  simp only [nonparallelCorners,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  · have h0 := contact_projection_3_0_positive
    have h1 := contact_projection_3_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_5_0_positive
    have h1 := contact_projection_5_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_6_0_positive
    have h1 := contact_projection_6_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_9_0_positive
    have h1 := contact_projection_9_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_12_0_positive
    have h1 := contact_projection_12_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_13_0_positive
    have h1 := contact_projection_13_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_14_0_positive
    have h1 := contact_projection_14_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_15_0_positive
    have h1 := contact_projection_15_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_16_0_positive
    have h1 := contact_projection_16_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_17_0_positive
    have h1 := contact_projection_17_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
  · have h0 := contact_projection_18_0_positive
    have h1 := contact_projection_18_1_positive
    norm_num [contactPairs,cornerSign]
    constructor <;> linarith
theorem nonparallelCorners_designated : ∀ w ∈ nonparallelCorners,
    (w.1,w.2.1) ∈ designatedOptions := by decide +kernel

theorem designated_options_classified : ∀ r : Fin 19, ∀ k : Fin 8,
    (r,k) ∈ designatedOptions →
      r ∈ ([0,1,2,4,7,8,10,11] : List (Fin 19)) ∨
      ∃ w ∈ nonparallelCorners, w.1=r ∧ w.2.1=k := by decide +kernel

end Sq17.LocalSlider
#print axioms Sq17.LocalSlider.nonparallel_corner_tight
#print axioms Sq17.LocalSlider.nonparallel_corner_signs
