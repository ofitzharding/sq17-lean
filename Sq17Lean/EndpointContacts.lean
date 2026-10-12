import Sq17Lean.EndpointSupport

namespace Sq17.EndpointGeometry
open Sq17.PolynomialBox
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem denominator_facts : t ≠ 0 ∧ t+1 ≠ 0 ∧ 1-t*t ≠ 0 ∧ 1+t*t ≠ 0 ∧
    1+beta*beta ≠ 0 ∧ 1+2*t-t*t ≠ 0 := by
  have ht := t_bounds
  exact ⟨by linarith,by linarith,by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (show 0 ≤ t by linarith)],
    ne_of_gt denominator_positive.1,ne_of_gt denominator_positive.2.1,ne_of_gt denominator_positive.2.2⟩

macro "endpoint_identity" : tactic =>
  `(tactic| (
    obtain ⟨ht,ht1,hm,hp,hb,hS⟩ := denominator_facts
    have hm2 : 1-t^2 ≠ 0 := by convert hm using 1 <;> ring
    have hS2 : 1+t*2-t^2 ≠ 0 := by convert hS using 1 <;> ring
    norm_num [pairGap,wallGap,centres,axes,directionKind,axisKind,supportTable,crossSupport,rotate,h,X,Y,A,B,u10,v10,u11,v11,u13,T,side,c,s,d,e]
    <;> field_simp [ht,ht1,hm,hp,hb,hS]
    <;> ring_nf
    <;> field_simp [ht,ht1,hm,hm2,hp,hb,hS,hS2]
    <;> ring))

theorem wall_contact_1_0 : wallGap 0 0=0 := by endpoint_identity

theorem wall_contact_1_2 : wallGap 0 2=0 := by endpoint_identity

theorem wall_contact_2_2 : wallGap 1 2=0 := by endpoint_identity

theorem wall_contact_3_0 : wallGap 2 0=0 := by endpoint_identity

theorem wall_contact_4_0 : wallGap 3 0=0 := by endpoint_identity

theorem wall_contact_4_3 : wallGap 3 3=0 := by endpoint_identity

theorem wall_contact_5_2 : wallGap 4 2=0 := by endpoint_identity

theorem wall_contact_7_1 : wallGap 6 1=0 := by endpoint_identity

theorem wall_contact_8_1 : wallGap 7 1=0 := by endpoint_identity

theorem wall_contact_8_3 : wallGap 7 3=0 := by endpoint_identity

theorem wall_contact_9_0 : wallGap 8 0=0 := by endpoint_identity

theorem wall_contact_15_3 : wallGap 14 3=0 := by endpoint_identity

theorem wall_contact_17_1 : wallGap 16 1=0 := by endpoint_identity

theorem wall_contact_5_1 : wallGap 4 1=0 := by endpoint_identity

theorem wall_contact_6_2 : wallGap 5 2=0 := by endpoint_identity

theorem pair_contact_1_2 : pairGap 0 1 0=0 := by endpoint_identity

theorem pair_contact_1_3 : pairGap 0 2 1=0 := by endpoint_identity

theorem pair_contact_5_7 : pairGap 4 6 1=0 := by endpoint_identity

theorem pair_contact_3_9 : pairGap 2 8 1=0 := by endpoint_identity

theorem pair_contact_9_10 : pairGap 8 9 2=0 := by endpoint_identity

theorem pair_contact_4_10 : pairGap 3 9 3=0 := by endpoint_identity

theorem pair_contact_3_11 : pairGap 2 10 2=0 := by endpoint_identity

theorem pair_contact_11_12 : pairGap 10 11 2=0 := by endpoint_identity

theorem pair_contact_10_12 : pairGap 9 11 3=0 := by endpoint_identity

theorem pair_contact_2_13 : pairGap 1 12 2=0 := by endpoint_identity

theorem pair_contact_13_14 : pairGap 12 13 2=0 := by endpoint_identity

theorem pair_contact_12_14 : pairGap 11 13 3=0 := by endpoint_identity

theorem pair_contact_10_15 : pairGap 9 14 2=0 := by endpoint_identity

theorem pair_contact_14_17 : pairGap 13 16 2=0 := by endpoint_identity

theorem pair_contact_15_16 : pairGap 14 15 4=0 := by endpoint_identity

theorem pair_contact_16_8 : pairGap 15 7 5=0 := by endpoint_identity

theorem pair_contact_14_7 : pairGap 13 6 3=0 := by endpoint_identity

theorem pair_contact_16_17 : pairGap 15 16 4=0 := by
  have hid : pairGap 15 16 4 =
      1*eval EndpointRoot.polynomial0 (t,beta)/(t*(t+1)*(1+t*t)*(1+beta*beta)) := by
    simp only [EndpointRoot.polynomial0,eval,Term.eval]
    endpoint_identity
  have hp : eval EndpointRoot.polynomial0 (t,beta)=0 := EndpointRoot.coordinates_spec.2.1
  rw [hid,hp]; ring

theorem pair_contact_12_16 : pairGap 11 15 2=0 := by
  have hid : pairGap 11 15 2 =
      2*eval EndpointRoot.polynomial1 (t,beta)/((1+beta*beta)^2*(t+1)*(1+t*t)^2) := by
    simp only [EndpointRoot.polynomial1,eval,Term.eval]
    endpoint_identity
  have hp : eval EndpointRoot.polynomial1 (t,beta)=0 := EndpointRoot.coordinates_spec.2.2
  rw [hid,hp]; ring

theorem pair_contact_9_11 : pairGap 8 10 3=0 := by endpoint_identity

theorem pair_contact_3_2 : pairGap 2 1 0=0 := by endpoint_identity

end Sq17.EndpointGeometry
#print axioms Sq17.EndpointGeometry.pair_contact_16_17
#print axioms Sq17.EndpointGeometry.pair_contact_12_16
