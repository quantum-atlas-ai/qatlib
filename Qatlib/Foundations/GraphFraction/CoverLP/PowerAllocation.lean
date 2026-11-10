/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.GraphFraction.CoverLP.WeightedCover

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.GraphFraction.CoverLP
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def magnitudeRoot (c : ℝ) : ℝ := |c| ^ (1/(3:ℝ))

omit [Fintype V] [DecidableEq V] [Nonempty V] in

theorem magnitudeRoot_cube (c : ℝ) : magnitudeRoot c^3=|c| := by
  unfold magnitudeRoot
  rw [← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg c)]
  norm_num

omit [Fintype V] [DecidableEq V] [Nonempty V] in

theorem magnitudeRoot_square (c : ℝ) : magnitudeRoot c^2=|c|^((2:ℝ)/3) := by
  unfold magnitudeRoot
  rw [← Real.rpow_natCast,← Real.rpow_mul (abs_nonneg c)]
  norm_num

theorem attained_power_strategy (G : SimpleGraph V) (c : V → ℝ) (hc : ∀ i,c i≠0) :
    let C : ℝ := ∑ i,|c i|^((2:ℝ)/3)
    let a : V → ℝ := fun i => |c i|^((2:ℝ)/3)/C
    0<coverValue G a ∧ ∃ q : Context G → ℝ,q∈stdSimplex ℝ (Context G) ∧
      (∀ i,0<coverage G q i) ∧
      (∀ i,a i/coverValue G a ≤ coverage G q i) ∧
      (∑ i,|c i|/Real.sqrt (coverage G q i))^2 ≤ coverValue G a*C^3 := by
  let r : V → ℝ := fun i => magnitudeRoot (c i)
  have hr (i : V) : 0<r i := Real.rpow_pos_of_pos (abs_pos.mpr (hc i)) _
  let C : ℝ := ∑ i,r i^2
  have hC : 0<C := Finset.sum_pos (fun i _ => sq_pos_of_pos (hr i)) Finset.univ_nonempty
  let a : V → ℝ := fun i => r i^2/C
  have ha (i : V) : 0<a i := div_pos (sq_pos_of_pos (hr i)) hC
  obtain ⟨hχ,q,hq,hcov⟩ := attained_strategy G a (fun i => (ha i).le)
    (Classical.choice ‹Nonempty V›) (ha _)
  let χ : ℝ := coverValue G a
  have hχ' : 0<χ := hχ
  have hχC : 0<C*χ := mul_pos hC hχ'
  have hp (i : V) : 0<coverage G q i := lt_of_lt_of_le (div_pos (ha i) hχ) (hcov i)
  have hcoord (i : V) : r i ≤ Real.sqrt (coverage G q i)*Real.sqrt (C*χ) := by
    have hb : r i^2 ≤ coverage G q i*(C*χ) := by
      have hh := (div_le_iff₀ hχ).mp (hcov i)
      have hh' := (div_le_iff₀ hC).mp hh
      dsimp [a] at hh'
      nlinarith
    have hs := Real.sq_sqrt (hp i).le
    have ht := Real.sq_sqrt hχC.le
    have hn := mul_nonneg (Real.sqrt_nonneg (coverage G q i)) (Real.sqrt_nonneg (C*χ))
    nlinarith [hr i]
  have hamp : (∑ i,|c i|/Real.sqrt (coverage G q i)) ≤ C*Real.sqrt (C*χ) := by
    calc _ ≤ ∑ i,r i^2*Real.sqrt (C*χ) := by
           apply Finset.sum_le_sum
           intro i _
           apply (div_le_iff₀ (Real.sqrt_pos.mpr (hp i))).mpr
           have hh := mul_le_mul_of_nonneg_left (hcoord i) (sq_nonneg (r i))
           rw [← magnitudeRoot_cube (c i)]
           change r i^3 ≤ _
           nlinarith
         _ = _ := (Finset.sum_mul _ _ _).symm
  have hbound : (∑ i,|c i|/Real.sqrt (coverage G q i))^2 ≤ χ*C^3 := by
    have hh := pow_le_pow_left₀ (Finset.sum_nonneg
      (fun i _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))) hamp 2
    have hs := Real.sq_sqrt hχC.le
    calc _ ≤ (C*Real.sqrt (C*χ))^2 := hh
         _ = χ*C^3 := by rw [mul_pow,hs];ring
  have hCs : (∑ i,|c i|^((2:ℝ)/3))=C := by
    simp_rw [← magnitudeRoot_square]
    rfl
  dsimp only
  rw [hCs]
  simp_rw [← magnitudeRoot_square]
  exact ⟨hχ,q,hq,hp,hcov,hbound⟩

end Qatlib.Foundations.GraphFraction.CoverLP
