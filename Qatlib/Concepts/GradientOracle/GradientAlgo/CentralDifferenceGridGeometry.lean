/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.GradientAlgo.AnalyticCentralDifferenceGridErrorStat
import Qatlib.Concepts.GradientOracle.GradientAlgo.TensorChebyshevGridBoundOpti
import Mathlib.Data.Fin.Rev
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open scoped Classical BigOperators

theorem centralDiff_grid_abs (M : ℕ) (z : Fin M) : |gridCenter M 1 z|≤1/2 := by
  have hM : (0 : ℝ)<M := by
    exact_mod_cast (show 0<M from Nat.pos_of_ne_zero (by intro h; subst M; exact Fin.elim0 z))
  have hz : (z : ℝ)<M := by exact_mod_cast z.isLt
  have hz0 : (0 : ℝ)≤z := Nat.cast_nonneg _
  dsimp [gridCenter]
  rw [one_mul,abs_le]
  constructor
  · have h := div_nonneg (by positivity : (0 : ℝ)≤2*(z : ℝ)+1) (by positivity : (0 : ℝ)≤2*M)
    linarith
  · have h : (2*(z : ℝ)+1)/(2*M)≤1 := (div_le_one (by positivity)).mpr (by
      have hzn : z.val+1≤M := z.isLt
      have hzr : (z : ℝ)+1≤M := by exact_mod_cast hzn
      linarith)
    linarith

theorem centralDiff_grid_rev (M : ℕ) (z : Fin M) : gridCenter M 1 z.rev= -gridCenter M 1 z := by
  have hM : (M : ℝ)≠0 := by exact_mod_cast (show M≠0 by intro h; subst M; exact Fin.elim0 z)
  have hz : (z.rev : ℝ)+(z : ℝ)+1=M := by
    have h : z.rev.val+z.val+1=M := by simp only [Fin.val_rev]; omega
    exact_mod_cast h
  dsimp [gridCenter]
  simp only [Fin.val_rev] at hz
  field_simp
  nlinarith

theorem centralDiff_grid_injective (M : ℕ) : Function.Injective (gridCenter M 1) := by
  intro z w h
  have hM : (M : ℝ)≠0 := by exact_mod_cast (show M≠0 by intro h; subst M; exact Fin.elim0 z)
  dsimp [gridCenter] at h
  have hzw : (z : ℝ)=(w : ℝ) := by field_simp at h; nlinarith
  apply Fin.ext
  exact_mod_cast hzw

theorem centralDiff_grid_tensor_count (d k M : ℕ) (hd : 0<d) (hk : 0<k)
    (r : ℝ) (hr : 1<r) (H : (Fin k → Fin d) → ℝ) (hH : ∀ α,|H α|≤1) :
    ((Finset.univ.filter fun z : Fin d → Fin M =>
      Real.sqrt 2*(r*Real.sqrt ((d : ℝ)*k/2))^k≤
        |∑ α : Fin k → Fin d,H α*(∏ i : Fin k,gridCenter M 1 (z (α i)))|).card : ℝ)
      ≤((M^d : ℕ) : ℝ)/r^(2*k) := by
  by_cases hM : M=0
  · subst M
    have : IsEmpty (Fin d → Fin 0) := ⟨fun z => Fin.elim0 (z ⟨0,hd⟩)⟩
    simp [Nat.ne_of_gt hd]
  have hp : 0<M := Nat.pos_of_ne_zero hM
  let S := Finset.univ.image (gridCenter M 1)
  have hbound : ∀ v∈S,|v|≤1/2 := by
    intro v hv
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hv
    exact centralDiff_grid_abs M z
  have hsym : ∀ v∈S,-v∈S := by
    intro v hv
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨z.rev,Finset.mem_univ _,centralDiff_grid_rev M z⟩
  have hne : S.Nonempty :=
      ⟨gridCenter M 1 ⟨0,hp⟩,Finset.mem_image.mpr ⟨⟨0,hp⟩,Finset.mem_univ _,rfl⟩⟩
  let e : Fin M ≃ S := Equiv.ofBijective
    (fun z => ⟨gridCenter M 1 z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩⟩)
    ⟨fun z w h => centralDiff_grid_injective M (congrArg Subtype.val h),by
      intro v
      obtain ⟨z,_,hz⟩ := Finset.mem_image.mp v.property
      exact ⟨z,Subtype.ext hz⟩⟩
  let E := Equiv.piCongrRight (fun _ : Fin d => e)
  have hc : S.card=M := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_fin,Fintype.card_coe] using h.symm
  have heq : (Finset.univ.filter fun z : Fin d → Fin M =>
      Real.sqrt 2*(r*Real.sqrt ((d : ℝ)*k/2))^k≤
        |∑ α : Fin k → Fin d,H α*(∏ i : Fin k,gridCenter M 1 (z (α i)))|).card=
      (Finset.univ.filter fun y : Fin d → S =>
        Real.sqrt 2*(r*Real.sqrt ((d : ℝ)*k/2))^k≤
          |∑ α : Fin k → Fin d,H α*(∏ i : Fin k,(y (α i) : ℝ))|).card := by
    apply Finset.card_equiv E
    intro z
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rfl
  rw [heq]
  simpa only [hc] using tensorChebyshevGridBound d k hd hk r hr S hbound hsym hne H hH
end Qatlib.Concepts.GradientOracle.GradientAlgo
