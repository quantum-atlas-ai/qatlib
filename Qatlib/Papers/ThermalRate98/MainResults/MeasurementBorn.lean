/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalRate98.MainResults.PhysicalRateFormula
import Qatlib.Foundations.QueryWordCore.Circuit
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace Qatlib.Papers.ThermalRate98.MainResults
open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem born_eq_normsq (ψ : QState I) (i : I) : BornProb ψ i = ‖ψ i‖ ^ 2 := rfl

theorem position_basis_energy_coords {V : Matrix I I ℂ} (j : I) :
    Vᴴ *ᵥ (Ket j : QState I) = fun n => star (V j n) := by
  funext n
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Ket]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

def energyAmplitude (V : Matrix I I ℂ) (ψ : QState I) (n : I) : ℂ :=
  ∑ j, star (V j n) * ψ j

theorem energyAmplitude_eq_coords (V : Matrix I I ℂ) (ψ : QState I) (n : I) :
    energyAmplitude V ψ n = (Vᴴ *ᵥ ψ) n := by
  simp [energyAmplitude, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]

theorem energyAmplitude_ket (V : Matrix I I ℂ) (j n : I) :
    energyAmplitude V (Ket j) n = star (V j n) := by
  rw [energyAmplitude_eq_coords, position_basis_energy_coords]

theorem amplitude_recovery {V : Matrix I I ℂ} (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (j : I) :
    (∑ n, energyAmplitude V ψ n * V j n) = ψ j := by
  have hVV : V * Vᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hV
  have hinner : ∀ j' : I, (∑ n, star (V j' n) * V j n) = if j = j' then 1 else 0 := by
    intro j'
    have hmul : (V * Vᴴ) j j' = ∑ n, star (V j' n) * V j n := by
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Matrix.conjTranspose_apply]
      ring
    rw [← hmul, hVV, Matrix.one_apply]
  unfold energyAmplitude
  calc (∑ n, (∑ j', star (V j' n) * ψ j') * V j n)
      = ∑ n, ∑ j', (star (V j' n) * ψ j') * V j n := by
        apply Finset.sum_congr rfl; intro n _; rw [Finset.sum_mul]
    _ = ∑ j', ∑ n, (star (V j' n) * ψ j') * V j n := Finset.sum_comm
    _ = ∑ j', (∑ n, star (V j' n) * V j n) * ψ j' := by
        apply Finset.sum_congr rfl; intro j' _; rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _; ring
    _ = ∑ j', (if j = j' then 1 else 0) * ψ j' := by
        apply Finset.sum_congr rfl; intro j' _; rw [hinner]
    _ = ψ j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [if_neg hb.symm]
          simp
        · intro h; exact absurd (Finset.mem_univ j) h

theorem energyAmplitude_propagation {V U : Matrix I I ℂ} (hV : V ∈ Matrix.unitaryGroup I ℂ)
    (u : I → ℂ) (hU : Vᴴ * U * V = Matrix.diagonal u) (ψ : QState I) (n : I) :
    energyAmplitude V (U *ᵥ ψ) n = u n * energyAmplitude V ψ n := by
  have hVV : V * Vᴴ = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using hV
  have hVU : Vᴴ * U = Matrix.diagonal u * Vᴴ := by
    calc Vᴴ * U = Vᴴ * U * (V * Vᴴ) := by rw [hVV, Matrix.mul_one]
      _ = (Vᴴ * U * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal u * Vᴴ := by rw [hU]
  rw [energyAmplitude_eq_coords, energyAmplitude_eq_coords, Matrix.mulVec_mulVec, hVU,
    ← Matrix.mulVec_mulVec]

  simp only [Matrix.mulVec, dotProduct, Matrix.diagonal, Matrix.of_apply]
  rw [Finset.sum_eq_single n]
  · simp
  · intro k _ hk
    rw [if_neg hk.symm]
    simp
  · intro h; exact absurd (Finset.mem_univ n) h

theorem energyAmplitude_propagation_norm {V U : Matrix I I ℂ}
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (u : I → ℂ)
    (hU : Vᴴ * U * V = Matrix.diagonal u) (hu : ∀ n, ‖u n‖ = 1) (ψ : QState I) (n : I) :
    ‖energyAmplitude V (U *ᵥ ψ) n‖ = ‖energyAmplitude V ψ n‖ := by
  rw [energyAmplitude_propagation hV u hU ψ n, norm_mul, hu n, one_mul]

theorem energyAmplitude_zero_stable {V U : Matrix I I ℂ}
    (hV : V ∈ Matrix.unitaryGroup I ℂ) (u : I → ℂ)
    (hU : Vᴴ * U * V = Matrix.diagonal u) (ψ : QState I) (n : I)
    (h0 : energyAmplitude V ψ n = 0) :
    energyAmplitude V (U *ᵥ ψ) n = 0 := by
  rw [energyAmplitude_propagation hV u hU ψ n, h0, mul_zero]

def energyLevelSet (E : I → ℝ) (lam : ℝ) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => E i = lam)

def eigenspaceProjector (E : I → ℝ) (lam : ℝ) : Matrix I I ℂ := by
  classical
  exact Matrix.diagonal (fun i => if E i = lam then (1 : ℂ) else 0)

theorem born_eigenspace_mass (ψ : QState I) (E : I → ℝ) (lam : ℝ) :
    MeasureProb ψ (energyLevelSet E lam) =
      ∑ i, ‖(eigenspaceProjector E lam *ᵥ ψ) i‖ ^ 2 := by
  have hleft : MeasureProb ψ (energyLevelSet E lam) =
      ∑ i, if E i = lam then ‖ψ i‖ ^ 2 else 0 := by
    unfold MeasureProb energyLevelSet BornProb
    rw [Finset.sum_filter]
  have hproj : ∀ i, (eigenspaceProjector E lam *ᵥ ψ) i =
      (if E i = lam then (1 : ℂ) else 0) * ψ i := by
    intro i
    simp only [eigenspaceProjector, Matrix.mulVec, dotProduct, Matrix.diagonal, Matrix.of_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [if_neg hk.symm]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hleft]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : E i = lam
  · rw [hproj i, if_pos h]
    simp [h]
  · rw [hproj i, if_neg h]
    simp [h]

theorem born_single_level (ψ : QState I) (E : I → ℝ) (hE : Function.Injective E) (i : I) :
    MeasureProb ψ (energyLevelSet E (E i)) = ‖ψ i‖ ^ 2 := by
  have hset : energyLevelSet E (E i) = {i} := by
    unfold energyLevelSet
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hE h, fun h => by rw [h]⟩
  rw [hset, MeasureProb, Finset.sum_singleton]
  rfl

theorem born_level_masses_total (ψ : QState I) (E : I → ℝ) (hψ : Normalized ψ) :
    ∑ lam ∈ (Finset.univ.image E),
      MeasureProb ψ (energyLevelSet E lam) = 1 := by
  unfold MeasureProb energyLevelSet BornProb
  rw [Finset.sum_fiberwise_of_maps_to (t := Finset.univ.image E)
    (g := E) (f := fun i => ‖ψ i‖ ^ 2)
    (fun i _ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)]
  simpa using! hψ

theorem born_gauge (c : ℂ) (hc : ‖c‖ = 1) (ψ : QState I) (i : I) :
    BornProb (c • ψ) i = BornProb ψ i := by
  unfold BornProb
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

theorem measureProb_gauge (c : ℂ) (hc : ‖c‖ = 1) (ψ : QState I) (S : Finset I) :
    MeasureProb (c • ψ) S = MeasureProb ψ S := by
  unfold MeasureProb
  apply Finset.sum_congr rfl
  intro i _
  rw [born_gauge c hc]

theorem energyAmplitude_gauge (V : Matrix I I ℂ) (c : ℂ) (ψ : QState I) (n : I) :
    energyAmplitude V (c • ψ) n = c * energyAmplitude V ψ n := by
  unfold energyAmplitude
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem fresh_runs_total (n : ℕ) (ψ : QState I) (hψ : Normalized ψ) :
    (∑ ω : Fin n → I, ∏ k, BornProb ψ (ω k)) = 1 := by
  rw [show (Finset.univ : Finset (Fin n → I)) =
      Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset I)) from
    (Fintype.piFinset_univ).symm]
  rw [Finset.sum_prod_piFinset (s := (Finset.univ : Finset I))
    (g := fun (_ : Fin n) (i : I) => BornProb ψ i)]
  simp [bornProb_sum_eq_one hψ]

def bellPair : QState (Bool × Bool) :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

theorem bellPair_normalized : Normalized bellPair := by
  unfold Normalized bellPair
  rw [Fintype.sum_prod_type]
  have hstar : ∀ a b : Bool, ‖(if a = b then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)‖ ^ 2 =
      if a = b then ((Real.sqrt 2 : ℝ)⁻¹) ^ 2 else 0 := by
    intro a b
    by_cases h : a = b <;> simp [h]
  simp only [hstar]
  have hsq : ((Real.sqrt 2 : ℝ)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hsq]
  norm_num [Fintype.sum_bool]

theorem bell_pair_not_independent :
    BornProb bellPair (false, false) ≠
      (∑ b, BornProb bellPair (false, b)) * (∑ a, BornProb bellPair (a, false)) := by
  have hjoint : BornProb bellPair (false, false) = 1 / 2 := by
    unfold BornProb bellPair
    simp only [if_true]
    rw [norm_inv]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [abs_of_pos hpos, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hmargF : (∑ b, BornProb bellPair (false, b)) = 1 / 2 := by
    rw [Fintype.sum_bool]
    have h0 : BornProb bellPair (false, false) = 1 / 2 := hjoint
    have h1 : BornProb bellPair (false, true) = 0 := by
      unfold BornProb bellPair
      simp [Bool.false_eq_true]
    rw [h0, h1]
    norm_num
  have hmargS : (∑ a, BornProb bellPair (a, false)) = 1 / 2 := by
    rw [Fintype.sum_bool]
    have h0 : BornProb bellPair (false, false) = 1 / 2 := hjoint
    have h1 : BornProb bellPair (true, false) = 0 := by
      unfold BornProb bellPair
      simp
    rw [h0, h1]
    norm_num
  rw [hjoint, hmargF, hmargS]
  norm_num

end Qatlib.Papers.ThermalRate98.MainResults
