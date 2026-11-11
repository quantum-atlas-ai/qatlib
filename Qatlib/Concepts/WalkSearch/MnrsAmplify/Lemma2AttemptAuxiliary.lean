/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma2Stat
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Lemma1Sear

/-!
# Auxiliary bounds for tolerant amplification

Establishes norm, success, and cost estimates for the repeated attempts used in tolerant MNRS
amplitude amplification [MagniezNayakRolandSantha2011]. The results handle zero marked mass,
normalization of unsuccessful branches, and confinement of successive attempts to the unmarked
ray of an invariant plane.

## Main statements

* `mnrs_zero_mass_tolerant_success`: Under the stated fixed-state hypotheses, zero initial
  marked mass gives zero tolerant success through level `n`.
* `mnrs_tolerant_attempt_cost_bound`: Bounds the sum of recursive amplification costs through
  `max tMax 1` by `2 * 3 ^ tMax * (c₁ * (Real.log (1 / γ) + 3) + c₂)` under the logarithmic
  reflection-cost schedule.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped Real BigOperators
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify
noncomputable section

/-- The normalized unmarked remainder `leftoverState M ψ` has norm at most one. -/
theorem mnrs_leftover_norm_le (M : Submodule ℂ W) (ψ : W) : ‖leftoverState M ψ‖ ≤ 1 := by
  change ‖NormedSpace.normalize (unmarkedPart M ψ)‖ ≤ 1
  by_cases h : unmarkedPart M ψ = 0
  · simp [h]
  · rw [NormedSpace.norm_normalize h]
end
noncomputable section

/-- If the initial state has norm at most one, every state produced by the tolerant attempt
recursion also has norm at most one. -/
theorem mnrs_attempt_norm_le (M : Submodule ℂ W) (A : ℕ → W ≃ₗᵢ[ℂ] W)
    (x₀ : W) (hx : ‖x₀‖ ≤ 1) (i : ℕ) : ‖attemptState M A x₀ i‖ ≤ 1 := by
  cases i with
  | zero => exact hx
  | succ i => exact mnrs_leftover_norm_le M _
end
noncomputable section

/-- For a vector of norm at most one, its marked mass lies in `[0, 1]`. -/
theorem mnrs_marked_mass_bounds (M : Submodule ℂ W) (ψ : W) (hψ : ‖ψ‖ ≤ 1) :
    0 ≤ markedMass M ψ ∧ markedMass M ψ ≤ 1 := by
  have hp : ‖markProj M ψ‖ ≤ 1 := (M.norm_starProjection_apply_le ψ).trans hψ
  unfold markedMass
  constructor
  · positivity
  · nlinarith only [hp, norm_nonneg (markProj M ψ)]
end
noncomputable section

/-- The cumulative tolerant success value is at least the initial marked mass when the initial
state has norm at most one. -/
theorem mnrs_tolerant_success_ge_initial (M : Submodule ℂ W) (A : ℕ → W ≃ₗᵢ[ℂ] W)
    (x₀ : W) (hx : ‖x₀‖ ≤ 1) (n : ℕ) :
    markedMass M x₀ ≤ tolerantSuccess M A x₀ n := by
  have hp := mnrs_marked_mass_bounds M x₀ hx
  have hq (i : ℕ) : 0 ≤ markedMass M (A i (attemptState M A x₀ (i-1))) ∧
      markedMass M (A i (attemptState M A x₀ (i-1))) ≤ 1 := by
    apply mnrs_marked_mass_bounds
    rw [(A i).norm_map]
    exact mnrs_attempt_norm_le M A x₀ hx _
  have hprod : (∏ i ∈ Finset.Icc 1 n,
      (1-markedMass M (A i (attemptState M A x₀ (i-1))))) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (hq i).2) (fun i _ => by linarith [(hq i).1])
  have hm := mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hp.2)
  unfold tolerantSuccess
  linarith
end
noncomputable section

/-- If the initial marked mass is zero, the unmarking operation is the identity on the unmarked
subspace, and each reflection fixes the preceding state, all recursive states through level
`n` equal the initial state. -/
theorem mnrs_zero_mass_raa_fix (M : Submodule ℂ W) (U : W ≃ₗᵢ[ℂ] W)
    (hU : ∀ z ∈ Mᗮ, U z = z) (x₀ : W) (hp : markedMass M x₀ = 0)
    (R : ℕ → W ≃ₗᵢ[ℂ] W) (n : ℕ)
    (hfix : ∀ i, 1 ≤ i → i ≤ n → R i (raaState U R x₀ (i-1)) = raaState U R x₀ (i-1)) :
    ∀ i, i ≤ n → raaState U R x₀ i = x₀ := by
  have hp0 : markProj M x₀ = 0 := by
    apply norm_eq_zero.mp
    have hs : ‖markProj M x₀‖^2 = 0 := hp
    nlinarith only [hs, norm_nonneg (markProj M x₀)]
  have hxM : x₀ ∈ Mᗮ := (Submodule.starProjection_apply_eq_zero_iff M).mp hp0
  have hUx := hU x₀ hxM
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    have hRi := hfix (i+1) (by omega) hi
    simp only [Nat.add_sub_cancel] at hRi
    rw [hprev] at hRi
    change R (i+1) (U (raaState U R x₀ i)) = x₀
    rw [hprev, hUx, hRi]
end
noncomputable section

/-- Under the stated fixed-state hypotheses, zero initial marked mass gives zero tolerant
success through level `n`. -/
theorem mnrs_zero_mass_tolerant_success (M : Submodule ℂ W) (U : W ≃ₗᵢ[ℂ] W)
    (hU : ∀ z ∈ Mᗮ, U z = z) (x₀ : W) (hx : ‖x₀‖ = 1) (hp : markedMass M x₀ = 0)
    (R : ℕ → W ≃ₗᵢ[ℂ] W) (n : ℕ)
    (hfix : ∀ i, 1 ≤ i → i ≤ n → R i (raaState U R x₀ (i-1)) = raaState U R x₀ (i-1)) :
    tolerantSuccess M (raaUnitary U R) x₀ n = 0 := by
  have hraa := mnrs_zero_mass_raa_fix M U hU x₀ hp R n hfix
  have hp0 : markProj M x₀ = 0 := by
    apply norm_eq_zero.mp
    have hs : ‖markProj M x₀‖^2 = 0 := hp
    nlinarith only [hs, norm_nonneg (markProj M x₀)]
  have hleft : leftoverState M x₀ = x₀ := by
    change ‖x₀-markProj M x₀‖⁻¹ • (x₀-markProj M x₀) = x₀
    rw [hp0, sub_zero, hx]
    simp
  have hattempt (i : ℕ) (hi : i ≤ n) : attemptState M (raaUnitary U R) x₀ i = x₀ := by
    induction i with
    | zero => rfl
    | succ i ih =>
      change leftoverState M ((raaUnitary U R (i+1)) (attemptState M (raaUnitary U R) x₀ i)) = x₀
      rw [ih (by omega)]
      change leftoverState M (raaState U R x₀ (i+1)) = x₀
      rw [hraa (i+1) hi, hleft]
  unfold tolerantSuccess
  rw [hp]
  have hq (i : ℕ) (hi : i ∈ Finset.Icc 1 n) :
      markedMass M ((raaUnitary U R i) (attemptState M (raaUnitary U R) x₀ (i-1))) = 0 := by
    have hin := (Finset.mem_Icc.mp hi).2
    rw [hattempt (i-1) (by omega)]
    change markedMass M (raaState U R x₀ i) = 0
    rw [hraa i hin, hp]
  have hprod : (∏ i ∈ Finset.Icc 1 n,
      (1-markedMass M ((raaUnitary U R i) (attemptState M (raaUnitary U R) x₀ (i-1))))) = 1 :=
    Finset.prod_eq_one (fun i hi => by rw [hq i hi]; norm_num)
  rw [hprod]
  norm_num
end
noncomputable section

/-- Bounds the sum of recursive amplification costs through `max tMax 1` by `2 * 3 ^ tMax * (c₁
* (Real.log (1 / γ) + 3) + c₂)` under the logarithmic reflection-cost schedule. -/
theorem mnrs_tolerant_attempt_cost_bound (γ c₁ c₂ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (costR : ℕ → ℝ) (costMark : ℝ) (tMax : ℕ)
    (hcost : ∀ i, 1 ≤ i → i ≤ max tMax 1 → costR i ≤ c₁*Real.log (1/betaAt γ i))
    (hmark : costMark ≤ c₂) :
    (∑ i ∈ Finset.Icc 1 (max tMax 1), raaCost costR costMark i) ≤
      2*(3 : ℝ)^tMax*(c₁*(Real.log (1/γ)+3)+c₂) := by
  let X := c₁*(Real.log (1/γ)+3)+c₂
  have hlog : 0 ≤ Real.log (1/γ) :=
    Real.log_nonneg ((le_div_iff₀ hγ).mpr (by simpa using hγ1))
  have hX : 0 ≤ X := by dsimp [X]; positivity
  by_cases ht : tMax = 0
  · subst tMax
    simp only [Nat.zero_max, Finset.Icc_self, Finset.sum_singleton, pow_zero, mul_one]
    have hl := (hcost 1 le_rfl (by simp)).trans
      (mul_le_mul_of_nonneg_left (mnrs_schedule_log_bound γ hγ 1 le_rfl) hc₁)
    simp only [raaCost, mul_zero, zero_add, Nat.cast_one] at hl ⊢
    nlinarith only [hl, hmark, hc₁, hc₂, mul_nonneg hc₁ hlog]
  · have hn : max tMax 1 = tMax := max_eq_left (by omega)
    rw [hn]
    have hbound (i : ℕ) (hi : i ∈ Finset.Icc 1 tMax) :
        raaCost costR costMark i ≤ (3 : ℝ)^i*X/2 := by
      have hb := mnrs_raa_cost_bound γ c₁ c₂ hγ hc₁ costR costMark i
        (fun j hj hji => hcost j hj (by rw [hn]; exact hji.trans (Finset.mem_Icc.mp hi).2)) hmark
      change raaCost costR costMark i ≤ ((3 : ℝ)^i-1)*X/2-c₁*(i : ℝ) at hb
      exact hb.trans (by nlinarith only [hX, mul_nonneg hc₁ (Nat.cast_nonneg i)])
    have hsum := Finset.sum_le_sum hbound
    have hsubset : (∑ i ∈ Finset.Icc 1 tMax, (3 : ℝ)^i) ≤
        ∑ i ∈ Finset.range (tMax+1), (3 : ℝ)^i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        have := (Finset.mem_Icc.mp hi).2
        exact Finset.mem_range.mpr (by omega)
      · intro i _ _; positivity
    have hgeom : (∑ i ∈ Finset.range (tMax+1), (3 : ℝ)^i)*2+1 = (3 : ℝ)^(tMax+1) := by
      have hg := geom_sum_mul_add (2 : ℝ) (tMax+1)
      norm_num at hg
      exact hg
    have he := congrArg (fun r : ℝ => r*X) hgeom
    rw [pow_succ] at he
    have hprod : 0 ≤ (3 : ℝ)^tMax*X := mul_nonneg (by positivity) hX
    calc
      _ ≤ (∑ i ∈ Finset.Icc 1 tMax, (3 : ℝ)^i*X/2) := hsum
      _ = (∑ i ∈ Finset.Icc 1 tMax, (3 : ℝ)^i)*X/2 := by rw [← Finset.sum_div, ← Finset.sum_mul]
      _ ≤ (∑ i ∈ Finset.range (tMax+1), (3 : ℝ)^i)*X/2 := by gcongr
      _ ≤ 2*(3 : ℝ)^tMax*X := by nlinarith only [he, hX, hprod]
end
noncomputable section

/-- The cumulative tolerant success through `n` is at least the marked mass of any individual
attempt indexed by `j ∈ Finset.Icc 1 n`. -/
theorem mnrs_tolerant_success_ge_attempt (M : Submodule ℂ W) (A : ℕ → W ≃ₗᵢ[ℂ] W)
    (x₀ : W) (hx : ‖x₀‖ ≤ 1) (n j : ℕ) (hj : j ∈ Finset.Icc 1 n) :
    markedMass M (A j (attemptState M A x₀ (j-1))) ≤ tolerantSuccess M A x₀ n := by
  let q := fun i => markedMass M (A i (attemptState M A x₀ (i-1)))
  let f := fun i => 1-q i
  have hp := mnrs_marked_mass_bounds M x₀ hx
  have hq (i : ℕ) : 0 ≤ q i ∧ q i ≤ 1 := by
    apply mnrs_marked_mass_bounds
    rw [(A i).norm_map]
    exact mnrs_attempt_norm_le M A x₀ hx _
  have hf0 (i : ℕ) : 0 ≤ f i := sub_nonneg.mpr (hq i).2
  have hf1 (i : ℕ) : f i ≤ 1 := by dsimp [f]; linarith only [(hq i).1]
  have hprod0 : 0 ≤ ∏ i ∈ Finset.Icc 1 n, f i := Finset.prod_nonneg (fun i _ => hf0 i)
  have hprod : (∏ i ∈ Finset.Icc 1 n, f i) ≤ f j := by
    rw [← Finset.mul_prod_erase _ _ hj]
    exact (mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun i _ => hf0 i)
      (fun i _ => hf1 i)) (hf0 j)).trans_eq (mul_one _)
  have hfail : (1-markedMass M x₀)*(∏ i ∈ Finset.Icc 1 n, f i) ≤ f j := by
    exact (mul_le_mul_of_nonneg_right (by linarith only [hp.1] : 1-markedMass M x₀ ≤ 1)
      hprod0).trans ((one_mul _).le.trans hprod)
  change q j ≤ 1-(1-markedMass M x₀)*(∏ i ∈ Finset.Icc 1 n, f i)
  change (1-markedMass M x₀)*(∏ i ∈ Finset.Icc 1 n, f i) ≤ 1-q j at hfail
  linarith only [hfail]
end
noncomputable section

/-- If no attempt through level `n` has marked mass one, every normalized remainder through that
level is a unit vector. -/
theorem mnrs_attempt_unit_before (M : Submodule ℂ W) (A : ℕ → W ≃ₗᵢ[ℂ] W)
    (x₀ : W) (hx : ‖x₀‖ = 1) (n : ℕ)
    (hno : ∀ j, 1 ≤ j → j ≤ n → markedMass M (A j (attemptState M A x₀ (j-1))) ≠ 1) :
    ∀ i, i ≤ n → ‖attemptState M A x₀ i‖ = 1 := by
  intro i
  induction i with
  | zero => intro _; exact hx
  | succ i ih =>
    intro hi
    let ψ := A (i+1) (attemptState M A x₀ i)
    have hψ : ‖ψ‖ = 1 := by rw [(A (i+1)).norm_map, ih (by omega)]
    have hu : unmarkedPart M ψ ≠ 0 := by
      intro hz
      have hp : markProj M ψ = ψ := (sub_eq_zero.mp hz).symm
      apply hno (i+1) (by omega) hi
      simp only [Nat.add_sub_cancel]
      change ‖markProj M ψ‖^2 = 1
      rw [hp, hψ]; norm_num
    change ‖NormedSpace.normalize (unmarkedPart M ψ)‖ = 1
    exact NormedSpace.norm_normalize hu
end
noncomputable section

/-- The unmarked remainder of a vector in the span of a marked vector `g` and an unmarked vector
`v` is a scalar multiple of `v`. -/
private theorem mnrs_leftover_plane (M : Submodule ℂ W) (g v z : W)
    (hg : g ∈ M) (hv : v ∈ Mᗮ) (hz : z ∈ Submodule.span ℂ ({g,v} : Set W)) :
    ∃ c : ℂ, leftoverState M z = c • v := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
  have hPg : markProj M g = g := Submodule.starProjection_eq_self_iff.mpr hg
  have hPv : markProj M v = 0 := (Submodule.starProjection_apply_eq_zero_iff M).mpr hv
  have hu : unmarkedPart M z = b • v := by
    rw [← hab]
    change (a • g+b • v)-markProj M (a • g+b • v) = b • v
    rw [map_add, map_smul, map_smul, hPg, hPv]
    module
  refine ⟨((‖b • v‖⁻¹ : ℝ) : ℂ)*b, ?_⟩
  unfold leftoverState
  rw [hu, ← Complex.coe_smul, smul_smul]
end
noncomputable section

/-- If each amplification map preserves the good-bad plane, every positive-index remainder
through level `n` is a scalar multiple of the unmarked vector `v`. -/
theorem mnrs_attempt_bad_ray (M : Submodule ℂ W) (g v : W) (hg : g ∈ M) (hv : v ∈ Mᗮ)
    (A : ℕ → W ≃ₗᵢ[ℂ] W) (x₀ : W) (hx : x₀ ∈ Submodule.span ℂ ({g,v} : Set W))
    (n : ℕ)
    (hA : ∀ i, i ≤ n → ∀ z ∈ Submodule.span ℂ ({g,v} : Set W),
      A i z ∈ Submodule.span ℂ ({g,v} : Set W)) :
    ∀ i, 1 ≤ i → i ≤ n → ∃ c : ℂ, attemptState M A x₀ i = c • v := by
  let K := Submodule.span ℂ ({g,v} : Set W)
  have hvK : v ∈ K := Submodule.subset_span (by simp)
  have hrec : ∀ i, i ≤ n → attemptState M A x₀ i ∈ K ∧
      (1 ≤ i → ∃ c : ℂ, attemptState M A x₀ i = c • v) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨hx, fun h => by omega⟩
    | succ i ih =>
      intro hi
      have hprev := (ih (by omega)).1
      have hz := hA (i+1) hi _ hprev
      obtain ⟨c, hc⟩ := mnrs_leftover_plane M g v _ hg hv hz
      change attemptState M A x₀ (i+1) = c • v at hc
      exact ⟨by rw [hc]; exact K.smul_mem _ hvK, fun _ => ⟨c, hc⟩⟩
  intro i hi hin
  exact (hrec i hin).2 hi
end
noncomputable section
omit [FiniteDimensional ℂ W] in

/-- A unit good-bad superposition with nonnegative cosine and squared sine at most `1 / 12` lies
within distance `Real.sqrt (1 / 6)` of its unit unmarked vector. -/
private theorem mnrs_bad_ray_distance (g v x : W) (_hg : ‖g‖ = 1) (hv : ‖v‖ = 1)
    (ho : inner ℂ g v = 0) (hx : ‖x‖ = 1) (θ : ℝ)
    (hdecomp : x = (Real.sin θ : ℂ) • g+(Real.cos θ : ℂ) • v)
    (hcos : 0 ≤ Real.cos θ) (hsmall : (Real.sin θ)^2 ≤ 1/12) :
    ‖x-v‖ ≤ Real.sqrt (1/6) := by
  have hvg : inner ℂ v g = 0 := by rw [← inner_conj_symm, ho, map_zero]
  have hxx : inner ℂ x x = 1 := inner_self_eq_one_of_norm_eq_one hx
  have hvv : inner ℂ v v = 1 := inner_self_eq_one_of_norm_eq_one hv
  have hvx : inner ℂ v x = (Real.cos θ : ℂ) := by
    rw [hdecomp, inner_add_right, inner_smul_right, inner_smul_right, hvg, hvv]
    ring
  have hxv : inner ℂ x v = (Real.cos θ : ℂ) := by
    rw [← inner_conj_symm, hvx, Complex.conj_ofReal]
  have he : inner ℂ (x-v) (x-v) = ((2-2*Real.cos θ : ℝ) : ℂ) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hxx, hvv, hxv, hvx]
    push_cast; ring
  rw [inner_self_eq_norm_sq_to_K] at he
  have hd : ‖x-v‖^2 = 2-2*Real.cos θ := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow] using! he
  have ht := Real.sin_sq_add_cos_sq θ
  have hc := mul_nonneg hcos (sub_nonneg.mpr (Real.cos_le_one θ))
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/6)
  nlinarith only [hd, ht, hc, hsmall, hs, Real.sqrt_nonneg (1/6), norm_nonneg (x-v)]
end
end Qatlib.Concepts.WalkSearch.MnrsAmplify
