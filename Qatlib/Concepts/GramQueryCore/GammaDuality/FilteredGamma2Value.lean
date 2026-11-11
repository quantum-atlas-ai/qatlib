/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredCert.FilteredGamma2
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Filtered γ₂ values and weak duality

This module defines the extended nonnegative filtered value `filteredGamma2`, the approximate
target optimization `stateConversionSDP`, and `gramFunctionEvaluationMatrix`. Certificate
bounds, a block witness-map factorization, and function-evaluation certificates establish weak
duality and the comparison between masked and unmasked query filters used in [LeeEtAl2011].

## Main statements

* `filteredGamma2`: The extended nonnegative infimum of the budgets of Gram filtered
  certificates for `A` relative to `Z`.

* `stateConversionSDP`: The infimum of query-filtered γ₂ distances from `ρ` to positive
  semidefinite targets `σ'` possessing an unfiltered certificate of budget `δ` for `σ' - σ`.

* `filteredGamma2_dual_ge`: Every dual-feasible multiplier gives an operator-norm lower bound on
  the filtered γ₂ value [Lee et al., Lemma A.1][LeeEtAl2011].

* `filteredGamma2_queryDelta_le_of_evalRelaxed`: The unmasked query-filtered γ₂ value is bounded
  by the output-masked value times `2 * (1 - 1 / Fintype.card E)` [Lee et al., Theorem
  3.4][LeeEtAl2011].

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert

namespace Qatlib.Concepts.GramQueryCore.GammaDuality

open Matrix

open scoped ENNReal ComplexOrder

set_option autoImplicit false
set_option linter.unusedSectionVars false

section Definitions

variable {X : Type} {n : ℕ}

/-- The extended nonnegative infimum of the budgets of Gram filtered certificates for `A`
relative to `Z`. -/
noncomputable def filteredGamma2 (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) :
    ℝ≥0∞ :=
  sInf {W : ℝ≥0∞ | ∃ w : ℝ, W = ENNReal.ofReal w ∧ gramFilteredCert A Z w}

/-- The infimum of query-filtered γ₂ distances from `ρ` to positive semidefinite targets `σ'`
possessing an unfiltered certificate of budget `δ` for `σ' - σ`. -/
noncomputable def stateConversionSDP (input : X → Fin n → Bool) (δ : ℝ)
    (ρ σ : Matrix X X ℂ) : ℝ≥0∞ :=
  ⨅ σ' : {σ' : Matrix X X ℂ // σ'.PosSemidef ∧
      gramFilteredCert (σ' - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ},
    filteredGamma2 (ρ - σ'.1) (gramFilterDelta input)

/-- The matrix with entry zero on pairs of equal outputs of `f` and one on pairs of different
outputs. -/
def gramFunctionEvaluationMatrix {E : Type} [DecidableEq E] (f : X → E) :
    Matrix X X ℂ :=
  fun x y => if f x = f y then 0 else 1

end Definitions

/-- A Gram filtered certificate of budget `w` bounds the filtered γ₂ value by `ENNReal.ofReal w`
[LeeEtAl2011]. -/
theorem filteredGamma2_le_of_gramFilteredCert {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {w : ℝ} (h : gramFilteredCert A Z w) :
    filteredGamma2 A Z ≤ ENNReal.ofReal w := by
  unfold filteredGamma2
  exact sInf_le ⟨w, rfl, h⟩

/-- Every real budget strictly above the filtered γ₂ value possesses a Gram filtered certificate
[LeeEtAl2011]. -/
theorem gramFilteredCert_of_filteredGamma2_lt {X : Type} {n : ℕ} {A : Matrix X X ℂ}
    {Z : Fin n → Matrix X X ℂ} {W : ℝ}
    (h : filteredGamma2 A Z < ENNReal.ofReal W) : gramFilteredCert A Z W := by
  by_contra hcon
  have hex : ∃ W₀ ∈ {W₀ : ℝ≥0∞ | ∃ w, W₀ = ENNReal.ofReal w ∧ gramFilteredCert A Z w},
      W₀ < ENNReal.ofReal W := by
    by_contra hnex
    push Not at hnex
    exact absurd (le_antisymm h.le (le_sInf hnex)) h.ne
  obtain ⟨W₀, hW₀mem, hW₀lt⟩ := hex
  obtain ⟨w₀, rfl, hcert⟩ := hW₀mem
  have hw₀ : w₀ < W := by
    by_contra hc
    push Not at hc
    exact absurd (le_antisymm hW₀lt.le (ENNReal.ofReal_le_ofReal hc)) hW₀lt.ne
  exact hcon (gramFilteredCert_mono hcert hw₀.le)

/-- For nonnegative tolerance and a positive semidefinite target, the state-conversion SDP is
bounded by the query-filtered γ₂ distance to that target [LeeEtAl2011]. -/
theorem stateConversionSDP_le_queryDistance {X : Type} {n : ℕ} (input : X → Fin n → Bool)
    {δ : ℝ} (hδ : 0 ≤ δ) {ρ σ : Matrix X X ℂ} (hσ : σ.PosSemidef) :
    stateConversionSDP input δ ρ σ ≤ filteredGamma2 (ρ - σ) (gramFilterDelta input) := by
  have hz : gramFilteredCert (σ - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ := by
    rw [sub_self]
    exact gramFilteredCert_zero _ hδ
  exact iInf_le (fun σ' : {σ' : Matrix X X ℂ // σ'.PosSemidef ∧
      gramFilteredCert (σ' - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ} =>
      filteredGamma2 (ρ - σ'.1) (gramFilterDelta input)) ⟨σ, hσ, hz⟩

/-- Increasing the tolerance can only decrease the state-conversion SDP value [LeeEtAl2011]. -/
theorem stateConversionSDP_mono {X : Type} {n : ℕ} (input : X → Fin n → Bool)
    {δ δ' : ℝ} (h : δ ≤ δ') {ρ σ : Matrix X X ℂ} :
    stateConversionSDP input δ' ρ σ ≤ stateConversionSDP input δ ρ σ := by
  refine le_iInf fun σ' => ?_
  exact iInf_le (fun σ'' : {σ'' : Matrix X X ℂ // σ''.PosSemidef ∧
      gramFilteredCert (σ'' - σ) (fun _ : Fin 1 => gramFilterAllOnes) δ'} =>
      filteredGamma2 (ρ - σ''.1) (gramFilterDelta input))
    ⟨σ'.1, σ'.2.1, gramFilteredCert_mono σ'.2.2 h⟩

/-- A finite sum with one distinguished summand equals that summand plus the common remaining
value times the number of other indices. -/
private theorem sum_if_single {E : Type} [DecidableEq E] [Fintype E] (e₀ : E) (a b : ℝ) :
    ∑ e : E, (if e₀ = e then a else b) = a + ((Fintype.card E - 1 : ℕ) : ℝ) * b := by
  classical
  have h1 : ∑ e ∈ Finset.univ.erase e₀, b + (if e₀ = e₀ then a else b)
      = ∑ e : E, (if e₀ = e then a else b) := by
    rw [← Finset.sum_erase_add Finset.univ (fun e => if e₀ = e then a else b : E → ℝ)
      (Finset.mem_univ e₀)]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase he))]
  rw [← h1, if_pos rfl, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ e₀), Finset.card_univ]
  ring

/-- A finite sum with two distinct distinguished indices equals their two values plus the common
remaining value times the number of other indices. -/
private theorem sum_if_two {E : Type} [DecidableEq E] [Fintype E] {e₁ e₂ : E} (h : e₁ ≠ e₂)
    (hcard : 2 ≤ Fintype.card E) (a b c : ℝ) :
    ∑ e : E, (if e₁ = e then a else if e₂ = e then b else c)
      = a + b + ((Fintype.card E - 2 : ℕ) : ℝ) * c := by
  classical
  have he₂ : e₂ ∈ Finset.univ.erase e₁ :=
    Finset.mem_erase.mpr ⟨Ne.symm h, Finset.mem_univ e₂⟩
  have h1 : ∑ e ∈ Finset.univ.erase e₁, (if e₂ = e then b else c)
        + (if e₁ = e₁ then a else if e₂ = e₁ then b else c)
      = ∑ e : E, (if e₁ = e then a else if e₂ = e then b else c) := by
    rw [← Finset.sum_erase_add Finset.univ
      (fun e => if e₁ = e then a else if e₂ = e then b else c : E → ℝ)
      (Finset.mem_univ e₁)]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase he))]
  have h2 : ∑ e ∈ (Finset.univ.erase e₁).erase e₂, c + (if e₂ = e₂ then b else c)
      = ∑ e ∈ Finset.univ.erase e₁, (if e₂ = e then b else c) := by
    rw [← Finset.sum_erase_add (Finset.univ.erase e₁)
      (fun e => if e₂ = e then b else c : E → ℝ) he₂]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [if_neg (Ne.symm (Finset.ne_of_mem_erase he))]
  have hsub : (Fintype.card E - 1 - 1 : ℕ) = Fintype.card E - 2 := by omega
  rw [← h1, ← h2, if_pos rfl, if_pos rfl, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem he₂, Finset.card_erase_of_mem (Finset.mem_univ e₁),
    Finset.card_univ, hsub]
  ring

/-- The function-evaluation matrix has an unfiltered certificate of budget `2 * (1 - 1 /
Fintype.card E)` [LeeEtAl2011]. -/
theorem gramFilteredCert_gramFunctionEvaluation {X E : Type} [Fintype E] [DecidableEq E]
    (f : X → E) :
    gramFilteredCert (gramFunctionEvaluationMatrix f) (fun _ : Fin 1 => gramFilterAllOnes)
      (2 * (1 - 1 / (Fintype.card E : ℝ))) := by
  classical
  rcases Nat.lt_trichotomy (Fintype.card E) 1 with h0 | h1 | h2n
  · have hcard : Fintype.card E = 0 := Nat.lt_one_iff.mp h0
    have hE : IsEmpty E := Fintype.card_eq_zero_iff.mp hcard
    have hX : IsEmpty X := Function.isEmpty f
    have hzero : gramFunctionEvaluationMatrix f = 0 := by
      ext x y
      exact (hX.false x).elim
    have hc : ((Fintype.card E : ℕ) : ℝ) = 0 := by exact_mod_cast hcard
    rw [hzero]
    refine gramFilteredCert_zero _ ?_
    rw [hc]
    norm_num
  · haveI hsub : Subsingleton E := Equiv.subsingleton (Fintype.equivFinOfCardEq h1)
    have hzero : gramFunctionEvaluationMatrix f = 0 := by
      ext x y
      simp only [gramFunctionEvaluationMatrix, if_pos (Subsingleton.elim (f x) (f y)),
        Matrix.zero_apply]
    have hc : ((Fintype.card E : ℕ) : ℝ) = 1 := by exact_mod_cast h1
    rw [hzero]
    refine gramFilteredCert_zero _ ?_
    rw [hc]
    norm_num
  · have hcard2 : 2 ≤ Fintype.card E := h2n
    have hk : (2 : ℝ) ≤ (Fintype.card E : ℝ) := by exact_mod_cast hcard2
    set k : ℝ := (Fintype.card E : ℝ) with hkdef
    have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_two hk
    have hk1 : 0 < k - 1 := by linarith
    set s : ℝ := Real.sqrt (k - 1) with hsdef
    have hs2 : s ^ 2 = k - 1 := Real.sq_sqrt hk1.le
    have hs0 : 0 < s := Real.sqrt_pos_of_pos hk1
    have hk4 : 4 * (k - 1) ≤ k ^ 2 := by nlinarith [sq_nonneg (k - 2)]
    have hsle : s ≤ k / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have h4 : (k / 2) ^ 2 = k ^ 2 / 4 := by field_simp; ring
      rw [h4]
      nlinarith [hk4]
    set α : ℝ := Real.sqrt (1 / 2 - s / k) with hαdef
    have hαnn : (0 : ℝ) ≤ 1 / 2 - s / k := by
      have h1 : s / k ≤ 1 / 2 := by
        rw [div_le_iff₀ hk0]
        linarith [hsle]
      linarith
    have hα2 : α ^ 2 = 1 / 2 - s / k := Real.sq_sqrt hαnn
    have hα0 : 0 ≤ α := Real.sqrt_nonneg _
    set γ : ℝ := Real.sqrt (1 / 2 + s / k) with hγdef
    have hγ2 : γ ^ 2 = 1 / 2 + s / k := Real.sq_sqrt (by positivity)
    have hγ0 : 0 ≤ γ := Real.sqrt_nonneg _
    set c : ℝ := Real.sqrt (2 * (1 - 1 / k)) with hcdef
    have hc2 : c ^ 2 = 2 * (1 - 1 / k) := by
      refine Real.sq_sqrt ?_
      have h1 : 1 / k ≤ 1 := by
        rw [div_le_iff₀ hk0]
        linarith
      nlinarith [hk0.le]
    have hc0 : 0 ≤ c := Real.sqrt_nonneg _
    have hne0 : k ≠ 0 := ne_of_gt hk0
    have hne1 : k - 1 ≠ 0 := ne_of_gt hk1
    have hαγ : α * γ = (k - 2) / (2 * k) := by
      have hsq : (α * γ) ^ 2 = ((k - 2) / (2 * k)) ^ 2 := by
        have h1 : (α * γ) ^ 2 = α ^ 2 * γ ^ 2 := by ring
        rw [h1, hα2, hγ2]
        have h3 : (1 / 2 - s / k) * (1 / 2 + s / k) = 1 / 4 - s ^ 2 / k ^ 2 := by ring
        rw [h3, hs2]
        field_simp
        ring
      have hnng : 0 ≤ α * γ := mul_nonneg hα0 hγ0
      have hnng2 : 0 ≤ (k - 2) / (2 * k) :=
        div_nonneg (by linarith) (by positivity)
      rw [← Real.sqrt_sq hnng, ← Real.sqrt_sq hnng2, hsq]
    have hcast1 : ((Fintype.card E - 1 : ℕ) : ℝ) = k - 1 := by
      rw [hkdef, Nat.cast_sub (by omega : 1 ≤ Fintype.card E), Nat.cast_one]
    have hcast2 : ((Fintype.card E - 2 : ℕ) : ℝ) = k - 2 := by
      rw [hkdef, Nat.cast_sub hcard2, Nat.cast_two]
    have hmassid : α ^ 2 + (k - 1) * (γ / s) ^ 2 = 1 := by
      rw [div_pow, hs2,
        show (k - 1) * (γ ^ 2 / (k - 1)) = γ ^ 2 by field_simp, hα2, hγ2]
      ring
    have hmassid' : γ ^ 2 + (k - 1) * (α / s) ^ 2 = 1 := by
      rw [div_pow, hs2,
        show (k - 1) * (α ^ 2 / (k - 1)) = α ^ 2 by field_simp, hα2, hγ2]
      ring
    have hinner : ∀ x y : X,
        ∑ e : E, (if f x = e then -α else γ / s) * (if f y = e then γ else α / s)
          = if f x = f y then -α * γ + (k - 1) * ((γ / s) * (α / s)) else
              (-α) * (α / s) + (γ / s) * γ + (k - 2) * ((γ / s) * (α / s)) := by
      intro x y
      by_cases hxy : f x = f y
      · have hterm : ∀ e : E,
            (if f x = e then -α else γ / s) * (if f y = e then γ else α / s)
            = if f x = e then (-α) * γ else (γ / s) * (α / s) := by
          intro e
          by_cases h : f x = e
          · simp only [if_pos h, if_pos (hxy.symm.trans h)]
          · simp only [if_neg h, if_neg (fun hc => h (hxy.trans hc))]
        rw [Finset.sum_congr rfl fun e _ => hterm e, sum_if_single (f x) _ _, hcast1,
          if_pos hxy]
      · have hterm : ∀ e : E,
            (if f x = e then -α else γ / s) * (if f y = e then γ else α / s)
            = if f x = e then (-α) * (α / s) else
              if f y = e then (γ / s) * γ else (γ / s) * (α / s) := by
          intro e
          by_cases h1 : f x = e
          · simp only [if_pos h1, if_neg (fun hc : f y = e => hxy (h1.trans hc.symm))]
          · by_cases h2 : f y = e
            · simp only [if_neg h1, if_pos h2]
            · simp only [if_neg h1, if_neg h2]
        rw [Finset.sum_congr rfl fun e _ => hterm e, sum_if_two hxy hcard2 _ _ _,
          hcast2, if_neg hxy]
    refine ⟨E, inferInstance,
      fun _ x e => ((c * (if f x = e then -α else γ / s) : ℝ) : ℂ),
      fun _ y e => ((c * (if f y = e then γ else α / s) : ℝ) : ℂ), ?_, ?_, ?_⟩
    · intro x
      simp only [Fin.sum_univ_one]
      have hterm : ∀ e : E,
          Complex.normSq (((c * (if f x = e then -α else γ / s) : ℝ) : ℂ))
          = c ^ 2 * (if f x = e then α ^ 2 else (γ / s) ^ 2) := by
        intro e
        rw [Complex.normSq_ofReal]
        by_cases h : f x = e
        · simp only [if_pos h]; ring
        · simp only [if_neg h]; ring
      rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.mul_sum,
        sum_if_single (f x) _ _, hcast1, hmassid, hc2, mul_one]
    · intro y
      simp only [Fin.sum_univ_one]
      have hterm : ∀ e : E,
          Complex.normSq (((c * (if f y = e then γ else α / s) : ℝ) : ℂ))
          = c ^ 2 * (if f y = e then γ ^ 2 else (α / s) ^ 2) := by
        intro e
        rw [Complex.normSq_ofReal]
        by_cases h : f y = e
        · simp only [if_pos h]; ring
        · simp only [if_neg h]; ring
      rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.mul_sum,
        sum_if_single (f y) _ _, hcast1, hmassid', hc2, mul_one]
    · intro x y
      simp only [Fin.sum_univ_one, gramFilterAllOnes, one_mul]
      rw [gramFunctionEvaluationMatrix, dotProduct]
      simp only [Pi.star_apply, RCLike.star_def]
      have hcast : ∀ e : E,
          starRingEnd ℂ (((c * (if f x = e then -α else γ / s) : ℝ) : ℂ)) *
            (((c * (if f y = e then γ else α / s) : ℝ) : ℂ))
          = ((c * c * ((if f x = e then -α else γ / s) *
              (if f y = e then γ else α / s)) : ℝ) : ℂ) := by
        intro e
        simp only [Complex.conj_ofReal, ← Complex.ofReal_mul]
        exact congrArg ((↑) : ℝ → ℂ) (by ring)
      rw [Finset.sum_congr rfl fun e _ => hcast e, ← Complex.ofReal_sum, ← Finset.mul_sum,
        hinner x y]
      by_cases hxy : f x = f y
      · rw [if_pos hxy, if_pos hxy]
        have hz : c * c * (-α * γ + (k - 1) * ((γ / s) * (α / s))) = 0 := by
          rw [show (γ / s) * (α / s) = α * γ / s ^ 2 by field_simp, hs2,
            show (k - 1) * (α * γ / (k - 1)) = α * γ by field_simp]
          ring
        rw [hz]
        norm_num
      · rw [if_neg hxy, if_neg hxy]
        have hone : c * c * ((-α) * (α / s) + (γ / s) * γ + (k - 2) * ((γ / s) * (α / s)))
            = 1 := by
          have e0 : (γ / s) * (α / s) = α * γ / s ^ 2 := by field_simp
          have e1 : (-α) * (α / s) + (γ / s) * γ + (k - 2) * (α * γ / s ^ 2)
              = (γ ^ 2 - α ^ 2) / s + (k - 2) * (α * γ) / s ^ 2 := by
            field_simp
            ring
          rw [e0, e1, show γ ^ 2 - α ^ 2 = 2 * s / k by rw [hγ2, hα2]; ring, hαγ, hs2,
            show c * c = c ^ 2 by ring, hc2,
            show 2 * s / k / s = 2 / k by field_simp]
          field_simp
          ring
        rw [hone, Complex.ofReal_one]

open scoped Matrix.Norms.L2Operator

section Dual

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The norm of a Hermitian pairing is bounded by the product of the square roots of the two
squared-mass sums. -/
private theorem abs_dotProduct_le {Q : Type} [Fintype Q] [DecidableEq Q] (a b : Q → ℂ) :
    ‖(star a ⬝ᵥ b : ℂ)‖ ≤ Real.sqrt (∑ q, Complex.normSq (a q)) *
      Real.sqrt (∑ q, Complex.normSq (b q)) := by
  have h1 : ‖toEuclidean_fromVec a‖ = Real.sqrt (∑ q, Complex.normSq (a q)) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toEuclidean_fromVec_sq]
    exact congrArg Real.sqrt
      (Finset.sum_congr rfl fun q _ => (Complex.normSq_eq_norm_sq _).symm)
  have h2 : ‖toEuclidean_fromVec b‖ = Real.sqrt (∑ q, Complex.normSq (b q)) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_toEuclidean_fromVec_sq]
    exact congrArg Real.sqrt
      (Finset.sum_congr rfl fun q _ => (Complex.normSq_eq_norm_sq _).symm)
  rw [show (star a ⬝ᵥ b : ℂ) = Inner a b from rfl, ← inner_euclidean_fromVec]
  calc ‖inner ℂ (toEuclidean_fromVec a) (toEuclidean_fromVec b)‖
      ≤ ‖toEuclidean_fromVec a‖ * ‖toEuclidean_fromVec b‖ :=
        norm_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ Real.sqrt (∑ q, Complex.normSq (a q)) * Real.sqrt (∑ q, Complex.normSq (b q)) := by
        rw [h1, h2]

/-- A filtered factorization with budget `W` and a dual-feasible multiplier bound every entry of
the resulting entrywise product by `max W 0`. -/
private theorem hadamard_entry_le {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ} (W : ℝ)
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (M : Matrix X X ℂ)
    (u v : Fin n → X → Q → ℂ)
    (hu : ∀ x, ∑ j, ∑ q, Complex.normSq (u j x q) ≤ W)
    (hv : ∀ y, ∑ j, ∑ q, Complex.normSq (v j y q) ≤ W)
    (huv : ∀ x y, A x y = ∑ j, Z j x y * (star (u j x) ⬝ᵥ v j y))
    (hM : ∀ j, ‖(fun x y => Z j x y * M x y : Matrix X X ℂ)‖ ≤ 1) (x y : X) :
    ‖(fun x' y' => A x' y' * M x' y' : Matrix X X ℂ) x y‖ ≤ max W 0 := by
  classical
  have hentry : (fun x' y' => A x' y' * M x' y' : Matrix X X ℂ) x y
      = ∑ j, (Z j x y * M x y) * (star (u j x) ⬝ᵥ v j y) := by
    simp only [huv]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hfeas : ∀ j, ‖Z j x y * M x y‖ ≤ 1 := by
    intro j
    have h1 := (pi_norm_le_iff_of_nonneg zero_le_one).mp (hM j)
    have h2 := (pi_norm_le_iff_of_nonneg zero_le_one).mp (h1 x)
    exact h2 y
  have hterm : ∀ j, ‖(Z j x y * M x y) * (star (u j x) ⬝ᵥ v j y)‖
      ≤ Real.sqrt (∑ q, Complex.normSq (u j x q)) *
        Real.sqrt (∑ q, Complex.normSq (v j y q)) := by
    intro j
    have hcs := abs_dotProduct_le (u j x) (v j y)
    calc ‖(Z j x y * M x y) * (star (u j x) ⬝ᵥ v j y)‖
        ≤ ‖Z j x y * M x y‖ * ‖star (u j x) ⬝ᵥ v j y‖ := norm_mul_le _ _
      _ ≤ 1 * ‖star (u j x) ⬝ᵥ v j y‖ := by
          exact mul_le_mul_of_nonneg_right (hfeas j) (norm_nonneg _)
      _ = ‖star (u j x) ⬝ᵥ v j y‖ := one_mul _
      _ ≤ Real.sqrt (∑ q, Complex.normSq (u j x q)) *
            Real.sqrt (∑ q, Complex.normSq (v j y q)) := hcs
  have hsum : ∑ j, Real.sqrt (∑ q, Complex.normSq (u j x q)) *
        Real.sqrt (∑ q, Complex.normSq (v j y q))
      ≤ max W 0 := by
    have h1 := Real.sum_sqrt_mul_sqrt_le
      (f := fun j => ∑ q, Complex.normSq (u j x q))
      (g := fun j => ∑ q, Complex.normSq (v j y q)) Finset.univ
      (fun _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      (fun _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    have h2 : Real.sqrt (∑ j, ∑ q, Complex.normSq (u j x q)) *
          Real.sqrt (∑ j, ∑ q, Complex.normSq (v j y q))
        ≤ max W 0 := by
      have hW' : (0 : ℝ) ≤ max W 0 := le_max_right W 0
      have hmu : (0 : ℝ) ≤ ∑ j, ∑ q, Complex.normSq (u j x q) :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
      have hmv : (0 : ℝ) ≤ ∑ j, ∑ q, Complex.normSq (v j y q) :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
      have hprod : (∑ j, ∑ q, Complex.normSq (u j x q)) * (∑ j, ∑ q, Complex.normSq (v j y q))
          ≤ max W 0 * max W 0 :=
        mul_le_mul ((hu x).trans (le_max_left W 0)) ((hv y).trans (le_max_left W 0)) hmv
          (le_max_right W 0)
      calc Real.sqrt (∑ j, ∑ q, Complex.normSq (u j x q)) *
            Real.sqrt (∑ j, ∑ q, Complex.normSq (v j y q))
          = Real.sqrt ((∑ j, ∑ q, Complex.normSq (u j x q)) *
              (∑ j, ∑ q, Complex.normSq (v j y q))) := (Real.sqrt_mul hmu _).symm
        _ ≤ Real.sqrt (max W 0 * max W 0) := Real.sqrt_le_sqrt hprod
        _ = max W 0 := by
            rw [Real.sqrt_mul (le_max_right W 0) (max W 0),
              Real.mul_self_sqrt (le_max_right W 0)]
    exact h1.trans h2
  calc ‖(fun x' y' => A x' y' * M x' y' : Matrix X X ℂ) x y‖
      = ‖∑ j, (Z j x y * M x y) * (star (u j x) ⬝ᵥ v j y)‖ := by rw [hentry]
    _ ≤ ∑ j, ‖(Z j x y * M x y) * (star (u j x) ⬝ᵥ v j y)‖ := norm_sum_le _ _
    _ ≤ ∑ j, Real.sqrt (∑ q, Complex.normSq (u j x q)) *
          Real.sqrt (∑ q, Complex.normSq (v j y q)) := Finset.sum_le_sum fun j _ => hterm j
    _ ≤ max W 0 := hsum

/-- The operator norm of a dual-feasible entrywise product, viewed in the extended nonnegative
reals, is bounded by the filtered γ₂ value. -/
theorem filteredGamma2_entrywise_dual_ge {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (M : Matrix X X ℂ)
    (hM : ∀ j, ‖(fun x y => Z j x y * M x y : Matrix X X ℂ)‖ ≤ 1) :
    ENNReal.ofReal ‖(fun x y => A x y * M x y : Matrix X X ℂ)‖ ≤ filteredGamma2 A Z := by
  classical
  unfold filteredGamma2
  refine le_sInf fun W hW => ?_
  obtain ⟨w, rfl, hcert⟩ := hW
  rcases hcert with ⟨Q, hQ, u, v, hu, hv, huv⟩
  have hsup : ‖(fun x y => A x y * M x y : Matrix X X ℂ)‖ ≤ max w 0 := by
    rw [pi_norm_le_iff_of_nonneg (le_max_right w 0)]
    intro x
    rw [pi_norm_le_iff_of_nonneg (le_max_right w 0)]
    intro y
    exact hadamard_entry_le w A Z M u v hu hv huv hM x y
  refine le_trans (ENNReal.ofReal_le_ofReal hsup) ?_
  have hmax : ENNReal.ofReal (max w 0) = ENNReal.ofReal w := by
    rcases le_or_gt 0 w with h | h
    · rw [max_eq_left h]
    · have h0 : ENNReal.ofReal w = 0 := ENNReal.ofReal_eq_zero.mpr h.le
      rw [max_eq_right h.le, h0, ENNReal.ofReal_zero]
  rw [hmax]

/-- The matrix placing each filtered witness in the block corresponding to its input index and
zero in the other input blocks. -/
private def filteredWitnessMap {Q : Type} [Fintype Q] {n : ℕ}
    (u : Fin n → X → Q → ℂ) : Matrix (X × (Fin n × Q)) X ℂ :=
  fun r y => if r.1 = y then u r.2.1 r.1 r.2.2 else 0

/-- The Gram matrix of the block witness map is diagonal, with entries equal to the total
squared witness mass at each input. -/
private theorem filteredWitnessMap_gram {Q : Type} [Fintype Q] {n : ℕ}
    (u : Fin n → X → Q → ℂ) :
    (filteredWitnessMap u)ᴴ * filteredWitnessMap u =
      Matrix.diagonal (fun x => ((∑ j, ∑ q, Complex.normSq (u j x q) : ℝ) : ℂ)) := by
  classical
  ext x y
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    filteredWitnessMap]
  rw [Finset.sum_eq_single x]
  · by_cases h : x = y
    · subst y
      simp only [ite_true,Matrix.diagonal_apply_eq]
      simp [mul_comm, Complex.mul_conj]
    · simp [h]
  · intro z _ hz
    simp [hz]
  · simp

/-- A witness map with squared-mass budget `W` has operator norm at most `Real.sqrt (max W 0)`. -/
private theorem filteredWitnessMap_norm {Q : Type} [Fintype Q] {n : ℕ}
    (u : Fin n → X → Q → ℂ) (W : ℝ)
    (hu : ∀ x, ∑ j, ∑ q, Complex.normSq (u j x q) ≤ W) :
    ‖filteredWitnessMap u‖ ≤ Real.sqrt (max W 0) := by
  classical
  have hmass : ‖Matrix.diagonal (fun x =>
      ((∑ j, ∑ q, Complex.normSq (u j x q) : ℝ) : ℂ))‖ ≤ max W 0 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (le_max_right W 0)).mpr
    intro x
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    · exact (hu x).trans (le_max_left W 0)
    · exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  rw [← filteredWitnessMap_gram,Matrix.l2_opNorm_conjTranspose_mul_self] at hmass
  have hs := Real.sq_sqrt (le_max_right W 0)
  nlinarith [norm_nonneg (filteredWitnessMap u),Real.sqrt_nonneg (max W 0)]

/-- Applying a block-diagonal matrix acts on each block slice by the corresponding component
matrix. -/
private theorem blockDiagonal_slice {B : Type} [Fintype B] [DecidableEq B]
    (N : B → Matrix X X ℂ) (s : QState (X × B)) (x : X) (b : B) :
    (Matrix.blockDiagonal N *ᵥ s) (x,b) = (N b *ᵥ (fun y => s (y,b))) x := by
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.blockDiagonal_apply]
  simp [ite_mul]

/-- A block-diagonal matrix is a contraction when every component block is a contraction. -/
private theorem blockDiagonal_contraction {B : Type} [Fintype B] [DecidableEq B]
    (N : B → Matrix X X ℂ) (hN : ∀ b, ‖N b‖ ≤ 1) :
    ‖Matrix.blockDiagonal N‖ ≤ 1 := by
  apply l2_opNorm_le_of_mulVec_le zero_le_one
  intro s
  have hs : (∑ r, ‖(Matrix.blockDiagonal N *ᵥ s) r‖^2) ≤ ∑ r, ‖s r‖^2 := by
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro b _
    have h := l2_norm_mulVec_fromVec_le (N b) (fun y => s (y,b))
    have hb := h.trans (mul_le_of_le_one_left (norm_nonneg _) (hN b))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [norm_toEuclidean_fromVec_sq,norm_toEuclidean_fromVec_sq] at hsq
    simpa only [blockDiagonal_slice] using hsq
  rw [← norm_toEuclidean_fromVec_sq,← norm_toEuclidean_fromVec_sq] at hs
  simp only [one_mul]
  nlinarith [norm_nonneg (toEuclidean_fromVec (Matrix.blockDiagonal N *ᵥ s)),
    norm_nonneg (toEuclidean_fromVec s)]

/-- A filtered factorization expresses `A ⊙ M` as the product of the adjoint row witness map,
the block-diagonal filtered multipliers, and the column witness map. -/
private theorem filteredWitnessMap_factor {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (M : Matrix X X ℂ)
    (u v : Fin n → X → Q → ℂ)
    (huv : ∀ x y, A x y = ∑ j, Z j x y * (star (u j x) ⬝ᵥ v j y)) :
    A ⊙ M = (filteredWitnessMap u)ᴴ *
      Matrix.blockDiagonal (fun jq : Fin n × Q => Z jq.1 ⊙ M) * filteredWitnessMap v := by
  classical
  have hDV (z : X) (j : Fin n) (q : Q) (y : X) :
      (Matrix.blockDiagonal (fun jq : Fin n × Q => Z jq.1 ⊙ M) *
        filteredWitnessMap v) (z,(j,q)) y = Z j z y * M z y * v j y q := by
    simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.blockDiagonal_apply,
      filteredWitnessMap,Matrix.hadamard_apply]
    simp [ite_mul,mul_ite,ite_and]
  rw [Matrix.mul_assoc]
  ext x y
  simp only [Matrix.hadamard_apply,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.conjTranspose_apply,hDV,filteredWitnessMap]
  rw [Finset.sum_eq_single x]
  · simp only [ite_true]
    rw [huv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dotProduct,Finset.mul_sum,Finset.sum_mul,Pi.star_apply]
    apply Finset.sum_congr rfl
    intro q _
    ring
  · intro z _ hz
    simp [hz]
  · simp

set_option maxHeartbeats 800000 in

/-- Every dual-feasible multiplier gives an operator-norm lower bound on the filtered γ₂ value
[Lee et al., Lemma A.1][LeeEtAl2011]. -/
theorem filteredGamma2_dual_ge {X : Type} [Fintype X] [DecidableEq X] {n : ℕ}
    (A : Matrix X X ℂ) (Z : Fin n → Matrix X X ℂ) (M : Matrix X X ℂ)
    (hM : ∀ j, ‖Z j ⊙ M‖ ≤ 1) :
    ENNReal.ofReal ‖A ⊙ M‖ ≤ filteredGamma2 A Z := by
  classical
  unfold filteredGamma2
  refine le_sInf fun W hW => ?_
  obtain ⟨w,rfl,hcert⟩ := hW
  rcases hcert with ⟨Q,hQ,u,v,hu,hv,huv⟩
  let U := filteredWitnessMap u
  let V := filteredWitnessMap v
  let D := Matrix.blockDiagonal (fun jq : Fin n × Q => Z jq.1 ⊙ M)
  have hU : ‖U‖ ≤ Real.sqrt (max w 0) := filteredWitnessMap_norm u w hu
  have hV : ‖V‖ ≤ Real.sqrt (max w 0) := filteredWitnessMap_norm v w hv
  have hD : ‖D‖ ≤ 1 := blockDiagonal_contraction _ (fun jq => hM jq.1)
  have hbound : ‖A ⊙ M‖ ≤ max w 0 := by
    rw [filteredWitnessMap_factor A Z M u v huv]
    change ‖Uᴴ * D * V‖ ≤ max w 0
    calc _ ≤ ‖Uᴴ * D‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖D‖) * ‖V‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = (‖U‖ * ‖D‖) * ‖V‖ := by rw [Matrix.l2_opNorm_conjTranspose]
      _ ≤ (Real.sqrt (max w 0) * 1) * Real.sqrt (max w 0) :=
        mul_le_mul (mul_le_mul hU hD (norm_nonneg _) (Real.sqrt_nonneg _)) hV
          (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) zero_le_one)
      _ = max w 0 := by rw [mul_one,Real.mul_self_sqrt (le_max_right w 0)]
  refine (ENNReal.ofReal_le_ofReal hbound).trans ?_
  simp only [ENNReal.ofReal_max,ENNReal.ofReal_zero]
  exact max_le le_rfl bot_le

/-- A feasible matrix vanishing on pairs of equal function outputs has norm bounded by the
query-filtered γ₂ value of the function-evaluation matrix [LeeEtAl2011]. -/
theorem adversary_le_filteredGamma2_queryDelta {X : Type} [Fintype X] [DecidableEq X]
    {E : Type} [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E)
    (Γ : Matrix X X ℂ) (hzero : ∀ x y, f x = f y → Γ x y = 0)
    (hfeas : ∀ j, ‖gramFilterDelta input j ⊙ Γ‖ ≤ 1) :
    ENNReal.ofReal ‖Γ‖ ≤ filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) := by
  have he : gramFunctionEvaluationMatrix f ⊙ Γ = Γ := by
    ext x y
    by_cases h : f x = f y <;> simp [gramFunctionEvaluationMatrix,Matrix.hadamard_apply,h,hzero x y]
  simpa only [he] using
      filteredGamma2_dual_ge (gramFunctionEvaluationMatrix f) (gramFilterDelta input) Γ hfeas

end Dual

/-- A certificate using output-masked query filters gives an unmasked certificate after
multiplying its budget by `2 * (1 - 1 / Fintype.card E)` [LeeEtAl2011]. -/
theorem gramFilteredCert_queryDelta_of_evalRelaxed {X : Type} [Fintype X] [DecidableEq X]
    {E : Type} [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E)
    {W : ℝ} (h : gramFilteredCert (gramFunctionEvaluationMatrix f)
        (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) W) :
    gramFilteredCert (gramFunctionEvaluationMatrix f) (gramFilterDelta input)
      (W * (2 * (1 - 1 / (Fintype.card E : ℝ)))) :=
  gramFilteredCert_hadamard_le h (gramFilteredCert_gramFunctionEvaluation f)

/-- The unmasked query-filtered γ₂ value is bounded by the output-masked value times `2 * (1 - 1
/ Fintype.card E)` [Lee et al., Theorem 3.4][LeeEtAl2011]. -/
theorem filteredGamma2_queryDelta_le_of_evalRelaxed {X : Type} [Fintype X] [DecidableEq X]
    {E : Type} [Fintype E] [DecidableEq E] {n : ℕ} (input : X → Fin n → Bool) (f : X → E) :
    filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ≤
      ENNReal.ofReal (2 * (1 - 1 / (Fintype.card E : ℝ))) *
        filteredGamma2 (gramFunctionEvaluationMatrix f)
          (fun j x y => gramFilterDelta input j x y *
            gramFunctionEvaluationMatrix f x y) := by
  classical
  rcases le_or_gt (Fintype.card E) 1 with hle | hgt
  · have hconst : ∀ x y : X, f x = f y := by
      rcases Nat.lt_or_ge (Fintype.card E) 1 with h0 | h1
      · have hE : IsEmpty E := Fintype.card_eq_zero_iff.mp (Nat.lt_one_iff.mp h0)
        intro x y
        exact (hE.false (f x)).elim
      · haveI : Subsingleton E :=
          Equiv.subsingleton (Fintype.equivFinOfCardEq (by omega : Fintype.card E = 1))
        intro x y
        exact Subsingleton.elim _ _
    have hzero : gramFunctionEvaluationMatrix f = 0 := by
      ext x y
      simp only [gramFunctionEvaluationMatrix, if_pos (hconst x y), Matrix.zero_apply]
    have hL : filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input)
        ≤ ENNReal.ofReal 0 := by
      rw [hzero]
      exact filteredGamma2_le_of_gramFilteredCert (gramFilteredCert_zero _ le_rfl)
    refine hL.trans ?_
    simp
  · have hk0 : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast (by omega : (0:ℕ) < Fintype.card E)
    have hk1 : (1 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast hgt
    have hcpos : (0 : ℝ) < 2 * (1 - 1 / (Fintype.card E : ℝ)) := by
      have h1 : (1 : ℝ) / (Fintype.card E : ℝ) < 1 := by
        rw [div_lt_iff₀ hk0]
        linarith
      have h2 : (0 : ℝ) < 1 - 1 / (Fintype.card E : ℝ) := by linarith
      nlinarith [h2]
    have hcne : ENNReal.ofReal (2 * (1 - 1 / (Fintype.card E : ℝ))) ≠ 0 := by
      simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using hcpos
    conv_rhs =>
      rw [filteredGamma2, sInf_eq_iInf, ENNReal.mul_iInf_of_ne hcne ENNReal.ofReal_ne_top]
    refine le_iInf fun W => ?_
    rw [ENNReal.mul_iInf_of_ne hcne ENNReal.ofReal_ne_top]
    refine le_iInf fun hW => ?_
    obtain ⟨w, rfl, hcert⟩ := hW
    have h := filteredGamma2_le_of_gramFilteredCert
      (gramFilteredCert_queryDelta_of_evalRelaxed input f hcert)
    simpa only [mul_comm w, ENNReal.ofReal_mul hcpos.le] using h

end Qatlib.Concepts.GramQueryCore.GammaDuality
