/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module


public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

@[expose] public section

/-!
# The operator and Krylov components of genuine Hamiltonian truncation

These results retain the actual projected Hamiltonian P H P. They prove that orthogonality to
the complement forces the first Krylov vectors into the projection range, and hence the first
Taylor terms of the two dynamics coincide. The time evolution is the real operator exponential
and its norm preservation follows from self-adjointness, not an abstract output field.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UniversalWalk12.MainResults.Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The complement of an idempotent projection is itself idempotent. -/
theorem complement_idem (P : E →L[ℂ] E) (hP : P * P = P) :
    (1 - P) * (1 - P) = 1 - P := by
  noncomm_ring [hP]

/-- Orthogonality to the full complementary range forces a vector into the projection range. -/
theorem projection_of_orth (P : E →L[ℂ] E) (hP : P * P = P) (hPs : star P = P)
    (w : E) (hw : ∀ α : E, (1 - P) α = α → inner (𝕜 := ℂ) α w = 0) : P w = w := by
  let α := (1 - P) w
  have hα : (1 - P) α = α := by
    change ((1 - P) * (1 - P)) w = (1 - P) w
    rw [complement_idem P hP]
  have hPα : P α = 0 := by
    have hzero : P * (1 - P) = 0 := by noncomm_ring [hP]
    change (P * (1 - P)) w = 0
    rw [hzero]
    rfl
  have hpinner : inner (𝕜 := ℂ) α (P w) = 0 := by
    rw [← hPs, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, hPα, inner_zero_left]
  have hinner : inner (𝕜 := ℂ) α α = 0 := by
    change inner (𝕜 := ℂ) α ((1 - P) w) = 0
    rw [sub_apply, one_apply_eq_self, inner_sub_right,
      hw α hα, hpinner, sub_self]
  have hz : α = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hinner
  change w - P w = 0 at hz
  exact (sub_eq_zero.mp hz).symm

/-- The source's orthogonality condition puts every low-degree Krylov vector in the range of P. -/
theorem krylov_in_range (H P : E →L[ℂ] E) (hP : P * P = P) (hPs : star P = P)
    (Φ : E) (N : ℕ)
    (horth : ∀ α : E, (1 - P) α = α → ∀ n : ℕ, n < N →
      inner (𝕜 := ℂ) α ((H ^ n) Φ) = 0) :
    ∀ n : ℕ, n < N → P ((H ^ n) Φ) = (H ^ n) Φ := by
  intro n hn
  exact projection_of_orth P hP hPs _ (fun α hα => horth α hα n hn)

omit [CompleteSpace E] in
/-- The original and truncated Hamiltonians have identical Krylov vectors below the cut-off. -/
theorem krylov_powers (H P : E →L[ℂ] E) (Φ : E) (N : ℕ)
    (hrange : ∀ n : ℕ, n < N → P ((H ^ n) Φ) = (H ^ n) Φ) :
    ∀ n : ℕ, n < N → ((P * H * P) ^ n) Φ = (H ^ n) Φ := by
  intro n
  induction n with
  | zero => intro _hn; rfl
  | succ n ih =>
    intro hn
    have hn' : n < N := by omega
    rw [pow_succ', mul_apply_eq_comp, ih hn']
    change P (H (P ((H ^ n) Φ))) = (H ^ (n + 1)) Φ
    rw [hrange n hn']
    simpa only [pow_succ', mul_apply_eq_comp] using hrange (n + 1) hn

/-- An orthogonal projection has operator norm at most one. -/
theorem projection_contracts (P : E →L[ℂ] E) (hP : P * P = P) (hPs : star P = P) :
    ‖P‖ ≤ 1 :=
  IsStarProjection.norm_le P (isStarProjection_iff'.mpr ⟨hP, hPs⟩)

/-- Compression by an orthogonal projection does not increase the Hamiltonian norm. -/
theorem compression_norm (H P : E →L[ℂ] E) (hP : P * P = P) (hPs : star P = P) :
    ‖P * H * P‖ ≤ ‖H‖ := by
  have hp := projection_contracts P hP hPs
  calc
    ‖P * H * P‖ ≤ ‖P * H‖ * ‖P‖ := norm_mul_le _ _
    _ ≤ (‖P‖ * ‖H‖) * ‖P‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ (1 * ‖H‖) * 1 := by gcongr
    _ = ‖H‖ := by ring

/-- The generator -itH is skew-adjoint for every real time and self-adjoint H. -/
theorem generator_skew (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    ((-(t : ℂ) * Complex.I) • H) ∈ skewAdjoint (E →L[ℂ] E) := by
  apply IsSelfAdjoint.smul_mem_skewAdjoint _ hH
  rw [skewAdjoint.mem_iff]
  simp

/-- Actual Hamiltonian evolution is a unitary operator. -/
theorem evolution_unitary (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) ∈ unitary (E →L[ℂ] E) := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (generator_skew H hH t)

/-- Hamiltonian propagation preserves the norm of every actual initial state. -/
theorem evolution_norm (H : E →L[ℂ] E) (hH : IsSelfAdjoint H) (t : ℝ) (Φ : E) :
    ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ‖ = ‖Φ‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (evolution_unitary H hH t) Φ


/-- The nonnegative scalar tail controlling the actual operator-exponential remainder. -/
def scalarTail (r : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, r ^ (k + N) / ((k + N).factorial : ℝ)

/-- The scalar exponential power series has its usual exact sum. -/
theorem scalar_exp_hasSum (r : ℝ) :
    HasSum (fun n : ℕ => r ^ n / (n.factorial : ℝ)) (Real.exp r) := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm, ← Real.exp_eq_exp_ℝ] using
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) r

/-- Every fixed shift of the scalar exponential tail remains summable. -/
theorem scalarTail_summable (r : ℝ) (N : ℕ) :
    Summable (fun k : ℕ => r ^ (k + N) / ((k + N).factorial : ℝ)) :=
  (scalar_exp_hasSum r).summable.comp_injective (fun _ _ h => Nat.add_right_cancel h)

/-- The exponential is the sum of its finite Taylor prefix and its exact remainder. -/
theorem scalar_exp_split (r : ℝ) (N : ℕ) :
    Real.exp r = (∑ n ∈ Finset.range N, r ^ n / (n.factorial : ℝ)) + scalarTail r N := by
  rw [← (scalar_exp_hasSum r).tsum_eq]
  exact ((scalar_exp_hasSum r).summable.sum_add_tsum_nat_add N).symm

/-- A nonnegative exponential tail is bounded by the full exponential. -/
theorem scalarTail_le_exp (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    scalarTail r N ≤ Real.exp r := by
  rw [scalar_exp_split r N]
  have hp : 0 ≤ ∑ n ∈ Finset.range N, r ^ n / (n.factorial : ℝ) := by positivity
  linarith

/-- Rescaling the exponential series gives the sharp Chernoff bound on its Taylor tail. -/
theorem scalarTail_rescale (r c : ℝ) (hr : 0 ≤ r) (hc : 1 ≤ c) (N : ℕ) :
    c ^ N * scalarTail r N ≤ Real.exp (c * r) := by
  have hsum : c ^ N * scalarTail r N ≤ scalarTail (c * r) N := by
    unfold scalarTail
    rw [← tsum_mul_left]
    apply Summable.tsum_le_tsum
    · intro k
      have hp : c ^ N ≤ c ^ (k + N) := pow_le_pow_right₀ hc (by omega)
      calc
        c ^ N * (r ^ (k + N) / ((k + N).factorial : ℝ)) ≤
            c ^ (k + N) * (r ^ (k + N) / ((k + N).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = (c * r) ^ (k + N) / ((k + N).factorial : ℝ) := by rw [mul_pow]; ring
    · exact (scalarTail_summable r N).mul_left _
    · exact scalarTail_summable (c * r) N
  exact hsum.trans (scalarTail_le_exp _ (mul_nonneg (by linarith) hr) N)

/-- The actual operator-exponential tail, expressed by its convergent Taylor series. -/
def operatorTail (A : E →L[ℂ] E) (N : ℕ) : E →L[ℂ] E :=
  ∑' k : ℕ, (((k + N).factorial : ℂ)⁻¹) • A ^ (k + N)

/-- The real operator exponential splits into the finite Krylov prefix and its actual tail. -/
theorem operator_exp_split (A : E →L[ℂ] E) (N : ℕ) :
    NormedSpace.exp A =
      (∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • A ^ n) + operatorTail A N := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact ((NormedSpace.expSeries_summable' (𝕂 := ℂ) A).sum_add_tsum_nat_add N).symm


omit [CompleteSpace E] in
/-- Norm comparison bounds the actual operator tail by its scalar Taylor tail. -/
theorem operatorTail_norm (A : E →L[ℂ] E) (r : ℝ) (hAr : ‖A‖ ≤ r) (N : ℕ) :
    ‖operatorTail A N‖ ≤ scalarTail r N := by
  have hnorm : Summable (fun k : ℕ =>
      ‖((((k + N).factorial : ℂ)⁻¹) • A ^ (k + N))‖) :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) A).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  calc
    ‖operatorTail A N‖ ≤ ∑' k : ℕ,
        ‖((((k + N).factorial : ℂ)⁻¹) • A ^ (k + N))‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ scalarTail r N := by
      apply hnorm.tsum_le_tsum _ (scalarTail_summable r N)
      intro k
      simp only [norm_smul, norm_inv, Complex.norm_natCast]
      calc
        (((k + N).factorial : ℝ)⁻¹) * ‖A ^ (k + N)‖ ≤
            (((k + N).factorial : ℝ)⁻¹) * r ^ (k + N) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hpower : ‖A ^ (k + N)‖ ≤ ‖A‖ ^ (k + N) := by
            by_cases hn : k + N = 0
            · simpa only [hn, pow_zero, ContinuousLinearMap.one_def] using
                (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E))
            · exact norm_pow_le' A (Nat.pos_of_ne_zero hn)
          exact hpower.trans
            (pow_le_pow_left₀ (norm_nonneg A) hAr (k + N))
        _ = _ := by ring

/-- Exact Krylov-prefix cancellation leaves only the two actual exponential tails. -/
theorem exponential_difference_tail (A B : E →L[ℂ] E) (Φ : E) (N : ℕ)
    (hpowers : ∀ n : ℕ, n < N → (A ^ n) Φ = (B ^ n) Φ)
    (r : ℝ) (hAr : ‖A‖ ≤ r) (hBr : ‖B‖ ≤ r) :
    ‖NormedSpace.exp A Φ - NormedSpace.exp B Φ‖ ≤
      2 * scalarTail r N * ‖Φ‖ := by
  have hprefix : (∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • A ^ n) Φ =
      (∑ n ∈ Finset.range N, ((n.factorial : ℂ)⁻¹) • B ^ n) Φ := by
    rw [sum_apply, sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [smul_apply, hpowers n (Finset.mem_range.mp hn)]
  rw [operator_exp_split A N, operator_exp_split B N]
  simp only [add_apply]
  rw [hprefix, add_sub_add_left_eq_sub]
  calc
    ‖operatorTail A N Φ - operatorTail B N Φ‖ ≤
        ‖operatorTail A N Φ‖ + ‖operatorTail B N Φ‖ := norm_sub_le _ _
    _ ≤ ‖operatorTail A N‖ * ‖Φ‖ + ‖operatorTail B N‖ * ‖Φ‖ :=
      add_le_add ((operatorTail A N).le_opNorm Φ) ((operatorTail B N).le_opNorm Φ)
    _ ≤ scalarTail r N * ‖Φ‖ + scalarTail r N * ‖Φ‖ :=
      add_le_add (mul_le_mul_of_nonneg_right (operatorTail_norm A r hAr N) (norm_nonneg Φ))
        (mul_le_mul_of_nonneg_right (operatorTail_norm B r hBr N) (norm_nonneg Φ))
    _ = 2 * scalarTail r N * ‖Φ‖ := by ring

/-- Compression preserves self-adjointness for an orthogonal projection. -/
theorem compression_self (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hPs : star P = P) :
    IsSelfAdjoint (P * H * P) := by
  rw [isSelfAdjoint_iff]
  simp only [star_mul, hPs, hH.star_eq, mul_assoc]

/-- The optimized scalar Taylor tail has the factorial-free bound used in Proposition 1. -/
theorem scalarTail_optimized (r : ℝ) (hr : 0 < r) (N : ℕ) (hN : 0 < N)
    (hrN : r ≤ (N : ℝ)) :
    scalarTail r N ≤ (Real.exp 1 * r / (N : ℝ)) ^ N := by
  let c := (N : ℝ) / r
  have hc : 1 ≤ c := (one_le_div hr).mpr hrN
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcr : c * r = (N : ℝ) := by dsimp [c]; field_simp
  have hb := scalarTail_rescale r c hr.le hc N
  rw [hcr] at hb
  have hexp : Real.exp (N : ℝ) = (Real.exp 1) ^ N := by
    simpa only [mul_one] using Real.exp_nat_mul (x := 1) N
  calc
    scalarTail r N ≤ Real.exp (N : ℝ) / c ^ N :=
      (le_div_iff₀ (pow_pos hcpos N)).mpr (by nlinarith [hb])
    _ = ((Real.exp 1) / c) ^ N := by
      rw [hexp]
      exact (div_pow (Real.exp 1) c N).symm
    _ = (Real.exp 1 * r / (N : ℝ)) ^ N := by
      congr 1
      dsimp [c]
      field_simp


/-- The sharp truncation estimate follows from actual Krylov cancellation and unitarity. -/
theorem truncation_exp_bound
    (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hP : P * P = P) (hPs : star P = P) (Φ : E) (hΦ : ‖Φ‖ = 1)
    (N : ℕ) (hN : 0 < N)
    (hrange : ∀ n : ℕ, n < N → P ((H ^ n) Φ) = (H ^ n) Φ)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ -
        NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖ ≤
      2 * (Real.exp 1 * ‖H‖ * t / (N : ℝ)) ^ N := by
  let A := (-(t : ℂ) * Complex.I) • H
  let B := (-(t : ℂ) * Complex.I) • (P * H * P)
  let r := ‖H‖ * t
  have hr : 0 ≤ r := mul_nonneg (norm_nonneg H) ht
  have hcoef : ‖-(t : ℂ) * Complex.I‖ = t := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  have hAr : ‖A‖ ≤ r := by
    dsimp [A, r]
    rw [norm_smul, hcoef]
    exact le_of_eq (mul_comm _ _)
  have hBr : ‖B‖ ≤ r := by
    dsimp [B, r]
    rw [norm_smul, hcoef]
    calc
      t * ‖P * H * P‖ ≤ t * ‖H‖ :=
        mul_le_mul_of_nonneg_left (compression_norm H P hP hPs) ht
      _ = _ := mul_comm _ _
  have hpowers : ∀ n : ℕ, n < N → (A ^ n) Φ = (B ^ n) Φ := by
    intro n hn
    simpa only [A, B, smul_pow, smul_apply] using
      congrArg (fun w : E => ((-(t : ℂ) * Complex.I) ^ n) • w)
        (krylov_powers H P Φ N hrange n hn).symm
  have htail := exponential_difference_tail A B Φ N hpowers r hAr hBr
  rw [hΦ, mul_one] at htail
  by_cases hrzero : r = 0
  · have hz : scalarTail r N = 0 := by
      rw [hrzero]
      unfold scalarTail
      have heach (k : ℕ) : (0 : ℝ) ^ (k + N) / ((k + N).factorial : ℝ) = 0 := by
        rw [zero_pow (by omega : k + N ≠ 0), zero_div]
      simp only [heach, tsum_zero]
    rw [hz, mul_zero] at htail
    exact htail.trans (by positivity)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrzero)
    by_cases hrN : r ≤ (N : ℝ)
    · have hb := scalarTail_optimized r hrpos N hN hrN
      have hb' : ‖NormedSpace.exp A Φ - NormedSpace.exp B Φ‖ ≤
          2 * (Real.exp 1 * r / (N : ℝ)) ^ N :=
        htail.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
      simpa only [A, B, r, mul_assoc] using hb'
    · have hnorm : ‖NormedSpace.exp A Φ - NormedSpace.exp B Φ‖ ≤ 2 := by
        calc
          _ ≤ ‖NormedSpace.exp A Φ‖ + ‖NormedSpace.exp B Φ‖ := norm_sub_le _ _
          _ = 2 := by
            rw [evolution_norm H hH t Φ,
              evolution_norm (P * H * P) (compression_self H P hH hPs) t Φ, hΦ]
            norm_num
      have hNc : 0 < (N : ℝ) := by exact_mod_cast hN
      have he : 1 ≤ Real.exp 1 := by
        simp
      have hbase : 1 ≤ Real.exp 1 * r / (N : ℝ) := by
        apply (le_div_iff₀ hNc).mpr
        have hnr : (N : ℝ) ≤ r := le_of_not_ge hrN
        nlinarith
      have hpow : 1 ≤ (Real.exp 1 * r / (N : ℝ)) ^ N := one_le_pow₀ hbase
      have hb : ‖NormedSpace.exp A Φ - NormedSpace.exp B Φ‖ ≤
          2 * (Real.exp 1 * r / (N : ℝ)) ^ N := hnorm.trans (by linarith)
      simpa only [A, B, r, mul_assoc] using hb


/-- Homogeneity gives the sharp Krylov truncation estimate for an arbitrary unnormalized vector. -/
theorem truncation_exp_scaled
    (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hP : P * P = P) (hPs : star P = P) (Φ : E)
    (N : ℕ) (hN : 0 < N)
    (hrange : ∀ n : ℕ, n < N → P ((H ^ n) Φ) = (H ^ n) Φ)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ -
        NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖ ≤
      2 * (Real.exp 1 * ‖H‖ * t / (N : ℝ)) ^ N * ‖Φ‖ := by
  by_cases hz : Φ = 0
  · subst Φ
    simp
  have hn : ‖Φ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let ψ := ((‖Φ‖ : ℂ)⁻¹) • Φ
  have hψ : ‖ψ‖ = 1 := by
    dsimp [ψ]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg Φ), inv_mul_cancel₀ hn]
  have hψrange : ∀ n : ℕ, n < N → P ((H ^ n) ψ) = (H ^ n) ψ := by
    intro n hni
    simp only [ψ, map_smul, hrange n hni]
  have hb := truncation_exp_bound H P hH hP hPs ψ hψ N hN hψrange t ht
  have hdiff :
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) ψ -
          NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) ψ‖ =
        ‖Φ‖⁻¹ * ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ -
          NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖ := by
    simp only [ψ, map_smul, ← smul_sub, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg Φ)]
  rw [hdiff] at hb
  have hmul := mul_le_mul_of_nonneg_left hb (norm_nonneg Φ)
  rwa [← mul_assoc, mul_inv_cancel₀ hn, one_mul, mul_comm ‖Φ‖] at hmul

/-- The exact unitary power telescope accumulates only local errors along one actual trajectory. -/
theorem power_error_bound (U V : E →L[ℂ] E) (hV : V ∈ unitary (E →L[ℂ] E))
    (Φ : E) (M : ℕ) :
    ‖(U ^ M) Φ - (V ^ M) Φ‖ ≤
      ∑ j ∈ Finset.range M, ‖(U - V) ((U ^ j) Φ)‖ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, Finset.sum_range_succ]
    have hid : U ((U ^ M) Φ) - V ((V ^ M) Φ) =
        (U - V) ((U ^ M) Φ) + V ((U ^ M) Φ - (V ^ M) Φ) := by
      simp only [sub_apply, map_sub]
      abel
    rw [hid]
    calc
      _ ≤ ‖(U - V) ((U ^ M) Φ)‖ + ‖V ((U ^ M) Φ - (V ^ M) Φ)‖ := norm_add_le _ _
      _ = ‖(U - V) ((U ^ M) Φ)‖ + ‖(U ^ M) Φ - (V ^ M) Φ‖ := by
        rw [ContinuousLinearMap.norm_map_of_mem_unitary hV]
      _ ≤ _ := by linarith

/-- Repeated equal-duration Hamiltonian steps equal propagation for the total elapsed time. -/
theorem evolution_power (H : E →L[ℂ] E) (t : ℝ) (M : ℕ) :
    (NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) ^ M) =
      NormedSpace.exp ((-(((M : ℝ) * t : ℝ) : ℂ) * Complex.I) • H) := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [← NormedSpace.exp_nsmul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  push_cast
  ring

/-- Subdivision into any positive number of steps exactly reproduces Hamiltonian propagation. -/
theorem evolution_subdivide (H : E →L[ℂ] E) (t : ℝ) (M : ℕ) (hM : 0 < M) :
    (NormedSpace.exp ((-((t / (M : ℝ) : ℝ) : ℂ) * Complex.I) • H) ^ M) =
      NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) := by
  rw [evolution_power]
  have hMc : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  rw [mul_div_cancel₀ _ hMc]

end Qatlib.Papers.UniversalWalk12.MainResults.Truncation
