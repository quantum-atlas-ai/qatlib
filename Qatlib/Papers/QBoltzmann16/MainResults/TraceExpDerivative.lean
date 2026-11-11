/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QBoltzmann16.MainResults.BoltzmannDefs

/-!
# Differentiating finite trace exponentials

This module proves cyclic trace identities for matrix powers and the derivative of the trace
exponential for a real-parameter matrix family with a continuous derivative at the evaluation
point. The finite Gibbs partition derivative follows by substituting `-H`, providing the
noncommuting trace calculation used in [AminEtAl2018].

## Main statements

* `trace_pow_hasDerivAt`: the derivative of the trace of a matrix power.
* `trace_exp_hasDerivAt`: the trace-exponential derivative.
* `gibbsPartition_hasDerivAt`: the finite Gibbs partition derivative.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QBoltzmann16.MainResults

open Matrix Filter
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator Topology
set_option warningAsError false

/-- The matrix trace regarded as a continuous real-linear map from finite complex operators to
the complex numbers. -/
def traceCLM (D : ℕ) : Operator D →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin D) ℝ ℂ).toContinuousLinearMap

/-- The continuous-linear trace map evaluates to the ordinary matrix trace. -/
@[simp]
theorem traceCLM_apply (D : ℕ) (A : Operator D) : traceCLM D A = Matrix.trace A := rfl

/-- Cyclicity of the trace collapses the sum of the `n` matrix-power derivative terms to `n`
times `trace (A ^ n.pred * Y)`. -/
theorem trace_pow_deriv_sum (D : ℕ) (A Y : Operator D) (n : ℕ) :
    (∑ i ∈ Finset.range n, Matrix.trace (A ^ (n.pred - i) * Y * A ^ i))
      = (n : ℂ) * Matrix.trace (A ^ n.pred * Y) := by
  have hterm : ∀ i ∈ Finset.range n,
      Matrix.trace (A ^ (n.pred - i) * Y * A ^ i) = Matrix.trace (A ^ n.pred * Y) := by
    intro i hi
    rw [Matrix.trace_mul_comm (A ^ (n.pred - i) * Y) (A ^ i), ← Matrix.mul_assoc,
      ← pow_add]
    have hi' : i < n := Finset.mem_range.mp hi
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi'
    have hn : n.pred + 1 = n := Nat.succ_pred_eq_of_pos hnpos
    rw [show i + (n.pred - i) = n.pred by omega]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- For a differentiable matrix family, the derivative of `trace (A t ^ n)` is `n * trace (A θ ^
n.pred * A' θ)`. -/
theorem trace_pow_hasDerivAt (D : ℕ) (A A' : ℝ → Operator D) (n : ℕ) (θ : ℝ)
    (hA : HasDerivAt A (A' θ) θ) :
    HasDerivAt (fun t : ℝ => Matrix.trace (A t ^ n))
      ((n : ℂ) * Matrix.trace (A θ ^ n.pred * A' θ)) θ := by
  have hpow := hA.pow' n
  have htr : HasDerivAt (fun t : ℝ => Matrix.trace (A t ^ n))
      (Matrix.trace (∑ i ∈ Finset.range n,
        A θ ^ (n.pred - i) * A' θ * A θ ^ i)) θ := by
    exact (traceCLM D).hasFDerivAt.comp_hasDerivAt θ hpow
  have hval : Matrix.trace (∑ i ∈ Finset.range n,
        A θ ^ (n.pred - i) * A' θ * A θ ^ i)
      = (n : ℂ) * Matrix.trace (A θ ^ n.pred * A' θ) := by
    change traceCLM D (∑ i ∈ Finset.range n,
      A θ ^ (n.pred - i) * A' θ * A θ ^ i) = _
    rw [map_sum]
    simp only [traceCLM_apply]
    exact trace_pow_deriv_sum D (A θ) (A' θ) n
  rwa [hval] at htr

/-- The complex norm of each matrix entry is bounded by the matrix's ℓ² operator norm. -/
lemma norm_entry_le_opNorm (D : ℕ) (B : Operator D) (i j : Fin D) : ‖B i j‖ ≤ ‖B‖ := by
  let x : EuclideanSpace ℂ (Fin D) := EuclideanSpace.single j 1
  have hx : ‖x‖ = 1 := by simp [x]
  have h := B.l2_opNorm_mulVec x
  have hcoord : ‖B i j‖ ≤ ‖(EuclideanSpace.equiv (Fin D) ℂ).symm (B *ᵥ x)‖ := by
    have hle := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin D) ℂ).symm (B *ᵥ x)) i
    simpa [x, Matrix.mulVec, dotProduct, EuclideanSpace.single] using! hle
  calc ‖B i j‖ ≤ ‖(EuclideanSpace.equiv (Fin D) ℂ).symm (B *ᵥ x)‖ := hcoord
    _ ≤ ‖B‖ * ‖x‖ := h
    _ = ‖B‖ := by rw [hx, mul_one]

/-- The norm of the trace is at most the dimension times the matrix's ℓ² operator norm. -/
lemma norm_trace_le (D : ℕ) (B : Operator D) : ‖Matrix.trace B‖ ≤ (D : ℝ) * ‖B‖ := by
  calc ‖Matrix.trace B‖ = ‖∑ i, B i i‖ := by simp [Matrix.trace]
    _ ≤ ∑ i, ‖B i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin D, ‖B‖ := Finset.sum_le_sum (fun i _ => norm_entry_le_opNorm D B i i)
    _ = (D : ℝ) * ‖B‖ := by
        simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- In positive dimension, the ℓ² operator norm of `B ^ n` is at most `‖B‖ ^ n`. -/
lemma l2_opNorm_pow_le (D : ℕ) (hD : 0 < D) (B : Operator D) (n : ℕ) : ‖B ^ n‖ ≤ ‖B‖ ^ n := by
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact le_of_eq (by
      rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]; simp)
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))

/-- For a differentiable matrix family in positive dimension whose derivative is continuous at
`θ`, the trace-exponential derivative is `trace (exp (A θ) * A' θ)` without a commutation
hypothesis. -/
theorem trace_exp_hasDerivAt (D : ℕ) (hD : 0 < D)
    (A A' : ℝ → Operator D) (θ : ℝ)
    (hA : ∀ t, HasDerivAt A (A' t) t) (hA' : ContinuousAt A' θ) :
    HasDerivAt (fun s : ℝ => Matrix.trace (NormedSpace.exp (A s)))
      (Matrix.trace (NormedSpace.exp (A θ) * A' θ)) θ := by
  letI : NormedRing (Operator D) := Matrix.instL2OpNormedRing
  let g : ℕ → ℝ → ℂ := fun n s => ((Nat.factorial n : ℕ) : ℂ)⁻¹ • Matrix.trace (A s ^ n)
  let g' : ℕ → ℝ → ℂ := fun n s =>
    ((Nat.factorial n : ℕ) : ℂ)⁻¹ • (n : ℂ) • Matrix.trace (A s ^ n.pred * A' s)
  have hg : ∀ n s, HasDerivAt (g n) (g' n s) s := by
    intro n s
    have h := trace_pow_hasDerivAt D A A' n s (hA s)
    simpa [g, g', mul_assoc] using! h.const_mul (((Nat.factorial n : ℕ) : ℂ)⁻¹)
  have hcontA : ContinuousAt A θ := (hA θ).continuousAt
  have hevA : ∀ᶠ s in 𝓝 θ, A s ∈ Metric.ball (A θ) 1 :=
    hcontA.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hevA
  have hevA' : ∀ᶠ s in 𝓝 θ, A' s ∈ Metric.ball (A' θ) 1 :=
    hA'.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.mem_nhds_iff.mp hevA'
  let R : ℝ := ‖A θ‖ + 1
  let M : ℝ := ‖A' θ‖ + 1
  have hR : 0 ≤ R := by positivity
  have hM : 0 ≤ M := by positivity
  have hAbound : ∀ s, dist s θ < δ₁ → ‖A s‖ ≤ R := by
    intro s hs
    have h1 : A s ∈ Metric.ball (A θ) 1 := hδ₁ (by simpa [Metric.mem_ball] using! hs)
    have h2 : ‖A s - A θ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using! h1
    calc ‖A s‖ = ‖A θ + (A s - A θ)‖ := by rw [show A θ + (A s - A θ) = A s by abel]
      _ ≤ ‖A θ‖ + ‖A s - A θ‖ := norm_add_le _ _
      _ ≤ ‖A θ‖ + 1 := by linarith
      _ = R := rfl
  have hA'bound : ∀ s, dist s θ < δ₂ → ‖A' s‖ ≤ M := by
    intro s hs
    have h1 : A' s ∈ Metric.ball (A' θ) 1 := hδ₂ (by simpa [Metric.mem_ball] using! hs)
    have h2 : ‖A' s - A' θ‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using! h1
    calc ‖A' s‖ = ‖A' θ + (A' s - A' θ)‖ := by rw [show A' θ + (A' s - A' θ) = A' s by abel]
      _ ≤ ‖A' θ‖ + ‖A' s - A' θ‖ := norm_add_le _ _
      _ ≤ ‖A' θ‖ + 1 := by linarith
      _ = M := rfl
  let C : ℝ := (D : ℝ)
  have hC : 0 ≤ C := Nat.cast_nonneg D
  let u : ℕ → ℝ := fun n => ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) * C * R ^ n.pred * M
  have hTraceBound : ∀ (n : ℕ) (s : ℝ), dist s θ < δ₁ →
      ‖Matrix.trace (A s ^ n.pred * A' s)‖ ≤ C * (‖A s‖ ^ n.pred * ‖A' s‖) := by
    intro n s hs
    calc ‖Matrix.trace (A s ^ n.pred * A' s)‖ ≤ C * ‖A s ^ n.pred * A' s‖ := norm_trace_le D _
      _ ≤ C * (‖A s ^ n.pred‖ * ‖A' s‖) := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
      _ ≤ C * (‖A s‖ ^ n.pred * ‖A' s‖) := by
          gcongr
          exact l2_opNorm_pow_le D hD (A s) n.pred
  have hug' : ∀ n s, dist s θ < min δ₁ δ₂ → ‖g' n s‖ ≤ u n := by
    intro n s hs
    have hs1 : dist s θ < δ₁ := lt_of_lt_of_le hs (min_le_left _ _)
    have hs2 : dist s θ < δ₂ := lt_of_lt_of_le hs (min_le_right _ _)
    have hAs : ‖A s‖ ≤ R := hAbound s hs1
    have hA's : ‖A' s‖ ≤ M := hA'bound s hs2
    have htr := hTraceBound n s hs1
    have hpowR : ‖A s‖ ^ n.pred ≤ R ^ n.pred :=
      pow_le_pow_left₀ (norm_nonneg _) hAs n.pred
    have hcalc : ‖g' n s‖
        = ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) *
            ‖Matrix.trace (A s ^ n.pred * A' s)‖ := by
      simp [g', norm_inv, mul_assoc]
    rw [hcalc]
    calc ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) *
          ‖Matrix.trace (A s ^ n.pred * A' s)‖
        ≤ ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) *
            (C * (‖A s‖ ^ n.pred * ‖A' s‖)) := by gcongr
      _ ≤ ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) *
            (C * (R ^ n.pred * M)) := by gcongr
      _ = u n := by unfold u; ring
  have hu : Summable u := by
    have hbase : Summable (fun m : ℕ => ((Nat.factorial m : ℕ) : ℝ)⁻¹ * R ^ m) := by
      simpa [div_eq_mul_inv, mul_comm] using! Real.summable_pow_div_factorial R
    have hshift : Summable (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) * R ^ n.pred) := by
      rw [← summable_nat_add_iff 1]
      have hfun : (fun m : ℕ => ((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹ * ((m + 1 : ℕ) : ℝ) *
          R ^ (m + 1).pred) = fun m : ℕ => ((Nat.factorial m : ℕ) : ℝ)⁻¹ * R ^ m := by
        funext m
        rw [Nat.factorial_succ, show (m + 1).pred = m from rfl]
        push_cast
        field_simp
      rw [hfun]
      exact hbase
    have hmul : Summable (fun n : ℕ =>
        ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (n : ℝ) * R ^ n.pred * (C * M)) :=
      Summable.mul_right (C * M) hshift
    convert! hmul using 1
    funext n
    unfold u
    ring
  have hg0 : Summable (fun n => g n θ) := by
    have hbase : Summable (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ‖A θ‖ ^ n) := by
      simpa [div_eq_mul_inv, mul_comm] using! Real.summable_pow_div_factorial ‖A θ‖
    have hmul : Summable (fun n : ℕ => C * (((Nat.factorial n : ℕ) : ℝ)⁻¹ * ‖A θ‖ ^ n)) :=
      Summable.mul_left C hbase
    refine Summable.of_norm_bounded hmul (fun n => ?_)
    have htr : ‖Matrix.trace (A θ ^ n)‖ ≤ C * ‖A θ‖ ^ n := by
      calc ‖Matrix.trace (A θ ^ n)‖ ≤ C * ‖A θ ^ n‖ := norm_trace_le D _
        _ ≤ C * ‖A θ‖ ^ n := by
            gcongr
            exact l2_opNorm_pow_le D hD (A θ) n
    have hnorm : ‖g n θ‖ = ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ‖Matrix.trace (A θ ^ n)‖ := by
      simp [g]
    rw [hnorm]
    calc ((Nat.factorial n : ℕ) : ℝ)⁻¹ * ‖Matrix.trace (A θ ^ n)‖
        ≤ ((Nat.factorial n : ℕ) : ℝ)⁻¹ * (C * ‖A θ‖ ^ n) := by gcongr
      _ = C * (((Nat.factorial n : ℕ) : ℝ)⁻¹ * ‖A θ‖ ^ n) := by ring
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁pos hδ₂pos
  have hmain : HasDerivAt (fun s => ∑' n, g n s) (∑' n, g' n θ) θ :=
    hasDerivAt_tsum_of_isPreconnected (u := u) hu Metric.isOpen_ball
      (convex_ball θ (min δ₁ δ₂)).isPreconnected (fun n s _ => hg n s)
      (fun n s hs => hug' n s hs) (Metric.mem_ball_self hδ) hg0 (Metric.mem_ball_self hδ)
  have hfun : (fun s => ∑' n, g n s) = fun s => Matrix.trace (NormedSpace.exp (A s)) := by
    funext s
    rw [NormedSpace.exp_eq_tsum ℂ]
    change ∑' n, g n s = traceCLM D (∑' n, ((Nat.factorial n : ℕ) : ℂ)⁻¹ • A s ^ n)
    rw [(traceCLM D).map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) (A s))]
    refine tsum_congr (fun n => ?_)
    simp [g, traceCLM_apply, smul_eq_mul]
  have hderivval : (∑' n, g' n θ) = Matrix.trace (NormedSpace.exp (A θ) * A' θ) := by
    have hsummable : Summable (fun n => g' n θ) := by
      refine Summable.of_norm_bounded hu (fun n => ?_)
      exact hug' n θ (Metric.mem_ball_self hδ)
    have hsplit := hsummable.sum_add_tsum_nat_add 1
    have hzero : (∑ i ∈ Finset.range 1, g' i θ) = 0 := by simp [g']
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    have hcongr : ∀ m : ℕ, g' (m + 1) θ =
        ((Nat.factorial m : ℕ) : ℂ)⁻¹ • Matrix.trace (A θ ^ m * A' θ) := by
      intro m
      simp only [g']
      rw [show (m + 1).pred = m from rfl, Nat.factorial_succ]
      push_cast
      rw [smul_smul]
      field_simp
    rw [tsum_congr hcongr]
    rw [NormedSpace.exp_eq_tsum ℂ]
    change ∑' m, ((Nat.factorial m : ℕ) : ℂ)⁻¹ • Matrix.trace (A θ ^ m * A' θ)
      = Matrix.trace ((∑' n, ((Nat.factorial n : ℕ) : ℂ)⁻¹ • A θ ^ n) * A' θ)
    have hmul : ∑' n, (((Nat.factorial n : ℕ) : ℂ)⁻¹ • A θ ^ n) * A' θ
        = ((∑' n, ((Nat.factorial n : ℕ) : ℂ)⁻¹ • A θ ^ n) * A' θ) :=
      (NormedSpace.expSeries_summable' (𝕂 := ℂ) (A θ)).tsum_mul_right (A' θ)
    rw [← hmul]
    change ∑' m, ((Nat.factorial m : ℕ) : ℂ)⁻¹ • Matrix.trace (A θ ^ m * A' θ)
      = traceCLM D (∑' n, ((Nat.factorial n : ℕ) : ℂ)⁻¹ • A θ ^ n * A' θ)
    rw [(traceCLM D).map_tsum ((NormedSpace.expSeries_summable' (𝕂 := ℂ) (A θ)).mul_right (A' θ))]
    refine tsum_congr (fun m => ?_)
    simp [traceCLM_apply, Matrix.trace_smul, smul_eq_mul]
  rw [hfun, hderivval] at hmain
  simpa using! hmain

/-- For a differentiable Hamiltonian family in positive dimension with derivative continuous at
`θ`, the partition derivative is the negative real trace of `exp (-(H θ)) * H' θ`
[AminEtAl2018]. -/
theorem gibbsPartition_hasDerivAt (D : ℕ) (hD : 0 < D)
    (H H' : ℝ → Operator D) (θ : ℝ)
    (hH : ∀ t, HasDerivAt H (H' t) t) (hH' : ContinuousAt H' θ) :
    HasDerivAt (fun t => gibbsPartition D (H t))
      (-(Matrix.trace (NormedSpace.exp (-(H θ)) * H' θ)).re) θ := by
  have hA : ∀ t, HasDerivAt (fun s => -H s) (-(H' t)) t := fun t => (hH t).neg
  have hA' : ContinuousAt (fun t => -(H' t)) θ := hH'.neg
  have h := trace_exp_hasDerivAt D hD (fun s => -H s) (fun t => -(H' t)) θ hA hA'
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ h
  simpa [gibbsPartition, Matrix.mul_neg, Matrix.trace_neg, Complex.neg_re] using! hre

end Qatlib.Papers.QBoltzmann16.MainResults
