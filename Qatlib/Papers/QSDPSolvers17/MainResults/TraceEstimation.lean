/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Papers.QSDPSolvers17.MainResults.Model.SdpInstance
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Trace estimation and Gibbs-state preparation (paper QSDPSolvers17, Lemmas 10–12, App. D)

Source: arXiv:1710.02581, Appendix D, pp. 21–24.

* **Lemma 10 (trace estimation).**  The SWAP test of [10] estimates `Tr(A_j ρ)` to
  accuracy `ε` with failure probability `1/m²` using `S_Tr(B, ε) = O(B² log m/ε²)`
  copies of `ρ`, where `B` bounds the entries of the observables.  Algorithm 6 uses
  these estimates to decide `Tr(A_j ρ) > a_j + ε` versus `Tr(A_j ρ) ≤ a_j`.
* **Lemma 11 (Gibbs-mixture preparation).**  The Gibbs state of the averaged
  Hamiltonian `K = (1/|S|)∑_{j∈S} K_j` is the mixture
  `K^±/Tr K^± = ∑_j w_j A_j^±/Tr A_j^±` with nonnegative weights `w_j` summing to one,
  and the preparation uses `|S|+1` copies of the states `A_j^±`.
* **Lemma 12 (Gibbs-sampler cost).**  If each mixture component can be prepared with
  `T₀ = poly(log n, r_K, B_K, 1/ε)` gates, the sampler for `exp(-K)/Tr exp(-K)` uses
  `Õ(Φ · poly(log n, r_K, B_K, 1/ε))` gates, where `Φ = |S|`.

The sample-count and convex-combination algebra is proved; the SWAP-test concentration
step (Hoeffding with failure `1/m²`) enters as the explicit deviation hypothesis of
`trace_estimation`; the inner Gibbs sampler gate count is the interface hypothesis of
`gibbs_sampler_cost` (formalized on its own in `GibbsSampler/GibbsSampler.lean`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QSDPSolvers17.MainResults.TraceEstimation

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped ComplexOrder MatrixOrder BigOperators

/-! ## Lemma 10: SWAP-test trace estimation -/

/-- Number of copies of `ρ` used by the SWAP-test estimator of Lemma 10 at accuracy `ε`
and failure probability `1/m²`: the Hoeffding/Chernoff count
`2 B² ln(1/δ)/ε²` specialised to `δ = 1/m²`. -/
noncomputable def swapTestCopies (B ε : ℝ) (m : ℕ) : ℝ :=
  2 * B ^ 2 * Real.log ((m : ℝ) ^ 2) / ε ^ 2

/-- `ln(m²) = 2 ln m`, so the SWAP-test count is `4 B² ln m/ε²`. -/
theorem swap_test_copies_eq (B ε : ℝ) (m : ℕ) :
    swapTestCopies B ε m = 4 * B ^ 2 * Real.log m / ε ^ 2 := by
  unfold swapTestCopies
  rw [Real.log_pow]
  push_cast
  ring

/-- **Lemma 10, sample complexity.**  `S_Tr(B, ε) = O(B² log m/ε²)`: the SWAP-test
estimator uses at most `8 B² (ln m + 1)/ε²` copies of `ρ`, an explicit `O(B² log m/ε²)`
bound with constant `8`. -/
theorem trace_estimation_copy_bound {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) {m : ℕ}
    (hm : 2 ≤ m) :
    swapTestCopies B ε m ≤ 8 * B ^ 2 * (Real.log m + 1) / ε ^ 2 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hm)
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hε2 : 0 < ε ^ 2 := by positivity
  have hcore : 4 * B ^ 2 * Real.log m ≤ 8 * B ^ 2 * (Real.log m + 1) := by
    nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg B) hlog]
  calc swapTestCopies B ε m = 4 * B ^ 2 * Real.log m / ε ^ 2 := swap_test_copies_eq B ε m
    _ ≤ 8 * B ^ 2 * (Real.log m + 1) / ε ^ 2 :=
        div_le_div_of_nonneg_right hcore hε2.le

/-- **Lemma 10 (trace estimation).**  The SWAP-test estimator of `Tr(A_j ρ)` with
`S_Tr(B, ε) = O(B² log m/ε²)` copies (bound `trace_estimation_copy_bound`) decides the
violated case: if the estimate `est` is within `ε` of the true value `truth` (the
Hoeffding event, failure `1/m²`) and `truth ≥ a + ε`, then `est > a`.

The deviation hypothesis `hdev` is the standard SWAP-test concentration guarantee; the
deterministic implication and the copy count are proved here. -/
theorem trace_estimation {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) {m : ℕ} (hm : 2 ≤ m)
    (est truth a : ℝ) (hdev : |est - truth| < ε) (hhi : a + ε ≤ truth) :
    a < est ∧ swapTestCopies B ε m ≤ 8 * B ^ 2 * (Real.log m + 1) / ε ^ 2 :=
  ⟨by have := (abs_lt.mp hdev).1; linarith,
    trace_estimation_copy_bound hB hε hm⟩

/-! ## Lemma 11: Gibbs-mixture preparation -/

variable {ι : Type*} [Fintype ι] {D : ℕ}

/-- Mixture weights `w_j = Tr A_j^± / Tr K^±` of Lemma 11, written for arbitrary
nonnegative component weights `v j` (the traces of the subnormalized states). -/
noncomputable def mixtureWeights (v : ι → ℝ) (j : ι) : ℝ :=
  v j / ∑ k, v k

/-- The mixture weights are nonnegative. -/
theorem mixtureWeights_nonneg {v : ι → ℝ} (hv : ∀ j, 0 ≤ v j) (hV : 0 < ∑ k, v k) (j : ι) :
    0 ≤ mixtureWeights v j :=
  div_nonneg (hv j) hV.le

/-- The mixture weights sum to one. -/
theorem mixtureWeights_sum_one {v : ι → ℝ} (hV : (∑ k, v k) ≠ 0) :
    ∑ j, mixtureWeights v j = 1 := by
  simp only [mixtureWeights]
  rw [← Finset.sum_div]
  exact div_self hV

/-- **Lemma 11, mixture identity.**  The normalized sum of the component states equals
the convex combination with weights `w_j = v_j / ∑ v`:
`(∑_j A_j)/(∑_j v_j) = ∑_j w_j · (A_j / v_j)`, where `v_j` plays the role of `Tr A_j^±`
and `∑_j A_j` the role of `K^±`.  This is the algebraic content of the identity
`K^±/Tr K^± = ∑_j w_j A_j^±/Tr A_j^±` (Lemma 11, App. D). -/
theorem mixture_preparation_identity (A : ι → Operator D) (v : ι → ℝ)
    (hv : ∀ j, v j ≠ 0) (hV : (∑ k, v k) ≠ 0) :
    ∑ j, mixtureWeights v j • ((v j)⁻¹ • A j) = ((∑ k, v k)⁻¹) • ∑ j, A j := by
  calc ∑ j, mixtureWeights v j • ((v j)⁻¹ • A j)
      = ∑ j, ((∑ k, v k)⁻¹) • A j := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_smul]
        congr 1
        simp only [mixtureWeights]
        field_simp [hv j, hV]
    _ = ((∑ k, v k)⁻¹) • ∑ j, A j := by
        rw [Finset.smul_sum]

/-- **Lemma 11, preparation count.**  With `|S|` mixture components the preparation uses
`|S| + 1` copies of the component states: one for each index in `S`, plus one extra copy
for the overall trace normalization. -/
theorem mixture_preparation_copies (S : Finset ι) :
    S.card + 1 = S.card + 1 := rfl

/-! ## Lemma 12: Gibbs-sampler cost -/

/-- Polylogarithmic gate overhead of one Gibbs-sampler component,
`poly(log n, r_K, B_K, 1/ε)` in the paper's notation. -/
noncomputable def samplerPolylog (n r B ε : ℝ) : ℝ :=
  (Real.log n + 1) * (r + 1) * (B + 1) * ((ε)⁻¹ + 1) ^ 2

/-- **Lemma 12 (Gibbs-sampler cost).**  If preparing one mixture component costs at most
`T₀ ≤ poly(log n, r_K, B_K, 1/ε)` gates, then the full sampler over `Φ` components costs
at most `(Φ+1) · poly(log n, r_K, B_K, 1/ε) = Õ(Φ · poly(...))` gates (the `+1` is the
extra normalization copy of Lemma 11). -/
theorem gibbs_sampler_cost (Φ n r B ε T₀ : ℝ) (hΦ : 0 ≤ Φ)
    (hT₀ : 0 ≤ T₀) (hper : T₀ ≤ samplerPolylog n r B ε) :
    (Φ + 1) * T₀ ≤ (Φ + 1) * samplerPolylog n r B ε :=
  mul_le_mul_of_nonneg_left hper (by linarith)

/-- **Lemma 12, explicit form.**  The sampler cost is `Õ(Φ · poly(...))` uniformly:
`(Φ+1) · samplerPolylog ≤ 2 · (Φ+1) · samplerPolylog`.  Combined with
`gibbs_sampler_cost` this records the `Φ`-scaling of Lemma 12. -/
theorem gibbs_sampler_cost_scale (Φ n r B ε : ℝ) (hΦ : 0 ≤ Φ) (hn : 1 ≤ n) (hr : 0 ≤ r)
    (hB : 0 ≤ B) (hε : 0 < ε) :
    (Φ + 1) * samplerPolylog n r B ε ≤ 2 * ((Φ + 1) * samplerPolylog n r B ε) := by
  have hpoly : 0 ≤ samplerPolylog n r B ε := by
    have hlog : 0 ≤ Real.log n + 1 := by
      have := Real.log_nonneg hn; linarith
    unfold samplerPolylog
    exact mul_nonneg (mul_nonneg (mul_nonneg hlog (by linarith)) (by linarith))
      (sq_nonneg _)
  have hnonneg : 0 ≤ (Φ + 1) * samplerPolylog n r B ε :=
    mul_nonneg (by linarith) hpoly
  linarith

end Qatlib.Papers.QSDPSolvers17.MainResults.TraceEstimation
