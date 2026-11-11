/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Qatlib.Papers.LatticeSieve21.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# LatticeSieve21 / MainResults / Concentration — cap statistics and concentration

Fixed paper version: arXiv:2105.05608v1 (12 May 2021), André Chailloux and
Johanna Loyer, *Lattice sieving via quantum random walks*.

This file formalizes the probabilistic statements of Section 3 (p.5) and
Section 5 (p.10) of the paper:

* Proposition 5 (claim c004): the two cap events `v ∈ H_{s,α}` and `s ∈ H_{v,α}`
  have the same probability, and both equal the cap measure `V_d(α)`;
* Proposition 6 (claim c005): the multiplicative Chernoff tail
  `Pr[|S ∩ H_{v,α}| ≥ 2N^x] ≤ exp(-N^x/3)` for a sum of independent Bernoulli
  indicators of mean `N^x`;
* Proposition 9 (claim c009): the intersection bound
  `Pr[E₁ ∧ E₂] ≥ Pr[E₁] + Pr[E₂] - 1`;
* Lemma 1 (claim c010): the expected number of reducing pairs is exact
  (linearity of expectation), and a probability lower bound transfers to
  `min{…,1}`-truncated products;
* Lemma 2 (claim c011): the union bound `Pr[E₂] ≥ 1 - |C₂|·exp(-N^{c₂}/3)`.

Statements are phrased over an abstract probability space; the analytic inputs
that the paper derives from the uniform measure on the sphere (namely the cap
measure `V_d(α)` and the Bernoulli moment generating function bound) are kept
as explicit hypotheses, exactly as they enter the paper's argument.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped RealInnerProductSpace ENNReal

namespace Qatlib.Papers.LatticeSieve21.MainResults.Concentration

open InnerProductGeometry
open Qatlib.Papers.LatticeSieve21.MainResults.Definitions

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Proposition 5 — symmetry of the cap event -/

/-- **Proposition 5 (claim c004), symmetry part, p.5.**  For any measure and any
random vector `v`, the cap events `θ(v,s) ≤ α` and `θ(s,v) ≤ α` coincide,
because the angle is symmetric. -/
theorem prop5_cap_event_symm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (μ : Measure Ω) (v : Ω → E) (s : E) (α : ℝ) :
    μ.real {ω | angle (v ω) s ≤ α} = μ.real {ω | angle s (v ω) ≤ α} := by
  congr 1
  ext ω
  simp only [Set.mem_setOf_eq, angle_comm]

/-- **Proposition 5 (claim c004), p.5.**  If `v` is uniform on the unit sphere
and the cap measure hypothesis `hcap : Pr[θ(v,s) ≤ α] = V_d(α)` holds, then both
`Pr[v ∈ H_{s,α}]` and `Pr[s ∈ H_{v,α}]` equal `V_d(α)`.  The cap measure itself
is the uniform-sphere input recorded by `hcap` (the paper's Proposition 2). -/
theorem prop5 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : Ω → E) (s : E) (α d : ℝ)
    (hcap : μ.real {ω | angle (v ω) s ≤ α} = V d α) :
    μ.real {ω | angle (v ω) s ≤ α} = μ.real {ω | angle s (v ω) ≤ α} ∧
      μ.real {ω | angle s (v ω) ≤ α} = V d α := by
  refine ⟨prop5_cap_event_symm μ v s α, ?_⟩
  rw [← prop5_cap_event_symm μ v s α]
  exact hcap

/-! ## Proposition 6 — Chernoff tail -/

/-- **Proposition 6 (claim c005), p.5.**  Let `X` be the number of points of a
random `N^x`-subset that fall in the cap `H_{v,α}`.  `X` is a sum of independent
Bernoulli variables of mean `N^x = m`, so its moment generating function obeys
`mgf X (log 2) ≤ exp((e^{log 2} - 1)·m)`.  Then the multiplicative Chernoff
bound gives `Pr[X ≥ 2m] ≤ exp(-m/3)`, i.e. `Pr[|S ∩ H_{v,α}| ≥ 2N^x] ≤
exp(-N^x/3)`.  The mgf bound is the only analytic input; it is recorded as
`hmgf`. -/
theorem prop6_chernoff (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {m : ℝ} (hm : 0 ≤ m)
    (hint : Integrable (fun ω => Real.exp (Real.log 2 * X ω)) μ)
    (hmgf : mgf X μ (Real.log 2) ≤ Real.exp ((Real.exp (Real.log 2) - 1) * m)) :
    μ.real {ω | 2 * m ≤ X ω} ≤ Real.exp (-(m / 3)) := by
  have ht : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcher := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) (t := Real.log 2)
    (2 * m) ht hint
  have hlog2 : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hbound : Real.exp (-(Real.log 2) * (2 * m)) * mgf X μ (Real.log 2) ≤
      Real.exp (-(m / 3)) := by
    have hstep : Real.exp (-(Real.log 2) * (2 * m)) * mgf X μ (Real.log 2) ≤
        Real.exp (-(Real.log 2) * (2 * m)) *
          Real.exp ((Real.exp (Real.log 2) - 1) * m) := by
      gcongr
    refine hstep.trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hexp2]
    have hfac : m * (4 / 3 - 2 * Real.log 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hm (by linarith)
    nlinarith
  exact hcher.trans hbound

/-! ## Proposition 9 — the intersection bound -/

/-- **Proposition 9 (claim c009), p.10.**  For any probability measure and any
measurable event `E₂`, `Pr[E₁ ∧ E₂] ≥ Pr[E₁] + Pr[E₂] - 1`; this is the paper's
step `Pr[E₁ ∧ E₂] ≥ Pr[E₁] + Pr[E₂] - 1`, obtained from
`Pr[E₁ ∪ E₂] + Pr[E₁ ∩ E₂] = Pr[E₁] + Pr[E₂]` and `Pr[E₁ ∪ E₂] ≤ 1`. -/
theorem prop9_intersection (μ : Measure Ω) [IsProbabilityMeasure μ]
    {E1 E2 : Set Ω} (hE2 : MeasurableSet E2) :
    μ.real E1 + μ.real E2 - 1 ≤ μ.real (E1 ∩ E2) := by
  have hunion := measureReal_union_add_inter (μ := μ) (s := E1) (t := E2) hE2
  have hle : μ.real (E1 ∪ E2) ≤ 1 := by
    calc μ.real (E1 ∪ E2) ≤ μ.real Set.univ :=
          measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp [Measure.real]
  linarith

/-! ## Lemma 1 — first-step cap bound -/

/-- **Lemma 1 (claim c010), expectation part, p.10.**  For a finite family of
real random variables with common expectation `p`, linearity of expectation
gives `E[Σᵢ Xᵢ] = |ι|·p`.  In the paper `Xᵢ` is the indicator that the `i`-th
point lies in the cap `H_{v,α}`, and the expectation is `N^{2c₁}V_d(β)`. -/
theorem lemma1_expected_pairs {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsFiniteMeasure μ] (X : ι → Ω → ℝ) (p : ℝ)
    (hint : ∀ i, Integrable (X i) μ) (hmean : ∀ i, ∫ ω, X i ω ∂μ = p) :
    ∫ ω, ∑ i, X i ω ∂μ = (Fintype.card ι : ℝ) * p := by
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  simp [hmean, Finset.sum_const, nsmul_eq_mul]

/-- **Lemma 1 (claim c010), probability part, p.10.**  A lower bound `a` on the
probability of `E₀ ⊆ E₁`, multiplied by any `b ∈ [0,1]`, is still a lower bound
on `Pr[E₁]`.  This is the paper's step turning the cap estimate
`Θ(N^{2c₁}V_d(β))` into `Θ(min{N^{2c₁}V_d(β),1})`: the second factor is the
probability that the remaining events occur, which is at most one. -/
theorem lemma1_cap_bound (μ : Measure Ω) [IsFiniteMeasure μ] {E0 E1 : Set Ω}
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (h : a ≤ μ.real E0) (hsub : E0 ⊆ E1) : a * b ≤ μ.real E1 := by
  have hm : μ.real E0 ≤ μ.real E1 := measureReal_mono hsub
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  nlinarith

/-! ## Lemma 2 — union bound over the bad buckets -/

/-- **Lemma 2 (claim c011), p.10.**  If each of finitely many measurable events
`Aᵢ` has probability at least `1 - q`, then the probability that all of them
occur is at least `1 - |ι|·q`.  In the paper `Aᵢ` is the good event for the
`i`-th bucket, `q = exp(-N^{c₂}/3)` (Proposition 6) and `|ι| = |C₂|`, giving
`Pr[E₂] ≥ 1 - |C₂|·exp(-N^{c₂}/3)`. -/
theorem lemma2_union_bound {ι : Type*} [Fintype ι] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : ι → Set Ω) (q : ℝ)
    (hmeas : ∀ i, MeasurableSet (A i))
    (hA : ∀ i, 1 - q ≤ μ.real (A i)) :
    1 - (Fintype.card ι : ℝ) * q ≤ μ.real (⋂ i, A i) := by
  have hu : μ.real Set.univ = 1 := by simp [Measure.real]
  have hI : MeasurableSet (⋂ i, A i) := MeasurableSet.iInter hmeas
  have hpart : μ.real (⋂ i, A i) + μ.real (⋂ i, A i)ᶜ = 1 := by
    have h := measureReal_add_measureReal_compl (μ := μ) hI
    rwa [hu] at h
  have hterm : ∀ i, μ.real ((A i)ᶜ) ≤ q := by
    intro i
    have h := measureReal_add_measureReal_compl (μ := μ) (hmeas i)
    rw [hu] at h
    linarith [hA i]
  have hsum : ∑ i, μ.real ((A i)ᶜ) ≤ ∑ _i : ι, q :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hbound : μ.real (⋃ i, (A i)ᶜ) ≤ (Fintype.card ι : ℝ) * q := by
    refine (measureReal_iUnion_fintype_le (μ := μ) (fun i => (A i)ᶜ)).trans ?_
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  have hcompl : (⋂ i, A i)ᶜ = ⋃ i, (A i)ᶜ := Set.compl_iInter A
  rw [← hcompl] at hbound
  linarith

end Qatlib.Papers.LatticeSieve21.MainResults.Concentration
