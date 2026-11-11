/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowNormSubgoalHuan
import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowChannelSubgoalHuan
import QuantumInfo.ForMathlib.Matrix

/-!
# Proposition 5, linear variance terms for random Clifford measurements

Fixed source: Hsin-Yuan Huang, Richard Kueng, John Preskill, *Predicting Many
Properties of a Quantum System from Very Few Measurements*, arXiv:2002.08953v2,
PDF SHA256 `7d0b0d0896354d6261fa36f3e4b5ed79c5b0334c966310d5d516e53671e0eef5`.

Source location: supplementary §6C ("Concrete variance bounds for random
Clifford measurements"), PDF pp. 29--31 — Proposition 5 Eq. (S69) together with
its proof Eqs. (S71)--(S76), and Lemma 6 Eq. (S70).

Proposition 5 bounds the three variance terms of the quadratic-function
estimator `tr(O ρ̂₁⊗ρ̂₂)`. Two of the three terms are *linear* in a single
snapshot, `Var[tr(O ρ⊗ρ̂)]` and `Var[tr(O ρ̂⊗ρ)]`; the source computes both with
the linear-feature variance bound of Proposition 1, Eq. (S71):
`Var[tr(Oρ⊗ρ̂)] ≤ 3·tr(Õ_ρ²) ≤ 3·tr(O²)` with `Õ_ρ = tr₁(ρ⊗I·O)`.
The third (double-shadow) term is Lemma 6, Eq. (S70); that term needs the
Clifford 3-design identity (S77) and is **not** delivered here.

Delivered here (the two *linear* terms of Eq. (S69), and the source's stated
traceless constant):

* `cliffordShadowVariance_le_traceless` — the single-snapshot shadow variance of
  `tr(Aσ)` is at most `3·tr(A₀²)`, `A₀` the traceless part of `A`. This is the
  source's linear-feature bound `Var[tr(Õ_ρ ρ̂)] ≤ 3·tr(Õ_ρ²)`, derived from the
  frozen third-moment shadow-norm bound (S36)/(S43) plus the unbiasedness of
  Proposition 1 (both imported, not re-proved).
* `cliffordShadowVariance_le_three_trace_sq_of_traceless` — for a traceless
  Hermitian `A` the bound reads `Var ≤ 3·tr(A²)`, the exact constant of
  Eq. (S71) in the form the source uses for its traceless variants `O₀`
  (Eq. (S72)).
* `clifford_quadratic_second_copy_variance_le` — `Var[tr(O ρ̂⊗ρ)] ≤ 3·tr((Õ_ρ)₀²)`
  for the quadratic target `tr(Oρ⊗ρ)`, with `Õ_ρ = tr₂(O·(𝟙⊗ρ))` the partial
  trace of the source's `Õ_ρ = tr₁(ρ⊗𝟙·O)` (copy roles exchanged).
* `clifford_quadratic_first_copy_variance_le` — the same bound for
  `Var[tr(O ρ⊗ρ̂)]`, with `Õ_ρ = tr₁(O·(ρ⊗𝟙))`.

Both two-copy bounds are obtained from the single-snapshot theorem through the
library's Kronecker/partial-trace identities
(`Matrix.trace_mul_kron_one_right`, `Matrix.trace_mul_one_kron_right`), so no
index shuffling is re-derived here. Since the partial trace of a two-copy
observable need not be Hermitian, the observable that enters the variance bound
is its Hermitian part; the real score is unchanged
(`trace_conjTranspose_mul_re_eq`), which is exactly the "ignore symmetrization"
step on PDF p. 30.

Residual gaps (deliberately **not** claimed):

* Lemma 6, Eq. (S70) — the double-shadow term `Var[tr(Oρ̂₁⊗ρ̂₂)] ≤ 9tr(O²) +
  (6/2^n)‖O‖²∞`. It needs the Clifford 3-design permutation-operator
  computation (S77)--(S81), which is not available in the frozen library.
* The "standard norm inequality" `tr(Õ_ρ²) ≤ tr(O²)` of Eq. (S71), i.e. the step
  from the delivered `3·tr((Õ_ρ)₀²)` to the source's final `3·tr(O²)`.
* The two source hypotheses are quantified as hypotheses, as in the frozen
  Proposition 1 contracts: the 2-design identity (S35)
  (`CliffordMomentHypothesisV2`, imported) and the 3-design identity (S36)
  (`CliffordThirdMoment`, defined here). Existence of the `n`-qubit Clifford
  ensemble realizing them is not delivered.

The variance is stated with the *actual* Born record law of the frozen
Clifford primitive (basis outcome `b`, ensemble member `i`, mass
`μᵢ·⟨b|UᵢσUᵢ†|b⟩`) and the actual shadow `ρ̂ = (d+1)U†|b⟩⟨b|U − 𝟙`, so the
statement is not a re-encoding of an abstract distribution.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.ShadowModels.ShadowChannel

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Qatlib.Papers.ClassShadows20.ShadowChannel

open Matrix
open scoped Classical BigOperators ComplexOrder Kronecker

variable {d : ℕ}

/-- The Born weight `⟨b|UσU†|b⟩` of the computational-basis outcome `b` after
the ensemble member `U` is applied to the state `σ`. -/
def cliffordBornWeight (σ U : Operator d) (b : Fin d) : ℝ :=
  (Matrix.trace (basisProjector b * (U * σ * Uᴴ))).re

/-- The third Haar-moment hypothesis on the finite unitary ensemble, i.e. the
source's Eq. (S36) in the exact form consumed by the frozen Clifford
shadow-norm bound. This is the `n`-qubit Clifford group's 3-design property
quantified as a hypothesis, exactly as the frozen Proposition 1 contracts do
for the 2-design identity (S35). -/
def CliffordThirdMoment (d : ℕ) (I : Type) [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) : Prop :=
  ∀ Pp : Operator d, IsPureDensityOperator Pp →
    ∀ B₀ C₀ : Operator d, B₀.IsHermitian → C₀.IsHermitian →
      Matrix.trace B₀ = 0 → Matrix.trace C₀ = 0 →
    (∑ i, (μ.prob i * (Matrix.trace (B₀ * ((Uf i)ᴴ * Pp * Uf i))).re *
        (Matrix.trace (C₀ * ((Uf i)ᴴ * Pp * Uf i))).re) •
        ((Uf i)ᴴ * Pp * Uf i)) =
      ((Matrix.trace (B₀ * C₀)).re /
          ((d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 2))) • 1 +
      (1 / ((d : ℝ) * ((d : ℝ) + 1) * ((d : ℝ) + 2))) • (B₀ * C₀ + C₀ * B₀)

/-- The classical-shadow score of the observable `O` for the record with
ensemble member `U` and computational-basis outcome `b`, i.e.
`tr(O ρ̂) = (d+1)⟨b|UOU†|b⟩ − tr(O)`. -/
def cliffordShadowScore (O U : Operator d) (b : Fin d) : ℝ :=
  ((d : ℝ) + 1) * (Matrix.trace (O * (Uᴴ * basisProjector b * U))).re -
    (Matrix.trace O).re

/-- The exact classical shadow of one record, `ρ̂ = (d+1)U†|b⟩⟨b|U − 𝟙`
(source Proposition 1, Eq. (S38)). -/
def shadowReconstruction (U : Operator d) (b : Fin d) : Operator d :=
  ((d : ℝ) + 1) • (Uᴴ * basisProjector b * U) - 1

/-- The single-snapshot variance of the shadow estimator of `tr(Oσ)`: the
second moment of the score under the actual Born record law minus the square
of its mean `tr(Oσ)`. -/
def cliffordShadowVariance {I : Type} [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) (σ O : Operator d) : ℝ :=
  (∑ b : Fin d, ∑ i : I, μ.prob i * cliffordBornWeight σ (Uf i) b *
      (cliffordShadowScore O (Uf i) b) ^ 2) - (Matrix.trace (O * σ)).re ^ 2

/-- The traceless part `O₀ = O − (tr O/d)·𝟙` of an observable, source
Eq. (S72). -/
def tracelessObservable (O : Operator d) : Operator d :=
  O - (((Matrix.trace O).re : ℂ) / ((d : ℕ) : ℂ)) • (1 : Operator d)

/-- The computational-basis projector has unit trace. -/
theorem trace_basisProjector (b : Fin d) : Matrix.trace (basisProjector b) = 1 := by
  simp [basisProjector, Matrix.trace, Matrix.diag_apply]

/-- A unitary pull-back of a computational-basis projector still has unit
trace, since `tr(U†PU) = tr(PUU†) = tr P`. -/
theorem trace_unitary_conj_basisProjector {U : Operator d} (hU : U * Uᴴ = 1)
    (b : Fin d) : Matrix.trace (Uᴴ * basisProjector b * U) = 1 := by
  calc Matrix.trace (Uᴴ * basisProjector b * U)
      = Matrix.trace (U * Uᴴ * basisProjector b) := Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace (basisProjector b) := by rw [hU, Matrix.one_mul]
    _ = 1 := trace_basisProjector b

/-- A Hermitian matrix has a real trace. -/
theorem trace_isHermitian_real {O : Operator d} (hO : O.IsHermitian) :
    Matrix.trace O = ((Matrix.trace O).re : ℂ) := by
  have him : (Matrix.trace O).im = 0 := by
    rw [Matrix.trace, Complex.im_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hdiag : star (O i i) = O i i := hO.apply i i
    have himi : (O i i).im = 0 := by
      have h := congrArg Complex.im hdiag
      simp only [Complex.star_def, Complex.conj_im] at h
      linarith
    simpa only [Matrix.diag_apply] using himi
  exact Complex.ext rfl (by simpa using him)

/-- The traceless part of a Hermitian observable is Hermitian. -/
theorem tracelessObservable_isHermitian {O : Operator d} (hO : O.IsHermitian) :
    (tracelessObservable O).IsHermitian := by
  have hk : IsSelfAdjoint (((Matrix.trace O).re : ℂ) / ((d : ℕ) : ℂ)) := by
    rw [isSelfAdjoint_iff]
    simp
  exact hO.sub (isHermitian_one.smul hk)

/-- The traceless part has vanishing trace in any positive dimension. -/
theorem tracelessObservable_trace {O : Operator d} (hd : 0 < d) (hO : O.IsHermitian) :
    Matrix.trace (tracelessObservable O) = 0 := by
  have ht : Matrix.trace O = ((Matrix.trace O).re : ℂ) := trace_isHermitian_real hO
  have hdR : ((d : ℝ)) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
  simp only [tracelessObservable, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, smul_eq_mul]
  rw [ht, Complex.ofReal_re]
  have hdC : (((d : ℕ) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hdR
  field_simp
  ring

/-- Decomposition of the shadow score into its traceless part plus the
constant `tr O/d`, source Eq. (S73): the linear-in-one-snapshot terms of the
quadratic estimator. -/
theorem cliffordShadowScore_eq_traceless {U : Operator d} (hU : U * Uᴴ = 1)
    (hd : 0 < d) (O : Operator d) (b : Fin d) :
    cliffordShadowScore O U b =
      ((d : ℝ) + 1) *
          (Matrix.trace (tracelessObservable O * (Uᴴ * basisProjector b * U))).re
        + (Matrix.trace O).re / (d : ℝ) := by
  have hdR : ((d : ℝ)) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
  set Q : Operator d := Uᴴ * basisProjector b * U with hQ
  have htr : Matrix.trace Q = 1 := by
    rw [hQ, trace_unitary_conj_basisProjector hU b]
  have hsplit : Matrix.trace (tracelessObservable O * Q)
      = Matrix.trace (O * Q) - (((Matrix.trace O).re : ℂ) / ((d : ℕ) : ℂ)) := by
    simp only [tracelessObservable, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.one_mul, htr, smul_eq_mul, mul_one]
  have hre : ((Matrix.trace (O * Q) - (((Matrix.trace O).re : ℂ) / ((d : ℕ) : ℂ))).re)
      = (Matrix.trace (O * Q)).re - (Matrix.trace O).re / (d : ℝ) := by
    rw [Complex.sub_re, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [hsplit, hre]
  simp only [cliffordShadowScore, hQ]
  field_simp
  ring


/-- Flattening a double sum into a sum over the product index. -/
theorem sum_prod_eq {α β : Type} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ p : α × β, f p.1 p.2 := by
  rw [Fintype.sum_prod_type]

/-- The shadow score is the real part of the trace against the reconstructed
shadow `ρ̂ = (d+1)U†|b⟩⟨b|U − 𝟙`. -/
theorem cliffordShadowScore_eq_trace_reconstruction {U : Operator d} (O : Operator d)
    (b : Fin d) :
    cliffordShadowScore O U b = (Matrix.trace (O * shadowReconstruction U b)).re := by
  simp only [cliffordShadowScore, shadowReconstruction, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
    smul_eq_mul]

/-- The shadow score of `tr(Oσ)` is unbiased under the actual Born record law
(source Proposition 1, Eq. (S42)), hence the second moment minus the square of
`tr(Oσ)` is a genuine variance. -/
theorem cliffordShadowScore_expect_eq
    (hd : 2 ≤ d) {I : Type} [Fintype I] [DecidableEq I] (μ : FinDist I)
    (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf)
    (σ : Operator d) (hσ : IsDensityOperator σ) (O : Operator d) :
    (∑ b : Fin d, ∑ i : I, μ.prob i * cliffordBornWeight σ (Uf i) b *
        cliffordShadowScore O (Uf i) b) = (Matrix.trace (O * σ)).re := by
  have hch := clifford_actual_channel d hd I μ Uf h35 σ hσ
  have h := clifford_unbiased_of_actual_channel d I μ Uf hκU σ hσ hch O
  rw [← h]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  rw [cliffordShadowScore_eq_trace_reconstruction]
  rfl

/-- **Proposition 5, Eq. (S71), single-snapshot variance bound.**  For every
Hermitian observable `O` and every density `σ`, the shadow estimator of
`tr(Oσ)` has variance at most `3·tr(O₀²)`, `O₀` the traceless part of `O`.
This is the source's linear-feature variance bound, derived from the frozen
third-moment shadow-norm bound (S36)/(S43) and the unbiasedness of
Proposition 1. -/
theorem cliffordShadowVariance_le_traceless
    (hd : 2 ≤ d) {I : Type} [Fintype I] [DecidableEq I] (μ : FinDist I)
    (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf)
    (h36 : CliffordThirdMoment d I μ Uf)
    (σ : Operator d) (hσ : IsDensityOperator σ)
    (O : Operator d) (hO : O.IsHermitian) :
    cliffordShadowVariance μ Uf σ O ≤
      3 * (Matrix.trace (tracelessObservable O * tracelessObservable O)).re := by
  classical
  have hd0 : 0 < d := by omega
  set O₀ : Operator d := tracelessObservable O with hO₀def
  have hO₀herm : O₀.IsHermitian := tracelessObservable_isHermitian hO
  have hO₀tr : Matrix.trace O₀ = 0 := tracelessObservable_trace hd0 hO
  set c : ℝ := (Matrix.trace O).re / (d : ℝ) with hc
  set W : Fin d × I → ℝ := fun p => μ.prob p.2 * cliffordBornWeight σ (Uf p.2) p.1 with hW
  set S : Fin d × I → ℝ := fun p => cliffordShadowScore O (Uf p.2) p.1 with hS
  set S₀ : Fin d × I → ℝ := fun p =>
    ((d : ℝ) + 1) * (Matrix.trace (O₀ * ((Uf p.2)ᴴ * basisProjector p.1 * Uf p.2))).re with hS₀
  -- the score splits into the traceless score plus the constant `tr O/d`
  have hSe : ∀ p : Fin d × I, μ.prob p.2 ≠ 0 → S p = S₀ p + c := by
    intro p hp
    have hpos : 0 < μ.prob p.2 := lt_of_le_of_ne (μ.nonneg p.2) (Ne.symm hp)
    have hmem : Uf p.2 ∈ Matrix.unitaryGroup (Fin d) ℂ := hκU p.2 hpos
    have h1 : (Uf p.2)ᴴ * Uf p.2 = 1 := by
      simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hmem
    have huu : Uf p.2 * (Uf p.2)ᴴ = 1 := mul_eq_one_comm.mp h1
    have h := cliffordShadowScore_eq_traceless huu hd0 O p.1
    simpa only [hS, hS₀, hc, hO₀def] using h
  -- pointwise expansion of the centered square
  have hsplit : ∀ p : Fin d × I,
      W p * (S p) ^ 2 = W p * (S₀ p) ^ 2 + (2 * c) * (W p * S₀ p) + c ^ 2 * W p := by
    intro p
    by_cases hp : μ.prob p.2 = 0
    · have hWz : W p = 0 := by
        simp only [hW, hp, zero_mul]
      rw [hWz]
      ring
    · have hSe' := hSe p hp
      rw [hSe']
      ring
  -- the Born record law has total mass one
  have hW1 : (∑ p : Fin d × I, W p) = 1 := by
    rw [← sum_prod_eq (α := Fin d) (β := I)
      (f := fun b i => μ.prob i * cliffordBornWeight σ (Uf i) b)]
    simpa only [hW, cliffordBornWeight] using clifford_basis_record_mass_one d I μ Uf hκU σ hσ
  -- the shadow score is unbiased
  have hS1 : (∑ p : Fin d × I, W p * S p) = (Matrix.trace (O * σ)).re := by
    rw [← sum_prod_eq (α := Fin d) (β := I)
      (f := fun b i => (μ.prob i * cliffordBornWeight σ (Uf i) b) *
        cliffordShadowScore O (Uf i) b)]
    simpa only [hW, hS] using cliffordShadowScore_expect_eq hd μ Uf hκU h35 σ hσ O
  -- therefore the first moment of the traceless score is `tr(Oσ) − tr O/d`
  have hS0 : (∑ p : Fin d × I, W p * S₀ p) = (Matrix.trace (O * σ)).re - c := by
    have hpoint : ∀ p : Fin d × I, W p * S₀ p = W p * S p - c * W p := by
      intro p
      by_cases hp : μ.prob p.2 = 0
      · have hWz : W p = 0 := by
          simp only [hW, hp, zero_mul]
        rw [hWz]
        ring
      · have hSe' := hSe p hp
        rw [hSe']
        ring
    calc (∑ p : Fin d × I, W p * S₀ p)
        = ∑ p : Fin d × I, (W p * S p - c * W p) := Finset.sum_congr rfl fun p _ => hpoint p
      _ = (∑ p : Fin d × I, W p * S p) - c * (∑ p : Fin d × I, W p) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = (Matrix.trace (O * σ)).re - c := by rw [hS1, hW1, mul_one]
  -- the frozen third-moment bound at the traceless part
  have hS0sq : (∑ p : Fin d × I, W p * (S₀ p) ^ 2) ≤
      3 * (Matrix.trace (O₀ * O₀)).re := by
    have h := cliffordBasisShadowNormSubgoal d hd I μ Uf hκU h36 σ hσ O₀ hO₀herm hO₀tr
    rw [sum_prod_eq (α := Fin d) (β := I)
      (f := fun b i => (μ.prob i * (Matrix.trace (basisProjector b *
          (Uf i * σ * (Uf i)ᴴ))).re) *
        (((d : ℝ) + 1) *
          (Matrix.trace (O₀ * ((Uf i)ᴴ * basisProjector b * Uf i))).re) ^ 2)] at h
    simpa only [hW, hS₀, cliffordBornWeight] using h
  -- assemble
  have hvar : cliffordShadowVariance μ Uf σ O
      = (∑ p : Fin d × I, W p * (S p) ^ 2) - (Matrix.trace (O * σ)).re ^ 2 := by
    rw [cliffordShadowVariance]
    rw [← sum_prod_eq (α := Fin d) (β := I)
      (f := fun b i => (μ.prob i * cliffordBornWeight σ (Uf i) b) *
        (cliffordShadowScore O (Uf i) b) ^ 2)]
  have hsq : (∑ p : Fin d × I, W p * (S p) ^ 2)
      = (∑ p : Fin d × I, W p * (S₀ p) ^ 2) + (2 * c) * (∑ p : Fin d × I, W p * S₀ p)
        + c ^ 2 * (∑ p : Fin d × I, W p) := by
    calc (∑ p : Fin d × I, W p * (S p) ^ 2)
        = ∑ p : Fin d × I, (W p * (S₀ p) ^ 2 + (2 * c) * (W p * S₀ p) + c ^ 2 * W p) :=
          Finset.sum_congr rfl fun p _ => hsplit p
      _ = (∑ p : Fin d × I, W p * (S₀ p) ^ 2) + (∑ p : Fin d × I, (2 * c) * (W p * S₀ p))
            + ∑ p : Fin d × I, c ^ 2 * W p := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = (∑ p : Fin d × I, W p * (S₀ p) ^ 2) + (2 * c) * (∑ p : Fin d × I, W p * S₀ p)
            + c ^ 2 * (∑ p : Fin d × I, W p) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  rw [hvar, hsq, hS0, hW1]
  have hfin : (∑ p : Fin d × I, W p * (S₀ p) ^ 2)
        + (2 * c) * ((Matrix.trace (O * σ)).re - c) + c ^ 2 * 1
        - (Matrix.trace (O * σ)).re ^ 2
      = (∑ p : Fin d × I, W p * (S₀ p) ^ 2) - ((Matrix.trace (O * σ)).re - c) ^ 2 := by
    ring
  rw [hfin]
  nlinarith [hS0sq, sq_nonneg ((Matrix.trace (O * σ)).re - c)]


/-! ## The two-copy quadratic functional `Var[tr(O ρ̂⊗ρ)]` -/

/-- A two-copy operator on `d ⊗ d`, indexed by pairs `(copy₁, copy₂)`. This is
the carrier of the quadratic target `tr(O ρ⊗ρ)`, source Eq. (S69). -/
abbrev TwoCopy (d : ℕ) := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ

/-- The partial trace `tr₂(O·(𝟙⊗ρ))` of a two-copy operator against the true
state `ρ` on the second copy. This is the source's `Õ_ρ = tr₁(ρ⊗𝟙·O)` written
with the roles of the two copies exchanged, i.e. the linear observable whose
shadow estimator is `tr(O ρ̂⊗ρ)`. -/
def twoCopyPartialTrace (ρ : Operator d) (O : TwoCopy d) : Operator d :=
  (O * ((1 : Operator d) ⊗ₖ ρ)).traceRight

/-- The Hermitian part `(Õ_ρ + Õ_ρ†)/2` of the partial-trace observable. The
source explicitly discards symmetrization ("which can only make the variance
smaller", PDF p. 30); for a Hermitian `O` and Hermitian `ρ` the symmetrization
does not change the real score, which `twoCopy_score_eq` records. -/
def twoCopyObservable (ρ : Operator d) (O : TwoCopy d) : Operator d :=
  (((1 : ℝ) / 2 : ℝ) : ℂ) •
    (twoCopyPartialTrace ρ O + (twoCopyPartialTrace ρ O)ᴴ)

/-- The computational basis projector is Hermitian. -/
theorem basisProjector_isHermitian (b : Fin d) : (basisProjector b).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  by_cases hi : i = b <;> by_cases hj : j = b <;>
    simp [basisProjector, hi, hj]

/-- A unitarily pulled-back computational projector is Hermitian. -/
theorem unitary_conj_basisProjector_isHermitian (U : Operator d) (b : Fin d) :
    (Uᴴ * basisProjector b * U).IsHermitian := by
  rw [Matrix.IsHermitian]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, (basisProjector_isHermitian b).eq, Matrix.mul_assoc]

/-- The classical shadow `(d+1)U†|b⟩⟨b|U − 𝟙` is Hermitian. -/
theorem shadowReconstruction_isHermitian (U : Operator d) (b : Fin d) :
    (shadowReconstruction U b).IsHermitian := by
  have hk : IsSelfAdjoint (((((d : ℝ) + 1) : ℝ)) : ℂ) := by
    rw [isSelfAdjoint_iff]
    simp
  have hQ : (Uᴴ * basisProjector b * U).IsHermitian :=
    unitary_conj_basisProjector_isHermitian U b
  have h1 : ((1 : Operator d)).IsHermitian := isHermitian_one
  exact (hQ.smul hk).sub h1

/-- The Hermitian part of a matrix is Hermitian. -/
theorem hermitianPart_isHermitian (A : Operator d) :
    (((((1 : ℝ) / 2 : ℝ)) : ℂ) • (A + Aᴴ)).IsHermitian := by
  have hk : IsSelfAdjoint (((((1 : ℝ) / 2 : ℝ)) : ℂ)) := by
    rw [isSelfAdjoint_iff]
    simp
  have hsum : (A + Aᴴ).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
  exact hsum.smul hk

/-- The symmetrized partial-trace observable is Hermitian without any
hypothesis on `O`. -/
theorem twoCopyObservable_isHermitian (ρ : Operator d) (O : TwoCopy d) :
    (twoCopyObservable ρ O).IsHermitian :=
  hermitianPart_isHermitian _

/-- A Hermitian `N` makes the real trace pairing insensitive to adjunction of
the other factor: `Re tr(M†N) = Re tr(MN)`. -/
theorem trace_conjTranspose_mul_re_eq {M N : Operator d} (hN : N.IsHermitian) :
    (Matrix.trace (Mᴴ * N)).re = (Matrix.trace (M * N)).re := by
  have h : Matrix.trace (Mᴴ * N) = star (Matrix.trace (M * N)) := by
    calc Matrix.trace (Mᴴ * N) = star (Matrix.trace ((Mᴴ * N)ᴴ)) := by
          rw [Matrix.trace_conjTranspose]
          simp
      _ = star (Matrix.trace (Nᴴ * M)) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      _ = star (Matrix.trace (M * Nᴴ)) := by rw [Matrix.trace_mul_comm]
      _ = star (Matrix.trace (M * N)) := by rw [hN.eq]
  rw [h, Complex.star_def, Complex.conj_re]

/-- The source's identity `tr(O ρ̂⊗ρ) = tr(Õ_ρ ρ̂)` (Eq. (S71) first step),
obtained from the Kronecker/partial-trace identity of the library. -/
theorem twoCopy_trace_eq (ρ ρhat : Operator d) (O : TwoCopy d) :
    Matrix.trace (O * (ρhat ⊗ₖ ρ)) = Matrix.trace (twoCopyPartialTrace ρ O * ρhat) := by
  rw [show O * (ρhat ⊗ₖ ρ) =
      O * ((1 : Operator d) ⊗ₖ ρ) * (ρhat ⊗ₖ (1 : Operator d)) from by
    rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul]
    simp]
  rw [Matrix.trace_mul_kron_one_right]
  rfl

/-- The real score of the two-copy functional equals the shadow score of the
symmetrized partial-trace observable, for every record `(U, b)`:
`Re tr(O ρ̂⊗ρ) = tr(Õ_ρ ρ̂)` with `ρ̂ = (d+1)U†|b⟩⟨b|U − 𝟙` the actual shadow. -/
theorem twoCopy_score_eq {ρ : Operator d} (O : TwoCopy d)
    (U : Operator d) (b : Fin d) :
    (Matrix.trace (O * (shadowReconstruction U b ⊗ₖ ρ))).re =
      cliffordShadowScore (twoCopyObservable ρ O) U b := by
  have hρh : (shadowReconstruction U b).IsHermitian := shadowReconstruction_isHermitian U b
  have hid := twoCopy_trace_eq ρ (shadowReconstruction U b) O
  have hscore := cliffordShadowScore_eq_trace_reconstruction (U := U) (twoCopyObservable ρ O) b
  have hsymm : ((twoCopyObservable ρ O) * shadowReconstruction U b).trace
      = (((1 : ℝ) / 2 : ℝ) : ℂ) *
        ((twoCopyPartialTrace ρ O * shadowReconstruction U b).trace
          + ((twoCopyPartialTrace ρ O)ᴴ * shadowReconstruction U b).trace) := by
    simp only [twoCopyObservable, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul]
  have hpair : ((twoCopyPartialTrace ρ O)ᴴ * shadowReconstruction U b).trace.re
      = ((twoCopyPartialTrace ρ O) * shadowReconstruction U b).trace.re :=
    trace_conjTranspose_mul_re_eq hρh
  rw [hid, hscore, hsymm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, hpair]
  ring


/-- The real trace pairing against the true state is unchanged by the
symmetrization: `Re tr(Õ_ρ ρ) = Re tr(Õ_ρ† ρ)` for Hermitian `ρ`. -/
theorem twoCopyObservable_mul_trace_re {ρ : Operator d} (hρ : ρ.IsHermitian)
    (O : TwoCopy d) :
    (Matrix.trace (twoCopyObservable ρ O * ρ)).re
      = (Matrix.trace (twoCopyPartialTrace ρ O * ρ)).re := by
  have hpair : ((twoCopyPartialTrace ρ O)ᴴ * ρ).trace.re
      = ((twoCopyPartialTrace ρ O) * ρ).trace.re := trace_conjTranspose_mul_re_eq hρ
  have hsymm : ((twoCopyObservable ρ O) * ρ).trace
      = (((1 : ℝ) / 2 : ℝ) : ℂ) *
        ((twoCopyPartialTrace ρ O * ρ).trace + ((twoCopyPartialTrace ρ O)ᴴ * ρ).trace) := by
    simp only [twoCopyObservable, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul]
  rw [hsymm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, hpair]
  ring

/-- **Proposition 5, Eq. (S71), variance of the two-copy term
`tr(O ρ̂⊗ρ)`.**  Under the actual Clifford Born record law, the variance of the
quadratic functional `tr(O ρ̂⊗ρ)` — with `ρ̂ = (d+1)U†|b⟩⟨b|U − 𝟙` and the
true state `ρ` on the second copy — is at most `3·tr((Õ_ρ)₀²)`, where `Õ_ρ` is
the partial trace `tr₂(O·(𝟙⊗ρ))` (the source's `Õ_ρ = tr₁(ρ⊗𝟙·O)` with the two
copies exchanged) and `(Õ_ρ)₀` its traceless part.  This is the first inequality
of Eq. (S71); the subsequent "standard norm inequality"
`tr(Õ_ρ²) ≤ tr(O²)`, hence the source's final `3·tr(O²)`, is not formalized
here. -/
theorem clifford_quadratic_second_copy_variance_le
    (hd : 2 ≤ d) {I : Type} [Fintype I] [DecidableEq I] (μ : FinDist I)
    (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf)
    (h36 : CliffordThirdMoment d I μ Uf)
    (ρ : Operator d) (hρ : IsDensityOperator ρ) (O : TwoCopy d) :
    (∑ b : Fin d, ∑ i : I, μ.prob i * cliffordBornWeight ρ (Uf i) b *
        (Matrix.trace (O * (shadowReconstruction (Uf i) b ⊗ₖ ρ))).re ^ 2)
      - (Matrix.trace (O * (ρ ⊗ₖ ρ))).re ^ 2
      ≤ 3 * (Matrix.trace (tracelessObservable (twoCopyObservable ρ O) *
          tracelessObservable (twoCopyObservable ρ O))).re := by
  classical
  set A : Operator d := twoCopyObservable ρ O with hA
  have hAh : A.IsHermitian := twoCopyObservable_isHermitian ρ O
  have hbound := cliffordShadowVariance_le_traceless hd μ Uf hκU h35 h36 ρ hρ A hAh
  have hscore : ∀ (b : Fin d) (i : I),
      (Matrix.trace (O * (shadowReconstruction (Uf i) b ⊗ₖ ρ))).re
        = cliffordShadowScore A (Uf i) b := by
    intro b i
    rw [hA]
    exact twoCopy_score_eq O (Uf i) b
  have hmean : (Matrix.trace (O * (ρ ⊗ₖ ρ))).re = (Matrix.trace (A * ρ)).re := by
    rw [hA, twoCopy_trace_eq, twoCopyObservable_mul_trace_re hρ.1.isHermitian]
  have heq : (∑ b : Fin d, ∑ i : I, μ.prob i * cliffordBornWeight ρ (Uf i) b *
        (Matrix.trace (O * (shadowReconstruction (Uf i) b ⊗ₖ ρ))).re ^ 2)
      - (Matrix.trace (O * (ρ ⊗ₖ ρ))).re ^ 2
      = cliffordShadowVariance μ Uf ρ A := by
    rw [cliffordShadowVariance]
    simp only [hscore, hmean]
  rw [heq]
  exact hbound

/-- A traceless observable equals its own traceless part. -/
theorem tracelessObservable_eq_self {O : Operator d} (h : Matrix.trace O = 0) :
    tracelessObservable O = O := by
  simp only [tracelessObservable, h]
  simp

/-- **Proposition 5, Eq. (S71), the source's stated constant.**  For a
*traceless* Hermitian observable the single-snapshot shadow variance is at most
`3·tr(O²)`, the form in which the source applies the linear bound to the
traceless variants `O₀` of Eq. (S72). -/
theorem cliffordShadowVariance_le_three_trace_sq_of_traceless
    (hd : 2 ≤ d) {I : Type} [Fintype I] [DecidableEq I] (μ : FinDist I)
    (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf)
    (h36 : CliffordThirdMoment d I μ Uf)
    (σ : Operator d) (hσ : IsDensityOperator σ)
    (O : Operator d) (hO : O.IsHermitian) (hO0 : Matrix.trace O = 0) :
    cliffordShadowVariance μ Uf σ O ≤ 3 * (Matrix.trace (O * O)).re := by
  simpa only [tracelessObservable_eq_self hO0] using
    cliffordShadowVariance_le_traceless hd μ Uf hκU h35 h36 σ hσ O hO


/-- The partial trace `tr₁(O·(ρ⊗𝟙))`: the observable contracting the *first*
copy against the true state. This is the source's `Õ_ρ = tr₁(ρ⊗𝟙·O)` with the
copy roles as in the variance term `Var[tr(O ρ⊗ρ̂)]`. -/
def twoCopyPartialTraceLeft (ρ : Operator d) (O : TwoCopy d) : Operator d :=
  (O * (ρ ⊗ₖ (1 : Operator d))).traceLeft

/-- The Hermitian part of the first-copy partial-trace observable. -/
def twoCopyObservableLeft (ρ : Operator d) (O : TwoCopy d) : Operator d :=
  (((1 : ℝ) / 2 : ℝ) : ℂ) •
    (twoCopyPartialTraceLeft ρ O + (twoCopyPartialTraceLeft ρ O)ᴴ)

/-- The symmetrized first-copy partial trace is Hermitian. -/
theorem twoCopyObservableLeft_isHermitian (ρ : Operator d) (O : TwoCopy d) :
    (twoCopyObservableLeft ρ O).IsHermitian :=
  hermitianPart_isHermitian _

/-- The source's identity `tr(O ρ⊗ρ̂) = tr(Õ_ρ ρ̂)` for the first-copy partial
trace, from the Kronecker/partial-trace identity of the library. -/
theorem twoCopy_trace_eq_left (ρ ρhat : Operator d) (O : TwoCopy d) :
    Matrix.trace (O * (ρ ⊗ₖ ρhat)) = Matrix.trace (twoCopyPartialTraceLeft ρ O * ρhat) := by
  rw [show O * (ρ ⊗ₖ ρhat) =
      O * (ρ ⊗ₖ (1 : Operator d)) * ((1 : Operator d) ⊗ₖ ρhat) from by
    rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul]
    simp]
  rw [Matrix.trace_mul_one_kron_right]
  rfl

/-- The real score of the first-copy two-copy functional equals the shadow
score of the symmetrized first-copy partial trace. -/
theorem twoCopy_score_eq_left {ρ : Operator d} (O : TwoCopy d) (U : Operator d)
    (b : Fin d) :
    (Matrix.trace (O * (ρ ⊗ₖ shadowReconstruction U b))).re =
      cliffordShadowScore (twoCopyObservableLeft ρ O) U b := by
  have hρh : (shadowReconstruction U b).IsHermitian := shadowReconstruction_isHermitian U b
  have hid := twoCopy_trace_eq_left ρ (shadowReconstruction U b) O
  have hscore := cliffordShadowScore_eq_trace_reconstruction (U := U)
    (twoCopyObservableLeft ρ O) b
  have hsymm : ((twoCopyObservableLeft ρ O) * shadowReconstruction U b).trace
      = (((1 : ℝ) / 2 : ℝ) : ℂ) *
        ((twoCopyPartialTraceLeft ρ O * shadowReconstruction U b).trace
          + ((twoCopyPartialTraceLeft ρ O)ᴴ * shadowReconstruction U b).trace) := by
    simp only [twoCopyObservableLeft, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul]
  have hpair : ((twoCopyPartialTraceLeft ρ O)ᴴ * shadowReconstruction U b).trace.re
      = ((twoCopyPartialTraceLeft ρ O) * shadowReconstruction U b).trace.re :=
    trace_conjTranspose_mul_re_eq hρh
  rw [hid, hscore, hsymm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, hpair]
  ring

/-- The real trace pairing of the symmetrized first-copy partial trace against
the true state is unchanged. -/
theorem twoCopyObservableLeft_mul_trace_re {ρ : Operator d} (hρ : ρ.IsHermitian)
    (O : TwoCopy d) :
    (Matrix.trace (twoCopyObservableLeft ρ O * ρ)).re
      = (Matrix.trace (twoCopyPartialTraceLeft ρ O * ρ)).re := by
  have hpair : ((twoCopyPartialTraceLeft ρ O)ᴴ * ρ).trace.re
      = ((twoCopyPartialTraceLeft ρ O) * ρ).trace.re := trace_conjTranspose_mul_re_eq hρ
  have hsymm : ((twoCopyObservableLeft ρ O) * ρ).trace
      = (((1 : ℝ) / 2 : ℝ) : ℂ) *
        ((twoCopyPartialTraceLeft ρ O * ρ).trace
          + ((twoCopyPartialTraceLeft ρ O)ᴴ * ρ).trace) := by
    simp only [twoCopyObservableLeft, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
      Matrix.trace_add, smul_eq_mul]
  rw [hsymm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, hpair]
  ring

/-- **Proposition 5, Eq. (S71), variance of the other two-copy term
`tr(O ρ⊗ρ̂)`.**  Same statement as
`clifford_quadratic_second_copy_variance_le` with the true state on the first
copy and the shadow on the second; this is the second of the two linear terms
in Eq. (S69). -/
theorem clifford_quadratic_first_copy_variance_le
    (hd : 2 ≤ d) {I : Type} [Fintype I] [DecidableEq I] (μ : FinDist I)
    (Uf : I → Operator d)
    (hκU : ∀ i, 0 < μ.prob i → Uf i ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (h35 : CliffordMomentHypothesisV2 d I μ Uf)
    (h36 : CliffordThirdMoment d I μ Uf)
    (ρ : Operator d) (hρ : IsDensityOperator ρ) (O : TwoCopy d) :
    (∑ b : Fin d, ∑ i : I, μ.prob i * cliffordBornWeight ρ (Uf i) b *
        (Matrix.trace (O * (ρ ⊗ₖ shadowReconstruction (Uf i) b))).re ^ 2)
      - (Matrix.trace (O * (ρ ⊗ₖ ρ))).re ^ 2
      ≤ 3 * (Matrix.trace (tracelessObservable (twoCopyObservableLeft ρ O) *
          tracelessObservable (twoCopyObservableLeft ρ O))).re := by
  classical
  set A : Operator d := twoCopyObservableLeft ρ O with hA
  have hAh : A.IsHermitian := twoCopyObservableLeft_isHermitian ρ O
  have hbound := cliffordShadowVariance_le_traceless hd μ Uf hκU h35 h36 ρ hρ A hAh
  have hscore : ∀ (b : Fin d) (i : I),
      (Matrix.trace (O * (ρ ⊗ₖ shadowReconstruction (Uf i) b))).re
        = cliffordShadowScore A (Uf i) b := by
    intro b i
    rw [hA]
    exact twoCopy_score_eq_left O (Uf i) b
  have hmean : (Matrix.trace (O * (ρ ⊗ₖ ρ))).re = (Matrix.trace (A * ρ)).re := by
    rw [hA, twoCopy_trace_eq_left, twoCopyObservableLeft_mul_trace_re hρ.1.isHermitian]
  have heq : (∑ b : Fin d, ∑ i : I, μ.prob i * cliffordBornWeight ρ (Uf i) b *
        (Matrix.trace (O * (ρ ⊗ₖ shadowReconstruction (Uf i) b))).re ^ 2)
      - (Matrix.trace (O * (ρ ⊗ₖ ρ))).re ^ 2
      = cliffordShadowVariance μ Uf ρ A := by
    rw [cliffordShadowVariance]
    simp only [hscore, hmean]
  rw [heq]
  exact hbound

end Qatlib.Papers.ClassShadows20.ShadowChannel
