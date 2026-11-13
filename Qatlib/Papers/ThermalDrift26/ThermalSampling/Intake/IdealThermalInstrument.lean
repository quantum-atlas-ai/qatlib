/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Ideal Thermal Source Instruments

This module constructs the finite quantum instrument underlying the thermal source of
[JiangEtAl2026]. `ReflectionFamily` records Hermitian involutions, and `sourceKraus` normalizes
the weak operators `1 + a*sigma` and `1 - a*sigma` against a finite index distribution. Their
completeness yields `idealInstrument` and its joint index-and-sign law `bornLaw`.

`pathKraus` and `pathInstrument` compose repeated outcomes in chronological order. `bornState`
and `pathBornState` return normalized conditional states on positive-probability outcomes and
use a supplied reference state otherwise, so probability-weighted states still recover the
corresponding instrument branches.

## Main statements

* `sourceKraus_index_complete` and `sourceKraus_complete` prove the local and total Kraus
  completeness identities.
- `bornLaw_index` recovers the original index distribution after summing over the sign.
- `pathInstrument_branch_succ` decomposes a path at its first outcome.
- `pathBornState_branch` recovers a path branch from its probability and conditional state.

## References

* [Jiang et al., 2026][JiangEtAl2026], *Thermal-Drift Sampling: Generating Thermal Ensembles for
  Learning Many-Body Systems*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators ComplexOrder

/-- A family of `L` operators on a `d`-dimensional space, each Hermitian and squaring to the
identity. -/
structure ReflectionFamily (L d : ℕ) where
  sigma : Fin L → Qatlib.Foundations.PureStateMath.Operator d
  hermitian : ∀ j, (sigma j).IsHermitian
  square : ∀ j, sigma j * sigma j = 1

/-- The weak-reflection operator `I + a*sigma_j` for sign `false` and `I - a*sigma_j` for sign
`true`. -/
def weakOperator {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ) (j : Fin L) (b : Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  1 + ((if b then -a else a : ℝ) : ℂ) • F.sigma j

/-- Every weak-reflection operator equals its conjugate transpose for real `a`. -/
private theorem weakOperator_hermitian {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ)
    (j : Fin L) (b : Bool) : (weakOperator F a j b)ᴴ = weakOperator F a j b := by
  have hj : (F.sigma j)ᴴ = F.sigma j := F.hermitian j
  cases b <;> simp [weakOperator, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hj]

/-- For a fixed reflection index, the squares of the two weak-reflection operators sum to
`2*(1+a^2)` times the identity. -/
private theorem weakOperator_square_pair {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ) (j : Fin L) :
    weakOperator F a j true * weakOperator F a j true +
      weakOperator F a j false * weakOperator F a j false =
      ((2 * (1 + a ^ 2) : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) := by
  dsimp only [weakOperator]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, F.square]
  ext i k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The nonnegative normalization coefficient `sqrt(p_j / (2*(1+a^2)))` for a source outcome
with index `j`. -/
def sourceCoefficient {L : ℕ} (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (j : Fin L) : ℝ :=
  Real.sqrt (p.prob j / (2 * (1 + a ^ 2)))

/-- The source Kraus operator for an index-and-sign outcome, obtained by scaling its
weak-reflection operator by `sourceCoefficient`. -/
def sourceKraus {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (o : Fin L × Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  (sourceCoefficient p a o.1 : ℂ) • weakOperator F a o.1 o.2

/-- For a fixed index `j`, summing `Kᴴ*K` over its two signs gives `p_j` times the identity. -/
theorem sourceKraus_index_complete {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (j : Fin L) :
    (∑ b : Bool, (sourceKraus F p a (j, b))ᴴ * sourceKraus F p a (j, b)) =
      (p.prob j : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) := by
  have hd : 0 < 2 * (1 + a ^ 2) := by nlinarith [sq_nonneg a]
  have hc : sourceCoefficient p a j * sourceCoefficient p a j * (2 * (1 + a ^ 2)) = p.prob j := by
    have hs := Real.sq_sqrt (div_nonneg (p.nonneg j) hd.le)
    have he := (eq_div_iff (ne_of_gt hd)).mp hs
    simpa only [sourceCoefficient, pow_two] using he
  rw [Fintype.sum_bool]
  simp only [sourceKraus, Matrix.conjTranspose_smul, weakOperator_hermitian,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  rw [← smul_add, weakOperator_square_pair, smul_smul]
  congr 1
  exact_mod_cast hc

/-- The source Kraus operators satisfy the completeness relation `sum_o K_oᴴ*K_o = I` over all
index-and-sign outcomes. -/
theorem sourceKraus_complete {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) :
    ∑ o : Fin L × Bool, (sourceKraus F p a o)ᴴ * sourceKraus F p a o = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [sourceKraus_index_complete]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum, p.sum_one, Complex.ofReal_one, one_smul]

/-- The quantum instrument on index-and-sign outcomes defined by the complete family
`sourceKraus`, for the ideal thermal source model of [JiangEtAl2026]. -/
def idealInstrument {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (Fin L × Bool) d d :=
  Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus (sourceKraus F p a) (sourceKraus_complete F p a)

/-- The ideal instrument branch for outcome `o` sends `rho` to `sourceKraus o * rho *
(sourceKraus o)ᴴ`. -/
@[simp] theorem idealInstrument_branch {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (o : Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (idealInstrument F p a).branch o rho = sourceKraus F p a o * rho * (sourceKraus F p a o)ᴴ := rfl

/-- The normalized finite distribution of index-and-sign outcomes given by the ideal
instrument's Born probabilities on the input density operator. -/
def bornLaw {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L × Bool) where
  prob := Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (idealInstrument F p a) rho.val
  nonneg := fun o => Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg _ rho.property.1 o
  sum_one := Qatlib.Concepts.AdaptiveCP.BranchTrace.sum_instrumentProb_isDensityOperator _ rho.property

/-- The normalized conditional output density of the ideal instrument when the selected outcome
has positive probability, and the supplied reference density otherwise. -/
def bornState {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (rho reference : Qatlib.Foundations.PureStateMath.DensityOperator d) (o : Fin L × Bool) : Qatlib.Foundations.PureStateMath.DensityOperator d := by
  classical
  by_cases h : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (idealInstrument F p a) rho.val o
  · exact ⟨(idealInstrument F p a).conditionalState rho.val o h,
      Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.isDensityOperator_conditionalState _ rho.property o h⟩
  · exact reference

/-- Summing the Born probabilities over both signs at index `j` recovers `p_j`, independently of
the input density and real weak-step parameter. -/
theorem bornLaw_index {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) :
    ∑ b : Bool, (bornLaw F p a rho).prob (j, b) = p.prob j := by
  have he : (∑ b : Bool, Matrix.trace (sourceKraus F p a (j, b) * rho.val *
      (sourceKraus F p a (j, b))ᴴ)) =
      Matrix.trace ((∑ b : Bool, (sourceKraus F p a (j, b))ᴴ * sourceKraus F p a (j, b)) * rho.val) := by
    rw [Finset.sum_mul, Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Matrix.trace_mul_comm (sourceKraus F p a (j, b) * rho.val), ← Matrix.mul_assoc]
  simp only [bornLaw, Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb,
      idealInstrument_branch]
  rw [← Complex.re_sum, he, sourceKraus_index_complete, Matrix.smul_mul, Matrix.one_mul,
    Matrix.trace_smul, rho.property.2]
  simp

/-- The branch at `(j,b)` is the weak-reflection sandwich of `rho`, scaled by `p_j /
(2*(1+a^2))`. -/
theorem idealInstrument_branch_weak {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (j : Fin L) (b : Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (idealInstrument F p a).branch (j, b) rho =
      ((p.prob j / (2 * (1 + a ^ 2)) : ℝ) : ℂ) •
        (weakOperator F a j b * rho * weakOperator F a j b) := by
  rw [idealInstrument_branch]
  simp only [sourceKraus, Matrix.conjTranspose_smul, weakOperator_hermitian,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.star_def, Complex.conj_ofReal]
  have hd : 0 < 2 * (1 + a ^ 2) := by nlinarith [sq_nonneg a]
  have hs := Real.sq_sqrt (div_nonneg (p.nonneg j) hd.le)
  have hc : (sourceCoefficient p a j : ℂ) * (sourceCoefficient p a j : ℂ) =
      ((p.prob j / (2 * (1 + a ^ 2)) : ℝ) : ℂ) := by
    exact_mod_cast (show sourceCoefficient p a j * sourceCoefficient p a j =
      p.prob j / (2 * (1 + a ^ 2)) by simpa only [sourceCoefficient, pow_two] using hs)
  rw [hc]

/-- The ordered Kraus product along a finite outcome path, with the earliest outcome acting
first and the empty path assigned the identity. -/
def pathKraus {O : Type} {d : ℕ} (K : O → Qatlib.Foundations.PureStateMath.Operator d) : (N : ℕ) → (Fin N → O) → Qatlib.Foundations.PureStateMath.Operator d
  | 0, _ => 1
  | N + 1, w => pathKraus K N (fun i => w i.succ) * K (w 0)

/-- If a finite one-step Kraus family is complete, its ordered products over all length-`N`
paths also satisfy Kraus completeness. -/
private theorem pathKraus_complete {O : Type} [Fintype O] {d : ℕ} (K : O → Qatlib.Foundations.PureStateMath.Operator d)
    (hK : ∑ o, (K o)ᴴ * K o = 1) (N : ℕ) :
    ∑ w : Fin N → O, (pathKraus K N w)ᴴ * pathKraus K N w = 1 := by
  induction N with
  | zero => simp [pathKraus]
  | succ N ih =>
    have he : (∑ w : Fin (N + 1) → O, (pathKraus K (N + 1) w)ᴴ * pathKraus K (N + 1) w) =
        ∑ o : O, ∑ tail : Fin N → O,
          (pathKraus K N tail * K o)ᴴ * (pathKraus K N tail * K o) := by
      have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (N + 1) => O))
        (fun z : O × (Fin N → O) => (pathKraus K N z.2 * K z.1)ᴴ * (pathKraus K N z.2 * K z.1))
        (fun w => (pathKraus K (N + 1) w)ᴴ * pathKraus K (N + 1) w)
        (fun z => by simp [pathKraus, Fin.consEquiv])
      rw [Fintype.sum_prod_type] at h
      exact h.symm
    rw [he]
    calc
      _ = ∑ o : O, (K o)ᴴ * (∑ tail : Fin N → O, (pathKraus K N tail)ᴴ * pathKraus K N tail) * K o := by
        apply Finset.sum_congr rfl
        intro o _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro tail _
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ∑ o : O, (K o)ᴴ * K o := by simp only [ih, Matrix.mul_one]
      _ = 1 := hK

/-- The instrument whose outcomes are length-`N` source paths and whose Kraus operators are the
ordered products of the one-step source Kraus operators. -/
def pathInstrument {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) :
    Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument (Fin N → Fin L × Bool) d d :=
  Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.ofKraus (pathKraus (sourceKraus F p a) N)
    (pathKraus_complete (sourceKraus F p a) (sourceKraus_complete F p a) N)

/-- The branch of the path instrument is the sandwich of `rho` by the path's ordered Kraus
product and its conjugate transpose. -/
@[simp] theorem pathInstrument_branch {L d : ℕ} (F : ReflectionFamily L d)
    (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ) (N : ℕ) (w : Fin N → Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (pathInstrument F p a N).branch w rho =
      pathKraus (sourceKraus F p a) N w * rho * (pathKraus (sourceKraus F p a) N w)ᴴ := rfl

/-- A length-`N+1` branch first applies the ideal instrument at the first outcome, then applies
the length-`N` path instrument along the remaining outcomes. -/
theorem pathInstrument_branch_succ {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (a : ℝ) (N : ℕ) (w : Fin (N + 1) → Fin L × Bool) (rho : Qatlib.Foundations.PureStateMath.Operator d) :
    (pathInstrument F p a (N + 1)).branch w rho =
      (pathInstrument F p a N).branch (fun i => w i.succ)
        ((idealInstrument F p a).branch (w 0) rho) := by
  simp only [pathInstrument_branch, idealInstrument_branch, pathKraus,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The normalized finite Born distribution associated with an arbitrary instrument and input
density operator. -/
private def instrumentLaw {O : Type} [Fintype O] {d : ℕ} (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist O where
  prob := Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I rho.val
  nonneg := fun o => Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg I rho.property.1 o
  sum_one := Qatlib.Concepts.AdaptiveCP.BranchTrace.sum_instrumentProb_isDensityOperator I rho.property

/-- The conditional output density for a positive-probability instrument outcome, using the
outcome-specific reference density when its probability is zero. -/
private def instrumentState {O : Type} [Fintype O] {d : ℕ} (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : O → Qatlib.Foundations.PureStateMath.DensityOperator d) (o : O) : Qatlib.Foundations.PureStateMath.DensityOperator d := by
  classical
  by_cases h : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I rho.val o
  · exact ⟨I.conditionalState rho.val o h,
      Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.isDensityOperator_conditionalState I rho.property o h⟩
  · exact reference o

/-- Multiplying the chosen conditional state's matrix by the outcome probability recovers the
instrument branch, including zero-probability outcomes where the reference state is
arbitrary. -/
private theorem instrumentState_branch {O : Type} [Fintype O] {d : ℕ} (I : Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument O d d)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : O → Qatlib.Foundations.PureStateMath.DensityOperator d) (o : O) :
    ((instrumentLaw I rho).prob o : ℂ) • (instrumentState I rho reference o).val = I.branch o rho.val := by
  classical
  change (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I rho.val o : ℂ) •
      (instrumentState I rho reference o).val = _
  by_cases h : 0 < Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I rho.val o
  · simp only [instrumentState, h, dite_true, Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument.conditionalState, smul_smul]
    have hn : (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I rho.val o : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt h
    rw [mul_inv_cancel₀ hn, one_smul]
  · have hz : Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb I rho.val o = 0 := by
      have hn := Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_nonneg I rho.property.1 o
      have hle := not_lt.mp h
      linarith
    have hb :=
        (Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb_eq_zero_iff I rho.property.1 o).mp hz
    simp only [hz, Complex.ofReal_zero, zero_smul, hb]

/-- The finite Born distribution of length-`N` outcome paths generated by the source path
instrument on `rho`. -/
def pathBornLaw {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (N : ℕ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin N → Fin L × Bool) :=
  instrumentLaw (pathInstrument F p a N) rho

/-- The conditional density at the end of a source path, using the path-dependent reference
density when the path probability is zero. -/
def pathBornState {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (N : ℕ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d)
    (w : Fin N → Fin L × Bool) : Qatlib.Foundations.PureStateMath.DensityOperator d :=
  instrumentState (pathInstrument F p a N) rho reference w

/-- The path probability times its conditional density matrix equals the path instrument's
unnormalized output branch, for every path and every supplied reference family. -/
theorem pathBornState_branch {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L)) (a : ℝ)
    (N : ℕ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (reference : (Fin N → Fin L × Bool) → Qatlib.Foundations.PureStateMath.DensityOperator d)
    (w : Fin N → Fin L × Bool) :
    ((pathBornLaw F p a N rho).prob w : ℂ) • (pathBornState F p a N rho reference w).val =
      (pathInstrument F p a N).branch w rho.val :=
  instrumentState_branch (pathInstrument F p a N) rho reference w

end Qatlib.Papers.ThermalDrift26.ThermalSampling
