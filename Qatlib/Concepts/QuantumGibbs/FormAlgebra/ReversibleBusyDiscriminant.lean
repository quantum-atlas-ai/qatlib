/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.WalkSearch
public import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Stochastic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AmplitudeCore.InvFreePhase Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout Qatlib.Concepts.WalkSearch.TwoLevelLower Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.StateBlockEncoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription Qatlib.Concepts.GateVocabulary.LocalReflectionGates Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.QuantumGibbs.FormAlgebra.ReversibleBusyDiscriminant

open Matrix
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

noncomputable def weightedDiscriminant {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) : Matrix I I ℝ :=
  fun x y => Real.sqrt (π x) * P x y / Real.sqrt (π y)

def AbsoluteDiscriminantGap {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (δ : ℝ) : Prop :=
  IsLUB
    {b : ℝ | b = 0 ∨
      ∃ (ν : ℝ) (v : I → ℝ),
        ν ≠ 1 ∧ v ≠ 0 ∧ SzegedyDiscriminant P *ᵥ v = ν • v ∧ b = |ν|}
    (1 - δ)

/-- For a transition matrix reversible with respect to positive weights, the weighted
discriminant equals the Szegedy discriminant entrywise. -/
theorem weightedDiscriminant_eq {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (hP : IsTransitionMatrix P)
    (hπ : ∀ x, 0 < π x) (hrev : IsReversible P π) (x y : I) :
    weightedDiscriminant P π x y = SzegedyDiscriminant P x y := by
  have ha : 0 ≤ Real.sqrt (π x) * P x y / Real.sqrt (π y) :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hP.1 x y)) (Real.sqrt_nonneg _)
  have hsq : P x y * P y x = (Real.sqrt (π x) * P x y / Real.sqrt (π y)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (hπ x).le, Real.sq_sqrt (hπ y).le]
    have hr := congrArg (fun t : ℝ => t * P x y) (hrev x y)
    field_simp [ne_of_gt (hπ y)]
    nlinarith
  rw [weightedDiscriminant, szegedyDiscriminant_apply]
  calc
    Real.sqrt (π x) * P x y / Real.sqrt (π y) =
        Real.sqrt ((Real.sqrt (π x) * P x y / Real.sqrt (π y)) ^ 2) :=
      (Real.sqrt_sq ha).symm
    _ = Real.sqrt (P x y * P y x) := congrArg Real.sqrt hsq.symm

/-- An absolute discriminant gap parameter is at most one. -/
theorem AbsoluteDiscriminantGap.le_one {I : Type} [Fintype I] [DecidableEq I]
    {P : I → I → ℝ} {δ : ℝ} (hgap : AbsoluteDiscriminantGap P δ) : δ ≤ 1 := by
  have h : (0 : ℝ) ≤ 1 - δ := hgap.1 (Or.inl rfl)
  linarith

/-- An absolute discriminant gap bounds the modulus of every real discriminant eigenvalue other
than one by one minus the gap. -/
theorem AbsoluteDiscriminantGap.eigenvalue_bound {I : Type} [Fintype I] [DecidableEq I]
    {P : I → I → ℝ} {δ ν : ℝ} (hgap : AbsoluteDiscriminantGap P δ)
    (v : I → ℝ) (hν : ν ≠ 1) (hv : v ≠ 0)
    (he : SzegedyDiscriminant P *ᵥ v = ν • v) : |ν| ≤ 1 - δ :=
  hgap.1 (Or.inr ⟨ν, v, hν, hv, he, rfl⟩)

/-- A vector fixed by a matrix is fixed by every natural power of that matrix. -/
theorem fixed_pow {I : Type} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℝ) (v : I → ℝ) (hv : P *ᵥ v = v) (k : ℕ) :
    (P ^ k) *ᵥ v = v := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hv, ih]

/-- Every real fixed vector of a primitive transition matrix on a nonempty finite type is
constant. -/
theorem primitive_fixed_constant {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (P : Matrix I I ℝ) (hP : IsTransitionMatrix P) (hprim : P.IsPrimitive)
    (v : I → ℝ) (hv : P *ᵥ v = v) : ∃ c : ℝ, ∀ x, v x = c := by
  have hP' : P ∈ Matrix.rowStochastic ℝ I := Matrix.mem_rowStochastic_iff_sum.mpr hP
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image Finset.univ v Finset.univ_nonempty
  obtain ⟨k, _, hk⟩ := hprim.exists_pos_pow
  have hp := (Matrix.rowStochastic ℝ I).pow_mem hP' k
  have he := congrFun (fixed_pow P v hv k) z
  have hs : ∑ y, (P ^ k) z y * (v z - v y) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Matrix.sum_row_of_mem_rowStochastic hp, one_mul]
    simpa [Matrix.mulVec, dotProduct] using! sub_eq_zero.mpr he.symm
  have hn : ∀ y ∈ (Finset.univ : Finset I), 0 ≤ (P ^ k) z y * (v z - v y) := by
    intro y hy
    exact mul_nonneg (le_of_lt (hk z y)) (sub_nonneg.mpr (hz y hy))
  refine ⟨v z, fun x => ?_⟩
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hs x (Finset.mem_univ x)
  have hd := (mul_eq_zero.mp h0).resolve_left (ne_of_gt (hk z x))
  exact (sub_eq_zero.mp hd).symm

/-- Dividing a discriminant fixed vector by the square roots of positive reversible weights
yields a transition-matrix fixed vector. -/
theorem transition_fixed_of_discriminant_plus_one {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (hP : IsTransitionMatrix P)
    (hπ : ∀ x, 0 < π x) (hrev : IsReversible P π)
    (w : I → ℝ) (hw : SzegedyDiscriminant P *ᵥ w = w) :
    P *ᵥ (fun x => w x / Real.sqrt (π x)) = fun x => w x / Real.sqrt (π x) := by
  funext x
  apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr (hπ x)))).mpr
  have hx := congrFun hw x
  calc
    (∑ y, P x y * (w y / Real.sqrt (π y))) * Real.sqrt (π x) =
        ∑ y, (Real.sqrt (π x) * P x y / Real.sqrt (π y)) * w y := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      field_simp
    _ = (SzegedyDiscriminant P *ᵥ w) x := by
      simp only [← weightedDiscriminant_eq P π hP hπ hrev, weightedDiscriminant,
        Matrix.mulVec, dotProduct]
    _ = w x := hx

/-- For a primitive reversible transition matrix with positive weights, every real discriminant
fixed vector is a multiple of their square roots. -/
theorem discriminant_plus_one_real_eq_stationary_smul {I : Type}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (hP : IsTransitionMatrix P) (hprim : Matrix.IsPrimitive P)
    (hπ : ∀ x, 0 < π x) (hrev : IsReversible P π)
    (w : I → ℝ) (hw : SzegedyDiscriminant P *ᵥ w = w) :
    ∃ c : ℝ, w = c • (fun x => Real.sqrt (π x)) := by
  obtain ⟨c, hc⟩ := primitive_fixed_constant P hP hprim _
    (transition_fixed_of_discriminant_plus_one P π hP hπ hrev w hw)
  refine ⟨c, ?_⟩
  funext x
  have hx := (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (hπ x)))).mp (hc x)
  simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using! hx

/-- A complex eigenvector of a real matrix with real eigenvalue yields a nonzero real
eigenvector with the same eigenvalue. -/
theorem exists_real_eigenvector_of_complex {I : Type} [Fintype I] [DecidableEq I]
    (D : Matrix I I ℝ) (v : QState I) (lam : ℝ) (hv : v ≠ 0)
    (he : (D.map Complex.ofReal) *ᵥ v = (lam : ℂ) • v) :
    ∃ w : I → ℝ, w ≠ 0 ∧ D *ᵥ w = lam • w := by
  let vr : I → ℝ := fun x => (v x).re
  let vi : I → ℝ := fun x => (v x).im
  have her : D *ᵥ vr = lam • vr := by
    funext x
    have hx := congrArg Complex.re (congrFun he x)
    simpa [vr, Matrix.mulVec, dotProduct, Complex.mul_re] using! hx
  have hei : D *ᵥ vi = lam • vi := by
    funext x
    have hx := congrArg Complex.im (congrFun he x)
    simpa [vi, Matrix.mulVec, dotProduct, Complex.mul_im] using! hx
  by_cases hr : vr = 0
  · refine ⟨vi, ?_, hei⟩
    intro hi
    apply hv
    funext x
    apply Complex.ext
    · have hx := congrFun hr x
      exact hx
    · have hx := congrFun hi x
      exact hx
  · exact ⟨vr, hr, her⟩

/-- A positive absolute discriminant gap forces every complex discriminant eigenvector at minus
one to vanish. -/
theorem discriminant_minus_one_complex_eq_zero {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (δ : ℝ) (hδ : 0 < δ) (hgap : AbsoluteDiscriminantGap P δ)
    (v : QState I) (hv : (SzegedyDiscriminant P).map Complex.ofReal *ᵥ v = (-1 : ℂ) • v) :
    v = 0 := by
  by_contra hn
  obtain ⟨w, hw, he⟩ := exists_real_eigenvector_of_complex (SzegedyDiscriminant P) v (-1) hn
    (by simpa using! hv)
  have hb := AbsoluteDiscriminantGap.eigenvalue_bound hgap w (by norm_num) hw he
  norm_num at hb
  linarith

/-- For a primitive reversible transition matrix with positive weights, complex discriminant
fixed vectors lie in the span of their square roots. -/
theorem discriminant_plus_one_complex_mem_span {I : Type}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (hP : IsTransitionMatrix P) (hprim : Matrix.IsPrimitive P)
    (hπ : ∀ x, 0 < π x) (hrev : IsReversible P π)
    (v : QState I) (hv : (SzegedyDiscriminant P).map Complex.ofReal *ᵥ v = v) :
    v ∈ Submodule.span ℂ {fun x => (Real.sqrt (π x) : ℂ)} := by
  let vr : I → ℝ := fun x => (v x).re
  let vi : I → ℝ := fun x => (v x).im
  have he : (SzegedyDiscriminant P).map Complex.ofReal *ᵥ v = (1 : ℂ) • v := by
    simpa using! hv
  have her : SzegedyDiscriminant P *ᵥ vr = vr := by
    funext x
    have h := congrArg Complex.re (congrFun he x)
    simpa [vr, Matrix.mulVec, dotProduct, Complex.mul_re] using! h
  have hei : SzegedyDiscriminant P *ᵥ vi = vi := by
    funext x
    have h := congrArg Complex.im (congrFun he x)
    simpa [vi, Matrix.mulVec, dotProduct, Complex.mul_im] using! h
  obtain ⟨cr, hcr⟩ := discriminant_plus_one_real_eq_stationary_smul P π hP hprim hπ hrev vr her
  obtain ⟨ci, hci⟩ := discriminant_plus_one_real_eq_stationary_smul P π hP hprim hπ hrev vi hei
  let c : ℂ := (cr : ℂ) + Complex.I * (ci : ℂ)
  have hvc : v = c • (fun x => (Real.sqrt (π x) : ℂ)) := by
    funext x
    apply Complex.ext
    · have hx := congrFun hcr x
      simp [c, vr, hx]
    · have hx := congrFun hci x
      simp [c, vi, hx]
  rw [hvc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- A real eigenvalue of the Szegedy bipartite discriminant yields a nonzero real Szegedy
discriminant eigenvector at that eigenvalue or its negative. -/
theorem exists_real_eigenvector_of_szegedy_bipartite {I : Type}
    [Fintype I] [DecidableEq I] (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (lam : ℝ) (u : QState (I ⊕ I)) (hu : u ≠ 0)
    (he : bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ u =
      (lam : ℂ) • u) :
    ∃ w : I → ℝ, w ≠ 0 ∧
      (SzegedyDiscriminant P *ᵥ w = lam • w ∨ SzegedyDiscriminant P *ᵥ w = -lam • w) := by
  let a : QState I := fun i => u (.inl i)
  let b : QState I := fun i => u (.inr i)
  let D : Matrix I I ℂ := (SzegedyDiscriminant P).map Complex.ofReal
  have hab : D *ᵥ b = (lam : ℂ) • a := by
    have h := congrArg (fun v : QState (I ⊕ I) => fun i => v (.inl i)) he
    simpa [D, a, b, bipartiteDiscriminant, Matrix.fromBlocks_mulVec,
      szegedy_gram_eq_discriminant P hP] using! h
  have hba : D *ᵥ a = (lam : ℂ) • b := by
    have h := congrArg (fun v : QState (I ⊕ I) => fun j => v (.inr j)) he
    have hrev : (SzegedyIsometryB P)ᴴ * SzegedyIsometry P = D := by
      calc
        (SzegedyIsometryB P)ᴴ * SzegedyIsometry P =
            ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P)ᴴ := by simp
        _ = (SzegedyIsometry P)ᴴ * SzegedyIsometryB P := szegedy_gram_hermitian P hP
        _ = D := szegedy_gram_eq_discriminant P hP
    simpa [D, a, b, bipartiteDiscriminant, Matrix.fromBlocks_mulVec, hrev] using! h
  have hplus : D *ᵥ (a + b) = (lam : ℂ) • (a + b) := by
    rw [Matrix.mulVec_add, hab, hba]
    module
  have hminus : D *ᵥ (a - b) = ((-lam : ℝ) : ℂ) • (a - b) := by
    rw [Matrix.mulVec_sub, hab, hba]
    simp only [Complex.ofReal_neg]
    module
  by_cases hp : a + b = 0
  · have hm : a - b ≠ 0 := by
      intro hm
      apply hu
      ext (i | j)
      · have h1 := congrFun hp i
        have h2 := congrFun hm i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2
        change a i = 0
        linear_combination (h1 + h2) / 2
      · have h1 := congrFun hp j
        have h2 := congrFun hm j
        simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply] at h1 h2
        change b j = 0
        linear_combination (h1 - h2) / 2
    obtain ⟨w, hw, hew⟩ := exists_real_eigenvector_of_complex
      (SzegedyDiscriminant P) (a - b) (-lam) hm hminus
    exact ⟨w, hw, Or.inr hew⟩
  · obtain ⟨w, hw, hew⟩ := exists_real_eigenvector_of_complex
      (SzegedyDiscriminant P) (a + b) lam hp hplus
    exact ⟨w, hw, Or.inl hew⟩

/-- Away from both endpoint eigenvalues, a bipartite discriminant eigenvalue has modulus at most
one minus the absolute gap. -/
theorem abs_discriminant_le_of_szegedy_bipartite {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (δ lam : ℝ) (hP : IsTransitionMatrix P)
    (hgap : AbsoluteDiscriminantGap P δ) (hlam : lam ≠ 1) (hnlam : -lam ≠ 1)
    (u : QState (I ⊕ I)) (hu : u ≠ 0)
    (he : bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ u =
      (lam : ℂ) • u) : |lam| ≤ 1 - δ := by
  obtain ⟨w, hw, hew | hew⟩ := exists_real_eigenvector_of_szegedy_bipartite P hP lam u hu he
  · exact AbsoluteDiscriminantGap.eigenvalue_bound hgap w hlam hw hew
  · simpa only [abs_neg] using! AbsoluteDiscriminantGap.eigenvalue_bound hgap w hnlam hw hew

/-- Under primitivity, reversibility, positive weights, and a positive absolute gap, the tilde
image of a bipartite discriminant fixed vector lies in the stationary span. -/
theorem szegedy_tilde_plus_one_mem_stationary_span {I : Type}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (δ : ℝ) (hP : IsTransitionMatrix P)
    (hprim : Matrix.IsPrimitive P) (hπ : ∀ x, 0 < π x) (hrev : IsReversible P π)
    (hδ : 0 < δ) (hgap : AbsoluteDiscriminantGap P δ) (u : QState (I ⊕ I))
    (he : bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ u = u) :
    bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ u ∈
      Submodule.span ℂ {SzegedyEmbedState P π} := by
  let a : QState I := fun i => u (.inl i)
  let b : QState I := fun i => u (.inr i)
  let D : Matrix I I ℂ := (SzegedyDiscriminant P).map Complex.ofReal
  have he' : bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ u =
      (1 : ℂ) • u := by simpa using! he
  have hab : D *ᵥ b = a := by
    have h := congrArg (fun v : QState (I ⊕ I) => fun i => v (.inl i)) he'
    simpa [D, a, b, bipartiteDiscriminant, Matrix.fromBlocks_mulVec,
      szegedy_gram_eq_discriminant P hP] using! h
  have hba : D *ᵥ a = b := by
    have h := congrArg (fun v : QState (I ⊕ I) => fun j => v (.inr j)) he'
    have hrev' : (SzegedyIsometryB P)ᴴ * SzegedyIsometry P = D := by
      calc
        (SzegedyIsometryB P)ᴴ * SzegedyIsometry P =
            ((SzegedyIsometry P)ᴴ * SzegedyIsometryB P)ᴴ := by simp
        _ = (SzegedyIsometry P)ᴴ * SzegedyIsometryB P := szegedy_gram_hermitian P hP
        _ = D := szegedy_gram_eq_discriminant P hP
    simpa [D, a, b, bipartiteDiscriminant, Matrix.fromBlocks_mulVec, hrev'] using! h
  have hminus : D *ᵥ (a - b) = (-1 : ℂ) • (a - b) := by
    rw [Matrix.mulVec_sub, hab, hba]
    module
  have hm : a - b = 0 := discriminant_minus_one_complex_eq_zero P δ hδ hgap (a - b) hminus
  have hb : b = a := (sub_eq_zero.mp hm).symm
  have hDa : D *ᵥ a = a := by simpa [hb] using! hba
  have ha : a ∈ Submodule.span ℂ {fun x => (Real.sqrt (π x) : ℂ)} :=
    discriminant_plus_one_complex_mem_span P π hP hprim hπ hrev a hDa
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  have ht : bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ u =
      ((2 : ℂ) * c) • SzegedyEmbedState P π := by
    rw [bipartiteTilde, Matrix.fromCols_mulVec]
    change SzegedyIsometry P *ᵥ a + SzegedyIsometryB P *ᵥ b = _
    rw [hb, ← hc, Matrix.mulVec_smul, Matrix.mulVec_smul]
    change c • SzegedyEmbedState P π + c • (SzegedyIsometryB P *ᵥ
      (fun x => (Real.sqrt (π x) : ℂ))) = _
    have hswap : SzegedyIsometryB P *ᵥ (fun x => (Real.sqrt (π x) : ℂ)) =
        SzegedyEmbedState P π := by
      funext p
      obtain ⟨x, y⟩ := p
      rw [szegedyEmbedState_apply]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single y]
      · rw [szegedyIsometryB_apply, ite_eq_left rfl, ← Complex.ofReal_mul]
        norm_cast
        rw [← Real.sqrt_mul (hP.1 y x) (π y), ← Real.sqrt_mul (hP.1 x y) (π x),
          mul_comm (P y x) (π y), hrev, mul_comm (P x y) (π x)]
      · intro j _ hj
        rw [szegedyIsometryB_apply, ite_eq_right (fun h => hj h.symm), zero_mul]
      · simp
    rw [hswap]
    module
  rw [ht]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- Under primitivity, reversibility, positive weights, and a positive absolute gap, every busy
Szegedy walk fixed vector lies in the stationary span. -/
theorem szegedy_busy_plus_one_mem_stationary_span {I : Type}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (δ : ℝ) (hP : IsTransitionMatrix P)
    (hprim : Matrix.IsPrimitive P) (hπ : ∀ x, 0 < π x) (hrev : IsReversible P π)
    (hδ : 0 < δ) (hgap : AbsoluteDiscriminantGap P δ) (w : QState (I × I))
    (hw : SzegedyWalk P *ᵥ w = w)
    (hbusy : w ∈ LinearMap.range
      (bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P)).toLin') :
    w ∈ Submodule.span ℂ {SzegedyEmbedState P π} := by
  have hA := szegedyIsometry_conjTranspose_mul P hP
  have hB := szegedyIsometryB_conjTranspose_mul P hP
  obtain ⟨⟨e₁, he₁⟩, _⟩ := bipartite_endpoint_eigenspace_transport
    (I × I) I I (SzegedyIsometry P) (SzegedyIsometryB P) hA hB
  have hw' : bipartiteWalk (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ w = w := by
    simpa only [bipartiteWalk, ← szegedyWalk_eq_twoReflections P hP] using! hw
  have hmem : w ∈ LinearMap.ker
      ((bipartiteWalk (SzegedyIsometry P) (SzegedyIsometryB P) -
        (1 : Matrix (I × I) (I × I) ℂ)).toLin') ⊓
      LinearMap.range (bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P)).toLin' := by
    refine ⟨?_, hbusy⟩
    change (bipartiteWalk (SzegedyIsometry P) (SzegedyIsometryB P) - 1) *ᵥ w = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hw', sub_self]
  let v := e₁.symm ⟨w, hmem⟩
  have ht : bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ v.val = w := by
    rw [← he₁ v]
    exact congrArg Subtype.val (e₁.apply_symm_apply ⟨w, hmem⟩)
  have hd : bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) *ᵥ v.val =
      v.val := by
    have h := v.property
    change (bipartiteDiscriminant (SzegedyIsometry P) (SzegedyIsometryB P) - 1) *ᵥ
      v.val = 0 at h
    simpa only [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] using! h
  have hs := szegedy_tilde_plus_one_mem_stationary_span P π δ hP hprim hπ hrev hδ hgap
    v.val hd
  rwa [ht] at hs

/-- The columns of an isometry are orthonormal. -/
theorem isometry_inner_columns {H K : Type} [Fintype H] [DecidableEq H]
    [Fintype K] [DecidableEq K] (V : Matrix H K ℂ)
    (hV : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V) (i j : K) :
    Qatlib.Foundations.PureStateMath.Inner (fun h => V h i) (fun h => V h j) = if i = j then 1 else 0 := by
  have h := congrFun (congrFun (show Vᴴ * V = 1 from hV) i) j
  simpa [Qatlib.Foundations.PureStateMath.Inner, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] using! h

/-- Normalized vectors lying in the same one-dimensional span have identical outer products. -/
theorem outerProduct_eq_of_normalized_mem_span {H : Type} [Fintype H] [DecidableEq H]
    (v u : QState H) (hv : Normalized v) (hu : Normalized u)
    (hmem : v ∈ Submodule.span ℂ {u}) : outerProduct v = outerProduct u := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hvn : Qatlib.Foundations.PureStateMath.Inner v v = 1 :=
      (normalized_iff_inner_self v).mp hv
  have hun : Qatlib.Foundations.PureStateMath.Inner u u = 1 :=
      (normalized_iff_inner_self u).mp hu
  have hc2 : (starRingEnd ℂ) c * c = 1 := by
    rw [← hc, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      hun, mul_one] at hvn
    exact hvn
  ext i j
  rw [← hc]
  simp only [outerProduct_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  calc
    c * u i * ((starRingEnd ℂ) c * (starRingEnd ℂ) (u j)) =
        ((starRingEnd ℂ) c * c) * (u i * (starRingEnd ℂ) (u j)) := by ring
    _ = u i * (starRingEnd ℂ) (u j) := by rw [hc2, one_mul]

noncomputable def interiorPhase (lam : ℝ) (s : Bool) : ℝ :=
  if s then -(Real.arccos lam / Real.pi) else Real.arccos lam / Real.pi

/-- Exponentiating the scaled interior phase gives the corresponding bipartite phase for an
eigenvalue between minus one and one. -/
theorem exp_interiorPhase (lam : ℝ) (s : Bool) (hl : -1 ≤ lam) (hu : lam ≤ 1) :
    Complex.exp (2 * Real.pi * Complex.I * (interiorPhase lam s : ℂ)) =
      bipartitePhase lam s := by
  have hc := Real.cos_arccos hl hu
  have hs := Real.sin_arccos lam
  rw [show 2 * Real.pi * Complex.I * (interiorPhase lam s : ℂ) =
      (((if s then -(2 * Real.arccos lam) else 2 * Real.arccos lam) : ℝ) : ℂ) *
        Complex.I by
    cases s <;> simp [interiorPhase] <;> field_simp [Real.pi_ne_zero]]
  rw [Complex.exp_ofReal_mul_I]
  cases s <;>
    simp [bipartitePhase, Real.cos_two_mul, Real.sin_two_mul, hc, hs] <;> ring

/-- For an eigenvalue strictly between zero and one, the bipartite phase is not one. -/
theorem bipartitePhase_ne_one_of_interior (lam : ℝ) (s : Bool)
    (hl : 0 < lam) (hu : lam < 1) : bipartitePhase lam s ≠ 1 := by
  intro h
  have hi := congrArg Complex.im h
  have hr : 0 < Real.sqrt (1 - lam ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  simp [bipartitePhase, pow_two, Complex.mul_im, Complex.mul_re] at hi
  simp only [pow_two] at hr
  cases s <;> simp at hi
  all_goals rcases hi with hi | hi <;> first | exact hl.ne' hi | exact hr.ne' hi

/-- For a positive eigenvalue, the distance of its interior phase from zero is its arccosine
divided by pi. -/
theorem phaseDistance_interiorPhase (lam : ℝ) (s : Bool) (hl : 0 < lam) :
    phaseDistance (interiorPhase lam s) 0 = Real.arccos lam / Real.pi := by
  have hθ0 := Real.arccos_nonneg lam
  have hθhalf : Real.arccos lam < Real.pi / 2 := Real.arccos_lt_pi_div_two.mpr hl
  have hq0 : 0 ≤ Real.arccos lam / Real.pi := div_nonneg hθ0 Real.pi_pos.le
  have hqhalf : Real.arccos lam / Real.pi < 1 / 2 := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith
  cases s
  · have hf : ⌊Real.arccos lam / Real.pi + (2 : ℝ)⁻¹⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith
    simp [interiorPhase, phaseDistance, one_div, hf, abs_of_nonneg hq0]
  · have hf : ⌊-(Real.arccos lam / Real.pi) + (2 : ℝ)⁻¹⌋ = (0 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      norm_num
      constructor <;> linarith
    simp [interiorPhase, phaseDistance, one_div, hf, abs_of_nonneg hq0]

/-- For an eigenvalue strictly between zero and one obeying the absolute gap bound, its interior
phase distance from zero is at least half the gap. -/
theorem half_gap_le_phaseDistance_interiorPhase {lam δ : ℝ} (s : Bool)
    (hl : 0 < lam) (hu : lam < 1) (hgaplam : |lam| ≤ 1 - δ) :
    δ / 2 ≤ phaseDistance (interiorPhase lam s) 0 := by
  rw [phaseDistance_interiorPhase lam s hl]
  have hθhalf : Real.arccos lam ≤ Real.pi / 2 := Real.arccos_le_pi_div_two.mpr hl.le
  have hcos := Real.one_sub_mul_le_cos (Real.arccos_nonneg lam) hθhalf
  rw [Real.cos_arccos (by linarith) hu.le] at hcos
  have hlam : lam ≤ 1 - δ := le_trans (le_abs_self lam) hgaplam
  have hδθ : δ ≤ (2 / Real.pi) * Real.arccos lam := by linarith
  calc
    δ / 2 ≤ ((2 / Real.pi) * Real.arccos lam) / 2 := by gcongr
    _ = Real.arccos lam / Real.pi := by ring

/-- A busy spectral frame of a reversible transition matrix with normalized nonnegative weights
contains an eigenvalue equal to one. -/
theorem exists_one_of_busy_spectral_frame {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (hP : IsTransitionMatrix P)
    (hπ : ∀ x, 0 ≤ π x) (hsum : ∑ x, π x = 1) (hrev : IsReversible P π)
    (m : ℕ) (V : Matrix (I × I) (Fin m) ℂ) (z : Fin m → ℂ)
    (hV : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V)
    (hVV : V * Vᴴ = bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P) *
      matrixPseudoinverse (bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P)))
    (hWV : bipartiteWalk (SzegedyIsometry P) (SzegedyIsometryB P) * V =
      V * Matrix.diagonal z) : ∃ j, z j = 1 := by
  let A := SzegedyIsometry P
  let B := SzegedyIsometryB P
  let T := bipartiteTilde A B
  let W := bipartiteWalk A B
  let Φ := SzegedyEmbedState P π
  let s : QState I := fun x => (Real.sqrt (π x) : ℂ)
  let u : QState (I ⊕ I) := Sum.elim s 0
  have hnorm : Normalized Φ := normalized_szegedyEmbedState P hP hπ hsum
  have hΦ0 : Φ ≠ 0 := by
    intro hz
    have hi := (normalized_iff_inner_self Φ).mp hnorm
    rw [hz] at hi
    simp [Qatlib.Foundations.PureStateMath.Inner] at hi
  have hΦW : W *ᵥ Φ = Φ := by
    simpa only [W, A, B, bipartiteWalk, ← szegedyWalk_eq_twoReflections P hP] using!
      szegedyWalk_fixes_stationary P hP hrev
  have hΦsrc : T *ᵥ u = Φ := by
    simp [T, A, B, u, s, Φ, bipartiteTilde, SzegedyEmbedState]
  have hprojΦ : (V * Vᴴ) *ᵥ Φ = Φ := by
    rw [hVV, ← hΦsrc]
    change (T * matrixPseudoinverse T) *ᵥ (T *ᵥ u) = T *ᵥ u
    rw [Matrix.mulVec_mulVec, mul_matrixPseudoinverse_mul]
  let c : QState (Fin m) := Vᴴ *ᵥ Φ
  have hrep : V *ᵥ c = Φ := by
    change V *ᵥ (Vᴴ *ᵥ Φ) = Φ
    rw [Matrix.mulVec_mulVec]
    exact hprojΦ
  have hdiag : Matrix.diagonal z *ᵥ c = z • c := by
    funext j
    simp [Matrix.mulVec_diagonal]
  have haction : V *ᵥ c = V *ᵥ (z • c) := by
    calc
      V *ᵥ c = Φ := hrep
      _ = W *ᵥ Φ := hΦW.symm
      _ = W *ᵥ (V *ᵥ c) := by rw [hrep]
      _ = (W * V) *ᵥ c := Matrix.mulVec_mulVec c W V
      _ = (V * Matrix.diagonal z) *ᵥ c := by rw [hWV]
      _ = V *ᵥ (Matrix.diagonal z *ᵥ c) := (Matrix.mulVec_mulVec c V (Matrix.diagonal z)).symm
      _ = V *ᵥ (z • c) := by rw [hdiag]
  have hc : c = z • c := by
    have h := congrArg (fun v => Vᴴ *ᵥ v) haction
    simpa only [Matrix.mulVec_mulVec, show Vᴴ * V = 1 from hV,
      Matrix.one_mulVec] using! h
  by_contra hn
  push Not at hn
  have hc0 : c = 0 := by
    funext j
    have hj := congrFun hc j
    simp only [smul_eq_mul, Pi.mul_apply, Pi.zero_apply] at hj ⊢
    have hf : (1 - z j) * c j = 0 := by linear_combination hj
    exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr (Ne.symm (hn j)))
  rw [hc0, Matrix.mulVec_zero] at hrep
  exact hΦ0 hrep.symm

/-- Constructs a busy Szegedy spectral frame with a unique stationary eigenvector and nonzero
phase distances at least half the positive absolute gap. -/
theorem exists_busy_szegedy_frame_of_positive_absolute_gap {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    (P : I → I → ℝ) (π : I → ℝ) (δ : ℝ) (hP : IsTransitionMatrix P)
    (hprim : Matrix.IsPrimitive P) (hπ : ∀ x, 0 < π x) (hsum : ∑ x, π x = 1)
    (hrev : IsReversible P π) (hδ : 0 < δ) (hgap : AbsoluteDiscriminantGap P δ) :
    ∃ (m : ℕ) (V : Matrix (I × I) (Fin m) ℂ) (z : Fin m → ℂ) (p : Fin m → ℝ)
      (j0 : Fin m),
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry V ∧
      V * Vᴴ = bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P) *
        matrixPseudoinverse (bipartiteTilde (SzegedyIsometry P) (SzegedyIsometryB P)) ∧
      SzegedyWalk P * V = V * Matrix.diagonal z ∧
      (∀ i, z i = Complex.exp (2 * Real.pi * Complex.I * (p i : ℂ))) ∧
      z j0 = 1 ∧ p j0 = 0 ∧
      outerProduct (fun h => V h j0) = outerProduct (SzegedyEmbedState P π) ∧
      (∀ i, z i = 1 → i = j0) ∧
      (∀ i, z i ≠ 1 → δ / 2 ≤ phaseDistance (p i) 0) := by
  have hA := szegedyIsometry_conjTranspose_mul P hP
  have hB := szegedyIsometryB_conjTranspose_mul P hP
  obtain ⟨m, V, z, hV, hVV, hWV, hm, hlabels⟩ := bipartite_labeled_busy_spectral_frame
    (I × I) I I (SzegedyIsometry P) (SzegedyIsometryB P) hA hB
  have hwalk : SzegedyWalk P * V = V * Matrix.diagonal z := by
    simpa only [bipartiteWalk, ← szegedyWalk_eq_twoReflections P hP] using! hWV
  have hphase : ∀ i, ∃ q : ℝ,
      z i = Complex.exp (2 * Real.pi * Complex.I * (q : ℂ)) ∧
      (z i = 1 → q = 0) ∧ (z i ≠ 1 → δ / 2 ≤ phaseDistance q 0) := by
    intro i
    rcases hlabels i with hp | hm | ⟨lam, hl, hu, s, u, hu0, hd, hz, ht⟩
    · refine ⟨0, by simp [hp.1], fun _ => rfl, ?_⟩
      intro hn
      exact (hn hp.1).elim
    · have hz := hm.1
      have hexp : z i = Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) := by
        rw [hz]
        have he : 2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I := by
          push_cast
          ring
        rw [he, Complex.exp_pi_mul_I]
      have hdist : phaseDistance (1 / 2 : ℝ) 0 = 1 / 2 := by
        norm_num [phaseDistance, Int.floor_eq_iff]
      refine ⟨1 / 2, hexp, ?_, ?_⟩
      · intro h
        rw [hz] at h
        norm_num at h
      · intro _
        rw [hdist]
        have hδ1 := AbsoluteDiscriminantGap.le_one hgap
        linarith
    · have hz1 : z i ≠ 1 := by
        rw [hz]
        exact bipartitePhase_ne_one_of_interior lam s hl hu
      have hb := abs_discriminant_le_of_szegedy_bipartite P δ lam hP hgap
        (by linarith) (by linarith) u hu0 hd
      refine ⟨interiorPhase lam s, hz.trans
        (exp_interiorPhase lam s (by linarith) hu.le).symm, ?_, ?_⟩
      · intro h
        exact (hz1 h).elim
      · intro _
        exact half_gap_le_phaseDistance_interiorPhase s hl hu hb
  choose p hpe hp0 hpg using hphase
  obtain ⟨j0, hj0⟩ := exists_one_of_busy_spectral_frame P π hP (fun x => (hπ x).le)
    hsum hrev m V z hV hVV hWV
  have hone_mem (i : Fin m) (hi : z i = 1) :
      (fun h => V h i) ∈ Submodule.span ℂ {SzegedyEmbedState P π} := by
    rcases hlabels i with hp | hm | ⟨lam, hl, hu, s, u, hu0, hd, hz, ht⟩
    · obtain ⟨u, hu0, hd, ht⟩ := hp.2
      rw [ht]
      exact szegedy_tilde_plus_one_mem_stationary_span P π δ hP hprim hπ hrev hδ hgap u hd
    · rw [hm.1] at hi
      norm_num at hi
    · exact ((bipartitePhase_ne_one_of_interior lam s hl hu) (hz.symm.trans hi)).elim
  have hunique : ∀ i, z i = 1 → i = j0 := by
    intro i hi
    by_contra hij
    have horth := isometry_inner_columns V hV i j0
    rw [ite_eq_right hij] at horth
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hone_mem i hi)
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hone_mem j0 hj0)
    have hw0 : (fun h => V h j0) ≠ 0 := by
      intro hz0
      have hn := isometry_inner_columns V hV j0 j0
      rw [hz0] at hn
      simp [Qatlib.Foundations.PureStateMath.Inner] at hn
    have hd0 : d ≠ 0 := by
      intro hd0
      rw [hd0, zero_smul] at hd
      exact hw0 hd.symm
    have hnorm : Normalized (SzegedyEmbedState P π) :=
      normalized_szegedyEmbedState P hP (fun x => (hπ x).le) hsum
    rw [← hc, ← hd, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left, Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      (normalized_iff_inner_self _).mp hnorm, mul_one] at horth
    have hcd : (starRingEnd ℂ) c * d = 0 := by simpa using! horth
    have hc0 : c = 0 := by
      have hs0 := (mul_eq_zero.mp hcd).resolve_right hd0
      simpa using! hs0
    have hwi0 : (fun h => V h i) = 0 := by rw [← hc, hc0, zero_smul]
    have hn := isometry_inner_columns V hV i i
    rw [hwi0] at hn
    simp [Qatlib.Foundations.PureStateMath.Inner] at hn
  have hnorm : Normalized (SzegedyEmbedState P π) :=
    normalized_szegedyEmbedState P hP (fun x => (hπ x).le) hsum
  have hncol : Normalized (fun h => V h j0) := by
    rw [normalized_iff_inner_self]
    simpa using! isometry_inner_columns V hV j0 j0
  have houter := outerProduct_eq_of_normalized_mem_span (fun h => V h j0)
    (SzegedyEmbedState P π) hncol hnorm (hone_mem j0 hj0)
  exact ⟨m, V, z, p, j0, hV, hVV, hwalk, hpe, hj0, hp0 j0 hj0, houter, hunique, hpg⟩

end Qatlib.Concepts.QuantumGibbs.FormAlgebra.ReversibleBusyDiscriminant
