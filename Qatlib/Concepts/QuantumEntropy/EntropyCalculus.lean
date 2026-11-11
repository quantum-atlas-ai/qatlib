/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import QuantumInfo.Entropy.DPI
import QuantumInfo.Entropy.SSA

/-!
# Density-matrix entropy calculus

This module connects positive semidefinite trace-one matrices to mixed states and transports
entropy and relative entropy across that correspondence. It establishes spectral formulas,
unitary invariance, tensor-product additivity, and partial-trace identities in
finite-dimensional quantum information as developed in [Watrous2018].

The main consumer theorem packages data processing, strong subadditivity, conditional entropy,
and coherent information, with nonsingularity assumptions for finite real relative-entropy
differences.

## Main statements

* `entropy_density_bridge`: Entropy formulas and compatibility with pure states, conjugation,
  products, and partial trace.
* `relative_entropy_density_bridge`: Support, trace-log, equality, invariance, and classical
  relative-entropy formulas.
* `dpi_ssa_partial_trace_consumers`: Channel and partial-trace entropy consequences.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.ChannelTheory.Stinespring

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QuantumEntropy.EntropyCalculus

open Qatlib
open scoped BigOperators ComplexOrder InnerProductSpace RealInnerProductSpace Matrix

/-- The type of positive semidefinite complex matrices with trace one on the finite index type
`I`. -/
abbrev Density (I : Type) [Fintype I] [DecidableEq I] :=
  {ρ : Matrix I I ℂ // ρ.PosSemidef ∧ Matrix.trace ρ = 1}

/-- Convert a density matrix to the corresponding mixed state. -/
def state {I : Type} [Fintype I] [DecidableEq I] (ρ : Density I) : MState I :=
  Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState I ρ

/-- Convert a mixed state to its positive semidefinite trace-one density matrix. -/
def localState {I : Type} [Fintype I] [DecidableEq I] (ρ : MState I) : Density I :=
  (Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState I).symm ρ

/-- The von Neumann entropy of the mixed state corresponding to a density matrix. -/
def entropy {I : Type} [Fintype I] [DecidableEq I] (ρ : Density I) : ℝ := Sᵥₙ (state ρ)

/-- The extended nonnegative quantum relative entropy of the mixed states corresponding to two
density matrices. -/
def relative {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Density I) : ENNReal :=
  qRelativeEnt (state ρ) (state σ)

/-- The real part of the trace of `ρ` times the difference of the matrix logarithms of `ρ` and
`σ`. -/
def logTrace {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Density I) : ℝ :=
  (Matrix.trace (ρ.val * ((state ρ).M.log.mat - (state σ).M.log.mat))).re

/-- The matrix underlying the converted mixed state is the original density matrix. -/
@[simp] theorem state_m {I : Type} [Fintype I] [DecidableEq I] (ρ : Density I) :
    (state ρ).m = ρ.val :=
  Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState_m ρ

/-- The density matrix obtained from a mixed state is its underlying matrix. -/
@[simp] theorem localState_val {I : Type} [Fintype I] [DecidableEq I] (s : MState I) :
    (localState s).val = s.m :=
  Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState_symm_val s

/-- Converting a mixed state to a density matrix and back returns the original state. -/
@[simp] theorem state_localState {I : Type} [Fintype I] [DecidableEq I] (s : MState I) :
    state (localState s) = s := by
  apply MState.ext_m
  rfl

/-- The entropy of a finite probability distribution is the sum of `Real.negMulLog` of its
probabilities. -/
private theorem Hₛ_eq_sum_negMulLog {α : Type} [Fintype α] (d : ProbDistribution α) :
    Hₛ d = ∑ i, Real.negMulLog ((d i : ℝ)) := rfl

/-- Von Neumann entropy is additive on tensor products of mixed states. -/
private theorem Sᵥₙ_prod_add {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (s : MState I) (t : MState J) :
    Sᵥₙ (s ⊗ᴹ t) = Sᵥₙ s + Sᵥₙ t := by
  obtain ⟨e, he⟩ := MState.spectrum_prod s t
  have hcoe : ∀ i j, (((s ⊗ᴹ t).spectrum (e (i, j)) : ℝ)) =
      ((s.spectrum i : ℝ)) * ((t.spectrum j : ℝ)) := fun i j => by
    simpa using congrArg (fun p : Prob => (p : ℝ)) (he i j)
  show Hₛ (s ⊗ᴹ t).spectrum = Hₛ s.spectrum + Hₛ t.spectrum
  rw [Hₛ_eq_sum_negMulLog, Hₛ_eq_sum_negMulLog, Hₛ_eq_sum_negMulLog]
  have hreindex : ∑ k : I × J, Real.negMulLog (((s ⊗ᴹ t).spectrum k : ℝ)) =
      ∑ i, ∑ j, Real.negMulLog (((s ⊗ᴹ t).spectrum (e (i, j)) : ℝ)) := by
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  rw [hreindex]
  simp only [hcoe, Real.negMulLog_mul, Finset.sum_add_distrib]
  have h1 : ∑ i, ∑ j, ((t.spectrum j : ℝ)) * Real.negMulLog ((s.spectrum i : ℝ)) =
      ∑ i, Real.negMulLog ((s.spectrum i : ℝ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, t.spectrum.normalized, one_mul]
  have h2 : ∑ i, ∑ j, ((s.spectrum i : ℝ)) * Real.negMulLog ((t.spectrum j : ℝ)) =
      ∑ j, Real.negMulLog ((t.spectrum j : ℝ)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, s.spectrum.normalized, one_mul]
  rw [h1, h2]

/-- Transfer the spectral entropy formula, nonnegativity, dimension bound, pure-state vanishing,
unitary invariance, and product additivity to density matrices. The bridge also identifies
partial trace and records the zero convention for `Real.negMulLog`, as in [Watrous2018]. -/
theorem entropy_density_bridge :
  (∀ (I : Type) [Fintype I] [DecidableEq I] (ρ : Density I),
    (state ρ).m = ρ.val ∧
    entropy ρ = ∑ i, Real.negMulLog ((state ρ).M.H.eigenvalues i) ∧
    0 ≤ entropy ρ ∧ entropy ρ ≤ Real.log (Fintype.card I)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
    (ψ : {ψ : QState I // Normalized ψ}),
    let ρ :=
        localState (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet I ψ))
    ρ.val = outerProduct ψ.val ∧ entropy ρ = 0) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (ρ : Density I)
    (U : Matrix.unitaryGroup I ℂ),
    let σ := localState ((state ρ).uConj U)
    σ.val = U.val * ρ.val * U.val.conjTranspose ∧ entropy σ = entropy ρ) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : Density I) (σ : Density J),
    let τ := localState ((state ρ).prod (state σ))
    τ.val = TensorGate ρ.val σ.val ∧ entropy τ = entropy ρ + entropy σ) ∧
  (∀ (D E : ℕ) (ρ : Density (Fin D × Fin E)),
    (localState (state ρ).traceRight).val = PartialTrace ρ.val) ∧
  Real.negMulLog 0 = 0 := by
  refine ⟨fun I _ _ ρ => ⟨by simp, ?_, Sᵥₙ_nonneg _, by simpa using! Sᵥₙ_le_log_d (state ρ)⟩,
    ?_, ?_, ?_, ?_, by simp⟩
  · show Sᵥₙ (state ρ) = ∑ i, Real.negMulLog ((state ρ).M.H.eigenvalues i)
    rw [Sᵥₙ, Hₛ_eq_sum_negMulLog]
    rfl
  · intro I _ _ ψ
    constructor
    · show ((Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState I).symm
          (MState.pure (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet I ψ))).val = outerProduct ψ.val
      rw [Qatlib.Foundations.PureStateMath.BornBridge.densityMatrixEquivMState_symm_val,
        Qatlib.Foundations.PureStateMath.BornBridge.pure_normalizedStateEquivKet_m]
      ext i j
      rw [outerProduct_apply]
      rfl
    · show Sᵥₙ (state (localState (MState.pure
          (Qatlib.Foundations.PureStateMath.BornBridge.normalizedStateEquivKet I ψ)))) = 0
      rw [state_localState]
      exact Sᵥₙ_of_pure_zero _
  · intro I _ _ ρ U
    constructor
    · show (((state ρ).uConj U).m) = U.val * ρ.val * U.val.conjTranspose
      rfl
    · show Sᵥₙ (state (localState ((state ρ).uConj U))) = Sᵥₙ (state ρ)
      rw [state_localState]
      exact congrArg Hₛ (MState.uConj_spectrum_eq (state ρ) U)
  · intro I _ _ J _ _ ρ σ
    constructor
    · show (((state ρ).prod (state σ)).m) = TensorGate ρ.val σ.val
      rfl
    · show Sᵥₙ (state (localState ((state ρ).prod (state σ)))) =
        Sᵥₙ (state ρ) + Sᵥₙ (state σ)
      rw [state_localState]
      exact Sᵥₙ_prod_add _ _
  · intro D E ρ
    show ((state ρ).traceRight).m = PartialTrace ρ.val
    rfl

/-- The trace-log expression equals the real inner product of the density operator with the
logarithm difference. -/
private theorem logTrace_eq_inner {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Density I) :
    logTrace ρ σ = ⟪(state ρ).M, (state ρ).M.log - (state σ).M.log⟫ := rfl

/-- For nonnegative `v`, its coercion through `NNReal` to `ENNReal` agrees with `ENNReal.ofReal
v`. -/
private theorem ofNNReal_eq_ofReal {v : ℝ} (hv : 0 ≤ v) :
    ENNReal.ofNNReal ⟨v, hv⟩ = ENNReal.ofReal v := by
  rw [ENNReal.ofReal_eq_coe_nnreal hv]
  rfl

/-- Under the kernel inclusion expressing support containment, quantum relative entropy equals
`ENNReal.ofReal` of the logarithmic inner product. -/
private theorem qRelativeEnt_of_ker {I : Type} [Fintype I] [DecidableEq I]
    (s t : MState I) (h : t.M.ker ≤ s.M.ker) :
    qRelativeEnt s t = ENNReal.ofReal ⟪s.M, s.M.log - t.M.log⟫ := by
  have h1 : qRelativeEnt s t = ENNReal.ofNNReal ⟨⟪s.M, s.M.log - t.M.log⟫,
      inner_log_sub_log_nonneg h⟩ := by
    simp [qRelativeEnt, SandwichedRelRentropy, h]
  rw [h1, ofNNReal_eq_ofReal (inner_log_sub_log_nonneg h)]

/-- For positive `t`, the expression `t * log t - t + 1` is nonnegative. -/
private theorem le_aux_log (t : ℝ) (ht : 0 < t) : 0 ≤ t * Real.log t - t + 1 := by
  have h1 : Real.log (1 / t) ≤ 1 / t - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [show 1 / t = t⁻¹ from (inv_eq_one_div t).symm, Real.log_inv t] at h1
  have h2 : t * (1 - 1 / t) ≤ t * Real.log t := by
    have h3 := mul_le_mul_of_nonneg_right h1 ht.le
    field_simp at h3 ⊢
    linarith
  have h4 : t * (1 - 1 / t) = t - 1 := by field_simp
  nlinarith [h2, h4]

/-- For positive `t` different from one, the expression `t * log t - t + 1` is strictly
positive. -/
private theorem lt_aux_log (t : ℝ) (ht : 0 < t) (ht1 : t ≠ 1) :
    0 < t * Real.log t - t + 1 := by
  have hne : 1 / t ≠ 1 := by
    intro h
    apply ht1
    have h2 : t⁻¹ = 1 := by rwa [inv_eq_one_div]
    exact inv_eq_one.mp h2
  have h1 : Real.log (1 / t) < 1 / t - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) hne
  rw [show 1 / t = t⁻¹ from (inv_eq_one_div t).symm, Real.log_inv t] at h1
  have h2 : t * (1 - 1 / t) < t * Real.log t := by
    have h3 := mul_lt_mul_of_pos_right h1 ht
    field_simp at h3 ⊢
    linarith
  have h4 : t * (1 - 1 / t) = t - 1 := by field_simp
  nlinarith [h2, h4]

/-- The real trace of the product of the two displayed rank-one matrices equals the squared norm
of the corresponding entry of `Uᴴ * V`. -/
private theorem trace_proj_mul_normSq {I : Type} [Fintype I] [DecidableEq I]
    (U V : Matrix I I ℂ) (i j : I) :
    RCLike.re ((U * Matrix.single i i 1 * U.conjTranspose *
        (V * Matrix.single j j 1 * V.conjTranspose)).trace)
      = ‖(U.conjTranspose * V) i j‖ ^ 2 := by
  have hP : ∀ (m c : I), ((U * Matrix.single i i 1 * U.conjTranspose : Matrix I I ℂ)) m c
      = U m i * star (U c i) := by
    intro m c
    have h1 : ∀ k, ((U * Matrix.single i i 1 : Matrix I I ℂ)) m k = if k = i then U m i else 0 := by
      intro k
      simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hki : k = i
      · simp [hki]
      · simp [hki, Ne.symm hki]
    simp only [Matrix.mul_apply, h1, Matrix.conjTranspose_apply]
    by_cases hci : c = i <;> simp [hci]
  have hQ : ∀ (m c : I), ((V * Matrix.single j j 1 * V.conjTranspose : Matrix I I ℂ)) m c
      = V m j * star (V c j) := by
    intro m c
    have h1 : ∀ k, ((V * Matrix.single j j 1 : Matrix I I ℂ)) m k = if k = j then V m j else 0 := by
      intro k
      simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hkj : k = j
      · simp [hkj]
      · simp [hkj, Ne.symm hkj]
    simp only [Matrix.mul_apply, h1, Matrix.conjTranspose_apply]
    by_cases hcj : c = j <;> simp [hcj]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hP, hQ]
  have hnorm : ∑ m, ∑ c, (U m i * star (U c i)) * (V c j * star (V m j))
      = ∑ m, ∑ c, (U m i * star (V m j)) * (star (U c i) * V c j) :=
    Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun c _ => by ring
  rw [hnorm]
  have hsplit : ∀ (f g : I → ℂ), ∑ m, ∑ c, f m * g c = (∑ m, f m) * (∑ c, g c) := by
    intro f g
    calc ∑ m, ∑ c, f m * g c = ∑ m, f m * ∑ c, g c := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
      _ = (∑ m, f m) * (∑ c, g c) := by rw [Finset.sum_mul]
  rw [hsplit]
  have hSc : star (∑ c, star (U c i) * V c j) = ∑ m, U m i * star (V m j) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun m _ => by
      rw [star_mul, star_star]
      ring
  rw [← hSc]
  have h2 : RCLike.re (star (∑ c, star (U c i) * V c j) * ∑ c, star (U c i) * V c j)
      = ‖∑ c, star (U c i) * V c j‖ ^ 2 := by
    have hcc : RCLike.re (star (∑ c, star (U c i) * V c j) * ∑ c, star (U c i) * V c j)
        = Complex.normSq (∑ c, star (U c i) * V c j) := by
      simp only [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self]
      rfl
    rw [hcc, Complex.normSq_eq_norm_sq]
  exact h2

/-- Under support containment, a zero logarithmic inner product forces the two mixed states'
density matrices to coincide. -/
private theorem strict_klein_density {I : Type} [Fintype I] [DecidableEq I]
    (s t : MState I) (hker : t.M.ker ≤ s.M.ker)
    (hD : ⟪s.M, s.M.log - t.M.log⟫ = 0) : s.m = t.m := by
  set a := s.M.H.eigenvalues with ha
  set b := t.M.H.eigenvalues with hb
  set U := s.M.H.eigenvectorUnitary.val with hU
  set V := t.M.H.eigenvectorUnitary.val with hV
  set P := fun i => U * Matrix.single i i 1 * U.conjTranspose with hP
  set Q := fun j => V * Matrix.single j j 1 * V.conjTranspose with hQ
  set X := U.conjTranspose * V with hX
  set w := fun i j => ‖X i j‖ ^ 2 with hw

  have hU1 : U * U.conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp s.M.H.eigenvectorUnitary.property
  have hU2 : U.conjTranspose * U = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp s.M.H.eigenvectorUnitary.property
  have hV1 : V * V.conjTranspose = 1 :=
    Matrix.mem_unitaryGroup_iff.mp t.M.H.eigenvectorUnitary.property
  have hV2 : V.conjTranspose * V = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp t.M.H.eigenvectorUnitary.property
  have hX1 : X * X.conjTranspose = 1 := by
    rw [hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show U.conjTranspose * V * (V.conjTranspose * U)
          = U.conjTranspose * (V * V.conjTranspose) * U from by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hV1, Matrix.mul_one, hU2]
  have hX2 : X.conjTranspose * X = 1 := by
    rw [hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show V.conjTranspose * U * (U.conjTranspose * V)
          = V.conjTranspose * (U * U.conjTranspose) * V from by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc]]
    rw [hU1, Matrix.mul_one, hV2]

  have hAexp : s.M.mat = ∑ i, a i • P i := by
    have h := HermitianMat.cfc_toMat_eq_sum_smul_proj (f := fun x => x) s.M
    rw [HermitianMat.cfc_id'] at h
    exact h
  have hBlog : (t.M.log).mat = ∑ j, Real.log (b j) • Q j := by
    have h := HermitianMat.cfc_toMat_eq_sum_smul_proj (f := Real.log) t.M
    exact h

  have htrace : ∀ i j, RCLike.re ((P i * Q j).trace) = w i j :=
    fun i j => trace_proj_mul_normSq U V i j
  have hre : ∀ (r : ℝ) (z : ℂ), RCLike.re (r • z) = r * RCLike.re z := fun r z => by
    simp [smul_eq_mul, Complex.mul_re, Complex.ofReal_re]
  have hrow : ∀ i, ∑ j, w i j = 1 := fun i => Matrix.unitary_row_sum_norm_sq X hX1 i
  have hcol : ∀ j, ∑ i, w i j = 1 := fun j => Matrix.unitary_col_sum_norm_sq X hX2 j

  have hann : ∀ i, 0 ≤ a i := fun i => s.psd.eigenvalues_nonneg i
  have hbnn : ∀ j, 0 ≤ b j := fun j => t.psd.eigenvalues_nonneg j
  have hasum : ∑ i, a i = 1 := by
    rw [HermitianMat.sum_eigenvalues_eq_trace s.M]
    exact s.tr
  have hbsum : ∑ j, b j = 1 := by
    rw [HermitianMat.sum_eigenvalues_eq_trace t.M]
    exact t.tr

  have hPentry : ∀ (i m l : I), ((P i : Matrix I I ℂ)) m l = U m i * star (U l i) := by
    intro i m l
    have h1 : ∀ k, ((U * Matrix.single i i 1 : Matrix I I ℂ)) m k
        = if k = i then U m i else 0 := by
      intro k
      simp only [Matrix.mul_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
      by_cases hki : k = i
      · simp [hki]
      · simp [hki, Ne.symm hki]
    simp only [hP, Matrix.mul_apply, h1, Matrix.conjTranspose_apply]
    by_cases hli : l = i <;> simp [hli]

  have hkercol : ∀ j, b j = 0 → ∀ i, a i * w i j = 0 := by
    intro j hb i
    have hv : ∀ l, (t.M.H.eigenvectorBasis j : I → ℂ) l = V l j :=
      fun l => (Matrix.IsHermitian.eigenvectorUnitary_apply t.M.H l j)
    have hvin : (t.M.H.eigenvectorBasis j) ∈ t.M.ker := by
      rw [HermitianMat.mem_ker_iff_mulVec_zero, t.M.H.mulVec_eigenvectorBasis,
        show t.M.H.eigenvalues j = 0 from hb, zero_smul]
    have hvinA : (t.M.H.eigenvectorBasis j) ∈ s.M.ker := hker hvin
    have hAv : ∀ c, ∑ l, s.M.mat c l * V l j = 0 := by
      intro c
      have h := (HermitianMat.mem_ker_iff_mulVec_zero s.M _).mp hvinA
      have hc := congrFun h c
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hc
      rw [Finset.sum_congr rfl (fun l _ => by rw [hv l])] at hc
      exact hc
    have hsum : ∑ i, a i * w i j = 0 := by
      have hexp : ∑ i, a i * w i j = RCLike.re ((s.M.mat * Q j).trace) := by
        rw [hAexp]
        have h1 : (∑ i, a i • P i) * Q j = ∑ i, a i • (P i * Q j) := by
          rw [Matrix.sum_mul]
          exact Finset.sum_congr rfl fun i _ => Matrix.smul_mul _ _ _
        rw [h1]
        have h2 : RCLike.re ((∑ i, a i • (P i * Q j)).trace)
            = ∑ i, a i * w i j := by
          simp only [Matrix.trace_sum, Matrix.trace_smul, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hre, htrace i j]
        exact h2.symm
      rw [hexp]
      have hpick : ∀ (M : Matrix I I ℂ) (k : I),
          (M * Matrix.single k k 1).trace = M k k := by
        intro M k
        have h2 : ∀ x x_1, ((M * Matrix.single k k 1 : Matrix I I ℂ)) x x_1
            = if x_1 = k then M x k else 0 := by
          intro x x_1
          by_cases hxk : x_1 = k
          · simp [Matrix.mul_apply, Matrix.single_apply, hxk]
          · simp [Matrix.mul_apply, Matrix.single_apply, hxk, Ne.symm hxk]
        simp only [Matrix.trace, Matrix.diag_apply, h2]
        simp
      have hcyc : (s.M.mat * Q j).trace
          = ((V.conjTranspose * (s.M.mat * V)) * Matrix.single j j 1).trace := by
        rw [hQ]
        have hstep1 : s.M.mat * (V * Matrix.single j j 1 * V.conjTranspose)
            = s.M.mat * V * Matrix.single j j 1 * V.conjTranspose := by
          simp only [← Matrix.mul_assoc]
        have hstep2 : V.conjTranspose * (s.M.mat * V * Matrix.single j j 1)
            = V.conjTranspose * (s.M.mat * V) * Matrix.single j j 1 := by
          simp only [← Matrix.mul_assoc]
        calc (s.M.mat * (V * Matrix.single j j 1 * V.conjTranspose)).trace
            = (s.M.mat * V * Matrix.single j j 1 * V.conjTranspose).trace := by
              rw [hstep1]
          _ = (V.conjTranspose * (s.M.mat * V * Matrix.single j j 1)).trace :=
              Matrix.trace_mul_comm _ _
          _ = ((V.conjTranspose * (s.M.mat * V)) * Matrix.single j j 1).trace := by
              rw [hstep2]
      rw [hcyc, hpick]
      have hentry : (V.conjTranspose * (s.M.mat * V)) j j = 0 := by
        have h1 : ∀ k, (s.M.mat * V) k j = 0 := by
          intro k
          have := hAv k
          simpa [Matrix.mul_apply] using! this
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, h1, mul_zero,
          Finset.sum_const_zero]
      rw [hentry, map_zero]
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hann i) (by positivity))).mp hsum i
      (Finset.mem_univ i)

  have hLA : ⟪s.M, s.M.log⟫ = ∑ i, a i * Real.log (a i) := by
    have h1 : ⟪s.M, s.M.log⟫ = -Sᵥₙ s := by
      rw [Sᵥₙ_eq_neg_trace_log, real_inner_comm, neg_neg]
    rw [h1, Sᵥₙ, Hₛ_eq_sum_negMulLog]
    have hspec : ∀ i, ((s.spectrum i : ℝ)) = a i := fun i => rfl
    simp only [hspec, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  have hLB : ⟪s.M, t.M.log⟫ = ∑ i, ∑ j, a i * w i j * Real.log (b j) := by
    have h : ⟪s.M, t.M.log⟫ = RCLike.re ((s.M.mat * (t.M.log).mat).trace) := rfl
    rw [h, hAexp, hBlog]
    have h1 : (∑ i, a i • P i) * (∑ j, Real.log (b j) • Q j)
        = ∑ i, ∑ j, (a i * Real.log (b j)) • (P i * Q j) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [h1]
    have h2 : (∑ i, ∑ j, (a i * Real.log (b j)) • (P i * Q j)).trace
        = ∑ i, ∑ j, (a i * Real.log (b j)) • (P i * Q j).trace := by
      simp only [Matrix.trace_sum, Matrix.trace_smul]
    rw [h2]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hre, htrace i j]
    ring
  rw [inner_sub_right, hLA, hLB] at hD

  set F := fun i j => a i * w i j * (Real.log (a i) - Real.log (b j))
    - w i j * (a i - b j) with hF
  have hFsum : ∑ i, ∑ j, F i j = 0 := by
    have hS1 : ∑ i, ∑ j, a i * w i j * Real.log (a i) = ∑ i, a i * Real.log (a i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have h : ∑ j, a i * w i j * Real.log (a i)
          = a i * Real.log (a i) * ∑ j, w i j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h, hrow i, mul_one]
    have hS3 : ∑ i, ∑ j, w i j * a i = ∑ i, a i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have h : ∑ j, w i j * a i = a i * ∑ j, w i j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [h, hrow i, mul_one]
    have hS4 : ∑ i, ∑ j, w i j * b j = ∑ j, b j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h : ∑ i, w i j * b j = b j * ∑ i, w i j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h, hcol j, mul_one]
    have hsplit : ∀ i j, F i j = a i * w i j * Real.log (a i)
        - (a i * w i j * Real.log (b j) + (w i j * a i - w i j * b j)) := by
      intro i j
      rw [hF]
      ring
    have hfinal : (∑ i, a i * Real.log (a i))
        - (∑ i, ∑ j, a i * w i j * Real.log (b j))
        - ((∑ i, a i) - (∑ j, b j)) = 0 := by
      rw [hasum, hbsum, sub_self, sub_zero]
      exact hD
    have hstep : ∑ i, ∑ j, F i j = (∑ i, ∑ j, a i * w i j * Real.log (a i))
        - (∑ i, ∑ j, a i * w i j * Real.log (b j) + (∑ i, ∑ j, w i j * a i
          - ∑ i, ∑ j, w i j * b j)) := by
      rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hsplit i j))]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hstep, hS1, hS3, hS4]
    rw [show (∑ i, a i) - ∑ j, b j = (∑ i, a i) - (∑ j, b j) from rfl]
    linarith
  have hFnn : ∀ i j, 0 ≤ F i j := by
    intro i j
    by_cases hb : b j = 0
    · have hz := hkercol j hb i
      show 0 ≤ a i * w i j * (Real.log (a i) - Real.log (b j)) - w i j * (a i - b j)
      have h1 : a i * w i j * (Real.log (a i) - Real.log (b j)) = 0 := by
        rw [hz, zero_mul]
      have h2 : w i j * (a i - b j) = 0 := by
        rw [hb, sub_zero]
        rw [show w i j * a i = a i * w i j from mul_comm _ _]
        exact hz
      rw [h1, h2, sub_zero]
    · by_cases hai : a i = 0
      · show 0 ≤ a i * w i j * (Real.log (a i) - Real.log (b j)) - w i j * (a i - b j)
        have hzero : a i * w i j * (Real.log (a i) - Real.log (b j)) - w i j * (a i - b j)
            = w i j * b j := by
          rw [hai, Real.log_zero]
          ring
        rw [hzero]
        exact mul_nonneg (by positivity) (hbnn j)
      · have hposa : 0 < a i := lt_of_le_of_ne (hann i) (Ne.symm hai)
        have hposb : 0 < b j := lt_of_le_of_ne (hbnn j) (Ne.symm hb)
        have hFeq : F i j = w i j * b j
            * ((a i / b j) * Real.log (a i / b j) - a i / b j + 1) := by
          show a i * w i j * (Real.log (a i) - Real.log (b j)) - w i j * (a i - b j)
            = w i j * b j * ((a i / b j) * Real.log (a i / b j) - a i / b j + 1)
          rw [Real.log_div hposa.ne' hposb.ne']
          field_simp
          ring
        rw [hFeq]
        exact mul_nonneg (mul_nonneg (by positivity) hposb.le)
          (le_aux_log (a i / b j) (div_pos hposa hposb))
  have hstar : ∀ i j, 0 < a i → 0 < w i j → a i = b j := by
    intro i j ha hw
    have hF0 : F i j = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        Finset.sum_nonneg (fun j _ => hFnn i j))).mp hFsum i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hFnn i j)).mp hall j
        (Finset.mem_univ j)
    by_cases hb : b j = 0
    · exact absurd (hkercol j hb i) (ne_of_gt (mul_pos ha hw))
    · by_contra hne
      have hposb : 0 < b j := lt_of_le_of_ne (hbnn j) (Ne.symm hb)
      have hstrict : 0 < F i j := by
        have hFeq : F i j = w i j * b j
            * ((a i / b j) * Real.log (a i / b j) - a i / b j + 1) := by
          show a i * w i j * (Real.log (a i) - Real.log (b j)) - w i j * (a i - b j)
            = w i j * b j * ((a i / b j) * Real.log (a i / b j) - a i / b j + 1)
          rw [Real.log_div ha.ne' hposb.ne']
          field_simp
          ring
        rw [hFeq]
        refine mul_pos (mul_pos (by positivity) hposb) ?_
        refine lt_aux_log (a i / b j) (div_pos ha hposb) ?_
        intro heq
        apply hne
        field_simp at heq
        linarith
      exact absurd hF0 (ne_of_gt hstrict)

  have hpos_case : ∀ i, a i ≠ 0 → ∑ j, b j * w i j = a i := by
    intro i hi
    have hposa : 0 < a i := lt_of_le_of_ne (hann i) (Ne.symm hi)
    have hterm : ∀ j, b j * w i j = a i * w i j := by
      intro j
      by_cases hwj : w i j = 0
      · simp [hwj]
      · have hwm : 0 < w i j := lt_of_le_of_ne (by positivity) (fun h => hwj h.symm)
        rw [hstar i j hposa hwm]
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    have h3 : ∑ j, a i * w i j = a i * ∑ j, w i j := by
      rw [Finset.mul_sum]
    rw [h3, hrow i, mul_one]
  have hgw : ∀ i, ∑ j, b j * w i j = a i := by
    intro i
    by_cases hai : a i = 0
    · have hgsum : ∑ i, (∑ j, b j * w i j - a i) = 0 := by
        rw [Finset.sum_sub_distrib]
        have h1 : ∑ i, ∑ j, b j * w i j = ∑ j, b j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          have h2 : ∑ i, b j * w i j = b j * ∑ i, w i j := by
            rw [Finset.mul_sum]
          rw [h2, hcol j, mul_one]
        rw [h1, hbsum, hasum, sub_self]
      have hgpos : ∀ i, a i = 0 → 0 ≤ ∑ j, b j * w i j - a i := by
        intro i hi
        have h1 : 0 ≤ ∑ j, b j * w i j :=
          Finset.sum_nonneg (fun j _ => mul_nonneg (hbnn j) (by positivity))
        rw [hi, sub_zero]
        exact h1
      have hgzero : ∀ i, a i ≠ 0 → ∑ j, b j * w i j - a i = 0 := by
        intro i hi
        rw [hpos_case i hi, sub_self]
      have hgnonneg : ∀ i, 0 ≤ ∑ j, b j * w i j - a i := by
        intro i
        by_cases hia : a i = 0
        · exact hgpos i hia
        · exact le_of_eq (hgzero i hia).symm
      have hgi : ∑ j, b j * w i j - a i = 0 := by
        by_contra hne
        have hlt : 0 < ∑ j, b j * w i j - a i :=
          lt_of_le_of_ne (hgnonneg i) (fun h => hne h.symm)
        have hgt : 0 < ∑ i, (∑ j, b j * w i j - a i) :=
          Finset.sum_pos' (fun i _ => hgnonneg i) ⟨i, Finset.mem_univ i, hlt⟩
        rw [hgsum] at hgt
        exact absurd hgt (by norm_num)
      rw [hai] at hgi
      linarith
    · exact hpos_case i hai

  have hcoef : ∀ i m, ((b m : ℝ) : ℂ) * star (X i m) = ((a i : ℝ) : ℂ) * star (X i m) := by
    intro i m
    by_cases hwj : w i m = 0
    · have hXm : X i m = 0 := by
        refine norm_eq_zero.mp ?_
        have hp : (‖X i m‖ : ℝ) ^ 2 = 0 := hwj
        have hnn : 0 ≤ ‖X i m‖ := norm_nonneg _
        nlinarith [hp, hnn]
      simp [hXm]
    · have hwm : 0 < w i m := lt_of_le_of_ne (by positivity) (fun h => hwj h.symm)
      by_cases hai : a i = 0
      · have hbw : b m * w i m = 0 := by
          have h1 : ∑ j, b j * w i j = 0 := by
            rw [hgw i, hai]
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun j _ => mul_nonneg (hbnn j) (by positivity))).mp h1 m
            (Finset.mem_univ m)
        have hbm : b m = 0 := by
          rcases eq_or_ne (b m) 0 with h | h
          · exact h
          · exact absurd hbw (by
              have h2 : 0 < b m * w i m :=
                mul_pos (lt_of_le_of_ne (hbnn m) (Ne.symm h)) hwm
              exact ne_of_gt h2)
        rw [hbm, hai]
      · rw [hstar i m (lt_of_le_of_ne (hann i) (Ne.symm hai)) hwm]

  have hBVcol : ∀ m k, ∑ l, t.M.mat k l * V l m = ((b m : ℝ) : ℂ) * V k m := by
    intro m k
    have hv : ∀ l, (t.M.H.eigenvectorBasis m : I → ℂ) l = V l m :=
      fun l => (Matrix.IsHermitian.eigenvectorUnitary_apply t.M.H l m)
    have h := t.M.H.mulVec_eigenvectorBasis m
    have hx : (t.M.H.eigenvectorBasis m : I → ℂ) = fun l => V l m := funext hv
    rw [hx] at h
    have hk := congrFun h k
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hk
    exact hk
  have hUV : U = V * X.conjTranspose := by
    rw [hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [show V * (V.conjTranspose * U) = U from by
        rw [← Matrix.mul_assoc, hV1, one_mul]]
  have hUcol : ∀ (l i : I), U l i = ∑ m, V l m * star (X i m) := by
    intro l i
    rw [hUV]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hBu : ∀ i k, ∑ l, t.M.mat k l * U l i = ((a i : ℝ) : ℂ) * U k i := by
    intro i k
    have hLHS : ∑ l, t.M.mat k l * U l i
        = ∑ m, (((b m : ℝ) : ℂ) * V k m) * star (X i m) := by
      have hstep1 : ∀ l, t.M.mat k l * U l i
          = t.M.mat k l * ∑ m, V l m * star (X i m) := fun l => by rw [hUcol l i]
      rw [Finset.sum_congr rfl (fun l _ => hstep1 l)]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h3 : (∑ x, t.M.mat k x * V x m) * star (X i m)
          = ∑ x, t.M.mat k x * (V x m * star (X i m)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [← h3]
      have h1 : ∑ l, t.M.mat k l * V l m = ((b m : ℝ) : ℂ) * V k m := hBVcol m k
      rw [h1]
    have hRHS : ((a i : ℝ) : ℂ) * U k i
        = ∑ m, (((a i : ℝ) : ℂ) * V k m) * star (X i m) := by
      rw [hUcol k i]
      rw [show ((a i : ℝ) : ℂ) * ∑ m, V k m * star (X i m)
            = ∑ m, ((a i : ℝ) : ℂ) * (V k m * star (X i m)) from
        Finset.mul_sum _ _ _]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hLHS, hRHS]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hc := hcoef i m
    rw [show ((b m : ℝ) : ℂ) * V k m * star (X i m)
            = ((b m : ℝ) : ℂ) * star (X i m) * V k m from by ring,
      show ((a i : ℝ) : ℂ) * V k m * star (X i m)
            = ((a i : ℝ) : ℂ) * star (X i m) * V k m from by ring,
      hc]

  have hPsum : ∑ i, P i = (1 : Matrix I I ℂ) := by
    have h2 : (∑ i, Matrix.single i i (1 : ℂ)) = (1 : Matrix I I ℂ) := by
      ext m l
      have hentry : ∀ i, Matrix.single i i (1 : ℂ) m l = if i = m ∧ i = l then 1 else 0 := by
        intro i
        simp [Matrix.single_apply]
      simp only [Matrix.sum_apply, hentry]
      by_cases hml : m = l
      · simp [hml, Matrix.one_apply]
      · simp [hml, Ne.symm hml, Matrix.one_apply]
    calc ∑ i, P i = U * (∑ i, Matrix.single i i 1) * U.conjTranspose := by
          rw [Matrix.mul_sum, Matrix.sum_mul]
      _ = U * 1 * U.conjTranspose := by rw [h2]
      _ = 1 := by rw [Matrix.mul_one, hU1]
  have hBP : ∀ i m l, (t.M.mat * P i) m l = (a i : ℝ) * P i m l := by
    intro i m l
    have h1 : ∀ c, P i c l = U c i * star (U l i) := fun c => hPentry i c l
    have h2 : ∑ c, t.M.mat m c * P i c l
        = star (U l i) * ∑ c, t.M.mat m c * U c i := by
      simp only [h1]
      rw [show (∑ c, t.M.mat m c * (U c i * star (U l i)))
            = star (U l i) * ∑ c, t.M.mat m c * U c i from by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring]
    show ∑ c, t.M.mat m c * P i c l = (a i : ℝ) * P i m l
    rw [h2, hBu i m, h1 m]
    ring
  have hBexp : t.M.mat = ∑ i, a i • P i := by
    ext m l
    have hentry : t.M.mat m l = ∑ i, (t.M.mat * P i) m l := by
      have heq : t.M.mat * (∑ i, P i) = ∑ i, t.M.mat * P i := Matrix.mul_sum _ _ _
      calc t.M.mat m l = (t.M.mat * (∑ i, P i)) m l := by
            rw [hPsum, Matrix.mul_one]
        _ = (∑ i, t.M.mat * P i) m l := by rw [heq]
        _ = ∑ i, (t.M.mat * P i) m l := by
            exact Matrix.sum_apply m l _ _
    rw [hentry]
    rw [show (∑ i, a i • P i) m l = ∑ i, a i * P i m l from by
        rw [Matrix.sum_apply]
        exact Finset.sum_congr rfl fun i _ => rfl]
    exact Finset.sum_congr rfl fun i _ => hBP i m l
  show s.M.mat = t.M.mat
  rw [hAexp, hBexp]

/-- A vector lies in the kernel of a classical mixed state exactly when each probability times
the corresponding vector coordinate is zero. -/
private theorem mem_ker_ofClassical_iff {I : Type} [Fintype I] [DecidableEq I]
    (q : ProbDistribution I) (x : EuclideanSpace ℂ I) :
    x ∈ (MState.ofClassical q).M.ker ↔ ∀ i, ((q i : ℝ) : ℂ) * x i = 0 := by
  rw [HermitianMat.mem_ker_iff_mulVec_zero]
  constructor
  · intro hx i
    have hc := congrFun hx i
    simp only [Pi.zero_apply, MState.coe_ofClassical, HermitianMat.diagonal_mat,
      Matrix.mulVec_diagonal] at hc
    exact hc
  · intro hx
    funext i
    simp only [Pi.zero_apply, MState.coe_ofClassical, HermitianMat.diagonal_mat,
      Matrix.mulVec_diagonal]
    exact hx i

/-- Classical support containment implies the corresponding reverse inclusion of mixed-state
kernels. -/
private theorem ker_ofClassical_le_of_support {I : Type} [Fintype I] [DecidableEq I]
    (p q : ProbDistribution I) (h : ∀ i, (q i : ℝ) = 0 → (p i : ℝ) = 0) :
    (MState.ofClassical q).M.ker ≤ (MState.ofClassical p).M.ker := by
  intro x hx
  rw [mem_ker_ofClassical_iff] at hx ⊢
  intro i
  by_cases hqi : (q i : ℝ) = 0
  · rw [h i hqi]
    simp
  · have hc : x i = 0 := by
      by_contra hxi
      have hprod := hx i
      rw [mul_eq_zero] at hprod
      rcases hprod with h0 | h0
      · exact hqi (Complex.ofReal_eq_zero.mp h0)
      · exact hxi h0
    rw [hc, mul_zero]

/-- Failure of classical support containment prevents the corresponding reverse kernel
inclusion. -/
private theorem not_ker_ofClassical {I : Type} [Fintype I] [DecidableEq I]
    (p q : ProbDistribution I) (h : ¬ ∀ i, (q i : ℝ) = 0 → (p i : ℝ) = 0) :
    ¬ ((MState.ofClassical q).M.ker ≤ (MState.ofClassical p).M.ker) := by
  intro hker
  obtain ⟨i, hi⟩ := not_forall.mp h
  push_neg at hi
  have hmem : (EuclideanSpace.single i (1 : ℂ)) ∈ (MState.ofClassical q).M.ker := by
    rw [mem_ker_ofClassical_iff]
    intro k
    rw [PiLp.single_apply]
    by_cases hki : k = i
    · rw [if_pos hki, hki, hi.1]
      simp
    · rw [if_neg hki, mul_zero]
  have hmem2 := hker hmem
  rw [mem_ker_ofClassical_iff] at hmem2
  have hval := hmem2 i
  simp only [PiLp.single_apply, mul_one, if_true, Complex.ofReal_eq_zero,
    if_true] at hval
  exact hi.2 hval

/-- Under classical support containment, the logarithmic operator inner product equals the sum
of `p i * (log (p i) - log (q i))`. -/
private theorem inner_log_ofClassical {I : Type} [Fintype I] [DecidableEq I]
    (p q : ProbDistribution I) (h : ∀ i, (q i : ℝ) = 0 → (p i : ℝ) = 0) :
    ⟪(MState.ofClassical p).M, (MState.ofClassical p).M.log - (MState.ofClassical q).M.log⟫
      = ∑ i, (p i : ℝ) * (Real.log (p i : ℝ) - Real.log (q i : ℝ)) := by
  have hlog : ∀ d : ProbDistribution I, (MState.ofClassical d).M.log.mat
      = Matrix.diagonal (fun i => ((Real.log (d i : ℝ) : ℝ) : ℂ)) := by
    intro d
    show ((MState.ofClassical d).M.cfc Real.log).mat = _
    rw [show (MState.ofClassical d).M = HermitianMat.diagonal ℂ (fun i => (d i : ℝ)) from
        MState.coe_ofClassical d, HermitianMat.cfc_diagonal]
    rfl
  have hsub : ((MState.ofClassical p).M.log - (MState.ofClassical q).M.log).mat
      = Matrix.diagonal (fun i => ((Real.log (p i : ℝ) - Real.log (q i : ℝ) : ℝ) : ℂ)) := by
    rw [show ((MState.ofClassical p).M.log - (MState.ofClassical q).M.log).mat
          = (MState.ofClassical p).M.log.mat - (MState.ofClassical q).M.log.mat from rfl,
      hlog, hlog]
    ext a b
    by_cases hab : a = b
    · simp [Matrix.diagonal_apply, Matrix.sub_apply, hab]
    · simp [Matrix.diagonal_apply, Matrix.sub_apply, hab, Ne.symm hab]
  have hpd : ((MState.ofClassical p).M).mat
      = Matrix.diagonal (fun i => (((p i : ℝ)) : ℂ)) := rfl
  rw [HermitianMat.inner_eq_re_trace, hpd, hsub, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, map_sum]
  simp [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_re, Complex.mul_re,
    mul_comm]

set_option maxHeartbeats 2000000 in

/-- Characterize finite relative entropy by support containment and prove its trace-log formula
and zero-equality criterion. Also record simultaneous unitary invariance, product
additivity, and the extended classical relative-entropy formula; see [Watrous2018]. -/
theorem relative_entropy_density_bridge :
  (∀ (I : Type) [Fintype I] [DecidableEq I] (ρ σ : Density I),
    (relative ρ σ ≠ ⊤ ↔ (state σ).M.ker ≤ (state ρ).M.ker) ∧
    (¬ (state σ).M.ker ≤ (state ρ).M.ker → relative ρ σ = ⊤) ∧
    ((state σ).M.ker ≤ (state ρ).M.ker →
      0 ≤ logTrace ρ σ ∧ relative ρ σ = ENNReal.ofReal (logTrace ρ σ)) ∧
    (relative ρ σ = 0 ↔ ρ = σ)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (ρ σ : Density I)
    (U : Matrix.unitaryGroup I ℂ),
    relative (localState ((state ρ).uConj U)) (localState ((state σ).uConj U)) =
      relative ρ σ) ∧
  (∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ₁ σ₁ : Density I) (ρ₂ σ₂ : Density J),
    relative (localState ((state ρ₁).prod (state ρ₂)))
      (localState ((state σ₁).prod (state σ₂))) = relative ρ₁ σ₁ + relative ρ₂ σ₂) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (p q : ProbDistribution I),
    qRelativeEnt (MState.ofClassical p) (MState.ofClassical q) =
      if ∀ i, (q i : ℝ) = 0 → (p i : ℝ) = 0 then
        ENNReal.ofReal (∑ i, (p i : ℝ) * (Real.log (p i : ℝ) - Real.log (q i : ℝ)))
      else ⊤) := by
  refine ⟨fun I _ _ ρ σ => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · by_cases h : (state σ).M.ker ≤ (state ρ).M.ker
    · refine ⟨fun _ => h, fun _ => ?_⟩
      show qRelativeEnt (state ρ) (state σ) ≠ ⊤
      rw [qRelativeEnt_of_ker _ _ h]
      exact ENNReal.ofReal_ne_top
    · refine ⟨fun hne => ?_, fun hk => absurd hk h⟩
      by_contra hk
      exact hne (show relative ρ σ = ⊤ by
        show qRelativeEnt (state ρ) (state σ) = ⊤
        simp [qRelativeEnt, SandwichedRelRentropy, hk])
  · intro h
    show qRelativeEnt (state ρ) (state σ) = ⊤
    simp [qRelativeEnt, SandwichedRelRentropy, h]
  · intro h
    have hval := qRelativeEnt_of_ker (state ρ) (state σ) h
    rw [← logTrace_eq_inner] at hval
    refine ⟨inner_log_sub_log_nonneg h, hval⟩
  · constructor
    · intro h0
      apply Subtype.ext
      have hker : (state σ).M.ker ≤ (state ρ).M.ker := by
        by_contra hk
        exact absurd (show qRelativeEnt (state ρ) (state σ) = ⊤ by
          simp [qRelativeEnt, SandwichedRelRentropy, hk])
          (fun htop => ENNReal.zero_ne_top (h0.symm.trans htop))
      have hinner : ⟪(state ρ).M, (state ρ).M.log - (state σ).M.log⟫ = 0 := by
        have hval := qRelativeEnt_of_ker (state ρ) (state σ) hker
        have h0' : qRelativeEnt (state ρ) (state σ) = 0 := h0
        rw [h0'] at hval
        exact le_antisymm (ENNReal.ofReal_eq_zero.mp hval.symm)
          (inner_log_sub_log_nonneg hker)
      have hm : (state ρ).m = (state σ).m :=
        strict_klein_density (state ρ) (state σ) hker hinner
      simpa using hm
    · intro hσρ
      subst hσρ
      show qRelativeEnt (state ρ) (state ρ) = 0
      exact qRelEntropy_self _
  · intro I _ _ ρ σ U
    show qRelativeEnt ((state ρ).uConj U) ((state σ).uConj U) =
      qRelativeEnt (state ρ) (state σ)
    exact sandwichedRenyiEntropy_conj_unitary zero_lt_one _ _ U
  · intro I _ _ J _ _ ρ₁ σ₁ ρ₂ σ₂
    show qRelativeEnt ((state ρ₁).prod (state ρ₂)) ((state σ₁).prod (state σ₂)) =
      qRelativeEnt (state ρ₁) (state σ₁) + qRelativeEnt (state ρ₂) (state σ₂)
    exact qRelativeEnt_additive _ _ _ _
  · intro I _ _ p q
    by_cases h : ∀ i, (q i : ℝ) = 0 → (p i : ℝ) = 0
    · rw [if_pos h]
      have hker := ker_ofClassical_le_of_support p q h
      rw [qRelativeEnt_of_ker _ _ hker, inner_log_ofClassical p q h]
    · rw [if_neg h]
      have hk := not_ker_ofClassical p q h
      show qRelativeEnt (MState.ofClassical p) (MState.ofClassical q) = ⊤
      rw [qRelativeEnt, SandwichedRelRentropy]
      rw [dif_pos zero_lt_one]
      exact dif_neg hk

/-- Transfer channel data processing, strong subadditivity, conditional entropy, and
coherent-information identities to the density-matrix bridge. For a nonsingular reference
state, also identify the finite nonnegative relative-entropy loss under partial trace with
the corresponding trace-log difference. -/
theorem dpi_ssa_partial_trace_consumers :
  (∀ (D E : ℕ) (T : QuantumChannel D E) (ρ σ : Density (Fin D)),
    let Φ := Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T
    (Φ (state ρ)).m = T.map ρ.val ∧
    qRelativeEnt (Φ (state ρ)) (Φ (state σ)) ≤ relative ρ σ) ∧
  (∀ (A B C : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] (ρ : Density (A × B × C)),
    let s := state ρ
    Sᵥₙ s + Sᵥₙ s.traceLeft.traceRight ≤ Sᵥₙ s.assoc'.traceRight + Sᵥₙ s.traceLeft) ∧
  (∀ (A B C D : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (ρ σ : Density ((A × B) × (C × D))),
    (state σ).M.NonSingular →
    let ρc := localState (state ρ).traceLeft
    let σc := localState (state σ).traceLeft
    relative ρ σ ≠ ⊤ ∧ relative ρc σc ≠ ⊤ ∧
    0 ≤ (relative ρ σ).toReal - (relative ρc σc).toReal ∧
    (relative ρ σ).toReal - (relative ρc σc).toReal = logTrace ρ σ - logTrace ρc σc) ∧
  (∀ (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Density (A × B)),
    let σ := localState (state ρ).traceLeft
    σ.val = Matrix.traceLeft ρ.val ∧ qConditionalEnt (state ρ) = entropy ρ - entropy σ) ∧
  (∀ (D E : ℕ) (ρ : Density (Fin D)) (T : QuantumChannel D E),
    let ω := (Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T).prod (CPTPMap.id (dIn := Fin D))
      (MState.pure (state ρ).purify)
    coherentInfo (state ρ) (Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T) = Sᵥₙ ω.traceLeft - Sᵥₙ ω) := by
  refine ⟨fun D E T ρ σ => ⟨?_, ?_⟩, fun A B C _ _ _ _ _ _ ρ =>
    Sᵥₙ_strong_subadditivity (state ρ), ?_, ?_, ?_⟩
  · show (Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T (state ρ)).m = T.map ρ.val
    rw [CPTPMap.mat_coe_eq_apply_mat]
    simp
  · exact sandwichedRenyiEntropy_DPI_eq_one (state ρ) (state σ)
      (Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T)
  · intro A B C D _ _ _ _ _ _ _ _ ρ σ hσ
    have hPD : (state σ).M.mat.PosDef :=
      (HermitianMat.nonSingular_iff_posDef_of_PSD (state σ).nonneg).mp hσ
    have hneAB : Nonempty (A × B) := (nonempty_prod.mp (state σ).nonempty).1
    have hPDc : (state σ).traceLeft.M.mat.PosDef :=
      PosDef_traceLeft (dA := A × B) (dB := C × D) (state σ).M hPD
    haveI : (state σ).traceLeft.M.NonSingular := HermitianMat.nonSingular_of_posDef hPDc
    have hker1 : (state σ).M.ker ≤ (state ρ).M.ker := by
      rw [HermitianMat.nonSingular_ker_bot]
      exact bot_le
    have hker2 : (state σ).traceLeft.M.ker ≤ (state ρ).traceLeft.M.ker := by
      rw [HermitianMat.nonSingular_ker_bot]
      exact bot_le
    have hdpi := sandwichedRenyiEntropy_DPI_eq_one (state ρ) (state σ)
      (CPTPMap.traceLeft (d₁ := A × B) (d₂ := C × D))
    simp only [CPTPMap.traceLeft_eq_MState_traceLeft] at hdpi
    have hval1 : relative ρ σ = ENNReal.ofReal (logTrace ρ σ) :=
      qRelativeEnt_of_ker _ _ hker1
    have hval2 : relative (localState (state ρ).traceLeft) (localState (state σ).traceLeft)
        = ENNReal.ofReal (logTrace (localState (state ρ).traceLeft)
          (localState (state σ).traceLeft)) := by
      show qRelativeEnt ((state ρ).traceLeft) ((state σ).traceLeft) = _
      exact qRelativeEnt_of_ker _ _ hker2
    have hle : qRelativeEnt ((state ρ).traceLeft) ((state σ).traceLeft) ≤ relative ρ σ :=
      hdpi
    have hfin1 : relative ρ σ ≠ ⊤ := by
      rw [hval1]; exact ENNReal.ofReal_ne_top
    have hfin2 : qRelativeEnt ((state ρ).traceLeft) ((state σ).traceLeft) ≠ ⊤ :=
      qRelativeEnt_ne_top
    refine ⟨hfin1, hfin2, ?_, ?_⟩
    · have h3 := (ENNReal.toReal_le_toReal hfin2 hfin1).mpr hle
      have h5 : (relative (localState (state ρ).traceLeft)
          (localState (state σ).traceLeft)).toReal
          = (qRelativeEnt ((state ρ).traceLeft) ((state σ).traceLeft)).toReal := by
        show ((qRelativeEnt ((state ρ).traceLeft)
          ((state σ).traceLeft) : ENNReal)).toReal = _
        rfl
      show 0 ≤ (relative ρ σ).toReal
        - (relative (localState (state ρ).traceLeft)
          (localState (state σ).traceLeft)).toReal
      rw [h5]
      linarith
    · have hn1 : 0 ≤ logTrace ρ σ := by
        rw [logTrace_eq_inner]
        exact inner_log_sub_log_nonneg hker1
      have hn2 : 0 ≤ logTrace (localState (state ρ).traceLeft)
          (localState (state σ).traceLeft) := by
        rw [logTrace_eq_inner]
        show 0 ≤ ⟪(state ρ).traceLeft.M, (state ρ).traceLeft.M.log
          - (state σ).traceLeft.M.log⟫
        exact inner_log_sub_log_nonneg hker2
      show (relative ρ σ).toReal - (relative (localState (state ρ).traceLeft)
          (localState (state σ).traceLeft)).toReal
        = logTrace ρ σ - logTrace (localState (state ρ).traceLeft)
          (localState (state σ).traceLeft)
      rw [hval1, hval2, ENNReal.toReal_ofReal hn1, ENNReal.toReal_ofReal hn2]
  · intro A B _ _ _ _ ρ
    constructor
    · show ((state ρ).traceLeft).m = Matrix.traceLeft ρ.val
      rfl
    · show qConditionalEnt (state ρ) = Sᵥₙ (state ρ) - Sᵥₙ ((state ρ).traceLeft)
      rfl
  · intro D E ρ T
    show coherentInfo (state ρ) (Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T) =
      Sᵥₙ ((Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T).prod (CPTPMap.id (dIn := Fin D))
        (MState.pure (state ρ).purify)).traceLeft
      - Sᵥₙ ((Qatlib.Concepts.ChannelTheory.Stinespring.toPhyslib T).prod (CPTPMap.id (dIn := Fin D))
        (MState.pure (state ρ).purify))
    simp only [coherentInfo, qConditionalEnt]
    ring_nf
