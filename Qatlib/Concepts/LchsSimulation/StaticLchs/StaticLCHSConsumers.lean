/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.StaticNoncommutingLCHS
import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Postselected static LCHS outputs and finite windows

`staticLchsDataBranch` extracts the selected label branch, and `staticLchsOutputDensity` forms
its norm-normalized outer product. Prepared amplification preserves the density of every
positive-success branch. Operator and quadrature error bounds imply a trace norm error of `4 * ε
/ τ`, while the finite iteration mixture has success at least `1 / 8` and explicit access
budgets.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `static_lchs_same_postselected_solution_state`: bounds the postselected solution density
  error.
* `static_lchs_finite_window_success_and_preparation_budget`: gives the finite-window success
  and access bounds.

## References

* [An et al., 2023][AnLiuLin2023]
-/

open Qatlib.Foundations.PureStateMath.Reflection
set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 200000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.LchsSimulation.StaticLchs
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The data vector obtained by restricting a joint label-and-data state to the label `j₀`. -/
noncomputable def staticLchsDataBranch {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
    (j₀ : Fin N) (y : QState (Fin N × I)) : QState I := fun i => y (j₀,i)

/-- The outer product of a vector scaled by the inverse of its Euclidean norm, yielding zero
when the vector is zero. -/
noncomputable def staticLchsOutputDensity {I : Type} [Fintype I] [DecidableEq I] (v : QState I) :=
  outerProduct (((‖toEuclidean_fromVec v‖⁻¹ : ℝ) : ℂ) • v)

/-- The iteration window `max 1 (Nat.ceil (2 * α / τ))`. -/
noncomputable def staticLchsWindow (α τ : ℝ) : ℕ := max 1 (Nat.ceil (2*α/τ))

/-- The iteration weight given by half the uniform mass on `Fin m` plus an additional half mass
at iteration zero. -/
noncomputable def staticLchsIterationWeight (m : ℕ) (j : Fin m) : ℝ :=
  1/(2*(m:ℝ)) + if j.val = 0 then 1/2 else 0

/-- For positive `m`, the iteration weights are nonnegative and sum to one. -/
theorem static_lchs_iteration_weight_distribution (m : ℕ) (hm : 0 < m) :
    (∀ j : Fin m, 0 ≤ staticLchsIterationWeight m j) ∧
      (∑ j : Fin m, staticLchsIterationWeight m j) = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro j
    unfold staticLchsIterationWeight
    split_ifs <;> positivity
  · simp only [staticLchsIterationWeight, Finset.sum_add_distrib]
    have hdelta : (∑ j : Fin m, if j.val = 0 then (1/2 : ℝ) else 0) = 1/2 := by
      have he (j : Fin m) : j.val = 0 ↔ j = ⟨0, hm⟩ := by
        constructor
        · intro hj; exact Fin.ext hj
        · intro hj; simp [hj]
      simp only [he]
      simp
    rw [hdelta]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

/-- For positive `α` and `τ`, the static LCHS window is positive and at most `2 * α / τ + 1`. -/
theorem static_lchs_window_bound (α τ : ℝ) (hα : 0 < α) (hτ : 0 < τ) :
    0 < staticLchsWindow α τ ∧ (staticLchsWindow α τ : ℝ) ≤ 2*α/τ+1 := by
  have hp : 0 < 2*α/τ := by positivity
  refine ⟨lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), ?_⟩
  simp only [staticLchsWindow, Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (Nat.ceil_lt_add_one hp.le).le

/-- Every iteration index in `Fin m` gives at most `2 * m + 1` input accesses and at most `2 * m
+ 1` selection accesses in the compiled static LCHS word. -/
theorem static_lchs_window_actual_access_budget
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) (m : ℕ) (j : Fin m) :
    (staticLchsWord j.val).count .inputF + (staticLchsWord j.val).count .inputB ≤ 2*m+1 ∧
      (staticLchsWord j.val).count .selectF + (staticLchsWord j.val).count .selectB ≤ 2*m+1 := by
  obtain ⟨_, _, hsf, hsb, hif, hib, _, _, _, _⟩ :=
    static_lchs_actual_expanded_prepare_select_amplification I N c V B j₀ i₀ j.val hα hV hB
  rw [hif, hib, hsf, hsb]
  constructor <;> omega

/-- The selected data branch at iteration zero equals the coefficient-mass-normalized linear
combination of the unitary nodes applied to the prepared input. -/
theorem static_lchs_actual_initial_data_branch
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) :
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    staticLchsDataBranch j₀
      (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) =
      (∑ j, (c j / (coefficientMass c : ℂ)) • V j) *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀) := by
  (try dsimp only)
  let U := coefficientLCUUnitary c V j₀
  have hr := (static_lchs_actual_expanded_prepare_select_amplification
    I N c V B j₀ i₀ 0 hα hV hB).2.1
  rw [hr]
  simp only [preparedAACircuit, RepeatCircuit, List.append_nil, run_gate, run_nil]
  have hc (x y : I) :
      compress (prepareLift (I := I) (Qatlib.Foundations.PureStateMath.Ket j₀)) (coefficientLCUUnitary c V j₀)
        (prepareLift (I := I) (Qatlib.Foundations.PureStateMath.Ket j₀)) x y =
        U (j₀,x) (j₀,y) := by
    dsimp only [U]
    simp [compress, Matrix.mul_apply, Matrix.conjTranspose_apply, prepareLift,
      Qatlib.Foundations.PureStateMath.Ket, Fintype.sum_prod_type, ite_mul, apply_ite]
  have ht : ApplyGate (TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) B) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀)) =
      TensorState (Qatlib.Foundations.PureStateMath.Ket j₀) (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀) := by
    rw [← tensorState_ket_ket, applyGate_tensorGate]
    simp only [ApplyGate, Matrix.one_mulVec]
  change staticLchsDataBranch j₀
      (ApplyGate (U * _) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) = _
  rw [applyGate_mul, ht]
  rw [← coefficientLCUUnitary_compress c V j₀ hα]
  ext x
  simp only [staticLchsDataBranch, ApplyGate, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, TensorState, Qatlib.Foundations.PureStateMath.Ket, ite_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hc]
  simp only [one_mul, zero_mul, mul_zero]
  simp_rw [Finset.sum_ite_irrel]
  simp

/-- The joint-state probability of a selected label equals the total Born mass of its extracted
data branch. -/
theorem static_lchs_label_probability {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
    (j₀ : Fin N) (y : QState (Fin N × I)) :
    MeasureProb y (Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)) =
      MeasureProb (staticLchsDataBranch j₀ y) Finset.univ := by
  simp only [MeasureProb, BornProb, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [staticLchsDataBranch]
  rw [Finset.sum_comm]
  simp

/-- Every amplification iterate of the prepared state lies in the span of its initial marked and
unmarked components. -/
private theorem staticLchs_prepared_span {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (x₀ : J) (S : Finset J) (hA : A ∈ unitaryGroup J ℂ) (k : ℕ) :
    ∃ a b : ℂ, ApplyGate ((preparedAAIterate A x₀ S)^k) (preparedAAState A x₀) =
      a • (preparedAAState A x₀ - Collapse (preparedAAState A x₀) S) +
        b • Collapse (preparedAAState A x₀) S := by
  let p := MeasureProb (preparedAAState A x₀) S
  induction k with
  | zero =>
    refine ⟨1, 1, ?_⟩
    simp [ApplyGate]
  | succ k ih =>
    obtain ⟨a, b, hab⟩ := ih
    obtain ⟨hbad, hgood⟩ := prepared_aa_two_component_step A x₀ S hA
    refine ⟨a * ((1-2*p : ℝ) : ℂ) + b * ((-2*p : ℝ) : ℂ),
      a * ((2*(1-p) : ℝ) : ℂ) + b * ((1-2*p : ℝ) : ℂ), ?_⟩
    rw [pow_succ', applyGate_mul, hab]
    simp only [ApplyGate, Matrix.mulVec_add, Matrix.mulVec_smul] at hbad hgood ⊢
    rw [hbad, hgood]
    dsimp only [p]
    module

/-- The selected data branch after any number of compiled amplification iterations is a scalar
multiple of its iteration-zero branch. -/
theorem static_lchs_actual_data_branch_collinear
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I) (k : ℕ)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) :
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    ∃ b : ℂ, staticLchsDataBranch j₀
      (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ k) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) =
      b • staticLchsDataBranch j₀
        (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) := by
  (try dsimp only)
  let A := coefficientLCUUnitary c V j₀ * TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) B
  let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
  have hA : A ∈ unitaryGroup (Fin N × I) ℂ :=
    (unitaryGroup _ ℂ).mul_mem (coefficientLCUUnitary_unitary c V j₀ hα hV)
      (tensorGate_unitary (unitaryGroup (Fin N) ℂ).one_mem hB)
  have hk := (static_lchs_actual_expanded_prepare_select_amplification
    I N c V B j₀ i₀ k hα hV hB).2.1
  have h0 := (static_lchs_actual_expanded_prepare_select_amplification
    I N c V B j₀ i₀ 0 hα hV hB).2.1
  rw [hk, h0]
  change ∃ b : ℂ, staticLchsDataBranch j₀
    (Run (preparedMark S) (preparedAACircuit A (j₀,i₀) k) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) =
    b • staticLchsDataBranch j₀
      (Run (preparedMark S) (preparedAACircuit A (j₀,i₀) 0) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀)))
  rw [(prepared_aa_actual_circuit A (j₀,i₀) S k hA).2.2.2]
  simp only [preparedAACircuit, RepeatCircuit, List.append_nil, run_gate, run_nil]
  obtain ⟨a, b, hab⟩ := staticLchs_prepared_span A (j₀,i₀) S hA k
  rw [applyGate_mul, hab]
  refine ⟨b, ?_⟩
  ext i
  simp [staticLchsDataBranch, collapse_apply, S, preparedAAState, A, applyGate_mul]

/-- Multiplying a vector by a nonzero complex scalar leaves its norm-normalized output density
unchanged. -/
theorem static_lchs_output_density_smul {I : Type} [Fintype I] [DecidableEq I]
    (v : QState I) (b : ℂ) (hb : b ≠ 0) :
    staticLchsOutputDensity (b • v) = staticLchsOutputDensity v := by
  have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hs : ‖toEuclidean_fromVec (b • v)‖ = ‖b‖ * ‖toEuclidean_fromVec v‖ := by
    rw [toEuclidean_fromVec, WithLp.toLp_smul, norm_smul]
    rfl
  have hbb : b * star b = ((‖b‖^2 : ℝ) : ℂ) := by
    simpa [Complex.normSq_eq_norm_sq] using! Complex.mul_conj b
  ext i j
  simp only [staticLchsOutputDensity, hs, outerProduct, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul, _root_.mul_inv_rev, Complex.ofReal_mul,
    map_mul, Complex.conj_ofReal]
  have hnC : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  have hbb' : b * (starRingEnd ℂ) b = (‖b‖ : ℂ)^2 := by exact_mod_cast hbb
  simp only [Complex.ofReal_inv]
  calc
    _ = ((‖b‖ : ℂ)⁻¹)^2 * (b * (starRingEnd ℂ) b) *
        ((‖toEuclidean_fromVec v‖ : ℂ)⁻¹ * v i *
          ((‖toEuclidean_fromVec v‖ : ℂ)⁻¹ * (starRingEnd ℂ) (v j))) := by ring
    _ = _ := by rw [hbb']; field_simp

/-- Every positive-success compiled amplification output has the same selected data density as
the normalized linear combination of the unitary nodes acting on the prepared input. -/
theorem static_lchs_actual_postselected_density_invariant
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I) (k : ℕ)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) :
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    let y :=
        Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ k)
        (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))
    0 < MeasureProb y S →
    staticLchsOutputDensity (staticLchsDataBranch j₀ y) =
      staticLchsOutputDensity ((∑ j, (c j / (coefficientMass c : ℂ)) • V j) *ᵥ
        (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀)) := by
  (try dsimp only)
  intro hp
  obtain ⟨b, hb⟩ := static_lchs_actual_data_branch_collinear
    I N c V B j₀ i₀ k hα hV hB
  have hb0 : b ≠ 0 := by
    intro hz
    rw [static_lchs_label_probability, hb, hz, zero_smul] at hp
    simp [MeasureProb, BornProb] at hp
  rw [hb, static_lchs_output_density_smul _ b hb0,
    static_lchs_actual_initial_data_branch I N c V B j₀ i₀ hα hV hB]

/-- An expectation under the iteration weights is half the uniform average plus half the value
at iteration zero. -/
private theorem staticLchs_mixture (m : ℕ) (hm : 0 < m) (f : Fin m → ℝ) :
    (∑ j : Fin m, staticLchsIterationWeight m j * f j) =
      (∑ j : Fin m, f j) / (2*(m:ℝ)) + f ⟨0, hm⟩ / 2 := by
  simp only [staticLchsIterationWeight, add_mul, Finset.sum_add_distrib]
  have hd : (∑ j : Fin m, (if j.val = 0 then (1/2 : ℝ) else 0) * f j) =
      f ⟨0, hm⟩ / 2 := by
    have he (j : Fin m) : j.val = 0 ↔ j = ⟨0, hm⟩ := by
      constructor
      · intro hj; exact Fin.ext hj
      · intro hj; simp [hj]
    simp only [he, ite_mul, zero_mul]
    simp [div_eq_mul_inv, mul_comm]
  rw [hd, ← Finset.mul_sum]
  ring

/-- If the initial success amplitude is at least `τ / (2 * α)`, the prescribed prepared
amplification window has weighted success at least `1 / 8`. -/
private theorem staticLchs_prepared_window_success {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix J J ℂ) (x₀ : J) (S : Finset J) (α τ : ℝ)
    (hA : A ∈ unitaryGroup J ℂ) (hα : 0 < α) (hτ : 0 < τ)
    (hroot : τ/(2*α) ≤ Real.sqrt (MeasureProb (preparedAAState A x₀) S)) :
    (1/8 : ℝ) ≤ ∑ j : Fin (staticLchsWindow α τ),
      staticLchsIterationWeight (staticLchsWindow α τ) j *
        MeasureProb (Run (preparedMark S) (preparedAACircuit A x₀ j.val) (Qatlib.Foundations.PureStateMath.Ket x₀)) S := by
  let m := staticLchsWindow α τ
  have hm : 0 < m := (static_lchs_window_bound α τ hα hτ).1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let a := MeasureProb (preparedAAState A x₀) S
  let f := fun j : Fin m =>
    MeasureProb (Run (preparedMark S) (preparedAACircuit A x₀ j.val) (Qatlib.Foundations.PureStateMath.Ket x₀)) S
  have ha0 : 0 ≤ a := measureProb_nonneg _ _
  have hf0 : 0 ≤ ∑ j, f j := Finset.sum_nonneg (fun j _ => measureProb_nonneg _ _)
  have hfzero : f ⟨0, hm⟩ = a := by
    simp [f, a, preparedAACircuit, RepeatCircuit, preparedAAState]
  change (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j * f j
  rw [staticLchs_mixture m hm f, hfzero]
  by_cases ha : 1/2 ≤ a
  · have hnonneg : 0 ≤ (∑ j, f j)/(2*(m:ℝ)) := div_nonneg hf0 (by positivity)
    linarith
  · have ha1 : a < 1/2 := lt_of_not_ge ha
    have hratio : 0 < τ/(2*α) := by positivity
    have haPos : 0 < a := Real.sqrt_pos.mp (lt_of_lt_of_le hratio hroot)
    let θ := Real.arcsin (Real.sqrt a)
    have hθ0 : 0 < θ := Real.arcsin_pos.mpr (Real.sqrt_pos.mpr haPos)
    have hroot1 : Real.sqrt a < 1 := by
      simpa only [Real.sqrt_one] using! Real.sqrt_lt_sqrt ha0 (show a < 1 by linarith)
    have hθ1 : θ < Real.pi/2 := Real.arcsin_lt_pi_div_two.mpr hroot1
    have hsin : Real.sin θ = Real.sqrt a :=
      Real.sin_arcsin (by linarith [Real.sqrt_nonneg a]) hroot1.le
    have hprob : a = (Real.sin θ)^2 := by rw [hsin, Real.sq_sqrt ha0]
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
    have hcosHalf : 1/2 ≤ Real.cos θ := by
      have ht := Real.sin_sq_add_cos_sq θ
      rw [← hprob] at ht
      nlinarith
    have hsin2 : Real.sqrt a ≤ Real.sin (2*θ) := by
      rw [Real.sin_two_mul, hsin]
      nlinarith [Real.sqrt_nonneg a]
    have hwindow : 2*α/τ ≤ (m : ℝ) := by
      exact (Nat.le_ceil (2*α/τ)).trans (by
        exact_mod_cast (le_max_right 1 (Nat.ceil (2*α/τ))))
    have hprod : (1 : ℝ) = (2*α/τ)*(τ/(2*α)) := by field_simp
    have hmature : 1 ≤ (m : ℝ)*Real.sin (2*θ) := by
      rw [hprod]
      exact mul_le_mul hwindow (hroot.trans hsin2) (by positivity) hmR.le
    have hu := prepared_aa_uniform_success_lower A x₀ S θ m hA hm hθ0 hθ1 hprob hmature
    change (1/4 : ℝ) ≤ (∑ j, f j)/(m:ℝ) at hu
    have he : (∑ j, f j)/(2*(m:ℝ)) = ((∑ j, f j)/(m:ℝ))/2 := by ring
    rw [he]
    linarith

/-- An initial compiled LCHS success amplitude at least `τ / (2 * α)` ensures weighted window
success at least `1 / 8`. -/
theorem static_lchs_window_success_of_initial_mass
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I) (τ : ℝ)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) (hτ : 0 < τ) :
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    let α := coefficientMass c
    let m := staticLchsWindow α τ
    τ/(2*α) ≤ Real.sqrt (MeasureProb
      (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) S) →
    (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
      MeasureProb (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ j.val)
        (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) S := by
  (try dsimp only)
  let A := coefficientLCUUnitary c V j₀ * TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) B
  let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
  have hA : A ∈ unitaryGroup (Fin N × I) ℂ :=
    (unitaryGroup _ ℂ).mul_mem (coefficientLCUUnitary_unitary c V j₀ hα hV)
      (tensorGate_unitary (unitaryGroup (Fin N) ℂ).one_mem hB)
  have hr (k : ℕ) := (static_lchs_actual_expanded_prepare_select_amplification
    I N c V B j₀ i₀ k hα hV hB).2.1
  simp_rw [hr]
  simp only [preparedAACircuit, RepeatCircuit, List.append_nil, run_gate, run_nil]
  exact staticLchs_prepared_window_success A (j₀,i₀) S (coefficientMass c) τ hA hα hτ

/-- The trace norm of the rank-one matrix with entries `u i * star (v j)` is at most the product
of the Euclidean norms of `u` and `v`. -/
private theorem staticLchs_rankOne_trace_bound {I : Type} [Fintype I] [DecidableEq I]
    (u v : QState I) :
    Matrix.traceNorm (Matrix.of (fun i j => u i * (starRingEnd ℂ) (v j))) ≤
      ‖toEuclidean_fromVec u‖ * ‖toEuclidean_fromVec v‖ := by
  classical
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U
    (Matrix.of (fun i j => u i * (starRingEnd ℂ) (v j)))).1
  have he : (U.val * Matrix.of (fun i j => u i * (starRingEnd ℂ) (v j))).trace =
      Qatlib.Foundations.PureStateMath.Inner v (ApplyGate U.val u) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply,
      Qatlib.Foundations.PureStateMath.Inner, ApplyGate, Matrix.mulVec, dotProduct, starRingEnd_apply, Pi.star_apply]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hunit : U.val ∈ unitaryGroup I ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    ext i j
    have hh := congrArg (fun M : Matrix I I ℂ => M i j) U.prop.1
    by_cases hij : i = j <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.one_apply, hij, if_true, if_false] at hh ⊢ <;>
      exact hh
  have hn : ‖toEuclidean_fromVec (ApplyGate U.val u)‖ = ‖toEuclidean_fromVec u‖ := by
    simpa only [toEuclideanCLM_applyGate] using!
      (norm_toEuclideanCLM_of_mem_unitaryGroup hunit (toEuclidean_fromVec u))
  calc
    _ = (Qatlib.Foundations.PureStateMath.Inner v (ApplyGate U.val u)).re := by rw [← hU, he]
    _ ≤ ‖Qatlib.Foundations.PureStateMath.Inner v (ApplyGate U.val u)‖ := Complex.re_le_norm _
    _ ≤ ‖toEuclidean_fromVec v‖ * ‖toEuclidean_fromVec (ApplyGate U.val u)‖ := by
      rw [← inner_euclidean_fromVec]
      exact norm_inner_le_norm _ _
    _ = _ := by rw [hn, mul_comm]

/-- The trace norm distance between two outer products is at most the sum of the vector norms
times the norm of their difference. -/
theorem static_lchs_pure_trace_error {I : Type} [Fintype I] [DecidableEq I]
    (u v : QState I) :
    Matrix.traceNorm (outerProduct u - outerProduct v) ≤
      (‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec v‖) *
        ‖toEuclidean_fromVec (u-v)‖ := by
  have he : outerProduct u - outerProduct v =
      Matrix.of (fun i j => (u-v) i * (starRingEnd ℂ) (u j)) +
        Matrix.of (fun i j => v i * (starRingEnd ℂ) ((u-v) j)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, outerProduct_apply, Matrix.of_apply,
      Pi.sub_apply, map_sub]
    ring
  rw [he]
  exact (Matrix.traceNorm_add_le _ _).trans
    ((add_le_add (staticLchs_rankOne_trace_bound (u-v) u)
      (staticLchs_rankOne_trace_bound v (u-v))).trans_eq (by ring))

/-- If the Euclidean norm of `x` is at least `τ` and the Euclidean distance from `y` to `x` is
at most `ε ≤ τ / 2`, with positive `ε` and `τ`, then `y` is nonzero and the normalized
output densities differ in trace norm by at most `4 * ε / τ`. -/
theorem static_lchs_output_density_error_of_vector_error
    {I : Type} [Fintype I] [DecidableEq I] (x y : QState I) (ε τ : ℝ)
    (hε : 0 < ε) (hτ : 0 < τ) (hετ : ε ≤ τ/2)
    (hτx : τ ≤ ‖toEuclidean_fromVec x‖)
    (he : ‖toEuclidean_fromVec (y-x)‖ ≤ ε) :
    y ≠ 0 ∧ Matrix.traceNorm (staticLchsOutputDensity y - staticLchsOutputDensity x) ≤
      4*ε/τ := by
  have hgap : ε < ‖toEuclidean_fromVec x‖ := by linarith
  have he' : ‖toEuclidean_fromVec y - toEuclidean_fromVec x‖ ≤ ε := by
    simpa only [toEuclidean_fromVec, WithLp.toLp_sub] using! he
  obtain ⟨hy, herr⟩ := Qatlib.Concepts.BlockEncoding.Postselection.normalize_error_of_gap he' hgap
  have hx : toEuclidean_fromVec x ≠ 0 := norm_pos_iff.mp (by linarith : 0 < ‖toEuclidean_fromVec x‖)
  let u : QState I := ((‖toEuclidean_fromVec y‖⁻¹ : ℝ) : ℂ) • y
  let v : QState I := ((‖toEuclidean_fromVec x‖⁻¹ : ℝ) : ℂ) • x
  have hu : toEuclidean_fromVec u = NormedSpace.normalize (toEuclidean_fromVec y) := by
    ext i
    simp [u, NormedSpace.normalize, Complex.real_smul]
  have hv : toEuclidean_fromVec v = NormedSpace.normalize (toEuclidean_fromVec x) := by
    ext i
    simp [v, NormedSpace.normalize, Complex.real_smul]
  have hun : ‖toEuclidean_fromVec u‖ = 1 := by rw [hu]; exact NormedSpace.norm_normalize hy
  have hvn : ‖toEuclidean_fromVec v‖ = 1 := by rw [hv]; exact NormedSpace.norm_normalize hx
  have hdiff : ‖toEuclidean_fromVec (u-v)‖ ≤ 2*ε/‖toEuclidean_fromVec x‖ := by
    simpa only [toEuclidean_fromVec, WithLp.toLp_sub, ← hu, ← hv] using! herr
  refine ⟨?_, ?_⟩
  · intro hz
    apply hy
    simp [hz, toEuclidean_fromVec]
  · change Matrix.traceNorm (outerProduct u - outerProduct v) ≤ _
    calc
      _ ≤ (‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec v‖) *
          ‖toEuclidean_fromVec (u-v)‖ := static_lchs_pure_trace_error u v
      _ ≤ 4*ε/‖toEuclidean_fromVec x‖ := by
        rw [hun, hvn]
        calc
          _ ≤ (1+1) * (2*ε/‖toEuclidean_fromVec x‖) :=
            mul_le_mul_of_nonneg_left hdiff (by norm_num)
          _ = _ := by ring
      _ ≤ 4*ε/τ := div_le_div_of_nonneg_left (by positivity) hτ hτx

/-- The iteration-zero selected data branch is the unnormalized unitary linear combination
applied to the prepared input, scaled by the inverse coefficient mass. -/
theorem static_lchs_initial_data_branch_raw
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) :
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    staticLchsDataBranch j₀
      (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ 0) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) =
      ((coefficientMass c : ℂ)⁻¹) • ((∑ j, c j • V j) *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀)) := by
  (try dsimp only)
  rw [static_lchs_actual_initial_data_branch I N c V B j₀ i₀ hα hV hB]
  rw [← Matrix.smul_mulVec, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, div_eq_mul_inv, mul_comm]

/-- The square root of the probability of a selected label equals the Euclidean norm of its
extracted data branch. -/
private theorem staticLchs_sqrt_label_mass {I : Type} [Fintype I] [DecidableEq I] {N : ℕ}
    (j₀ : Fin N) (y : QState (Fin N × I)) :
    Real.sqrt (MeasureProb y (Finset.univ.filter (fun x : Fin N × I => x.1 = j₀))) =
      ‖toEuclidean_fromVec (staticLchsDataBranch j₀ y)‖ := by
  rw [static_lchs_label_probability]
  have he : MeasureProb (staticLchsDataBranch j₀ y) Finset.univ =
      ‖toEuclidean_fromVec (staticLchsDataBranch j₀ y)‖^2 := by
    rw [norm_toEuclidean_fromVec_sq]
    rfl
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- An operator approximation error at most `ε ≤ τ / 2` and target output norm at least `τ`
imply postselected density error at most `4 * ε / τ` at every positive-success iteration and
weighted window success at least `1 / 8`. -/
theorem static_lchs_actual_output_and_window_of_operator_error
    (I : Type) [Fintype I] [DecidableEq I] (N : ℕ) (c : Fin N → ℂ)
    (V : Fin N → Matrix I I ℂ) (B T : Matrix I I ℂ) (j₀ : Fin N) (i₀ : I) (ε τ : ℝ)
    (hα : 0 < coefficientMass c) (hV : ∀ j, V j ∈ unitaryGroup I ℂ)
    (hB : B ∈ unitaryGroup I ℂ) (hε : 0 < ε) (hτ : 0 < τ) (hετ : ε ≤ τ/2)
    (hτx : τ ≤ ‖toEuclidean_fromVec (T *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))‖)
    (he : ‖(∑ j, c j • V j)-T‖ ≤ ε) :
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    let α := coefficientMass c
    let m := staticLchsWindow α τ
    (∀ k : ℕ,
      let y :=
          Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ k)
          (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))
      0 < MeasureProb y S →
        Matrix.traceNorm (staticLchsOutputDensity (staticLchsDataBranch j₀ y) -
          staticLchsOutputDensity (T *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))) ≤ 4*ε/τ) ∧
    (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
      MeasureProb (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ j.val)
        (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) S := by
  (try dsimp only)
  let ψ := B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀
  let x := T *ᵥ ψ
  let y := (∑ j, c j • V j) *ᵥ ψ
  have hnψ : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp (normalized_applyGate hB (normalized_ket i₀))
  have hvec : ‖toEuclidean_fromVec (y-x)‖ ≤ ε := by
    have hh :=
        Qatlib.Concepts.BlockEncoding.Postselection.stateVector_mulVec_norm_le ((∑ j, c j • V j)-T) ψ
    change ‖toEuclidean_fromVec (((∑ j, c j • V j)-T) *ᵥ ψ)‖ ≤
      ‖(∑ j, c j • V j)-T‖ * ‖toEuclidean_fromVec ψ‖ at hh
    rw [Matrix.sub_mulVec, hnψ, mul_one] at hh
    exact hh.trans he
  have herr := (static_lchs_output_density_error_of_vector_error x y ε τ hε hτ hετ hτx hvec).2
  have hnorm : τ/2 ≤ ‖toEuclidean_fromVec y‖ := by
    have hh := abs_norm_sub_norm_le (toEuclidean_fromVec x) (toEuclidean_fromVec y)
    have hdiff : ‖toEuclidean_fromVec x - toEuclidean_fromVec y‖ ≤ ε := by
      rw [norm_sub_rev]
      simpa only [toEuclidean_fromVec, WithLp.toLp_sub] using! hvec
    have hh' := (le_abs_self _).trans (hh.trans hdiff)
    linarith
  have hα0 : (coefficientMass c : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hα.ne')
  constructor
  · intro k hp
    have hi := static_lchs_actual_postselected_density_invariant I N c V B j₀ i₀ k hα hV hB hp
    have hr : (∑ j, (c j / (coefficientMass c : ℂ)) • V j) *ᵥ ψ =
        ((coefficientMass c : ℂ)⁻¹) • y := by
      rw [← static_lchs_actual_initial_data_branch I N c V B j₀ i₀ hα hV hB,
        static_lchs_initial_data_branch_raw I N c V B j₀ i₀ hα hV hB]
    rw [hi, hr, static_lchs_output_density_smul y _ hα0]
    exact herr
  · apply static_lchs_window_success_of_initial_mass I N c V B j₀ i₀ τ hα hV hB hτ
    rw [staticLchs_sqrt_label_mass, static_lchs_initial_data_branch_raw I N c V B j₀ i₀ hα hV hB]
    simp only [toEuclidean_fromVec, WithLp.toLp_smul, norm_smul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg hα.le]
    change τ/(2*coefficientMass c) ≤ (coefficientMass c)⁻¹ * ‖toEuclidean_fromVec y‖
    calc
      τ/(2*coefficientMass c) = (τ/2)/(coefficientMass c) := by ring
      _ ≤ ‖toEuclidean_fromVec y‖ / coefficientMass c := div_le_div_of_nonneg_right hnorm hα.le
      _ = _ := by ring

/-- A static LCHS quadrature error at most `ε ≤ τ / 2` yields positive coefficient mass,
postselected density error at most `4 * ε / τ`, and weighted window success at least `1 /
8`. -/
theorem static_lchs_output_and_window_of_quadrature_error
    (I : Type) [Fintype I] [DecidableEq I] (L H B : Matrix I I ℂ) (i₀ : I) (t ε τ : ℝ)
    (hL : L.PosSemidef) (hH : H.IsHermitian) (hB : B ∈ unitaryGroup I ℂ)
    (ht : 0 ≤ t) (hε : 0 < ε) (hτ : 0 < τ) (hετ : ε ≤ τ/2)
    (hτx : τ ≤ ‖toEuclidean_fromVec (staticNonunitaryEvolution L H t *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))‖)
    (he : ‖staticLchsQuadrature L H t (staticLchsCutoff ε) (staticLchsNodes L t ε) -
      staticNonunitaryEvolution L H t‖ ≤ ε) :
    let K := staticLchsCutoff ε
    let N := staticLchsNodes L t ε
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => hamiltonianEvolution (H+staticLchsGrid K N j • L) t
    let α := coefficientMass c
    let m := staticLchsWindow α τ
    0 < α ∧ ∀ j₀ : Fin N,
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    (∀ k : ℕ,
      let y :=
          Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ k)
          (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))
      0 < MeasureProb y S →
        Matrix.traceNorm (staticLchsOutputDensity (staticLchsDataBranch j₀ y) -
          staticLchsOutputDensity (staticNonunitaryEvolution L H t *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))) ≤ 4*ε/τ) ∧
    (1/8 : ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
      MeasureProb (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ j.val)
        (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) S := by
  (try dsimp only)
  obtain ⟨hK, hN, _⟩ := static_lchs_computed_quadrature_budget L t ε ht hε
  have hα := static_lchs_coefficient_mass_pos (staticLchsCutoff ε) (staticLchsNodes L t ε) hK hN
  refine ⟨hα, fun j₀ => ?_⟩
  exact static_lchs_actual_output_and_window_of_operator_error I (staticLchsNodes L t ε)
    (staticLchsCoeff (staticLchsCutoff ε) (staticLchsNodes L t ε))
    (fun j => hamiltonianEvolution (H+staticLchsGrid (staticLchsCutoff ε) (staticLchsNodes L t ε) j • L) t)
    B (staticNonunitaryEvolution L H t) j₀ i₀ ε τ hα
    (fun j => hamiltonianEvolution_unitary
      (hH.add (hL.isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) t)
    hB hε hτ hετ hτx he

/-- For the prescribed static quadrature schedule, the coefficient mass lies in `(0, 2]`,
quadrature error is at most `ε`, and every positive-success compiled output has density
error at most `4 * ε / τ` [AnLiuLin2023]. -/
theorem static_lchs_same_postselected_solution_state :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H B : Matrix I I ℂ) (i₀ : I) (t ε τ : ℝ),
    L.PosSemidef → H.IsHermitian → B ∈ unitaryGroup I ℂ → 0 ≤ t →
    0 < ε → ε ≤ 1 → 0 < τ → ε ≤ τ/2 →
    τ ≤ ‖toEuclidean_fromVec (staticNonunitaryEvolution L H t *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))‖ →
    let K := staticLchsCutoff ε
    let N := staticLchsNodes L t ε
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => hamiltonianEvolution (H+staticLchsGrid K N j • L) t
    let α := coefficientMass c
    0 < α ∧ α ≤ 2 ∧
    ‖staticLchsQuadrature L H t K N-staticNonunitaryEvolution L H t‖ ≤ ε ∧
    ∀ j₀ : Fin N, ∀ k : ℕ,
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    let y :=
        Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ k)
        (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))
    0 < MeasureProb y S →
    Matrix.traceNorm (staticLchsOutputDensity (staticLchsDataBranch j₀ y) -
      staticLchsOutputDensity (staticNonunitaryEvolution L H t *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))) ≤ 4*ε/τ := by
  intro I _ _ L H B i₀ t ε τ hL hH hB ht hε hε1 hτ hετ hτx
  (try dsimp only)
  obtain ⟨hK, hN, hb⟩ := static_lchs_computed_quadrature_budget L t ε ht hε
  obtain ⟨hα, hα2⟩ := static_lchs_computed_coefficient_mass L t ε ht hε hε1
  have he : ‖staticLchsQuadrature L H t (staticLchsCutoff ε) (staticLchsNodes L t ε) -
      staticNonunitaryEvolution L H t‖ ≤ ε :=
    (static_noncommuting_lchs_quadrature_error I L H t (staticLchsCutoff ε)
      (staticLchsNodes L t ε) hL hH ht hK hN).trans hb
  refine ⟨hα, hα2, he, ?_⟩
  intro j₀ k hp
  exact ((static_lchs_output_and_window_of_quadrature_error I L H B i₀ t ε τ
    hL hH hB ht hε hτ hετ hτx he).2 j₀).1 k hp

/-- The static LCHS iteration weights sum to one, the window is at most `2 * α / τ + 1`, its
success is at least `1 / 8`, and each sampled word uses at most `2 * m + 1` input and
selection accesses [AnLiuLin2023]. -/
theorem static_lchs_finite_window_success_and_preparation_budget :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H B : Matrix I I ℂ) (i₀ : I) (t ε τ : ℝ),
    L.PosSemidef → H.IsHermitian → B ∈ unitaryGroup I ℂ → 0 ≤ t →
    0 < ε → ε ≤ 1 → 0 < τ → ε ≤ τ/2 →
    τ ≤ ‖toEuclidean_fromVec (staticNonunitaryEvolution L H t *ᵥ (B *ᵥ Qatlib.Foundations.PureStateMath.Ket i₀))‖ →
    let K := staticLchsCutoff ε
    let N := staticLchsNodes L t ε
    let c := staticLchsCoeff K N
    let V := fun j : Fin N => hamiltonianEvolution (H+staticLchsGrid K N j • L) t
    let α := coefficientMass c
    let m := staticLchsWindow α τ
    (∑ j : Fin m, staticLchsIterationWeight m j) = 1 ∧ (m:ℝ) ≤ 2*α/τ+1 ∧
    ∀ j₀ : Fin N,
    let S := Finset.univ.filter (fun x : Fin N × I => x.1 = j₀)
    (1/8:ℝ) ≤ ∑ j : Fin m, staticLchsIterationWeight m j *
      MeasureProb (Run (preparedMark S) (staticLchsCompile c V B j₀ i₀ j.val) (Qatlib.Foundations.PureStateMath.Ket (j₀,i₀))) S ∧
    (∀ j : Fin m, (staticLchsWord j.val).count .inputF + (staticLchsWord j.val).count .inputB ≤ 2*m+1 ∧
      (staticLchsWord j.val).count .selectF + (staticLchsWord j.val).count .selectB ≤ 2*m+1) := by
  intro I _ _ L H B i₀ t ε τ hL hH hB ht hε hε1 hτ hετ hτx
  (try dsimp only)
  obtain ⟨hα, _, he, _⟩ := static_lchs_same_postselected_solution_state I L H B i₀ t ε τ
    hL hH hB ht hε hε1 hτ hετ hτx
  obtain ⟨hm, hmb⟩ := static_lchs_window_bound
    (coefficientMass (staticLchsCoeff (staticLchsCutoff ε) (staticLchsNodes L t ε))) τ hα hτ
  refine ⟨(static_lchs_iteration_weight_distribution _ hm).2, hmb, ?_⟩
  intro j₀
  refine ⟨((static_lchs_output_and_window_of_quadrature_error I L H B i₀ t ε τ
    hL hH hB ht hε hτ hετ hτx he).2 j₀).2, fun j => ?_⟩
  exact static_lchs_window_actual_access_budget I (staticLchsNodes L t ε)
    (staticLchsCoeff (staticLchsCutoff ε) (staticLchsNodes L t ε))
    (fun j => hamiltonianEvolution (H+staticLchsGrid (staticLchsCutoff ε) (staticLchsNodes L t ε) j • L) t)
    B j₀ i₀ hα
    (fun j => hamiltonianEvolution_unitary
      (hH.add (hL.isHermitian.smul (R := ℝ) (IsSelfAdjoint.all _))) t) hB _ j

end Qatlib.Concepts.LchsSimulation.StaticLchs
