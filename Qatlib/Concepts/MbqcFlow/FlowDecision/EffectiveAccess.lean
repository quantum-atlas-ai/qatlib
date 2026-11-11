/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.EffectiveAccessDefs
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding

/-!
# Exact state preparation and finite access circuits

This module verifies Householder-based preparation of dense and nonzero sparse amplitude data.
It proves unitarity of the completion and its action on a designated basis vector, then packages
exact preparation as a circuit with one arbitrary unitary gate and no oracle queries. The
finite-dimensional circuit model is described in [NielsenChuang2010].

The module also realizes a sparse-support flag oracle, its controlled and adjoint forms, and an
index-loading permutation by circuits with at most one arbitrary unitary gate and no oracle
queries. Together these constructions establish the stated `HasEffectiveAccess` property.

## Main statements

* `g1`: exact dense and sparse state preparation with the stated gate and query counts.
* `g2`: unitary circuits for the finite access operators and the resulting effective-access
  property.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ResourceBounds.AsymBounds

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccess

open Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccess Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The total squared norm of the amplitude function represented by sparse access data. -/
private noncomputable def sparseNorm {N b : ℕ} (s : SparseAccessData N b) : ℝ :=
  ∑ i, ‖sparseValue s i‖ ^ 2

/-- The sparse amplitude vector divided by the square root of its total squared norm. -/
private noncomputable def sparseTarget {N b : ℕ} (s : SparseAccessData N b) :
    QState (Fin N) :=
  fun i => sparseValue s i / ((Real.sqrt (sparseNorm s) : ℝ) : ℂ)

/-- The circuit consisting of one Householder-completion gate for the sparse target, using basis
index zero as the initial vector. -/
private noncomputable def prepareWordSparse {N b : ℕ} (s : SparseAccessData N b)
    (hN : 0 < N) : Circuit (Fin N) :=
  [Step.gate (householderCompletion (⟨0, hN⟩ : Fin N) (sparseTarget s))]

/-- The `b`-bit encoding of an index when the index range fits in `2 ^ b` addresses. -/
private def addrBits {N b : ℕ} (hN : N ≤ 2 ^ b) (i : Fin N) : Reg b :=
  (bitVecEquiv b).symm ⟨i.val, lt_of_lt_of_le i.isLt hN⟩

/-- The bit-register encoding of an address and a Boolean target, with the target following the
`b` address bits. -/
private def pairBits {N b : ℕ} (hN : N ≤ 2 ^ b) (p : Fin N × Bool) : Reg (b + 1) :=
  fun j => if h : (j : ℕ) < b then addrBits hN p.1 ⟨j, h⟩ else p.2

/-- The bit-register encoding of an address-target pair followed by an additional Boolean
control bit. -/
private def ctlBits {N b : ℕ} (hN : N ≤ 2 ^ b)
    (q : Bool × (Fin N × Bool)) : Reg (b + 2) :=
  fun j => if h : (j : ℕ) < b + 1 then pairBits hN q.2 ⟨j, h⟩ else q.1

/-- The register formed by concatenating the `b`-bit address encoding with a `b`-bit payload
register. -/
private def indexBits {N b : ℕ} (hN : N ≤ 2 ^ b) (p : Fin N × Reg b) : Reg (b + b) :=
  fun j => if h : (j : ℕ) < b then addrBits hN p.1 ⟨j, h⟩
    else p.2 ⟨(j : ℕ) - b, by have := j.isLt; omega⟩

/-- The extension of a state along a map into a bit register, using zero as the default
amplitude outside its image. -/
private noncomputable def extendState {w : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (ι : I → Reg w) (ψ : QState I) : QState (Reg w) :=
  Function.extend ι ψ 0

/-- The conjunction of polynomial bounds on local-gate count, encoded program length, and
register width plus program length, in terms of `2 ^ w + w + k + 1`. -/
private def SynthBudget {w : ℕ} (gs : List (LocalQFTGate w)) (k Cg Dg Cb Db : ℕ) :
    Prop :=
  gs.length ≤ Cg * (2 ^ w + w + k + 1) ^ Dg ∧
    (localGateProgramBits gs).length ≤ Cb * (2 ^ w + w + k + 1) ^ Db ∧
    (w + (localGateProgramBits gs).length) ≤ w + Cb * (2 ^ w + w + k + 1) ^ Db

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The unit complex phase given by the argument of the designated state component. -/
private noncomputable def hhPhase (i₀ : I) (v : QState I) : ℂ :=
  Complex.exp (Complex.arg (v i₀) * Complex.I)

/-- The vector obtained by removing `hhPhase` from the state and subtracting the designated
computational-basis vector. -/
private noncomputable def hhW (i₀ : I) (v : QState I) : QState I :=
  fun i => (hhPhase i₀ v)⁻¹ * v i - Ket i₀ i

/-- The sum of the squared component norms of the Householder difference vector `hhW`. -/
private noncomputable def hhNrm (i₀ : I) (v : QState I) : ℝ :=
  ∑ i, ‖hhW i₀ v i‖ ^ 2

/-- The outer product of a complex vector with its conjugate, with entries `w i * starRingEnd ℂ
(w j)`. -/
private noncomputable def hhOuter (w : QState I) : Matrix I I ℂ :=
  Matrix.of fun i j => w i * starRingEnd ℂ (w j)

/-- The Householder matrix formed by subtracting twice the outer product of `hhW`, divided by
its squared norm, from the identity. -/
private noncomputable def hhReflect (i₀ : I) (v : QState I) : Matrix I I ℂ :=
  1 - ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) • hhOuter (hhW i₀ v)

/-- Each entry of the Householder matrix is the corresponding identity entry minus the scaled
outer-product entry. -/
private theorem hhReflect_entry (i₀ : I) (v : QState I) (i j : I) :
    hhReflect i₀ v i j = (if i = j then (1 : ℂ) else 0)
      - (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v j))) := rfl

/-- The completion entries are a phase times the identity when `hhNrm` vanishes, and otherwise
include the explicit scaled Householder correction. -/
private theorem householderCompletion_entry (i₀ : I) (v : QState I) (i j : I) :
    householderCompletion i₀ v i j =
      (if hhNrm i₀ v = 0 then hhPhase i₀ v * (if i = j then (1 : ℂ) else 0)
        else hhPhase i₀ v * (if i = j then (1 : ℂ) else 0)
          - ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) * hhPhase i₀ v * hhW i₀ v i
            * starRingEnd ℂ (hhW i₀ v j)) := rfl

/-- The Householder completion equals `hhReflect` multiplied by the scalar phase `hhPhase`. -/
private theorem householderCompletion_eq_smul (i₀ : I) (v : QState I) :
    householderCompletion i₀ v = hhPhase i₀ v • hhReflect i₀ v := by
  ext i j
  rw [householderCompletion_entry, Matrix.smul_apply, smul_eq_mul, hhReflect_entry]
  by_cases hn : hhNrm i₀ v = 0
  · rw [if_pos hn, mul_sub]
    have ht : ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) = 0 := by
      rw [hn, Complex.ofReal_zero, div_zero]
    rw [ht, zero_mul, mul_zero, sub_zero]
  · rw [if_neg hn]
    ring

/-- The phase used in the Householder construction has norm one. -/
private theorem hhPhase_norm_one (i₀ : I) (v : QState I) : ‖hhPhase i₀ v‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The phase used in the Householder construction is nonzero. -/
private theorem hhPhase_ne_zero (i₀ : I) (v : QState I) : hhPhase i₀ v ≠ 0 := by
  intro h0
  have h1 : ‖hhPhase i₀ v‖ = 1 := hhPhase_norm_one i₀ v
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

/-- The product of the conjugate Householder phase with the phase itself is one. -/
private theorem hhPhase_star_mul (i₀ : I) (v : QState I) :
    starRingEnd ℂ (hhPhase i₀ v) * hhPhase i₀ v = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    hhPhase_norm_one i₀ v, one_pow, Complex.ofReal_one]

/-- Multiplication by the inverse Householder phase preserves the norm of a complex number. -/
private theorem hhPhase_inv_mul_norm (i₀ : I) (v : QState I) (z : ℂ) :
    ‖((hhPhase i₀ v)⁻¹ * z)‖ = ‖z‖ := by
  rw [norm_mul, norm_inv, hhPhase_norm_one, inv_one, one_mul]

/-- The outer product `hhOuter w` is equal to its conjugate transpose. -/
private theorem hhOuter_star (w : QState I) : (hhOuter w)ᴴ = hhOuter w := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hhOuter, Matrix.of_apply, RCLike.star_def,
    map_mul, Complex.conj_conj]
  ring

/-- The sum of the conjugate-self products of vector components equals the complex cast of the
sum of their squared norms. -/
private theorem sum_star_mul_self (w : QState I) :
    ∑ i, starRingEnd ℂ (w i) * w i = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- Squaring the outer-product matrix multiplies it by the sum of the squared component norms of
its defining vector. -/
private theorem hhOuter_mul (w : QState I) :
    hhOuter w * hhOuter w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) • hhOuter w := by
  ext i j
  simp only [Matrix.mul_apply, hhOuter, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hrew : ∀ k : I, (w i * starRingEnd ℂ (w k)) * (w k * starRingEnd ℂ (w j))
      = (w i * starRingEnd ℂ (w j)) * (starRingEnd ℂ (w k) * w k) := fun k => by ring
  rw [Finset.sum_congr rfl (fun k _ => hrew k), ← Finset.mul_sum, sum_star_mul_self]
  ring

/-- The Householder matrix `hhReflect` is equal to its conjugate transpose. -/
private theorem hhReflect_star (i₀ : I) (v : QState I) :
    (hhReflect i₀ v)ᴴ = hhReflect i₀ v := by
  rw [hhReflect, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, Complex.star_def, hhOuter_star,
    show ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) = (((2 : ℝ) / hhNrm i₀ v : ℝ) : ℂ) from
      (Complex.ofReal_div _ _).symm,
    Complex.conj_ofReal]

/-- Summing a complex function against a left identity-entry selector returns its value at the
selected index. -/
private theorem sum_ite_mul_left (i : I) (f : I → ℂ) :
    ∑ k, (if i = k then (1 : ℂ) else 0) * f k = f i := by
  rw [Finset.sum_eq_single i
    (fun k (_ : k ∈ Finset.univ) (hk : k ≠ i) => by rw [if_neg (Ne.symm hk), zero_mul])
    (by simp)]
  rw [if_pos rfl, one_mul]

/-- Summing a complex function against a right identity-entry selector returns its value at the
selected index. -/
private theorem sum_ite_mul_right (j : I) (f : I → ℂ) :
    ∑ k, f k * (if k = j then (1 : ℂ) else 0) = f j := by
  rw [Finset.sum_eq_single j
    (fun k (_ : k ∈ Finset.univ) (hk : k ≠ j) => by rw [if_neg hk, mul_zero])
    (by simp)]
  rw [if_pos rfl, mul_one]

/-- The square of the Householder matrix is the identity, including when its defining difference
vector has zero norm. -/
private theorem hhReflect_mul_self (i₀ : I) (v : QState I) :
    hhReflect i₀ v * hhReflect i₀ v = 1 := by
  ext i j
  have hsum : ∑ k, starRingEnd ℂ (hhW i₀ v k) * hhW i₀ v k
      = ((hhNrm i₀ v : ℝ) : ℂ) := sum_star_mul_self _
  simp only [hhReflect_entry, Matrix.mul_apply, Matrix.one_apply]
  have hprod : ∀ k : I,
      ((if i = k then (1 : ℂ) else 0)
          - ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v k)))
        * ((if k = j then (1 : ℂ) else 0)
          - ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v k * starRingEnd ℂ (hhW i₀ v j)))
      = (if i = k then (1 : ℂ) else 0) * (if k = j then (1 : ℂ) else 0)
        - (if i = k then (1 : ℂ) else 0)
          * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v k * starRingEnd ℂ (hhW i₀ v j)))
        - (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v k)))
          * (if k = j then (1 : ℂ) else 0)
        + (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v k)))
          * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v k * starRingEnd ℂ (hhW i₀ v j))) :=
    fun k => by ring
  rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hprod k),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_ite_mul_left, sum_ite_mul_left, sum_ite_mul_right]
  have hS4 : ∑ k : I,
      (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v k)))
        * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
          * (hhW i₀ v k * starRingEnd ℂ (hhW i₀ v j)))
      = ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
          * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v j)))
          * ((hhNrm i₀ v : ℝ) : ℂ) := by
    have hrew : ∀ k : I,
        (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v k)))
          * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v k * starRingEnd ℂ (hhW i₀ v j)))
        = (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v j)))
          * (starRingEnd ℂ (hhW i₀ v k) * hhW i₀ v k) := fun k => by ring
    rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hrew k), ← Finset.mul_sum,
      hsum]
    ring
  rw [hS4]
  by_cases hnc : ((hhNrm i₀ v : ℝ) : ℂ) = 0
  · have ht0 : ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) = 0 := by
      rw [hnc, div_zero]
    rw [ht0]
    ring
  · have h2 : ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) * ((hhNrm i₀ v : ℝ) : ℂ) = (2 : ℂ) :=
      div_mul_cancel₀ _ hnc
    rw [show ((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
          * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v j)))
          * ((hhNrm i₀ v : ℝ) : ℂ)
        = (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ))
            * (hhW i₀ v i * starRingEnd ℂ (hhW i₀ v j)))
          * (((2 : ℂ) / ((hhNrm i₀ v : ℝ) : ℂ)) * ((hhNrm i₀ v : ℝ) : ℂ)) from by ring,
      h2]
    ring

/-- The Householder completion is unitary for every input vector and designated basis index. -/
private theorem householderCompletion_mem_unitaryGroup (i₀ : I) (v : QState I) :
    householderCompletion i₀ v ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    householderCompletion_eq_smul, Matrix.conjTranspose_smul, Complex.star_def,
    hhReflect_star, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hhReflect_mul_self,
    mul_comm, hhPhase_star_mul, one_smul]

/-- Multiplying a matrix by a computational-basis vector selects the corresponding matrix
column. -/
private theorem mulVec_ket_apply (M : Matrix I I ℂ) (i₀ : I) (j : I) :
    (M *ᵥ Ket i₀) j = M j i₀ := by
  simp only [Matrix.mulVec, dotProduct, ket_apply]
  rw [Finset.sum_eq_single i₀ (fun i _ hi => by rw [if_neg hi, mul_zero]) (by simp)]
  rw [if_pos rfl, mul_one]

/-- Under the reciprocal and difference identities, the diagonal Householder column expression
simplifies to `c * ((a - 1) + 1)`. -/
private theorem hh_col_diag {c t x a : ℂ} (hk : t * x = 1) (hx : a - 1 = -x) :
    c * 1 - t * c * (a - 1) * (a - 1) = c * ((a - 1) + 1) := by
  rw [hx]
  linear_combination (-c) * x * hk

/-- Under the reciprocal and difference identities, the off-diagonal Householder column
expression simplifies to `c * (u + 0)`. -/
private theorem hh_col_offdiag {c t x a u : ℂ} (hk : t * x = 1) (hx : a - 1 = -x) :
    c * 0 - t * c * u * (a - 1) = c * (u + 0) := by
  rw [hx]
  linear_combination c * u * hk

/-- For a normalized target vector, its Householder completion maps the designated
computational-basis vector exactly to that target. -/
private theorem householderCompletion_mulVec_ket (i₀ : I) {v : QState I}
    (hv : Normalized v) : householderCompletion i₀ v *ᵥ Ket i₀ = v := by
  have hmod : ∀ i : I, ‖(hhPhase i₀ v)⁻¹ * v i‖ = ‖v i‖ :=
    fun i => hhPhase_inv_mul_norm i₀ v (v i)
  have hfac : v i₀ = ((‖v i₀‖ : ℝ) : ℂ) * hhPhase i₀ v :=
    (Complex.norm_mul_exp_arg_mul_I (v i₀)).symm
  have hWself : hhW i₀ v i₀ = ((‖v i₀‖ : ℝ) : ℂ) - 1 := by
    have h1 : (hhPhase i₀ v)⁻¹ * v i₀ = ((‖v i₀‖ : ℝ) : ℂ) := by
      conv_lhs => rw [hfac]
      rw [mul_comm ((‖v i₀‖ : ℝ) : ℂ) (hhPhase i₀ v), ← mul_assoc,
        inv_mul_cancel₀ (hhPhase_ne_zero i₀ v), one_mul]
    show (hhPhase i₀ v)⁻¹ * v i₀ - Ket i₀ i₀ = _
    rw [ket_self, h1]
  have hWother : ∀ i : I, i ≠ i₀ → hhW i₀ v i = (hhPhase i₀ v)⁻¹ * v i := by
    intro i hi
    show (hhPhase i₀ v)⁻¹ * v i - Ket i₀ i = _
    rw [ket_ne hi, sub_zero]
  have hvW : ∀ i : I, v i = hhPhase i₀ v * (hhW i₀ v i + Ket i₀ i) := by
    intro i
    show v i = hhPhase i₀ v * ((hhPhase i₀ v)⁻¹ * v i - Ket i₀ i + Ket i₀ i)
    rw [sub_add_cancel, ← mul_assoc, mul_inv_cancel₀ (hhPhase_ne_zero i₀ v), one_mul]

  have hsumall : ∑ i, ‖(hhPhase i₀ v)⁻¹ * v i‖ ^ 2 = 1 := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hmod i])]
    exact hv
  have hsing : ‖(hhPhase i₀ v)⁻¹ * v i₀‖ ^ 2 = ‖v i₀‖ ^ 2 := by rw [hmod i₀]
  have herase : ∑ i ∈ Finset.univ.erase i₀, ‖hhW i₀ v i‖ ^ 2 = 1 - ‖v i₀‖ ^ 2 := by
    rw [Finset.sum_congr rfl
      (fun i (hi : i ∈ Finset.univ.erase i₀) =>
        by rw [hWother i (Finset.ne_of_mem_erase hi)])]
    have hsplit0 := Finset.sum_erase_add (Finset.univ : Finset I)
      (fun i => ‖(hhPhase i₀ v)⁻¹ * v i‖ ^ 2) (Finset.mem_univ i₀)
    have hsplit : ∑ x ∈ Finset.univ.erase i₀, ‖(hhPhase i₀ v)⁻¹ * v x‖ ^ 2
        + ‖(hhPhase i₀ v)⁻¹ * v i₀‖ ^ 2
        = ∑ x, ‖(hhPhase i₀ v)⁻¹ * v x‖ ^ 2 := hsplit0
    rw [hsing, hsumall] at hsplit
    linarith
  have hnrm : hhNrm i₀ v = 2 * (1 - ‖v i₀‖) := by
    have hsplitW0 := Finset.sum_erase_add (Finset.univ : Finset I)
      (fun i => ‖hhW i₀ v i‖ ^ 2) (Finset.mem_univ i₀)
    have hsplitW : ∑ x ∈ Finset.univ.erase i₀, ‖hhW i₀ v x‖ ^ 2 + ‖hhW i₀ v i₀‖ ^ 2
        = ∑ x, ‖hhW i₀ v x‖ ^ 2 := hsplitW0
    have hself : ‖hhW i₀ v i₀‖ ^ 2 = (1 - ‖v i₀‖) ^ 2 := by
      have hcast : (((‖v i₀‖ : ℝ) : ℂ) - 1) = (((‖v i₀‖ - 1 : ℝ) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hWself, hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    calc hhNrm i₀ v = ∑ i, ‖hhW i₀ v i‖ ^ 2 := rfl
      _ = ‖hhW i₀ v i₀‖ ^ 2 + ∑ i ∈ Finset.univ.erase i₀, ‖hhW i₀ v i‖ ^ 2 := by
            rw [← hsplitW]
            ring
      _ = (1 - ‖v i₀‖) ^ 2 + (1 - ‖v i₀‖ ^ 2) := by rw [hself, herase]
      _ = 2 * (1 - ‖v i₀‖) := by ring

  funext j
  rw [mulVec_ket_apply, householderCompletion_entry]
  by_cases hn : hhNrm i₀ v = 0
  · have hWall : ∀ i : I, hhW i₀ v i = 0 := by
      have hsum0 : ∑ i, ‖hhW i₀ v i‖ ^ 2 = 0 := by
        rw [show hhNrm i₀ v = ∑ i, ‖hhW i₀ v i‖ ^ 2 from rfl] at hn
        exact hn
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ Finset.univ) => by positivity)).mp hsum0
      intro i
      have h2 := (pow_eq_zero_iff (two_ne_zero)).mp (h i (Finset.mem_univ i))
      exact norm_eq_zero.mp h2
    rw [if_pos hn]
    rcases eq_or_ne j i₀ with hj | hj
    · rw [hj, if_pos rfl, hvW i₀, hWall i₀, ket_self, zero_add]
    · rw [if_neg hj, hvW j, hWall j, ket_ne hj, add_zero]
  · rw [if_neg hn]

    have h1a : (1 : ℝ) - ‖v i₀‖ ≠ 0 := by
      intro h0
      apply hn
      rw [hnrm, h0]
      ring
    have hcast0 : (((2 * (1 - ‖v i₀‖) : ℝ) : ℝ) : ℂ)
        = (2 : ℂ) * ((1 - ‖v i₀‖ : ℝ) : ℂ) := by
      push_cast
      ring
    have hxne : ((1 - ‖v i₀‖ : ℝ) : ℂ) ≠ 0 := by
      intro h0
      exact h1a (by exact_mod_cast h0)
    have hkey : ((2 : ℂ) / (((2 * (1 - ‖v i₀‖)) : ℝ) : ℂ))
        * ((1 - ‖v i₀‖ : ℝ) : ℂ) = 1 := by
      rw [hcast0]
      field_simp
    have hxneg : (((‖v i₀‖ : ℝ) : ℂ) - 1) = -(((1 - ‖v i₀‖ : ℝ) : ℂ)) := by
      push_cast
      ring
    have hstarW : starRingEnd ℂ (hhW i₀ v i₀) = hhW i₀ v i₀ := by
      rw [hWself, map_sub, Complex.conj_ofReal, map_one]
    rw [hnrm]
    rcases eq_or_ne j i₀ with hj | hj
    · rw [hj, if_pos rfl, hstarW]
      conv_rhs => rw [hvW i₀]
      rw [hWself, ket_self]
      exact hh_col_diag hkey hxneg
    · rw [if_neg hj, hstarW, hWself, hvW j, hWother j hj, ket_ne hj]
      exact hh_col_offdiag hkey hxneg

/-- The rescaled sparse target is normalized when its total squared amplitude norm is positive. -/
private theorem sparseTarget_normalized {N b : ℕ} (s : SparseAccessData N b)
    (h : 0 < sparseNorm s) : Normalized (sparseTarget s) := by
  have hnb : 0 ≤ sparseNorm s := le_of_lt h
  have hr : 0 < Real.sqrt (sparseNorm s) := Real.sqrt_pos_of_pos h
  have hstep : ∀ i : Fin N, ‖sparseValue s i / (((Real.sqrt (sparseNorm s) : ℝ) : ℂ))‖
      = ‖sparseValue s i‖ / Real.sqrt (sparseNorm s) := by
    intro i
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.le]
  unfold Normalized sparseTarget
  simp only [hstep, div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt hnb,
    show (∑ i, ‖sparseValue s i‖ ^ 2 : ℝ) = sparseNorm s from rfl, div_self (ne_of_gt h)]

/-- Dense normalized data and sparse data with positive total squared norm possess exact
preparation circuits with one arbitrary unitary gate and zero queries. The theorem also
records unitarity, the action on arbitrary inputs, and zero preparation error from the
designated basis vector. -/
theorem g1 :
  (∀ (n : ℕ) (d : DenseAmplitudeData n) (ε : ℝ), 0 ≤ ε →
    IsUnitaryCircuit (prepareWordDense d) ∧
    QueryCount (prepareWordDense d) = 0 ∧
    GateCount (prepareWordDense d) = 1 ∧
    prepareUnitary d ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
    (∀ ψ : QState (Reg n),
      Run (1 : Matrix (Reg n) (Reg n) ℂ) (prepareWordDense d) ψ
        = ApplyGate (prepareUnitary d) ψ) ∧
    ‖Run (1 : Matrix (Reg n) (Reg n) ℂ) (prepareWordDense d) (Ket (ZeroStr n))
      - d.amp‖ ≤ 0) ∧
  (∀ (N b : ℕ) (s : SparseAccessData N b) (ε : ℝ) (hN : 0 < N),
    0 ≤ ε → 0 < sparseNorm s →
    Normalized (sparseTarget s) ∧
    IsUnitaryCircuit (prepareWordSparse s hN) ∧
    QueryCount (prepareWordSparse s hN) = 0 ∧
    GateCount (prepareWordSparse s hN) = 1 ∧
    householderCompletion (⟨0, hN⟩ : Fin N) (sparseTarget s)
      ∈ Matrix.unitaryGroup (Fin N) ℂ ∧
    (∀ ψ : QState (Fin N),
      Run (1 : Matrix (Fin N) (Fin N) ℂ) (prepareWordSparse s hN) ψ
        = ApplyGate (householderCompletion (⟨0, hN⟩ : Fin N) (sparseTarget s)) ψ) ∧
    ‖Run (1 : Matrix (Fin N) (Fin N) ℂ) (prepareWordSparse s hN)
        (Ket (⟨0, hN⟩ : Fin N)) - sparseTarget s‖ ≤ 0) := by
  refine ⟨fun n d ε _hε => ?_, fun N b s ε hN _hε hsparse => ?_⟩
  · have hpu : prepareUnitary d ∈ Matrix.unitaryGroup (Reg n) ℂ :=
      householderCompletion_mem_unitaryGroup (ZeroStr n) d.amp
    have hcol : householderCompletion (ZeroStr n) d.amp *ᵥ Ket (ZeroStr n) = d.amp :=
      householderCompletion_mulVec_ket (ZeroStr n) d.normalized
    have hrun : Run (1 : Matrix (Reg n) (Reg n) ℂ) (prepareWordDense d) (Ket (ZeroStr n))
        = d.amp := hcol
    refine ⟨(isUnitaryCircuit_gate _ []).mpr ⟨hpu, isUnitaryCircuit_nil⟩, rfl, rfl, hpu,
      fun ψ => rfl, ?_⟩
    rw [hrun, sub_self, norm_zero]
  · have hnrm : Normalized (sparseTarget s) := sparseTarget_normalized s hsparse
    have hpu : householderCompletion (⟨0, hN⟩ : Fin N) (sparseTarget s)
        ∈ Matrix.unitaryGroup (Fin N) ℂ :=
      householderCompletion_mem_unitaryGroup _ _
    have hcol : householderCompletion (⟨0, hN⟩ : Fin N) (sparseTarget s)
        *ᵥ Ket (⟨0, hN⟩ : Fin N) = sparseTarget s :=
      householderCompletion_mulVec_ket _ hnrm
    have hrun : Run (1 : Matrix (Fin N) (Fin N) ℂ) (prepareWordSparse s hN)
        (Ket (⟨0, hN⟩ : Fin N)) = sparseTarget s := hcol
    refine ⟨hnrm, (isUnitaryCircuit_gate _ []).mpr ⟨hpu, isUnitaryCircuit_nil⟩, rfl, rfl,
      hpu, fun ψ => rfl, ?_⟩
    rw [hrun, sub_self, norm_zero]

/-- The map that leaves the address fixed and flips a Boolean target exactly when the addressed
sparse amplitude is nonzero. -/
private noncomputable def oracleFlip {N b : ℕ} (d : SparseAccessData N b) (p : Fin N × Bool) :
    Fin N × Bool :=
  (p.1, Bool.xor p.2 (sparseValue d p.1 ≠ 0))

/-- Applying the sparse-support target flip twice returns the original address-target pair. -/
private theorem oracleFlip_involutive {N b : ℕ} (d : SparseAccessData N b) :
    Function.Involutive (oracleFlip d) := by
  intro ⟨i, β⟩
  show (i, Bool.xor (Bool.xor β (sparseValue d i ≠ 0)) (sparseValue d i ≠ 0)) = (i, β)
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The sparse value oracle is the permutation matrix of the support-controlled Boolean flip
`oracleFlip`. -/
private theorem sparseValueOracle_eq_permMatrix {N b : ℕ} (d : SparseAccessData N b) :
    sparseValueOracle d = permMatrix (oracleFlip d) := by
  ext x y
  simp only [sparseValueOracle, Matrix.of_apply, permMatrix, oracleFlip]
  by_cases hxy : x.1 = y.1 ∧ y.2 = Bool.xor x.2 (sparseValue d x.1 ≠ 0)
  · rw [if_pos hxy]
    obtain ⟨h1, h2⟩ := hxy
    rw [h1] at h2
    have hx2 : x.2 = (y.2 ^^ decide (sparseValue d y.1 ≠ 0)) := by
      rw [h2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    refine Eq.symm (if_pos ?_)
    have hxe : x = (y.1, y.2 ^^ decide (sparseValue d y.1 ≠ 0)) := by
      rw [Prod.ext_iff]
      exact ⟨h1, hx2⟩
    rw [hxe]
  · rw [if_neg hxy, if_neg]
    intro heq
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp heq
    refine hxy ⟨h1, ?_⟩
    rw [h1, h2, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The sparse-support flag oracle is unitary. -/
private theorem sparseValueOracle_mem_unitaryGroup {N b : ℕ} (d : SparseAccessData N b) :
    sparseValueOracle d ∈ Matrix.unitaryGroup (Fin N × Bool) ℂ := by
  rw [sparseValueOracle_eq_permMatrix]
  exact permMatrix_unitary (oracleFlip_involutive d)

/-- For each fixed address, the map exchanges the zero payload with the encoded address and
leaves every other payload fixed. -/
private def indexFlip {N b : ℕ} (enc : Fin N → Reg b) (p : Fin N × Reg b) :
    Fin N × Reg b :=
  (p.1, if p.2 = ZeroStr b then enc p.1
        else if p.2 = enc p.1 then ZeroStr b else p.2)

/-- Applying the address-dependent payload exchange twice returns the original address and
payload. -/
private theorem indexFlip_involutive {N b : ℕ} (enc : Fin N → Reg b) :
    Function.Involutive (indexFlip enc) := by
  intro ⟨i, r⟩
  simp only [indexFlip]
  by_cases h0 : r = ZeroStr b
  · subst h0
    by_cases he : enc i = ZeroStr b
    · simp [he]
    · simp [he]
  · by_cases he : r = enc i
    · subst he
      simp [h0]
    · simp [h0, he]

/-- The index-loading oracle is unitary for every address encoding. -/
private theorem indexLoadOracle_mem_unitaryGroup {N b : ℕ} (enc : Fin N → Reg b) :
    indexLoadOracle enc ∈ Matrix.unitaryGroup (Fin N × Reg b) ℂ := by
  have hEq : indexLoadOracle enc = permMatrix (indexFlip enc) := rfl
  rw [hEq]
  exact permMatrix_unitary (indexFlip_involutive enc)

/-- Under the address-capacity, error, and weight bounds, the sparse-support oracle, its
controlled and adjoint forms, and every index-loading oracle possess exact circuits with
zero queries and at most one arbitrary unitary gate. The sparse data also satisfy
`HasEffectiveAccess d ε 0`. -/
theorem g2 : ∀ (N b : ℕ) (d : SparseAccessData N b) (ε : ℝ),
    N ≤ 2 ^ b → 0 ≤ ε →
    (d.entries.map (fun e => ‖e.2‖ ^ 2)).sum ≤ d.weightBound →
    (∃ Csel : Circuit (Fin N × Bool), IsUnitaryCircuit Csel ∧
      QueryCount Csel = 0 ∧ GateCount Csel ≤ 1 ∧
      ∀ ψ : QState (Fin N × Bool),
        Run (1 : Matrix (Fin N × Bool) (Fin N × Bool) ℂ) Csel ψ
          = sparseValueOracle d *ᵥ ψ) ∧
    (∃ Cctl : Circuit (Bool × (Fin N × Bool)), IsUnitaryCircuit Cctl ∧
      QueryCount Cctl = 0 ∧ GateCount Cctl ≤ 1 ∧
      ∀ φ : QState (Bool × (Fin N × Bool)),
        Run (1 : Matrix (Bool × (Fin N × Bool)) (Bool × (Fin N × Bool)) ℂ) Cctl φ
          = controlledSparseValueOracle d *ᵥ φ) ∧
    (∃ Cadj : Circuit (Fin N × Bool), IsUnitaryCircuit Cadj ∧
      QueryCount Cadj = 0 ∧ GateCount Cadj ≤ 1 ∧
      ∀ ψ : QState (Fin N × Bool),
        Run (1 : Matrix (Fin N × Bool) (Fin N × Bool) ℂ) Cadj ψ
          = sparseValueOracleAdjoint d *ᵥ ψ) ∧
    (∀ enc : Fin N → Reg b,
      ∃ Cl : Circuit (Fin N × Reg b), IsUnitaryCircuit Cl ∧
        QueryCount Cl = 0 ∧ GateCount Cl ≤ 1 ∧
        ∀ χ : QState (Fin N × Reg b),
          Run (1 : Matrix (Fin N × Reg b) (Fin N × Reg b) ℂ) Cl χ
            = indexLoadOracle enc *ᵥ χ) ∧
    HasEffectiveAccess d ε 0 := by
  intro N b d ε _hNb hε _hw
  have hsel : sparseValueOracle d ∈ Matrix.unitaryGroup (Fin N × Bool) ℂ :=
    sparseValueOracle_mem_unitaryGroup d
  have hctl : controlledSparseValueOracle d
      ∈ Matrix.unitaryGroup (Bool × (Fin N × Bool)) ℂ :=
    Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary hsel
  have hadj : sparseValueOracleAdjoint d ∈ Matrix.unitaryGroup (Fin N × Bool) ℂ :=
    Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary hsel
  refine ⟨⟨[Step.gate (sparseValueOracle d)],
      (isUnitaryCircuit_gate _ []).mpr ⟨hsel, isUnitaryCircuit_nil⟩, rfl,
      le_of_eq rfl, fun _ => rfl⟩,
    ⟨[Step.gate (controlledSparseValueOracle d)],
      (isUnitaryCircuit_gate _ []).mpr ⟨hctl, isUnitaryCircuit_nil⟩, rfl,
      le_of_eq rfl, fun _ => rfl⟩,
    ⟨[Step.gate (sparseValueOracleAdjoint d)],
      (isUnitaryCircuit_gate _ []).mpr ⟨hadj, isUnitaryCircuit_nil⟩, rfl,
      le_of_eq rfl, fun _ => rfl⟩,
    fun enc => ⟨[Step.gate (indexLoadOracle enc)],
      (isUnitaryCircuit_gate _ []).mpr
        ⟨indexLoadOracle_mem_unitaryGroup enc, isUnitaryCircuit_nil⟩, rfl,
      le_of_eq rfl, fun _ => rfl⟩,
    ⟨hε, ⟨[Step.gate (sparseValueOracle d)],
      (isUnitaryCircuit_gate _ []).mpr ⟨hsel, isUnitaryCircuit_nil⟩, le_of_eq rfl,
      fun ψ => by
        rw [show Run (1 : Matrix (Fin N × Bool) (Fin N × Bool) ℂ)
            [Step.gate (sparseValueOracle d)] ψ = sparseValueOracle d *ᵥ ψ from rfl,
          sub_self, norm_zero]
        exact hε⟩,
      ⟨[Step.gate (controlledSparseValueOracle d)],
      (isUnitaryCircuit_gate _ []).mpr ⟨hctl, isUnitaryCircuit_nil⟩, le_of_eq rfl,
      fun φ => by
        rw [show Run (1 : Matrix (Bool × (Fin N × Bool)) (Bool × (Fin N × Bool)) ℂ)
            [Step.gate (controlledSparseValueOracle d)] φ
            = controlledSparseValueOracle d *ᵥ φ from rfl,
          sub_self, norm_zero]
        exact hε⟩,
      ⟨[Step.gate (sparseValueOracleAdjoint d)],
      (isUnitaryCircuit_gate _ []).mpr ⟨hadj, isUnitaryCircuit_nil⟩, le_of_eq rfl,
      fun ψ => by
        rw [show Run (1 : Matrix (Fin N × Bool) (Fin N × Bool) ℂ)
            [Step.gate (sparseValueOracleAdjoint d)] ψ
            = sparseValueOracleAdjoint d *ᵥ ψ from rfl,
          sub_self, norm_zero]
        exact hε⟩⟩⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccess
