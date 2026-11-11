/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OneWayDanos05.MainResults.FlowRewrite
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs

/-!
# Input-frame identities for MBQC flow rewrites

The register-indexed frame `inputFrame` prepares noninput qubits in the plus state. Local X
invariance and controlled-Z conjugation identities move corrections across the entangler, and
relabeling transfers these identities to `mbqcInputFrame`. These matrix equalities support the
flow correction arguments of [DanosKashefi2006].

## Main statements

* `localXGate_mul_mbqcInputFrame`: A native local X gate on a noninput wire leaves the MBQC
  input frame unchanged.
* `localZpow_mul_cz_mul_localX`: For adjacent distinct vertices in a canonical graph, a
  Boolean-controlled local Z can be moved across the entangler using the corresponding local X
  and dependent Z corrections.
* `localZ_mul_entangler_mul_mbqcInputFrame`: For adjacent distinct vertices in a canonical graph
  with noninput successor, the local Z entangler identity transfers to native MBQC operators and
  input frames.

## References

* [Danos and Kashefi, 2006][DanosKashefi2006]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical BigOperators ComplexOrder

namespace Qatlib.Papers.OneWayDanos05.MainResults

variable {n : ℕ}

/-- Left multiplication by the permutation matrix of an involution selects the matrix row
indexed by that involution. -/
theorem permMatrix_mul_apply {α β : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : Function.Involutive σ) (M : Matrix α β ℂ) (x : α) (y : β) :
    (permMatrix σ * M) x y = M (σ x) y := by
  rw [Matrix.mul_apply]
  have hsingle : ∑ j : α, (permMatrix σ) x j * M j y
      = (permMatrix σ) x (σ x) * M (σ x) y := by
    refine Finset.sum_eq_single (σ x) ?_ ?_
    · intro j _ hj
      have hne : x ≠ σ j := fun h => hj (by rw [← hσ j, ← h])
      simp [permMatrix, hne]
    · intro h
      exact absurd (Finset.mem_univ (σ x)) h
  rw [hsingle]
  simp [permMatrix, hσ x]

/-- The input embedding on bit registers, retaining input bits and assigning the normalized plus
amplitude to each noninput bit. -/
noncomputable def inputFrame (I : Finset (Fin n)) :
    Matrix (Reg n) (Fin (2 ^ I.card)) ℂ :=
  Matrix.of fun x y => ∏ v : Fin n,
    if h : v ∈ I then
      if x v = (bitVecEquiv I.card).symm y (I.equivFin ⟨v, h⟩) then (1 : ℂ) else 0
    else (Real.sqrt 2 : ℂ)⁻¹

/-- The native MBQC input frame is the row relabeling of the register-indexed input frame by
`bitVecEquiv`. -/
theorem mbqcInputFrame_eq_submatrix (I : Finset (Fin n)) :
    mbqcInputFrame I = (inputFrame I).submatrix (bitVecEquiv n).symm id := by
  ext x y
  simp [mbqcInputFrame, inputFrame]

/-- Flipping a noninput bit leaves every input-frame entry unchanged. -/
theorem inputFrame_flip (I : Finset (Fin n)) {v : Fin n} (hv : v ∉ I)
    (x : Reg n) (y : Fin (2 ^ I.card)) :
    inputFrame I (flipBit v x) y = inputFrame I x y := by
  unfold inputFrame
  simp only [Matrix.of_apply]
  refine Finset.prod_congr rfl (fun w _ => ?_)
  by_cases hw : w ∈ I
  · have hwv : w ≠ v := fun h => hv (h ▸ hw)
    have hupd : flipBit v x w = x w := by
      unfold flipBit
      exact Function.update_of_ne hwv _ x
    simp [hw, hupd]
  · simp [hw]

/-- A local X operator on a noninput wire leaves the register-indexed input frame unchanged. -/
theorem localX_mul_inputFrame (I : Finset (Fin n)) {v : Fin n} (hv : v ∉ I) :
    localX v * inputFrame I = inputFrame I := by
  ext x y
  rw [show localX v = permMatrix (flipBit v) from rfl,
    permMatrix_mul_apply (flipBit v) (flipBit_involutive v)]
  exact inputFrame_flip I hv x y

/-- The local X matrix relabeled from bit-register indices to the native finite-dimensional
operator indices. -/
noncomputable def localXGate (v : Fin n) : Operator (2 ^ n) :=
  relabelGate (bitVecEquiv n) (localX v)

/-- A native local X gate on a noninput wire leaves the MBQC input frame unchanged
[DanosKashefi2006]. -/
theorem localXGate_mul_mbqcInputFrame (I : Finset (Fin n)) {v : Fin n} (hv : v ∉ I) :
    localXGate v * mbqcInputFrame I = mbqcInputFrame I := by
  unfold localXGate
  rw [show relabelGate (bitVecEquiv n) (localX v)
      = (localX v).submatrix (bitVecEquiv n).symm (bitVecEquiv n).symm from rfl]
  rw [mbqcInputFrame_eq_submatrix I]
  rw [submatrix_mul_equiv (localX v) (inputFrame I)
    (bitVecEquiv n).symm (bitVecEquiv n).symm id]
  rw [localX_mul_inputFrame I hv]

/-- The dependent Z correction matrix squares to the identity. -/
theorem depZMatrix_mul_self (G : MbqcGraph n) (w v : Fin n) :
    depZMatrix G w v * depZMatrix G w v = 1 := by
  rw [depZMatrix, Matrix.diagonal_mul_diagonal]
  have h : (fun x : Reg n => depZVal G w v x * depZVal G w v x) = fun _ => (1 : ℂ) := by
    funext x
    exact depZVal_sq G w v x
  rw [h, Matrix.diagonal_one]

/-- A local Z matrix squares to the identity. -/
theorem localZ_mul_self (v : Fin n) : localZ v * localZ v = 1 := by
  rw [localZ, Matrix.diagonal_mul_diagonal]
  have h : (fun x : Reg n => (if x v then (-1 : ℂ) else 1) * (if x v then (-1 : ℂ) else 1))
      = fun _ => (1 : ℂ) := by
    funext x
    split_ifs <;> norm_num
  rw [h, Matrix.diagonal_one]

/-- A local X matrix squares to the identity. -/
theorem localX_mul_self (v : Fin n) : localX v * localX v = 1 := by
  rw [show localX v = permMatrix (flipBit v) from rfl]
  exact permMatrix_mul_self (flipBit_involutive v)

/-- For adjacent distinct vertices in a canonical graph, with the successor outside the inputs,
local Z after entangling the input frame equals local X times the dependent Z correction. -/
theorem localZ_mul_cz_mul_inputFrame (G : MbqcGraph n) (hcanon : mbqcCanonical G)
    (I : Finset (Fin n)) {v w : Fin n} (hvw : mbqcAdj G v w = true) (hne : v ≠ w)
    (hwI : w ∉ I) :
    localZ v * czMatrix G.edges * inputFrame I
      = localX w * depZMatrix G w v * czMatrix G.edges * inputFrame I := by
  calc localZ v * czMatrix G.edges * inputFrame I
      = (localX w * depZMatrix G w v * czMatrix G.edges * localX w) * inputFrame I := by
        rw [localZ_mul_cz_mul_localX G hcanon hvw hne]
    _ = localX w * depZMatrix G w v * czMatrix G.edges * inputFrame I := by
        rw [Matrix.mul_assoc, localX_mul_inputFrame I hwI]

/-- For adjacent distinct vertices in a canonical graph, a Boolean-controlled local Z can be
moved across the entangler using the corresponding local X and dependent Z corrections
[DanosKashefi2006]. -/
theorem localZpow_mul_cz_mul_localX (G : MbqcGraph n) (hcanon : mbqcCanonical G)
    {v w : Fin n} (hvw : mbqcAdj G v w = true) (hne : v ≠ w) (s : Bool) :
    (if s then localZ v else 1) * czMatrix G.edges
      = (if s then localX w * depZMatrix G w v else 1) * czMatrix G.edges
          * (if s then localX w else 1) := by
  cases s
  · simp
  · simpa [Matrix.mul_assoc] using localZ_mul_cz_mul_localX G hcanon hvw hne

/-- Multiplying a relabeled gate by the native input frame equals relabeling its product with
the register-indexed input frame. -/
theorem relabelGate_mul_mbqcInputFrame (I : Finset (Fin n))
    (M : Matrix (Reg n) (Reg n) ℂ) :
    relabelGate (bitVecEquiv n) M * mbqcInputFrame I
      = (M * inputFrame I).submatrix (bitVecEquiv n).symm id := by
  rw [mbqcInputFrame_eq_submatrix]
  rw [show relabelGate (bitVecEquiv n) M
      = M.submatrix (bitVecEquiv n).symm (bitVecEquiv n).symm from rfl]
  rw [submatrix_mul_equiv M (inputFrame I)
    (bitVecEquiv n).symm (bitVecEquiv n).symm id]

/-- For adjacent distinct vertices in a canonical graph with noninput successor, the local Z
entangler identity transfers to native MBQC operators and input frames [DanosKashefi2006]. -/
theorem localZ_mul_entangler_mul_mbqcInputFrame (G : MbqcGraph n)
    (hcanon : mbqcCanonical G) (I : Finset (Fin n)) {v w : Fin n}
    (hvw : mbqcAdj G v w = true) (hne : v ≠ w) (hwI : w ∉ I) :
    relabelGate (bitVecEquiv n) (localZ v) * mbqcEntangler G * mbqcInputFrame I
      = relabelGate (bitVecEquiv n) (localX w)
          * relabelGate (bitVecEquiv n) (depZMatrix G w v)
          * mbqcEntangler G * mbqcInputFrame I := by
  have hstep := localZ_mul_cz_mul_inputFrame G hcanon I hvw hne hwI
  have hL : relabelGate (bitVecEquiv n) (localZ v) * mbqcEntangler G * mbqcInputFrame I
      = (localZ v * czMatrix G.edges * inputFrame I).submatrix
          (bitVecEquiv n).symm id := by
    rw [mbqcEntangler, ← relabelGate_mul]
    exact relabelGate_mul_mbqcInputFrame I (localZ v * czMatrix G.edges)
  have hR : relabelGate (bitVecEquiv n) (localX w)
        * relabelGate (bitVecEquiv n) (depZMatrix G w v)
        * mbqcEntangler G * mbqcInputFrame I
      = (localX w * depZMatrix G w v * czMatrix G.edges * inputFrame I).submatrix
          (bitVecEquiv n).symm id := by
    rw [mbqcEntangler, ← relabelGate_mul, ← relabelGate_mul]
    exact relabelGate_mul_mbqcInputFrame I
      (localX w * depZMatrix G w v * czMatrix G.edges)
  rw [hL, hR, hstep]

end Qatlib.Papers.OneWayDanos05.MainResults
