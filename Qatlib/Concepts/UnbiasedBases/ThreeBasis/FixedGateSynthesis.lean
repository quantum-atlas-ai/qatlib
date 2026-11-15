/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Linarith
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
public import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateCompiler

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MatrixAccess.RitzPipeline Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.BinaryCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CountedTake
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StateEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Call
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.MatrixAccess.RitzPipeline

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

open scoped Kronecker

noncomputable section

namespace Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis

open Matrix
open scoped Matrix.Norms.L2Operator

open Qatlib
open Qatlib
open Qatlib

def lastWire (w : ℕ) : Fin (w + 1) := ⟨w, Nat.lt_succ_self w⟩

def liftFin {w : ℕ} (i : Fin w) : Fin (w + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

def flipAt {n : ℕ} (r : Fin n) (z : Reg n) : Reg n := fun i => if i = r then !z i else z i

/-- Flipping a register at a wire negates the bit at that wire. -/
@[simp] theorem flipAt_self {n : ℕ} (r : Fin n) (z : Reg n) : flipAt r z r = !z r := by
  show (if r = r then !z r else z r) = !z r
  rw [ite_eq_left rfl]

/-- Flipping a register at a wire preserves every other bit. -/
theorem flipAt_of_ne {n : ℕ} (r : Fin n) (z : Reg n) {j : Fin n} (h : j ≠ r) :
    flipAt r z j = z j := by
  show (if j = r then !z j else z j) = z j
  rw [ite_eq_right h]

/-- Flipping a fixed wire is an involution. -/
theorem flipAt_involutive {n : ℕ} (r : Fin n) : Function.Involutive (flipAt r) := by
  intro z
  funext j
  by_cases h : j = r
  · subst h
    simp [flipAt]
  · simp [flipAt, h]

/-- Flipping a wire changes the register. -/
theorem flipAt_ne_self {n : ℕ} (r : Fin n) (z : Reg n) : flipAt r z ≠ z := by
  intro h
  have h1 : flipAt r z r = z r := congrFun h r
  rw [flipAt_self] at h1
  cases z r <;> simp at h1

/-- Two Boolean values differ exactly when one is the negation of the other. -/
theorem bool_ne_iff_not {b c : Bool} : b ≠ c ↔ b = !c := by
  cases b <;> cases c <;> simp

/-- A Boolean value differs from the negation of another exactly when the values are equal. -/
theorem bool_ne_not_iff_eq {b c : Bool} : b ≠ !c ↔ b = c := by
  cases b <;> cases c <;> simp

def padEmbed {w : ℕ} (x : Reg w) : Reg (w + 1) :=
  fun i => if h : i.val < w then x ⟨i.val, h⟩ else false

/-- Evaluates the clean embedding matrix as the indicator of the padded register. -/
theorem cleanEmbed_apply {w : ℕ} (p : Reg (w + 1)) (x : Reg w) :
    cleanEmbed w (w + 1) p x = if p = padEmbed x then 1 else 0 := rfl

/-- Padding a register preserves its original bits at lifted wire indices. -/
theorem padEmbed_liftFin {w : ℕ} (x : Reg w) (i : Fin w) :
    padEmbed x (liftFin i) = x i := by
  show (if h : i.val < w then x ⟨i.val, h⟩ else false) = x i
  rw [dite_eq_left i.isLt]

/-- The last wire of a padded register is false. -/
theorem padEmbed_lastWire {w : ℕ} (x : Reg w) : padEmbed x (lastWire w) = false := by
  show (if h : (lastWire w).val < w then x ⟨(lastWire w).val, h⟩ else false) = false
  rw [dite_eq_right (by simp [lastWire])]

/-- Padding registers is injective. -/
theorem padEmbed_injective {w : ℕ} : Function.Injective (padEmbed (w := w)) := by
  intro x y h
  funext i
  have h1 := congrFun h (liftFin i)
  rw [padEmbed_liftFin, padEmbed_liftFin] at h1
  exact h1

/-- Registers agreeing away from one wire are either equal or related by a flip at that wire. -/
theorem agree_cases {n : ℕ} (r : Fin n) (y x : Reg n)
    (h : ∀ j : Fin n, j ≠ r → y j = x j) : y = x ∨ y = flipAt r x := by
  by_cases hy : y r = x r
  · left
    funext j
    by_cases hj : j = r
    · subst hj; exact hy
    · exact h j hj
  · right
    funext j
    by_cases hj : j = r
    · rw [hj]
      have hflip : y r = !x r := by
        cases hv : y r <;> cases hw : x r <;> simp_all
      show y r = flipAt r x r
      rw [flipAt_self, hflip]
    · show y j = flipAt r x j
      rw [flipAt_of_ne r x hj]
      exact h j hj

/-- Reduces a sum sandwiched between Hadamard entries to the two registers agreeing off the
selected wire. -/
theorem hmul_sum {n : ℕ} (r : Fin n) (y x : Reg n) (F : Reg n → ℂ) :
    ∑ z : Reg n, localGateMatrix (.h r) y z * F z * localGateMatrix (.h r) z x
      = if (∀ j : Fin n, j ≠ r → y j = x j) then
          Hadamard (y r) (x r) * F x * Hadamard (x r) (x r)
            + Hadamard (y r) (!(x r)) * F (flipAt r x) * Hadamard (!(x r)) (x r)
        else 0 := by
  have hterm : ∀ z : Reg n, localGateMatrix (.h r) y z * F z * localGateMatrix (.h r) z x
      = if (∀ j : Fin n, j ≠ r → z j = x j) then
          (if (∀ j : Fin n, j ≠ r → y j = z j)
            then Hadamard (y r) (z r) * F z * Hadamard (z r) (x r) else 0) else 0 := by
    intro z
    rw [localGateMatrix_h, localGateMatrix_h]
    split_ifs <;> first | rfl | ring
  by_cases hyx : ∀ j : Fin n, j ≠ r → y j = x j
  · rw [ite_eq_left hyx]
    have hrewrite : ∀ z : Reg n, localGateMatrix (.h r) y z * F z * localGateMatrix (.h r) z x
        = if (∀ j : Fin n, j ≠ r → z j = x j) then
            Hadamard (y r) (z r) * F z * Hadamard (z r) (x r) else 0 := by
      intro z
      rw [hterm z]
      by_cases hz : ∀ j : Fin n, j ≠ r → z j = x j
      · rw [ite_eq_left hz, ite_eq_left (fun j hj => (hyx j hj).trans (hz j hj).symm), ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz]
    rw [Finset.sum_congr rfl (fun z _ => hrewrite z)]
    have hset : (Finset.univ.filter (fun z : Reg n => ∀ j : Fin n, j ≠ r → z j = x j)
        : Finset (Reg n)) = {x, flipAt r x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact ⟨fun hz => agree_cases r z x hz, fun hz => by
        rcases hz with rfl | rfl
        · intro _ _; rfl
        · intro j hj; rw [flipAt_of_ne r x hj]⟩
    rw [← Finset.sum_filter, hset, Finset.sum_pair (Ne.symm (flipAt_ne_self r x)),
      flipAt_self]
  · rw [ite_eq_right hyx]
    have hzero : ∀ z : Reg n,
        localGateMatrix (.h r) y z * F z * localGateMatrix (.h r) z x = 0 := by
      intro z
      rw [hterm z]
      by_cases hz : ∀ j : Fin n, j ≠ r → z j = x j
      · rw [ite_eq_left hz, ite_eq_right (fun hyz => hyx (fun j hj => (hyz j hj).trans (hz j hj)))]
      · simp only [ite_eq_right hz]
    rw [Finset.sum_congr rfl (fun z _ => hzero z)]
    exact Finset.sum_const_zero

/-- The product of two complex inverse square roots of two is one half. -/
theorem inv_sqrt2_mul_self :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← sq, sqrt2_sq]

def cnotUpdate {n : ℕ} (ctl tgt : Fin n) (z : Reg n) : Reg n :=
  fun i => if i = tgt then (z ctl != z tgt) else z i

def cnotWord {n : ℕ} (ctl tgt : Fin n) : List (LocalQFTGate n) :=
  [.h tgt, .cp ctl tgt 1 false, .h tgt]

/-- The CNOT word has length three. -/
theorem cnotWord_length {n : ℕ} (ctl tgt : Fin n) : (cnotWord ctl tgt).length = 3 := rfl

/-- Every gate in the CNOT word is a fixed primitive. -/
theorem cnotWord_legal {n : ℕ} (ctl tgt : Fin n) :
    ∀ g ∈ cnotWord ctl tgt, IsFixedPrim g := by
  intro g hg
  simp only [cnotWord, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp [IsFixedPrim]

/-- A CNOT update preserves bits away from its target. -/
theorem cnotUpdate_off {n : ℕ} (ctl tgt : Fin n) (z : Reg n) {j : Fin n} (h : j ≠ tgt) :
    cnotUpdate ctl tgt z j = z j := by
  show (if j = tgt then _ else z j) = z j
  rw [ite_eq_right h]

/-- A CNOT update with distinct control and target is an involution. -/
theorem cnotUpdate_involutive {n : ℕ} (ctl tgt : Fin n) (h : ctl ≠ tgt) :
    Function.Involutive (cnotUpdate ctl tgt) := by
  intro z
  funext j
  by_cases hj : j = tgt
  · rw [hj]
    show (if tgt = tgt then ((cnotUpdate ctl tgt z) ctl != (cnotUpdate ctl tgt z) tgt)
        else (cnotUpdate ctl tgt z) tgt) = z tgt
    rw [ite_eq_left rfl, cnotUpdate_off ctl tgt z h]
    have hc : cnotUpdate ctl tgt z tgt = (z ctl != z tgt) := by
      show (if tgt = tgt then (z ctl != z tgt) else z tgt) = _
      rw [ite_eq_left rfl]
    rw [hc]
    cases hzc : z ctl <;> cases hzt : z tgt <;> simp
  · show (if j = tgt then _ else (cnotUpdate ctl tgt z) j) = z j
    rw [ite_eq_right hj, cnotUpdate_off ctl tgt z hj]

/-- For registers agreeing away from the target, equality with the CNOT update is equivalent to
the target XOR condition. -/
theorem eq_cnotUpdate_iff {n : ℕ} (ctl tgt : Fin n) (hct : ctl ≠ tgt)
    (y x : Reg n) (hyx : ∀ j : Fin n, j ≠ tgt → y j = x j) :
    y = cnotUpdate ctl tgt x ↔ y tgt = (x ctl != x tgt) := by
  constructor
  · intro h
    have := congrFun h tgt
    rw [cnotUpdate, ite_eq_left rfl] at this
    exact this
  · intro h
    funext j
    by_cases hj : j = tgt
    · rw [hj, cnotUpdate, ite_eq_left rfl, h]
    · rw [cnotUpdate_off ctl tgt x hj, hyx j hj]

/-- The CNOT word implements the permutation matrix of the CNOT update for distinct control and
target. -/
theorem cnotWord_matrix {n : ℕ} (ctl tgt : Fin n) (hct : ctl ≠ tgt) :
    localProgramMatrix (cnotWord ctl tgt) = permMatrix (cnotUpdate ctl tgt) := by
  ext y x
  have hexp : Complex.exp (dyadicPhaseAngle 1 false * Complex.I) = -1 := by
    have h : dyadicPhaseAngle 1 false = Real.pi := by
      simp only [dyadicPhaseAngle]
      norm_num
    rw [h, Complex.exp_pi_mul_I]
  have hsplit : (localProgramMatrix (cnotWord ctl tgt)) y x
      = ∑ z : Reg n, localGateMatrix (.h tgt) y z
          * (fun z : Reg n =>
              if z ctl && z tgt then Complex.exp (dyadicPhaseAngle 1 false * Complex.I) else 1) z
          * localGateMatrix (.h tgt) z x := by
    simp only [cnotWord, localProgramMatrix_cons, localProgramMatrix_cons,
      localProgramMatrix_nil, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have hmid : (localGateMatrix (.cp ctl tgt 1 false) * localGateMatrix (.h tgt)) z x
        = (if z ctl && z tgt then Complex.exp (dyadicPhaseAngle 1 false * Complex.I) else 1)
            * localGateMatrix (.h tgt) z x := by
      simp only [localGateMatrix]
      exact Matrix.diagonal_mul _ _ z x
    rw [hmid, mul_assoc]
  rw [hsplit, hmul_sum tgt y x _]
  by_cases hyx : ∀ j : Fin n, j ≠ tgt → y j = x j
  · rw [ite_eq_left hyx, permMatrix, Matrix.of_apply]
    simp only [eq_cnotUpdate_iff ctl tgt hct y x hyx]
    have hFexp : ∀ z : Reg n,
        (if z ctl && z tgt then Complex.exp (dyadicPhaseAngle 1 false * Complex.I) else 1 : ℂ)
          = if z ctl && z tgt then -1 else 1 := by
      intro z
      by_cases h : z ctl && z tgt <;> simp [h, hexp]
    have hdflip : (flipAt tgt x) ctl = x ctl := flipAt_of_ne tgt x hct
    rw [hFexp x, hFexp (flipAt tgt x), hdflip, flipAt_self]
    rcases hxc : x ctl <;> rcases hxt : x tgt <;> rcases hyt : y tgt <;>
      simp only [Hadamard, Matrix.of_apply, hxc, hxt, hyt, Bool.false_and, Bool.true_and,
        Bool.and_false, Bool.and_self, Bool.not_true, Bool.not_false] <;>
      first
        | rfl
        | norm_num [inv_sqrt2_mul_self]
  · rw [ite_eq_right hyx, permMatrix, Matrix.of_apply]
    rw [ite_eq_right (fun h => hyx (fun j hj => by
      rw [h]
      exact cnotUpdate_off ctl tgt x hj))]

/-- Conjugating a diagonal matrix by an involutive permutation matrix permutes its diagonal
entries. -/
theorem perm_diag_perm {I : Type*} [Fintype I] [DecidableEq I] {σ : I → I}
    (hσ : Function.Involutive σ) (d : I → ℂ) :
    permMatrix σ * Matrix.diagonal d * permMatrix σ = Matrix.diagonal (fun i => d (σ i)) := by
  ext y x
  have h1 : ∀ z : I, (permMatrix σ * Matrix.diagonal d) y z
      = (if y = σ z then d z else 0) := by
    intro z
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single z (fun w _ hw => by
      simp only [permMatrix, Matrix.of_apply, Matrix.diagonal_apply]
      rw [ite_eq_right hw, mul_zero])
      (fun hz => by exact absurd (Finset.mem_univ z) hz)]
    simp only [permMatrix, Matrix.of_apply, Matrix.diagonal_apply, ite_eq_left rfl]
    by_cases hy : y = σ z <;> simp [hy]
  have h2 : ∑ z : I, (permMatrix σ * Matrix.diagonal d) y z * permMatrix σ z x
      = (if y = σ (σ x) then d (σ x) else 0) := by
    simp only [h1]
    rw [Finset.sum_eq_single (σ x) (fun w _ hw => by
      simp only [permMatrix, Matrix.of_apply]
      rw [ite_eq_right hw, mul_zero])
      (fun hz => by exact absurd (Finset.mem_univ (σ x)) hz)]
    by_cases hy : y = σ (σ x) <;> simp [permMatrix, Matrix.of_apply, hy]
  rw [Matrix.mul_apply, h2, hσ x]
  simp only [Matrix.diagonal_apply]
  by_cases hy : y = x <;> simp [hy]

/-- Conjugating a conditional sign diagonal by Hadamard implements the corresponding conditional
bit flip. -/
theorem h_diag_h_perm {n : ℕ} (r : Fin n) (cond : Reg n → Bool)
    (hcond : ∀ z : Reg n, cond (flipAt r z) = cond z)
    (dval : Reg n → ℂ)
    (hd : ∀ z : Reg n, dval z = if cond z then (if z r then -1 else 1 : ℂ) else 1) :
    localGateMatrix (.h r) * Matrix.diagonal dval * localGateMatrix (.h r)
      = permMatrix (fun z => if cond z then flipAt r z else z) := by
  ext y x
  have hentry : (localGateMatrix (.h r) * Matrix.diagonal dval * localGateMatrix (.h r)) y x
      = ∑ z : Reg n, localGateMatrix (.h r) y z * dval z * localGateMatrix (.h r) z x := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Matrix.diagonal_mul, mul_assoc]
  rw [hentry, hmul_sum r y x dval, hd x]
  have hdf : dval (flipAt r x) = if cond x then (if !(x r) then -1 else 1 : ℂ) else 1 := by
    rw [hd (flipAt r x), hcond, flipAt_self]
  rw [hdf]
  by_cases hyx : ∀ j : Fin n, j ≠ r → y j = x j
  · rw [ite_eq_left hyx]
    have hfix : y = x ↔ y r = x r := by
      constructor
      · intro h; exact congrFun h r
      · intro h
        funext j
        by_cases hj : j = r
        · rw [hj, h]
        · rw [hyx j hj]
    have hfl : y = flipAt r x ↔ y r = !(x r) := by
      constructor
      · intro h
        have h1 := congrFun h r
        rw [flipAt_self] at h1
        exact h1
      · intro h
        funext j
        by_cases hj : j = r
        · rw [hj, flipAt_self, h]
        · rw [flipAt_of_ne r x hj, hyx j hj]
    simp only [permMatrix, Matrix.of_apply]
    rcases Bool.eq_false_or_eq_true (cond x) with hc | hc
    · simp only [ite_eq_left hc]
      by_cases hyfl : y = flipAt r x
      · rw [ite_eq_left hyfl]
        have hyy : y r = !(x r) := hfl.mp hyfl
        rcases hxr : x r <;>
          simp [Hadamard, hc, hyy, hxr] <;> norm_num [inv_sqrt2_mul_self]
      · rw [ite_eq_right hyfl]
        have hyy : y r = x r := bool_ne_not_iff_eq.mp (fun h => hyfl (hfl.mpr h))
        rcases hxr : x r <;> simp [Hadamard, hc, hyy, hxr]
    · simp only [ite_eq_right (show ¬(cond x = true) from by simp [hc])]
      by_cases hyxeq : y = x
      · rw [ite_eq_left hyxeq]
        have hyy : y r = x r := congrFun hyxeq r
        rcases hxr : x r <;>
          simp [Hadamard, hc, hyy, hxr] <;> norm_num [inv_sqrt2_mul_self]
      · rw [ite_eq_right hyxeq]
        have hyy : y r = !(x r) := bool_ne_iff_not.mp (fun h => hyxeq (hfix.mpr h))
        rcases hxr : x r <;> simp [Hadamard, hc, hyy, hxr]
  · rw [ite_eq_right hyx]
    have h' : (permMatrix (fun z : Reg n => if cond z then flipAt r z else z)) y x = 0 := by
      simp only [permMatrix, Matrix.of_apply]
      refine ite_eq_right ?_
      intro h
      refine hyx (fun j hj => ?_)
      rcases Bool.eq_false_or_eq_true (cond x) with hcond | hcond
      · rw [ite_eq_left hcond] at h
        have h1 := congrFun h j
        rw [flipAt_of_ne r x hj] at h1
        exact h1
      · rw [ite_eq_right (show ¬(cond x = true) from by simp [hcond])] at h
        exact congrFun h j
    rw [h']

/-- The positive dyadic phase at exponent two is the imaginary unit. -/
theorem exp_dyadicAngle_two_false :
    Complex.exp (dyadicPhaseAngle 2 false * Complex.I) = Complex.I := by
  have h : dyadicPhaseAngle 2 false = Real.pi / 2 := by
    simp only [dyadicPhaseAngle]
    rw [ite_eq_right (show ¬((false : Bool) = true) from by decide)]
    ring
  rw [h, Complex.ofReal_div]
  push_cast
  exact Complex.exp_pi_div_two_mul_I

/-- The negative dyadic phase at exponent two is the negative imaginary unit. -/
theorem exp_dyadicAngle_two_true :
    Complex.exp (dyadicPhaseAngle 2 true * Complex.I) = -Complex.I := by
  have h : dyadicPhaseAngle 2 true = -(Real.pi / 2) := by
    simp only [dyadicPhaseAngle]
    rw [ite_eq_left trivial]
    ring
  rw [h, Complex.ofReal_neg, Complex.ofReal_div]
  push_cast
  rw [neg_mul, Complex.exp_neg, Complex.exp_pi_div_two_mul_I]
  simp

/-- A lifted original wire is distinct from the last wire. -/
theorem liftFin_ne_lastWire {w : ℕ} (i : Fin w) : liftFin i ≠ lastWire w := by
  intro h
  have hv : i.val = w := by simpa [liftFin, lastWire] using h
  have hlt := i.isLt
  omega

/-- Lifting wire indices is injective. -/
theorem liftFin_injective {w : ℕ} : Function.Injective (liftFin (w := w)) := by
  intro i j h
  have hv : i.val = j.val := by simpa [liftFin] using h
  exact Fin.ext hv

/-- The controlled phase matrix is diagonal with its phase applied exactly when both selected
bits are true. -/
theorem cp_matrix_diag {n : ℕ} (a c : Fin n) (e : ℕ) (neg : Bool) :
    localGateMatrix (.cp a c e neg)
      = Matrix.diagonal (fun z : Reg n =>
          if z a && z c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1) := rfl

/-- Multiplying diagonal matrices multiplies their diagonal entries pointwise. -/
theorem diag_mul_diag {I : Type*} [Fintype I] [DecidableEq I] (d e : I → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal fun i => d i * e i := by
  ext x y
  rw [Matrix.diagonal_mul, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : x = y <;> simp [h]

/-- Reassociates a product of four matrices with the stated ordering. -/
theorem mul_mid_assoc {I : Type*} [Fintype I] (A B C D : Matrix I I ℂ) :
    ((A * C) * D) * B = A * (C * D * B) := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc C D B]

def andUpdate {w : ℕ} (a c : Fin w) : Reg (w + 1) → Reg (w + 1) :=
  fun z => if z (liftFin a) && z (liftFin c) then flipAt (lastWire w) z else z

/-- The AND update flips the last wire exactly when both selected original bits are true. -/
theorem andUpdate_eq {w : ℕ} (a c : Fin w) (z : Reg (w + 1)) :
    andUpdate a c z
      = if z (liftFin a) && z (liftFin c) then flipAt (lastWire w) z else z := rfl

/-- The AND update preserves every bit away from the last wire. -/
theorem andUpdate_off {w : ℕ} (a c : Fin w) (z : Reg (w + 1)) {j : Fin (w + 1)}
    (hj : j ≠ lastWire w) : andUpdate a c z j = z j := by
  rw [andUpdate_eq]
  by_cases h : z (liftFin a) && z (liftFin c)
  · rw [ite_eq_left h, flipAt_of_ne _ _ hj]
  · rw [ite_eq_right h]

/-- The AND update is an involution. -/
theorem andUpdate_involutive {w : ℕ} (a c : Fin w) :
    Function.Involutive (andUpdate a c) := by
  intro z
  have hfa : (flipAt (lastWire w) z) (liftFin a) = z (liftFin a) :=
    flipAt_of_ne _ _ (liftFin_ne_lastWire a)
  have hfc : (flipAt (lastWire w) z) (liftFin c) = z (liftFin c) :=
    flipAt_of_ne _ _ (liftFin_ne_lastWire c)
  by_cases h : z (liftFin a) && z (liftFin c)
  · have hf : flipAt (lastWire w) z (liftFin a) && flipAt (lastWire w) z (liftFin c) := by
      rw [hfa, hfc]; exact h
    have hin : andUpdate a c z = flipAt (lastWire w) z := by
      rw [andUpdate_eq, ite_eq_left h]
    rw [hin, andUpdate_eq, ite_eq_left hf]
    exact flipAt_involutive (lastWire w) z
  · have hf : ¬(flipAt (lastWire w) z (liftFin a) && flipAt (lastWire w) z (liftFin c)) := by
      rw [hfa, hfc]; exact h
    have hin : andUpdate a c z = z := by
      rw [andUpdate_eq, ite_eq_right h]
    rw [hin, hin]

/-- A CNOT from an original wire to the last wire equals the AND update with both controls
equal, evaluated on a register. -/
theorem cnotUpdate_eq_andUpdate_self {w : ℕ} (a : Fin w) (z : Reg (w + 1)) :
    cnotUpdate (liftFin a) (lastWire w) z = andUpdate a a z := by
  funext j
  rw [andUpdate_eq]
  by_cases hj : j = lastWire w
  · subst hj
    show (if lastWire w = lastWire w then (z (liftFin a) != z (lastWire w)) else z (lastWire w))
        = (if z (liftFin a) && z (liftFin a)
            then flipAt (lastWire w) z else z) (lastWire w)
    rw [ite_eq_left rfl]
    by_cases ha : z (liftFin a) <;> simp [ha]
  · rw [cnotUpdate_off _ _ z hj]
    by_cases haa : z (liftFin a) && z (liftFin a)
    · rw [ite_eq_left haa, flipAt_of_ne _ _ hj]
    · rw [ite_eq_right haa]

/-- A CNOT from an original wire to the last wire is the AND update with repeated control. -/
theorem cnotUpdate_eq_andUpdate_self' {w : ℕ} (a : Fin w) :
    cnotUpdate (liftFin a) (lastWire w) = andUpdate a a :=
  funext (cnotUpdate_eq_andUpdate_self a)

def tofMid {w : ℕ} (a c : Fin w) : List (LocalQFTGate (w + 1)) :=
  cnotWord (liftFin a) (liftFin c)
    ++ [.cp (liftFin c) (lastWire w) 2 true]
    ++ cnotWord (liftFin a) (liftFin c)
    ++ [.cp (liftFin a) (lastWire w) 2 false, .cp (liftFin c) (lastWire w) 2 false]

def tofWord {w : ℕ} (a c : Fin w) : List (LocalQFTGate (w + 1)) :=
  [.h (lastWire w)] ++ tofMid a c ++ [.h (lastWire w)]

/-- The Toffoli word has length eleven. -/
theorem tofWord_length {w : ℕ} (a c : Fin w) : (tofWord a c).length = 11 := rfl

/-- Every gate in the Toffoli word is a fixed primitive. -/
theorem tofWord_legal {w : ℕ} (a c : Fin w) : ∀ g ∈ tofWord a c, IsFixedPrim g := by
  intro g hg
  simp only [tofWord, tofMid, cnotWord, List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false, or_assoc] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [IsFixedPrim]

/-- Hadamard gates surrounding a word give the corresponding Hadamard sandwich of its program
matrix. -/
theorem h_sandwich {n : ℕ} (r : Fin n) (L : List (LocalQFTGate n)) :
    localProgramMatrix ([.h r] ++ L ++ [.h r])
      = localGateMatrix (.h r) * localProgramMatrix L * localGateMatrix (.h r) := by
  simp only [localProgramMatrix_append, localProgramMatrix_cons, localProgramMatrix_nil,
    Matrix.one_mul]
  rw [Matrix.mul_assoc]

/-- Conjugating a diagonal matrix by an involutive permutation permutes the diagonal, with the
displayed association. -/
theorem perm_diag_perm' {I : Type*} [Fintype I] [DecidableEq I] {σ : I → I}
    (hσ : Function.Involutive σ) (d : I → ℂ) :
    permMatrix σ * (Matrix.diagonal d * permMatrix σ) = Matrix.diagonal fun i => d (σ i) := by
  rw [← Matrix.mul_assoc]
  exact perm_diag_perm hσ d

/-- The Toffoli word implements the AND update permutation when its controls are distinct. -/
theorem tofWord_matrix {w : ℕ} (a c : Fin w) (hac : a ≠ c) :
    localProgramMatrix (tofWord a c) = permMatrix (andUpdate a c) := by
  have hA : liftFin a ≠ liftFin c := fun h => hac (liftFin_injective h)
  have hCt : liftFin c ≠ lastWire w := liftFin_ne_lastWire c
  have hCm : localProgramMatrix (cnotWord (liftFin a) (liftFin c))
      = permMatrix (cnotUpdate (liftFin a) (liftFin c)) := cnotWord_matrix _ _ hA
  have hPm : localProgramMatrix [.cp (liftFin c) (lastWire w) 2 true]
      = Matrix.diagonal (fun z : Reg (w + 1) =>
          if z (liftFin c) && z (lastWire w) then -Complex.I else 1) := by
    rw [localProgramMatrix_cons, localProgramMatrix_nil, Matrix.one_mul, cp_matrix_diag,
      exp_dyadicAngle_two_true]
  have hSm : localProgramMatrix
      [.cp (liftFin a) (lastWire w) 2 false, .cp (liftFin c) (lastWire w) 2 false]
      = Matrix.diagonal (fun z : Reg (w + 1) =>
          (if z (liftFin c) && z (lastWire w) then Complex.I else 1)
            * (if z (liftFin a) && z (lastWire w) then Complex.I else 1)) := by
    rw [localProgramMatrix_cons, localProgramMatrix_cons, localProgramMatrix_nil,
      Matrix.one_mul, cp_matrix_diag, cp_matrix_diag, exp_dyadicAngle_two_false]
    exact diag_mul_diag _ _
  have hmid : localProgramMatrix (tofMid a c)
      = Matrix.diagonal (fun z : Reg (w + 1) =>
          if z (liftFin a) && z (liftFin c) && z (lastWire w) then -1 else 1) := by
    rw [tofMid, localProgramMatrix_append, localProgramMatrix_append,
      localProgramMatrix_append, hCm, hPm, hSm]
    rw [perm_diag_perm' (cnotUpdate_involutive (liftFin a) (liftFin c) hA) _, diag_mul_diag]
    refine Matrix.ext fun z z' => ?_
    simp only [Matrix.diagonal_apply]
    by_cases hzz : z = z'
    · subst hzz
      simp only [ite_eq_left rfl]
      have hsC : cnotUpdate (liftFin a) (liftFin c) z (liftFin c)
          = (z (liftFin a) != z (liftFin c)) := by
        show (if liftFin c = liftFin c then _ else _) = _
        rw [ite_eq_left rfl]
      have hsT : cnotUpdate (liftFin a) (liftFin c) z (lastWire w) = z (lastWire w) :=
        cnotUpdate_off _ _ z (Ne.symm hCt)
      rw [hsC, hsT]
      rcases ht : z (lastWire w) <;> rcases ha : z (liftFin a) <;>
        rcases hcc : z (liftFin c) <;>
        simp [ha, hcc, ht, Complex.I_mul_I]
    · rw [ite_eq_right hzz, ite_eq_right hzz]
  rw [tofWord, h_sandwich, hmid]
  refine h_diag_h_perm (lastWire w) (fun z : Reg (w + 1) => z (liftFin a) && z (liftFin c))
    ?_ (fun z : Reg (w + 1) =>
      if z (liftFin a) && z (liftFin c) && z (lastWire w) then -1 else 1) ?_
  · intro z
    simp only [flipAt_of_ne (lastWire w) z (liftFin_ne_lastWire a),
      flipAt_of_ne (lastWire w) z (liftFin_ne_lastWire c)]
  · intro z
    rcases ht : z (lastWire w) <;> rcases ha : z (liftFin a) <;> rcases hcc : z (liftFin c) <;>
      simp [ha, hcc, ht]

def andWord {w : ℕ} (a c : Fin w) : List (LocalQFTGate (w + 1)) :=
  if a = c then cnotWord (liftFin a) (lastWire w) else tofWord a c

/-- The AND word implements the AND update permutation for any pair of controls. -/
theorem andWord_matrix {w : ℕ} (a c : Fin w) :
    localProgramMatrix (andWord a c) = permMatrix (andUpdate a c) := by
  by_cases hac : a = c
  · subst hac
    rw [andWord, ite_eq_left rfl, cnotWord_matrix _ _ (liftFin_ne_lastWire a),
      cnotUpdate_eq_andUpdate_self']
  · rw [andWord, ite_eq_right hac, tofWord_matrix _ _ hac]

/-- Every gate in the AND word is a fixed primitive. -/
theorem andWord_legal {w : ℕ} (a c : Fin w) : ∀ g ∈ andWord a c, IsFixedPrim g := by
  by_cases hac : a = c
  · subst hac
    rw [andWord, ite_eq_left rfl]
    exact cnotWord_legal _ _
  · rw [andWord, ite_eq_right hac]
    exact tofWord_legal _ _

/-- The AND word has length at most eleven. -/
theorem andWord_length {w : ℕ} (a c : Fin w) : (andWord a c).length ≤ 11 := by
  by_cases hac : a = c
  · subst hac
    rw [andWord, ite_eq_left rfl, cnotWord_length]
    norm_num
  · rw [andWord, ite_eq_right hac, tofWord_length]

/-- The sole element of the finite type with one element is zero. -/
theorem fin1_eq (j : Fin 1) : j = ⟨0, by omega⟩ := Fin.ext (by omega)

/-- A one-wire register is either constantly false or constantly true. -/
theorem reg1_cases (z : Reg 1) : z = (fun _ => false) ∨ z = (fun _ => true) := by
  by_cases h : z ⟨0, by omega⟩
  · right
    funext j
    rw [fin1_eq j]
    exact h
  · left
    funext j
    rw [fin1_eq j]
    rcases hb : z ⟨0, by omega⟩
    · rfl
    · exact absurd hb h

/-- Constant one-wire registers are equal exactly when their Boolean values are equal. -/
theorem reg1_const_eq (b c : Bool) :
    (fun _ : Fin 1 => b) = (fun _ => c) ↔ b = c := by
  constructor
  · intro h
    exact congrFun h ⟨0, by omega⟩
  · intro h
    funext j
    exact h

/-- A sum over one-wire registers is the sum of its values on the two constant registers. -/
theorem sum_reg1 (f : Reg 1 → ℂ) :
    ∑ z : Reg 1, f z = f (fun _ => false) + f (fun _ => true) := by
  have hset : (Finset.univ : Finset (Reg 1))
      = {fun _ => true, fun _ => false} := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
    rcases reg1_cases z with rfl | rfl <;> simp
  rw [hset, Finset.sum_pair (by
    intro h
    have h1 := congrFun h ⟨0, by omega⟩
    simp at h1)]
  exact add_comm _ _

/-- Splits a sum over registers into the cases where the last wire is false and true. -/
theorem sum_reg_succ {w : ℕ} (f : Reg (w + 1) → ℂ) :
    ∑ y : Reg (w + 1), f y
      = ∑ s : Reg w, (f (padEmbed s) + f (flipAt (lastWire w) (padEmbed s))) := by
  classical
  have hrow : ∀ y : Reg (w + 1),
      y = (if y (lastWire w) then flipAt (lastWire w) (padEmbed (fun i => y (liftFin i)))
        else padEmbed (fun i => y (liftFin i))) := by
    intro y
    rcases hy : y (lastWire w)
    · funext j
      by_cases hj : j = lastWire w
      · rw [hj, ite_eq_right (by simp [hy]), padEmbed_lastWire, hy]
      · rw [ite_eq_right (by simp [hy])]
        have hjv : j.val ≠ w := by
          intro h
          exact hj (by rw [lastWire]; exact Fin.ext h)
        obtain ⟨i, rfl⟩ : ∃ i : Fin w, j = liftFin i :=
          ⟨⟨j.val, by have := j.isLt; omega⟩, by simp [liftFin]⟩
        rw [padEmbed_liftFin]
    · funext j
      by_cases hj : j = lastWire w
      · rw [hj, ite_eq_left (by simp [hy]), flipAt_self, hy, padEmbed_lastWire]
        rfl
      · rw [ite_eq_left (by simp [hy]), flipAt_of_ne _ _ hj]
        have hjv : j.val ≠ w := by
          intro h
          exact hj (by rw [lastWire]; exact Fin.ext h)
        obtain ⟨i, rfl⟩ : ∃ i : Fin w, j = liftFin i :=
          ⟨⟨j.val, by have := j.isLt; omega⟩, by simp [liftFin]⟩
        rw [padEmbed_liftFin]
  have hl : ∀ s : Reg w, ∀ b : Bool,
      (if b then flipAt (lastWire w) (padEmbed s) else padEmbed s) (lastWire w) = b := by
    intro s b
    rcases b
    · rw [ite_eq_right (by decide), padEmbed_lastWire]
    · rw [ite_eq_left (by decide), flipAt_self, padEmbed_lastWire]
      rfl
  have hd : ∀ s : Reg w, ∀ b : Bool, ∀ i : Fin w,
      (if b then flipAt (lastWire w) (padEmbed s) else padEmbed s) (liftFin i) = s i := by
    intro s b i
    rcases b
    · rw [ite_eq_right (by decide), padEmbed_liftFin]
    · rw [ite_eq_left (by decide), flipAt_of_ne _ _ (liftFin_ne_lastWire i), padEmbed_liftFin]
  have hbij : Function.Bijective (fun p : Reg w × Bool =>
      if p.2 then flipAt (lastWire w) (padEmbed p.1) else padEmbed p.1) := by
    constructor
    · rintro ⟨s1, b1⟩ ⟨s2, b2⟩ h
      have h1 : (if b1 then flipAt (lastWire w) (padEmbed s1) else padEmbed s1) (lastWire w)
          = (if b2 then flipAt (lastWire w) (padEmbed s2) else padEmbed s2) (lastWire w) :=
        congrFun h (lastWire w)
      rw [hl s1 b1, hl s2 b2] at h1
      have hs : s1 = s2 := by
        funext i
        have h2 : (if b1 then flipAt (lastWire w) (padEmbed s1) else padEmbed s1) (liftFin i)
            = (if b2 then flipAt (lastWire w) (padEmbed s2) else padEmbed s2) (liftFin i) :=
          congrFun h (liftFin i)
        rw [hd s1 b1 i, hd s2 b2 i] at h2
        exact h2
      rw [hs, h1]
    · intro y
      refine ⟨((fun i => y (liftFin i)), y (lastWire w)), ?_⟩
      exact (hrow y).symm
  have hbool : ∀ (F : Bool → ℂ), ∑ b : Bool, F b = F false + F true := by
    intro F
    have hset : (Finset.univ : Finset Bool) = {false, true} := by
      ext b
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
      rcases b <;> simp
    rw [hset, Finset.sum_pair (by decide)]
  rw [← Equiv.sum_comp (Equiv.ofBijective _ hbij) f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun s _ => hbool (fun b =>
    f (if b then flipAt (lastWire w) (padEmbed s) else padEmbed s)))

def liftToWire {n : ℕ} (i : Fin n) : LocalQFTGate 1 → LocalQFTGate n
  | .h _ => .h i
  | .cp _ _ e neg => .cp i i e neg
  | .swap _ _ => .swap i i

/-- Lifting a one-wire fixed primitive to a selected wire preserves the fixed primitive
property. -/
theorem liftToWire_legal {n : ℕ} (i : Fin n) (g : LocalQFTGate 1) (hg : IsFixedPrim g) :
    IsFixedPrim (liftToWire i g) := by
  cases g with
  | h a => simp [IsFixedPrim, liftToWire]
  | cp a c e neg => simp only [liftToWire, IsFixedPrim]; exact hg
  | swap a c => simp [IsFixedPrim, liftToWire]

/-- Evaluates the matrix entries of a lifted Hadamard gate using agreement off the selected
wire. -/
theorem localGateMatrix_lift_h {n : ℕ} (i : Fin n) (a : Fin 1) (y x : Reg n) :
    localGateMatrix (liftToWire i (.h a)) y x =
      if (∀ j : Fin n, j ≠ i → y j = x j) then Hadamard (y i) (x i) else 0 := rfl

/-- Evaluates a lifted one-wire controlled phase as a diagonal phase on the selected bit. -/
theorem localGateMatrix_lift_cp {n : ℕ} (i : Fin n) (a c : Fin 1) (e : ℕ) (neg : Bool)
    (y x : Reg n) :
    localGateMatrix (liftToWire i (.cp a c e neg)) y x =
      if y = x then (if y i then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)
        else 0 := by
  simp only [liftToWire]
  rw [localGateMatrix_cp]
  simp only [Bool.and_self]

/-- A lifted one-wire swap has the identity matrix. -/
theorem localGateMatrix_lift_swap {n : ℕ} (i : Fin n) (a c : Fin 1) (y x : Reg n) :
    localGateMatrix (liftToWire i (.swap a c)) y x = if y = x then 1 else 0 := by
  have hfun : (fun k : Fin n => x (Equiv.swap i i k)) = x := by
    funext k
    simp [Equiv.swap_self]
  simp only [liftToWire, localGateMatrix_swap]
  rw [hfun]

/-- A nonzero matrix entry of a lifted one-wire gate forces agreement at every other wire. -/
theorem lift_entry_agree {n : ℕ} (i : Fin n) (g : LocalQFTGate 1) (y z : Reg n)
    (h : localGateMatrix (liftToWire i g) y z ≠ 0) : ∀ j : Fin n, j ≠ i → y j = z j := by
  cases g with
  | h a =>
      rw [localGateMatrix_lift_h] at h
      by_cases hag : ∀ j : Fin n, j ≠ i → y j = z j
      · exact hag
      · rw [ite_eq_right hag] at h
        simp at h
  | cp a c e neg =>
      rw [localGateMatrix_lift_cp] at h
      by_cases hyz : y = z
      · rw [hyz]
        intro j _
        rfl
      · rw [ite_eq_right hyz] at h
        simp at h
  | swap a c =>
      rw [localGateMatrix_lift_swap] at h
      by_cases hyz : y = z
      · rw [hyz]
        intro j _
        rfl
      · rw [ite_eq_right hyz] at h
        simp at h

/-- Evaluates a lifted one-wire word by its original program matrix when the registers agree off
the selected wire, and by zero otherwise. -/
theorem liftedWord_matrix {n : ℕ} (i : Fin n) (L : List (LocalQFTGate 1)) :
    ∀ (y x : Reg n),
      localProgramMatrix (L.map (liftToWire i)) y x =
        if (∀ j : Fin n, j ≠ i → y j = x j) then
          localProgramMatrix L (fun _ => y i) (fun _ => x i) else 0 := by
  induction L with
  | nil =>
      intro y x
      rw [List.map_nil, localProgramMatrix_nil, Matrix.one_apply]
      by_cases hyx : ∀ j : Fin n, j ≠ i → y j = x j
      · rw [ite_eq_left hyx, localProgramMatrix_nil, Matrix.one_apply]
        rcases agree_cases i y x hyx with rfl | rfl
        · simp
        · have hne : (fun _ : Fin 1 => !(x i)) ≠ (fun _ => x i) := by
            intro h
            have h0 : (!(x i)) = x i := congrFun h ⟨0, by omega⟩
            rcases hx : x i <;> simp [hx] at h0
          rw [flipAt_self, ite_eq_right (flipAt_ne_self i x), ite_eq_right hne]
      · rw [ite_eq_right hyx, ite_eq_right (fun h => hyx (fun j hj => by rw [h]))]
  | cons g gs ih =>
      intro y x
      rw [List.map_cons, localProgramMatrix_cons, Matrix.mul_apply]
      have hsum : ∑ z : Reg n, localProgramMatrix (gs.map (liftToWire i)) y z
              * localGateMatrix (liftToWire i g) z x
          = ∑ z : Reg n, (if (∀ j : Fin n, j ≠ i → y j = z j)
              then localProgramMatrix gs (fun _ => y i) (fun _ => z i) else 0)
              * localGateMatrix (liftToWire i g) z x :=
        Finset.sum_congr rfl (fun z _ => by rw [ih y z])
      rw [hsum]
      by_cases hyx : ∀ j : Fin n, j ≠ i → y j = x j
      · rw [ite_eq_left hyx, localProgramMatrix_cons, Matrix.mul_apply]
        cases g with
        | cp a c e neg =>
            have hcond : ((fun _ : Fin 1 => x i) a && (fun _ : Fin 1 => x i) c) = x i := by
              simp [fin1_eq a, fin1_eq c]
            simp only [localGateMatrix_lift_cp, localGateMatrix_cp]
            rw [Finset.sum_eq_single x
              (fun z _ hz => by rw [ite_eq_right hz, mul_zero])
              (fun hz => by exact absurd (Finset.mem_univ x) hz),
              ite_eq_left hyx, ite_eq_left rfl]
            rw [Finset.sum_eq_single (fun _ => x i)
              (fun u _ hu => by rw [ite_eq_right hu, mul_zero])
              (fun hz => by exact absurd (Finset.mem_univ (fun _ => x i)) hz),
              ite_eq_left rfl, hcond]
        | swap a c =>
            have hac : a = c := by rw [fin1_eq a, fin1_eq c]
            have hcol : ∀ v : Reg 1, (fun k : Fin 1 => v (Equiv.swap a c k)) = v := by
              intro v
              rw [hac]
              funext k
              simp [Equiv.swap_self]
            simp only [localGateMatrix_lift_swap, localGateMatrix_swap]
            rw [Finset.sum_eq_single x
              (fun z _ hz => by rw [ite_eq_right hz, mul_zero])
              (fun hz => by exact absurd (Finset.mem_univ x) hz),
              ite_eq_left hyx, ite_eq_left rfl, mul_one]
            rw [Finset.sum_eq_single (fun _ => x i)
              (fun u _ hu => by rw [ite_eq_right hu, mul_zero])
              (fun hz => by exact absurd (Finset.mem_univ (fun _ => x i)) hz),
              hcol (fun _ => x i), ite_eq_left rfl, mul_one]
        | h a =>
            simp only [localGateMatrix_lift_h]
            have hvac : ∀ u : Reg 1, ∀ k : Fin 1, k ≠ a → u k = (fun _ : Fin 1 => x i) k := by
              intro u k hk
              rw [fin1_eq k, fin1_eq a] at hk
              exact absurd rfl hk
            have hrhs : ∑ u : Reg 1, localProgramMatrix gs (fun _ => y i) u
                  * localGateMatrix (LocalQFTGate.h a) u (fun _ : Fin 1 => x i)
                = ∑ u : Reg 1, localProgramMatrix gs (fun _ => y i) u
                  * Hadamard (u a) (x i) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              congr 1
              have hexp : localGateMatrix (LocalQFTGate.h a) u (fun _ : Fin 1 => x i)
                  = Hadamard (u a) (x i) := by
                rw [localGateMatrix_h]
                rw [ite_eq_left (hvac u)]
              rw [hexp]
            rw [hrhs]
            have hterm : ∀ z : Reg n,
                (if (∀ j : Fin n, j ≠ i → y j = z j)
                    then localProgramMatrix gs (fun _ => y i) (fun _ => z i) else 0)
                * (if (∀ j : Fin n, j ≠ i → z j = x j) then Hadamard (z i) (x i) else 0)
                = if (∀ j : Fin n, j ≠ i → z j = x j)
                  then localProgramMatrix gs (fun _ => y i) (fun _ => z i)
                    * Hadamard (z i) (x i) else 0 := by
              intro z
              by_cases hz : ∀ j : Fin n, j ≠ i → z j = x j
              · rw [ite_eq_left hz,
                  ite_eq_left (fun j hj => (hyx j hj).trans (hz j hj).symm), ite_eq_left hz]
              · rw [ite_eq_right hz, ite_eq_right hz, mul_zero]
            rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.sum_filter]
            have hset : (Finset.univ.filter (fun z : Reg n => ∀ j : Fin n, j ≠ i → z j = x j)
                : Finset (Reg n)) = {x, flipAt i x} := by
              ext z
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                Finset.mem_singleton]
              exact ⟨fun hz => agree_cases i z x hz, fun hz => by
                rcases hz with rfl | rfl
                · intro _ _
                  rfl
                · intro j hj
                  rw [flipAt_of_ne i x hj]⟩
            have hsum1 : ∑ u : Reg 1, localProgramMatrix gs (fun _ => y i) u
                  * Hadamard (u a) ((fun _ : Fin 1 => x i) a)
                = localProgramMatrix gs (fun _ => y i) (fun _ => false) * Hadamard false (x i)
                  + localProgramMatrix gs (fun _ => y i) (fun _ => true) * Hadamard true (x i) := by
              rw [sum_reg1 (fun u => localProgramMatrix gs (fun _ => y i) u
                    * Hadamard (u a) ((fun _ : Fin 1 => x i) a))]
            rw [hsum1, hset, Finset.sum_pair (Ne.symm (flipAt_ne_self i x)), flipAt_self]
            rcases hx : x i with _ | _
            · simp only [hx, Bool.not_false]
            · simp only [hx, Bool.not_true]
              ring
      · rw [ite_eq_right hyx]
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases hz : (∀ j : Fin n, j ≠ i → y j = z j)
        · by_cases hM : localGateMatrix (liftToWire i g) z x = 0
          · rw [hM, mul_zero]
          · exact absurd (fun j hj => (hz j hj).trans (lift_entry_agree i g z x hM j hj)) hyx
        · rw [ite_eq_right hz, zero_mul]

def regSplit (w : ℕ) (z : Reg (w + 1)) : Reg w × Reg 1 :=
  ⟨fun j => z (liftFin j), fun _ => z (lastWire w)⟩

/-- Splitting a register into its original wires and last wire is injective. -/
theorem regSplit_injective (w : ℕ) : Function.Injective (regSplit (w := w)) := by
  intro z₁ z₂ h
  funext r
  by_cases hr : r.val < w
  · have h1 := congrFun (congrArg Prod.fst h) ⟨r.val, hr⟩
    have hl : liftFin ⟨r.val, hr⟩ = r := by
      ext
      simp [liftFin]
    show z₁ (liftFin ⟨r.val, hr⟩) = z₂ (liftFin ⟨r.val, hr⟩)
    exact h1
  · have hrw : r.val = w := by
      have := r.isLt
      omega
    have h2 := congrFun (congrArg Prod.snd h) (⟨0, by omega⟩ : Fin 1)
    have hrl : r = lastWire w := by
      ext
      simp [lastWire, hrw]
    rw [hrl]
    show z₁ (lastWire w) = z₂ (lastWire w)
    exact h2

/-- Splitting a register into its original wires and last wire is surjective. -/
theorem regSplit_surjective (w : ℕ) : Function.Surjective (regSplit (w := w)) := by
  rintro ⟨s, u⟩
  refine ⟨fun r => if h : r.val < w then s ⟨r.val, h⟩ else u ⟨0, by omega⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · funext j
    show (if h : (liftFin j).val < w then s ⟨(liftFin j).val, h⟩ else u ⟨0, by omega⟩) = s j
    have hv : (liftFin j).val = j.val := rfl
    rw [hv, dite_eq_left j.isLt]
  · funext j
    show (if h : (lastWire w).val < w then s ⟨(lastWire w).val, h⟩ else u ⟨0, by omega⟩) = u j
    rw [dite_eq_right (by simp [lastWire])]
    exact congrArg u (fin1_eq j).symm

def regSuccView (w : ℕ) : Reg (w + 1) ≃ Reg w × Reg 1 :=
  Equiv.ofBijective (regSplit w) ⟨regSplit_injective w, regSplit_surjective w⟩

/-- Evaluates `regSuccView` as the pair of the original register and the last-wire register. -/
theorem regSuccView_apply (w : ℕ) (z : Reg (w + 1)) :
    regSuccView w z = ⟨fun j => z (liftFin j), fun _ => z (lastWire w)⟩ := rfl

/-- Registers are equal when both components of their successor views agree. -/
theorem eq_of_regSuccView_eq (w : ℕ) {y x : Reg (w + 1)}
    (h1 : (regSuccView w y).1 = (regSuccView w x).1)
    (h2 : (regSuccView w y).2 = (regSuccView w x).2) : y = x :=
  (regSuccView w).injective (Prod.ext h1 h2)

/-- Equality of the original-register components is equivalent to agreement away from the last
wire. -/
theorem agree_lastWire_iff (w : ℕ) (y x : Reg (w + 1)) :
    ((regSuccView w y).1 = (regSuccView w x).1)
      ↔ ∀ j : Fin (w + 1), j ≠ lastWire w → y j = x j := by
  constructor
  · intro h j hj
    have hjw : j.val < w := by
      have h1 := j.isLt
      have h2 : j.val ≠ w := by
        intro hv
        exact hj (by ext; simp [lastWire, hv])
      omega
    obtain ⟨i, rfl⟩ : ∃ i : Fin w, j = liftFin i :=
      ⟨⟨j.val, hjw⟩, by ext; simp [liftFin]⟩
    exact congrFun h i
  · intro h
    funext i
    exact h (liftFin i) (liftFin_ne_lastWire i)

/-- Evaluates a relabeled matrix using the inverse equivalence on its indices. -/
theorem relabelGate_entry {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) (N : Matrix I I ℂ) (j j' : J) :
    relabelGate e N j j' = N (e.symm j) (e.symm j') := by
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Relabeling matrices preserves multiplication. -/
theorem relabelGate_mul {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (A B : Matrix I I ℂ) :
    relabelGate e (A * B) = relabelGate e A * relabelGate e B := by
  ext j j'
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Equiv.symm_symm]
  exact Fintype.sum_equiv e
    (fun i : I => A (e.symm j) i * B i (e.symm j'))
    (fun l : J => A (e.symm j) (e.symm l) * B (e.symm l) (e.symm j'))
    (fun i => by simp only [Equiv.symm_apply_apply])

/-- Relabeling preserves the identity matrix. -/
theorem relabelGate_one {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) : relabelGate e (1 : Matrix I I ℂ) = 1 := by
  ext j j'
  simp only [relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply,
    Equiv.symm_symm]
  by_cases hj : j = j'
  · subst hj
    simp
  · rw [ite_eq_right hj, ite_eq_right (fun h => hj (e.symm.injective h))]

/-- Relabeling commutes with subtracting a scalar multiple of a matrix. -/
theorem relabelGate_sub_smul {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (e : I ≃ J) (A B : Matrix I I ℂ) (c : ℂ) :
    relabelGate e A - c • relabelGate e B = relabelGate e (A - c • B) := by
  ext j j'
  simp [relabelGate, Matrix.sub_apply, Matrix.smul_apply]

/-- Lifting a one-wire gate to the last wire is a relabeling of its tensor product with the
identity. -/
theorem liftToWire_matrix (w : ℕ) (g : LocalQFTGate 1) :
    localGateMatrix (liftToWire (lastWire w) g)
      = relabelGate (regSuccView w).symm
          ((1 : Matrix (Reg w) (Reg w) ℂ) ⊗ₖ localGateMatrix g) := by
  ext y x
  rw [relabelGate_entry, Equiv.symm_symm, Matrix.kronecker_apply, Matrix.one_apply]
  cases g with
  | h a =>
      rw [localGateMatrix_lift_h, localGateMatrix_h]
      have hvac : ∀ u v : Reg 1, ∀ k : Fin 1, k ≠ a → u k = v k := by
        intro u v k hk
        rw [fin1_eq k, fin1_eq a] at hk
        exact absurd rfl hk
      by_cases hs : (regSuccView w y).1 = (regSuccView w x).1
      · rw [ite_eq_left hs, ite_eq_left ((agree_lastWire_iff w y x).mp hs), ite_eq_left (hvac _ _), one_mul]
        rfl
      · rw [ite_eq_right hs, ite_eq_right ((agree_lastWire_iff w y x).not.mp hs), zero_mul]
  | cp a c e neg =>
      rw [localGateMatrix_lift_cp, localGateMatrix_cp]
      by_cases hyx : y = x
      · subst hyx
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, one_mul]
        show (if y (lastWire w) = true then
            (Complex.exp ((dyadicPhaseAngle e neg : ℝ) * Complex.I) : ℂ) else 1)
          = (if (y (lastWire w) && y (lastWire w)) = true then
            (Complex.exp ((dyadicPhaseAngle e neg : ℝ) * Complex.I) : ℂ) else 1)
        rw [Bool.and_self]
      · rw [ite_eq_right hyx]
        by_cases hs : (regSuccView w y).1 = (regSuccView w x).1
        · rw [ite_eq_left hs, ite_eq_right (fun hu => hyx (eq_of_regSuccView_eq w hs hu)), mul_zero]
        · rw [ite_eq_right hs, zero_mul]
  | swap a c =>
      rw [localGateMatrix_lift_swap, localGateMatrix_swap]
      have hcol : ∀ v : Reg 1, (fun k => v (Equiv.swap a c k)) = v := by
        intro v
        have hac : a = c := by rw [fin1_eq a, fin1_eq c]
        rw [hac]
        funext k
        simp [Equiv.swap_self]
      rw [hcol ((regSuccView w x).2)]
      by_cases hyx : y = x
      · subst hyx
        rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, one_mul]
      · rw [ite_eq_right hyx]
        by_cases hs : (regSuccView w y).1 = (regSuccView w x).1
        · rw [ite_eq_left hs, ite_eq_right (fun hu => hyx (eq_of_regSuccView_eq w hs hu)), mul_zero]
        · rw [ite_eq_right hs, zero_mul]

/-- Lifting a one-wire word to the last wire is a relabeling of its program matrix tensored with
the identity. -/
theorem liftedWord_tensor (w : ℕ) (L : List (LocalQFTGate 1)) :
    localProgramMatrix (L.map (liftToWire (lastWire w)))
      = relabelGate (regSuccView w).symm
          ((1 : Matrix (Reg w) (Reg w) ℂ) ⊗ₖ localProgramMatrix L) := by
  induction L with
  | nil =>
      have h1 : ((1 : Matrix (Reg w) (Reg w) ℂ) ⊗ₖ (1 : Matrix (Reg 1) (Reg 1) ℂ))
          = (1 : Matrix (Reg w × Reg 1) (Reg w × Reg 1) ℂ) := Matrix.one_kronecker_one
      rw [List.map_nil, localProgramMatrix_nil, localProgramMatrix_nil, h1]
      exact (relabelGate_one (regSuccView w).symm).symm
  | cons g gs ih =>
      have hr : relabelGate (regSuccView w).symm
            ((1 : Matrix (Reg w) (Reg w) ℂ)
              ⊗ₖ (localProgramMatrix gs * localGateMatrix g))
          = relabelGate (regSuccView w).symm
              ((1 ⊗ₖ localProgramMatrix gs) * (1 ⊗ₖ localGateMatrix g)) := by
        rw [← Matrix.mul_kronecker_mul, Matrix.mul_one]
      rw [List.map_cons, localProgramMatrix_cons, localProgramMatrix_cons, ih,
        liftToWire_matrix, ← relabelGate_mul, hr]

/-- A last-wire phase matrix is the relabeling of the one-wire phase matrix tensored with the
identity. -/
theorem oneWirePhaseMatrix_lift (w : ℕ) (θ : ℝ) :
    oneWirePhaseMatrix (lastWire w) θ
      = relabelGate (regSuccView w).symm
          ((1 : Matrix (Reg w) (Reg w) ℂ) ⊗ₖ oneWirePhaseMatrix (0 : Fin 1) θ) := by
  ext y x
  rw [relabelGate_entry, Equiv.symm_symm, Matrix.kronecker_apply, Matrix.one_apply,
    oneWirePhaseMatrix, oneWirePhaseMatrix, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hyx : y = x
  · subst hyx
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, one_mul]
    rfl
  · rw [ite_eq_right hyx]
    by_cases hs : (regSuccView w y).1 = (regSuccView w x).1
    · rw [ite_eq_left hs, ite_eq_right (fun hu => hyx (eq_of_regSuccView_eq w hs hu)), mul_zero]
    · rw [ite_eq_right hs, zero_mul]

/-- Expresses the lifted word's phase-adjusted error as a relabeled tensor product of the
original error with the identity. -/
theorem liftedWord_error (w : ℕ) (L : List (LocalQFTGate 1)) (e : ℕ) (neg : Bool) (φ : ℝ) :
    localProgramMatrix (L.map (liftToWire (lastWire w)))
        - (Complex.exp (φ * Complex.I))
            • oneWirePhaseMatrix (lastWire w) (dyadicPhaseAngle e neg)
      = relabelGate (regSuccView w).symm
          ((1 : Matrix (Reg w) (Reg w) ℂ) ⊗ₖ
            (localProgramMatrix L
              - (Complex.exp (φ * Complex.I))
                  • oneWirePhaseMatrix (0 : Fin 1) (dyadicPhaseAngle e neg))) := by
  rw [liftedWord_tensor, oneWirePhaseMatrix_lift, relabelGate_sub_smul,
    ← Matrix.kronecker_smul, ← Qatlib.Concepts.ReferenceError.RefTraceError.kronecker_sub_right]

/-- Lifting a one-wire word to the last wire preserves its phase-adjusted approximation error
norm. -/
theorem liftedWord_error_norm (w : ℕ) (L : List (LocalQFTGate 1)) (e : ℕ) (neg : Bool)
    (φ : ℝ) :
    ‖localProgramMatrix (L.map (liftToWire (lastWire w)))
        - (Complex.exp (φ * Complex.I))
            • oneWirePhaseMatrix (lastWire w) (dyadicPhaseAngle e neg)‖
      = ‖localProgramMatrix L
          - (Complex.exp (φ * Complex.I))
              • oneWirePhaseMatrix (0 : Fin 1) (dyadicPhaseAngle e neg)‖ := by
  rw [liftedWord_error, l2_norm_relabelGate, l2_norm_kronecker, l2_norm_one_eq, one_mul]

/-- The matrix of an involutive permutation has norm at most one. -/
theorem permMatrix_norm_le {I : Type*} [Fintype I] [DecidableEq I] {σ : I → I}
    [Nonempty I] (hσ : Function.Involutive σ) : ‖permMatrix σ‖ ≤ 1 :=
  (l2_norm_unitary_eq_one (permMatrix_unitary hσ)).le

/-- The clean embedding matrix has norm at most one. -/
theorem cleanEmbed_norm_le (w : ℕ) : ‖cleanEmbed w (w + 1)‖ ≤ 1 := by
  refine l2_opNorm_le_of_mulVec_le (by norm_num) _ fun v => ?_
  have hat : ∀ t : Reg w, (cleanEmbed w (w + 1) *ᵥ v) (padEmbed t) = v t := by
    intro t
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single t]
    · rw [cleanEmbed_apply, ite_eq_left rfl, one_mul]
    · intro t' _ ht'
      rw [cleanEmbed_apply, ite_eq_right (fun h => ht' (padEmbed_injective h).symm), zero_mul]
    · intro hmem
      exact absurd (Finset.mem_univ t) hmem
  have hzero : ∀ p : Reg (w + 1), (∀ t : Reg w, p ≠ padEmbed t) →
      (cleanEmbed w (w + 1) *ᵥ v) p = 0 := by
    intro p hp
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_zero]
    intro t _
    rw [cleanEmbed_apply, ite_eq_right (fun h => hp t h), zero_mul]
  have hsq : ‖toEuclidean_fromVec (cleanEmbed w (w + 1) *ᵥ v)‖ ^ 2
      = ‖toEuclidean_fromVec v‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq, ← Finset.sum_subset
      (Finset.subset_univ _) (fun p _ hpu =>
        by rw [hzero p (fun t ht => hpu (ht ▸ Finset.mem_image_of_mem padEmbed
          (Finset.mem_univ t)))]; simp)]
    rw [Finset.sum_image (fun a _ b _ h => padEmbed_injective h)]
    exact Finset.sum_congr rfl fun t _ => by rw [hat t]
  calc ‖toEuclidean_fromVec (cleanEmbed w (w + 1) *ᵥ v)‖
      = Real.sqrt (‖toEuclidean_fromVec (cleanEmbed w (w + 1) *ᵥ v)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖toEuclidean_fromVec v‖ ^ 2) := by rw [hsq]
    _ = ‖toEuclidean_fromVec v‖ := Real.sqrt_sq (norm_nonneg _)
    _ ≤ 1 * ‖toEuclidean_fromVec v‖ := by norm_num

def dirtyMask (w : ℕ) : Matrix (Reg (w + 1)) (Reg (w + 1)) ℂ :=
  Matrix.diagonal fun z => if z (lastWire w) then 1 else 0

/-- The dirty ancilla mask has norm at most one. -/
theorem dirtyMask_norm_le (w : ℕ) : ‖dirtyMask w‖ ≤ 1 := by
  have h1 : ∀ z : Reg (w + 1), ‖(if z (lastWire w) then (1 : ℂ) else 0)‖ ≤ 1 := by
    intro z
    by_cases h : z (lastWire w) <;> simp [h]
  rw [dirtyMask, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg (by norm_num)).2 h1

/-- The dirty ancilla mask annihilates the clean embedding. -/
theorem dirtyMask_mul_cleanEmbed (w : ℕ) : dirtyMask w * cleanEmbed w (w + 1) = 0 := by
  ext p t
  rw [dirtyMask, Matrix.diagonal_mul, cleanEmbed_apply]
  by_cases hpt : p = padEmbed t
  · rw [ite_eq_left hpt]
    have hp : p (lastWire w) = false := by rw [hpt, padEmbed_lastWire]
    rw [ite_eq_right (by simp [hp]), zero_mul]
    simp
  · rw [ite_eq_right hpt, mul_zero]
    simp

/-- The dirty ancilla mask retains exactly the amplitudes with a true last wire. -/
theorem dirtyMask_mulVec (w : ℕ) (u : QState (Reg (w + 1))) (z : Reg (w + 1)) :
    (dirtyMask w *ᵥ u) z = (if z (lastWire w) then (1 : ℂ) else 0) * u z := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single z]
  · rw [dirtyMask, Matrix.diagonal_apply, ite_eq_left rfl]
  · intro y _ hy
    rw [dirtyMask, Matrix.diagonal_apply, ite_eq_right (fun h => hy h.symm), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ z) hmem

/-- Evaluates a permutation matrix entry as the indicator of the image of the input register. -/
theorem permMatrix_entry {n : ℕ} (σ : Reg n → Reg n) (y x : Reg n) :
    permMatrix σ y x = if y = σ x then (1 : ℂ) else 0 := rfl

/-- Right multiplication by a diagonal matrix scales each column by its diagonal entry. -/
theorem mul_diagonal_entry {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix m n ℂ) (d : n → ℂ) (y : m) (x : n) :
    (M * Matrix.diagonal d) y x = M y x * d x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · rw [Matrix.diagonal_apply, ite_eq_left rfl]
  · intro z _ hz
    rw [Matrix.diagonal_apply, ite_eq_right hz, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ x) hmem

def andConjugate {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1)) :
    List (LocalQFTGate (w + 1)) :=
  andWord a c ++ L.map (liftToWire (lastWire w)) ++ andWord a c

/-- Expresses the AND-conjugated word's matrix as the lifted word conjugated by the AND
permutation matrix. -/
theorem andConjugate_matrix {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1)) :
    localProgramMatrix (andConjugate a c L)
      = permMatrix (andUpdate a c) * localProgramMatrix (L.map (liftToWire (lastWire w)))
          * permMatrix (andUpdate a c) := by
  rw [andConjugate, localProgramMatrix_append, localProgramMatrix_append,
    andWord_matrix, Matrix.mul_assoc]

/-- The AND-conjugated word has twice the AND word's length plus the original word's length. -/
theorem andConjugate_length {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1)) :
    (andConjugate a c L).length = 2 * (andWord a c).length + L.length := by
  rw [andConjugate, List.length_append, List.length_append, List.length_map]
  omega

/-- AND conjugation preserves the fixed primitive property of every gate in a word. -/
theorem andConjugate_legal {w : ℕ} (a c : Fin w) {L : List (LocalQFTGate 1)}
    (hL : ∀ g ∈ L, IsFixedPrim g) : ∀ g ∈ andConjugate a c L, IsFixedPrim g := by
  intro g hg
  rw [andConjugate, List.mem_append, List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact andWord_legal a c g h
  · obtain ⟨g', hg'1, hg'2⟩ := List.mem_map.mp h
    rw [← hg'2]
    exact liftToWire_legal (lastWire w) g' (hL g' hg'1)
  · exact andWord_legal a c g h

/-- The AND update of a padded register places the conjunction of the selected bits on the last
wire. -/
theorem andUpdate_padEmbed_lastWire (w : ℕ) (a c : Fin w) (t : Reg w) :
    (andUpdate a c (padEmbed t)) (lastWire w) = (t a && t c) := by
  cases hta : t a <;> cases htc : t c <;>
    simp [andUpdate, flipAt, apply_ite, padEmbed_liftFin, padEmbed_lastWire, hta, htc]

/-- Evaluates the entries of a diagonal matrix conjugated by an involutive permutation matrix. -/
theorem perm_diag_perm_entry {n : ℕ} (σ : Reg n → Reg n) (hσ : Function.Involutive σ)
    (d : Reg n → ℂ) (p q : Reg n) :
    (permMatrix σ * Matrix.diagonal d * permMatrix σ) p q
      = (if p = q then (1 : ℂ) else 0) * d (σ q) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ q)]
  · rw [mul_diagonal_entry, permMatrix_entry, permMatrix_entry, ite_eq_left rfl, hσ q, mul_one]
  · intro z _ hz
    rw [permMatrix_entry, ite_eq_right hz, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Conjugating a last-wire phase by the AND permutation implements the controlled phase on
cleanly embedded inputs. -/
theorem andConjugate_exact {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) :
    permMatrix (andUpdate a c) * oneWirePhaseMatrix (lastWire w) (dyadicPhaseAngle e neg)
        * permMatrix (andUpdate a c) * cleanEmbed w (w + 1)
      = cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg) := by
  have hentry : ∀ (p : Reg (w + 1)) (t : Reg w),
      (permMatrix (andUpdate a c) * oneWirePhaseMatrix (lastWire w)
          (dyadicPhaseAngle e neg) * permMatrix (andUpdate a c)) p (padEmbed t)
        = (if p = padEmbed t then (1 : ℂ) else 0)
            * (if t a && t c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1) := by
    intro p t
    rw [oneWirePhaseMatrix, perm_diag_perm_entry (andUpdate a c) (andUpdate_involutive a c)
      (fun z : Reg (w + 1) => if z (lastWire w)
        then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1) p (padEmbed t)]
    show (if p = padEmbed t then (1 : ℂ) else 0)
        * (if andUpdate a c (padEmbed t) (lastWire w)
          then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)
      = (if p = padEmbed t then (1 : ℂ) else 0)
          * (if t a && t c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)
    rw [andUpdate_padEmbed_lastWire w a c t]
  ext p t
  rw [Matrix.mul_apply, Finset.sum_eq_single (padEmbed t)]
  · rw [cleanEmbed_apply, ite_eq_left rfl, hentry p t, mul_one, cp_matrix_diag,
      mul_diagonal_entry, cleanEmbed_apply]
  · intro u _ hu
    rw [cleanEmbed_apply, ite_eq_right (fun h => hu h), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- Factors the phase-adjusted error of the AND-conjugated word through the lifted scalar error. -/
theorem andConjugate_error {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1)) (e : ℕ)
    (neg : Bool) (φ : ℝ) :
    localProgramMatrix (andConjugate a c L) * cleanEmbed w (w + 1)
        - (Complex.exp (φ * Complex.I))
            • (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg))
      = permMatrix (andUpdate a c)
          * (localProgramMatrix (L.map (liftToWire (lastWire w)))
              - (Complex.exp (φ * Complex.I))
                  • oneWirePhaseMatrix (lastWire w) (dyadicPhaseAngle e neg))
          * permMatrix (andUpdate a c) * cleanEmbed w (w + 1) := by
  have hexact := andConjugate_exact a c e neg
  rw [andConjugate_matrix, ← hexact]
  simp only [Matrix.mul_assoc]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul]

/-- The product of two matrices of norm at most one has norm at most one. -/
theorem mul4_norm_le_one {w : ℕ} (A B : Matrix (Reg (w + 1)) (Reg (w + 1)) ℂ)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) : ‖A * B‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_mul A B
  nlinarith [h, hA, hB, norm_nonneg A, norm_nonneg B]

/-- Multiplication on either side by the stated contractions bounds the four-factor product norm
by the middle matrix norm. -/
theorem mul4_norm_le {w : ℕ} (A B C : Matrix (Reg (w + 1)) (Reg (w + 1)) ℂ)
    (hA : ‖A‖ ≤ 1) (hC : ‖C‖ ≤ 1) (E : Matrix (Reg (w + 1)) (Reg w) ℂ) (hE : ‖E‖ ≤ 1) :
    ‖A * B * C * E‖ ≤ ‖B‖ := by
  have h1 := Matrix.l2_opNorm_mul (A * B * C) E
  have h2 := Matrix.l2_opNorm_mul (A * B) C
  have h3 := Matrix.l2_opNorm_mul A B
  have hnA : 0 ≤ ‖A‖ := norm_nonneg _
  have hnB : 0 ≤ ‖B‖ := norm_nonneg _
  have hnC : 0 ≤ ‖C‖ := norm_nonneg _
  have hnE : 0 ≤ ‖E‖ := norm_nonneg _
  have hCE : ‖C‖ * ‖E‖ ≤ 1 := by nlinarith [hC, hE, hnC, hnE]
  have hACE : ‖A‖ * (‖C‖ * ‖E‖) ≤ 1 := by
    nlinarith [hA, hnA, hCE, mul_nonneg hnC hnE]
  have hfin := mul_le_mul_of_nonneg_right hACE hnB
  calc ‖A * B * C * E‖ ≤ ‖A * B * C‖ * ‖E‖ := h1
    _ ≤ (‖A * B‖ * ‖C‖) * ‖E‖ := by
        nlinarith [h2, hnE, mul_nonneg (mul_nonneg hnA hnB) hnC]
    _ ≤ ((‖A‖ * ‖B‖) * ‖C‖) * ‖E‖ := by
        nlinarith [h3, mul_nonneg (mul_nonneg hnA hnB) hnC,
          mul_nonneg hnC hnE, mul_nonneg hnA hnB]
    _ = (‖A‖ * (‖C‖ * ‖E‖)) * ‖B‖ := by ring
    _ ≤ (1 : ℝ) * ‖B‖ := hfin
    _ = ‖B‖ := by ring

/-- Bounds the AND-conjugated word's error on clean inputs by the original one-wire phase
approximation error. -/
theorem andConjugate_error_norm {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1))
    (e : ℕ) (neg : Bool) (φ : ℝ) :
    ‖localProgramMatrix (andConjugate a c L) * cleanEmbed w (w + 1)
        - (Complex.exp (φ * Complex.I))
            • (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg))‖
      ≤ ‖localProgramMatrix L
          - (Complex.exp (φ * Complex.I))
              • oneWirePhaseMatrix (0 : Fin 1) (dyadicPhaseAngle e neg)‖ := by
  rw [andConjugate_error]
  refine le_trans (mul4_norm_le (permMatrix (andUpdate a c)) _ (permMatrix (andUpdate a c))
    (permMatrix_norm_le (andUpdate_involutive a c))
    (permMatrix_norm_le (andUpdate_involutive a c)) (cleanEmbed w (w + 1))
    (cleanEmbed_norm_le w)) ?_
  rw [liftedWord_error_norm]

/-- The empty word approximates a padded controlled phase when its exponent is at least the
precision plus two. -/
theorem emptyWord_approx_cp_padded {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : k + 2 ≤ e) :
    approxUpToPhase (localProgramMatrix ([] : List (LocalQFTGate (w + 1))) * cleanEmbed w (w + 1))
      (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) (tolerance k) := by
  obtain ⟨θ, hθ⟩ := emptyWord_approx_cp a c e neg k he
  rw [localProgramMatrix_nil, cleanEmbed_self w] at hθ
  simp only [Matrix.one_mul, Matrix.mul_one] at hθ
  refine ⟨θ, ?_⟩
  rw [localProgramMatrix_nil, Matrix.one_mul]
  have hkey : (cleanEmbed w (w + 1) : Matrix (Reg (w + 1)) (Reg w) ℂ)
        - (Complex.exp (θ * Complex.I))
            • (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg))
      = cleanEmbed w (w + 1) * ((1 : Matrix (Reg w) (Reg w) ℂ)
          - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg)) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [hkey]
  calc ‖cleanEmbed w (w + 1) * ((1 : Matrix (Reg w) (Reg w) ℂ)
          - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg))‖
      ≤ ‖cleanEmbed w (w + 1)‖ * ‖(1 : Matrix (Reg w) (Reg w) ℂ)
          - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * tolerance k := by
        have h1 := cleanEmbed_norm_le w
        have h2 : 0 ≤ ‖(1 : Matrix (Reg w) (Reg w) ℂ)
            - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ := norm_nonneg _
        calc ‖cleanEmbed w (w + 1)‖ * ‖(1 : Matrix (Reg w) (Reg w) ℂ)
                - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg)‖
            ≤ 1 * ‖(1 : Matrix (Reg w) (Reg w) ℂ)
                - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = ‖(1 : Matrix (Reg w) (Reg w) ℂ)
                - (Complex.exp (θ * Complex.I)) • localGateMatrix (.cp a c e neg)‖ := by ring
          _ ≤ tolerance k := hθ
          _ = 1 * tolerance k := by ring
    _ = tolerance k := by ring

/-- The auxiliary bits of a register are zero exactly when its last wire is false. -/
theorem auxBits_w1_iff (w : ℕ) (z : Reg (w + 1)) :
    (auxBits w z = Qatlib.Foundations.PureStateMath.ZeroStr (w + 1 - w)) ↔ z (lastWire w) = false := by
  constructor
  · intro heq
    have h0 := congrFun heq (⟨0, by omega⟩ : Fin (w + 1 - w))
    exact h0
  · intro hz
    funext i
    have hij : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hij
    exact hz

/-- A bound on the dirty-mask component implies the corresponding ancilla restoration bound. -/
theorem ancillaRestored_of_dirtyMask_norm {w : ℕ} (M : Matrix (Reg (w + 1)) (Reg w) ℂ)
    {tol : ℝ} (h : ‖dirtyMask w * M‖ ≤ tol) : ancillaRestored w M tol := by
  intro ψ hψ
  have hmask : (fun z : Reg (w + 1) =>
        if auxBits w z = Qatlib.Foundations.PureStateMath.ZeroStr (w + 1 - w) then 0 else (M *ᵥ ψ) z)
      = dirtyMask w *ᵥ (M *ᵥ ψ) := by
    funext z
    rw [dirtyMask_mulVec]
    by_cases hz : z (lastWire w)
    · have hne : ¬(auxBits w z = Qatlib.Foundations.PureStateMath.ZeroStr (w + 1 - w)) := by
        intro hcon
        rw [auxBits_w1_iff] at hcon
        rw [hcon] at hz
        exact Bool.noConfusion hz
      rw [ite_eq_right hne, ite_eq_left hz, one_mul]
    · have hzf : z (lastWire w) = false := by simpa using hz
      rw [ite_eq_left ((auxBits_w1_iff w z).mpr hzf), ite_eq_right hz, zero_mul]
  rw [hmask, Matrix.mulVec_mulVec]
  calc ‖toEuclidean_fromVec ((dirtyMask w * M) *ᵥ ψ)‖
      ≤ ‖dirtyMask w * M‖ * ‖toEuclidean_fromVec ψ‖ := l2_norm_mulVec_fromVec_le _ _
    _ = ‖dirtyMask w * M‖ * 1 := by
        rw [(Qatlib.Foundations.PureStateMath.BornBridge.normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ]
    _ ≤ tol := by rw [mul_one]; exact h

/-- Factors the dirty component of the AND-conjugated word through its scalar phase
approximation error. -/
theorem dirtyMask_andConjugate {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1))
    (e : ℕ) (neg : Bool) (φ : ℝ) :
    dirtyMask w * (localProgramMatrix (andConjugate a c L) * cleanEmbed w (w + 1))
      = dirtyMask w * permMatrix (andUpdate a c)
          * (localProgramMatrix (L.map (liftToWire (lastWire w)))
              - (Complex.exp (φ * Complex.I))
                  • oneWirePhaseMatrix (lastWire w) (dyadicPhaseAngle e neg))
          * permMatrix (andUpdate a c) * cleanEmbed w (w + 1) := by
  have hsecond : dirtyMask w
      * ((Complex.exp (φ * Complex.I))
          • (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg))) = 0 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, dirtyMask_mul_cleanEmbed, Matrix.zero_mul,
      smul_zero]
  have hsplit2 : localProgramMatrix (andConjugate a c L) * cleanEmbed w (w + 1)
      = (localProgramMatrix (andConjugate a c L) * cleanEmbed w (w + 1)
          - (Complex.exp (φ * Complex.I))
              • (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)))
        + (Complex.exp (φ * Complex.I))
            • (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) :=
    (sub_add_cancel _ _).symm
  rw [hsplit2, Matrix.mul_add, hsecond, add_zero, andConjugate_error,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

/-- An accurate scalar phase word yields ancilla restoration for the AND-conjugated word at the
same tolerance. -/
theorem andConjugate_clean {w : ℕ} (a c : Fin w) (L : List (LocalQFTGate 1)) (e : ℕ)
    (neg : Bool) (φ : ℝ) (k : ℕ)
    (hφ : ‖localProgramMatrix L - (Complex.exp (φ * Complex.I))
        • oneWirePhaseMatrix (0 : Fin 1) (dyadicPhaseAngle e neg)‖ ≤ tolerance k) :
    ancillaRestored w (localProgramMatrix (andConjugate a c L) * cleanEmbed w (w + 1))
      (tolerance k) := by
  refine ancillaRestored_of_dirtyMask_norm _ ?_
  rw [dirtyMask_andConjugate]
  refine le_trans (mul4_norm_le (dirtyMask w * permMatrix (andUpdate a c)) _
      (permMatrix (andUpdate a c))
      (mul4_norm_le_one (dirtyMask w) (permMatrix (andUpdate a c))
        (dirtyMask_norm_le w) (permMatrix_norm_le (andUpdate_involutive a c)))
      (permMatrix_norm_le (andUpdate_involutive a c))
      (cleanEmbed w (w + 1)) (cleanEmbed_norm_le w)) ?_
  rw [liftedWord_error_norm]
  exact hφ

/-- The clean embedding satisfies ancilla restoration at every specified tolerance. -/
theorem cleanEmbed_ancillaRestored (w : ℕ) (k : ℕ) :
    ancillaRestored w (cleanEmbed w (w + 1)) (tolerance k) := by
  refine ancillaRestored_of_dirtyMask_norm _ ?_
  rw [dirtyMask_mul_cleanEmbed]
  exact (norm_zero).trans_le (tolerance_nonneg k)

/-- The empty word preserves the clean embedding and satisfies ancilla restoration. -/
theorem emptyWord_clean_padded (w : ℕ) (k : ℕ) :
    ancillaRestored w (localProgramMatrix ([] : List (LocalQFTGate (w + 1)))
      * cleanEmbed w (w + 1)) (tolerance k) := by
  rw [localProgramMatrix_nil, Matrix.one_mul]
  exact cleanEmbed_ancillaRestored w k

def transportEmit (S : ScalarPhaseSynthesizer) (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool)
    (k : ℕ) : List (LocalQFTGate (w + 1)) :=
  if k + 2 ≤ e then [] else andConjugate a c (S.emit neg e k)

/-- The transported emitter returns the empty word when the phase exponent is at least the
precision plus two. -/
theorem transportEmit_far (S : ScalarPhaseSynthesizer) {w : ℕ} (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) (hfar : k + 2 ≤ e) :
    transportEmit S w a c e neg k = [] := by
  rw [transportEmit, ite_eq_left hfar]

/-- In the complementary exponent range, the transported emitter is the AND conjugation of the
emitted scalar word. -/
theorem transportEmit_middle (S : ScalarPhaseSynthesizer) {w : ℕ} (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) (hmid : ¬ (k + 2 ≤ e)) :
    transportEmit S w a c e neg k = andConjugate a c (S.emit neg e k) := by
  rw [transportEmit, ite_eq_right hmid]

/-- Every gate emitted by the transported synthesizer is a fixed primitive. -/
theorem transportEmit_legal (S : ScalarPhaseSynthesizer) (w : ℕ) (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) : ∀ h ∈ transportEmit S w a c e neg k, IsFixedPrim h := by
  by_cases hfar : k + 2 ≤ e
  · rw [transportEmit_far S a c e neg k hfar]
    intro h hh
    simp at hh
  · rw [transportEmit_middle S a c e neg k hfar]
    exact andConjugate_legal a c (S.legal neg e k)

/-- The transported word approximates the requested controlled phase on clean inputs, up to
global phase, at the requested tolerance. -/
theorem transportEmit_correct (S : ScalarPhaseSynthesizer) (w : ℕ) (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) (he : 4 ≤ e) (hk : 1 ≤ k) :
    approxUpToPhase (localProgramMatrix (transportEmit S w a c e neg k) * cleanEmbed w (w + 1))
      (cleanEmbed w (w + 1) * localGateMatrix (.cp a c e neg)) (tolerance k) := by
  by_cases hfar : k + 2 ≤ e
  · rw [transportEmit_far S a c e neg k hfar]
    exact emptyWord_approx_cp_padded a c e neg k hfar
  · rw [transportEmit_middle S a c e neg k hfar]
    obtain ⟨φ, hφ⟩ := S.correct neg e k he hk
    exact ⟨φ, le_trans (andConjugate_error_norm a c (S.emit neg e k) e neg φ) hφ⟩

/-- The transported word restores the ancilla within the requested tolerance. -/
theorem transportEmit_clean (S : ScalarPhaseSynthesizer) (w : ℕ) (a c : Fin w) (e : ℕ)
    (neg : Bool) (k : ℕ) (he : 4 ≤ e) (hk : 1 ≤ k) :
    ancillaRestored w (localProgramMatrix (transportEmit S w a c e neg k)
      * cleanEmbed w (w + 1)) (tolerance k) := by
  by_cases hfar : k + 2 ≤ e
  · rw [transportEmit_far S a c e neg k hfar]
    exact emptyWord_clean_padded w k
  · rw [transportEmit_middle S a c e neg k hfar]
    obtain ⟨φ, hφ⟩ := S.correct neg e k he hk
    exact andConjugate_clean a c (S.emit neg e k) e neg φ k hφ

/-- The request size is at least the precision plus one. -/
theorem requestSize_ge_succ_k {w : ℕ} (g : LocalQFTGate w) (k : ℕ) :
    k + 1 ≤ requestSize w g k := by
  unfold requestSize synthInputBits
  omega

/-- An explicit polynomial scalar length bound gives the stated explicit polynomial bound for
the transported word. -/
theorem transportEmit_bounded_explicit (S : ScalarPhaseSynthesizer) (C₀ D₀ : ℕ)
    (hC₀ : ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
      (S.emit neg e k).length ≤ C₀ * (e + k) ^ D₀) :
    ∀ (w : ℕ) (a c : Fin w) (e k : ℕ) (neg : Bool), 4 ≤ e → 1 ≤ k →
      (transportEmit S w a c e neg k).length
        ≤ (22 + C₀ * 2 ^ D₀) * (requestSize w (.cp a c e neg) k) ^ D₀ := by
  intro w a c e k neg he hk
  by_cases hfar : k + 2 ≤ e
  · rw [transportEmit_far S a c e neg k hfar]
    have hrs : 1 ≤ requestSize w (.cp a c e neg) k := requestSize_pos _ k
    have hpow1 : 1 ≤ (requestSize w (.cp a c e neg) k) ^ D₀ :=
      one_le_pow_nat hrs D₀
    have hbase : 1 ≤ (22 + C₀ * 2 ^ D₀)
        * (requestSize w (.cp a c e neg) k) ^ D₀ := by
      have h1 : 1 ≤ 22 + C₀ * 2 ^ D₀ := by omega
      nlinarith [h1, hpow1]
    exact (Nat.zero_le _).trans hbase
  · rw [transportEmit_middle S a c e neg k hfar, andConjugate_length]
    have hrs : 1 ≤ requestSize w (.cp a c e neg) k := requestSize_pos _ k
    have hek : e + k ≤ 2 * requestSize w (.cp a c e neg) k := by
      have h1 : k + 1 ≤ requestSize w (.cp a c e neg) k := requestSize_ge_succ_k _ k
      have h2 : e ≤ k + 1 := by omega
      omega
    have hmono : (e + k) ^ D₀
        ≤ 2 ^ D₀ * (requestSize w (.cp a c e neg) k) ^ D₀ := by
      have hstep : (e + k) ^ D₀
          ≤ (2 * requestSize w (.cp a c e neg) k) ^ D₀ :=
        Nat.pow_le_pow_left hek D₀
      rw [mul_pow] at hstep
      exact hstep
    have hb : (S.emit neg e k).length ≤ C₀ * (e + k) ^ D₀ := hC₀ neg e k he hk
    have hpow1 : 1 ≤ (requestSize w (.cp a c e neg) k) ^ D₀ := one_le_pow_nat hrs D₀
    have h22 : 22 ≤ 22 * (requestSize w (.cp a c e neg) k) ^ D₀ := by
      have := Nat.mul_le_mul (le_refl 22) hpow1
      omega
    calc 2 * (andWord a c).length + (S.emit neg e k).length
        ≤ 2 * 11 + C₀ * (e + k) ^ D₀ := by
          have hA : (andWord a c).length ≤ 11 := andWord_length a c
          have hB : 2 * (andWord a c).length ≤ 2 * 11 := by omega
          omega
      _ ≤ 22 + C₀ * (2 ^ D₀ * (requestSize w (.cp a c e neg) k) ^ D₀) := by
          have hB : C₀ * (e + k) ^ D₀
              ≤ C₀ * (2 ^ D₀ * (requestSize w (.cp a c e neg) k) ^ D₀) := by
            gcongr
          omega
      _ ≤ (22 + C₀ * 2 ^ D₀) * (requestSize w (.cp a c e neg) k) ^ D₀ := by
          nlinarith [hpow1, h22]

/-- Transported words have a uniform polynomial length bound in the request size. -/
theorem transportEmit_bounded (S : ScalarPhaseSynthesizer) :
    ∃ C D : ℕ, ∀ (w : ℕ) (a c : Fin w) (e k : ℕ) (neg : Bool), 4 ≤ e → 1 ≤ k →
      (transportEmit S w a c e neg k).length
        ≤ C * (requestSize w (.cp a c e neg) k) ^ D := by
  obtain ⟨C₀, D₀, hC₀⟩ := S.bounded
  exact ⟨22 + C₀ * 2 ^ D₀, D₀, transportEmit_bounded_explicit S C₀ D₀ hC₀⟩

def transportSynth (S : ScalarPhaseSynthesizer) : MiddleWindowSynthesizer where
  emit := transportEmit S
  legal := fun w a c e k neg h hh => transportEmit_legal S w a c e neg k h hh
  correct := fun w a c e k neg he hk => transportEmit_correct S w a c e neg k he hk
  clean := fun w a c e k neg he hk => transportEmit_clean S w a c e neg k he hk
  bounded := transportEmit_bounded S

/-- The transported synthesizer's next segment is accepted for every request with precision at
least one. -/
theorem frontier1 (S : ScalarPhaseSynthesizer) :
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      Accepts w g k (nextSegment (transportSynth S) w g k) := by
  intro w g k hk
  cases g with
  | h a => exact nextSegment_accepts_primitive _ (.h a) k (by simp [IsFixedPrim])
  | swap a c => exact nextSegment_accepts_primitive _ (.swap a c) k (by simp [IsFixedPrim])
  | cp a c e neg =>
      by_cases he4 : 4 ≤ e
      · exact nextSegment_accepts_middleWindow _ a c e neg k hk he4
      · exact nextSegment_accepts_primitive _ (.cp a c e neg) k (by
          simp only [IsFixedPrim]
          omega)

/-- The transported synthesizer's next segment uses at most one additional wire. -/
theorem frontier1_ancilla (S : ScalarPhaseSynthesizer) (w : ℕ) (g : LocalQFTGate w)
    (k : ℕ) : (nextSegment (transportSynth S) w g k).width ≤ w + 1 := by
  cases g with
  | h a => simp [nextSegment, effectiveEmit, effectiveAnc]
  | swap a c => simp [nextSegment, effectiveEmit, effectiveAnc]
  | cp a c e neg =>
      by_cases he4 : 4 ≤ e
      · rw [nextSegment_cp_ge4 _ a c e neg k he4]
      · rw [nextSegment_cp_lt4 _ a c e neg k he4]
        exact Nat.le_succ w

/-- An explicit polynomial scalar length bound gives the stated polynomial gate ledger bound for
the next segment. -/
theorem frontier1_ledger (S : ScalarPhaseSynthesizer) (C₀ D₀ : ℕ)
    (hC₀ : ∀ (neg : Bool) (e k : ℕ), 4 ≤ e → 1 ≤ k →
      (S.emit neg e k).length ≤ C₀ * (e + k) ^ D₀) :
    ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k →
      (nextSegment (transportSynth S) w g k).word.length
        ≤ (23 + C₀ * 2 ^ D₀) * (requestSize w g k) ^ (D₀ + 1) := by
  intro w g k hk
  have hrs : 1 ≤ requestSize w g k := requestSize_pos g k
  have hpow1 : 1 ≤ (requestSize w g k) ^ (D₀ + 1) := one_le_pow_nat hrs (D₀ + 1)
  have hbase : 1 ≤ (23 + C₀ * 2 ^ D₀) * (requestSize w g k) ^ (D₀ + 1) := by
    have h1 : 1 ≤ 23 + C₀ * 2 ^ D₀ := by omega
    nlinarith [h1, hpow1]
  cases g with
  | h a =>
      have hlen : (nextSegment (transportSynth S) w (.h a) k).word.length ≤ 1 := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      calc (nextSegment (transportSynth S) w (.h a) k).word.length ≤ 1 := hlen
        _ ≤ (23 + C₀ * 2 ^ D₀) * (requestSize w (.h a) k) ^ (D₀ + 1) := hbase
  | swap a c =>
      have hlen : (nextSegment (transportSynth S) w (.swap a c) k).word.length ≤ 1 := by
        simp [nextSegment, effectiveEmit, effectiveAnc]
      calc (nextSegment (transportSynth S) w (.swap a c) k).word.length ≤ 1 := hlen
        _ ≤ (23 + C₀ * 2 ^ D₀) * (requestSize w (.swap a c) k) ^ (D₀ + 1) := hbase
  | cp a c e neg =>
      by_cases he4 : 4 ≤ e
      · have hb := transportEmit_bounded_explicit S C₀ D₀ hC₀ w a c e k neg he4 hk
        have hmono : (requestSize w (.cp a c e neg) k) ^ D₀
            ≤ (requestSize w (.cp a c e neg) k) ^ (D₀ + 1) := by
          exact Nat.pow_le_pow_right (by omega) (Nat.le_succ D₀)
        calc (nextSegment (transportSynth S) w (.cp a c e neg) k).word.length
            = (transportEmit S w a c e neg k).length := by
              rw [nextSegment_cp_ge4 _ a c e neg k he4]
              rfl
          _ ≤ (22 + C₀ * 2 ^ D₀) * (requestSize w (.cp a c e neg) k) ^ D₀ := hb
          _ ≤ (22 + C₀ * 2 ^ D₀) * (requestSize w (.cp a c e neg) k) ^ (D₀ + 1) :=
              Nat.mul_le_mul_left _ hmono
          _ ≤ (23 + C₀ * 2 ^ D₀) * (requestSize w (.cp a c e neg) k) ^ (D₀ + 1) := by
              gcongr
              omega
      · have hlen : (nextSegment (transportSynth S) w (.cp a c e neg) k).word.length ≤ 1 := by
          rw [nextSegment_cp_lt4 _ a c e neg k he4]
          have he3 : e ≤ 3 := by omega
          simp [effectiveEmit, effectiveAnc, he3]
        calc (nextSegment (transportSynth S) w (.cp a c e neg) k).word.length ≤ 1 := hlen
          _ ≤ (23 + C₀ * 2 ^ D₀) * (requestSize w (.cp a c e neg) k) ^ (D₀ + 1) := hbase

/-- Expands a product of one-wire matrices as a sum over the false and true intermediate
registers. -/
theorem mul_apply2 (A B : Matrix (Reg 1) (Reg 1) ℂ) (y x : Reg 1) :
    (A * B) y x = A y (fun _ => false) * B (fun _ => false) x
      + A y (fun _ => true) * B (fun _ => true) x := by
  rw [Matrix.mul_apply, sum_reg1]

/-- Any two one-wire registers agree at every index distinct from zero. -/
theorem vacuous_ne_zero {y x : Reg 1} : ∀ k : Fin 1, k ≠ (0 : Fin 1) → y k = x k := by
  intro k hk
  exact absurd (fin1_eq k) hk

/-- The constantly false one-wire register differs from the constantly true register. -/
theorem basis_ne : (fun _ : Fin 1 => false) ≠ (fun _ : Fin 1 => true) := by
  intro h
  have h0 := congrFun h (⟨0, by omega⟩ : Fin 1)
  simp at h0

/-- The constantly true one-wire register differs from the constantly false register. -/
theorem basis_ne' : (fun _ : Fin 1 => true) ≠ (fun _ : Fin 1 => false) :=
  Ne.symm basis_ne

/-- Multiplying each of two complex factors by the imaginary unit negates their product. -/
theorem I_mul_I_mul (p q : ℂ) : Complex.I * p * (Complex.I * q) = -(p * q) := by
  rw [show Complex.I * p * (Complex.I * q) = (Complex.I * Complex.I) * (p * q) by ring,
    Complex.I_mul_I, neg_one_mul]

/-- Multiplication on the left by the imaginary unit and on the right by its negative cancels. -/
theorem I_mul_negI_mul (p : ℂ) : Complex.I * p * (-Complex.I) = p := by
  rw [show Complex.I * p * (-Complex.I) = (Complex.I * Complex.I) * p * (-(1 : ℂ)) by ring,
    Complex.I_mul_I]
  ring

/-- The false-to-false entry of the one-wire identity matrix is one. -/
theorem one_00 : (1 : Matrix (Reg 1) (Reg 1) ℂ) (fun _ => false) (fun _ => false) = 1 := by
  rw [Matrix.one_apply, ite_eq_left rfl]

/-- The true-to-true entry of the one-wire identity matrix is one. -/
theorem one_11 : (1 : Matrix (Reg 1) (Reg 1) ℂ) (fun _ => true) (fun _ => true) = 1 := by
  rw [Matrix.one_apply, ite_eq_left rfl]

/-- The false-row, true-column entry of the one-wire identity matrix is zero. -/
theorem one_01 : (1 : Matrix (Reg 1) (Reg 1) ℂ) (fun _ => false) (fun _ => true) = 0 := by
  rw [Matrix.one_apply, ite_eq_right basis_ne]

/-- The true-row, false-column entry of the one-wire identity matrix is zero. -/
theorem one_10 : (1 : Matrix (Reg 1) (Reg 1) ℂ) (fun _ => true) (fun _ => false) = 0 := by
  rw [Matrix.one_apply, ite_eq_right basis_ne']

def rotX (a : ℝ) : Matrix (Reg 1) (Reg 1) ℂ := Matrix.of fun y x =>
  if y = x then (Real.cos a : ℂ) else Complex.I * (Real.sin a : ℂ)

def rotY (a : ℝ) : Matrix (Reg 1) (Reg 1) ℂ := Matrix.of fun y x =>
  if y = x then (Real.cos a : ℂ)
  else if x ⟨0, by omega⟩ then (Real.sin a : ℂ) else (-(Real.sin a) : ℂ)

def rotZ (a : ℝ) : Matrix (Reg 1) (Reg 1) ℂ := Matrix.of fun y x =>
  if y = x then Complex.exp ((if x ⟨0, by omega⟩ then -a else a) * Complex.I) else 0

/-- Gives the entrywise formula for `rotX` in the one-wire computational basis. -/
theorem rotX_apply (a : ℝ) (y x : Reg 1) :
    rotX a y x = if y = x then (Real.cos a : ℂ) else Complex.I * (Real.sin a : ℂ) := rfl

/-- Gives the entrywise formula for `rotY` in the one-wire computational basis. -/
theorem rotY_apply (a : ℝ) (y x : Reg 1) :
    rotY a y x = if y = x then (Real.cos a : ℂ)
  else if x ⟨0, by omega⟩ then (Real.sin a : ℂ) else (-(Real.sin a) : ℂ) := rfl

/-- Gives the entrywise formula for `rotZ` in the one-wire computational basis. -/
theorem rotZ_apply (a : ℝ) (y x : Reg 1) :
    rotZ a y x = if y = x then Complex.exp ((if x ⟨0, by omega⟩ then -a else a) * Complex.I)
      else 0 := rfl

/-- The entry of `rotX` at row 0, column 0 is the cosine of the angle. -/
theorem rotX_00 (a : ℝ) : rotX a (fun _ => false) (fun _ => false) = (Real.cos a : ℂ) := by
  rw [rotX_apply, ite_eq_left rfl]

/-- The entry of `rotX` at row 1, column 1 is the cosine of the angle. -/
theorem rotX_11 (a : ℝ) : rotX a (fun _ => true) (fun _ => true) = (Real.cos a : ℂ) := by
  rw [rotX_apply, ite_eq_left rfl]

/-- The entry of `rotX` at row 0, column 1 is the imaginary unit times the sine of the angle. -/
theorem rotX_01 (a : ℝ) :
    rotX a (fun _ => false) (fun _ => true) = Complex.I * (Real.sin a : ℂ) := by
  rw [rotX_apply, ite_eq_right basis_ne]

/-- The entry of `rotX` at row 1, column 0 is the imaginary unit times the sine of the angle. -/
theorem rotX_10 (a : ℝ) :
    rotX a (fun _ => true) (fun _ => false) = Complex.I * (Real.sin a : ℂ) := by
  rw [rotX_apply, ite_eq_right basis_ne']

/-- The entry of `rotY` at row 0, column 0 is the cosine of the angle. -/
theorem rotY_00 (a : ℝ) : rotY a (fun _ => false) (fun _ => false) = (Real.cos a : ℂ) := by
  rw [rotY_apply, ite_eq_left rfl]

/-- The entry of `rotY` at row 1, column 1 is the cosine of the angle. -/
theorem rotY_11 (a : ℝ) : rotY a (fun _ => true) (fun _ => true) = (Real.cos a : ℂ) := by
  rw [rotY_apply, ite_eq_left rfl]

/-- The entry of `rotY` at row 0, column 1 is the sine of the angle. -/
theorem rotY_01 (a : ℝ) :
    rotY a (fun _ => false) (fun _ => true) = (Real.sin a : ℂ) := by
  rw [rotY_apply, ite_eq_right basis_ne]
  show (if (fun _ : Fin 1 => true) ⟨0, by omega⟩ = true then (Real.sin a : ℂ)
      else (-(Real.sin a) : ℂ)) = _
  rw [ite_eq_left rfl]

/-- The entry of `rotY` at row 1, column 0 is the negative sine of the angle. -/
theorem rotY_10 (a : ℝ) :
    rotY a (fun _ => true) (fun _ => false) = (-(Real.sin a) : ℂ) := by
  rw [rotY_apply, ite_eq_right basis_ne']
  show (if (fun _ : Fin 1 => false) ⟨0, by omega⟩ = true then (Real.sin a : ℂ)
      else (-(Real.sin a) : ℂ)) = _
  rw [ite_eq_right (by decide)]

/-- The entry of `rotZ` at row 0, column 0 is the complex exponential of the angle times the
imaginary unit. -/
theorem rotZ_00 (a : ℝ) :
    rotZ a (fun _ => false) (fun _ => false) = Complex.exp (a * Complex.I) := by
  rw [rotZ_apply, ite_eq_left rfl]
  simp

/-- The entry of `rotZ` at row 1, column 1 is the complex exponential of the negated angle times
the imaginary unit. -/
theorem rotZ_11 (a : ℝ) :
    rotZ a (fun _ => true) (fun _ => true) = Complex.exp ((-a) * Complex.I) := by
  rw [rotZ_apply, ite_eq_left rfl]
  simp

/-- The entry of `rotZ` at row 0, column 1 is zero. -/
theorem rotZ_01 (a : ℝ) : rotZ a (fun _ => false) (fun _ => true) = 0 := by
  rw [rotZ_apply, ite_eq_right basis_ne]

/-- The entry of `rotZ` at row 1, column 0 is zero. -/
theorem rotZ_10 (a : ℝ) : rotZ a (fun _ => true) (fun _ => false) = 0 := by
  rw [rotZ_apply, ite_eq_right basis_ne']

/-- `rotX` at angle zero is the identity matrix. -/
theorem rotX_zero : rotX 0 = 1 := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [rotX_00, rotX_01, rotX_10, rotX_11, one_00, one_01, one_10, one_11,
      Real.cos_zero, Real.sin_zero, mul_zero, Complex.ofReal_one, Complex.ofReal_zero,
      zero_mul]

/-- `rotY` at angle zero is the identity matrix. -/
theorem rotY_zero : rotY 0 = 1 := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [rotY_00, rotY_01, rotY_10, rotY_11, one_00, one_01, one_10, one_11,
      Real.cos_zero, Real.sin_zero, Complex.ofReal_one, Complex.ofReal_zero,
      zero_mul, neg_zero]

/-- `rotZ` at angle zero is the identity matrix. -/
theorem rotZ_zero : rotZ 0 = 1 := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [rotZ_00, rotZ_01, rotZ_10, rotZ_11, one_00, one_01, one_10, one_11,
      Complex.exp_zero, Complex.ofReal_zero, zero_mul, neg_zero]

/-- Negating the angle of `rotX` gives its conjugate transpose. -/
theorem rotX_neg (a : ℝ) : rotX (-a) = (rotX a)ᴴ := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [Matrix.conjTranspose_apply, Complex.star_def, rotX_00, rotX_01, rotX_10,
      rotX_11, Real.cos_neg, Real.sin_neg, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, Complex.ofReal_neg]
  all_goals ring

/-- Negating the angle of `rotY` gives its conjugate transpose. -/
theorem rotY_neg (a : ℝ) : rotY (-a) = (rotY a)ᴴ := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [Matrix.conjTranspose_apply, Complex.star_def, rotY_00, rotY_01, rotY_10,
      rotY_11, Real.cos_neg, Real.sin_neg, map_mul, map_neg, Complex.conj_I,
      Complex.conj_ofReal, Complex.ofReal_neg]
  all_goals ring

/-- Negating the angle of `rotZ` gives its conjugate transpose. -/
theorem rotZ_neg (a : ℝ) : rotZ (-a) = (rotZ a)ᴴ := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [Matrix.conjTranspose_apply, Complex.star_def, rotZ_00, rotZ_01, rotZ_10,
      rotZ_11, map_mul, map_zero]
  all_goals
    first
      | rfl
      | (rw [← Complex.exp_conj];
          simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
            Complex.ofReal_neg];
          congr 1;
          ring)

/-- Multiplying two `rotX` matrices adds their angles. -/
theorem rotX_mul (a b : ℝ) : rotX a * rotX b = rotX (a + b) := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    rw [mul_apply2] <;>
    simp only [rotX_00, rotX_01, rotX_10, rotX_11, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_neg, Complex.ofReal_add, I_mul_I_mul, Complex.cos_add,
      Complex.sin_add] <;>
    ring

/-- Multiplying two `rotY` matrices adds their angles. -/
theorem rotY_mul (a b : ℝ) : rotY a * rotY b = rotY (a + b) := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    rw [mul_apply2] <;>
    simp only [rotY_00, rotY_01, rotY_10, rotY_11, Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.ofReal_neg, Complex.ofReal_add, Complex.cos_add, Complex.sin_add] <;>
    ring

/-- Multiplying two `rotZ` matrices adds their angles. -/
theorem rotZ_mul (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    rw [mul_apply2] <;>
    simp only [rotZ_00, rotZ_01, rotZ_10, rotZ_11, zero_mul, mul_zero, add_zero, zero_add,
      one_mul, mul_one] <;>
    first
      | rfl
      | (rw [← Complex.exp_add]; congr 1; push_cast; ring)

/-- Every `rotX` matrix is unitary. -/
theorem rotX_unitary (a : ℝ) : rotX a ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← rotX_neg, rotX_mul,
    show (-a) + a = 0 from by ring, rotX_zero]

/-- Every `rotY` matrix is unitary. -/
theorem rotY_unitary (a : ℝ) : rotY a ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← rotY_neg, rotY_mul,
    show (-a) + a = 0 from by ring, rotY_zero]

/-- Every `rotZ` matrix is unitary. -/
theorem rotZ_unitary (a : ℝ) : rotZ a ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← rotZ_neg, rotZ_mul,
    show (-a) + a = 0 from by ring, rotZ_zero]

/-- Every `rotX` matrix has norm one. -/
theorem rotX_norm (a : ℝ) : ‖rotX a‖ = 1 := l2_norm_unitary_eq_one (rotX_unitary a)

/-- Every `rotY` matrix has norm one. -/
theorem rotY_norm (a : ℝ) : ‖rotY a‖ = 1 := l2_norm_unitary_eq_one (rotY_unitary a)

/-- Every `rotZ` matrix has norm one. -/
theorem rotZ_norm (a : ℝ) : ‖rotZ a‖ = 1 := l2_norm_unitary_eq_one (rotZ_unitary a)

/-- The constantly false one-wire register evaluates to false at zero. -/
theorem bit_false : (fun _ : Fin 1 => false) (0 : Fin 1) = false := rfl

/-- The constantly true one-wire register evaluates to true at zero. -/
theorem bit_true : (fun _ : Fin 1 => true) (0 : Fin 1) = true := rfl

/-- The false-to-false Hadamard entry is the inverse square root of two. -/
theorem hadamard_ff : Hadamard false false = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Hadamard]

/-- The false-row, true-column Hadamard entry is the inverse square root of two. -/
theorem hadamard_ft : Hadamard false true = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Hadamard]

/-- The true-row, false-column Hadamard entry is the inverse square root of two. -/
theorem hadamard_tf : Hadamard true false = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Hadamard]

/-- The true-to-true Hadamard entry is the negative inverse square root of two. -/
theorem hadamard_tt : Hadamard true true = -((Real.sqrt 2 : ℂ)⁻¹) := by
  simp [Hadamard]

/-- A one-wire Hadamard gate's entries are the corresponding Boolean Hadamard entries. -/
theorem h1_entries (y x : Reg 1) :
    localGateMatrix (.h (0 : Fin 1)) y x = Hadamard (y (0 : Fin 1)) (x (0 : Fin 1)) := by
  rw [localGateMatrix_h]
  rw [ite_eq_left (vacuous_ne_zero (y := y) (x := x))]

/-- Sandwiching a complex scalar between two inverse square roots of two gives half that scalar. -/
theorem inv_sqrt2_mul_mid (X : ℂ) :
    (Real.sqrt 2 : ℂ)⁻¹ * X * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ * X := by
  rw [show (Real.sqrt 2 : ℂ)⁻¹ * X * (Real.sqrt 2 : ℂ)⁻¹
      = ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) * X by ring,
    inv_sqrt2_mul_self]

/-- Multiplying a complex scalar twice by the imaginary unit negates it. -/
theorem I_mul_smul_I (X : ℂ) : Complex.I * (X * Complex.I) = -X := by
  rw [show Complex.I * (X * Complex.I) = (Complex.I * Complex.I) * X by ring,
    Complex.I_mul_I, neg_one_mul]

/-- The half-sum of opposite imaginary exponentials is the cosine. -/
theorem half_exp_cos (u : ℝ) :
    (2 : ℂ)⁻¹ * Complex.exp (u * Complex.I)
      + (2 : ℂ)⁻¹ * Complex.exp (-(u * Complex.I))
      = (Real.cos u : ℂ) := by
  rw [Complex.ofReal_cos]
  have hbody : Complex.cos (u : ℂ)
      = (Complex.exp ((u : ℂ) * Complex.I)
          + Complex.exp (-(u : ℂ) * Complex.I)) / 2 := rfl
  have hneg : Complex.exp (-(u * Complex.I)) = Complex.exp (-(u : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hbody, hneg]
  ring

/-- The half-difference of opposite imaginary exponentials is the imaginary unit times the sine. -/
theorem half_exp_sin (u : ℝ) :
    (2 : ℂ)⁻¹ * Complex.exp (u * Complex.I)
      - (2 : ℂ)⁻¹ * Complex.exp (-(u * Complex.I))
      = Complex.I * (Real.sin u : ℂ) := by
  rw [Complex.ofReal_sin]
  have hbody : Complex.sin (u : ℂ)
      = (Complex.exp (-(u : ℂ) * Complex.I) - Complex.exp ((u : ℂ) * Complex.I))
          * Complex.I / 2 := rfl
  have hneg : Complex.exp (-(u * Complex.I)) = Complex.exp (-(u : ℂ) * Complex.I) := by
    congr 1
    ring
  have key : Complex.I * ((Complex.exp (-(u : ℂ) * Complex.I)
        - Complex.exp ((u : ℂ) * Complex.I)) * Complex.I / 2)
      = -((Complex.exp (-(u : ℂ) * Complex.I) - Complex.exp ((u : ℂ) * Complex.I)) / 2) := by
    rw [show Complex.I * ((Complex.exp (-(u : ℂ) * Complex.I)
            - Complex.exp ((u : ℂ) * Complex.I)) * Complex.I / 2)
          = Complex.I * (((Complex.exp (-(u : ℂ) * Complex.I)
              - Complex.exp ((u : ℂ) * Complex.I)) / 2) * Complex.I) by ring,
      I_mul_smul_I]
  rw [hbody, key, hneg]
  ring

/-- Conjugating a Z rotation by Hadamard yields the X rotation with the same angle. -/
theorem h_rotZ_h (u : ℝ) :
    localGateMatrix (.h (0 : Fin 1)) * rotZ u * localGateMatrix (.h (0 : Fin 1)) = rotX u := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [mul_apply2, h1_entries, bit_false, bit_true, hadamard_ff, hadamard_ft,
      hadamard_tf, hadamard_tt, rotZ_00, rotZ_01, rotZ_10, rotZ_11, rotX_00, rotX_01,
      rotX_10, rotX_11, zero_mul, mul_zero, add_zero, zero_add, mul_neg, neg_mul, neg_neg,
      Complex.ofReal_neg, inv_sqrt2_mul_mid] <;>
    first
      | exact half_exp_cos u
      | exact half_exp_sin u

/-- The one-wire positive exponent-two phase gate is diagonal with entries one and the imaginary
unit. -/
theorem s1_matrix :
    localGateMatrix (.cp (0 : Fin 1) (0 : Fin 1) 2 false)
      = Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then Complex.I else 1) := by
  rw [cp_matrix_diag, exp_dyadicAngle_two_false]
  ext z w
  simp only [Matrix.diagonal_apply]
  by_cases hz : z = w
  · subst hz
    by_cases h : z (0 : Fin 1) <;> simp [h, Bool.and_self]
  · rw [ite_eq_right hz, ite_eq_right hz]

/-- The one-wire negative exponent-two phase gate is diagonal with entries one and the negative
imaginary unit. -/
theorem sAdj1_matrix :
    localGateMatrix (.cp (0 : Fin 1) (0 : Fin 1) 2 true)
      = Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then -Complex.I else 1) := by
  rw [cp_matrix_diag, exp_dyadicAngle_two_true]
  ext z w
  simp only [Matrix.diagonal_apply]
  by_cases hz : z = w
  · subst hz
    by_cases h : z (0 : Fin 1) <;> simp [h, Bool.and_self]
  · rw [ite_eq_right hz, ite_eq_right hz]

/-- Conjugating an X rotation by the displayed S phase matrices yields the Y rotation with the
same angle. -/
theorem s_rotX_sAdj (u : ℝ) :
    (Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then Complex.I else 1) : _)
      * rotX u
      * (Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then -Complex.I else 1) : _)
      = rotY u := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [mul_apply2, Matrix.diagonal_mul, Matrix.mul_diagonal, rotX_00, rotX_01,
      rotX_10, rotX_11, rotY_00, rotY_01, rotY_10, rotY_11, Matrix.diagonal_apply,
      mul_one] <;>
    first
      | (rw [ite_eq_right (by decide), ite_eq_right (by decide)]; ring)
      | (rw [ite_eq_right (by decide), ite_eq_left trivial];
          simp only [one_mul, I_mul_negI_mul])
      | (rw [ite_eq_left trivial, ite_eq_right (by decide)];
          simp only [mul_one, ← mul_assoc, Complex.I_mul_I]; ring)
      | (rw [ite_eq_left trivial, ite_eq_left trivial]; simp only [I_mul_negI_mul])

/-- A diagonal one-wire phase equals a Z rotation by negative half the angle, multiplied by the
corresponding global phase. -/
theorem diag_phase_rotZ (θ : ℝ) :
    (Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then Complex.exp (θ * Complex.I)
      else 1) : Matrix (Reg 1) (Reg 1) ℂ)
      = Complex.exp (θ / 2 * Complex.I) • rotZ (-(θ / 2)) := by
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [Matrix.diagonal_apply, ite_eq_left rfl, ite_eq_right basis_ne, ite_eq_right basis_ne',
      ite_eq_right (show ¬((false : Bool) = true) from by decide), ite_true,
      Matrix.smul_apply, smul_eq_mul, rotZ_00, rotZ_01, rotZ_10, rotZ_11,
      zero_mul, mul_zero] <;>
    first
      | rfl
      | (rw [← Complex.exp_add,
          show Complex.ofReal θ / 2 * Complex.I
            + Complex.ofReal (-(θ / 2)) * Complex.I = 0 from by
            push_cast
            ring, Complex.exp_zero])
      | (rw [← Complex.exp_add]; congr 1; push_cast; ring)

def axisSign (s : Bool) : ℝ := if s then 1 else -1

/-- The axis sign of true is one. -/
theorem axisSign_true : axisSign true = 1 := rfl

/-- The axis sign of false is negative one. -/
theorem axisSign_false : axisSign false = -1 := rfl

/-- The exponent-three dyadic phase angle is negative `axisSign` times one quarter of pi. -/
theorem dyadicPhaseAngle_three (s : Bool) :
    dyadicPhaseAngle 3 s = -(axisSign s) * (Real.pi / 4) := by
  cases s
  · simp only [dyadicPhaseAngle, axisSign]
    rw [ite_eq_right (show ¬((false : Bool) = true) from by decide),
      ite_eq_right (show ¬((false : Bool) = true) from by decide)]
    ring
  · simp only [dyadicPhaseAngle, axisSign]
    norm_num
    ring

def tPow (j : ℕ) (s : Bool) : List (LocalQFTGate 1) :=
  List.replicate j (.cp (0 : Fin 1) (0 : Fin 1) 3 s)

/-- The T-power word has length equal to its exponent. -/
theorem tPow_length (j : ℕ) (s : Bool) : (tPow j s).length = j := by
  simp [tPow]

/-- Every gate in a T-power word is a fixed primitive. -/
theorem tPow_legal (j : ℕ) (s : Bool) : ∀ g ∈ tPow j s, IsFixedPrim g := by
  intro g hg
  simp only [tPow, List.mem_replicate] at hg
  obtain ⟨-, rfl⟩ := hg
  simp [IsFixedPrim]

/-- The T-power word is the diagonal phase matrix with the stated signed multiple of one quarter
of pi. -/
theorem tPow_diag (j : ℕ) (s : Bool) :
    localProgramMatrix (tPow j s)
      = Matrix.diagonal (fun x : Reg 1 =>
          if x (0 : Fin 1) = true then
            Complex.exp (-(axisSign s) * j * (Real.pi / 4) * Complex.I)
            else 1) := by
  induction j with
  | zero =>
      ext y x
      rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
        simp only [tPow, List.replicate, localProgramMatrix_nil, Matrix.one_apply,
          ite_eq_left rfl, ite_eq_right basis_ne, ite_eq_right basis_ne',
          ite_eq_right (show ¬((false : Bool) = true) from by decide), ite_true,
          Matrix.diagonal_apply, Nat.cast_zero, Complex.ofReal_zero, zero_mul, mul_zero,
          Complex.exp_zero]
  | succ n ih =>
      rw [show tPow (n + 1) s
          = LocalQFTGate.cp (0 : Fin 1) (0 : Fin 1) 3 s :: tPow n s from by
          simp [tPow, List.replicate_succ], localProgramMatrix_cons, ih, cp_matrix_diag,
        dyadicPhaseAngle_three]
      ext y x
      rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
        simp only [Matrix.diagonal_mul, Matrix.diagonal_apply, ite_eq_left rfl,
          ite_eq_right basis_ne, ite_eq_right basis_ne',
          ite_eq_right (show ¬((false : Bool) = true) from by decide), ite_true,
          Bool.and_self, mul_zero, mul_one, one_mul]
      all_goals
        first
          | rfl
          | (rw [← Complex.exp_add]; congr 1; push_cast; ring)

/-- The T-power word is the stated Z rotation multiplied by its explicit global phase. -/
theorem tPow_rotZ (j : ℕ) (s : Bool) :
    localProgramMatrix (tPow j s)
      = Complex.exp (Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I)
          • rotZ (axisSign s * j * (Real.pi / 8)) := by
  rw [tPow_diag]
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [Matrix.diagonal_apply, ite_eq_left rfl, ite_eq_right basis_ne, ite_eq_right basis_ne',
      ite_eq_right (show ¬((false : Bool) = true) from by decide), ite_true,
      Matrix.smul_apply, smul_eq_mul, rotZ_00, rotZ_01, rotZ_10, rotZ_11,
      zero_mul, mul_zero] <;>
    first
      | rfl
      | (rw [← Complex.exp_add,
          show Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I
            + Complex.ofReal (axisSign s * j * (Real.pi / 8)) * Complex.I = 0 from by
            push_cast
            ring, Complex.exp_zero])
      | (rw [← Complex.exp_add]; congr 1; push_cast; ring)

inductive Axis : Type
  | x : Axis
  | y : Axis
  | z : Axis

def rotAxis : Axis → ℝ → Matrix (Reg 1) (Reg 1) ℂ
  | Axis.x, a => rotX a
  | Axis.y, a => rotY a
  | Axis.z, a => rotZ a

/-- The X case of `rotAxis` is `rotX`. -/
theorem rotAxis_x (a : ℝ) : rotAxis Axis.x a = rotX a := rfl

/-- The Y case of `rotAxis` is `rotY`. -/
theorem rotAxis_y (a : ℝ) : rotAxis Axis.y a = rotY a := rfl

/-- The Z case of `rotAxis` is `rotZ`. -/
theorem rotAxis_z (a : ℝ) : rotAxis Axis.z a = rotZ a := rfl

def axisWord : Axis → Bool → ℕ → List (LocalQFTGate 1)
  | Axis.z, s, j => tPow j s
  | Axis.x, s, j => [.h (0 : Fin 1)] ++ tPow j s ++ [.h (0 : Fin 1)]
  | Axis.y, s, j =>
      [.cp (0 : Fin 1) (0 : Fin 1) 2 true] ++ [.h (0 : Fin 1)] ++ tPow j s
        ++ [.h (0 : Fin 1)] ++ [.cp (0 : Fin 1) (0 : Fin 1) 2 false]

/-- The Z-axis word is the T-power word. -/
theorem axisWord_z (s : Bool) (j : ℕ) : axisWord Axis.z s j = tPow j s := rfl

/-- The X-axis word is a T-power word surrounded by Hadamard gates. -/
theorem axisWord_x_eq (s : Bool) (j : ℕ) :
    axisWord Axis.x s j = [.h (0 : Fin 1)] ++ tPow j s ++ [.h (0 : Fin 1)] := rfl

/-- The Y-axis word is the X-axis word preceded by the adjoint S gate and followed by the S
gate. -/
theorem axisWord_y_eq (s : Bool) (j : ℕ) :
    axisWord Axis.y s j = [.cp (0 : Fin 1) (0 : Fin 1) 2 true] ++ axisWord Axis.x s j
      ++ [.cp (0 : Fin 1) (0 : Fin 1) 2 false] := by
  simp only [axisWord, List.append_assoc]

/-- The global phase in the T-power rotation formula has norm one. -/
theorem tPow_phase_norm (j : ℕ) (s : Bool) :
    ‖Complex.exp (Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I)‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The X-axis word implements the stated X rotation with the explicit global phase. -/
theorem axisWord_x_matrix (s : Bool) (j : ℕ) :
    localProgramMatrix (axisWord Axis.x s j)
      = Complex.exp (Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I)
          • rotX (axisSign s * j * (Real.pi / 8)) := by
  have hstep : localProgramMatrix (axisWord Axis.x s j)
      = localGateMatrix (.h (0 : Fin 1)) * localProgramMatrix (tPow j s)
        * localGateMatrix (.h (0 : Fin 1)) := by
    simp only [axisWord_x_eq, localProgramMatrix_append, localProgramMatrix_singleton,
      Matrix.mul_assoc]
  rw [hstep, tPow_rotZ, Matrix.mul_smul, Matrix.smul_mul, h_rotZ_h]

/-- Every axis word implements the corresponding signed rotation by a multiple of one eighth of
pi, up to a scalar of norm one. -/
theorem axisWord_matrix (ax : Axis) (s : Bool) (j : ℕ) :
    ∃ p : ℂ, ‖p‖ = 1 ∧ localProgramMatrix (axisWord ax s j)
      = p • rotAxis ax (axisSign s * j * (Real.pi / 8)) := by
  cases ax with
  | z =>
      refine ⟨Complex.exp (Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I),
        tPow_phase_norm j s, ?_⟩
      rw [axisWord_z, rotAxis_z]
      exact tPow_rotZ j s
  | x =>
      refine ⟨Complex.exp (Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I),
        tPow_phase_norm j s, ?_⟩
      rw [rotAxis_x]
      exact axisWord_x_matrix s j
  | y =>
      refine ⟨Complex.exp (Complex.ofReal (-(axisSign s) * j * (Real.pi / 8)) * Complex.I),
        tPow_phase_norm j s, ?_⟩
      rw [rotAxis_y]
      have hstep : localProgramMatrix (axisWord Axis.y s j)
          = Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then Complex.I else 1)
            * localProgramMatrix (axisWord Axis.x s j)
            * Matrix.diagonal (fun x : Reg 1 => if x (0 : Fin 1) = true then -Complex.I
                else 1) := by
        rw [axisWord_y_eq, localProgramMatrix_append, localProgramMatrix_append,
          localProgramMatrix_singleton, localProgramMatrix_singleton, s1_matrix,
          sAdj1_matrix, Matrix.mul_assoc]
      rw [hstep, axisWord_x_matrix, Matrix.mul_smul, Matrix.smul_mul, s_rotX_sAdj]

/-- The Z-axis word has length `j`. -/
theorem axisWord_length_z (s : Bool) (j : ℕ) : (axisWord Axis.z s j).length = j := by
  rw [axisWord_z, tPow_length]

/-- The X-axis word has length `j` plus two. -/
theorem axisWord_length_x (s : Bool) (j : ℕ) : (axisWord Axis.x s j).length = j + 2 := by
  simp only [axisWord_x_eq, List.length_append, List.length_singleton, tPow_length]
  omega

/-- The Y-axis word has length `j` plus four. -/
theorem axisWord_length_y (s : Bool) (j : ℕ) : (axisWord Axis.y s j).length = j + 4 := by
  simp only [axisWord_y_eq, List.length_append, List.length_singleton,
    axisWord_length_x]
  omega

/-- Every gate in the X-axis word is a fixed primitive. -/
theorem axisWord_x_legal (s : Bool) (j : ℕ) :
    ∀ g ∈ axisWord Axis.x s j, IsFixedPrim g := by
  intro g hg
  simp only [axisWord_x_eq, List.mem_append, List.mem_singleton, or_assoc] at hg
  rcases hg with h | h | h
  · subst h
    simp [IsFixedPrim]
  · exact tPow_legal j s g h
  · subst h
    simp [IsFixedPrim]

/-- Every gate in any axis word is a fixed primitive. -/
theorem axisWord_legal (ax : Axis) (s : Bool) (j : ℕ) :
    ∀ g ∈ axisWord ax s j, IsFixedPrim g := by
  intro g hg
  cases ax with
  | z =>
      rw [axisWord_z] at hg
      exact tPow_legal j s g hg
  | x => exact axisWord_x_legal s j g hg
  | y =>
      simp only [axisWord_y_eq, List.mem_append, List.mem_singleton, or_assoc] at hg
      rcases hg with h | h | h
      · subst h
        simp [IsFixedPrim]
      · exact axisWord_x_legal s j g h
      · subst h
        simp [IsFixedPrim]

/-- The adjoint program's matrix is the conjugate transpose of the original program matrix. -/
theorem localProgramAdjoint_matrix {n : ℕ} (gs : List (LocalQFTGate n)) :
    localProgramMatrix (localProgramAdjoint gs) = (localProgramMatrix gs)ᴴ :=
  (localDyadicProgram_run_adjoint_cost n gs (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))).2.1

/-- Every local gate word has a unitary program matrix. -/
theorem word_matrix_unitary {n : ℕ} (gs : List (LocalQFTGate n)) :
    localProgramMatrix gs ∈ Matrix.unitaryGroup (Reg n) ℂ :=
  (localDyadicProgram_run_adjoint_cost n gs (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))).2.2.2.2.1

/-- Every local gate word has program matrix norm one. -/
theorem word_matrix_norm {n : ℕ} (gs : List (LocalQFTGate n)) :
    ‖localProgramMatrix gs‖ = 1 :=
  l2_norm_unitary_eq_one (word_matrix_unitary gs)

/-- Taking the adjoint of a program preserves its length. -/
theorem localProgramAdjoint_length {n : ℕ} (gs : List (LocalQFTGate n)) :
    (localProgramAdjoint gs).length = gs.length := by
  simp [localProgramAdjoint, List.length_map, List.length_reverse]

/-- Taking the adjoint of a gate preserves the fixed primitive property. -/
theorem localGateAdjoint_fixedPrim {n : ℕ} {g : LocalQFTGate n} (hg : IsFixedPrim g) :
    IsFixedPrim (localGateAdjoint g) :=
  (isFixedPrim_adjoint_iff g).mpr hg

/-- Taking the adjoint of a program preserves the fixed primitive property of every gate. -/
theorem localProgramAdjoint_legal {n : ℕ} (gs : List (LocalQFTGate n))
    (hgs : ∀ g ∈ gs, IsFixedPrim g) :
    ∀ g ∈ localProgramAdjoint gs, IsFixedPrim g := by
  intro g hg
  simp only [localProgramAdjoint, List.mem_map, List.mem_reverse] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  exact localGateAdjoint_fixedPrim (hgs g' hg')

def commWord {n : ℕ} (V W : List (LocalQFTGate n)) : List (LocalQFTGate n) :=
  V ++ W ++ localProgramAdjoint V ++ localProgramAdjoint W

/-- The commutator word implements the product of the adjoints of `W` and `V`, followed by `W`
and `V`. -/
theorem commWord_matrix {n : ℕ} (V W : List (LocalQFTGate n)) :
    localProgramMatrix (commWord V W)
      = (localProgramMatrix W)ᴴ * (localProgramMatrix V)ᴴ
        * localProgramMatrix W * localProgramMatrix V := by
  rw [commWord, localProgramMatrix_append, localProgramMatrix_append,
    localProgramMatrix_append, localProgramAdjoint_matrix, localProgramAdjoint_matrix]
  simp only [Matrix.mul_assoc]

/-- The commutator word has twice the sum of its input lengths. -/
theorem commWord_length {n : ℕ} (V W : List (LocalQFTGate n)) :
    (commWord V W).length = 2 * (V.length + W.length) := by
  rw [commWord, List.length_append, List.length_append, List.length_append,
    localProgramAdjoint_length, localProgramAdjoint_length]
  omega

/-- The commutator word uses only fixed primitives when both input words do. -/
theorem commWord_legal {n : ℕ} (V W : List (LocalQFTGate n))
    (hV : ∀ g ∈ V, IsFixedPrim g) (hW : ∀ g ∈ W, IsFixedPrim g) :
    ∀ g ∈ commWord V W, IsFixedPrim g := by
  intro g hg
  simp only [commWord, List.mem_append, or_assoc] at hg
  rcases hg with h | h | h | h
  · exact hV g h
  · exact hW g h
  · exact localProgramAdjoint_legal V hV g h
  · exact localProgramAdjoint_legal W hW g h

/-- Factors scalar coefficients out of the commutator of a scaled Z rotation and a scaled X
rotation. -/
theorem comm_smul_rot (q p : ℂ) (a b : ℝ) :
    ((q • rotZ b)ᴴ * (p • rotX a)ᴴ * (q • rotZ b) * (p • rotX a))
      = (star q * star p * q * p) • (rotZ (-b) * rotX (-a) * rotZ b * rotX a) := by
  simp only [Matrix.conjTranspose_smul, ← rotZ_neg, ← rotX_neg, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, mul_assoc]
  congr 1
  ring

/-- The commutator of X-axis and Z-axis words implements the displayed rotation commutator up to
a scalar of norm one. -/
theorem commWord_axisWord_matrix (sx sz : Bool) (jx jz : ℕ) :
    ∃ r : ℂ, ‖r‖ = 1 ∧
      localProgramMatrix (commWord (axisWord Axis.x sx jx) (axisWord Axis.z sz jz))
        = r • (rotZ (-(axisSign sz * jz * (Real.pi / 8)))
            * rotX (-(axisSign sx * jx * (Real.pi / 8)))
            * rotZ (axisSign sz * jz * (Real.pi / 8))
            * rotX (axisSign sx * jx * (Real.pi / 8))) := by
  obtain ⟨pV, hpV1, hpV2⟩ := axisWord_matrix Axis.x sx jx
  obtain ⟨pW, hpW1, hpW2⟩ := axisWord_matrix Axis.z sz jz
  rw [rotAxis_x] at hpV2
  rw [rotAxis_z] at hpW2
  refine ⟨star pW * star pV * pW * pV, ?_, ?_⟩
  · rw [norm_mul, norm_mul, norm_mul, norm_star, norm_star, hpW1, hpV1]
    norm_num
  · rw [commWord_matrix, hpW2, hpV2]
    exact comm_smul_rot pW pV _ _

/-- The scalar factors in a commutator cancel when both have norm one. -/
theorem phase_comm_cancel {q p : ℂ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1) :
    star q * star p * q * p = 1 := by
  have hq' : star q * q = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hq]
    norm_num
  have hp' : star p * p = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hp]
    norm_num
  rw [show star q * star p * q * p = star q * q * (star p * p) by ring, hq', hp', mul_one]

/-- The commutator of phase-scaled X and Z rotations equals the unscaled rotation commutator
when both phases have norm one. -/
theorem comm_smul_rot_exact {q p : ℂ} (hq : ‖q‖ = 1) (hp : ‖p‖ = 1) (a b : ℝ) :
    (q • rotZ b)ᴴ * (p • rotX a)ᴴ * (q • rotZ b) * (p • rotX a)
      = rotZ (-b) * rotX (-a) * rotZ b * rotX a := by
  rw [comm_smul_rot q p a b, phase_comm_cancel hq hp, one_smul]

/-- The commutator of X-axis and Z-axis words equals the displayed rotation commutator exactly. -/
theorem commWord_axisWord_matrix_exact (sx sz : Bool) (jx jz : ℕ) :
    localProgramMatrix (commWord (axisWord Axis.x sx jx) (axisWord Axis.z sz jz))
      = rotZ (-(axisSign sz * jz * (Real.pi / 8))) * rotX (-(axisSign sx * jx * (Real.pi / 8)))
        * rotZ (axisSign sz * jz * (Real.pi / 8)) * rotX (axisSign sx * jx * (Real.pi / 8)) := by
  obtain ⟨pV, hpV1, hpV2⟩ := axisWord_matrix Axis.x sx jx
  obtain ⟨pW, hpW1, hpW2⟩ := axisWord_matrix Axis.z sz jz
  rw [rotAxis_x] at hpV2
  rw [rotAxis_z] at hpW2
  rw [commWord_matrix, hpW2, hpV2]
  exact comm_smul_rot_exact hpW1 hpV1 _ _

def commRot (a b : ℝ) : Matrix (Reg 1) (Reg 1) ℂ :=
  rotZ (-b) * rotX (-a) * rotZ b * rotX a

/-- Reassociates `commRot` into a product of two rotation pairs. -/
theorem commRot_eq (a b : ℝ) :
    commRot a b = (rotZ (-b) * rotX (-a)) * (rotZ b * rotX a) := by
  rw [commRot, Matrix.mul_assoc]

/-- The false-to-false entry of a Z rotation times an X rotation is the positive phase times the
cosine. -/
theorem rotZ_mul_rotX_ff_ff (c d : ℝ) :
    (rotZ c * rotX d) (fun _ => false) (fun _ => false)
      = Complex.exp (c * Complex.I) * (Real.cos d : ℂ) := by
  rw [mul_apply2, rotZ_00, rotX_00, rotZ_01, zero_mul, add_zero]

/-- The false-row, true-column entry of a Z rotation times an X rotation is the positive phase
times the imaginary sine. -/
theorem rotZ_mul_rotX_ff_tt (c d : ℝ) :
    (rotZ c * rotX d) (fun _ => false) (fun _ => true)
      = Complex.exp (c * Complex.I) * (Complex.I * (Real.sin d : ℂ)) := by
  rw [mul_apply2, rotZ_00, rotX_01, rotZ_01, zero_mul, add_zero]

/-- The true-row, false-column entry of a Z rotation times an X rotation is the negative phase
times the imaginary sine. -/
theorem rotZ_mul_rotX_tt_ff (c d : ℝ) :
    (rotZ c * rotX d) (fun _ => true) (fun _ => false)
      = Complex.exp ((-c) * Complex.I) * (Complex.I * (Real.sin d : ℂ)) := by
  rw [mul_apply2, rotZ_10, rotX_10, rotZ_11, zero_mul, zero_add]

/-- The true-to-true entry of a Z rotation times an X rotation is the negative phase times the
cosine. -/
theorem rotZ_mul_rotX_tt_tt (c d : ℝ) :
    (rotZ c * rotX d) (fun _ => true) (fun _ => true)
      = Complex.exp ((-c) * Complex.I) * (Real.cos d : ℂ) := by
  rw [mul_apply2, rotZ_10, rotX_11, rotZ_11, zero_mul, zero_add]

/-- The sum of the squared complex cosine and sine of a real argument is one. -/
theorem cos_sin_sq_complex (x : ℝ) :
    (Complex.cos (x : ℂ)) ^ 2 + (Complex.sin (x : ℂ)) ^ 2 = 1 := by
  rw [add_comm]
  exact Complex.sin_sq_add_cos_sq (x : ℂ)

/-- Gives the real and imaginary parts of the false-to-false entry of `commRot` as trigonometric
products. -/
theorem commRot_00 (a b : ℝ) :
    commRot a b (fun _ => false) (fun _ => false)
      = ((1 - 2 * Real.sin a * Real.sin a * Real.sin b * Real.sin b : ℝ) : ℂ)
        + ((-2 * Real.sin a * Real.sin a * Real.sin b * Real.cos b : ℝ) : ℂ) * Complex.I := by
  have hI2 : Complex.I * Complex.I = -(1 : ℂ) := Complex.I_mul_I
  have hca2 := cos_sin_sq_complex a
  have hcb2 := cos_sin_sq_complex b
  rw [commRot_eq,
    mul_apply2 (rotZ (-b) * rotX (-a)) (rotZ b * rotX a) (fun _ => false) (fun _ => false),
    rotZ_mul_rotX_ff_ff (-b) (-a), rotZ_mul_rotX_ff_tt (-b) (-a),
    rotZ_mul_rotX_ff_ff b a, rotZ_mul_rotX_tt_ff b a]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_neg, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  linear_combination
    (-(Complex.I * Complex.I) * (Complex.sin (a : ℂ)) ^ 2 * (Complex.sin (b : ℂ)) ^ 2
      + 2 * Complex.I * (Complex.sin (a : ℂ)) ^ 2 * Complex.cos (b : ℂ) * Complex.sin (b : ℂ)
      - (Complex.cos (a : ℂ)) ^ 2 * (Complex.sin (b : ℂ)) ^ 2
      - (Complex.sin (a : ℂ)) ^ 2 * (Complex.cos (b : ℂ)) ^ 2
      + (Complex.sin (a : ℂ)) ^ 2 * (Complex.sin (b : ℂ)) ^ 2) * hI2
    + ((Complex.cos (b : ℂ)) ^ 2 + (Complex.sin (b : ℂ)) ^ 2) * hca2 + hcb2

/-- Gives the real and imaginary parts of the true-to-true entry of `commRot` as trigonometric
products. -/
theorem commRot_11 (a b : ℝ) :
    commRot a b (fun _ => true) (fun _ => true)
      = ((1 - 2 * Real.sin a * Real.sin a * Real.sin b * Real.sin b : ℝ) : ℂ)
        + ((2 * Real.sin a * Real.sin a * Real.sin b * Real.cos b : ℝ) : ℂ) * Complex.I := by
  have hI2 : Complex.I * Complex.I = -(1 : ℂ) := Complex.I_mul_I
  have hca2 := cos_sin_sq_complex a
  have hcb2 := cos_sin_sq_complex b
  rw [commRot_eq,
    mul_apply2 (rotZ (-b) * rotX (-a)) (rotZ b * rotX a) (fun _ => true) (fun _ => true),
    rotZ_mul_rotX_tt_ff (-b) (-a), rotZ_mul_rotX_ff_tt b a,
    rotZ_mul_rotX_tt_tt (-b) (-a), rotZ_mul_rotX_tt_tt b a]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_neg, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  linear_combination
    (-(Complex.I * Complex.I) * (Complex.sin (a : ℂ)) ^ 2 * (Complex.sin (b : ℂ)) ^ 2
      - 2 * Complex.I * (Complex.sin (a : ℂ)) ^ 2 * Complex.cos (b : ℂ) * Complex.sin (b : ℂ)
      - (Complex.cos (a : ℂ)) ^ 2 * (Complex.sin (b : ℂ)) ^ 2
      - (Complex.sin (a : ℂ)) ^ 2 * (Complex.cos (b : ℂ)) ^ 2
      + (Complex.sin (a : ℂ)) ^ 2 * (Complex.sin (b : ℂ)) ^ 2) * hI2
    + ((Complex.cos (b : ℂ)) ^ 2 + (Complex.sin (b : ℂ)) ^ 2) * hca2 + hcb2

/-- Gives the real and imaginary parts of the false-row, true-column entry of `commRot` as
trigonometric products. -/
theorem commRot_01 (a b : ℝ) :
    commRot a b (fun _ => false) (fun _ => true)
      = ((-2 * Real.sin a * Real.sin b * Real.cos a * Real.cos b : ℝ) : ℂ)
        + ((2 * Real.sin a * Real.cos a * Real.sin b * Real.sin b : ℝ) : ℂ) * Complex.I := by
  have hI2 : Complex.I * Complex.I = -(1 : ℂ) := Complex.I_mul_I
  have hca2 := cos_sin_sq_complex a
  have hcb2 := cos_sin_sq_complex b
  rw [commRot_eq,
    mul_apply2 (rotZ (-b) * rotX (-a)) (rotZ b * rotX a) (fun _ => false) (fun _ => true),
    rotZ_mul_rotX_ff_ff (-b) (-a), rotZ_mul_rotX_ff_tt b a,
    rotZ_mul_rotX_ff_tt (-b) (-a), rotZ_mul_rotX_tt_tt b a]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_neg, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  linear_combination
    (-2 * Complex.I * Complex.cos (a : ℂ) * Complex.sin (a : ℂ) * (Complex.sin (b : ℂ)) ^ 2
      + 2 * Complex.cos (a : ℂ) * Complex.sin (a : ℂ) * Complex.cos (b : ℂ)
        * Complex.sin (b : ℂ)) * hI2

/-- Gives the real and imaginary parts of the true-row, false-column entry of `commRot` as
trigonometric products. -/
theorem commRot_10 (a b : ℝ) :
    commRot a b (fun _ => true) (fun _ => false)
      = ((2 * Real.sin a * Real.sin b * Real.cos a * Real.cos b : ℝ) : ℂ)
        + ((2 * Real.sin a * Real.cos a * Real.sin b * Real.sin b : ℝ) : ℂ) * Complex.I := by
  have hI2 : Complex.I * Complex.I = -(1 : ℂ) := Complex.I_mul_I
  have hca2 := cos_sin_sq_complex a
  have hcb2 := cos_sin_sq_complex b
  rw [commRot_eq,
    mul_apply2 (rotZ (-b) * rotX (-a)) (rotZ b * rotX a) (fun _ => true) (fun _ => false),
    rotZ_mul_rotX_tt_ff (-b) (-a), rotZ_mul_rotX_ff_ff b a,
    rotZ_mul_rotX_tt_tt (-b) (-a), rotZ_mul_rotX_tt_ff b a]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_neg, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  linear_combination
    (-2 * Complex.I * Complex.cos (a : ℂ) * Complex.sin (a : ℂ) * (Complex.sin (b : ℂ)) ^ 2
      - 2 * Complex.cos (a : ℂ) * Complex.sin (a : ℂ) * Complex.cos (b : ℂ)
        * Complex.sin (b : ℂ)) * hI2

/-- The trace of `commRot` is twice one minus twice the product of the squared sines of its
angles. -/
theorem commRot_trace (a b : ℝ) :
    commRot a b (fun _ => false) (fun _ => false) + commRot a b (fun _ => true) (fun _ => true)
      = ((2 * (1 - 2 * Real.sin a * Real.sin a * Real.sin b * Real.sin b : ℝ)) : ℂ) := by
  rw [commRot_00, commRot_11]
  push_cast
  ring

/-- Multiplying `commRot` by its conjugate transpose gives the identity. -/
theorem commRot_mul_conjTranspose (a b : ℝ) :
    commRot a b * (commRot a b)ᴴ = 1 := by
  have hu : commRot a b ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
    rw [commRot]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _
      (rotZ_unitary (-b)) (rotX_unitary (-a))) (rotZ_unitary b)) (rotX_unitary a)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hu
  exact hu

/-- The product of the commutator's deviation from identity and its conjugate transpose is four
times the product of squared sines times the identity. -/
theorem commRot_sub_one_mul_conjTranspose (a b : ℝ) :
    (commRot a b - 1) * (commRot a b - 1)ᴴ
      = ((4 * Real.sin a * Real.sin a * Real.sin b * Real.sin b : ℝ) : ℂ)
          • (1 : Matrix (Reg 1) (Reg 1) ℂ) := by
  have h1 : commRot a b * (commRot a b)ᴴ = 1 := commRot_mul_conjTranspose a b
  have h2 : (commRot a b - 1) * ((commRot a b)ᴴ - 1)
      = 1 - commRot a b - (commRot a b)ᴴ + 1 := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, h1]
    abel
  rw [show (commRot a b - 1)ᴴ = (commRot a b)ᴴ - 1 from by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one], h2]
  ext y x
  rcases reg1_cases y with rfl | rfl <;> rcases reg1_cases x with rfl | rfl <;>
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, ite_eq_left rfl,
      ite_eq_right basis_ne, ite_eq_right basis_ne',
      ite_eq_right (show ¬((false : Bool) = true) from by decide), ite_true,
      Matrix.sub_apply, Matrix.add_apply, commRot_00, commRot_11, commRot_01, commRot_10,
      Matrix.conjTranspose_apply, Complex.star_def, map_sub, map_add, map_mul,
      Complex.conj_ofReal, Complex.conj_I] <;>
    push_cast <;>
    ring

/-- The norm distance of `commRot` from identity is twice the absolute product of the sines of
its angles. -/
theorem commRot_dist (a b : ℝ) :
    ‖commRot a b - 1‖ = 2 * |Real.sin a * Real.sin b| := by
  have hnnnn : 0 ≤ 4 * Real.sin a * Real.sin a * Real.sin b * Real.sin b := by
    rw [show 4 * Real.sin a * Real.sin a * Real.sin b * Real.sin b
        = 4 * ((Real.sin a * Real.sin a) * (Real.sin b * Real.sin b)) from by ring]
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  have hcert := commRot_sub_one_mul_conjTranspose a b
  have hsq : ‖commRot a b - 1‖ ^ 2 = 4 * Real.sin a * Real.sin a * Real.sin b * Real.sin b := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self ((commRot a b - 1)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose] at h
    rw [sq, ← h, hcert, norm_smul, Complex.norm_of_nonneg hnnnn, l2_norm_one_eq,
      mul_one]
  have habs : (2 * |Real.sin a * Real.sin b|) ^ 2
      = 4 * Real.sin a * Real.sin a * Real.sin b * Real.sin b := by
    rw [show (2 * |Real.sin a * Real.sin b|) ^ 2
        = (|Real.sin a * Real.sin b|) * (|Real.sin a * Real.sin b|) * 4 from by ring,
      ← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
    ring
  rcases mul_eq_zero.mp (show (‖commRot a b - 1‖ - 2 * |Real.sin a * Real.sin b|)
        * (‖commRot a b - 1‖ + 2 * |Real.sin a * Real.sin b|) = 0 by
      linear_combination hsq - habs) with h | h
  · linarith
  · have h1 := norm_nonneg (commRot a b - 1)
    have h2 := abs_nonneg (Real.sin a * Real.sin b)
    linarith

/-- The norm distance of `commRot` from identity is at most twice the product of the absolute
angles. -/
theorem commRot_dist_le (a b : ℝ) :
    ‖commRot a b - 1‖ ≤ 2 * |a| * |b| := by
  rw [commRot_dist, abs_mul (Real.sin a) (Real.sin b)]
  have key : |Real.sin a| * |Real.sin b| ≤ |a| * |b| :=
    mul_le_mul Real.abs_sin_le_abs Real.abs_sin_le_abs (abs_nonneg _) (abs_nonneg _)
  calc 2 * (|Real.sin a| * |Real.sin b|) ≤ 2 * (|a| * |b|) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 2 * |a| * |b| := by ring

/-- The absolute value of `axisSign` is one. -/
theorem abs_axisSign (s : Bool) : |axisSign s| = 1 := by
  cases s <;> simp [axisSign_true, axisSign_false, abs_neg, abs_one]

/-- The norm distance of an axis-word commutator from identity is twice the absolute product of
the sines of its signed rotation angles. -/
theorem commWord_axisWord_dist (sx sz : Bool) (jx jz : ℕ) :
    ‖localProgramMatrix (commWord (axisWord Axis.x sx jx) (axisWord Axis.z sz jz)) - 1‖
      = 2 * |Real.sin (axisSign sx * jx * (Real.pi / 8))
          * Real.sin (axisSign sz * jz * (Real.pi / 8))| := by
  rw [commWord_axisWord_matrix_exact]
  exact commRot_dist _ _

/-- Bounds the axis-word commutator's distance from identity by twice the product of its
unsigned rotation angles. -/
theorem commWord_axisWord_dist_le (sx sz : Bool) (jx jz : ℕ) :
    ‖localProgramMatrix (commWord (axisWord Axis.x sx jx) (axisWord Axis.z sz jz)) - 1‖
      ≤ 2 * (jx * (Real.pi / 8)) * (jz * (Real.pi / 8)) := by
  have hpinn : ∀ j : ℕ, |(j : ℝ)| = j := fun j => abs_of_nonneg (Nat.cast_nonneg j)
  have hpi : |Real.pi / 8| = Real.pi / 8 :=
    abs_of_nonneg (div_nonneg Real.pi_pos.le (by norm_num))
  have hx : |axisSign sx * jx * (Real.pi / 8)| = jx * (Real.pi / 8) := by
    rw [abs_mul, abs_mul, abs_axisSign, one_mul, hpinn, hpi]
  have hz : |axisSign sz * jz * (Real.pi / 8)| = jz * (Real.pi / 8) := by
    rw [abs_mul, abs_mul, abs_axisSign, one_mul, hpinn, hpi]
  rw [commWord_axisWord_dist, abs_mul]
  have h1 : |Real.sin (axisSign sx * jx * (Real.pi / 8))| ≤ jx * (Real.pi / 8) :=
    le_trans Real.abs_sin_le_abs (le_of_eq hx)
  have h2 : |Real.sin (axisSign sz * jz * (Real.pi / 8))| ≤ jz * (Real.pi / 8) :=
    le_trans Real.abs_sin_le_abs (le_of_eq hz)
  have hx0 : 0 ≤ jx * (Real.pi / 8) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg Real.pi_pos.le (by norm_num))
  have key : |Real.sin (axisSign sx * jx * (Real.pi / 8))|
        * |Real.sin (axisSign sz * jz * (Real.pi / 8))|
      ≤ (jx * (Real.pi / 8)) * (jz * (Real.pi / 8)) :=
    mul_le_mul h1 h2 (abs_nonneg _) hx0
  calc 2 * (|Real.sin (axisSign sx * jx * (Real.pi / 8))|
          * |Real.sin (axisSign sz * jz * (Real.pi / 8))|)
      ≤ 2 * ((jx * (Real.pi / 8)) * (jz * (Real.pi / 8))) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 2 * (jx * (Real.pi / 8)) * (jz * (Real.pi / 8)) := by ring

end Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis
