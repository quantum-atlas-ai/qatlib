/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.FixedGateSynthesisDefs
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Partial fixed-gate synthesis and compilation bounds

This module constructs `partialCompiler`, which emits fixed primitives exactly and omits
controlled phases outside the primitive range. `partialCompiler_accepts_primitive` and
`partialCompiler_accepts_smallAngle` certify its two supported regimes, with clean ancillas and
a uniform resource ledger. Circuit and operator-norm conventions are standard
[NielsenChuang2010]; approximation over a fixed alphabet is the broader synthesis setting
[DawsonNielsen2006].

`telescoping_program_error` and `telescoping_mixed_error` bound accumulated substitution error.
The mixed-word lemmas preserve paid oracle calls, while `emit_answerPlan` and
`partialCompiler_machine_budget` connect answer serialization to a uniform Turing-machine
emitter.

## Main statements

* `emptyWord_approx_cp` bounds the phase-adjusted error of omitting a sufficiently small
  controlled phase.
* `partialCompiler_accepts_primitive`, `partialCompiler_accepts_smallAngle`, and
  `partialCompiler_uniform` certify the partial compiler.
* `telescoping_mixed_error`, `compileWord_formCount`, and `compileWord_paidLegal` control error
  and paid calls under substitution.
* `partialCompiler_machine_budget` gives polynomial time and space budgets for emitting
  partial-compiler answers.

## References

- [Nielsen and Chuang, 2010][NielsenChuang2010]
- [Dawson and Nielsen, 2006][DawsonNielsen2006]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.LoopCore
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatEmit

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.StateEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ValidatorSemantics

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline

open Matrix
open scoped Matrix.Norms.L2Operator
open scoped Classical

/-- The clean embedding at unchanged width is the identity matrix. -/
theorem cleanEmbed_self (w : ℕ) : cleanEmbed w w = 1 := by
  ext p t
  simp only [cleanEmbed, Matrix.one_apply]
  have hkey : (fun i : Fin w => if h : i.val < w then t ⟨i, h⟩ else false) = t := by
    funext i
    rw [dif_pos i.isLt]
  rw [hkey]

/-- Any two bit registers of width zero are equal. -/
theorem eq_zero_reg_of_index_zero {m : ℕ} (hm : m = 0) (f g : Reg m) : f = g := by
  subst hm
  funext i
  exact Fin.elim0 i

/-- If the output width equals the data width, every matrix satisfies ancilla restoration at any
nonnegative tolerance. -/
theorem ancillaRestored_trivial {w width : ℕ} (h : width = w)
    (M : Matrix (Reg width) (Reg w) ℂ) (tol : ℝ) (htol : 0 ≤ tol) :
    ancillaRestored w M tol := by
  subst width
  intro ψ _hψ
  have hz : ∀ z : Reg w, auxBits w z = ZeroStr (w - w) := by
    intro z
    exact eq_zero_reg_of_index_zero (Nat.sub_self w) _ _
  have hfun : (fun z : Reg w =>
      if auxBits w z = ZeroStr (w - w) then (0:ℂ) else (M *ᵥ ψ) z) = 0 := by
    funext z
    rw [hz z, if_pos rfl]
    simp
  have hzero : toEuclidean_fromVec (0 : QState (Reg w)) = 0 := rfl
  rw [hfun, hzero, norm_zero]
  exact htol

/-- Every matrix approximates itself up to phase at any nonnegative tolerance, using phase zero. -/
theorem approxUpToPhase_refl {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (tol : ℝ) (htol : 0 ≤ tol) : approxUpToPhase A A tol := by
  refine ⟨0, ?_⟩
  have h1 : Complex.exp ((0:ℝ) * Complex.I) = 1 := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [h1, one_smul, sub_self, norm_zero]
  exact htol

/-- The matrix of a singleton gate program is the matrix of its gate. -/
theorem localProgramMatrix_singleton {w : ℕ} (g : LocalQFTGate w) :
    localProgramMatrix [g] = localGateMatrix g := by
  simp [localProgramMatrix]

/-- The dyadic tolerance `tolerance k` is strictly positive for every precision parameter. -/
theorem tolerance_pos (k : ℕ) : 0 < tolerance k :=
  pow_pos (inv_pos.mpr (by norm_num : (0:ℝ) < 2)) k

/-- The dyadic tolerance `tolerance k` is nonnegative. -/
theorem tolerance_nonneg (k : ℕ) : 0 ≤ tolerance k := (tolerance_pos k).le

/-- The operator-norm error between a matrix and itself is zero. -/
theorem opError_self {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    opError A A = 0 := by
  simp [opError]

/-- The identity matrix on an `n`-qubit register has Euclidean operator norm one. -/
theorem l2_opNorm_one (n : ℕ) : ‖(1 : Matrix (Reg n) (Reg n) ℂ)‖ = 1 := by
  have hdiag : (1 : Matrix (Reg n) (Reg n) ℂ) = diagonal fun _ => (1:ℂ) := by
    simp
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  have hle : ‖(fun _ : Reg n => (1:ℂ))‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg (by norm_num)]
    intro i
    simp
  have hge : (1:ℝ) ≤ ‖(fun _ : Reg n => (1:ℂ))‖ := by
    have h := norm_le_pi_norm (fun _ : Reg n => (1:ℂ)) (default : Reg n)
    have h1 : (1:ℝ) = ‖((fun _ : Reg n => (1:ℂ)) (default : Reg n))‖ := by simp
    rw [h1]
    exact h
  exact le_antisymm hle hge

/-- A unitary matrix on an `n`-qubit register has Euclidean operator norm one. -/
theorem l2_opNorm_unitary {n : ℕ} {U : Matrix (Reg n) (Reg n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) : ‖U‖ = 1 := by
  have hstar : (Uᴴ : Matrix (Reg n) (Reg n) ℂ) * U = 1 := by
    have h1 : star U * U = 1 := Unitary.star_mul_self_of_mem hU
    rw [Matrix.star_eq_conjTranspose] at h1
    exact h1
  have hmul : ‖U‖ * ‖U‖ = 1 := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, hstar, l2_opNorm_one]
  have hnn : 0 ≤ ‖U‖ := norm_nonneg U
  nlinarith only [hmul, hnn]

/-- The matrix of every local gate program is unitary. -/
theorem localProgramMatrix_mem_unitary {n : ℕ} (gs : List (LocalQFTGate n)) :
    localProgramMatrix gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction gs with
  | nil => exact (Matrix.unitaryGroup (Reg n) ℂ).one_mem
  | cons g gs ih =>
    rw [localProgramMatrix_cons]
    exact Submonoid.mul_mem (Matrix.unitaryGroup (Reg n) ℂ) ih
      (localGateMatrix_unitary g)

/-- Taking a local gate's adjoint preserves its Boolean fixed-primitive test. -/
theorem isFixedPrim_adjoint {w : ℕ} (g : LocalQFTGate w) :
    isFixedPrim (localGateAdjoint g) = isFixedPrim g := by
  cases g with
  | h a => rfl
  | swap a c => rfl
  | cp a c e neg => rfl

/-- A local gate's adjoint is a fixed primitive exactly when the original gate is. -/
theorem isFixedPrim_adjoint_iff {w : ℕ} (g : LocalQFTGate w) :
    IsFixedPrim (localGateAdjoint g) ↔ IsFixedPrim g := by
  rw [← isFixedPrim_eq_true_iff, ← isFixedPrim_eq_true_iff, isFixedPrim_adjoint]

/-- A singleton adjoint gate program realizes the conjugate transpose of the original gate
matrix with zero operator-norm error. -/
theorem adjoint_letter_exact {w : ℕ} (g : LocalQFTGate w) :
    localProgramMatrix [localGateAdjoint g] = (localGateMatrix g)ᴴ ∧
      opError (localProgramMatrix [localGateAdjoint g]) ((localGateMatrix g)ᴴ) = 0 := by
  constructor
  · rw [localProgramMatrix_singleton, localGateMatrix_localGateAdjoint]
  · rw [localProgramMatrix_singleton, localGateMatrix_localGateAdjoint]
    exact opError_self _

/-- A fixed primitive is accepted at every precision by its singleton program at the original
width. -/
theorem exactAccepts_of_isFixedPrim {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrim g) : Accepts w g k ⟨w, [g]⟩ := by
  show (∃ a : ℕ, w = w + a) ∧
    (∀ h ∈ ([g] : List (LocalQFTGate w)), IsFixedPrim h) ∧
    answerOracleCalls ⟨w, [g]⟩ = 0 ∧
    approxUpToPhase (localProgramMatrix [g] * cleanEmbed w w)
      (cleanEmbed w w * localGateMatrix g) (tolerance k) ∧
    ancillaRestored w (localProgramMatrix [g] * cleanEmbed w w) (tolerance k)
  refine ⟨⟨0, rfl⟩, ?_, rfl, ?_, ?_⟩
  · intro h hh
    rw [List.mem_singleton] at hh
    rw [hh]
    exact hg
  · rw [cleanEmbed_self, localProgramMatrix_singleton, Matrix.mul_one, Matrix.one_mul]
    exact approxUpToPhase_refl _ _ (tolerance_nonneg k)
  · exact ancillaRestored_trivial rfl _ _ (tolerance_nonneg k)

/-- The adjoint of a fixed primitive is accepted at every precision by its singleton program at
the original width. -/
theorem exactAccepts_adjoint {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrim g) : Accepts w (localGateAdjoint g) k ⟨w, [localGateAdjoint g]⟩ :=
  exactAccepts_of_isFixedPrim (localGateAdjoint g) k ((isFixedPrim_adjoint_iff g).mpr hg)

/-- The absolute value of a signed dyadic phase angle is `2 * Real.pi / 2 ^ e`. -/
theorem dyadicPhaseAngle_abs (e : ℕ) (neg : Bool) :
    |dyadicPhaseAngle e neg| = 2 * Real.pi / (2 ^ e : ℝ) := by
  cases neg with
  | false =>
    show |2 * Real.pi / (2 ^ e : ℝ)| = _
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (by positivity))]
  | true =>
    show |-(2 * Real.pi / (2 ^ e : ℝ))| = _
    rw [abs_neg, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (by positivity))]

/-- Half the absolute dyadic phase angle is `Real.pi / 2 ^ e`, independently of its sign. -/
theorem abs_dyadicPhaseAngle_div_two (e : ℕ) (neg : Bool) :
    |dyadicPhaseAngle e neg| / 2 = Real.pi / (2 ^ e : ℝ) := by
  rw [dyadicPhaseAngle_abs, mul_div_assoc,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- Taking absolute values commutes with division of a real number by two. -/
theorem abs_div_two (x : ℝ) : |x / 2| = |x| / 2 := by
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- If `k + 2 ≤ e`, half the absolute dyadic phase angle is at most `tolerance k`. -/
theorem smallAngle_tol_le (e k : ℕ) (neg : Bool) (he : k + 2 ≤ e) :
    |dyadicPhaseAngle e neg| / 2 ≤ tolerance k := by
  rw [abs_dyadicPhaseAngle_div_two, tolerance]
  have h2e : (2:ℝ) ^ (k + 2) ≤ (2:ℝ) ^ e := pow_le_pow_right₀ (by norm_num) he
  have hpow : (2:ℝ) ^ (k + 2) = 4 * (2:ℝ) ^ k := by
    rw [pow_add]
    ring
  have hpi : Real.pi / (2 ^ e : ℝ) ≤ (4:ℝ) / (2:ℝ) ^ e :=
    div_le_div_of_nonneg_right Real.pi_le_four (by positivity)
  have hdiv : (4:ℝ) / (2:ℝ) ^ e ≤ (4:ℝ) / (2:ℝ) ^ (k + 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) h2e
  have hfinal : (4:ℝ) / (2:ℝ) ^ (k + 2) ≤ ((2:ℝ)⁻¹) ^ k := by
    rw [hpow, inv_eq_one_div, _root_.div_pow, one_pow]
    have h4 : (4:ℝ) / (4 * (2:ℝ) ^ k) = 1 / (2:ℝ) ^ k := by field_simp
    rw [h4]
  exact le_trans (le_trans hpi hdiv) hfinal

/-- The distance from one to the complex phase `exp (t * I)` is bounded by `|t|`. -/
theorem one_sub_exp_mul_I_norm (t : ℝ) :
    ‖(1:ℂ) - Complex.exp ((t:ℂ) * Complex.I)‖ ≤ |t| := by
  have h := norm_exp_mul_I_sub_le 0 t
  rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero, zero_sub, abs_neg] at h
  exact h

/-- Multiplying the phase of angle `-θ / 2` by the phase of angle `θ` gives the phase of angle
`θ / 2`. -/
theorem exp_half_mul_exp (θ : ℝ) :
    Complex.exp (((-θ / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp ((θ:ℂ) * Complex.I)
      = Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The difference between the identity and a phase-scaled controlled-phase matrix is diagonal,
with entries determined by the two selected bits. -/
theorem one_sub_phase_smul_cp {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (φ : ℝ) :
    (1 : Matrix (Reg w) (Reg w) ℂ) - (Complex.exp (φ * Complex.I))
        • localGateMatrix (.cp a c e neg)
      = Matrix.diagonal (fun x : Reg w =>
        1 - Complex.exp (φ * Complex.I)
          * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.diagonal_apply_eq, localGateMatrix_cp]
  · simp [localGateMatrix_cp, hxy]

/-- When `k + 2 ≤ e`, the empty program approximates the controlled dyadic phase up to a global
phase within `tolerance k` at unchanged width. -/
theorem emptyWord_approx_cp {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : k + 2 ≤ e) :
    approxUpToPhase (localProgramMatrix ([] : List (LocalQFTGate w)) * cleanEmbed w w)
      (cleanEmbed w w * localGateMatrix (.cp a c e neg)) (tolerance k) := by
  have hpad : cleanEmbed w w = 1 := cleanEmbed_self w
  rw [hpad, localProgramMatrix_nil]
  simp only [Matrix.one_mul, Matrix.mul_one]
  refine ⟨-(dyadicPhaseAngle e neg) / 2, ?_⟩
  set φ : ℝ := -(dyadicPhaseAngle e neg) / 2
  have hrew : (1 : Matrix (Reg w) (Reg w) ℂ) - (Complex.exp (φ * Complex.I))
      • localGateMatrix (.cp a c e neg)
      = Matrix.diagonal (fun x : Reg w =>
        1 - Complex.exp (φ * Complex.I)
          * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)) :=
    one_sub_phase_smul_cp a c e neg φ
  have hle : ‖(Matrix.diagonal (fun x : Reg w =>
      1 - Complex.exp (φ * Complex.I)
        * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)) :
      Matrix (Reg w) (Reg w) ℂ)‖ ≤ tolerance k := by
    have hnorm : ‖(Matrix.diagonal (fun x : Reg w =>
        1 - Complex.exp (φ * Complex.I)
          * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)) :
        Matrix (Reg w) (Reg w) ℂ)‖
        = ‖(fun x : Reg w =>
        1 - Complex.exp (φ * Complex.I)
          * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1))‖ :=
      Matrix.l2_opNorm_diagonal _
    rw [hnorm, pi_norm_le_iff_of_nonneg (tolerance_nonneg k)]
    intro x
    by_cases hx : x a && x c
    · rw [if_pos hx, exp_half_mul_exp]
      refine le_trans (one_sub_exp_mul_I_norm _) ?_
      have hθ : |dyadicPhaseAngle e neg / 2| = |dyadicPhaseAngle e neg| / 2 :=
        abs_div_two _
      rw [hθ]
      exact smallAngle_tol_le e k neg he
    · rw [if_neg hx, mul_one]
      refine le_trans (one_sub_exp_mul_I_norm _) ?_
      have hθ : |(-(dyadicPhaseAngle e neg) / 2 : ℝ)| = |dyadicPhaseAngle e neg| / 2 := by
        rw [abs_div_two, abs_neg]
      rw [hθ]
      exact smallAngle_tol_le e k neg he
  rw [hrew]
  exact hle

/-- Every gate has a rational angle input satisfying `angleInputOK` at any requested bit
precision. -/
theorem angleInputOK_exists {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) :
    ∃ q : ℚ, angleInputOK g bits q := by
  cases g with
  | h a => exact ⟨0, trivial⟩
  | swap a c => exact ⟨0, trivial⟩
  | cp a c e neg =>
    refine ⟨(Int.floor ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2)) / (2 ^ bits : ℚ), ?_⟩
    have h2b : (0 : ℝ) < (2:ℝ) ^ bits := by positivity
    have hround : |(((Int.floor ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2) : ℤ) : ℝ)
        / (2 ^ bits : ℝ)) - dyadicPhaseAngle e neg| ≤ ((2 : ℝ) ⁻¹) ^ bits := by
      have hkey : ((Int.floor ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2) : ℤ) : ℝ)
          / (2 ^ bits : ℝ) - dyadicPhaseAngle e neg
          = (((Int.floor ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2) : ℤ) : ℝ)
            - dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) / (2 ^ bits : ℝ) := by
        field_simp
      rw [hkey, abs_div, abs_of_pos h2b]
      have hnumle : |((Int.floor ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2) : ℤ) : ℝ)
          - dyadicPhaseAngle e neg * (2 ^ bits : ℝ)| ≤ 1 / 2 := by
        rw [abs_sub_le_iff]
        constructor
        · linarith [Int.floor_le ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2)]
        · linarith [Int.lt_floor_add_one ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2)]
      refine le_trans (div_le_div_of_nonneg_right hnumle (le_of_lt h2b)) ?_
      have hpow : (1 / 2 / (2:ℝ) ^ bits : ℝ) = ((2 : ℝ) ⁻¹) ^ (bits + 1) := by
        rw [inv_eq_one_div, pow_succ, div_pow, one_pow]
        field_simp
      rw [hpow]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    refine ⟨?_, ⟨Int.floor ((dyadicPhaseAngle e neg * (2 ^ bits : ℝ)) + 1 / 2), rfl⟩⟩
    rw [tolerance]
    push_cast
    exact hround

/-- The partial compiler's ancilla allocation is zero for every request. -/
def partialAnc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ := fun _ _ _ => 0

/-- Emit the input Hadamard or swap, and emit a controlled phase exactly when its exponent is at
most three. Larger-exponent controlled phases produce the empty word. -/
def partialEmit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) →
    List (LocalQFTGate (w + partialAnc w g k)) :=
  fun _ g _ =>
    match g with
    | .h a => [.h a]
    | .cp a c e neg => if e ≤ 3 then [.cp a c e neg] else []
    | .swap a c => [.swap a c]

/-- The compiler combining zero ancilla allocation with singleton emission of fixed primitives
and omission of other controlled phases. -/
def partialCompiler : Compiler :=
  ⟨partialAnc, partialEmit⟩

/-- The partial compiler allocates no ancillas for any request. -/
theorem partialCompiler_anc_eq (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    partialCompiler.anc w g k = 0 := rfl

/-- On a fixed primitive, the partial compiler emits the singleton word containing that gate. -/
theorem partialCompiler_emit_primitive {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrim g) : partialCompiler.emit w g k = [g] := by
  cases g with
  | h a => rfl
  | swap a c => rfl
  | cp a c e neg =>
    have he : e ≤ 3 := hg
    show (if e ≤ 3 then [LocalQFTGate.cp a c e neg] else []) = [LocalQFTGate.cp a c e neg]
    rw [if_pos he]

/-- A controlled phase with exponent greater than three produces the empty word under the
partial compiler. -/
theorem partialCompiler_emit_empty {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 3 < e) : partialCompiler.emit w (.cp a c e neg) k = [] := by
  show (if e ≤ 3 then [LocalQFTGate.cp a c e neg] else []) = []
  rw [if_neg (Nat.not_le.mpr he)]

/-- Every word emitted by the partial compiler has length at most one. -/
theorem partialCompiler_emit_length {w : ℕ} (g : LocalQFTGate w) (k : ℕ) :
    (partialCompiler.emit w g k).length ≤ 1 := by
  cases g with
  | h a => rfl
  | swap a c => rfl
  | cp a c e neg =>
    by_cases h : e ≤ 3
    · rw [partialCompiler_emit_primitive (.cp a c e neg) k h]
      show (1:ℕ) ≤ 1
      exact le_rfl
    · rw [partialCompiler_emit_empty a c e neg k (Nat.lt_of_not_ge h)]
      show (0:ℕ) ≤ 1
      exact Nat.zero_le 1

/-- The partial compiler answers a Hadamard request with the same-width singleton Hadamard
program. -/
theorem partialCompiler_segment_h {w : ℕ} (a : Fin w) (k : ℕ) :
    partialCompiler.Segment w (.h a) k = ⟨w, [LocalQFTGate.h a]⟩ := rfl

/-- The partial compiler answers a swap request with the same-width singleton swap program. -/
theorem partialCompiler_segment_swap {w : ℕ} (a c : Fin w) (k : ℕ) :
    partialCompiler.Segment w (.swap a c) k = ⟨w, [Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalQFTGate.swap a c]⟩ := rfl

/-- For exponent at most three, the partial compiler answers a controlled-phase request with
that same-width singleton gate. -/
theorem partialCompiler_segment_cp {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : e ≤ 3) :
    partialCompiler.Segment w (.cp a c e neg) k = ⟨w, [LocalQFTGate.cp a c e neg]⟩ := by
  change (⟨w + 0, if e ≤ 3 then [LocalQFTGate.cp a c e neg] else []⟩ : SynthAnswer)
    = ⟨w, [LocalQFTGate.cp a c e neg]⟩
  rw [if_pos he]
  exact rfl

/-- For exponent greater than three, the partial compiler's controlled-phase answer is the empty
program at the input width. -/
theorem partialCompiler_segment_cp_empty {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 3 < e) :
    partialCompiler.Segment w (.cp a c e neg) k = ⟨w, []⟩ := by
  change (⟨w + 0, if e ≤ 3 then [LocalQFTGate.cp a c e neg] else []⟩ : SynthAnswer) = ⟨w, []⟩
  rw [if_neg (Nat.not_le.mpr he)]
  exact rfl

/-- The partial compiler satisfies the acceptance contract for every fixed primitive at every
precision. -/
theorem partialCompiler_accepts_primitive (w : ℕ) (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrim g) : AcceptsAt partialCompiler w g k := by
  have hemit : partialCompiler.emit w g k = [g] := partialCompiler_emit_primitive g k hg
  show Accepts w g k (partialCompiler.Segment w g k)
  rw [Compiler.Segment, hemit]
  exact exactAccepts_of_isFixedPrim g k hg

/-- For `1 ≤ k` and `k + 2 ≤ e`, the partial compiler satisfies the acceptance contract for a
controlled phase of exponent `e`. -/
theorem partialCompiler_accepts_smallAngle {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool)
    (k : ℕ) (_hk : 1 ≤ k) (he : k + 2 ≤ e) :
    AcceptsAt partialCompiler w (.cp a c e neg) k := by
  by_cases h3 : e ≤ 3
  · exact partialCompiler_accepts_primitive w (.cp a c e neg) k h3
  · have hemit : partialCompiler.emit w (.cp a c e neg) k = [] :=
      partialCompiler_emit_empty a c e neg k (Nat.lt_of_not_ge h3)
    show Accepts w (.cp a c e neg) k (partialCompiler.Segment w (.cp a c e neg) k)
    rw [Compiler.Segment, hemit]
    show (∃ aN : ℕ, w + partialCompiler.anc w (.cp a c e neg) k = w + aN) ∧
      (∀ h ∈ ([] : List (LocalQFTGate (w + partialCompiler.anc w (.cp a c e neg) k))),
        IsFixedPrim h) ∧
      answerOracleCalls
        ⟨w + partialCompiler.anc w (.cp a c e neg) k, []⟩ = 0 ∧
      approxUpToPhase
        (localProgramMatrix ([] : List (LocalQFTGate (w + partialCompiler.anc w (.cp a c e neg) k)))
          * cleanEmbed w (w + partialCompiler.anc w (.cp a c e neg) k))
        (cleanEmbed w (w + partialCompiler.anc w (.cp a c e neg) k)
          * localGateMatrix (.cp a c e neg)) (tolerance k) ∧
      ancillaRestored w
        (localProgramMatrix ([] : List (LocalQFTGate (w + partialCompiler.anc w (.cp a c e neg) k)))
          * cleanEmbed w (w + partialCompiler.anc w (.cp a c e neg) k)) (tolerance k)
    refine ⟨⟨0, rfl⟩, ?_, rfl, ?_, ?_⟩
    · intro g hg
      exact (List.not_mem_nil hg).elim
    · exact emptyWord_approx_cp a c e neg k he
    · exact ancillaRestored_trivial rfl _ _ (tolerance_nonneg k)

/-- Every gate emitted by the partial compiler is a fixed primitive. -/
theorem partialCompiler_legal (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ∀ g' ∈ partialCompiler.emit w g k, IsFixedPrim g' := by
  cases g with
  | h a =>
    intro g' hg'
    have hg'' : g' = LocalQFTGate.h a := List.mem_singleton.mp hg'
    rw [hg'']
    trivial
  | swap a c =>
    intro g' hg'
    have hg'' : g' = Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalQFTGate.swap a c :=
        List.mem_singleton.mp hg'
    rw [hg'']
    trivial
  | cp a c e neg =>
    by_cases h : e ≤ 3
    · rw [partialCompiler_emit_primitive (.cp a c e neg) k h]
      intro g' hg'
      have hg'' : g' = LocalQFTGate.cp a c e neg := List.mem_singleton.mp hg'
      rw [hg'']
      exact h
    · rw [partialCompiler_emit_empty a c e neg k (Nat.lt_of_not_ge h)]
      intro g' hg'
      exact (List.not_mem_nil hg').elim

/-- Every partial-compiler answer has zero synthesis oracle calls. -/
theorem partialCompiler_zero_oracle (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    answerOracleCalls (partialCompiler.Segment w g k) = 0 := rfl

/-- The width of a partial-compiler answer is the input width plus a natural ancilla count. -/
theorem partialCompiler_width (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ∃ a : ℕ, (partialCompiler.Segment w g k).width = w + a :=
  ⟨partialCompiler.anc w g k, rfl⟩

/-- Every partial-compiler answer satisfies clean-ancilla restoration at the requested dyadic
tolerance. -/
theorem partialCompiler_clean (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ancillaRestored w
      (localProgramMatrix (partialCompiler.Segment w g k).word
        * cleanEmbed w (partialCompiler.Segment w g k).width) (tolerance k) :=
  ancillaRestored_trivial (width := (partialCompiler.Segment w g k).width)
    (h := rfl) _ _ (tolerance_nonneg k)

/-- The partial compiler has a uniform polynomial ledger for emitted length and ancilla count. -/
theorem partialCompiler_uniform : UniformLedger partialCompiler := by
  refine ⟨1, 1, fun w g k => ⟨?_, ?_⟩⟩
  · have hlen := partialCompiler_emit_length (w := w) g k
    have hs : (1:ℕ) ≤ requestSize w g k := by
      dsimp [requestSize]; omega
    rw [one_mul, Nat.pow_one]
    exact le_trans hlen hs
  · rw [one_mul, Nat.pow_one, partialCompiler_anc_eq]
    exact Nat.zero_le _

/-- Split the difference of two matrix products into the error of the left factor and the error
of the right factor. -/
theorem matrix_two_letter_split {n : Type*} [Fintype n]
    (A₀ A₁ B₀ B₁ : Matrix n n ℂ) :
    A₁ * A₀ - B₁ * B₀ = (A₁ - B₁) * A₀ + B₁ * (A₀ - B₀) := by
  rw [sub_mul, mul_sub]
  abel

/-- If `A₀` and `B₁` are unitary, the operator-norm error between `A₁ * A₀` and `B₁ * B₀` is at
most the sum of the two factor errors. -/
theorem opError_comp_le {n : ℕ} (A₀ A₁ B₀ B₁ : Matrix (Reg n) (Reg n) ℂ)
    (hA₀ : A₀ ∈ Matrix.unitaryGroup (Reg n) ℂ) (hB₁ : B₁ ∈ Matrix.unitaryGroup (Reg n) ℂ) :
    opError (A₁ * A₀) (B₁ * B₀) ≤ opError A₁ B₁ + opError A₀ B₀ := by
  have hkey : A₁ * A₀ - B₁ * B₀ = (A₁ - B₁) * A₀ + B₁ * (A₀ - B₀) :=
    matrix_two_letter_split A₀ A₁ B₀ B₁
  have hA₀n : ‖A₀‖ = 1 := l2_opNorm_unitary hA₀
  have hB₁n : ‖B₁‖ = 1 := l2_opNorm_unitary hB₁
  show ‖A₁ * A₀ - B₁ * B₀‖ ≤ ‖A₁ - B₁‖ + ‖A₀ - B₀‖
  calc ‖A₁ * A₀ - B₁ * B₀‖
      = ‖(A₁ - B₁) * A₀ + B₁ * (A₀ - B₀)‖ := by rw [hkey]
    _ ≤ ‖(A₁ - B₁) * A₀‖ + ‖B₁ * (A₀ - B₀)‖ := norm_add_le _ _
    _ ≤ ‖A₁ - B₁‖ * ‖A₀‖ + ‖B₁‖ * ‖A₀ - B₀‖ :=
        add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = ‖A₁ - B₁‖ + ‖A₀ - B₀‖ := by rw [hA₀n, hB₁n, mul_one, one_mul]

/-- Replacing each local gate by a same-width program incurs operator-norm error at most the sum
of the individual replacement errors. -/
theorem telescoping_program_error {n : ℕ} (f : LocalQFTGate n → List (LocalQFTGate n))
    (gs : List (LocalQFTGate n)) :
    opError (localProgramMatrix (gs.flatMap f)) (localProgramMatrix gs)
      ≤ ((gs.map (fun g => opError (localProgramMatrix (f g)) (localGateMatrix g))).sum) := by
  induction gs with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, localProgramMatrix_nil]
    exact (opError_self (1 : Matrix (Reg n) (Reg n) ℂ)).le
  | cons g gs ih =>
    rw [List.flatMap_cons, localProgramMatrix_append, localProgramMatrix_cons,
      List.map_cons, List.sum_cons]
    refine le_trans
      (opError_comp_le (localProgramMatrix (f g)) (localProgramMatrix (gs.flatMap f))
        (localGateMatrix g) (localProgramMatrix gs)
        (localProgramMatrix_mem_unitary _) (localProgramMatrix_mem_unitary _)) ?_
    linarith

/-- A nonnegative total error allowance gives a nonnegative uniform per-slot budget. -/
theorem uniformBudget_nonneg {ε : ℝ} (hε : 0 ≤ ε) (count : ℕ) :
    0 ≤ uniformBudget ε count := by
  simpa [uniformBudget] using div_nonneg hε (by positivity : (0:ℝ) ≤ (count:ℝ) + 1)

/-- With count zero, the uniform budget equals the full error allowance. -/
theorem uniformBudget_zero (ε : ℝ) : uniformBudget ε 0 = ε := by
  simp [uniformBudget]

/-- For a nonnegative allowance, assigning `uniformBudget ε m` to each of `m` slots stays within
`ε`. -/
theorem uniformBudget_sum_le {ε : ℝ} (hε : 0 ≤ ε) (m : ℕ) :
    (m : ℝ) * uniformBudget ε m ≤ ε := by
  have hden : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have h2 : (m:ℝ) / ((m:ℝ) + 1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have key : (m:ℝ) * uniformBudget ε m = ε * ((m:ℝ) / ((m:ℝ) + 1)) := by
    rw [uniformBudget, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [key]
  have h3 : ε * ((m:ℝ) / ((m:ℝ) + 1)) ≤ ε * 1 := mul_le_mul_of_nonneg_left h2 hε
  simpa using h3

/-- At most `L + 1` slots, each assigned `uniformBudget ε L`, consume at most the nonnegative
allowance `ε`. -/
theorem uniformBudget_slots_le {ε : ℝ} (hε : 0 ≤ ε) (L m : ℕ) (hm : m ≤ L + 1) :
    (m : ℝ) * uniformBudget ε L ≤ ε := by
  have hden : (0:ℝ) < (L:ℝ) + 1 := by positivity
  have h2 : (m:ℝ) / ((L:ℝ) + 1) ≤ 1 := (div_le_one hden).mpr (by exact_mod_cast hm)
  have key : (m:ℝ) * uniformBudget ε L = ε * ((m:ℝ) / ((L:ℝ) + 1)) := by
    rw [uniformBudget, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [key]
  have h3 : ε * ((m:ℝ) / ((L:ℝ) + 1)) ≤ ε * 1 := mul_le_mul_of_nonneg_left h2 hε
  simpa using h3

/-- The count of a specified call form is additive under concatenation of mixed words. -/
theorem formCount_append {n : ℕ} {S : Type} (φ : CallForm S) (xs ys : List (PaidStep n S)) :
    formCount φ (xs ++ ys) = formCount φ xs + formCount φ ys := by
  induction xs with
  | nil => simp [formCount]
  | cons s rest ih =>
    rw [List.cons_append]
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · show formCount φ (rest ++ ys) = formCount φ rest + formCount φ ys
      exact ih
    · show formCount φ (rest ++ ys) + (if ψ = φ then 1 else 0)
        = formCount φ rest + (if ψ = φ then 1 else 0) + formCount φ ys
      rw [ih]
      by_cases h : ψ = φ
      · rw [if_pos h]
        omega
      · rw [if_neg h]
        omega

/-- The total number of paid calls is additive under concatenation of mixed words. -/
theorem callCount_append {n : ℕ} {S : Type} (xs ys : List (PaidStep n S)) :
    callCount (xs ++ ys) = callCount xs + callCount ys := by
  induction xs with
  | nil => simp [callCount]
  | cons s rest ih =>
    rw [List.cons_append]
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · show callCount (rest ++ ys) = callCount (rest) + callCount ys
      exact ih
    · show callCount (rest ++ ys) + 1 = callCount rest + 1 + callCount ys
      rw [ih]
      omega

/-- A word obtained by marking local gates as known contains no occurrence of any call form. -/
theorem formCount_map_known {m : ℕ} {S : Type} (φ : CallForm S)
    (gs : List (LocalQFTGate m)) :
    formCount φ (gs.map PaidStep.known) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [formCount, ih]

/-- A word obtained by marking local gates as known has no paid calls. -/
theorem callCount_map_known {m : ℕ} {S : Type} (gs : List (LocalQFTGate m)) :
    callCount (gs.map (PaidStep.known (S := S))) = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [callCount, ih]

/-- Compiling known gates preserves the multiplicity of each individual call form. -/
theorem compileWord_formCount {n m : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate m)) (φ : CallForm S) (W : List (PaidStep n S)) :
    formCount φ (compileWord f W) = formCount φ W := by
  induction W with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · show formCount φ ((f g).map PaidStep.known ++ compileWord f rest) = formCount φ rest
      rw [formCount_append, formCount_map_known, zero_add, ih]
    · show formCount φ (compileWord f rest) + (if ψ = φ then 1 else 0)
        = formCount φ rest + (if ψ = φ then 1 else 0)
      rw [ih]

/-- Compiling known gates preserves the total number of paid calls. -/
theorem compileWord_callCount {n m : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate m)) (W : List (PaidStep n S)) :
    callCount (compileWord f W) = callCount W := by
  induction W with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · show callCount ((f g).map PaidStep.known ++ compileWord f rest) = callCount rest
      rw [callCount_append, callCount_map_known, zero_add, ih]
    · show callCount (compileWord f rest) + 1 = callCount rest + 1
      rw [ih]

/-- Compiling known gates preserves legality with respect to the allowed paid call forms. -/
theorem compileWord_paidLegal {n m : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate m)) (W : List (PaidStep n S))
    (paid : List (CallForm S)) (h : paidLegal W paid) :
    paidLegal (compileWord f W) paid := by
  induction W with
  | nil =>
    intro s hs
    exact (List.not_mem_nil hs).elim
  | cons t rest ih =>
    have hrest : paidLegal rest paid := fun s hs => h s (List.mem_cons_of_mem t hs)
    rcases t with ⟨g⟩ | ⟨ψ⟩
    · show paidLegal ((f g).map PaidStep.known ++ compileWord f rest) paid
      intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · obtain ⟨h', _hh', rfl⟩ := List.mem_map.mp hs
        trivial
      · exact ih hrest s hs
    · show paidLegal (PaidStep.call ψ :: compileWord f rest) paid
      intro s hs
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact h _ List.mem_cons_self
      · exact ih hrest s hs

/-- A mixed word containing no known gates is unchanged by same-width compilation. -/
theorem compileWord_id_of_no_known {n : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate n)) (W : List (PaidStep n S))
    (h : knownGates W = []) : compileWord f W = W := by
  induction W with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · simp [knownGates] at h
    · have h' : knownGates rest = [] := by simpa [knownGates] using h
      show (PaidStep.call ψ :: compileWord f rest) = PaidStep.call ψ :: rest
      rw [ih h']

/-- Extracting the known gates from a word formed entirely from known gates recovers the
original list. -/
theorem knownGates_map_known {n : ℕ} {S : Type} (gs : List (LocalQFTGate n)) :
    knownGates (gs.map (PaidStep.known (S := S))) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [knownGates, ih]

set_option linter.unusedSimpArgs false

/-- Extracting known gates commutes with concatenation of mixed words. -/
theorem knownGates_append {n : ℕ} {S : Type} (xs ys : List (PaidStep n S)) :
    knownGates (xs ++ ys) = knownGates xs ++ knownGates ys := by
  induction xs with
  | nil => simp [knownGates]
  | cons s rest ih =>
    rw [List.cons_append]
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · show g :: knownGates (rest ++ ys) = (g :: knownGates rest) ++ knownGates ys
      rw [ih]
      exact List.cons_append.symm
    · show knownGates (rest ++ ys) = knownGates rest ++ knownGates ys
      exact ih

/-- The known gates of a compiled word are the concatenated replacement programs for its
original known gates. -/
theorem knownGates_compileWord {n m : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate m)) (W : List (PaidStep n S)) :
    knownGates (compileWord f W) = (knownGates W).flatMap f := by
  induction W with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨g⟩ | ⟨ψ⟩
    · show knownGates ((f g).map PaidStep.known ++ compileWord f rest)
        = (g :: knownGates rest).flatMap f
      rw [knownGates_append, knownGates_map_known, List.flatMap_cons, ih]
    · show knownGates (compileWord f rest) = (knownGates rest).flatMap f
      exact ih

/-- The matrix of a mixed word consisting only of known gates equals their local program matrix. -/
theorem wordMatrix_map_known {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (gs : List (LocalQFTGate n)) :
    wordMatrix O (gs.map (PaidStep.known (S := S))) = localProgramMatrix gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, wordMatrix, localProgramMatrix_cons, stepMatrix, ih]

/-- The matrix of `xs ++ ys` is the matrix of `ys` multiplied by the matrix of `xs`, matching
execution order. -/
theorem wordMatrix_append {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (xs ys : List (PaidStep n S)) :
    wordMatrix O (xs ++ ys) = wordMatrix O ys * wordMatrix O xs := by
  induction xs with
  | nil => simp [wordMatrix]
  | cons s rest ih =>
    rw [List.cons_append, wordMatrix, wordMatrix, ih]
    exact mul_assoc (wordMatrix O ys) (wordMatrix O rest) (stepMatrix O s)

/-- The empty mixed word has identity matrix. -/
theorem wordMatrix_nil {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ) :
    wordMatrix O ([] : List (PaidStep n S)) = 1 := rfl

/-- The matrix of a nonempty mixed word is the tail matrix multiplied by the first step's
matrix. -/
theorem wordMatrix_cons {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (s : PaidStep n S) (rest : List (PaidStep n S)) :
    wordMatrix O (s :: rest) = wordMatrix O rest * stepMatrix O s := rfl

/-- The matrix of a known step is its local gate matrix. -/
theorem stepMatrix_known {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (g : LocalQFTGate n) : stepMatrix O (PaidStep.known g) = localGateMatrix g := rfl

/-- The matrix of a paid call step is the oracle matrix assigned to its call form. -/
theorem stepMatrix_call {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (φ : CallForm S) : stepMatrix O (PaidStep.call φ) = O φ := rfl

/-- Extracting known gates retains a leading known gate and then extracts the tail's known
gates. -/
theorem knownGates_cons_known {n : ℕ} {S : Type} (g : LocalQFTGate n)
    (rest : List (PaidStep n S)) :
    knownGates (PaidStep.known g :: rest) = g :: knownGates rest := rfl

/-- Extracting known gates discards a leading paid call. -/
theorem knownGates_cons_call {n : ℕ} {S : Type} (φ : CallForm S)
    (rest : List (PaidStep n S)) :
    knownGates (PaidStep.call φ :: rest) = knownGates rest := rfl

/-- Compilation replaces a leading known gate by its replacement word of known steps before
compiling the tail. -/
theorem compileWord_cons_known {n m : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate m)) (g : LocalQFTGate n)
    (rest : List (PaidStep n S)) :
    compileWord f (PaidStep.known g :: rest)
      = (f g).map PaidStep.known ++ compileWord f rest := rfl

/-- Compilation retains a leading paid call with the same form and compiles the tail. -/
theorem compileWord_cons_call {n m : ℕ} {S : Type}
    (f : LocalQFTGate n → List (LocalQFTGate m)) (φ : CallForm S)
    (rest : List (PaidStep n S)) :
    compileWord f (PaidStep.call φ :: rest) = PaidStep.call φ :: compileWord f rest := rfl

/-- A mixed word has a unitary matrix whenever every oracle matrix assigned to a call form is
unitary. -/
theorem wordMatrix_mem_unitary {n : ℕ} {S : Type} (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (hO : ∀ φ, O φ ∈ Matrix.unitaryGroup (Reg n) ℂ) (W : List (PaidStep n S)) :
    wordMatrix O W ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  induction W with
  | nil => exact (Matrix.unitaryGroup (Reg n) ℂ).one_mem
  | cons s rest ih =>
    rw [wordMatrix]
    refine Submonoid.mul_mem (Matrix.unitaryGroup (Reg n) ℂ) ih ?_
    rcases s with ⟨g⟩ | ⟨φ⟩
    · exact localGateMatrix_unitary g
    · exact hO φ

/-- With unitary oracle matrices, same-width compilation of known gates incurs error at most the
sum of their individual replacement errors. -/
theorem telescoping_mixed_error {n : ℕ} {S : Type}
    (O : CallForm S → Matrix (Reg n) (Reg n) ℂ)
    (hO : ∀ φ, O φ ∈ Matrix.unitaryGroup (Reg n) ℂ)
    (f : LocalQFTGate n → List (LocalQFTGate n)) (W : List (PaidStep n S)) :
    opError (wordMatrix O (compileWord f W)) (wordMatrix O W)
      ≤ ((knownGates W).map
        (fun g => opError (localProgramMatrix (f g)) (localGateMatrix g))).sum := by
  induction W with
  | nil =>
    simp only [compileWord, wordMatrix, knownGates, List.map_nil, List.sum_nil]
    exact (opError_self (1 : Matrix (Reg n) (Reg n) ℂ)).le
  | cons s rest ih =>
    rcases s with ⟨g⟩ | ⟨φ⟩
    · rw [compileWord_cons_known, wordMatrix_append, wordMatrix_map_known,
        wordMatrix_cons, stepMatrix_known, knownGates_cons_known, List.map_cons, List.sum_cons]
      refine le_trans
        (opError_comp_le (localProgramMatrix (f g)) (wordMatrix O (compileWord f rest))
          (localGateMatrix g) (wordMatrix O rest)
          (localProgramMatrix_mem_unitary _) (wordMatrix_mem_unitary O hO rest)) ?_
      linarith
    · rw [compileWord_cons_call, wordMatrix_cons, wordMatrix_cons, stepMatrix_call,
        knownGates_cons_call]
      refine le_trans
        (opError_comp_le (O φ) (wordMatrix O (compileWord f rest)) (O φ) (wordMatrix O rest)
          (hO φ) (wordMatrix_mem_unitary O hO rest)) ?_
      have key : opError (O φ) (O φ) = 0 := opError_self _
      rw [key]
      simpa using ih

/-- Executing a field-emission plan concatenates the canonical natural-number encodings of its
fields, independently of parameters and counters. -/
theorem emit_fieldsPlan (fs : List ℕ) (params : List (List Bool)) (k : ℕ)
    (counters : List ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit params k counters (fieldsPlan fs) = fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits := by
  induction fs with
  | nil => rfl
  | cons j fs ih =>
    show Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit params k counters (fieldsPlan fs)
      = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j ++ fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits
    rw [ih]

/-- Executing an answer's emission plan with empty counters produces exactly its canonical
answer bits. -/
theorem emit_answerPlan (ans : SynthAnswer) (params : List (List Bool)) (k : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit params k [] (answerPlan ans) = answerBits ans := by
  show Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width
      ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)
        ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit params k []
            (fieldsPlan ((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields)))
    = answerBits ans
  rw [emit_fieldsPlan]
  rfl

/-- Mapping a synthesis answer's local gates to opcodes yields a legal canonical word at the
answer's width. -/
theorem answerWord_legal (ans : SynthAnswer) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Legal ⟨ans.width, ans.word.map opcodeOf⟩ := by
  intro op hop
  obtain ⟨g, _hg, rfl⟩ := List.mem_map.mp hop
  cases g with
  | h a => simp [opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.legalOpcode]
  | cp a c e neg => simp [opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.legalOpcode]
  | swap a c => simp [opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.legalOpcode]

/-- The work of a field-emission plan is one plus the sum of each field's encoded length and two
units of overhead. -/
theorem work_fieldsPlan (fs : List ℕ) (params : List (List Bool)) (k : ℕ)
    (counters : List ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work params k counters (fieldsPlan fs)
      = (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 2)).sum + 1 := by
  induction fs with
  | nil => rfl
  | cons j fs ih =>
    show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 1 + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work params k counters (fieldsPlan fs) + 1
      = ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 2
        + (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 2)).sum) + 1
    rw [ih]
    omega

/-- Summing encoded field lengths with overhead two equals the concatenated encoding length plus
twice the field count. -/
theorem sum_map_natBits_len_add_two (fs : List ℕ) :
    (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 2)).sum
      = (fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits).length + 2 * fs.length := by
  induction fs with
  | nil => rfl
  | cons j fs ih =>
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.length_cons,
      ih]
    omega

/-- Summing encoded field lengths with overhead thirteen equals the concatenated encoding length
plus thirteen times the field count. -/
theorem sum_map_natBits_len_add13 (fs : List ℕ) :
    (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 13)).sum
      = (fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits).length + 13 * fs.length := by
  induction fs with
  | nil => rfl
  | cons j fs ih =>
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, List.length_cons,
      ih]
    omega

/-- An answer's encoded length is the sum of the encoded width, encoded gate count, and encoded
opcode fields. -/
theorem answerBits_length (ans : SynthAnswer) :
    (answerBits ans).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)).length
        + (((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits).length := by
  have hexp : answerBits ans
      = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width
          ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)
            ++ (((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits)) := rfl
  rw [hexp]
  simp only [List.length_append]
  omega

/-- The work of an answer-emission plan is at most three times the answer's bit length plus
eight. -/
theorem answerPlan_work_le (ans : SynthAnswer) (params : List (List Bool)) (k : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work params k [] (answerPlan ans) ≤ 3 * (answerBits ans).length + 8 := by
  set fs := (ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields
  have hwork : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work params k [] (answerPlan ans)
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)).length
        + (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 2)).sum + 5 := by
    show (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width).length + 1
        + ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)).length + 1
          + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work params k [] (fieldsPlan fs) + 1) + 1
      = _
    rw [work_fieldsPlan]
    omega
  have hout : (answerBits ans).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)).length
        + (fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits).length := by
    have hkey :
        fs = (ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields := rfl
    rw [hkey]
    exact answerBits_length ans
  have hsum : (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 2)).sum
      = (fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits).length + 2 * fs.length :=
    sum_map_natBits_len_add_two fs
  have hge : fs.length ≤ (fs.flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits).length :=
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.flatNatBits_length_ge fs
  rw [hwork, hout, hsum]
  omega

/-- A canonical natural-number encoding has length twice the length of `Nat.bits` plus one. -/
theorem natBits_len (j : ℕ) : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length = 2 * j.bits.length + 1 :=
  Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits_length j

/-- Every canonical natural-number encoding contains at least one bit. -/
theorem natBits_length_pos (j : ℕ) : 1 ≤ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length := by
  rw [natBits_len]
  omega

/-- The encoded partial-compiler Hadamard answer has the encoded width and opcode fields,
together with three bits for the singleton gate count. -/
theorem partialCompiler_answerBits_h (w : ℕ) (a : Fin w) (k : ℕ) :
    (answerBits (partialCompiler.Segment w (.h a) k)).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + 3 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length := by
  rw [partialCompiler_segment_h]
  simp [answerBits, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.wordBits, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
    List.flatMap_nil, List.length_append, List.length_cons, List.length_nil, List.append_nil]
  have h1 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length = 3 := rfl
  rw [h1]
  omega

/-- The encoded partial-compiler swap answer has the encoded width, swap tag, and two wire
indices, together with three bits for the singleton gate count. -/
theorem partialCompiler_answerBits_swap (w : ℕ) (a c : Fin w) (k : ℕ) :
    (answerBits (partialCompiler.Segment w (.swap a c) k)).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + 3 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c.val).length := by
  rw [partialCompiler_segment_swap]
  simp [answerBits, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.wordBits, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
    List.flatMap_nil, List.length_append, List.length_cons, List.length_nil, List.append_nil]
  have h1 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length = 3 := rfl
  rw [h1]
  omega

/-- For exponent at most three, the encoded partial-compiler phase answer has the encoded width,
phase tag, wire indices, exponent, and sign, plus three bits for the singleton count. -/
theorem partialCompiler_answerBits_cp (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : e ≤ 3) :
    (answerBits (partialCompiler.Segment w (.cp a c e neg) k)).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + 3 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c.val).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits e).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (if neg then 1 else 0)).length := by
  rw [partialCompiler_segment_cp _ _ _ _ _ he]
  simp [answerBits, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.wordBits, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
    List.flatMap_nil, List.length_append, List.length_cons, List.length_nil, List.append_nil]
  have h1 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length = 3 := rfl
  rw [h1]
  omega

/-- For exponent greater than three, the partial compiler's empty answer has the encoded width
length plus one bit for the zero gate count. -/
theorem partialCompiler_answerBits_empty (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 3 < e) :
    (answerBits (partialCompiler.Segment w (.cp a c e neg) k)).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + 1 := by
  rw [partialCompiler_segment_cp_empty _ _ _ _ _ he]
  have h0 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length = 1 := rfl
  simp [answerBits, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.wordBits, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
    List.flatMap_nil, List.length_append, List.length_cons, List.length_nil, List.append_nil, h0]

/-- The bit length of a partial-compiler answer is at most its synthesis input length plus
three. -/
theorem partialCompiler_answerBits_le (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    (answerBits (partialCompiler.Segment w g k)).length ≤ synthInputBits w g k + 3 := by
  have h1 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length = 3 := rfl
  have h0 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length = 1 := rfl
  cases g with
  | h a =>
    rw [partialCompiler_answerBits_h]
    have hB : synthInputBits w (.h a) k
        = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits k).length
          + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length := by
      simp [synthInputBits, synthInput, gateFields, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
        List.flatMap_nil, List.length_append, List.length_cons, List.length_nil,
        List.append_nil]
      omega
    rw [hB, h0]
    have := natBits_length_pos k
    omega
  | swap a c =>
    rw [partialCompiler_answerBits_swap]
    have hB : synthInputBits w (.swap a c) k
        = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits k).length
          + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length
          + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c.val).length := by
      simp [synthInputBits, synthInput, gateFields, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
        List.flatMap_nil, List.length_append, List.length_cons, List.length_nil,
        List.append_nil]
      omega
    rw [hB]
    have := natBits_length_pos k
    omega
  | cp a c e neg =>
    by_cases he : e ≤ 3
    · rw [partialCompiler_answerBits_cp _ _ _ _ _ _ he]
      have hB : synthInputBits w (.cp a c e neg) k
          = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits k).length
            + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length
            + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c.val).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits e).length
            + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (if neg then 1 else 0)).length := by
        simp [synthInputBits, synthInput, gateFields, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
          List.flatMap_nil, List.length_append, List.length_cons, List.length_nil,
          List.append_nil]
        omega
      rw [hB]
      have := natBits_length_pos k
      omega
    · rw [partialCompiler_answerBits_empty _ _ _ _ _ _ (Nat.lt_of_not_ge he)]
      have hB : synthInputBits w (.cp a c e neg) k
          = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits k).length
            + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 1).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits a.val).length
            + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits c.val).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits e).length
            + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits (if neg then 1 else 0)).length := by
        simp [synthInputBits, synthInput, gateFields, opcodeOf, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields, List.flatMap_cons,
          List.flatMap_nil, List.length_append, List.length_cons, List.length_nil,
          List.append_nil]
        omega
      rw [hB, h1]
      have h1' := natBits_length_pos k
      have h2' := natBits_length_pos a.val
      have h3' := natBits_length_pos c.val
      have h4' := natBits_length_pos e
      have h5' := natBits_length_pos (if neg then 1 else 0)
      omega

/-- A field plan's serialized length is two plus the sum of each encoded field length and
thirteen bits of overhead. -/
theorem planBits_fieldsPlan_len (fs : List ℕ) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (fieldsPlan fs)).length
      = (fs.map (fun j => (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j).length + 13)).sum + 2 := by
  have h5 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5).length = 7 := rfl
  have h2 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2).length = 5 := rfl
  have h0 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length = 1 := rfl
  induction fs with
  | nil => rfl
  | cons j fs ih =>
    have hexp : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (fieldsPlan (j :: fs))
        = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5
            ++ ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2 ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0 ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits j)
              ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (fieldsPlan fs)) := rfl
    rw [hexp, List.map_cons, List.sum_cons]
    simp only [List.length_append]
    rw [ih]
    omega

/-- The serialized answer plan has length at most fourteen times the answer's bit length plus
twenty-eight. -/
theorem answerPlan_planBits_le (ans : SynthAnswer) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (answerPlan ans)).length
      ≤ 14 * (answerBits ans).length + 28 := by
  have h5 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5).length = 7 := rfl
  have h2 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2).length = 5 := rfl
  have h0 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length = 1 := rfl
  have hA : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (answerPlan ans)).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length)).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (fieldsPlan ((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields))).length := by
    have hexp : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (answerPlan ans)
        = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5
            ++ ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2 ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0 ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ans.width)
              ++ (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 5
                ++ ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 2 ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0
                    ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits ((ans.word.map opcodeOf).length))
                  ++ Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits
                    (fieldsPlan ((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields))))) := rfl
    rw [hexp]
    simp only [List.length_append]
    omega
  have hsum :=
      sum_map_natBits_len_add13
      ((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields)
  have hout := answerBits_length ans
  have hge :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.flatNatBits_length_ge
      ((ans.word.map opcodeOf).flatMap Qatlib.Concepts.BitWordCompiler.CanonicalCodec.fields)
  have hpos := natBits_length_pos ans.width
  rw [hA, planBits_fieldsPlan_len]
  omega

/-- Emitting a partial-compiler answer requires plan work at most twenty-four times the request
size. -/
theorem partialCompiler_work_le (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))
      ≤ 24 * requestSize w g k := by
  have h := answerPlan_work_le (partialCompiler.Segment w g k) [] k
  have hout := partialCompiler_answerBits_le w g k
  dsimp [requestSize] at *
  omega

/-- A single finite-state Turing machine emits every answer from its encoded emission plan, with
common time and space budgets bounded by a fixed constant times the twelfth power of one
plus input length, output length, and plan work. -/
theorem emitter_machine_for_answers :
    ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))) (C : ℕ), 0 < C ∧
      ∀ (ans : SynthAnswer) (k : ℕ),
        let p := answerPlan ans
        let input := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput p [] k
        let budget := C * (1 + input.length + (answerBits ans).length
          + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] p) ^ 12
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M input (answerBits ans) budget budget := by
  obtain ⟨q, M, C, hC, hM⟩ :=
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler.uniform_emitter_machine
  refine ⟨q, M, C, hC, ?_⟩
  intro ans k
  have hemit : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] (answerPlan ans) = answerBits ans :=
    emit_answerPlan ans [] k
  have hraw := hM (answerPlan ans) [] k
  have h1 : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan ans) [] k) (answerBits ans)
      (C * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan ans) [] k).length
        + (answerBits ans).length + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan ans)) ^ 12)
      (C * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan ans) [] k).length
        + (answerBits ans).length + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan ans)) ^ 12) := by
    have h2 := hraw.1
    simpa [hemit] using h2
  exact h1

/-- A single finite-state Turing machine emits every partial-compiler answer from its emitter
input within time and space `C * requestSize w g k ^ 12`, for a uniform positive constant
`C`. -/
theorem partialCompiler_machine_budget :
    ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q + 1))) (C : ℕ), 0 < C ∧
      ∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ),
        let ans := partialCompiler.Segment w g k
        let p := answerPlan ans
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] p = answerBits ans ∧
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput p [] k) (answerBits ans)
          (C * requestSize w g k ^ 12) (C * requestSize w g k ^ 12) := by
  obtain ⟨q, M, C₀, hC₀, hM⟩ := emitter_machine_for_answers
  refine ⟨q, M, C₀ * 2048 ^ 12, by positivity, ?_⟩
  intro w g k
  show Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] (answerPlan (partialCompiler.Segment w g k))
        = answerBits (partialCompiler.Segment w g k) ∧
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M
        (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k)
        (answerBits (partialCompiler.Segment w g k))
        ((C₀ * 2048 ^ 12) * requestSize w g k ^ 12)
        ((C₀ * 2048 ^ 12) * requestSize w g k ^ 12)
  have hemit : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emit [] k [] (answerPlan (partialCompiler.Segment w g k))
      = answerBits (partialCompiler.Segment w g k) :=
    emit_answerPlan (partialCompiler.Segment w g k) [] k
  have hplanB := answerPlan_planBits_le (partialCompiler.Segment w g k)
  have hout := partialCompiler_answerBits_le w g k
  have hwork := partialCompiler_work_le w g k
  have hplan : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
      = (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.planBits (answerPlan (partialCompiler.Segment w g k))).length
        + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits k).length := by
    simp only [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput, List.length_append, List.flatMap_nil, List.length_nil,
      List.nil_append]
    omega
  have hsz0 : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits 0).length = 1 := rfl
  have hnat : (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits k).length ≤ 2 * k + 1 := by
    rw [natBits_len]
    have := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Counter.bits_length_le k
    omega
  have hlen : 1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
      + (answerBits (partialCompiler.Segment w g k)).length
      + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))
      ≤ 2048 * requestSize w g k := by
    rw [hplan, hsz0]
    dsimp [requestSize] at hwork ⊢
    omega
  have hmono : (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
        + (answerBits (partialCompiler.Segment w g k)).length
        + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))) ^ 12
      ≤ (2048 * requestSize w g k) ^ 12 :=
    Nat.pow_le_pow_left hlen 12
  have hrun : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.Runs M
      (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k)
      (answerBits (partialCompiler.Segment w g k))
      (C₀ * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
        + (answerBits (partialCompiler.Segment w g k)).length
        + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))) ^ 12)
      (C₀ * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
        + (answerBits (partialCompiler.Segment w g k)).length
        + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))) ^ 12) :=
    hM (partialCompiler.Segment w g k) k
  have hbudget : C₀ * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
        + (answerBits (partialCompiler.Segment w g k)).length
        + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))) ^ 12
      ≤ (C₀ * 2048 ^ 12) * requestSize w g k ^ 12 := by
    calc C₀ * (1 + (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.emitterInput (answerPlan (partialCompiler.Segment w g k)) [] k).length
          + (answerBits (partialCompiler.Segment w g k)).length
          + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.work [] k [] (answerPlan (partialCompiler.Segment w g k))) ^ 12
          ≤ C₀ * (2048 * requestSize w g k) ^ 12 := Nat.mul_le_mul_left C₀ hmono
      _ = (C₀ * 2048 ^ 12) * requestSize w g k ^ 12 := by
          rw [Nat.mul_pow, Nat.mul_assoc]
  exact ⟨hemit, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.runs_mono hrun hbudget hbudget⟩

end Qatlib.Concepts.MatrixAccess.RitzPipeline
