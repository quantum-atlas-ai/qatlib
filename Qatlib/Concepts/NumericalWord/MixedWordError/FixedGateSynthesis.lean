/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.RationalPiApproximation
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.NativeModels

/-!
# Partial fixed gate synthesis and compilation bounds

The partial compiler retains fixed primitive gates and drops controlled phase gates whose angles
meet the proved approximation bound. Rational angle approximation and compilation lemmas record
legality and access counts; the general circuit approximation background is given in
[NielsenChuang2010].

The module also constructs `coarseWord`, whose precision zero input prevents a total error
budget of `1 / 2`, and uses it to refute the universal contract `clause43Body`.

## Main statements

* `partialCompiler_accepts_smallAngle`: certifies controlled phase gates in the small angle
  regime.
* `accessPreserved_compileWord`: preserves every oracle access form count.
* `angleRatOf_error`: proves the rounded rational angle error bound.
* `not_clause3`: refutes the stated universal compilation contract.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.NumericalWord.MixedWordError

namespace Qatlib.Concepts.NumericalWord.MixedWordError

set_option autoImplicit false

open Matrix Qatlib.Concepts.NumericalWord.MixedWordError
open scoped Classical Matrix.Norms.L2Operator

noncomputable section

/-- Padding a register to its own width is the identity matrix. -/
theorem padClean_self (w : ℕ) : padClean w w = 1 := by
  ext p t
  simp only [padClean, Matrix.one_apply]
  have hkey : (fun i : Fin w => if h : i.val < w then t ⟨i.val, h⟩ else false) = t := by
    funext i
    rw [dif_pos i.isLt]
  rw [hkey]

/-- Any two registers of width zero are equal. -/
theorem eq_zero_reg_of_index_zero {m : ℕ} (hm : m = 0) (f g : Reg m) : f = g := by
  subst hm
  funext i
  exact Fin.elim0 i

/-- When the output width equals the data width, every matrix satisfies the clean ancilla
condition for any nonnegative tolerance. -/
theorem cleanAncillaRestored_trivial {w width : ℕ} (h : width = w)
    (M : Matrix (Reg width) (Reg w) ℂ) (tol : ℝ) (htol : 0 ≤ tol) :
    cleanAncillaRestored w M tol := by
  subst width
  intro ψ hψ
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

/-- Every finite matrix approximates itself up to phase at any nonnegative tolerance. -/
theorem approxUpToPhase_refl {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ)
    (tol : ℝ) (htol : 0 ≤ tol) : ApproxUpToPhase A A tol := by
  refine ⟨0, ?_⟩
  have h1 : Complex.exp ((0:ℝ) * Complex.I) = 1 := by
    rw [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  rw [h1, one_smul, sub_self, norm_zero]
  exact htol

/-- The matrix of a singleton local program is the matrix of its gate. -/
theorem localProgramMatrix_singleton {w : ℕ} (g : LocalQFTGate w) :
    localProgramMatrix [g] = localGateMatrix g := by
  simp [localProgramMatrix]

/-- A fixed primitive gate synthesizes itself as a singleton word at every dyadic tolerance. -/
theorem synthesisApprox_singleton {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrimitive g) :
    synthesisApprox w g ⟨w, [g]⟩ (((2 : ℝ) ⁻¹) ^ k) := by
  show (∃ a : ℕ, w = w + a) ∧
    synthWordLegal ⟨w, [g]⟩ ∧
    synthWordOracleCalls ⟨w, [g]⟩ = 0 ∧
    ApproxUpToPhase (localProgramMatrix [g] * padClean w w)
      (padClean w w * localGateMatrix g) (((2 : ℝ) ⁻¹) ^ k) ∧
    cleanAncillaRestored w (localProgramMatrix [g] * padClean w w) (((2 : ℝ) ⁻¹) ^ k)
  refine ⟨⟨0, rfl⟩, ?_, rfl, ?_, ?_⟩
  · intro g' hg'
    rw [List.mem_singleton] at hg'
    rw [hg']
    exact hg
  · have hpad : padClean w w = 1 := padClean_self w
    rw [hpad, localProgramMatrix_singleton, Matrix.mul_one, Matrix.one_mul]
    exact approxUpToPhase_refl _ _ (by positivity)
  · exact cleanAncillaRestored_trivial rfl _ _ (by positivity)

/-- The absolute dyadic phase angle is `2 * π / 2^e`, independently of its sign flag. -/
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

/-- Half the absolute dyadic phase angle is `π / 2^e`. -/
theorem abs_dyadicPhaseAngle_div_two (e : ℕ) (neg : Bool) :
    |dyadicPhaseAngle e neg| / 2 = Real.pi / (2 ^ e : ℝ) := by
  rw [dyadicPhaseAngle_abs, mul_div_assoc,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- If `k + 2 ≤ e`, half the absolute dyadic phase angle is at most `2⁻ᵏ`. -/
theorem smallAngle_tol_le (e k : ℕ) (neg : Bool) (he : k + 2 ≤ e) :
    |dyadicPhaseAngle e neg| / 2 ≤ ((2 : ℝ) ⁻¹) ^ k := by
  rw [abs_dyadicPhaseAngle_div_two]
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

/-- For a real number, the absolute value of its half is half its absolute value. -/
theorem abs_div_two (x : ℝ) : |x / 2| = |x| / 2 := by
  rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]

/-- The distance from one to the complex phase with real angle `t` is at most `|t|`. -/
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

/-- The difference between the identity and a phase scaled controlled phase gate is the diagonal
matrix with the displayed phase differences. -/
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

/-- When `k + 2 ≤ e`, the empty word approximates the controlled phase gate up to global phase
within `2⁻ᵏ`. -/
theorem emptyWord_approx_cp {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : k + 2 ≤ e) :
    ApproxUpToPhase (localProgramMatrix ([] : List (LocalQFTGate w)) * padClean w w)
      (padClean w w * localGateMatrix (.cp a c e neg)) (((2 : ℝ) ⁻¹) ^ k) := by
  have hpad : padClean w w = 1 := padClean_self w
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
      Matrix (Reg w) (Reg w) ℂ)‖ ≤ ((2 : ℝ) ⁻¹) ^ k := by
    have hnorm : ‖(Matrix.diagonal (fun x : Reg w =>
        1 - Complex.exp (φ * Complex.I)
          * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1)) :
        Matrix (Reg w) (Reg w) ℂ)‖
        = ‖(fun x : Reg w =>
        1 - Complex.exp (φ * Complex.I)
          * (if x a && x c then Complex.exp (dyadicPhaseAngle e neg * Complex.I) else 1))‖ :=
      Matrix.l2_opNorm_diagonal _
    rw [hnorm, pi_norm_le_iff_of_nonneg (by positivity)]
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

/-- The partial compiler allocates zero additional ancillas for every gate and precision. -/
def partialAnc : (w : ℕ) → LocalQFTGate w → ℕ → ℕ := fun _ _ _ => 0

/-- The partial compiler emits Hadamard and swap gates unchanged, retains controlled phase gates
with exponent at most three, and otherwise emits the empty word. -/
def partialEmit : (w : ℕ) → (g : LocalQFTGate w) → (k : ℕ) →
    List (LocalQFTGate (w + partialAnc w g k)) :=
  fun _ g _ =>
    match g with
    | .h a => [.h a]
    | .cp a c e neg => if e ≤ 3 then [.cp a c e neg] else []
    | .swap a c => [.swap a c]

/-- The compiler formed from `partialAnc` and `partialEmit`. -/
def partialCompiler : SynthCompiler :=
  ⟨partialAnc, partialEmit⟩

/-- The partial compiler allocates no ancillas. -/
theorem partialCompiler_anc_eq (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    partialCompiler.anc w g k = 0 := rfl

/-- The partial compiler emits a fixed primitive gate as its singleton word. -/
theorem partialCompiler_emit_primitive {w : ℕ} (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrimitive g) : partialCompiler.emit w g k = [g] := by
  cases g with
  | h a => rfl
  | swap a c => rfl
  | cp a c e neg =>
    have he : e ≤ 3 := hg
    show (if e ≤ 3 then [LocalQFTGate.cp a c e neg] else []) = [LocalQFTGate.cp a c e neg]
    rw [if_pos he]

/-- For a controlled phase exponent greater than three, the partial compiler emits the empty
word. -/
theorem partialCompiler_emit_empty {w : ℕ} (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ)
    (he : 3 < e) : partialCompiler.emit w (.cp a c e neg) k = [] := by
  show (if e ≤ 3 then [LocalQFTGate.cp a c e neg] else []) = []
  rw [if_neg (Nat.not_le.mpr he)]

/-- Every word emitted by the partial compiler has length at most one. -/
theorem partialCompiler_emit_length (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
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

/-- The partial compiler satisfies the synthesis acceptance condition for every fixed primitive
gate and precision. -/
theorem partialCompiler_accepts_primitive (w : ℕ) (g : LocalQFTGate w) (k : ℕ)
    (hg : IsFixedPrimitive g) : partialCompiler.AcceptsAt w g k := by
  have hemit : partialCompiler.emit w g k = [g] := partialCompiler_emit_primitive g k hg
  show synthesisWordAccepted w g k (partialCompiler.Segment w g k)
  rw [SynthCompiler.Segment, hemit, synthesisWordAccepted]
  exact synthesisApprox_singleton g k hg

/-- For `1 ≤ k` and `k + 2 ≤ e`, the partial compiler satisfies the synthesis acceptance
condition for the controlled phase gate. -/
theorem partialCompiler_accepts_smallAngle (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool)
    (k : ℕ) (_hk : 1 ≤ k) (he : k + 2 ≤ e) :
    partialCompiler.AcceptsAt w (.cp a c e neg) k := by
  by_cases h3 : e ≤ 3
  · exact partialCompiler_accepts_primitive w (.cp a c e neg) k h3
  · have hemit : partialCompiler.emit w (.cp a c e neg) k = [] :=
      partialCompiler_emit_empty a c e neg k (Nat.lt_of_not_ge h3)
    show synthesisWordAccepted w (.cp a c e neg) k (partialCompiler.Segment w (.cp a c e neg) k)
    rw [SynthCompiler.Segment, hemit, synthesisWordAccepted]
    show (∃ aN : ℕ, w + partialCompiler.anc w (.cp a c e neg) k = w + aN) ∧
      synthWordLegal ⟨w + partialCompiler.anc w (.cp a c e neg) k, []⟩ ∧
      synthWordOracleCalls ⟨w + partialCompiler.anc w (.cp a c e neg) k, []⟩ = 0 ∧
      ApproxUpToPhase
        (localProgramMatrix ([] : List (LocalQFTGate (w + partialCompiler.anc w (.cp a c e neg) k)))
          * padClean w (w + partialCompiler.anc w (.cp a c e neg) k))
        (padClean w (w + partialCompiler.anc w (.cp a c e neg) k)
          * localGateMatrix (.cp a c e neg)) (((2 : ℝ) ⁻¹) ^ k) ∧
      cleanAncillaRestored w
        (localProgramMatrix ([] : List (LocalQFTGate (w + partialCompiler.anc w (.cp a c e neg) k)))
          * padClean w (w + partialCompiler.anc w (.cp a c e neg) k)) (((2 : ℝ) ⁻¹) ^ k)
    refine ⟨⟨0, rfl⟩, ?_, rfl, ?_, ?_⟩
    · intro g hg
      exact (List.not_mem_nil hg).elim
    · exact emptyWord_approx_cp a c e neg k he
    · exact cleanAncillaRestored_trivial rfl _ _ (by positivity)

/-- Every segment emitted by the partial compiler consists of fixed primitive gates. -/
theorem partialCompiler_legal (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    synthWordLegal (partialCompiler.Segment w g k) := by
  have hemit : ∀ g' ∈ partialCompiler.emit w g k, IsFixedPrimitive g' := by
    cases g with
    | h a =>
      intro g' hg'
      have hg'' : g' = LocalQFTGate.h a := List.mem_singleton.mp hg'
      rw [hg'']
      exact True.intro
    | swap a c =>
      intro g' hg'
      have hg'' : g' = LocalQFTGate.swap a c := List.mem_singleton.mp hg'
      rw [hg'']
      exact True.intro
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
  exact fun g' hg' => hemit g' hg'

/-- Every segment emitted by the partial compiler has zero oracle calls. -/
theorem partialCompiler_zero_oracle (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    synthWordOracleCalls (partialCompiler.Segment w g k) = 0 := rfl

/-- The width of each partial compiler segment is the input width plus a natural ancilla count. -/
theorem partialCompiler_width (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    ∃ a : ℕ, (partialCompiler.Segment w g k).width = w + a :=
  ⟨partialCompiler.anc w g k, rfl⟩

/-- The partial compiler segment satisfies the clean ancilla condition at tolerance `2⁻ᵏ`. -/
theorem partialCompiler_clean (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    cleanAncillaRestored w
      (localProgramMatrix (partialCompiler.Segment w g k).letters
        * padClean w (partialCompiler.Segment w g k).width) (((2 : ℝ) ⁻¹) ^ k) :=
  cleanAncillaRestored_trivial (width := (partialCompiler.Segment w g k).width)
    (h := rfl) _ _ (by positivity)

/-- The partial compiler has polynomial bounds on emitted word length and ancilla count in the
synthesis input size and precision. -/
theorem partialCompiler_uniform : UniformSynthLedger partialCompiler := by
  refine ⟨1, 1, fun w g k => ⟨?_, ?_⟩⟩
  · have hlen := partialCompiler_emit_length w g k
    have hs : (1 : ℕ) ≤ 1 + synthInputBits w g k + k := by omega
    rw [one_mul, Nat.pow_one]
    exact le_trans hlen hs
  · rw [one_mul, Nat.pow_one, partialCompiler_anc_eq]
    exact Nat.zero_le _

/-- Lifting an oracle call's control index to a larger register preserves its access form. -/
theorem form_liftCall {n w A : ℕ} {S : Type} (slot : S) (adj : Bool)
    (ctrl : Option (Fin n × Bool)) :
    (MixedStep.call slot adj (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2)))
      : MixedStep (n + A) w S).form
      = (MixedStep.call slot adj ctrl : MixedStep n w S).form := by
  cases ctrl <;> rfl

/-- Prepending a known gate leaves the oracle call count unchanged. -/
theorem callCount_cons_known {n w : ℕ} {S : Type} (g : LocalQFTGate n) (m : ℕ)
    (rest : List (MixedStep n w S)) :
    callCount (MixedStep.known g m :: rest) = callCount rest := by
  show List.countP _ _ = _
  rw [List.countP_cons, if_neg (by simp), add_zero]
  exact rfl

/-- A list consisting only of known gates has zero oracle calls. -/
theorem callCount_map_known {n w A : ℕ} {S : Type} (seg : List (LocalQFTGate (n + A))) :
    callCount (seg.map (fun h => (MixedStep.known h 0 : MixedStep (n + A) w S))) = 0 := by
  induction seg with
  | nil => rfl
  | cons h seg ih =>
    rw [List.map_cons, callCount_cons_known (g := h) (m := 0), ih]

/-- The oracle call count of an appended word is the sum of the call counts. -/
theorem callCount_append {n w : ℕ} {S : Type} (xs ys : List (MixedStep n w S)) :
    callCount (xs ++ ys) = callCount xs + callCount ys := by
  show List.countP _ (xs ++ ys) = _
  exact List.countP_append

/-- Prepending an oracle call increases the call count by one. -/
theorem callCount_cons_call {n w : ℕ} {S : Type} (slot : S) (adj : Bool)
    (ctrl : Option (Fin n × Bool)) (rest : List (MixedStep n w S)) :
    callCount (MixedStep.call slot adj ctrl :: rest) = callCount rest + 1 := by
  show List.countP _ _ = _
  rw [List.countP_cons, if_pos (by simp)]
  exact rfl

/-- Replacing known gates by supplied segments preserves the total oracle call count. -/
theorem callCount_compileWord {n w A : ℕ} {S : Type} :
    ∀ (W : List (MixedStep n w S)) (segs : List (List (LocalQFTGate (n + A)))),
    callCount (compileWord W segs) = callCount W := by
  intro W
  induction W with
  | nil => intro segs; rfl
  | cons st rest ih =>
    intro segs
    cases st with
    | known g m =>
      cases segs with
      | nil =>
        have h := ih []
        simpa [compileWord] using! h
      | cons seg segs' =>
        show callCount (seg.map (fun h => (MixedStep.known h 0 : MixedStep (n + A) w S))
            ++ compileWord rest segs') = callCount (MixedStep.known g m :: rest)
        rw [callCount_append, callCount_map_known, zero_add, ih, callCount_cons_known]
    | call slot adj ctrl =>
      show callCount ((MixedStep.call slot adj
          (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2)))
          : MixedStep (n + A) w S) :: compileWord rest segs)
        = callCount (MixedStep.call slot adj ctrl :: rest)
      rw [callCount_cons_call, callCount_cons_call, ih]

/-- Prepending a step increases an access form's count by one exactly when the step has that
form. -/
theorem accessCount_cons {n w : ℕ} {S : Type} (s : MixedStep n w S)
    (rest : List (MixedStep n w S)) (φ : AccessForm S) :
    accessCount (s :: rest) φ =
      accessCount rest φ +
      (match s.form with
       | some φ' => if φ' = φ then 1 else 0
       | none => 0) := by
  cases s with
  | known g m =>
    show List.countP _ (MixedStep.known g m :: rest) = _
    rw [List.countP_cons, if_neg (by simp [MixedStep.form]), add_zero]
    exact rfl
  | call slot adj ctrl =>
    show List.countP _ (MixedStep.call slot adj ctrl :: rest) = _
    rw [List.countP_cons]
    have hform : (MixedStep.call slot adj ctrl : MixedStep n w S).form
        = some (⟨slot, adj, ctrl.isSome⟩ : AccessForm S) := rfl
    rw [hform]
    by_cases hc : (⟨slot, adj, ctrl.isSome⟩ : AccessForm S) = φ <;> simp [hc, accessCount]

/-- Prepending a known gate leaves every access form count unchanged. -/
theorem accessCount_cons_known {n w : ℕ} {S : Type} (g : LocalQFTGate n) (m : ℕ)
    (rest : List (MixedStep n w S)) (φ : AccessForm S) :
    accessCount (MixedStep.known g m :: rest) φ = accessCount rest φ := by
  rw [accessCount_cons]
  exact rfl

/-- A list consisting only of known gates has zero occurrences of every access form. -/
theorem accessCount_map_known {n w A : ℕ} {S : Type} (seg : List (LocalQFTGate (n + A)))
    (φ : AccessForm S) :
    accessCount (seg.map (fun h => (MixedStep.known h 0 : MixedStep (n + A) w S))) φ = 0 := by
  induction seg with
  | nil => rfl
  | cons h seg ih =>
    rw [List.map_cons, accessCount_cons_known (g := h) (m := 0), ih]

/-- The count of an access form in an appended word is the sum of its counts in the two words. -/
theorem accessCount_append {n w : ℕ} {S : Type} (xs ys : List (MixedStep n w S))
    (φ : AccessForm S) :
    accessCount (xs ++ ys) φ = accessCount xs φ + accessCount ys φ := by
  show List.countP _ (xs ++ ys) = _
  exact List.countP_append

/-- Replacing known gates by supplied segments preserves the count of each access form. -/
theorem accessCount_compileWord {n w A : ℕ} {S : Type} (φ : AccessForm S) :
    ∀ (W : List (MixedStep n w S)) (segs : List (List (LocalQFTGate (n + A)))),
    accessCount (compileWord W segs) φ = accessCount W φ := by
  intro W
  induction W with
  | nil => intro segs; rfl
  | cons st rest ih =>
    intro segs
    cases st with
    | known g m =>
      cases segs with
      | nil =>
        have h := ih []
        simpa [compileWord] using! h
      | cons seg segs' =>
        show accessCount (seg.map (fun h => (MixedStep.known h 0 : MixedStep (n + A) w S))
            ++ compileWord rest segs') φ
          = accessCount (MixedStep.known g m :: rest) φ
        rw [accessCount_append, accessCount_map_known, zero_add, ih, accessCount_cons_known]
    | call slot adj ctrl =>
      show accessCount ((MixedStep.call slot adj
          (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2)))
          : MixedStep (n + A) w S) :: compileWord rest segs) φ
        = accessCount (MixedStep.call slot adj ctrl :: rest) φ
      rw [accessCount_cons, accessCount_cons, form_liftCall, ih]

/-- Compilation by replacing known gates preserves all access form counts. -/
theorem accessPreserved_compileWord {n w A : ℕ} {S : Type}
    (W : List (MixedStep n w S)) (segs : List (List (LocalQFTGate (n + A)))) :
    AccessPreserved W (compileWord W segs) :=
  fun φ => accessCount_compileWord φ W segs

/-- Replacing known gates by supplied segments preserves legality with respect to the same paid
access forms. -/
theorem mixedWordLegal_compileWord {n w A : ℕ} {S : Type} :
    ∀ (W : List (MixedStep n w S)) (segs : List (List (LocalQFTGate (n + A))))
      (paid : List (AccessForm S)), mixedWordLegal W paid →
      mixedWordLegal (compileWord W segs) paid := by
  intro W
  induction W with
  | nil =>
    intro segs paid _ s hs
    exact (List.not_mem_nil hs).elim
  | cons st rest ih =>
    intro segs paid hleg s hs
    cases st with
    | known g m =>
      cases segs with
      | nil =>
        exact ih [] paid (fun x hx => hleg x (List.mem_cons_of_mem _ hx)) s hs
      | cons seg segs' =>
        have hcomp : compileWord (MixedStep.known g m :: rest) (seg :: segs')
            = seg.map (fun h => (MixedStep.known h 0 : MixedStep (n + A) w S))
              ++ compileWord rest segs' := rfl
        rw [hcomp] at hs
        rcases List.mem_append.1 hs with hs | hs
        · obtain ⟨h, -, rfl⟩ := List.mem_map.1 hs
          trivial
        · exact ih segs' paid (fun x hx => hleg x (List.mem_cons_of_mem _ hx)) s hs
    | call slot adj ctrl =>
      have hcomp : compileWord (MixedStep.call slot adj ctrl :: rest) segs
          = (MixedStep.call slot adj
              (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2)))
              : MixedStep (n + A) w S) :: compileWord rest segs := rfl
      rw [hcomp] at hs
      rcases List.mem_cons.1 hs with rfl | hs
      · have hform := hleg (MixedStep.call slot adj ctrl) (List.mem_cons_self)
        show (match (MixedStep.call slot adj
            (ctrl.map (fun c => ((⟨c.1.val, by omega⟩ : Fin (n + A)), c.2)))
            : MixedStep (n + A) w S).form with
          | some φ => φ ∈ paid | none => True)
        rw [form_liftCall]
        exact hform
      · exact ih segs paid (fun x hx => hleg x (List.mem_cons_of_mem _ hx)) s hs

/-- A signed rational approximation to the dyadic phase angle, using `piRatApprox` at precision
`bits + e + 2`. -/
def angleRatT (e : ℕ) (neg : Bool) (bits : ℕ) : ℚ :=
  (if neg then (-1 : ℚ) else (1 : ℚ)) * 2 * piRatApprox (bits + e + 2) / (2 ^ e : ℚ)

/-- The rational dyadic value obtained by rounding `angleRatT` to a multiple of `1 / 2^bits`
using a shifted floor. -/
def angleRatOf (e : ℕ) (neg : Bool) (bits : ℕ) : ℚ :=
  (Int.floor ((angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ) + 1 / 2)) / (2 ^ bits : ℚ)

/-- The rounded rational angle for a controlled phase gate, and zero for every other local gate. -/
def angleRatOfGate {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) : ℚ :=
  match g with
  | .cp _ _ e neg => angleRatOf e neg bits
  | _ => 0

/-- The rounded angle is an integer multiple of `1 / 2^bits`. -/
theorem angleRatOf_dyadic (e : ℕ) (neg : Bool) (bits : ℕ) :
    ∃ m : ℤ, angleRatOf e neg bits = m / ((2 : ℚ) ^ bits) :=
  ⟨Int.floor ((angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ) + 1 / 2), rfl⟩

/-- Rounding a real number with `Int.floor (x + 1 / 2)` incurs absolute error at most one half. -/
theorem floor_round_error (x : ℝ) :
    |((Int.floor (x + 1 / 2) : ℤ) : ℝ) - x| ≤ 1 / 2 := by
  have h1 : ((Int.floor (x + 1 / 2) : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have h2 : x + 1 / 2 < ((Int.floor (x + 1 / 2) : ℤ) : ℝ) + 1 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The rounded angle differs from `angleRatT` by at most `(1 / 2)^(bits + 1)` after casting to
the reals. -/
theorem angleRatOf_near_T (e : ℕ) (neg : Bool) (bits : ℕ) :
    |((angleRatOf e neg bits : ℚ) : ℝ) - (angleRatT e neg bits : ℝ)|
      ≤ ((2 : ℝ) ⁻¹) ^ (bits + 1) := by
  have h2b : (0 : ℝ) < (2:ℝ) ^ bits := by positivity
  have hcast : ((angleRatOf e neg bits : ℚ) : ℝ)
      = ((Int.floor ((angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ) + 1 / 2)) : ℝ)
          / (2 ^ bits : ℝ) := by
    rw [angleRatOf]
    push_cast; rfl
  have hnum := floor_round_error ((angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ))
  have hkey : ((Int.floor ((angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ) + 1 / 2)) : ℝ)
      / (2 ^ bits : ℝ) - (angleRatT e neg bits : ℝ)
      = (((Int.floor ((angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ) + 1 / 2)) : ℝ)
          - (angleRatT e neg bits : ℝ) * (2 ^ bits : ℝ)) / (2 ^ bits : ℝ) := by
    field_simp
  rw [hcast, hkey, abs_div, abs_of_pos h2b]
  refine le_trans (div_le_div_of_nonneg_right hnum (le_of_lt h2b)) ?_
  have hpow : (1 / 2 / (2:ℝ) ^ bits : ℝ) = ((2 : ℝ) ⁻¹) ^ (bits + 1) := by
    have h : ((2:ℝ)⁻¹) ^ (bits + 1) = 1 / (2:ℝ) ^ (bits + 1) := by
      rw [inv_eq_one_div, _root_.div_pow, one_pow]
    rw [h]
    have h2 : (2:ℝ) ^ (bits + 1) = 2 * (2:ℝ) ^ bits := by
      rw [pow_succ]
      ring
    rw [h2]
    field_simp
  exact le_of_eq hpow

/-- The scaled power of two tail term is at most `(1 / 2)^(bits + 1)`. -/
theorem two_pow_tail_bound (e bits : ℕ) :
    2 * ((2 : ℝ) ⁻¹) ^ (bits + e + 4) / (2:ℝ) ^ e ≤ ((2 : ℝ) ⁻¹) ^ (bits + 1) := by
  have hinv : ((2:ℝ) ^ e)⁻¹ = ((2:ℝ)⁻¹) ^ e := (inv_pow (2:ℝ) e).symm
  have h1 : 2 * ((2:ℝ)⁻¹) ^ (bits + e + 4) / (2:ℝ) ^ e
      = 2 * ((2:ℝ)⁻¹) ^ (bits + e + 4) * ((2:ℝ)⁻¹) ^ e := by
    rw [div_eq_mul_inv, hinv]
  have h2 : 2 * ((2:ℝ)⁻¹) ^ (bits + e + 4) * ((2:ℝ)⁻¹) ^ e
      = 2 * ((2:ℝ)⁻¹) ^ (bits + e + 4 + e) := by
    rw [mul_assoc, ← pow_add]
  have h3 : 2 * ((2:ℝ)⁻¹) ^ (bits + e + 4 + e) = ((2:ℝ)⁻¹) ^ (bits + 2 * e + 3) := by
    have ha : bits + e + 4 + e = bits + 2 * e + 3 + 1 := by omega
    rw [ha, pow_succ]
    field_simp
  have h4 : ((2:ℝ)⁻¹) ^ (bits + 2 * e + 3) ≤ ((2:ℝ)⁻¹) ^ (bits + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [h1, h2, h3]
  exact h4

/-- The rational angle `angleRatT` approximates the dyadic phase angle within `(1 / 2)^(bits +
1)`. -/
theorem angleRatT_error (e : ℕ) (neg : Bool) (bits : ℕ) :
    |((angleRatT e neg bits : ℚ) : ℝ) - dyadicPhaseAngle e neg|
      ≤ ((2 : ℝ) ⁻¹) ^ (bits + 1) := by
  have hpi := (rational_machin_pi_computed_precision.2 (bits + e + 2)).2.2
  have h2e : (0 : ℝ) < (2:ℝ) ^ e := by positivity
  have hcast : ((angleRatT e neg bits : ℚ) : ℝ)
      = (if neg then (-1:ℝ) else 1) * 2 * ((piRatApprox (bits + e + 2) : ℚ) : ℝ)
          / (2 ^ e : ℝ) := by
    rw [angleRatT]
    by_cases hn : neg
    · rw [if_pos hn, if_pos hn]
      push_cast; ring
    · rw [if_neg hn, if_neg hn]
      push_cast; ring
  have hθ : dyadicPhaseAngle e neg
      = (if neg then (-1:ℝ) else 1) * (2 * Real.pi / (2 ^ e : ℝ)) := by
    cases neg <;> simp [dyadicPhaseAngle]
  have hmain : |((angleRatT e neg bits : ℚ) : ℝ)
      - (if neg then (-1:ℝ) else 1) * (2 * Real.pi / (2 ^ e : ℝ))|
      = 2 * |((piRatApprox (bits + e + 2) : ℚ) : ℝ) - Real.pi| / (2:ℝ) ^ e := by
    rw [hcast]
    by_cases hn : neg
    · rw [if_pos hn]
      have hz : (-1:ℝ) * 2 * ((piRatApprox (bits + e + 2) : ℚ) : ℝ) / (2 ^ e : ℝ)
          - (-1) * (2 * Real.pi / (2 ^ e : ℝ))
          = -((2:ℝ) * (((piRatApprox (bits + e + 2) : ℚ) : ℝ) - Real.pi) / (2:ℝ) ^ e) := by
        field_simp; ring
      rw [hz, abs_neg, abs_div, abs_mul, abs_of_pos h2e, abs_of_nonneg (by norm_num)]
    · rw [if_neg hn]
      have hz : (1:ℝ) * 2 * ((piRatApprox (bits + e + 2) : ℚ) : ℝ) / (2 ^ e : ℝ)
          - 1 * (2 * Real.pi / (2 ^ e : ℝ))
          = (2:ℝ) * (((piRatApprox (bits + e + 2) : ℚ) : ℝ) - Real.pi) / (2:ℝ) ^ e := by
        field_simp
      rw [hz, abs_div, abs_mul, abs_of_pos h2e, abs_of_nonneg (by norm_num)]
  rw [hθ, hmain]
  refine le_trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpi (by norm_num)) (by positivity)) ?_
  exact two_pow_tail_bound e bits

/-- The rounded rational angle approximates the dyadic phase angle within `(1 / 2)^bits`. -/
theorem angleRatOf_error (e : ℕ) (neg : Bool) (bits : ℕ) :
    |((angleRatOf e neg bits : ℚ) : ℝ) - dyadicPhaseAngle e neg|
      ≤ ((2 : ℝ) ⁻¹) ^ bits := by
  have h1 := angleRatOf_near_T e neg bits
  have h2 := angleRatT_error e neg bits
  refine le_trans (abs_sub_le _ _ _) (le_trans (add_le_add h1 h2) ?_)
  have hpow : ((2 : ℝ) ⁻¹) ^ (bits + 1) + ((2 : ℝ) ⁻¹) ^ (bits + 1) = ((2 : ℝ) ⁻¹) ^ bits := by
    rw [pow_succ ((2 : ℝ) ⁻¹) bits]
    field_simp; ring
  rw [hpow]

/-- The gate dependent rounded rational angle satisfies the required error bound and dyadic
denominator condition. -/
theorem angleInputOK_angleRatOfGate {w : ℕ} (g : LocalQFTGate w) (bits : ℕ) :
    angleInputOK g bits (angleRatOfGate g bits) := by
  cases g with
  | h a => trivial
  | swap a c => trivial
  | cp a c e neg =>
    show |((angleRatOf e neg bits : ℚ) : ℝ) - dyadicPhaseAngle e neg|
        ≤ ((2 : ℝ) ⁻¹) ^ bits ∧
      ∃ m : ℤ, angleRatOf e neg bits = m / ((2 : ℚ) ^ bits)
    exact ⟨angleRatOf_error e neg bits, angleRatOf_dyadic e neg bits⟩

/-- The condition that a controlled phase exponent lies strictly between three and `k + 2` and
that the partial compiler accepts the gate at precision `k`. -/
def synthesisGapWindow (w : ℕ) (a c : Fin w) (e : ℕ) (neg : Bool) (k : ℕ) : Prop :=
  3 < e ∧ e < k + 2 ∧ partialCompiler.AcceptsAt w (.cp a c e neg) k

/-- The source native program obtained by converting a compiler's emitted gates into local steps
at the expanded register width. -/
def scBuild (c : SynthCompiler) (w : ℕ) (g : LocalQFTGate w) (k : ℕ) :
    Qatlib.Concepts.BitWordCompiler.WordComposition.SourceNativeProgram :=
  ⟨w + c.anc w g k, (c.emit w g k).map
    (fun h => Qatlib.Concepts.BitWordCompiler.WordComposition.SourceNativeStep.local h)⟩

/-- The native program obtained from a compiler's ancilla count and emitted gates, with the all
zero auxiliary string listed as its clean output. -/
def lsBuild (c : SynthCompiler) (h : ℕ) (g : LocalQFTGate h) (k : ℕ) :
    Qatlib.Concepts.BitWordCompiler.WordComposition.NativeProgram h :=
  ⟨c.anc h g k, (c.emit h g k).map
    (fun x => Qatlib.Concepts.BitWordCompiler.WordComposition.NativeStep.local x),
    [ZeroStr (c.anc h g k)]⟩

/-- The contract asserting a universally accepting synthesis compiler with uniform size bounds,
error controlled mixed word compilation preserving access counts, and source and native
synthesis time bounds. -/
def clause43Body : Prop :=
  ∃ (c : SynthCompiler) (C D : ℕ),
    (∀ (w : ℕ) (g : LocalQFTGate w) (k : ℕ), 1 ≤ k → c.AcceptsAt w g k) ∧
    UniformSynthLedger c ∧
    (∀ (n w : ℕ) (S : Type) (O : S → Matrix (Reg w) (Reg w) ℂ)
      (paid : List (AccessForm S)) (W : List (MixedStep n w S)) (L : ℕ) (ε : ℝ)
      (hw : w ≤ n),
      (∀ s, O s ∈ Matrix.unitaryGroup (Reg w) ℂ) →
      mixedWordLegal W paid →
      callCount W = L →
      0 < ε →
      ∃ (cmp : WordCompilation c W) (segs : List (List (LocalQFTGate (n + cmp.A))))
        (W' : List (MixedStep (n + cmp.A) w S)) (bitTime peakSpace : ℕ),
        AlignedWith W segs cmp.ks ∧
        SegmentsFrom c W segs cmp.ks ∧
        W' = compileWord W segs ∧
        List.Forall₂
          (fun (g : LocalQFTGate n) (sk : List (LocalQFTGate (n + cmp.A)) × ℕ) =>
            synthesisApprox n g ⟨n + cmp.A, sk.1⟩ (((2 : ℝ) ⁻¹) ^ sk.2))
          (knownGates W) (List.zip segs cmp.ks) ∧
        BudgetLE cmp ε ∧
        AccessPreserved W W' ∧
        callCount W' = L ∧
        mixedWordLegal W' paid ∧
        CompiledOperatorErrorLE hw (show w ≤ n + cmp.A from by omega) O W W' ε ∧
        CompiledWholeStateErrorLE hw (show w ≤ n + cmp.A from by omega) O W W' ε ∧
        CompiledCleanPoolLE (show w ≤ n + cmp.A from by omega) O W' ε ∧
        CompileLedgersOK
          ((List.zip (knownGates W) cmp.ks).map (fun gk => segmentSize gk.1 gk.2))
          (mixedWordGates W') bitTime peakSpace C D) ∧
    (∃ C1 D1 : ℕ, Qatlib.Concepts.BitWordCompiler.WordComposition.sourceSynthesisCompilerTime
      (fun {w : ℕ} (g : LocalQFTGate w) (k : ℕ) => scBuild c w g k) C1 D1) ∧
    (∃ C2 D2 : ℕ,
      Qatlib.Concepts.BitWordCompiler.WordComposition.nativeSynthesisTime
      (fun {h : ℕ} (g : LocalQFTGate h) (k : ℕ) => lsBuild c h g k) C2 D2)

/-- The one qubit mixed word containing a single known Hadamard gate at precision zero. -/
def coarseWord : List (MixedStep 1 1 Empty) := [.known (.h 0) 0]

/-- The list of known gate precisions in `coarseWord` is `[0]`. -/
theorem knownPrecs_coarseWord : knownPrecs coarseWord = [0] := rfl

/-- The word `coarseWord` contains exactly one known gate. -/
theorem knownCount_coarseWord : knownCount coarseWord = 1 := rfl

/-- No compilation of `coarseWord` satisfies the total error budget `1 / 2`. -/
theorem budgetLE_false_coarseWord (c : SynthCompiler) (cmp : WordCompilation c coarseWord) :
    ¬ BudgetLE cmp (1/2 : ℝ) := by
  have hlen : cmp.ks.length = 1 := by
    rw [cmp.hlen, knownCount_coarseWord]
  obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hlen
  show ¬ (((List.zip (knownPrecs coarseWord) cmp.ks).map
      (fun mk => ((2 : ℝ) ⁻¹) ^ mk.1 + ((2 : ℝ) ⁻¹) ^ mk.2)).sum ≤ (1/2 : ℝ))
  rw [knownPrecs_coarseWord, hk]
  intro h
  have hpow : (0:ℝ) ≤ ((2 : ℝ) ⁻¹) ^ k := by positivity
  have hzip : (List.zip ([0] : List ℕ) [k]) = [((0, k) : ℕ × ℕ)] := rfl
  rw [hzip] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero] at h
  linarith

/-- The universal synthesis and compilation contract `clause43Body` is false. -/
theorem not_clause3 : ¬ clause43Body := by
  rintro ⟨c, _C, _D, _hacc, _hled, hall, _hsrc, _hnat⟩
  have hunit : ∀ s : Empty,
      (fun _ : Empty => (1 : Matrix (Reg 1) (Reg 1) ℂ)) s
        ∈ Matrix.unitaryGroup (Reg 1) ℂ := fun s => nomatch s
  have hlegal : mixedWordLegal coarseWord ([] : List (AccessForm Empty)) := by
    intro s hs
    have hs' : s = MixedStep.known (.h 0) 0 := by simpa [coarseWord] using! hs
    subst hs'
    trivial
  have hcount : callCount coarseWord = 0 := rfl
  specialize hall 1 1 Empty (fun _ : Empty => (1 : Matrix (Reg 1) (Reg 1) ℂ))
    [] coarseWord 0 (1/2 : ℝ) (le_refl 1)
    hunit hlegal hcount (by norm_num)
  obtain ⟨cmp, _segs, _W', _bt, _ps, _, _, _, _, hbudget, _⟩ := hall
  exact budgetLE_false_coarseWord c cmp hbudget

end

end Qatlib.Concepts.NumericalWord.MixedWordError
