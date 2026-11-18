/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Data.Fintype.Basic

public import Qatlib.Concepts.GateKit.Cor74Net
public import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
public import Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
public import Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
public import Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
public import Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
public import Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliGadget
public import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
public import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownQubitEuler
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.CostModels.Profile
public import Qatlib.Concepts.CostModels.Budget

@[expose] public section

/-!
# GateKit elementary-gate counts of the compiled Corollary 7.4 word

This module measures the compiled `Cor74Net` word gate by gate and compares
the resulting counts with the source budget. Three counting conventions are kept apart
and each is a theorem on the actual `cor74Word` product:

* one-qubit versus two-qubit elementary gates (`cor74OneQ`, `cor74TwoQ`), summing to
  the public exact word length `48 * m - 109` (`cor74LenSum`);
* Toffoli macro blocks (`toffCount` of the block ledger, `8 * m - 24` public census);
* the literal T-count `cor74TGate`: gates whose single-qubit matrix is the literal
  `tGate` or its adjoint. This is a syntactic count on the produced word: the four
  exact Toffoli middle words contribute twenty-four literal T/T† gates and the packed
  commutator frame contributes one more (the canceler `tGateᴴ`, provably equal to
  `tGateAdj`), for a total of twenty-five independent of `m`. Composite single-qubit
  frame matrices containing a T rotation, such as `tGate * Rᴴ`, are single elementary
  gates here. The literal count is for this word before any decomposition into
  a Clifford+T basis.

Resource-unit distinction: the paper's `48 * n - 204` bound is a
sum of one-qubit and two-qubit gates, while `BudgetLe` compares per-field slots, so
`cor74BasicBound` delivers the sum bound as an independent theorem and no seven-field
budget expresses it.

## Main statements

* `cor74OneQ`/`cor74TwoQ`: exact elementary counts `24 * m - 49` and `24 * m - 60`.
* `cor74LenSum`: the two elementary counts sum to the public length `48 * m - 109`.
* `cor74BasicBound`: the measured elementary total is at most `48 * (m + 2) - 204`.
* `cor7Cert`: a `CompileCert` for the seven-wire instance against `cor74Budget 7`.
-/

set_option autoImplicit false
set_option warningAsError true

open Matrix
open scoped ComplexConjugate Classical
open Qatlib.Concepts.CircuitImpl.MultiControl
open Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
open Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
open Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
open Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.Budget

namespace Qatlib.Concepts.GateKit

/-! ## Elementary counting functions -/

/-- Number of single-qubit elementary gates (`.inl` entries) in a reflection word. -/
def oneQOf {N : ℕ} : List (ReflectionGate N) → ℕ
  | [] => 0
  | .inl _ :: gs => oneQOf gs + 1
  | .inr _ :: gs => oneQOf gs

/-- Number of two-qubit elementary gates (`.inr` entries) in a reflection word. -/
def twoQOf {N : ℕ} : List (ReflectionGate N) → ℕ
  | [] => 0
  | .inl _ :: gs => twoQOf gs
  | .inr _ :: gs => twoQOf gs + 1

/-- Literal T-coverage of one reflection gate: one when its matrix is the literal
`tGate` or `tGateAdj` phase gate, zero otherwise, and never a fabricated count for a
composite matrix. -/
noncomputable def gateTCount {N : ℕ} (g : ReflectionGate N) : ℕ :=
  match g with
  | .inl (_, U) => if U = tGate then 1 else if U = tGateAdj then 1 else 0
  | .inr _ => 0

/-- Word-level literal T-count of a reflection word. -/
noncomputable def tGateOf {N : ℕ} : List (ReflectionGate N) → ℕ
  | [] => 0
  | g :: gs => tGateOf gs + gateTCount g

/-- Prepending one gate adds its own one-qubit count to the word count. -/
private theorem oneQOfCons {N : ℕ} (g : ReflectionGate N) (gs : List (ReflectionGate N)) :
    oneQOf (g :: gs) = oneQOf gs + oneQOf [g] := by cases g <;> rfl

/-- Prepending one gate adds its own two-qubit count to the word count. -/
private theorem twoQOfCons {N : ℕ} (g : ReflectionGate N) (gs : List (ReflectionGate N)) :
    twoQOf (g :: gs) = twoQOf gs + twoQOf [g] := by cases g <;> rfl

/-- Prepending one gate adds its own literal T-count to the word count. -/
private theorem tGateOfCons {N : ℕ} (g : ReflectionGate N) (gs : List (ReflectionGate N)) :
    tGateOf (g :: gs) = tGateOf gs + tGateOf [g] := by simp only [tGateOf, zero_add]

/-- A one-gate word has exactly one elementary gate. -/
private theorem oneTwoSingle {N : ℕ} (g : ReflectionGate N) : oneQOf [g] + twoQOf [g] = 1 := by
  cases g <;> rfl

/-- The one-qubit count is additive under word concatenation. -/
theorem oneQOfAppend {N : ℕ} (as bs : List (ReflectionGate N)) :
    oneQOf (as ++ bs) = oneQOf as + oneQOf bs := by
  induction as with
  | nil => simp [oneQOf]
  | cons a as ih =>
    rw [List.cons_append, oneQOfCons a (as ++ bs), oneQOfCons a as, ih]; omega

/-- The two-qubit count is additive under word concatenation. -/
theorem twoQOfAppend {N : ℕ} (as bs : List (ReflectionGate N)) :
    twoQOf (as ++ bs) = twoQOf as + twoQOf bs := by
  induction as with
  | nil => simp [twoQOf]
  | cons a as ih =>
    rw [List.cons_append, twoQOfCons a (as ++ bs), twoQOfCons a as, ih]; omega

/-- The literal T-count is additive under word concatenation. -/
theorem tGateOfAppend {N : ℕ} (as bs : List (ReflectionGate N)) :
    tGateOf (as ++ bs) = tGateOf as + tGateOf bs := by
  induction as with
  | nil => simp [tGateOf]
  | cons a as ih =>
    rw [List.cons_append, tGateOfCons a (as ++ bs), tGateOfCons a as, ih]; omega

/-- The one- and two-qubit counts partition the word length. -/
theorem oneTwoSum {N : ℕ} (gs : List (ReflectionGate N)) :
    oneQOf gs + twoQOf gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [oneQOfCons g gs, twoQOfCons g gs, List.length_cons]
    have h1 := oneTwoSingle g
    omega

/-! ## The two literal T gates -/

/-- The conjugate transpose of the phase gate `Rz θ` is `Rz (-θ)`. -/
private theorem rzConj (θ : ℝ) : (Rz θ)ᴴ = Rz (-θ) := by
  ext i j
  rw [Matrix.conjTranspose_apply, Rz, Rz, Matrix.diagonal_apply, Matrix.diagonal_apply]
  cases i <;> cases j
  · simp
  · simp
  · simp
  · show conj (Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp ((↑(-θ) : ℂ) * Complex.I)
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

/-- The adjoint of the literal T gate is the literal T† gate. -/
private theorem tGateConj : tGateᴴ = tGateAdj := rzConj (Real.pi / 4)

/-- The adjoint of the literal T† gate is the literal T gate. -/
private theorem tGateAdjConj : tGateAdjᴴ = tGate := by
  have h := rzConj (-(Real.pi / 4))
  show (Rz (-(Real.pi / 4)))ᴴ = Rz (Real.pi / 4)
  rw [h]
  congr 1
  ring

/-- The literal T and T† gates are distinct phase gates. -/
private theorem tGateNeAdj : tGate ≠ tGateAdj := by
  intro h
  have e1 : tGate true true = Complex.exp (Complex.ofReal (Real.pi / 4) * Complex.I) := rfl
  have e2 : tGateAdj true true
      = Complex.exp (Complex.ofReal (-(Real.pi / 4)) * Complex.I) := rfl
  have htt := congrArg (fun M => M true true) h
  rw [e1, e2, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg,
    Complex.ofReal_neg, Real.cos_pi_div_four, Real.sin_pi_div_four] at htt
  have h6 : Complex.ofReal (Real.sqrt 2 / 2) * Complex.I
      = -(Complex.ofReal (Real.sqrt 2 / 2)) * Complex.I := add_left_cancel htt
  have h8 : (2 : ℂ) * (Complex.ofReal (Real.sqrt 2 / 2) * Complex.I) = 0 := by
    linear_combination h6
  have h9 := (mul_eq_zero.mp h8).resolve_left two_ne_zero
  have h10 := (mul_eq_zero.mp h9).resolve_right Complex.I_ne_zero
  exact absurd (Complex.ofReal_eq_zero.mp h10) (by positivity)

/-- Complex conjugation fixes real coerced numbers. -/
private theorem starOfReal (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
  show conj ((x : ℝ) : ℂ) = _
  exact Complex.conj_ofReal x

/-- The half-angle of the packed rotation frame is never a multiple of `2π`, so its
cosine is never one. -/
private theorem cosAngNeOne (h : Real.cos (-Real.pi / 4 / 2) = 1) : False := by
  have hn : -Real.pi / 4 / 2 = -(Real.pi / 8) := by ring
  rw [hn, Real.cos_neg, Real.cos_eq_one_iff_of_lt_of_lt
    (by nlinarith [Real.pi_pos] : -(2 * Real.pi) < Real.pi / 8)
    (by nlinarith [Real.pi_pos] : Real.pi / 8 < 2 * Real.pi)] at h
  nlinarith [Real.pi_pos]

/-- The false-false entry of the packed rotation frame differs from one. -/
private theorem eulFfNe : (qubitEulerRotation (-Real.pi / 4)) false false ≠ 1 := by
  intro h
  exact cosAngNeOne (Complex.ofReal_eq_one.mp h)

/-- The false-false entry of the packed rotation frame is the real cosine of half the
negative quarter-turn angle. -/
private theorem eulEntry : (qubitEulerRotation (-Real.pi / 4)) false false
    = (Real.cos (-Real.pi / 4 / 2) : ℂ) := rfl

/-- The false-false entry of the adjoint packed rotation frame differs from one. -/
private theorem eulAdjFfNe : ((qubitEulerRotation (-Real.pi / 4))ᴴ) false false ≠ 1 := by
  intro h
  rw [Matrix.conjTranspose_apply] at h
  have h2 : star ((Real.cos (-Real.pi / 4 / 2) : ℂ)) = 1 := h
  rw [starOfReal] at h2
  exact cosAngNeOne (Complex.ofReal_eq_one.mp h2)

/-- The false-false entry of the Hadamard gate differs from one. -/
private theorem hadFf : Hadamard false false ≠ 1 := by
  intro h
  simp [Hadamard] at h

/-- The false-false entry of the merged frame product `tGate * Rᴴ` differs from one. -/
private theorem prod1FfNe :
    (tGate * (qubitEulerRotation (-Real.pi / 4))ᴴ) false false ≠ 1 := by
  intro h
  have hsum : (tGate * (qubitEulerRotation (-Real.pi / 4))ᴴ) false false
      = star ((Real.cos (-Real.pi / 4 / 2) : ℂ)) := by
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, eulEntry]
    rw [show tGate false true = 0 from rfl, show tGate false false = 1 from rfl,
      zero_mul, one_mul, zero_add]
  rw [hsum, starOfReal] at h
  exact cosAngNeOne (Complex.ofReal_eq_one.mp h)

/-- The false-false entry of the merged frame product `R * tGateᴴ` differs from one. -/
private theorem prod2FfNe :
    ((qubitEulerRotation (-Real.pi / 4)) * tGateᴴ) false false ≠ 1 := by
  intro h
  have hE : tGateᴴ false false = 1 := by rw [tGateConj]; rfl
  have hE2 : tGateᴴ true false = 0 := by rw [tGateConj]; rfl
  have hsum : ((qubitEulerRotation (-Real.pi / 4)) * tGateᴴ) false false
      = (Real.cos (-Real.pi / 4 / 2) : ℂ) := by
    simp only [Matrix.mul_apply, Fintype.sum_bool, hE, hE2, eulEntry, mul_one, mul_zero,
      zero_add]
  rw [hsum] at h
  exact cosAngNeOne (Complex.ofReal_eq_one.mp h)

/-! ## Per-gate literal T coverage -/

/-- Both literal T gates have false-false entry one, so any single-qubit matrix with a
different false-false entry is neither of them. -/
private theorem neTOfFf {U : Matrix Bool Bool ℂ} (h : U false false ≠ 1) :
    U ≠ tGate ∧ U ≠ tGateAdj := by
  constructor
  · intro he
    exact h (by rw [he]; rfl)
  · intro he
    exact h (by rw [he]; rfl)

/-- A literal T gate contributes one to the literal T-count. -/
private theorem gateTTG {N : ℕ} (w : Fin N) : gateTCount (Sum.inl (w, tGate)) = 1 := by
  show (if tGate = tGate then 1 else if tGate = tGateAdj then 1 else 0) = 1
  rw [ite_eq_left rfl]

/-- A literal T† gate contributes one to the literal T-count. -/
private theorem gateTAdj {N : ℕ} (w : Fin N) : gateTCount (Sum.inl (w, tGateAdj)) = 1 := by
  show (if tGateAdj = tGate then 1 else if tGateAdj = tGateAdj then 1 else 0) = 1
  rw [ite_eq_right (Ne.symm tGateNeAdj), ite_eq_left rfl]

/-- The frame canceler `tGateᴴ` is a literal T† gate and contributes one. -/
private theorem gateTTAdj {N : ℕ} (w : Fin N) : gateTCount (Sum.inl (w, tGateᴴ)) = 1 := by
  show (if tGateᴴ = tGate then 1 else if tGateᴴ = tGateAdj then 1 else 0) = 1
  rw [tGateConj, ite_eq_right (Ne.symm tGateNeAdj), ite_eq_left rfl]

/-- A single-qubit matrix with false-false entry different from one contributes zero
to the literal T-count. -/
private theorem gateTOfFf {N : ℕ} (w : Fin N) {U : Matrix Bool Bool ℂ}
    (h : U false false ≠ 1) : gateTCount (Sum.inl (w, U)) = 0 := by
  obtain ⟨h1, h2⟩ := neTOfFf h
  show (if U = tGate then 1 else if U = tGateAdj then 1 else 0) = 0
  rw [ite_eq_right h1, ite_eq_right h2]

/-- The packed rotation frame gate is not a literal T gate. -/
private theorem gateTEul {N : ℕ} (w : Fin N) :
    gateTCount (Sum.inl (w, qubitEulerRotation (-Real.pi / 4))) = 0 :=
  gateTOfFf w eulFfNe

/-- The adjoint packed rotation frame gate is not a literal T gate. -/
private theorem gateTEulAdj {N : ℕ} (w : Fin N) :
    gateTCount (Sum.inl (w, (qubitEulerRotation (-Real.pi / 4))ᴴ)) = 0 :=
  gateTOfFf w eulAdjFfNe

/-- The Hadamard frame gate is not a literal T gate. -/
private theorem gateTHad {N : ℕ} (w : Fin N) : gateTCount (Sum.inl (w, Hadamard)) = 0 :=
  gateTOfFf w hadFf

/-- The merged frame product `tGate * Rᴴ` is not a literal T gate. -/
private theorem gateTProd1 {N : ℕ} (w : Fin N) :
    gateTCount (Sum.inl (w, tGate * (qubitEulerRotation (-Real.pi / 4))ᴴ)) = 0 :=
  gateTOfFf w prod1FfNe

/-- The merged frame product `R * tGateᴴ` is not a literal T gate. -/
private theorem gateTProd2 {N : ℕ} (w : Fin N) :
    gateTCount (Sum.inl (w, (qubitEulerRotation (-Real.pi / 4)) * tGateᴴ)) = 0 :=
  gateTOfFf w prod2FfNe

/-- Taking the adjoint of a single gate preserves its literal T-coverage. -/
private theorem gateTAdjInv {N : ℕ} (g : ReflectionGate N) :
    gateTCount (reflectionGateAdjoint g) = gateTCount g := by
  rcases g with ⟨w, U⟩ | ⟨c, t⟩
  · by_cases h1 : U = tGate
    · subst h1
      show (if tGateᴴ = tGate then 1 else if tGateᴴ = tGateAdj then 1 else 0)
          = (if tGate = tGate then 1 else if tGate = tGateAdj then 1 else 0)
      rw [tGateConj, ite_eq_right (Ne.symm tGateNeAdj), ite_eq_left rfl, ite_eq_left rfl]
    · by_cases h2 : U = tGateAdj
      · subst h2
        show (if tGateAdjᴴ = tGate then 1 else if tGateAdjᴴ = tGateAdj then 1 else 0)
            = (if tGateAdj = tGate then 1 else if tGateAdj = tGateAdj then 1 else 0)
        rw [tGateAdjConj, ite_eq_left rfl, ite_eq_right (Ne.symm tGateNeAdj), ite_eq_left rfl]
      · show (if Uᴴ = tGate then 1 else if Uᴴ = tGateAdj then 1 else 0)
            = (if U = tGate then 1 else if U = tGateAdj then 1 else 0)
        have n1 : ¬(Uᴴ = tGate) := by
          intro hh
          refine h2 ?_
          rw [← Matrix.conjTranspose_conjTranspose U, hh, tGateConj]
        have n2 : ¬(Uᴴ = tGateAdj) := by
          intro hh
          refine h1 ?_
          rw [← Matrix.conjTranspose_conjTranspose U, hh, tGateAdjConj]
        rw [ite_eq_right n1, ite_eq_right n2, ite_eq_right h1, ite_eq_right h2]
  · rfl

/-- A two-qubit gate contributes nothing to the literal T-count. -/
private theorem gateTInr {N : ℕ} (p : Fin N × Fin N) : gateTCount (Sum.inr p) = 0 := rfl

/-- The word adjoint of a cons word is the adjoint tail appended with the adjoint
head gate. -/
private theorem reflAdjCons {N : ℕ} (g : ReflectionGate N) (gs : List (ReflectionGate N)) :
    reflectionAdjoint (g :: gs) = reflectionAdjoint gs ++ [reflectionGateAdjoint g] := by
  simp [reflectionAdjoint]

/-- Taking the adjoint of a word preserves its one-qubit count. -/
theorem oneQOfAdjoint {N : ℕ} (gs : List (ReflectionGate N)) :
    oneQOf (reflectionAdjoint gs) = oneQOf gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [reflAdjCons g gs, oneQOfAppend, ih, oneQOfCons g gs]
    cases g <;> rfl

/-- Taking the adjoint of a word preserves its two-qubit count. -/
theorem twoQOfAdjoint {N : ℕ} (gs : List (ReflectionGate N)) :
    twoQOf (reflectionAdjoint gs) = twoQOf gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [reflAdjCons g gs, twoQOfAppend, ih, twoQOfCons g gs]
    cases g <;> rfl

/-- Taking the adjoint of a word preserves its literal T-count. -/
theorem tGateOfAdjoint {N : ℕ} (gs : List (ReflectionGate N)) :
    tGateOf (reflectionAdjoint gs) = tGateOf gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [reflAdjCons g gs, tGateOfAppend, ih, tGateOfCons g gs]
    have h2 : tGateOf [reflectionGateAdjoint g] = gateTCount (reflectionGateAdjoint g) := by
      simp only [tGateOf, zero_add]
    have h3 : gateTCount (reflectionGateAdjoint g) = gateTCount g := gateTAdjInv g
    have h4 : tGateOf [g] = gateTCount g := by simp only [tGateOf, zero_add]
    omega

/-! ## Per-segment shapes -/

/-- The relative Toffoli middle word has two one-qubit gates. -/
private theorem oneQRelMid {N : ℕ} (a b t : Fin N) :
    oneQOf (sourceRelativeMiddle a b t) = 2 := by
  simp only [sourceRelativeMiddle, oneQOf]

/-- The relative Toffoli middle word has three two-qubit gates. -/
private theorem twoQRelMid {N : ℕ} (a b t : Fin N) :
    twoQOf (sourceRelativeMiddle a b t) = 3 := by
  simp only [sourceRelativeMiddle, twoQOf]

/-- The relative Toffoli middle word has no literal T gate. -/
private theorem tGRelMid {N : ℕ} (a b t : Fin N) :
    tGateOf (sourceRelativeMiddle a b t) = 0 := by
  simp only [sourceRelativeMiddle, tGateOf, gateTInr]
  rw [gateTEul, gateTEulAdj]

/-- The relative Toffoli gadget word has four one-qubit gates. -/
private theorem oneQRelSteps {N : ℕ} (a b t : Fin N) :
    oneQOf (sourceRelativeToffoliSteps a b t) = 4 := by
  simp only [sourceRelativeToffoliSteps, oneQOf]

/-- The relative Toffoli gadget word has three two-qubit gates. -/
private theorem twoQRelSteps {N : ℕ} (a b t : Fin N) :
    twoQOf (sourceRelativeToffoliSteps a b t) = 3 := by
  simp only [sourceRelativeToffoliSteps, twoQOf]

/-- The relative Toffoli gadget word has no literal T gate. -/
private theorem tGRelSteps {N : ℕ} (a b t : Fin N) :
    tGateOf (sourceRelativeToffoliSteps a b t) = 0 := by
  simp only [sourceRelativeToffoliSteps, tGateOf, gateTInr]
  rw [gateTEul, gateTEulAdj]

/-- The exact Toffoli middle word has six one-qubit gates. -/
private theorem oneQToffMid {N : ℕ} (a b t : Fin N) :
    oneQOf (sourceToffoliMiddle a b t) = 6 := by
  simp only [sourceToffoliMiddle, oneQOf]

/-- The exact Toffoli middle word has six two-qubit gates. -/
private theorem twoQToffMid {N : ℕ} (a b t : Fin N) :
    twoQOf (sourceToffoliMiddle a b t) = 6 := by
  simp only [sourceToffoliMiddle, twoQOf]

/-- The exact Toffoli middle word has six literal T/T† gates. -/
private theorem tGToffMid {N : ℕ} (a b t : Fin N) :
    tGateOf (sourceToffoliMiddle a b t) = 6 := by
  simp only [sourceToffoliMiddle, tGateOf, gateTInr]
  rw [gateTAdj, gateTTG, gateTTG, gateTAdj]

/-- For `r ≥ 1`, the compressed prefix ladder has `6 * r - 2` one-qubit gates, `6 * r - 3`
two-qubit gates, and no literal T gate. -/
private theorem cntPrefix {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) (hr : 1 ≤ r) :
    oneQOf (sourcePrefixCompressed c w r) = 6 * r - 2 ∧
    twoQOf (sourcePrefixCompressed c w r) = 6 * r - 3 ∧
    tGateOf (sourcePrefixCompressed c w r) = 0 := by
  induction r using Nat.twoStepInduction with
  | zero => omega
  | one =>
    simp only [sourcePrefixCompressed, sourceRelativeToffoliSteps, oneQOf, twoQOf, tGateOf,
      gateTInr]
    rw [gateTEul, gateTEulAdj]
    exact ⟨trivial, trivial, rfl⟩
  | more r _ ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (by omega)
    simp only [sourcePrefixCompressed, oneQOfAppend, twoQOfAppend, tGateOfAppend,
      oneQRelMid, twoQRelMid, tGRelMid, oneQOf, twoQOf, tGateOf, gateTEul, gateTEulAdj,
      ih1, ih2, ih3]
    exact ⟨by omega, by omega, trivial⟩

/-- For `r ≥ 1`, the relative borrowed core has `12 * r` one-qubit gates, `12 * r`
two-qubit gates, and no literal T gate. -/
private theorem cntRelCore {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ) (hr : 1 ≤ r) :
    oneQOf (sourceBorrowedRelativeCore c w s r) = 12 * r ∧
    twoQOf (sourceBorrowedRelativeCore c w s r) = 12 * r ∧
    tGateOf (sourceBorrowedRelativeCore c w s r) = 0 := by
  obtain ⟨h1, h2, h3⟩ := cntPrefix c w r hr
  simp only [sourceBorrowedRelativeCore, oneQOfAppend, twoQOfAppend, tGateOfAppend,
    oneQRelMid, twoQRelMid, tGRelMid, h1, h2, h3]
  exact ⟨by omega, by omega, trivial⟩

/-- For `r ≥ 1`, the exact borrowed core has `12 * r + 8` one-qubit gates, `12 * r + 6`
two-qubit gates, and twelve literal T/T† gates. -/
private theorem cntExactCore {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) (hr : 1 ≤ r) :
    oneQOf (sourceBorrowedExactCore c w t r) = 12 * r + 8 ∧
    twoQOf (sourceBorrowedExactCore c w t r) = 12 * r + 6 ∧
    tGateOf (sourceBorrowedExactCore c w t r) = 12 := by
  obtain ⟨h1, h2, h3⟩ := cntPrefix c w r hr
  simp only [sourceBorrowedExactCore, oneQOfAppend, twoQOfAppend, tGateOfAppend,
    oneQOfAdjoint, twoQOfAdjoint, tGateOfAdjoint, oneQToffMid, twoQToffMid, tGToffMid,
    h1, h2, h3]
  exact ⟨by omega, by omega, trivial⟩

/-- The packed commutator of the Corollary 7.4 frame doubles both component counts,
adds seven one-qubit frame gates, and contributes one literal T† gate (the frame
canceler `tGateᴴ`). -/
private theorem cntPacked {N : ℕ} (s t : Fin N) (as bs : List (ReflectionGate N)) :
    oneQOf (sourcePackedCommutator s t (qubitEulerRotation (-Real.pi / 4)) tGate as bs)
      = 2 * (oneQOf as + oneQOf bs) + 7 ∧
    twoQOf (sourcePackedCommutator s t (qubitEulerRotation (-Real.pi / 4)) tGate as bs)
      = 2 * (twoQOf as + twoQOf bs) ∧
    tGateOf (sourcePackedCommutator s t (qubitEulerRotation (-Real.pi / 4)) tGate as bs)
      = 2 * (tGateOf as + tGateOf bs) + 1 := by
  simp only [sourcePackedCommutator, oneQOfAppend, twoQOfAppend, tGateOfAppend,
    oneQOfAdjoint, twoQOfAdjoint, tGateOfAdjoint, oneQOf, twoQOf, tGateOf,
    gateTHad, gateTEul, gateTProd1, gateTProd2, gateTTAdj]
  omega

/-! ## Counts of the produced Corollary 7.4 word -/

/-- For `m ≥ 5`, the compiled Corollary 7.4 word has exactly `24 * m - 49` one-qubit
elementary gates. -/
theorem cor74OneQ {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (hm : 5 ≤ m) :
    oneQOf (cor74Word m c s t) = 24 * m - 49 := by
  rw [cor74Word_eq]
  obtain ⟨h1, h2, h3⟩ := cntRelCore c (fun j => c ((m + 1) / 2 + j)) s ((m + 1) / 2 - 2)
    (by omega)
  obtain ⟨h4, h5, h6⟩ :=
    cntExactCore (fun i => if i < m / 2 then c ((m + 1) / 2 + i) else s) c t (m / 2 - 1)
      (by omega)
  obtain ⟨p1, _, _⟩ := cntPacked s t _ _
  rw [p1, h1, h4]
  omega

/-- For `m ≥ 5`, the compiled Corollary 7.4 word has exactly `24 * m - 60` two-qubit
elementary gates. -/
theorem cor74TwoQ {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (hm : 5 ≤ m) :
    twoQOf (cor74Word m c s t) = 24 * m - 60 := by
  rw [cor74Word_eq]
  obtain ⟨h1, h2, h3⟩ := cntRelCore c (fun j => c ((m + 1) / 2 + j)) s ((m + 1) / 2 - 2)
    (by omega)
  obtain ⟨h4, h5, h6⟩ :=
    cntExactCore (fun i => if i < m / 2 then c ((m + 1) / 2 + i) else s) c t (m / 2 - 1)
      (by omega)
  obtain ⟨_, p2, _⟩ := cntPacked s t _ _
  rw [p2, h2, h5]
  omega

/-- For `m ≥ 5`, the compiled Corollary 7.4 word has exactly twenty-five literal T/T†
gates: twenty-four from its four exact Toffoli middle words plus the single frame
canceler `tGateᴴ`. The count is independent of the number of controls. -/
theorem cor74TGate {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (hm : 5 ≤ m) :
    tGateOf (cor74Word m c s t) = 25 := by
  rw [cor74Word_eq]
  obtain ⟨h1, h2, h3⟩ := cntRelCore c (fun j => c ((m + 1) / 2 + j)) s ((m + 1) / 2 - 2)
    (by omega)
  obtain ⟨h4, h5, h6⟩ :=
    cntExactCore (fun i => if i < m / 2 then c ((m + 1) / 2 + i) else s) c t (m / 2 - 1)
      (by omega)
  obtain ⟨_, _, p3⟩ := cntPacked s t _ _
  rw [p3, h3, h6]

/-- Self-consistency: the one- and two-qubit counts of the produced word sum to the
public exact word length `48 * m - 109`. -/
theorem cor74LenSum {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (hm : 5 ≤ m) :
    oneQOf (cor74Word m c s t) + twoQOf (cor74Word m c s t) = 48 * m - 109 := by
  rw [oneTwoSum, cor74Word_length m c s t hm]

/-! ## Cost-profile integration -/

/-- The measured cost profile of a compiled Corollary 7.4 network: measured zeros for
oracle queries, the Toffoli block census for macro gates, measured elementary and
literal-T counts read off the produced word, and unmodeled depth and width. -/
noncomputable def cor74Profile {N : ℕ} (net : Cor74Net N) : CostProfile where
  queries := some 0
  macroGates := some (toffCount net.blocks)
  oneQ := some (oneQOf net.word)
  twoQ := some (twoQOf net.word)
  tCount := some (tGateOf net.word)
  depth := none
  width := none

/-- The source budget of an `n`-wire Corollary 7.4 claim: zero oracle queries and at
most `8 * (n - 5)` Toffoli blocks; elementary-gate, T-count, depth, and width slots
are left unconstrained. -/
def cor74Budget (n : ℕ) : CostProfile where
  queries := some 0
  macroGates := some (8 * (n - 5))
  oneQ := none
  twoQ := none
  tCount := none
  depth := none
  width := none

/-- The measured elementary total of a compiled Corollary 7.4 network is at most
`48 * (m + 2) - 204`, the paper's basic-operation bound restated on the produced
word. The seven per-field slots of `BudgetLe` compare individual counts, while
this bound concerns the sum of the one-qubit and two-qubit gate counts. -/
theorem cor74BasicBound {N : ℕ} (net : Cor74Net N) :
    oneQOf net.word + twoQOf net.word ≤ 48 * (net.m + 2) - 204 := by
  have h5 := net.hm
  show oneQOf (cor74Word net.m net.ctl net.spc net.tgt)
      + twoQOf (cor74Word net.m net.ctl net.spc net.tgt) ≤ _
  rw [cor74OneQ net.m net.ctl net.spc net.tgt net.hm,
    cor74TwoQ net.m net.ctl net.spc net.tgt net.hm]
  omega

/-- The seven-wire instance measures sixteen Toffoli macro blocks. -/
theorem cor7Macro : (cor74Profile cor7Net).macroGates = some 16 := by
  simp only [cor74Profile, Cor74Net.blocks]
  show some (toffCount (cor74Blocks 5 cor7Ctl cor7Spc cor7Tgt)) = some 16
  rw [(cor74Blocks_census 5 cor7Ctl cor7Spc cor7Tgt (by omega)).2.2]

/-- The seven-wire Corollary 7.4 network together with its measured profile meets the
seven-wire source budget: a compilation cost certificate whose conformance is read
off the product, never assumed. -/
noncomputable def cor7Cert : CompileCert (α := Cor74Net 7) cor74Profile (cor74Budget 7) where
  out := cor7Net
  fits := budgetLeIntro
    ⟨0, rfl, Nat.le_refl 0⟩
    ⟨16, cor7Macro, by norm_num⟩
    trivial trivial trivial trivial trivial

end Qatlib.Concepts.GateKit
