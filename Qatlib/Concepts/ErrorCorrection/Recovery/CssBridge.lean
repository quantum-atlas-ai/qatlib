/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.Stabilizer
public import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli
import Qatlib.Concepts.WalshMoment.Forrelation.BooleanHadamardPhase
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Abel

@[expose] public section

/-!
# CSS errors in the signed stabilizer recovery framework

The CSS computational basis uses vectors over `ZMod 2`, while signed Pauli
operators use Boolean registers. The explicit equivalence
`Qatlib.Concepts.PauliClifford.PauliAlgebra.regVecEquiv` transports the actual
CSS ordered X-times-Z product to a signed Pauli product, including its phase;
Z acts first on column states. Joint
support weight is preserved, and the transported error consumes
`Qatlib.Concepts.ErrorCorrection.Recovery.stabRecCh`.

This is an operator, weight, and fixed-error recovery bridge. It does not
identify two complete recovery channels or claim arbitrary-noise recovery.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open scoped Matrix

/-- CSS signs agree with the additive Boolean character at the same binary dot
product. -/
theorem css_phase_character {n : ℕ} (z a : BooleanVec n) :
    phaseOfBit (bitDot z a) = booleanCharacter z a := by
  change phaseOfBit (booleanDot z a) = booleanCharacter z a
  rw [booleanCharacter_apply]
  rcases StabilizerDesign.zmod2_eq_zero_or_one (booleanDot z a) with h | h <;>
    simp [h]

/-- Reindexing CSS X by the register/vector equivalence gives the signed
translation operator. -/
theorem css_x_reindex {n : ℕ} (x : BooleanVec n) :
    (cssPauliX x).submatrix regToVec regToVec = op (translationRow x).decode := by
  rw [translationRow_op]
  ext r s
  change (if regToVec r = regToVec s + x then (1 : ℂ) else 0) =
    if s = regXor r (vecToReg x) then 1 else 0
  have hxx : x + x = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (x i)
  have hc : (regToVec r = regToVec s + x) ↔ s = regXor r (vecToReg x) := by
    constructor
    · intro h
      apply regVecEquiv.injective
      change regToVec s = regToVec (regXor r (vecToReg x))
      rw [regToVec_regXor_vecToReg]
      calc
        regToVec s = regToVec s + (x + x) := by rw [hxx, add_zero]
        _ = x + (regToVec s + x) := by abel
        _ = x + regToVec r := by rw [h]
    · intro h
      rw [h, regToVec_regXor_vecToReg]
      calc
        regToVec r = regToVec r + (x + x) := by rw [hxx, add_zero]
        _ = x + regToVec r + x := by abel
  simp only [hc]

/-- Reindexing CSS Z gives the phase-zero signed diagonal operator. -/
theorem css_z_reindex {n : ℕ} (z : BooleanVec n) :
    (cssPauliZ z).submatrix regToVec regToVec = op (rawDiagonalRow z 0).decode := by
  rw [rawDiagonalRow_op]
  ext r s
  by_cases h : r = s
  · subst s
    simp [cssPauliZ, css_phase_character]
  · have hv : regToVec r ≠ regToVec s := fun he => h (regVecEquiv.injective he)
    simp [cssPauliZ, h, hv]

/-- The signed Pauli representing the actual CSS X-times-Z product, with Z
acting first on column states. The product retains the phase required when
the supports overlap. -/
def cssSigned {n : ℕ} (x z : BooleanVec n) : PauliElem n :=
  (translationRow x).decode.mul (rawDiagonalRow z 0).decode

/-- The transported CSS operator equals the actual signed Pauli operator,
without discarding a phase for overlapping X and Z supports. -/
theorem css_signed_operator {n : ℕ} (x z : BooleanVec n) :
    (cssPauliX x * cssPauliZ z).submatrix regToVec regToVec = op (cssSigned x z) := by
  rw [cssSigned, op_mul]
  rw [← css_x_reindex, ← css_z_reindex]
  exact (Matrix.submatrix_mul_equiv (cssPauliX x) (cssPauliZ z)
    regToVec regVecEquiv regToVec).symm

/-- Computational-basis transport intertwines every matrix action, so CSS
fixed-check states can be used as Boolean-register states. -/
theorem css_state_transport {n : ℕ} (M : Matrix (BooleanVec n) (BooleanVec n) ℂ)
    (f : BooleanVec n → ℂ) :
    M.submatrix regToVec regToVec *ᵥ stateOfFn f = stateOfFn (M *ᵥ f) := by
  have hcomp : stateOfFn f ∘ regVecEquiv.symm = f := by
    funext v
    change f (regToVec (regVecEquiv.symm v)) = f v
    exact congrArg f (regVecEquiv.apply_symm_apply v)
  have he : (regVecEquiv : Reg n → BooleanVec n) = regToVec := rfl
  have hs := Matrix.submatrix_mulVec_equiv M (stateOfFn f) regToVec regVecEquiv
  rw [hcomp, he] at hs
  exact hs

/-- The signed CSS product has precisely the input binary X and Z labels. -/
theorem css_signed_label {n : ℕ} (x z : BooleanVec n) :
    symplecticVec (cssSigned x z).word = (x, z) := by
  have hx : symplecticVec (translationRow x).decode.word = (x, 0) :=
    symplecticVec_pauliRow x 0 0
  have hz : symplecticVec (rawDiagonalRow z 0).decode.word = (0, z) :=
    symplecticVec_pauliRow 0 z 0
  rw [cssSigned, pauliElem_mul_word, symplecticVec_mul, hx, hz]
  simp

/-- CSS joint-support weight is the same symplectic weight, with Y counted once. -/
theorem css_symplectic_weight {n : ℕ} (x z : BooleanVec n) :
    pauliWeight x z = sympWt (x, z) := rfl

/-- The actual signed CSS product preserves the CSS error weight. -/
theorem css_signed_weight {n : ℕ} (x z : BooleanVec n) :
    pauliWt (cssSigned x z) = pauliWeight x z := by
  rw [pauliWt_symp]
  change sympWt (symplecticVec (cssSigned x z).word) = pauliWeight x z
  rw [css_signed_label]
  rfl

/-- The CSS product and the phase-zero label produce equal corrupted density
operators after the explicit computational-basis reindexing. -/
theorem css_label_density {n : ℕ} (x z : BooleanVec n) (ψ : QState (Reg n)) :
    outerProduct ((cssPauliX x * cssPauliZ z).submatrix regToVec regToVec *ᵥ ψ) =
      outerProduct (op (labelPauli (x, z)) *ᵥ ψ) := by
  rw [css_signed_operator]
  apply out_same
  rw [css_signed_label, label_vec]

/-- A CSS-form error consumes the general signed-stabilizer recovery theorem
under the same actual decoder residual condition. -/
theorem css_stab_recovers {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (x z : BooleanVec n)
    (hres : stabRes prog (x, z) ∈ sympSpan (fun a => (t a).decode))
    (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    stabRecCh t prog
      (outerProduct ((cssPauliX x * cssPauliZ z).submatrix regToVec regToVec *ᵥ ψ)) =
      outerProduct ψ := by
  rw [css_label_density]
  exact stab_recovers t ht hind prog (x, z) hres ψ hψ

/-- A bounded CSS error uses a bounded signed-stabilizer decoder through the
exact weight and operator bridges. -/
theorem css_stab_corrects {n k : ℕ} (t : Tableau n k) (ht : ConsistentTableau t)
    (hind : IndependentGenerators (tableauGenerators t)) (prog : StabProg t)
    (r : ℕ) (hp : StabCorrects prog r) (x z : BooleanVec n)
    (hw : pauliWeight x z ≤ r) (ψ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) :
    stabRecCh t prog
      (outerProduct ((cssPauliX x * cssPauliZ z).submatrix regToVec regToVec *ᵥ ψ)) =
      outerProduct ψ :=
  css_stab_recovers t ht hind prog x z (hp (x, z) hw) ψ hψ

end Qatlib.Concepts.ErrorCorrection.Recovery
