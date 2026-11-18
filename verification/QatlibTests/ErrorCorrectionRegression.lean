/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CssCodeCS96.Construction.Repetition
public import Qatlib.Papers.CssCodeCS96.Construction.HammingSteane
public import Qatlib.Papers.PerfectQEC96.FiveQubit
public import Qatlib.Papers.Armillary26.Instances.Routed

@[expose] public section

/-!
# Error-correction component and consumer regression

These examples consume the actual classical, CSS, signed-stabilizer, and
Armillary interfaces. They cover parameter families, real decoders, the
five-qubit recovery endpoint, the static/ordered separation, and small K/chi
and universal-parameter consumers.
-/

set_option autoImplicit false

namespace QatlibTests.ErrorCorrectionRegression

open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.CodeCert.PermBlocks
open Qatlib.Papers.CssCodeCS96.Construction
open Qatlib.Papers.PerfectQEC96
open Qatlib.Papers.Armillary26.Pairing
open Qatlib.Papers.Armillary26.Instances
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open scoped Matrix

/-- The length-six repetition consumer has exact parameters `[6,1,6]`. -/
example : Fintype.card (Fin 6) = 6 ∧ codeDim (repCode 5) = 1 ∧ minDist (repCode 5) = 6 := by
  have h := rep_params 5
  norm_num at h ⊢
  exact h

/-- The length-six repetition decoder corrects every single-bit error. -/
example : BoundDecode (repCode 5) (repDecode 5) 1 := rep_correct 5 1 (by omega)

/-- The m=3 Hamming consumer has the source `[7,4,3]` parameters. -/
example : Fintype.card {v : Fin 3 → ZMod 2 // v ≠ 0} = 7 ∧
    codeDim (hamCode 3) = 4 ∧ minDist (hamCode 3) = 3 := by
  have h := hamParams 3 (by omega)
  norm_num at h ⊢
  exact h

/-- The actual m=3 Hamming syndrome decoder corrects every single-bit error. -/
example : BoundDecode (hamCode 3) (hamDecode 3) 1 := hamSyn 3

/-- The general m=3 Hamming representation is exactly the canonical Steane CSS data. -/
example : toCss ham3Code ham3_self = steaneData := ham3_to_steane

/-- The explicit seven-column transport is a full bijection, as proved by
`Qatlib.Papers.CssCodeCS96.Construction.ham_col_bij`. -/
example : Function.Bijective hamToSteane := ham_col_bij

/-- The inverse coordinate transport preserves every Hamming syndrome through
`Qatlib.Papers.CssCodeCS96.Construction.ham_syn_trans`. -/
example (v : Fin 7 → ZMod 2) : hamCheck 3 *ᵥ hamVector v = steaneH *ᵥ v :=
  ham_syn_trans v

/-- All classical parameters survive the column bijection in
`Qatlib.Papers.CssCodeCS96.Construction.ham3_params`. -/
example : Fintype.card (Fin 7) = 7 ∧ codeDim ham3Code = 4 ∧
    minDist ham3Code = (3 : ℕ∞) := ham3_params

/-- The transported self-orthogonal Hamming code consumes the exact CSS
parameters in `Qatlib.Papers.CssCodeCS96.Construction.ham3_css_params`. -/
example : (toCss ham3Code ham3_self).numQubits = 7 ∧
    (toCss ham3Code ham3_self).encodedQubits = 1 ∧
    cssDistance (toCss ham3Code ham3_self) = 3 := ham3_css_params

/-- The five-qubit signed stabilizer has dimension two and exact distance three. -/
example : Module.finrank ℂ (codeSpace fiveTab) = 2 ∧
    stabDist fiveGens = (3 : ℕ∞) ∧ ¬ (minusI 5 ∈ generatedSubgroup (tableauGenerators fiveTab)) :=
  five_params

/-- The perfect-code decoder returns a concrete single-site X label unchanged. -/
example : fiveCorr (tabSyn fiveTab (fiveX 0)) = fiveX 0 := five_decode (fiveX 0) (by decide)

/-- Every signed single-qubit Pauli error is recovered on every five-qubit code state. -/
example (e : PauliElem 5) (he : pauliWt e ≤ 1)
    (ψ : QState (Reg 5)) (hψ : ψ ∈ codeSpace fiveTab) :
    stabRecCh fiveTab fiveProg (outerProduct (op e *ᵥ ψ)) = outerProduct ψ :=
  five_recovers e he ψ hψ

/-- Static elimination on the same accumulated data coordinates does not imply
ordered elimination in
`Qatlib.Papers.Armillary26.Pairing.reg_static_ord`. -/
example : omegaMat (∑ t, regX t) (∑ t, regZ t) = 0 ∧ ordC regX regZ ≠ 0 :=
  reg_static_ord

/-- A realizable source route with twelve groups and one internal coordinate. -/
def tinyArm : ArmParam 1 1 where
  hp := by decide
  hq := by decide
  perm := fun _ _ => Equiv.refl _
  shift := fun _ _ _ => 0

/-- Three distinct even X groups retained from the actual source route. -/
def tinyX (x : Fin 3) : Fin 12 := ⟨2 * x.val, by omega⟩

/-- Three distinct even Z groups disjoint from the retained X groups. -/
def tinyZ (z : Fin 3) : Fin 12 := ⟨6 + 2 * z.val, by omega⟩

/-- Exchange neighboring columns; every visit-order interval has even endpoints. -/
def tinyPair (_x _z : Fin 3) (b : Fin 12) : Fin 12 :=
  if b.val % 2 = 0 then b + 1 else b - 1

/-- The three retained X groups are distinct. -/
theorem tiny_x_injective : Function.Injective tinyX := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [tinyX] at hv
  omega

/-- The three retained Z groups are distinct. -/
theorem tiny_z_injective : Function.Injective tinyZ := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [tinyZ] at hv
  omega

/-- The two retained group families are disjoint. -/
theorem tiny_groups_disjoint (x z : Fin 3) : tinyX x ≠ tinyZ z := by
  intro h
  have hv := congrArg Fin.val h
  simp only [tinyX, tinyZ] at hv
  omega

/-- The actual route satisfies the source channel, modular shift, and nontrivial
order-pairing conditions of
`Qatlib.Papers.Armillary26.Instances.ShiftPair`. -/
theorem tiny_shift_pair : ShiftPair tinyArm tinyX tinyZ tinyPair where
  involutive := by
    intro x z b
    dsimp only [tinyPair]
    fin_cases b <;> decide
  noFixed := by
    intro x z b
    dsimp only [tinyPair]
    fin_cases b <;> decide
  channel := by
    intro x z b
    exact Subsingleton.elim _ _
  shift := by
    intro x z b j
    exact Subsingleton.elim _ _
  order := by
    intro x z b
    fin_cases x <;> fin_cases z <;> fin_cases b <;> decide

/-- Visit-order weights take both values; ordered elimination is not vacuous. -/
theorem tiny_chi_nontrivial :
    chi (tinyX 0) (tinyZ 0) 0 = 1 ∧ chi (tinyX 0) (tinyZ 0) 6 = 0 := by
  decide

/-- Every retained row has a unit entry on the original twelve data coordinates. -/
theorem tiny_row_nonzero (g : Fin 3 → Fin 12) (x : Fin 3) :
    (permBlocks (K := ZMod 2) (fun a => armEff tinyArm (g a)) (x, (0, 0))) ≠ 0 := by
  intro h
  have he : armEff tinyArm (g x) 0 (0, 0) = (0, 0) := Subsingleton.elim _ _
  have hz := congrFun h (0, (0, 0))
  simp [permBlocks, he] at hz

/-- Both retained check families have nonzero rows, despite their internal
coordinate having cardinality one. -/
example (x z : Fin 3) :
    (permBlocks (K := ZMod 2) (fun a => armEff tinyArm (tinyX a)) (x, (0, 0))) ≠ 0 ∧
    (permBlocks (K := ZMod 2) (fun a => armEff tinyArm (tinyZ a)) (z, (0, 0))) ≠ 0 :=
  ⟨tiny_row_nonzero tinyX x, tiny_row_nonzero tinyZ z⟩

/-- The same realizable, nondegenerate order consumer closes the entire
`Qatlib.Papers.Armillary26.Instances.route_shift_pair` chain. -/
example :
    (routeCode tinyArm tinyX tinyZ tinyPair tiny_shift_pair).hX *
      (routeCode tinyArm tinyX tinyZ tinyPair tiny_shift_pair).hZᵀ = 0 ∧
    10 ≤ (routeCode tinyArm tinyX tinyZ tinyPair tiny_shift_pair).encodedQubits ∧
    (1 / 2 : ℚ) <
      ((routeCode tinyArm tinyX tinyZ tinyPair tiny_shift_pair).encodedQubits : ℚ) / 12 ∧
    ordC (steps tinyX (fun x => armEff tinyArm (tinyX x)))
      (steps tinyZ (fun z => armEff tinyArm (tinyZ z))) = 0 := by
  simpa using route_shift_pair tinyArm tinyX tinyZ tinyPair tiny_shift_pair

/-- The universal retained construction consumes a tiny fiber and identity permutations. -/
example : 6 * Fintype.card (Fin 1) + 4
      ≤ (retainedCode (fun _ : Fin 3 => fun _ : Fin 12 => Equiv.refl (Fin 1))
        (fun _ : Fin 3 => fun _ : Fin 12 => Equiv.refl (Fin 1))
        (pairCompat (m := 6) (fun _ : Fin 3 => fun _ : Fin 12 => Equiv.refl (Fin 1))
          (fun _ : Fin 3 => fun _ : Fin 12 => Equiv.refl (Fin 1)) (by
            intro a a' i
            rfl))).encodedQubits := by
  apply encoded_lower (ι := Fin 1) 0

/-- The generic rank bound also consumes the tiny identity-fiber instance. -/
example : Matrix.rank
      (permBlocks (fun _ : Fin 3 => fun _ : Fin 12 => Equiv.refl (Fin 1)) :
        Matrix (Fin 3 × Fin 1) (Fin 12 × Fin 1) (ZMod 2)) ≤ 3 * Fintype.card (Fin 1) - 2 := by
  apply rankBound (P := Fin 1) 0

end QatlibTests.ErrorCorrectionRegression
