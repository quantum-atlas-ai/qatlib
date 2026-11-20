/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ErrorCorrection.Recovery.CssBridge
public import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section

/-!
# CSS recovery as signed stabilizer recovery

The signed tableau follows the check order used by the CSS syndrome projector. Reindexing
the computational basis and the syndrome outcomes identifies the two projectors and their
decoders. The choice of phase for a correction disappears in its conjugation action.
-/

namespace Qatlib.Concepts.ErrorCorrection.Recovery

set_option autoImplicit false

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix

variable {n : ℕ} {κX κZ : Type} [Fintype κX] [Fintype κZ] [DecidableEq κX] [DecidableEq κZ]

/-- The check list used to form the CSS projector. -/
noncomputable def checkOrder (κX κZ : Type) [Fintype κX] [Fintype κZ] : List (κX ⊕ κZ) :=
  Finset.univ.toList

/-- An index in the ordered tableau corresponds to one of the original CSS checks. -/
noncomputable def checkAt (κX κZ : Type) [Fintype κX] [Fintype κZ]
    [DecidableEq κX] [DecidableEq κZ] : Fin (checkOrder κX κZ).length ≃ κX ⊕ κZ :=
  List.Nodup.getEquivOfForallMemList (checkOrder κX κZ) (Finset.nodup_toList _) (by
    intro i
    simp [checkOrder])

/-- The check equivalence lists the checks in the exact order of the CSS product. -/
private theorem list_checkAt (κX κZ : Type) [Fintype κX] [Fintype κZ]
    [DecidableEq κX] [DecidableEq κZ] :
    (List.finRange (checkOrder κX κZ).length).map (checkAt κX κZ) = checkOrder κX κZ :=
  List.map_get_finRange _

/-- Reindex operators from the CSS vector basis to the signed Boolean-register basis. -/
noncomputable abbrev toRegisters (n : ℕ) :
    Matrix (BooleanVec n) (BooleanVec n) ℂ ≃ₐ[ℂ] Matrix (Reg n) (Reg n) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ regVecEquiv.symm

/-- The basis transport preserves the conjugate transpose. -/
private theorem registers_star (A : Matrix (BooleanVec n) (BooleanVec n) ℂ) :
    (toRegisters n A)ᴴ = toRegisters n Aᴴ :=
  Matrix.conjTranspose_submatrix A regToVec regToVec

/-- Represent a CSS check by its phase-zero X or Z row. -/
def cssRow (c : CssData (Fin n) κX κZ) (k : κX ⊕ κZ) : Row n :=
  Sum.elim (fun i => translationRow (c.hX i)) (fun j => rawDiagonalRow (c.hZ j) 0) k

/-- The signed tableau for the CSS checks in product order. -/
noncomputable def cssTable (c : CssData (Fin n) κX κZ) :
    Tableau n (checkOrder κX κZ).length :=
  fun a => cssRow c (checkAt κX κZ a)

/-- Equivalence between CSS syndrome pairs and ordered tableau syndromes. -/
noncomputable def cssSynEquiv (κX κZ : Type) [Fintype κX] [Fintype κZ]
    [DecidableEq κX] [DecidableEq κZ] :
    ((κX → ZMod 2) × (κZ → ZMod 2)) ≃ (Fin (checkOrder κX κZ).length → ZMod 2) :=
  (Equiv.sumArrowEquivProdArrow κX κZ (ZMod 2)).symm.trans
    (Equiv.arrowCongr (checkAt κX κZ).symm (Equiv.refl _))

/-- Applying the syndrome equivalence selects the corresponding original check bit. -/
theorem cssSyn_apply (η : (κX → ZMod 2) × (κZ → ZMod 2))
    (a : Fin (checkOrder κX κZ).length) :
    cssSynEquiv κX κZ η a = Sum.elim η.1 η.2 (checkAt κX κZ a) := rfl

/-- The signed tableau and the CSS matrices compute exactly the same syndrome. -/
theorem cssSyn_eq (c : CssData (Fin n) κX κZ) (e : PauliLabel (Fin n)) :
    tabSyn (cssTable c) e = cssSynEquiv κX κZ (pauliSyndrome c e) := by
  funext a
  rw [cssSyn_apply]
  change symplecticForm e (symplecticVec (cssRow c (checkAt κX κZ a)).decode.word) = _
  rcases h : checkAt κX κZ a with i | j
  · have hx : symplecticVec (translationRow (c.hX i)).decode.word = (c.hX i, 0) :=
      symplecticVec_pauliRow (c.hX i) 0 0
    simp only [cssRow, Sum.elim_inl, hx]
    simp [symplecticForm, pauliSyndrome, booleanDot, Matrix.mulVec, dotProduct, mul_comm]
  · have hz : symplecticVec (rawDiagonalRow (c.hZ j) 0).decode.word = (0, c.hZ j) :=
      symplecticVec_pauliRow 0 (c.hZ j) 0
    simp only [cssRow, Sum.elim_inr, hz]
    simp [symplecticForm, pauliSyndrome, booleanDot, Matrix.mulVec, dotProduct, mul_comm]

omit [Fintype κX] [Fintype κZ] [DecidableEq κX] [DecidableEq κZ] in
/-- Each CSS check becomes the operator of its corresponding signed row. -/
private theorem check_rebase (c : CssData (Fin n) κX κZ) (k : κX ⊕ κZ) :
    toRegisters n (cssCheck c k) = op (cssRow c k).decode := by
  cases k with
  | inl i => exact css_x_reindex (c.hX i)
  | inr j => exact css_z_reindex (c.hZ j)

/-- The recursive signed projector is a product of the half-projectors. -/
private theorem proj_prod (gs : List (PauliElem n)) :
    projectorAux gs = (gs.map fun g => (2⁻¹ : ℂ) • (1 + op g)).prod := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [projectorAux_cons, List.map_cons, List.prod_cons, Matrix.smul_mul, ih]

/-- A factor in the signed projector equals the corresponding transported CSS factor. -/
private theorem factor_rebase (c : CssData (Fin n) κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (a : Fin (checkOrder κX κZ).length) :
    toRegisters n (cssCheckProjector (cssCheck c (checkAt κX κZ a))
      (Sum.elim η.1 η.2 (checkAt κX κZ a))) =
      (2⁻¹ : ℂ) • (1 + op (synGen (cssTable c) (cssSynEquiv κX κZ η) a)) := by
  rw [cssCheckProjector, map_smul, map_add, map_one, map_smul, check_rebase,
    op_synGen, cssSyn_apply]
  rcases StabilizerDesign.zmod2_eq_zero_or_one (Sum.elim η.1 η.2 (checkAt κX κZ a)) with h | h
  · simp [h, cssTable]
  · simp [h, cssTable]

/-- The CSS joint projector transports to the signed-tableau joint projector. -/
theorem cssProj_eq (c : CssData (Fin n) κX κZ) (η : (κX → ZMod 2) × (κZ → ZMod 2)) :
    toRegisters n (cssSyndromeProjector c η) =
      synProj (cssTable c) (cssSynEquiv κX κZ η) := by
  rw [synProj, stabilizerProjector, proj_prod, synGens, List.map_map,
    cssSyndromeProjector, map_list_prod, List.map_map]
  change ((checkOrder κX κZ).map _).prod = _
  conv_lhs => rw [← list_checkAt κX κZ, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro a _
  exact factor_rebase c η a

/-- Conjugation by a signed Pauli is independent of its global phase. -/
private theorem phase_conj (p : PauliElem n) (A : Matrix (Reg n) (Reg n) ℂ) :
    op p * A * (op p)ᴴ = pauliWordOp n p.word * A * (pauliWordOp n p.word)ᴴ := by
  simp only [op, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [star_I_pow_mul_self, one_smul]

/-- The signed program applies the CSS decoder at the corresponding syndrome outcome. -/
noncomputable def cssStabProg (c : CssData (Fin n) κX κZ) (prog : RecoveryProgram c) :
    StabProg (cssTable c) :=
  ⟨fun η => prog.corr ((cssSynEquiv κX κZ).symm η)⟩

/-- CSS recovery and signed-stabilizer recovery agree on every input operator after reindexing. -/
theorem cssRecovery_eq (c : CssData (Fin n) κX κZ) (prog : RecoveryProgram c)
    (ρ : Matrix (BooleanVec n) (BooleanVec n) ℂ) :
    toRegisters n (recoveryChannel c prog ρ) =
      stabRecCh (cssTable c) (cssStabProg c prog) (toRegisters n ρ) := by
  simp only [recoveryChannel, stabRecCh, map_sum]
  apply Fintype.sum_equiv (cssSynEquiv κX κZ)
  intro η
  let P := cssSyndromeProjector c η
  let e := prog.corr η
  let R := cssPauliX e.1 * cssPauliZ e.2
  let Q := synProj (cssTable c) (cssSynEquiv κX κZ η)
  change toRegisters n (R * (P * ρ * P) * Rᴴ) =
    op (labelPauli ((cssStabProg c prog).corr (cssSynEquiv κX κZ η))) *
      (Q * toRegisters n ρ * Qᴴ) *
      (op (labelPauli ((cssStabProg c prog).corr (cssSynEquiv κX κZ η))))ᴴ
  have hP : toRegisters n P = Q := cssProj_eq c η
  have hQ : Qᴴ = Q := by
    rw [← hP, registers_star, (cssSyndromeProjector_isHermitian c η).eq]
  have hR : toRegisters n R = op (cssSigned e.1 e.2) := css_signed_operator e.1 e.2
  have hword : (cssSigned e.1 e.2).word = (labelPauli e).word := by
    apply symplecticVec_injective
    rw [css_signed_label, label_vec]
  calc
    _ = (toRegisters n R) * ((toRegisters n P) * (toRegisters n ρ) * (toRegisters n P)) *
        (toRegisters n R)ᴴ := by simp only [map_mul, ← registers_star]
    _ = _ := by
      rw [hP, hR]
      simp only [cssStabProg, Equiv.symm_apply_apply, hQ, phase_conj, hword]
      rfl

end Qatlib.Concepts.ErrorCorrection.Recovery
