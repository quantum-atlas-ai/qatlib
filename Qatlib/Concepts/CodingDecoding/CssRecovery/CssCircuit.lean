/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CodingDecoding.CssRecovery.ParityCircuit
public import Qatlib.Concepts.ErrorCorrection.Recovery.CssBridge
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.GateVocabulary.GateVocab.GateVocabulary
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# CSS extraction by CNOTs and Hadamards

A transversal Hadamard turns the X checks into parity measurements. A second parity word
measures the Z checks. The branch of these two executed measurements equals the public CSS
syndrome projector acting on both sides of the input density matrix.
-/

namespace Qatlib.Concepts.CodingDecoding.CssRecovery

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath
open scoped Matrix

variable {n m p q : ℕ}

/-- The register Hadamard in binary CSS computational coordinates. -/
noncomputable def basisHad (n : ℕ) : Matrix (Bits n) (Bits n) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ regVecEquiv (HadamardN n)

/-- In Boolean register indices each site conjugates the diagonal Pauli into a translation. -/
private theorem regHad_z (z : Bits n) :
    HadamardN n * op (rawDiagonalRow z 0).decode * HadamardN n =
      op (translationRow z).decode := by
  have hZ : op (rawDiagonalRow z 0).decode =
      productMatrix (fun i : Fin n => P1 (letter false (vecToReg z i))) := by
    change (Complex.I ^ (0 : ZMod 4).val : ℂ) •
      pauliWordOp n ((rawDiagonalRow z 0).decode.word) = _
    rw [pauliWordOp_eq]
    simp only [show (0 : ZMod 4).val = 0 from rfl, pow_zero, one_smul, rawDiagonalRow, Row.decode]
  have hX : op (translationRow z).decode =
      productMatrix (fun i : Fin n => P1 (letter (vecToReg z i) false)) := by
    change (Complex.I ^ (0 : ZMod 4).val : ℂ) •
      pauliWordOp n ((translationRow z).decode.word) = _
    rw [pauliWordOp_eq]
    simp only [show (0 : ZMod 4).val = 0 from rfl, pow_zero, one_smul, translationRow, Row.decode]
  rw [hZ, hX]
  change productMatrix (fun _ : Fin n => Hadamard) * _ *
    productMatrix (fun _ : Fin n => Hadamard) = _
  rw [productMatrix_mul, productMatrix_mul]
  congr 1
  funext i
  cases vecToReg z i with
  | false => simp only [letter, P1_one, mul_one, hadamard_mul_self]
  | true =>
    have hz : P1 .Z = PauliZ := by
      ext a b
      cases a <;> cases b <;> simp [P1, PauliZ]
    have hx : P1 .X = PauliX := by
      ext a b
      cases a <;> cases b <;> simp [P1, PauliX, permMatrix]
    simpa only [letter, hz, hx] using hadamard_z_conjugation

/-- The CSS basis Hadamard converts a Z Pauli check into the X check on the same sites. -/
theorem basisHad_z (z : Bits n) :
    basisHad n * cssPauliZ z * basisHad n = cssPauliX z := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ (regVecEquiv (n := n)).symm
  apply T.injective
  have h (M : Matrix (Bits n) (Bits n) ℂ) : T M = M.submatrix regToVec regToVec := rfl
  have hh : T (basisHad n) = HadamardN n := by
    change T (T.symm (HadamardN n)) = _
    exact T.apply_symm_apply _
  rw [map_mul, map_mul, hh, h (cssPauliZ z), h (cssPauliX z),
    css_z_reindex, css_x_reindex, regHad_z]

/-- The CSS basis Hadamard is self-adjoint. -/
theorem basisHad_star (n : ℕ) : (basisHad n)ᴴ = basisHad n := by
  let e := regVecEquiv (n := n)
  let T := Matrix.reindexAlgEquiv ℂ ℂ e
  have hH : (HadamardN n)ᴴ = HadamardN n := by
    change (productMatrix (fun _ : Fin n => Hadamard))ᴴ = productMatrix (fun _ : Fin n => Hadamard)
    simp only [productMatrix_adjoint, hadamard_conjTranspose]
  calc
    _ = T (HadamardN n)ᴴ := Matrix.conjTranspose_reindex e e _
    _ = _ := congrArg T hH

/-- The CSS basis Hadamard squares to the identity. -/
theorem basisHad_sq (n : ℕ) : basisHad n * basisHad n = 1 := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ (regVecEquiv (n := n))
  change T (HadamardN n) * T (HadamardN n) = 1
  rw [← map_mul, ← map_one T]
  congr 1
  change productMatrix (fun _ : Fin n => Hadamard) *
    productMatrix (fun _ : Fin n => Hadamard) = _
  rw [productMatrix_mul]
  simp only [hadamard_mul_self, productMatrix_one]

/-- The Z-check effect selects exactly the indicated binary dot product. -/
private theorem zCheck_diag (z : Bits n) (b : ZMod 2) :
    cssCheckProjector (cssPauliZ z) b =
      Matrix.diagonal (fun x : Bits n => if bitDot z x = b then (1 : ℂ) else 0) := by
  rw [cssCheckProjector, cssPauliZ, ← Matrix.diagonal_smul, ← Matrix.diagonal_one,
    Matrix.diagonal_add, ← Matrix.diagonal_smul]
  apply congrArg Matrix.diagonal
  funext x
  change (2⁻¹ : ℂ) * (1 + phaseOfBit b * phaseOfBit (bitDot z x)) =
    if bitDot z x = b then 1 else 0
  rcases StabilizerDesign.zmod2_eq_zero_or_one b with hb | hb <;>
    rcases StabilizerDesign.zmod2_eq_zero_or_one (bitDot z x) with hx | hx <;>
    norm_num [hb, hx, phaseOfBit]

/-- All Z-check effects in the given order select the conjunction of their parity tests. -/
private theorem zWord_diag (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (η : Bits m) (rows : List (Fin m)) :
    (rows.map fun i => cssCheckProjector (cssPauliZ (A i)) (η i)).prod =
      Matrix.diagonal (fun x : Bits n =>
        if ∀ i ∈ rows, (A *ᵥ x) i = η i then (1 : ℂ) else 0) := by
  induction rows with
  | nil => simp [Matrix.diagonal_one]
  | cons i rows ih =>
    rw [List.map_cons, List.prod_cons, zCheck_diag, ih, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext x
    change (if (A *ᵥ x) i = η i then (1 : ℂ) else 0) *
      (if ∀ j ∈ rows, (A *ᵥ x) j = η j then 1 else 0) =
      if ∀ j ∈ i :: rows, (A *ᵥ x) j = η j then 1 else 0
    by_cases hi : (A *ᵥ x) i = η i <;>
      by_cases hs : ∀ j ∈ rows, (A *ᵥ x) j = η j <;>
      simp [hi, hs]

/-- Executing the zero-prepared parity word realizes the entire family of Z-check effects. -/
theorem parity_zChecks (gs : List (ParityGate n m)) (η : Bits m) :
    readAfter (parityOp gs) η =
      ((List.finRange m).map fun i =>
        cssCheckProjector (cssPauliZ (circuitCheck gs i)) (η i)).prod := by
  rw [parity_branch, zWord_diag]
  apply congrArg Matrix.diagonal
  funext x
  simp only [List.mem_finRange, true_implies, funext_iff]

/-- Unitary Hadamard conjugation converts the Z-check projector to its X-check counterpart. -/
private theorem basisHad_check (z : Bits n) (b : ZMod 2) :
    basisHad n * cssCheckProjector (cssPauliZ z) b * basisHad n =
      cssCheckProjector (cssPauliX z) b := by
  simp only [cssCheckProjector, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_one,
    basisHad_sq, basisHad_z]

/-- Hadamard conjugation distributes over a list of operator factors. -/
private theorem basisHad_prod (L : List (Matrix (Bits n) (Bits n) ℂ)) :
    basisHad n * L.prod * basisHad n =
      (L.map fun M => basisHad n * M * basisHad n).prod := by
  induction L with
  | nil => simp [basisHad_sq]
  | cons M L ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    simp only [Matrix.mul_assoc]
    rw [show basisHad n * (basisHad n * (L.prod * basisHad n)) =
       L.prod * basisHad n by rw [← Matrix.mul_assoc, basisHad_sq, one_mul]]

/-- The ordered Z and X effects agree with the public product over all checks. -/
private theorem cssProd_order (c : CssData (Fin n) (Fin p) (Fin q))
    (η : Bits p × Bits q) :
    cssSyndromeProjector c η =
      (((List.finRange q).map Sum.inr ++ (List.finRange p).map Sum.inl).map
        fun k => cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k)).prod := by
  let checks : List (Fin p ⊕ Fin q) :=
    (List.finRange q).map Sum.inr ++ (List.finRange p).map Sum.inl
  let proj := fun k : Fin p ⊕ Fin q => cssCheckProjector (cssCheck c k) (Sum.elim η.1 η.2 k)
  have hperm : (Finset.univ : Finset (Fin p ⊕ Fin q)).toList.Perm checks := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _)
    · change ((List.finRange q).map Sum.inr ++ (List.finRange p).map Sum.inl :
        List (Fin p ⊕ Fin q)).Nodup
      rw [List.nodup_append]
      refine ⟨(List.nodup_finRange _).map Sum.inr_injective,
        (List.nodup_finRange _).map Sum.inl_injective, ?_⟩
      intro a ha b hb he
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hb
      cases he
    · ext k
      cases k <;> simp [checks, List.mem_map]
  change ((Finset.univ.toList.map proj).prod) = (checks.map proj).prod
  apply (hperm.map proj).prod_eq'
  rw [List.pairwise_map]
  exact List.pairwise_of_forall_mem_list (fun k _ k' _ => cssCheckProjector_commute c k k' _ _)

/-- The full syndrome operator is the actual Z readout after the Hadamard-rotated X readout. -/
theorem css_readout (c : CssData (Fin n) (Fin p) (Fin q))
    (xs : List (ParityGate n p)) (zs : List (ParityGate n q))
    (hx : circuitCheck xs = c.hX) (hz : circuitCheck zs = c.hZ) (η : Bits p × Bits q) :
    readAfter (parityOp zs) η.2 *
      (basisHad n * readAfter (parityOp xs) η.1 * basisHad n) = cssSyndromeProjector c η := by
  rw [parity_zChecks, parity_zChecks, hx, hz, basisHad_prod, cssProd_order]
  simp only [List.map_append, List.prod_append, List.map_map, Function.comp_def, basisHad_check,
    cssCheck, Sum.elim_inl, Sum.elim_inr]

/-- The data Hadamard gate indexed by the finite instrument interface. -/
noncomputable def indexedHad (n : ℕ) : Operator (Fintype.card (Bits n)) :=
  Matrix.reindexAlgEquiv ℂ ℂ (dataIndex n) (basisHad n)

/-- The indexed Hadamard can be used as an instrument gate. -/
theorem indexedHad_unitary (n : ℕ) :
    indexedHad n ∈ Matrix.unitaryGroup (Fin (Fintype.card (Bits n))) ℂ := by
  apply (relabelGate_mem_unitaryGroup (dataIndex n) (basisHad n)).mpr
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, basisHad_star, basisHad_sq]

/-- Apply Hadamard, measure the X word, undo Hadamard, and measure the Z word. -/
private noncomputable def rawExtract (xs : List (ParityGate n p)) (zs : List (ParityGate n q)) :
    Instrument ((Fin 1 × Bits p) × Fin 1 × Bits q)
      (Fintype.card (Bits n)) (Fintype.card (Bits n)) :=
  let H := unitaryInstrument (indexedHad n) (indexedHad_unitary n)
  (H.seq (parityInstr xs)).seq (H.seq (parityInstr zs))

/-- In instrument basis, each actual branch conjugates by the public joint CSS projector. -/
private theorem raw_extract (c : CssData (Fin n) (Fin p) (Fin q))
    (xs : List (ParityGate n p)) (zs : List (ParityGate n q))
    (hx : circuitCheck xs = c.hX) (hz : circuitCheck zs = c.hZ) (η : Bits p × Bits q) :
    (rawExtract xs zs).branch ((0, η.1), 0, η.2) =
      conjBranch (Matrix.reindexAlgEquiv ℂ ℂ (dataIndex n) (cssSyndromeProjector c η)) := by
  let T := Matrix.reindexAlgEquiv ℂ ℂ (dataIndex n)
  change ((conjBranch (parityKraus zs η.2)).comp (conjBranch (indexedHad n))).comp
      ((conjBranch (parityKraus xs η.1)).comp (conjBranch (indexedHad n))) =
        conjBranch (T (cssSyndromeProjector c η))
  rw [conjBranch_comp, conjBranch_comp, conjBranch_comp]
  change conjBranch ((T (readAfter (parityOp zs) η.2) * T (basisHad n)) *
      (T (readAfter (parityOp xs) η.1) * T (basisHad n))) = _
  rw [← map_mul, ← map_mul, ← map_mul, mul_assoc (readAfter (parityOp zs) η.2),
    ← mul_assoc (basisHad n), css_readout c xs zs hx hz η]

/-- The two Hadamard gates have one deterministic outcome each. -/
private def extractLabels (p q : ℕ) :
    ((Fin 1 × Bits p) × Fin 1 × Bits q) ≃ (Bits p × Bits q) where
  toFun o := (o.1.2, o.2.2)
  invFun η := ((0, η.1), 0, η.2)
  left_inv := by
    rintro ⟨⟨i, x⟩, j, z⟩
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    rfl
  right_inv := fun _ => rfl

/-- Measure the two ordered check words and report the pair of X and Z syndrome bits. -/
@[no_expose] noncomputable def cssExtract (xs : List (ParityGate n p)) (zs : List (ParityGate n q)) :
    Instrument (Bits p × Bits q) (Fintype.card (Bits n)) (Fintype.card (Bits n)) :=
  (rawExtract xs zs).coarsen (extractLabels p q)

/-- Each joint outcome of the executed CSS instrument gives the public syndrome branch. -/
theorem css_extract (c : CssData (Fin n) (Fin p) (Fin q))
    (xs : List (ParityGate n p)) (zs : List (ParityGate n q))
    (hx : circuitCheck xs = c.hX) (hz : circuitCheck zs = c.hZ) (η : Bits p × Bits q) :
    (cssExtract xs zs).branch η =
      conjBranch (Matrix.reindexAlgEquiv ℂ ℂ (dataIndex n) (cssSyndromeProjector c η)) := by
  rw [cssExtract, Instrument.coarsen_branch_equiv]
  exact raw_extract c xs zs hx hz η

/-- A data Hadamard transports a binary translation to the corresponding diagonal Pauli. -/
private theorem basisHad_x (x : Bits n) :
    basisHad n * cssPauliX x * basisHad n = cssPauliZ x := by
  calc
    _ = (basisHad n * basisHad n) * cssPauliZ x * (basisHad n * basisHad n) := by
      rw [← basisHad_z x]
      simp only [mul_assoc]
    _ = _ := by simp only [basisHad_sq, one_mul, mul_one]

/-- Each Z readout branch commutes with diagonal data errors. -/
private theorem parity_z_comm (gs : List (ParityGate n m)) (η : Bits m) (z : Bits n) :
    Commute (readAfter (parityOp gs) η) (cssPauliZ z) := by
  show readAfter (parityOp gs) η * cssPauliZ z = cssPauliZ z * readAfter (parityOp gs) η
  rw [parity_branch, cssPauliZ, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  exact mul_comm _ _

/-- The Hadamards turn the X-round data flip into a phase error. The combined measured
branch is the ideal CSS projection at the two shifted outcomes, followed by the propagated
X and Z data residuals. -/
theorem css_faultBranch (c : CssData (Fin n) (Fin p) (Fin q))
    (xs : List (ParityGate n p)) (zs : List (ParityGate n q))
    (hx : circuitCheck xs = c.hX) (hz : circuitCheck zs = c.hZ)
    (fx : Fin xs.length → Joint n p) (fz : Fin zs.length → Joint n q)
    (η : Bits p × Bits q) :
    readAfter (faultyOp zs fz) η.2 * (basisHad n * readAfter (faultyOp xs fx) η.1 * basisHad n) =
      (cssPauliX (faultRun zs fz 0).1 * cssPauliZ (faultRun xs fx 0).1) *
        cssSyndromeProjector c (η.1 - (faultRun xs fx 0).2, η.2 - (faultRun zs fz 0).2) := by
  rw [faulty_operator zs fz, faulty_operator xs fx]
  let X := cssPauliX (faultRun zs fz 0).1
  let D := cssPauliX (faultRun xs fx 0).1
  let Z := cssPauliZ (faultRun xs fx 0).1
  let H := basisHad n
  let B := readAfter (parityOp xs) (η.1 - (faultRun xs fx 0).2)
  let P := readAfter (parityOp zs) (η.2 - (faultRun zs fz 0).2)
  have hc : H * D * H = Z := basisHad_x _
  have hs : H * H = 1 := basisHad_sq _
  have hP : P * Z = Z * P := parity_z_comm _ _ _
  calc
    _ = (X * P) * ((H * D * H) * (H * B * H)) := by
      simp only [mul_assoc]
      rw [show H * (H * (B * H)) = B * H from by rw [← mul_assoc, hs, one_mul]]
    _ = (X * Z) * (P * (H * B * H)) := by
      rw [hc]
      calc
        _ = X * ((P * Z) * (H * B * H)) := by simp only [mul_assoc]
        _ = _ := by rw [hP]; simp only [mul_assoc]
    _ = _ := by
      congr 1
      exact css_readout c xs zs hx hz
        (η.1 - (faultRun xs fx 0).2, η.2 - (faultRun zs fz 0).2)

/-- For local data flips of weight at most one, the joint residual weight is bounded by
the total number of faulty gates in the two executed rounds. -/
theorem css_faultWeight
    (xs : List (ParityGate n p)) (zs : List (ParityGate n q))
    (fx : Fin xs.length → Joint n p) (fz : Fin zs.length → Joint n q)
    (hx : ∀ i, bitWeight (fx i).1 ≤ 1) (hz : ∀ i, bitWeight (fz i).1 ≤ 1)
    (F : Finset (Fin xs.length)) (G : Finset (Fin zs.length)) :
    pauliWeight (faultRun zs (faultsAt zs fz G) 0).1 (faultRun xs (faultsAt xs fx F) 0).1 ≤
      F.card + G.card := by
  let x := (faultRun zs (faultsAt zs fz G) 0).1
  let z := (faultRun xs (faultsAt xs fx F) 0).1
  have h : pauliWeight x z ≤ bitWeight x + bitWeight z := by
    simpa only [add_zero, zero_add, pauliWeight_zero_right, pauliWeight_zero_left] using
      pauliWeight_add_le x 0 0 z
  rw [add_comm F.card G.card]
  exact h.trans (Nat.add_le_add (fault_weight zs fz hz G) (fault_weight xs fx hx F))

end Qatlib.Concepts.CodingDecoding.CssRecovery
