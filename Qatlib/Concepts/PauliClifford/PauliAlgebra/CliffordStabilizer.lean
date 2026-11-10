/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option autoImplicit false

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs Matrix

theorem pauli_ext {n : ℕ} {p q : PauliElem n}
    (hw : p.word = q.word) (hp : p.phase = q.phase) : p = q := by
  cases p
  cases q
  simp_all

theorem decode_encode {n : ℕ} (p : PauliElem n) : (encode p).decode = p := by
  apply pauli_ext
  · funext k
    change letter (bitX (p.word k)) (bitZ (p.word k)) = p.word k
    cases p.word k <;> rfl
  · rfl

theorem encode_decode {n : ℕ} (r : Row n) : encode r.decode = r := by
  apply Row.ext
  · funext k
    change bitX (letter (r.x k) (r.z k)) = r.x k
    cases r.x k <;> cases r.z k <;> rfl
  · funext k
    change bitZ (letter (r.x k) (r.z k)) = r.z k
    cases r.x k <;> cases r.z k <;> rfl
  · rfl

theorem row_x {n : ℕ} (r : Row n) (k : Fin n) :
    symplecticX r.decode.word k = if r.x k then 1 else 0 := by
  cases hx : r.x k <;> cases hz : r.z k <;>
    simp [symplecticX, Row.decode, letter, hx, hz]

theorem row_z {n : ℕ} (r : Row n) (k : Fin n) :
    symplecticZ r.decode.word k = if r.z k then 1 else 0 := by
  cases hx : r.x k <;> cases hz : r.z k <;>
    simp [symplecticZ, Row.decode, letter, hx, hz]

theorem row_bits_length {n : ℕ} (r : Row n) : r.bits.length = 2 * n + 2 := by
  simp [Row.bits]
  omega

theorem tableau_bits_length {n m : ℕ} (t : Tableau n m) :
    (tableauBits t).length = m * (2 * n + 2) := by
  simp [tableauBits, List.length_flatMap, row_bits_length, Function.comp_def]

theorem letter_mul (x z y w : Bool) :
    letter (xor x y) (xor z w) = pauliMul1 (letter x z) (letter y w) := by
  cases x <;> cases z <;> cases y <;> cases w <;> rfl

theorem decode_mul {n : ℕ} (r s : Row n) :
    (r.mul s).decode = r.decode.mul s.decode := by
  apply pauli_ext
  · funext k
    exact letter_mul _ _ _ _
  · rfl

theorem row_mul_op {n : ℕ} (r s : Row n) :
    op (r.mul s).decode = op r.decode * op s.decode := by
  rw [decode_mul, op_mul]

theorem decode_update {n : ℕ} (g : CliffordGate n) (hg : legalGate g) (r : Row n) :
    (r.update g).decode = verifiedCliffordAction g r.decode := by
  cases g with
  | H i =>
    apply pauli_ext
    · funext k
      by_cases hk : k = i
      · subst k
        cases hxi : r.x i <;> cases hzi : r.z i <;>
          simp [Row.decode, Row.update, letter, conjHWord, hxi, hzi,
            verifiedCliffordAction]
      · simp [Row.decode, Row.update, hk, verifiedCliffordAction]
    · simp only [Row.decode, Row.update, verifiedCliffordAction, sum_ite_single4]
      cases hxi : r.x i <;> cases hzi : r.z i <;>
        simp [letter, conjHPhase]
  | S i =>
    apply pauli_ext
    · funext k
      by_cases hk : k = i
      · subst k
        cases hxi : r.x i <;> cases hzi : r.z i <;>
          simp [Row.decode, Row.update, letter, conjSWord, hxi, hzi,
            verifiedCliffordAction]
      · simp [Row.decode, Row.update, hk, verifiedCliffordAction]
    · simp only [Row.decode, Row.update, verifiedCliffordAction, sum_ite_single4]
      cases hxi : r.x i <;> cases hzi : r.z i <;>
        simp [letter, conjSPhase]
  | CNOT i j =>
    have hij : i ≠ j := hg
    apply pauli_ext
    · funext k
      by_cases hi : k = i
      · subst k
        cases hxi : r.x i <;> cases hzi : r.z i <;>
          cases hxj : r.x j <;> cases hzj : r.z j <;>
            simp [Row.decode, Row.update, verifiedCliffordAction, hij, letter,
              pauliMul1, cnotTargetCross, hxi, hzi, hxj, hzj]
      · by_cases hj : k = j
        · subst k
          cases hxi : r.x i <;> cases hzi : r.z i <;>
            cases hxj : r.x j <;> cases hzj : r.z j <;>
              simp [Row.decode, Row.update, verifiedCliffordAction, Ne.symm hij, letter,
                pauliMul1, cnotControlCross, hxi, hzi, hxj, hzj]
        · simp [Row.decode, Row.update, verifiedCliffordAction, hi, hj]
    · cases hxi : r.x i <;> cases hzi : r.z i <;>
        cases hxj : r.x j <;> cases hzj : r.z j <;>
          simp [Row.decode, Row.update, verifiedCliffordAction, cnotPhaseCorrection,
            letter, hxi, hzi, hxj, hzj]

theorem row_update_op {n : ℕ} (g : CliffordGate n) (hg : legalGate g) (r : Row n) :
    op (r.update g).decode = cliffordGateOp n g * op r.decode * (cliffordGateOp n g)ᴴ := by
  rw [decode_update g hg, gate_conj g hg]

theorem run_decode {n m : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) (t : Tableau n m) (a : Fin m) :
    (run gs t a).decode = actionWord gs (t a).decode := by
  induction gs generalizing t with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (update g t) a).decode = actionWord gs (verifiedCliffordAction g (t a).decode)
    rw [ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')),
      show (update g t a).decode = verifiedCliffordAction g (t a).decode from
        decode_update g (hgs g List.mem_cons_self) (t a)]

theorem run_op {n m : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) (t : Tableau n m) (a : Fin m) :
    op (run gs t a).decode = Uword gs * op (t a).decode * (Uword gs)ᴴ := by
  rw [run_decode gs hgs, Uword_conj gs _ hgs]

theorem mem_run_iff {n m : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) (t : Tableau n m) (ψ : QState (Reg n)) :
    Uword gs *ᵥ ψ ∈ codeSpace (run gs t) ↔ ψ ∈ codeSpace t := by
  have hU := Uword_unitary gs hgs
  have hinv : (Uword gs)ᴴ * Uword gs = 1 :=
    (Matrix.mem_unitaryGroup_iff'.mp hU)
  have hinj : Function.Injective (fun v => Uword gs *ᵥ v) := by
    intro v w hvw
    have := congrArg (fun v => (Uword gs)ᴴ *ᵥ v) hvw
    simpa only [mulVec_mulVec, hinv, one_mulVec] using this
  have hrow (a : Fin m) : op (run gs t a).decode * Uword gs = Uword gs * op (t a).decode := by
    rw [run_op gs hgs, Matrix.mul_assoc, hinv, Matrix.mul_one]
  change (∀ a, op (run gs t a).decode *ᵥ (Uword gs *ᵥ ψ) = Uword gs *ᵥ ψ) ↔
    ∀ a, op (t a).decode *ᵥ ψ = ψ
  simp_rw [mulVec_mulVec, hrow, ← mulVec_mulVec, hinj.eq_iff]

noncomputable def runCodeEquiv {n m : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) (t : Tableau n m) :
    codeSpace t ≃ₗ[ℂ] codeSpace (run gs t) := by
  let e := Matrix.UnitaryGroup.toLinearEquiv ⟨Uword gs, Uword_unitary gs hgs⟩
  apply e.ofSubmodules
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (mem_run_iff gs hgs t φ).mpr hφ
  · intro hψ
    refine ⟨e.symm ψ, ?_, e.apply_symm_apply ψ⟩
    apply (mem_run_iff gs hgs t (e.symm ψ)).mp
    change e (e.symm ψ) ∈ codeSpace (run gs t)
    simpa only [e.apply_symm_apply] using hψ

theorem finrank_run {n m : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) (t : Tableau n m) :
    Module.finrank ℂ (codeSpace (run gs t)) = Module.finrank ℂ (codeSpace t) :=
  (runCodeEquiv gs hgs t).finrank_eq.symm

theorem zero_row_op {n : ℕ} (i : Fin n) :
    op (zeroTableau n i).decode = Matrix.diagonal (fun b : Reg n =>
      if b i then (-1 : ℂ) else 1) := by
  ext b c
  rw [op_apply]
  simp only [zeroTableau, Row.decode, ZMod.val_zero, pow_zero, one_mul,
    Matrix.diagonal_apply]
  by_cases hbc : b = c
  · subst c
    rw [if_pos rfl]
    have hf : ∀ k, P1 (letter false (decide (k = i))) (b k) (b k) =
        if k = i then (if b i then (-1 : ℂ) else 1) else 1 := by
      intro k
      by_cases hk : k = i
      · subst k
        cases b i <;> simp [letter, P1]
      · cases b k <;> simp [hk, letter, P1]
    simp_rw [hf]
    simp
  · rw [if_neg hbc]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hbc
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    by_cases hki : k = i <;> cases hb : b k <;> cases hc : c k <;>
      simp_all [letter, P1]

theorem zero_row_mulVec {n : ℕ} (i : Fin n) (ψ : QState (Reg n)) (b : Reg n) :
    (op (zeroTableau n i).decode *ᵥ ψ) b = (if b i then (-1 : ℂ) else 1) * ψ b := by
  rw [zero_row_op]
  exact Matrix.mulVec_diagonal _ _ _

theorem mem_zero_code_iff (n : ℕ) (ψ : QState (Reg n)) :
    ψ ∈ codeSpace (zeroTableau n) ↔ ∃ c : ℂ, ψ = c • Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) := by
  constructor
  · intro hψ
    refine ⟨ψ (ZeroStr n), ?_⟩
    funext b
    by_cases hb : b = ZeroStr n
    · subst b
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hb
      have hbi : b i = true := by
        cases hh : b i <;> simp_all [ZeroStr]
      have h := congrFun (hψ i) b
      rw [zero_row_mulVec, hbi, if_pos rfl] at h
      have hz : ψ b = 0 := by linear_combination (-(1 / 2 : ℂ)) * h
      simp [Qatlib.Foundations.PureStateMath.Ket, hb, hz]
  · rintro ⟨c, rfl⟩ i
    rw [Matrix.mulVec_smul]
    congr 1
    apply op_ZI_stabilizes_ket_zero
    intro k
    by_cases hk : k = i <;> simp [zeroTableau, letter, hk]

theorem zero_code_eq_span (n : ℕ) :
    codeSpace (zeroTableau n) = Submodule.span ℂ {Qatlib.Foundations.PureStateMath.Ket (ZeroStr n)} := by
  ext ψ
  rw [mem_zero_code_iff, Submodule.mem_span_singleton]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨c, hc.symm⟩⟩

theorem zero_ket_ne_zero (n : ℕ) : (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) : QState (Reg n)) ≠ 0 := by
  intro h
  have := congrFun h (ZeroStr n)
  simp [Qatlib.Foundations.PureStateMath.Ket] at this

theorem finrank_zero_code (n : ℕ) : Module.finrank ℂ (codeSpace (zeroTableau n)) = 1 := by
  rw [zero_code_eq_span]
  exact finrank_span_singleton (zero_ket_ne_zero n)

theorem prepared_mem {n : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) :
    Uword gs *ᵥ Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) ∈ codeSpace (run gs (zeroTableau n)) := by
  apply (mem_run_iff gs hgs _ _).mpr
  exact (mem_zero_code_iff _ _).mpr ⟨1, (one_smul ℂ _).symm⟩

theorem prepared_normalized {n : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) : Normalized (Uword gs *ᵥ Qatlib.Foundations.PureStateMath.Ket (ZeroStr n)) :=
  normalized_applyGate (Uword_unitary gs hgs) (normalized_ket _)

theorem finrank_prepared_code {n : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) :
    Module.finrank ℂ (codeSpace (run gs (zeroTableau n))) = 1 := by
  rw [finrank_run gs hgs, finrank_zero_code]

theorem mem_prepared_code_iff {n : ℕ} (gs : List (CliffordGate n))
    (hgs : ∀ g ∈ gs, legalGate g) (ψ : QState (Reg n)) :
    ψ ∈ codeSpace (run gs (zeroTableau n)) ↔
      ∃ c : ℂ, ψ = c • (Uword gs *ᵥ Qatlib.Foundations.PureStateMath.Ket (ZeroStr n)) := by
  have hU : Uword gs * (Uword gs)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Uword_unitary gs hgs)
  constructor
  · intro hψ
    have hi : (Uword gs)ᴴ *ᵥ ψ ∈ codeSpace (zeroTableau n) := by
      apply (mem_run_iff gs hgs _ _).mp
      simpa only [mulVec_mulVec, hU, one_mulVec] using hψ
    obtain ⟨c, hc⟩ := (mem_zero_code_iff _ _).mp hi
    refine ⟨c, ?_⟩
    have := congrArg (fun v => Uword gs *ᵥ v) hc
    simpa only [mulVec_mulVec, hU, one_mulVec, Matrix.mulVec_smul] using this
  · rintro ⟨c, rfl⟩
    exact (codeSpace _).smul_mem c (prepared_mem gs hgs)

theorem empty_code (n : ℕ) (t : Tableau n 0) : codeSpace t = ⊤ := by
  ext ψ
  simp [codeSpace]

theorem finrank_empty_code (n : ℕ) (t : Tableau n 0) :
    Module.finrank ℂ (codeSpace t) = 2 ^ n := by
  rw [empty_code, finrank_top, Module.finrank_fintype_fun_eq_card, card_reg]

theorem minusI_op (n : ℕ) :
    op (Row.decode (⟨fun _ => false, fun _ => false, 2⟩ : Row n)) = -1 := by
  have h : op (⟨fun _ => Pauli1.I, 0⟩ : PauliElem n) = 1 := op_one
  change (Complex.I ^ (2 : Phase4).val : ℂ) • pauliWordOp n (fun _ => .I) = -1
  have hword : pauliWordOp n (fun _ => .I) = 1 := by
    simpa [op] using h
  rw [hword]
  simp [zmod4_val_two]

theorem code_eq_bot_of_minusI {n m : ℕ} (t : Tableau n m) (a : Fin m)
    (ha : t a = ⟨fun _ => false, fun _ => false, 2⟩) : codeSpace t = ⊥ := by
  apply bot_unique
  intro ψ hψ
  change ψ = 0
  have h := hψ a
  rw [ha, minusI_op] at h
  funext b
  change ψ b = 0
  have hb := congrFun h b
  simp only [Matrix.neg_mulVec, Matrix.one_mulVec, Pi.neg_apply] at hb
  linear_combination (-(1 / 2 : ℂ)) * hb

end Qatlib.Concepts.PauliClifford.PauliAlgebra
