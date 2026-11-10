/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib.Concepts.PauliClifford.PauliAlgebra Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix

theorem Uword_nil {n : ℕ} : Uword ([] : List (CliffordGate n)) = 1 := rfl

theorem foldl_Uword {n : ℕ} (gs : List (CliffordGate n)) (M : Matrix (Reg n) (Reg n) ℂ) :
    gs.foldl (fun U g => cliffordGateOp n g * U) M = Uword gs * M := by
  induction gs generalizing M with
  | nil => simp [Uword]
  | cons g gs ih =>
    simp only [List.foldl_cons, Uword, Matrix.mul_one]
    rw [ih, ih, Matrix.mul_assoc]

theorem Uword_cons {n : ℕ} (g : CliffordGate n) (gs : List (CliffordGate n)) :
    Uword (g :: gs) = Uword gs * cliffordGateOp n g := by
  show (g :: gs).foldl (fun U g => cliffordGateOp n g * U) 1 = _
  rw [List.foldl_cons, Matrix.mul_one]
  exact foldl_Uword gs (cliffordGateOp n g)

theorem gate_unitary {n : ℕ} (g : CliffordGate n) (hg : legalGate g) :
    cliffordGateOp n g ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  cases g with
  | H i => exact cliffordGateOp_H_unitary n i
  | S i => exact cliffordGateOp_S_unitary n i
  | CNOT i j => exact cliffordGateOp_CNOT_unitary i j hg

theorem gate_conj {n : ℕ} (g : CliffordGate n) (hg : legalGate g) (p : PauliElem n) :
    cliffordGateOp n g * op p * (cliffordGateOp n g)ᴴ = op (verifiedCliffordAction g p) := by
  cases g with
  | H i => exact cliffordGateOp_H_conj i p
  | S i => exact cliffordGateOp_S_conj i p
  | CNOT i j => exact cliffordGateOp_CNOT_conj i j hg p

theorem mul_push {ι : Type*} [Fintype ι] [DecidableEq ι] (U G M : Matrix ι ι ℂ) :
    U * (G * M * Gᴴ) * Uᴴ = U * G * M * (Gᴴ * Uᴴ) := by
  calc U * (G * M * Gᴴ) * Uᴴ = (U * (G * M)) * Gᴴ * Uᴴ := by
        rw [← Matrix.mul_assoc U (G * M) Gᴴ]
    _ = ((U * G) * M) * Gᴴ * Uᴴ := by rw [← Matrix.mul_assoc U G M]
    _ = ((U * G) * M) * (Gᴴ * Uᴴ) := by rw [Matrix.mul_assoc (U * G * M) Gᴴ Uᴴ]

theorem Uword_unitary {n : ℕ} : ∀ gs : List (CliffordGate n),
    (∀ g ∈ gs, legalGate g) → Uword gs ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  intro gs
  induction gs with
  | nil => intro _; exact (Matrix.unitaryGroup (Reg n) ℂ).one_mem
  | cons g gs ih =>
    intro hgs
    rw [Uword_cons]
    exact Submonoid.mul_mem (Matrix.unitaryGroup (Reg n) ℂ)
      (ih fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')) (gate_unitary g
        (hgs g List.mem_cons_self))

theorem Uword_conj {n : ℕ} : ∀ (gs : List (CliffordGate n)) (p : PauliElem n),
    (∀ g ∈ gs, legalGate g) →
      Uword gs * op p * (Uword gs)ᴴ = op (actionWord gs p) := by
  intro gs
  induction gs with
  | nil => intro p _; simp [Uword, actionWord]
  | cons g gs ih =>
    intro p hgs
    have hg : legalGate g := hgs g List.mem_cons_self
    rw [Uword_cons, Matrix.conjTranspose_mul, ← mul_push, gate_conj g hg p]
    have hA : actionWord (g :: gs) p = actionWord gs (verifiedCliffordAction g p) := rfl
    rw [hA]
    exact ih _ fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')

theorem mulVec_ket {n : ℕ} (M : Matrix (Reg n) (Reg n) ℂ) (z : Reg n) :
    M *ᵥ (Qatlib.Foundations.PureStateMath.Ket z : QState (Reg n)) = fun b => M b z := by
  funext b
  simp only [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket]
  rw [Finset.sum_eq_single z
    (fun c _ hc => by rw [if_neg hc]; simp)
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_one]

theorem cnot_mulVec {n : ℕ} (i j : Fin n) (hij : i ≠ j) (v : QState (Reg n)) :
    cliffordGateOp n (.CNOT i j) *ᵥ v = fun b => v (cnotT i j b) := by
  funext b
  simp only [Matrix.mulVec, dotProduct, cliffordGateOp_CNOT_apply i j hij]
  rw [Finset.sum_eq_single (cnotT i j b)
    (fun c _ hc => by
      rw [if_neg (fun he => hc (by rw [he, cnotT_involutive i j c]))]
      simp)
    (fun h => absurd (Finset.mem_univ _) h), if_pos ((cnotT_involutive i j b).symm),
    one_mul]

theorem op_ZI_stabilizes_ket_zero {n : ℕ} (w : PauliWord n)
    (hw : ∀ k, w k = .Z ∨ w k = .I) :
    op ⟨w, 0⟩ *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) : QState (Reg n)) = Qatlib.Foundations.PureStateMath.Ket (ZeroStr n) := by
  funext b
  simp only [mulVec_ket, op_apply, Qatlib.Foundations.PureStateMath.Ket, ZMod.val_zero,
      pow_zero, one_mul]
  have hf : ∀ k, P1 (w k) (b k) ((ZeroStr n : Reg n) k)
      = if b k then (0 : ℂ) else 1 := by
    intro k
    rcases hw k with h | h <;> rw [h] <;> cases b k <;> simp [P1, ZeroStr]
  by_cases hb : b = ZeroStr n
  · rw [if_pos hb]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hf k]
    have hk : b k = false := by rw [hb]; rfl
    rw [hk]
    simp
  · rw [if_neg hb]
    obtain ⟨k, hk⟩ := Classical.not_forall.mp fun hall => hb (funext hall)
    have hbt : b k = true := by
      cases hh : b k with
      | false => exact absurd (by rw [hh]; rfl) hk
      | true => rfl
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by
      show P1 (w k) (b k) ((ZeroStr n : Reg n) k) = 0
      rw [hf k, hbt]
      simp)]

theorem stabilizer_transport {n : ℕ} {U : Matrix (Reg n) (Reg n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) {p q : PauliElem n}
    (hconj : U * op q * Uᴴ = op p) {φ : QState (Reg n)} (hq : op q *ᵥ φ = φ) :
    op p *ᵥ (U *ᵥ φ) = U *ᵥ φ := by
  have h1 : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  have h2 : op p * U = U * op q := by
    rw [← hconj, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [mulVec_mulVec, h2, ← mulVec_mulVec, hq]

theorem hbell_legal :
    ∀ g ∈ [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1], legalGate g := by
  simp [legalGate]

theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨kv, hklt⟩
  rcases Nat.eq_zero_or_pos kv with h0 | h0
  · left
    exact Fin.ext h0
  · right
    exact Fin.ext (by omega : kv = 1)

theorem Uword_H_CNOT :
    Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1]
      = cliffordGateOp 2 (CliffordGate.CNOT (0 : Fin 2) 1)
        * cliffordGateOp 2 (CliffordGate.H (0 : Fin 2)) := by
  rw [Uword_cons, Uword_cons, Uword_nil, Matrix.one_mul]

theorem actionWord_bell_ZI :
    actionWord [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] ⟨![.Z, .I], 0⟩
      = ⟨fun _ => .X, 0⟩ := by
  have h1 : verifiedCliffordAction (CliffordGate.H (0 : Fin 2)) ⟨![.Z, .I], 0⟩
      = ⟨![.X, .I], 0⟩ := by
    simp only [verifiedCliffordAction, PauliElem.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext k
      fin_cases k <;> simp [conjHWord]
    · simp [conjHPhase]
  have h2 : verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.X, .I], 0⟩
      = ⟨fun _ => .X, 0⟩ := by
    simp only [verifiedCliffordAction, PauliElem.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext k
      fin_cases k <;> simp [pauliMul1, cnotTargetCross, cnotControlCross]
    · simp [cnotPhaseCorrection]
  show (verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1)
      (verifiedCliffordAction (CliffordGate.H (0 : Fin 2)) ⟨![.Z, .I], 0⟩)) = _
  rw [h1, h2]

theorem actionWord_bell_IZ :
    actionWord [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] ⟨![.I, .Z], 0⟩
      = ⟨fun _ => .Z, 0⟩ := by
  have h1 : verifiedCliffordAction (CliffordGate.H (0 : Fin 2)) ⟨![.I, .Z], 0⟩
      = ⟨![.I, .Z], 0⟩ := by
    simp only [verifiedCliffordAction, PauliElem.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext k
      fin_cases k <;> simp [conjHWord]
    · simp [conjHPhase]
  have h2 : verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1) ⟨![.I, .Z], 0⟩
      = ⟨fun _ => .Z, 0⟩ := by
    simp only [verifiedCliffordAction, PauliElem.mk.injEq]
    refine ⟨?_, ?_⟩
    · funext k
      fin_cases k <;> simp [pauliMul1, cnotTargetCross, cnotControlCross]
    · simp [cnotPhaseCorrection]
  show (verifiedCliffordAction (CliffordGate.CNOT (0 : Fin 2) 1)
      (verifiedCliffordAction (CliffordGate.H (0 : Fin 2)) ⟨![.I, .Z], 0⟩)) = _
  rw [h1, h2]

theorem bell_state :
    Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) + Qatlib.Foundations.PureStateMath.Ket (fun _ => true)) := by
  have hH : (cliffordGateOp 2 (CliffordGate.H (0 : Fin 2)) *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
      = fun b => if b 1 then (0 : ℂ) else (Real.sqrt 2 : ℂ)⁻¹ := by
    funext b
    simp only [mulVec_ket, cliffordGateOp]
    by_cases hb1 : b 1 = false
    · have hcond : ∀ j : Fin 2, j ≠ (0 : Fin 2) → b j = (ZeroStr 2 : Reg 2) j := by
        intro j hj
        have hj1 : j = 1 := Fin.ext (by
          have h1 : j.val ≠ 0 := fun h => hj (Fin.ext h)
          omega)
        rw [hj1, hb1]
        rfl
      rw [if_pos hcond]
      have hz : (ZeroStr 2 : Reg 2) 0 = false := rfl
      rw [hz, hb1]
      cases b 0 <;> simp [Hadamard]
    · have hcond : ¬ (∀ j : Fin 2, j ≠ (0 : Fin 2) → b j = (ZeroStr 2 : Reg 2) j) := by
        intro hall
        have h1 : b 1 = (ZeroStr 2 : Reg 2) 1 := hall 1 (by decide)
        exact absurd (show b 1 = false from h1) hb1
      rw [if_neg hcond]
      have hbt : b 1 = true := by
        cases hh : b 1 <;> simp_all
      rw [if_pos hbt]
  rw [Uword_H_CNOT, ← mulVec_mulVec, cnot_mulVec (0 : Fin 2) 1 (by decide), hH]
  funext b
  have hT : (cnotT (0 : Fin 2) 1 b) 1 = (b 1 ^^ b 0) := by
    simp [cnotT]
  simp only [hT, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Qatlib.Foundations.PureStateMath.Ket]
  have hzt : (ZeroStr 2 : Reg 2) ≠ (fun _ => true) := by
    intro he
    have h0 : (ZeroStr 2 : Reg 2) ⟨0, by decide⟩ = true := congrFun he ⟨0, by decide⟩
    simp [ZeroStr] at h0
  by_cases hb : b = (ZeroStr 2 : Reg 2)
  · subst hb
    have hx : ((ZeroStr 2 : Reg 2) 1 ^^ (ZeroStr 2 : Reg 2) 0) = false := by
      simp [ZeroStr]
    rw [hx, if_neg (by simp), if_pos rfl, if_neg hzt]
    simp
  · by_cases hb2 : b = (fun _ => true)
    · subst hb2
      have hx : ((fun _ => true : Reg 2) 1 ^^ (fun _ => true : Reg 2) 0) = false := by
        simp
      rw [hx, if_neg (by simp), if_neg (fun he => hzt he.symm), if_pos rfl]
      simp
    · rw [if_neg hb, if_neg hb2, add_zero, mul_zero]
      have hx : (b 1 ^^ b 0) = true := by
        cases hh0 : b 0
        · cases hh1 : b 1
          · exact absurd (funext fun k => by
              rcases fin2_cases k with rfl | rfl
              · simp [ZeroStr, hh0]
              · simp [ZeroStr, hh1]) hb
          · rfl
        · cases hh1 : b 1
          · rfl
          · exact absurd (funext fun k => by
              rcases fin2_cases k with rfl | rfl
              · simp [hh0]
              · simp [hh1]) hb2
      rw [hx]
      simp

theorem bell_normalized :
    Normalized (Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
      (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2))) :=
  normalized_applyGate (Uword_unitary _ hbell_legal) (normalized_ket (ZeroStr 2))

theorem bell_XX_stabilizer :
    op ⟨fun _ => Pauli1.X, 0⟩ *ᵥ (Uword [CliffordGate.H (0 : Fin 2),
          CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
      = Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)) := by
  refine stabilizer_transport (Uword_unitary _ hbell_legal)
    (q := ⟨![.Z, .I], 0⟩) ?_ (op_ZI_stabilizes_ket_zero _ (by
      intro k
      fin_cases k <;> simp))
  rw [Uword_conj _ _ hbell_legal, actionWord_bell_ZI]

theorem bell_ZZ_stabilizer :
    op ⟨fun _ => Pauli1.Z, 0⟩ *ᵥ (Uword [CliffordGate.H (0 : Fin 2),
          CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
      = Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)) := by
  refine stabilizer_transport (Uword_unitary _ hbell_legal)
    (q := ⟨![.I, .Z], 0⟩) ?_ (op_ZI_stabilizes_ket_zero _ (by
      intro k
      fin_cases k <;> simp))
  rw [Uword_conj _ _ hbell_legal, actionWord_bell_IZ]

theorem hH_legal : ∀ g ∈ [CliffordGate.H (0 : Fin 1)], legalGate g := by
  simp [legalGate]

theorem actionWord_H_Z :
    actionWord [CliffordGate.H (0 : Fin 1)] ⟨fun _ => .Z, 0⟩
      = ⟨fun _ => .X, 0⟩ := by
  show (verifiedCliffordAction (CliffordGate.H (0 : Fin 1)) ⟨fun _ => .Z, 0⟩) = _
  simp only [verifiedCliffordAction, PauliElem.mk.injEq, conjHWord]
  refine ⟨?_, ?_⟩
  · funext k
    fin_cases k; simp
  · simp [conjHPhase]

theorem h_state :
    Uword [CliffordGate.H (0 : Fin 1)] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) : QState (Reg 1))
      = (fun _ => ((Real.sqrt 2 : ℂ)⁻¹)) := by
  have hU : Uword [CliffordGate.H (0 : Fin 1)]
      = cliffordGateOp 1 (CliffordGate.H (0 : Fin 1)) := by
    rw [Uword_cons, Uword_nil, Matrix.one_mul]
  rw [hU]
  funext b
  simp only [mulVec_ket, cliffordGateOp]
  have hcond : ∀ j : Fin 1, j ≠ (0 : Fin 1) → b j = (ZeroStr 1 : Reg 1) j := by
    intro j hj
    exact absurd (Fin.ext (Nat.lt_one_iff.mp j.isLt)) hj
  rw [if_pos hcond]
  have hz : (ZeroStr 1 : Reg 1) 0 = false := rfl
  rw [hz]
  cases b 0 <;> simp [Hadamard]

theorem h_state_X_stabilizer :
    op ⟨fun _ => Pauli1.X, 0⟩ *ᵥ (Uword [CliffordGate.H (0 : Fin 1)] *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) : QState (Reg 1)))
      = Uword [CliffordGate.H (0 : Fin 1)] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) : QState (Reg 1)) := by
  refine stabilizer_transport (Uword_unitary _ hH_legal) (q := ⟨fun _ => .Z, 0⟩) ?_
    (op_ZI_stabilizes_ket_zero _ (fun _ => Or.inl rfl))
  rw [Uword_conj _ _ hH_legal, actionWord_H_Z]

theorem actual_word_and_bell_consumers :
    (∀ (n : ℕ) (gs : List (CliffordGate n)),
      (∀ g ∈ gs, legalGate g) → ∀ (p : PauliElem n),
        (Uword gs ∈ Matrix.unitaryGroup (Reg n) ℂ)
        ∧ (Uword gs * op p * (Uword gs)ᴴ = op (actionWord gs p)))
    ∧ (Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2))
      = ((Real.sqrt 2 : ℂ)⁻¹) • (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) + Qatlib.Foundations.PureStateMath.Ket (fun _ => true)))
    ∧ (Normalized (Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
        (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
      ∧ op ⟨fun _ => Pauli1.X, 0⟩ *ᵥ (Uword [CliffordGate.H (0 : Fin 2),
          CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
        = Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
            (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2))
      ∧ op ⟨fun _ => Pauli1.Z, 0⟩ *ᵥ (Uword [CliffordGate.H (0 : Fin 2),
          CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
        = Uword [CliffordGate.H (0 : Fin 2), CliffordGate.CNOT (0 : Fin 2) 1] *ᵥ
            (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 2) : QState (Reg 2)))
    ∧ (Uword [CliffordGate.H (0 : Fin 1)] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) : QState (Reg 1))
        = (fun _ => ((Real.sqrt 2 : ℂ)⁻¹))
      ∧ op ⟨fun _ => Pauli1.X, 0⟩ *ᵥ
          (Uword [CliffordGate.H (0 : Fin 1)] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) : QState (Reg 1)))
        = Uword [CliffordGate.H (0 : Fin 1)] *ᵥ (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1) : QState (Reg 1))) := by
  exact ⟨fun n gs hgs p => ⟨Uword_unitary gs hgs, Uword_conj gs p hgs⟩, bell_state,
    ⟨bell_normalized, bell_XX_stabilizer, bell_ZZ_stabilizer⟩,
    ⟨h_state, h_state_X_stabilizer⟩⟩

end Qatlib.Concepts.PauliClifford.PauliAlgebra
