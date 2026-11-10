/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstructionDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs Matrix

open Qatlib.Concepts.PauliClifford.ExactRank (BooleanVec booleanDot)

open scoped Classical

theorem pauliElem_mul_self {n : ℕ} (p : PauliElem n) :
    p.mul p = ⟨fun _ => Pauli1.I, p.phase + p.phase⟩ := by
  apply pauli_ext
  · funext k
    exact pauliMul1_self _
  · simp only [PauliElem.mul, pauliMulPhase_self, Finset.sum_const_zero, add_zero]

theorem op_trivial_word {n : ℕ} (φ : Phase4) :
    op (⟨fun _ => Pauli1.I, φ⟩ : PauliElem n) = (Complex.I ^ φ.val : ℂ) • 1 := by
  have hword : pauliWordOp n (fun _ => Pauli1.I) = 1 := by
    rw [pauliWordOp_eq]
    have h : (fun _ : Fin n => P1 Pauli1.I) = fun _ => (1 : Matrix Bool Bool ℂ) :=
      funext fun _ => P1_one
    rw [h, Qatlib.Concepts.TensorRegisters.RegisterModel.productMatrix_one]
  simp only [op]
  rw [hword]

theorem op_mul_self_eq_phase {n : ℕ} (p : PauliElem n) :
    op p * op p = (Complex.I ^ (p.phase + p.phase).val : ℂ) • 1 := by
  rw [← op_mul, pauliElem_mul_self, op_trivial_word]

theorem zmod4_zero_add_zero : (0 : ZMod 4) + 0 = 0 := by decide

theorem zmod4_two_add_two : (2 : ZMod 4) + 2 = 0 := by decide

theorem op_mul_self {n : ℕ} {p : PauliElem n} (hp : IsHermitianPauli p) :
    op p * op p = 1 := by
  rw [op_mul_self_eq_phase]
  rcases hp with hp0 | hp2
  · rw [hp0, zmod4_zero_add_zero, ZMod.val_zero, pow_zero, one_smul]
  · rw [hp2, zmod4_two_add_two, ZMod.val_zero, pow_zero, one_smul]

theorem pauliElem_neg_phase {n : ℕ} {p : PauliElem n} (hp : IsHermitianPauli p) :
    ⟨p.word, -p.phase⟩ = p := by
  apply pauli_ext
  · rfl
  · rcases hp with hp0 | hp2
    · rw [hp0, neg_zero]
    · rw [hp2, show (-2 : ZMod 4) = 2 by decide]

theorem op_conjTranspose_herm {n : ℕ} {p : PauliElem n} (hp : IsHermitianPauli p) :
    (op p)ᴴ = op p := by
  rw [op_conjTranspose, pauliElem_neg_phase hp]

theorem phase_mul_comm {n : ℕ} (p q : PauliElem n) :
    (Complex.I ^ (p.mul q).phase.val : ℂ)
      = ((-1 : ℂ) ^ (symplecticForm (symplecticX p.word, symplecticZ p.word)
          (symplecticX q.word, symplecticZ q.word)).val)
        * (Complex.I ^ (q.mul p).phase.val : ℂ) := by
  have hscalar : Complex.I ^ (∑ i, pauliMulPhase (p.word i) (q.word i)).val
      = ((-1 : ℂ) ^ (symplecticForm (symplecticX p.word, symplecticZ p.word)
          (symplecticX q.word, symplecticZ q.word)).val)
        * Complex.I ^ (∑ i, pauliMulPhase (q.word i) (p.word i)).val := by
    rw [I_pow_sum_val, I_pow_sum_val, symplecticForm_eq_sum_site p.word q.word,
      neg_one_pow_sum_val, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => P1_site_comm (p.word i) (q.word i)
  show (Complex.I ^ (p.phase + q.phase + ∑ i, pauliMulPhase (p.word i) (q.word i)).val : ℂ)
      = ((-1 : ℂ) ^ (symplecticForm (symplecticX p.word, symplecticZ p.word)
          (symplecticX q.word, symplecticZ q.word)).val)
        * (Complex.I ^ (q.phase + p.phase + ∑ i, pauliMulPhase (q.word i) (p.word i)).val : ℂ)
  simp only [I_pow_val_add, hscalar]
  ring

theorem op_mul_comm_symplectic {n : ℕ} (p q : PauliElem n) :
    op p * op q
      = ((-1 : ℂ) ^ (symplecticForm (symplecticX p.word, symplecticZ p.word)
          (symplecticX q.word, symplecticZ q.word)).val) • (op q * op p) := by
  have hword : (fun i => pauliMul1 (p.word i) (q.word i))
      = (fun i => pauliMul1 (q.word i) (p.word i)) :=
    funext fun i => pauliMul1_comm _ _
  have hmul : (p.mul q).word = (q.mul p).word := by
    rw [PauliElem.mul, PauliElem.mul]
    exact funext fun i => pauliMul1_comm _ _
  rw [← op_mul, ← op_mul]
  simp only [op]
  rw [hmul, phase_mul_comm]
  ext x y
  simp only [Matrix.smul_apply]
  ring

theorem zmod2_val_eq_zero {e : ZMod 2} : e.val = 0 ↔ e = 0 := by
  constructor
  · intro h
    rw [← ZMod.natCast_zmod_val e, h, Nat.cast_zero]
  · intro h
    subst h
    exact ZMod.val_zero

theorem zmod2_eq_zero_of_val_eq_zero {e : ZMod 2} (h : e.val = 0) : e = 0 := by
  rw [← ZMod.natCast_zmod_val e, h, Nat.cast_zero]

theorem neg_one_pow_val_eq_one {e : ZMod 2} : ((-1 : ℂ) ^ e.val = 1) ↔ e = 0 := by
  have hlt : e.val < 2 := ZMod.val_lt e
  have hcases : e.val = 0 ∨ e.val = 1 := by omega
  rcases hcases with h0 | h1
  · constructor
    · intro _
      exact zmod2_eq_zero_of_val_eq_zero h0
    · intro _
      rw [h0, pow_zero]
  · constructor
    · intro h
      rw [h1, pow_one] at h
      exact absurd h (by norm_num)
    · intro h
      have hval := congrArg ZMod.val h
      rw [h1, ZMod.val_zero] at hval
      exact absurd hval (by simp)

theorem smul_eq_one_of_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (M : Matrix ι ι ℂ) (hM : M ≠ 0) (h : c • M = M) : c = 1 := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, M x y ≠ 0 := by
    by_contra hcon
    apply hM
    ext x y
    by_contra hxy
    exact hcon ⟨x, y, hxy⟩
  have h2 := congrArg (fun m => m x y) h
  change c * M x y = M x y at h2
  exact mul_right_cancel₀ hxy (h2.trans (one_mul (M x y)).symm)

theorem op_mul_ne_zero {n : ℕ} (p q : PauliElem n) : op p * op q ≠ 0 := by
  rw [← op_mul]
  intro hz
  have hu := op_unitary (p.mul q)
  rw [Matrix.mem_unitaryGroup_iff'] at hu
  rw [hz] at hu
  simp at hu

theorem op_commute_iff {n : ℕ} (p q : PauliElem n) :
    op p * op q = op q * op p ↔ pauliCommute p q := by
  constructor
  · intro h
    have hsmul : ((-1 : ℂ) ^ (symplecticForm (symplecticX p.word, symplecticZ p.word)
        (symplecticX q.word, symplecticZ q.word)).val) • (op q * op p) = op q * op p := by
      rw [← op_mul_comm_symplectic p q, h]
    have heps : ((-1 : ℂ) ^ (symplecticForm (symplecticX p.word, symplecticZ p.word)
        (symplecticX q.word, symplecticZ q.word)).val) = 1 :=
      smul_eq_one_of_ne_zero _ _ (op_mul_ne_zero q p) hsmul
    rw [neg_one_pow_val_eq_one] at heps
    exact heps
  · intro h
    rw [op_mul_comm_symplectic, h]
    simp

theorem half_mul_two : ((2 : ℂ)⁻¹) * 2 = 1 := by norm_num

theorem half_add_half : ((2 : ℂ)⁻¹) + ((2 : ℂ)⁻¹) = 1 := by norm_num

theorem conj_half : star ((2 : ℂ)⁻¹) = ((2 : ℂ)⁻¹) := by
  norm_num [Complex.conj_ofReal, map_inv₀]

theorem smul_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (M : Matrix ι ι ℂ) (v : ι → ℂ) : (c • M) *ᵥ v = c • (M *ᵥ v) := by
  funext i
  change (∑ j, (c * M i j) * v j) = c * (∑ j, M i j * v j)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem half_smul_add {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) :
    ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • (X + X) = ((2 : ℂ)⁻¹) • X := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  calc ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) * (X i j + X i j) = ((2 : ℂ)⁻¹) * (((2 : ℂ)⁻¹) * 2) * X i j := by
        ring
    _ = ((2 : ℂ)⁻¹) * X i j := by rw [half_mul_two]; ring

theorem mul_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (M N : Matrix ι ι ℂ) : M * (c • N) = c • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem smul_mul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ)
    (M N : Matrix ι ι ℂ) : (c • M) * N = c • (M * N) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem mem_cons_tail {α : Type*} {g a : α} {l : List α} (h : a ∈ l) : a ∈ g :: l :=
  List.mem_cons_of_mem g h

theorem smul_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (c d : ℂ)
    (M : Matrix ι ι ℂ) : c • (d • M) = (c * d) • M := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem half_half_two : ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) * 2 = (2 : ℂ)⁻¹ := by
  norm_num

theorem half_half_two_mul (x : ℂ) : ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) * (2 * x) = (2 : ℂ)⁻¹ * x := by
  rw [← mul_assoc, half_half_two]

theorem addOne_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (hsq : G * G = 1) :
    (1 + G) * (1 + G) = (2 : ℂ) • (1 + G) := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hsq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.one_apply]
  ring

theorem addOne_star {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (hherm : Gᴴ = G) :
    (1 + G)ᴴ = 1 + G := by
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hherm]

theorem projectorAux_cons {n : ℕ} (g : PauliElem n) (gs : List (PauliElem n)) :
    projectorAux (g :: gs) = ((2 : ℂ)⁻¹) • ((1 + op g) * projectorAux gs) := by
  show ((2 : ℂ)⁻¹) • (projectorAux gs + op g * projectorAux gs) = _
  rw [Matrix.add_mul, Matrix.one_mul]

theorem projectorAux_comm {n : ℕ} (g : PauliElem n) (gs : List (PauliElem n))
    (hg : ∀ h ∈ gs, op g * op h = op h * op g) :
    op g * projectorAux gs = projectorAux gs * op g := by
  induction gs with
  | nil =>
      show op g * 1 = 1 * op g
      rw [Matrix.mul_one, Matrix.one_mul]
  | cons h hs ih =>
      have hgh : op g * op h = op h * op g := hg h (List.mem_cons_self)
      have hghs : ∀ k ∈ hs, op g * op k = op k * op g :=
        fun k hk => hg k (mem_cons_tail hk)
      have ih' : op g * projectorAux hs = projectorAux hs * op g := ih hghs
      have key : op g * ((1 + op h) * projectorAux hs) = ((1 + op h) * projectorAux hs) * op g := by
        calc op g * ((1 + op h) * projectorAux hs)
            = (op g * (1 + op h)) * projectorAux hs := (Matrix.mul_assoc _ _ _).symm
          _ = (op g * 1 + op g * op h) * projectorAux hs := by rw [Matrix.mul_add]
          _ = (op g + op h * op g) * projectorAux hs := by rw [Matrix.mul_one, hgh]
          _ = ((1 + op h) * op g) * projectorAux hs := by
              have h2 : op g + op h * op g = (1 + op h) * op g := by
                rw [Matrix.add_mul, Matrix.one_mul]
              rw [h2]
          _ = (1 + op h) * (op g * projectorAux hs) := by rw [← Matrix.mul_assoc]
          _ = (1 + op h) * (projectorAux hs * op g) := by rw [ih']
          _ = ((1 + op h) * projectorAux hs) * op g := by rw [Matrix.mul_assoc]
      rw [projectorAux_cons, mul_smul_matrix, smul_mul_matrix, key]

theorem projectorAux_mul_gen {n : ℕ} (gs : List (PauliElem n))
    (hherm : ∀ h ∈ gs, IsHermitianPauli h)
    (hcomm : ∀ u ∈ gs, ∀ v ∈ gs, op u * op v = op v * op u)
    (h : PauliElem n) (hh : h ∈ gs) :
    op h * projectorAux gs = projectorAux gs := by
  induction gs with
  | nil => cases hh
  | cons g gs ih =>
      rw [projectorAux_cons, mul_smul_matrix]
      cases List.mem_cons.mp hh with
      | inl heq =>
          rw [heq]
          have hsq : op g * op g = 1 := op_mul_self (hherm g (List.mem_cons_self))
          congr 1
          calc op g * ((1 + op g) * projectorAux gs)
              = (op g * (1 + op g)) * projectorAux gs := (Matrix.mul_assoc _ _ _).symm
            _ = (op g * 1 + op g * op g) * projectorAux gs := by rw [Matrix.mul_add]
            _ = (op g + 1) * projectorAux gs := by rw [Matrix.mul_one, hsq]
            _ = (1 + op g) * projectorAux gs := by rw [add_comm]
      | inr htail =>
          have hgh : op h * op g = op g * op h :=
            hcomm h (mem_cons_tail htail) g (List.mem_cons_self)
          have hghs : ∀ u ∈ gs, ∀ v ∈ gs, op u * op v = op v * op u := by
            intro u hu v hv
            exact hcomm u (mem_cons_tail hu) v (mem_cons_tail hv)
          have hgs_herm : ∀ k ∈ gs, IsHermitianPauli k :=
            fun k hk => hherm k (mem_cons_tail hk)
          have ih' : op h * projectorAux gs = projectorAux gs := ih hgs_herm hghs htail
          congr 1
          calc op h * ((1 + op g) * projectorAux gs)
              = (op h * (1 + op g)) * projectorAux gs := (Matrix.mul_assoc _ _ _).symm
            _ = (op h * 1 + op h * op g) * projectorAux gs := by rw [Matrix.mul_add]
            _ = (op h + op g * op h) * projectorAux gs := by rw [Matrix.mul_one, hgh]
            _ = ((1 + op g) * op h) * projectorAux gs := by
                have h2 : op h + op g * op h = (1 + op g) * op h := by
                  rw [Matrix.add_mul, Matrix.one_mul, add_comm]
                rw [h2]
            _ = (1 + op g) * (op h * projectorAux gs) := by rw [← Matrix.mul_assoc]
            _ = (1 + op g) * projectorAux gs := by rw [ih']

theorem projectorAux_sub_gen {n : ℕ} (g : PauliElem n) (gs : List (PauliElem n))
    (hg : IsHermitianPauli g) : (op g - 1) * projectorAux (g :: gs) = 0 := by
  have hsq : op g * op g = 1 := op_mul_self hg
  have hcore : (op g - 1) * (1 + op g) = 0 := by
    rw [Matrix.sub_mul]
    exact sub_eq_zero.mpr (by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, hsq,
        add_comm])
  rw [projectorAux_cons, mul_smul_matrix]
  have hz : (op g - 1) * ((1 + op g) * projectorAux gs) = 0 := by
    rw [← Matrix.mul_assoc, hcore, Matrix.zero_mul]
  rw [hz]
  ext i j
  simp only [Matrix.smul_apply, Matrix.zero_apply]
  ring

theorem projectorAux_mul_self {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) :
    projectorAux gs * projectorAux gs = projectorAux gs := by
  induction gs with
  | nil =>
      show (1 : Matrix (Reg n) (Reg n) ℂ) * 1 = 1
      rw [Matrix.mul_one]
  | cons g gs ih =>
      have hg_herm : IsHermitianPauli g := hgs.1 g (List.mem_cons_self)
      have hg_comm : ∀ k ∈ gs, op g * op k = op k * op g :=
        fun k hk => hgs.2 g (List.mem_cons_self) k (mem_cons_tail hk)
      have hgs' : CommutingHermitianPaulis gs :=
        ⟨fun k hk => hgs.1 k (mem_cons_tail hk),
         fun u hu v hv => hgs.2 u (mem_cons_tail hu) v (mem_cons_tail hv)⟩
      have ih' : projectorAux gs * projectorAux gs = projectorAux gs := ih hgs'
      have hGsq : op g * op g = 1 := op_mul_self hg_herm
      have hQP : (1 + op g) * projectorAux gs = projectorAux gs * (1 + op g) := by
        calc (1 + op g) * projectorAux gs = projectorAux gs + op g * projectorAux gs := by
              rw [Matrix.add_mul, Matrix.one_mul]
          _ = projectorAux gs + projectorAux gs * op g := by
              rw [projectorAux_comm g gs hg_comm]
          _ = projectorAux gs * (1 + op g) := by rw [Matrix.mul_add, Matrix.mul_one]
      have hQQ : (1 + op g) * (1 + op g) = (2 : ℂ) • (1 + op g) := addOne_sq _ hGsq
      have key : (1 + op g) * projectorAux gs * ((1 + op g) * projectorAux gs)
          = ((1 + op g) * (1 + op g)) * (projectorAux gs * projectorAux gs) := by
        calc (1 + op g) * projectorAux gs * ((1 + op g) * projectorAux gs)
            = (1 + op g) * (projectorAux gs * ((1 + op g) * projectorAux gs)) :=
              Matrix.mul_assoc (1 + op g) (projectorAux gs) ((1 + op g) * projectorAux gs)
            _ = (1 + op g) * ((projectorAux gs * (1 + op g)) * projectorAux gs) := by
              congr 1
              rw [← Matrix.mul_assoc]
            _ = (1 + op g) * (((1 + op g) * projectorAux gs) * projectorAux gs) := by
              congr 1
              rw [← hQP]
            _ = (1 + op g) * ((1 + op g) * (projectorAux gs * projectorAux gs)) := by
              congr 1
              rw [← Matrix.mul_assoc]
            _ = ((1 + op g) * (1 + op g)) * (projectorAux gs * projectorAux gs) :=
              (Matrix.mul_assoc (1 + op g) (1 + op g) (projectorAux gs * projectorAux gs)).symm
      have hstep : ((2 : ℂ) • (1 + op g)) * projectorAux gs = (2 : ℂ) • ((1 + op g) * projectorAux gs) :=
        smul_mul_matrix _ _ _
      rw [projectorAux_cons, smul_mul_matrix, mul_smul_matrix, smul_smul_matrix, key, hQQ, ih',
        hstep]
      ext i j
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [half_half_two_mul]

theorem projectorAux_star {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) :
    (projectorAux gs)ᴴ = projectorAux gs := by
  induction gs with
  | nil =>
      show (1 : Matrix (Reg n) (Reg n) ℂ)ᴴ = 1
      rw [Matrix.conjTranspose_one]
  | cons g gs ih =>
      have hg_herm : IsHermitianPauli g := hgs.1 g (List.mem_cons_self)
      have hg_comm : ∀ k ∈ gs, op g * op k = op k * op g :=
        fun k hk => hgs.2 g (List.mem_cons_self) k (mem_cons_tail hk)
      have hgs' : CommutingHermitianPaulis gs :=
        ⟨fun k hk => hgs.1 k (mem_cons_tail hk),
         fun u hu v hv => hgs.2 u (mem_cons_tail hu) v (mem_cons_tail hv)⟩
      have ih' : (projectorAux gs)ᴴ = projectorAux gs := ih hgs'
      have hGherm : (op g)ᴴ = op g := op_conjTranspose_herm hg_herm
      have hQP : (1 + op g) * projectorAux gs = projectorAux gs * (1 + op g) := by
        calc (1 + op g) * projectorAux gs = projectorAux gs + op g * projectorAux gs := by
              rw [Matrix.add_mul, Matrix.one_mul]
          _ = projectorAux gs + projectorAux gs * op g := by
              rw [projectorAux_comm g gs hg_comm]
          _ = projectorAux gs * (1 + op g) := by rw [Matrix.mul_add, Matrix.mul_one]
      have hQstar : (1 + op g)ᴴ = 1 + op g := addOne_star _ hGherm
      rw [projectorAux_cons, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul,
        ih', hQstar, conj_half, hQP]

theorem projectorAux_isOrthogonalProjector {n : ℕ} (gs : List (PauliElem n))
    (hgs : CommutingHermitianPaulis gs) : IsOrthogonalProjector (projectorAux gs) := by
  show IsStarProjection (projectorAux gs)
  rw [isStarProjection_iff']
  refine ⟨projectorAux_mul_self gs hgs, ?_⟩
  rw [Matrix.star_eq_conjTranspose]
  exact projectorAux_star gs hgs

theorem projectorAux_mulVec_iff {n : ℕ} (gs : List (PauliElem n))
    (hherm : ∀ h ∈ gs, IsHermitianPauli h)
    (hcomm : ∀ u ∈ gs, ∀ v ∈ gs, op u * op v = op v * op u)
    (ψ : QState (Reg n)) :
    projectorAux gs *ᵥ ψ = ψ ↔ ∀ h ∈ gs, op h *ᵥ ψ = ψ := by
  induction gs with
  | nil =>
      constructor
      · intro _
        intro h hx
        cases hx
      · intro _
        show (1 : Matrix (Reg n) (Reg n) ℂ) *ᵥ ψ = ψ
        rw [Matrix.one_mulVec]
  | cons g gs ih =>
      have hgs_herm : ∀ k ∈ gs, IsHermitianPauli k := fun k hk => hherm k (mem_cons_tail hk)
      have hgs_comm : ∀ u ∈ gs, ∀ v ∈ gs, op u * op v = op v * op u := by
        intro u hu v hv
        exact hcomm u (mem_cons_tail hu) v (mem_cons_tail hv)
      have ih' : projectorAux gs *ᵥ ψ = ψ ↔ ∀ h ∈ gs, op h *ᵥ ψ = ψ :=
        ih hgs_herm hgs_comm
      constructor
      · intro hP
        intro h hh
        have hgen : op h * projectorAux (g :: gs) = projectorAux (g :: gs) :=
          projectorAux_mul_gen (g :: gs) hherm hcomm h hh
        calc op h *ᵥ ψ = op h *ᵥ (projectorAux (g :: gs) *ᵥ ψ) := by rw [hP]
          _ = (op h * projectorAux (g :: gs)) *ᵥ ψ :=
            Matrix.mulVec_mulVec ψ (op h) (projectorAux (g :: gs))
          _ = projectorAux (g :: gs) *ᵥ ψ := by rw [hgen]
          _ = ψ := hP
      · intro hall
        have hfix : op g *ᵥ ψ = ψ := hall g (List.mem_cons_self)
        have htail : projectorAux gs *ᵥ ψ = ψ :=
          (ih').mpr fun h hh => hall h (mem_cons_tail hh)
        rw [projectorAux_cons, smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
          Matrix.one_mulVec]
        simp only [htail]
        rw [hfix]
        funext x
        simp only [Pi.smul_apply, Pi.add_apply]
        calc ((2 : ℂ)⁻¹) * (ψ x + ψ x) = ((2 : ℂ)⁻¹) * (2 * ψ x) := by ring
          _ = ((2 : ℂ)⁻¹ * 2) * ψ x := by ring
          _ = ψ x := by rw [half_mul_two]; ring

theorem mem_codeSpace_iff {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n)) :
    ψ ∈ codeSpace t ↔ ∀ a, op (t a).decode *ᵥ ψ = ψ := by
  rfl

theorem mem_tableauGenerators {n m : ℕ} (t : Tableau n m) (h : PauliElem n) :
    h ∈ tableauGenerators t ↔ ∃ a : Fin m, (t a).decode = h := by
  rw [tableauGenerators, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, List.mem_finRange a, rfl⟩

theorem stabilizerProjector_mem_codeSpace {n m : ℕ} (t : Tableau n m)
    (ht : ConsistentTableau t) (ψ : QState (Reg n)) :
    ψ ∈ codeSpace t ↔ stabilizerProjector (tableauGenerators t) *ᵥ ψ = ψ := by
  have hherm : ∀ h ∈ tableauGenerators t, IsHermitianPauli h := by
    intro h hh
    obtain ⟨a, rfl⟩ := (mem_tableauGenerators t h).mp hh
    exact ht.1 a
  have hcomm : ∀ u ∈ tableauGenerators t, ∀ v ∈ tableauGenerators t,
      op u * op v = op v * op u := by
    intro u hu v hv
    obtain ⟨a, rfl⟩ := (mem_tableauGenerators t u).mp hu
    obtain ⟨b, rfl⟩ := (mem_tableauGenerators t v).mp hv
    exact ht.2 a b
  have hrow : (∀ a, op (t a).decode *ᵥ ψ = ψ)
      ↔ (∀ h ∈ tableauGenerators t, op h *ᵥ ψ = ψ) := by
    constructor
    · intro h h' hh'
      obtain ⟨a, rfl⟩ := (mem_tableauGenerators t h').mp hh'
      exact h a
    · intro h a
      exact h (t a).decode ((mem_tableauGenerators t _).mpr ⟨a, rfl⟩)
  have hmain : (∀ h ∈ tableauGenerators t, op h *ᵥ ψ = ψ)
      ↔ stabilizerProjector (tableauGenerators t) *ᵥ ψ = ψ :=
    (projectorAux_mulVec_iff (tableauGenerators t) hherm hcomm ψ).symm
  rw [mem_codeSpace_iff]
  exact hrow.trans hmain

theorem amplitudeFn_stateOfFn {n : ℕ} (f : BooleanVec n → ℂ) :
    amplitudeFn (stateOfFn f) = f := by
  funext x
  change f (regToVec (vecToReg x)) = f x
  have hx : regToVec (vecToReg x) = x := regVecEquiv.right_inv x
  rw [hx]

theorem stateOfFn_amplitudeFn {n : ℕ} (ψ : QState (Reg n)) :
    stateOfFn (amplitudeFn ψ) = ψ := by
  funext r
  have hr : vecToReg (regToVec r) = r := regVecEquiv.left_inv r
  show ψ (vecToReg (regToVec r)) = ψ r
  rw [hr]

theorem stateOfFn_smul {n : ℕ} (lam : ℂ) (f : BooleanVec n → ℂ) :
    stateOfFn (fun x => lam * f x) = lam • stateOfFn f := by
  funext r
  rfl

theorem neg_one_eq_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (-1 : Matrix ι ι ℂ) = ((-1 : ℂ) • 1) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, if_pos rfl]
    ring
  · simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, if_neg hij]
    ring

theorem neg_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    (-1 : ℂ) • M = -M := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, if_pos rfl]
    ring
  · simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply, if_neg hij]
    ring

theorem one_add_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (1 : Matrix ι ι ℂ) + (-1 : Matrix ι ι ℂ) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.zero_apply, if_pos rfl]
    ring
  · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.neg_apply, Matrix.zero_apply, if_neg hij]
    ring

theorem mul_neg_one {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) : M * -1 = -M := by
  rw [neg_one_eq_smul_one, mul_smul_matrix, Matrix.mul_one, neg_smul, one_smul]

theorem op_minusI {n : ℕ} : op (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n) = -1 := by
  rw [op_trivial_word, zmod4_val_two, I_pow_two, neg_one_eq_smul_one, neg_smul, one_smul]

theorem projectorAux_eq_zero_of_minusI {n : ℕ} (gs : List (PauliElem n))
    (h : (⟨fun _ => Pauli1.I, 2⟩ : PauliElem n) ∈ gs) : projectorAux gs = 0 := by
  induction gs with
  | nil => cases h
  | cons g gs ih =>
      rw [projectorAux_cons]
      cases List.mem_cons.mp h with
      | inl heq =>
          subst heq
          rw [op_minusI, one_add_neg_one]
          ext i j
          simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.zero_apply]
      | inr htail =>
          have hz : projectorAux gs = 0 := ih htail
          rw [hz]
          ext i j
          simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.zero_apply]

theorem pauliBranchProjector_compl {n : ℕ} (p : PauliElem n) :
    1 - pauliBranchProjector p true = pauliBranchProjector p false := by
  ext i j
  simp only [pauliBranchProjector, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    ring
  · simp only [if_neg hij]
    ring

theorem op_p_branchProjector_true {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) :
    op p * pauliBranchProjector p true = (1 : ℂ) • pauliBranchProjector p true := by
  have hsq : op p * op p = 1 := op_mul_self hp
  show op p * (((2 : ℂ)⁻¹) • (1 + op p)) = 1 • (((2 : ℂ)⁻¹) • (1 + op p))
  rw [mul_smul_matrix, Matrix.mul_add, Matrix.mul_one, hsq, one_smul]
  congr 1
  rw [add_comm]

theorem op_p_branchProjector_false {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) :
    op p * pauliBranchProjector p false = (-1 : ℂ) • pauliBranchProjector p false := by
  have hsq : op p * op p = 1 := op_mul_self hp
  show op p * (((2 : ℂ)⁻¹) • (1 - op p)) = (-1) • (((2 : ℂ)⁻¹) • (1 - op p))
  rw [mul_smul_matrix, Matrix.mul_sub, Matrix.mul_one, hsq]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem op_feedbackRow {n : ℕ} (p : PauliElem n) (b : Bool) :
    op (feedbackRow p b).decode = if b then op p else -op p := by
  cases b with
  | true =>
      show op (encode p).decode = op p
      rw [decode_encode]
  | false =>
      show op ((encode p).mul (minusIRow n)).decode = -op p
      rw [minusIRow, row_mul_op, decode_encode, minusI_op, mul_neg_one]

theorem op_feedbackRow_branch {n : ℕ} (p : PauliElem n) (hp : IsHermitianPauli p) (b : Bool)
    (ψ : QState (Reg n)) :
    op (feedbackRow p b).decode *ᵥ (pauliBranchProjector p b *ᵥ ψ) = pauliBranchProjector p b *ᵥ ψ := by
  cases b with
  | true =>
      show op (encode p).decode *ᵥ (pauliBranchProjector p true *ᵥ ψ)
        = pauliBranchProjector p true *ᵥ ψ
      rw [decode_encode, Matrix.mulVec_mulVec, op_p_branchProjector_true p hp, smul_mulVec,
        one_smul]
  | false =>
      show op ((encode p).mul (minusIRow n)).decode *ᵥ (pauliBranchProjector p false *ᵥ ψ)
        = pauliBranchProjector p false *ᵥ ψ
      rw [minusIRow, row_mul_op, decode_encode, minusI_op, mul_neg_one, Matrix.neg_mulVec,
        Matrix.mulVec_mulVec, op_p_branchProjector_false p hp, smul_mulVec, neg_smul, one_smul]
      funext x
      simp only [Pi.neg_apply]
      ring

theorem op_row_comm_branch {n : ℕ} (c : PauliElem n) (p : PauliElem n) (b : Bool)
    (hcomm : op c * op p = op p * op c) :
    op c * pauliBranchProjector p b = pauliBranchProjector p b * op c := by
  cases b with
  | true =>
      show op c * (((2 : ℂ)⁻¹) • (1 + op p)) = (((2 : ℂ)⁻¹) • (1 + op p)) * op c
      rw [mul_smul_matrix, smul_mul_matrix, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
        Matrix.one_mul, hcomm]
  | false =>
      show op c * (((2 : ℂ)⁻¹) • (1 - op p)) = (((2 : ℂ)⁻¹) • (1 - op p)) * op c
      rw [mul_smul_matrix, smul_mul_matrix, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
        Matrix.one_mul, hcomm]

theorem mem_feedback_codeSpace_true {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (a : Fin m) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hcomm : ∀ c, c ≠ a → op (t c).decode * op p = op p * op (t c).decode) :
    ProjectiveBranch (pauliBranchProjector p true) true ψ ∈ codeSpace (feedbackTableau t a p true) := by
  have hbr : ProjectiveBranch (pauliBranchProjector p true) true ψ
      = pauliBranchProjector p true *ᵥ ψ := rfl
  rw [mem_codeSpace_iff]
  intro c
  by_cases hc : c = a
  · subst c
    rw [feedbackTableau, if_pos rfl, hbr]
    exact op_feedbackRow_branch p hp true ψ
  · rw [feedbackTableau, if_neg hc, hbr]
    have hswap : op (t c).decode * pauliBranchProjector p true
        = pauliBranchProjector p true * op (t c).decode :=
      op_row_comm_branch (t c).decode p true (hcomm c hc)
    have hstep : op (t c).decode *ᵥ (pauliBranchProjector p true *ᵥ ψ)
        = (op (t c).decode * pauliBranchProjector p true) *ᵥ ψ :=
      Matrix.mulVec_mulVec ψ (op (t c).decode) (pauliBranchProjector p true)
    rw [hstep, hswap]
    have hfix : op (t c).decode *ᵥ ψ = ψ := (mem_codeSpace_iff t ψ).mp hψ c
    rw [← Matrix.mulVec_mulVec, hfix]

theorem mem_feedback_codeSpace_false {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (a : Fin m) (p : PauliElem n) (hp : IsHermitianPauli p)
    (hcomm : ∀ c, c ≠ a → op (t c).decode * op p = op p * op (t c).decode) :
    ProjectiveBranch (pauliBranchProjector p true) false ψ ∈
      codeSpace (feedbackTableau t a p false) := by
  have hbr : ProjectiveBranch (pauliBranchProjector p true) false ψ
      = pauliBranchProjector p false *ᵥ ψ := by
    show ApplyGate (1 - pauliBranchProjector p true) ψ = pauliBranchProjector p false *ᵥ ψ
    rw [pauliBranchProjector_compl]
    rfl
  rw [mem_codeSpace_iff]
  intro c
  by_cases hc : c = a
  · subst c
    rw [feedbackTableau, if_pos rfl, hbr]
    exact op_feedbackRow_branch p hp false ψ
  · rw [feedbackTableau, if_neg hc, hbr]
    have hswap : op (t c).decode * pauliBranchProjector p false
        = pauliBranchProjector p false * op (t c).decode :=
      op_row_comm_branch (t c).decode p false (hcomm c hc)
    have hstep : op (t c).decode *ᵥ (pauliBranchProjector p false *ᵥ ψ)
        = (op (t c).decode * pauliBranchProjector p false) *ᵥ ψ :=
      Matrix.mulVec_mulVec ψ (op (t c).decode) (pauliBranchProjector p false)
    rw [hstep, hswap]
    have hfix : op (t c).decode *ᵥ ψ = ψ := (mem_codeSpace_iff t ψ).mp hψ c
    rw [← Matrix.mulVec_mulVec, hfix]

theorem pauliBranchProjector_isOrthogonalProjector {n : ℕ} {p : PauliElem n}
    (hp : IsHermitianPauli p) (b : Bool) :
    IsOrthogonalProjector (pauliBranchProjector p b) := by
  show IsStarProjection (pauliBranchProjector p b)
  rw [isStarProjection_iff']
  have hsq : op p * op p = 1 := op_mul_self hp
  have hherm : (op p)ᴴ = op p := op_conjTranspose_herm hp
  have hone : (1 : Matrix (Reg n) (Reg n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  cases b with
  | false =>
      refine ⟨?_, ?_⟩
      · have hNN : (1 - op p) * (1 - op p) = (1 - op p) + (1 - op p) := by
          have h1 : (1 - op p) * (1 - op p) = 1 * (1 - op p) - op p * (1 - op p) :=
            Matrix.sub_mul _ _ _
          have h2 : op p * (1 - op p) = op p * 1 - op p * op p := Matrix.mul_sub _ _ _
          rw [h1, h2, Matrix.mul_one, Matrix.one_mul, hsq]
          abel
        have hsm : pauliBranchProjector p false * pauliBranchProjector p false
            = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((1 - op p) * (1 - op p)) := by
          exact smul_mul_smul' _ _ _ _
        rw [hsm, hNN, half_smul_add]
        rfl
      · rw [Matrix.star_eq_conjTranspose, pauliBranchProjector, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_sub, hone, hherm, conj_half]
  | true =>
      refine ⟨?_, ?_⟩
      · have hNN : (1 + op p) * (1 + op p) = (1 + op p) + (1 + op p) := by
          have h1 : (1 + op p) * (1 + op p) = 1 * (1 + op p) + op p * (1 + op p) :=
            Matrix.add_mul _ _ _
          have h2 : op p * (1 + op p) = op p * 1 + op p * op p := Matrix.mul_add _ _ _
          rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hsq]
          abel
        have hsm : pauliBranchProjector p true * pauliBranchProjector p true
            = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((1 + op p) * (1 + op p)) := by
          show (((2 : ℂ)⁻¹) • (1 + op p)) * (((2 : ℂ)⁻¹) • (1 + op p))
            = ((2 : ℂ)⁻¹ * (2 : ℂ)⁻¹) • ((1 + op p) * (1 + op p))
          exact smul_mul_smul' _ _ _ _
        rw [hsm, hNN, half_smul_add]
        rfl
      · rw [Matrix.star_eq_conjTranspose, pauliBranchProjector, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_add, hone, hherm, conj_half]

theorem op_anticommute {n : ℕ} (p q : PauliElem n)
    (hanti : op p * op q = - (op q * op p)) : op p * op q = - (op q * op p) := hanti

theorem pauliBranchProjector_add {n : ℕ} (p : PauliElem n) :
    pauliBranchProjector p true + pauliBranchProjector p false = 1 := by
  ext i j
  simp only [pauliBranchProjector, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
    smul_eq_mul]
  have hone : (1 : Matrix (Reg n) (Reg n) ℂ) i j = if i = j then 1 else 0 := Matrix.one_apply
  by_cases hij : i = j
  · rw [hone, if_pos hij]
    calc ((2 : ℂ)⁻¹) * (1 + op p i j) + ((2 : ℂ)⁻¹) * (1 - op p i j)
        = ((2 : ℂ)⁻¹) + ((2 : ℂ)⁻¹) * op p i j + ((2 : ℂ)⁻¹) - ((2 : ℂ)⁻¹) * op p i j := by
          ring
      _ = ((2 : ℂ)⁻¹) + ((2 : ℂ)⁻¹) := by ring
      _ = 1 := half_add_half
  · rw [hone, if_neg hij]
    calc ((2 : ℂ)⁻¹) * (0 + op p i j) + ((2 : ℂ)⁻¹) * (0 - op p i j)
        = ((2 : ℂ)⁻¹) * op p i j + (0 - ((2 : ℂ)⁻¹) * op p i j) := by ring
      _ = 0 := by ring

theorem anticommute_branch_swap {n : ℕ} (A p : PauliElem n)
    (hanti : op A * op p = - (op p * op A)) :
    op A * pauliBranchProjector p true = pauliBranchProjector p false * op A := by
  have h1 : op A * (((2 : ℂ)⁻¹) • (1 + op p)) = ((2 : ℂ)⁻¹) • (op A * (1 + op p)) :=
    mul_smul_matrix _ _ _
  have h2 : op A * (1 + op p) = op A * 1 + op A * op p := Matrix.mul_add _ _ _
  have h3 : op A * op p = - (op p * op A) := hanti
  have h4 : op A + - (op p * op A) = op A - op p * op A := by abel
  have h5 : op A - op p * op A = (1 - op p) * op A := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  have h6 : ((2 : ℂ)⁻¹) • ((1 - op p) * op A) = (((2 : ℂ)⁻¹) • (1 - op p)) * op A :=
    (smul_mul_matrix _ _ _).symm
  rw [pauliBranchProjector, pauliBranchProjector, h1, h2, Matrix.mul_one, h3, h4, h5, h6]

theorem pauliBranch_equiprobable {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (a : Fin m)
    (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : op (t a).decode * op p = - (op p * op (t a).decode)) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = MeasureProb ψ Finset.univ / 2 ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = MeasureProb ψ Finset.univ / 2 := by
  have hrow : op (t a).decode *ᵥ ψ = ψ := hψ a
  have hswap := anticommute_branch_swap (t a).decode p hanti
  have hu : op (t a).decode *ᵥ (pauliBranchProjector p true *ᵥ ψ)
      = pauliBranchProjector p false *ᵥ ψ := by
    calc op (t a).decode *ᵥ (pauliBranchProjector p true *ᵥ ψ)
        = (op (t a).decode * pauliBranchProjector p true) *ᵥ ψ :=
          Matrix.mulVec_mulVec ψ (op (t a).decode) (pauliBranchProjector p true)
      _ = (pauliBranchProjector p false * op (t a).decode) *ᵥ ψ := by rw [hswap]
      _ = pauliBranchProjector p false *ᵥ (op (t a).decode *ᵥ ψ) :=
        (Matrix.mulVec_mulVec ψ (pauliBranchProjector p false) (op (t a).decode)).symm
      _ = pauliBranchProjector p false *ᵥ ψ := by rw [hrow]
  have hmass : MeasureProb (pauliBranchProjector p true *ᵥ ψ) Finset.univ
      = MeasureProb (pauliBranchProjector p false *ᵥ ψ) Finset.univ := by
    have h := measureProb_applyGate_univ (op_unitary (t a).decode)
      (pauliBranchProjector p true *ᵥ ψ)
    rw [ApplyGate, hu] at h
    exact h.symm
  have hcompl : 1 - pauliBranchProjector p true = pauliBranchProjector p false := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact (pauliBranchProjector_add p).symm
  have hplus : ProjectiveBranchMass (pauliBranchProjector p true) true ψ
      = MeasureProb (pauliBranchProjector p true *ᵥ ψ) Finset.univ := by
    have hbr : ProjectiveBranch (pauliBranchProjector p true) true ψ
        = pauliBranchProjector p true *ᵥ ψ := by
      show ApplyGate (if true then pauliBranchProjector p true
          else 1 - pauliBranchProjector p true) ψ
        = pauliBranchProjector p true *ᵥ ψ
      rfl
    simp only [ProjectiveBranchMass]
    rw [hbr]
  have hminus : ProjectiveBranchMass (pauliBranchProjector p true) false ψ
      = MeasureProb (pauliBranchProjector p false *ᵥ ψ) Finset.univ := by
    have hbr : ProjectiveBranch (pauliBranchProjector p true) false ψ
        = pauliBranchProjector p false *ᵥ ψ := by
      show ApplyGate (if false then pauliBranchProjector p true
          else 1 - pauliBranchProjector p true) ψ
        = pauliBranchProjector p false *ᵥ ψ
      rw [hcompl]
      rfl
    simp only [ProjectiveBranchMass]
    rw [hbr]
  have hsum := projectiveBranchMass_add (pauliBranchProjector_isOrthogonalProjector hp true) ψ
  rw [hplus, hminus] at hsum
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

theorem pauliBranchMass_fairBit {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (hn : Normalized ψ) (a : Fin m)
    (p : PauliElem n) (hp : IsHermitianPauli p)
    (hanti : op (t a).decode * op p = - (op p * op (t a).decode)) :
    ProjectiveBranchMass (pauliBranchProjector p true) true ψ = fairBitLaw.prob true ∧
      ProjectiveBranchMass (pauliBranchProjector p true) false ψ = fairBitLaw.prob false := by
  obtain ⟨hplus, hminus⟩ :=
    pauliBranch_equiprobable t ψ hψ a p hp hanti
  refine ⟨?_, ?_⟩
  · rw [hplus]
    rw [MeasureProb, bornProb_sum_eq_one hn]
    norm_num [fairBitLaw]
  · rw [hminus]
    rw [MeasureProb, bornProb_sum_eq_one hn]
    norm_num [fairBitLaw]

theorem pauliBranch_deterministic {n m : ℕ} (t : Tableau n m) (ψ : QState (Reg n))
    (hψ : ψ ∈ codeSpace t) (a : Fin m) (hherm : IsHermitianPauli (t a).decode) :
    ProjectiveBranchMass (pauliBranchProjector (t a).decode true) true ψ = MeasureProb ψ Finset.univ ∧
      ProjectiveBranchMass (pauliBranchProjector (t a).decode true) false ψ = 0 := by
  have hrow : op (t a).decode *ᵥ ψ = ψ := hψ a
  have hplus : pauliBranchProjector (t a).decode true *ᵥ ψ = ψ := by
    have hstep : pauliBranchProjector (t a).decode true *ᵥ ψ
        = ((2 : ℂ)⁻¹) • ((1 + op (t a).decode) *ᵥ ψ) := by
      rw [pauliBranchProjector]
      exact smul_mulVec _ _ _
    rw [hstep, Matrix.add_mulVec, Matrix.one_mulVec, hrow]
    funext x
    simp only [Pi.smul_apply, Pi.add_apply]
    calc ((2 : ℂ)⁻¹) * (ψ x + ψ x) = ((2 : ℂ)⁻¹) * (2 * ψ x) := by ring
      _ = ((2 : ℂ)⁻¹ * 2) * ψ x := by ring
      _ = ψ x := by rw [half_mul_two]; ring
  refine ⟨?_, ?_⟩
  · have hbranch : ProjectiveBranch (pauliBranchProjector (t a).decode true) true ψ = ψ := by
      rw [ProjectiveBranch]
      exact hplus
    simp only [ProjectiveBranchMass]
    rw [hbranch]
  · have hsum := projectiveBranchMass_add
      (pauliBranchProjector_isOrthogonalProjector hherm true) ψ
    have hplusmass : ProjectiveBranchMass (pauliBranchProjector (t a).decode true) true ψ
        = MeasureProb ψ Finset.univ := by
      have hbranch : ProjectiveBranch (pauliBranchProjector (t a).decode true) true ψ = ψ := by
        rw [ProjectiveBranch]
        exact hplus
      simp only [ProjectiveBranchMass]
      rw [hbranch]
    rw [hplusmass] at hsum
    linarith

end Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
