/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Lean.Elab.Tactic.NormCast
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs

namespace Qatlib.Foundations.PureStateMath

open Matrix
open scoped Matrix

set_option linter.unusedSectionVars false

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Reg (n : ℕ) := Fin n → Bool

def ZeroStr (n : ℕ) : Reg n := fun _ => false

theorem card_reg (n : ℕ) : Fintype.card (Reg n) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

def boolEquivFin2 : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun k := if k = 0 then false else true
  left_inv b := by cases b <;> rfl
  right_inv k := by fin_cases k <;> rfl

def regSuccEquiv (n : ℕ) : Reg (n + 1) ≃ Reg n × Bool := Fin.succFunEquiv Bool n

def bitVecEquiv : (n : ℕ) → Reg n ≃ Fin (2 ^ n)
  | 0 => Equiv.ofUnique (Reg 0) (Fin 1)
  | n + 1 =>
    (regSuccEquiv n).trans
      ((Equiv.prodCongr (bitVecEquiv n) boolEquivFin2).trans
        (finProdFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.pow_succ 2 n).symm))))

@[simp] theorem bitVecEquiv_zero (x : Reg 0) : bitVecEquiv 0 x = 0 := by
  haveI : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
  exact Subsingleton.elim _ _

theorem bitVecEquiv_zeroStr (n : ℕ) : bitVecEquiv n (ZeroStr n) = 0 := by
  induction n with
  | zero =>
    haveI : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
    exact Subsingleton.elim _ _
  | succ n ih =>
    have h2 : bitVecEquiv (n + 1) (ZeroStr (n + 1))
        = Equiv.cast (congrArg Fin (Nat.pow_succ 2 n).symm)
            (finProdFinEquiv ((Equiv.prodCongr (bitVecEquiv n) boolEquivFin2)
              (regSuccEquiv n (ZeroStr (n + 1))))) := rfl
    have h1 : regSuccEquiv n (ZeroStr (n + 1)) = (ZeroStr n, false) := rfl
    rw [h2, h1]
    show (Equiv.cast (congrArg Fin (Nat.pow_succ 2 n).symm))
        (finProdFinEquiv (bitVecEquiv n (ZeroStr n), boolEquivFin2 false)) = 0
    rw [ih]
    apply Fin.val_injective
    have h3 : ∀ (e : 2 ^ n * 2 = 2 ^ (n + 1)) (y : Fin (2 ^ n * 2)),
        ((Equiv.cast (congrArg Fin e)) y).val = y.val := by
      intro e y; cases e; rfl
    rw [h3 (Nat.pow_succ 2 n).symm]
    simp [finProdFinEquiv, boolEquivFin2]

theorem bitVecEquiv_symm_zero (n : ℕ) : (bitVecEquiv n).symm 0 = ZeroStr n := by
  rw [Equiv.symm_apply_eq]
  exact (bitVecEquiv_zeroStr n).symm

abbrev QState (I : Type*) := I → ℂ

def Ket (i : I) : QState I := fun j => if j = i then 1 else 0

@[simp] theorem ket_self (i : I) : Ket i i = 1 := by simp [Ket]

theorem ket_apply (i j : I) : Ket i j = if j = i then 1 else 0 := rfl

theorem ket_ne {i j : I} (h : j ≠ i) : Ket i j = 0 := by simp [Ket, h]

noncomputable def Normalized (ψ : QState I) : Prop := ∑ i, ‖ψ i‖ ^ 2 = 1

noncomputable def BornProb (ψ : QState I) (i : I) : ℝ := ‖ψ i‖ ^ 2

theorem bornProb_nonneg (ψ : QState I) (i : I) : 0 ≤ BornProb ψ i := by
  unfold BornProb; positivity

theorem bornProb_ket (i j : I) : BornProb (Ket i) j = if j = i then 1 else 0 := by
  unfold BornProb Ket; split_ifs <;> simp

theorem normalized_ket (i : I) : Normalized (Ket i) := by
  unfold Normalized
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ket, hj]) (by simp)]
  simp

theorem bornProb_sum_eq_one {ψ : QState I} (hψ : Normalized ψ) : ∑ i, BornProb ψ i = 1 := hψ

noncomputable def MeasureProb (ψ : QState I) (S : Finset I) : ℝ := ∑ i ∈ S, BornProb ψ i

theorem measureProb_nonneg (ψ : QState I) (S : Finset I) : 0 ≤ MeasureProb ψ S :=
  Finset.sum_nonneg fun i _ => bornProb_nonneg ψ i

theorem measureProb_univ {ψ : QState I} (hψ : Normalized ψ) :
    MeasureProb ψ Finset.univ = 1 := hψ

noncomputable def Uniform (I : Type*) [Fintype I] : QState I :=
  fun _ => (Real.sqrt (Fintype.card I) : ℂ)⁻¹

theorem normalized_uniform (hN : 0 < Fintype.card I) : Normalized (Uniform I) := by
  have hpos : (0 : ℝ) < (Fintype.card I : ℝ) := Nat.cast_pos.mpr hN
  have hsqrt : (0 : ℝ) < Real.sqrt (Fintype.card I) := Real.sqrt_pos_of_pos hpos
  unfold Normalized Uniform
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : ‖((Real.sqrt (Fintype.card I) : ℂ))⁻¹‖ = (Real.sqrt (Fintype.card I))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsqrt.le]
  rw [h1, inv_pow, Real.sq_sqrt hpos.le, mul_inv_cancel₀ hpos.ne']

noncomputable def ApplyGate (U : Matrix I I ℂ) (ψ : QState I) : QState I := U.mulVec ψ

@[simp] theorem applyGate_one (ψ : QState I) : ApplyGate 1 ψ = ψ := by
  unfold ApplyGate; simp

theorem applyGate_mul (U V : Matrix I I ℂ) (ψ : QState I) :
    ApplyGate (U * V) ψ = ApplyGate U (ApplyGate V ψ) := by
  unfold ApplyGate; rw [Matrix.mulVec_mulVec]

theorem sum_mul_conj_mulVec_of_mem_unitaryGroup {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    (∑ i, (U *ᵥ ψ) i * (starRingEnd ℂ) ((U *ᵥ ψ) i)) = ∑ j, ψ j * (starRingEnd ℂ) (ψ j) := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
  have hUU : ∀ j k : I, (∑ i, (starRingEnd ℂ) (U i k) * U i j) = if k = j then (1 : ℂ) else 0 := by
    intro j k
    have heq : (∑ i, (starRingEnd ℂ) (U i k) * U i j) = (Uᴴ * U) k j := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def]
    rw [heq, hU, Matrix.one_apply]
  calc ∑ i, (U *ᵥ ψ) i * (starRingEnd ℂ) ((U *ᵥ ψ) i)
      = ∑ i, (∑ j, U i j * ψ j) * ∑ k, (starRingEnd ℂ) (U i k) * (starRingEnd ℂ) (ψ k) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    _ = ∑ i, ∑ j, ∑ k, (U i j * ψ j) * ((starRingEnd ℂ) (U i k) * (starRingEnd ℂ) (ψ k)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ = ∑ j, ∑ k, ∑ i, (U i j * ψ j) * ((starRingEnd ℂ) (U i k) * (starRingEnd ℂ) (ψ k)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        exact Finset.sum_comm
    _ = ∑ j, ∑ k, (ψ j * (starRingEnd ℂ) (ψ k)) * ∑ i, (starRingEnd ℂ) (U i k) * U i j := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ∑ j, ∑ k, (ψ j * (starRingEnd ℂ) (ψ k)) * (if k = j then (1 : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        rw [hUU j k]
    _ = ∑ j, ψ j * (starRingEnd ℂ) (ψ j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_eq_single j (fun k _ hkj => by rw [if_neg hkj, mul_zero])
          (fun h => absurd (Finset.mem_univ j) h)]
        rw [if_pos rfl, mul_one]

theorem sum_normSq_mulVec_of_mem_unitaryGroup {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ : QState I) :
    ∑ i, Complex.normSq ((U *ᵥ ψ) i) = ∑ j, Complex.normSq (ψ j) := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj]
  exact sum_mul_conj_mulVec_of_mem_unitaryGroup hU ψ

theorem normalized_applyGate {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ)
    {ψ : QState I} (hψ : Normalized ψ) : Normalized (ApplyGate U ψ) := by
  unfold Normalized at hψ ⊢
  unfold ApplyGate
  rw [← hψ]
  simp_rw [← Complex.normSq_eq_norm_sq]
  exact sum_normSq_mulVec_of_mem_unitaryGroup hU ψ

def permMatrix (σ : I → I) : Matrix I I ℂ := Matrix.of fun i j => if i = σ j then (1 : ℂ) else 0

theorem permMatrix_mul_self {σ : I → I} (hσ : Function.Involutive σ) :
    permMatrix σ * permMatrix σ = 1 := by
  ext i j
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ j) (fun k _ hk => by rw [if_neg hk, mul_zero])
    (fun h => absurd (Finset.mem_univ (σ j)) h)]
  simp [hσ j]

theorem permMatrix_conjTranspose {σ : I → I} (hσ : Function.Involutive σ) :
    (permMatrix σ)ᴴ = permMatrix σ := by
  ext i j
  simp only [permMatrix, Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def]
  by_cases hji : j = σ i
  · have hij : i = σ j := by rw [← hσ i, ← hji]
    rw [if_pos hji, if_pos hij, map_one]
  · have hij : i ≠ σ j := fun e => hji (by rw [← hσ j, ← e])
    rw [if_neg hji, if_neg hij, map_zero]

theorem permMatrix_unitary {σ : I → I} (hσ : Function.Involutive σ) :
    permMatrix σ ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, permMatrix_conjTranspose hσ]
  exact permMatrix_mul_self hσ

theorem applyGate_permMatrix {σ : I → I} (hσ : Function.Involutive σ) (ψ : QState I) (i : I) :
    ApplyGate (permMatrix σ) ψ i = ψ (σ i) := by
  simp only [ApplyGate, permMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ i)]
  · rw [hσ i]
    simp
  · intro j _ hj
    have hne : i ≠ σ j := fun h => hj (by rw [← hσ j, ← h])
    simp [hne]
  · simp

theorem applyGate_permMatrix_ket {σ : I → I} (hσ : Function.Involutive σ) (j : I) :
    ApplyGate (permMatrix σ) (Ket j) = Ket (σ j) := by
  funext i
  rw [applyGate_permMatrix hσ]
  by_cases h : i = σ j
  · subst h
    simp [Ket, hσ j]
  · have h' : σ i ≠ j := fun e => h (by rw [← e, hσ i])
    simp [Ket, h, h']

noncomputable def Hadamard : Matrix Bool Bool ℂ :=
  Matrix.of fun a b : Bool => (Real.sqrt 2 : ℂ)⁻¹ * (if a && b then -1 else 1)

theorem sqrt2_sq : ((Real.sqrt 2 : ℂ)) ^ 2 = 2 := by
  rw [show ((Real.sqrt 2 : ℂ)) ^ 2 = ((Real.sqrt 2 ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem hadamard_mul_self : Hadamard * Hadamard = 1 := by
  ext i j
  simp only [Hadamard, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_bool, Matrix.one_apply]
  rcases i <;> rcases j <;> simp <;> ring_nf <;> norm_num [sqrt2_sq]

theorem hadamard_conjTranspose : Hadamardᴴ = Hadamard := by
  ext i j
  simp only [Hadamard, Matrix.conjTranspose_apply, Matrix.of_apply, Bool.and_comm]
  rcases i <;> rcases j <;> simp [Complex.conj_ofReal]

theorem hadamard_unitary : Hadamard ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  rw [show star Hadamard = Hadamard from hadamard_conjTranspose]
  exact hadamard_mul_self

noncomputable def Plus : QState Bool := fun b => Hadamard b false

noncomputable def Minus : QState Bool := fun b => Hadamard b true

theorem applyGate_hadamard_ket_false : ApplyGate Hadamard (Ket false) = Plus := by
  funext b
  simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, Plus]

theorem applyGate_hadamard_ket_true : ApplyGate Hadamard (Ket true) = Minus := by
  funext b
  simp [ApplyGate, Matrix.mulVec, dotProduct, Ket, Minus]

theorem normalized_plus : Normalized Plus := by
  rw [← applyGate_hadamard_ket_false]
  exact normalized_applyGate hadamard_unitary (normalized_ket false)

theorem normalized_minus : Normalized Minus := by
  rw [← applyGate_hadamard_ket_true]
  exact normalized_applyGate hadamard_unitary (normalized_ket true)

noncomputable def PauliX : Matrix Bool Bool ℂ := permMatrix Bool.not

theorem pauliX_unitary : PauliX ∈ Matrix.unitaryGroup Bool ℂ :=
  permMatrix_unitary Bool.not_not

theorem applyGate_pauliX_ket (b : Bool) : ApplyGate PauliX (Ket b) = Ket (!b) :=
  applyGate_permMatrix_ket Bool.not_not b

noncomputable def PauliZ : Matrix Bool Bool ℂ := Matrix.diagonal fun a => if a then (-1 : ℂ) else 1

theorem pauliZ_mul_self : PauliZ * PauliZ = 1 := by
  unfold PauliZ
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> ring

theorem pauliZ_conjTranspose : PauliZᴴ = PauliZ := by
  unfold PauliZ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem pauliZ_unitary : PauliZ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, pauliZ_conjTranspose]
  exact pauliZ_mul_self

def cnotFlip : Bool × Bool → Bool × Bool := fun p => (p.1, p.2 ^^ p.1)

theorem cnotFlip_involutive : Function.Involutive cnotFlip := by
  intro p
  obtain ⟨c, d⟩ := p
  show (c, (d ^^ c) ^^ c) = (c, d)
  congr 1
  rw [Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

noncomputable def CNOT : Matrix (Bool × Bool) (Bool × Bool) ℂ := permMatrix cnotFlip

theorem cnot_unitary : CNOT ∈ Matrix.unitaryGroup (Bool × Bool) ℂ :=
  permMatrix_unitary cnotFlip_involutive

theorem applyGate_cnot_ket (c d : Bool) : ApplyGate CNOT (Ket (c, d)) = Ket (c, d ^^ c) :=
  applyGate_permMatrix_ket cnotFlip_involutive (c, d)

noncomputable def Rz (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp ((θ : ℂ) * Complex.I) else 1

theorem rz_unitary (θ : ℝ) : Rz θ ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold Rz
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  show star (if a then Complex.exp ((θ : ℂ) * Complex.I) else 1) *
      (if a then Complex.exp ((θ : ℂ) * Complex.I) else 1) = 1
  split_ifs with ha
  · rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      Complex.norm_exp_ofReal_mul_I]
    norm_num
  · simp

variable {n : ℕ}

noncomputable def HadamardN (n : ℕ) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => ∏ i, Hadamard (x i) (y i)

theorem hadamard_apply_false (a : Bool) : Hadamard a false = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Hadamard]

theorem hadamard_false_apply (b : Bool) : Hadamard false b = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [Hadamard]

theorem hadamardN_apply_zero_right (z : Reg n) :
    HadamardN n z (ZeroStr n) = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  simp only [HadamardN, Matrix.of_apply]
  rw [show (fun i => Hadamard (z i) (ZeroStr n i)) = (fun _ : Fin n => (Real.sqrt 2 : ℂ)⁻¹) by
    funext i; rw [ZeroStr, hadamard_apply_false], Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem hadamardN_apply_zero_left (z : Reg n) :
    HadamardN n (ZeroStr n) z = ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  simp only [HadamardN, Matrix.of_apply]
  rw [show (fun i => Hadamard (ZeroStr n i) (z i)) = (fun _ : Fin n => (Real.sqrt 2 : ℂ)⁻¹) by
    funext i; rw [ZeroStr, hadamard_false_apply], Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

theorem inv_sqrt2_mul_self : ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← sqrt2_sq, sq]

theorem hadamardN_mulVec_ket_zero :
    (HadamardN n).mulVec (Ket (ZeroStr n)) = fun _ => ((Real.sqrt 2 : ℂ)⁻¹) ^ n := by
  funext z
  simp only [Matrix.mulVec, dotProduct, Ket, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact hadamardN_apply_zero_right z

theorem applyGate_hadamardN_ket_zero (n : ℕ) :
    ApplyGate (HadamardN n) (Ket (ZeroStr n)) = Uniform (Reg n) := by
  have hsqrt : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  change (HadamardN n).mulVec (Ket (ZeroStr n)) = _
  rw [hadamardN_mulVec_ket_zero]
  funext i
  simp [Uniform, hsqrt, inv_pow]

theorem hadamardN_apply (y z : Reg n) :
    HadamardN n y z = ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ∏ i, (if y i && z i then (-1 : ℂ) else 1) := by
  simp only [HadamardN, Matrix.of_apply]
  rw [show (fun i => Hadamard (y i) (z i))
        = (fun i => (Real.sqrt 2 : ℂ)⁻¹ * (if y i && z i then (-1 : ℂ) else 1)) by
    funext i; simp [Hadamard]]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem bv_orthogonality (u v : Reg n) :
    (∑ z : Reg n, ∏ i,
        ((if u i && z i then (-1 : ℂ) else 1) * (if v i && z i then (-1 : ℂ) else 1)))
      = if (∀ i, u i = v i) then (2 : ℂ) ^ n else 0 := by
  rw [show (∑ z : Reg n, ∏ i,
        ((if u i && z i then (-1 : ℂ) else 1) * (if v i && z i then (-1 : ℂ) else 1)))
      = ∏ i, ∑ c : Bool,
        ((if u i && c then (-1 : ℂ) else 1) * (if v i && c then (-1 : ℂ) else 1)) by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]]
  rw [show (fun i => ∑ c : Bool,
        ((if u i && c then (-1 : ℂ) else 1) * (if v i && c then (-1 : ℂ) else 1)))
      = (fun i => if u i = v i then (2 : ℂ) else 0) by
    funext i; rcases u i <;> rcases v i <;> norm_num [Fintype.sum_bool]]
  split_ifs with h
  · rw [show (fun i => if u i = v i then (2 : ℂ) else 0) = (fun _ => (2 : ℂ)) by
      funext i; simp [h i]]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [not_forall] at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

theorem hadamardN_conj (y z : Reg n) :
    (starRingEnd ℂ) (HadamardN n y z) = HadamardN n y z := by
  rw [hadamardN_apply, map_mul, map_pow, map_inv₀, Complex.conj_ofReal, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp

theorem hadamardN_unitary (n : ℕ) : HadamardN n ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, RCLike.star_def,
    hadamardN_conj]
  have key : ∀ x y : Reg n,
      (∑ z : Reg n, (∏ i, (if z i && x i then (-1 : ℂ) else 1))
          * (∏ i, (if z i && y i then (-1 : ℂ) else 1)))
        = if (∀ i, x i = y i) then (2 : ℂ) ^ n else 0 := by
    intro x y
    rw [← bv_orthogonality (n := n) x y]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Bool.and_comm (z i) (x i), Bool.and_comm (z i) (y i)]
  rw [show (∑ z : Reg n, HadamardN n z x * HadamardN n z y)
      = ((Real.sqrt 2 : ℂ)⁻¹ ^ n * (Real.sqrt 2 : ℂ)⁻¹ ^ n) *
        ∑ z : Reg n, (∏ i, (if z i && x i then (-1 : ℂ) else 1))
          * (∏ i, (if z i && y i then (-1 : ℂ) else 1)) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [hadamardN_apply, hadamardN_apply]
    ring]
  rw [key]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos (fun _ => rfl), if_pos rfl, ← mul_pow, inv_sqrt2_mul_self, ← mul_pow,
      inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_pow]
  · rw [if_neg (by rwa [← funext_iff]), if_neg hxy, mul_zero]

theorem exp_unitary_of_skewHermitian {A : Matrix I I ℂ} (h : Aᴴ = -A) :
    NormedSpace.exp A ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, h,
    ← Matrix.exp_add_of_commute (-A) A ((Commute.refl A).neg_left), neg_add_cancel,
    NormedSpace.exp_zero]

noncomputable def HamiltonianEvolution (H : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)

theorem hamiltonianEvolution_unitary {H : Matrix I I ℂ} (hH : H.IsHermitian) (t : ℝ) :
    HamiltonianEvolution H t ∈ Matrix.unitaryGroup I ℂ := by
  apply exp_unitary_of_skewHermitian
  rw [Matrix.conjTranspose_smul, hH.eq, ← neg_smul]
  congr 1
  simp only [RCLike.star_def, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    neg_mul, neg_neg]

@[simp] theorem hamiltonianEvolution_zero (H : Matrix I I ℂ) :
    HamiltonianEvolution H 0 = 1 := by
  simp only [HamiltonianEvolution, Complex.ofReal_zero, mul_zero, zero_smul]
  exact NormedSpace.exp_zero

theorem hamiltonianEvolution_add (H : Matrix I I ℂ) (s t : ℝ) :
    HamiltonianEvolution H (s + t) = HamiltonianEvolution H s * HamiltonianEvolution H t := by
  unfold HamiltonianEvolution
  have hsplit : (-Complex.I * ((s + t : ℝ) : ℂ)) • H
      = (-Complex.I * (s : ℂ)) • H + (-Complex.I * (t : ℂ)) • H := by
    rw [← add_smul]; congr 1; push_cast; ring
  rw [hsplit, Matrix.exp_add_of_commute]
  exact ((Commute.refl H).smul_left _).smul_right _

theorem hamiltonianEvolution_neg (H : Matrix I I ℂ) (t : ℝ) :
    HamiltonianEvolution H (-t) * HamiltonianEvolution H t = 1 := by
  rw [← hamiltonianEvolution_add, neg_add_cancel, hamiltonianEvolution_zero]

noncomputable def Inner (ψ φ : QState I) : ℂ := star ψ ⬝ᵥ φ

theorem inner_apply (ψ φ : QState I) : Inner ψ φ = ∑ i, (starRingEnd ℂ) (ψ i) * φ i := by
  simp only [Inner, dotProduct, Pi.star_apply, RCLike.star_def]

theorem inner_self (ψ : QState I) : Inner ψ ψ = ∑ i, ((‖ψ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

theorem normalized_iff_inner_self (ψ : QState I) : Normalized ψ ↔ Inner ψ ψ = 1 := by
  rw [inner_self, ← Complex.ofReal_sum]
  unfold Normalized
  exact_mod_cast Iff.rfl

theorem inner_ket_ket (i j : I) : Inner (Ket i) (Ket j) = if i = j then 1 else 0 := by
  rw [inner_apply, Finset.sum_eq_single i]
  · simp [Ket]
  · intro k _ hk
    simp [Ket, hk]
  · simp

theorem inner_applyGate {U : Matrix I I ℂ} (hU : U ∈ Matrix.unitaryGroup I ℂ) (ψ φ : QState I) :
    Inner (ApplyGate U ψ) (ApplyGate U φ) = Inner ψ φ := by
  have hUU : Uᴴ * U = 1 := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at hU
    exact hU
  simp only [Inner, ApplyGate]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hUU, Matrix.vecMul_one]

end Qatlib.Foundations.PureStateMath

open Matrix
open scoped ComplexOrder

set_option linter.unusedSectionVars false
namespace Qatlib.Foundations.PureStateMath

theorem diagonal_mem_unitaryGroup {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℂ)
    (h : ∀ i, ‖d i‖ = 1) : Matrix.diagonal d ∈ Matrix.unitaryGroup I ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have hi : ((Complex.normSq (d i) : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h i]
    push_cast
    simp
  rw [Complex.normSq_eq_conj_mul_self] at hi
  exact hi

theorem applyGate_diagonal {I : Type*} [Fintype I] [DecidableEq I] (d : I → ℂ)
    (ψ : QState I) : ApplyGate (Matrix.diagonal d) ψ = fun i => d i * ψ i := by
  funext i
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Fintype.sum_eq_single i]
  · rw [if_pos rfl]
  · intro k hk
    rw [if_neg (Ne.symm hk), zero_mul]
end Qatlib.Foundations.PureStateMath

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {I : Type} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.PureStateMath

theorem applyGate_eq_mulVec_ket (A : Matrix I I ℂ) (j : I) (i : I) :
    ApplyGate A (Ket j) i = A i j := by
  simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ j) hcon
end Qatlib.Foundations.PureStateMath

open Matrix Set
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false

variable {I : Type} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.PureStateMath

theorem sum_norm_sq_orthonormal {J : Type} [Fintype J]
    (v : J → QState I) (d : J → ℂ)
    (hv : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0) :
    (∑ i, ‖(∑ j, d j • v j) i‖ ^ 2) = ∑ j, ‖d j‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum]
  rw [← inner_self]
  simp only [Inner, star_sum, star_smul, sum_dotProduct, dotProduct_sum,
    smul_dotProduct, dotProduct_smul, Finset.smul_sum]
  change (∑ j, ∑ k, d j * (star (d k) * Inner (v k) (v j))) = _
  simp_rw [hv]
  simp [mul_ite, Complex.mul_conj, Complex.normSq_eq_norm_sq, RCLike.star_def]
end Qatlib.Foundations.PureStateMath

open Matrix
open scoped Classical BigOperators
set_option autoImplicit false
namespace Qatlib.Foundations.PureStateMath

theorem state_ket_expansion {I : Type*} [Fintype I] [DecidableEq I] (ψ : QState I) :
    ψ = ∑ x, ψ x • Ket x := by
  funext z
  simp [Ket, Finset.sum_apply]
end Qatlib.Foundations.PureStateMath

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]
namespace Qatlib.Foundations.PureStateMath

theorem inner_mulVec_left_rect {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K]
    [DecidableEq K] (M : Matrix K I ℂ) (ψ : QState I) (φ : QState K) :
    Inner (M *ᵥ ψ) φ = Inner ψ (Mᴴ *ᵥ φ) := by
  have hL : ∀ k, (starRingEnd ℂ) ((M *ᵥ ψ) k) * φ k
      = ∑ i, (starRingEnd ℂ) (M k i) * ((starRingEnd ℂ) (ψ i)) * φ k := by
    intro k
    rw [show (M *ᵥ ψ) k = ∑ i, M k i * ψ i from by simp [Matrix.mulVec, dotProduct]]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by rw [map_mul]
  have hR : ∀ i, (starRingEnd ℂ) (ψ i) * ((Mᴴ *ᵥ φ) i)
      = ∑ k, (starRingEnd ℂ) (ψ i) * ((starRingEnd ℂ) (M k i) * φ k) := by
    intro i
    rw [show (Mᴴ *ᵥ φ) i = ∑ k, (starRingEnd ℂ) (M k i) * φ k from by
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, RCLike.star_def]]
    rw [Finset.mul_sum]
  rw [inner_apply, inner_apply]
  refine (Finset.sum_congr rfl fun k _ => hL k).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Finset.sum_congr rfl fun k _ => by ring).trans (hR i).symm
end Qatlib.Foundations.PureStateMath
