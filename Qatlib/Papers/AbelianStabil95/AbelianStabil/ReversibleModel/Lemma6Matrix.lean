/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel.ReversibleOperationDefs

/-!
# Matrix realization of a controlled operation

`lemma6Mat` realizes the five-block controlled-copy construction for a complex matrix acting on
a bit register. The module computes its action on basis inputs and on `liftState`; when the
matrix fixes the zero basis state, the construction implements its controlled action on states
with a zero auxiliary register. The development follows [Kitaev1995].

## Main statements

* `lemma6Mat_liftState`: proves controlled matrix action on lifted states.
* `lemma6Blocks_cost`: computes the block cost as `4 * n + 1`.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators

/-- The controlled XOR operation copying the first data register into the second when the
Boolean control is true. -/
def ccopyAB {n : ℕ} (x : CtrlMem n) : CtrlMem n :=
  (x.1, x.2.1, if x.1 then bxor x.2.2 x.2.1 else x.2.2)

/-- The controlled XOR operation `ccopyAB` is involutive. -/
theorem ccopyAB_involutive {n : ℕ} : Function.Involutive (@ccopyAB n) := by
  intro x
  obtain ⟨a, ξ, η⟩ := x
  cases a <;> simp [ccopyAB, bxor_bxor_cancel]

/-- The controlled XOR operation copying the second data register into the first when the
Boolean control is true. -/
def ccopyBA {n : ℕ} (x : CtrlMem n) : CtrlMem n :=
  (x.1, if x.1 then bxor x.2.1 x.2.2 else x.2.1, x.2.2)

/-- The controlled XOR operation `ccopyBA` is involutive. -/
theorem ccopyBA_involutive {n : ℕ} : Function.Involutive (@ccopyBA n) := by
  intro x
  obtain ⟨a, ξ, η⟩ := x
  cases a <;> simp [ccopyBA, bxor_bxor_cancel]

/-- The matrix applying `U` to the second data register and acting as the identity on the
Boolean control and first data register. -/
def uBMat {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) : Matrix (CtrlMem n) (CtrlMem n) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then U p.2.2 q.2.2 else 0

/-- The matrix product of four controlled-copy blocks surrounding one use of `uBMat U`. -/
def lemma6Mat {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (CtrlMem n) (CtrlMem n) ℂ :=
  permMatrix (@ccopyAB n) * permMatrix (@ccopyBA n) * uBMat U *
    permMatrix (@ccopyBA n) * permMatrix (@ccopyAB n)

/-- With true control, the matrix of `ccopyAB` XORs the first data register into the second on a
basis state. -/
theorem applyGate_ccopyAB_ket_true {n : ℕ} (ξ η : Reg n) :
    ApplyGate (permMatrix (@ccopyAB n)) (Ket (true, ξ, η)) =
      Ket (true, ξ, bxor η ξ) := by
  rw [applyGate_permMatrix_ket ccopyAB_involutive]
  simp [ccopyAB]

/-- With false control, the matrix of `ccopyAB` preserves a basis state. -/
theorem applyGate_ccopyAB_ket_false {n : ℕ} (ξ η : Reg n) :
    ApplyGate (permMatrix (@ccopyAB n)) (Ket (false, ξ, η)) =
      Ket (false, ξ, η) := by
  rw [applyGate_permMatrix_ket ccopyAB_involutive]
  simp [ccopyAB]

/-- With true control, the matrix of `ccopyBA` XORs the second data register into the first on a
basis state. -/
theorem applyGate_ccopyBA_ket_true {n : ℕ} (ξ η : Reg n) :
    ApplyGate (permMatrix (@ccopyBA n)) (Ket (true, ξ, η)) =
      Ket (true, bxor ξ η, η) := by
  rw [applyGate_permMatrix_ket ccopyBA_involutive]
  simp [ccopyBA]

/-- With false control, the matrix of `ccopyBA` preserves a basis state. -/
theorem applyGate_ccopyBA_ket_false {n : ℕ} (ξ η : Reg n) :
    ApplyGate (permMatrix (@ccopyBA n)) (Ket (false, ξ, η)) =
      Ket (false, ξ, η) := by
  rw [applyGate_permMatrix_ket ccopyBA_involutive]
  simp [ccopyBA]

/-- Applying `uBMat U` to a basis state expands the second data register with coefficients from
the corresponding column of `U`. -/
theorem applyGate_uBMat {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (a : Bool) (ξ η : Reg n) :
    ApplyGate (uBMat U) (Ket (a, ξ, η)) =
      ∑ η' : Reg n, U η' η • Ket (a, ξ, η') := by
  funext p
  obtain ⟨a', ξ', η'⟩ := p
  have hL : ApplyGate (uBMat U) (Ket (a, ξ, η)) (a', ξ', η') =
      if a' = a ∧ ξ' = ξ then U η' η else 0 := by
    simp only [ApplyGate, Matrix.mulVec, dotProduct, Ket, uBMat, Matrix.of_apply]
    rw [Finset.sum_eq_single (a, ξ, η)]
    · simp
    · intro x _ hx
      obtain ⟨x1, x2, x3⟩ := x
      simp [Ket, hx]
    · intro h
      exact absurd (Finset.mem_univ (a, ξ, η)) h
  rw [hL]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ket]
  by_cases h : a' = a ∧ ξ' = ξ
  · obtain ⟨ha, hξ⟩ := h
    rw [ha, hξ]
    rw [if_pos ⟨rfl, rfl⟩]
    rw [Finset.sum_eq_single η']
    · simp
    · intro b _ hb
      have hne : (a, ξ, η') ≠ (a, ξ, b) := by
        intro he
        exact hb (congrArg (fun z => z.2.2) he).symm
      simp [hne]
    · intro hh
      exact absurd (Finset.mem_univ η') hh
  · rw [if_neg h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : (a', ξ', η') ≠ (a, ξ, b) := by
      intro he
      exact h ⟨congrArg Prod.fst he, congrArg (fun z => z.2.1) he⟩
    simp [hne]

/-- Matrix application distributes over a finite linear combination of state vectors. -/
theorem applyGate_sum_smul {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (M : Matrix I I ℂ) (c : J → ℂ) (v : J → QState I) :
    ApplyGate M (∑ j, c j • v j) = ∑ j, c j • ApplyGate M (v j) := by
  unfold ApplyGate
  rw [Matrix.mulVec_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_smul]

/-- The embedding of a data state with a fixed Boolean control and a zero second data register. -/
def liftState {n : ℕ} (a : Bool) (ψ : QState (Reg n)) : QState (CtrlMem n) :=
  fun p => if p.1 = a ∧ p.2.2 = ZeroStr n then ψ p.2.1 else 0

/-- A lifted state is the linear combination of zero-auxiliary basis states with coefficients
given by the original data amplitudes. -/
theorem liftState_eq_sum {n : ℕ} (a : Bool) (ψ : QState (Reg n)) :
    liftState a ψ = ∑ ξ : Reg n, ψ ξ • Ket (a, ξ, ZeroStr n) := by
  funext p
  obtain ⟨a', ξ', η'⟩ := p
  simp only [liftState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Ket]
  by_cases h : a' = a ∧ η' = ZeroStr n
  · obtain ⟨ha, hη⟩ := h
    rw [ha, hη]
    rw [if_pos ⟨rfl, rfl⟩]
    rw [Finset.sum_eq_single ξ']
    · simp
    · intro b _ hb
      have hne : (a, ξ', ZeroStr n) ≠ (a, b, ZeroStr n) := by
        intro he
        exact hb (congrArg (fun z => z.2.1) he).symm
      simp [hne]
    · intro hh
      exact absurd (Finset.mem_univ ξ') hh
  · rw [if_neg h]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro b _
    have hne : (a', ξ', η') ≠ (a, b, ZeroStr n) := by
      intro he
      exact h ⟨congrArg Prod.fst he, congrArg (fun z => z.2.2) he⟩
    simp [hne]

/-- With true control and zero auxiliary register, `lemma6Mat U` applies the column of `U` to
the data register and restores the auxiliary register to zero. -/
theorem lemma6Mat_ket_true {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ) (ξ : Reg n) :
    ApplyGate (lemma6Mat U) (Ket (true, ξ, ZeroStr n)) =
      ∑ η : Reg n, U η ξ • Ket (true, η, ZeroStr n) := by
  rw [lemma6Mat, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul]
  rw [applyGate_ccopyAB_ket_true]
  rw [show (true, ξ, bxor (ZeroStr n) ξ) = (true, ξ, ξ) from by rw [bxor_zero_left]]
  rw [applyGate_ccopyBA_ket_true]
  rw [show (true, bxor ξ ξ, ξ) = (true, ZeroStr n, ξ) from by rw [bxor_self]]
  rw [applyGate_uBMat]
  rw [applyGate_sum_smul, applyGate_sum_smul]
  simp only [applyGate_ccopyBA_ket_true, applyGate_ccopyAB_ket_true,
    bxor_zero_left, bxor_self]

/-- If `U` fixes the zero basis state, `lemma6Mat U` preserves every zero-auxiliary basis state
with false control. -/
theorem lemma6Mat_ket_false {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (hU0 : U *ᵥ Ket (ZeroStr n) = Ket (ZeroStr n)) (ξ : Reg n) :
    ApplyGate (lemma6Mat U) (Ket (false, ξ, ZeroStr n)) = Ket (false, ξ, ZeroStr n) := by
  rw [lemma6Mat, applyGate_mul, applyGate_mul, applyGate_mul, applyGate_mul]
  rw [applyGate_ccopyAB_ket_false, applyGate_ccopyBA_ket_false, applyGate_uBMat]
  rw [applyGate_sum_smul, applyGate_sum_smul]
  rw [Finset.sum_congr rfl (fun η' _ => by
    rw [applyGate_ccopyBA_ket_false, applyGate_ccopyAB_ket_false])]
  have hU0' : ∀ η : Reg n, U η (ZeroStr n) = (if η = ZeroStr n then 1 else 0) := by
    intro η
    have hcol := congrFun hU0 η
    simpa [Ket, Matrix.mulVec, dotProduct] using hcol
  simp only [hU0']
  rw [Finset.sum_eq_single (ZeroStr n)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (ZeroStr n)) h

/-- If `U` fixes the zero basis state, `lemma6Mat U` acts on a lifted state by applying `U`
exactly when the control is true, with zero auxiliary output. This is the matrix realization
of [Kitaev, 1995, Lemma 6][Kitaev1995]. -/
theorem lemma6Mat_liftState {n : ℕ} (U : Matrix (Reg n) (Reg n) ℂ)
    (hU0 : U *ᵥ Ket (ZeroStr n) = Ket (ZeroStr n)) (a : Bool) (ψ : QState (Reg n)) :
    ApplyGate (lemma6Mat U) (liftState a ψ) =
      liftState a (if a then U *ᵥ ψ else ψ) := by
  rw [liftState_eq_sum, applyGate_sum_smul]
  cases a
  · simp only [Bool.false_eq_true, if_false]
    rw [Finset.sum_congr rfl (fun ξ _ => by rw [lemma6Mat_ket_false U hU0 ξ])]
    rw [liftState_eq_sum]
  · simp only [if_true]
    rw [Finset.sum_congr rfl (fun ξ _ => by rw [lemma6Mat_ket_true U ξ])]
    rw [liftState_eq_sum]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_congr rfl (fun ξ _ => Finset.smul_sum)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    simp only [smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro ξ _
    ring

/-- The list of block identifiers and costs for the five-block controlled-operation
construction. -/
def lemma6Blocks (n : ℕ) : List (ℕ × ℕ) := [(0, n), (1, n), (2, 1), (1, n), (0, n)]

/-- The costs of the five controlled-operation blocks sum to `4 * n + 1`, as in [Kitaev, 1995,
Lemma 6][Kitaev1995]. -/
theorem lemma6Blocks_cost (n : ℕ) : ((lemma6Blocks n).map Prod.snd).sum = 4 * n + 1 := by
  simp [lemma6Blocks]
  omega

end Qatlib.Papers.AbelianStabil95.AbelianStabil.ReversibleModel
