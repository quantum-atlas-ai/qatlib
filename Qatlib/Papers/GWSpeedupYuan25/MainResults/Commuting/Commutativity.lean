/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GWSpeedupYuan25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Disconnected Transition Graph for Commuting Pauli Hamiltonians with Nontrivial Diagonal Group

This module proves Proposition 33: if a Pauli-expanded Hamiltonian has pairwise
commuting support Paulis and a nontrivial traceless diagonal group `diagGroup`,
then its computational-basis transition graph is disconnected (there exists a
nonempty proper subset of basis bitstrings closed under nonzero transitions).

## Main statements

* `prop33_commuting_disconnected`: commuting Pauli support with nonempty `diagGroup`
  disconnects the computational-basis transition graph.

## References

* [Yuan et al., 2025][YuanEtAl2025GWSpeedup], Proposition 33, Appendix E.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GWSpeedupYuan25.MainResults.Commuting

open Matrix Qatlib.Papers.GWSpeedupYuan25.MainResults
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

private def sympForm {n : ℕ}
    (u v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) : ZMod 2 :=
  ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)

private lemma sympForm_add {n : ℕ}
    (u v w : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    sympForm (u + v) w = sympForm u w + sympForm v w := by
  simp only [sympForm, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma sympForm_smul {n : ℕ} (r : ZMod 2)
    (u v : (Fin n → ZMod 2) × (Fin n → ZMod 2)) :
    sympForm (r • u) v = r * sympForm u v := by
  simp [sympForm, Finset.mul_sum, mul_add, mul_assoc]

private lemma pauli1Mat_mul_comm (x₁ z₁ x₂ z₂ : Bool) :
    pauli1Mat x₁ z₁ * pauli1Mat x₂ z₂ =
      (if xor (x₁ && z₂) (z₁ && x₂) then (-1 : ℂ) else 1) •
        (pauli1Mat x₂ z₂ * pauli1Mat x₁ z₁) := by
  cases x₁ <;> cases z₁ <;> cases x₂ <;> cases z₂ <;>
    ext a b <;> cases a <;> cases b <;>
      simp [pauli1Mat, Matrix.mul_apply]

private lemma pauliOp_mul_apply {n : ℕ} (p q : PauliIndex n) (i j : Reg n) :
    (pauliOp n p * pauliOp n q) i j =
      ∏ k, (pauli1Mat (p.1 k) (p.2 k) * pauli1Mat (q.1 k) (q.2 k)) (i k) (j k) := by
  simp only [Matrix.mul_apply, pauliOp, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k b =>
    pauli1Mat (p.1 k) (p.2 k) (i k) b * pauli1Mat (q.1 k) (q.2 k) b (j k))).symm

private lemma pauliOp_mul_comm {n : ℕ} (p q : PauliIndex n) :
    pauliOp n p * pauliOp n q =
      (∏ k, if xor (p.1 k && q.2 k) (p.2 k && q.1 k) then (-1 : ℂ) else 1) •
        (pauliOp n q * pauliOp n p) := by
  ext i j
  simp only [pauliOp_mul_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  exact congrFun (congrFun (pauli1Mat_mul_comm _ _ _ _) (i k)) (j k)

private lemma pauli1Mat_mul_entry_ne_zero (x₁ z₁ x₂ z₂ : Bool) :
    (pauli1Mat x₁ z₁ * pauli1Mat x₂ z₂) false (xor x₁ x₂) ≠ 0 := by
  cases x₁ <;> cases z₁ <;> cases x₂ <;> cases z₂ <;>
    simp [pauli1Mat, Matrix.mul_apply, Complex.I_ne_zero]

private lemma pauliOp_mul_ne_zero {n : ℕ} (p q : PauliIndex n) :
    pauliOp n p * pauliOp n q ≠ 0 := by
  intro h
  have he := congrFun (congrFun h (fun _ => false)) (fun k => xor (p.1 k) (q.1 k))
  rw [pauliOp_mul_apply] at he
  exact (Finset.prod_ne_zero_iff.mpr (fun k _ => pauli1Mat_mul_entry_ne_zero
    (p.1 k) (p.2 k) (q.1 k) (q.2 k))) he

private def paritySign (r : ZMod 2) : ℂ := if r = 0 then 1 else -1

private lemma paritySign_add (r s : ZMod 2) :
    paritySign (r + s) = paritySign r * paritySign s := by
  fin_cases r <;> fin_cases s <;>
    norm_num [paritySign, show (1 : ZMod 2) + 1 = 0 from rfl]

private lemma prod_sign {ι : Type*} (s : Finset ι) (b : ι → Bool) :
    (∏ i ∈ s, if b i then (-1 : ℂ) else 1) =
      paritySign (∑ i ∈ s, if b i then (1 : ZMod 2) else 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [paritySign]
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, paritySign_add, ih]
      cases b i <;> norm_num [paritySign]

private lemma sympVec_pairing {n : ℕ} (p q : PauliIndex n) :
    sympForm (sympVec p) (sympVec q) =
      ∑ k, if xor (p.1 k && q.2 k) (p.2 k && q.1 k) then (1 : ZMod 2) else 0 := by
  apply Finset.sum_congr rfl
  intro k _
  cases hp₁ : p.1 k <;> cases hp₂ : p.2 k <;>
    cases hq₁ : q.1 k <;> cases hq₂ : q.2 k <;>
      norm_num [sympVec, hp₁, hp₂, hq₁, hq₂,
        show (1 : ZMod 2) + 1 = 0 from rfl]

private lemma sympForm_eq_zero_of_commute {n : ℕ} (p q : PauliIndex n)
    (h : Commute (pauliOp n p) (pauliOp n q)) :
    sympForm (sympVec p) (sympVec q) = 0 := by
  have hs : (∏ k, if xor (p.1 k && q.2 k) (p.2 k && q.1 k)
      then (-1 : ℂ) else 1) = 1 := by
    apply smul_left_injective ℂ (pauliOp_mul_ne_zero q p)
    dsimp only
    rw [one_smul, ← pauliOp_mul_comm]
    exact h.eq
  rw [prod_sign, ← sympVec_pairing] at hs
  by_contra hn
  norm_num [paritySign, hn] at hs

private lemma diagGroup_sign {n : ℕ} (c : PauliIndex n → ℝ)
    (hcomm : ∀ p q : PauliIndex n, c p ≠ 0 → c q ≠ 0 →
      Commute (pauliOp n p) (pauliOp n q))
    (A : Finset (Fin n))
    (hA : ((0 : Fin n → ZMod 2), vectorOfFinset A) ∈ pauliSpan (pauliSupport c))
    (q : PauliIndex n) (hq : c q ≠ 0) :
    (∏ i ∈ A, if q.1 i then (-1 : ℂ) else 1) = 1 := by
  have hspan : ∀ u ∈ pauliSpan (pauliSupport c), sympForm u (sympVec q) = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨p, hp, rfl⟩ := hv
        exact sympForm_eq_zero_of_commute p q (hcomm p q hp hq)
    | zero => simp [sympForm]
    | add u v _ _ hu hv => rw [sympForm_add, hu, hv, add_zero]
    | smul r u _ hu => rw [sympForm_smul, hu, mul_zero]
  have hsum : (∑ i ∈ A, if q.1 i then (1 : ZMod 2) else 0) = 0 := by
    have heq : sympForm ((0 : Fin n → ZMod 2), vectorOfFinset A) (sympVec q) =
        ∑ i ∈ A, if q.1 i then (1 : ZMod 2) else 0 := by
      simp only [sympForm, vectorOfFinset, sympVec, Pi.zero_apply, zero_mul,
        zero_add, ite_mul, one_mul]
      simp
    rw [← heq]
    exact hspan _ hA
  rw [prod_sign, hsum]
  simp [paritySign]

private lemma pauli1Mat_entry_flip (a b x z : Bool) (h : pauli1Mat x z a b ≠ 0) :
    b = xor a x := by
  cases a <;> cases b <;> cases x <;> cases z <;> simp_all [pauli1Mat]

private lemma zSign_eq_of_entry_ne_zero {n : ℕ} (A : Finset (Fin n))
    (q : PauliIndex n) (x y : Reg n) (h : pauliOp n q x y ≠ 0) :
    zSign n A y = zSign n A x * (∏ i ∈ A, if q.1 i then (-1 : ℂ) else 1) := by
  unfold zSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi := (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
  rw [pauli1Mat_entry_flip (x i) (y i) (q.1 i) (q.2 i) hi]
  cases x i <;> cases q.1 i <;> norm_num

/-- **Proposition 33**: if `C = pauliExpand c` has pairwise commuting Pauli terms on its
support and its traceless diagonal group `diagGroup (pauliSupport c)` is nonempty, then
there is a nonempty proper subset `S` of `Reg n` closed under nonzero transitions of
`pauliExpand c`. -/
theorem prop33_commuting_disconnected (n : ℕ) (C : Matrix (Reg n) (Reg n) ℂ)
    (c : PauliIndex n → ℝ) (_hC : C = pauliExpand c)
    (hcomm : ∀ p q : PauliIndex n, c p ≠ 0 → c q ≠ 0 →
      Commute (pauliOp n p) (pauliOp n q))
    (hD : (diagGroup (pauliSupport c)).Nonempty) :
    ∃ S : Set (Reg n), S.Nonempty ∧ S ≠ Set.univ ∧
      ∀ x ∈ S, ∀ y : Reg n, pauliExpand c x y ≠ 0 → y ∈ S := by
  classical
  obtain ⟨A, hA, hA_ne⟩ := hD
  let S : Set (Reg n) := {x | zSign n A x = 1}
  refine ⟨S, ?_, ?_, ?_⟩
  · exact ⟨fun _ => false, by simp [S, zSign]⟩
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hA_ne
    let x₁ : Reg n := fun i => decide (i = i₀)
    have hx₁ : zSign n A x₁ = -1 := by
      unfold zSign
      rw [Finset.prod_eq_single i₀]
      · simp [x₁]
      · intro i _ hi
        simp [x₁, hi]
      · exact fun hi => (hi hi₀).elim
    intro hS
    have hx : x₁ ∈ S := hS.symm ▸ Set.mem_univ x₁
    change zSign n A x₁ = 1 at hx
    rw [hx₁] at hx
    norm_num at hx
  · intro x hx y hxy
    have hterm : ∃ q : PauliIndex n, (c q : ℂ) * pauliOp n q x y ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hxy
      simp only [pauliExpand, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      exact Finset.sum_eq_zero (fun q _ => hn q)
    obtain ⟨q, hq⟩ := hterm
    obtain ⟨hcq, hpq⟩ := mul_ne_zero_iff.mp hq
    have hcq' : c q ≠ 0 := by
      intro hz
      exact hcq (by simp [hz])
    change zSign n A y = 1
    rw [zSign_eq_of_entry_ne_zero A q x y hpq, diagGroup_sign c hcomm A hA q hcq']
    simpa only [mul_one] using (show zSign n A x = 1 from hx)

end Qatlib.Papers.GWSpeedupYuan25.MainResults.Commuting
