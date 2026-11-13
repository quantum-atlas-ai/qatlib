/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.Theorem35RandomOracleFiniteStat

/-!
# Counting lemmas for random-oracle failure

The module provides finite counting estimates used in the random-oracle lower bound of
[BennettEtAl1997]. A single-value update argument relates target-avoiding functions to failures,
and an elementary power bound compares target avoidance with the full function space. The
background is described in [BennettEtAl1997].

## Main statements

* `random_oracle_failure_count`: failure counting from single-input updates.
* `random_oracle_avoid_card`: exact target-avoidance count.
* `even_oracle_avoid_count`: comparison with all functions on an even-sized set.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open scoped Classical BigOperators

/-- The number of elements satisfying `p` splits into those also satisfying `q` and those
satisfying its negation. -/
private theorem predicate_card_partition {X : Type} [Fintype X] (p q : X → Prop) :
    Fintype.card {x : X // p x} = Fintype.card {x : X // p x ∧ q x}+
      Fintype.card {x : X // p x ∧ ¬q x} := by
  classical
  let e : {x : X // p x} ≃ ({x : X // p x ∧ q x} ⊕ {x : X // p x ∧ ¬q x}) :=
    { toFun := fun x => if h : q x.val then Sum.inl ⟨x.val,x.property,h⟩ else Sum.inr ⟨x.val,x.property,h⟩
      invFun := fun x => x.elim (fun a => ⟨a.val,a.property.1⟩) (fun a => ⟨a.val,a.property.1⟩)
      left_inv := by intro x; (try dsimp only); split_ifs <;> rfl
      right_inv := by
        intro x
        cases x with
        | inl x => (try dsimp only); simp only [Sum.elim_inl]; rw [dif_pos x.property.2]
        | inr x => (try dsimp only); simp only [Sum.elim_inr]; rw [dif_neg x.property.2] }
  simpa only [Fintype.card_sum] using Fintype.card_congr e

/-- If each successful oracle avoiding `t` has at most half the domain marked and updating any
unmarked input to `t` causes failure, then the number of oracles avoiding `t` is at most
twice the total number of failing oracles. -/
theorem random_oracle_failure_count {V : Type} [Fintype V] [DecidableEq V]
    (t : V) (fails : (V → V) → Prop) (S : (V → V) → Finset V)
    (hsmall : ∀ A, (∀ x, A x ≠ t) → ¬fails A → 2*(S A).card ≤ Fintype.card V)
    (hupdate : ∀ A, (∀ x, A x ≠ t) → ¬fails A → ∀ y, y ∉ S A → fails (Function.update A y t)) :
    Fintype.card {A : V → V // ∀ x, A x ≠ t} ≤ 2*Fintype.card {A : V → V // fails A} := by
  classical
  let avoid := fun A : V → V => ∀ x, A x ≠ t
  let Good := {A : V → V // avoid A ∧ ¬fails A}
  let Bad0 := {A : V → V // avoid A ∧ fails A}
  let BadPlus := {A : V → V // fails A ∧ ¬avoid A}
  let NT := {z : V // z ≠ t}
  let Edge := Σ A : Good, {y : V // y ∉ S A.val}
  let F : Edge → BadPlus × NT := fun z =>
    (⟨Function.update z.1.val z.2.val t,
      hupdate z.1.val z.1.property.1 z.1.property.2 z.2.val z.2.property,
      by intro h; exact h z.2.val (Function.update_self ..)⟩,
      ⟨z.1.val z.2.val, z.1.property.1 z.2.val⟩)
  have hF : Function.Injective F := by
    rintro ⟨A,y⟩ ⟨B,z⟩ he
    have hb : Function.update A.val y.val t = Function.update B.val z.val t :=
      congrArg (fun u : BadPlus × NT => u.1.val) he
    have hv : A.val y.val = B.val z.val := congrArg (fun u : BadPlus × NT => u.2.val) he
    have hy : y.val = z.val := by
      by_contra hn
      have hh := congrFun hb y.val
      rw [Function.update_self, Function.update_of_ne hn] at hh
      exact B.property.1 y.val hh.symm
    have hAB : A = B := by
      apply Subtype.ext
      funext x
      by_cases hx : x = y.val
      · subst x; simpa only [hy] using hv
      · have hh := congrFun hb x
        rw [Function.update_of_ne hx, Function.update_of_ne (by simpa only [← hy] using hx)] at hh
        exact hh
    subst B
    congr 1
    exact Subtype.ext hy
  have hNT : Fintype.card NT = Fintype.card V-1 := by
    simp only [NT, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hupper : Fintype.card Edge ≤ Fintype.card BadPlus*(Fintype.card V-1) := by
    have hc := Fintype.card_le_of_injective F hF
    simpa only [Fintype.card_prod, hNT] using hc
  have hdegree (A : Good) : Fintype.card V ≤ 2*Fintype.card {y : V // y ∉ S A.val} := by
    have hc : Fintype.card {y : V // y ∉ S A.val} = Fintype.card V-(S A.val).card := by
      rw [Fintype.card_subtype]
      have he : (Finset.univ.filter (fun y => y ∉ S A.val)) = (S A.val)ᶜ := by ext y; simp
      rw [he, Finset.card_compl]
    rw [hc]
    have hs := hsmall A.val A.property.1 A.property.2
    omega
  have hlower : Fintype.card V*Fintype.card Good ≤ 2*Fintype.card Edge := by
    calc
      _ = ∑ _A : Good, Fintype.card V := by simp [Nat.mul_comm]
      _ ≤ ∑ A : Good, 2*Fintype.card {y : V // y ∉ S A.val} := Finset.sum_le_sum (fun A _ => hdegree A)
      _ = _ := by rw [← Finset.mul_sum, Fintype.card_sigma]
  have hN : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨t⟩
  have hGood : Fintype.card Good ≤ 2*Fintype.card BadPlus := by
    apply (mul_le_mul_iff_right₀ hN).mp
    calc
      _ ≤ 2*Fintype.card Edge := hlower
      _ ≤ 2*(Fintype.card BadPlus*(Fintype.card V-1)) := Nat.mul_le_mul_left 2 hupper
      _ ≤ Fintype.card V*(2*Fintype.card BadPlus) := by nlinarith only [Nat.sub_le (Fintype.card V) 1]
  have hpart : Fintype.card {A : V → V // avoid A} = Fintype.card Bad0+Fintype.card Good := by
    simpa only [Fintype.card_eq_nat_card] using predicate_card_partition avoid fails
  have hcomm : Fintype.card {A : V → V // fails A ∧ avoid A} = Fintype.card Bad0 :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => and_comm))
  have hfpart : Fintype.card {A : V → V // fails A} = Fintype.card Bad0+Fintype.card BadPlus := by
    have hf := predicate_card_partition fails avoid
    simp only [Fintype.card_eq_nat_card] at hf hcomm ⊢
    rw [hcomm] at hf
    exact hf
  simp only [Fintype.card_eq_nat_card] at hpart hfpart hGood ⊢
  change Nat.card {A : V → V // avoid A} ≤ 2*Nat.card {A : V → V // fails A}
  omega

/-- The number of functions from a finite type to itself that avoid a fixed target is
`(Fintype.card V - 1)^(Fintype.card V)`. -/
theorem random_oracle_avoid_card {V : Type} [Fintype V] [DecidableEq V] (t : V) :
    Fintype.card {A : V → V // ∀ x, A x ≠ t} = (Fintype.card V-1)^(Fintype.card V) := by
  classical
  let e : {A : V → V // ∀ x, A x ≠ t} ≃ (V → {z : V // z ≠ t}) :=
    { toFun := fun A x => ⟨A.val x,A.property x⟩
      invFun := fun A => ⟨fun x => (A x).val,fun x => (A x).property⟩
      left_inv := by intro A; rfl
      right_inv := by intro A; rfl }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_subtype_eq] using hc

/-- For positive `m`, the total count `(2*m)^(2*m)` is at most four times the target-avoiding
count `(2*m - 1)^(2*m)`. -/
theorem even_oracle_avoid_count (m : ℕ) (hm : 0 < m) :
    (2*m)^(2*m) ≤ 4*(2*m-1)^(2*m) := by
  let N := 2*m
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNMR : (N : ℝ) = 2*(m : ℝ) := by dsimp [N]; push_cast; rfl
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hi : (1 : ℝ)/(N : ℝ) ≤ 1 := (div_le_iff₀ hNR).mpr (by simpa only [one_mul] using hN1R)
  let q : ℝ := 1-1/(N : ℝ)
  have hq : 0 ≤ q := by dsimp [q]; linarith only [hi]
  have hb := one_add_mul_le_pow (by linarith only [hi] : (-2 : ℝ) ≤ -(1/(N : ℝ))) m
  have hhalf : (1/2 : ℝ) ≤ q^m := by
    calc
      _ = 1+(m : ℝ)*(-(1/(N : ℝ))) := by rw [hNMR]; field_simp; ring
      _ ≤ _ := hb
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hhalf 2
  have hs' : (1 : ℝ) ≤ 4*q^N := by
    have he : (q^m)^2 = q^N := by dsimp [N]; rw [← pow_mul, Nat.mul_comm]
    rw [he] at hs
    nlinarith only [hs]
  have heq : q = ((N-1 : ℕ) : ℝ)/(N : ℝ) := by
    rw [Nat.cast_sub hN1, Nat.cast_one]
    dsimp [q]; field_simp
  rw [heq, div_pow] at hs'
  have hr : (N : ℝ)^N ≤ 4*((N-1 : ℕ) : ℝ)^N := by
    have hh : (1 : ℝ) ≤ (4*((N-1 : ℕ) : ℝ)^N)/(N : ℝ)^N := by simpa only [mul_div_assoc] using hs'
    have hc := (le_div_iff₀ (pow_pos hNR N)).mp hh
    simpa only [one_mul] using hc
  exact_mod_cast hr

end Qatlib.Concepts.UniformBqp.OracleAmplify
