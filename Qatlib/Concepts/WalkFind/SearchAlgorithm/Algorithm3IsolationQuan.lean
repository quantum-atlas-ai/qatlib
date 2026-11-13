/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationStat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Qatlib.Concepts.WalkFind.SearchAlgorithm.Algorithm3IsolationAsymptotics

/-!
# Quantitative isolation of a collision

This module proves `Algorithm3Isolation` by comparing retention under approximately independent
permutations with independent sampling. Binomial occupancy estimates and a packing dichotomy
control the probability of retaining no collision relative to retaining a unique collision.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `approxIndependent_iid_event`: gives the permutation-to-independent-sampling error bound.
* `collision_packing_dichotomy`: gives either small collision support or many disjoint
  collisions.
* `algorithm3Isolation_quantitative`: proves an explicit isolation error estimate.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm
open scoped Classical BigOperators

/-- Pointwise implication of finite seed events implies the corresponding inequality of event
probabilities. -/
theorem eventProbability_mono {R : ℕ} {P Q : Fin R → Prop}
    (h : ∀ s, P s → Q s) : eventProbability P ≤ eventProbability Q := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg R)
  exact_mod_cast Finset.card_le_card (show Finset.univ.filter P ⊆ Finset.univ.filter Q from
    fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h s (Finset.mem_filter.mp hs).2⟩)

/-- Every finite seed event has probability between zero and one, including the convention for
an empty seed space. -/
theorem eventProbability_bounds {R : ℕ} (P : Fin R → Prop) :
    0 ≤ eventProbability P ∧ eventProbability P ≤ 1 := by
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · by_cases hr : R = 0
    · simp [eventProbability, hr]
    · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hr)).mpr
      have h := Finset.card_le_card (Finset.filter_subset P (Finset.univ : Finset (Fin R)))
      rw [Finset.card_univ, Fintype.card_fin] at h
      exact_mod_cast h

/-- The finite seed event probability is the sum of its indicator values divided by the number
of seeds. -/
theorem eventProbability_indicator {R : ℕ} (P : Fin R → Prop) :
    eventProbability P = (∑ s : Fin R, if P s then (1 : ℝ) else 0)/R := by
  simp [eventProbability, Finset.sum_boole]

/-- An event on images of distinct inputs is the sum of the probabilities of its injective image
tuples. -/
theorem permutationCylinder_partition {q R m : ℕ}
    (π : Fin R → Equiv.Perm (Fin q)) (i : Fin m → Fin q)
    (hi : Function.Injective i) (V : (Fin m → Fin q) → Prop) :
    eventProbability (fun s => V (fun z => π s (i z))) =
      ∑ j ∈ (Finset.univ : Finset (Fin m → Fin q)).filter
        (fun j => Function.Injective j ∧ V j),
        eventProbability (fun s => ∀ z, π s (i z) = j z) := by
  classical
  simp_rw [eventProbability_indicator]
  rw [← Finset.sum_div, ← Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  let f : Fin m → Fin q := fun z => π s (i z)
  have hf : Function.Injective f := (π s).injective.comp hi
  by_cases hv : V f
  · rw [if_pos hv]
    apply Eq.symm
    have hoff : ∀ j ∈ Finset.univ.filter (fun j : Fin m → Fin q =>
        Function.Injective j ∧ V j), j ≠ f →
        (if ∀ z, π s (i z) = j z then (1 : ℝ) else 0) = 0 := by
      intro j _ hj
      apply if_neg
      intro h
      exact hj (funext h).symm
    have hnot : f ∉ Finset.univ.filter (fun j : Fin m → Fin q =>
        Function.Injective j ∧ V j) →
        (if ∀ z, π s (i z) = f z then (1 : ℝ) else 0) = 0 := by
      simp [hf, hv]
    have hsum := Finset.sum_eq_single f hoff hnot
    convert! hsum using 1
    · apply Finset.sum_congr rfl
      intro j _
      by_cases h : ∀ z, π s (i z) = j z
      · simp only [if_pos h]
      · simp only [if_neg h]
    · simp [f]
  · rw [if_neg hv]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro j hj
    apply if_neg
    intro h
    have : j = f := (funext h).symm
    exact hv (this ▸ (Finset.mem_filter.mp hj).2.2)

/-- Approximate independence bounds an event on `m` distinct inputs between `1 - η` and `1 + η`
times its uniform injective-tuple probability. -/
theorem approxIndependent_cylinder {q R d m : ℕ} {η : ℝ}
    {π : Fin R → Equiv.Perm (Fin q)} (hπ : ApproxIndependent d η π)
    (hmd : m ≤ d) (hmq : m ≤ q) (i : Fin m → Fin q)
    (hi : Function.Injective i) (V : (Fin m → Fin q) → Prop) :
    let A := (Finset.univ : Finset (Fin m → Fin q)).filter
      (fun j => Function.Injective j ∧ V j)
    (1-η)*(A.card : ℝ)/(q.descFactorial m : ℝ) ≤
      eventProbability (fun s => V (fun z => π s (i z))) ∧
    eventProbability (fun s => V (fun z => π s (i z))) ≤
      (1+η)*(A.card : ℝ)/(q.descFactorial m : ℝ) := by
  (try dsimp only)
  rw [permutationCylinder_partition π i hi V]
  constructor
  · calc
      _ = ∑ j ∈ Finset.univ.filter (fun j => Function.Injective j ∧ V j),
          (1-η)/(q.descFactorial m : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
        (hπ m hmd hmq i j hi (Finset.mem_filter.mp hj).2.1).1
  · calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j => Function.Injective j ∧ V j),
          (1+η)/(q.descFactorial m : ℝ) := Finset.sum_le_sum fun j hj =>
        (hπ m hmd hmq i j hi (Finset.mem_filter.mp hj).2.1).2
      _ = _ := by simp; ring

/-- A planned retention step preserves well-formedness of the frame. -/
theorem nextFrame_wellFormed {k N : ℕ} {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (hf : frameWellFormed f) (s : Fin P.seeds) :
    frameWellFormed (nextFrame P s) := by
  intro i j v hi hj
  dsimp only [nextFrame] at hi hj
  split_ifs at hi with hia
  · split_ifs at hj with hja
    · have heq := hf _ _ _ hi hj
      have hvals := congrArg Fin.val heq
      have hpre : (P.permutation s).symm (Fin.castLE P.kept_le i) =
          (P.permutation s).symm (Fin.castLE P.kept_le j) := Fin.ext hvals
      have hcast := (P.permutation s).symm.injective hpre
      exact Fin.ext (congrArg (fun z : Fin P.q => z.val) hcast)

/-- An original index lies in the next frame exactly when a current frame position representing
it is mapped below the retained cutoff. -/
theorem mem_frameSet_nextFrame {k N : ℕ} {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (s : Fin P.seeds) (v : Fin N) :
    v ∈ frameSet (nextFrame P s) ↔ ∃ j : Fin f.size,
      f.origin j = some v ∧ (P.permutation s (Fin.castLE P.enough j)).val < P.kept := by
  simp only [frameSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    dsimp only [nextFrame] at hi
    split_ifs at hi with h
    · refine ⟨⟨((P.permutation s).symm (Fin.castLE P.kept_le i)).val,h⟩,hi,?_⟩
      have heq : Fin.castLE P.enough
          (⟨((P.permutation s).symm (Fin.castLE P.kept_le i)).val,h⟩ : Fin f.size) =
          (P.permutation s).symm (Fin.castLE P.kept_le i) := Fin.ext rfl
      rw [heq, Equiv.apply_symm_apply]
      exact i.isLt
  · rintro ⟨j,hj,hlt⟩
    let i : Fin P.kept := ⟨(P.permutation s (Fin.castLE P.enough j)).val,hlt⟩
    have hcast : Fin.castLE P.kept_le i =
        P.permutation s (Fin.castLE P.enough j) := Fin.ext rfl
    refine ⟨i,?_⟩
    dsimp only [nextFrame]
    rw [hcast, Equiv.symm_apply_apply]
    have hbound : (Fin.castLE P.enough j).val < f.size := j.isLt
    rw [dif_pos hbound]
    exact hj

/-- The set represented by the next frame is contained in the set represented by the current
frame. -/
theorem frameSet_nextFrame_subset {k N : ℕ} {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (s : Fin P.seeds) :
    frameSet (nextFrame P s) ⊆ frameSet f := by
  intro v hv
  obtain ⟨j,hj,_⟩ := (mem_frameSet_nextFrame P s v).mp hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj⟩

/-- A collision in the next frame is also a collision in the current frame. -/
theorem frameHasCollision_nextFrame {k N M : ℕ} {f : Algorithm3Frame N}
    (P : Algorithm3Plan k N f) (s : Fin P.seeds) (x : Fin N → ZMod M)
    (h : frameHasCollision k x (nextFrame P s)) : frameHasCollision k x f := by
  obtain ⟨S,hS,hcollision⟩ := h
  exact ⟨S, hS.trans (frameSet_nextFrame_subset P s), hcollision⟩

/-- The binomial mass `choose m l * p^l * (1 - p)^(m - l)`. -/
def collisionBinomialMass (m : ℕ) (p : ℝ) (l : ℕ) : ℝ :=
  (m.choose l : ℝ)*p^l*(1-p)^(m-l)

/-- The binomial mass is nonnegative when `p` lies in `[0, 1]`. -/
theorem collisionBinomialMass_nonneg (m : ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (l : ℕ) : 0 ≤ collisionBinomialMass m p l := by
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- Adjacent binomial masses satisfy the standard recurrence for `l < m`, after multiplication
by `l + 1` and `1 - p`. -/
theorem collisionBinomialMass_recurrence (m l : ℕ) (p : ℝ) (hl : l < m) :
    (l+1 : ℝ)*collisionBinomialMass m p (l+1)*(1-p) =
      (m-l : ℝ)*collisionBinomialMass m p l*p := by
  have hc : (l+1 : ℝ)*(m.choose (l+1) : ℝ) =
      (m-l : ℝ)*(m.choose l : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq m l)
    push_cast [Nat.cast_sub hl.le] at h
    nlinarith
  have hsub : m-l = (m-(l+1))+1 := by omega
  unfold collisionBinomialMass
  rw [pow_succ, hsub, pow_succ]
  push_cast at hc
  calc
    _ = ((l+1 : ℝ)*(m.choose (l+1) : ℝ))*
        (p^l*p*(1-p)^(m-(l+1))*(1-p)) := by ring
    _ = _ := by rw [hc]; ring

/-- If `k ≤ m` and `2 * k * (1 - p) ≤ p` with `0 < p ≤ 1`, each binomial mass below level `k` is
at most half the next mass. -/
theorem collisionBinomialMass_step (k m l : ℕ) (hkm : k ≤ m) (hlk : l < k)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpkeep : 2*k*(1-p) ≤ p) :
    2*collisionBinomialMass m p l ≤ collisionBinomialMass m p (l+1) := by
  have hlm : l < m := lt_of_lt_of_le hlk hkm
  have hml : (l : ℝ) < m := by exact_mod_cast hlm
  have hn : (0 : ℝ) < m-l := by linarith
  have hls : (l+1 : ℝ) ≤ k := by exact_mod_cast hlk
  have hmn : (1 : ℝ) ≤ m-l := by
    have h := (show l+1 ≤ m from hlm)
    have hreal : (l : ℝ)+1 ≤ m := by exact_mod_cast h
    linarith
  have h1p : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hrec := collisionBinomialMass_recurrence m l p hlm
  have hnxt := collisionBinomialMass_nonneg m hp0.le hp1 (l+1)
  have hcoef : 2*(l+1 : ℝ)*(1-p) ≤ (m-l : ℝ)*p := by
    nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcoef hnxt
  nlinarith [mul_pos hn hp0]

/-- Under the stated retention-ratio condition, the sum of binomial masses below `k` is at most
the mass at `k`. -/
theorem collisionBinomialMass_no_le_unique (k m : ℕ) (hkm : k ≤ m)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (hpkeep : 2*k*(1-p) ≤ p) :
    (∑ l ∈ Finset.range k, collisionBinomialMass m p l) ≤
      collisionBinomialMass m p k := by
  have hprefix : ∀ n, n ≤ k →
      (∑ l ∈ Finset.range n, collisionBinomialMass m p l) ≤
        collisionBinomialMass m p n := by
    intro n
    induction n with
    | zero =>
      intro _
      simpa using! collisionBinomialMass_nonneg m hp0.le hp1 0
    | succ n ih =>
      intro hnk
      rw [Finset.sum_range_succ]
      have hprev := ih (by omega)
      have hstep := collisionBinomialMass_step k m n hkm (by omega) p hp0 hp1 hpkeep
      linarith
  exact hprefix k le_rfl

/-- The number of injective functions from `Fin m` to `Fin q` is the descending factorial
`q.descFactorial m`. -/
theorem injectiveTuple_card (q m : ℕ) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter Function.Injective).card =
      q.descFactorial m := by
  classical
  let e : {j : Fin m → Fin q // Function.Injective j} ≃ (Fin m ↪ Fin q) :=
    { toFun := fun j => ⟨j.1,j.2⟩
      invFun := fun j => ⟨j,j.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_embedding_eq]
  simp

/-- For positive `q` and `m ≤ q`, the failure probability of injectivity for an independent
uniform `m`-tuple is at most `m^2 / q`. -/
theorem descFactorial_birthday_loss (q m : ℕ) (hq : 0 < q) (hm : m ≤ q) :
    1-(q.descFactorial m : ℝ)/(q : ℝ)^m ≤ (m : ℝ)^2/q := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hmr : (m : ℝ) ≤ q := by exact_mod_cast hm
  have hbase : 0 ≤ (q : ℝ)-m := sub_nonneg.mpr hmr
  have hfactorial : ((q : ℝ)-m)^m ≤ (q.descFactorial m : ℝ) := by
    have hnat : (q-m)^m ≤ q.descFactorial m := le_trans
      (Nat.pow_le_pow_left (show q-m ≤ q+1-m by omega) m) (Nat.pow_sub_le_descFactorial q m)
    have hreal := (show (((q-m)^m : ℕ) : ℝ) ≤ (q.descFactorial m : ℝ) from by
      exact_mod_cast hnat)
    simpa only [Nat.cast_pow, Nat.cast_sub hm] using! hreal
  have hbern := one_add_mul_le_pow (a := -(m : ℝ)/q) (by
    apply (le_div_iff₀ hqr).mpr
    linarith) m
  have hident : 1+ -(m : ℝ)/q = ((q : ℝ)-m)/q := by field_simp; ring
  rw [hident, div_pow] at hbern
  have hfdiv := div_le_div_of_nonneg_right hfactorial (pow_nonneg hqr.le m)
  have htotal := le_trans hbern hfdiv
  have hmul : (m : ℝ)*(-(m : ℝ)/q) = -(m : ℝ)^2/q := by ring
  rw [hmul, neg_div] at htotal
  linarith

/-- The difference between the conditional ratio `a / i` and the full ratio `(a + b) / t` is at
most `1 - i / t` under the stated mass bounds. -/
private theorem conditionalCounting_gap (a b i t : ℝ) (hi : 0 < i)
    (hit : i ≤ t) (ha : 0 ≤ a) (hai : a ≤ i) (hb : 0 ≤ b) (hbit : b ≤ t-i) :
    |a/i-(a+b)/t| ≤ 1-i/t := by
  have ht : 0 < t := lt_of_lt_of_le hi hit
  have hx0 : 0 ≤ a/i := div_nonneg ha hi.le
  have hx1 : a/i ≤ 1 := (div_le_one hi).mpr hai
  have hg0 : 0 ≤ i/t := div_nonneg hi.le ht.le
  have hg1 : i/t ≤ 1 := (div_le_one ht).mpr hit
  have hb0 : 0 ≤ b/t := div_nonneg hb ht.le
  have hb1 : b/t ≤ 1-i/t := by
    have hid : 1-i/t = (t-i)/t := by field_simp
    rw [hid]
    exact div_le_div_of_nonneg_right hbit ht.le
  have hid : (a+b)/t = (i/t)*(a/i)+b/t := by field_simp
  rw [hid, abs_le]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hg1) hx0,
    mul_nonneg (sub_nonneg.mpr hg1) (sub_nonneg.mpr hx1)]

/-- Conditioning a uniform finite sample on a nonempty subset changes any event probability by
at most the probability outside that subset. -/
theorem uniformConditioning_gap {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (I : Finset Ω) (hI : 0 < I.card) (V : Ω → Prop) :
    |((I.filter V).card : ℝ)/I.card -
      ((Finset.univ.filter V).card : ℝ)/Fintype.card Ω| ≤
      1-(I.card : ℝ)/Fintype.card Ω := by
  classical
  let C := I.filter V
  let K := Finset.univ.filter (fun v : Ω => v ∉ I ∧ V v)
  have hpart : Finset.univ.filter V = C ∪ K := by
    ext v
    simp only [C,K,Finset.mem_filter,Finset.mem_union,Finset.mem_univ,true_and]
    tauto
  have hdis : Disjoint C K := by
    apply Finset.disjoint_left.mpr
    intro v hv hk
    exact (Finset.mem_filter.mp hk).2.1 (Finset.mem_filter.mp hv).1
  have hdisI : Disjoint I K := by
    apply Finset.disjoint_left.mpr
    intro v hv hk
    exact (Finset.mem_filter.mp hk).2.1 hv
  have hc : C.card ≤ I.card := Finset.card_le_card (Finset.filter_subset V I)
  have hit : I.card ≤ Fintype.card Ω := Finset.card_le_univ I
  have hk : I.card+K.card ≤ Fintype.card Ω := by
    rw [← Finset.card_union_of_disjoint hdisI]
    exact Finset.card_le_univ _
  rw [hpart, Finset.card_union_of_disjoint hdis, Nat.cast_add]
  apply conditionalCounting_gap
  · exact_mod_cast hI
  · exact_mod_cast hit
  · exact Nat.cast_nonneg _
  · exact_mod_cast hc
  · exact Nat.cast_nonneg _
  · have hreal : (I.card : ℝ)+K.card ≤ Fintype.card Ω := by exact_mod_cast hk
    linarith

/-- For `m ≤ q` and positive `q`, uniform injective-tuple and independent uniform-tuple event
probabilities differ by at most `m^2 / q`. -/
theorem injectiveTuple_iid_gap (q m : ℕ) (hq : 0 < q) (hm : m ≤ q)
    (V : (Fin m → Fin q) → Prop) :
    |(((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun j => Function.Injective j ∧ V j)).card : ℝ)/(q.descFactorial m : ℝ) -
      (((Finset.univ : Finset (Fin m → Fin q)).filter V).card : ℝ)/(q : ℝ)^m| ≤
      (m : ℝ)^2/q := by
  classical
  have hp : 0 < q.descFactorial m := Nat.descFactorial_pos.mpr hm
  have hgap := uniformConditioning_gap
    ((Finset.univ : Finset (Fin m → Fin q)).filter Function.Injective)
    (by simpa [injectiveTuple_card] using! hp) V
  simp only [Finset.filter_filter, injectiveTuple_card, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow] at hgap
  exact le_trans hgap (descFactorial_birthday_loss q m hq hm)

/-- An approximately independent permutation changes an event on `m` distinct inputs from its
independent uniform probability by at most `η + m^2 / q` [Ambainis2007ElementDistinctness]. -/
theorem approxIndependent_iid_event {q R d m : ℕ} {η : ℝ}
    {π : Fin R → Equiv.Perm (Fin q)} (hq : 0 < q) (hη : 0 ≤ η)
    (hπ : ApproxIndependent d η π) (hmd : m ≤ d) (hmq : m ≤ q)
    (i : Fin m → Fin q) (hi : Function.Injective i)
    (V : (Fin m → Fin q) → Prop) :
    |eventProbability (fun s => V (fun z => π s (i z))) -
      (((Finset.univ : Finset (Fin m → Fin q)).filter V).card : ℝ)/(q : ℝ)^m| ≤
      η+(m : ℝ)^2/q := by
  classical
  let A := (Finset.univ : Finset (Fin m → Fin q)).filter
    (fun j => Function.Injective j ∧ V j)
  let ref : ℝ := (A.card : ℝ)/(q.descFactorial m : ℝ)
  have hd : (0 : ℝ) < q.descFactorial m := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hmq)
  have ha : A.card ≤ q.descFactorial m := by
    rw [← injectiveTuple_card]
    apply Finset.card_le_card
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2.1⟩
  have href0 : 0 ≤ ref := div_nonneg (Nat.cast_nonneg _) hd.le
  have href1 : ref ≤ 1 := (div_le_one hd).mpr (by exact_mod_cast ha)
  obtain ⟨hlo,hhi⟩ := approxIndependent_cylinder hπ hmd hmq i hi V
  have hlo' : (1-η)*ref ≤ eventProbability (fun s => V (fun z => π s (i z))) := by
    simpa only [A,ref,mul_div_assoc] using! hlo
  have hhi' : eventProbability (fun s => V (fun z => π s (i z))) ≤ (1+η)*ref := by
    simpa only [A,ref,mul_div_assoc] using! hhi
  have happrox : |eventProbability (fun s => V (fun z => π s (i z)))-ref| ≤ η := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hη (sub_nonneg.mpr href1)]
  have hgap := injectiveTuple_iid_gap q m hq hmq V
  change |ref- _| ≤ _ at hgap
  exact le_trans (abs_sub_le _ ref _) (add_le_add happrox hgap)

/-- The subset of `T` consisting of indices that belong to some `k`-collision in `T`. -/
def collisionSupport {q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (T : Finset (Fin q)) : Finset (Fin q) :=
  T.filter (fun i => ∃ S, CollisionIn k x T S ∧ i ∈ S)

/-- The collision support is contained in its ambient set. -/
theorem collisionSupport_subset {q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (T : Finset (Fin q)) : collisionSupport k x T ⊆ T := Finset.filter_subset _ _

/-- For `U ⊆ T`, a specified set is a collision in `U` exactly when it is a collision in `U`
intersected with the collision support of `T`. -/
theorem collisionIn_support_iff {q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (T U S : Finset (Fin q)) (hUT : U ⊆ T) :
    CollisionIn k x U S ↔ CollisionIn k x (U ∩ collisionSupport k x T) S := by
  constructor
  · rintro ⟨hSU,hcol⟩
    refine ⟨?_,hcol⟩
    intro i hi
    apply Finset.mem_inter.mpr
    refine ⟨hSU hi,?_⟩
    exact Finset.mem_filter.mpr ⟨hUT (hSU hi),S,⟨hSU.trans hUT,hcol⟩,hi⟩
  · rintro ⟨hS,hcol⟩
    exact ⟨hS.trans Finset.inter_subset_left,hcol⟩

/-- The set of indexed positions whose supplied image values lie below the cutoff. -/
def selectedTuplePositions {q m : ℕ} (cut : ℕ) (i : Fin m → Fin q)
    (images : Fin m → Fin q) : Finset (Fin q) :=
  (Finset.univ.filter (fun z => (images z).val < cut)).image i

/-- Selecting positions from an enumeration of `S` by their permutation images equals filtering
`S` by the same cutoff. -/
theorem selectedTuplePositions_permutation {q R : ℕ} (S : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (s : Fin R) (cut : ℕ) :
    selectedTuplePositions cut (S.orderEmbOfFin rfl) (fun z => π s (S.orderEmbOfFin rfl z)) =
      S.filter (fun j => (π s j).val < cut) := by
  classical
  ext j
  simp only [selectedTuplePositions,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨S.orderEmbOfFin_mem rfl z,hz⟩
  · rintro ⟨hj,hcut⟩
    have hrange : j ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [S.range_orderEmbOfFin rfl]
      exact hj
    obtain ⟨z,hz⟩ := hrange
    exact ⟨z,hz ▸ hcut,hz⟩

/-- Collisions in the retained set are exactly collisions among the selected positions of the
collision-support enumeration. -/
theorem retained_collision_tuple_iff {q R M : ℕ} (k : ℕ)
    (x : Fin q → ZMod M) (T : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (s : Fin R) (S : Finset (Fin q)) :
    CollisionIn k x (retained k T π s) S ↔
    CollisionIn k x
      (selectedTuplePositions (Nat.ceil ((2*k : ℝ)/(2*k+1)*q))
        ((collisionSupport k x T).orderEmbOfFin rfl)
        (fun z => π s ((collisionSupport k x T).orderEmbOfFin rfl z))) S := by
  rw [selectedTuplePositions_permutation]
  have heq : retained k T π s ∩ collisionSupport k x T =
      (collisionSupport k x T).filter
        (fun j => (π s j).val < Nat.ceil ((2*k : ℝ)/(2*k+1)*q)) := by
    ext j
    simp only [retained,collisionSupport,Finset.mem_inter,Finset.mem_filter]
    tauto
  exact (collisionIn_support_iff k x T (retained k T π s) S
    (Finset.filter_subset _ _)).trans (by rw [heq])

/-- When the collision support has size at most `d`, the no-collision event under retention
differs from its independent-sampling version by at most `η + m^2 / q`. -/
theorem collisionSupport_none_iid_gap {q R M d : ℕ} {η : ℝ}
    (k : ℕ) (x : Fin q → ZMod M) (T : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (hq : 0 < q) (hη : 0 ≤ η)
    (hπ : ApproxIndependent d η π) (hs : (collisionSupport k x T).card ≤ d) :
    let m := (collisionSupport k x T).card
    let i := (collisionSupport k x T).orderEmbOfFin rfl
    let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
    |eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) -
      (((Finset.univ : Finset (Fin m → Fin q)).filter (fun images =>
        ¬∃ S, CollisionIn k x (selectedTuplePositions cut i images) S)).card : ℝ)/(q : ℝ)^m| ≤
      η+(m : ℝ)^2/q := by
  classical
  let A := collisionSupport k x T
  let i := A.orderEmbOfFin rfl
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  let V : (Fin A.card → Fin q) → Prop := fun images =>
    ¬∃ S, CollisionIn k x (selectedTuplePositions cut i images) S
  have hmq : A.card ≤ q := by simpa using! Finset.card_le_univ A
  have h := approxIndependent_iid_event hq hη hπ hs hmq i i.injective V
  have hevent : (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) =
      (fun s => V (fun z => π s (i z))) := by
    funext s
    apply propext
    apply not_congr
    apply exists_congr
    intro S
    exact retained_collision_tuple_iff k x T π s S
  rw [hevent]
  convert! h using 1
  congr

/-- When the collision support has size at most `d`, the unique-collision event under retention
differs from its independent-sampling version by at most `η + m^2 / q`. -/
theorem collisionSupport_unique_iid_gap {q R M d : ℕ} {η : ℝ}
    (k : ℕ) (x : Fin q → ZMod M) (T : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (hq : 0 < q) (hη : 0 ≤ η)
    (hπ : ApproxIndependent d η π) (hs : (collisionSupport k x T).card ≤ d) :
    let m := (collisionSupport k x T).card
    let i := (collisionSupport k x T).orderEmbOfFin rfl
    let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
    |eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S) -
      (((Finset.univ : Finset (Fin m → Fin q)).filter (fun images =>
        ∃! S, CollisionIn k x (selectedTuplePositions cut i images) S)).card : ℝ)/(q : ℝ)^m| ≤
      η+(m : ℝ)^2/q := by
  classical
  let A := collisionSupport k x T
  let i := A.orderEmbOfFin rfl
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  let V : (Fin A.card → Fin q) → Prop := fun images =>
    ∃! S, CollisionIn k x (selectedTuplePositions cut i images) S
  have hmq : A.card ≤ q := by simpa using! Finset.card_le_univ A
  have h := approxIndependent_iid_event hq hη hπ hs hmq i i.injective V
  have hevent : (fun s => ∃! S, CollisionIn k x (retained k T π s) S) =
      (fun s => V (fun z => π s (i z))) := by
    funext s
    apply propext
    apply existsUnique_congr
    intro S
    exact retained_collision_tuple_iff k x T π s S
  rw [hevent]
  exact h

/-- The number of `t`-tuples whose every entry satisfies `P` is the `t`th power of the number of
entries satisfying `P`. -/
theorem iidBlocks_card {β : Type} [Fintype β] [DecidableEq β]
    (t : ℕ) (P : β → Prop) :
    ((Finset.univ : Finset (Fin t → β)).filter (fun f => ∀ a, P (f a))).card =
      ((Finset.univ : Finset β).filter P).card^t := by
  classical
  let e : {f : Fin t → β // ∀ a, P (f a)} ≃ (Fin t → {b : β // P b}) :=
    { toFun := fun f a => ⟨f.1 a,f.2 a⟩
      invFun := fun f => ⟨fun a => (f a).1,fun a => (f a).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_fun]
  simp only [Fintype.card_fin,Fintype.card_subtype]

/-- The number of `k`-tuples with a specified coordinate in `B` is `B.card * q^(k - 1)`. -/
theorem iidCoordinate_card (k q : ℕ) (a : Fin k) (B : Finset (Fin q)) :
    ((Finset.univ : Finset (Fin k → Fin q)).filter (fun f => f a ∈ B)).card =
      B.card*q^(k-1) := by
  classical
  let split := Equiv.funSplitAt a (Fin q)
  let e : {f : Fin k → Fin q // f a ∈ B} ≃ (B × ({z : Fin k // z ≠ a} → Fin q)) :=
    { toFun := fun f => (⟨f.1 a,f.2⟩,fun z => f.1 z)
      invFun := fun g => ⟨split.symm (g.1.val,g.2),by simp [split,Equiv.funSplitAt,
        Equiv.piSplitAt]⟩
      left_inv := fun f => by
        apply Subtype.ext
        exact split.left_inv f.1
      right_inv := fun g => by
        have h := split.right_inv (g.1.val,g.2)
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst h
        · funext z
          simp [split,Equiv.funSplitAt,Equiv.piSplitAt,z.2] }
  rw [← Fintype.card_subtype,Fintype.card_congr e,Fintype.card_prod,Fintype.card_fun]
  have hc : Fintype.card {z : Fin k // z ≠ a} = k-1 := by
    rw [Fintype.card_subtype_compl (p := fun z : Fin k => z = a)]
    simp
  simp only [Fintype.card_fin,Fintype.card_coe,hc]

/-- The number of `k`-tuples with at least one coordinate in `B` is at most `k * B.card * q^(k -
1)`. -/
theorem iidBadBlock_card (k q : ℕ) (B : Finset (Fin q)) :
    ((Finset.univ : Finset (Fin k → Fin q)).filter (fun f => ∃ a, f a ∈ B)).card ≤
      k*B.card*q^(k-1) := by
  classical
  have heq : (Finset.univ : Finset (Fin k → Fin q)).filter (fun f => ∃ a, f a ∈ B) =
      (Finset.univ : Finset (Fin k)).biUnion (fun a => Finset.univ.filter (fun f => f a ∈ B)) := by
    ext f
    simp
  rw [heq]
  calc
    _ ≤ ∑ a : Fin k, ((Finset.univ : Finset (Fin k → Fin q)).filter (fun f => f a ∈ B)).card :=
      Finset.card_biUnion_le
    _ = _ := by simp [iidCoordinate_card, Nat.mul_assoc]

/-- If `2 * k * B.card ≤ q` with positive `k` and `q`, the probability that each of `t`
independent blocks meets `B` is at most `2^(-t)`. -/
theorem iidAllBadBlocks_probability (k q t : ℕ) (hk : 0 < k) (hq : 0 < q)
    (B : Finset (Fin q)) (hB : 2*k*B.card ≤ q) :
    (((Finset.univ : Finset (Fin t → Fin k → Fin q)).filter
        (fun f => ∀ a, ∃ z, f a z ∈ B)).card : ℝ)/(q : ℝ)^(k*t) ≤ (1/2 : ℝ)^t := by
  classical
  let bad := (Finset.univ : Finset (Fin k → Fin q)).filter (fun f => ∃ z, f z ∈ B)
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : (0 : ℝ) < (q : ℝ)^k := pow_pos hqreal k
  have hcast : (bad.card : ℝ) ≤ (k : ℝ)*B.card*(q : ℝ)^(k-1) := by
    exact_mod_cast iidBadBlock_card k q B
  have hBreal : (2 : ℝ)*k*B.card ≤ q := by exact_mod_cast hB
  have hpoweq : (q : ℝ)^k = (q : ℝ)^(k-1)*(q : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hprob : (bad.card : ℝ)/(q : ℝ)^k ≤ 1/2 := by
    apply (div_le_iff₀ hpow).mpr
    rw [hpoweq]
    nlinarith [mul_nonneg (pow_nonneg hqreal.le (k-1)) (sub_nonneg.mpr hBreal)]
  have hnum : (bad.card : ℝ)^t/(q : ℝ)^(k*t) ≤ (1/2 : ℝ)^t := by
    rw [pow_mul,← div_pow]
    exact pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hpow.le) hprob t
  convert! hnum using 1
  congr 1
  have hcount := iidBlocks_card t (fun f : Fin k → Fin q => ∃ z, f z ∈ B)
  have hcastcount := congrArg (fun n : ℕ => (n : ℝ)) hcount
  push_cast at hcastcount
  convert! hcastcount using 1 <;> congr
  ext f
  simp [bad]

/-- The complement of the retained prefix has cardinality at most the amount specified by `2 * k
* outside.card ≤ q`. -/
theorem retained_outside_card (k q : ℕ) :
    2*k*((Finset.univ : Finset (Fin q)).filter
      (fun j => Nat.ceil ((2*k : ℝ)/(2*k+1)*q) ≤ j.val)).card ≤ q := by
  classical
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  have hden : (0 : ℝ) < 2*k+1 := by positivity
  have hratio : (2*k : ℝ)/(2*k+1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hcut : cut ≤ q := Nat.ceil_le.mpr (by
    exact mul_le_of_le_one_left (Nat.cast_nonneg q) hratio)
  have hcardLt : ((Finset.univ : Finset (Fin q)).filter (fun j => j.val < cut)).card = cut := by
    simpa [Nat.min_eq_right hcut] using! (Fin.card_filter_val_lt (n := q) (m := cut))
  have hcardSplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin q))) (fun j => j.val < cut)
  simp only [Finset.card_univ,Fintype.card_fin,hcardLt,not_lt] at hcardSplit
  have hsplit : (cut : ℝ)+
      (((Finset.univ : Finset (Fin q)).filter (fun j => cut ≤ j.val)).card : ℝ) = q := by
    exact_mod_cast hcardSplit
  have hceil := Nat.le_ceil ((2*k : ℝ)/(2*k+1)*q)
  have hceil' : (2*k : ℝ)/(2*k+1)*q ≤ (cut : ℝ) := hceil
  have hceilMul := (div_le_iff₀ hden).mp (show (2*k : ℝ)*q/(2*k+1) ≤ cut from by
    rw [← div_mul_eq_mul_div]
    exact hceil')
  have hreal : (2*k : ℝ)*
      (((Finset.univ : Finset (Fin q)).filter (fun j => cut ≤ j.val)).card : ℝ) ≤ q := by
    have hb0 : (0 : ℝ) ≤ (((Finset.univ : Finset (Fin q)).filter
      (fun j => cut ≤ j.val)).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hnat : 2*k*((Finset.univ : Finset (Fin q)).filter (fun j => cut ≤ j.val)).card ≤ q := by
    exact_mod_cast hreal
  convert! hnat using 1

/-- If retention leaves no collision, each supplied collision block has an element whose
permutation image lies outside the retained prefix. -/
theorem retained_none_misses_blocks {q R M t : ℕ} (k : ℕ)
    (x : Fin q → ZMod M) (T : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (s : Fin R)
    (i : Fin t → Fin k → Fin q)
    (hblocks : ∀ a, CollisionIn k x T (Finset.univ.image (i a)))
    (hnone : ¬∃ S, CollisionIn k x (retained k T π s) S) :
    ∀ a, ∃ z, Nat.ceil ((2*k : ℝ)/(2*k+1)*q) ≤ (π s (i a z)).val := by
  classical
  intro a
  by_contra h
  push Not at h
  apply hnone
  refine ⟨Finset.univ.image (i a),?_,(hblocks a).2⟩
  intro j hj
  obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_filter.mpr ⟨(hblocks a).1 (Finset.mem_image.mpr
    ⟨z,Finset.mem_univ _,rfl⟩),h z⟩

/-- Flattening a block-indexed tuple preserves the count of assignments for which every block
meets `B`. -/
theorem iidFlatAllBad_card (k q t : ℕ) (B : Finset (Fin q)) :
    ((Finset.univ : Finset (Fin (t*k) → Fin q)).filter
      (fun f => ∀ a : Fin t, ∃ z : Fin k, f (finProdFinEquiv (a,z)) ∈ B)).card =
    ((Finset.univ : Finset (Fin t → Fin k → Fin q)).filter
      (fun f => ∀ a, ∃ z, f a z ∈ B)).card := by
  classical
  let e : (Fin (t*k) → Fin q) ≃ (Fin t → Fin k → Fin q) :=
    { toFun := fun f a z => f (finProdFinEquiv (a,z))
      invFun := fun f n => f (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2
      left_inv := fun f => by
        funext n
        change f (finProdFinEquiv (finProdFinEquiv.symm n)) = f n
        rw [Equiv.apply_symm_apply]
      right_inv := fun f => by
        funext a z
        change f (finProdFinEquiv.symm (finProdFinEquiv (a,z))).1
          (finProdFinEquiv.symm (finProdFinEquiv (a,z))).2 = f a z
        rw [Equiv.symm_apply_apply] }
  let e' : {f : Fin (t*k) → Fin q // ∀ a : Fin t, ∃ z : Fin k,
      f (finProdFinEquiv (a,z)) ∈ B} ≃
      {f : Fin t → Fin k → Fin q // ∀ a, ∃ z, f a z ∈ B} :=
    { toFun := fun f => ⟨e f,f.2⟩
      invFun := fun f => ⟨e.symm f,by
        intro a
        obtain ⟨z,hz⟩ := f.2 a
        refine ⟨z,?_⟩
        change f.1 (finProdFinEquiv.symm (finProdFinEquiv (a,z))).1
          (finProdFinEquiv.symm (finProdFinEquiv (a,z))).2 ∈ B
        rw [Equiv.symm_apply_apply]
        exact hz⟩
      left_inv := fun f => Subtype.ext (e.left_inv f.1)
      right_inv := fun f => Subtype.ext (e.right_inv f.1) }
  rw [← Fintype.card_subtype,← Fintype.card_subtype,Fintype.card_congr e']

/-- Given `t` disjoint collision blocks and sufficient approximate independence, the
no-collision probability after retention is at most `2^(-t) + η + (t * k)^2 / q`. -/
theorem disjointBlocks_none_bound {q R M d t : ℕ} {η : ℝ}
    (k : ℕ) (hk : 0 < k) (hq : 0 < q) (hη : 0 ≤ η)
    (x : Fin q → ZMod M) (T : Finset (Fin q))
    (π : Fin R → Equiv.Perm (Fin q)) (hπ : ApproxIndependent d η π)
    (i : Fin t → Fin k → Fin q)
    (hi : Function.Injective (fun z : Fin t × Fin k => i z.1 z.2))
    (hblocks : ∀ a, CollisionIn k x T (Finset.univ.image (i a))) (htd : t*k ≤ d) :
    eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) ≤
      (1/2 : ℝ)^t+η+((t*k : ℕ) : ℝ)^2/q := by
  classical
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  let B := (Finset.univ : Finset (Fin q)).filter (fun j => cut ≤ j.val)
  let flat : Fin (t*k) → Fin q := fun n => i (finProdFinEquiv.symm n).1
    (finProdFinEquiv.symm n).2
  have hflat : Function.Injective flat := hi.comp finProdFinEquiv.symm.injective
  have hmq : t*k ≤ q := by
    have h := Fintype.card_le_of_injective flat hflat
    simpa using! h
  let V : (Fin (t*k) → Fin q) → Prop := fun f =>
    ∀ a : Fin t, ∃ z : Fin k, f (finProdFinEquiv (a,z)) ∈ B
  have hclose := approxIndependent_iid_event hq hη hπ htd hmq flat hflat V
  have hhalf := iidAllBadBlocks_probability k q t hk hq B (retained_outside_card k q)
  have hflatHalf : (((Finset.univ : Finset (Fin (t*k) → Fin q)).filter V).card : ℝ)/
      (q : ℝ)^(t*k) ≤ (1/2 : ℝ)^t := by
    have hcount := iidFlatAllBad_card k q t B
    have hcountreal := congrArg (fun n : ℕ => (n : ℝ)) hcount
    have hcountreal' : (((Finset.univ : Finset (Fin (t*k) → Fin q)).filter V).card : ℝ) =
        (((Finset.univ : Finset (Fin t → Fin k → Fin q)).filter
          (fun f => ∀ a, ∃ z, f a z ∈ B)).card : ℝ) := by
      convert! hcountreal using 1
    rw [hcountreal',Nat.mul_comm t k]
    exact hhalf
  have hmono : eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) ≤
      eventProbability (fun s => V (fun z => π s (flat z))) := by
    apply eventProbability_mono
    intro s hs a
    obtain ⟨z,hz⟩ := retained_none_misses_blocks k x T π s i hblocks hs a
    refine ⟨z,?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change cut ≤ (π s (flat (finProdFinEquiv (a,z)))).val
    dsimp only [flat]
    rw [Equiv.symm_apply_apply]
    exact hz
  have hupper := (abs_le.mp hclose).2
  calc
    _ ≤ eventProbability (fun s => V (fun z => π s (flat z))) := hmono
    _ ≤ (((Finset.univ : Finset (Fin (t*k) → Fin q)).filter V).card : ℝ)/(q : ℝ)^(t*k)+
        (η+((t*k : ℕ) : ℝ)^2/q) := by
      convert! le_add_of_sub_left_le hupper using 1
      congr
    _ ≤ (1/2 : ℝ)^t+(η+((t*k : ℕ) : ℝ)^2/q) := add_le_add hflatHalf le_rfl
    _ = _ := by ring

/-- For positive `k`, there exists a pairwise disjoint family of collisions whose union
intersects every collision in `T`. -/
theorem exists_maximal_collision_packing {q M : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) :
    ∃ P : Finset (Finset (Fin q)),
      (∀ S ∈ P, CollisionIn k x T S) ∧
      (P : Set (Finset (Fin q))).Pairwise (fun S U => Disjoint S U) ∧
      ∀ S, CollisionIn k x T S → ¬Disjoint S (P.biUnion id) := by
  classical
  let packs : Finset (Finset (Finset (Fin q))) := Finset.univ.filter
    (fun P => (∀ S ∈ P, CollisionIn k x T S) ∧ (P : Set (Finset (Fin q))).Pairwise (fun S U => Disjoint S U))
  have hempty : (∅ : Finset (Finset (Fin q))) ∈ packs := by simp [packs]
  obtain ⟨P,hP,hmax⟩ := packs.exists_max_image Finset.card ⟨∅,hempty⟩
  obtain ⟨hblocks,hpair⟩ := (Finset.mem_filter.mp hP).2
  refine ⟨P,hblocks,hpair,?_⟩
  intro S hS hdis
  have hnot : S ∉ P := by
    intro hSP
    have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hS.2.1]; exact hk)
    obtain ⟨i,hi⟩ := hSne
    exact (Finset.disjoint_left.mp hdis) hi
      (Finset.mem_biUnion.mpr ⟨S,hSP,hi⟩)
  have hnew : insert S P ∈ packs := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · intro U hU
      rcases Finset.mem_insert.mp hU with rfl | hU
      · exact hS
      · exact hblocks U hU
    · intro U hU V hV hUV
      have hUm : U ∈ insert S P := hU
      have hVm : V ∈ insert S P := hV
      by_cases hUS : U = S
      · subst U
        have hVP : V ∈ P := (Finset.mem_insert.mp hVm).resolve_left (Ne.symm hUV)
        exact hdis.mono_right (Finset.subset_biUnion_of_mem (s := P) id hVP)
      · by_cases hVS : V = S
        · subst V
          have hUP : U ∈ P := (Finset.mem_insert.mp hUm).resolve_left hUS
          exact (hdis.mono_right (Finset.subset_biUnion_of_mem (s := P) id hUP)).symm
        · exact hpair ((Finset.mem_insert.mp hUm).resolve_left hUS)
            ((Finset.mem_insert.mp hVm).resolve_left hVS) hUV
  have hcontr := hmax (insert S P) hnew
  rw [Finset.card_insert_of_notMem hnot] at hcontr
  omega

/-- If every collision intersects `U`, each value class in `T` outside `U` has fewer than `k`
elements. -/
theorem maximalPacking_remainingClass_lt {q M : ℕ} (k : ℕ)
    (x : Fin q → ZMod M) (T U : Finset (Fin q))
    (hmax : ∀ S, CollisionIn k x T S → ¬Disjoint S U) (v : ZMod M) :
    ((T \ U).filter (fun i => x i = v)).card < k := by
  classical
  by_contra h
  have hkcard : k ≤ ((T \ U).filter (fun i => x i = v)).card := le_of_not_gt h
  obtain ⟨S,hS,hcard⟩ := Finset.exists_subset_card_eq hkcard
  have hST : S ⊆ T := hS.trans ((Finset.filter_subset _ _).trans Finset.sdiff_subset)
  have hcol : CollisionIn k x T S := ⟨hST,hcard,v,fun i hi =>
    (Finset.mem_filter.mp (hS hi)).2⟩
  apply hmax S hcol
  apply Finset.disjoint_left.mpr
  intro i hi hU
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hS hi)).1).2 hU

/-- The collision support has size at most `2 * k * P.card` when `P` consists of collisions and
its union intersects every collision. -/
theorem maximalPacking_support_card {q M : ℕ} (k : ℕ)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (P : Finset (Finset (Fin q)))
    (hblocks : ∀ S ∈ P, CollisionIn k x T S)
    (hmax : ∀ S, CollisionIn k x T S → ¬Disjoint S (P.biUnion id)) :
    (collisionSupport k x T).card ≤ 2*k*P.card := by
  classical
  let U := P.biUnion id
  let value : P → ZMod M := fun B => (hblocks B.1 B.2).2.2.choose
  have hvalue (B : P) (i : Fin q) (hi : i ∈ B.1) : x i = value B :=
    (hblocks B.1 B.2).2.2.choose_spec i hi
  let left : P → Finset (Fin q) := fun B => (T \ U).filter (fun i => x i = value B)
  have hcover : collisionSupport k x T ⊆ U ∪ Finset.univ.biUnion left := by
    intro i hi
    by_cases hiU : i ∈ U
    · exact Finset.mem_union_left _ hiU
    · obtain ⟨hiT,S,hS,hiS⟩ := Finset.mem_filter.mp hi
      obtain ⟨v,hv⟩ := hS.2.2
      have hmeet := hmax S hS
      obtain ⟨j,hjS,hjU⟩ := Finset.not_disjoint_iff.mp hmeet
      obtain ⟨B,hBP,hjB⟩ := Finset.mem_biUnion.mp hjU
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨⟨B,hBP⟩,Finset.mem_univ _,?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨hiT,hiU⟩,?_⟩
      exact (hv i hiS).trans ((hv j hjS).symm.trans (hvalue ⟨B,hBP⟩ j hjB))
  have hUcard : U.card ≤ k*P.card := by
    calc
      _ ≤ ∑ B ∈ P, B.card := Finset.card_biUnion_le
      _ = _ := by
        have hc : ∀ B ∈ P, B.card = k := fun B hB => (hblocks B hB).2.1
        rw [Finset.sum_congr rfl hc]
        simp [Nat.mul_comm]
  have hleftcard : (Finset.univ.biUnion left).card ≤ (k-1)*P.card := by
    calc
      _ ≤ ∑ B : P, (left B).card := Finset.card_biUnion_le
      _ ≤ ∑ B : P, (k-1) := Finset.sum_le_sum fun B _ => by
        have hlt := maximalPacking_remainingClass_lt k x T U hmax (value B)
        exact Nat.le_sub_one_of_lt hlt
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ ≤ (U ∪ Finset.univ.biUnion left).card := Finset.card_le_card hcover
    _ ≤ U.card+(Finset.univ.biUnion left).card := Finset.card_union_le _ _
    _ ≤ k*P.card+(k-1)*P.card := Nat.add_le_add hUcard hleftcard
    _ ≤ _ := by nlinarith [Nat.sub_le k 1]

/-- For positive `k`, either the collision support has size at most `2 * k * (t - 1)` or there
are `t` pairwise disjoint indexed collisions [Ambainis2007ElementDistinctness]. -/
theorem collision_packing_dichotomy {q M : ℕ} (k : ℕ) (hk : 0 < k)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (t : ℕ) :
    (collisionSupport k x T).card ≤ 2*k*(t-1) ∨
      ∃ i : Fin t → Fin k → Fin q,
        Function.Injective (fun z : Fin t × Fin k => i z.1 z.2) ∧
        ∀ a, CollisionIn k x T (Finset.univ.image (i a)) := by
  classical
  obtain ⟨P,hblocks,hpair,hmax⟩ := exists_maximal_collision_packing k hk x T
  by_cases hpt : P.card < t
  · left
    exact le_trans (maximalPacking_support_card k x T P hblocks hmax)
      (Nat.mul_le_mul_left (2*k) (Nat.le_sub_one_of_lt hpt))
  · right
    have hcard : Fintype.card (Fin t) ≤ Fintype.card P := by simpa using! le_of_not_gt hpt
    let e : Fin t ↪ P := Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
    let i : Fin t → Fin k → Fin q := fun a =>
      (e a).1.orderEmbOfFin (hblocks (e a).1 (e a).2).2.1
    refine ⟨i,?_,?_⟩
    · rintro ⟨a,z⟩ ⟨b,w⟩ h
      by_cases hab : a = b
      · subst b
        have hzw : z = w := ((e a).1.orderEmbOfFin
          (hblocks (e a).1 (e a).2).2.1).injective h
        exact Prod.ext rfl hzw
      · have hne : (e a).1 ≠ (e b).1 := fun he => hab (e.injective (Subtype.ext he))
        have hd := hpair (e a).2 (e b).2 hne
        have hza : i a z ∈ (e a).1 := (e a).1.orderEmbOfFin_mem _ z
        have hwb : i b w ∈ (e b).1 := (e b).1.orderEmbOfFin_mem _ w
        have hwb' : i a z ∈ (e b).1 := by
          change i a z = i b w at h
          rw [h]
          exact hwb
        exact ((Finset.disjoint_left.mp hd) hza hwb').elim
    · intro a
      dsimp only [i]
      rw [Finset.image_orderEmbOfFin_univ]
      exact hblocks (e a).1 (e a).2

/-- The number of functions satisfying independent coordinate constraints is the product of the
numbers of allowed values at each coordinate. -/
theorem iidConstraints_card {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (P : α → β → Prop) :
    ((Finset.univ : Finset (α → β)).filter (fun f => ∀ z, P z (f z))).card =
      ∏ z : α, ((Finset.univ : Finset β).filter (P z)).card := by
  classical
  let e : {f : α → β // ∀ z, P z (f z)} ≃ (∀ z : α, {b : β // P z b}) :=
    { toFun := fun f z => ⟨f.1 z,f.2 z⟩
      invFun := fun f => ⟨fun z => (f z).1,fun z => (f z).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_subtype,Fintype.card_congr e,Fintype.card_pi]
  simp only [Fintype.card_subtype]

/-- The number of `m`-tuples whose coordinates in `B` occur at exactly `S` is `B.card^S.card *
(q - B.card)^(m - S.card)`. -/
theorem iidMask_card (m q : ℕ) (B : Finset (Fin q)) (S : Finset (Fin m)) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => Finset.univ.filter (fun z => f z ∈ B) = S)).card =
      B.card^S.card*(q-B.card)^(m-S.card) := by
  classical
  have heq : (Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => Finset.univ.filter (fun z => f z ∈ B) = S) =
      Finset.univ.filter (fun f => ∀ z, (f z ∈ B ↔ z ∈ S)) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro h z
      have hm : z ∈ Finset.univ.filter (fun z => f z ∈ B) ↔ z ∈ S := by rw [h]
      simpa using! hm
    · intro h
      ext z
      simpa using! h z
  rw [heq]
  have hconstraints := iidConstraints_card (fun z : Fin m => fun b : Fin q => b ∈ B ↔ z ∈ S)
  trans ∏ z : Fin m, ((Finset.univ : Finset (Fin q)).filter (fun b => b ∈ B ↔ z ∈ S)).card
  · convert! hconstraints using 1 <;> congr
    funext z
    congr
  have hnotB : (Finset.univ : Finset (Fin q)).filter (fun b => b ∉ B) = Bᶜ := by
    ext b
    simp
  have hnotS : (Finset.univ : Finset (Fin m)).filter (fun z => z ∉ S) = Sᶜ := by
    ext z
    simp
  have hcoord (z : Fin m) :
      ((Finset.univ : Finset (Fin q)).filter (fun b => b ∈ B ↔ z ∈ S)).card =
        if z ∈ S then B.card else q-B.card := by
    by_cases hz : z ∈ S
    · simp [hz]
    · simp only [hz,iff_false,if_false]
      rw [hnotB,Finset.card_compl,Fintype.card_fin]
  simp_rw [hcoord]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hposS : (Finset.univ : Finset (Fin m)).filter (fun z => z ∈ S) = S := by
    ext z
    simp
  rw [hposS,hnotS,Finset.card_compl,Fintype.card_fin]

/-- The number of `m`-tuples having exactly `l` coordinates in `B` is the stated binomial
coefficient times the two occupancy powers. -/
theorem iidOccupancy_card (m q l : ℕ) (B : Finset (Fin q)) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card = l)).card =
      m.choose l*B.card^l*(q-B.card)^(m-l) := by
  classical
  let mask : (Fin m → Fin q) → Finset (Fin m) := fun f =>
    Finset.univ.filter (fun z => f z ∈ B)
  have hsplit := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin m → Fin q)) (Finset.univ.powersetCard l) mask
  have hsplit' : ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => (mask f).card = l)).card =
      ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
        ((Finset.univ : Finset (Fin m → Fin q)).filter (fun f => mask f = S)).card := by
    simpa only [Finset.mem_powersetCard,Finset.subset_univ,true_and] using! hsplit.symm
  rw [hsplit']
  calc
    _ = ∑ S ∈ (Finset.univ : Finset (Fin m)).powersetCard l,
        B.card^l*(q-B.card)^(m-l) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hcard := (Finset.mem_powersetCard.mp hS).2
      rw [iidMask_card,hcard]
    _ = _ := by simp [Finset.card_powersetCard,Nat.mul_assoc]

/-- For positive `q` and `l ≤ m`, the probability of exactly `l` coordinates in `B` is the
binomial mass with parameter `B.card / q`. -/
theorem iidOccupancy_probability (m q l : ℕ) (hq : 0 < q) (hl : l ≤ m)
    (B : Finset (Fin q)) :
    (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card = l)).card : ℝ)/(q : ℝ)^m =
      collisionBinomialMass m ((B.card : ℝ)/q) l := by
  classical
  have hB : B.card ≤ q := by simpa using! Finset.card_le_univ B
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hcard := iidOccupancy_card m q l B
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) hcard
  push_cast [Nat.cast_sub hB] at hcast
  have hcard' : (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card = l)).card : ℝ) =
      (m.choose l : ℝ)*(B.card : ℝ)^l*((q : ℝ)-B.card)^(m-l) := by
    convert! hcast using 1
  rw [hcard']
  unfold collisionBinomialMass
  have hqpow : (q : ℝ)^m = (q : ℝ)^l*(q : ℝ)^(m-l) := by
    rw [← pow_add]
    congr 1
    omega
  have hpident : 1-(B.card : ℝ)/q = ((q : ℝ)-B.card)/q := by field_simp
  rw [hpident,div_pow,div_pow,hqpow]
  field_simp

/-- Under the stated positive-size and retention-ratio hypotheses, fewer-than-`k` occupancy
assignments are no more numerous than exactly-`k` assignments. -/
theorem iidOccupancy_less_le_equal (k m q : ℕ) (hkm : k ≤ m) (hq : 0 < q)
    (B : Finset (Fin q)) (hBpos : 0 < B.card) (hkeep : 2*k*(q-B.card) ≤ B.card) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card < k)).card ≤
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card = k)).card := by
  classical
  let occupancy : (Fin m → Fin q) → ℕ := fun f =>
    (Finset.univ.filter (fun z => f z ∈ B)).card
  have hsplit := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin m → Fin q)) (Finset.range k) occupancy
  simp only [Finset.mem_range] at hsplit
  have hsplit' : ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => occupancy f < k)).card =
      ∑ l ∈ Finset.range k, ((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun f => occupancy f = l)).card := by
    convert! hsplit.symm using 1
  have hB : B.card ≤ q := by simpa using! Finset.card_le_univ B
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  let p : ℝ := (B.card : ℝ)/q
  have hp0 : 0 < p := div_pos (by exact_mod_cast hBpos) hqp
  have hp1 : p ≤ 1 := (div_le_one hqp).mpr (by exact_mod_cast hB)
  have hpkeep : 2*k*(1-p) ≤ p := by
    have hh : (2*k : ℝ)*((q : ℝ)-B.card) ≤ B.card := by
      have hc := (show ((2*k*(q-B.card) : ℕ) : ℝ) ≤ B.card from by exact_mod_cast hkeep)
      simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hB] using! hc
    dsimp [p]
    have hid : 2*(k : ℝ)*(1-(B.card : ℝ)/q) =
        (2*(k : ℝ)*((q : ℝ)-B.card))/q := by field_simp
    rw [hid]
    exact div_le_div_of_nonneg_right hh hqp.le
  have hmass := collisionBinomialMass_no_le_unique k m hkm p hp0 hp1 hpkeep
  have hprob : (((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => occupancy f < k)).card : ℝ)/(q : ℝ)^m ≤
      (((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun f => occupancy f = k)).card : ℝ)/(q : ℝ)^m := by
    rw [hsplit']
    push_cast
    rw [Finset.sum_div]
    calc
      _ = ∑ l ∈ Finset.range k, collisionBinomialMass m p l := by
        apply Finset.sum_congr rfl
        intro l hl
        exact iidOccupancy_probability m q l hq (by have := Finset.mem_range.mp hl; omega) B
      _ ≤ collisionBinomialMass m p k := hmass
      _ = _ := (iidOccupancy_probability m q k hq hkm B).symm
  exact_mod_cast (div_le_div_iff_of_pos_right (pow_pos hqp m)).mp hprob

/-- Counts of events depending separately on a finite subset and its complement multiply to give
the count of their conjunction. -/
theorem iidSubsetEvents_card {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (I : Finset α)
    (P : (I → β) → Prop) (Q : ({z : α // z ∉ I} → β) → Prop) :
    ((Finset.univ : Finset (α → β)).filter (fun f =>
      P (fun z : I => f z) ∧ Q (fun z : {z : α // z ∉ I} => f z))).card =
      ((Finset.univ : Finset (I → β)).filter P).card*
      ((Finset.univ : Finset ({z : α // z ∉ I} → β)).filter Q).card := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun z : α => z ∈ I) (fun _ => β)
  let e' : {f : α → β // P (fun z : I => f z) ∧ Q (fun z : {z : α // z ∉ I} => f z)} ≃
      ({f : I → β // P f} × {f : {z : α // z ∉ I} → β // Q f}) :=
    { toFun := fun f => (⟨(e f).1,f.2.1⟩,⟨(e f).2,f.2.2⟩)
      invFun := fun g => ⟨e.symm (g.1.val,g.2.val),by
        constructor
        · change P ((e (e.symm (g.1.val,g.2.val))).1)
          rw [Equiv.apply_symm_apply]
          exact g.1.prop
        · change Q ((e (e.symm (g.1.val,g.2.val))).2)
          rw [Equiv.apply_symm_apply]
          exact g.2.prop⟩
      left_inv := fun f => Subtype.ext (e.left_inv f.1)
      right_inv := fun g => by
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst (e.right_inv (g.1.val,g.2.val))
        · apply Subtype.ext
          exact congrArg Prod.snd (e.right_inv (g.1.val,g.2.val)) }
  rw [← Fintype.card_subtype,Fintype.card_congr e',Fintype.card_prod,
    Fintype.card_subtype,Fintype.card_subtype]

/-- There is no collision in `T` exactly when the chosen value class has size below `k` and its
complement contains no collision. -/
theorem collisionIn_value_class_none_iff {q M : ℕ} (k : ℕ)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (v : ZMod M) :
    (¬∃ S, CollisionIn k x T S) ↔
      (T.filter (fun i => x i = v)).card < k ∧
      ¬∃ S, CollisionIn k x (T \ T.filter (fun i => x i = v)) S := by
  classical
  let I := T.filter (fun i => x i = v)
  constructor
  · intro hnone
    constructor
    · by_contra hcard
      obtain ⟨S,hS,hSk⟩ := Finset.exists_subset_card_eq (le_of_not_gt hcard)
      exact hnone ⟨S,hS.trans (Finset.filter_subset _ _),hSk,v,
        fun i hi => (Finset.mem_filter.mp (hS hi)).2⟩
    · rintro ⟨S,hS,hcol⟩
      exact hnone ⟨S,hS.trans Finset.sdiff_subset,hcol⟩
  · rintro ⟨hlt,hother⟩ ⟨S,hS,hcard,u,hu⟩
    by_cases huv : u = v
    · have hSI : S ⊆ I := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨hS hi,(hu i hi).trans huv⟩
      have hle := Finset.card_le_card hSI
      rw [hcard] at hle
      exact (not_le_of_gt hlt) hle
    · apply hother
      refine ⟨S,?_,hcard,u,hu⟩
      intro i hi
      apply Finset.mem_sdiff.mpr
      refine ⟨hS hi,?_⟩
      intro hI
      exact huv ((hu i hi).symm.trans (Finset.mem_filter.mp hI).2)

/-- If a value class has exactly `k` elements and its complement contains no collision, then `T`
contains a unique collision. -/
theorem collisionIn_value_class_unique {q M : ℕ} (k : ℕ)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (v : ZMod M)
    (hk : (T.filter (fun i => x i = v)).card = k)
    (hother : ¬∃ S, CollisionIn k x (T \ T.filter (fun i => x i = v)) S) :
    ∃! S, CollisionIn k x T S := by
  classical
  let I := T.filter (fun i => x i = v)
  refine ⟨I,⟨Finset.filter_subset _ _,hk,v,fun i hi => (Finset.mem_filter.mp hi).2⟩,?_⟩
  rintro S ⟨hS,hcard,u,hu⟩
  by_cases huv : u = v
  · have hSI : S ⊆ I := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨hS hi,(hu i hi).trans huv⟩
    exact Finset.eq_of_subset_of_card_le hSI (by rw [hk,hcard])
  · exfalso
    apply hother
    refine ⟨S,?_,hcard,u,hu⟩
    intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨hS hi,?_⟩
    intro hI
    exact huv ((hu i hi).symm.trans (Finset.mem_filter.mp hI).2)

/-- Reindexing a finite domain by `Fin` of its cardinality preserves the count of any occupancy
event. -/
theorem iidDomainOccupancy_card {α : Type} [Fintype α] [DecidableEq α]
    (q : ℕ) (B : Finset (Fin q)) (V : ℕ → Prop) :
    ((Finset.univ : Finset (α → Fin q)).filter
      (fun f => V (Finset.univ.filter (fun z => f z ∈ B)).card)).card =
    ((Finset.univ : Finset (Fin (Fintype.card α) → Fin q)).filter
      (fun f => V (Finset.univ.filter (fun z => f z ∈ B)).card)).card := by
  classical
  let ea := Fintype.equivFin α
  let ef : (α → Fin q) ≃ (Fin (Fintype.card α) → Fin q) :=
    { toFun := fun f z => f (ea.symm z)
      invFun := fun f z => f (ea z)
      left_inv := fun f => by
        funext z
        change f (ea.symm (ea z)) = f z
        rw [Equiv.symm_apply_apply]
      right_inv := fun f => by
        funext z
        change f (ea (ea.symm z)) = f z
        rw [Equiv.apply_symm_apply] }
  have hcount (f : α → Fin q) :
      (Finset.univ.filter (fun z => f z ∈ B)).card =
      (Finset.univ.filter (fun z => ef f z ∈ B)).card := by
    let e : {z : α // f z ∈ B} ≃ {z : Fin (Fintype.card α) // ef f z ∈ B} :=
      { toFun := fun z => ⟨ea z,by
          change f (ea.symm (ea z.1)) ∈ B
          rw [Equiv.symm_apply_apply]
          exact z.prop⟩
        invFun := fun z => ⟨ea.symm z,z.prop⟩
        left_inv := fun z => Subtype.ext (ea.left_inv z.1)
        right_inv := fun z => Subtype.ext (ea.right_inv z.1) }
    simpa only [Fintype.card_subtype] using! Fintype.card_congr e
  let e : {f : α → Fin q // V (Finset.univ.filter (fun z => f z ∈ B)).card} ≃
      {f : Fin (Fintype.card α) → Fin q // V (Finset.univ.filter (fun z => f z ∈ B)).card} :=
    { toFun := fun f => ⟨ef f,by rw [← hcount f.1]; exact f.prop⟩
      invFun := fun f => ⟨ef.symm f,by
        rw [hcount (ef.symm f),Equiv.apply_symm_apply]
        exact f.prop⟩
      left_inv := fun f => Subtype.ext (ef.left_inv f.1)
      right_inv := fun f => Subtype.ext (ef.right_inv f.1) }
  simpa only [Fintype.card_subtype] using! Fintype.card_congr e

/-- For an arbitrary finite domain, the stated retention-ratio hypotheses bound the count of
occupancy below `k` by the count of occupancy equal to `k`. -/
theorem iidDomainOccupancy_less_le_equal {α : Type} [Fintype α] [DecidableEq α]
    (k q : ℕ) (hkm : k ≤ Fintype.card α) (hq : 0 < q)
    (B : Finset (Fin q)) (hBpos : 0 < B.card) (hkeep : 2*k*(q-B.card) ≤ B.card) :
    ((Finset.univ : Finset (α → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card < k)).card ≤
    ((Finset.univ : Finset (α → Fin q)).filter
      (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card = k)).card := by
  classical
  calc
    _ = ((Finset.univ : Finset (Fin (Fintype.card α) → Fin q)).filter
        (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card < k)).card := by
      convert! iidDomainOccupancy_card (α := α) q B (fun n => n < k) using 1 <;> congr
    _ ≤ ((Finset.univ : Finset (Fin (Fintype.card α) → Fin q)).filter
        (fun f => (Finset.univ.filter (fun z => f z ∈ B)).card = k)).card :=
      iidOccupancy_less_le_equal k (Fintype.card α) q hkm hq B hBpos hkeep
    _ = _ := by
      convert! (iidDomainOccupancy_card (α := α) q B (fun n => n = k)).symm using 1 <;> congr

/-- The retained mask on a subset, mapped to the ambient type, is the intersection of the
ambient mask with that subset. -/
theorem iidMask_subtype_image {α : Type} [Fintype α] [DecidableEq α]
    (q : ℕ) (B : Finset (Fin q)) (I : Finset α) (f : α → Fin q) :
    ((Finset.univ : Finset I).filter (fun z : I => f z.val ∈ B)).image Subtype.val =
      (Finset.univ.filter (fun z => f z ∈ B)) ∩ I := by
  classical
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,i.prop⟩
  · rintro ⟨hz,hI⟩
    exact ⟨⟨z,hI⟩,hz,rfl⟩

/-- The retained mask on a subset's complement, mapped to the ambient type, is the ambient mask
with that subset removed. -/
theorem iidMask_compl_image {α : Type} [Fintype α] [DecidableEq α]
    (q : ℕ) (B : Finset (Fin q)) (I : Finset α) (f : α → Fin q) :
    ((Finset.univ : Finset {z : α // z ∉ I}).filter (fun z : {z : α // z ∉ I} => f z.val ∈ B)).image Subtype.val =
      (Finset.univ.filter (fun z => f z ∈ B)) \ I := by
  classical
  ext z
  simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact ⟨hi,i.prop⟩
  · rintro ⟨hz,hI⟩
    exact ⟨⟨z,hI⟩,hz,rfl⟩

/-- When the input has a collision and the stated retention ratio holds, independent sampling
yields no more no-collision assignments than unique-collision assignments. -/
theorem iidCollision_none_le_unique (k m q M : ℕ) (hq : 0 < q)
    (x : Fin m → ZMod M) (hx : HasCollision k x) (B : Finset (Fin q))
    (hBpos : 0 < B.card) (hkeep : 2*k*(q-B.card) ≤ B.card) :
    ((Finset.univ : Finset (Fin m → Fin q)).filter (fun f =>
      ¬∃ S, CollisionIn k x (Finset.univ.filter (fun z => f z ∈ B)) S)).card ≤
    ((Finset.univ : Finset (Fin m → Fin q)).filter (fun f =>
      ∃! S, CollisionIn k x (Finset.univ.filter (fun z => f z ∈ B)) S)).card := by
  classical
  obtain ⟨S0,hS0,v,hv⟩ := hx
  let I := (Finset.univ : Finset (Fin m)).filter (fun z => x z = v)
  have hIcard : k ≤ Fintype.card I := by
    have hSI : S0 ⊆ I := fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv z hz⟩
    have hc := Finset.card_le_card hSI
    simpa only [hS0,Fintype.card_coe] using! hc
  let mask := fun f : Fin m → Fin q => Finset.univ.filter (fun z => f z ∈ B)
  let Pnone : (I → Fin q) → Prop := fun f =>
    ((Finset.univ : Finset I).filter (fun z => f z ∈ B)).card < k
  let Pexact : (I → Fin q) → Prop := fun f =>
    ((Finset.univ : Finset I).filter (fun z => f z ∈ B)).card = k
  let Q : ({z : Fin m // z ∉ I} → Fin q) → Prop := fun f =>
    ¬∃ S, CollisionIn k x
      (((Finset.univ : Finset {z : Fin m // z ∉ I}).filter (fun z => f z ∈ B)).image Subtype.val) S
  have hclass (f : Fin m → Fin q) : (mask f).filter (fun z => x z = v) = mask f ∩ I := by
    ext z
    simp [mask,I]
  have hrest (f : Fin m → Fin q) : mask f \ (mask f).filter (fun z => x z = v) = mask f \ I := by
    rw [hclass]
    ext z
    simp
  have hclassCard (f : Fin m → Fin q) : ((mask f).filter (fun z => x z = v)).card =
      ((Finset.univ : Finset I).filter (fun z : I => f z.val ∈ B)).card := by
    rw [hclass,← iidMask_subtype_image q B I f,
      Finset.card_image_of_injective _ Subtype.val_injective]
  have hnone (f : Fin m → Fin q) : (¬∃ S, CollisionIn k x (mask f) S) ↔
      Pnone (fun z : I => f z) ∧ Q (fun z : {z : Fin m // z ∉ I} => f z) := by
    rw [collisionIn_value_class_none_iff k x (mask f) v,hclassCard,hrest,
      ← iidMask_compl_image q B I f]
  have hexact (f : Fin m → Fin q)
      (hp : Pexact (fun z : I => f z)) (hqrest : Q (fun z : {z : Fin m // z ∉ I} => f z)) :
      ∃! S, CollisionIn k x (mask f) S := by
    apply collisionIn_value_class_unique k x (mask f) v
    · rw [hclassCard]
      exact hp
    · rw [hrest,← iidMask_compl_image q B I f]
      exact hqrest
  have hnoneSet : (Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => ¬∃ S, CollisionIn k x (mask f) S) =
      Finset.univ.filter (fun f => Pnone (fun z : I => f z) ∧
        Q (fun z : {z : Fin m // z ∉ I} => f z)) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hnone f
  have huniqueSubset : (Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => Pexact (fun z : I => f z) ∧ Q (fun z : {z : Fin m // z ∉ I} => f z)) ⊆
      Finset.univ.filter (fun f => ∃! S, CollisionIn k x (mask f) S) := by
    intro f hf
    obtain ⟨hp,hqrest⟩ := (Finset.mem_filter.mp hf).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hexact f hp hqrest⟩
  have hclassCompare := iidDomainOccupancy_less_le_equal (α := I) k q hIcard hq B hBpos hkeep
  have hnoneCount := iidSubsetEvents_card I Pnone Q
  have hexactCount := iidSubsetEvents_card I Pexact Q
  change ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => ¬∃ S, CollisionIn k x (mask f) S)).card ≤
    ((Finset.univ : Finset (Fin m → Fin q)).filter
      (fun f => ∃! S, CollisionIn k x (mask f) S)).card
  rw [hnoneSet]
  calc
    _ = ((Finset.univ : Finset (I → Fin q)).filter Pnone).card*
        ((Finset.univ : Finset ({z : Fin m // z ∉ I} → Fin q)).filter Q).card := by
      convert! hnoneCount using 1 <;> congr
    _ ≤ ((Finset.univ : Finset (I → Fin q)).filter Pexact).card*
        ((Finset.univ : Finset ({z : Fin m // z ∉ I} → Fin q)).filter Q).card :=
      Nat.mul_le_mul_right _ hclassCompare
    _ = ((Finset.univ : Finset (Fin m → Fin q)).filter
        (fun f => Pexact (fun z : I => f z) ∧ Q (fun z : {z : Fin m // z ∉ I} => f z))).card := by
      convert! hexactCount.symm using 1 <;> congr
    _ ≤ _ := Finset.card_le_card huniqueSubset

/-- An injective index map transports a collision and its ambient set to their images. -/
theorem collisionIn_image_map {m q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (i : Fin m → Fin q) (hi : Function.Injective i) (U S : Finset (Fin m))
    (h : CollisionIn k (fun z => x (i z)) U S) :
    CollisionIn k x (U.image i) (S.image i) := by
  obtain ⟨hSU,hcard,v,hv⟩ := h
  refine ⟨Finset.image_subset_image hSU,?_,v,?_⟩
  · rw [Finset.card_image_of_injective _ hi]
    exact hcard
  · intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact hv a ha

/-- Every collision in the image of an injective index map lifts to a collision in its domain
with the specified image. -/
theorem collisionIn_image_preimage {m q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (i : Fin m → Fin q) (hi : Function.Injective i) (U : Finset (Fin m))
    (S : Finset (Fin q)) (h : CollisionIn k x (U.image i) S) :
    ∃ V, CollisionIn k (fun z => x (i z)) U V ∧ V.image i = S := by
  classical
  let V := U.filter (fun a => i a ∈ S)
  have himage : V.image i = S := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ha).2
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (h.1 hz)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hz⟩,rfl⟩
  obtain ⟨_,hcard,v,hv⟩ := h
  refine ⟨V,⟨Finset.filter_subset _ _,?_,v,?_⟩,himage⟩
  · rw [← Finset.card_image_of_injective _ hi,himage]
    exact hcard
  · intro z hz
    exact hv (i z) (Finset.mem_filter.mp hz).2

/-- An injective index map preserves the existence of a collision in the corresponding ambient
sets. -/
theorem collisionIn_image_exists_iff {m q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (i : Fin m → Fin q) (hi : Function.Injective i) (U : Finset (Fin m)) :
    (∃ S, CollisionIn k x (U.image i) S) ↔
      ∃ S, CollisionIn k (fun z => x (i z)) U S := by
  constructor
  · rintro ⟨S,hS⟩
    obtain ⟨V,hV,_⟩ := collisionIn_image_preimage k x i hi U S hS
    exact ⟨V,hV⟩
  · rintro ⟨S,hS⟩
    exact ⟨S.image i,collisionIn_image_map k x i hi U S hS⟩

/-- An injective index map preserves the existence of a unique collision in the corresponding
ambient sets. -/
theorem collisionIn_image_unique_iff {m q M : ℕ} (k : ℕ) (x : Fin q → ZMod M)
    (i : Fin m → Fin q) (hi : Function.Injective i) (U : Finset (Fin m)) :
    (∃! S, CollisionIn k x (U.image i) S) ↔
      ∃! S, CollisionIn k (fun z => x (i z)) U S := by
  constructor
  · rintro ⟨S,hS,huniq⟩
    obtain ⟨V,hV,himage⟩ := collisionIn_image_preimage k x i hi U S hS
    refine ⟨V,hV,?_⟩
    intro W hW
    have heq := huniq (W.image i) (collisionIn_image_map k x i hi U W hW)
    exact (Finset.image_inj hi).mp (heq.trans himage.symm)
  · rintro ⟨V,hV,huniq⟩
    refine ⟨V.image i,collisionIn_image_map k x i hi U V hV,?_⟩
    intro S hS
    obtain ⟨W,hW,himage⟩ := collisionIn_image_preimage k x i hi U S hS
    rw [← himage,huniq W hW]

/-- The retained prefix satisfies `2 * k * (q - B.card) ≤ B.card`. -/
theorem retained_prefix_keep_ratio (k q : ℕ) :
    let B := (Finset.univ : Finset (Fin q)).filter
      (fun j => j.val < Nat.ceil ((2*k : ℝ)/(2*k+1)*q))
    2*k*(q-B.card) ≤ B.card := by
  classical
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  have hden : (0 : ℝ) < 2*k+1 := by positivity
  have hratio : (2*k : ℝ)/(2*k+1) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hcut : cut ≤ q := Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg q) hratio)
  have hcard : ((Finset.univ : Finset (Fin q)).filter (fun j => j.val < cut)).card = cut := by
    simpa [Nat.min_eq_right hcut] using! (Fin.card_filter_val_lt (n := q) (m := cut))
  have hceil : (2*k : ℝ)/(2*k+1)*q ≤ (cut : ℝ) := Nat.le_ceil _
  have hmul : (2*k : ℝ)*q ≤ (cut : ℝ)*(2*k+1) := by
    apply (div_le_iff₀ hden).mp
    rw [← div_mul_eq_mul_div]
    exact hceil
  have hreal : (2*k : ℝ)*((q : ℝ)-cut) ≤ cut := by nlinarith
  have hnat : 2*k*(q-cut) ≤ cut := by
    have hcast : (((2*k*(q-cut)) : ℕ) : ℝ) ≤ cut := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hcut] using! hreal
    exact_mod_cast hcast
  (try dsimp only)
  rw [hcard]
  exact hnat

/-- For positive `k` and `q`, the retained prefix is nonempty. -/
theorem retained_prefix_positive (k q : ℕ) (hk : 0 < k) (hq : 0 < q) :
    0 < ((Finset.univ : Finset (Fin q)).filter
      (fun j => j.val < Nat.ceil ((2*k : ℝ)/(2*k+1)*q))).card := by
  have hzero : (⟨0,hq⟩ : Fin q) ∈ (Finset.univ : Finset (Fin q)).filter
      (fun j => j.val < Nat.ceil ((2*k : ℝ)/(2*k+1)*q)) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and ]
    apply Nat.ceil_pos.mpr
    exact mul_pos (div_pos (by exact_mod_cast (show 0 < 2*k by omega)) (by positivity))
      (by exact_mod_cast hq)
  exact Finset.card_pos.mpr ⟨⟨0,hq⟩,hzero⟩

/-- If `T` contains a collision, independent selection on its collision support gives no more
no-collision assignments than unique-collision assignments. -/
theorem collisionSupport_iid_none_le_unique {q M : ℕ} (k : ℕ) (hk : 0 < k)
    (hq : 0 < q) (x : Fin q → ZMod M) (T : Finset (Fin q))
    (hcollision : ∃ S, CollisionIn k x T S) :
    let A := collisionSupport k x T
    let i := A.orderEmbOfFin rfl
    let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
    ((Finset.univ : Finset (Fin A.card → Fin q)).filter (fun f =>
      ¬∃ S, CollisionIn k x (selectedTuplePositions cut i f) S)).card ≤
    ((Finset.univ : Finset (Fin A.card → Fin q)).filter (fun f =>
      ∃! S, CollisionIn k x (selectedTuplePositions cut i f) S)).card := by
  classical
  let A := collisionSupport k x T
  let i := A.orderEmbOfFin rfl
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  let B := (Finset.univ : Finset (Fin q)).filter (fun j => j.val < cut)
  have hlocal : HasCollision k (fun z => x (i z)) := by
    obtain ⟨S,hS⟩ := hcollision
    have hSA : S ⊆ A := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨hS.1 hz,S,hS,hz⟩
    have himage : (Finset.univ.image i) = A := A.image_orderEmbOfFin_univ rfl
    have hsrc : ∃ S, CollisionIn k x (Finset.univ.image i) S := by
      rw [himage]
      exact ⟨S,hSA,hS.2⟩
    obtain ⟨V,hV⟩ := (collisionIn_image_exists_iff k x i i.injective Finset.univ).mp hsrc
    exact ⟨V,hV.2⟩
  have hmask (f : Fin A.card → Fin q) : selectedTuplePositions cut i f =
      (Finset.univ.filter (fun z => f z ∈ B)).image i := by
    unfold selectedTuplePositions
    congr 1
    ext z
    simp [B]
  have hnone : (Finset.univ : Finset (Fin A.card → Fin q)).filter (fun f =>
      ¬∃ S, CollisionIn k x (selectedTuplePositions cut i f) S) =
      Finset.univ.filter (fun f => ¬∃ S, CollisionIn k (fun z => x (i z))
        (Finset.univ.filter (fun z => f z ∈ B)) S) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hmask,collisionIn_image_exists_iff k x i i.injective]
  have hunique : (Finset.univ : Finset (Fin A.card → Fin q)).filter (fun f =>
      ∃! S, CollisionIn k x (selectedTuplePositions cut i f) S) =
      Finset.univ.filter (fun f => ∃! S, CollisionIn k (fun z => x (i z))
        (Finset.univ.filter (fun z => f z ∈ B)) S) := by
    ext f
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hmask,collisionIn_image_unique_iff k x i i.injective]
  (try dsimp only)
  rw [hnone,hunique]
  exact iidCollision_none_le_unique k A.card q M hq (fun z => x (i z)) hlocal B
    (retained_prefix_positive k q hk hq) (retained_prefix_keep_ratio k q)

/-- For collision support of size at most `d`, approximate independence bounds the no-collision
probability by the unique-collision probability plus `2 * (η + support.card^2 / q)`. -/
theorem collisionSupport_none_le_unique {q R M d : ℕ} {η : ℝ}
    (k : ℕ) (hk : 0 < k) (hq : 0 < q) (hη : 0 ≤ η)
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (π : Fin R → Equiv.Perm (Fin q))
    (hπ : ApproxIndependent d η π) (hsupport : (collisionSupport k x T).card ≤ d)
    (hcollision : ∃ S, CollisionIn k x T S) :
    eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) ≤
      eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S)+
        2*(η+((collisionSupport k x T).card : ℝ)^2/q) := by
  classical
  let A := collisionSupport k x T
  let i := A.orderEmbOfFin rfl
  let cut := Nat.ceil ((2*k : ℝ)/(2*k+1)*q)
  let Vnone : (Fin A.card → Fin q) → Prop := fun f =>
    ¬∃ S, CollisionIn k x (selectedTuplePositions cut i f) S
  let Vunique : (Fin A.card → Fin q) → Prop := fun f =>
    ∃! S, CollisionIn k x (selectedTuplePositions cut i f) S
  let refnone : ℝ := ((Finset.univ.filter Vnone).card : ℝ)/(q : ℝ)^A.card
  let refunique : ℝ := ((Finset.univ.filter Vunique).card : ℝ)/(q : ℝ)^A.card
  let err : ℝ := η+(A.card : ℝ)^2/q
  have hcount := collisionSupport_iid_none_le_unique k hk hq x T hcollision
  have hcount' : (Finset.univ.filter Vnone).card ≤ (Finset.univ.filter Vunique).card := by
    convert! hcount using 1
  have href : refnone ≤ refunique := div_le_div_of_nonneg_right
    (by exact_mod_cast hcount') (pow_nonneg (Nat.cast_nonneg q) A.card)
  have hn := collisionSupport_none_iid_gap k x T π hq hη hπ hsupport
  have hu := collisionSupport_unique_iid_gap k x T π hq hη hπ hsupport
  have hn' : |eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S)-refnone| ≤ err := by
    convert! hn using 1
  have hu' : |eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S)-refunique| ≤ err := by
    convert! hu using 1
  have hnoneupper := (abs_le.mp hn').2
  have huniqueupper := (abs_le.mp hu').1
  change eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) ≤
      eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S)+2*err
  nlinarith

/-- Under the stated size, logarithm, collision, and approximate-independence hypotheses, the
no-collision probability is at most the unique-collision probability plus the explicit
geometric, inverse-size, and logarithmic error [Ambainis2007ElementDistinctness]. -/
theorem algorithm3Isolation_quantitative {q R M N : ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hN : 0 < N) (hlog : 2 ≤ Real.log (N : ℝ))
    (x : Fin q → ZMod M) (T : Finset (Fin q)) (π : Fin R → Equiv.Perm (Fin q))
    (hsqrt : Real.sqrt N ≤ T.card)
    (hπ : ApproxIndependent (Nat.ceil (2*(k : ℝ)*Real.log N)) (1/(N : ℝ)) π)
    (hcollision : ∃ S, CollisionIn k x T S) :
    eventProbability (fun s => ¬∃ S, CollisionIn k x (retained k T π s) S) ≤
      eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S)+
        ((1/2 : ℝ)^(Nat.floor (Real.log (N : ℝ)))+4/(N : ℝ)+
          16*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N) := by
  classical
  have hkp : 0 < k := by omega
  have hkreal : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrtpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNp
  have hTq : (T.card : ℝ) ≤ q := by
    have hh : T.card ≤ q := by simpa using! Finset.card_le_univ T
    exact_mod_cast hh
  have hqge : Real.sqrt N ≤ q := le_trans hsqrt hTq
  have hqreal : (0 : ℝ) < q := lt_of_lt_of_le hsqrtpos hqge
  have hq : 0 < q := by exact_mod_cast hqreal
  let l := Nat.floor (Real.log (N : ℝ))
  let t := l+1
  have hfloor : (l : ℝ) ≤ Real.log N := Nat.floor_le (by linarith)
  have ht : (t : ℝ) ≤ Real.log N+1 := by dsimp [t]; push_cast; linarith
  have htk : ((t*k : ℕ) : ℝ) ≤ 2*(k : ℝ)*Real.log N := by
    push_cast
    nlinarith [mul_nonneg hkreal (sub_nonneg.mpr ht),
      mul_nonneg hkreal (show 0 ≤ Real.log (N : ℝ)-1 by linarith)]
  have htd : t*k ≤ Nat.ceil (2*(k : ℝ)*Real.log N) := by
    exact_mod_cast le_trans htk (Nat.le_ceil _)
  have hbound (a : ℕ) (ha : (a : ℝ) ≤ 2*(k : ℝ)*(Real.log (N : ℝ)+1)) :
      (a : ℝ)^2/q ≤ 4*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N := by
    have hsq : (a : ℝ)^2 ≤ 4*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2 := by
      have hsq' := pow_le_pow_left₀ (Nat.cast_nonneg a) ha 2
      nlinarith only [hsq']
    calc
      _ ≤ (4*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2)/(q : ℝ) :=
        div_le_div_of_nonneg_right hsq hqreal.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hsqrtpos hqge
  let E := 4*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N
  have hE0 : 0 ≤ E := div_nonneg (by positivity) hsqrtpos.le
  have hη0 : 0 ≤ 1/(N : ℝ) := div_nonneg (by norm_num) hNp.le
  have hu0 : 0 ≤ eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S) :=
    (eventProbability_bounds _).1
  have hmajor : 16*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N = 4*E := by
    dsimp [E]
    ring
  rw [hmajor]
  obtain hsmall | ⟨i,hi,hblocks⟩ := collision_packing_dichotomy k hkp x T t
  · have htm1 : t-1 = l := rfl
    rw [htm1] at hsmall
    have hmreal : ((collisionSupport k x T).card : ℝ) ≤ 2*(k : ℝ)*Real.log N := by
      have hcast : ((collisionSupport k x T).card : ℝ) ≤ 2*(k : ℝ)*(l : ℝ) := by
        exact_mod_cast hsmall
      nlinarith [mul_nonneg hkreal (sub_nonneg.mpr hfloor)]
    have hmd : (collisionSupport k x T).card ≤ Nat.ceil (2*(k : ℝ)*Real.log N) := by
      exact_mod_cast le_trans hmreal (Nat.le_ceil _)
    have hprob := collisionSupport_none_le_unique k hkp hq hη0 x T π hπ hmd hcollision
    have herr := hbound (collisionSupport k x T).card (by nlinarith)
    change ((collisionSupport k x T).card : ℝ)^2/q ≤ E at herr
    have htail0 : 0 ≤ (1/2 : ℝ)^l := pow_nonneg (by norm_num) l
    change _ ≤ _+((1/2 : ℝ)^l+4/(N : ℝ)+4*E)
    have herror : 2*(1/(N : ℝ)+((collisionSupport k x T).card : ℝ)^2/q) ≤
        (1/2 : ℝ)^l+4/(N : ℝ)+4*E := by
      simp only [div_eq_mul_inv,one_mul] at herr hη0 ⊢
      nlinarith only [herr,hη0,hE0,htail0]
    calc
      _ ≤ eventProbability (fun s => ∃! S, CollisionIn k x (retained k T π s) S)+
          2*(1/(N : ℝ)+((collisionSupport k x T).card : ℝ)^2/q) := by
        convert! hprob using 1
      _ ≤ _ := add_le_add le_rfl herror
  · have hprob := disjointBlocks_none_bound k hkp hq hη0 x T π hπ i hi hblocks htd
    have herr := hbound (t*k) (by nlinarith [htk])
    change ((t*k : ℕ) : ℝ)^2/q ≤ E at herr
    have htail : (1/2 : ℝ)^t ≤ (1/2 : ℝ)^l := by
      dsimp [t]
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) l]
    change _ ≤ _+((1/2 : ℝ)^l+4/(N : ℝ)+4*E)
    have herror : (1/2 : ℝ)^t+1/(N : ℝ)+((t*k : ℕ) : ℝ)^2/q ≤
        (1/2 : ℝ)^l+4/(N : ℝ)+4*E := by
      simp only [div_eq_mul_inv,one_mul] at herr hη0 ⊢
      nlinarith only [herr,htail,hη0,hE0]
    calc
      _ ≤ (1/2 : ℝ)^t+1/(N : ℝ)+((t*k : ℕ) : ℝ)^2/q := by
        convert! hprob using 1
      _ ≤ (1/2 : ℝ)^l+4/(N : ℝ)+4*E := herror
      _ ≤ _ := le_add_of_nonneg_left hu0

namespace IsolationAsymptotics
noncomputable section
open Filter
open scoped Topology

end
end IsolationAsymptotics

/-- The Algorithm 3 isolation proposition holds [Ambainis2007ElementDistinctness]. -/
theorem algorithm3Isolation_answer : Algorithm3Isolation := by
  intro k hk ε hε
  obtain ⟨N0,hthreshold⟩ :=
      Qatlib.Concepts.WalkFind.SearchAlgorithm.isolationError_threshold k hk ε hε
  refine ⟨max N0 1,?_⟩
  intro N q R M hN _hR _hM x T π hsqrt _hTN _hTq _hnear hπ hcollision
  have hNpos : 0 < N := lt_of_lt_of_le (by omega : 0 < max N0 1) hN
  obtain ⟨_,hlog,herror⟩ := hthreshold N (le_trans (Nat.le_max_left N0 1) hN)
  have hquant := algorithm3Isolation_quantitative k hk hNpos hlog x T π hsqrt hπ hcollision
  have hden : 0 < 1+(k : ℝ)*Real.log (N : ℝ) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      (show 0 ≤ Real.log (N : ℝ) by linarith)]
  have hsmall : ((1/2 : ℝ)^(Nat.floor (Real.log (N : ℝ)))+4/(N : ℝ)+
      16*(k : ℝ)^2*(Real.log (N : ℝ)+1)^2/Real.sqrt N) ≤
      ε/(1+(k : ℝ)*Real.log (N : ℝ)) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [herror]
  exact le_trans hquant (add_le_add le_rfl hsmall)

end Qatlib.Concepts.WalkFind.SearchAlgorithm
