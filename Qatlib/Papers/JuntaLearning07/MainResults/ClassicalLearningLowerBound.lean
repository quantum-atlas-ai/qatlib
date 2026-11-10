/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningDefs
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Sqrt
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

variable {n : ℕ}

structure ClassicalMembershipLearner (n T : ℕ) where

  query : (Fin T → Bool) → Fin n → Bool

  hypothesis : (Fin T → Bool) → ((Fin n → Bool) → Bool)

def answers {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (f : (Fin n → Bool) → Bool) : (t : ℕ) → (Fin T → Bool)
  | 0 => fun _ => false
  | t + 1 =>
      fun i : Fin T =>
        if i.val = t then f (L.query (answers L f t)) else (answers L f t) i

def classicalHypothesis {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → Bool :=
  L.hypothesis (answers L f T)

def ClassicalLearnsTo {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (k : ℕ) (ε : ℝ) : Prop :=
  ∀ f : (Fin n → Bool) → Bool, IsKJunta (n := n) k f →
    disagreement f (classicalHypothesis L f) ≤ ε

theorem disagreement_pointwise (f g h : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (if f x = h x then (0 : ℝ) else 1)
      ≤ (if f x = g x then (0 : ℝ) else 1) + (if g x = h x then (0 : ℝ) else 1) := by
  cases h1 : f x <;> cases h2 : g x <;> cases h3 : h x <;> simp

theorem disagreement_triangle (f g h : (Fin n → Bool) → Bool) :
    disagreement f h ≤ disagreement f g + disagreement g h := by
  unfold disagreement uniformExpect
  have hsum : (∑ x : Fin n → Bool, (if f x = h x then (0 : ℝ) else 1))
      ≤ ∑ x : Fin n → Bool,
          ((if f x = g x then (0 : ℝ) else 1) + (if g x = h x then (0 : ℝ) else 1)) :=
    Finset.sum_le_sum (fun x _ => disagreement_pointwise f g h x)
  rw [Finset.sum_add_distrib] at hsum
  have hinv : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  calc ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → Bool, (if f x = h x then (0 : ℝ) else 1)
      ≤ ((2 : ℝ) ^ n)⁻¹ *
          ((∑ x : Fin n → Bool, (if f x = g x then (0 : ℝ) else 1)) +
            ∑ x : Fin n → Bool, (if g x = h x then (0 : ℝ) else 1)) :=
        mul_le_mul_of_nonneg_left hsum hinv
    _ = ((2 : ℝ) ^ n)⁻¹ * (∑ x : Fin n → Bool, (if f x = g x then (0 : ℝ) else 1)) +
        ((2 : ℝ) ^ n)⁻¹ * (∑ x : Fin n → Bool, (if g x = h x then (0 : ℝ) else 1)) := by
        ring

theorem disagreement_symm (f g : (Fin n → Bool) → Bool) :
    disagreement f g = disagreement g f := by
  unfold disagreement uniformExpect
  rw [show (∑ x : Fin n → Bool, (if f x = g x then (0 : ℝ) else 1))
        = ∑ x : Fin n → Bool, (if g x = f x then (0 : ℝ) else 1) from by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : f x = g x
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (fun hh => h hh.symm)]]

theorem zero_query_hypothesis_constant {n : ℕ} (L : ClassicalMembershipLearner n 0)
    (f : (Fin n → Bool) → Bool) :
    classicalHypothesis L f = L.hypothesis (fun _ => false) := by
  unfold classicalHypothesis
  rfl

theorem zero_query_cannot_learn {n k : ℕ} (L : ClassicalMembershipLearner n 0)
    {ε : ℝ} {f g : (Fin n → Bool) → Bool}
    (hf : IsKJunta (n := n) k f) (hg : IsKJunta (n := n) k g)
    (hlearn : ClassicalLearnsTo L k ε) (hfar : 2 * ε < disagreement f g) : False := by
  have hHf : classicalHypothesis L f = L.hypothesis (fun _ => false) :=
    zero_query_hypothesis_constant L f
  have hHg : classicalHypothesis L g = L.hypothesis (fun _ => false) :=
    zero_query_hypothesis_constant L g
  have h1 : disagreement f (classicalHypothesis L f) ≤ ε := hlearn f hf
  have h2 : disagreement g (classicalHypothesis L g) ≤ ε := hlearn g hg
  rw [hHf] at h1
  rw [hHg] at h2
  have tri : disagreement f g ≤
      disagreement f (L.hypothesis (fun _ => false)) +
        disagreement (L.hypothesis (fun _ => false)) g :=
    disagreement_triangle f (L.hypothesis (fun _ => false)) g
  rw [disagreement_symm (L.hypothesis (fun _ => false)) g] at tri
  linarith

open Qatlib.Concepts.ProbabilityCore.DistributionAA

variable {n : ℕ}

def dictator {n : ℕ} (i : Fin n) : (Fin n → Bool) → Bool := fun x => x i

theorem dictator_isKJunta {n : ℕ} (i : Fin n) :
    IsKJunta (n := n) 1 (dictator i) := by
  refine ⟨{i}, by simp, ?_⟩
  intro x y hxy
  exact hxy i (by simp)

theorem disagreement_dictator_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    disagreement (dictator i) (dictator j) = 1 / 2 := by
  classical
  unfold disagreement uniformExpect dictator
  set S : ℝ := ∑ x : Fin n → Bool, (if x i = x j then (0 : ℝ) else 1) with hSdef
  have hstep : ∀ x : Fin n → Bool,
      (if x i = x j then (0 : ℝ) else 1) +
        (if (cubeFlip x j) i = (cubeFlip x j) j then (0 : ℝ) else 1) = 1 := by
    intro x
    have h1 : (cubeFlip x j) i = x i := by
      rw [cubeFlip]
      exact if_neg hij
    have h2 : (cubeFlip x j) j = !x j := by simp [cubeFlip]
    rw [h1, h2]
    cases x i <;> cases x j <;> simp
  have hreindex : ∑ x : Fin n → Bool,
        (if (cubeFlip x j) i = (cubeFlip x j) j then (0 : ℝ) else 1) = S := by
    rw [hSdef]
    exact Equiv.sum_comp (cubeFlipEquiv j) (fun x => if x i = x j then (0 : ℝ) else 1)
  have htwo : S + S = (2 : ℝ) ^ n := by
    have hcomm : S + S =
        (∑ x : Fin n → Bool, (if x i = x j then (0 : ℝ) else 1)) +
          ∑ x : Fin n → Bool,
            (if (cubeFlip x j) i = (cubeFlip x j) j then (0 : ℝ) else 1) := by
      rw [hreindex]
    rw [hcomm, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun x _ => hstep x)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_one]
  have hS : S = (2 : ℝ) ^ n / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℝ) ≠ 0)]
    linarith
  calc ((2 : ℝ) ^ n)⁻¹ * S = ((2 : ℝ) ^ n)⁻¹ * ((2 : ℝ) ^ n / 2) := by rw [hS]
    _ = 1 / 2 := by
        have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
        field_simp

theorem answers_eq_of_agree_query {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (f g : (Fin n → Bool) → Bool)
    (h : ∀ t : Fin T, g (L.query (answers L f (t : ℕ))) =
      f (L.query (answers L f (t : ℕ)))) :
    answers L f T = answers L g T := by
  have hstep : ∀ t ≤ T, answers L f t = answers L g t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
        intro ht
        have ih' : answers L f t = answers L g t := ih (Nat.le_of_succ_le ht)
        have htT : t < T := Nat.lt_of_succ_le ht
        funext i
        show (if (i : ℕ) = t then f (L.query (answers L f t))
              else answers L f t i) =
            (if (i : ℕ) = t then g (L.query (answers L g t))
              else answers L g t i)
        by_cases hi : (i : ℕ) = t
        · rw [if_pos hi, if_pos hi]
          have hq : g (L.query (answers L f t)) = f (L.query (answers L f t)) := h ⟨t, htT⟩
          rw [← hq, ih']
        · rw [if_neg hi, if_neg hi, congrFun ih' i]
  exact hstep T le_rfl

def querySet {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (f : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.image (fun t : Fin T => L.query (answers L f (t : ℕ)))

theorem mem_querySet {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (f : (Fin n → Bool) → Bool) (t : Fin T) :
    L.query (answers L f (t : ℕ)) ∈ querySet L f :=
  Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩

def flipOff {n : ℕ} (P : Finset (Fin n → Bool)) (f : (Fin n → Bool) → Bool) :
    (Fin n → Bool) → Bool :=
  fun x => if x ∈ P then f x else !(f x)

theorem flipOff_agree_querySet {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (f : (Fin n → Bool) → Bool) (t : Fin T) :
    flipOff (querySet L f) f (L.query (answers L f (t : ℕ))) =
      f (L.query (answers L f (t : ℕ))) := by
  unfold flipOff
  rw [if_pos (mem_querySet L f t)]

theorem disagreement_flipOff {n : ℕ} (f : (Fin n → Bool) → Bool)
    (P : Finset (Fin n → Bool)) :
    disagreement f (flipOff P f) = ((Finset.univ \ P).card : ℝ) / (2 : ℝ) ^ n := by
  classical
  unfold disagreement uniformExpect
  have hind : ∀ x : Fin n → Bool,
      (if f x = flipOff P f x then (0 : ℝ) else 1) = (if x ∈ P then (0 : ℝ) else 1) := by
    intro x
    by_cases hx : x ∈ P <;> cases hfx : f x <;> simp [flipOff, hx, hfx]
  rw [Finset.sum_congr rfl (fun x _ => hind x)]
  have hsum : (∑ x : Fin n → Bool, (if x ∈ P then (0 : ℝ) else 1)) =
      ((Finset.univ \ P).card : ℝ) := by
    rw [show (∑ x : Fin n → Bool, (if x ∈ P then (0 : ℝ) else 1)) =
        ∑ x : Fin n → Bool, (if x ∉ P then (1 : ℝ) else 0) from by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ P <;> simp [hx]]
    rw [← Finset.sum_filter]
    have hfil : (Finset.univ.filter (fun x : Fin n → Bool => x ∉ P)) = Finset.univ \ P := by
      ext x; simp
    rw [hfil]
    simp
  rw [hsum, div_eq_mul_inv]
  ring

theorem classical_learning_log_lower {n T : ℕ} (L : ClassicalMembershipLearner n T)
    (hlearn : ClassicalLearnsTo L 1 (1 / 5)) : n ≤ 2 ^ T := by
  classical
  have hsep : ∀ i j : Fin n, i ≠ j →
      classicalHypothesis L (dictator i) ≠ classicalHypothesis L (dictator j) := by
    intro i j hij heq
    have h1 : disagreement (dictator i) (classicalHypothesis L (dictator i)) ≤ 1 / 5 :=
      hlearn (dictator i) (dictator_isKJunta i)
    have h2 : disagreement (dictator j) (classicalHypothesis L (dictator j)) ≤ 1 / 5 :=
      hlearn (dictator j) (dictator_isKJunta j)
    have htri : disagreement (dictator i) (dictator j) ≤
        disagreement (dictator i) (classicalHypothesis L (dictator i)) +
          disagreement (classicalHypothesis L (dictator i)) (dictator j) :=
      disagreement_triangle _ _ _
    rw [disagreement_symm (classicalHypothesis L (dictator i)) (dictator j),
      heq] at htri
    rw [disagreement_dictator_ne hij] at htri
    rw [heq] at h1
    linarith
  have hinj : Function.Injective (fun i : Fin n => answers L (dictator i) T) := by
    intro i j hij
    by_contra hne
    have hij' : answers L (dictator i) T = answers L (dictator j) T := hij
    exact hsep i j hne (by unfold classicalHypothesis; rw [hij'])
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_fin, Fintype.card_bool] using! hcard

theorem classical_learning_pow_two_lower {n T : ℕ}
    (L : ClassicalMembershipLearner n T)
    (hlearn : ClassicalLearnsTo L n (1 / 5)) :
    (3 / 5 : ℝ) * (2 : ℝ) ^ n ≤ (T : ℝ) := by
  classical
  let f : (Fin n → Bool) → Bool := fun _ => false
  have hf : IsKJunta (n := n) n f := by
    refine ⟨Finset.univ, by simp, ?_⟩
    intro x y hxy
    simp [f]
  set P : Finset (Fin n → Bool) := querySet L f with hP
  let g : (Fin n → Bool) → Bool := flipOff P f
  have hg : IsKJunta (n := n) n g := by
    refine ⟨Finset.univ, by simp, ?_⟩
    intro x y hxy
    have hxy' : x = y := funext (fun i => hxy i (Finset.mem_univ i))
    rw [hxy']
  have hagree : answers L f T = answers L g T := by
    apply answers_eq_of_agree_query L f g
    intro t
    simpa [g, hP] using! flipOff_agree_querySet L f t
  have hH : classicalHypothesis L g = classicalHypothesis L f := by
    unfold classicalHypothesis
    rw [← hagree]
  have h1 : disagreement f (classicalHypothesis L f) ≤ 1 / 5 := hlearn f hf
  have h2 : disagreement g (classicalHypothesis L g) ≤ 1 / 5 := hlearn g hg
  rw [hH] at h2
  have htri : disagreement f g ≤
      disagreement f (classicalHypothesis L f) +
        disagreement (classicalHypothesis L f) g :=
    disagreement_triangle _ _ _
  rw [disagreement_symm (classicalHypothesis L f) g] at htri
  have hdle : disagreement f g ≤ 2 / 5 := by linarith
  have hdg : disagreement f g = ((Finset.univ \ P).card : ℝ) / (2 : ℝ) ^ n :=
    disagreement_flipOff f P
  have hPcard : P.card ≤ T := by
    calc P.card = (Finset.univ.image
          (fun t : Fin T => L.query (answers L f (t : ℕ)))).card := rfl
      _ ≤ (Finset.univ : Finset (Fin T)).card := Finset.card_image_le
      _ = T := by simp
  have hPle : P.card ≤ 2 ^ n := by
    calc P.card ≤ (Finset.univ : Finset (Fin n → Bool)).card :=
          Finset.card_le_card (Finset.subset_univ P)
      _ = 2 ^ n := by simp
  have hcard : (Finset.univ \ P).card = 2 ^ n - P.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ]
    simp
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hcardR : ((Finset.univ \ P).card : ℝ) = (2 : ℝ) ^ n - (P.card : ℝ) := by
    rw [hcard, Nat.cast_sub hPle, Nat.cast_pow, Nat.cast_ofNat]
  have hlower : ((2 : ℝ) ^ n - (T : ℝ)) / (2 : ℝ) ^ n ≤ disagreement f g := by
    rw [hdg]
    apply div_le_div_of_nonneg_right ?_ (le_of_lt hpow)
    rw [hcardR]
    have hPT : (P.card : ℝ) ≤ (T : ℝ) := by exact_mod_cast hPcard
    linarith
  have hmain : ((2 : ℝ) ^ n - (T : ℝ)) / (2 : ℝ) ^ n ≤ 2 / 5 := le_trans hlower hdle
  rw [div_le_iff₀ hpow] at hmain
  nlinarith

end Qatlib.Papers.JuntaLearning07.MainResults
