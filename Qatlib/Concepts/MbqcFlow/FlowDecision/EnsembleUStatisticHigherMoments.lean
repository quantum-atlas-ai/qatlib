/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics

/-!
# Higher moments of finite U-statistics

This module defines centered overlap moments of finite record tuples through `overlapMomentK`.
It reduces expectations to distinct used records, proves invariance under record permutations
and factorization for disjoint families, and expands centered U-statistic moments by tuple
families and their overlap labels.

The absolute kernel moments `centeredAbsMomentK` and a count of coinciding families yield
explicit moment and deviation bounds. The finite-POVM specialization `frontier1_povm` places
these identities in the measurement-record estimation setting of [HuangKuengPreskill2020].

## Main statements

* `uStatistic_moment_overlap_type`: the centered moment expansion grouped by overlap labels.
* `overlapMoment_append_disjoint`: factorization for families using disjoint records.
* `uStatistic_moment_abs_le`: a moment bound from the coincidence count.
* `probEvent_uStatistic_hkp`: an even-moment bound on the deviation probability.
* `frontier1_povm`: the combined results for independent finite-POVM records.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

open Qatlib.Foundations.PureStateMath
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {O : Type} [Fintype O] [DecidableEq O]

/-- Every tuple in the family selects distinct record indices. -/
def familyInjective {n k r : ℕ} (T : Fin r → Fin k → Fin n) : Prop :=
  ∀ a : Fin r, Function.Injective (T a)

/-- The record index selected by a tuple position in the family. -/
def posRead {n k r : ℕ} (T : Fin r → Fin k → Fin n) : Fin r × Fin k → Fin n :=
  fun α => T α.1 α.2

/-- Distinct positions across the entire tuple family select distinct records. -/
def coincidenceFree {n k r : ℕ} (T : Fin r → Fin k → Fin n) : Prop :=
  ∀ α β : Fin r × Fin k, α ≠ β → posRead T α ≠ posRead T β

/-- The expectation of the product of the centered kernel evaluations selected by `T` under
independent records with law `p`. -/
noncomputable def overlapMomentK (p : FinDist O) {n k r : ℕ} (h : (Fin k → O) → ℝ)
    (T : Fin r → Fin k → Fin n) : ℝ :=
  ∑ ω : Fin n → O, p.probOf ω
    * ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h)

/-- Pointwise equal tuple families have equal centered overlap moments. -/
theorem overlapMomentK_congr (p : FinDist O) {n k r : ℕ} (h : (Fin k → O) → ℝ)
    (T S : Fin r → Fin k → Fin n) (hTS : ∀ a, T a = S a) :
    overlapMomentK p h T = overlapMomentK p h S := by
  have hT : T = S := funext hTS
  rw [hT]

/-- The finite set of record indices used anywhere in the tuple family. -/
def usedRecords {n k r : ℕ} (T : Fin r → Fin k → Fin n) : Finset (Fin n) :=
  Finset.univ.image (posRead T)

/-- The increasing enumeration of the distinct record indices used by `T`. -/
def mergeTuple {n k r : ℕ} (T : Fin r → Fin k → Fin n) :
    Fin (usedRecords T).card → Fin n :=
  fun j => ↑((usedRecords T).orderIsoOfFin rfl j)

/-- The index of a tuple position's record in the increasing enumeration `mergeTuple`. -/
def posIndex {n k r : ℕ} (T : Fin r → Fin k → Fin n) (α : Fin r × Fin k) :
    Fin (usedRecords T).card :=
  ((usedRecords T).orderIsoOfFin rfl).symm
    ⟨posRead T α, Finset.mem_image_of_mem _ (Finset.mem_univ α)⟩

/-- The enumeration of the used record indices is injective. -/
theorem mergeTuple_injective {n k r : ℕ} (T : Fin r → Fin k → Fin n) :
    Function.Injective (mergeTuple T) := by
  intro j₁ j₂ hj
  exact ((usedRecords T).orderIsoOfFin rfl).injective (Subtype.ext hj)

/-- Reading `mergeTuple` at `posIndex T α` recovers the record selected at position `α`. -/
theorem mergeTuple_posIndex {n k r : ℕ} (T : Fin r → Fin k → Fin n)
    (α : Fin r × Fin k) : mergeTuple T (posIndex T α) = posRead T α := by
  simp [mergeTuple, posIndex]

/-- Every record enumerated by `mergeTuple` belongs to `usedRecords T`. -/
theorem mergeTuple_mem {n k r : ℕ} (T : Fin r → Fin k → Fin n)
    (j : Fin (usedRecords T).card) : mergeTuple T j ∈ usedRecords T :=
  Subtype.coe_prop ((usedRecords T).orderIsoOfFin rfl j)

/-- An expectation depending on the records selected by `T` can be computed over only its
distinct used records, with product weights. -/
theorem familyReadExpect (p : FinDist O) {n k r : ℕ} (T : Fin r → Fin k → Fin n)
    (F : (Fin r × Fin k → O) → ℝ) :
    (∑ ω : Fin n → O, p.probOf ω * F (fun α => ω (posRead T α)))
      = ∑ z : Fin (usedRecords T).card → O, (∏ j, p.prob (z j))
          * F (fun α => z (posIndex T α)) := by
  have hjoint : (∑ ω : Fin n → O, p.probOf ω
          * F (fun α => ω (mergeTuple T (posIndex T α))))
      = ∑ z : Fin (usedRecords T).card → O, (∏ j, p.prob (z j))
          * F (fun α => z (posIndex T α)) :=
    povm_joint_expect p (mergeTuple T) (mergeTuple_injective T)
      (fun z => F (fun α => z (posIndex T α)))
  have hfun : ∀ ω : Fin n → O, F (fun α => ω (posRead T α))
      = F (fun α => ω (mergeTuple T (posIndex T α))) :=
    fun ω => congrArg F
      (funext fun α => congrArg ω (mergeTuple_posIndex T α).symm)
  calc (∑ ω : Fin n → O, p.probOf ω * F (fun α => ω (posRead T α)))
      = ∑ ω : Fin n → O, p.probOf ω
          * F (fun α => ω (mergeTuple T (posIndex T α))) :=
        Finset.sum_congr rfl fun ω _ => by rw [hfun ω]
    _ = ∑ z : Fin (usedRecords T).card → O, (∏ j, p.prob (z j))
          * F (fun α => z (posIndex T α)) := hjoint

/-- The centered overlap moment equals the product-weighted sum over assignments to the distinct
used records. -/
theorem overlapMomentK_eq_merged (p : FinDist O) {n k r : ℕ} (h : (Fin k → O) → ℝ)
    (T : Fin r → Fin k → Fin n) :
    overlapMomentK p h T
      = ∑ z : Fin (usedRecords T).card → O, (∏ j, p.prob (z j))
          * ∏ a : Fin r,
              (h (fun i => z (posIndex T (a, i))) - kernelMeanK p h) :=
  familyReadExpect p T
    (fun y => ∏ a : Fin r, (h (fun i => y (a, i)) - kernelMeanK p h))

/-- The centered overlap moment of a single injective tuple is zero. -/
theorem overlapMoment_single_zero (p : FinDist O) {n k : ℕ} (t : Fin k → Fin n)
    (ht : Function.Injective t) (h : (Fin k → O) → ℝ) :
    overlapMomentK p h (fun _ : Fin 1 => t) = 0 := by
  have h1 := read_expect p t ht h
  have h2 : ∑ ω : Fin n → O, p.probOf ω = 1 := probOf_sum_one p n
  have hsplit : ∀ ω : Fin n → O,
      (p.probOf ω
        * ∏ a : Fin 1, (h (fun i => ω ((fun _ : Fin 1 => t) a i)) - kernelMeanK p h))
      = p.probOf ω * h (fun i => ω (t i))
        - kernelMeanK p h * p.probOf ω := by
    intro ω
    rw [Fin.prod_univ_one]
    ring
  unfold overlapMomentK
  rw [Finset.sum_congr rfl fun ω _ => hsplit ω, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h1, h2, mul_one, sub_self]

/-- Functions on a disjoint sum correspond to pairs of functions on its two summands. -/
def elimTableEquiv {B₁ B₂ : Type} [Fintype B₁] [Fintype B₂] :
    ((B₁ ⊕ B₂) → O) ≃ ((B₁ → O) × (B₂ → O)) where
  toFun w := (fun i => w (Sum.inl i), fun j => w (Sum.inr j))
  invFun pr := Sum.elim pr.1 pr.2
  left_inv w := by funext c; rcases c with i | j <;> rfl
  right_inv pr := by
    rcases pr with ⟨a, b⟩
    rfl

/-- Reading an injectively indexed finite collection of independent records gives the
corresponding product-law expectation. -/
theorem jointExpectGeneral {B : Type} [Fintype B] [DecidableEq B] {n : ℕ}
    (p : FinDist O) (u : B → Fin n) (hu : Function.Injective u)
    (G : (B → O) → ℝ) :
    (∑ ω : Fin n → O, p.probOf ω * G (fun b => ω (u b)))
      = ∑ y : B → O, (∏ b, p.prob (y b)) * G y := by
  classical
  set e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B with he
  have hidx : Function.Injective (fun t => u (e.symm t)) :=
    hu.comp (Equiv.injective _)
  have h0 := povm_joint_expect p (fun t => u (e.symm t)) hidx
    (fun z => G (fun b => z (e b)))
  beta_reduce at h0

  have hL : (∑ ω : Fin n → O, p.probOf ω
        * (fun z => G (fun b => z (e b))) (fun t => ω (u (e.symm t))))
      = ∑ ω : Fin n → O, p.probOf ω * G (fun b => ω (u b)) := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    refine congrArg (fun X => p.probOf ω * X) ?_
    refine congrArg G (funext fun b => ?_)
    simp

  have hR : (∑ z : Fin (Fintype.card B) → O, (∏ t, p.prob (z t))
        * (fun z' => G (fun b => z' (e b))) z)
      = ∑ y : B → O, (∏ b, p.prob (y b)) * G y := by
    set T : (Fin (Fintype.card B) → O) ≃ (B → O) :=
      Equiv.arrowCongr e.symm (Equiv.refl O) with hT
    have hgo : ∀ z : Fin (Fintype.card B) → O,
        ((∏ t, p.prob (z t)) * (fun z' => G (fun b => z' (e b))) z)
        = (∏ b, p.prob (T z b)) * G (T z) := by
      intro z
      have h1 : (∏ t, p.prob (z t)) = ∏ b, p.prob (T z b) := by
        have hp := Equiv.prod_comp e.symm (fun b => p.prob (z (e b)))
        simp only [Equiv.apply_symm_apply] at hp
        exact hp
      rw [h1]
      rfl
    exact Fintype.sum_equiv T
      (fun z => (∏ t, p.prob (z t)) * (fun z' => G (fun b => z' (e b))) z)
      (fun y => (∏ b, p.prob (y b)) * G y) hgo
  rw [hL, hR] at h0
  exact h0

/-- Expectations of two functions of disjoint, injectively selected record sets factor as the
product of their expectations. -/
theorem jointReadFactor {B₁ B₂ : Type} [Fintype B₁] [Fintype B₂] [DecidableEq B₁]
    [DecidableEq B₂] {n : ℕ} (p : FinDist O) (u₁ : B₁ → Fin n)
    (h₁ : Function.Injective u₁) (u₂ : B₂ → Fin n) (h₂ : Function.Injective u₂)
    (hdis : ∀ b₁ b₂, u₁ b₁ ≠ u₂ b₂)
    (F₁ : (B₁ → O) → ℝ) (F₂ : (B₂ → O) → ℝ) :
    (∑ ω : Fin n → O, p.probOf ω * F₁ (fun b => ω (u₁ b)) * F₂ (fun b => ω (u₂ b)))
      = (∑ y₁ : B₁ → O, (∏ b, p.prob (y₁ b)) * F₁ y₁)
        * (∑ y₂ : B₂ → O, (∏ b, p.prob (y₂ b)) * F₂ y₂) := by
  classical
  have huinj : Function.Injective (Sum.elim u₁ u₂) := by
    intro c d hcd
    rcases c with b₁ | b₂ <;> rcases d with c₁ | c₂ <;>
      simp only [Sum.elim_inl, Sum.elim_inr] at hcd
    · exact congrArg Sum.inl (h₁ hcd)
    · exact absurd hcd (hdis b₁ c₂)
    · exact absurd hcd.symm (hdis c₁ b₂)
    · exact congrArg Sum.inr (h₂ hcd)
  have hjr := jointExpectGeneral p (Sum.elim u₁ u₂) huinj
    (fun w => F₁ (fun b => w (Sum.inl b)) * F₂ (fun b => w (Sum.inr b)))
  beta_reduce at hjr
  simp only [Sum.elim_inl, Sum.elim_inr] at hjr

  have hstep2 : (∑ w : (B₁ ⊕ B₂) → O, (∏ c, p.prob (w c))
        * (F₁ (fun b => w (Sum.inl b)) * F₂ (fun b => w (Sum.inr b))))
      = (∑ y₁ : B₁ → O, (∏ b, p.prob (y₁ b)) * F₁ y₁)
        * (∑ y₂ : B₂ → O, (∏ b, p.prob (y₂ b)) * F₂ y₂) := by
    have hgo : ∀ w : (B₁ ⊕ B₂) → O,
        (∏ c, p.prob (w c))
          * (F₁ (fun b => w (Sum.inl b)) * F₂ (fun b => w (Sum.inr b)))
        = ((∏ b, p.prob ((elimTableEquiv w).1 b)) * F₁ (elimTableEquiv w).1)
          * ((∏ b, p.prob ((elimTableEquiv w).2 b)) * F₂ (elimTableEquiv w).2) := by
      intro w
      have hE1 : (elimTableEquiv w).1 = fun b => w (Sum.inl b) := rfl
      have hE2 : (elimTableEquiv w).2 = fun b => w (Sum.inr b) := rfl
      have hprod : (∏ c : B₁ ⊕ B₂, p.prob (w c))
          = (∏ b : B₁, p.prob (w (Sum.inl b))) * ∏ b : B₂, p.prob (w (Sum.inr b)) :=
        Fintype.prod_sum_type _
      rw [hprod]
      simp only [hE1, hE2]
      ring
    rw [Fintype.sum_equiv elimTableEquiv
        (fun w => (∏ c, p.prob (w c))
          * (F₁ (fun b => w (Sum.inl b)) * F₂ (fun b => w (Sum.inr b))))
        (fun pr => (∏ b, p.prob (pr.1 b)) * F₁ pr.1
          * ((∏ b, p.prob (pr.2 b)) * F₂ pr.2))
        hgo]
    rw [Fintype.sum_prod_type]
    simp only []
    rw [← Finset.sum_mul_sum]

  calc (∑ ω : Fin n → O, p.probOf ω * F₁ (fun b => ω (u₁ b))
          * F₂ (fun b => ω (u₂ b)))
      = ∑ ω : Fin n → O, p.probOf ω
          * (F₁ (fun b => ω (u₁ b)) * F₂ (fun b => ω (u₂ b))) :=
        Finset.sum_congr rfl fun ω _ => mul_assoc _ _ _
    _ = ∑ w : (B₁ ⊕ B₂) → O, (∏ c, p.prob (w c))
          * (F₁ (fun b => w (Sum.inl b)) * F₂ (fun b => w (Sum.inr b))) := hjr
    _ = (∑ y₁ : B₁ → O, (∏ b, p.prob (y₁ b)) * F₁ y₁)
        * (∑ y₂ : B₂ → O, (∏ b, p.prob (y₂ b)) * F₂ y₂) := hstep2

/-- Concatenation of two families of record tuples. -/
def familyAppend {n k r r' : ℕ} (T : Fin r → Fin k → Fin n)
    (S : Fin r' → Fin k → Fin n) : Fin (r + r') → Fin k → Fin n :=
  fun a => Sum.elim T S (finSumFinEquiv.symm a)

/-- The first part of an appended tuple family agrees with the first family. -/
theorem familyAppend_castAdd {n k r r' : ℕ} (T : Fin r → Fin k → Fin n)
    (S : Fin r' → Fin k → Fin n) (a : Fin r) :
    familyAppend T S (Fin.castAdd r' a) = T a := by
  simp only [familyAppend, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]

/-- The second part of an appended tuple family agrees with the second family. -/
theorem familyAppend_natAdd {n k r r' : ℕ} (T : Fin r → Fin k → Fin n)
    (S : Fin r' → Fin k → Fin n) (b : Fin r') :
    familyAppend T S (Fin.natAdd r b) = S b := by
  simp only [familyAppend, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-- The overlap moment of two appended families factors when each tuple is injective and the
families use disjoint records. -/
theorem overlapMoment_append_disjoint (p : FinDist O) {n k r r' : ℕ}
    (h : (Fin k → O) → ℝ) (T : Fin r → Fin k → Fin n) (S : Fin r' → Fin k → Fin n)
    (hT : familyInjective T) (hS : familyInjective S)
    (hdis : ∀ (a : Fin r) (b : Fin r') (i j : Fin k), T a i ≠ S b j) :
    overlapMomentK p h (familyAppend T S)
      = overlapMomentK p h T * overlapMomentK p h S := by
  classical

  have hcross : ∀ j₁ j₂, mergeTuple T j₁ ≠ mergeTuple S j₂ := by
    intro j₁ j₂ hcontra
    obtain ⟨α, -, hα⟩ := Finset.mem_image.1 (mergeTuple_mem T j₁)
    obtain ⟨β, -, hβ⟩ := Finset.mem_image.1 (mergeTuple_mem S j₂)
    rw [← hα, ← hβ] at hcontra
    exact hdis α.1 β.1 α.2 β.2 hcontra

  have hinl : ∀ a : Fin r,
      finSumFinEquiv (Sum.inl a : Fin r ⊕ Fin r') = Fin.castAdd r' a := by
    intro a
    rw [show Sum.inl a = finSumFinEquiv.symm (Fin.castAdd r' a) from
      (finSumFinEquiv_symm_apply_castAdd a).symm, Equiv.apply_symm_apply]
  have hinr : ∀ b : Fin r',
      finSumFinEquiv (Sum.inr b : Fin r ⊕ Fin r') = Fin.natAdd r b := by
    intro b
    rw [show Sum.inr b = finSumFinEquiv.symm (Fin.natAdd r b) from
      (finSumFinEquiv_symm_apply_natAdd b).symm, Equiv.apply_symm_apply]
  have hprod : ∀ ω : Fin n → O,
      (∏ a : Fin (r + r'),
          (h (fun i => ω (familyAppend T S a i)) - kernelMeanK p h))
      = (∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h))
        * ∏ b : Fin r', (h (fun i => ω (S b i)) - kernelMeanK p h) := by
    intro ω
    have h1 : (∏ a : Fin (r + r'),
          (h (fun i => ω (familyAppend T S a i)) - kernelMeanK p h))
        = ∏ c : Fin r ⊕ Fin r',
          (h (fun i => ω (familyAppend T S (finSumFinEquiv c) i)) - kernelMeanK p h) :=
      (Fintype.prod_equiv finSumFinEquiv _ _ fun _ => rfl).symm
    rw [h1, Fintype.prod_sum_type]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun a _ => ?_)
      (Finset.prod_congr rfl fun b _ => ?_)
    · show (h (fun i => ω (familyAppend T S (finSumFinEquiv (Sum.inl a)) i))
          - kernelMeanK p h)
        = h (fun i => ω (T a i)) - kernelMeanK p h
      rw [hinl a, familyAppend_castAdd]
    · show (h (fun i => ω (familyAppend T S (finSumFinEquiv (Sum.inr b)) i))
          - kernelMeanK p h)
        = h (fun i => ω (S b i)) - kernelMeanK p h
      rw [hinr b, familyAppend_natAdd]

  have hF₁ : ∀ ω : Fin n → O,
      (∏ a : Fin r, (h (fun i =>
          ω (mergeTuple T (posIndex T (a, i)))) - kernelMeanK p h))
      = ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) := by
    intro ω
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [mergeTuple_posIndex, posRead]
  have hF₂ : ∀ ω : Fin n → O,
      (∏ b : Fin r', (h (fun i =>
          ω (mergeTuple S (posIndex S (b, i)))) - kernelMeanK p h))
      = ∏ b : Fin r', (h (fun i => ω (S b i)) - kernelMeanK p h) := by
    intro ω
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [mergeTuple_posIndex, posRead]
  have hjr := jointReadFactor p (mergeTuple T) (mergeTuple_injective T)
    (mergeTuple S) (mergeTuple_injective S) hcross
    (fun y => ∏ a : Fin r, (h (fun i => y (posIndex T (a, i))) - kernelMeanK p h))
    (fun y => ∏ b : Fin r', (h (fun i => y (posIndex S (b, i))) - kernelMeanK p h))
  beta_reduce at hjr
  unfold overlapMomentK
  calc (∑ ω : Fin n → O, p.probOf ω
          * ∏ a : Fin (r + r'),
              (h (fun i => ω (familyAppend T S a i)) - kernelMeanK p h))
      = ∑ ω : Fin n → O, p.probOf ω
          * (∏ a : Fin r, (h (fun i =>
                ω (mergeTuple T (posIndex T (a, i)))) - kernelMeanK p h))
          * (∏ b : Fin r', (h (fun i =>
                ω (mergeTuple S (posIndex S (b, i)))) - kernelMeanK p h)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hprod ω, ← hF₁ ω, ← hF₂ ω]
        ring
    _ = overlapMomentK p h T * overlapMomentK p h S := by
        rw [hjr, overlapMomentK_eq_merged p h T, overlapMomentK_eq_merged p h S]

/-- Appending the final tuple to the preceding tuples reconstructs the original family. -/
theorem familyAppend_snoc {n k r : ℕ} (T : Fin (r + 1) → Fin k → Fin n) :
    familyAppend (fun a => T (Fin.castAdd 1 a)) (fun _ : Fin 1 => T (Fin.natAdd r 0)) = T := by
  funext a i
  rcases Nat.lt_or_ge (a : Fin (r + 1)).val r with hlt | hge
  · have ha : a = Fin.castAdd 1 ⟨(a : Fin (r + 1)).val, hlt⟩ := Fin.ext rfl
    rw [ha]
    simp only [familyAppend, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · have hval : (a : Fin (r + 1)).val = r := by omega
    have ha : a = Fin.natAdd r 0 := by
      refine Fin.ext ?_
      show (a : Fin (r + 1)).val = (Fin.natAdd r 0).val
      simp only [Fin.val_natAdd, Fin.val_zero]
      omega
    rw [ha]
    simp only [familyAppend, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

/-- The overlap moment factors into the preceding family and the last tuple when all tuples are
injective and the last tuple uses disjoint records. -/
theorem overlapMoment_snoc (p : FinDist O) {n k r : ℕ} (h : (Fin k → O) → ℝ)
    (T : Fin (r + 1) → Fin k → Fin n) (hT : familyInjective T)
    (hdis : ∀ (a : Fin r) (i j : Fin k),
      T (Fin.castAdd 1 a) i ≠ T (Fin.natAdd r 0) j) :
    overlapMomentK p h T
      = overlapMomentK p h (fun a => T (Fin.castAdd 1 a))
        * overlapMomentK p h (fun _ : Fin 1 => T (Fin.natAdd r 0)) := by
  have hinj : familyInjective (fun _ : Fin 1 => T (Fin.natAdd r 0)) := fun _ => hT _
  have hinj' : familyInjective (fun a => T (Fin.castAdd 1 a)) := fun a => hT _
  calc overlapMomentK p h T
      = overlapMomentK p h (familyAppend (fun a => T (Fin.castAdd 1 a))
          (fun _ : Fin 1 => T (Fin.natAdd r 0))) := by
        rw [familyAppend_snoc T]
    _ = overlapMomentK p h (fun a => T (Fin.castAdd 1 a))
        * overlapMomentK p h (fun _ : Fin 1 => T (Fin.natAdd r 0)) :=
          overlapMoment_append_disjoint p h _ _ hinj' hinj (fun a _ i j => hdis a i j)

/-- A nonempty family of injective tuples with no record coincidences has zero centered overlap
moment. -/
theorem overlapMoment_coincidenceFree_zero (p : FinDist O) {n k r : ℕ}
    (h : (Fin k → O) → ℝ) (hr : 0 < r) (T : Fin r → Fin k → Fin n)
    (hT : familyInjective T) (hfree : coincidenceFree T) :
    overlapMomentK p h T = 0 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos hr).symm⟩
  have hlast : Function.Injective (T (Fin.natAdd r' 0)) := hT _
  have hcross : ∀ (a : Fin r') (i j : Fin k),
      T (Fin.castAdd 1 a) i ≠ T (Fin.natAdd r' 0) j := by
    intro a i j hcontra
    refine hfree (Fin.castAdd 1 a, i) (Fin.natAdd r' 0, j) ?_ hcontra
    intro heq
    have hval : ((Fin.castAdd 1 a : Fin (r' + 1)) : ℕ)
        = ((Fin.natAdd r' 0 : Fin (r' + 1)) : ℕ) :=
      congrArg Fin.val (congrArg Prod.fst heq)
    simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at hval
    have : (a : Fin r').val < r' := a.2
    omega
  rw [overlapMoment_snoc p h T hT hcross,
    overlapMoment_single_zero p (T (Fin.natAdd r' 0)) hlast h, mul_zero]

/-- A common permutation of the record indices preserves the centered overlap moment. -/
theorem overlapMomentK_transport (p : FinDist O) {n k r : ℕ} (h : (Fin k → O) → ℝ)
    (σ : Fin n ≃ Fin n) (T T' : Fin r → Fin k → Fin n)
    (hT' : ∀ a i, T' a i = σ (T a i)) :
    overlapMomentK p h T = overlapMomentK p h T' := by
  have hsymm : ∀ a i, σ.symm (T' a i) = T a i := by
    intro a i
    rw [hT' a i]
    simp
  have hgo : ∀ ω : Fin n → O,
      (p.probOf ω * ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h))
      = p.probOf (precompEquiv σ ω)
          * ∏ a : Fin r,
              (h (fun i => precompEquiv σ ω (T' a i)) - kernelMeanK p h) := by
    intro ω
    have hp : p.probOf (precompEquiv σ ω) = p.probOf ω := by
      rw [precompEquiv]
      unfold Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf
      exact Equiv.prod_comp σ.symm (fun y => p.prob (ω y))
    rw [hp]
    have hbeta : ∀ a : Fin r,
        (fun i => precompEquiv σ ω (T' a i)) = (fun i => ω (T a i)) := by
      intro a
      funext i
      show ω (σ.symm (T' a i)) = ω (T a i)
      rw [hsymm a i]
    simp only [hbeta]
  exact Fintype.sum_equiv (precompEquiv σ)
    (fun ω => p.probOf ω * ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h))
    (fun ω => p.probOf ω * ∏ a : Fin r, (h (fun i => ω (T' a i)) - kernelMeanK p h)) hgo

/-- The least flattened position selecting the same record as `α`, used as its overlap label. -/
def overlapLabel {n k r : ℕ} (T : Fin r → Fin k → Fin n) (α : Fin r × Fin k) :
    Fin (r * k) :=
  ((Finset.univ : Finset (Fin (r * k))).filter
      (fun j => posRead T (finProdFinEquiv.symm j) = posRead T α)).min'
    ⟨finProdFinEquiv α, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simp⟩⟩

/-- Equal nonempty finite sets have equal minima, independently of the nonemptiness proofs. -/
theorem filterMin'_congr {m : ℕ} (s t : Finset (Fin m)) (h : s = t)
    (hs : s.Nonempty) (ht : t.Nonempty) : s.min' hs = t.min' ht := by
  subst h
  rfl

/-- A common permutation of record indices preserves the overlap labels of all positions. -/
theorem overlapLabel_transport {n k r : ℕ} (σ : Fin n ≃ Fin n)
    (T T' : Fin r → Fin k → Fin n) (hT' : ∀ α, posRead T' α = σ (posRead T α)) :
    overlapLabel T' = overlapLabel T := by
  funext α
  have hfilter : ((Finset.univ : Finset (Fin (r * k))).filter
      (fun j => posRead T' (finProdFinEquiv.symm j) = posRead T' α))
    = ((Finset.univ : Finset (Fin (r * k))).filter
      (fun j => posRead T (finProdFinEquiv.symm j) = posRead T α)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hT' _, hT' α]
    exact ⟨fun heq => σ.injective heq, fun heq => by rw [heq]⟩
  unfold overlapLabel
  exact filterMin'_congr _ _ hfilter _ _

/-- Pointwise transport of a tuple family by a record permutation preserves its overlap
labeling. -/
theorem overlapLabel_transport_family {n k r : ℕ} (σ : Fin n ≃ Fin n)
    (T T' : Fin r → Fin k → Fin n) (hT' : ∀ a i, T' a i = σ (T a i)) :
    overlapLabel T' = overlapLabel T :=
  overlapLabel_transport σ T T' (fun α => hT' α.1 α.2)

/-- The sum over families of injective tuples decomposes into sums indexed by their overlap
label functions. -/
theorem familyInjective_type_sum {n k r : ℕ} (F : (Fin r → Fin k → Fin n) → ℝ) :
    (∑ T : Fin r → Fin k → Fin n, (if familyInjective T then F T else 0))
      = ∑ c : Fin r × Fin k → Fin (r * k), ∑ T : Fin r → Fin k → Fin n,
          (if overlapLabel T = c ∧ familyInjective T then F T else 0) := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin r → Fin k → Fin n))
    overlapLabel (fun T => if familyInjective T then F T else 0)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases h1 : overlapLabel T = c <;>
    by_cases h2 : familyInjective T <;> simp [h1, h2]

/-- When the distinct-tuple count is nonzero, the centered U-statistic is the normalized sum of
centered kernel values over injective tuples. -/
theorem uStatistic_centered_eq_sum (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (hN : (distinctTupleCount n k : ℕ) ≠ 0) (ω : Fin n → O) :
    povmUStatisticK h ω - kernelMeanK p h
      = (∑ t : Fin k → Fin n, (if Function.Injective t then
          h (fun i => ω (t i)) - kernelMeanK p h else 0))
        / ((distinctTupleCount n k : ℕ) : ℝ) := by
  have hc := sum_injective_const (n := n) (k := k) (kernelMeanK p h)
  have hNne : ((distinctTupleCount n k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hN
  have hsplit : ∀ t : Fin k → Fin n,
      (if Function.Injective t then h (fun i => ω (t i)) - kernelMeanK p h else 0)
      = (if Function.Injective t then h (fun i => ω (t i)) else 0)
        - (if Function.Injective t then kernelMeanK p h else 0) := by
    intro t
    by_cases ht : Function.Injective t <;> simp [ht]
  have hkey : (∑ t : Fin k → Fin n, (if Function.Injective t then
        h (fun i => ω (t i)) else 0))
      - ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h
      = ∑ t : Fin k → Fin n, (if Function.Injective t then
          h (fun i => ω (t i)) - kernelMeanK p h else 0) := by
    rw [Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_sub_distrib, hc]
  calc povmUStatisticK h ω - kernelMeanK p h
      = (∑ t : Fin k → Fin n, (if Function.Injective t then
            h (fun i => ω (t i)) else 0)) / ((distinctTupleCount n k : ℕ) : ℝ)
          - kernelMeanK p h := rfl
    _ = ((∑ t : Fin k → Fin n, (if Function.Injective t then
            h (fun i => ω (t i)) else 0))
          - ((distinctTupleCount n k : ℕ) : ℝ) * kernelMeanK p h)
        / ((distinctTupleCount n k : ℕ) : ℝ) := by
          field_simp
    _ = (∑ t : Fin k → Fin n, (if Function.Injective t then
            h (fun i => ω (t i)) - kernelMeanK p h else 0))
        / ((distinctTupleCount n k : ℕ) : ℝ) := by rw [hkey]

/-- When the distinct-tuple count is nonzero, the centered U-statistic moment is the normalized
sum of overlap moments over families of injective tuples. -/
theorem uStatistic_moment_overlap (p : FinDist O) {n k r : ℕ} (h : (Fin k → O) → ℝ)
    (hN : (distinctTupleCount n k : ℕ) ≠ 0) :
    (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r)
      = (∑ T : Fin r → Fin k → Fin n,
          (if familyInjective T then overlapMomentK p h T else 0))
        / (((distinctTupleCount n k : ℕ) : ℝ) ^ r) := by
  classical

  have hstep : ∀ ω : Fin n → O,
      (povmUStatisticK h ω - kernelMeanK p h) ^ r
        = ((∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
              (fun t => Function.Injective t),
              (h (fun i => ω (t i)) - kernelMeanK p h)) ^ r)
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ r := by
    intro ω
    have h1 := uStatistic_centered_eq_sum p h hN ω
    have h2 : (∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
          (fun t => Function.Injective t),
          (h (fun i => ω (t i)) - kernelMeanK p h))
        = ∑ t : Fin k → Fin n, (if Function.Injective t then
            h (fun i => ω (t i)) - kernelMeanK p h else 0) :=
      Finset.sum_filter _ _
    rw [h1, h2, div_pow]

  have hpow : ∀ ω : Fin n → O,
      ((∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
            (fun t => Function.Injective t),
            (h (fun i => ω (t i)) - kernelMeanK p h)) ^ r)
      = ∑ T ∈ Fintype.piFinset
            (fun _ : Fin r => (Finset.univ : Finset (Fin k → Fin n)).filter
              (fun t => Function.Injective t)),
          ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) :=
    fun ω => Finset.sum_pow' _ _ r

  have hconv : ∀ ω : Fin n → O,
      (∑ T ∈ Fintype.piFinset
            (fun _ : Fin r => (Finset.univ : Finset (Fin k → Fin n)).filter
              (fun t => Function.Injective t)),
          ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h))
      = ∑ T : Fin r → Fin k → Fin n, (if familyInjective T then
          ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0) := by
    intro ω
    calc (∑ T ∈ Fintype.piFinset
            (fun _ : Fin r => (Finset.univ : Finset (Fin k → Fin n)).filter
              (fun t => Function.Injective t)),
          ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h))
        = ∑ T ∈ Fintype.piFinset
            (fun _ : Fin r => (Finset.univ : Finset (Fin k → Fin n)).filter
              (fun t => Function.Injective t)),
            (if familyInjective T then
              ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0) :=
          Finset.sum_congr rfl fun T hT =>
            ((if_pos (fun a =>
              (Finset.mem_filter.1 (Fintype.mem_piFinset.1 hT a)).2) :
              (if familyInjective T then
                ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0)
              = _).symm)
      _ = ∑ T : Fin r → Fin k → Fin n, (if familyInjective T then
            ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0) :=
          Finset.sum_subset (Finset.subset_univ _)
            (fun T _ hnot => if_neg (fun hTinj => hnot
              (Fintype.mem_piFinset.2 fun a =>
                Finset.mem_filter.2 ⟨Finset.mem_univ _, hTinj a⟩)))

  have hinner : ∀ T : Fin r → Fin k → Fin n,
      (∑ ω : Fin n → O, p.probOf ω * (if familyInjective T then
          ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0))
      = (if familyInjective T then overlapMomentK p h T else 0) := by
    intro T
    by_cases hT : familyInjective T
    · have hE : ∀ ω : Fin n → O,
          (p.probOf ω * (if familyInjective T then
            ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0))
          = p.probOf ω
              * ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) :=
        fun ω => congrArg (fun X => p.probOf ω * X)
          (if_pos hT : (if familyInjective T then
              ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0)
            = _)
      rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => hE ω, if_pos hT]
      rfl
    · have hE : ∀ ω : Fin n → O,
          (p.probOf ω * (if familyInjective T then
            ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0)) = 0 :=
        fun ω => by rw [if_neg hT, mul_zero]
      rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => hE ω,
        Finset.sum_eq_zero fun ω _ => rfl, if_neg hT]

  have hstep' : ∀ ω : Fin n → O,
      p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r
        = p.probOf ω * ((∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
              (fun t => Function.Injective t),
              (h (fun i => ω (t i)) - kernelMeanK p h)) ^ r)
          / ((distinctTupleCount n k : ℕ) : ℝ) ^ r := by
    intro ω
    rw [hstep ω, mul_div_assoc]
  calc (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r)
      = (∑ ω : Fin n → O, p.probOf ω
          * ((∑ t ∈ (Finset.univ : Finset (Fin k → Fin n)).filter
                (fun t => Function.Injective t),
                (h (fun i => ω (t i)) - kernelMeanK p h)) ^ r))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ r := by
        rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => hstep' ω,
          Finset.sum_div]
    _ = (∑ ω : Fin n → O, p.probOf ω
          * ∑ T : Fin r → Fin k → Fin n, (if familyInjective T then
              ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ r := by
        congr 1
        exact Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => by
          rw [hpow ω, hconv ω]
    _ = (∑ T : Fin r → Fin k → Fin n,
          (if familyInjective T then overlapMomentK p h T else 0))
        / ((distinctTupleCount n k : ℕ) : ℝ) ^ r := by
        congr 1
        have hswap : (∑ ω : Fin n → O, p.probOf ω
            * ∑ T : Fin r → Fin k → Fin n, (if familyInjective T then
                ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0))
          = ∑ T : Fin r → Fin k → Fin n, ∑ ω : Fin n → O, p.probOf ω
              * (if familyInjective T then
                  ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0) := by
          calc (∑ ω : Fin n → O, p.probOf ω
                * ∑ T : Fin r → Fin k → Fin n, (if familyInjective T then
                    ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0))
              = ∑ ω : Fin n → O, ∑ T : Fin r → Fin k → Fin n, p.probOf ω
                  * (if familyInjective T then
                      ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0) :=
                Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
                  Finset.mul_sum _ _ _
            _ = ∑ T : Fin r → Fin k → Fin n, ∑ ω : Fin n → O, p.probOf ω
                  * (if familyInjective T then
                      ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h) else 0) :=
                Finset.sum_comm
        rw [hswap, Finset.sum_congr rfl fun T (_ : T ∈ Finset.univ) => hinner T]

/-- The centered U-statistic moment decomposes by overlap labels, with normalization by the
distinct-tuple count raised to the moment order. -/
theorem uStatistic_moment_overlap_type (p : FinDist O) {n k r : ℕ}
    (h : (Fin k → O) → ℝ) (hN : (distinctTupleCount n k : ℕ) ≠ 0) :
    (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r)
      = (∑ c : Fin r × Fin k → Fin (r * k), ∑ T : Fin r → Fin k → Fin n,
          (if overlapLabel T = c ∧ familyInjective T then
            overlapMomentK p h T else 0))
        / (((distinctTupleCount n k : ℕ) : ℝ) ^ r) := by
  rw [uStatistic_moment_overlap p h hN,
    familyInjective_type_sum (fun T => overlapMomentK p h T)]

/-- The first tuple of the family formed by appending two singleton families is the first
supplied tuple. -/
theorem familyAppend_pair_zero {n k : ℕ} (t s : Fin k → Fin n) :
    familyAppend (fun _ : Fin 1 => t) (fun _ : Fin 1 => s) (0 : Fin 2) = t := by
  have h0 : (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) := Fin.ext rfl
  rw [h0, familyAppend_castAdd]

/-- The second tuple of the family formed by appending two singleton families is the second
supplied tuple. -/
theorem familyAppend_pair_one {n k : ℕ} (t s : Fin k → Fin n) :
    familyAppend (fun _ : Fin 1 => t) (fun _ : Fin 1 => s) (1 : Fin 2) = s := by
  have h1 : (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) := Fin.ext rfl
  rw [h1, familyAppend_natAdd]

/-- For two injective tuples, their centered overlap moment equals their overlap covariance. -/
theorem overlapMoment_pair (p : FinDist O) {n k : ℕ} (h : (Fin k → O) → ℝ)
    (t s : Fin k → Fin n) (ht : Function.Injective t) (hs : Function.Injective s) :
    overlapMomentK p h (familyAppend (fun _ : Fin 1 => t) (fun _ : Fin 1 => s))
      = overlapCovarianceK p h t s := by
  rw [overlapCovarianceK_eq p h t s ht hs]
  unfold overlapMomentK
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Fin.prod_univ_two, familyAppend_pair_zero, familyAppend_pair_one]
  ring

/-- The absolute centered moment of order `m` of the kernel under the product law with marginal
`p`. -/
noncomputable def centeredAbsMomentK (p : FinDist O) {k : ℕ} (h : (Fin k → O) → ℝ)
    (m : ℕ) : ℝ :=
  ∑ y : Fin k → O, (∏ i : Fin k, p.prob (y i)) * |h y - kernelMeanK p h| ^ m

/-- Reading any injective tuple of independent records gives the kernel's absolute centered
moment. -/
theorem read_abs_moment (p : FinDist O) {n k : ℕ} (t : Fin k → Fin n)
    (ht : Function.Injective t) (h : (Fin k → O) → ℝ) (m : ℕ) :
    (∑ ω : Fin n → O, p.probOf ω
        * |h (fun i => ω (t i)) - kernelMeanK p h| ^ m)
      = centeredAbsMomentK p h m :=
  povm_joint_expect p t ht (fun y => |h y - kernelMeanK p h| ^ m)

/-- Every absolute centered kernel moment is nonnegative. -/
theorem centeredAbsMomentK_nonneg (p : FinDist O) {k : ℕ} (h : (Fin k → O) → ℝ)
    (m : ℕ) : 0 ≤ centeredAbsMomentK p h m := by
  refine Finset.sum_nonneg fun y (_ : y ∈ Finset.univ) => ?_
  exact mul_nonneg (Finset.prod_nonneg fun i (_ : i ∈ Finset.univ) => p.nonneg _)
    (pow_nonneg (abs_nonneg _) _)

/-- For a nonempty finite family of nonnegative reals, the product is bounded by the average of
their powers of order equal to the family size. -/
theorem prod_le_average_pow {m : ℕ} (hm : 0 < m) (u : Fin m → ℝ) (hu : ∀ a, 0 ≤ u a) :
    ∏ a : Fin m, u a ≤ (∑ a : Fin m, u a ^ m) / (m : ℝ) := by
  have hmR : ((m : ℝ)) ≠ 0 := by exact_mod_cast hm.ne'
  have hz : ∀ a ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ u a ^ ((m : ℝ)) := by
    intro a _
    rw [Real.rpow_natCast]
    exact pow_nonneg (hu a) m
  have hw : ∀ a ∈ (Finset.univ : Finset (Fin m)), 0 ≤ ((m : ℝ)⁻¹) := by
    intro a _
    exact inv_nonneg.mpr (by exact_mod_cast hm.le)
  have hwsum : ∑ a ∈ (Finset.univ : Finset (Fin m)), ((m : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hmR
  have ham := Real.geom_mean_le_arith_mean_weighted
    (Finset.univ : Finset (Fin m))
    (fun _ : Fin m => ((m : ℝ)⁻¹)) (fun a => u a ^ ((m : ℝ))) hw hwsum hz
  have hlhs : ∏ a ∈ (Finset.univ : Finset (Fin m)),
      (u a ^ ((m : ℝ))) ^ ((m : ℝ)⁻¹) = ∏ a : Fin m, u a := by
    refine Finset.prod_congr rfl fun a _ => ?_
    exact Real.rpow_rpow_inv (hu a) hmR
  rw [hlhs] at ham
  have hrhs : ∑ a ∈ (Finset.univ : Finset (Fin m)),
      ((m : ℝ)⁻¹) * (u a ^ ((m : ℝ)))
      = (∑ a : Fin m, u a ^ m) / (m : ℝ) := by
    calc ∑ a ∈ (Finset.univ : Finset (Fin m)), ((m : ℝ)⁻¹) * (u a ^ ((m : ℝ)))
        = ∑ a : Fin m, (u a ^ m) * ((m : ℝ)⁻¹) := by
          refine Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => ?_
          rw [Real.rpow_natCast (u a) m, mul_comm]
      _ = (∑ a : Fin m, u a ^ m) * ((m : ℝ)⁻¹) := (Finset.sum_mul _ _ _).symm
      _ = (∑ a : Fin m, u a ^ m) / (m : ℝ) := (div_eq_mul_inv _ _).symm
  rw [hrhs] at ham
  exact ham

/-- For positive order and injective tuples, the absolute overlap moment is bounded by the
corresponding absolute centered kernel moment. -/
theorem overlapMoment_abs_le (p : FinDist O) {n k r : ℕ} (hr : 0 < r)
    (h : (Fin k → O) → ℝ) (T : Fin r → Fin k → Fin n) (hT : familyInjective T) :
    |overlapMomentK p h T| ≤ centeredAbsMomentK p h r := by

  have hAM : ∀ ω : Fin n → O,
      (∏ a : Fin r, |h (fun i => ω (T a i)) - kernelMeanK p h|)
      ≤ (∑ a : Fin r,
          |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r) / (r : ℝ) :=
    fun ω => prod_le_average_pow hr
      (fun a => |h (fun i => ω (T a i)) - kernelMeanK p h|)
      (fun a => abs_nonneg _)

  have hread : ∀ a : Fin r, (∑ ω : Fin n → O, p.probOf ω
      * |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r)
      = centeredAbsMomentK p h r := fun a => read_abs_moment p (T a) (hT a) h r

  have habsprod : ∀ ω : Fin n → O,
      |∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h)|
      = ∏ a : Fin r, |h (fun i => ω (T a i)) - kernelMeanK p h| :=
    fun ω => Finset.abs_prod _ _
  have hRne : ((r : ℝ)) ≠ 0 := by exact_mod_cast hr.ne'
  unfold overlapMomentK
  calc |∑ ω : Fin n → O, p.probOf ω
          * ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h)|
      ≤ ∑ ω : Fin n → O,
          |p.probOf ω
            * ∏ a : Fin r, (h (fun i => ω (T a i)) - kernelMeanK p h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω : Fin n → O, p.probOf ω
          * ∏ a : Fin r, |h (fun i => ω (T a i)) - kernelMeanK p h| := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [← habsprod ω, abs_mul, abs_of_nonneg (probOf_nonneg p ω)]
    _ ≤ ∑ ω : Fin n → O, p.probOf ω
          * ((∑ a : Fin r,
              |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r) / (r : ℝ)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hAM ω)
          (probOf_nonneg p ω)
    _ = (∑ a : Fin r, ∑ ω : Fin n → O, p.probOf ω
          * |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r) / (r : ℝ) := by
        calc (∑ ω : Fin n → O, p.probOf ω
              * ((∑ a : Fin r,
                  |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r) / (r : ℝ)))
            = ∑ ω : Fin n → O, (p.probOf ω
                * ∑ a : Fin r, |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r)
                / (r : ℝ) :=
              Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
                (mul_div_assoc _ _ _).symm
          _ = ((∑ ω : Fin n → O, p.probOf ω
                * ∑ a : Fin r, |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r))
              / (r : ℝ) := by rw [Finset.sum_div]
          _ = ((∑ a : Fin r, ∑ ω : Fin n → O, p.probOf ω
                * |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r)) / (r : ℝ) := by
              congr 1
              calc (∑ ω : Fin n → O, p.probOf ω
                    * ∑ a : Fin r, |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r)
                  = ∑ ω : Fin n → O, ∑ a : Fin r, p.probOf ω
                      * |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r :=
                    Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
                      Finset.mul_sum _ _ _
                _ = ∑ a : Fin r, ∑ ω : Fin n → O, p.probOf ω
                      * |h (fun i => ω (T a i)) - kernelMeanK p h| ^ r :=
                    Finset.sum_comm
    _ = (∑ a : Fin r, centeredAbsMomentK p h r) / (r : ℝ) := by
        exact congrArg (· / (r : ℝ))
          (Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hread a)
    _ = centeredAbsMomentK p h r := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_div_cancel_left₀ _ hRne]

/-- Currying identifies tuple families with functions from pairs of tuple and coordinate
indices. -/
def familyEquiv {n k r : ℕ} : (Fin r → Fin k → Fin n) ≃ (Fin r × Fin k → Fin n) where
  toFun T := posRead T
  invFun g a i := g (a, i)
  left_inv T := by funext a i; rfl
  right_inv g := by funext α; rcases α with ⟨a, i⟩; rfl

/-- Functions taking equal values at two distinct positions correspond to arbitrary functions on
all positions except the first. -/
def posFiberEquiv {n k r : ℕ} (α β : Fin r × Fin k) (hβ : β ≠ α) :
    {g : Fin r × Fin k → Fin n // g α = g β} ≃ (∀ x : {x : Fin r × Fin k // x ≠ α}, Fin n) where
  toFun hg x := hg.1 x.1
  invFun w := ⟨fun x => dite (x = α) (fun _ => w ⟨β, hβ⟩) (fun hx => w ⟨x, hx⟩), by
    show dite (α = α) (fun _ => w ⟨β, hβ⟩) (fun hx => w ⟨α, hx⟩)
        = dite (β = α) (fun _ => w ⟨β, hβ⟩) (fun hx => w ⟨β, hx⟩)
    rw [dif_pos rfl, dif_neg hβ]⟩
  left_inv hg := by
    refine Subtype.ext (funext fun x => ?_)
    show dite (x = α) (fun _ => hg.1 β) (fun hx => hg.1 x) = hg.1 x
    by_cases hx : x = α
    · rw [dif_pos hx, hx]
      exact hg.2.symm
    · rw [dif_neg hx]
  right_inv w := by
    funext x
    by_cases hx : (x : Fin r × Fin k) = α
    · exact absurd hx x.2
    · show dite ((x : Fin r × Fin k) = α) (fun _ => w ⟨β, hβ⟩)
          (fun hx' => w ⟨x, hx'⟩) = w x
      rw [dif_neg hx]

/-- The number of record assignments identifying two distinct positions is `n` raised to the
number of remaining positions. -/
theorem pos_fiber_card {n k r : ℕ} (α β : Fin r × Fin k) (hαβ : α ≠ β) :
    Fintype.card {g : Fin r × Fin k → Fin n // g α = g β}
      = n ^ (Fintype.card (Fin r × Fin k) - 1) := by
  classical
  calc Fintype.card {g : Fin r × Fin k → Fin n // g α = g β}
      = Fintype.card (∀ x : {x : Fin r × Fin k // x ≠ α}, Fin n) :=
        Fintype.card_congr (posFiberEquiv α β (Ne.symm hαβ))
    _ = n ^ (Fintype.card {x : Fin r × Fin k // x ≠ α}) := by
        simp
    _ = n ^ (Fintype.card (Fin r × Fin k) - 1) := by
        congr 1
        classical
        rw [Fintype.card_congr (Equiv.subtypeEquivRight
            (fun x : Fin r × Fin k => (Iff.rfl : x ≠ α ↔ ¬(x = α)))),
          Fintype.card_subtype_compl, Fintype.card_subtype_eq α]

/-- The number of tuple families whose reads coincide at two fixed distinct positions is `n`
raised to the total position count minus one. -/
theorem pos_fiber_filter_card {n k r : ℕ} (α β : Fin r × Fin k) (hαβ : α ≠ β) :
    ((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
        (fun T => posRead T α = posRead T β)).card
      = n ^ (Fintype.card (Fin r × Fin k) - 1) := by
  classical
  have hbridge : ((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
      (fun T => posRead T α = posRead T β)).card
      = Fintype.card {T : Fin r → Fin k → Fin n // posRead T α = posRead T β} := by
    have e : {T : Fin r → Fin k → Fin n // posRead T α = posRead T β}
        ≃ {T : Fin r → Fin k → Fin n //
            T ∈ Finset.univ.filter (fun T => posRead T α = posRead T β)} :=
      Equiv.subtypeEquivRight (fun T => by simp [Finset.mem_filter])
    rw [Fintype.card_congr e, Fintype.card_coe]
  have he : {T : Fin r → Fin k → Fin n // posRead T α = posRead T β}
      ≃ {g : Fin r × Fin k → Fin n // g α = g β} :=
    Equiv.subtypeEquiv familyEquiv (fun _ => Iff.rfl)
  rw [hbridge, Fintype.card_congr he, pos_fiber_card α β hαβ]

/-- A family of `r` tuples of length `k` has `r * k` positions. -/
theorem pos_card {k r : ℕ} : Fintype.card (Fin r × Fin k) = r * k := by
  rw [Fintype.card_prod]
  simp

/-- The number of families of injective tuples with a record coincidence is at most `(r * k) *
(r * k) * n ^ (r * k - 1)`. -/
theorem coinciding_family_card_le {n k r : ℕ} :
    ((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
        (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
          α ≠ β ∧ posRead T α = posRead T β)).card
      ≤ (r * k) * (r * k) * n ^ (r * k - 1) := by
  classical
  set A : Fin r × Fin k → Fin r × Fin k → Finset (Fin r → Fin k → Fin n) := fun α β =>
    Finset.univ.filter (fun T => posRead T α = posRead T β) with hA
  have hsub : ((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
        (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
          α ≠ β ∧ posRead T α = posRead T β))
      ⊆ Finset.biUnion ((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
        (fun pq => pq.1 ≠ pq.2)) (fun pq => A pq.1 pq.2) := by
    intro T hT
    obtain ⟨_, ⟨_, α, β, hαβ, hco⟩⟩ := Finset.mem_filter.1 hT
    refine Finset.mem_biUnion.2 ⟨(α, β),
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hαβ⟩, ?_⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hco⟩
  have hpaircard : (((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
        (fun pq => pq.1 ≠ pq.2)).card : ℕ) ≤ r * k * (r * k) := by
    refine Nat.le_trans (Finset.card_filter_le _ _) ?_
    rw [Finset.card_univ]
    simp [Fintype.card_prod]
  calc ((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
        (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
          α ≠ β ∧ posRead T α = posRead T β)).card
      ≤ (Finset.biUnion ((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
          (fun pq => pq.1 ≠ pq.2)) (fun pq => A pq.1 pq.2)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ pq ∈ ((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
          (fun pq => pq.1 ≠ pq.2)), (A pq.1 pq.2).card :=
        Finset.card_biUnion_le
    _ ≤ (r * k * (r * k)) * n ^ (r * k - 1) := by
        have hfib : ∀ pq ∈ ((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
            (fun pq => pq.1 ≠ pq.2)),
            (A pq.1 pq.2).card ≤ n ^ (r * k - 1) := by
          intro pq hpq
          have hne : pq.1 ≠ pq.2 := (Finset.mem_filter.1 hpq).2
          rw [hA, pos_fiber_filter_card pq.1 pq.2 hne, pos_card]
        calc ∑ pq ∈ ((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
              (fun pq => pq.1 ≠ pq.2)), (A pq.1 pq.2).card
            ≤ ∑ pq ∈ ((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
                (fun pq => pq.1 ≠ pq.2)), n ^ (r * k - 1) :=
              Finset.sum_le_sum fun pq hpq => hfib pq hpq
          _ = (((Finset.univ : Finset ((Fin r × Fin k) × (Fin r × Fin k))).filter
                (fun pq => pq.1 ≠ pq.2)).card : ℕ) * n ^ (r * k - 1) := by
              rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
          _ ≤ (r * k * (r * k)) * n ^ (r * k - 1) :=
              Nat.mul_le_mul hpaircard (Nat.le_refl _)

/-- For positive order and a nonzero distinct-tuple count, the absolute centered U-statistic
moment is bounded by the absolute kernel moment times the coincidence count bound, divided
by the tuple-count normalization. -/
theorem uStatistic_moment_abs_le (p : FinDist O) {n k r : ℕ} (hr : 0 < r)
    (h : (Fin k → O) → ℝ) (hN : (distinctTupleCount n k : ℕ) ≠ 0) :
    |∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r|
      ≤ centeredAbsMomentK p h r
          * (((r * k) * (r * k) * n ^ (r * k - 1) : ℕ) : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ r) := by
  classical
  have hNpos : (0 : ℝ) < ((distinctTupleCount n k : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hNr : (0 : ℝ) < ((distinctTupleCount n k : ℕ) : ℝ) ^ r :=
    pow_pos hNpos r
  rw [uStatistic_moment_overlap p h hN, abs_div, abs_of_nonneg hNr.le]
  have hpoint : ∀ T : Fin r → Fin k → Fin n,
      |(if familyInjective T then overlapMomentK p h T else 0)|
      ≤ (if familyInjective T ∧ ∃ α β : Fin r × Fin k,
            α ≠ β ∧ posRead T α = posRead T β
          then centeredAbsMomentK p h r else 0) := by
    intro T
    by_cases hT : familyInjective T
    · by_cases hc : ∃ α β : Fin r × Fin k, α ≠ β ∧ posRead T α = posRead T β
      · rw [if_pos hT, if_pos ⟨hT, hc⟩]
        exact overlapMoment_abs_le p hr h T hT
      · rw [if_pos hT, if_neg (fun hc' => hc hc'.2)]
        have hfree : coincidenceFree T := by
          intro α β hαβ hco
          exact hc ⟨α, β, hαβ, hco⟩
        rw [overlapMoment_coincidenceFree_zero p h hr T hT hfree]
        simp
    · rw [if_neg hT, if_neg (fun hc' => hT hc'.1)]
      simp
  have hsumabs : |(∑ T : Fin r → Fin k → Fin n,
      (if familyInjective T then overlapMomentK p h T else 0))|
      ≤ (((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
          (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
            α ≠ β ∧ posRead T α = posRead T β)).card : ℝ)
        * centeredAbsMomentK p h r := by
    have h1 := Finset.abs_sum_le_sum_abs
      (fun T : Fin r → Fin k → Fin n =>
        if familyInjective T then overlapMomentK p h T else 0) Finset.univ
    have hsumle : (∑ T : Fin r → Fin k → Fin n,
        |(if familyInjective T then overlapMomentK p h T else 0)|)
      ≤ (((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
          (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
            α ≠ β ∧ posRead T α = posRead T β)).card : ℝ)
        * centeredAbsMomentK p h r := by
      have hstep := Finset.sum_le_sum (fun T (_ : T ∈ Finset.univ) => hpoint T)
      have hsumeq : (∑ T : Fin r → Fin k → Fin n,
          (if familyInjective T ∧ ∃ α β : Fin r × Fin k,
                α ≠ β ∧ posRead T α = posRead T β
              then centeredAbsMomentK p h r else 0))
        = (((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
          (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
            α ≠ β ∧ posRead T α = posRead T β)).card : ℝ)
          * centeredAbsMomentK p h r := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [hsumeq] at hstep
      exact hstep
    exact h1.trans hsumle
  have hcast : (((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
      (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
        α ≠ β ∧ posRead T α = posRead T β)).card : ℝ)
    ≤ (((r * k) * (r * k) * n ^ (r * k - 1) : ℕ) : ℝ) := by
    exact_mod_cast coinciding_family_card_le
  exact div_le_div_of_nonneg_right
    (le_trans hsumabs
      (calc (((Finset.univ : Finset (Fin r → Fin k → Fin n)).filter
            (fun T => familyInjective T ∧ ∃ α β : Fin r × Fin k,
              α ≠ β ∧ posRead T α = posRead T β)).card : ℝ)
          * centeredAbsMomentK p h r
        ≤ (((r * k) * (r * k) * n ^ (r * k - 1) : ℕ) : ℝ)
            * centeredAbsMomentK p h r :=
          mul_le_mul_of_nonneg_right hcast (centeredAbsMomentK_nonneg p h r)
      _ = centeredAbsMomentK p h r
            * (((r * k) * (r * k) * n ^ (r * k - 1) : ℕ) : ℝ) := by ring))
    hNr.le

/-- The probability of a deviation strictly exceeding a positive threshold is bounded by a
positive even centered moment divided by the corresponding threshold power. -/
theorem probEvent_le_even_moment {X : Type} [Fintype X] {n : ℕ} (p : FinDist X)
    (f : (Fin n → X) → ℝ) (μ : ℝ) (hμ : ∑ ω : Fin n → X, p.probOf ω * f ω = μ)
    {s : ℕ} (hs : 0 < s) (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p (fun ω : Fin n → X => ε < |f ω - μ|)
      ≤ (∑ ω : Fin n → X, p.probOf ω * (f ω - μ) ^ (2 * s)) / ε ^ (2 * s) := by
  classical
  have hpos : 0 < 2 * s := by omega
  have h2 : 0 < ε ^ (2 * s) := by positivity
  have hpt : ∀ x : ℝ, 0 ≤ x ^ (2 * s) := by
    intro x
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hsub : (Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|))
      ⊆ (Finset.univ : Finset (Fin n → X)) := Finset.filter_subset _ _
  have hpoint : ∀ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
      p.probOf ω ≤ p.probOf ω * (f ω - μ) ^ (2 * s) / ε ^ (2 * s) := by
    intro ω hω
    have hev : ε < |f ω - μ| := Finset.mem_filter.mp hω |>.2
    have hnonneg : 0 ≤ (f ω - μ) ^ (2 * s) := hpt _
    have h1 : ε ^ (2 * s) < (f ω - μ) ^ (2 * s) := by
      have habs : ε ^ (2 * s) < |f ω - μ| ^ (2 * s) :=
        pow_lt_pow_left₀ hev hε.le hpos.ne'
      have heq : |f ω - μ| ^ (2 * s) = (f ω - μ) ^ (2 * s) := by
        rcases lt_or_ge 0 (f ω - μ) with hpos' | hnn
        · rw [abs_of_nonneg (le_of_lt hpos')]
        · rw [abs_of_nonpos hnn, neg_pow, Even.neg_one_pow ⟨s, Nat.two_mul s⟩,
            one_mul]
      rwa [heq] at habs
    have hle : (1 : ℝ) ≤ (f ω - μ) ^ (2 * s) / ε ^ (2 * s) := by
      rw [le_div_iff₀ h2, one_mul]
      exact le_of_lt h1
    calc p.probOf ω = p.probOf ω * 1 := by ring
      _ ≤ p.probOf ω * ((f ω - μ) ^ (2 * s) / ε ^ (2 * s)) :=
          mul_le_mul_of_nonneg_left hle (probOf_nonneg p ω)
      _ = p.probOf ω * (f ω - μ) ^ (2 * s) / ε ^ (2 * s) := by ring
  have hsum1 : (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|), p.probOf ω)
      ≤ (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
          p.probOf ω * (f ω - μ) ^ (2 * s)) / ε ^ (2 * s) := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum fun ω hω => hpoint ω hω
  have hsum2 : (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
      p.probOf ω * (f ω - μ) ^ (2 * s))
      ≤ ∑ ω : Fin n → X, p.probOf ω * (f ω - μ) ^ (2 * s) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ =>
      mul_nonneg (probOf_nonneg p ω) (hpt _)
  have hdef : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p (fun ω : Fin n → X => ε < |f ω - μ|)
      = ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|), p.probOf ω :=
    rfl
  rw [hdef]
  calc ∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|), p.probOf ω
      ≤ (∑ ω ∈ Finset.univ.filter (fun ω : Fin n → X => ε < |f ω - μ|),
          p.probOf ω * (f ω - μ) ^ (2 * s)) / ε ^ (2 * s) := hsum1
    _ ≤ (∑ ω : Fin n → X, p.probOf ω * (f ω - μ) ^ (2 * s)) / ε ^ (2 * s) :=
        div_le_div_of_nonneg_right hsum2 h2.le

/-- The U-statistic deviation probability is bounded using the absolute centered kernel moment
of order `2 * s` and the record-coincidence count. -/
theorem probEvent_uStatistic_hkp (p : FinDist O) {n k s : ℕ} (hs : 0 < s)
    (h : (Fin k → O) → ℝ) (hN : (distinctTupleCount n k : ℕ) ≠ 0)
    (ε : ℝ) (hε : 0 < ε) :
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p
        (fun ω : Fin n → O => ε < |povmUStatisticK h ω - kernelMeanK p h|)
      ≤ centeredAbsMomentK p h (2 * s)
          * ((((2 * s) * k) * ((2 * s) * k) * n ^ ((2 * s) * k - 1) : ℕ) : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ (2 * s) * ε ^ (2 * s)) := by
  have hunb := povmUStatisticK_unbiased p h hN
  have hcheb := probEvent_le_even_moment p (povmUStatisticK h) (kernelMeanK p h) hunb
    hs ε hε
  have hr2 : 0 < 2 * s := by omega
  have hvar := uStatistic_moment_abs_le p hr2 h hN
  have h2 : 0 < ε ^ (2 * s) := by positivity
  have hnn : 0 ≤ ∑ ω : Fin n → O,
      p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ (2 * s) := by
    refine Finset.sum_nonneg fun ω _ => ?_
    refine mul_nonneg (probOf_nonneg p ω) ?_
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  calc Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p
        (fun ω : Fin n → O => ε < |povmUStatisticK h ω - kernelMeanK p h|)
      ≤ (∑ ω : Fin n → O,
          p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ (2 * s))
        / ε ^ (2 * s) := hcheb
    _ ≤ (centeredAbsMomentK p h (2 * s)
          * ((((2 * s) * k) * ((2 * s) * k) * n ^ ((2 * s) * k - 1) : ℕ) : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ (2 * s))) / ε ^ (2 * s) :=
        div_le_div_of_nonneg_right (le_trans (le_abs_self _) hvar) h2.le
    _ = centeredAbsMomentK p h (2 * s)
          * ((((2 * s) * k) * ((2 * s) * k) * n ^ ((2 * s) * k - 1) : ℕ) : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ (2 * s) * ε ^ (2 * s)) := by
        rw [div_div]

/-- Collects the overlap and overlap-type moment expansions, permutation invariance, disjoint
factorization, vanishing and covariance identities, and moment and deviation bounds for
finite U-statistics. -/
theorem frontier1 :
    ∀ {O : Type} [Fintype O] [DecidableEq O] (p : FinDist O) {n k r : ℕ},
      0 < r → (distinctTupleCount n k : ℕ) ≠ 0 → ∀ (h : (Fin k → O) → ℝ),
      (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r
        = (∑ T : Fin r → Fin k → Fin n,
            (if familyInjective T then overlapMomentK p h T else 0))
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ r)) ∧
      (∑ ω : Fin n → O, p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r
        = (∑ c : Fin r × Fin k → Fin (r * k), ∑ T : Fin r → Fin k → Fin n,
            (if overlapLabel T = c ∧ familyInjective T then
              overlapMomentK p h T else 0))
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ r)) ∧
      (∀ (σ : Fin n ≃ Fin n) (T T' : Fin r → Fin k → Fin n),
        (∀ a i, T' a i = σ (T a i)) →
        overlapMomentK p h T = overlapMomentK p h T'
          ∧ overlapLabel T' = overlapLabel T) ∧
      (∀ (r' : ℕ) (T : Fin r → Fin k → Fin n) (S : Fin r' → Fin k → Fin n),
        familyInjective T → familyInjective S →
        (∀ (a : Fin r) (b : Fin r') (i j : Fin k), T a i ≠ S b j) →
        overlapMomentK p h (familyAppend T S)
          = overlapMomentK p h T * overlapMomentK p h S) ∧
      (∀ T : Fin r → Fin k → Fin n, familyInjective T → coincidenceFree T →
        overlapMomentK p h T = 0) ∧
      (∀ (t s : Fin k → Fin n), Function.Injective t → Function.Injective s →
        overlapMomentK p h (familyAppend (fun _ : Fin 1 => t) (fun _ : Fin 1 => s))
          = overlapCovarianceK p h t s) ∧
      (|∑ ω : Fin n → O,
          p.probOf ω * (povmUStatisticK h ω - kernelMeanK p h) ^ r|
        ≤ centeredAbsMomentK p h r
            * (((r * k) * (r * k) * n ^ (r * k - 1) : ℕ) : ℝ)
            / (((distinctTupleCount n k : ℕ) : ℝ) ^ r)) ∧
      (∀ (s : ℕ), 0 < s → ∀ ε : ℝ, 0 < ε →
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) p
            (fun ω : Fin n → O =>
              ε < |povmUStatisticK h ω - kernelMeanK p h|)
          ≤ centeredAbsMomentK p h (2 * s)
              * ((((2 * s) * k) * ((2 * s) * k) * n ^ ((2 * s) * k - 1) : ℕ) : ℝ)
              / (((distinctTupleCount n k : ℕ) : ℝ) ^ (2 * s) * ε ^ (2 * s))) := by
  intro O _ _ p n k r hr hN h
  exact ⟨uStatistic_moment_overlap p h hN,
    uStatistic_moment_overlap_type p h hN,
    fun σ T T' hT' => ⟨overlapMomentK_transport p h σ T T' hT',
      overlapLabel_transport_family σ T T' hT'⟩,
    fun r' T S hT hS hdis => overlapMoment_append_disjoint p h T S hT hS hdis,
    fun T hT hfree => overlapMoment_coincidenceFree_zero p h hr T hT hfree,
    fun t s ht hs => overlapMoment_pair p h t s ht hs,
    uStatistic_moment_abs_le p hr h hN,
    fun s hs ε hε => probEvent_uStatistic_hkp p hs h hN ε hε⟩

section Povm

open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative

variable {D : ℕ}

/-- Specializes the overlap expansions, permutation invariance, factorization, vanishing and
covariance identities, and moment and deviation bounds to independent records of a finite
POVM. -/
theorem frontier1_povm (E : FinitePOVM O D) (ρ : Operator D) (hρ : IsDensityOperator ρ)
    {n k r : ℕ} (hr : 0 < r) (hN : (distinctTupleCount n k : ℕ) ≠ 0)
    (h : (Fin k → O) → ℝ) :
    ((povmSampleLaw E ρ hρ).expect (fun ω : Fin n → O =>
        (povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h) ^ r)
      = (∑ T : Fin r → Fin k → Fin n,
          (if familyInjective T then
            overlapMomentK (povmRecordLaw E ρ hρ) h T else 0))
        / (((distinctTupleCount n k : ℕ) : ℝ) ^ r)) ∧
    ((povmSampleLaw E ρ hρ).expect (fun ω : Fin n → O =>
        (povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h) ^ r)
      = (∑ c : Fin r × Fin k → Fin (r * k), ∑ T : Fin r → Fin k → Fin n,
          (if overlapLabel T = c ∧ familyInjective T then
            overlapMomentK (povmRecordLaw E ρ hρ) h T else 0))
        / (((distinctTupleCount n k : ℕ) : ℝ) ^ r)) ∧
    (∀ (σ : Fin n ≃ Fin n) (T T' : Fin r → Fin k → Fin n),
      (∀ a i, T' a i = σ (T a i)) →
      overlapMomentK (povmRecordLaw E ρ hρ) h T
        = overlapMomentK (povmRecordLaw E ρ hρ) h T'
        ∧ overlapLabel T' = overlapLabel T) ∧
    (∀ (r' : ℕ) (T : Fin r → Fin k → Fin n) (S : Fin r' → Fin k → Fin n),
      familyInjective T → familyInjective S →
      (∀ (a : Fin r) (b : Fin r') (i j : Fin k), T a i ≠ S b j) →
      overlapMomentK (povmRecordLaw E ρ hρ) h (familyAppend T S)
        = overlapMomentK (povmRecordLaw E ρ hρ) h T
          * overlapMomentK (povmRecordLaw E ρ hρ) h S) ∧
    (∀ T : Fin r → Fin k → Fin n, familyInjective T → coincidenceFree T →
      overlapMomentK (povmRecordLaw E ρ hρ) h T = 0) ∧
    (∀ (t s : Fin k → Fin n), Function.Injective t → Function.Injective s →
      overlapMomentK (povmRecordLaw E ρ hρ) h (familyAppend (fun _ : Fin 1 => t) (fun _ : Fin 1 => s))
        = overlapCovarianceK (povmRecordLaw E ρ hρ) h t s) ∧
    (|(povmSampleLaw E ρ hρ).expect (fun ω : Fin n → O =>
        (povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h) ^ r)|
      ≤ centeredAbsMomentK (povmRecordLaw E ρ hρ) h r
          * (((r * k) * (r * k) * n ^ (r * k - 1) : ℕ) : ℝ)
          / (((distinctTupleCount n k : ℕ) : ℝ) ^ r)) ∧
    (∀ (s : ℕ), 0 < s → ∀ ε : ℝ, 0 < ε →
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n) (povmRecordLaw E ρ hρ)
          (fun ω : Fin n → O =>
            ε < |povmUStatisticK h ω - kernelMeanK (povmRecordLaw E ρ hρ) h|)
        ≤ centeredAbsMomentK (povmRecordLaw E ρ hρ) h (2 * s)
            * ((((2 * s) * k) * ((2 * s) * k) * n ^ ((2 * s) * k - 1) : ℕ) : ℝ)
            / (((distinctTupleCount n k : ℕ) : ℝ) ^ (2 * s) * ε ^ (2 * s))) := by
  have hb := frontier1 (povmRecordLaw E ρ hρ) hr hN h
  have hexpect : ∀ f : (Fin n → O) → ℝ,
      (povmSampleLaw E ρ hρ).expect f
        = ∑ ω : Fin n → O, (povmRecordLaw E ρ hρ).probOf ω * f ω := fun _ => rfl
  simp only [hexpect]
  exact hb

end Povm

end Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments
