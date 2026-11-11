/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ApproxPolynomialBlockSensitivityBeal

/-!
# Fourth-power comparison for exact query complexity

The Möbius coefficients of a Boolean function define its canonical multilinear polynomial and
the degree `mobiusDegree`, which is proved equal to `exactDegree`. Sensitive blocks yield a
small set hitting all maximum-degree monomials; restricting that set lowers the degree and
permits a recursive deterministic query-tree construction.

Combining this construction with the quadratic block-sensitivity bound gives deterministic query
complexity at most twice the fourth power of exact degree. The theorem `frontier1` also gives
the corresponding bound in `exactMinimum`, in the polynomial-method setting of [BealsEtAl2001].

## Main statements

* `mobiusDegree_eq_exactDegree`: Möbius degree equals exact polynomial degree.
* `exists_hitting`: maximum-degree monomials have a hitting set controlled by degree and block
  sensitivity.
* `exists_dec_tree`: a query tree is constructed with cost bounded by degree squared times block
  sensitivity.
* `frontier1`: the fourth-power bounds in exact degree and exact quantum query complexity.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison

open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs (exactMinimum minimum_degree_bounds)
open scoped Classical BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

variable {N : ℕ}

/-- The Boolean characteristic input of a finite set of coordinates. -/
def chiSet (T : Finset (Fin N)) : Fin N → Bool := fun i => i ∈ T

/-- The Boolean input that is false at every coordinate. -/
def zeroInput : Fin N → Bool := fun _ => false

/-- The characteristic input of the empty set is the all-false input. -/
@[simp] theorem chiSet_empty : chiSet (∅ : Finset (Fin N)) = zeroInput := by
  funext i; simp [chiSet, zeroInput]

/-- Embeds a Boolean value into the real numbers as zero or one. -/
def bval (b : Bool) : ℝ := if b then 1 else 0

/-- The real encoding of `true` is one. -/
@[simp] theorem bval_true : bval true = 1 := rfl

/-- The real encoding of `false` is zero. -/
@[simp] theorem bval_false : bval false = 0 := rfl

/-- Equality of real Boolean encodings implies equality of the Boolean values. -/
theorem bval_injective {a b : Bool} (h : bval a = bval b) : a = b := by
  cases a <;> cases b <;> simp_all [bval]

/-- Embeds a Boolean input into the real zero-one cube coordinatewise. -/
def cubePoint (x : Fin N → Bool) : Fin N → ℝ := fun i => if x i then 1 else 0

/-- The finite set of coordinates where a Boolean input is true. -/
def suppOf (x : Fin N → Bool) : Finset (Fin N) := Finset.univ.filter (fun i => x i = true)

/-- A coordinate belongs to the support of a Boolean input exactly when its value is true. -/
theorem mem_suppOf {x : Fin N → Bool} {i : Fin N} : i ∈ suppOf x ↔ x i = true := by
  simp [suppOf]

/-- The characteristic input of a Boolean input's support recovers that input. -/
theorem chiSet_suppOf (x : Fin N → Bool) : chiSet (suppOf x) = x := by
  funext i
  by_cases h : x i <;> simp [chiSet, mem_suppOf, h]

/-- Flipping a block of the all-false input gives the characteristic input of that block. -/
theorem flipBlock_zeroInput (B : Finset (Fin N)) :
    flipBlock zeroInput B = chiSet B := by
  funext i
  by_cases h : i ∈ B <;> simp [flipBlock, chiSet, zeroInput, h]

/-- A block whose flip changes the function value is nonempty. -/
theorem BlockSensitive_nonempty {f : (Fin N → Bool) → Bool} {x : Fin N → Bool}
    {B : Finset (Fin N)} (h : BlockSensitive f x B) : B.Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty.mp hne] at h
  exact h rfl

/-- The alternating sum over subsets is one for the empty set and zero otherwise. -/
theorem sum_pow_neg_one_powerset {α : Type} [DecidableEq α] (S : Finset α) :
    ∑ U ∈ S.powerset, (-1 : ℝ) ^ U.card = if S = ∅ then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      refine Finset.disjoint_right.mpr fun W hW hmem => ?_
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hW
      exact ha ((Finset.mem_powerset.mp hmem) (Finset.mem_insert_self a U))
    rw [Finset.powerset_insert, Finset.sum_union hdisj]
    have hinj : ∀ U ∈ s.powerset, ∀ V ∈ s.powerset,
        insert a U = insert a V → U = V := by
      intro U hU V hV heq
      have hmemU : a ∉ U := fun hc => ha ((Finset.mem_powerset.mp hU) hc)
      have hmemV : a ∉ V := fun hc => ha ((Finset.mem_powerset.mp hV) hc)
      ext i
      by_cases hia : i = a
      · subst hia
        exact ⟨fun hi => (hmemU hi).elim, fun hi => (hmemV hi).elim⟩
      · have hmem : i ∈ insert a U ↔ i ∈ insert a V := by rw [heq]
        simp only [Finset.mem_insert, hia, false_or] at hmem
        exact hmem
    have himg : ∑ W ∈ s.powerset.image (insert a), (-1 : ℝ) ^ W.card
        = -(∑ U ∈ s.powerset, (-1 : ℝ) ^ U.card) := by
      rw [Finset.sum_image hinj, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun U hU => ?_
      rw [Finset.card_insert_of_notMem (fun hc => ha ((Finset.mem_powerset.mp hU) hc)),
        pow_succ]
      ring
    rw [himg]
    have hne : insert a s ≠ ∅ := by simp
    rw [if_neg hne]
    ring

/-- For `T ⊆ U`, the alternating sum over subsets of `U` containing `T` is one exactly when `T =
U`. -/
theorem sum_sign_subset_eq {α : Type} [DecidableEq α] (T U : Finset α) (hTU : T ⊆ U) :
    ∑ S ∈ U.powerset, (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card else 0)
      = if T = U then 1 else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hsplit : ∀ {S : Finset α}, T ⊆ S → S = T ∪ (S \ T) := by
    intro S h
    ext i
    by_cases hi : i ∈ T
    · simp [hi, h hi]
    · simp [hi]
  have hnbij :
      ∑ S ∈ U.powerset.filter (fun S => T ⊆ S), (-1 : ℝ) ^ (S \ T).card
        = ∑ W ∈ (U \ T).powerset, (-1 : ℝ) ^ W.card := by
    refine Finset.sum_nbij (fun S => S \ T) (fun S hS => ?_) (fun S₁ hS₁ S₂ hS₂ hsub => ?_)
      (fun W hW => ?_) (fun S hS => ?_)
    · rcases Finset.mem_filter.mp hS with ⟨hpu, _⟩
      exact Finset.mem_powerset.mpr
        (Finset.sdiff_subset_sdiff (Finset.mem_powerset.mp hpu) (subset_rfl))
    · rcases Finset.mem_filter.mp hS₁ with ⟨_, hsub₁⟩
      rcases Finset.mem_filter.mp hS₂ with ⟨_, hsub₂⟩
      have hsub' : S₁ \ T = S₂ \ T := hsub
      rw [hsplit hsub₁, hsub', ← hsplit hsub₂]
    · refine ⟨T ∪ W, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.union_subset hTU
          ((Finset.mem_powerset.mp hW).trans (Finset.sdiff_subset))),
        Finset.subset_union_left⟩, ?_⟩
      ext i
      by_cases hit : i ∈ T
      · have hiW : i ∉ W := fun hw =>
          ((Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hW) hw)).2 hit).elim
        simp [Finset.mem_sdiff, Finset.mem_union, hit, hiW]
      · simp only [Finset.mem_sdiff, Finset.mem_union, hit, not_false_iff, false_or, and_true]
    · rfl
  rw [hnbij, sum_pow_neg_one_powerset]
  by_cases hTe : T = U
  · subst hTe
    simp
  · have hne : (U \ T) ≠ ∅ := by
      intro heq
      refine hTe (Finset.Subset.antisymm hTU ?_)
      intro i hi
      by_contra hc
      exact Finset.eq_empty_iff_forall_notMem.mp heq i (Finset.mem_sdiff.mpr ⟨hi, hc⟩)
    rw [if_neg hTe, if_neg hne]

/-- The Boolean-lattice Möbius coefficient obtained by alternating the real function values over
subsets of the given coordinate set. -/
def mobiusCoef (f : (Fin N → Bool) → Bool) (S : Finset (Fin N)) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * bval (f (chiSet T))

/-- The alternating sum weighted by complement cardinality is one for the empty set and zero
otherwise. -/
theorem sum_sign_powerset_self (S : Finset (Fin N)) :
    ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card = if S = ∅ then 1 else 0 := by
  classical
  have hnbij : ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card
      = ∑ W ∈ S.powerset, (-1 : ℝ) ^ W.card := by
    refine Finset.sum_nbij (fun T => S \ T) (fun T hT => ?_) (fun T₁ h₁ T₂ h₂ h => ?_)
      (fun W hW => ?_) (fun _ _ => ?_)
    · exact Finset.mem_powerset.mpr fun i hi => (Finset.mem_sdiff.mp hi).1
    · have h' : S \ T₁ = S \ T₂ := h
      ext i
      by_cases hi : i ∈ S
      · constructor
        · intro hm
          by_contra hc
          have h2 : i ∈ S \ T₂ := Finset.mem_sdiff.mpr ⟨hi, hc⟩
          have h1 : i ∈ S \ T₁ := h'.symm ▸ h2
          exact (Finset.mem_sdiff.mp h1).2 hm
        · intro hm
          by_contra hc
          have h1 : i ∈ S \ T₁ := Finset.mem_sdiff.mpr ⟨hi, hc⟩
          have h2 : i ∈ S \ T₂ := h' ▸ h1
          exact (Finset.mem_sdiff.mp h2).2 hm
      · have h1 : i ∉ T₁ := fun hc => hi ((Finset.mem_powerset.mp h₁) hc)
        have h2 : i ∉ T₂ := fun hc => hi ((Finset.mem_powerset.mp h₂) hc)
        exact ⟨fun hc => (h1 hc).elim, fun hc => (h2 hc).elim⟩
    · refine ⟨S \ W, Finset.mem_powerset.mpr
        (fun i hi => (Finset.mem_sdiff.mp hi).1), ?_⟩
      ext i
      by_cases hiW : i ∈ W
      · have hiS : i ∈ S := Finset.mem_powerset.mp hW hiW
        simp [hiW, hiS]
      · by_cases hiS : i ∈ S
        · simp [hiW, hiS]
        · simp [hiW, hiS]
    · rfl
  rw [hnbij, sum_pow_neg_one_powerset]

/-- A nonempty set has zero Möbius coefficient if the function is constant on all characteristic
inputs of its subsets. -/
theorem mobiusCoef_eq_zero_of_const {f : (Fin N → Bool) → Bool} {S : Finset (Fin N)}
    (hne : S.Nonempty) (hc : ∀ T ∈ S.powerset, f (chiSet T) = f zeroInput) :
    mobiusCoef f S = 0 := by
  classical
  have h1 : ∀ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * bval (f (chiSet T))
      = bval (f zeroInput) * (-1 : ℝ) ^ (S \ T).card := by
    intro T hT
    rw [hc T hT]
    ring
  rw [mobiusCoef, Finset.sum_congr rfl (fun T hT => h1 T hT), ← Finset.mul_sum,
    sum_sign_powerset_self, if_neg hne.ne_empty, mul_zero]

/-- Summing the Boolean-lattice Möbius transform over all subsets recovers the value at the full
set. -/
theorem moebius_inversion_sum {α : Type} [DecidableEq α] (U : Finset α) (F : Finset α → ℝ) :
    ∑ S ∈ U.powerset, ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * F T = F U := by
  classical
  have hinner : ∀ S ∈ U.powerset,
      (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * F T)
        = ∑ T ∈ U.powerset, (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card * F T else 0) := by
    intro S hS
    have h1 : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * F T)
        = ∑ T ∈ S.powerset, (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card * F T else 0) :=
      Finset.sum_congr rfl fun T hT => by rw [if_pos (Finset.mem_powerset.mp hT)]
    rw [h1]
    exact Finset.sum_subset
      (fun T hT => Finset.mem_powerset.mpr
        ((Finset.mem_powerset.mp hT).trans (Finset.mem_powerset.mp hS)))
      (fun T hT hnot => if_neg fun hsub => hnot (Finset.mem_powerset.mpr hsub))
  have hstep2 : ∀ T ∈ U.powerset,
      (∑ S ∈ U.powerset, (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card * F T else 0))
        = F T * (if T = U then 1 else 0) := by
    intro T hT
    have hmul : ∀ S ∈ U.powerset,
        (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card * F T else 0)
          = F T * (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card else 0) := by
      intro S _
      by_cases hc : T ⊆ S
      · rw [if_pos hc, if_pos hc, mul_comm]
      · rw [if_neg hc, if_neg hc, mul_zero]
    rw [Finset.sum_congr rfl (fun S hS => hmul S hS), ← Finset.mul_sum,
      sum_sign_subset_eq T U (Finset.mem_powerset.mp hT)]
  calc ∑ S ∈ U.powerset, ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * F T
      = ∑ S ∈ U.powerset, ∑ T ∈ U.powerset,
          (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card * F T else 0) :=
        Finset.sum_congr rfl fun S hS => hinner S hS
    _ = ∑ T ∈ U.powerset, ∑ S ∈ U.powerset,
          (if T ⊆ S then (-1 : ℝ) ^ (S \ T).card * F T else 0) :=
        Finset.sum_comm
    _ = ∑ T ∈ U.powerset, F T * (if T = U then 1 else 0) :=
        Finset.sum_congr rfl fun T hT => hstep2 T hT
    _ = F U := by
        rw [Finset.sum_eq_single_of_mem U (Finset.mem_powerset.mpr (subset_rfl))]
        · simp
        · intro T hT hne
          rw [if_neg hne, mul_zero]

/-- The squarefree monomial given by the product of variables indexed by a finite set. -/
def supMono (S : Finset (Fin N)) : MvPolynomial (Fin N) ℝ :=
  ∏ i ∈ S, MvPolynomial.X i

/-- Inserting a new coordinate into a squarefree monomial multiplies it by that coordinate's
variable. -/
theorem supMono_insert {S : Finset (Fin N)} {i : Fin N} (h : i ∉ S) :
    supMono (insert i S) = MvPolynomial.X i * supMono S := by
  simp only [supMono, Finset.prod_insert h]

/-- The total degree of the squarefree monomial is at most the cardinality of its index set. -/
theorem supMono_totalDegree (S : Finset (Fin N)) :
    (supMono S).totalDegree ≤ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [supMono]
  | insert a s ha ih =>
    rw [supMono_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := MvPolynomial.totalDegree_mul (MvPolynomial.X a) (supMono s)
    rw [MvPolynomial.totalDegree_X] at h1
    omega

/-- A squarefree monomial evaluates to one on a Boolean input exactly when every indexed
coordinate is true, and to zero otherwise. -/
theorem eval_supMono (S : Finset (Fin N)) (x : Fin N → Bool) :
    MvPolynomial.eval (cubePoint x) (supMono S) = if S ⊆ suppOf x then (1 : ℝ) else 0 := by
  classical
  rw [supMono, MvPolynomial.eval_prod]
  by_cases hd : S ⊆ suppOf x
  · rw [if_pos hd]
    refine Finset.prod_eq_one fun i hi => ?_
    have hx : x i = true := mem_suppOf.mp (hd hi)
    simp only [MvPolynomial.eval_X, cubePoint, if_pos hx]
  · rw [if_neg hd]
    have hex : ∃ i, i ∈ S ∧ ¬(i ∈ suppOf x) := by
      by_contra hcon
      push Not at hcon
      exact hd hcon
    obtain ⟨i, hi⟩ := hex
    refine Finset.prod_eq_zero hi.1 ?_
    have hx : ¬ (x i = true) := fun h => hi.2 (mem_suppOf.mpr h)
    simp only [MvPolynomial.eval_X, cubePoint, if_neg hx]

/-- The canonical multilinear polynomial formed from the Boolean function's Möbius coefficients. -/
def canonPoly (f : (Fin N → Bool) → Bool) : MvPolynomial (Fin N) ℝ :=
  ∑ S ∈ Finset.univ.powerset, MvPolynomial.C (mobiusCoef f S) * supMono S

/-- Evaluating the canonical polynomial on a Boolean input sums the Möbius coefficients over
subsets of its support. -/
theorem eval_canonPoly_sum (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    MvPolynomial.eval (cubePoint x) (canonPoly f)
      = ∑ S ∈ (suppOf x).powerset, mobiusCoef f S := by
  classical
  rw [canonPoly, MvPolynomial.eval_sum]
  have hinner : ∀ S ∈ Finset.univ.powerset,
      MvPolynomial.eval (cubePoint x) (MvPolynomial.C (mobiusCoef f S) * supMono S)
        = (if S ⊆ suppOf x then mobiusCoef f S else 0) := by
    intro S _
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_supMono]
    by_cases h : S ⊆ suppOf x <;> simp [h]
  rw [Finset.sum_congr rfl fun S hS => hinner S hS]
  have hset : (suppOf x).powerset = Finset.univ.powerset.filter (fun S => S ⊆ suppOf x) := by
    ext S
    simp only [Finset.mem_powerset, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.subset_univ S, h⟩, fun h => h.2⟩
  rw [hset, Finset.sum_filter]

/-- The canonical polynomial represents the Boolean function exactly on the Boolean cube. -/
theorem canonPoly_represents (f : (Fin N → Bool) → Bool) (g : Fin N → Bool) :
    boolEval (canonPoly f) g = if f g then (1 : ℝ) else 0 := by
  have h1 : MvPolynomial.eval (cubePoint g) (canonPoly f)
      = ∑ S ∈ (suppOf g).powerset, mobiusCoef f S := eval_canonPoly_sum f g
  have h2 : ∑ S ∈ (suppOf g).powerset, mobiusCoef f S = bval (f g) := by
    have hinv := moebius_inversion_sum (suppOf g) (fun T => bval (f (chiSet T)))
    rw [chiSet_suppOf g] at hinv
    exact hinv
  unfold boolEval
  rw [show (fun i => if g i then (1 : ℝ) else 0) = cubePoint g from rfl, h1, h2]
  rfl

/-- The maximum cardinality of a coordinate set with nonzero Möbius coefficient, with value zero
when there are no such sets. -/
noncomputable def mobiusDegree (f : (Fin N → Bool) → Bool) : ℕ :=
  (Finset.univ.powerset.filter (fun S => mobiusCoef f S ≠ 0)).sup Finset.card

/-- A coordinate set with nonzero Möbius coefficient has cardinality at most the Möbius degree. -/
theorem card_le_mobiusDegree {f : (Fin N → Bool) → Bool} {S : Finset (Fin N)}
    (h : mobiusCoef f S ≠ 0) : S.card ≤ mobiusDegree f :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), h⟩)

/-- The canonical polynomial's total degree is at most the Möbius degree. -/
theorem totalDegree_canonPoly_le (f : (Fin N → Bool) → Bool) :
    (canonPoly f).totalDegree ≤ mobiusDegree f := by
  classical
  rw [canonPoly]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
  refine Finset.sup_le fun S hS => ?_
  by_cases hc : mobiusCoef f S = 0
  · have h0 : (MvPolynomial.C (mobiusCoef f S) * supMono S).totalDegree = 0 := by
      rw [hc, MvPolynomial.C_0, zero_mul, MvPolynomial.totalDegree_zero]
    omega
  · have hcm : (MvPolynomial.C (mobiusCoef f S) * supMono S).totalDegree
          ≤ (supMono S).totalDegree := by
      have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (mobiusCoef f S)) (supMono S)
      rw [MvPolynomial.totalDegree_C] at h
      omega
    have hmem : S ∈ Finset.univ.powerset.filter (fun S => mobiusCoef f S ≠ 0) :=
      Finset.mem_filter.mpr ⟨hS, hc⟩
    exact hcm.trans ((supMono_totalDegree S).trans (Finset.le_sup hmem))

/-- The finitely supported exponent vector taking value one on the given set and zero elsewhere. -/
def indExp (S : Finset (Fin N)) : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => if i ∈ S then 1 else 0)

/-- The indicator exponent vector is one on its defining set and zero outside it. -/
theorem indExp_apply (S : Finset (Fin N)) (i : Fin N) :
    indExp S i = if i ∈ S then 1 else 0 := by
  simp [indExp]

/-- The support of an indicator exponent vector is its defining set. -/
theorem indExp_support (S : Finset (Fin N)) : (indExp S).support = S := by
  ext i
  simp [indExp_apply]

/-- The sum of the indicator exponents equals the cardinality of the defining set. -/
theorem indExp_sum_card (S : Finset (Fin N)) : (indExp S).sum (fun _ e => e) = S.card := by
  classical
  have h1 : (indExp S).sum (fun _ e => e) = ∑ i : Fin N, (indExp S i) :=
    Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h2 : ∑ i : Fin N, (indExp S i) = S.card := by
    have hfilter : (Finset.univ.filter (fun i => i ∈ S) : Finset (Fin N)) = S := by
      ext i; simp
    simp_rw [indExp_apply]
    calc ∑ i : Fin N, (if i ∈ S then (1 : ℕ) else 0)
        = ∑ i ∈ (Finset.univ : Finset (Fin N)), (if i ∈ S then (1 : ℕ) else 0) := rfl
      _ = ∑ i ∈ (Finset.univ.filter (fun i => i ∈ S) : Finset (Fin N)), (1 : ℕ) := by
          rw [Finset.sum_filter]
      _ = S.card := by rw [hfilter, Finset.card_eq_sum_ones]
  rw [h1, h2]

/-- Every multilinear real polynomial representing the Boolean function has its coefficient at
`indExp S` equal to `mobiusCoef f S`. -/
theorem multilinear_coeff_eq_mobius (f : (Fin N → Bool) → Bool)
    (q : MvPolynomial (Fin N) ℝ)
    (hq : ∀ g : Fin N → Bool, MvPolynomial.eval (cubePoint g) q = bval (f g))
    (hml : ∀ d ∈ q.support, ∀ i, d i ≤ 1)
    (S : Finset (Fin N)) :
    q.coeff (indExp S) = mobiusCoef f S := by
  classical
  have hprod : ∀ (T : Finset (Fin N)) (d : Fin N →₀ ℕ),
      (∏ i, (cubePoint (chiSet T) i) ^ (d i))
        = if d.support ⊆ T then (1 : ℝ) else 0 := by
    intro T d
    by_cases hd : d.support ⊆ T
    · rw [if_pos hd, Finset.prod_eq_one]
      intro i _
      by_cases hid : d i = 0
      · rw [hid, pow_zero]
      · have hiT : i ∈ T := hd (Finsupp.mem_support_iff.mpr hid)
        have h1 : cubePoint (chiSet T) i = 1 := by
          simp only [cubePoint, chiSet]
          exact if_pos (decide_eq_true hiT)
        rw [h1, one_pow]
    · rw [if_neg hd]
      have hex : ∃ i, i ∈ d.support ∧ ¬(i ∈ T) := by
        by_contra hcon
        push Not at hcon
        exact hd hcon
      obtain ⟨i, hi⟩ := hex
      have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi.1
      have h0 : cubePoint (chiSet T) i = 0 := by simp [cubePoint, chiSet, hi.2]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [h0, zero_pow hne]
  have heval : ∀ T : Finset (Fin N),
      MvPolynomial.eval (cubePoint (chiSet T)) q
        = ∑ d ∈ q.support, q.coeff d * (if d.support ⊆ T then (1 : ℝ) else 0) := by
    intro T
    rw [MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hprod T d]
  have hinner : ∀ d : Fin N →₀ ℕ,
      (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * (if d.support ⊆ T then (1 : ℝ) else 0))
        = if d.support = S then (1 : ℝ) else 0 := by
    intro d
    by_cases hsub : d.support ⊆ S
    · have hterm : ∀ T ∈ S.powerset,
          (-1 : ℝ) ^ (S \ T).card * (if d.support ⊆ T then (1 : ℝ) else 0)
            = if d.support ⊆ T then (-1 : ℝ) ^ (S \ T).card else 0 := by
        intro T _; by_cases hc : d.support ⊆ T <;> simp [hc]
      have hsdiff : ∀ T ∈ S.powerset, S \ (S \ T) = T := by
        intro T hT
        ext i
        by_cases hi : i ∈ T
        · simp [hi, (Finset.mem_powerset.mp hT) hi]
        · by_cases his : i ∈ S
          · simp [hi, his]
          · simp [hi, his]
      have hreind : ∑ T ∈ S.powerset, (if d.support ⊆ T then (-1 : ℝ) ^ (S \ T).card else 0)
          = ∑ W ∈ (S \ d.support).powerset, (-1 : ℝ) ^ W.card := by
        rw [← Finset.sum_filter]
        refine Finset.sum_nbij (fun T => S \ T) (fun T hT => ?_) (fun T₁ h₁ T₂ h₂ h => ?_)
          (fun W hW => ?_) (fun T hT => ?_)
        · rcases Finset.mem_filter.mp hT with ⟨hpu, hsubT⟩
          refine Finset.mem_powerset.mpr fun i hi => ?_
          rcases Finset.mem_sdiff.mp hi with ⟨his, hit⟩
          exact Finset.mem_sdiff.mpr ⟨his, fun hsd => hit (hsubT hsd)⟩
        · have h' : S \ T₁ = S \ T₂ := h
          rcases Finset.mem_filter.mp h₁ with ⟨hpu₁, _⟩
          rcases Finset.mem_filter.mp h₂ with ⟨hpu₂, _⟩
          ext i
          constructor
          · intro hmem
            by_contra hc2
            have h1 : i ∈ S := (Finset.mem_powerset.mp hpu₁) hmem
            have h2 : i ∈ S \ T₂ := Finset.mem_sdiff.mpr ⟨h1, hc2⟩
            rw [← h'] at h2
            exact (Finset.mem_sdiff.mp h2).2 hmem
          · intro hmem
            by_contra hc1
            have h1 : i ∈ S := (Finset.mem_powerset.mp hpu₂) hmem
            have h2 : i ∈ S \ T₁ := Finset.mem_sdiff.mpr ⟨h1, hc1⟩
            rw [h'] at h2
            exact (Finset.mem_sdiff.mp h2).2 hmem
        · refine ⟨S \ W, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
              (fun i hi => (Finset.mem_sdiff.mp hi).1),
            fun i hi => Finset.mem_sdiff.mpr ⟨hsub hi, fun hw =>
              ((Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hW) hw)).2 hi).elim⟩⟩, ?_⟩
          show S \ (S \ W) = W
          rw [hsdiff W (Finset.mem_powerset.mpr
            ((Finset.mem_powerset.mp hW).trans fun i hi => (Finset.mem_sdiff.mp hi).1))]
        · rfl
      rw [Finset.sum_congr rfl (fun T hT => hterm T hT), hreind, sum_pow_neg_one_powerset]
      have hE : (S \ d.support = ∅) ↔ (d.support = S) := by
        constructor
        · intro heq
          refine Finset.Subset.antisymm hsub ?_
          intro i hi
          by_contra hni
          exact Finset.eq_empty_iff_forall_notMem.mp heq i (Finset.mem_sdiff.mpr ⟨hi, hni⟩)
        · intro heq
          rw [heq, Finset.sdiff_self]
      by_cases hempty : S \ d.support = ∅
      · rw [if_pos hempty, if_pos (hE.mp hempty)]
      · rw [if_neg hempty, if_neg (fun heq => hempty (hE.mpr heq))]
    · rw [if_neg (fun heq => hsub (by rw [heq]))]
      refine Finset.sum_eq_zero fun T hT => ?_
      have hc : ¬(d.support ⊆ T) := fun h => hsub (h.trans (Finset.mem_powerset.mp hT))
      rw [if_neg hc, mul_zero]
  have key : mobiusCoef f S
      = ∑ d ∈ q.support, q.coeff d * (if d.support = S then (1 : ℝ) else 0) := by
    unfold mobiusCoef
    have hstep1 : (∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card * bval (f (chiSet T)))
        = ∑ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card
            * ∑ d ∈ q.support, q.coeff d * (if d.support ⊆ T then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl fun T _ => by rw [(hq (chiSet T)).symm, heval T]
    rw [hstep1]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hpull : ∀ T ∈ S.powerset, (-1 : ℝ) ^ (S \ T).card
          * (q.coeff d * (if d.support ⊆ T then (1 : ℝ) else 0))
        = q.coeff d * ((-1 : ℝ) ^ (S \ T).card * (if d.support ⊆ T then (1 : ℝ) else 0)) := by
      intro T _; ring
    rw [Finset.sum_congr rfl (fun T hT => hpull T hT), ← Finset.mul_sum, hinner d]
  rw [key]
  have hmlind : ∀ d ∈ q.support, d.support = S → d = indExp S := by
    intro d hd hds
    refine Finsupp.ext fun i => ?_
    have hle := hml d hd i
    rw [indExp_apply]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      have hdi : d i ≠ 0 := by
        intro h0
        have hnotmem : i ∉ d.support := by
          rw [Finsupp.mem_support_iff, h0]; simp
        exact hnotmem (by rw [hds]; exact hi)
      omega
    · rw [if_neg hi]
      have hdi : d i = 0 := by
        by_contra h0
        have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr h0
        rw [hds] at hmem
        exact hi hmem
      exact hdi
  have h₀ : indExp S ∉ q.support →
      q.coeff (indExp S) * (if (indExp S).support = S then (1 : ℝ) else 0) = 0 := by
    intro hnot
    have hc0 : q.coeff (indExp S) = 0 := by
      by_contra hne
      exact hnot (MvPolynomial.mem_support_iff.mpr hne)
    rw [hc0, zero_mul]
  have h₁ : ∀ d ∈ q.support, d ≠ indExp S →
      q.coeff d * (if d.support = S then (1 : ℝ) else 0) = 0 := by
    intro d hd hne
    rw [if_neg (fun heq => hne (hmlind d hd heq)), mul_zero]
  rw [Finset.sum_eq_single (indExp S) h₁ h₀, indExp_support, if_pos rfl, mul_one]

/-- The Möbius degree is at most the exact polynomial degree. -/
theorem mobiusDegree_le_exactDegree (f : (Fin N → Bool) → Bool) :
    mobiusDegree f ≤ exactDegree f := by
  classical
  have key : ∀ p : MvPolynomial (Fin N) ℝ,
      (∀ g, boolEval p g = if f g then (1 : ℝ) else 0) → mobiusDegree f ≤ p.totalDegree := by
    intro p hp
    have hqrep : ∀ g : Fin N → Bool,
        MvPolynomial.eval (cubePoint g) (multilinearize p) = bval (f g) := by
      intro g
      rw [multilinearize_eval p (cubePoint g) (by intro i; cases g i <;> simp [cubePoint])]
      exact hp g
    have hmlq : ∀ d ∈ (multilinearize p).support, ∀ i, d i ≤ 1 := fun d hd i =>
      multilinearize_coeff_multilinear p d (MvPolynomial.mem_support_iff.mp hd) i
    rw [mobiusDegree]
    refine Finset.sup_le fun S hS => ?_
    rcases Finset.mem_filter.mp hS with ⟨_, hcoef⟩
    have hext := multilinear_coeff_eq_mobius f (multilinearize p) hqrep hmlq S
    rw [← hext] at hcoef
    have hmem : indExp S ∈ (multilinearize p).support := MvPolynomial.mem_support_iff.mpr hcoef
    have h1 : (indExp S).sum (fun _ e => e) ≤ (multilinearize p).totalDegree :=
      MvPolynomial.le_totalDegree hmem
    have h2 : (indExp S).sum (fun _ e => e) = S.card := indExp_sum_card S
    have h3 : (multilinearize p).totalDegree ≤ p.totalDegree := multilinearize_totalDegree_le p
    omega
  have hne : {p : MvPolynomial (Fin N) ℝ |
      ∀ g, boolEval p g = if f g then (1 : ℝ) else 0}.Nonempty :=
    ⟨canonPoly f, fun g => canonPoly_represents f g⟩
  have hfinal : ∀ d ∈ (fun p : MvPolynomial (Fin N) ℝ => p.totalDegree) ''
      {p | ∀ g, boolEval p g = if f g then (1 : ℝ) else 0}, mobiusDegree f ≤ d := by
    intro d hd
    obtain ⟨p, hpmem, hpd⟩ := hd
    have hpd' : p.totalDegree = d := hpd
    exact (key p hpmem).trans_eq hpd'
  exact hfinal _ (Nat.sInf_mem (hne.image fun p => p.totalDegree))

/-- The exact polynomial degree is at most the Möbius degree. -/
theorem exactDegree_le_mobiusDegree (f : (Fin N → Bool) → Bool) :
    exactDegree f ≤ mobiusDegree f := by
  have hrep : ∀ g, boolEval (canonPoly f) g = if f g then (1 : ℝ) else 0 :=
    fun g => canonPoly_represents f g
  have hmem : (canonPoly f).totalDegree ∈ (fun p : MvPolynomial (Fin N) ℝ => p.totalDegree) ''
      {p | ∀ g, boolEval p g = if f g then (1 : ℝ) else 0} :=
    ⟨canonPoly f, hrep, rfl⟩
  exact (Nat.sInf_le hmem).trans (totalDegree_canonPoly_le f)

/-- The Möbius degree equals the exact polynomial degree. -/
theorem mobiusDegree_eq_exactDegree (f : (Fin N → Bool) → Bool) :
    mobiusDegree f = exactDegree f :=
  le_antisymm (mobiusDegree_le_exactDegree f) (exactDegree_le_mobiusDegree f)

/-- A nonempty set with nonzero Möbius coefficient contains a block sensitive at the all-false
input. -/
theorem exists_sensitive_of_mobiusCoef {f : (Fin N → Bool) → Bool} {S : Finset (Fin N)}
    (h0 : mobiusCoef f S ≠ 0) (hne : S.Nonempty) :
    ∃ B ∈ S.powerset, BlockSensitive f zeroInput B := by
  classical
  by_contra hcon
  push Not at hcon
  refine h0 (mobiusCoef_eq_zero_of_const hne fun T hT => ?_)
  have hns := hcon T hT
  simp only [BlockSensitive, not_not] at hns
  rw [flipBlock_zeroInput T] at hns
  exact hns.symm

/-- A Boolean function of Möbius degree zero is constant. -/
theorem constant_of_mobiusDegree_zero {f : (Fin N → Bool) → Bool}
    (h : mobiusDegree f = 0) (x : Fin N → Bool) : f x = f zeroInput := by
  classical
  have hcoef : ∀ S, mobiusCoef f S ≠ 0 → S = ∅ := by
    intro S hS
    by_contra hne
    have h1 : 1 ≤ S.card := by
      by_contra hc
      exact hne (Finset.card_eq_zero.mp (by omega))
    have h2 : S.card ≤ mobiusDegree f := card_le_mobiusDegree hS
    omega
  have h1 : MvPolynomial.eval (cubePoint x) (canonPoly f) = mobiusCoef f ∅ := by
    rw [eval_canonPoly_sum,
      Finset.sum_eq_single_of_mem ∅ (Finset.mem_powerset.mpr (Finset.empty_subset _))]
    intro T _ hne
    by_contra hne0
    exact hne (hcoef T hne0)
  have h2 := canonPoly_represents f x
  have h3 : mobiusCoef f ∅ = bval (f zeroInput) := by
    rw [mobiusCoef]
    simp [chiSet_empty]
  unfold boolEval at h2
  rw [show (fun i => if x i then (1 : ℝ) else 0) = cubePoint x from rfl, h1, h3] at h2
  exact bval_injective h2.symm

/-- The coordinate sets of maximum cardinality among the nonzero Möbius coefficients. -/
def maxonomials (f : (Fin N → Bool) → Bool) : Finset (Finset (Fin N)) :=
  Finset.univ.powerset.filter fun S => mobiusCoef f S ≠ 0 ∧ S.card = mobiusDegree f

/-- Any finite family of maximum-degree monomials for a function of positive degree has a
pairwise disjoint family of sensitive blocks hitting every monomial. Each block lies in a
monomial of the family and has size at most the Möbius degree. -/
theorem greedy_blocks (f : (Fin N → Bool) → Bool) (hD : 1 ≤ mobiusDegree f) :
    ∀ k : ℕ, ∀ 𝓜 : Finset (Finset (Fin N)), 𝓜.card ≤ k → 𝓜 ⊆ maxonomials f →
      ∃ 𝔅 : Finset (Finset (Fin N)),
        (∀ B ∈ 𝔅, ∃ M ∈ 𝓜, B ⊆ M ∧ BlockSensitive f zeroInput B) ∧
        (∀ M ∈ 𝓜, ∃ B ∈ 𝔅, (M ∩ B).Nonempty) ∧
        (∀ B₁ ∈ 𝔅, ∀ B₂ ∈ 𝔅, B₁ ≠ B₂ → B₁ ∩ B₂ = ∅) ∧
        ∀ B ∈ 𝔅, B.card ≤ mobiusDegree f := by
  intro k
  induction k with
  | zero =>
    intro 𝓜 hcard hsub
    have hempty : 𝓜 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    subst hempty
    exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    intro 𝓜 hcard hsub
    by_cases hempty : 𝓜.Nonempty
    · obtain ⟨M₀, hM₀⟩ := hempty
      obtain ⟨hcoef, hcardM⟩ := (Finset.mem_filter.mp (hsub hM₀)).2
      have hM₀ne : M₀.Nonempty := Finset.card_pos.mp (by rw [hcardM]; omega)
      obtain ⟨B₀, hB₀pow, hB₀sens⟩ := exists_sensitive_of_mobiusCoef hcoef hM₀ne
      have hB₀sub : B₀ ⊆ M₀ := Finset.mem_powerset.mp hB₀pow
      have hB₀ne : B₀.Nonempty := BlockSensitive_nonempty hB₀sens
      have hB₀card : B₀.card ≤ mobiusDegree f :=
        (Finset.card_le_card hB₀sub).trans_eq hcardM
      have hintM₀ : M₀ ∩ B₀ = B₀ := Finset.inter_eq_right.mpr hB₀sub
      have hM₀not' : M₀ ∉ 𝓜.filter fun M => M ∩ B₀ = ∅ := by
        intro hmem
        have h1 : M₀ ∩ B₀ = ∅ := (Finset.mem_filter.mp hmem).2
        rw [hintM₀] at h1
        simp [h1] at hB₀ne
      have hlt : (𝓜.filter fun M => M ∩ B₀ = ∅).card < 𝓜.card :=
        Finset.card_lt_card
          ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨M₀, hM₀, hM₀not'⟩)
      obtain ⟨𝔅', hsub', hhit', hdisj', hcard'⟩ :=
        ih (𝓜.filter fun M => M ∩ B₀ = ∅) (by omega)
          (fun M hM => hsub (Finset.filter_subset _ _ hM))
      have hB₀not' : B₀ ∉ 𝔅' := by
        intro hmem
        obtain ⟨M, hMmem, hB₀M, -⟩ := hsub' B₀ hmem
        have h1 : M ∩ B₀ = ∅ := (Finset.mem_filter.mp hMmem).2
        have h2 : B₀ ⊆ M ∩ B₀ := by
          intro a ha
          rw [Finset.mem_inter]
          exact ⟨hB₀M ha, ha⟩
        have h3 : B₀ = ∅ := Finset.subset_empty.mp (by
          rw [← h1]
          exact h2)
        simp [h3] at hB₀ne
      have hpair : ∀ B ∈ insert B₀ 𝔅', B ≠ B₀ → B ∩ B₀ = ∅ := by
        intro B hB hne
        obtain ⟨M, hMmem, hBM, -⟩ := hsub' B
          ((Finset.mem_insert.mp hB).resolve_left (fun heq => hne heq))
        have h1 : M ∩ B₀ = ∅ := (Finset.mem_filter.mp hMmem).2
        have h2 : B ∩ B₀ ⊆ M ∩ B₀ := Finset.inter_subset_inter_right hBM
        rw [h1] at h2
        exact Finset.subset_empty.mp h2
      refine ⟨insert B₀ 𝔅', ?_, ?_, ?_, ?_⟩
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB'
        · exact ⟨M₀, hM₀, hB₀sub, hB₀sens⟩
        · obtain ⟨M, hM, hBM, hsens⟩ := hsub' B hB'
          exact ⟨M, Finset.filter_subset _ _ hM, hBM, hsens⟩
      · intro M hM
        by_cases hmb : M ∩ B₀ = ∅
        · obtain ⟨B, hB, hint⟩ := hhit' M (Finset.mem_filter.mpr ⟨hM, hmb⟩)
          exact ⟨B, Finset.mem_insert.mpr (Or.inr hB), hint⟩
        · exact ⟨B₀, Finset.mem_insert.mpr (Or.inl rfl),
            Finset.nonempty_iff_ne_empty.mpr hmb⟩
      · intro B₁ h₁ B₂ h₂ hne
        by_cases h₁₀ : B₁ = B₀
        · by_cases h₂₀ : B₂ = B₀
          · exact absurd (h₁₀.trans h₂₀.symm) hne
          · subst h₁₀
            rw [Finset.inter_comm]
            exact hpair B₂ h₂ (Ne.symm hne)
        · by_cases h₂₀ : B₂ = B₀
          · subst h₂₀
            exact hpair B₁ h₁ hne
          · exact hdisj' B₁ ((Finset.mem_insert.mp h₁).resolve_left h₁₀)
              B₂ ((Finset.mem_insert.mp h₂).resolve_left h₂₀) hne
      · intro B hB
        rcases Finset.mem_insert.mp hB with rfl | hB'
        · exact hB₀card
        · exact hcard' B hB'
    · have hempty' : 𝓜 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      subst hempty'
      exact ⟨∅, by simp, by simp, by simp, by simp⟩

/-- For positive Möbius degree, there is a set hitting every maximum-degree monomial whose size
is at most the degree times the block sensitivity. -/
theorem exists_hitting {f : (Fin N → Bool) → Bool} (hD : 1 ≤ mobiusDegree f) :
    ∃ H : Finset (Fin N),
      (∀ M ∈ maxonomials f, (M ∩ H).Nonempty) ∧
      H.card ≤ mobiusDegree f * blockSensitivity f := by
  classical
  obtain ⟨𝔅, hsub, hhit, hdisj, hcardB⟩ :=
    greedy_blocks f hD (maxonomials f).card (maxonomials f) le_rfl (fun M hM => hM)
  have h𝔅bs : 𝔅.card ≤ blockSensitivityAt f zeroInput := by
    rw [blockSensitivityAt]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ 𝔅,
      ⟨fun B hB => (hsub B hB).elim fun _ hM => hM.2.2, hdisj⟩⟩)
  have hbsat : blockSensitivityAt f zeroInput ≤ blockSensitivity f := by
    have hmem : blockSensitivityAt f zeroInput ∈
        (Finset.univ.image fun x : Fin N → Bool => blockSensitivityAt f x) :=
      Finset.mem_image.mpr ⟨zeroInput, Finset.mem_univ _, rfl⟩
    have h5 : blockSensitivityAt f zeroInput ≤
        (Finset.univ.image fun x : Fin N → Bool => blockSensitivityAt f x).sup id :=
      Finset.le_sup (f := id) hmem
    rw [blockSensitivity]
    exact h5
  refine ⟨𝔅.biUnion id, fun M hM => ?_, ?_⟩
  · obtain ⟨B, hB, hint⟩ := hhit M hM
    exact Finset.Nonempty.mono
      (Finset.inter_subset_inter_left (Finset.subset_biUnion_of_mem id hB)) hint
  · calc (𝔅.biUnion id).card ≤ ∑ B ∈ 𝔅, B.card := Finset.card_biUnion_le
      _ ≤ ∑ B ∈ 𝔅, mobiusDegree f := Finset.sum_le_sum fun B hB => hcardB B hB
      _ = 𝔅.card * mobiusDegree f := by rw [Finset.sum_const]; simp
      _ ≤ blockSensitivityAt f zeroInput * mobiusDegree f :=
          Nat.mul_le_mul_right _ h𝔅bs
      _ ≤ blockSensitivity f * mobiusDegree f := Nat.mul_le_mul_right _ hbsat
      _ = mobiusDegree f * blockSensitivity f := Nat.mul_comm _ _

/-- The input taking values from `a` on `H` and from `y` outside `H`. -/
def combine (H : Finset (Fin N)) (a y : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ H then a i else y i

/-- Flipping coordinates before fixing those in `H` is equivalent to flipping only the
coordinates outside `H` afterward. -/
theorem combine_flipBlock (H : Finset (Fin N)) (a y : Fin N → Bool) (B : Finset (Fin N)) :
    combine H a (flipBlock y B) = flipBlock (combine H a y) (B \ H) := by
  funext i
  by_cases hiH : i ∈ H
  · simp [combine, flipBlock, hiH]
  · by_cases hiB : i ∈ B
    · simp [combine, flipBlock, hiH, hiB]
    · simp [combine, flipBlock, hiH, hiB]

/-- The combined input agrees with `a` on `H`. -/
theorem combine_at (H : Finset (Fin N)) (a y : Fin N → Bool) {i : Fin N} (hi : i ∈ H) :
    combine H a y i = a i := by
  simp [combine, hi]

/-- The combined input agrees with `y` outside `H`. -/
theorem combine_out (H : Finset (Fin N)) (a y : Fin N → Bool) {i : Fin N} (hi : i ∉ H) :
    combine H a y i = y i := by
  simp [combine, hi]

/-- Block sensitivity at any input is at most the global block sensitivity. -/
theorem blockSensitivityAt_le (f : (Fin N → Bool) → Bool) (x : Fin N → Bool) :
    blockSensitivityAt f x ≤ blockSensitivity f := by
  have hmem : blockSensitivityAt f x ∈
      (Finset.univ.image fun y : Fin N → Bool => blockSensitivityAt f y) :=
    Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have h5 : blockSensitivityAt f x ≤
      (Finset.univ.image fun y : Fin N → Bool => blockSensitivityAt f y).sup id :=
    Finset.le_sup (f := id) hmem
  rw [blockSensitivity]
  exact h5

/-- Fixing coordinates does not increase block sensitivity at the corresponding input. -/
theorem blockSensitivityAt_combine_le (f : (Fin N → Bool) → Bool)
    (H : Finset (Fin N)) (a y : Fin N → Bool) :
    blockSensitivityAt (fun y' => f (combine H a y')) y
      ≤ blockSensitivityAt f (combine H a y) := by
  classical
  rw [blockSensitivityAt]
  refine Finset.sup_le fun 𝔅 h𝔅 => ?_
  obtain ⟨hsens, hdisj⟩ := (Finset.mem_filter.mp h𝔅).2
  have hmap : ∀ B ∈ 𝔅, (B \ H).Nonempty ∧ BlockSensitive f (combine H a y) (B \ H) := by
    intro B hB
    have hs' : f (combine H a y) ≠ f (combine H a (flipBlock y B)) := hsens B hB
    rw [combine_flipBlock] at hs'
    refine ⟨?_, hs'⟩
    by_contra hempty
    have heq : B \ H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [heq] at hs'
    simp at hs'
  have hinj : Set.InjOn (fun B : Finset (Fin N) => B \ H) (𝔅 : Set (Finset (Fin N))) := by
    intro B₁ h₁ B₂ h₂ heq
    by_contra hneB
    have hdis : B₁ ∩ B₂ = ∅ := hdisj B₁ h₁ B₂ h₂ hneB
    obtain ⟨i, hi⟩ := (hmap B₁ h₁).1
    have hi' : i ∈ B₂ \ H := by
      have heq' : B₁ \ H = B₂ \ H := heq
      rw [← heq']
      exact hi
    have hmem' : i ∈ B₁ ∩ B₂ :=
      Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi').1⟩
    rw [hdis] at hmem'
    simp at hmem'
  have himg : (𝔅.image fun B => B \ H).card = 𝔅.card :=
    Finset.card_image_of_injOn hinj
  rw [← himg]
  refine Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩)
  · intro B' hB'
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hB'
    exact (hmap B hB).2
  · intro B₁' h₁' B₂' h₂' hne'
    obtain ⟨B₁, h₁, rfl⟩ := Finset.mem_image.mp h₁'
    obtain ⟨B₂, h₂, rfl⟩ := Finset.mem_image.mp h₂'
    have hneB : B₁ ≠ B₂ := fun heq => hne' (by rw [heq])
    have hsub : (B₁ \ H) ∩ (B₂ \ H) ⊆ B₁ ∩ B₂ := by
      intro i hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).2).1⟩
    have hempty : B₁ ∩ B₂ = ∅ := hdisj B₁ h₁ B₂ h₂ hneB
    exact Finset.subset_empty.mp fun x hx => hempty ▸ hsub hx

/-- Fixing coordinates does not increase global block sensitivity. -/
theorem blockSensitivity_combine_le (f : (Fin N → Bool) → Bool)
    (H : Finset (Fin N)) (a : Fin N → Bool) :
    blockSensitivity (fun y' => f (combine H a y')) ≤ blockSensitivity f := by
  rw [blockSensitivity]
  refine Finset.sup_le fun b hb => ?_
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hb
  exact (blockSensitivityAt_combine_le f H a y).trans (blockSensitivityAt_le f (combine H a y))

/-- The Möbius degree is at most the total degree of any real polynomial representing the
Boolean function. -/
theorem mobiusDegree_le_rep (f : (Fin N → Bool) → Bool) (p : MvPolynomial (Fin N) ℝ)
    (hp : ∀ g, boolEval p g = if f g then (1 : ℝ) else 0) :
    mobiusDegree f ≤ p.totalDegree := by
  classical
  have hqrep : ∀ g : Fin N → Bool,
      MvPolynomial.eval (cubePoint g) (multilinearize p) = bval (f g) := by
    intro g
    rw [multilinearize_eval p (cubePoint g) (by intro i; cases g i <;> simp [cubePoint])]
    exact hp g
  have hmlq : ∀ d ∈ (multilinearize p).support, ∀ i, d i ≤ 1 := fun d hd i =>
    multilinearize_coeff_multilinear p d (MvPolynomial.mem_support_iff.mp hd) i
  rw [mobiusDegree]
  refine Finset.sup_le fun S hS => ?_
  rcases Finset.mem_filter.mp hS with ⟨_, hcoef⟩
  have hext := multilinear_coeff_eq_mobius f (multilinearize p) hqrep hmlq S
  rw [← hext] at hcoef
  have hmem : indExp S ∈ (multilinearize p).support := MvPolynomial.mem_support_iff.mpr hcoef
  have h1 : (indExp S).sum (fun _ e => e) ≤ (multilinearize p).totalDegree :=
    MvPolynomial.le_totalDegree hmem
  have h2 : (indExp S).sum (fun _ e => e) = S.card := indExp_sum_card S
  have h3 : (multilinearize p).totalDegree ≤ p.totalDegree := multilinearize_totalDegree_le p
  omega

/-- Fixing a set of coordinates hitting every maximum-degree monomial strictly lowers a positive
Möbius degree. -/
theorem mobiusDegree_restrict_lt (f : (Fin N → Bool) → Bool)
    (H : Finset (Fin N)) (a : Fin N → Bool)
    (hhit : ∀ M ∈ maxonomials f, (M ∩ H).Nonempty) (hD : 1 ≤ mobiusDegree f) :
    mobiusDegree (fun y => f (combine H a y)) < mobiusDegree f := by
  classical
  have hex : ∃ q : MvPolynomial (Fin N) ℝ,
      (∀ y, MvPolynomial.eval (cubePoint y) q = bval (f (combine H a y))) ∧
      q.totalDegree ≤ mobiusDegree f - 1 := by
    refine ⟨∑ S ∈ Finset.univ.powerset.filter
        fun S => mobiusCoef f S ≠ 0 ∧ ∀ i ∈ S ∩ H, a i,
        MvPolynomial.C (mobiusCoef f S *
          (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0)) * supMono (S \ H), ?_, ?_⟩
    · intro y
      rw [MvPolynomial.eval_sum]
      have hstep : ∀ S ∈ Finset.univ.powerset.filter
          (fun S => mobiusCoef f S ≠ 0 ∧ ∀ i ∈ S ∩ H, a i),
          MvPolynomial.eval (cubePoint y)
            (MvPolynomial.C (mobiusCoef f S * (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0))
              * supMono (S \ H))
          = mobiusCoef f S * (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0)
            * (if S \ H ⊆ suppOf y then (1 : ℝ) else 0) := by
        intro S _
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, eval_supMono]
      rw [Finset.sum_congr rfl hstep]
      have hneg : ∀ S : Finset (Fin N), ¬(∀ i ∈ S ∩ H, a i) →
          ¬(S ⊆ suppOf (combine H a y)) := by
        intro S hall hsub
        obtain ⟨i, hi⟩ := not_forall.mp hall
        push Not at hi
        obtain ⟨hiSI, hia⟩ := hi
        have hx := mem_suppOf.mp (hsub (Finset.mem_inter.mp hiSI).1)
        rw [combine_at H a y (Finset.mem_inter.mp hiSI).2] at hx
        exact hia hx
      have hkey : ∀ S : Finset (Fin N),
          (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0)
            * (if S \ H ⊆ suppOf y then (1 : ℝ) else 0)
            = if S ⊆ suppOf (combine H a y) then (1 : ℝ) else 0 := by
        intro S
        by_cases h1 : ∀ i ∈ S ∩ H, a i
        · by_cases h2 : S \ H ⊆ suppOf y
          · have hsub : S ⊆ suppOf (combine H a y) := by
              intro i hi
              refine mem_suppOf.mpr ?_
              by_cases hiH : i ∈ H
              · rw [combine_at H a y hiH]
                exact h1 i (Finset.mem_inter.mpr ⟨hi, hiH⟩)
              · rw [combine_out H a y hiH]
                exact mem_suppOf.mp (h2 (Finset.mem_sdiff.mpr ⟨hi, hiH⟩))
            rw [if_pos h1, if_pos h2, if_pos hsub, mul_one]
          · have hns : ¬(S ⊆ suppOf (combine H a y)) := by
              intro hsub
              refine h2 ?_
              intro i hi
              have hx : combine H a y i = true :=
                mem_suppOf.mp (hsub (Finset.mem_sdiff.mp hi).1)
              rw [combine_out H a y (Finset.mem_sdiff.mp hi).2] at hx
              exact mem_suppOf.mpr hx
            rw [if_pos h1, if_neg h2, if_neg hns, mul_zero]
        · rw [if_neg h1, zero_mul, if_neg (hneg S h1)]
      have hstep2 : ∀ S ∈ Finset.univ.powerset.filter
          (fun S => mobiusCoef f S ≠ 0 ∧ ∀ i ∈ S ∩ H, a i),
          mobiusCoef f S * (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0)
            * (if S \ H ⊆ suppOf y then (1 : ℝ) else 0)
          = mobiusCoef f S * (if S ⊆ suppOf (combine H a y) then (1 : ℝ) else 0) := by
        intro S _
        rw [mul_assoc, hkey S]
      rw [Finset.sum_congr rfl hstep2]
      have hcond : ∀ S ∈ Finset.univ.powerset,
          mobiusCoef f S * (if S ⊆ suppOf (combine H a y) then (1 : ℝ) else 0)
          = (if S ⊆ suppOf (combine H a y) then mobiusCoef f S else 0) := by
        intro S _
        by_cases h : S ⊆ suppOf (combine H a y) <;> simp [h]
      rw [Finset.sum_congr rfl (fun S hS => hcond S (Finset.mem_filter.mp hS).1)]
      have hext : (∑ S ∈ Finset.univ.powerset.filter
          (fun S => mobiusCoef f S ≠ 0 ∧ ∀ i ∈ S ∩ H, a i),
          (if S ⊆ suppOf (combine H a y) then mobiusCoef f S else 0))
          = ∑ S ∈ Finset.univ.powerset,
            (if S ⊆ suppOf (combine H a y) then mobiusCoef f S else 0) := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro S hS hne
        by_cases hsub : S ⊆ suppOf (combine H a y)
        · rw [if_pos hsub]
          rcases not_and_or.mp
            (fun hp => hne (Finset.mem_filter.mpr ⟨hS, hp⟩)) with hc | hc
          · exact not_not.mp hc
          · exact absurd hsub (hneg S hc)
        · rw [if_neg hsub]
      have hset : (suppOf (combine H a y)).powerset =
          Finset.univ.powerset.filter (fun S => S ⊆ suppOf (combine H a y)) := by
        ext S
        simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨fun h => ⟨Finset.subset_univ S, h⟩, fun h => h.2⟩
      refine hext.trans ?_
      calc ∑ S ∈ Finset.univ.powerset,
            (if S ⊆ suppOf (combine H a y) then mobiusCoef f S else 0)
          = MvPolynomial.eval (cubePoint (combine H a y)) (canonPoly f) := by
              rw [eval_canonPoly_sum f (combine H a y), hset, Finset.sum_filter]
        _ = bval (f (combine H a y)) := canonPoly_represents f (combine H a y)
    · refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
      refine Finset.sup_le fun S hS => ?_
      obtain ⟨-, ⟨hcoef, -⟩⟩ := Finset.mem_filter.mp hS
      have hcardS : S.card ≤ mobiusDegree f := card_le_mobiusDegree hcoef
      have hsd : (S \ H).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
      have hle : (S \ H).card ≤ mobiusDegree f - 1 := by
        by_cases heq : S.card = mobiusDegree f
        · have hmax : S ∈ maxonomials f :=
            Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hS).1, ⟨hcoef, heq⟩⟩
          obtain ⟨i, hi⟩ := hhit S hmax
          have hlt : (S \ H).card < S.card :=
            Finset.card_lt_card
              ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
                ⟨i, (Finset.mem_inter.mp hi).1, fun hmem =>
                  (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hi).2⟩)
          omega
        · omega
      calc (MvPolynomial.C (mobiusCoef f S * (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0))
            * supMono (S \ H)).totalDegree ≤ (supMono (S \ H)).totalDegree := by
            have h := MvPolynomial.totalDegree_mul
              (MvPolynomial.C (mobiusCoef f S * (if ∀ i ∈ S ∩ H, a i then (1 : ℝ) else 0)))
              (supMono (S \ H))
            rw [MvPolynomial.totalDegree_C] at h
            omega
        _ ≤ (S \ H).card := supMono_totalDegree _
        _ ≤ mobiusDegree f - 1 := hle
  obtain ⟨q, hrep, hdeg⟩ := hex
  have h1 := mobiusDegree_le_rep (fun y => f (combine H a y)) q (by
    intro g
    exact hrep g)
  omega

/-- Block sensitivity is at most twice the square of the exact polynomial degree. -/
theorem blockSensitivity_le_two_mul_exactDegree_sq (f : (Fin N → Bool) → Bool) :
    blockSensitivity f ≤ 2 * exactDegree f ^ 2 := by
  have hpoly : ∀ x : Fin N → Bool,
      0 ≤ MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (canonPoly f) ∧
        MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (canonPoly f) ≤ 1 ∧
        |MvPolynomial.eval (fun i => if x i then (1 : ℝ) else 0) (canonPoly f)
          - (if f x then (1 : ℝ) else 0)| ≤ 0 := by
    intro x
    have hv := canonPoly_represents f x
    show (0 : ℝ) ≤ boolEval (canonPoly f) x ∧ boolEval (canonPoly f) x ≤ 1 ∧
      |boolEval (canonPoly f) x - (if f x then (1 : ℝ) else 0)| ≤ 0
    rw [hv]
    cases hx : f x <;> simp
  have h := approximatePolynomialBlockSensitivity N f (canonPoly f) 0
    (by norm_num) (by norm_num) hpoly
  simp only [mul_zero, sub_zero, one_mul] at h
  have htd' : (canonPoly f).totalDegree ≤ exactDegree f :=
    (totalDegree_canonPoly_le f).trans_eq (mobiusDegree_eq_exactDegree f)
  have hn : (canonPoly f).totalDegree ^ 2 ≤ exactDegree f ^ 2 := by
    gcongr
  have hn2 : (2 : ℕ) * (canonPoly f).totalDegree ^ 2 ≤ 2 * exactDegree f ^ 2 :=
    Nat.mul_le_mul_left _ hn
  refine Nat.cast_le.mp (h.trans ?_)
  have hp2 : (2 : ℝ) * (((canonPoly f).totalDegree : ℕ) : ℝ) ^ 2
      ≤ ((2 * exactDegree f ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hn2
  linarith

/-- Replaces the coordinates listed by their values in `x`, retaining the initial assignment at
all other coordinates. -/
def extendPartial (x : Fin N → Bool) :
    List (Fin N) → (Fin N → Bool) → (Fin N → Bool)
  | [], p0 => p0
  | i :: rest, p0 => extendPartial x rest (fun j => if j = i then x i else p0 j)

/-- Extending a partial assignment leaves coordinates outside the queried list unchanged. -/
theorem extendPartial_not_mem {x : Fin N → Bool} {j : Fin N} :
    ∀ (l : List (Fin N)) (p0 : Fin N → Bool), j ∉ l →
      extendPartial x l p0 j = p0 j := by
  intro l
  induction l with
  | nil => intro p0 _; rfl
  | cons i rest ih =>
      intro p0 hj
      by_cases hji : j = i
      · exact absurd (by simp [hji]) hj
      · have hmem : j ∉ rest := fun hm => hj (by simp [hm, hji])
        rw [extendPartial, ih _ hmem]
        simp [hji]

/-- Extending a partial assignment makes each coordinate in the queried list agree with `x`. -/
theorem extendPartial_agrees {x : Fin N → Bool} {j : Fin N} :
    ∀ (l : List (Fin N)) (p0 : Fin N → Bool), j ∈ l →
      extendPartial x l p0 j = x j := by
  intro l
  induction l with
  | nil => intro p0 hm; exact absurd hm (by simp)
  | cons i rest ih =>
      intro p0 hj
      by_cases hji : j = i
      · rw [extendPartial]
        by_cases hmem : j ∈ rest
        · exact ih _ hmem
        · rw [extendPartial_not_mem _ _ hmem]
          simp [hji]
      · rw [extendPartial]
        exact ih _ (by simp [hji] at hj; exact hj)

/-- Queries the listed coordinates in order, updates the partial assignment, and continues with
the tree selected by that assignment. -/
def queryChain (l : List (Fin N)) (p0 : Fin N → Bool)
    (next : (Fin N → Bool) → BoolQueryTree (Fin N) Bool) : BoolQueryTree (Fin N) Bool :=
  match l with
  | [] => next p0
  | i :: rest => BoolQueryTree.ask i
      (queryChain rest (fun j => if j = i then false else p0 j) next)
      (queryChain rest (fun j => if j = i then true else p0 j) next)

/-- Running a query chain has the same output as its continuation evaluated at the completed
partial assignment. -/
theorem queryChain_run (l : List (Fin N)) (p0 : Fin N → Bool)
    (next : (Fin N → Bool) → BoolQueryTree (Fin N) Bool) (x : Fin N → Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (queryChain l p0 next)).1
      = (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (next (extendPartial x l p0))).1 := by
  induction l generalizing p0 with
  | nil => rfl
  | cons i rest ih =>
      simp only [queryChain, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run]
      split
      · next hx =>
        have hp : (fun j => if j = i then true else p0 j)
            = (fun j => if j = i then x i else p0 j) := by
          funext j; by_cases h : j = i <;> simp [h, hx]
        rw [hp]
        exact ih _
      · next hx =>
        have hp : (fun j => if j = i then false else p0 j)
            = (fun j => if j = i then x i else p0 j) := by
          funext j; by_cases h : j = i <;> simp [h, hx]
        rw [hp]
        exact ih _

/-- A query chain adds at most its list length to a uniform bound on the continuation's query
count. -/
theorem queryChain_maxQueries (l : List (Fin N)) (p0 : Fin N → Bool)
    (next : (Fin N → Bool) → BoolQueryTree (Fin N) Bool) (M : ℕ)
    (hM : ∀ a : Fin N → Bool, (next a).MaxQueries ≤ M) :
    (queryChain l p0 next).MaxQueries ≤ l.length + M := by
  induction l generalizing p0 with
  | nil => simpa using! hM p0
  | cons i rest ih =>
      simp only [queryChain, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries,
          List.length_cons]
      have h1 := ih (fun j => if j = i then false else p0 j)
      have h2 := ih (fun j => if j = i then true else p0 j)
      omega

/-- A Boolean function of Möbius degree at most `k` has a deterministic query tree computing it
with at most `k * (k * blockSensitivity f)` queries. -/
theorem exists_dec_tree : ∀ (k : ℕ) (f : (Fin N → Bool) → Bool), mobiusDegree f ≤ k →
    ∃ t : BoolQueryTree (Fin N) Bool,
      (∀ x : Fin N → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1 = f x) ∧
      t.MaxQueries ≤ k * (k * blockSensitivity f) := by
  intro k
  induction k with
  | zero =>
      intro f hk
      have h0 : mobiusDegree f = 0 := Nat.le_zero.mp hk
      refine ⟨BoolQueryTree.halt (f zeroInput), ?_, ?_⟩
      · intro x
        have hc := constant_of_mobiusDegree_zero h0 x
        simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hc]
      · simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | succ k ih =>
      intro f hk
      by_cases hd0 : mobiusDegree f ≤ k
      · obtain ⟨t, htrun, htmax⟩ := ih f hd0
        refine ⟨t, htrun, htmax.trans ?_⟩
        have hinner1 : k * blockSensitivity f ≤ (k + 1) * blockSensitivity f :=
          Nat.mul_le_mul (Nat.le_succ k) (le_refl _)
        exact Nat.mul_le_mul (Nat.le_succ k) hinner1
      · have hd1 : 1 ≤ mobiusDegree f := by omega
        obtain ⟨H, hhit, hHcard⟩ := exists_hitting hd1
        have hrest : ∀ a : Fin N → Bool, ∃ t : BoolQueryTree (Fin N) Bool,
            (∀ x : Fin N → Bool, (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x t).1 = f (combine H a x)) ∧
            t.MaxQueries ≤ k * (k * blockSensitivity f) := by
          intro a
          have hlt := mobiusDegree_restrict_lt f H a hhit hd1
          obtain ⟨t, htrun, htmax⟩ := ih (fun y => f (combine H a y)) (by omega)
          refine ⟨t, htrun, htmax.trans ?_⟩
          have hbs := blockSensitivity_combine_le f H a
          exact Nat.mul_le_mul (le_refl k) (Nat.mul_le_mul (le_refl k) hbs)
        choose t htval htmax using hrest
        refine ⟨queryChain H.toList (fun _ => false) t, ?_, ?_⟩
        · intro x
          have hrun := queryChain_run H.toList (fun _ => false) t x
          have hagrees : ∀ i ∈ H, (extendPartial x H.toList (fun _ => false)) i = x i :=
            fun i hi => extendPartial_agrees H.toList (fun _ => false) (Finset.mem_toList.mpr hi)
          rw [hrun, htval (extendPartial x H.toList (fun _ => false)) x]
          have hcomb : combine H (extendPartial x H.toList (fun _ => false)) x = x := by
            funext i
            by_cases hi : i ∈ H
            · rw [combine_at H _ x hi]
              exact hagrees i hi
            · rw [combine_out H _ x hi]
          rw [hcomb]
        · have hchain := queryChain_maxQueries H.toList (fun _ => false) t
            (k * (k * blockSensitivity f)) htmax
          have hlen : H.toList.length = H.card := by simp
          have hH' : H.card ≤ (k + 1) * blockSensitivity f := by
            have hm : mobiusDegree f = k + 1 := by omega
            rw [hm] at hHcard
            exact hHcard
          have hle : H.toList.length + k * (k * blockSensitivity f)
              ≤ (k + 1) * ((k + 1) * blockSensitivity f) := by
            have e : (k + 1) * ((k + 1) * blockSensitivity f)
                = k * (k * blockSensitivity f)
                  + ((k + 1) * blockSensitivity f + k * blockSensitivity f) := by
              ring
            rw [hlen, e]
            omega
          exact hchain.trans hle

/-- Deterministic query complexity is at most the square of the Möbius degree times block
sensitivity. -/
theorem deterministicQueryComplexity_le (f : (Fin N → Bool) → Bool) :
    deterministicQueryComplexity f
      ≤ mobiusDegree f * (mobiusDegree f * blockSensitivity f) := by
  obtain ⟨t, htrun, htmax⟩ := exists_dec_tree (mobiusDegree f) f le_rfl
  unfold deterministicQueryComplexity
  exact (Nat.sInf_le (Set.mem_range.mpr ⟨⟨t, fun x => htrun x⟩, rfl⟩)).trans htmax

/-- Deterministic query complexity is at most the square of the exact polynomial degree times
block sensitivity. -/
theorem deterministicQueryComplexity_le_mul (f : (Fin N → Bool) → Bool) :
    deterministicQueryComplexity f
      ≤ exactDegree f * (exactDegree f * blockSensitivity f) := by
  rw [← mobiusDegree_eq_exactDegree]
  exact deterministicQueryComplexity_le f

/-- Deterministic query complexity is at most twice the fourth power of exact polynomial degree. -/
theorem det_le_two_exactDegree_fourth (f : (Fin N → Bool) → Bool) :
    deterministicQueryComplexity f ≤ 2 * exactDegree f ^ 4 := by
  have h1 := deterministicQueryComplexity_le_mul f
  have h2 := blockSensitivity_le_two_mul_exactDegree_sq f
  have h3 : exactDegree f * (exactDegree f * blockSensitivity f)
      ≤ exactDegree f * (exactDegree f * (2 * exactDegree f ^ 2)) :=
    Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) h2)
  calc deterministicQueryComplexity f
      ≤ exactDegree f * (exactDegree f * blockSensitivity f) := h1
    _ ≤ exactDegree f * (exactDegree f * (2 * exactDegree f ^ 2)) := h3
    _ = 2 * exactDegree f ^ 4 := by ring

/-- Deterministic query complexity is at most `2 * exactDegree f ^ 4` and at most `32 *
exactMinimum f ^ 4`, giving the exact-query fourth-power comparison discussed in
[BealsEtAl2001]. -/
theorem frontier1 (f : (Fin N → Bool) → Bool) :
    deterministicQueryComplexity f ≤ 2 * exactDegree f ^ 4 ∧
      deterministicQueryComplexity f ≤ 32 * exactMinimum f ^ 4 := by
  refine ⟨det_le_two_exactDegree_fourth f, ?_⟩
  have hdeg := (minimum_degree_bounds f).1
  calc deterministicQueryComplexity f
      ≤ 2 * exactDegree f ^ 4 := det_le_two_exactDegree_fourth f
    _ ≤ 2 * (2 * exactMinimum f) ^ 4 := by
      gcongr
    _ = 32 * exactMinimum f ^ 4 := by ring

end
