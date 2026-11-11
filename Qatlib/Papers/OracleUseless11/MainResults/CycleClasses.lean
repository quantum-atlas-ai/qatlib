/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OracleUseless11.MainResults.OracleProblem
import Qatlib.Papers.OracleUseless11.MainResults.ClassicalTranscript
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Support

set_option backward.isDefEq.respectTransparency false

/-!
# The cycle-vs-involution oracle problem (paper §2.1, pp. 2–3)

Formal model for the separation of Harrow–Rosenbaum, *Uselessness for an Oracle Model
with Internal Randomness*, arXiv:1111.1462v2, §2.1.

The oracle is a permutation `π ∈ S_N`; the promise is that `π` is either

* an `N`-cycle (`CYC`), or
* a fixed-point-free involution (`INV`),

and the task is to decide which.  Theorems 1 and 2 of the paper say that no classical
algorithm can do this with unbounded error (any number of queries), while a single
quantum query suffices with one-sided error `1/2` (the swap-test computation, eq. (1)–(2)
on p. 3).

The key classical fact is that for a *uniformly random* permutation from either class,
the answer to a query `x` is uniform on `[N] ∖ {x}`.  This is proved here for an
arbitrary conjugacy class of `S_Y`: conjugation by the transposition `(z z')` gives a
bijection between the permutations of the class sending `x` to `z` and those sending
`x` to `z'`, so the two answer probabilities agree.
-/

namespace Qatlib.Papers.OracleUseless11.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open scoped BigOperators

set_option autoImplicit false

-- All class-level statements below are about finite cardinalities of subtypes of a
-- finite permutation group; we resolve the necessary decidability classically.
attribute [local instance] Classical.propDecidable

/-- `π` is an `N`-cycle: a single cycle moving every point (paper's class `CYC`). -/
def IsFullCycle {Y : Type*} [Fintype Y] [DecidableEq Y] (π : Equiv.Perm Y) : Prop :=
  π.IsCycle ∧ π.support = Finset.univ

/-- `π` is a fixed-point-free involution (paper's class `INV`). -/
def IsFixedPointFreeInvolution {Y : Type*} (π : Equiv.Perm Y) : Prop :=
  π * π = 1 ∧ ∀ x, π x ≠ x

/-- The transposition `(z z')` is an involution. -/
theorem swap_mul_self {Y : Type*} [DecidableEq Y] (z z' : Y) :
    Equiv.swap z z' * Equiv.swap z z' = 1 := by
  ext a
  rw [Equiv.Perm.mul_apply]
  rcases eq_or_ne a z with rfl | ha
  · rw [Equiv.swap_apply_left, Equiv.swap_apply_right]; rfl
  · rcases eq_or_ne a z' with rfl | ha'
    · rw [Equiv.swap_apply_right, Equiv.swap_apply_left]; rfl
    · rw [Equiv.swap_apply_of_ne_of_ne ha ha', Equiv.swap_apply_of_ne_of_ne ha ha']
      rfl

/-- **Uniformity on a conjugacy class.**  If `P` is invariant under conjugation and every
element of `P` moves `x`, then for the uniform distribution on the class `P` the answer
`π x` is equidistributed over all `z ≠ x`.

The bijection is conjugation by `(z z')`, which fixes `x` and sends `z ↦ z'`. -/
theorem card_class_answer_eq {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Equiv.Perm Y → Prop) (hP : ∀ (σ π : Equiv.Perm Y), P π ↔ P (σ * π * σ⁻¹))
    {x z z' : Y} (hz : z ≠ x) (hz' : z' ≠ x) :
    Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z}
      = Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z'} := by
  classical
  rcases eq_or_ne z z' with rfl | hzz'
  · rfl
  have hσ : (Equiv.swap z z')⁻¹ = Equiv.swap z z' :=
    inv_eq_of_mul_eq_one_right (swap_mul_self z z')
  -- conjugation is an involution on the subtype
  have hconj : ∀ (π : Equiv.Perm Y), (Equiv.swap z z') * ((Equiv.swap z z') * π *
      (Equiv.swap z z')⁻¹) * (Equiv.swap z z')⁻¹ = π := by
    intro π
    rw [hσ]
    calc Equiv.swap z z' * (Equiv.swap z z' * π * Equiv.swap z z') * Equiv.swap z z'
        = (Equiv.swap z z' * Equiv.swap z z') * π * (Equiv.swap z z' * Equiv.swap z z') := by
          group
      _ = π := by rw [swap_mul_self]; group
  have hval : ∀ π : Equiv.Perm Y, π x = z →
      ((Equiv.swap z z') * π * (Equiv.swap z z')⁻¹) x = z' := by
    intro π hπ
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hz.symm hz'.symm, hπ, Equiv.swap_apply_left]
  refine Fintype.card_congr ?_
  refine
    { toFun := fun π => ⟨Equiv.swap z z' * π.1 * (Equiv.swap z z')⁻¹,
        (hP _ _).mp π.2.1, hval π.1 π.2.2⟩
      invFun := fun π => ⟨Equiv.swap z z' * π.1 * (Equiv.swap z z')⁻¹,
        (hP _ _).mp π.2.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- the same map sends `z'` back to `z`
    rw [hσ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hz.symm hz'.symm, π.2.2, Equiv.swap_apply_right]
  · intro π
    exact Subtype.ext (hconj π.1)
  · intro π
    exact Subtype.ext (hconj π.1)

/-- The push-forward of the uniform law on a class `P` under `π ↦ π x`.
The class is assumed nonempty so that the normalising constant is nonzero. -/
noncomputable def classAnswerLaw {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Equiv.Perm Y → Prop) [Nonempty {π : Equiv.Perm Y // P π}] (x : Y) : FinDist Y where
  prob z :=
    (Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z} : ℝ) /
      (Fintype.card {π : Equiv.Perm Y // P π} : ℝ)
  nonneg z := by
    classical
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  sum_one := by
    classical
    have hclass_ne : (Fintype.card {π : Equiv.Perm Y // P π} : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero (α := {π : Equiv.Perm Y // P π}))
    have hfib : ∀ z : Y, Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z}
        = Fintype.card {π : {π : Equiv.Perm Y // P π} // π.1 x = z} := by
      intro z
      refine Fintype.card_congr ?_
      exact
        { toFun := fun π => ⟨⟨π.1, π.2.1⟩, π.2.2⟩
          invFun := fun π => ⟨π.1.1, π.1.2, π.2⟩
          left_inv := fun π => by rfl
          right_inv := fun π => by rfl }
    have hsum : ∑ z : Y, (Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z} : ℝ)
        = (Fintype.card {π : Equiv.Perm Y // P π} : ℝ) := by
      have h1 : ∑ z : Y, (Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z} : ℝ)
          = ∑ z : Y, (Fintype.card {π : {π : Equiv.Perm Y // P π} // π.1 x = z} : ℝ) :=
        Finset.sum_congr rfl (fun z _ => by rw [hfib z])
      rw [h1, ← Nat.cast_sum, ← Fintype.card_sigma]
      exact_mod_cast (Fintype.card_congr
        (Equiv.sigmaFiberEquiv (fun π : {π : Equiv.Perm Y // P π} => π.1 x)))
    rw [← Finset.sum_div, hsum, div_self hclass_ne]


/-! ## The uniform law on the off-diagonal -/

/-- Sum of `0` at `x` and a constant `c` elsewhere: `(|Y|-1) * c`. -/
theorem sum_ite_zero_offdiag {Y : Type*} [Fintype Y] [DecidableEq Y] (x : Y) (c : ℝ) :
    ∑ z : Y, (if z = x then (0 : ℝ) else c) = ((Fintype.card Y : ℝ) - 1) * c := by
  classical
  have h1 : 1 ≤ Fintype.card Y := by
    have := Fintype.card_pos_iff.mpr ⟨x⟩
    omega
  rw [← Finset.sum_erase_add (Finset.univ : Finset Y)
    (fun z => if z = x then (0 : ℝ) else c) (a := x) (Finset.mem_univ x)]
  have hx : (if x = x then (0 : ℝ) else c) = 0 := if_pos rfl
  rw [hx, add_zero]
  have hstep : ∑ z ∈ Finset.univ.erase x, (if z = x then (0 : ℝ) else c)
      = ∑ _z ∈ Finset.univ.erase x, c :=
    Finset.sum_congr rfl (fun z hz => by
      rw [if_neg (by simpa using (Finset.mem_erase.mp hz).1)])
  rw [hstep, Finset.sum_const, nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
  push_cast [h1]
  ring

/-- The uniform law on `Y ∖ {x}` (probability `1/(|Y|-1)` on every `z ≠ x`), the common
answer law of a uniformly random member of a conjugacy class of `S_Y` none of whose
elements fixes `x`.  Requires `|Y| ≥ 2`. -/
noncomputable def uniformOffDiag {Y : Type*} [Fintype Y] [DecidableEq Y]
    (hY : 2 ≤ Fintype.card Y) (x : Y) : FinDist Y where
  prob z := if z = x then 0 else 1 / ((Fintype.card Y : ℝ) - 1)
  nonneg z := by
    classical
    by_cases h : z = x
    · simp [h]
    · rw [if_neg h]
      refine div_nonneg zero_le_one ?_
      have : (2 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
      linarith
  sum_one := by
    classical
    have hne : (Fintype.card Y : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
      linarith
    rw [sum_ite_zero_offdiag x (1 / ((Fintype.card Y : ℝ) - 1))]
    field_simp

/-- **Off-diagonal value of a constant-on-fibres law.**  If `p` vanishes at `x` and is
constant `p z` on the whole off-diagonal `z' ≠ x`, then `p z = 1/(|Y|-1)`. -/
theorem prob_eq_inv_card_sub_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p : FinDist Y) (x : Y) (h0 : p.prob x = 0) (hY : 2 ≤ Fintype.card Y)
    {z : Y} (hz : z ≠ x) (hconst : ∀ z' : Y, z' ≠ x → p.prob z' = p.prob z) :
    p.prob z = 1 / ((Fintype.card Y : ℝ) - 1) := by
  classical
  have h1 : 1 ≤ Fintype.card Y := le_trans (by norm_num) hY
  have hne : (Fintype.card Y : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast hY
    linarith
  have htotal : ∑ z' : Y, p.prob z' = ((Fintype.card Y : ℝ) - 1) * p.prob z := by
    have hsum : ∑ z' : Y, p.prob z'
        = ∑ z' : Y, (if z' = x then (0 : ℝ) else p.prob z) := by
      refine Finset.sum_congr rfl (fun z' _ => ?_)
      by_cases hz' : z' = x
      · subst hz'
        simp [h0]
      · rw [if_neg hz', hconst z' hz']
    rw [hsum, sum_ite_zero_offdiag]
  rw [p.sum_one] at htotal
  rw [eq_div_iff hne, mul_comm]
  exact htotal.symm

/-- **Conjugacy classes have the uniform off-diagonal answer law.** -/
theorem classAnswerLaw_eq_uniformOffDiag {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Equiv.Perm Y → Prop) [Nonempty {π : Equiv.Perm Y // P π}]
    (hP : ∀ (σ π : Equiv.Perm Y), P π ↔ P (σ * π * σ⁻¹))
    (hfree : ∀ π : Equiv.Perm Y, P π → ∀ x, π x ≠ x)
    (hY : 2 ≤ Fintype.card Y) (x : Y) :
    classAnswerLaw P x = uniformOffDiag hY x := by
  classical
  refine FinDist.eq_of_prob_eq (fun z => ?_)
  by_cases hz : z = x
  · rw [hz]
    haveI : IsEmpty {π : Equiv.Perm Y // P π ∧ π x = x} :=
      ⟨fun π => hfree π.1 π.2.1 x π.2.2⟩
    simp [classAnswerLaw, uniformOffDiag]
  · have hconst : ∀ z' : Y, z' ≠ x →
        (classAnswerLaw P x).prob z' = (classAnswerLaw P x).prob z := by
      intro z' hz'
      show (Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z'} : ℝ) /
          (Fintype.card {π : Equiv.Perm Y // P π} : ℝ) =
        (Fintype.card {π : Equiv.Perm Y // P π ∧ π x = z} : ℝ) /
          (Fintype.card {π : Equiv.Perm Y // P π} : ℝ)
      rw [card_class_answer_eq P hP hz' hz]
    have hzero : (classAnswerLaw P x).prob x = 0 := by
      haveI : IsEmpty {π : Equiv.Perm Y // P π ∧ π x = x} :=
        ⟨fun π => hfree π.1 π.2.1 x π.2.2⟩
      simp [classAnswerLaw]
    rw [prob_eq_inv_card_sub_one (classAnswerLaw P x) x hzero hY hz hconst]
    simp [uniformOffDiag, hz]
