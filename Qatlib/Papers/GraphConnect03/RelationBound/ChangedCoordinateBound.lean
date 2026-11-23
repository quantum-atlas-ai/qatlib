/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.AmbainisMethod

@[expose] public section

/-!
# ChangedCoordinateBound — the changed-coordinate form of Theorem 3

[DurrMhallaLei2003], Theorem 3 and its uses in Theorems 4 and 5 (pp. 6–8).

Theorem 3 (Ambainis' relation method): for finite yes/no families `X, Y`
and a relation `R ⊆ X × Y` where every `x` is related to at least `m`
inputs `y`, every `y` to at least `m'` inputs `x`, and the product of the
two changed-coordinate loads at any coordinate is at most `l_max`, the
bounded-error query complexity is `Ω(√(m·m'/l_max))`.

Theorem 3 counts, at a related pair, neighbors that differ from the fixed
input: `l(x,i)` is the number of related `y'` with `y' i ≠ x i`, and
`l'(y,i)` is the number of related `x'` with `x' i ≠ y i`.  The library
field `l_spec` of
`Qatlib.Papers.GraphConnect03.MainResults.LowerBounds.AmbainisRelation`
instead filters `y' i ≠ y i` and
`x' i ≠ x i`.  On a Boolean coordinate where the related inputs differ,
those library factors are the neighbors that keep the fixed input's bit.
This file separates that unchanged-neighbor product from the source's
changed-coordinate loads, and proves the monotonicity and the matrix-model
evaluation of the adversary value `√(m·m'/l_max)` used by Theorems 4 and 5.
The abstract bounded-error adversary theorem itself is not rebuilt here.

## Main statements

* `ambainisRelation_unchangedLoad_le`: on a changed coordinate
  `x i ≠ y i`, `l_spec` bounds the product of the unchanged-neighbor counts
  `y' i = x i` and `x' i = y i`.
* `ambainisRelation_sourceChangedLoad_eq`: the source loads `y' i ≠ x i`
  and `x' i ≠ y i` are the complementary counts, equal to agreeing with the
  other input.
* `adversaryValue`: the real number `√(m·m'/l_max)`.
* `adversaryValue_mono`: the adversary value is monotone in the relation
  degrees and antitone in the load bound.
* `adversaryValue_matrix`: at the representative Theorem 5 scales
  `m = m' = n²`, `l_max = n`, the adversary value is `n·√n`.
* `adversaryValue_matrix_ge`: at those parameters the value is at least
  `n` for `n ≥ 1`, the first step of the `Ω(n^{3/2})` scale.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.GraphConnect03.RelationBound

open Classical
open Qatlib.Papers.GraphConnect03.MainResults.LowerBounds

attribute [local instance] Classical.propDecidable

/-- The adversary value `√(m·m'/l_max)` of Theorem 3, for natural relation
parameters. -/
def adversaryValue (m m' lmax : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * (m' : ℝ) / (lmax : ℝ))

/-- On a Boolean coordinate where `x` and `y` differ, the other bit is the
negation of the fixed bit.  Agreeing with `x` is then the same as differing
from `y`, and differing from `x` is the same as agreeing with `y`. -/
lemma bool_changedCoordinate_bit {a b : Bool} (h : a ≠ b) :
    (∀ z : Bool, z = a ↔ z ≠ b) ∧ (∀ z : Bool, z ≠ a ↔ z = b) := by
  have hb : b = !a := by
    rcases Bool.eq_or_eq_not b a with hba | hba
    · exact (h hba.symm).elim
    · exact hba
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [hb]
    exact Bool.ne_not.symm
  · rw [hb]
    exact Bool.eq_not_iff.symm

/-- At a changed coordinate `x i ≠ y i`, the `l_spec` field bounds the
unchanged-neighbor product: related `y'` that keep `x`'s bit, times related
`x'` that keep `y`'s bit.  Theorem 3's changed-coordinate loads are the
complementary counts `y' i ≠ x i` and `x' i ≠ y i`; this bound does not
apply to them. -/
theorem ambainisRelation_unchangedLoad_le {n : ℕ}
    (A : AmbainisRelation n) {x : Fin n → Bool} (hx : x ∈ A.X)
    {y : Fin n → Bool} (hy : y ∈ A.Y) (hR : A.R x y) {i : Fin n}
    (hi : x i ≠ y i) :
    (A.Y.filter (fun y' => A.R x y' ∧ y' i = x i)).card *
        (A.X.filter (fun x' => A.R x' y ∧ x' i = y i)).card ≤ A.lmax := by
  obtain ⟨hKeep, hChange⟩ := bool_changedCoordinate_bit hi
  have hY : A.Y.filter (fun y' => A.R x y' ∧ y' i = x i) =
      A.Y.filter (fun y' => A.R x y' ∧ y' i ≠ y i) := by
    refine Finset.filter_congr ?_
    intro y' _
    exact and_congr_right fun _ => hKeep (y' i)
  have hX : A.X.filter (fun x' => A.R x' y ∧ x' i = y i) =
      A.X.filter (fun x' => A.R x' y ∧ x' i ≠ x i) := by
    refine Finset.filter_congr ?_
    intro x' _
    exact and_congr_right fun _ => (hChange (x' i)).symm
  rw [hY, hX]
  exact A.l_spec x hx y hy hR i

/-- Theorem 3's changed-coordinate loads count neighbors that differ from the
fixed input.  On a Boolean coordinate where `x i ≠ y i`, that is the same as
agreeing with the other input, and it is not the factor bounded by
`ambainisRelation_unchangedLoad_le`. -/
theorem ambainisRelation_sourceChangedLoad_eq {n : ℕ}
    (A : AmbainisRelation n) {x y : Fin n → Bool} {i : Fin n}
    (hi : x i ≠ y i) :
    (A.Y.filter (fun y' => A.R x y' ∧ y' i ≠ x i)).card =
        (A.Y.filter (fun y' => A.R x y' ∧ y' i = y i)).card ∧
      (A.X.filter (fun x' => A.R x' y ∧ x' i ≠ y i)).card =
        (A.X.filter (fun x' => A.R x' y ∧ x' i = x i)).card := by
  obtain ⟨hKeep, hChange⟩ := bool_changedCoordinate_bit hi
  refine ⟨?_, ?_⟩
  · refine congrArg Finset.card ?_
    refine Finset.filter_congr ?_
    intro y' _
    exact and_congr_right fun _ => hChange (y' i)
  · refine congrArg Finset.card ?_
    refine Finset.filter_congr ?_
    intro x' _
    exact and_congr_right fun _ => (hKeep (x' i)).symm

/-- The adversary value is monotone in the two relation degrees and
antitone in the load bound: larger relation degrees and a smaller
load bound can only increase `√(m·m'/l_max)`.
This is the comparison step used when the exact relation counts of
Theorems 4 and 5 are replaced by their `Θ(·)` estimates. -/
theorem adversaryValue_mono {m m' lmax M M' L : ℕ}
    (hm : m ≤ M) (hm' : m' ≤ M') (hL : L ≤ lmax) (hLpos : 0 < L) :
    adversaryValue m m' lmax ≤ adversaryValue M M' L := by
  unfold adversaryValue
  apply Real.sqrt_le_sqrt
  have hmR : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
  have hm'R : (m' : ℝ) ≤ (M' : ℝ) := by exact_mod_cast hm'
  have hLR : (L : ℝ) ≤ (lmax : ℝ) := by exact_mod_cast hL
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hlmaxposR : (0 : ℝ) < (lmax : ℝ) := lt_of_lt_of_le hLposR hLR
  have hnum : (m : ℝ) * (m' : ℝ) ≤ (M : ℝ) * (M' : ℝ) :=
    mul_le_mul hmR hm'R (by positivity) (by positivity)
  rw [div_le_div_iff₀ hlmaxposR hLposR]
  exact mul_le_mul hnum hLR (by positivity) (by positivity)

/-- Substituting `m = m' = n²` and `l_max = n` gives the value `n·√n`,
illustrating the scale of Theorem 5. -/
theorem adversaryValue_matrix (n : ℕ) (hn : 0 < n) :
    adversaryValue (n ^ 2) (n ^ 2) n = (n : ℝ) * Real.sqrt (n : ℝ) := by
  unfold adversaryValue
  have h : ((n ^ 2 : ℕ) : ℝ) * ((n ^ 2 : ℕ) : ℝ) / (n : ℝ) =
      ((n : ℝ) ^ 2) ^ 2 / (n : ℝ) := by
    push_cast
    ring
  rw [h]
  exact sqrt_matrix_parameters n hn

/-- At the Theorem 5 parameters the adversary value is at least `n`
whenever `n ≥ 1`: the `n^{3/2}` value dominates the linear scale. -/
theorem adversaryValue_matrix_ge (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ adversaryValue (n ^ 2) (n ^ 2) n := by
  have hn0 : 0 < n := hn
  rw [adversaryValue_matrix n hn0]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := by positivity
  calc (n : ℝ) = (n : ℝ) * 1 := by ring
    _ ≤ (n : ℝ) * Real.sqrt (n : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt hnR

/-- The numerical adversary value is positive when both degree parameters
and the load parameter are positive. -/
theorem adversaryValue_pos {m m' lmax : ℕ} (hm : 0 < m) (hm' : 0 < m')
    (hl : 0 < lmax) : 0 < adversaryValue m m' lmax := by
  unfold adversaryValue
  apply Real.sqrt_pos.mpr
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm'R : (0 : ℝ) < (m' : ℝ) := by exact_mod_cast hm'
  have hlR : (0 : ℝ) < (lmax : ℝ) := by exact_mod_cast hl
  exact div_pos (mul_pos hmR hm'R) hlR

end Qatlib.Papers.GraphConnect03.RelationBound
