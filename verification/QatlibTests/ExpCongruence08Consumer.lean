module

public import Qatlib.Papers.ExpCongruence08.MainResults.SearchDensity
public import Qatlib.Papers.ExpCongruence08.MainResults.DenseOrders

public section

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators
open Qatlib.Papers.ExpCongruence08.MainResults
open Qatlib.Papers.ExpCongruence08.MainResults

namespace QatlibTests.ExpCongruence08Consumer

/-- An ordinary module can use the squared-norm bound on the real Euclidean count vector. -/
theorem variance_consumer {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (r : ℕ) (hrt : r ≤ orderOf g) :
    ‖(countDeviation a b f g r : EuclideanSpace ℝ F)‖ ^ 2 ≤
      ((Fintype.card F : ℝ) - (orderOf f : ℝ)) * r :=
  countDeviation_norm_sq_le a b f g r hrt

/-- The consumer gets the exact exceptional-set and deviation bounds of Lemma 2. -/
theorem typical_count_consumer {F : Type*} [Field F] [Fintype F]
    (a b f g : Fˣ) (r : ℕ) (δ : ℝ) (hr : 1 ≤ r) (hrt : r ≤ orderOf g) (hδ : 0 < δ) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ (Fintype.card F : ℝ) / δ ^ 2 ∧
      ∀ c : Fˣ, c ∉ bad →
        |(numSolutions a b c f g (orderOf f) r : ℝ) -
          (r : ℝ) * (orderOf f : ℝ) / (Fintype.card F : ℝ)| < δ * Real.sqrt (r : ℝ) :=
  typical_count a b f g r δ hr hrt hδ

/-- The typical large-order result gives the scalar bound in terms of the actual marked count. -/
theorem marked_search_consumer {F : Type*} [Field F] [Fintype F] (a b f g : Fˣ)
    (hst : orderOf g ≤ orderOf f)
    (hlarge : (Fintype.card F : ℝ) ^ 4 * (Real.log (Fintype.card F : ℝ)) ^ 2 <
      ((orderOf f : ℝ) * (orderOf g : ℝ)) ^ 3) :
    ∃ bad : Finset Fˣ,
      (bad.card : ℝ) ≤ 4 * (Fintype.card F : ℝ) / Real.log (Fintype.card F : ℝ) ∧
      ∀ c : Fˣ, c ∉ bad →
        0 < (markedExponents a b c f g (orderOf g)).card ∧
        Real.sqrt ((orderOf g : ℝ) / (markedExponents a b c f g (orderOf g)).card) ≤
          Real.sqrt (2 * (Fintype.card F : ℝ) /
            Real.sqrt ((orderOf f : ℝ) * (orderOf g : ℝ))) :=
  typical_full_scan_marked_search a b f g hst hlarge

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A two-step period over the five-element field has a certified squared Euclidean bound
of six. Both sides of its exponent box have length two. -/
theorem variance_two_step_zmod_five :
    ‖countDeviation (1 : (ZMod 5)ˣ) 1 (-1) (-1) 2‖ ^ 2 ≤ 6 := by
  have horder : orderOf (-1 : (ZMod 5)ˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one]
    simp [ZMod.ringChar_zmod_n]
  have h := countDeviation_norm_sq_le (1 : (ZMod 5)ˣ) 1 (-1) (-1) 2 (by rw [horder])
  norm_num [ZMod.card, horder] at h
  exact h

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The dense-order premise holds over the three-element field for two periods of length two,
and every nonzero target is attained in that box. -/
theorem dense_scan_zmod_three (c : (ZMod 3)ˣ) :
    ∃ x y : ℕ, x < 2 ∧ y < 2 ∧ (-1 : ZMod 3) ^ x + (-1 : ZMod 3) ^ y = (c : ZMod 3) := by
  have horder : orderOf (-1 : (ZMod 3)ˣ) = 2 := by
    rw [← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one]
    simp [ZMod.ringChar_zmod_n]
  have h := solvable_of_card_lt_order_add_scan (1 : (ZMod 3)ˣ) 1 c (-1) (-1) 2
    (by rw [horder]) (by norm_num [ZMod.card, horder])
  simpa [horder] using h

end QatlibTests.ExpCongruence08Consumer
