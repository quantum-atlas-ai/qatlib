/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GroupExtTest13.MainResults.Lemma38.SourceLemma38

@[expose] public section


/-! Closed algebraic parts of Zatloukal, arXiv:1305.1327v1, Lemmas 3.7 and 3.10.
The unrestricted legacy forward direction is not asserted here. -/

set_option autoImplicit false

namespace Qatlib.Papers.GroupExtTest13.MainResults

open scoped BigOperators
open Qatlib.Papers.GroupExtTest13.MainResults

variable {Idx : Type*} [Fintype Idx]
variable {A : Type*} [AddCommGroup A]

/-- Factorised coboundaries are ordinary normalized coboundaries. -/
theorem lemma37_reverse (d : Idx → ℕ)
    {f g : CyclicProduct d → CyclicProduct d → A}
    (h : f - g ∈ BF2 (A := A) d) :
    f - g ∈ B2 (G := CyclicProduct d) (A := A) :=
  BF2_subset_B2 d h

variable [LinearOrder Idx]

/-- The `α`/`β` normal form of Lemma 3.9 (arXiv:1305.1327v1, page 10). -/
def paramForm (d : Idx → ℕ) (α : Idx → A) (β : Idx → Idx → A) :
    CyclicProduct d → CyclicProduct d → A :=
  fun x y =>
    (∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • α i)
      + ∑ i, ∑ j, (if i < j then (((y i).val : ℤ) * (x j).val) • β i j else 0)

/-- **Lemma 3.10, reverse direction.**  If the `β_{i,j}` agree for `i < j` and
`α'_i - α_i` is a `d_i`-multiple, then `f - f' ∈ B_F²(G,A)`.
Proof: `f - f' = ∑_i δ_i • (α_i - α'_i)` and `α_i - α'_i = d_i • (-a_i)`,
so `f - f' = ∂(FForm (fun i ↦ -a_i))` (Lemma 3.8). -/
theorem lemma310_reverse (d : Idx → ℕ) [∀ i, NeZero (d i)]
    (α α' : Idx → A) (β β' : Idx → Idx → A)
    (hβ : ∀ i j, i < j → β i j = β' i j)
    (hα : ∀ i, ∃ a : A, (d i : ℤ) • a = α' i - α i) :
    (paramForm d α β - paramForm d α' β') ∈ BF2 (A := A) d := by
  choose a ha using hα
  refine ⟨fun i => -a i, ?_⟩
  funext x y
  have hSβ :
      (∑ i, ∑ j, (if i < j then (((y i).val : ℤ) * (x j).val) • β i j else 0))
        = ∑ i, ∑ j,
            (if i < j then (((y i).val : ℤ) * (x j).val) • β' i j else 0) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hij : i < j
    · rw [ite_eq_left hij, ite_eq_left hij, hβ i j hij]
    · rw [ite_eq_right hij, ite_eq_right hij]
  simp only [Pi.sub_apply, paramForm]
  rw [hSβ, FForm_coboundary]
  have hcancel :
      ((∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • α i)
          + ∑ i, ∑ j, (if i < j then (((y i).val : ℤ) * (x j).val) • β' i j else 0))
        - ((∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • α' i)
          + ∑ i, ∑ j,
              (if i < j then (((y i).val : ℤ) * (x j).val) • β' i j else 0))
      = (∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • α i)
          - ∑ i, (if d i ≤ (x i).val + (y i).val then (1 : ℤ) else 0) • α' i := by
    abel
  rw [hcancel, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← smul_sub]
  congr 1
  rw [← neg_sub, ← ha i, ← smul_neg]


end Qatlib.Papers.GroupExtTest13.MainResults
