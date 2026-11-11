/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic

/-!
# Cyclic reindexing of phase mixtures

`rightArc` selects a discrete arc of cyclic indices and `rightIndex` enumerates it using a
centered integer interval. The module proves that this enumeration is bijective onto the
selected arc and transports sums of powers of a root of unity to cyclic coordinates.

`mixturePhase_sum` combines a full-cycle component with an arc component as a single weighted
cyclic sum. This finite phase bookkeeping supports the moment constructions associated with
[TangWright2025].

## Main statements

* `sum_rightIndex`: reindex an arc sum as a filtered cyclic sum.
* `rightIndex_phase`: centered integer and cyclic exponents define the same phase.
* `mixturePhase_sum`: combine full-cycle and arc phase sums.

## References

* [Tang and Wright, 2025][TangWright2025]
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open scoped BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.TorusMoments

/-- The cyclic indices satisfying `g.val ≤ q / 4` or `q - q / 4 ≤ g.val`. -/
def rightArc {q : ℕ} (g : Fin q) : Prop := g.val ≤ q/4 ∨ q-q/4 ≤ g.val

instance {q : ℕ} (g : Fin q) : Decidable (rightArc g) := by
  unfold rightArc
  infer_instance

/-- The cyclic index corresponding to the centered interval of `2 * (q / 4) + 1` indices, for `q
> 1`. -/
def rightIndex {q : ℕ} (hq : 1<q) (j : Fin (2*(q/4)+1)) : Fin q :=
  ⟨if j.val<q/4 then q-q/4+j.val else j.val-q/4,by split_ifs <;> omega⟩

/-- Every index produced by `rightIndex` belongs to `rightArc`. -/
theorem rightIndex_mem {q : ℕ} (hq : 1<q) (j : Fin (2*(q/4)+1)) :
    rightArc (rightIndex hq j) := by
  unfold rightArc rightIndex
  split_ifs <;> dsimp only <;> omega

/-- For `q > 1`, the arc-indexing function `rightIndex` is injective. -/
theorem rightIndex_injective {q : ℕ} (hq : 1<q) : Function.Injective (rightIndex hq) := by
  intro i j h
  have he := congrArg Fin.val h
  apply Fin.ext
  dsimp only [rightIndex] at he
  split_ifs at he <;> omega

/-- Every cyclic index in `rightArc` is produced by `rightIndex` when `q > 1`. -/
theorem rightIndex_surjective {q : ℕ} (hq : 1<q) (g : Fin q) (hg : rightArc g) :
    ∃j,rightIndex hq j=g := by
  by_cases hlo : g.val≤q/4
  · refine ⟨⟨q/4+g.val,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [rightIndex]
    split_ifs <;> omega
  · have hhi : q-q/4≤g.val := hg.resolve_left hlo
    refine ⟨⟨g.val-(q-q/4),by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [rightIndex]
    split_ifs <;> omega

/-- A sum over the centered arc enumeration equals the sum over all cyclic indices restricted by
`rightArc`. -/
theorem sum_rightIndex {q : ℕ} (hq : 1<q) (f : Fin q→ℂ) :
    (∑j : Fin (2*(q/4)+1),f (rightIndex hq j)) =
      ∑g : Fin q,if rightArc g then f g else 0 := by
  classical
  calc
    _ = ∑g ∈ Finset.univ.filter rightArc,f g := by
      apply Finset.sum_bij (fun j _=>rightIndex hq j)
      · intro j _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rightIndex_mem hq j⟩
      · intro i _ j _ he
        exact rightIndex_injective hq he
      · intro g hg
        obtain ⟨j,hj⟩ := rightIndex_surjective hq g (Finset.mem_filter.mp hg).2
        exact ⟨j,Finset.mem_univ _,hj⟩
      · intro _ _
        rfl
    _ = _ := Finset.sum_filter _ _

/-- For a nonzero complex number satisfying `omega^q = 1`, the centered integer exponent and its
cyclic representative give the same power. -/
theorem rightIndex_phase {q : ℕ} (hq : 1<q) (omega : ℂ) (hw0 : omega≠0)
    (hwq : omega^q=1) (j : Fin (2*(q/4)+1)) :
    omega^((j.val : ℤ)-(q/4 : ℕ))=omega^(rightIndex hq j).val := by
  have he : ((rightIndex hq j).val : ℤ)=
      ((j.val : ℤ)-(q/4 : ℕ))+(if j.val<q/4 then (q : ℤ) else 0) := by
    dsimp only [rightIndex]
    split_ifs <;> omega
  rw [← zpow_natCast,he,zpow_add₀ hw0]
  split_ifs <;> simp [hwq]

/-- A phase sum over centered integer exponents equals the corresponding sum over cyclic powers
restricted to `rightArc`. -/
theorem rightPhase_sum {q : ℕ} (hq : 1<q) (omega : ℂ) (hw0 : omega≠0)
    (hwq : omega^q=1) (f : ℂ→ℂ) :
    (∑j : Fin (2*(q/4)+1),f (omega^((j.val : ℤ)-(q/4 : ℕ)))) =
      ∑g : Fin q,if rightArc g then f (omega^g.val) else 0 := by
  simp_rw [rightIndex_phase hq omega hw0 hwq]
  exact sum_rightIndex hq (fun g=>f (omega^g.val))

/-- The weighted sum of full-cycle phases and centered arc phases is a single cyclic sum with
the arc weight added exactly on `rightArc`. -/
theorem mixturePhase_sum {q : ℕ} (hq : 1<q) (omega : ℂ) (hw0 : omega≠0)
    (hwq : omega^q=1) (a b : ℂ) (f : ℂ→ℂ) :
    (∑x : Fin q ⊕ Fin (2*(q/4)+1),
      Sum.elim (fun _=>a) (fun _=>b) x *
        f (Sum.elim (fun g : Fin q=>omega^g.val)
          (fun j : Fin (2*(q/4)+1)=>omega^((j.val : ℤ)-(q/4 : ℕ))) x)) =
    ∑g : Fin q,(a+(if rightArc g then b else 0))*f (omega^g.val) := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  rw [← Finset.mul_sum,← Finset.mul_sum,rightPhase_sum hq omega hw0 hwq f]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : rightArc g <;> simp [hg,add_mul]

end Qatlib.Foundations.MatrixAlgebra.TorusMoments
