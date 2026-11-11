/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Basic.ExistsUnique
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Logic.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SProd
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.CertQuery09.MainResults.Source.SpectralBound
import Qatlib.Papers.CertQuery09.MainResults.Source.QueryLowerSum

/-!
# An explicit two-level adversary matrix

This module represents Boolean matrices having one all-true row and exactly one false entry in
every other row. Adjacency between representatives gives a symmetric nonnegative adversary
matrix for identifying the distinguished row, as used in the two-level certification analysis of
[AmbainisEtAl2009].

## Main statements

* `gammaRep_opNorm`: computes the matrix norm as `d * (d - 1)`.
* `gammaRep_advDenom_le`: bounds each query-filtered operator norm by `d`.
* `two_level_advValue_ge`: proves the adversary-value lower bound `d - 1` when the ratio set is
  bounded above.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.propDecidable

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.CertQuery09.MainResults.Source

/-- The promise that a Boolean `d × d` matrix has exactly one all-true row and exactly one false
entry in each remaining row. -/
def TwoLevelPromise (d : ℕ) (x : Fin d → Fin d → Bool) : Prop :=
  (∃! j : Fin d, ∀ i : Fin d, x j i = true) ∧
    (∀ j : Fin d, ¬ (∀ i : Fin d, x j i = true) → ∃! i : Fin d, x j i = false)

/-- A distinguished row and a position function fixing that row, with other positions encoding
the unique false entry of each remaining row. -/
abbrev TwoLevelRep (d : ℕ) : Type := { q : Fin d × (Fin d → Fin d) // q.2 q.1 = q.1 }

/-- The distinguished row of a two-level representative. -/
def repRow {d : ℕ} (p : TwoLevelRep d) : Fin d := p.1.1

/-- The stored column-position function of a two-level representative. -/
def repPos {d : ℕ} (p : TwoLevelRep d) : Fin d → Fin d := p.1.2

/-- The stored position at the distinguished row equals that row's index. -/
theorem repPos_row {d : ℕ} (p : TwoLevelRep d) : repPos p (repRow p) = repRow p := p.2

instance twoLevelRepFintype (d : ℕ) : Fintype (TwoLevelRep d) := by
  classical exact inferInstance

instance twoLevelRepDecEq (d : ℕ) : DecidableEq (TwoLevelRep d) := Classical.decEq _

/-- The Boolean matrix represented by `p`, with an all-true distinguished row and a single false
entry at the stored position of every other row. -/
def repMat {d : ℕ} (p : TwoLevelRep d) : Fin d → Fin d → Bool :=
  fun r c => if r = repRow p then true else decide (repPos p r ≠ c)

/-- The output function returning the representative's distinguished row. -/
def repFun {d : ℕ} (p : TwoLevelRep d) : Fin d := repRow p

/-- The represented matrix viewed as Boolean input access indexed by a row-column pair. -/
def repBitsPair {d : ℕ} (p : TwoLevelRep d) : Fin d × Fin d → Bool :=
  fun rc => repMat p rc.1 rc.2

/-- The represented matrix flattened to Boolean input access on `Fin (d * d)` using
`finProdFinEquiv`. -/
def repBits (d : ℕ) : TwoLevelRep d → Fin (d * d) → Bool :=
  fun p i => repBitsPair p (finProdFinEquiv.symm i)

/-- The flattened bit at the encoding of `(r, c)` equals the represented matrix entry at row `r`
and column `c`. -/
theorem repBits_finProdFinEquiv {d : ℕ} (p : TwoLevelRep d) (r c : Fin d) :
    repBits d p (finProdFinEquiv (r, c)) = repMat p r c := by
  simp [repBits, repBitsPair]

/-- A represented matrix has exactly one all-true row. -/
theorem repMat_unique_true {d : ℕ} (p : TwoLevelRep d) :
    ∃! j : Fin d, ∀ i : Fin d, repMat p j i = true := by
  classical
  refine ⟨repRow p, fun i => ?_, ?_⟩
  · simp [repMat]
  · intro j hj
    by_contra hne
    have h := hj (repPos p j)
    simp [repMat, hne] at h

/-- Every row of a represented matrix that is not all true has exactly one false entry. -/
theorem repMat_unique_false {d : ℕ} (p : TwoLevelRep d) (j : Fin d)
    (hj : ¬ ∀ i : Fin d, repMat p j i = true) :
    ∃! i : Fin d, repMat p j i = false := by
  classical
  have hne : j ≠ repRow p := by
    intro h
    exact hj fun i => by simp [repMat, h]
  have hval : ∀ i, repMat p j i = decide (repPos p j ≠ i) := by
    intro i; simp [repMat, hne]
  refine ⟨repPos p j, by simp [hval], ?_⟩
  intro c hc
  rw [hval] at hc
  simp only [decide_eq_false_iff_not, not_not] at hc
  exact hc.symm

/-- Every represented matrix satisfies the two-level promise. -/
theorem repMat_promise {d : ℕ} (p : TwoLevelRep d) : TwoLevelPromise d (repMat p) :=
  ⟨repMat_unique_true p, fun j hj => repMat_unique_false p j hj⟩

/-- Adjacency of representatives with different distinguished rows and identical stored
positions on all rows other than those two. -/
def repAdj {d : ℕ} (p q : TwoLevelRep d) : Prop :=
  repRow p ≠ repRow q ∧ ∀ r : Fin d, r ≠ repRow p → r ≠ repRow q → repPos p r = repPos q r

/-- Representative adjacency is symmetric. -/
theorem repAdj_comm {d : ℕ} {p q : TwoLevelRep d} (h : repAdj p q) : repAdj q p := by
  obtain ⟨hne, hagree⟩ := h
  exact ⟨hne.symm, fun r hrq hrp => (hagree r hrp hrq).symm⟩

/-- The real zero-one matrix indicating adjacency of two-level representatives. -/
def gammaRep {d : ℕ} : Matrix (TwoLevelRep d) (TwoLevelRep d) ℝ := by
  classical
  exact fun p q => if repAdj p q then 1 else 0

/-- The representative adjacency matrix is symmetric. -/
theorem gammaRep_symm {d : ℕ} : ∀ p q, gammaRep (d := d) p q = gammaRep q p := by
  classical
  intro p q
  unfold gammaRep
  by_cases h : repAdj p q
  · rw [if_pos h, if_pos (repAdj_comm h)]
  · rw [if_neg h, if_neg (fun h' => h (repAdj_comm h'))]

/-- Every entry of the representative adjacency matrix is nonnegative. -/
theorem gammaRep_nonneg {d : ℕ} : ∀ p q, 0 ≤ gammaRep (d := d) p q := by
  classical
  intro p q
  unfold gammaRep
  by_cases h : repAdj p q <;> simp [h]

/-- The representative adjacency matrix vanishes between representatives with the same output
row. -/
theorem gammaRep_eq_zero {d : ℕ} : ∀ p q, repFun p = repFun q → gammaRep (d := d) p q = 0 := by
  classical
  intro p q h
  unfold gammaRep
  rw [if_neg]
  intro hadj
  exact hadj.1 h

/-- A neighbor of `p` is uniquely determined by its distinguished row and its stored position at
`p`'s distinguished row. -/
theorem repAdj_determined {d : ℕ} {p q q' : TwoLevelRep d}
    (hq : repAdj p q) (hq' : repAdj p q')
    (hr : repRow q = repRow q') (hp : repPos q (repRow p) = repPos q' (repRow p)) :
    q = q' := by
  obtain ⟨hne, hag⟩ := hq
  obtain ⟨hne', hag'⟩ := hq'
  have hpos : repPos q = repPos q' := by
    funext r
    by_cases hr1 : r = repRow p
    · subst hr1; exact hp
    · by_cases hr2 : r = repRow q
      · subst hr2
        rw [repPos_row q, hr, repPos_row q']
      · have h2 : r ≠ repRow q' := fun h => hr2 (h.trans hr.symm)
        rw [← hag r hr1 hr2, hag' r hr1 h2]
  exact Subtype.ext (Prod.ext hr hpos)

/-- If adjacent representatives differ at column `c` of `p`'s distinguished row, the neighbor's
stored position in that row is `c`. -/
theorem repAdj_pos_of_diff {d : ℕ} {p q : TwoLevelRep d} (hq : repAdj p q) (c : Fin d)
    (h : repMat p (repRow p) c ≠ repMat q (repRow p) c) :
    repPos q (repRow p) = c := by
  classical
  have hne : repRow p ≠ repRow q := hq.1
  have h1 : repMat p (repRow p) c = true := by simp [repMat]
  have h2 : repMat q (repRow p) c = false := by
    cases hb : repMat q (repRow p) c
    · rfl
    · exact absurd (h1.trans hb.symm) h
  simp only [repMat, if_neg hne, decide_eq_false_iff_not, not_not] at h2
  exact h2

/-- The representative with distinguished row `j`, stored position `c` at the old distinguished
row when distinct from `j`, and all other nondistinguished positions inherited from `p`. -/
def repRebuild {d : ℕ} (p : TwoLevelRep d) (j : Fin d) (c : Fin d) : TwoLevelRep d :=
  ⟨(j, fun r => if r = j then r else if r = repRow p then c else repPos p r),
    by simp⟩

/-- Rebuilding at a row different from `p`'s distinguished row produces a neighbor of `p`. -/
theorem repRebuild_adj {d : ℕ} (p : TwoLevelRep d) (j : Fin d) (c : Fin d)
    (hj : j ≠ repRow p) : repAdj p (repRebuild p j c) := by
  refine ⟨?_, ?_⟩
  · show repRow p ≠ repRow (repRebuild p j c)
    rw [show repRow (repRebuild p j c) = j from rfl]
    exact Ne.symm hj
  · intro r hrp hrj
    have hrj' : r ≠ j := fun h => hrj (show r = repRow (repRebuild p j c) from by
      rw [show repRow (repRebuild p j c) = j from rfl]; exact h)
    show repPos p r = repPos (repRebuild p j c) r
    simp only [repRebuild, repPos, hrj', if_false, hrp]

/-- The equivalence between neighbors of `p` and pairs consisting of a different distinguished
row and an arbitrary stored column at `p`'s distinguished row. -/
def neighbourEquiv {d : ℕ} (p : TwoLevelRep d) :
    {q : TwoLevelRep d // repAdj p q} ≃ ({j : Fin d // j ≠ repRow p} × Fin d) where
  toFun q := (⟨repRow q.1, fun h => q.2.1 h.symm⟩, repPos q.1 (repRow p))
  invFun jc := ⟨repRebuild p jc.1.1 jc.2, repRebuild_adj p jc.1.1 jc.2 jc.1.2⟩
  left_inv := by
    rintro ⟨q, hq⟩
    refine Subtype.ext ?_
    have hdet := repAdj_determined (q := q)
      (q' := repRebuild p (repRow q) (repPos q (repRow p))) hq
      (repRebuild_adj p (repRow q) (repPos q (repRow p)) (Ne.symm hq.1)) rfl (by
        simp only [repRebuild, repPos]
        rw [if_neg hq.1]
        simp)
    exact hdet.symm
  right_inv := by
    rintro ⟨⟨j, hj⟩, c⟩
    refine Prod.ext ?_ ?_
    · exact Subtype.ext (show j = repRow (repRebuild p j c) from rfl)
    · show repPos (repRebuild p j c) (repRow p) = c
      simp [repRebuild, repPos, Ne.symm hj]

/-- Every two-level representative has exactly `(d - 1) * d` neighbors. -/
theorem card_neighbours {d : ℕ} (p : TwoLevelRep d) :
    (Finset.univ.filter (fun q : TwoLevelRep d => repAdj p q)).card = (d - 1) * d := by
  classical
  set t : Finset (Fin d × Fin d) :=
    (Finset.univ.filter (fun j : Fin d => j ≠ repRow p)).product Finset.univ with ht
  have hfilter : (Finset.univ.filter (fun j : Fin d => j ≠ repRow p)).card = d - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
  have hcard : t.card = (d - 1) * d := by
    calc t.card = (Finset.univ.filter (fun j : Fin d => j ≠ repRow p)).card
          * (Finset.univ : Finset (Fin d)).card := by
          rw [ht]; exact Finset.card_product _ _
      _ = (d - 1) * d := by rw [hfilter, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_bij (fun q (_ : q ∈ Finset.univ.filter (fun q => repAdj p q)) =>
    (repRow q, repPos q (repRow p))) ?_ ?_ ?_
  · intro q hq
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2.1.symm⟩,
        Finset.mem_univ _⟩
  · intro q hq q' hq' heq
    have h1 := (Finset.mem_filter.mp hq).2
    have h1' := (Finset.mem_filter.mp hq').2
    simp only [Prod.mk.injEq] at heq
    exact repAdj_determined h1 h1' heq.1 heq.2
  · intro jc hjc
    have hj : jc.1 ≠ repRow p := (Finset.mem_filter.mp (Finset.mem_product.mp hjc).1).2
    refine ⟨repRebuild p jc.1 jc.2, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, repRebuild_adj p jc.1 jc.2 hj⟩
    · show (repRow (repRebuild p jc.1 jc.2), repPos (repRebuild p jc.1 jc.2) (repRow p)) = jc
      refine Prod.ext ?_ ?_
      · rfl
      · simp [repRebuild, repPos, Ne.symm hj]

/-- Every row of the representative adjacency matrix sums to `d * (d - 1)`. -/
theorem gammaRep_row_sum {d : ℕ} (p : TwoLevelRep d) :
    ∑ q, gammaRep (d := d) p q = ((d * (d - 1) : ℕ) : ℝ) := by
  classical
  have hterm : ∀ q : TwoLevelRep d,
      gammaRep (d := d) p q = if repAdj p q then (1 : ℝ) else 0 := by
    intro q; unfold gammaRep; rfl
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  have h1 : ∑ q : TwoLevelRep d, (if repAdj p q then (1 : ℝ) else 0)
      = ((Finset.univ.filter (fun q => repAdj p q)).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
    simp
  rw [h1, card_neighbours p, Nat.mul_comm (d - 1) d]

/-- If adjacent representatives differ in a row other than `p`'s distinguished row, that row is
the neighbor's distinguished row. -/
theorem repRow_eq_of_diff {d : ℕ} {p q : TwoLevelRep d} (hq : repAdj p q) {r c : Fin d}
    (hr : r ≠ repRow p) (hdiff : repMat p r c ≠ repMat q r c) : repRow q = r := by
  classical
  by_contra hne
  apply hdiff
  have hrq : r ≠ repRow q := fun h => hne h.symm
  simp only [repMat, if_neg hr, if_neg hrq]
  rw [hq.2 r hr hrq]

/-- At most `d` neighbors of any representative differ from it at a specified matrix entry. -/
theorem filter_diff_card_le {d : ℕ} (p : TwoLevelRep d) (r c : Fin d) :
    (Finset.univ.filter (fun q : TwoLevelRep d => repAdj p q ∧ repMat p r c ≠ repMat q r c)).card
      ≤ d := by
  classical
  by_cases hr : r = repRow p
  · subst hr
    have hle : (Finset.univ.filter (fun q : TwoLevelRep d =>
          repAdj p q ∧ repMat p (repRow p) c ≠ repMat q (repRow p) c)).card
        ≤ (Finset.univ.filter (fun j : Fin d => j ≠ repRow p)).card := by
      refine Finset.card_le_card_of_injOn (fun q : TwoLevelRep d => repRow q) ?_ ?_
      · intro q hq
        have hq' : repAdj p q ∧ repMat p (repRow p) c ≠ repMat q (repRow p) c := by
          simpa using hq
        simpa using Ne.symm hq'.1.1
      · intro q hq q' hq' heq
        have hq1 : repAdj p q ∧ repMat p (repRow p) c ≠ repMat q (repRow p) c := by
          simpa using hq
        have hq1' : repAdj p q' ∧ repMat p (repRow p) c ≠ repMat q' (repRow p) c := by
          simpa using hq'
        exact repAdj_determined hq1.1 hq1'.1 heq
          (by rw [repAdj_pos_of_diff hq1.1 c hq1.2, repAdj_pos_of_diff hq1'.1 c hq1'.2])
    have hcard : (Finset.univ.filter (fun j : Fin d => j ≠ repRow p)).card = d - 1 := by
      rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin]
    rw [hcard] at hle
    omega
  · have hle : (Finset.univ.filter (fun q : TwoLevelRep d =>
          repAdj p q ∧ repMat p r c ≠ repMat q r c)).card
        ≤ (Finset.univ : Finset (Fin d)).card := by
      refine Finset.card_le_card_of_injOn (fun q : TwoLevelRep d => repPos q (repRow p))
        (fun q _ => by simp) ?_
      intro q hq q' hq' heq
      have hq1 : repAdj p q ∧ repMat p r c ≠ repMat q r c := by
        simpa using hq
      have hq1' : repAdj p q' ∧ repMat p r c ≠ repMat q' r c := by
        simpa using hq'
      exact repAdj_determined hq1.1 hq1'.1
        (by rw [repRow_eq_of_diff hq1.1 hr hq1.2, repRow_eq_of_diff hq1'.1 hr hq1'.2]) heq
    rw [Finset.card_univ, Fintype.card_fin] at hle
    exact hle

/-- For `d ≥ 1`, the Euclidean operator norm of the representative adjacency matrix equals `d *
(d - 1)`. -/
theorem gammaRep_opNorm {d : ℕ} (hd : 1 ≤ d) :
    ‖gammaRep (d := d)‖ = ((d * (d - 1) : ℕ) : ℝ) := by
  haveI : Nonempty (TwoLevelRep d) :=
    ⟨⟨(⟨0, hd⟩, fun _ => ⟨0, hd⟩), rfl⟩⟩
  exact l2_opNorm_eq_of_regular gammaRep gammaRep_nonneg gammaRep_symm gammaRep_row_sum

/-- The query-filtered representative adjacency entry is one exactly for adjacent
representatives differing at the queried bit, and zero otherwise. -/
theorem hadamard_gammaRep {d : ℕ} (p q : TwoLevelRep d) (i : Fin (d * d)) :
    (gammaRep ⊙ diffMatrix (repBits d) i) p q
      = if repAdj p q ∧ repBits d p i ≠ repBits d q i then (1 : ℝ) else 0 := by
  classical
  unfold gammaRep diffMatrix
  by_cases h1 : repAdj p q <;> by_cases h2 : repBits d p i = repBits d q i <;>
    simp [h1, h2]

/-- Every row sum of the representative adjacency matrix filtered at a query position is at most
`d`. -/
theorem hadamard_row_sum_le {d : ℕ} (p : TwoLevelRep d) (i : Fin (d * d)) :
    ∑ q, (gammaRep ⊙ diffMatrix (repBits d) i) p q ≤ (d : ℝ) := by
  classical
  set rc := finProdFinEquiv.symm i with hrc
  have hterm : ∀ q : TwoLevelRep d,
      (gammaRep ⊙ diffMatrix (repBits d) i) p q
        = if repAdj p q ∧ repMat p rc.1 rc.2 ≠ repMat q rc.1 rc.2 then (1 : ℝ) else 0 :=
    fun q => hadamard_gammaRep p q i
  rw [Finset.sum_congr rfl fun q _ => hterm q]
  have hsum : ∑ q : TwoLevelRep d,
        (if repAdj p q ∧ repMat p rc.1 rc.2 ≠ repMat q rc.1 rc.2 then (1 : ℝ) else 0)
      = ((Finset.univ.filter (fun q : TwoLevelRep d =>
          repAdj p q ∧ repMat p rc.1 rc.2 ≠ repMat q rc.1 rc.2)).card : ℝ) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum]
    simp
  rw [hsum]
  exact_mod_cast filter_diff_card_le p rc.1 rc.2

/-- For positive input length, the representative adjacency matrix's adversary denominator is at
most `d`. -/
theorem gammaRep_advDenom_le {d : ℕ} (hn : 0 < d * d) :
    advDenom (repBits d) hn (gammaRep (d := d)) ≤ (d : ℝ) := by
  classical
  unfold advDenom
  refine Finset.sup'_le _ _ fun i _ => ?_
  refine l2_opNorm_le_of_row_sum_le _ (fun p q => ?_) (fun p q => ?_)
    (Nat.cast_nonneg d) (fun p => hadamard_row_sum_le p i)
  · exact mul_nonneg (gammaRep_nonneg p q) (by unfold diffMatrix; split <;> norm_num)
  · exact hadamard_symm gammaRep _ gammaRep_symm (fun x y => diffMatrix_symm _ _ x y) p q

/-- For `d ≥ 2`, the representative adjacency matrix's adversary denominator is strictly
positive. -/
theorem gammaRep_advDenom_pos {d : ℕ} (hd : 2 ≤ d) (hn : 0 < d * d) :
    0 < advDenom (repBits d) hn (gammaRep (d := d)) := by
  classical
  let p : TwoLevelRep d := ⟨(⟨0, by omega⟩, fun _ => ⟨0, by omega⟩), rfl⟩
  let j : Fin d := ⟨1, by omega⟩
  let q : TwoLevelRep d := repRebuild p j ⟨0, by omega⟩
  have hj : j ≠ repRow p := by
    intro h
    have h0 : (repRow p).val = 0 := rfl
    have h1 : j.val = 1 := rfl
    rw [h] at h1
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  have hpq : repAdj p q := repRebuild_adj p j ⟨0, by omega⟩ hj
  set c : Fin d := repPos q (repRow p) with hc
  let i : Fin (d * d) := finProdFinEquiv (repRow p, c)
  have hbits_p : repBits d p i = true := by
    show repBits d p (finProdFinEquiv (repRow p, c)) = true
    rw [repBits_finProdFinEquiv]
    simp [repMat]
  have hbits_q : repBits d q i = false := by
    show repBits d q (finProdFinEquiv (repRow p, c)) = false
    rw [repBits_finProdFinEquiv]
    have hval : repMat q (repRow p) c = decide (repPos q (repRow p) ≠ c) := by
      simp [repMat, hpq.1]
    rw [hval, hc]
    simp
  have hentry : (gammaRep ⊙ diffMatrix (repBits d) i) p q = 1 := by
    rw [hadamard_gammaRep]
    have hne : repBits d p i ≠ repBits d q i := by rw [hbits_p, hbits_q]; simp
    simp [hpq, hne]
  have hne0 : (gammaRep ⊙ diffMatrix (repBits d) i) ≠ 0 := by
    intro h
    have h1 := congrFun (congrFun h p) q
    simp only [hentry] at h1
    exact one_ne_zero h1
  have hpos_norm : 0 < ‖gammaRep ⊙ diffMatrix (repBits d) i‖ := by
    rw [norm_pos_iff]
    exact hne0
  unfold advDenom
  rw [Finset.lt_sup'_iff ⟨⟨0, hn⟩, Finset.mem_univ _⟩]
  exact ⟨i, Finset.mem_univ _, hpos_norm⟩

/-- For `d ≥ 2`, there exist adjacent two-level representatives. -/
theorem exists_repAdj {d : ℕ} (hd : 2 ≤ d) : ∃ p q : TwoLevelRep d, repAdj p q := by
  classical
  let p : TwoLevelRep d := ⟨(⟨0, by omega⟩, fun _ => ⟨0, by omega⟩), rfl⟩
  let j : Fin d := ⟨1, by omega⟩
  have hj : j ≠ repRow p := by
    intro h
    have h0 : (repRow p).val = 0 := rfl
    have h1 : j.val = 1 := rfl
    rw [h] at h1
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  exact ⟨p, repRebuild p j ⟨0, by omega⟩, repRebuild_adj p j ⟨0, by omega⟩ hj⟩

/-- For `d ≥ 2`, the representative adjacency matrix is nonzero. -/
theorem gammaRep_ne_zero {d : ℕ} (hd : 2 ≤ d) : gammaRep (d := d) ≠ 0 := by
  classical
  obtain ⟨p, q, hpq⟩ := exists_repAdj hd
  intro h
  have h1 := congrFun (congrFun h p) q
  unfold gammaRep at h1
  rw [if_pos hpq] at h1
  exact one_ne_zero h1

/-- For `d ≥ 2`, the representative adjacency matrix is an adversary matrix for the
distinguished-row output function. -/
theorem gammaRep_isAdversary {d : ℕ} (hd : 2 ≤ d) :
    IsAdversaryMatrix (repFun (d := d)) (gammaRep (d := d)) :=
  ⟨gammaRep_ne_zero hd, gammaRep_symm, gammaRep_nonneg, gammaRep_eq_zero⟩

/-- For `d ≥ 2`, the explicit representative matrix's norm ratio belongs to the adversary-ratio
set for the distinguished-row problem. -/
theorem two_level_advRatio_mem {d : ℕ} (hd : 2 ≤ d) (hn : 0 < d * d) :
    ‖gammaRep (d := d)‖ / advDenom (repBits d) hn (gammaRep (d := d))
      ∈ advRatios (repBits d) hn (repFun (d := d)) :=
  ⟨gammaRep, gammaRep_isAdversary hd, rfl⟩

/-- For `d ≥ 2`, the explicit representative adjacency matrix has adversary ratio at least `d -
1`. -/
theorem two_level_adv_ratio_ge {d : ℕ} (hd : 2 ≤ d) (hn : 0 < d * d) :
    (d : ℝ) - 1 ≤ ‖gammaRep (d := d)‖ / advDenom (repBits d) hn (gammaRep (d := d)) := by
  have hden : 0 < advDenom (repBits d) hn (gammaRep (d := d)) :=
    gammaRep_advDenom_pos hd hn
  rw [le_div_iff₀ hden]
  have hle : advDenom (repBits d) hn (gammaRep (d := d)) ≤ (d : ℝ) :=
    gammaRep_advDenom_le hn
  have hop : ‖gammaRep (d := d)‖ = ((d * (d - 1) : ℕ) : ℝ) :=
    gammaRep_opNorm (by omega)
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (le_trans (by norm_num) hd)
  calc ((d : ℝ) - 1) * advDenom (repBits d) hn (gammaRep (d := d))
      ≤ ((d : ℝ) - 1) * (d : ℝ) := mul_le_mul_of_nonneg_left hle (by linarith)
    _ = ((d * (d - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ d)]
        push_cast
        ring
    _ = ‖gammaRep (d := d)‖ := hop.symm

/-- For `d ≥ 2`, boundedness above of the distinguished-row adversary-ratio set implies an
adversary value of at least `d - 1`. This is the explicit two-level lower bound used in the
certification analysis of [AmbainisEtAl2009]. -/
theorem two_level_advValue_ge {d : ℕ} (hd : 2 ≤ d) (hn : 0 < d * d)
    (hbdd : BddAbove (advRatios (repBits d) hn (repFun (d := d)))) :
    (d : ℝ) - 1 ≤ advValue (repBits d) hn (repFun (d := d)) := by
  have hmem := two_level_advRatio_mem (d := d) hd hn
  have hle := le_csSup hbdd hmem
  exact le_trans (two_level_adv_ratio_ge (d := d) hd hn) hle

end Qatlib.Papers.CertQuery09.MainResults.Source
