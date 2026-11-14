/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Ring.CompTypeclasses
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic
public import Qatlib.Papers.SignedWtEnum99.MainResults.QSEN

@[expose] public section

/-!
# Independent-column construction for Lemma 10

This module constructs replacement columns for a binary matrix while preserving the required
triangular pairings with `H1`. The recursive family `build` is chosen in reverse column order to
maintain linear independence, and `H2mat` installs the resulting vectors into the first `n`
columns. See [KnillLaflamme1999] for the source development.

## Main statements

* `step_exists`: supplies a vector satisfying the pairing constraints outside the span of the
  existing family.
* `build_linIndep`: proves independence of the recursively chosen family through stage `n`.
* `lemma10`: preserves the strictly lower triangular and diagonal parts while making the first
  `n` columns independent.

## References

* [Knill and Laflamme, 1999][KnillLaflamme1999]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SignedWtEnum99.MainResults

/-- The column vector of a binary matrix at the specified column index. -/
def col {n N : ℕ} (M : Matrix (Fin n) (Fin N) (ZMod 2)) (j : Fin N) : Fin n → ZMod 2 :=
  fun r => M r j

/-- An entry of `Mᵀ * M'` is the dot product of the corresponding columns of `M` and `M'`. -/
lemma col_dot {n N : ℕ} (M M' : Matrix (Fin n) (Fin N) (ZMod 2)) (i j : Fin N) :
    (Mᵀ * M') i j = col M i ⬝ᵥ col M' j := by
  simp [col, Matrix.mul_apply, dotProduct, Matrix.transpose_apply]

section Step

variable {n N : ℕ} (hn : n ≤ N)

/-- The binary linear map recording dot products against the first `i.val + 1` columns of `H1`,
using `hn` to embed their indices. -/
def constraintMap (H1 : Matrix (Fin n) (Fin N) (ZMod 2)) (i : Fin n) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] ({j : Fin n // j ≤ i} → ZMod 2) where
  toFun v j := col H1 (Fin.castLE hn j.1) ⬝ᵥ v
  map_add' a b := by
    funext j
    simp [dotProduct_add]
  map_smul' c a := by
    funext j
    simp [dotProduct_smul]

/-- The kernel of `constraintMap`, consisting of vectors orthogonal to the specified initial
columns of `H1`. -/
def dotSub (H1 : Matrix (Fin n) (Fin N) (ZMod 2)) (i : Fin n) :
    Submodule (ZMod 2) (Fin n → ZMod 2) :=
  (constraintMap hn H1 i).ker

/-- Membership in `dotSub hn H1 i` means that all dot products with columns indexed by `j ≤ i`
vanish. -/
lemma mem_dotSub {H1 : Matrix (Fin n) (Fin N) (ZMod 2)} {i : Fin n}
    {v : Fin n → ZMod 2} :
    v ∈ dotSub hn H1 i ↔
      ∀ j : {j : Fin n // j ≤ i}, col H1 (Fin.castLE hn j.1) ⬝ᵥ v = 0 := by
  constructor
  · intro h j
    have := congrFun h j
    simpa [dotSub, constraintMap] using this
  · intro h
    funext j
    simpa [dotSub, constraintMap] using h j

/-- The dimension of `dotSub hn H1 i` is at least `n - (i.val + 1)`. -/
lemma finrank_dotSub_ge (H1 : Matrix (Fin n) (Fin N) (ZMod 2)) (i : Fin n) :
    n - (i.val + 1) ≤ Module.finrank (ZMod 2) ↥(dotSub hn H1 i) := by
  let L := constraintMap hn H1 i
  have hker : dotSub hn H1 i = L.ker := rfl
  rw [hker]
  have hrank := LinearMap.finrank_range_add_finrank_ker L
  have hdim : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have htop : Module.finrank (ZMod 2)
      ↥(⊤ : Submodule (ZMod 2) ({j : Fin n // j ≤ i} → ZMod 2)) =
      Fintype.card {j : Fin n // j ≤ i} := by
    rw [finrank_top, Module.finrank_pi]
  have hle : Module.finrank (ZMod 2) ↥(L.range) ≤ Fintype.card {j : Fin n // j ≤ i} := by
    calc Module.finrank (ZMod 2) ↥(L.range)
        ≤ Module.finrank (ZMod 2)
            ↥(⊤ : Submodule (ZMod 2) ({j : Fin n // j ≤ i} → ZMod 2)) :=
          Submodule.finrank_mono le_top
      _ = Fintype.card {j : Fin n // j ≤ i} := htop
  have hcard : Fintype.card {j : Fin n // j ≤ i} = i.val + 1 := by
    rw [Fintype.card_subtype]
    have hset : ({j : Fin n | j ≤ i} : Finset (Fin n)) = Finset.Iic i := by
      ext j
      simp
    rw [show ({j : Fin n | j ≤ i} : Finset (Fin n)) = Finset.Iic i from hset, Fin.card_Iic]
  have hsum : Module.finrank (ZMod 2) ↥L.range + Module.finrank (ZMod 2) ↥L.ker = n := by
    simpa [hdim] using hrank
  omega

/-- If `x0` lies outside `Vsub` and the dimension of `W` is at most that of `Vsub`, the coset
`x0 + Vsub` contains a vector outside `W`. -/
lemma exists_mem_coset_not_mem {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Vsub W : Submodule K V} {x0 : V}
    (hx0 : x0 ∉ Vsub) (hdim : Module.finrank K ↥W ≤ Module.finrank K ↥Vsub) :
    ∃ x : V, x - x0 ∈ Vsub ∧ x ∉ W := by
  classical
  by_contra h
  rw [not_exists] at h
  have hmem : ∀ x : V, x - x0 ∈ Vsub → x ∈ W := by
    intro x hx
    by_contra hxW
    exact h x ⟨hx, hxW⟩
  have hzero : x0 - x0 ∈ Vsub := by
    rw [sub_self]
    exact Submodule.zero_mem Vsub
  have hx0W : x0 ∈ W := hmem x0 hzero
  have hsub : Vsub ≤ W := by
    intro v hv
    have h1 : (x0 + v) - x0 ∈ Vsub := by
      simpa only [add_sub_cancel_left] using hv
    exact by simpa using W.sub_mem (hmem (x0 + v) h1) hx0W
  have hfin : Module.finrank K ↥Vsub = Module.finrank K ↥W :=
    le_antisymm (Submodule.finrank_mono hsub) hdim
  have hEq : Vsub = W := Submodule.eq_of_le_of_finrank_eq hsub hfin
  exact hx0 (hEq ▸ hx0W)

/-- Under the unit-diagonal pairing hypothesis, a vector can match the required initial column
pairings while lying outside the span of any family of size at most `n - 1 - i.val`. -/
lemma step_exists (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1)
    (i : Fin n) {k : ℕ} (hk : k ≤ n - 1 - i.val)
    (e : Fin k → (Fin n → ZMod 2)) :
    ∃ x : Fin n → ZMod 2,
      (∀ j : Fin n, j ≤ i →
        col H1 (Fin.castLE hn j) ⬝ᵥ x =
          col H1 (Fin.castLE hn j) ⬝ᵥ col H0 (Fin.castLE hn i)) ∧
      x ∉ Submodule.span (ZMod 2) (Set.range e) := by
  classical
  let V := dotSub hn H1 i
  let W := Submodule.span (ZMod 2) (Set.range e)
  have hx0 : col H0 (Fin.castLE hn i) ∉ V := by
    intro hv
    have h0 := (mem_dotSub hn).mp hv ⟨i, le_rfl⟩
    have h1 : col H1 (Fin.castLE hn i) ⬝ᵥ col H0 (Fin.castLE hn i) = 1 := by
      rw [dotProduct_comm, ← col_dot]
      exact hdiag i
    rw [h1] at h0
    exact zero_ne_one h0.symm
  have hdimV : n - 1 - i.val ≤ Module.finrank (ZMod 2) ↥V := by
    dsimp only [V]
    have := finrank_dotSub_ge hn H1 i
    omega
  have hdimW : Module.finrank (ZMod 2) ↥W ≤ k := by
    calc Module.finrank (ZMod 2) ↥W
        ≤ (Set.range e).toFinset.card := finrank_span_le_card _
      _ = Fintype.card (Set.range e) := Set.toFinset_card _
      _ ≤ Fintype.card (Fin k) := Fintype.card_range_le e
      _ = k := Fintype.card_fin k
  have hkV : Module.finrank (ZMod 2) ↥W ≤ Module.finrank (ZMod 2) ↥V :=
    le_trans hdimW (le_trans hk hdimV)
  obtain ⟨x, hxV, hxW⟩ := exists_mem_coset_not_mem hx0 hkV
  refine ⟨x, ?_, hxW⟩
  intro j hj
  have h0 : col H1 (Fin.castLE hn j) ⬝ᵥ (x - col H0 (Fin.castLE hn i)) = 0 :=
    (mem_dotSub hn).mp hxV ⟨j, hj⟩
  rw [dotProduct_sub] at h0
  exact sub_eq_zero.mp h0

/-- A chosen vector satisfying the pairing and span-avoidance conditions established by
`step_exists`. -/
def stepChoice (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1)
    (i : Fin n) {k : ℕ} (hk : k ≤ n - 1 - i.val)
    (e : Fin k → (Fin n → ZMod 2)) : Fin n → ZMod 2 :=
  Classical.choose (step_exists hn H0 H1 hdiag i hk e)

/-- The chosen vector matches the initial column pairings of the corresponding column of `H0`
and lies outside the span of the supplied family. -/
lemma stepChoice_spec (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1)
    (i : Fin n) {k : ℕ} (hk : k ≤ n - 1 - i.val)
    (e : Fin k → (Fin n → ZMod 2)) :
    (∀ j : Fin n, j ≤ i →
      col H1 (Fin.castLE hn j) ⬝ᵥ stepChoice hn H0 H1 hdiag i hk e =
        col H1 (Fin.castLE hn j) ⬝ᵥ col H0 (Fin.castLE hn i)) ∧
    stepChoice hn H0 H1 hdiag i hk e ∉ Submodule.span (ZMod 2) (Set.range e) :=
  Classical.choose_spec (step_exists hn H0 H1 hdiag i hk e)

end Step

section Build

variable {n N : ℕ}

/-- The reversal of a finite index, with value `n - 1 - i.val`. -/
def revIdx {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩

/-- The column index `n - 1 - K` used at construction stage `K < n`. -/
def stepIndex {n : ℕ} (K : ℕ) (hK : K < n) : Fin n := ⟨n - 1 - K, by omega⟩

/-- The value of the construction index `stepIndex K hK` is `n - 1 - K`. -/
lemma stepIndex_val {n : ℕ} (K : ℕ) (hK : K < n) :
    (stepIndex K hK).val = n - 1 - K := rfl

/-- The stage `K` satisfies the size bound needed to choose the column at `stepIndex K hK`. -/
lemma stepIndex_bound {n : ℕ} (K : ℕ) (hK : K < n) :
    K ≤ n - 1 - (stepIndex K hK).val := by
  rw [stepIndex_val]
  omega

/-- The recursively chosen family of replacement columns in reverse order, using `stepChoice`
through stage `n` and returning a zero family beyond that range. -/
noncomputable def build (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) :
    (K : ℕ) → (Fin K → (Fin n → ZMod 2))
| 0 => Fin.elim0
| K+1 =>
    if hK : K < n then
      Fin.snoc (build hn H0 H1 hdiag K)
        (stepChoice hn H0 H1 hdiag (stepIndex K hK) (stepIndex_bound K hK)
          (build hn H0 H1 hdiag K))
    else
      fun _ => 0

/-- The initial stage of the replacement-column construction is the empty family. -/
lemma build_zero (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) :
    build hn H0 H1 hdiag 0 = Fin.elim0 := by
  conv_lhs => rw [build]

/-- At a stage `K < n`, the recursive construction appends the vector selected by `stepChoice`
to the preceding family. -/
lemma build_succ (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1)
    {K : ℕ} (hK : K < n) :
    build hn H0 H1 hdiag (K + 1) =
      Fin.snoc (build hn H0 H1 hdiag K)
        (stepChoice hn H0 H1 hdiag (stepIndex K hK) (stepIndex_bound K hK)
          (build hn H0 H1 hdiag K)) := by
  conv_lhs => rw [build]
  simp only [dite_eq_left hK]

/-- For every stage `K ≤ n`, the family of replacement columns constructed by `build` is
linearly independent. -/
lemma build_linIndep (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1)
    (K : ℕ) (hK : K ≤ n) :
    LinearIndependent (ZMod 2) (build hn H0 H1 hdiag K) := by
  induction K with
  | zero =>
      exact linearIndependent_empty_type
  | succ K ih =>
      have hKlt : K < n := by omega
      rw [build_succ hn H0 H1 hdiag hKlt]
      rw [linearIndependent_finSnoc]
      exact ⟨ih (by omega), (stepChoice_spec hn H0 H1 hdiag (stepIndex K hKlt)
        (stepIndex_bound K hKlt) (build hn H0 H1 hdiag K)).2⟩

/-- At stage `K ≤ n`, each constructed vector has the same dot products as its corresponding
reversed column of `H0` against all required initial columns of `H1`. -/
lemma build_spec (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) :
    ∀ (K : ℕ) (hK : K ≤ n) (t : Fin K) (j : Fin n),
      j.val ≤ n - 1 - t.val →
      col H1 (Fin.castLE hn j) ⬝ᵥ build hn H0 H1 hdiag K t =
        col H1 (Fin.castLE hn j) ⬝ᵥ
          col H0 (Fin.castLE hn ⟨n - 1 - t.val, by omega⟩)
  | 0, _, t, _, _ => t.elim0
  | K + 1, hK, t, j, hj => by
      have hKlt : K < n := by omega
      revert j
      refine Fin.lastCases ?_ ?_ t
      · intro j hj
        rw [build_succ hn H0 H1 hdiag hKlt]
        simp only [Fin.snoc_last]
        have hspec := (stepChoice_spec hn H0 H1 hdiag (stepIndex K hKlt)
          (stepIndex_bound K hKlt) (build hn H0 H1 hdiag K)).1
        have hji : j ≤ stepIndex K hKlt := by
          rw [Fin.le_iff_val_le_val, stepIndex_val]
          simpa using hj
        have := hspec j hji
        simpa using! this
      · intro t' j hj
        rw [build_succ hn H0 H1 hdiag hKlt]
        simp only [Fin.snoc_castSucc]
        exact build_spec hn H0 H1 hdiag K (by omega) t' j (by simpa using hj)

/-- The completed replacement-column family, reindexed from construction order to the original
column order. -/
def finalVec (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) :
    Fin n → (Fin n → ZMod 2) :=
  fun i => build hn H0 H1 hdiag n (revIdx i)

/-- The completed replacement-column family `finalVec` is linearly independent. -/
lemma finalVec_linIndep (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) :
    LinearIndependent (ZMod 2) (finalVec hn H0 H1 hdiag) := by
  have hbase : LinearIndependent (ZMod 2) (build hn H0 H1 hdiag n) :=
    build_linIndep hn H0 H1 hdiag n le_rfl
  have hinj : Function.Injective (fun i : Fin n => revIdx i) := by
    intro a b h
    have hv : n - 1 - a.val = n - 1 - b.val := congrArg Fin.val h
    apply Fin.ext
    omega
  exact hbase.comp (fun i => revIdx i) hinj

/-- The matrix obtained by replacing the first `n` columns of `H0` with the supplied vectors and
retaining the later columns. -/
def H2mat (H0 : Matrix (Fin n) (Fin N) (ZMod 2))
    (c' : Fin n → (Fin n → ZMod 2)) : Matrix (Fin n) (Fin N) (ZMod 2) :=
  fun r j => if h : j.val < n then c' ⟨j.val, h⟩ r else H0 r j

/-- At an index embedded from `Fin n`, the corresponding column of `H2mat H0 c'` is `c' i`. -/
lemma H2mat_castLE (hn : n ≤ N) (H0 : Matrix (Fin n) (Fin N) (ZMod 2))
    (c' : Fin n → (Fin n → ZMod 2)) (i : Fin n) :
    (fun r => H2mat H0 c' r (Fin.castLE hn i)) = c' i := by
  funext r
  show (if h : (Fin.castLE hn i).val < n then c' ⟨(Fin.castLE hn i).val, h⟩ r
    else H0 r (Fin.castLE hn i)) = c' i r
  rw [dite_eq_left (show (Fin.castLE hn i).val < n from i.isLt)]
  congr 1

/-- Reversing a finite index twice recovers its original numerical value. -/
lemma orig_revIdx {n : ℕ} (i : Fin n) : n - 1 - (revIdx i).val = i.val := by
  simp only [revIdx, Fin.val_mk]
  have := i.isLt
  omega

/-- A column of `H2mat` whose index is less than `n` is the corresponding replacement vector. -/
lemma col_H2_lt {H0 : Matrix (Fin n) (Fin N) (ZMod 2)}
    {c' : Fin n → (Fin n → ZMod 2)} {i : Fin N} (hi : i.val < n) :
    col (H2mat H0 c') i = c' ⟨i.val, hi⟩ := by
  funext r
  show (if h : i.val < n then c' ⟨i.val, h⟩ r else H0 r i) = c' ⟨i.val, hi⟩ r
  rw [dite_eq_left hi]

/-- A column of `H2mat` whose index is at least `n` is the original column of `H0`. -/
lemma col_H2_ge {H0 : Matrix (Fin n) (Fin N) (ZMod 2)}
    {c' : Fin n → (Fin n → ZMod 2)} {i : Fin N} (hi : ¬ i.val < n) :
    col (H2mat H0 c') i = col H0 i := by
  funext r
  show (if h : i.val < n then c' ⟨i.val, h⟩ r else H0 r i) = H0 r i
  rw [dite_eq_right hi]

/-- For a replaced column `i`, its dot products against columns `j ≤ i` of `H1` agree with those
of the original column of `H0`. -/
lemma finalVec_spec (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1)
    {i : Fin N} (hi : i.val < n) (j : Fin N) (hj : j.val ≤ i.val) :
    col H1 j ⬝ᵥ finalVec hn H0 H1 hdiag ⟨i.val, hi⟩ =
      col H1 j ⬝ᵥ col H0 i := by
  have hjlt : j.val < n := lt_of_le_of_lt hj hi
  let jj : Fin n := ⟨j.val, hjlt⟩
  have hjj : (Fin.castLE hn jj) = j := Fin.ext rfl
  have hjeq : (Fin.castLE hn ⟨i.val, hi⟩) = i := Fin.ext rfl
  have hjt : jj.val ≤ n - 1 - (revIdx (⟨i.val, hi⟩ : Fin n)).val := by
    rw [orig_revIdx]
    exact hj
  have hspec := build_spec hn H0 H1 hdiag n le_rfl
    (revIdx (⟨i.val, hi⟩ : Fin n)) jj hjt
  have hfin : (⟨n - 1 - (revIdx (⟨i.val, hi⟩ : Fin n)).val, by omega⟩ : Fin n)
      = ⟨i.val, hi⟩ := by
    apply Fin.ext
    show n - 1 - (revIdx (⟨i.val, hi⟩ : Fin n)).val = i.val
    rw [orig_revIdx]
  have hcast : Fin.castLE hn (⟨n - 1 - (revIdx (⟨i.val, hi⟩ : Fin n)).val,
      by omega⟩ : Fin n) = i := by
    rw [hfin]
    exact hjeq
  rw [hcast] at hspec
  have hcolH1 : col H1 (Fin.castLE hn jj) = col H1 j := by rw [hjj]
  rw [hcolH1] at hspec
  dsimp only [finalVec]
  exact hspec

/-- Under the first-`n` unit-diagonal pairing hypothesis, there is a matrix with independent
first `n` columns preserving both `lwtr (H0ᵀ * H1)` and `diagMat (H0ᵀ * H1)`. See [Knill and
Laflamme, Lemma 10][KnillLaflamme1999]. -/
theorem lemma10 (hn : n ≤ N) (H0 H1 : Matrix (Fin n) (Fin N) (ZMod 2))
    (hdiag : ∀ i : Fin n,
      (H0ᵀ * H1) (Fin.castLE hn i) (Fin.castLE hn i) = 1) :
    ∃ H2' : Matrix (Fin n) (Fin N) (ZMod 2),
      LinearIndependent (ZMod 2)
        (fun i : Fin n => fun r => H2' r (Fin.castLE hn i)) ∧
      lwtr (H2'ᵀ * H1) = lwtr (H0ᵀ * H1) ∧
      diagMat (H2'ᵀ * H1) = diagMat (H0ᵀ * H1) := by
  classical
  refine ⟨H2mat H0 (finalVec hn H0 H1 hdiag), ?_, ?_, ?_⟩
  · have hcol : (fun i : Fin n => (fun r => H2mat H0 (finalVec hn H0 H1 hdiag) r
        (Fin.castLE hn i))) = finalVec hn H0 H1 hdiag := by
      funext i
      exact H2mat_castLE hn H0 _ i
    rw [hcol]
    exact finalVec_linIndep hn H0 H1 hdiag
  · ext i j
    simp only [lwtr]
    by_cases hji : j < i
    · rw [ite_eq_left hji, ite_eq_left hji, col_dot, col_dot]
      by_cases hi : i.val < n
      · have hcol2 : col (H2mat H0 (finalVec hn H0 H1 hdiag)) i =
            finalVec hn H0 H1 hdiag ⟨i.val, hi⟩ := by
          funext r
          show (if h : i.val < n then finalVec hn H0 H1 hdiag ⟨i.val, h⟩ r
            else H0 r i) = finalVec hn H0 H1 hdiag ⟨i.val, hi⟩ r
          rw [dite_eq_left hi]
        rw [hcol2]
        have hjlt : j.val < n := by
          have : j.val < i.val := hji
          omega
        let t : Fin n := revIdx ⟨i.val, hi⟩
        let j' : Fin n := ⟨j.val, hjlt⟩
        have hjt : j'.val ≤ n - 1 - t.val := by
          dsimp only [t, j']
          rw [orig_revIdx]
          exact le_of_lt hji
        have hspec := build_spec hn H0 H1 hdiag n le_rfl t j' hjt
        have htj : (Fin.castLE hn j') = j := Fin.ext rfl
        have hidx : Fin.castLE hn (⟨n - 1 - t.val, by omega⟩ : Fin n) = i := by
          apply Fin.ext
          show n - 1 - t.val = i.val
          dsimp only [t]
          rw [orig_revIdx]
        have hcolH0 : col H0 (Fin.castLE hn (⟨n - 1 - t.val, by omega⟩ : Fin n))
            = col H0 i := by rw [hidx]
        rw [htj, hcolH0] at hspec
        rw [dotProduct_comm (col H1 j) (build hn H0 H1 hdiag n t),
            dotProduct_comm (col H1 j) (col H0 i)] at hspec
        change build hn H0 H1 hdiag n t ⬝ᵥ col H1 j = col H0 i ⬝ᵥ col H1 j
        exact hspec
      · have hcol2 : col (H2mat H0 (finalVec hn H0 H1 hdiag)) i = col H0 i := by
          funext r
          show (if h : i.val < n then finalVec hn H0 H1 hdiag ⟨i.val, h⟩ r
            else H0 r i) = col H0 i r
          rw [dite_eq_right hi]
          rfl
        rw [hcol2]
    · rw [ite_eq_right hji, ite_eq_right hji]
  · ext i j
    simp only [diagMat]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ite_eq_left rfl, col_dot, col_dot]
      by_cases hi : i.val < n
      · have hcol2 : col (H2mat H0 (finalVec hn H0 H1 hdiag)) i =
            finalVec hn H0 H1 hdiag ⟨i.val, hi⟩ := by
          funext r
          show (if h : i.val < n then finalVec hn H0 H1 hdiag ⟨i.val, h⟩ r
            else H0 r i) = finalVec hn H0 H1 hdiag ⟨i.val, hi⟩ r
          rw [dite_eq_left hi]
        rw [hcol2]
        let t : Fin n := revIdx ⟨i.val, hi⟩
        let ii : Fin n := ⟨i.val, hi⟩
        have hcast : Fin.castLE hn ii = i := Fin.ext rfl
        have hjt : ii.val ≤ n - 1 - t.val := by
          dsimp only [t, ii]
          rw [orig_revIdx]
        have hspec := build_spec hn H0 H1 hdiag n le_rfl t ii hjt
        have hidx : Fin.castLE hn (⟨n - 1 - t.val, by omega⟩ : Fin n) = i := by
          apply Fin.ext
          show n - 1 - t.val = i.val
          dsimp only [t]
          rw [orig_revIdx]
        have hcolH0 : col H0 (Fin.castLE hn (⟨n - 1 - t.val, by omega⟩ : Fin n))
            = col H0 i := by rw [hidx]
        rw [hcast, hcolH0] at hspec
        rw [dotProduct_comm (col H1 i) (build hn H0 H1 hdiag n t),
            dotProduct_comm (col H1 i) (col H0 i)] at hspec
        change build hn H0 H1 hdiag n t ⬝ᵥ col H1 i = col H0 i ⬝ᵥ col H1 i
        exact hspec
      · have hcol2 : col (H2mat H0 (finalVec hn H0 H1 hdiag)) i = col H0 i := by
          funext r
          show (if h : i.val < n then finalVec hn H0 H1 hdiag ⟨i.val, h⟩ r
            else H0 r i) = col H0 i r
          rw [dite_eq_right hi]
          rfl
        rw [hcol2]
    · rw [ite_eq_right hij, ite_eq_right hij]

end Build

end Qatlib.Papers.SignedWtEnum99.MainResults
