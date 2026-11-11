/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ElemGates95.MultiControl.Section7.LowerBound
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates

/-!
# CNOT lower bound for fully controlled gates

This module connects wire-graph sparsity to matrix factorization and proves the CNOT lower bound
of Lemma 7.7 in [BarencoEtAl1995]. `cutSplit`, `kronAcross`, and `FactorsAcross` express a
register and its matrices across a wire partition. Single-wire gates and CNOTs supported on one
side factor across the partition, so `reflectionProgramMatrix_factors` extends this property to
a whole gate list.

The matrix `multiCtrlGate` applies `U` to its target when every other wire is true. For
nonscalar `U`, `multiCtrlGate_not_factors` rules out factorization across every nontrivial
partition. The interaction graph `cnotGraph` then turns a hypothetical program with fewer than
`n - 1` CNOT occurrences into an impossible uncrossed cut, yielding `lemma77_lower_bound` for
exact matrix equality.

## Main statements

* `reflectionProgramMatrix_factors` factors any program whose gates stay within the two sides of
  a cut.
* `multiCtrlGate_not_factors` proves the obstruction for a fully controlled nonscalar matrix.
* `exists_uncrossed_cut_of_sparse` extracts a cut from a small CNOT count.
* `lemma77_lower_bound` proves `n - 1 <= cnotCount gs` for an exact implementation.

## References

* [Barenco et al., 1995][BarencoEtAl1995], Section 7, Lemma 7.7.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open scoped BigOperators

namespace Qatlib.Papers.ElemGates95.MultiControl.Section7

/-- The type of Boolean register assignments on the wires belonging to `A`. -/
abbrev RegA {n : ℕ} (A : Finset (Fin n)) := {i : Fin n // i ∈ A} → Bool

/-- The type of Boolean register assignments on the wires outside `A`. -/
abbrev RegB {n : ℕ} (A : Finset (Fin n)) := {i : Fin n // i ∉ A} → Bool

/-- The equivalence splitting a full Boolean register into its restrictions to `A` and its
complement. -/
noncomputable def cutSplit {n : ℕ} (A : Finset (Fin n)) : Reg n ≃ (RegA A × RegB A) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin n => i ∈ A) (fun _ => Bool)

/-- The first component of `cutSplit A x` is the restriction of `x` to the wires in `A`. -/
@[simp] theorem cutSplit_apply_fst {n : ℕ} (A : Finset (Fin n)) (x : Reg n) :
    (cutSplit A x).1 = fun i : {i : Fin n // i ∈ A} => x i.1 := rfl

/-- The second component of `cutSplit A x` is the restriction of `x` to the wires outside `A`. -/
@[simp] theorem cutSplit_apply_snd {n : ℕ} (A : Finset (Fin n)) (x : Reg n) :
    (cutSplit A x).2 = fun i : {i : Fin n // i ∉ A} => x i.1 := rfl

/-- Recombining two partial registers uses the `A` component at a wire in `A` and the
complementary component at every other wire. -/
theorem cutSplit_symm_apply {n : ℕ} (A : Finset (Fin n)) (a : RegA A) (b : RegB A)
    (i : Fin n) : (cutSplit A).symm (a, b) i = if h : i ∈ A then a ⟨i, h⟩ else b ⟨i, h⟩ :=
  rfl

/-- Recombining partial registers recovers the first partial register on every wire in `A`. -/
@[simp] theorem cutSplit_symm_fst {n : ℕ} (A : Finset (Fin n)) (a : RegA A) (b : RegB A)
    (i : {i : Fin n // i ∈ A}) : (cutSplit A).symm (a, b) i.1 = a i := by
  rw [cutSplit_symm_apply, dif_pos i.2]

/-- Recombining partial registers recovers the second partial register on every wire outside
`A`. -/
@[simp] theorem cutSplit_symm_snd {n : ℕ} (A : Finset (Fin n)) (a : RegA A) (b : RegB A)
    (i : {i : Fin n // i ∉ A}) : (cutSplit A).symm (a, b) i.1 = b i := by
  rw [cutSplit_symm_apply, dif_neg i.2]

/-- The tensor product of matrices on the two sides of a wire partition, expressed in
full-register coordinates through `cutSplit`. -/
noncomputable def kronAcross {n : ℕ} (A : Finset (Fin n))
    (MA : Matrix (RegA A) (RegA A) ℂ) (MB : Matrix (RegB A) (RegB A) ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  fun x y => MA (cutSplit A x).1 (cutSplit A y).1 * MB (cutSplit A x).2 (cutSplit A y).2

/-- The property that a full-register matrix is a tensor product of two matrices acting on the
two sides of the partition. -/
def FactorsAcross {n : ℕ} (A : Finset (Fin n)) (M : Matrix (Reg n) (Reg n) ℂ) : Prop :=
  ∃ MA MB, M = kronAcross A MA MB

/-- An entry of `kronAcross A MA MB` is the product of the corresponding entries of `MA` and
`MB` after splitting both register indices. -/
theorem kronAcross_apply {n : ℕ} (A : Finset (Fin n))
    (MA : Matrix (RegA A) (RegA A) ℂ) (MB : Matrix (RegB A) (RegB A) ℂ)
    (x y : Reg n) :
    kronAcross A MA MB x y = MA (cutSplit A x).1 (cutSplit A y).1 *
      MB (cutSplit A x).2 (cutSplit A y).2 := rfl

/-- Multiplying two tensor products across the same wire partition multiplies their respective
factors. -/
theorem kronAcross_mul {n : ℕ} (A : Finset (Fin n))
    (MA MA' : Matrix (RegA A) (RegA A) ℂ) (MB MB' : Matrix (RegB A) (RegB A) ℂ) :
    kronAcross A MA MB * kronAcross A MA' MB' = kronAcross A (MA * MA') (MB * MB') := by
  ext x y
  rw [Matrix.mul_apply, kronAcross_apply, Matrix.mul_apply, Matrix.mul_apply]
  rw [← Equiv.sum_comp (cutSplit A).symm
    (fun z => kronAcross A MA MB x z * kronAcross A MA' MB' z y)]
  rw [Fintype.sum_prod_type]
  simp only [kronAcross_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The tensor product of the identity matrices on the two sides of a wire partition is the
full-register identity. -/
theorem kronAcross_one {n : ℕ} (A : Finset (Fin n)) :
    kronAcross A (1 : Matrix (RegA A) (RegA A) ℂ) (1 : Matrix (RegB A) (RegB A) ℂ) = 1 := by
  ext x y
  rw [kronAcross_apply, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  simp only [cutSplit_apply_fst, cutSplit_apply_snd]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hnot :
        (fun i : {i : Fin n // i ∈ A} => x i.1) ≠ (fun i : {i : Fin n // i ∈ A} => y i.1) ∨
          (fun j : {j : Fin n // j ∉ A} => x j.1) ≠
            (fun j : {j : Fin n // j ∉ A} => y j.1) := by
      by_contra hc
      rw [not_or] at hc
      push Not at hc
      exact hxy (funext fun k => by
        by_cases hk : k ∈ A
        · exact congrFun hc.1 ⟨k, hk⟩
        · exact congrFun hc.2 ⟨k, hk⟩)
    rcases hnot with h | h
    · simp [h, hxy]
    · simp [h, hxy]

/-- The matrix applying `U` to a specified wire in the partial register on `A` while preserving
its other wires. -/
noncomputable def wireGateA {n : ℕ} (A : Finset (Fin n)) (w : Fin n) (hw : w ∈ A)
    (U : Matrix Bool Bool ℂ) : Matrix (RegA A) (RegA A) ℂ :=
  fun a a' =>
    if ∀ i : {i : Fin n // i ∈ A}, i.1 ≠ w → a i = a' i then
      U (a ⟨w, hw⟩) (a' ⟨w, hw⟩)
    else 0

/-- A single-wire matrix supported in `A` factors as its restricted matrix on `A` tensored with
the identity on the complement. -/
theorem wireGate_factors_mem {n : ℕ} (A : Finset (Fin n)) (w : Fin n) (hw : w ∈ A)
    (U : Matrix Bool Bool ℂ) :
    wireGate n w U = kronAcross A (wireGateA A w hw U) (1 : Matrix (RegB A) (RegB A) ℂ) := by
  ext x y
  rw [wireGate_apply, kronAcross_apply, Matrix.one_apply]
  simp only [cutSplit_apply_fst, cutSplit_apply_snd, wireGateA]
  by_cases h : ∀ k : Fin n, k ≠ w → x k = y k
  · have hA : ∀ i : {i : Fin n // i ∈ A}, i.1 ≠ w → x i.1 = y i.1 :=
      fun i hi => h i.1 hi
    have hB : (fun j : {j : Fin n // j ∉ A} => x j.1) =
        (fun j : {j : Fin n // j ∉ A} => y j.1) := by
      funext j
      exact h j.1 (fun hwj => j.2 (hwj ▸ hw))
    rw [if_pos h, if_pos hA, if_pos hB, mul_one]
  · have hR : ¬ (∀ k : Fin n, k ≠ w → x k = y k) := h
    rw [if_neg hR]
    push Not at h
    obtain ⟨k, hkw, hkxy⟩ := h
    by_cases hkA : k ∈ A
    · have hne : ¬ (∀ i : {i : Fin n // i ∈ A}, i.1 ≠ w → x i.1 = y i.1) := by
        intro hall
        exact hkxy (hall ⟨k, hkA⟩ hkw)
      rw [if_neg hne, zero_mul]
    · have hBne : (fun j : {j : Fin n // j ∉ A} => x j.1) ≠
          (fun j : {j : Fin n // j ∉ A} => y j.1) := by
        intro he
        exact hkxy (congrFun he ⟨k, hkA⟩)
      rw [if_neg hBne, mul_zero]

/-- The matrix applying `U` to a specified wire in the partial register outside `A` while
preserving its other wires. -/
noncomputable def wireGateB {n : ℕ} (A : Finset (Fin n)) (w : Fin n) (hw : w ∉ A)
    (U : Matrix Bool Bool ℂ) : Matrix (RegB A) (RegB A) ℂ :=
  fun b b' =>
    if ∀ j : {j : Fin n // j ∉ A}, j.1 ≠ w → b j = b' j then
      U (b ⟨w, hw⟩) (b' ⟨w, hw⟩)
    else 0

/-- A single-wire matrix supported outside `A` factors as the identity on `A` tensored with its
restricted matrix on the complement. -/
theorem wireGate_factors_not_mem {n : ℕ} (A : Finset (Fin n)) (w : Fin n) (hw : w ∉ A)
    (U : Matrix Bool Bool ℂ) :
    wireGate n w U = kronAcross A (1 : Matrix (RegA A) (RegA A) ℂ) (wireGateB A w hw U) := by
  ext x y
  rw [wireGate_apply, kronAcross_apply, Matrix.one_apply]
  simp only [cutSplit_apply_fst, cutSplit_apply_snd, wireGateB]
  by_cases h : ∀ k : Fin n, k ≠ w → x k = y k
  · have hA : (fun i : {i : Fin n // i ∈ A} => x i.1) =
        (fun i : {i : Fin n // i ∈ A} => y i.1) := by
      funext i
      exact h i.1 (fun hwi => hw (hwi ▸ i.2))
    have hB : ∀ j : {j : Fin n // j ∉ A}, j.1 ≠ w → x j.1 = y j.1 :=
      fun j hj => h j.1 hj
    rw [if_pos h, if_pos hA, if_pos hB, one_mul]
  · have hR : ¬ (∀ k : Fin n, k ≠ w → x k = y k) := h
    rw [if_neg hR]
    push Not at h
    obtain ⟨k, hkw, hkxy⟩ := h
    by_cases hkA : k ∈ A
    · have hAne : (fun i : {i : Fin n // i ∈ A} => x i.1) ≠
          (fun i : {i : Fin n // i ∈ A} => y i.1) := by
        intro he
        exact hkxy (congrFun he ⟨k, hkA⟩)
      rw [if_neg hAne, zero_mul]
    · have hne : ¬ (∀ j : {j : Fin n // j ∉ A}, j.1 ≠ w → x j.1 = y j.1) := by
        intro hall
        exact hkxy (hall ⟨k, hkA⟩ hkw)
      rw [if_neg hne, mul_zero]

/-- Updating a full register at a wire in `A` is equivalent to updating its restriction to `A`
and leaving its complementary restriction unchanged. -/
theorem update_split_mem {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A)
    (x y : Reg n) (v : Bool) :
    x = Function.update y t v ↔
      ((fun i : {i : Fin n // i ∈ A} => x i.1) =
        Function.update (fun i : {i : Fin n // i ∈ A} => y i.1) ⟨t, ht⟩ v ∧
      (fun j : {j : Fin n // j ∉ A} => x j.1) = (fun j : {j : Fin n // j ∉ A} => y j.1)) := by
  rw [funext_iff]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [funext_iff]; intro i
      rw [hx i.1, Function.update_apply, Function.update_apply]
      by_cases hit : i.1 = t
      · have hi : i = ⟨t, ht⟩ := Subtype.ext hit
        rw [if_pos hit, if_pos hi]
      · have hi : ¬ (i = ⟨t, ht⟩) := fun h => hit (congrArg Subtype.val h)
        rw [if_neg hit, if_neg hi]
    · rw [funext_iff]; intro j
      rw [hx j.1, Function.update_apply, if_neg]
      intro hjt
      exact j.2 (by rw [hjt]; exact ht)
  · rintro ⟨hA, hB⟩
    intro k
    rw [Function.update_apply]
    by_cases hk : k ∈ A
    · have hkA := congrFun hA ⟨k, hk⟩
      rw [Function.update_apply] at hkA
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos (Subtype.ext rfl)] at hkA
        rw [if_pos rfl]
        exact hkA
      · have hne : ¬ ((⟨k, hk⟩ : {i : Fin n // i ∈ A}) = ⟨t, ht⟩) :=
          fun h => hkt (congrArg Subtype.val h)
        rw [if_neg hne] at hkA
        rw [if_neg hkt]
        exact hkA
    · have hkB := congrFun hB ⟨k, hk⟩
      have hkt : k ≠ t := fun h => hk (by rw [h]; exact ht)
      rw [if_neg hkt]
      exact hkB

/-- Updating a full register at a wire outside `A` is equivalent to leaving its restriction to
`A` unchanged and updating its complementary restriction. -/
theorem update_split_not_mem {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∉ A)
    (x y : Reg n) (v : Bool) :
    x = Function.update y t v ↔
      ((fun i : {i : Fin n // i ∈ A} => x i.1) = (fun i : {i : Fin n // i ∈ A} => y i.1) ∧
      (fun j : {j : Fin n // j ∉ A} => x j.1) =
        Function.update (fun j : {j : Fin n // j ∉ A} => y j.1) ⟨t, ht⟩ v) := by
  rw [funext_iff]
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [funext_iff]; intro i
      rw [hx i.1, Function.update_apply, if_neg]
      intro hit
      exact ht (hit ▸ i.2)
    · rw [funext_iff]; intro j
      rw [hx j.1, Function.update_apply, Function.update_apply]
      by_cases hjt : j.1 = t
      · have hj : j = ⟨t, ht⟩ := Subtype.ext hjt
        rw [if_pos hjt, if_pos hj]
      · have hj : ¬ (j = ⟨t, ht⟩) := fun h => hjt (congrArg Subtype.val h)
        rw [if_neg hjt, if_neg hj]
  · rintro ⟨hA, hB⟩
    intro k
    rw [Function.update_apply]
    by_cases hk : k ∈ A
    · have hkA := congrFun hA ⟨k, hk⟩
      have hkt : k ≠ t := fun h => ht (h ▸ hk)
      rw [if_neg hkt]
      exact hkA
    · have hkB := congrFun hB ⟨k, hk⟩
      rw [Function.update_apply] at hkB
      by_cases hkt : k = t
      · subst hkt
        rw [if_pos (Subtype.ext rfl)] at hkB
        rw [if_pos rfl]
        exact hkB
      · have hne : ¬ ((⟨k, hk⟩ : {j : Fin n // j ∉ A}) = ⟨t, ht⟩) :=
          fun h => hkt (congrArg Subtype.val h)
        rw [if_neg hne] at hkB
        rw [if_neg hkt]
        exact hkB

/-- The target-XOR-control matrix on the partial register over `A`, with both designated wires
belonging to `A`. -/
noncomputable def cnotGateA {n : ℕ} (A : Finset (Fin n)) (c t : Fin n)
    (hc : c ∈ A) (ht : t ∈ A) : Matrix (RegA A) (RegA A) ℂ :=
  permMatrix fun a : RegA A =>
    Function.update a ⟨t, ht⟩ (a ⟨t, ht⟩ ^^ a ⟨c, hc⟩)

/-- A CNOT matrix whose control and target lie in `A` factors as the corresponding restricted
matrix tensored with the complementary identity. -/
theorem cnotGate_factors_mem {n : ℕ} (A : Finset (Fin n)) (c t : Fin n)
    (hc : c ∈ A) (ht : t ∈ A) :
    cnotGate n c t = kronAcross A (cnotGateA A c t hc ht) (1 : Matrix (RegB A) (RegB A) ℂ) := by
  ext x y
  rw [cnotGate, permMatrix, kronAcross_apply, Matrix.one_apply]
  simp only [cutSplit_apply_fst, cutSplit_apply_snd, cnotGateA, permMatrix, Matrix.of_apply]
  have key := update_split_mem A t ht x y (y t ^^ y c)
  by_cases hx : x = Function.update y t (y t ^^ y c)
  · rw [if_pos hx, if_pos (key.mp hx).1, if_pos (key.mp hx).2, mul_one]
  · rw [if_neg hx]
    rcases Classical.em ((fun i : {i : Fin n // i ∈ A} => x i.1) =
        Function.update (fun i : {i : Fin n // i ∈ A} => y i.1) ⟨t, ht⟩
          ((fun i : {i : Fin n // i ∈ A} => y i.1) ⟨t, ht⟩ ^^
            (fun i : {i : Fin n // i ∈ A} => y i.1) ⟨c, hc⟩)) with hA | hA
    · rcases Classical.em ((fun j : {j : Fin n // j ∉ A} => x j.1) =
          (fun j : {j : Fin n // j ∉ A} => y j.1)) with hB | hB
      · exact absurd (key.mpr ⟨hA, hB⟩) hx
      · rw [if_pos hA, if_neg hB, mul_zero]
    · rw [if_neg hA, zero_mul]

/-- The target-XOR-control matrix on the partial register outside `A`, with both designated
wires outside `A`. -/
noncomputable def cnotGateB {n : ℕ} (A : Finset (Fin n)) (c t : Fin n)
    (hc : c ∉ A) (ht : t ∉ A) : Matrix (RegB A) (RegB A) ℂ :=
  permMatrix fun b : RegB A =>
    Function.update b ⟨t, ht⟩ (b ⟨t, ht⟩ ^^ b ⟨c, hc⟩)

/-- A CNOT matrix whose control and target lie outside `A` factors as the identity on `A`
tensored with the corresponding restricted matrix. -/
theorem cnotGate_factors_not_mem {n : ℕ} (A : Finset (Fin n)) (c t : Fin n)
    (hc : c ∉ A) (ht : t ∉ A) :
    cnotGate n c t = kronAcross A (1 : Matrix (RegA A) (RegA A) ℂ) (cnotGateB A c t hc ht) := by
  ext x y
  rw [cnotGate, permMatrix, kronAcross_apply, Matrix.one_apply]
  simp only [cutSplit_apply_fst, cutSplit_apply_snd, cnotGateB, permMatrix, Matrix.of_apply]
  have key := update_split_not_mem A t ht x y (y t ^^ y c)
  by_cases hx : x = Function.update y t (y t ^^ y c)
  · rw [if_pos hx, if_pos (key.mp hx).1, if_pos (key.mp hx).2, one_mul]
  · rw [if_neg hx]
    rcases Classical.em (((fun i : {i : Fin n // i ∈ A} => x i.1) =
        (fun i : {i : Fin n // i ∈ A} => y i.1))) with hA | hA
    · rcases Classical.em ((fun j : {j : Fin n // j ∉ A} => x j.1) =
          Function.update (fun j : {j : Fin n // j ∉ A} => y j.1) ⟨t, ht⟩
            ((fun j : {j : Fin n // j ∉ A} => y j.1) ⟨t, ht⟩ ^^
              (fun j : {j : Fin n // j ∉ A} => y j.1) ⟨c, hc⟩)) with hB | hB
      · exact absurd (key.mpr ⟨hA, hB⟩) hx
      · rw [if_pos hA, if_neg hB, mul_zero]
    · rw [if_neg hA, zero_mul]

/-- The matrix of a reflection-vocabulary gate factors across `A` whenever every wire used by
the gate belongs to `A`. -/
theorem reflectionGateMatrix_factors_of_subset {n : ℕ} {A : Finset (Fin n)}
    {g : ReflectionGate n} (h : reflectionGateWires g ⊆ A) :
    FactorsAcross A (reflectionGateMatrix g) := by
  cases g with
  | inl p =>
      obtain ⟨w, U⟩ := p
      have hw : w ∈ A :=
        h (by simp [reflectionGateWires])
      exact ⟨wireGateA A w hw U, 1, wireGate_factors_mem A w hw U⟩
  | inr p =>
      obtain ⟨c, t⟩ := p
      have hc : c ∈ A := h (by simp [reflectionGateWires])
      have ht : t ∈ A := h (by simp [reflectionGateWires])
      exact ⟨cnotGateA A c t hc ht, 1, cnotGate_factors_mem A c t hc ht⟩

/-- The matrix of a reflection-vocabulary gate factors across `A` whenever its wire set is
disjoint from `A`. -/
theorem reflectionGateMatrix_factors_of_disjoint {n : ℕ} {A : Finset (Fin n)}
    {g : ReflectionGate n} (h : Disjoint (reflectionGateWires g) A) :
    FactorsAcross A (reflectionGateMatrix g) := by
  have h' : ∀ x ∈ reflectionGateWires g, x ∉ A :=
    fun x hx => Finset.disjoint_left.mp h hx
  cases g with
  | inl p =>
      obtain ⟨w, U⟩ := p
      have hw : w ∉ A := h' w (by simp [reflectionGateWires])
      exact ⟨1, wireGateB A w hw U, wireGate_factors_not_mem A w hw U⟩
  | inr p =>
      obtain ⟨c, t⟩ := p
      have hc : c ∉ A := h' c (by simp [reflectionGateWires])
      have ht : t ∉ A := h' t (by simp [reflectionGateWires])
      exact ⟨1, cnotGateB A c t hc ht, cnotGate_factors_not_mem A c t hc ht⟩

/-- A program matrix factors across `A` if each gate uses wires entirely in `A` or entirely
outside `A`. -/
theorem reflectionProgramMatrix_factors {n : ℕ} {A : Finset (Fin n)}
    {gs : List (ReflectionGate n)}
    (h : ∀ g ∈ gs, reflectionGateWires g ⊆ A ∨ Disjoint (reflectionGateWires g) A) :
    FactorsAcross A (reflectionProgramMatrix gs) := by
  induction gs with
  | nil =>
      refine ⟨1, 1, ?_⟩
      rw [reflectionProgramMatrix]
      exact (kronAcross_one A).symm
  | cons g gs ih =>
      rw [reflectionProgramMatrix]
      have ih' : FactorsAcross A (reflectionProgramMatrix gs) :=
        ih (fun x hx => h x (by simp [hx]))
      have hg : FactorsAcross A (reflectionGateMatrix g) := by
        rcases h g (by simp) with hs | hd
        · exact reflectionGateMatrix_factors_of_subset hs
        · exact reflectionGateMatrix_factors_of_disjoint hd
      obtain ⟨MA₁, MB₁, h1⟩ := ih'
      obtain ⟨MA₂, MB₂, h2⟩ := hg
      exact ⟨MA₁ * MA₂, MB₁ * MB₂, by rw [h1, h2, kronAcross_mul]⟩

/-- The full-register matrix applying `U` to target `t` precisely when every other wire is true,
while preserving all control wires. -/
noncomputable def multiCtrlGate {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ) :
    Matrix (Reg n) (Reg n) ℂ :=
  fun x y =>
    if (∀ k : Fin n, k ≠ t → x k = y k) then
      (if (∀ k : Fin n, k ≠ t → x k = true) then U (x t) (y t)
        else (1 : Matrix Bool Bool ℂ) (x t) (y t))
    else 0

/-- Gives the entries of the fully controlled matrix by testing control-register agreement and
whether all controls are true. -/
theorem multiCtrlGate_apply {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ) (x y : Reg n) :
    multiCtrlGate t U x y =
      if (∀ k : Fin n, k ≠ t → x k = y k) then
        (if (∀ k : Fin n, k ≠ t → x k = true) then U (x t) (y t)
          else (1 : Matrix Bool Bool ℂ) (x t) (y t))
      else 0 := rfl

/-- When the two register indices agree off the target and every control is true, the matrix
entry is the corresponding entry of `U`. -/
theorem multiCtrlGate_apply_ctrl {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ)
    {x y : Reg n} (hxy : ∀ k : Fin n, k ≠ t → x k = y k)
    (hx : ∀ k : Fin n, k ≠ t → x k = true) :
    multiCtrlGate t U x y = U (x t) (y t) := by
  rw [multiCtrlGate_apply, if_pos hxy, if_pos hx]

/-- When the two register indices agree off the target but some control is false, the matrix
entry is the corresponding entry of the target identity matrix. -/
theorem multiCtrlGate_apply_id {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ)
    {x y : Reg n} (hxy : ∀ k : Fin n, k ≠ t → x k = y k)
    (hx : ¬ ∀ k : Fin n, k ≠ t → x k = true) :
    multiCtrlGate t U x y = (1 : Matrix Bool Bool ℂ) (x t) (y t) := by
  rw [multiCtrlGate_apply, if_pos hxy, if_neg hx]

/-- The partial register on `A` with every wire true. -/
def allTrueA {n : ℕ} (A : Finset (Fin n)) : RegA A := fun _ => true

/-- The partial register outside `A` with every wire true. -/
def allTrueB {n : ℕ} (A : Finset (Fin n)) : RegB A := fun _ => true

/-- The partial register on `A` taking value `b` at the designated target and true at every
other wire. -/
def ctrlA {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (_ht : t ∈ A) (b : Bool) : RegA A :=
  fun i => if i.1 = t then b else true

/-- The partial register outside `A` taking value `b` at the designated target and true at every
other wire. -/
def ctrlB {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (_ht : t ∉ A) (b : Bool) : RegB A :=
  fun j => if j.1 = t then b else true

/-- The partial register on `A` taking value false at the designated control and true at every
other wire. -/
def toggleA {n : ℕ} (A : Finset (Fin n)) (c : Fin n) (_hc : c ∈ A) : RegA A :=
  fun i => if i.1 = c then false else true

/-- The partial register outside `A` taking value false at the designated control and true at
every other wire. -/
def toggleB {n : ℕ} (A : Finset (Fin n)) (c : Fin n) (_hc : c ∉ A) : RegB A :=
  fun j => if j.1 = c then false else true

/-- Combining `ctrlA` with the all-true complementary register gives value `b` at the designated
target in `A`. -/
theorem symm_ctrlA_allTrueB_at {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A)
    (b : Bool) :
    (cutSplit A).symm (ctrlA A t ht b, allTrueB A) t = b := by
  rw [cutSplit_symm_apply, dif_pos ht]
  show (if t = t then b else true) = b
  simp

/-- Combining `ctrlA` with the all-true complementary register gives true at every wire other
than the designated target. -/
theorem symm_ctrlA_allTrueB_of_ne {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A)
    (b : Bool) {k : Fin n} (hk : k ≠ t) :
    (cutSplit A).symm (ctrlA A t ht b, allTrueB A) k = true := by
  rw [cutSplit_symm_apply]
  by_cases hkA : k ∈ A
  · rw [dif_pos hkA]
    show (if k = t then b else true) = true
    simp [hk]
  · rw [dif_neg hkA]
    rfl

/-- Combining `ctrlA` with a complementary register having one false control preserves value `b`
at the target in `A`. -/
theorem symm_ctrlA_toggleB_at {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A)
    (c : Fin n) (hc : c ∉ A) (b : Bool) :
    (cutSplit A).symm (ctrlA A t ht b, toggleB A c hc) t = b := by
  rw [cutSplit_symm_apply, dif_pos ht]
  show (if t = t then b else true) = b
  simp

/-- Combining `ctrlA` with `toggleB` gives false at the designated complementary control. -/
theorem symm_ctrlA_toggleB_at_c {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A)
    (c : Fin n) (hc : c ∉ A) (b : Bool) :
    (cutSplit A).symm (ctrlA A t ht b, toggleB A c hc) c = false := by
  rw [cutSplit_symm_apply, dif_neg hc]
  show (if c = c then false else true) = false
  simp

/-- Combining `ctrlA` with `toggleB` gives true at every wire distinct from both the target and
the designated false control. -/
theorem symm_ctrlA_toggleB_of_ne {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∈ A)
    (c : Fin n) (hc : c ∉ A) (b : Bool) {k : Fin n} (hk : k ≠ t) (hkc : k ≠ c) :
    (cutSplit A).symm (ctrlA A t ht b, toggleB A c hc) k = true := by
  rw [cutSplit_symm_apply]
  by_cases hkA : k ∈ A
  · rw [dif_pos hkA]
    show (if k = t then b else true) = true
    simp [hk]
  · rw [dif_neg hkA]
    show (if k = c then false else true) = true
    simp [hkc]

/-- Combining the all-true register on `A` with `ctrlB` gives value `b` at the designated target
outside `A`. -/
theorem symm_allTrueA_ctrlB_at {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∉ A)
    (b : Bool) :
    (cutSplit A).symm (allTrueA A, ctrlB A t ht b) t = b := by
  rw [cutSplit_symm_apply, dif_neg ht]
  show (if t = t then b else true) = b
  simp

/-- Combining the all-true register on `A` with `ctrlB` gives true at every wire other than the
designated target. -/
theorem symm_allTrueA_ctrlB_of_ne {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∉ A)
    (b : Bool) {k : Fin n} (hk : k ≠ t) :
    (cutSplit A).symm (allTrueA A, ctrlB A t ht b) k = true := by
  rw [cutSplit_symm_apply]
  by_cases hkA : k ∈ A
  · rw [dif_pos hkA]
    rfl
  · rw [dif_neg hkA]
    show (if k = t then b else true) = true
    simp [hk]

/-- Combining `toggleA` with `ctrlB` preserves value `b` at the designated target outside `A`. -/
theorem symm_toggleA_ctrlB_at {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∉ A)
    (c : Fin n) (hc : c ∈ A) (b : Bool) :
    (cutSplit A).symm (toggleA A c hc, ctrlB A t ht b) t = b := by
  rw [cutSplit_symm_apply, dif_neg ht]
  show (if t = t then b else true) = b
  simp

/-- Combining `toggleA` with `ctrlB` gives false at the designated control in `A`. -/
theorem symm_toggleA_ctrlB_at_c {n : ℕ} (A : Finset (Fin n)) (t : Fin n) (ht : t ∉ A)
    (c : Fin n) (hc : c ∈ A) (b : Bool) :
    (cutSplit A).symm (toggleA A c hc, ctrlB A t ht b) c = false := by
  rw [cutSplit_symm_apply, dif_pos hc]
  show (if c = c then false else true) = false
  simp

/-- For nonscalar `U`, the fully controlled matrix cannot factor across any partition having
wires on both sides. This supplies the matrix obstruction needed in the proof of Lemma 7.7
of [BarencoEtAl1995]. -/
theorem multiCtrlGate_not_factors {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ)
    (hU : ¬ IsScalar U) {A : Finset (Fin n)} (hA : A.Nonempty) (hB : ∃ i, i ∉ A) :
    ¬ FactorsAcross A (multiCtrlGate t U) := by
  rintro ⟨MA, MB, hM⟩
  have hentry : ∀ (a a' : RegA A) (b b' : RegB A),
      multiCtrlGate t U ((cutSplit A).symm (a, b)) ((cutSplit A).symm (a', b')) =
        MA a a' * MB b b' := by
    intro a a' b b'
    rw [hM, kronAcross_apply]
    simp only [Equiv.apply_symm_apply]
  by_cases ht : t ∈ A
  · obtain ⟨c, hc⟩ := hB
    have hct : c ≠ t := fun h => hc (h ▸ ht)
    have hxq_b : ∀ b : Bool, ¬ ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (ctrlA A t ht b, toggleB A c hc)) k = true := by
      intro b hall
      have h := hall c hct
      rw [symm_ctrlA_toggleB_at_c A t ht c hc b] at h
      exact Bool.false_ne_true h
    have hxyq : ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (ctrlA A t ht false, toggleB A c hc)) k =
          ((cutSplit A).symm (ctrlA A t ht true, toggleB A c hc)) k := by
      intro k hk
      by_cases hkc : k = c
      · rw [hkc, symm_ctrlA_toggleB_at_c A t ht c hc false,
          symm_ctrlA_toggleB_at_c A t ht c hc true]
      · rw [symm_ctrlA_toggleB_of_ne A t ht c hc false hk hkc,
          symm_ctrlA_toggleB_of_ne A t ht c hc true hk hkc]
    have e_αP : U false false =
        MA (ctrlA A t ht false) (ctrlA A t ht false) * MB (allTrueB A) (allTrueB A) := by
      have h := hentry (ctrlA A t ht false) (ctrlA A t ht false) (allTrueB A) (allTrueB A)
      rw [multiCtrlGate_apply_ctrl t U (fun _ _ => rfl)
            (fun k hk => symm_ctrlA_allTrueB_of_ne A t ht false hk),
          symm_ctrlA_allTrueB_at A t ht false] at h
      exact h
    have e_βP : U true true =
        MA (ctrlA A t ht true) (ctrlA A t ht true) * MB (allTrueB A) (allTrueB A) := by
      have h := hentry (ctrlA A t ht true) (ctrlA A t ht true) (allTrueB A) (allTrueB A)
      rw [multiCtrlGate_apply_ctrl t U (fun _ _ => rfl)
            (fun k hk => symm_ctrlA_allTrueB_of_ne A t ht true hk),
          symm_ctrlA_allTrueB_at A t ht true] at h
      exact h
    have e_γP : U false true =
        MA (ctrlA A t ht false) (ctrlA A t ht true) * MB (allTrueB A) (allTrueB A) := by
      have h := hentry (ctrlA A t ht false) (ctrlA A t ht true) (allTrueB A) (allTrueB A)
      rw [multiCtrlGate_apply_ctrl t U
            (fun k hk => by
              rw [symm_ctrlA_allTrueB_of_ne A t ht false hk,
                symm_ctrlA_allTrueB_of_ne A t ht true hk])
            (fun k hk => symm_ctrlA_allTrueB_of_ne A t ht false hk),
          symm_ctrlA_allTrueB_at A t ht false, symm_ctrlA_allTrueB_at A t ht true] at h
      exact h
    have e_δP : U true false =
        MA (ctrlA A t ht true) (ctrlA A t ht false) * MB (allTrueB A) (allTrueB A) := by
      have h := hentry (ctrlA A t ht true) (ctrlA A t ht false) (allTrueB A) (allTrueB A)
      rw [multiCtrlGate_apply_ctrl t U
            (fun k hk => by
              rw [symm_ctrlA_allTrueB_of_ne A t ht true hk,
                symm_ctrlA_allTrueB_of_ne A t ht false hk])
            (fun k hk => symm_ctrlA_allTrueB_of_ne A t ht true hk),
          symm_ctrlA_allTrueB_at A t ht true, symm_ctrlA_allTrueB_at A t ht false] at h
      exact h
    have e_αQ : MA (ctrlA A t ht false) (ctrlA A t ht false) *
        MB (toggleB A c hc) (toggleB A c hc) = 1 := by
      have h := hentry (ctrlA A t ht false) (ctrlA A t ht false) (toggleB A c hc) (toggleB A c hc)
      rw [multiCtrlGate_apply_id t U (fun _ _ => rfl) (hxq_b false),
          symm_ctrlA_toggleB_at A t ht c hc false] at h
      simpa using! h.symm
    have e_βQ : MA (ctrlA A t ht true) (ctrlA A t ht true) *
        MB (toggleB A c hc) (toggleB A c hc) = 1 := by
      have h := hentry (ctrlA A t ht true) (ctrlA A t ht true) (toggleB A c hc) (toggleB A c hc)
      rw [multiCtrlGate_apply_id t U (fun _ _ => rfl) (hxq_b true),
          symm_ctrlA_toggleB_at A t ht c hc true] at h
      simpa using! h.symm
    have e_γQ : MA (ctrlA A t ht false) (ctrlA A t ht true) *
        MB (toggleB A c hc) (toggleB A c hc) = 0 := by
      have h := hentry (ctrlA A t ht false) (ctrlA A t ht true) (toggleB A c hc) (toggleB A c hc)
      rw [multiCtrlGate_apply_id t U hxyq (hxq_b false),
          symm_ctrlA_toggleB_at A t ht c hc false,
          symm_ctrlA_toggleB_at A t ht c hc true] at h
      simpa using! h.symm
    have e_δQ : MA (ctrlA A t ht true) (ctrlA A t ht false) *
        MB (toggleB A c hc) (toggleB A c hc) = 0 := by
      have h := hentry (ctrlA A t ht true) (ctrlA A t ht false) (toggleB A c hc) (toggleB A c hc)
      rw [multiCtrlGate_apply_id t U (fun k hk => (hxyq k hk).symm) (hxq_b true),
          symm_ctrlA_toggleB_at A t ht c hc true,
          symm_ctrlA_toggleB_at A t ht c hc false] at h
      simpa using! h.symm
    have hQ : MB (toggleB A c hc) (toggleB A c hc) ≠ 0 := by
      intro h
      rw [h, mul_zero] at e_αQ
      exact one_ne_zero e_αQ.symm
    have hαβ : MA (ctrlA A t ht false) (ctrlA A t ht false) =
        MA (ctrlA A t ht true) (ctrlA A t ht true) :=
      mul_right_cancel₀ hQ (e_αQ.trans e_βQ.symm)
    have hγ : MA (ctrlA A t ht false) (ctrlA A t ht true) = 0 := by
      rcases mul_eq_zero.mp e_γQ with h | h
      · exact h
      · exact absurd h hQ
    have hδ : MA (ctrlA A t ht true) (ctrlA A t ht false) = 0 := by
      rcases mul_eq_zero.mp e_δQ with h | h
      · exact h
      · exact absurd h hQ
    have hU01 : U false true = 0 := by rw [e_γP, hγ, zero_mul]
    have hU10 : U true false = 0 := by rw [e_δP, hδ, zero_mul]
    have hU11 : U true true = U false false := by rw [e_βP, e_αP, hαβ]
    apply hU
    refine ⟨U false false, ?_⟩
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.smul_apply, smul_eq_mul, hU01, hU10, hU11]
  · obtain ⟨c, hc⟩ := hA
    have hct : c ≠ t := fun h => ht (h ▸ hc)
    have hxyp : ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (allTrueA A, ctrlB A t ht false)) k =
          ((cutSplit A).symm (allTrueA A, ctrlB A t ht false)) k := fun _ _ => rfl
    have hxp : ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (allTrueA A, ctrlB A t ht false)) k = true :=
      fun k hk => symm_allTrueA_ctrlB_of_ne A t ht false hk
    have hxyPtt : ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (allTrueA A, ctrlB A t ht false)) k =
          ((cutSplit A).symm (allTrueA A, ctrlB A t ht true)) k := by
      intro k hk
      rw [symm_allTrueA_ctrlB_of_ne A t ht false hk,
        symm_allTrueA_ctrlB_of_ne A t ht true hk]
    have hxr_b : ∀ b : Bool, ¬ ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (toggleA A c hc, ctrlB A t ht b)) k = true := by
      intro b hall
      have h := hall c hct
      rw [cutSplit_symm_apply, dif_pos hc] at h
      simp [toggleA] at h
    have hxyr : ∀ k : Fin n, k ≠ t →
        ((cutSplit A).symm (toggleA A c hc, ctrlB A t ht false)) k =
          ((cutSplit A).symm (toggleA A c hc, ctrlB A t ht true)) k := by
      intro k hk
      rw [cutSplit_symm_apply, cutSplit_symm_apply]
      by_cases hkA : k ∈ A
      · rw [dif_pos hkA, dif_pos hkA]
      · rw [dif_neg hkA, dif_neg hkA]
        show (if k = t then false else true) = (if k = t then true else true)
        simp [hk]
    have e_αP : U false false =
        MA (allTrueA A) (allTrueA A) * MB (ctrlB A t ht false) (ctrlB A t ht false) := by
      have h := hentry (allTrueA A) (allTrueA A) (ctrlB A t ht false) (ctrlB A t ht false)
      rw [multiCtrlGate_apply_ctrl t U hxyp hxp,
          symm_allTrueA_ctrlB_at A t ht false] at h
      exact h
    have e_βP : U true true =
        MA (allTrueA A) (allTrueA A) * MB (ctrlB A t ht true) (ctrlB A t ht true) := by
      have h := hentry (allTrueA A) (allTrueA A) (ctrlB A t ht true) (ctrlB A t ht true)
      rw [multiCtrlGate_apply_ctrl t U (fun _ _ => rfl)
            (fun k hk => symm_allTrueA_ctrlB_of_ne A t ht true hk),
          symm_allTrueA_ctrlB_at A t ht true] at h
      exact h
    have e_γP : U false true =
        MA (allTrueA A) (allTrueA A) * MB (ctrlB A t ht false) (ctrlB A t ht true) := by
      have h := hentry (allTrueA A) (allTrueA A) (ctrlB A t ht false) (ctrlB A t ht true)
      rw [multiCtrlGate_apply_ctrl t U hxyPtt hxp,
          symm_allTrueA_ctrlB_at A t ht false, symm_allTrueA_ctrlB_at A t ht true] at h
      exact h
    have e_δP : U true false =
        MA (allTrueA A) (allTrueA A) * MB (ctrlB A t ht true) (ctrlB A t ht false) := by
      have h := hentry (allTrueA A) (allTrueA A) (ctrlB A t ht true) (ctrlB A t ht false)
      rw [multiCtrlGate_apply_ctrl t U (fun k hk => (hxyPtt k hk).symm)
            (fun k hk => symm_allTrueA_ctrlB_of_ne A t ht true hk),
          symm_allTrueA_ctrlB_at A t ht true, symm_allTrueA_ctrlB_at A t ht false] at h
      exact h
    have e_αQ : MA (toggleA A c hc) (toggleA A c hc) *
        MB (ctrlB A t ht false) (ctrlB A t ht false) = 1 := by
      have h := hentry (toggleA A c hc) (toggleA A c hc) (ctrlB A t ht false) (ctrlB A t ht false)
      rw [multiCtrlGate_apply_id t U (fun _ _ => rfl) (hxr_b false),
          symm_toggleA_ctrlB_at A t ht c hc false] at h
      simpa using! h.symm
    have e_βQ : MA (toggleA A c hc) (toggleA A c hc) *
        MB (ctrlB A t ht true) (ctrlB A t ht true) = 1 := by
      have h := hentry (toggleA A c hc) (toggleA A c hc) (ctrlB A t ht true) (ctrlB A t ht true)
      rw [multiCtrlGate_apply_id t U (fun _ _ => rfl) (hxr_b true),
          symm_toggleA_ctrlB_at A t ht c hc true] at h
      simpa using! h.symm
    have e_γQ : MA (toggleA A c hc) (toggleA A c hc) *
        MB (ctrlB A t ht false) (ctrlB A t ht true) = 0 := by
      have h := hentry (toggleA A c hc) (toggleA A c hc) (ctrlB A t ht false) (ctrlB A t ht true)
      rw [multiCtrlGate_apply_id t U hxyr (hxr_b false),
          symm_toggleA_ctrlB_at A t ht c hc false,
          symm_toggleA_ctrlB_at A t ht c hc true] at h
      simpa using! h.symm
    have e_δQ : MA (toggleA A c hc) (toggleA A c hc) *
        MB (ctrlB A t ht true) (ctrlB A t ht false) = 0 := by
      have h := hentry (toggleA A c hc) (toggleA A c hc) (ctrlB A t ht true) (ctrlB A t ht false)
      rw [multiCtrlGate_apply_id t U (fun k hk => (hxyr k hk).symm) (hxr_b true),
          symm_toggleA_ctrlB_at A t ht c hc true,
          symm_toggleA_ctrlB_at A t ht c hc false] at h
      simpa using! h.symm
    have hQ : MA (toggleA A c hc) (toggleA A c hc) ≠ 0 := by
      intro h
      rw [h, zero_mul] at e_αQ
      exact one_ne_zero e_αQ.symm
    have hαβ : MB (ctrlB A t ht false) (ctrlB A t ht false) =
        MB (ctrlB A t ht true) (ctrlB A t ht true) :=
      mul_left_cancel₀ hQ (e_αQ.trans e_βQ.symm)
    have hγ : MB (ctrlB A t ht false) (ctrlB A t ht true) = 0 := by
      rcases mul_eq_zero.mp e_γQ with h | h
      · exact absurd h hQ
      · exact h
    have hδ : MB (ctrlB A t ht true) (ctrlB A t ht false) = 0 := by
      rcases mul_eq_zero.mp e_δQ with h | h
      · exact absurd h hQ
      · exact h
    have hU01 : U false true = 0 := by rw [e_γP, hγ, mul_zero]
    have hU10 : U true false = 0 := by rw [e_δP, hδ, mul_zero]
    have hU11 : U true true = U false false := by rw [e_βP, e_αP, hαβ]
    apply hU
    refine ⟨U false false, ?_⟩
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.smul_apply, smul_eq_mul, hU01, hU10, hU11]

/-- The list of unordered control-target wire pairs extracted from CNOT occurrences in a
reflection-vocabulary program, retaining repetitions. -/
def cnotPairs {n : ℕ} (gs : List (ReflectionGate n)) : List (Sym2 (Fin n)) :=
  gs.filterMap fun g =>
    match g with
    | Sum.inr (c, t) => some s(c, t)
    | Sum.inl _ => none

/-- The number of CNOT occurrences in a reflection-vocabulary program. -/
def cnotCount {n : ℕ} (gs : List (ReflectionGate n)) : ℕ := (cnotPairs gs).length

/-- The finite set of distinct unordered wire pairs appearing in CNOT occurrences of the
program. -/
def cnotEdges {n : ℕ} (gs : List (ReflectionGate n)) : Finset (Sym2 (Fin n)) :=
  (cnotPairs gs).toFinset

/-- The simple interaction graph whose edges are the distinct nonloop wire pairs used by the
program's CNOTs. -/
def cnotGraph {n : ℕ} (gs : List (ReflectionGate n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (↑(cnotEdges gs) : Set (Sym2 (Fin n)))

/-- The number of edges in the CNOT interaction graph is at most the number of CNOT occurrences
in the program. -/
theorem card_edgeSet_cnotGraph_le {n : ℕ} (gs : List (ReflectionGate n)) :
    Nat.card ↑(cnotGraph gs).edgeSet ≤ cnotCount gs := by
  rw [Nat.card_coe_set_eq]
  have hsub : (cnotGraph gs).edgeSet ⊆
      (↑(cnotPairs gs).toFinset : Set (Sym2 (Fin n))) := by
    rw [cnotGraph, cnotEdges, SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.diff_subset
  calc (cnotGraph gs).edgeSet.ncard
      ≤ (↑(cnotPairs gs).toFinset : Set (Sym2 (Fin n))).ncard :=
        Set.ncard_le_ncard hsub
    _ = (cnotPairs gs).toFinset.card := Set.ncard_coe_finset (cnotPairs gs).toFinset
    _ ≤ (cnotPairs gs).length := List.toFinset_card_le (cnotPairs gs)
    _ = cnotCount gs := rfl

/-- For `n >= 1`, a program with fewer than `n - 1` CNOT occurrences possesses a nontrivial wire
partition across which no gate acts. -/
theorem exists_uncrossed_cut_of_sparse {n : ℕ} (gs : List (ReflectionGate n)) (hn : 1 ≤ n)
    (hcount : cnotCount gs < n - 1) :
    ∃ A : Finset (Fin n), A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ g ∈ gs, reflectionGateWires g ⊆ A ∨ Disjoint (reflectionGateWires g) A := by
  have hcard : Nat.card ↑(cnotGraph gs).edgeSet < n - 1 :=
    lt_of_le_of_lt (card_edgeSet_cnotGraph_le gs) hcount
  obtain ⟨A, hAne, hAcne, hcut⟩ := exists_cut_of_sparse (cnotGraph gs) hn hcard
  refine ⟨A, hAne, hAcne, ?_⟩
  intro g hg
  cases g with
  | inl p =>
      obtain ⟨w, U⟩ := p
      rw [show reflectionGateWires (Sum.inl (w, U) : ReflectionGate n) = {w} from rfl]
      by_cases hw : w ∈ A
      · exact Or.inl (Finset.singleton_subset_iff.mpr hw)
      · exact Or.inr (Finset.disjoint_singleton_left.mpr hw)
  | inr p =>
      obtain ⟨c, t⟩ := p
      rw [show reflectionGateWires (Sum.inr (c, t) : ReflectionGate n) = {c, t} from rfl]
      by_cases hct : c = t
      · subst hct
        by_cases hc : c ∈ A
        · refine Or.inl ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact hc
        · refine Or.inr ?_
          rw [Finset.disjoint_left]
          intro x hx hxA
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact hc hxA
      · have hmem : s(c, t) ∈ cnotEdges gs := by
          rw [cnotEdges, List.mem_toFinset, cnotPairs]
          exact List.mem_filterMap.mpr ⟨Sum.inr (c, t), hg, rfl⟩
        have hadj : (cnotGraph gs).Adj c t := by
          rw [cnotGraph, SimpleGraph.fromEdgeSet_adj]
          exact ⟨hmem, hct⟩
        have hiff := hcut c t hadj
        by_cases hc : c ∈ A
        · have ht : t ∈ A := hiff.mp hc
          refine Or.inl ?_
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hc
          · exact ht
        · have ht : t ∉ A := fun h => hc (hiff.mpr h)
          refine Or.inr ?_
          rw [Finset.disjoint_left]
          intro x hx hxA
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hc hxA
          · exact ht hxA

/-- An exact implementation of a fully controlled nonscalar matrix has no nontrivial wire
partition for which every gate stays on one side. -/
theorem no_nontrivial_cut_of_multiCtrl {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ)
    (hU : ¬ IsScalar U) {gs : List (ReflectionGate n)}
    (hprog : reflectionProgramMatrix gs = multiCtrlGate t U) :
    ∀ A : Finset (Fin n), A.Nonempty → (∃ i, i ∉ A) →
      ¬ (∀ g ∈ gs, reflectionGateWires g ⊆ A ∨ Disjoint (reflectionGateWires g) A) := by
  intro A hA hB hcut
  have hfac : FactorsAcross A (multiCtrlGate t U) := by
    rw [← hprog]
    exact reflectionProgramMatrix_factors hcut
  exact multiCtrlGate_not_factors t U hU hA hB hfac

/-- Any reflection-vocabulary program exactly equal to the fully controlled matrix of a
nonscalar `U` on `n >= 1` wires contains at least `n - 1` CNOT occurrences. This proves the
CNOT lower bound underlying Lemma 7.7 of [BarencoEtAl1995]. -/
theorem lemma77_lower_bound {n : ℕ} (t : Fin n) (U : Matrix Bool Bool ℂ)
    (hU : ¬ IsScalar U) (gs : List (ReflectionGate n)) (hn : 1 ≤ n)
    (hprog : reflectionProgramMatrix gs = multiCtrlGate t U) :
    n - 1 ≤ cnotCount gs := by
  by_contra hlt
  have hlt' : cnotCount gs < n - 1 := not_le.mp hlt
  obtain ⟨A, hAne, hAcne, hcut⟩ := exists_uncrossed_cut_of_sparse gs hn hlt'
  exact no_nontrivial_cut_of_multiCtrl t U hU hprog A hAne
    (hAcne.imp fun i hi => Finset.mem_compl.mp hi) hcut

end Qatlib.Papers.ElemGates95.MultiControl.Section7
