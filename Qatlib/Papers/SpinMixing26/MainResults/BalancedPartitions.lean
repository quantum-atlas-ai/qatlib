/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults — `b`-balanced tripartitions of the chain (Lemma V.2)

Bergamaschi–Chen, *Fast Mixing of Quantum Spin Chains at All Temperatures*,
fixed arXiv:2510.08533v2, Lemma V.2 (p. 31), Eq. (5.14)–(5.17).

原文：设 `b : ℤ⁺ → ℤ⁺` 满足 `∀x, b(x) ≤ x/100`。则存在只依赖 `b` 的常数 `ℓ_b, c_b > 0`，
使任意长度 `r ≥ ℓ_b` 的区间 `R` 都有一族 `s` 个三元划分 `(A_i, B_i, C_i)`：
`A_i, B_i, C_i` 互不相交且并为 `R`；`⌈2r/3⌉ ≥ |A_i|, |C_i| ≥ ⌊r/3⌋` 且
`2·b(r) ≥ |B_i| ≥ b(r)`；各 `B_i` 两两不交；`s ≥ c_b · r / b(r)`。
原文证明取 `A_i = [1, ⌊r/3⌋ + i·b(r)]`、`B_i = [⌊r/3⌋ + i·b(r) + 1, ⌊r/3⌋ + (i+1)·b(r)]`、
`C_i = [⌊r/3⌋ + (i+1)·b(r) + 1, r]`，`s = ⌊r/(10·b(r))⌋`。

形式化约定：长度 `r` 的区间取 `Finset.range r`（即 `[0, r)` 上的格点，等价于原文 WLOG 取
`R = [1, r]` 的平移），三个块取 `Finset.Ico` 区间；常数取 `ℓ_b = 1000`、`c_b = 1/20`
（原文只断言存在性，故任取一组可行的显式常数即可），`c_b` 与 `ℓ_b` 在本文件中不依赖
具体函数 `b`，比原文“只依赖 `b`”更强。
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpinMixing26.MainResults

/-- A tripartition of a chain of `r` sites into three site sets: the left block `A`, the
middle block `B`, and the right block `C`, together covering the chain with pairwise disjoint
supports (Lemma V.2, items 1 and 3). -/
structure ChainTripartition (r : ℕ) where
  /-- The left block `A_i`. -/
  A : Finset ℕ
  /-- The middle block `B_i`. -/
  B : Finset ℕ
  /-- The right block `C_i`. -/
  C : Finset ℕ
  /-- The three blocks cover the whole chain. -/
  union_eq : A ∪ B ∪ C = Finset.range r
  /-- `A` and `B` are disjoint. -/
  disjoint_AB : Disjoint A B
  /-- `A` and `C` are disjoint. -/
  disjoint_AC : Disjoint A C
  /-- `B` and `C` are disjoint. -/
  disjoint_BC : Disjoint B C

/-- Lemma V.2 (`b`-balanced partitions of the chain): for every `b : ℕ → ℕ` with `0 < b x` and
`b x ≤ x / 100`, there are constants `ℓ` and `c > 0` such that each chain `[0, r)` with `r ≥ ℓ`
admits `s` tripartitions `(A_i, B_i, C_i)` whose blocks cover the chain, whose middle blocks are
pairwise disjoint, with `⌈2r/3⌉ ≥ |A_i|, |C_i| ≥ ⌊r/3⌋`, `2·b(r) ≥ |B_i| ≥ b(r)`, and
`s ≥ c · r / b(r)` (items 1–4 of Lemma V.2; `c` may depend on `b` in the paper). -/
theorem exists_balanced_tripartitions (b : ℕ → ℕ) (hbpos : ∀ x, 0 < b x)
    (hb : ∀ x, b x ≤ x / 100) :
    ∃ ℓ : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, ℓ ≤ r →
      ∃ s : ℕ, ∃ T : Fin s → ChainTripartition r,
        (∀ i, (T i).A.card ≤ (2 * r + 2) / 3) ∧
        (∀ i, r / 3 ≤ (T i).A.card) ∧
        (∀ i, (T i).B.card ≤ 2 * b r) ∧
        (∀ i, b r ≤ (T i).B.card) ∧
        (∀ i, (T i).C.card ≤ (2 * r + 2) / 3) ∧
        (∀ i, r / 3 ≤ (T i).C.card) ∧
        (∀ i j : Fin s, i ≠ j → Disjoint (T i).B (T j).B) ∧
        ((1 / 20 : ℝ) * r / (b r : ℝ) ≤ (s : ℝ)) := by
  refine ⟨1000, 1 / 20, by norm_num, ?_⟩
  intro r hr
  have hbr : b r ≤ r / 100 := hb r
  have hbposr : 0 < b r := hbpos r
  let bb := b r
  let s := r / (10 * bb)
  have hpos : 0 < 10 * bb := by positivity
  -- bound on `s * bb`
  have hsb : s * bb ≤ r / 10 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
    calc (s * bb) * 10 = s * (10 * bb) := by ring
      _ ≤ r := Nat.div_mul_le_self r (10 * bb)
  -- endpoints
  have hstep : ∀ i : ℕ, r / 3 + i * bb ≤ r / 3 + (i + 1) * bb := by
    intro i
    have : i * bb ≤ (i + 1) * bb := Nat.mul_le_mul_right bb (by omega)
    omega
  have hend : ∀ i : Fin s, r / 3 + (i + 1) * bb ≤ r := by
    intro i
    have hi : (i : ℕ) + 1 ≤ s := Nat.succ_le_of_lt i.isLt
    have h1 : ((i : ℕ) + 1) * bb ≤ s * bb := Nat.mul_le_mul_right bb hi
    omega
  -- cardinalities
  have hcardA : ∀ i : ℕ, (Finset.Ico 0 (r / 3 + i * bb)).card = r / 3 + i * bb := by
    intro i
    rw [Nat.card_Ico]
    omega
  have hcardB : ∀ i : ℕ, (Finset.Ico (r / 3 + i * bb) (r / 3 + (i + 1) * bb)).card = bb := by
    intro i
    rw [Nat.card_Ico]
    have h : r / 3 + (i + 1) * bb = (r / 3 + i * bb) + bb := by ring
    rw [h]
    omega
  have hcardC : ∀ i : ℕ, (Finset.Ico (r / 3 + (i + 1) * bb) r).card
      = r - (r / 3 + (i + 1) * bb) := by
    intro i
    rw [Nat.card_Ico]
  -- the tripartition family
  let T : Fin s → ChainTripartition r := fun i =>
    { A := Finset.Ico 0 (r / 3 + i * bb)
      B := Finset.Ico (r / 3 + i * bb) (r / 3 + (i + 1) * bb)
      C := Finset.Ico (r / 3 + (i + 1) * bb) r
      union_eq := by
        have h1 := Finset.Ico_union_Ico_eq_Ico (show (0:ℕ) ≤ r / 3 + (i : ℕ) * bb by omega)
          (hstep i)
        have h2 := Finset.Ico_union_Ico_eq_Ico
          (show (0:ℕ) ≤ r / 3 + ((i : ℕ) + 1) * bb by omega) (hend i)
        have h3 : Finset.range r = Finset.Ico 0 r := by
          ext x; simp
        rw [h3, ← h2, ← h1]
      disjoint_AB := Finset.Ico_disjoint_Ico_consecutive _ _ _
      disjoint_BC := Finset.Ico_disjoint_Ico_consecutive _ _ _
      disjoint_AC := by
        have hst := hstep (i : ℕ)
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_Ico] at hx hx'
        omega }
  refine ⟨s, T, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    show (Finset.Ico 0 (r / 3 + i * bb)).card ≤ (2 * r + 2) / 3
    rw [hcardA i]
    have h1 : (i : ℕ) * bb ≤ s * bb := Nat.mul_le_mul_right bb (Nat.le_of_lt i.isLt)
    omega
  · intro i
    show r / 3 ≤ (Finset.Ico 0 (r / 3 + i * bb)).card
    rw [hcardA i]
    omega
  · intro i
    show (Finset.Ico (r / 3 + i * bb) (r / 3 + (i + 1) * bb)).card ≤ 2 * bb
    rw [hcardB i]
    omega
  · intro i
    show bb ≤ (Finset.Ico (r / 3 + i * bb) (r / 3 + (i + 1) * bb)).card
    rw [hcardB i]
  · intro i
    show (Finset.Ico (r / 3 + (i + 1) * bb) r).card ≤ (2 * r + 2) / 3
    rw [hcardC i]
    have h1 : ((i : ℕ) + 1) * bb ≤ s * bb :=
      Nat.mul_le_mul_right bb (Nat.succ_le_of_lt i.isLt)
    omega
  · intro i
    show r / 3 ≤ (Finset.Ico (r / 3 + (i + 1) * bb) r).card
    rw [hcardC i]
    have h1 : ((i : ℕ) + 1) * bb ≤ s * bb :=
      Nat.mul_le_mul_right bb (Nat.succ_le_of_lt i.isLt)
    omega
  · intro i j hij
    have hval : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    show Disjoint (Finset.Ico (r / 3 + (i : ℕ) * bb) (r / 3 + ((i : ℕ) + 1) * bb))
      (Finset.Ico (r / 3 + (j : ℕ) * bb) (r / 3 + ((j : ℕ) + 1) * bb))
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    simp only [Finset.mem_Ico] at hx hx'
    rcases Nat.lt_or_gt_of_ne hval with hlt | hlt
    · have hle : ((i : ℕ) + 1) * bb ≤ (j : ℕ) * bb := Nat.mul_le_mul_right bb hlt
      omega
    · have hle : ((j : ℕ) + 1) * bb ≤ (i : ℕ) * bb := Nat.mul_le_mul_right bb hlt
      omega
  · -- count
    have hlt : r < (s + 1) * (10 * bb) := by
      have hmod : r % (10 * bb) < 10 * bb := Nat.mod_lt _ hpos
      have hdecomp : r = s * (10 * bb) + r % (10 * bb) := by
        calc r = (10 * bb) * (r / (10 * bb)) + r % (10 * bb) := (Nat.div_add_mod r (10 * bb)).symm
          _ = s * (10 * bb) + r % (10 * bb) := by rw [mul_comm]
      rw [hdecomp]
      have h1 : s * (10 * bb) + r % (10 * bb) < s * (10 * bb) + 10 * bb :=
        Nat.add_lt_add_left hmod _
      have h2 : s * (10 * bb) + 10 * bb = (s + 1) * (10 * bb) := by ring
      omega
    have hs1 : 1 ≤ s := by
      rw [Nat.le_div_iff_mul_le hpos]
      omega
    have hkey : r ≤ 20 * s * bb := by
      have h2 : s + 1 ≤ 2 * s := by omega
      have h3 : (s + 1) * (10 * bb) ≤ (2 * s) * (10 * bb) := Nat.mul_le_mul_right _ h2
      have h4 : (2 * s) * (10 * bb) = 20 * s * bb := by ring
      omega
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (bb:ℝ))]
    have : (r:ℝ) ≤ 20 * (s:ℝ) * (bb:ℝ) := by exact_mod_cast hkey
    calc (1 / 20 : ℝ) * r ≤ (1 / 20) * (20 * (s:ℝ) * (bb:ℝ)) := by linarith
      _ = (s:ℝ) * (bb:ℝ) := by ring
end Qatlib.Papers.SpinMixing26.MainResults
