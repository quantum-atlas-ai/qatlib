/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds.BooleanPolynomial
import Qatlib.Papers.LiftingWu25.ProtocolSetup.HybridModel
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Find

set_option backward.isDefEq.respectTransparency false

/-!
# SensitivityEntropic — block sensitivity is entropic

Wu--Yang--Yao, fixed arXiv:2511.17227v2, Section 2.1 and Proposition 2.5.

Block sensitivity at an input `x` is the largest number `k` of pairwise-disjoint
blocks `B₁,…,B_k` such that flipping any one block changes `f(x)`. Proposition
2.5 says that `bs(·)` is entropic (Definition 2.2): fixing the coordinate `i` to
the value `x i` of an optimal input destroys at most one of the `k` blocks, the
one that contains `i`.

Boundary: only the entropic property of block sensitivity is established. The
paper's uses of it (Theorem 5.2) are stated in `Tradeoff`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical

namespace Qatlib.Papers.LiftingWu25.ProtocolSetup

open Finset
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.TriangleDegreeBounds

variable {ι : Type*}

/-- Flip every coordinate inside the block `B`. -/
def flipBlock [DecidableEq ι] (x : ι → Bool) (B : Finset ι) : ι → Bool :=
  fun i => if i ∈ B then !x i else x i

/-- `Bs` is a family of pairwise-disjoint nonempty blocks on which `f` is sensitive at `x`:
flipping any of them changes the value of `f`. -/
def SensitiveBlocks [DecidableEq ι] (f : (ι → Bool) → ℝ) (x : ι → Bool)
    (Bs : Finset (Finset ι)) : Prop :=
  (∀ B ∈ Bs, B.Nonempty ∧ f x ≠ f (flipBlock x B)) ∧
    ∀ B ∈ Bs, ∀ C ∈ Bs, B ≠ C → Disjoint B C

/-- `k` is an attainable block-sensitivity count of `f`. -/
def Achievable [DecidableEq ι] (f : (ι → Bool) → ℝ) (k : ℕ) : Prop :=
  ∃ (x : ι → Bool) (Bs : Finset (Finset ι)), Bs.card = k ∧ SensitiveBlocks f x Bs

/-- `bs(f)`: the block sensitivity of `f` (Section 2.1), as the largest attainable number
of pairwise-disjoint sensitive blocks. -/
def blockSensitivity [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) : ℕ :=
  Nat.findGreatest (Achievable f) (Fintype.card ι)

/-- Pairwise-disjoint nonempty blocks over an `ι` of size `N` number at most `N`. -/
theorem card_le_of_sensitiveBlocks [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} {x : ι → Bool} {Bs : Finset (Finset ι)}
    (h : SensitiveBlocks f x Bs) : Bs.card ≤ Fintype.card ι := by
  have hpd : (↑Bs : Set (Finset ι)).PairwiseDisjoint id := by
    intro B hB C hC hne
    exact h.2 B hB C hC hne
  have hsum : (Bs.biUnion id).card = ∑ B ∈ Bs, B.card := Finset.card_biUnion hpd
  have hones : Bs.card = ∑ _B ∈ Bs, (1 : ℕ) := (Finset.card_eq_sum_ones Bs).trans rfl
  have hle : ∑ _B ∈ Bs, (1 : ℕ) ≤ ∑ B ∈ Bs, B.card := by
    apply Finset.sum_le_sum
    intro B hB
    exact Finset.card_pos.mpr (h.1 B hB).1
  have hunion : (Bs.biUnion id) ⊆ Finset.univ := Finset.subset_univ _
  have hcard_univ : (Finset.univ : Finset ι).card = Fintype.card ι := Finset.card_univ
  have := Finset.card_le_card hunion
  omega

/-- The block sensitivity is attained: there are `bs(f)` pairwise-disjoint sensitive blocks
at some input. -/
theorem blockSensitivity_spec [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) :
    ∃ (x : ι → Bool) (Bs : Finset (Finset ι)),
      Bs.card = blockSensitivity f ∧ SensitiveBlocks f x Bs := by
  have hzero : Achievable f 0 := by
    refine ⟨fun _ => false, ∅, by simp, ?_⟩
    refine ⟨?_, ?_⟩
    · intro B hB
      simp at hB
    · intro B hB
      simp at hB
  have hle : (0 : ℕ) ≤ Fintype.card ι := Nat.zero_le _
  exact Nat.findGreatest_spec hle hzero

/-- Restricting a single coordinate to the value it already has leaves the value unchanged. -/
theorem restrict_singleton_apply [DecidableEq ι] (f : (ι → Bool) → ℝ) (i : ι) (z : Bool)
    (x : ι → Bool) (hx : x i = z) : restrict {i} f (fun _ => z) x = f x := by
  refine congrArg f (funext fun a => ?_)
  by_cases hai : a = i
  · subst hai
    simp [hx]
  · simp [hai]

/-- Flipping a block that does not contain `i` does not change the coordinate `i`. -/
theorem flipBlock_apply_of_notMem [DecidableEq ι] (x : ι → Bool) {B : Finset ι} {i : ι}
    (hi : i ∉ B) : flipBlock x B i = x i := by
  simp [flipBlock, hi]

/-- Proposition 2.5: block sensitivity is entropic. -/
theorem prop25_blockSensitivity_entropic [Fintype ι] [DecidableEq ι] :
    Entropic (ι := ι) (fun (f : (ι → Bool) → ℝ) => (blockSensitivity f : ℝ)) := by
  intro f i
  obtain ⟨x0, Bs, hcard, hBs⟩ := blockSensitivity_spec f
  set z := x0 i with hz
  refine ⟨z, ?_⟩
  set g : (ι → Bool) → ℝ := restrict {i} f (fun _ => z) with hg
  set Bs' : Finset (Finset ι) := Bs.filter (fun B => i ∉ B) with hBs'
  have hBs'_mem : ∀ B ∈ Bs', B ∈ Bs ∧ i ∉ B := by
    intro B hB
    rw [hBs', Finset.mem_filter] at hB
    exact hB
  -- the surviving blocks are still sensitive for the restricted function at `x0`
  have hsens' : SensitiveBlocks g x0 Bs' := by
    refine ⟨?_, ?_⟩
    · intro B hB
      obtain ⟨hBin, hiB⟩ := hBs'_mem B hB
      obtain ⟨hne, hsens⟩ := hBs.1 B hBin
      refine ⟨hne, ?_⟩
      have hx0 : x0 i = z := rfl
      have hflip : flipBlock x0 B i = z := by
        rw [flipBlock_apply_of_notMem x0 hiB, hx0]
      rw [hg, restrict_singleton_apply f i z x0 hx0,
        restrict_singleton_apply f i z (flipBlock x0 B) hflip]
      exact hsens
    · intro B hB C hC hne
      exact hBs.2 B (hBs'_mem B hB).1 C (hBs'_mem C hC).1 hne
  -- at most one block of a disjoint family contains `i`
  have hdrop : Bs.card - 1 ≤ Bs'.card := by
    have hpart := Finset.card_filter_add_card_filter_not (s := Bs) (p := fun B => i ∉ B)
    have hone : {B ∈ Bs | ¬ i ∉ B}.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro B hB C hC
      rw [Finset.mem_filter] at hB hC
      by_contra hne
      have hiB : i ∈ B := not_not.mp hB.2
      have hiC : i ∈ C := not_not.mp hC.2
      exact (Finset.disjoint_left.mp (hBs.2 B hB.1 C hC.1 hne)) hiB hiC
    simp only [hBs']
    omega
  -- hence `Bs'.card` is an attainable count for `g`
  have hreach : (Bs'.card : ℝ) ≤ (blockSensitivity g : ℝ) := by
    have hbnd : Bs'.card ≤ Fintype.card ι := card_le_of_sensitiveBlocks hsens'
    have : Bs'.card ≤ blockSensitivity g :=
      Nat.le_findGreatest hbnd ⟨x0, Bs', rfl, hsens'⟩
    exact_mod_cast this
  have hgoal : (blockSensitivity f : ℝ) - 1 ≤ (blockSensitivity g : ℝ) := by
    rw [← hcard]
    rcases Nat.eq_zero_or_pos Bs.card with h0 | hpos
    · rw [h0]
      push_cast
      linarith
    · have h1 : ((Bs.card - 1 : ℕ) : ℝ) = (Bs.card : ℝ) - 1 := by
        push_cast [Nat.cast_sub (show 1 ≤ Bs.card from hpos)]
        ring
      have : ((Bs.card - 1 : ℕ) : ℝ) ≤ (Bs'.card : ℝ) := by exact_mod_cast hdrop
      linarith
  exact hgoal

/-- Proposition 2.4: the exact degree is entropic. Fixing one coordinate of the underlying
real acceptance function lowers the exact degree of the induced Boolean function by at most
one. The proof splices the integer interpolants of the two restricted functions through the
explicit factors `X i` and `1 - X i`; the spliced polynomial represents the function on the
whole Boolean cube with degree at most `1 + max`, and `integerBooleanRepresentative_map_degree_le`
converts this witness into the entropic inequality. -/
theorem prop24_exactDegree_entropic {ι : Type} [Fintype ι] [DecidableEq ι] :
    Entropic (ι := ι)
      (fun f => (exactDegree (fun x => decide (f x = 1)) : ℝ)) := by
  classical
  intro f i
  set g : (ι → Bool) → Bool := fun x => decide (f x = 1) with hgdef
  set gz : Bool → (ι → Bool) → Bool := fun z x =>
    decide (restrict {i} f (fun _ => z) x = 1) with hgzdef
  set R : Bool → MvPolynomial ι ℝ := fun z =>
    MvPolynomial.map (Int.castRingHom ℝ) (integerBooleanRepresentative (gz z)) with hRdef
  have hRdeg : ∀ z : Bool, (R z).totalDegree = exactDegree (gz z) := by
    intro z
    rw [hRdef]
    exact integerBooleanRepresentative_real_degree_eq (gz z)
  have hReval : ∀ (z : Bool) (y : ι → Bool),
      MvPolynomial.eval (booleanPoint y) (R z) = if gz z y then 1 else 0 := by
    intro z y
    rw [hRdef]
    exact integerBooleanRepresentative_map_eval (gz z) y
  set P : MvPolynomial ι ℝ :=
    MvPolynomial.X i * R true + (1 - MvPolynomial.X i) * R false with hPdef
  have hbp : ∀ (y : ι → Bool), booleanPoint y i = if y i then 1 else 0 := fun _ => rfl
  have hPeval : ∀ y : ι → Bool, boolEval P y = if g y then 1 else 0 := by
    intro y
    have hb : ∀ q : MvPolynomial ι ℝ,
        boolEval q y = MvPolynomial.eval (booleanPoint y) q := fun _ => rfl
    rw [hb P, hPdef]
    rw [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
      MvPolynomial.eval_X]
    by_cases hy : y i = true
    · have hrt : restrict {i} f (fun _ => true) y = f y :=
        restrict_singleton_apply f i true y hy
      have hgzty : gz true y = g y := by
        show decide (restrict {i} f (fun _ => true) y = 1) = decide (f y = 1)
        rw [hrt]
      have he1 : MvPolynomial.eval (booleanPoint y) (R true) = if g y then 1 else 0 := by
        rw [hReval true y, hgzty]
      have he0 : MvPolynomial.eval (booleanPoint y)
          ((1 : MvPolynomial ι ℝ) - MvPolynomial.X i) = 0 := by
        rw [MvPolynomial.eval_sub, MvPolynomial.eval_X]
        simp [booleanPoint, hy]
      rw [he1, he0]
      simp [booleanPoint, hy]
    · have hyf : y i = false := by
        cases hyi : y i with
        | true => exact absurd hyi hy
        | false => rfl
      have hrf : restrict {i} f (fun _ => false) y = f y :=
        restrict_singleton_apply f i false y hyf
      have hgzfy : gz false y = g y := by
        show decide (restrict {i} f (fun _ => false) y = 1) = decide (f y = 1)
        rw [hrf]
      have he0 : MvPolynomial.eval (booleanPoint y) (R false) = if g y then 1 else 0 := by
        rw [hReval false y, hgzfy]
      have he1 : MvPolynomial.eval (booleanPoint y)
          ((1 : MvPolynomial ι ℝ) - MvPolynomial.X i) = 1 := by
        rw [MvPolynomial.eval_sub, MvPolynomial.eval_X]
        simp [booleanPoint, hyf]
      rw [he0, he1]
      simp [booleanPoint, hyf]
  have hatt : exactDegree g ≤ P.totalDegree := by
    have h := integerBooleanRepresentative_map_degree_le (R := ℝ) g P hPeval
    rwa [integerBooleanRepresentative_real_degree_eq g] at h
  have hdegP : P.totalDegree ≤ 1 + max (exactDegree (gz true)) (exactDegree (gz false)) := by
    have h1 : (MvPolynomial.X i * R true).totalDegree ≤ 1 + exactDegree (gz true) := by
      have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.X i) (R true)
      rw [MvPolynomial.totalDegree_X, hRdeg true] at hmul
      exact hmul
    have h2 : ((1 - MvPolynomial.X i) * R false).totalDegree
        ≤ 1 + exactDegree (gz false) := by
      have hmul := MvPolynomial.totalDegree_mul
        ((1 : MvPolynomial ι ℝ) - MvPolynomial.X i) (R false)
      have hsub : ((1 : MvPolynomial ι ℝ) - MvPolynomial.X i).totalDegree ≤ 1 := by
        have hs := MvPolynomial.totalDegree_sub ((1 : MvPolynomial ι ℝ)) (MvPolynomial.X i)
        rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X] at hs
        simp at hs
        exact hs
      rw [hRdeg false] at hmul
      omega
    rw [hPdef]
    have hadd := MvPolynomial.totalDegree_add (MvPolynomial.X i * R true)
      (((1 : MvPolynomial ι ℝ) - MvPolynomial.X i) * R false)
    omega
  obtain ⟨z, hz⟩ : ∃ z : Bool, max (exactDegree (gz true)) (exactDegree (gz false))
      ≤ exactDegree (gz z) := by
    rcases le_total (exactDegree (gz false)) (exactDegree (gz true)) with hle | hle
    · exact ⟨true, max_le_iff.mpr ⟨le_rfl, hle⟩⟩
    · exact ⟨false, max_le_iff.mpr ⟨hle, le_rfl⟩⟩
  have hchain : exactDegree g ≤ 1 + exactDegree (gz z) :=
    hatt.trans (hdegP.trans (by omega))
  have hcast : ((exactDegree g : ℕ) : ℝ) ≤ 1 + ((exactDegree (gz z) : ℕ) : ℝ) := by
    have h : ((exactDegree g : ℕ) : ℝ)
        ≤ ((1 + exactDegree (gz z) : ℕ) : ℝ) := by exact_mod_cast hchain
    push_cast at h
    linarith
  refine ⟨z, ?_⟩
  show ((exactDegree (gz z) : ℕ) : ℝ) ≥ ((exactDegree g : ℕ) : ℝ) - 1
  linarith

end Qatlib.Papers.LiftingWu25.ProtocolSetup
