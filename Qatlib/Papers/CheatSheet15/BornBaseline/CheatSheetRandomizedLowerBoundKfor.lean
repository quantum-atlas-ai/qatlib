/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetRandomizedLowerBoundStat
public import Qatlib.Papers.CheatSheet15.BornBaseline.QueryTreeAgreementInvarianceKfor
public import Qatlib.Papers.CheatSheet15.BornBaseline.CheatSheetBasicSemanticsKfor

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

namespace Qatlib.Papers.CheatSheet15.BornBaseline

open scoped Classical
open scoped ENNReal

def blankBlockOracle {c M κ : ℕ} (j : Fin c) (X : Fin c → Fin M → Bool)
    (x : Fin M → Bool) : CheatSheetIndex c M κ → Bool :=
  Sum.elim (fun q => if q.1 = j then x q.2 else X q.1 q.2) (fun _ => false)

def cheatSheetHitTree {c M κ : ℕ} (j : Fin c) (ℓ : Fin (2 ^ c))
    (X : Fin c → Fin M → Bool) :
    BoolQueryTree (CheatSheetIndex c M κ) Bool → BoolQueryTree (Fin M) Bool
  | .halt _ => .halt false
  | .ask (.inl q) f t =>
      if q.1 = j then .ask q.2 (cheatSheetHitTree j ℓ X f) (cheatSheetHitTree j ℓ X t)
      else if X q.1 q.2 then cheatSheetHitTree j ℓ X t else cheatSheetHitTree j ℓ X f
  | .ask (.inr q) f _ =>
      if q.1 = ℓ then .halt true else cheatSheetHitTree j ℓ X f

/-- The cheat-sheet hit tree has maximum query count at most that of the original tree. -/
theorem cheatSheetHitTree_queries {c M κ : ℕ} (j : Fin c) (ℓ : Fin (2 ^ c))
    (X : Fin c → Fin M → Bool) (τ : BoolQueryTree (CheatSheetIndex c M κ) Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries (cheatSheetHitTree j ℓ X τ) ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ := by
  induction τ with
  | halt b => simp [cheatSheetHitTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
  | ask q f t ihf iht =>
    cases q with
    | inl q =>
      simp only [cheatSheetHitTree,
          Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
      split
      · simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
        omega
      · split <;> omega
    | inr q =>
      simp only [cheatSheetHitTree,
          Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
      split
      · simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries]
      · omega

/-- The hit tree returns true exactly when the original tree queries some certificate bit in the
specified sheet under the blank-block oracle. -/
theorem cheatSheetHitTree_run {c M κ : ℕ} (j : Fin c) (ℓ : Fin (2 ^ c))
    (X : Fin c → Fin M → Bool) (x : Fin M → Bool)
    (τ : BoolQueryTree (CheatSheetIndex c M κ) Bool) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x (cheatSheetHitTree j ℓ X τ)).1 =
      decide (∃ i : Fin c, ∃ b : Fin κ,
        Sum.inr (ℓ, i, b) ∈ queriesOf (blankBlockOracle (κ := κ) j X x) τ) := by
  induction τ with
  | halt b => simp [cheatSheetHitTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf]
  | ask q f t ihf iht =>
    cases q with
    | inl q =>
      by_cases hq : q.1 = j
      · cases hx : x q.2 with
        | false => simpa [cheatSheetHitTree, blankBlockOracle, hq, hx, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf] using! ihf
        | true => simpa [cheatSheetHitTree, blankBlockOracle, hq, hx, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf] using! iht
      · cases hx : X q.1 q.2 with
        | false => simpa [cheatSheetHitTree, blankBlockOracle, hq, hx, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf] using! ihf
        | true => simpa [cheatSheetHitTree, blankBlockOracle, hq, hx, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf] using! iht
    | inr q =>
      rcases q with ⟨r, i, b⟩
      by_cases hr : r = ℓ
      · subst r
        have hh : ∃ i' : Fin c, ∃ b' : Fin κ,
            Sum.inr (ℓ, i', b') ∈ queriesOf (blankBlockOracle (κ := κ) j X x)
              (.ask (.inr (ℓ, i, b)) f t) := by
          exact ⟨i, b, by simp [queriesOf, blankBlockOracle]⟩
        simp [cheatSheetHitTree, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, hh]
      · simpa [cheatSheetHitTree, blankBlockOracle, hr, Ne.symm hr, Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf,
          and_or_left, exists_or] using! ihf

/-- Mapping a randomized tree program to its cheat-sheet hit trees preserves the stated query
bound. -/
theorem cheatSheetHitTree_bounded_program {c M κ T : ℕ} (j : Fin c) (ℓ : Fin (2 ^ c))
    (X : Fin c → Fin M → Bool) (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool))
    (hA : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries A T) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries (A.map (cheatSheetHitTree j ℓ X)) T := by
  intro τ hτ
  have hs : τ ∈ (A.map (cheatSheetHitTree j ℓ X)).support := hτ
  obtain ⟨σ, hσ, rfl⟩ := (PMF.mem_support_map_iff (cheatSheetHitTree j ℓ X) A τ).mp hs
  exact (cheatSheetHitTree_queries j ℓ X σ).trans (hA σ hσ)

/-- The success probability of a randomized tree program equals the outer measure of trees whose
output satisfies the success predicate. -/
private theorem treeSuccessProb_outer {Q : Type} (A : PMF (BoolQueryTree Q Bool))
    (x : Q → Bool) (E : Bool → Prop) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x E =
      A.toOuterMeasure {τ | E (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1} := by
  unfold Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro τ
  by_cases h : E (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 <;> simp [Set.indicator, h]

/-- The hit-tree success probability is the original tree distribution's weighted sum of
indicators for querying the specified sheet. -/
theorem cheatSheetHitTree_success {c M κ : ℕ} (j : Fin c) (ℓ : Fin (2 ^ c))
    (X : Fin c → Fin M → Bool) (x : Fin M → Bool)
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (A.map (cheatSheetHitTree j ℓ X)) x (fun b => b = true) =
      ∑' τ, A τ * if (∃ i : Fin c, ∃ b : Fin κ,
        Sum.inr (ℓ, i, b) ∈ queriesOf (blankBlockOracle (κ := κ) j X x) τ) then 1 else 0 := by
  rw [treeSuccessProb_outer, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro τ
  by_cases h : ∃ i : Fin c, ∃ b : Fin κ,
      Sum.inr (ℓ, i, b) ∈ queriesOf (blankBlockOracle (κ := κ) j X x) τ
  · simp [Set.indicator, cheatSheetHitTree_run, h]
  · simp [Set.indicator, cheatSheetHitTree_run, h]

/-- The sum of consecutive differences along a finite sequence telescopes to its final value
minus its initial value. -/
private theorem cheatHybrid_telescope (c : ℕ) (q : Fin (c + 1) → ℝ) :
    (∑ j : Fin c, (q j.succ - q j.castSucc)) = q (Fin.last c) - q 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => q i.castSucc)
    have he : (∑ i : Fin c, (q i.castSucc.succ - q i.castSucc.castSucc)) =
        q (Fin.last c).castSucc - q 0 := by simpa using h
    rw [he]
    simp

/-- A positive-length sequence starting below one sixth and ending at least one third has a
consecutive increment greater than one divided by six times its length. -/
theorem cheatSheetHybrid_step (c : ℕ) (hc : 0 < c) (q : Fin (c + 1) → ℝ)
    (h0 : q 0 < 1 / 6) (h1 : 1 / 3 ≤ q (Fin.last c)) :
    ∃ j : Fin c, 1 / (6 * (c : ℝ)) < q j.succ - q j.castSucc := by
  by_contra h
  push Not at h
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin c))) => h j)
  rw [cheatHybrid_telescope, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
  have hcr : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have he : (c : ℝ) * (1 / (6 * (c : ℝ))) = 1 / 6 := by field_simp
  rw [he] at hs
  linarith

private def sheetBit (k m : ℕ) : Bool := decide (k / 2 ^ m % 2 = 1)

/-- The remainder modulo the next power of two is the previous remainder plus the next binary
bit weighted by that power of two. -/
private theorem mod_two_pow_succ (c k : ℕ) :
    k % 2 ^ (c + 1) = k % 2 ^ c + 2 ^ c * (if sheetBit k c then 1 else 0) := by
  have hp : 0 < 2 ^ c := Nat.two_pow_pos c
  have hpow : 2 ^ (c + 1) = 2 * 2 ^ c := by rw [Nat.pow_succ, Nat.mul_comm]
  have hr : k % 2 ^ c < 2 ^ c := Nat.mod_lt _ hp
  have hdm : 2 ^ c * (k / 2 ^ c) + k % 2 ^ c = k := Nat.div_add_mod k (2 ^ c)
  split
  · next hs =>
    rw [mul_one]
    have hb : k / 2 ^ c % 2 = 1 := by simpa [sheetBit] using hs
    obtain ⟨u, hu⟩ : ∃ u, k / 2 ^ c = 2 * u + 1 := ⟨k / 2 ^ c / 2, by omega⟩
    have hk : k = (2 ^ c + k % 2 ^ c) + 2 ^ (c + 1) * u := by
      calc k = 2 ^ c * (k / 2 ^ c) + k % 2 ^ c := hdm.symm
        _ = 2 ^ c * (2 * u + 1) + k % 2 ^ c := by rw [hu]
        _ = (2 ^ c + k % 2 ^ c) + 2 ^ (c + 1) * u := by rw [hpow]; ring
    have hlt : 2 ^ c + k % 2 ^ c < 2 ^ (c + 1) := by rw [hpow]; omega
    conv_lhs => rw [hk]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    omega
  · next hs =>
    rw [mul_zero, add_zero]
    have hb : ¬ (k / 2 ^ c % 2 = 1) := by simpa [sheetBit] using hs
    obtain ⟨u, hu⟩ : ∃ u, k / 2 ^ c = 2 * u := ⟨k / 2 ^ c / 2, by omega⟩
    have hk : k = k % 2 ^ c + 2 ^ (c + 1) * u := by
      calc k = 2 ^ c * (k / 2 ^ c) + k % 2 ^ c := hdm.symm
        _ = 2 ^ c * (2 * u) + k % 2 ^ c := by rw [hu]
        _ = k % 2 ^ c + 2 ^ (c + 1) * u := by rw [hpow]; ring
    have hlt : k % 2 ^ c < 2 ^ (c + 1) := by rw [hpow]; omega
    conv_lhs => rw [hk]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The weighted sum of the first `c` binary bits of a natural number equals its remainder
modulo two to the power `c`. -/
private theorem sum_sheetBit_mod (c : ℕ) : ∀ k : ℕ,
    ∑ m ∈ Finset.range c, (if sheetBit k m then 2 ^ m else 0) = k % 2 ^ c := by
  induction c with
  | zero => intro k; simp [Nat.mod_one]
  | succ c ih =>
      intro k
      rw [Finset.sum_range_succ, ih k, mod_two_pow_succ]
      split <;> simp

/-- Reconstructing a sheet index from its binary bits recovers the original index. -/
private theorem sheetIndex_sheetBit {c : ℕ} (k : Fin (2 ^ c)) :
    sheetIndex (fun m : Fin c => sheetBit (k : ℕ) (m : ℕ)) = k := by
  have h : ∑ m : Fin c, (if sheetBit (k : ℕ) (m : ℕ) then 2 ^ (m : ℕ) else 0) = (k : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => if sheetBit (k : ℕ) m then 2 ^ m else 0) c,
      sum_sheetBit_mod, Nat.mod_eq_of_lt k.isLt]
  exact Fin.ext (by simpa [sheetIndex] using h)

/-- The sheet index of the all-false vector is zero. -/
private theorem sheetIndex_false {c : ℕ} :
    sheetIndex (fun _ : Fin c => false) = 0 := by
  refine Fin.ext ?_
  simp [sheetIndex]

private def chainVec {c : ℕ} (ℓ : Fin (2 ^ c)) (j : ℕ) : Fin c → Bool :=
  fun m => if (m : ℕ) < j then sheetBit (ℓ : ℕ) (m : ℕ) else false

/-- The zeroth chain vector is the all-false vector. -/
private theorem chainVec_zero {c : ℕ} (ℓ : Fin (2 ^ c)) : chainVec ℓ 0 = fun _ => false := by
  funext m; simp [chainVec]

/-- The final chain vector consists of the binary bits of the sheet index. -/
private theorem chainVec_self {c : ℕ} (ℓ : Fin (2 ^ c)) :
    chainVec ℓ c = fun m : Fin c => sheetBit (ℓ : ℕ) (m : ℕ) := by
  funext m; simp [chainVec, m.isLt]

/-- The next chain vector is obtained by updating its current coordinate to the corresponding
sheet bit. -/
private theorem chainVec_succ_update {c : ℕ} (ℓ : Fin (2 ^ c)) (j : Fin c) :
    chainVec ℓ ((j : ℕ) + 1) = Function.update (chainVec ℓ (j : ℕ)) j (sheetBit (ℓ : ℕ) (j : ℕ)) := by
  funext m
  by_cases hm : m = j
  · subst hm
    simp [chainVec, Function.update_self]
  · have hmval : (m : ℕ) ≠ (j : ℕ) := fun h => hm (Fin.ext h)
    rcases Nat.lt_trichotomy (m : ℕ) (j : ℕ) with h1 | h1 | h1
    · simp [chainVec, Function.update_of_ne hm, h1, Nat.lt_succ_of_lt h1]
    · exact absurd (Fin.ext h1) hm
    · have hms : ¬ (m : ℕ) < (j : ℕ) + 1 := by omega
      have hnlt : ¬ (m : ℕ) < (j : ℕ) := by omega
      simp [chainVec, Function.update_of_ne hm, hnlt, hms]

private def Dsel {M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Bool) : PMF (Fin M → Bool) :=
  if b then D₁ else D₀

private noncomputable def DprodMass {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (X : Fin c → (Fin M → Bool)) : ℝ≥0∞ :=
  ∏ m, Dsel D₀ D₁ (b m) (X m)

/-- The product distribution mass sums to one over all block tuples. -/
private theorem dprodMass_eq_one {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool) :
    ∑ X, DprodMass D₀ D₁ b X = 1 := by
  classical
  have hinner : ∀ (bb : Bool), (∑ x : Fin M → Bool, Dsel D₀ D₁ bb x) = 1 := by
    intro bb
    cases bb
    · exact (tsum_fintype (fun x : Fin M → Bool => D₀ x)).symm.trans (PMF.tsum_coe D₀)
    · exact (tsum_fintype (fun x : Fin M → Bool => D₁ x)).symm.trans (PMF.tsum_coe D₁)
  have h := Finset.prod_univ_sum (fun _ : Fin c => (Finset.univ : Finset (Fin M → Bool)))
    (fun m (x : Fin M → Bool) => Dsel D₀ D₁ (b m) x)
  rw [Fintype.piFinset_univ] at h
  calc ∑ X, DprodMass D₀ D₁ b X
      = ∑ X : Fin c → (Fin M → Bool), ∏ m, Dsel D₀ D₁ (b m) (X m) := rfl
    _ = ∏ m, ∑ x : Fin M → Bool, Dsel D₀ D₁ (b m) x := h.symm
    _ = 1 := Finset.prod_eq_one fun m _ => hinner (b m)

/-- Factors a product distribution mass into the selected block's mass and the product over all
other blocks. -/
private theorem dprodMass_erase {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (X : Fin c → (Fin M → Bool)) (j : Fin c) :
    DprodMass D₀ D₁ b X =
      Dsel D₀ D₁ (b j) (X j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (X m) := by
  show (∏ m, Dsel D₀ D₁ (b m) (X m)) = _
  exact (Finset.mul_prod_erase Finset.univ (fun m => Dsel D₀ D₁ (b m) (X m))
    (Finset.mem_univ j)).symm

private def plantBlock {c M : ℕ} (X : Fin c → (Fin M → Bool)) (j : Fin c)
    (x : Fin M → Bool) : Fin c → (Fin M → Bool) :=
  Function.update X j x

/-- The planted block has the supplied replacement value at its selected index. -/
private theorem plantBlock_self {c M : ℕ} (X : Fin c → (Fin M → Bool)) (j : Fin c)
    (x : Fin M → Bool) : plantBlock X j x j = x :=
  by simp [plantBlock]

/-- Planting a block leaves every other block unchanged. -/
private theorem plantBlock_of_ne {c M : ℕ} (X : Fin c → (Fin M → Bool)) (j : Fin c)
    (x : Fin M → Bool) (m : Fin c) (hm : m ≠ j) : plantBlock X j x m = X m :=
  by simp [plantBlock, hm]

/-- Planting the existing value of a block leaves the block tuple unchanged. -/
private theorem plantBlock_eq_self {c M : ℕ} (X : Fin c → (Fin M → Bool)) (j : Fin c) :
    plantBlock X j (X j) = X :=
  by simp [plantBlock]

/-- Planting a block leaves the product of selected distribution masses over all other blocks
unchanged. -/
private theorem dprod_off_update {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (X : Fin c → (Fin M → Bool)) (j : Fin c) (x : Fin M → Bool) :
    (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (plantBlock X j x m)) =
      ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (X m) := by
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [plantBlock_of_ne X j x m (Finset.ne_of_mem_erase hm)]

private def blockOracle {c M κ : ℕ} (X : Fin c → (Fin M → Bool)) :
    CheatSheetIndex c M κ → Bool :=
  Sum.elim (fun p : Fin c × Fin M => X p.1 p.2) (fun _ => false)

private noncomputable def hitMass {c M κ : ℕ} (ℓ : Fin (2 ^ c)) (X : Fin c → (Fin M → Bool))
    (τ : BoolQueryTree (CheatSheetIndex c M κ) Bool) : ℝ≥0∞ :=
  if ∃ i b, Sum.inr (ℓ, i, b) ∈ queriesOf (blockOracle X) τ then 1 else 0

private noncomputable def Qvec {c M κ : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (ℓ : Fin (2 ^ c)) (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) : ℝ≥0∞ :=
  ∑' τ, A τ * ∑' X, DprodMass D₀ D₁ b X * hitMass ℓ X τ

/-- The hit mass of a sheet for a deterministic tree is at most one. -/
private theorem hitMass_le_one {c M κ : ℕ} (ℓ : Fin (2 ^ c)) (X : Fin c → (Fin M → Bool))
    (τ : BoolQueryTree (CheatSheetIndex c M κ) Bool) : hitMass ℓ X τ ≤ 1 := by
  unfold hitMass; split <;> simp

/-- The finite sum of a probability mass function is one. -/
private theorem finset_sum_pmf_eq_one {α : Type} [Fintype α] (p : PMF α) : ∑ a, p a = 1 :=
  (tsum_fintype (fun a => p a)).symm.trans (PMF.tsum_coe p)

/-- Every component `Qvec` is at most one. -/
private theorem qvec_le_one {c M κ : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (ℓ : Fin (2 ^ c)) (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    Qvec D₀ D₁ b ℓ A ≤ 1 := by
  have hinner : ∀ τ : BoolQueryTree (CheatSheetIndex c M κ) Bool,
      (∑' X, DprodMass D₀ D₁ b X * hitMass ℓ X τ) ≤ 1 := by
    intro τ
    have hmono : ∀ X : Fin c → (Fin M → Bool),
        DprodMass D₀ D₁ b X * hitMass ℓ X τ ≤ DprodMass D₀ D₁ b X * 1 :=
      fun X => mul_le_mul le_rfl (hitMass_le_one ℓ X τ) (by simp) (by simp)
    refine le_trans (ENNReal.tsum_le_tsum hmono) ?_
    rw [ENNReal.tsum_mul_right, tsum_fintype (f := fun X => DprodMass D₀ D₁ b X),
      dprodMass_eq_one, mul_one]
  have hmono : ∀ τ : BoolQueryTree (CheatSheetIndex c M κ) Bool,
      A τ * (∑' X, DprodMass D₀ D₁ b X * hitMass ℓ X τ) ≤ A τ * 1 :=
    fun τ => mul_le_mul le_rfl (hinner τ) (by simp) (by simp)
  refine le_trans (ENNReal.tsum_le_tsum hmono) ?_
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe A, mul_one]

/-- Every component `Qvec` is finite. -/
private theorem qvec_ne_top {c M κ : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (ℓ : Fin (2 ^ c)) (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    Qvec D₀ D₁ b ℓ A ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (qvec_le_one D₀ D₁ b ℓ A)

/-- Expands `Qvec` as a product-distribution average of the tree-distribution average of hit
masses. -/
private theorem qvec_eq_massFun {c M κ : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (ℓ : Fin (2 ^ c)) (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    Qvec D₀ D₁ b ℓ A =
      ∑' Y, DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ := by
  calc Qvec D₀ D₁ b ℓ A
      = ∑' τ, ∑' X, A τ * (DprodMass D₀ D₁ b X * hitMass ℓ X τ) := by
        refine tsum_congr fun τ => (ENNReal.tsum_mul_left (a := A τ)
          (f := fun X => DprodMass D₀ D₁ b X * hitMass ℓ X τ)).symm
    _ = ∑' X, ∑' τ, A τ * (DprodMass D₀ D₁ b X * hitMass ℓ X τ) := ENNReal.tsum_comm
    _ = ∑' Y, DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ := by
        refine tsum_congr fun X => ?_
        rw [← ENNReal.tsum_mul_left (a := DprodMass D₀ D₁ b X)
          (f := fun τ => A τ * hitMass ℓ X τ)]
        exact tsum_congr fun τ => by
          rw [← mul_assoc, mul_comm (A τ) (DprodMass D₀ D₁ b X), mul_assoc]

/-- Expands randomized tree success probability as the sum of tree masses weighted by the
success indicator. -/
private theorem successProb_eq_tsum {Q : Type} [Fintype Q] [DecidableEq Q]
    (A : PMF (BoolQueryTree Q Bool)) (x : Q → Bool) (E : Bool → Prop) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x E =
      ∑' τ, A τ * (if E (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 then (1 : ℝ≥0∞) else 0) := by
  rw [treeSuccessProb_outer, PMF.toOuterMeasure_apply]
  refine tsum_congr fun τ => ?_
  by_cases h : E (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 <;> simp [h]

/-- Expands the probability of output true as the sum of tree masses weighted by their Boolean
outputs. -/
private theorem successProb_true_eq {Q : Type} [Fintype Q] [DecidableEq Q]
    (A : PMF (BoolQueryTree Q Bool)) (x : Q → Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x (fun b => b = true) =
      ∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 then (1 : ℝ≥0∞) else 0) := by
  rw [successProb_eq_tsum]
  refine tsum_congr fun τ => ?_
  by_cases h : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 <;> simp [h]

/-- Randomized tree success probability is at most one. -/
private theorem successProb_le_one {Q : Type} [Fintype Q] [DecidableEq Q]
    (A : PMF (BoolQueryTree Q Bool)) (x : Q → Bool) (E : Bool → Prop) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x E ≤ 1 := by
  rw [successProb_eq_tsum]
  have hmono : ∀ τ : BoolQueryTree Q Bool,
      A τ * (if E (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 then (1 : ℝ≥0∞) else 0) ≤ A τ * 1 := by
    intro τ
    refine mul_le_mul le_rfl ?_ (by simp) (by simp)
    split <;> simp
  refine le_trans (ENNReal.tsum_le_tsum hmono) ?_
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe A, mul_one]

/-- Randomized tree success probability is finite. -/
private theorem successProb_ne_top {Q : Type} [Fintype Q] [DecidableEq Q]
    (A : PMF (BoolQueryTree Q Bool)) (x : Q → Bool) (E : Bool → Prop) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x E ≠ ∞ :=
  ne_top_of_le_ne_top (by simp) (successProb_le_one A x E)

/-- The probabilities of output true and output false sum to one. -/
private theorem successProb_compl {Q : Type} [Fintype Q] [DecidableEq Q]
    (A : PMF (BoolQueryTree Q Bool)) (x : Q → Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x (fun b => b = true) +
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x (fun b => b = false) = 1 := by
  have hsum : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x (fun b => b = true) +
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A x (fun b => b = false) = ∑' τ, A τ * 1 := by
    rw [successProb_eq_tsum, successProb_eq_tsum, ← ENNReal.tsum_add]
    refine tsum_congr fun τ => ?_
    by_cases h : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x τ).1 <;> simp [h]
  rw [hsum, ENNReal.tsum_mul_right, PMF.tsum_coe, mul_one]

/-- The query count returned by a tree run equals the length of its query list. -/
private theorem run_count_eq_queriesOf_length {Q : Type} {Output : Type} (o : Q → Bool)
    (τ : BoolQueryTree Q Output) :
    (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run o τ).2 = (queriesOf o τ).length := by
  induction τ with
  | halt _ => rfl
  | ask q f t ihf iht =>
      by_cases h : o q <;>
        simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run, queriesOf, h, ihf,
            iht, add_comm]

/-- The sum of hit masses over all sheets is at most the tree's maximum query count. -/
private theorem sheetHit_sum_le {c M κ : ℕ} (X : Fin c → (Fin M → Bool))
    (τ : BoolQueryTree (CheatSheetIndex c M κ) Bool) :
    ∑ ℓ : Fin (2 ^ c), hitMass ℓ X τ ≤ (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ : ℝ≥0∞) := by
  classical
  set SL : Finset (Fin (2 ^ c)) :=
    (((queriesOf (blockOracle X) τ).filter Sum.isRight).map
      (fun q : CheatSheetIndex c M κ =>
        Sum.elim (fun _ : Fin c × Fin M => (0 : Fin (2 ^ c))) (fun p => p.1) q)).toFinset
    with hSL
  have hmem : ∀ ℓ : Fin (2 ^ c), hitMass ℓ X τ ≠ 0 → ℓ ∈ SL := by
    intro ℓ hℓ
    by_cases hc : ∃ i b, Sum.inr (ℓ, i, b) ∈ queriesOf (blockOracle X) τ
    · obtain ⟨i, k, hk⟩ := hc
      refine List.mem_toFinset.mpr (List.mem_map.mpr ⟨Sum.inr (ℓ, i, k), ?_, rfl⟩)
      exact List.mem_filter.mpr ⟨hk, by simp⟩
    · exfalso
      apply hℓ
      rw [hitMass, ite_eq_right hc]
  have hzero : ∀ ℓ ∈ (Finset.univ : Finset (Fin (2 ^ c))), ℓ ∉ SL → hitMass ℓ X τ = 0 := by
    intro ℓ _ h
    by_cases hc : ∃ i b, Sum.inr (ℓ, i, b) ∈ queriesOf (blockOracle X) τ
    · exact absurd (hmem ℓ (by rw [hitMass, ite_eq_left hc]; exact one_ne_zero)) h
    · rw [hitMass, ite_eq_right hc]
  have hsub : ∑ ℓ ∈ SL, hitMass ℓ X τ = ∑ ℓ : Fin (2 ^ c), hitMass ℓ X τ :=
    Finset.sum_subset (fun ℓ _ => Finset.mem_univ ℓ) hzero
  have hlen : SL.card ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ := by
    have h1 : SL.card ≤ ((queriesOf (blockOracle X) τ).filter Sum.isRight).length := by
      rw [hSL]
      exact le_trans (List.toFinset_card_le
        (List.map (fun q : CheatSheetIndex c M κ =>
          Sum.elim (fun _ : Fin c × Fin M => (0 : Fin (2 ^ c))) (fun p => p.1) q)
          (List.filter Sum.isRight (queriesOf (blockOracle X) τ)))) (by simp)
    have h2 : (queriesOf (blockOracle X) τ).length ≤
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ := by
      rw [← run_count_eq_queriesOf_length]
      exact Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.run_queries_le _ _
    exact le_trans (le_trans h1
      (List.length_filter_le Sum.isRight (queriesOf (blockOracle X) τ))) h2
  calc ∑ ℓ : Fin (2 ^ c), hitMass ℓ X τ
      = ∑ ℓ ∈ SL, hitMass ℓ X τ := hsub.symm
    _ ≤ ∑ ℓ ∈ SL, (1 : ℝ≥0∞) := Finset.sum_le_sum fun ℓ _ => hitMass_le_one ℓ X τ
    _ = SL.card := by simp
    _ ≤ (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ : ℝ≥0∞) := by exact_mod_cast hlen

/-- A randomized tree program solving the certifying cheat-sheet function with error one third
hits the correctly indexed sheet with probability at least one third on valid block tuples. -/
private theorem hitTotal_ge_one_third {c M κ : ℕ} (hκ : 0 < κ) (hc : 0 < c)
    (dom : (Fin M → Bool) → Prop) (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (hcert : IsCertifying M κ hκ dom g φ)
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool))
    (hsolve : SolvesTotalTree (cheatSheetFun (c := c) g φ) A (1 / 3))
    (b : Fin c → Bool)
    (X : Fin c → (Fin M → Bool)) (hsup : ∀ m, dom (X m) ∧ g (X m) = b m) :
    (1 / 3 : ℝ) ≤ (∑' τ, A τ * hitMass (sheetIndex b) X τ).toReal := by
  classical
  have hex : ∀ m : Fin c, ∃ y, φ (X m) y = true := fun m => hcert.2.1 (X m) (hsup m).1
  choose! Y hY using hex
  set z : CheatSheetIndex c M κ → Bool := blockOracle X with hzdef
  set z' : CheatSheetIndex c M κ → Bool :=
    Sum.elim (fun p : Fin c × Fin M => X p.1 p.2)
      (fun p : Fin (2 ^ c) × Fin c × Fin κ =>
        if p.1 = sheetIndex b then Y p.2.1 p.2.2 else false)
    with hz'def
  have hfunz : cheatSheetFun (c := c) g φ z = false := by
    refine Bool.eq_false_iff.mpr fun h => ?_
    have hh := of_decide_eq_true h
    have h0 := hh ⟨0, hc⟩
    rw [hzdef] at h0
    have h0' : φ (X ⟨0, hc⟩) (fun _ => false) = true := h0
    rw [hcert.2.2 (X ⟨0, hc⟩)] at h0'
    exact Bool.noConfusion h0'
  have hsel : sheetIndex b = sheetIndex fun i => g (cheatBlock z' i) := by
    congr 1
    funext m
    exact (hsup m).2.symm
  have hcertcheck : ∀ i : Fin c,
      φ (cheatBlock z' i) (cheatCert z' (sheetIndex b) i) = true := by
    intro i
    have hc : cheatCert z' (sheetIndex b) i = Y i := by
      funext j
      rw [hz'def]
      show (if ((sheetIndex b, i, j) : Fin (2 ^ c) × (Fin c × Fin κ)).1 = sheetIndex b
          then Y ((sheetIndex b, i, j) : Fin (2 ^ c) × (Fin c × Fin κ)).2.1
              ((sheetIndex b, i, j) : Fin (2 ^ c) × (Fin c × Fin κ)).2.2 else false) = Y i j
      rw [ite_eq_left rfl]
    rw [hc]
    exact hY i
  have hfunz' : cheatSheetFun (c := c) g φ z' = true :=
    (cheatSheetBasicSemantics c M κ g φ hcert.2.2).2 z' (sheetIndex b) hsel hcertcheck
  have hslvz' := hsolve z'
  rw [hfunz'] at hslvz'
  have hslvz := hsolve z
  rw [hfunz] at hslvz
  set B : Finset (CheatSheetIndex c M κ) :=
    (Finset.univ : Finset (Fin c × Fin κ)).image
      (fun p => Sum.inr (sheetIndex b, p)) with hB
  have hagree : ∀ q : CheatSheetIndex c M κ, q ∉ B → z q = z' q := by
    intro q hq
    cases q with
    | inl p =>
        rw [hzdef, hz'def]
        rfl
    | inr p =>
        by_cases hp : p.1 = sheetIndex b
        · exfalso
          apply hq
          refine Finset.mem_image.mpr ⟨p.2, Finset.mem_univ _, ?_⟩
          rw [← hp]
        · rw [hzdef, hz'def]
          simp only [blockOracle, Sum.elim_inr, ite_eq_right hp]
  have hpt : ∀ τ : BoolQueryTree (CheatSheetIndex c M κ) Bool,
      (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0) ≤
        (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then 1 else 0) +
        hitMass (sheetIndex b) X τ := by
    intro τ
    obtain ⟨hiff, hout⟩ :=
      queryTreeAgreementInvariance (CheatSheetIndex c M κ) z z' B τ hagree
    by_cases h1 : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1
    · simp only [h1, ite_true]
      split <;> simp
    · by_cases h2 : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1
      · have hne : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 ≠ (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 := by
          simp [h1, h2]
        have hhit : ∃ q, q ∈ B ∧ q ∈ queriesOf z τ := by
          by_contra hcon
          exact hne (hout hcon).symm
        have hhitmass : hitMass (sheetIndex b) X τ = 1 := by
          unfold hitMass
          refine ite_eq_left ?_
          obtain ⟨q, hqB, hqL⟩ := hhit
          rw [hzdef] at hqL
          obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hqB
          rw [← hp] at hqL
          exact ⟨p.1, p.2, hqL⟩
        simp [h1, h2, hhitmass]
      · simp [h1, h2]
  have hmono : ∀ τ : BoolQueryTree (CheatSheetIndex c M κ) Bool,
      A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0) ≤
      A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0) +
        A τ * hitMass (sheetIndex b) X τ := by
    intro τ
    calc A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0)
        ≤ A τ * ((if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0) +
            hitMass (sheetIndex b) X τ) :=
          mul_le_mul le_rfl (hpt τ) (by simp) (by simp)
      _ = A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0) +
          A τ * hitMass (sheetIndex b) X τ := mul_add _ _ _
  have hagg : ∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0) ≤
      (∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0)) +
      ∑' τ, A τ * hitMass (sheetIndex b) X τ := by
    have h1 : ∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0) ≤
        ∑' τ, (A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0) +
          A τ * hitMass (sheetIndex b) X τ) :=
      ENNReal.tsum_le_tsum hmono
    rw [ENNReal.tsum_add] at h1
    exact h1
  have hSPz' : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A z' (fun bb => bb = true) =
      ∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0) :=
    successProb_true_eq A z'
  have hSPz : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A z (fun bb => bb = true) =
      ∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0) :=
    successProb_true_eq A z
  rw [hSPz'] at hslvz'
  have hneSP := successProb_ne_top A z (fun bb => bb = true)
  have hhitne : (∑' τ, A τ * hitMass (sheetIndex b) X τ) ≠ ∞ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑' τ, A τ * hitMass (sheetIndex b) X τ
        ≤ ∑' τ, A τ * (1 : ℝ≥0∞) :=
          ENNReal.tsum_le_tsum fun τ =>
            mul_le_mul le_rfl (hitMass_le_one _ X τ) (by simp) (by simp)
      _ = ∑' τ, A τ := tsum_congr fun τ => mul_one _
      _ = 1 := PMF.tsum_coe A
  have hneT : (∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0)) ≠ ∞ := by
    rw [← hSPz]
    exact successProb_ne_top A z (fun bb => bb = true)
  have hsumne : ((∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z τ).1 then (1 : ℝ≥0∞) else 0)) +
      ∑' τ, A τ * hitMass (sheetIndex b) X τ) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hneT, hhitne⟩
  have h4 := ENNReal.toReal_mono hsumne hagg
  rw [ENNReal.toReal_add hneT hhitne] at h4
  have e1' : (2 / 3 : ℝ) ≤
      (∑' τ, A τ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run z' τ).1 then (1 : ℝ≥0∞) else 0)).toReal := by
    have h5 : (2 / 3 : ℝ) = 1 - 1 / 3 := by norm_num
    rw [h5]
    exact hslvz'
  have e2' : (2 / 3 : ℝ) ≤
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A z (fun bb => bb = false)).toReal := by
    have h5 := hslvz
    norm_num at h5
    exact h5
  have hcomp : (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A z (fun bb => bb = true)).toReal +
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb A z (fun bb => bb = false)).toReal = 1 := by
    have h6 := congrArg ENNReal.toReal (successProb_compl A z)
    rw [ENNReal.toReal_add hneSP (successProb_ne_top A z (fun bb => bb = false)),
      ENNReal.toReal_one] at h6
    exact h6
  rw [hSPz] at hcomp
  linarith

/-- Under the certifying, support, and solving assumptions, `Qvec` at the sheet indexed by its
own block labels is at least one third after conversion to a real number. -/
private theorem qvec_self_ge {c M κ : ℕ} (hκ : 0 < κ) (hc : 0 < c)
    (dom : (Fin M → Bool) → Prop) (g : (Fin M → Bool) → Bool)
    (φ : (Fin M → Bool) → (Fin κ → Bool) → Bool)
    (hcert : IsCertifying M κ hκ dom g φ)
    (D₀ D₁ : PMF (Fin M → Bool))
    (hD₀ : ∀ x, D₀ x ≠ 0 → dom x ∧ g x = false)
    (hD₁ : ∀ x, D₁ x ≠ 0 → dom x ∧ g x = true)
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool))
    (hsolve : SolvesTotalTree (cheatSheetFun (c := c) g φ) A (1 / 3))
    (b : Fin c → Bool) :
    (1 / 3 : ℝ) ≤ (Qvec D₀ D₁ b (sheetIndex b) A).toReal := by
  refine (ENNReal.ofReal_le_iff_le_toReal (qvec_ne_top D₀ D₁ b (sheetIndex b) A)).mp ?_
  have hpt : ∀ Y : Fin c → (Fin M → Bool),
      DprodMass D₀ D₁ b Y * ENNReal.ofReal (1 / 3 : ℝ) ≤
      DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass (sheetIndex b) Y τ := by
    intro Y
    by_cases hsupY : ∀ m, Dsel D₀ D₁ (b m) (Y m) ≠ 0
    · have hsup : ∀ m, dom (Y m) ∧ g (Y m) = b m := by
        intro m
        cases bm : b m with
        | false =>
            have h0 : D₀ (Y m) ≠ 0 := by
              have hs := hsupY m
              rw [bm] at hs
              simpa [Dsel] using hs
            exact hD₀ (Y m) h0
        | true =>
            have h0 : D₁ (Y m) ≠ 0 := by
              have hs := hsupY m
              rw [bm] at hs
              simpa [Dsel] using hs
            exact hD₁ (Y m) h0
      have h1 := hitTotal_ge_one_third hκ hc dom g φ hcert A hsolve b Y hsup
      have hne : (∑' τ, A τ * hitMass (sheetIndex b) Y τ) ≠ ∞ := by
        refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        refine le_trans (ENNReal.tsum_le_tsum fun τ =>
          mul_le_mul le_rfl (hitMass_le_one _ Y τ) (by simp) (by simp)) ?_
        rw [ENNReal.tsum_mul_right, PMF.tsum_coe A, mul_one]
      exact mul_le_mul le_rfl ((ENNReal.ofReal_le_iff_le_toReal hne).mpr h1)
        (by simp) (by simp)
    · push Not at hsupY
      obtain ⟨m, hm⟩ := hsupY
      have hz : DprodMass D₀ D₁ b Y = 0 := by
        unfold DprodMass
        exact Finset.prod_eq_zero (Finset.mem_univ m) hm
      rw [hz]
      simp
  calc ENNReal.ofReal (1 / 3 : ℝ)
      = ENNReal.ofReal (1 / 3 : ℝ) * (∑' Y, DprodMass D₀ D₁ b Y) := by
        rw [tsum_fintype, dprodMass_eq_one, mul_one]
    _ = ∑' Y, ENNReal.ofReal (1 / 3 : ℝ) * DprodMass D₀ D₁ b Y :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' Y, DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass (sheetIndex b) Y τ :=
        ENNReal.tsum_le_tsum fun Y => by rw [mul_comm]; exact hpt Y
    _ = Qvec D₀ D₁ b (sheetIndex b) A := (qvec_eq_massFun D₀ D₁ b (sheetIndex b) A).symm

/-- A finite sum and an infinite sum of extended nonnegative real terms can be interchanged. -/
private theorem finset_tsum_swap {α β : Type} [Fintype α] (f : α → β → ℝ≥0∞) :
    ∑ a : α, ∑' b, f a b = ∑' b, ∑ a : α, f a b := by
  calc ∑ a : α, ∑' b, f a b
      = ∑' a : α, ∑' b, f a b := (tsum_fintype (f := fun a => ∑' b, f a b)).symm
    _ = ∑' b, ∑' a, f a b := ENNReal.tsum_comm
    _ = ∑' b, ∑ a : α, f a b := tsum_congr fun b => tsum_fintype (f := fun a => f a b)

/-- A constant extended nonnegative real factor can be pulled out of a finite sum. -/
private theorem sum_mul_pull {α : Type} [Fintype α] (a : ℝ≥0∞) (f : α → ℝ≥0∞) :
    ∑ i : α, a * f i = a * ∑ i : α, f i := by rw [Finset.mul_sum]

/-- For a program bounded by `T` queries, the sum of its `Qvec` components is at most `T`. -/
private theorem qvec_sum_le {c M κ : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) (T : ℕ)
    (hA : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries A T) :
    ∑ ℓ : Fin (2 ^ c), Qvec D₀ D₁ b ℓ A ≤ (T : ℝ≥0∞) := by
  have hinner : ∀ Y : Fin c → (Fin M → Bool),
      (∑ ℓ : Fin (2 ^ c), ∑' τ, A τ * hitMass ℓ Y τ) ≤ (T : ℝ≥0∞) := by
    intro Y
    calc ∑ ℓ : Fin (2 ^ c), ∑' τ, A τ * hitMass ℓ Y τ
        = ∑' τ, ∑ ℓ : Fin (2 ^ c), A τ * hitMass ℓ Y τ :=
          finset_tsum_swap fun ℓ τ => A τ * hitMass ℓ Y τ
      _ = ∑' τ, A τ * (∑ ℓ : Fin (2 ^ c), hitMass ℓ Y τ) :=
          tsum_congr fun τ => sum_mul_pull (A τ) fun ℓ => hitMass ℓ Y τ
      _ ≤ ∑' τ, A τ * (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries τ : ℝ≥0∞) :=
          ENNReal.tsum_le_tsum fun τ =>
            mul_le_mul le_rfl (sheetHit_sum_le Y τ) (by simp) (by simp)
      _ ≤ ∑' τ, A τ * (T : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun τ => ?_
          by_cases h0 : A τ = 0
          · simp [h0]
          · exact mul_le_mul le_rfl (by exact_mod_cast hA τ h0) (by simp) (by simp)
      _ = (T : ℝ≥0∞) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe A, one_mul]
  calc ∑ ℓ : Fin (2 ^ c), Qvec D₀ D₁ b ℓ A
      = ∑ ℓ : Fin (2 ^ c), ∑' Y, DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ :=
        Finset.sum_congr rfl fun ℓ _ => qvec_eq_massFun D₀ D₁ b ℓ A
    _ = ∑' Y, ∑ ℓ : Fin (2 ^ c), DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ :=
        finset_tsum_swap fun ℓ Y => DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ
    _ = ∑ Y, ∑ ℓ : Fin (2 ^ c), DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ :=
        tsum_fintype (f := fun Y : Fin c → (Fin M → Bool) =>
          ∑ ℓ : Fin (2 ^ c), DprodMass D₀ D₁ b Y * ∑' τ, A τ * hitMass ℓ Y τ)
    _ = ∑ Y, DprodMass D₀ D₁ b Y * (∑ ℓ : Fin (2 ^ c), ∑' τ, A τ * hitMass ℓ Y τ) :=
        Finset.sum_congr rfl fun Y _ =>
          sum_mul_pull (DprodMass D₀ D₁ b Y) fun ℓ => ∑' τ, A τ * hitMass ℓ Y τ
    _ ≤ ∑ Y, DprodMass D₀ D₁ b Y * (T : ℝ≥0∞) :=
        Finset.sum_le_sum fun Y _ =>
          mul_le_mul le_rfl (hinner Y) (by simp) (by simp)
    _ = (∑ Y, DprodMass D₀ D₁ b Y) * (T : ℝ≥0∞) :=
        (Finset.sum_mul (s := (Finset.univ : Finset (Fin c → (Fin M → Bool))))
          (f := fun Y => DprodMass D₀ D₁ b Y) (a := (T : ℝ≥0∞))).symm
    _ = (T : ℝ≥0∞) := by rw [dprodMass_eq_one, one_mul]

/-- Selecting a distribution with label true gives the mass function of the second distribution. -/
private theorem Dsel_true {M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (x : Fin M → Bool) :
    Dsel D₀ D₁ true x = D₁ x := by simp [Dsel]

/-- Selecting a distribution with label false gives the mass function of the first distribution. -/
private theorem Dsel_false {M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (x : Fin M → Bool) :
    Dsel D₀ D₁ false x = D₀ x := by simp [Dsel]

/-- Planting twice at the same block index leaves only the second replacement. -/
private theorem plantBlock_plantBlock {c M : ℕ} (X : Fin c → (Fin M → Bool)) (j : Fin c)
    (v x : Fin M → Bool) :
    plantBlock (plantBlock X j v) j x = plantBlock X j x := by
  simp [plantBlock]

/-- Updating a block label to true factors the product mass into the second distribution's
selected-block mass and the unchanged other-block product. -/
private theorem dprodMass_update_true {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (j : Fin c) (Y : Fin c → (Fin M → Bool)) :
    DprodMass D₀ D₁ (Function.update b j true) Y =
      D₁ (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m) := by
  unfold DprodMass
  rw [← Finset.mul_prod_erase Finset.univ
      (fun m => Dsel D₀ D₁ (Function.update b j true m) (Y m)) (Finset.mem_univ j),
    Function.update_self, Dsel_true]
  exact congrArg _ (Finset.prod_congr rfl fun m hm => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)])

/-- Averaging after planting a fresh block from `E` equals averaging with its coordinate mass
replaced by `E` and all other coordinate masses unchanged. -/
private theorem planted_fiber {c M : ℕ} (D₀ D₁ E : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (j : Fin c) (hb : b j = false)
    (F : (Fin c → (Fin M → Bool)) → ℝ≥0∞) :
    ∑' x, E x * ∑' X, DprodMass D₀ D₁ b X * F (plantBlock X j x) =
      ∑' Y, E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y := by
  classical
  have hcore : ∑ x : Fin M → Bool, ∑ X : Fin c → (Fin M → Bool),
        E x * (DprodMass D₀ D₁ b X * F (plantBlock X j x)) =
      ∑ Y : Fin c → (Fin M → Bool),
        E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y := by
    have hpair : ∑ x : Fin M → Bool, ∑ X : Fin c → (Fin M → Bool),
        E x * (DprodMass D₀ D₁ b X * F (plantBlock X j x)) =
      ∑ p : (Fin M → Bool) × (Fin c → (Fin M → Bool)),
        E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)) :=
      (Fintype.sum_prod_type' (f := fun (x : Fin M → Bool) (X : Fin c → (Fin M → Bool)) =>
        E x * (DprodMass D₀ D₁ b X * F (plantBlock X j x)))).symm
    have hfiber : ∑ p : (Fin M → Bool) × (Fin c → (Fin M → Bool)),
        E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)) =
      ∑ Y : Fin c → (Fin M → Bool),
        ∑ p ∈ Finset.univ.filter (fun (p : (Fin M → Bool) × (Fin c → (Fin M → Bool))) => plantBlock p.2 j p.1 = Y),
          E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)) := by
      have h1 := Finset.sum_fiberwise_eq_sum_filter
        (s := (Finset.univ : Finset ((Fin M → Bool) × (Fin c → (Fin M → Bool)))))
        (t := (Finset.univ : Finset (Fin c → (Fin M → Bool))))
        (g := fun p : (Fin M → Bool) × (Fin c → (Fin M → Bool)) => plantBlock p.2 j p.1)
        (f := fun p : (Fin M → Bool) × (Fin c → (Fin M → Bool)) =>
          E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)))
      simp at h1
      exact h1.symm
    have hfib : ∀ Y : Fin c → (Fin M → Bool),
        (∑ p ∈ Finset.univ.filter (fun (p : (Fin M → Bool) × (Fin c → (Fin M → Bool))) => plantBlock p.2 j p.1 = Y),
            E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1))) =
          (E (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y := by
      intro Y
      have hmem : ∀ u : Fin M → Bool,
          (Y j, plantBlock Y j u) ∈
            Finset.univ.filter (fun (p : (Fin M → Bool) × (Fin c → (Fin M → Bool))) => plantBlock p.2 j p.1 = Y) := by
        intro u
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [plantBlock_plantBlock Y j u (Y j), plantBlock_eq_self Y j]
      have harg : ∀ p : (Fin M → Bool) × (Fin c → (Fin M → Bool)),
          plantBlock p.2 j p.1 = Y → p.1 = Y j := by
        intro p hYp
        have h : plantBlock p.2 j p.1 j = Y j := by rw [hYp]
        rwa [plantBlock_self] at h
      have hoff : ∀ p : (Fin M → Bool) × (Fin c → (Fin M → Bool)),
          plantBlock p.2 j p.1 = Y →
          (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (p.2 m)) =
            ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m) := by
        intro p hYp
        refine Finset.prod_congr rfl fun m hm => ?_
        have h : plantBlock p.2 j p.1 m = Y m := by rw [hYp]
        rw [plantBlock_of_ne p.2 j p.1 m (Finset.ne_of_mem_erase hm)] at h
        exact congrArg _ h
      calc (∑ p ∈ Finset.univ.filter (fun (p : (Fin M → Bool) × (Fin c → (Fin M → Bool))) => plantBlock p.2 j p.1 = Y),
              E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)))
          = ∑ u : Fin M → Bool,
              (E (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) *
                (D₀ u * F Y) := by
            refine Finset.sum_bij'
              (i := fun (p : (Fin M → Bool) × (Fin c → (Fin M → Bool))) _ => p.2 j)
              (j := fun (u : Fin M → Bool) _ => (Y j, plantBlock Y j u))
              (fun _ _ => Finset.mem_univ _)
              (fun u _ => hmem u) ?_ ?_ ?_
            · intro p hp
              obtain ⟨_, hYp⟩ := Finset.mem_filter.mp hp
              have h2 : plantBlock Y j (p.2 j) = p.2 := by
                funext m
                by_cases hm : m = j
                · subst hm; simp [plantBlock]
                · rw [plantBlock_of_ne Y j (p.2 j) m hm]
                  have h : plantBlock p.2 j p.1 m = Y m := by rw [hYp]
                  rw [plantBlock_of_ne p.2 j p.1 m hm] at h
                  exact h.symm
              show (Y j, plantBlock Y j (p.2 j)) = p
              exact Prod.ext (harg p hYp).symm h2
            · intro u _
              exact plantBlock_self Y j u
            · intro p hp
              obtain ⟨_, hYp⟩ := Finset.mem_filter.mp hp
              show E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)) =
                (E (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) *
                  (D₀ (p.2 j) * F Y)
              rw [hYp, harg p hYp, dprodMass_erase D₀ D₁ b p.2 j, hb, Dsel_false,
                hoff p hYp]
              simp [mul_assoc, mul_comm, mul_left_comm]
        _ = (E (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) *
              ∑ u : Fin M → Bool, (D₀ u * F Y) := by rw [Finset.mul_sum]
        _ = (E (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) *
              ((∑ u : Fin M → Bool, D₀ u) * F Y) := by rw [Finset.sum_mul]
        _ = (E (Y j) * ∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y := by
              rw [finset_sum_pmf_eq_one D₀, one_mul]
    calc ∑ x : Fin M → Bool, ∑ X : Fin c → (Fin M → Bool),
          E x * (DprodMass D₀ D₁ b X * F (plantBlock X j x))
        = ∑ p : (Fin M → Bool) × (Fin c → (Fin M → Bool)),
            E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)) := hpair
      _ = ∑ Y : Fin c → (Fin M → Bool),
            ∑ p ∈ Finset.univ.filter (fun (p : (Fin M → Bool) × (Fin c → (Fin M → Bool))) => plantBlock p.2 j p.1 = Y),
              E p.1 * (DprodMass D₀ D₁ b p.2 * F (plantBlock p.2 j p.1)) := hfiber
      _ = ∑ Y : Fin c → (Fin M → Bool),
            E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y :=
          Finset.sum_congr rfl fun Y _ => hfib Y
  calc ∑' x, E x * ∑' X, DprodMass D₀ D₁ b X * F (plantBlock X j x)
      = ∑ x : Fin M → Bool, E x * ∑' X, DprodMass D₀ D₁ b X * F (plantBlock X j x) :=
        tsum_fintype (f := fun x : Fin M → Bool =>
          E x * ∑' X, DprodMass D₀ D₁ b X * F (plantBlock X j x))
    _ = ∑ x : Fin M → Bool, ∑ X : Fin c → (Fin M → Bool),
          E x * (DprodMass D₀ D₁ b X * F (plantBlock X j x)) :=
        Finset.sum_congr rfl fun x _ => by
          rw [tsum_fintype (f := fun X : Fin c → (Fin M → Bool) =>
            DprodMass D₀ D₁ b X * F (plantBlock X j x)), Finset.mul_sum]
    _ = ∑ Y : Fin c → (Fin M → Bool),
          E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y := hcore
    _ = ∑' Y : Fin c → (Fin M → Bool),
          E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y :=
        (tsum_fintype (f := fun Y : Fin c → (Fin M → Bool) =>
          E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) * F Y)).symm

/-- At a false-labeled block, planting a fresh block from the false distribution preserves the
product-distribution average. -/
private theorem planted_zero {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (j : Fin c) (hb : b j = false)
    (F : (Fin c → (Fin M → Bool)) → ℝ≥0∞) :
    ∑' x, D₀ x * ∑' X, DprodMass D₀ D₁ b X * F (plantBlock X j x) =
      ∑' Y, DprodMass D₀ D₁ b Y * F Y := by
  rw [planted_fiber D₀ D₁ D₀ b j hb F]
  refine tsum_congr fun Y => ?_
  rw [dprodMass_erase D₀ D₁ b Y j, hb, Dsel_false]

/-- At a false-labeled block, planting from the true distribution changes the
product-distribution average to the one with that block's label updated to true. -/
private theorem planted_one {c M : ℕ} (D₀ D₁ : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (j : Fin c) (hb : b j = false)
    (F : (Fin c → (Fin M → Bool)) → ℝ≥0∞) :
    ∑' x, D₁ x * ∑' X, DprodMass D₀ D₁ b X * F (plantBlock X j x) =
      ∑' Y, DprodMass D₀ D₁ (Function.update b j true) Y * F Y := by
  rw [planted_fiber D₀ D₁ D₁ b j hb F]
  refine tsum_congr fun Y => ?_
  rw [dprodMass_update_true D₀ D₁ b j Y]

/-- The tree-distribution average of a sheet's hit mass is at most one. -/
private theorem hitTsum_le_one {c M κ : ℕ} (ℓ : Fin (2 ^ c)) (Y : Fin c → (Fin M → Bool))
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    (∑' τ, A τ * hitMass ℓ Y τ) ≤ 1 := by
  refine le_trans (ENNReal.tsum_le_tsum fun τ =>
    mul_le_mul le_rfl (hitMass_le_one ℓ Y τ) (by simp) (by simp)) ?_
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe A, one_mul]

/-- The tree-distribution average of a sheet's hit mass is finite. -/
private theorem hitTsum_ne_top {c M κ : ℕ} (ℓ : Fin (2 ^ c)) (Y : Fin c → (Fin M → Bool))
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    (∑' τ, A τ * hitMass ℓ Y τ) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hitTsum_le_one ℓ Y A)

/-- The probability of output true under a bound mixture is the mixture-weighted sum of the
component probabilities. -/
private theorem successProb_true_bind {Q W : Type} [Fintype Q] [DecidableEq Q] (μ : PMF W)
    (f : W → PMF (BoolQueryTree Q Bool)) (x : Q → Bool) :
    Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (μ.bind f) x (fun b => b = true) =
      ∑' w, μ w * Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (f w) x (fun b => b = true) := by
  rw [successProb_true_eq]
  calc ∑' ρ, (μ.bind f) ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0)
      = ∑' ρ, (∑' w, μ w * f w ρ) * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0) := by
        simp only [PMF.bind_apply]
    _ = ∑' ρ, ∑' w, μ w * f w ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0) := by
        refine tsum_congr fun ρ => (ENNReal.tsum_mul_right
          (f := fun w => μ w * f w ρ)).symm
    _ = ∑' w, ∑' ρ, μ w * f w ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0) :=
        ENNReal.tsum_comm
    _ = ∑' w, μ w * (∑' ρ, f w ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0)) := by
        refine tsum_congr fun w => ?_
        calc ∑' ρ, μ w * f w ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0)
            = ∑' ρ, μ w * (f w ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0)) :=
              tsum_congr fun ρ => mul_assoc _ _ _
          _ = μ w * ∑' ρ, f w ρ * (if (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run x ρ).1 then (1 : ℝ≥0∞) else 0) :=
              ENNReal.tsum_mul_left
    _ = ∑' w, μ w * Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (f w) x (fun b => b = true) :=
        tsum_congr fun w => congrArg _ (successProb_true_eq (f w) x).symm

/-- The blank-block oracle equals the block oracle for the tuple with the designated replacement
planted. -/
private theorem blankBlockOracle_plant {c M κ : ℕ} (j : Fin c) (X : Fin c → (Fin M → Bool))
    (x : Fin M → Bool) :
    blankBlockOracle (κ := κ) j X x = blockOracle (κ := κ) (plantBlock X j x) := by
  funext q
  cases q with
  | inl q =>
      simp only [blankBlockOracle, blockOracle, Sum.elim_inl, plantBlock,
        Function.update_apply]
      split <;> rfl
  | inr q => rfl

/-- Expresses the expected acceptance of the planted hit-tree program as the real conversion of
the corresponding product-distribution weighted hit sum. -/
private theorem tae_planted {c M κ : ℕ} (D₀ D₁ E : PMF (Fin M → Bool)) (b : Fin c → Bool)
    (j : Fin c) (hb : b j = false) (ℓ : Fin (2 ^ c))
    (A : PMF (BoolQueryTree (CheatSheetIndex c M κ) Bool)) :
    TreeAcceptExpect
        ((PMF.ofFintype (DprodMass D₀ D₁ b) (dprodMass_eq_one D₀ D₁ b)).bind
          fun X => A.map (cheatSheetHitTree j ℓ X)) E =
      (∑' Y, E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) *
        ∑' τ, A τ * hitMass ℓ Y τ).toReal := by
  classical
  have hleaf : ∀ (X : Fin c → (Fin M → Bool)) (z : Fin M → Bool),
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb (A.map (cheatSheetHitTree j ℓ X)) z (fun bb => bb = true) =
        ∑' τ, A τ * hitMass ℓ (plantBlock X j z) τ := by
    intro X z
    rw [cheatSheetHitTree_success]
    refine tsum_congr fun τ => ?_
    rw [blankBlockOracle_plant]
    rfl
  have hS : ∀ z : Fin M → Bool,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb
          ((PMF.ofFintype (DprodMass D₀ D₁ b) (dprodMass_eq_one D₀ D₁ b)).bind
            fun X => A.map (cheatSheetHitTree j ℓ X)) z (fun bb => bb = true) =
        ∑' X, DprodMass D₀ D₁ b X * ∑' τ, A τ * hitMass ℓ (plantBlock X j z) τ := by
    intro z
    rw [successProb_true_bind]
    refine tsum_congr fun X => ?_
    rw [PMF.ofFintype_apply, hleaf X z]
  have hSne : ∀ z : Fin M → Bool,
      (∑' X, DprodMass D₀ D₁ b X * ∑' τ, A τ * hitMass ℓ (plantBlock X j z) τ) ≠ ∞ := by
    intro z
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    refine le_trans (ENNReal.tsum_le_tsum fun X =>
      mul_le_mul le_rfl (hitTsum_le_one ℓ (plantBlock X j z) A) (by simp) (by simp)) ?_
    rw [ENNReal.tsum_mul_right,
      tsum_fintype (f := fun X : Fin c → (Fin M → Bool) => DprodMass D₀ D₁ b X),
      dprodMass_eq_one, one_mul]
  calc TreeAcceptExpect
        ((PMF.ofFintype (DprodMass D₀ D₁ b) (dprodMass_eq_one D₀ D₁ b)).bind
          fun X => A.map (cheatSheetHitTree j ℓ X)) E
      = ∑' z : Fin M → Bool, (E z).toReal *
          (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb
            ((PMF.ofFintype (DprodMass D₀ D₁ b) (dprodMass_eq_one D₀ D₁ b)).bind
              fun X => A.map (cheatSheetHitTree j ℓ X)) z (fun bb => bb = true)).toReal := rfl
    _ = ∑' z : Fin M → Bool, (E z).toReal *
          (∑' X, DprodMass D₀ D₁ b X * ∑' τ, A τ * hitMass ℓ (plantBlock X j z) τ).toReal := by
        refine tsum_congr fun z => congrArg (fun v => (E z).toReal * v.toReal) (hS z)
    _ = ∑' z : Fin M → Bool,
          (E z * ∑' X, DprodMass D₀ D₁ b X * ∑' τ, A τ * hitMass ℓ (plantBlock X j z) τ).toReal := by
        refine tsum_congr fun z => ?_
        rw [ENNReal.toReal_mul]
    _ = (∑' z : Fin M → Bool,
          E z * ∑' X, DprodMass D₀ D₁ b X * ∑' τ, A τ * hitMass ℓ (plantBlock X j z) τ).toReal :=
        (ENNReal.tsum_toReal_eq fun z =>
          ENNReal.mul_ne_top (PMF.apply_ne_top E z) (hSne z)).symm
    _ = (∑' Y, E (Y j) * (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (b m) (Y m)) *
          ∑' τ, A τ * hitMass ℓ Y τ).toReal :=
        congrArg _ (planted_fiber D₀ D₁ E b j hb
          fun Y => ∑' τ, A τ * hitMass ℓ Y τ)

/-- Under the certifying, distributional hardness, size, and success assumptions, every
randomized cheat-sheet solver's query bound is at least `t`. -/
theorem cheatSheetRandomizedLowerBound : CheatSheetRandomizedLowerBound := by
  intro c M κ t T hκ dom g φ D₀ D₁ A hcert hD₀ hD₁ hhard hsize hA hsolve
  rcases Nat.lt_or_ge t T with hlt | hge
  · exact hlt.le
  by_contra hcon
  push Not at hcon
  have hc : 0 < c := by
    by_contra h0
    push Not at h0
    have hc0 : c = 0 := Nat.le_zero.mp h0
    have h2c : (2 : ℕ) ^ c = 1 := by rw [hc0]; simp
    omega
  have h6T : 6 * T < 2 ^ c := by omega
  have hex : ∃ ℓ : Fin (2 ^ c), (Qvec D₀ D₁ (fun _ => false) ℓ A).toReal < 1 / 6 := by
    by_contra hno
    push Not at hno
    have hsum : (2 ^ c : ℝ) / 6 ≤
        ∑ ℓ : Fin (2 ^ c), (Qvec D₀ D₁ (fun _ => false) ℓ A).toReal := by
      calc (2 ^ c : ℝ) / 6 = ∑ ℓ : Fin (2 ^ c), 1 / 6 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            push_cast
            ring
        _ ≤ ∑ ℓ : Fin (2 ^ c), (Qvec D₀ D₁ (fun _ => false) ℓ A).toReal :=
            Finset.sum_le_sum fun ℓ _ => hno ℓ
    have hle : ∑ ℓ : Fin (2 ^ c), (Qvec D₀ D₁ (fun _ => false) ℓ A).toReal ≤ (T : ℝ) := by
      rw [← ENNReal.toReal_sum (fun ℓ _ => qvec_ne_top D₀ D₁ (fun _ => false) ℓ A)]
      have hq := qvec_sum_le D₀ D₁ (fun _ => false) A T hA
      exact_mod_cast ENNReal.toReal_mono (by simp) hq
    have h26 : (6 * T : ℝ) < (2 ^ c : ℝ) := by exact_mod_cast h6T
    linarith
  obtain ⟨ℓ, hℓ0⟩ := hex
  have hbase : (Qvec D₀ D₁ (chainVec ℓ 0) ℓ A).toReal < 1 / 6 := by
    rw [chainVec_zero]
    exact hℓ0
  have htop : 1 / 3 ≤ (Qvec D₀ D₁ (chainVec ℓ c) ℓ A).toReal := by
    rw [chainVec_self]
    have h := qvec_self_ge hκ hc dom g φ hcert D₀ D₁ hD₀ hD₁ A hsolve
      (fun m : Fin c => sheetBit (ℓ : ℕ) (m : ℕ))
    rw [sheetIndex_sheetBit ℓ] at h
    exact h
  obtain ⟨j, hj⟩ := cheatSheetHybrid_step c hc
    (fun k : Fin (c + 1) => (Qvec D₀ D₁ (chainVec ℓ (k : ℕ)) ℓ A).toReal) hbase htop
  have hbj : chainVec ℓ (j : ℕ) j = false := by simp [chainVec]
  have hbit : sheetBit (ℓ : ℕ) (j : ℕ) = true := by
    by_contra hnot
    have hbb : sheetBit (ℓ : ℕ) (j : ℕ) = false := by
      cases hbb' : sheetBit (ℓ : ℕ) (j : ℕ) with
        | true => exact absurd hbb' hnot
        | false => rfl
    have heq : chainVec ℓ ((j : ℕ) + 1) = chainVec ℓ (j : ℕ) := by
      rw [chainVec_succ_update, hbb, ← hbj, Function.update_eq_self]
    have hjs : (j.succ : Fin (c + 1)).val = (j : ℕ) + 1 := by simp
    have hcs : (j.castSucc : Fin (c + 1)).val = (j : ℕ) := by simp
    rw [hjs, hcs, heq] at hj
    have hpos6 : 0 < 1 / (6 * (c : ℝ)) := by positivity
    linarith
  have hT0 := tae_planted D₀ D₁ D₀ (chainVec ℓ (j : ℕ)) j hbj ℓ A
  have hT1 := tae_planted D₀ D₁ D₁ (chainVec ℓ (j : ℕ)) j hbj ℓ A
  have hq0 : (∑' Y : Fin c → (Fin M → Bool), D₀ (Y j) *
        (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (chainVec ℓ (j : ℕ) m) (Y m)) *
        ∑' τ, A τ * hitMass ℓ Y τ) =
      Qvec D₀ D₁ (chainVec ℓ (j : ℕ)) ℓ A := by
    rw [qvec_eq_massFun]
    refine tsum_congr fun Y => ?_
    rw [dprodMass_erase D₀ D₁ (chainVec ℓ (j : ℕ)) Y j, hbj, Dsel_false]
  rw [hq0] at hT0
  have hq1 : (∑' Y : Fin c → (Fin M → Bool), D₁ (Y j) *
        (∏ m ∈ Finset.univ.erase j, Dsel D₀ D₁ (chainVec ℓ (j : ℕ) m) (Y m)) *
        ∑' τ, A τ * hitMass ℓ Y τ) =
      Qvec D₀ D₁ (Function.update (chainVec ℓ (j : ℕ)) j true) ℓ A := by
    rw [qvec_eq_massFun]
    refine tsum_congr fun Y => ?_
    rw [dprodMass_update_true D₀ D₁ (chainVec ℓ (j : ℕ)) j Y]
  rw [hq1] at hT1
  have hlink : (Qvec D₀ D₁ (Function.update (chainVec ℓ (j : ℕ)) j true) ℓ A).toReal =
      (Qvec D₀ D₁ (chainVec ℓ ((j : ℕ) + 1)) ℓ A).toReal := by
    refine congrArg ENNReal.toReal ?_
    congr 1
    rw [chainVec_succ_update, hbit]
  have hjs : (j.succ : Fin (c + 1)).val = (j : ℕ) + 1 := by simp
  have hcs : (j.castSucc : Fin (c + 1)).val = (j : ℕ) := by simp
  rw [hjs, hcs, ← hlink, ← hT0, ← hT1] at hj
  set P : PMF (BoolQueryTree (Fin M) Bool) :=
    (PMF.ofFintype (DprodMass D₀ D₁ (chainVec ℓ (j : ℕ)))
      (dprodMass_eq_one D₀ D₁ (chainVec ℓ (j : ℕ)))).bind
      fun X => A.map (cheatSheetHitTree j ℓ X) with hPdef
  have hP : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.BoundedQueries P t := by
    intro τ hτ
    rw [hPdef] at hτ
    obtain ⟨X, hX, hτ'⟩ :=
      (PMF.mem_support_bind_iff
        (p := PMF.ofFintype (DprodMass D₀ D₁ (chainVec ℓ (j : ℕ)))
          (dprodMass_eq_one D₀ D₁ (chainVec ℓ (j : ℕ))))
        (f := fun X => A.map (cheatSheetHitTree j ℓ X)) τ).mp hτ
    exact (cheatSheetHitTree_bounded_program j ℓ X A hA τ hτ').trans (by omega)
  have hadv := hhard P hP
  have hpos6 : 0 < 1 / (6 * (c : ℝ)) := by positivity
  have habs : DistAdvantage (Q := Fin M) P D₀ D₁ =
      TreeAcceptExpect (Q := Fin M) P D₁ - TreeAcceptExpect (Q := Fin M) P D₀ := by
    unfold DistAdvantage
    rw [abs_sub_comm, abs_of_pos (by linarith)]
  rw [habs] at hadv
  have h612 : 1 / (12 * (c : ℝ)) < 1 / (6 * (c : ℝ)) := by
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    rw [one_div, one_div, inv_lt_inv₀ (by positivity) (by positivity)]
    linarith
  linarith

end Qatlib.Papers.CheatSheet15.BornBaseline
