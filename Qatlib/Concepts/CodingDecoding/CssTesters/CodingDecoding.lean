/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecodingCoreDefs
import Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
import Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction

/-!
# CSS recovery correctness

This module constructs the minimum-weight correction `clause1Corr` and proves correctness of
`clause1Prog` for Pauli errors of weight at most `t` when the CSS distance is at least `2 * t +
1`. Stabilizer labels fix the codespace and preserve matrices with codespace columns, providing
the logical reference condition used in recovery. The CSS and stabilizer background is developed
in [CalderbankShor1996] and [Gottesman1997].

Syndrome projectors give complete outcome masses, select the true syndrome of a Pauli-corrupted
code vector, and yield recovery of its outer-product matrix when the residual is a stabilizer.
The theorem `g1` assembles encoding, recovery, and resource bounds; `g3` supplies a finite
realization of the gadget and noise conditions using trivial data.

## Main statements

* `logicalReferencePreserved_of_stabilizer`: proves logical reference preservation for
  stabilizer labels.
* `clause1Prog_correctsUpTo`: proves bounded-weight correction from the distance hypothesis.
* `sum_syndromeOutcomeMass`: proves completeness of syndrome outcome masses.
* `recoveryChannel_corrects_density`: restores code-vector outer products under a stabilizer
  residual.
* `g1`: assembles the CSS encoding and recovery guarantees.
* `g3`: gives a finite realization with gadget, noise, and resource bounds.

## References

* [Calderbank and Shor, 1996][CalderbankShor1996]
* [Gottesman, 1997][Gottesman1997]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Concepts.CodingDecoding.CssTesters.CssTester
open Qatlib.Concepts.CodingDecoding.CssTesters.LogicalNonscalarRestriction

set_option autoImplicit false

open Qatlib.Concepts.CodingDecoding.CssTesters

namespace Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding

open Matrix
open scoped Classical

/-- A binary vector with Hamming weight zero is the zero vector. -/
theorem bitWeight_eq_zero {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → ZMod 2}
    (h : bitWeight v = 0) : v = 0 := by
  funext i
  by_contra hi
  have hmem : i ∈ (Finset.univ.filter fun j => v j ≠ 0) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  have := Finset.card_pos.mpr ⟨i, hmem⟩
  simp only [bitWeight] at h
  omega

/-- A nonzero binary vector has positive Hamming weight. -/
theorem bitWeight_pos_of_ne_zero {κ : Type} [Fintype κ] [DecidableEq κ] {v : κ → ZMod 2}
    (h : v ≠ 0) : 0 < bitWeight v := by
  by_contra hn
  exact h (bitWeight_eq_zero (Nat.eq_zero_of_not_pos hn))

/-- The Pauli label with both components zero has weight zero. -/
theorem pauliWeight_zero_zero {κ : Type} [Fintype κ] [DecidableEq κ] :
    pauliWeight (0 : κ → ZMod 2) 0 = 0 := by
  unfold pauliWeight
  simp

/-- A Pauli label with weight zero has both components zero. -/
theorem pauliWeight_eq_zero {κ : Type} [Fintype κ] [DecidableEq κ] {x z : κ → ZMod 2}
    (h : pauliWeight x z = 0) : x = 0 ∧ z = 0 := by
  have hall : ∀ i : κ, x i = 0 ∧ z i = 0 := by
    intro i
    by_contra hi
    have hmem : i ∈ (Finset.univ.filter fun j => x j ≠ 0 ∨ z j ≠ 0) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact not_and_or.mp hi
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    unfold pauliWeight at h
    omega
  exact ⟨funext fun i => (hall i).1, funext fun i => (hall i).2⟩

/-- The zero vector lies in the range of the linear map defined by a binary matrix. -/
theorem zero_mem_range_mulVecLin {κ κ' : Type} [Fintype κ] [Fintype κ']
    (A : Matrix κ κ' (ZMod 2)) :
    (0 : κ → ZMod 2) ∈ LinearMap.range (Matrix.mulVecLin A) :=
  ⟨(0 : κ' → ZMod 2), map_zero (Matrix.mulVecLin A)⟩

/-- The zero Pauli label is a stabilizer label for every CSS code. -/
theorem isStabilizerLabel_zero {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) :
    IsStabilizerLabel c ((0 : ι → ZMod 2), 0) :=
  ⟨zero_mem_range_mulVecLin c.hXᵀ, zero_mem_range_mulVecLin c.hZᵀ⟩

/-- The extended-natural distance of every CSS code is at least one. -/
theorem one_le_cssDistance {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) :
    (1 : ℕ∞) ≤ cssDistance c := by
  have hside : ∀ (s : Set ℕ∞), (∀ w ∈ s, (1 : ℕ∞) ≤ w) → (1 : ℕ∞) ≤ sInf s := by
    intro s hs
    by_cases hne : s.Nonempty
    · exact le_sInf hs
    · rw [Set.not_nonempty_iff_eq_empty.mp hne]
      simp
  unfold cssDistance
  apply le_min
  · apply hside
    rintro w ⟨z, -, hout, rfl⟩
    have hz0 : z ≠ 0 := fun hh => hout (hh ▸ zero_mem_range_mulVecLin c.hZᵀ)
    have : (1 : ℕ) ≤ bitWeight z := Nat.succ_le_of_lt (bitWeight_pos_of_ne_zero hz0)
    exact_mod_cast this
  · apply hside
    rintro w ⟨x, -, hout, rfl⟩
    have hx0 : x ≠ 0 := fun hh => hout (hh ▸ zero_mem_range_mulVecLin c.hXᵀ)
    have : (1 : ℕ) ≤ bitWeight x := Nat.succ_le_of_lt (bitWeight_pos_of_ne_zero hx0)
    exact_mod_cast this

/-- The one-qubit CSS data with one zero X check and one zero Z check. -/
def trivialCode : CssData (Fin 1) (Fin 1) (Fin 1) where
  hX := 0
  hZ := 0
  hcompat := by simp

/-- The recovery program for `trivialCode` that always chooses zero correction and assigns zero
decoding time. -/
def trivialProg : RecoveryProgram trivialCode where
  corr := fun _ => (0, 0)
  decodeTime := fun _ => 0

/-- A gadget of the specified kind with one location, unit space and time, and zero ideal and
residual labels. -/
def trivialGadget (k : GadgetKind) : GadgetSpec trivialCode where
  kind := k
  locations := 1
  space := 1
  time := 1
  ideal := (0, 0)
  residual := fun _ => (0, 0)

/-- The finite fault-tolerance parameter record built from the trivial code, a zero-correction
decoder, and two trivial gadgets. -/
noncomputable def trivialFtRealization : FtRealization where
  N := 1
  mX := 1
  mZ := 1
  code := trivialCode
  prog := trivialProg
  t := 0
  ζ := 1
  gadgets := [trivialGadget .syndromeRound, trivialGadget .gate]
  pTh := 1 / 4
  ε := 1 / 2
  budget := 2
  peak := 1

/-- The trivial recovery program leaves every input Pauli label as its residual. -/
theorem residualLabel_trivialProg {e : PauliLabel (Fin 1)} :
    residualLabel trivialProg e = e := by
  unfold residualLabel residualFromObserved
  simp [trivialProg, pauliSyndrome]

/-- Every trivial gadget satisfies ideal correctness. -/
theorem trivialGadget_idealCorrect (k : GadgetKind) :
    (trivialGadget k).IsIdealCorrect :=
  ⟨isStabilizerLabel_zero trivialCode, rfl⟩

/-- Every trivial gadget satisfies the fault-tolerance predicate at tolerance zero. -/
theorem trivialGadget_faultTolerant (k : GadgetKind) :
    (trivialGadget k).IsFaultTolerantAt 0 := by
  intro F _
  show pauliWeight (0 : Fin 1 → ZMod 2) 0 ≤ 0
  simp [pauliWeight]

/-- For a single fault location, summing over nonempty fault sets equals summing over sets
containing the full location set. -/
theorem fin1_filter_card_pos (pp : Finset (Fin 1) → ℝ) :
    ∑ F ∈ Finset.univ.filter (fun F : Finset (Fin 1) => 0 < F.card), pp F =
      ∑ F ∈ Finset.univ.filter
        (fun F : Finset (Fin 1) => (Finset.univ : Finset (Fin 1)) ⊆ F), pp F := by
  have hiff : ∀ F : Finset (Fin 1), (0 < F.card ↔ (Finset.univ : Finset (Fin 1)) ⊆ F) := by
    intro F
    constructor
    · intro hcard
      have hne : F.Nonempty := Finset.card_pos.mp hcard
      have hF : F = (Finset.univ : Finset (Fin 1)) := by
        apply Finset.eq_univ_of_forall
        intro x
        obtain ⟨y, hy⟩ := hne
        exact (Subsingleton.elim x y) ▸ hy
      rw [hF]
    · intro hsub
      have h0 : (0 : Fin 1) ∈ Finset.univ := Finset.mem_univ 0
      exact Finset.card_pos.mpr ⟨0, hsub h0⟩
  rw [Finset.filter_congr fun F _ => hiff F]

/-- For one fault location under local stochastic noise, the zero-tolerance failure probability
is bounded by the first-order binomial expression. -/
theorem gadgetFailureProb_fin1_zero (pp : Finset (Fin 1) → ℝ) (p : ℝ)
    (h : LocalStochasticNoiseLaw pp p) :
    gadgetFailureProb pp 0 ≤ ((1 : ℕ).choose (0 + 1) : ℝ) * p ^ (0 + 1) := by
  have hsum := h.2.2 (Finset.univ : Finset (Fin 1)) (Finset.Subset.refl _)
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  have hg : gadgetFailureProb pp 0 =
      ∑ F ∈ Finset.univ.filter (fun F : Finset (Fin 1) => 0 < F.card), pp F := rfl
  rw [hg, fin1_filter_card_pos]
  simpa [pow_one] using hsum

/-- An adversarial fault budget of zero forces the zero-tolerance gadget failure probability to
vanish. -/
theorem gadgetFailureProb_adversarial_zero {ζ : ℕ} {pp : Finset (Fin ζ) → ℝ} {a : ℕ}
    (h : AdversarialFaultBudget pp a) (ha : a ≤ 0) : gadgetFailureProb pp 0 = 0 := by
  have hnonneg : ∀ F, 0 ≤ pp F := h.1
  have hsupp : ∀ F, 0 < pp F → F.card ≤ a := h.2.2
  have hzero : ∀ F : Finset (Fin ζ), 0 < F.card → pp F = 0 := by
    intro F hF
    by_contra hn
    have hpos : 0 < pp F := lt_of_le_of_ne (hnonneg F) (Ne.symm hn)
    have := hsupp F hpos
    omega
  unfold gadgetFailureProb
  apply Finset.sum_eq_zero
  intro F hF
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
  exact hzero F hF

/-- There exists a finite fault-tolerance realization with decoder correctness, ideal and
bounded-fault gadget properties, positive noise and error parameters, stochastic and
adversarial failure bounds, and spacetime and peak-space bounds. -/
theorem g3 :
  ∃ (r : FtRealization),

    (((2 * r.t + 1 : ℕ) : ℕ∞) ≤ cssDistance r.code) ∧
    CorrectsUpTo r.prog r.t ∧
    MinimumWeightSound r.prog ∧

    r.t + 1 ≤ r.ζ ∧

    r.gadgets.length ≠ 0 ∧
    (∃ g ∈ r.gadgets, g.kind = GadgetKind.syndromeRound) ∧
    (∃ g ∈ r.gadgets, g.kind = GadgetKind.gate) ∧

    (∀ g ∈ r.gadgets, g.IsIdealCorrect) ∧
    (∀ g ∈ r.gadgets, g.IsFaultTolerantAt r.t) ∧
    (∀ g ∈ r.gadgets, g.locations ≤ r.ζ) ∧

    0 < r.pTh ∧ r.pTh ≤ 1 ∧ 0 < r.ε ∧ r.ε < 1 ∧

    (composedErrWindow r.gadgets r.ζ r.t r.pTh ≤ r.ε) ∧

    (∀ p : ℝ, 0 < p → p ≤ r.pTh → composedFailureMass r.gadgets r.t p ≤ r.ε) ∧

    (∀ (pp : Finset (Fin r.ζ) → ℝ) (p : ℝ),
      LocalStochasticNoiseLaw pp p → p ≤ r.pTh →
      gadgetFailureProb pp r.t ≤ (r.ζ.choose (r.t + 1) : ℝ) * p ^ (r.t + 1)) ∧

    (∀ (pp : Finset (Fin r.ζ) → ℝ) (a : ℕ),
      AdversarialFaultBudget pp a → a ≤ r.t → gadgetFailureProb pp r.t = 0) ∧

    cumulativeSpaceTime r.gadgets ≤ r.budget ∧
    peakSpace r.gadgets ≤ r.peak := by
  refine ⟨trivialFtRealization,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ((1 : ℕ) : ℕ∞) ≤ cssDistance trivialCode
    exact one_le_cssDistance trivialCode
  · show CorrectsUpTo trivialProg 0
    intro e he
    have hz : e.1 = 0 ∧ e.2 = 0 := pauliWeight_eq_zero (Nat.eq_zero_of_le_zero he)
    have he0 : e = ((0 : Fin 1 → ZMod 2), 0) := Prod.ext hz.1 hz.2
    rw [he0, residualLabel_trivialProg]
    exact isStabilizerLabel_zero trivialCode
  · show MinimumWeightSound trivialProg
    intro η e _
    show pauliWeight (0 : Fin 1 → ZMod 2) 0 ≤ pauliWeight e.1 e.2
    simp [pauliWeight]
  · show (0 : ℕ) + 1 ≤ 1
    norm_num
  · show [trivialGadget .syndromeRound, trivialGadget .gate].length ≠ 0
    norm_num
  · refine ⟨trivialGadget .syndromeRound, ?_, rfl⟩
    show trivialGadget .syndromeRound ∈ [trivialGadget .syndromeRound, trivialGadget .gate]
    simp
  · refine ⟨trivialGadget .gate, ?_, rfl⟩
    show trivialGadget .gate ∈ [trivialGadget .syndromeRound, trivialGadget .gate]
    simp
  · intro g hg
    have hg' : g ∈ [trivialGadget .syndromeRound, trivialGadget .gate] := hg
    have hg'' : g = trivialGadget .syndromeRound ∨ g = trivialGadget .gate := by
      exact (List.mem_cons.mp hg').elim Or.inl
        (fun hh => Or.inr (List.mem_singleton.mp hh))
    rcases hg'' with rfl | rfl <;> exact trivialGadget_idealCorrect _
  · intro g hg
    have hg' : g ∈ [trivialGadget .syndromeRound, trivialGadget .gate] := hg
    have hg'' : g = trivialGadget .syndromeRound ∨ g = trivialGadget .gate := by
      exact (List.mem_cons.mp hg').elim Or.inl
        (fun hh => Or.inr (List.mem_singleton.mp hh))
    rcases hg'' with rfl | rfl <;> exact trivialGadget_faultTolerant _
  · intro g hg
    have hg' : g ∈ [trivialGadget .syndromeRound, trivialGadget .gate] := hg
    have hg'' : g = trivialGadget .syndromeRound ∨ g = trivialGadget .gate := by
      exact (List.mem_cons.mp hg').elim Or.inl
        (fun hh => Or.inr (List.mem_singleton.mp hh))
    rcases hg'' with rfl | rfl <;> show (1 : ℕ) ≤ 1 <;> norm_num
  · show 0 < (1 / 4 : ℝ)
    norm_num
  · show (1 / 4 : ℝ) ≤ 1
    norm_num
  · show 0 < (1 / 2 : ℝ)
    norm_num
  · show (1 / 2 : ℝ) < 1
    norm_num
  · show composedErrWindow [trivialGadget .syndromeRound, trivialGadget .gate] 1 0 (1 / 4) ≤ 1 / 2
    norm_num [composedErrWindow, GadgetSpec.failureMass, trivialGadget]
  · intro p _ hple
    show composedFailureMass [trivialGadget .syndromeRound, trivialGadget .gate] 0 p ≤ 1 / 2
    have hle : p ≤ 1 / 4 := hple
    simp only [composedFailureMass, GadgetSpec.failureMass, trivialGadget]
    norm_num
    linarith
  · intro pp p hlaw _
    show gadgetFailureProb pp 0 ≤ ((1 : ℕ).choose (0 + 1) : ℝ) * p ^ (0 + 1)
    exact gadgetFailureProb_fin1_zero pp p hlaw
  · intro pp a hadv ha
    show gadgetFailureProb pp 0 = 0
    exact gadgetFailureProb_adversarial_zero hadv ha
  · show cumulativeSpaceTime [trivialGadget .syndromeRound, trivialGadget .gate] ≤ 2
    norm_num [cumulativeSpaceTime, trivialGadget]
  · show peakSpace [trivialGadget .syndromeRound, trivialGadget .gate] ≤ 1
    norm_num [peakSpace, trivialGadget]

/-- A vector belongs to the CSS codespace exactly when every X check and every Z check fixes it. -/
theorem mem_cssCodespace_iff' {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (v : (ι → ZMod 2) → ℂ) :
    v ∈ cssCodespace c ↔
      (∀ i : κX, cssPauliX (c.hX i) *ᵥ v = v) ∧
      (∀ j : κZ, cssPauliZ (c.hZ j) *ᵥ v = v) := by
  simp [cssCodespace, cssXStabilized, cssZStabilized, cssXCheckKernel, cssZCheckKernel,
    sub_eq_zero]

/-- If each X operator in a finite family fixes a vector, the X operator labeled by the sum of
their labels also fixes it. -/
theorem cssPauliX_sum_fixes {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (s : Finset κ) (f : κ → ι → ZMod 2) (v : (ι → ZMod 2) → ℂ)
    (h : ∀ i ∈ s, cssPauliX (f i) *ᵥ v = v) : cssPauliX (∑ i ∈ s, f i) *ᵥ v = v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, cssPauliX_zero, Matrix.one_mulVec]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ← cssPauliX_mul, ← Matrix.mulVec_mulVec,
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), h i (Finset.mem_insert_self i s)]

/-- If each Z operator in a finite family fixes a vector, the Z operator labeled by the sum of
their labels also fixes it. -/
theorem cssPauliZ_sum_fixes {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (s : Finset κ) (f : κ → ι → ZMod 2) (v : (ι → ZMod 2) → ℂ)
    (h : ∀ i ∈ s, cssPauliZ (f i) *ᵥ v = v) : cssPauliZ (∑ i ∈ s, f i) *ᵥ v = v := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, cssPauliZ_zero, Matrix.one_mulVec]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ← cssPauliZ_mul, ← Matrix.mulVec_mulVec,
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), h i (Finset.mem_insert_self i s)]

/-- Multiplication by the transpose of a binary matrix is the linear combination of its rows
with the input coefficients. -/
theorem transpose_mulVec_eq_smul_sum {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : Matrix κ ι (ZMod 2)) (u : κ → ZMod 2) :
    Aᵀ *ᵥ u = ∑ i : κ, u i • A i := by
  ext q
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Every X operator labeled by a linear combination of X-check rows fixes every codespace
vector. -/
theorem cssPauliX_fixes_row {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (u : κX → ZMod 2) (v : (ι → ZMod 2) → ℂ)
    (hv : v ∈ cssCodespace c) : cssPauliX (c.hXᵀ *ᵥ u) *ᵥ v = v := by
  have hrow : ∀ i : κX, cssPauliX (c.hX i) *ᵥ v = v := (mem_cssCodespace_iff' c v).mp hv |>.1
  rw [transpose_mulVec_eq_smul_sum]
  refine cssPauliX_sum_fixes _ _ v (fun i _ => ?_)
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (u i) with h | h
  · rw [h, zero_smul, cssPauliX_zero, Matrix.one_mulVec]
  · rw [h, one_smul, hrow]

/-- Every Z operator labeled by a linear combination of Z-check rows fixes every codespace
vector. -/
theorem cssPauliZ_fixes_row {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (u : κZ → ZMod 2) (v : (ι → ZMod 2) → ℂ)
    (hv : v ∈ cssCodespace c) : cssPauliZ (c.hZᵀ *ᵥ u) *ᵥ v = v := by
  have hrow : ∀ j : κZ, cssPauliZ (c.hZ j) *ᵥ v = v := (mem_cssCodespace_iff' c v).mp hv |>.2
  rw [transpose_mulVec_eq_smul_sum]
  refine cssPauliZ_sum_fixes _ _ v (fun j _ => ?_)
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) (u j) with h | h
  · rw [h, zero_smul, cssPauliZ_zero, Matrix.one_mulVec]
  · rw [h, one_smul, hrow]

/-- The Pauli operator associated with a stabilizer label fixes every CSS codespace vector. -/
theorem isStabilizerLabel_fixes {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) {e : PauliLabel ι}
    (h : IsStabilizerLabel c e) (v : (ι → ZMod 2) → ℂ) (hv : v ∈ cssCodespace c) :
    (cssPauliX e.1 * cssPauliZ e.2) *ᵥ v = v := by
  obtain ⟨u, hu⟩ := h.1
  obtain ⟨w, hw⟩ := h.2
  have hu' : c.hXᵀ *ᵥ u = e.1 := by simpa only [Matrix.mulVecLin_apply] using hu
  have hw' : c.hZᵀ *ᵥ w = e.2 := by simpa only [Matrix.mulVecLin_apply] using hw
  rw [← Matrix.mulVec_mulVec, ← hw', cssPauliZ_fixes_row c w v hv, ← hu',
    cssPauliX_fixes_row c u v hv]

/-- Every CSS stabilizer label preserves all matrices whose columns lie in the codespace. -/
theorem logicalReferencePreserved_of_stabilizer {ι κX κZ : Type} [Fintype ι] [Fintype κX]
    [Fintype κZ] [DecidableEq ι] (c : CssData ι κX κZ) {e : PauliLabel ι}
    (h : IsStabilizerLabel c e) : LogicalReferencePreserved c e := by
  intro ρ _ M hM
  ext q r
  have hcol : (cssPauliX e.1 * cssPauliZ e.2) *ᵥ (fun q => M q r) = (fun q => M q r) :=
    isStabilizerLabel_fixes c h _ (hM r)
  have hkey : ((cssPauliX e.1 * cssPauliZ e.2) * M) q r =
      ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ (fun q => M q r)) q := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hkey, hcol]

/-- Every CSS check operator is Hermitian. -/
theorem cssCheck_hermitian {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (k : κX ⊕ κZ) : (cssCheck c k).IsHermitian := by
  cases k with
  | inl i => exact cssPauliX_isHermitian (c.hX i)
  | inr j => exact cssPauliZ_isHermitian (c.hZ j)

/-- Every X check commutes with every Z check of compatible CSS data. -/
theorem css_check_cross' {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (i : κX) (j : κZ) :
    cssPauliX (c.hX i) * cssPauliZ (c.hZ j) = cssPauliZ (c.hZ j) * cssPauliX (c.hX i) := by
  have h : bitDot (c.hX i) (c.hZ j) = 0 := by
    simpa [bitDot, dotProduct, Matrix.mul_apply] using congrFun (congrFun c.hcompat i) j
  rw [cssPauliXZ_comm, bitDot_comm, h, phaseOfBit_zero, one_smul]

/-- Any two CSS check operators commute. -/
theorem cssCheck_commute {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (k k' : κX ⊕ κZ) :
    Commute (cssCheck c k) (cssCheck c k') := by
  change cssCheck c k * cssCheck c k' = cssCheck c k' * cssCheck c k
  cases k with
  | inl i =>
    cases k' with
    | inl i' =>
      show cssPauliX (c.hX i) * cssPauliX (c.hX i') = cssPauliX (c.hX i') * cssPauliX (c.hX i)
      rw [cssPauliX_mul, cssPauliX_mul, add_comm]
    | inr j =>
      exact css_check_cross' c i j
  | inr j =>
    cases k' with
    | inl i =>
      exact (css_check_cross' c i j).symm
    | inr j' =>
      show cssPauliZ (c.hZ j) * cssPauliZ (c.hZ j') = cssPauliZ (c.hZ j') * cssPauliZ (c.hZ j)
      rw [cssPauliZ_mul, cssPauliZ_mul, add_comm]

/-- The outcome projectors of any two CSS checks commute. -/
theorem cssCheckProjector_commute {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (k k' : κX ⊕ κZ) (b b' : ZMod 2) :
    Commute (cssCheckProjector (cssCheck c k) b) (cssCheckProjector (cssCheck c k') b') := by
  have hST : Commute (cssCheck c k) (cssCheck c k') := cssCheck_commute c k k'
  have hS : Commute (phaseOfBit b • cssCheck c k) (phaseOfBit b' • cssCheck c k') :=
    (hST.smul_left (phaseOfBit b)).smul_right (phaseOfBit b')
  have h : Commute (1 + phaseOfBit b • cssCheck c k) (1 + phaseOfBit b' • cssCheck c k') :=
    Commute.add_left (Commute.add_right (Commute.one_left _) (Commute.one_left _))
      (Commute.add_right (Commute.one_right _) hS)
  exact (h.smul_left (2⁻¹ : ℂ)).smul_right (2⁻¹ : ℂ)

/-- Every outcome projector of a CSS check is Hermitian. -/
theorem cssCheckProjector_hermitian {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (k : κX ⊕ κZ) (b : ZMod 2) :
    (cssCheckProjector (cssCheck c k) b).IsHermitian :=
  (Matrix.isHermitian_one.add ((cssCheck_hermitian c k).smul (phaseOfBit_star b))).smul
    (by simp)

/-- The product of a list of pairwise commuting Hermitian matrices is Hermitian. -/
theorem list_prod_isHermitian {σ : Type} [Fintype σ] [DecidableEq σ] (l : List (Matrix σ σ ℂ))
    (hherm : ∀ S ∈ l, S.IsHermitian) (hcomm : ∀ S ∈ l, ∀ T ∈ l, Commute S T) :
    l.prod.IsHermitian := by
  induction l with
  | nil => exact Matrix.isHermitian_one
  | cons S l ih =>
    have hS : S.IsHermitian := hherm S List.mem_cons_self
    have hl : ∀ T ∈ l, T.IsHermitian := fun T hT => hherm T (List.mem_cons_of_mem _ hT)
    have hcomm' : ∀ T ∈ l, ∀ U ∈ l, Commute T U := fun T hT U hU =>
      hcomm T (List.mem_cons_of_mem _ hT) U (List.mem_cons_of_mem _ hU)
    have hSl : Commute S l.prod := Commute.list_prod_right l S
      (fun T hT => hcomm S List.mem_cons_self T (List.mem_cons_of_mem _ hT))
    have hlp : l.prod.IsHermitian := ih hl hcomm'
    have h1 : (S * l.prod).conjTranspose = l.prod.conjTranspose * S.conjTranspose :=
      Matrix.conjTranspose_mul _ _
    rw [hS.eq, hlp.eq] at h1
    show (S * l.prod).conjTranspose = S * l.prod
    rw [h1, hSl.eq]

/-- Every CSS syndrome projector is Hermitian. -/
theorem cssSyndromeProjector_isHermitian {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : (cssSyndromeProjector c η).IsHermitian := by
  classical
  unfold cssSyndromeProjector
  refine list_prod_isHermitian _ (fun S hS => ?_) (fun S hS T hT => ?_)
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hS
    exact cssCheckProjector_hermitian c k _
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp hS
    obtain ⟨k', _, rfl⟩ := List.mem_map.mp hT
    exact cssCheckProjector_commute c k k' _ _

/-- A product of matrices fixes a vector if every matrix in the list fixes it. -/
theorem list_prod_mulVec {σ : Type} [Fintype σ] [DecidableEq σ] (l : List (Matrix σ σ ℂ))
    (v : σ → ℂ) (h : ∀ S ∈ l, S *ᵥ v = v) : l.prod *ᵥ v = v := by
  induction l with
  | nil => simp
  | cons S l ih =>
    rw [List.prod_cons, ← Matrix.mulVec_mulVec,
      ih (fun T hT => h T (List.mem_cons_of_mem _ hT)), h S List.mem_cons_self]

/-- The coefficient inner product of a vector with itself is its real squared norm, embedded in
`ℂ`. -/
theorem coeffInner_self {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : (ι → ZMod 2) → ℂ) :
    coeffInner ψ ψ = (vecNormSq ψ : ℂ) := by
  classical
  simp only [coeffInner, vecNormSq, Complex.star_def]
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (show (Complex.normSq (ψ i) : ℂ) = starRingEnd ℂ (ψ i) * ψ i from
    Complex.normSq_eq_conj_mul_self).symm

/-- The coefficient inner product is additive in its second argument. -/
theorem coeffInner_add_right {ι : Type} [Fintype ι] [DecidableEq ι] (ψ u v : (ι → ZMod 2) → ℂ) :
    coeffInner ψ (u + v) = coeffInner ψ u + coeffInner ψ v := by
  classical
  simp only [coeffInner, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- A finite sum of coefficient inner products equals the inner product with the sum in the
second argument. -/
theorem coeffInner_sum_right {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (ψ : (ι → ZMod 2) → ℂ) (s : Finset κ) (f : κ → (ι → ZMod 2) → ℂ) :
    (∑ i ∈ s, coeffInner ψ (f i)) = coeffInner ψ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffInner]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, ih, Finset.sum_insert hi, coeffInner_add_right]

/-- A matrix acting in the first argument of the coefficient inner product transfers to its
conjugate transpose in the second argument. -/
theorem coeffInner_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (u v : (ι → ZMod 2) → ℂ) :
    coeffInner (M *ᵥ u) v = coeffInner u (Matrix.conjTranspose M *ᵥ v) := by
  classical
  simp only [coeffInner, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Complex.star_def]
  have h1 : ∀ i : ι → ZMod 2,
      starRingEnd ℂ (∑ j, M i j * u j) = ∑ j, starRingEnd ℂ (M i j) * starRingEnd ℂ (u j) := by
    intro i
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => map_mul (starRingEnd ℂ) _ _)
  conv_lhs => simp only [h1, Finset.sum_mul]
  conv_rhs => simp only [Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => by ring))

/-- The masses of all CSS syndrome outcomes sum to the squared norm of the input vector. -/
theorem sum_syndromeOutcomeMass {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (ψ : (ι → ZMod 2) → ℂ) :
    (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), syndromeOutcomeMass c η ψ) = vecNormSq ψ := by
  classical
  have key : ∀ η : (κX → ZMod 2) × (κZ → ZMod 2),
      (syndromeOutcomeMass c η ψ : ℂ) = coeffInner ψ (cssSyndromeProjector c η *ᵥ ψ) := by
    intro η
    have hH : (cssSyndromeProjector c η).IsHermitian := cssSyndromeProjector_isHermitian c η
    have hP : cssSyndromeProjector c η * cssSyndromeProjector c η = cssSyndromeProjector c η := by
      simpa using cssSyndromeProjector_mul c η η
    have hinner : coeffInner (cssSyndromeProjector c η *ᵥ ψ) (cssSyndromeProjector c η *ᵥ ψ) =
        coeffInner ψ (cssSyndromeProjector c η *ᵥ ψ) := by
      have ha : coeffInner (cssSyndromeProjector c η *ᵥ ψ) (cssSyndromeProjector c η *ᵥ ψ) =
          coeffInner ψ
            (Matrix.conjTranspose (cssSyndromeProjector c η) *ᵥ (cssSyndromeProjector c η *ᵥ ψ)) :=
        coeffInner_mulVec (cssSyndromeProjector c η) ψ (cssSyndromeProjector c η *ᵥ ψ)
      have hc : Matrix.conjTranspose (cssSyndromeProjector c η) *ᵥ (cssSyndromeProjector c η *ᵥ ψ)
          = cssSyndromeProjector c η *ᵥ ψ := by
        rw [hH.eq, Matrix.mulVec_mulVec, hP]
      exact ha.trans (congrArg (coeffInner ψ) hc)
    show (vecNormSq (cssSyndromeProjector c η *ᵥ ψ) : ℂ) = _
    exact (coeffInner_self (cssSyndromeProjector c η *ᵥ ψ)).symm.trans hinner
  have hsum : (∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
      (syndromeOutcomeMass c η ψ : ℂ)) = (vecNormSq ψ : ℂ) := by
    have h1 : (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), (syndromeOutcomeMass c η ψ : ℂ)) =
        ∑ η : (κX → ZMod 2) × (κZ → ZMod 2), coeffInner ψ (cssSyndromeProjector c η *ᵥ ψ) :=
      Finset.sum_congr rfl (fun η _ => key η)
    have h2 := coeffInner_sum_right ψ (Finset.univ : Finset ((κX → ZMod 2) × (κZ → ZMod 2)))
      (fun η => cssSyndromeProjector c η *ᵥ ψ)
    have h3 : (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), cssSyndromeProjector c η *ᵥ ψ) = ψ := by
      rw [← Matrix.sum_mulVec, cssSyndromeProjector_sum, Matrix.one_mulVec]
    calc (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), (syndromeOutcomeMass c η ψ : ℂ))
        = ∑ η : (κX → ZMod 2) × (κZ → ZMod 2), coeffInner ψ (cssSyndromeProjector c η *ᵥ ψ) := h1
      _ = coeffInner ψ (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), cssSyndromeProjector c η *ᵥ ψ) := h2
      _ = coeffInner ψ ψ := congrArg (coeffInner ψ) h3
      _ = (vecNormSq ψ : ℂ) := coeffInner_self ψ
  have hcast : ((∑ η : (κX → ZMod 2) × (κZ → ZMod 2), syndromeOutcomeMass c η ψ : ℝ) : ℂ)
      = (vecNormSq ψ : ℂ) := by
    rw [Complex.ofReal_sum]
    exact hsum
  exact Complex.ofReal_inj.mp hcast

/-- A Pauli correction of minimum weight among labels with syndrome `η`, or the zero label when
that syndrome has no representative. -/
noncomputable def clause1Corr {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) : PauliLabel ι :=
  if h : Set.Nonempty {e : PauliLabel ι | pauliSyndrome c e = η} then
    Function.argminOn (fun e : PauliLabel ι => pauliWeight e.1 e.2)
      {e : PauliLabel ι | pauliSyndrome c e = η} h
  else (0, 0)

/-- For a syndrome represented by `e`, `clause1Corr` is the selected weight minimizer over
labels with that syndrome. -/
theorem clause1Corr_eq_of_mem {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (e : PauliLabel ι) (he : pauliSyndrome c e = η) :
    clause1Corr c η = Function.argminOn (fun e : PauliLabel ι => pauliWeight e.1 e.2)
      {e : PauliLabel ι | pauliSyndrome c e = η} ⟨e, he⟩ := by
  have hne : Set.Nonempty {e : PauliLabel ι | pauliSyndrome c e = η} := ⟨e, he⟩
  show (if h : Set.Nonempty {e : PauliLabel ι | pauliSyndrome c e = η} then
    Function.argminOn (fun e : PauliLabel ι => pauliWeight e.1 e.2)
      {e : PauliLabel ι | pauliSyndrome c e = η} h
    else (0, 0)) = _
  rw [dif_pos hne]

/-- For a represented syndrome, the selected minimum-weight correction has that syndrome. -/
theorem clause1Corr_mem {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (e : PauliLabel ι) (he : pauliSyndrome c e = η) :
    pauliSyndrome c (clause1Corr c η) = η := by
  rw [clause1Corr_eq_of_mem c η e he]
  show Function.argminOn (fun e : PauliLabel ι => pauliWeight e.1 e.2)
      {e : PauliLabel ι | pauliSyndrome c e = η} ⟨e, he⟩ ∈
      {e : PauliLabel ι | pauliSyndrome c e = η}
  exact Function.argminOn_mem (fun e : PauliLabel ι => pauliWeight e.1 e.2) _ _

/-- The selected correction has weight at most that of any Pauli label with the given syndrome. -/
theorem clause1Corr_le {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (e : PauliLabel ι) (he : pauliSyndrome c e = η) :
    pauliWeight (clause1Corr c η).1 (clause1Corr c η).2 ≤ pauliWeight e.1 e.2 := by
  rw [clause1Corr_eq_of_mem c η e he]
  exact Function.argminOn_le (fun e : PauliLabel ι => pauliWeight e.1 e.2) _
    (show e ∈ {e : PauliLabel ι | pauliSyndrome c e = η} from he)

/-- The recovery program using `clause1Corr` and assigning zero classical decoding time. -/
noncomputable def clause1Prog {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) :
    RecoveryProgram c where
  corr := clause1Corr c
  decodeTime := fun _ => 0

/-- The program using `clause1Corr` satisfies minimum-weight soundness. -/
theorem clause1Prog_minimumWeightSound {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) :
    MinimumWeightSound (clause1Prog c) := by
  intro η e he
  show pauliWeight (clause1Corr c η).1 (clause1Corr c η).2 ≤ pauliWeight e.1 e.2
  exact clause1Corr_le c η e he

/-- The Pauli weight of a componentwise sum is at most the sum of the Pauli weights. -/
theorem pauliWeight_add_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (x x' z z' : ι → ZMod 2) :
    pauliWeight (x + x') (z + z') ≤ pauliWeight x z + pauliWeight x' z' := by
  classical
  show (Finset.univ.filter fun i => (x + x') i ≠ 0 ∨ (z + z') i ≠ 0).card ≤
    (Finset.univ.filter fun i => x i ≠ 0 ∨ z i ≠ 0).card +
      (Finset.univ.filter fun i => x' i ≠ 0 ∨ z' i ≠ 0).card
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  by_contra hn
  have h1 : ¬(x i ≠ 0 ∨ z i ≠ 0) := (not_or.mp hn).1
  have h2 : ¬(x' i ≠ 0 ∨ z' i ≠ 0) := (not_or.mp hn).2
  have hx : x i = 0 := not_not.mp (not_or.mp h1).1
  have hz : z i = 0 := not_not.mp (not_or.mp h1).2
  have hx' : x' i = 0 := not_not.mp (not_or.mp h2).1
  have hz' : z' i = 0 := not_not.mp (not_or.mp h2).2
  rcases hi with h | h <;> simp [Pi.add_apply, hx, hz, hx', hz'] at h

/-- If the CSS distance is at least `2 * t + 1`, a zero-syndrome Pauli label of weight at most
`2 * t` is a stabilizer label. -/
theorem isStabilizerLabel_of_syndrome_zero {ι κX κZ : Type} [Fintype ι] [Fintype κX]
    [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (t : ℕ) (e : PauliLabel ι) (hsyn : pauliSyndrome c e = (0, 0))
    (hw : pauliWeight e.1 e.2 ≤ 2 * t)
    (hd : ((2 * t + 1 : ℕ) : ℕ∞) ≤ cssDistance c) : IsStabilizerLabel c e := by
  by_contra hns
  have hz : c.hX *ᵥ e.2 = 0 := congrArg Prod.fst hsyn
  have hx : c.hZ *ᵥ e.1 = 0 := congrArg Prod.snd hsyn
  have hmem : (pauliWeight e.1 e.2 : ℕ∞) ∈
      {w : ℕ∞ | ∃ (x z : ι → ZMod 2), c.hX *ᵥ z = 0 ∧
        c.hZ *ᵥ x = 0 ∧ ¬(x ∈ LinearMap.range (Matrix.mulVecLin c.hXᵀ) ∧
        z ∈ LinearMap.range (Matrix.mulVecLin c.hZᵀ)) ∧ (pauliWeight x z : ℕ∞) = w} := by
    refine ⟨e.1, e.2, hz, hx, ?_, rfl⟩
    intro hh
    exact hns (show IsStabilizerLabel c e from hh)
  have hle : cssDistance c ≤ (pauliWeight e.1 e.2 : ℕ∞) := by
    have h := sInf_le hmem
    rwa [← cssDistance_eq_logical c] at h
  have h2 : ((2 * t + 1 : ℕ) : ℕ∞) ≤ (pauliWeight e.1 e.2 : ℕ∞) := hd.trans hle
  have h3 : 2 * t + 1 ≤ pauliWeight e.1 e.2 := by exact_mod_cast h2
  omega

/-- The minimum-weight recovery program corrects Pauli labels of weight at most `t` when the CSS
distance is at least `2 * t + 1`. -/
theorem clause1Prog_correctsUpTo {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) (t : ℕ)
    (hd : ((2 * t + 1 : ℕ) : ℕ∞) ≤ cssDistance c) : CorrectsUpTo (clause1Prog c) t := by
  intro e he
  have hcorr_mem : pauliSyndrome c (clause1Corr c (pauliSyndrome c e)) = pauliSyndrome c e :=
    clause1Corr_mem c (pauliSyndrome c e) e rfl
  have hmin : pauliWeight (clause1Corr c (pauliSyndrome c e)).1 (clause1Corr c (pauliSyndrome c e)).2
      ≤ pauliWeight e.1 e.2 :=
    clause1Corr_le c (pauliSyndrome c e) e rfl
  have hres : residualLabel (clause1Prog c) e =
      (e.1 + (clause1Corr c (pauliSyndrome c e)).1, e.2 + (clause1Corr c (pauliSyndrome c e)).2) := rfl
  have hsyn0 : pauliSyndrome c (residualLabel (clause1Prog c) e) = (0, 0) := by
    rw [hres]
    show (c.hX *ᵥ (e.2 + (clause1Corr c (pauliSyndrome c e)).2),
        c.hZ *ᵥ (e.1 + (clause1Corr c (pauliSyndrome c e)).1)) = (0, 0)
    have hη1 : c.hX *ᵥ (clause1Corr c (pauliSyndrome c e)).2 = c.hX *ᵥ e.2 :=
      congrArg Prod.fst hcorr_mem
    have hη2 : c.hZ *ᵥ (clause1Corr c (pauliSyndrome c e)).1 = c.hZ *ᵥ e.1 :=
      congrArg Prod.snd hcorr_mem
    rw [Matrix.mulVec_add, Matrix.mulVec_add, hη1, hη2]
    exact Prod.ext (binary_add_self _) (binary_add_self _)
  have hw : pauliWeight (residualLabel (clause1Prog c) e).1 (residualLabel (clause1Prog c) e).2 ≤ 2 * t := by
    rw [hres]
    show pauliWeight (e.1 + (clause1Corr c (pauliSyndrome c e)).1)
        (e.2 + (clause1Corr c (pauliSyndrome c e)).2) ≤ 2 * t
    have hadd := pauliWeight_add_le e.1 (clause1Corr c (pauliSyndrome c e)).1
      e.2 (clause1Corr c (pauliSyndrome c e)).2
    omega
  exact isStabilizerLabel_of_syndrome_zero c t (residualLabel (clause1Prog c) e) hsyn0 hw hd

/-- Conjugating a vector's outer-product matrix by `M` gives the outer-product matrix of `M *ᵥ
ψ`. -/
theorem densityOf_mul_conjTranspose {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (ψ : (ι → ZMod 2) → ℂ) :
    M * densityOf ψ * Matrix.conjTranspose M = densityOf (M *ᵥ ψ) := by
  classical
  ext a b
  have hL : (M * densityOf ψ * Matrix.conjTranspose M) a b =
      ∑ k : ι → ZMod 2, ∑ l : ι → ZMod 2,
        (M a k * ψ k) * (starRingEnd ℂ (M b l) * starRingEnd ℂ (ψ l)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, densityOf, Complex.star_def,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  have hR : densityOf (M *ᵥ ψ) a b =
      (∑ k, M a k * ψ k) * (∑ l, starRingEnd ℂ (M b l) * starRingEnd ℂ (ψ l)) := by
    simp only [densityOf, Matrix.mulVec, dotProduct, Complex.star_def, map_sum, map_mul]
  have key : (∑ k : ι → ZMod 2, ∑ l : ι → ZMod 2,
        (M a k * ψ k) * (starRingEnd ℂ (M b l) * starRingEnd ℂ (ψ l))) =
      (∑ k, M a k * ψ k) * (∑ l, starRingEnd ℂ (M b l) * starRingEnd ℂ (ψ l)) :=
    (Fintype.sum_mul_sum _ _).symm
  exact hL.trans (key.trans hR.symm)

/-- Multiplying a vector's outer-product matrix on both sides by a Hermitian matrix gives the
outer-product matrix of the transformed vector. -/
theorem densityOf_mul_hermitian {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (hH : P.IsHermitian) (ψ : (ι → ZMod 2) → ℂ) :
    P * densityOf ψ * P = densityOf (P *ᵥ ψ) := by
  have h := densityOf_mul_conjTranspose P ψ
  rw [hH.eq] at h
  exact h

/-- Scaling a vector by `z` scales its outer-product matrix by `z * star z`. -/
theorem densityOf_smul {ι : Type} [Fintype ι] [DecidableEq ι] (z : ℂ) (ψ : (ι → ZMod 2) → ℂ) :
    densityOf (z • ψ) = (z * star z) • densityOf ψ := by
  classical
  ext a b
  simp only [densityOf, Pi.smul_apply, smul_eq_mul, Complex.star_def, map_mul,
    Matrix.smul_apply]
  ring

/-- The outer-product matrix of the zero vector is zero. -/
theorem densityOf_zero {ι : Type} [Fintype ι] [DecidableEq ι] :
    densityOf (0 : (ι → ZMod 2) → ℂ) = 0 := by
  classical
  ext a b
  simp [densityOf]

/-- Multiplication by a binary phase leaves a vector's outer-product matrix unchanged. -/
theorem densityOf_smul_phase {ι : Type} [Fintype ι] [DecidableEq ι] (b : ZMod 2)
    (ψ : (ι → ZMod 2) → ℂ) : densityOf (phaseOfBit b • ψ) = densityOf ψ := by
  rw [densityOf_smul, phaseOfBit_star, phaseOfBit_mul_self, one_smul]

/-- The projector for outcome `b` fixes a vector on which the check acts by `phaseOfBit b`. -/
theorem cssCheckProjector_fixes {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) (b : ZMod 2)
    (v : (ι → ZMod 2) → ℂ) (h : S *ᵥ v = phaseOfBit b • v) :
    cssCheckProjector S b *ᵥ v = v := by
  have h1 : ((1 : Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ) + phaseOfBit b • S) *ᵥ v = v + v := by
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, h, smul_smul,
      phaseOfBit_mul_self, one_smul]
  rw [cssCheckProjector, Matrix.smul_mulVec, h1]
  rw [smul_add, ← add_smul, show (2 : ℂ)⁻¹ + 2⁻¹ = 1 from by ring, one_smul]

/-- A Pauli error applied to a codespace vector is an eigenvector of each check with eigenvalue
given by the corresponding syndrome bit. -/
theorem cssCheck_mulVec_pauli {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] (c : CssData ι κX κZ) (e : PauliLabel ι) (ψ : (ι → ZMod 2) → ℂ)
    (hψ : ψ ∈ cssCodespace c) (k : κX ⊕ κZ) :
    cssCheck c k *ᵥ ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) =
      phaseOfBit (Sum.elim (pauliSyndrome c e).1 (pauliSyndrome c e).2 k) •
        ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) := by
  cases k with
  | inl i =>
    have hrow : cssPauliX (c.hX i) *ᵥ ψ = ψ := (mem_cssCodespace_iff' c ψ).mp hψ |>.1 i
    have hph : bitDot e.2 (c.hX i) = (pauliSyndrome c e).1 i := by rw [bitDot_comm]; rfl
    have hE := cssPauliXZ_mul e.1 (c.hX i) e.2 0
    simp only [cssPauliZ_zero, mul_one, add_zero] at hE
    have hE' : cssPauliX (e.1 + c.hX i) * cssPauliZ e.2 =
        phaseOfBit (bitDot e.2 (c.hX i)) •
          ((cssPauliX e.1 * cssPauliZ e.2) * cssPauliX (c.hX i)) := by
      have h := congrArg (fun T => phaseOfBit (bitDot e.2 (c.hX i)) • T) hE
      simp only [smul_smul, phaseOfBit_mul_self, one_smul] at h
      exact h.symm
    have h1 : cssPauliX (c.hX i) * (cssPauliX e.1 * cssPauliZ e.2) =
        cssPauliX (e.1 + c.hX i) * cssPauliZ e.2 := by
      rw [← mul_assoc, cssPauliX_mul, add_comm]
    calc cssCheck c (Sum.inl i) *ᵥ ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ)
        = (cssPauliX (c.hX i) * (cssPauliX e.1 * cssPauliZ e.2)) *ᵥ ψ := by
            rw [Matrix.mulVec_mulVec]
            rfl
      _ = (cssPauliX (e.1 + c.hX i) * cssPauliZ e.2) *ᵥ ψ := by rw [h1]
      _ = (phaseOfBit (bitDot e.2 (c.hX i)) •
            ((cssPauliX e.1 * cssPauliZ e.2) * cssPauliX (c.hX i))) *ᵥ ψ := by rw [hE']
      _ = phaseOfBit (bitDot e.2 (c.hX i)) •
            ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ (cssPauliX (c.hX i) *ᵥ ψ)) := by
            rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
      _ = phaseOfBit (bitDot e.2 (c.hX i)) • ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) := by
            rw [hrow]
      _ = phaseOfBit (Sum.elim (pauliSyndrome c e).1 (pauliSyndrome c e).2 (Sum.inl i)) •
            ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) := by rw [hph, Sum.elim_inl]
  | inr j =>
    have hrow : cssPauliZ (c.hZ j) *ᵥ ψ = ψ := (mem_cssCodespace_iff' c ψ).mp hψ |>.2 j
    have hph : bitDot (c.hZ j) e.1 = (pauliSyndrome c e).2 j := rfl
    have hE := cssPauliXZ_mul e.1 0 e.2 (c.hZ j)
    simp only [cssPauliX_zero, one_mul, bitDot_zero_right, phaseOfBit_zero, one_smul,
        add_zero] at hE
    have hstep : cssPauliZ (c.hZ j) * (cssPauliX e.1 * cssPauliZ e.2) =
        phaseOfBit (bitDot (c.hZ j) e.1) •
          ((cssPauliX e.1 * cssPauliZ e.2) * cssPauliZ (c.hZ j)) := by
      have h := cssPauliZX_phase e.1 (c.hZ j)
      calc cssPauliZ (c.hZ j) * (cssPauliX e.1 * cssPauliZ e.2)
          = (cssPauliZ (c.hZ j) * cssPauliX e.1) * cssPauliZ e.2 := by rw [← mul_assoc]
        _ = (phaseOfBit (bitDot (c.hZ j) e.1) • (cssPauliX e.1 * cssPauliZ (c.hZ j))) *
              cssPauliZ e.2 := by rw [h]
        _ = phaseOfBit (bitDot (c.hZ j) e.1) •
              ((cssPauliX e.1 * cssPauliZ (c.hZ j)) * cssPauliZ e.2) := by
              rw [Matrix.smul_mul]
        _ = phaseOfBit (bitDot (c.hZ j) e.1) •
              (cssPauliX e.1 * (cssPauliZ (c.hZ j) * cssPauliZ e.2)) := by
              rw [mul_assoc]
        _ = phaseOfBit (bitDot (c.hZ j) e.1) •
              (cssPauliX e.1 * cssPauliZ (c.hZ j + e.2)) := by
              rw [cssPauliZ_mul]
        _ = phaseOfBit (bitDot (c.hZ j) e.1) •
              (cssPauliX e.1 * cssPauliZ (e.2 + c.hZ j)) := by
              rw [add_comm]
        _ = phaseOfBit (bitDot (c.hZ j) e.1) •
              ((cssPauliX e.1 * cssPauliZ e.2) * cssPauliZ (c.hZ j)) := by
              rw [← hE]
    calc cssCheck c (Sum.inr j) *ᵥ ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ)
        = (cssPauliZ (c.hZ j) * (cssPauliX e.1 * cssPauliZ e.2)) *ᵥ ψ := by
            rw [Matrix.mulVec_mulVec]
            rfl
      _ = (phaseOfBit (bitDot (c.hZ j) e.1) •
            ((cssPauliX e.1 * cssPauliZ e.2) * cssPauliZ (c.hZ j))) *ᵥ ψ := by rw [hstep]
      _ = phaseOfBit (bitDot (c.hZ j) e.1) •
            ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ (cssPauliZ (c.hZ j) *ᵥ ψ)) := by
            rw [Matrix.smul_mulVec, Matrix.mulVec_mulVec]
      _ = phaseOfBit (bitDot (c.hZ j) e.1) • ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) := by
            rw [hrow]
      _ = phaseOfBit (Sum.elim (pauliSyndrome c e).1 (pauliSyndrome c e).2 (Sum.inr j)) •
            ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) := by rw [hph, Sum.elim_inr]

/-- The projector for the true Pauli syndrome fixes the corrupted codespace vector. -/
theorem syndromeProjector_fixes_pauli {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) (e : PauliLabel ι)
    (ψ : (ι → ZMod 2) → ℂ) (hψ : ψ ∈ cssCodespace c) :
    cssSyndromeProjector c (pauliSyndrome c e) *ᵥ ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) =
      (cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ := by
  classical
  unfold cssSyndromeProjector
  apply list_prod_mulVec
  intro S hS
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hS
  exact cssCheckProjector_fixes _ _ _ (cssCheck_mulVec_pauli c e ψ hψ k)

/-- Applying a binary Pauli operator preserves the squared norm of a vector. -/
theorem vecNormSq_pauli {ι : Type} [Fintype ι] [DecidableEq ι] (x z : ι → ZMod 2)
    (ψ : (ι → ZMod 2) → ℂ) :
    vecNormSq ((cssPauliX x * cssPauliZ z) *ᵥ ψ) = vecNormSq ψ := by
  classical
  have hE : (cssPauliX x * cssPauliZ z).conjTranspose * (cssPauliX x * cssPauliZ z) = 1 := by
    rw [Matrix.conjTranspose_mul, (cssPauliX_isHermitian x).eq, (cssPauliZ_isHermitian z).eq]
    conv_lhs => rw [mul_assoc, ← mul_assoc (cssPauliX x) (cssPauliX x) (cssPauliZ z),
      cssPauliX_self_mul, one_mul]
    exact cssPauliZ_self_mul z
  have h1 : coeffInner ((cssPauliX x * cssPauliZ z) *ᵥ ψ) ((cssPauliX x * cssPauliZ z) *ᵥ ψ) =
      coeffInner ψ ((cssPauliX x * cssPauliZ z).conjTranspose *ᵥ ((cssPauliX x * cssPauliZ z) *ᵥ ψ)) :=
    coeffInner_mulVec (cssPauliX x * cssPauliZ z) ψ _
  have h2 : (cssPauliX x * cssPauliZ z).conjTranspose *ᵥ ((cssPauliX x * cssPauliZ z) *ᵥ ψ) = ψ := by
    rw [Matrix.mulVec_mulVec, hE, Matrix.one_mulVec]
  have h3 : coeffInner ((cssPauliX x * cssPauliZ z) *ᵥ ψ) ((cssPauliX x * cssPauliZ z) *ᵥ ψ) =
      coeffInner ψ ψ := by rw [h1, h2]
  have h4 := coeffInner_self ((cssPauliX x * cssPauliZ z) *ᵥ ψ)
  have h5 := coeffInner_self ψ
  exact_mod_cast h4.symm.trans (h3.trans h5)

/-- For a Pauli-corrupted codespace vector, the true syndrome outcome has mass equal to the
original squared norm. -/
theorem syndromeOutcomeMass_pauli {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) (e : PauliLabel ι)
    (ψ : (ι → ZMod 2) → ℂ) (hψ : ψ ∈ cssCodespace c) :
    syndromeOutcomeMass c (pauliSyndrome c e) ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) = vecNormSq ψ := by
  classical
  have hfix := syndromeProjector_fixes_pauli c e ψ hψ
  show vecNormSq (cssSyndromeProjector c (pauliSyndrome c e) *ᵥ ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ))
    = vecNormSq ψ
  rw [hfix]
  exact vecNormSq_pauli e.1 e.2 ψ

/-- The recovery channel on a vector's outer-product matrix is the sum of the outer-product
matrices of its syndrome-projected and corrected vectors. -/
theorem recoveryChannel_densityOf {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (prog : RecoveryProgram c) (ψ : (ι → ZMod 2) → ℂ) :
    recoveryChannel c prog (densityOf ψ) =
      ∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
        densityOf ((cssPauliX (prog.corr η).1 * cssPauliZ (prog.corr η).2) *ᵥ
          (cssSyndromeProjector c η *ᵥ ψ)) := by
  classical
  show (∑ η : (κX → ZMod 2) × (κZ → ZMod 2),
      (fun P R => R * (P * densityOf ψ * P) * Matrix.conjTranspose R)
        (cssSyndromeProjector c η)
        (cssPauliX (prog.corr η).1 * cssPauliZ (prog.corr η).2)) = _
  refine Finset.sum_congr rfl (fun η _ => ?_)
  show (cssPauliX (prog.corr η).1 * cssPauliZ (prog.corr η).2) *
      (cssSyndromeProjector c η * densityOf ψ * cssSyndromeProjector c η) *
      Matrix.conjTranspose (cssPauliX (prog.corr η).1 * cssPauliZ (prog.corr η).2) = _
  rw [densityOf_mul_hermitian (cssSyndromeProjector c η) (cssSyndromeProjector_isHermitian c η) ψ,
    densityOf_mul_conjTranspose]

/-- Every CSS code possesses an orthonormal encoding basis indexed by binary strings of length
`c.encodedQubits`. -/
theorem exists_cssEncoding {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ) :
    Nonempty (CssEncoding c c.encodedQubits) := by
  classical
  let e := (WithLp.linearEquiv 2 ℂ ((ι → ZMod 2) → ℂ)).symm
  let S := (cssCodespace c).map e.toLinearMap
  have hdim : Module.finrank ℂ S = Fintype.card (Fin c.encodedQubits → ZMod 2) := by
    rw [e.finrank_map_eq, cssCodespace_finrank]
    simp
  let b := (stdOrthonormalBasis ℂ S).reindex
    ((finCongr hdim).trans (Fintype.equivFin (Fin c.encodedQubits → ZMod 2)).symm)
  let f : S →ₗ[ℂ] ((ι → ZMod 2) → ℂ) := e.symm.toLinearMap.comp S.subtype
  have hmem (i : Fin c.encodedQubits → ZMod 2) : f (b i) ∈ cssCodespace c := by
    obtain ⟨x, hx, hxi⟩ := (b i).property
    change e.symm ((b i).val) ∈ cssCodespace c
    rw [← hxi]
    exact hx
  have hinner (u v : S) : coeffInner (f u) (f v) = inner ℂ u v := by
    change (∑ a, star (u.val a) * v.val a) = ∑ a, v.val a * star (u.val a)
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  refine ⟨⟨fun i => f (b i), hmem, ?_, ?_⟩⟩
  · intro i j
    exact (hinner (b i) (b j)).trans (b.inner_eq_ite i j)
  · intro v hv
    let x : S := e.submoduleMap (cssCodespace c) ⟨v, hv⟩
    have hsum := congrArg f (b.sum_repr x)
    have hfx : f x = v := by exact e.symm_apply_apply v
    rw [hfx, map_sum] at hsum
    rw [← hsum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- A syndrome projector different from the true Pauli syndrome annihilates the corrupted
codespace vector. -/
theorem syndromeProjector_other_pauli {ι κX κZ : Type} [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ] (c : CssData ι κX κZ)
    (e : PauliLabel ι) (ψ : (ι → ZMod 2) → ℂ) (hψ : ψ ∈ cssCodespace c)
    (η : (κX → ZMod 2) × (κZ → ZMod 2)) (hη : η ≠ pauliSyndrome c e) :
    cssSyndromeProjector c η *ᵥ ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) = 0 := by
  rw [← syndromeProjector_fixes_pauli c e ψ hψ, Matrix.mulVec_mulVec,
    cssSyndromeProjector_mul, if_neg hη, Matrix.zero_mulVec]

/-- If decoding leaves a stabilizer residual, the recovery channel restores the outer-product
matrix of every codespace vector after the Pauli error. -/
theorem recoveryChannel_corrects_density {ι κX κZ : Type} [Fintype ι] [Fintype κX]
    [Fintype κZ] [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]
    (c : CssData ι κX κZ) (prog : RecoveryProgram c) (e : PauliLabel ι)
    (he : IsStabilizerLabel c (residualLabel prog e))
    (ψ : (ι → ZMod 2) → ℂ) (hψ : ψ ∈ cssCodespace c) :
    recoveryChannel c prog (densityOf ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ)) =
      densityOf ψ := by
  classical
  rw [recoveryChannel_densityOf, Finset.sum_eq_single (pauliSyndrome c e)]
  · rw [syndromeProjector_fixes_pauli c e ψ hψ, Matrix.mulVec_mulVec, cssPauliXZ_mul,
      Matrix.smul_mulVec]
    have hres := isStabilizerLabel_fixes c he ψ hψ
    have hfix : (cssPauliX ((prog.corr (pauliSyndrome c e)).1 + e.1) *
        cssPauliZ ((prog.corr (pauliSyndrome c e)).2 + e.2)) *ᵥ ψ = ψ := by
      simpa only [residualLabel, add_comm] using! hres
    rw [hfix, densityOf_smul_phase]
  · intro η _ hη
    rw [syndromeProjector_other_pauli c e ψ hψ η hη, Matrix.mulVec_zero, densityOf_zero]
  · simp

/-- A CSS code of distance at least `2 * t + 1` possesses an encoding and a minimum-weight
recovery program correcting weight-`t` Pauli errors, preserving logical references, and
restoring encoded basis-state outer products. Syndrome masses obey completeness and
true-syndrome identities, and recovery receipts satisfy the stated gate, measurement, and
classical-time bounds. -/
theorem g1 :
  ∀ (ι κX κZ : Type) [Fintype ι] [Fintype κX] [Fintype κZ]
    [DecidableEq ι] [DecidableEq κX] [DecidableEq κZ]
    (c : CssData ι κX κZ) (t : ℕ),
    ((2 * t + 1 : ℕ) : ℕ∞) ≤ cssDistance c →
    ∃ (E : CssEncoding c c.encodedQubits) (prog : RecoveryProgram c) (Bg Bm Bc : ℕ),

      CorrectsUpTo prog t ∧

      MinimumWeightSound prog ∧

      (∀ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ t →
        LogicalReferencePreserved c (residualLabel prog e)) ∧

      (∀ ψ : (ι → ZMod 2) → ℂ,
        (∑ η : (κX → ZMod 2) × (κZ → ZMod 2), syndromeOutcomeMass c η ψ) = vecNormSq ψ) ∧

      (∀ (e : PauliLabel ι) (ψ : (ι → ZMod 2) → ℂ),
        ψ ∈ cssCodespace c →
        syndromeOutcomeMass c (pauliSyndrome c e)
          ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ ψ) = vecNormSq ψ) ∧

      (∀ (e : PauliLabel ι) (b : Fin c.encodedQubits → ZMod 2),
        pauliWeight e.1 e.2 ≤ t →
        recoveryChannel c prog
          (densityOf ((cssPauliX e.1 * cssPauliZ e.2) *ᵥ E.enc b)) = densityOf (E.enc b)) ∧

      (Bg = syndromeExtractionGates c + t ∧ Bm = syndromeMeasurements c ∧
        Bc = decodeTimeBound c prog) ∧

      (∀ e : PauliLabel ι, pauliWeight e.1 e.2 ≤ t →
        ∃ r : RecoveryReceipt c prog, r.Realizes e ∧
          r.cost.gates ≤ Bg ∧ r.cost.measurements = Bm ∧ r.cost.classicalTime ≤ Bc) := by
  intro ι κX κZ _ _ _ _ _ _ c t hd
  classical
  obtain ⟨E⟩ := exists_cssEncoding c
  refine ⟨E, clause1Prog c, syndromeExtractionGates c + t, syndromeMeasurements c,
    decodeTimeBound c (clause1Prog c), clause1Prog_correctsUpTo c t hd,
    clause1Prog_minimumWeightSound c, ?_, sum_syndromeOutcomeMass c, ?_, ?_,
    ⟨rfl, rfl, rfl⟩, ?_⟩
  · intro e he
    exact logicalReferencePreserved_of_stabilizer c (clause1Prog_correctsUpTo c t hd e he)
  · intro e ψ hψ
    exact syndromeOutcomeMass_pauli c e ψ hψ
  · intro e b he
    exact recoveryChannel_corrects_density c (clause1Prog c) e (clause1Prog_correctsUpTo c t hd e he)
      (E.enc b) (E.mem_codespace b)
  · intro e he
    let η := pauliSyndrome c e
    refine ⟨⟨η, (clause1Prog c).corr η, recoveryCost c (clause1Prog c) η⟩,
      ⟨rfl, rfl, rfl⟩, ?_, rfl, ?_⟩
    · exact Nat.add_le_add_left ((clause1Corr_le c η e rfl).trans he) _
    · exact Finset.le_sup (f := fun η => (clause1Prog c).decodeTime η) (Finset.mem_univ η)

end Qatlib.Concepts.CodingDecoding.CssTesters.CodingDecoding
