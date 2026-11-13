/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StabilizerSim04.MainResults.Basic

/-!
# Standard Pauli generators and the all-zero stabilizer

This module identifies the standard tableau rows with the single-site Pauli elements and proves
that they generate all Pauli words up to phase. It characterizes the elements fixing the
all-zero state, proves exact generation by the standard Z tableau, and counts these stabilizers,
supplying structural ingredients for [AaronsonGottesman2004].

## Main statements

* `standard_projective_pauli_generation`: the combined standard rows generate every Pauli word
  up to phase.
* `standard_stabilizer_generates_ket_zero`: the standard Z rows generate exactly the fixing
  Pauli elements.
* `stabilizerCount_ketZero`: the all-zero state has `2 ^ n` fixing Pauli elements.

## References

* [Aaronson and Gottesman, 2004][AaronsonGottesman2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.StabilizerSim04.MainResults

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped Classical BigOperators

/-- The zero-phase Pauli element acting as X at qubit `i` and as the identity elsewhere. -/
def XAt {n : ℕ} (i : Fin n) : PauliElem n :=
  ⟨fun k => if k = i then Pauli1.X else Pauli1.I, 0⟩

/-- The word of `XAt i` has X at `i` and the identity elsewhere. -/
@[simp] theorem XAt_word {n : ℕ} (i : Fin n) :
    (XAt i).word = fun k => if k = i then Pauli1.X else Pauli1.I := rfl

/-- The word of `ZAt i` has Z at `i` and the identity elsewhere. -/
@[simp] theorem ZAt_word {n : ℕ} (i : Fin n) :
    (ZAt i).word = fun k => if k = i then Pauli1.Z else Pauli1.I := rfl

/-- The phase of `XAt i` equals zero. -/
@[simp] theorem XAt_phase {n : ℕ} (i : Fin n) : (XAt i).phase = 0 := rfl

/-- Decoding the standard destabilizer row at `i` yields `XAt i`. -/
theorem standardDestabilizer_decode (n : ℕ) (i : Fin n) :
    (standardDestabilizer n i).decode = XAt i := by
  apply pauli_ext
  · funext k
    by_cases h : k = i <;> simp [standardDestabilizer, Row.decode, XAt, letter, h]
  · rfl

/-- Decoding the standard stabilizer row at `i` yields `ZAt i`. -/
theorem standardStabilizer_decode (n : ℕ) (i : Fin n) :
    (standardStabilizer n i).decode = ZAt i := by
  apply pauli_ext
  · funext k
    by_cases h : k = i <;> simp [standardStabilizer, Row.decode, ZAt, letter, h]
  · rfl

/-- The list of all single-site X generators followed by all single-site Z generators. -/
def standardGenList (n : ℕ) : List (PauliElem n) :=
  (List.finRange n).flatMap (fun i => [XAt i, ZAt i])

/-- Every single-site X element belongs to `standardGenList n`. -/
theorem XAt_mem_standardGenList {n : ℕ} (i : Fin n) : XAt i ∈ standardGenList n := by
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
  simp

/-- Every single-site Z element belongs to `standardGenList n`. -/
theorem ZAt_mem_standardGenList {n : ℕ} (i : Fin n) : ZAt i ∈ standardGenList n := by
  refine List.mem_flatMap.mpr ⟨i, List.mem_finRange i, ?_⟩
  simp

/-- Every single-site X element occurs among the standard destabilizer generators. -/
theorem XAt_mem_tableauDestabilizer {n : ℕ} (i : Fin n) :
    XAt i ∈ tableauGenerators (standardDestabilizer n) := by
  rw [tableauGenerators]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, standardDestabilizer_decode n i⟩

/-- Every single-site Z element occurs among the standard stabilizer generators. -/
theorem ZAt_mem_tableauStabilizer {n : ℕ} (i : Fin n) :
    ZAt i ∈ tableauGenerators (standardStabilizer n) := by
  rw [tableauGenerators]
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, standardStabilizer_decode n i⟩

/-- Membership in `standardGenList n` is equivalent to being a single-site X or Z element. -/
theorem mem_standardGenList_iff {n : ℕ} {g : PauliElem n} :
    g ∈ standardGenList n ↔
      ∃ i : Fin n, g = XAt i ∨ g = ZAt i := by
  constructor
  · intro hg
    rw [standardGenList, List.mem_flatMap] at hg
    obtain ⟨i, -, hi⟩ := hg
    exact ⟨i, by simpa using! hi⟩
  · rintro ⟨i, rfl | rfl⟩
    · exact XAt_mem_standardGenList i
    · exact ZAt_mem_standardGenList i

/-- Every standard generator belongs to the concatenated standard destabilizer and stabilizer
generator lists. -/
theorem standardGenList_mem_tableauGenerators {n : ℕ} {g : PauliElem n}
    (hg : g ∈ standardGenList n) :
    g ∈ tableauGenerators (standardDestabilizer n) ++
      tableauGenerators (standardStabilizer n) := by
  obtain ⟨i, rfl | rfl⟩ := (mem_standardGenList_iff).mp hg
  · exact List.mem_append_left _ (XAt_mem_tableauDestabilizer i)
  · exact List.mem_append_right _ (ZAt_mem_tableauStabilizer i)

/-- The list of single-site X and Z factors representing a Pauli letter at `i` up to phase. -/
def letterList {n : ℕ} (i : Fin n) : Pauli1 → List (PauliElem n)
  | Pauli1.I => []
  | Pauli1.X => [XAt i]
  | Pauli1.Y => [XAt i, ZAt i]
  | Pauli1.Z => [ZAt i]

/-- Multiplying by the factors for a letter changes the Pauli word by that letter at `i` and
leaves other sites unchanged. -/
theorem foldl_letterList_word {n : ℕ} (q : PauliElem n) (i : Fin n) (a : Pauli1) :
    ((letterList i a).foldl PauliElem.mul q).word =
      fun k => pauliMul1 (q.word k) (if k = i then a else Pauli1.I) := by
  funext k
  cases a with
  | I =>
      by_cases h : k = i <;> simp [letterList, h, pauliMul1_right_I]
  | X =>
      by_cases h : k = i <;>
        simp [letterList, XAt, PauliElem.mul, h, pauliMul1_right_I]
  | Y =>
      by_cases h : k = i
      · simp [letterList, XAt, ZAt, PauliElem.mul, h, pauliMul1_assoc]
        rfl
      · simp [letterList, XAt, ZAt, PauliElem.mul, h, pauliMul1_right_I]
  | Z =>
      by_cases h : k = i <;>
        simp [letterList, ZAt, PauliElem.mul, h, pauliMul1_right_I]

/-- A Pauli word supported in a finite set can be obtained, up to phase, by a product of
standard generators. -/
theorem exists_word_gen (n : ℕ) :
    ∀ (S : Finset (Fin n)) (w : PauliWord n), (∀ i, i ∉ S → w i = Pauli1.I) →
      ∃ l : List (PauliElem n),
        (∀ g ∈ l, g ∈ standardGenList n) ∧
          (l.foldl PauliElem.mul 1).word = w := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro w hw
      refine ⟨[], by simp, ?_⟩
      funext k
      rw [hw k (by simp)]
      rfl
  | insert a S ha ih =>
      intro w hw
      set w' : PauliWord n := fun k => if k = a then Pauli1.I else w k with hw'def
      have hw' : ∀ i, i ∉ S → w' i = Pauli1.I := by
        intro i hi
        rw [hw'def]
        by_cases hia : i = a
        · simp [hia]
        · have his : i ∉ insert a S := by simp [hia, hi]
          simp [hia, hw i his]
      obtain ⟨l, hmem, hword⟩ := ih w' hw'
      refine ⟨l ++ letterList a (w a), ?_, ?_⟩
      · intro g hg
        rw [List.mem_append] at hg
        rcases hg with hg | hg
        · exact hmem g hg
        · cases hwa : w a with
          | I =>
              have hlist : letterList a (w a) = [] := by simp [letterList, hwa]
              rw [hlist] at hg
              exact absurd hg (by simp)
          | X =>
              have hlist : letterList a (w a) = [XAt a] := by
                simp [letterList, hwa]
              rw [hlist] at hg
              simp only [List.mem_singleton] at hg
              rw [hg]
              exact XAt_mem_standardGenList a
          | Y =>
              have hlist : letterList a (w a) = [XAt a, ZAt a] := by
                simp [letterList, hwa]
              rw [hlist] at hg
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                or_false] at hg
              rcases hg with rfl | rfl
              · exact XAt_mem_standardGenList a
              · exact ZAt_mem_standardGenList a
          | Z =>
              have hlist : letterList a (w a) = [ZAt a] := by
                simp [letterList, hwa]
              rw [hlist] at hg
              simp only [List.mem_singleton] at hg
              rw [hg]
              exact ZAt_mem_standardGenList a
      · rw [List.foldl_append, foldl_letterList_word]
        funext k
        rw [hword]
        by_cases hk : k = a
        · simp [hw'def, hk, pauliMul1_I]
        · simp [hw'def, hk, pauliMul1_right_I]

/-- The group generated by the standard destabilizer and stabilizer rows contains an element
with any prescribed Pauli word [AaronsonGottesman2004]. -/
theorem standard_projective_pauli_generation (n : ℕ) (p : PauliElem n) :
    ∃ q ∈ generatedGroup (tableauGenerators (standardDestabilizer n) ++
        tableauGenerators (standardStabilizer n)), q.word = p.word := by
  let S : Finset (Fin n) := Finset.univ.filter (fun i => p.word i ≠ Pauli1.I)
  have hS : ∀ i, i ∉ S → p.word i = Pauli1.I := by
    intro i hi
    by_contra hne
    exact hi (by simp [S, hne])
  obtain ⟨l, hmem, hword⟩ := exists_word_gen n S p.word hS
  refine ⟨l.foldl PauliElem.mul 1, ⟨l, ?_, rfl⟩, hword⟩
  intro g hg
  exact standardGenList_mem_tableauGenerators (hmem g hg)

/-- A single-site Z operator fixes the all-zero state. -/
theorem ZAt_fixes_ketZero {n : ℕ} (i : Fin n) :
    op (ZAt i) *ᵥ KetZero n = KetZero n := by
  have h := op_ZI_stabilizes_ket_zero (n := n)
    (fun k => if k = i then Pauli1.Z else Pauli1.I) (by
      intro k
      by_cases hk : k = i <;> simp [hk])
  simpa [ZAt, KetZero] using! h

/-- A product of single-site Z elements, starting from an element fixing the all-zero state,
also fixes that state. -/
theorem foldl_mul_fixes_ketZero {n : ℕ} (l : List (PauliElem n))
    (h : ∀ g ∈ l, ∃ i : Fin n, g = ZAt i) (q : PauliElem n)
    (hq : op q *ᵥ KetZero n = KetZero n) :
    op (l.foldl PauliElem.mul q) *ᵥ KetZero n = KetZero n := by
  induction l generalizing q with
  | nil => simpa using! hq
  | cons g l ih =>
      obtain ⟨i, hi⟩ := h g List.mem_cons_self
      have hz : op g *ᵥ KetZero n = KetZero n := by
        rw [hi]
        exact ZAt_fixes_ketZero i
      have hq' : op (PauliElem.mul q g) *ᵥ KetZero n = KetZero n := by
        rw [op_mul, ← Matrix.mulVec_mulVec, hz, hq]
      have htail := ih (fun x hx => h x (List.mem_cons_of_mem g hx))
        (PauliElem.mul q g) hq'
      simpa using! htail

/-- A Pauli element fixing the all-zero state has only Z and identity letters and has phase
zero. -/
theorem fixes_ketZero_data {n : ℕ} {p : PauliElem n}
    (h : op p *ᵥ KetZero n = KetZero n) :
    (∀ k, p.word k = Pauli1.Z ∨ p.word k = Pauli1.I) ∧ p.phase = 0 := by
  have hentry : (Complex.I ^ p.phase.val : ℂ) *
      ∏ k, P1 (p.word k) false false = 1 := by
    have hh := congrFun h (ZeroStr n)
    rw [KetZero, mulVec_ket] at hh
    beta_reduce at hh
    rw [op_apply] at hh
    dsimp only [ZeroStr] at hh
    rw [Qatlib.Foundations.PureStateMath.ket_apply,
      if_pos rfl] at hh
    exact hh
  have hprod : (∏ k, P1 (p.word k) false false) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hentry
    exact zero_ne_one hentry
  have hword : ∀ k, p.word k = Pauli1.Z ∨ p.word k = Pauli1.I := by
    intro k
    have hk : P1 (p.word k) false false ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hprod) k (Finset.mem_univ k)
    have hne : P1 (p.word k) false false ≠ 0 ↔
        p.word k = Pauli1.I ∨ p.word k = Pauli1.Z := by
      cases p.word k <;> simp [P1]
    rcases hne.mp hk with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hone : (∏ k, P1 (p.word k) false false) = 1 := by
    refine Finset.prod_eq_one fun k _ => ?_
    rcases hword k with h | h <;> rw [h] <;> simp [P1]
  have hI : (Complex.I ^ p.phase.val : ℂ) = 1 := by
    rw [hone, mul_one] at hentry
    exact hentry
  have hval : p.phase.val = 0 := by
    apply complex_I_pow_inj (ZMod.val_lt p.phase) (by norm_num)
    simpa using! hI
  have hphase : p.phase = 0 := by
    calc p.phase = (p.phase.val : ZMod 4) :=
          (ZMod.natCast_zmod_val p.phase).symm
      _ = 0 := by rw [hval]; simp
  exact ⟨hword, hphase⟩

/-- A word equal to Z on a finite set and to the identity elsewhere is exactly a product of
single-site Z elements with phase zero. -/
theorem exists_zproduct (n : ℕ) :
    ∀ (S : Finset (Fin n)) (w : PauliWord n),
      (∀ i, i ∉ S → w i = Pauli1.I) →
      (∀ i, i ∈ S → w i = Pauli1.Z) →
      ∃ l : List (PauliElem n),
        (∀ g ∈ l, ∃ i : Fin n, g = ZAt i) ∧
          l.foldl PauliElem.mul 1 = (⟨w, 0⟩ : PauliElem n) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro w hw _
      refine ⟨[], by simp, ?_⟩
      apply pauli_ext
      · funext k
        change (1 : PauliElem n).word k = w k
        rw [hw k (by simp)]
        rfl
      · rfl
  | insert a S ha ih =>
      intro w hw hwS
      set w' : PauliWord n := fun k => if k = a then Pauli1.I else w k with hw'def
      have hw' : ∀ i, i ∉ S → w' i = Pauli1.I := by
        intro i hi
        rw [hw'def]
        by_cases hia : i = a
        · simp [hia]
        · have his : i ∉ insert a S := by simp [hia, hi]
          simp [hia, hw i his]
      have hwS' : ∀ i, i ∈ S → w' i = Pauli1.Z := by
        intro i hi
        have hia : i ≠ a := fun h => ha (h ▸ hi)
        rw [hw'def]
        simp [hia, hwS i (Finset.mem_insert_of_mem hi)]
      obtain ⟨l, hmem, hprod⟩ := ih w' hw' hwS'
      refine ⟨l ++ [ZAt a], ?_, ?_⟩
      · intro g hg
        rw [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hmem g hg
        · exact ⟨a, rfl⟩
      · rw [List.foldl_append, hprod]
        apply pauli_ext
        · funext k
          by_cases hk : k = a
          · have hZ : w a = Pauli1.Z := hwS a (Finset.mem_insert_self a S)
            simp [PauliElem.mul, ZAt, hw'def, hk, hZ]
            rfl
          · simp [PauliElem.mul, ZAt, hw'def, hk, pauliMul1_right_I]
        · have hzero : ∀ i,
              pauliMulPhase (w' i) (if i = a then Pauli1.Z else Pauli1.I) = 0 := by
            intro i
            by_cases hia : i = a
            · simp [hw'def, hia]
              rfl
            · simp [hia, pauliMulPhase_right_I]
          simp [PauliElem.mul, ZAt, hzero]

/-- The standard stabilizer tableau generates exactly the Pauli elements fixing the all-zero
state [AaronsonGottesman2004]. -/
theorem standard_stabilizer_generates_ket_zero (n : ℕ) :
    GeneratesStabilizer (standardStabilizer n) (KetZero n) := by
  intro p
  constructor
  · intro hp
    obtain ⟨hword, hphase⟩ := fixes_ketZero_data hp
    let S : Finset (Fin n) := Finset.univ.filter (fun i => p.word i = Pauli1.Z)
    have hSout : ∀ i, i ∉ S → p.word i = Pauli1.I := by
      intro i hi
      have hi' : ¬ (p.word i = Pauli1.Z) := by
        intro h
        exact hi (by simp [S, h])
      rcases hword i with h | h
      · exact absurd h hi'
      · exact h
    have hSin : ∀ i, i ∈ S → p.word i = Pauli1.Z := by
      intro i hi
      simpa [S] using! hi
    obtain ⟨l, hmem, hprod⟩ := exists_zproduct n S p.word hSout hSin
    have hp_eq : p = (⟨p.word, 0⟩ : PauliElem n) := by
      apply pauli_ext
      · rfl
      · exact hphase
    rw [hp_eq]
    refine ⟨l, ?_, hprod⟩
    intro g hg
    obtain ⟨i, rfl⟩ := hmem g hg
    rw [tableauGenerators]
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, standardStabilizer_decode n i⟩
  · intro hp
    obtain ⟨l, hl, rfl⟩ := hp
    refine foldl_mul_fixes_ketZero l ?_ 1 ?_
    · intro g hg
      have hg' := hl g hg
      rw [tableauGenerators, List.mem_map] at hg'
      obtain ⟨i, -, hi⟩ := hg'
      exact ⟨i, hi.symm.trans (standardStabilizer_decode n i)⟩
    · rw [op_one, Matrix.one_mulVec]

/-- The zero-phase Pauli element applying Z exactly at the qubits selected by the Boolean mask. -/
def zMaskPauli {n : ℕ} (φ : Fin n → Bool) : PauliElem n :=
  ⟨fun i => if φ i then Pauli1.Z else Pauli1.I, 0⟩

/-- Every masked product of Z operators fixes the all-zero state. -/
theorem zMaskPauli_fixes {n : ℕ} (φ : Fin n → Bool) :
    op (zMaskPauli φ) *ᵥ KetZero n = KetZero n := by
  have h := op_ZI_stabilizes_ket_zero (n := n)
    (fun i => if φ i then Pauli1.Z else Pauli1.I) (by
      intro k
      by_cases hk : φ k <;> simp [hk])
  simpa [zMaskPauli, KetZero] using! h

/-- Exactly `2 ^ n` Pauli elements fix the all-zero state [AaronsonGottesman2004]. -/
theorem stabilizerCount_ketZero (n : ℕ) :
    StabilizerCountEq (KetZero n) (2 ^ n) := by
  unfold StabilizerCountEq
  let ofPauli : {p : PauliElem n // op p *ᵥ KetZero n = KetZero n} → (Fin n → Bool) :=
    fun p i => decide (p.val.word i = Pauli1.Z)
  let toPauli : (Fin n → Bool) →
      {p : PauliElem n // op p *ᵥ KetZero n = KetZero n} :=
    fun φ => ⟨zMaskPauli φ, zMaskPauli_fixes φ⟩
  have hleft : Function.LeftInverse toPauli ofPauli := by
    intro p
    apply Subtype.ext
    obtain ⟨hword, hphase⟩ := fixes_ketZero_data p.property
    apply pauli_ext
    · funext k
      dsimp only [toPauli, ofPauli, zMaskPauli]
      rcases hword k with h | h <;> simp [h]
    · dsimp only [toPauli, ofPauli, zMaskPauli]
      exact hphase.symm
  have hright : Function.RightInverse toPauli ofPauli := by
    intro φ
    funext i
    dsimp only [ofPauli, toPauli, zMaskPauli]
    by_cases h : φ i <;> simp [h]
  let e : {p : PauliElem n // op p *ᵥ KetZero n = KetZero n} ≃ (Fin n → Bool) :=
    Equiv.ofBijective ofPauli ⟨hleft.injective, hright.surjective⟩
  rw [Nat.card_congr e, Nat.card_fun]
  simp [Nat.card_eq_fintype_card]

end Qatlib.Papers.StabilizerSim04.MainResults
