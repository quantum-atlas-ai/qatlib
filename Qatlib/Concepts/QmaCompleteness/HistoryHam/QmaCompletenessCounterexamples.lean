/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.QmaCompletenessDefs
import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false

open Matrix
open scoped BigOperators

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QmaCompleteness.HistoryHam

theorem natToBits_add_pow (len v : ℕ) : natToBits len (v + 2 ^ len) = natToBits len v := by
  have key : ∀ i < len, decide ((v + 2 ^ len) / 2 ^ i % 2 = 1) = decide (v / 2 ^ i % 2 = 1) := by
    intro i hi
    have hle : i ≤ len := Nat.le_of_lt hi
    have hlt : 0 < 2 ^ i := pow_pos two_pos i
    have hsplit : 2 ^ len = 2 ^ (len - i) * 2 ^ i := by
      rw [← pow_add]
      rw [Nat.sub_add_cancel hle]
    have hdiv : (v + 2 ^ len) / 2 ^ i = v / 2 ^ i + 2 ^ (len - i) := by
      conv_lhs => rw [hsplit]
      rw [Nat.add_mul_div_right _ _ hlt]
    have hk0 : 2 ^ (len - i) % 2 = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, len - i = k + 1 := ⟨len - i - 1, by omega⟩
      rw [hk, pow_succ, Nat.mul_comm, Nat.mul_mod_right]
    have hmod2 : (v / 2 ^ i + 2 ^ (len - i)) % 2 = v / 2 ^ i % 2 := by
      rw [Nat.add_mod, hk0, Nat.add_zero, Nat.mod_mod_of_dvd _ (dvd_refl 2)]
    rw [hdiv, hmod2]
  simp only [natToBits]
  apply List.map_congr_left
  intro i hi
  have hi' : i < len := by simpa [List.mem_range] using hi
  exact key i hi'

theorem intToBits_add_pow (len v : ℕ) :
    intToBits len ((v + 2 ^ len : ℕ) : ℤ) = intToBits len (v : ℤ) := by
  simp only [intToBits]
  have habs : ((v + 2 ^ len : ℕ) : ℤ).natAbs = v + 2 ^ len := Int.natAbs_natCast _
  have habs0 : (v : ℤ).natAbs = v := Int.natAbs_natCast _
  rw [habs, habs0, natToBits_add_pow]
  have h1 : decide (0 ≤ ((v + 2 ^ len : ℕ) : ℤ)) = true := by
    rw [decide_eq_true_eq]
    positivity
  have h2 : decide (0 ≤ ((v : ℕ) : ℤ)) = true := by
    rw [decide_eq_true_eq]
    positivity
  rw [h1, h2]

def clause3T1 : LhTerm 1 where
  wires := []
  re := 0
  im := 0

def clause3T2 : LhTerm 1 where
  wires := []
  re := Matrix.of fun _ _ => (2 ^ 65 : ℤ)
  im := 0

def clause3E1 : LhEncoding where
  qubitCount := 1
  width := 0
  terms := [clause3T1]

def clause3E2 : LhEncoding where
  qubitCount := 1
  width := 0
  terms := [clause3T2]

private theorem clause3_len : (0 + 2 ^ clause3T1.wires.length + 64 : ℕ) = 65 := rfl

private theorem clause3T1_re (p q : Fin 1) : clause3T1.re p q = 0 := rfl

private theorem clause3T2_re (p q : Fin 1) : clause3T2.re p q = (2 ^ 65 : ℤ) := rfl

theorem clause3_term_bits_eq : lhTermToBits 0 clause3T1 = lhTermToBits 0 clause3T2 := by decide

theorem clause3_bits_eq : lhToBits clause3E1 = lhToBits clause3E2 := by decide

private theorem list_mem_singleton_eq {α : Type} (a b : α) (h : a ∈ ([b] : List α)) :
    a = b := by
  cases h with
  | head => rfl
  | tail _ hh => cases hh

theorem clause3E1_local : lhLocal 3 clause3E1 := by
  intro t ht
  have hmem : t = clause3T1 := list_mem_singleton_eq t clause3T1 ht
  subst hmem
  show clause3T1.wires.length ≤ 3
  decide

theorem clause3E2_local : lhLocal 3 clause3E2 := by
  intro t ht
  have hmem : t = clause3T2 := list_mem_singleton_eq t clause3T2 ht
  subst hmem
  show clause3T2.wires.length ≤ 3
  decide

theorem clause3E1_herm : lhHermitian clause3E1 := by
  intro t ht p q
  have hmem : t = clause3T1 := list_mem_singleton_eq t clause3T1 ht
  subst hmem
  show (0 : ℤ) = 0 ∧ (0 : ℤ) = -(0 : ℤ)
  simp

theorem clause3E2_herm : lhHermitian clause3E2 := by
  intro t ht p q
  have hmem : t = clause3T2 := list_mem_singleton_eq t clause3T2 ht
  subst hmem
  show ((2 ^ 65 : ℤ)) = (2 ^ 65 : ℤ) ∧ (0 : ℤ) = -(0 : ℤ)
  simp

theorem clause3E1_ham_zero : lhHamiltonian clause3E1 = 0 := by
  show lhEmbedTerm 0 clause3T1 + 0 = 0
  have hz : lhEmbedTerm 0 clause3T1 = 0 := by
    ext x y
    simp only [lhEmbedTerm, Matrix.of_apply, Matrix.zero_apply]
    by_cases h : lhAgreeOutside clause3T1.wires x y
    · rw [if_pos h]
      show (((0 : ℤ) : ℂ) + Complex.I * ((0 : ℤ) : ℂ)) / (2 ^ 0 : ℂ) = 0
      norm_num
    · rw [if_neg h]
  rw [hz]
  simp

theorem clause3E1_yes : LhYesInst clause3E1 0 := by
  refine ⟨Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1), normalized_ket _, ?_⟩
  rw [clause3E1_ham_zero]
  show qmaEnergy (0 : Matrix (Reg 1) (Reg 1) ℂ)
      (Qatlib.Foundations.PureStateMath.Ket (ZeroStr 1)) ≤ 0
  unfold qmaEnergy
  simp [Qatlib.Foundations.PureStateMath.Inner]

private theorem lhAgreeOutside_nil {N : ℕ} (x y : Reg N) :
    lhAgreeOutside ([] : List (Fin N)) x y = true ↔ x = y := by
  have hall : lhAgreeOutside ([] : List (Fin N)) x y
      = (List.finRange N).all (fun j => ([] : List (Fin N)).contains j || (x j == y j)) := rfl
  rw [hall]
  constructor
  · intro h
    have hxy : ∀ j : Fin N, x j = y j := by
      intro j
      have hj := List.all_eq_true.mp h j (List.mem_finRange j)
      simp at hj
      exact hj
    funext j
    exact hxy j
  · intro h
    subst h
    apply List.all_eq_true.mpr
    intro j _
    simp

theorem clause3E2_ham : lhHamiltonian clause3E2 = ((2 ^ 65 : ℂ) • (1 : Matrix (Reg 1) (Reg 1) ℂ)) := by
  show lhEmbedTerm 0 clause3T2 + 0 = _
  have hz : lhEmbedTerm 0 clause3T2 = ((2 ^ 65 : ℂ) • (1 : Matrix (Reg 1) (Reg 1) ℂ)) := by
    ext x y
    simp only [lhEmbedTerm, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
    have hval : ∀ p q : Fin 1,
        lhValueMatrix 0 clause3T2.re clause3T2.im p q = (2 ^ 65 : ℂ) := by
      intro p q
      show (((2 ^ 65 : ℤ) : ℂ) + Complex.I * ((0 : ℤ) : ℂ)) / (2 ^ 0 : ℂ) = (2 ^ 65 : ℂ)
      norm_num
    by_cases h : x = y
    · subst h
      have htrue : lhAgreeOutside clause3T2.wires x x = true := (lhAgreeOutside_nil x x).mpr rfl
      rw [if_pos htrue, if_pos rfl]
      simp [hval]
    · have hfalse : ¬(lhAgreeOutside clause3T2.wires x y = true) :=
        fun hh => h ((lhAgreeOutside_nil x y).mp hh)
      rw [if_neg hfalse, if_neg h]
      simp
  rw [hz]
  simp

private theorem energy_smul_one {I : Type} [Fintype I] [DecidableEq I] (c : ℂ) (ζ : QState I) :
    qmaEnergy (c • (1 : Matrix I I ℂ)) ζ = (c * Qatlib.Foundations.PureStateMath.Inner ζ ζ).re := by
  unfold qmaEnergy
  have hmul : ((c • (1 : Matrix I I ℂ)) *ᵥ ζ) = (c • ζ) := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hmul]
  have hinner : Qatlib.Foundations.PureStateMath.Inner ζ (c • ζ) = c * Qatlib.Foundations.PureStateMath.Inner ζ ζ := by
    rw [inner_apply]
    have hs : ∀ i, (c • ζ) i = c * ζ i := fun i => by simp
    conv_lhs => simp only [hs]
    have hp : ∀ i, (starRingEnd ℂ) (ζ i) * (c * ζ i) = c * ((starRingEnd ℂ) (ζ i) * ζ i) :=
      fun i => by ring
    conv_lhs => simp only [hp]
    rw [← Finset.mul_sum, ← inner_apply]
  rw [hinner]

theorem clause3E2_no : LhNoInst clause3E2 (1 / (2 ^ 20 * (clause3E2.qubitCount + 1) ^ 4)) := by
  intro η hη
  have henergy : qmaEnergy (lhHamiltonian clause3E2) η = (((2 ^ 65 : ℂ)) * Qatlib.Foundations.PureStateMath.Inner η η).re := by
    rw [clause3E2_ham]
    exact energy_smul_one (2 ^ 65 : ℂ) η
  rw [henergy, (normalized_iff_inner_self η).mp hη, mul_one]
  conv_lhs => rw [show clause3E2.qubitCount = 1 from rfl]
  norm_num

theorem clause3_overlap : LhYesBits 3 (lhToBits clause3E1) ∧ LhNoBits 3 (lhToBits clause3E1) := by
  refine ⟨⟨clause3E1, rfl, clause3E1_local, clause3E1_herm, clause3E1_yes⟩,
      ⟨clause3E2, ?_, clause3E2_local, clause3E2_herm, clause3E2_no⟩⟩
  exact clause3_bits_eq.symm

theorem clause3_counter_clause1 : ¬ InPromiseQMA (LhYesBits 3) (LhNoBits 3) := by
  intro h
  obtain ⟨V, hyes, hno⟩ := h
  obtain ⟨h1, h2⟩ := clause3_overlap
  obtain ⟨ψ, hnorm, hacc⟩ := hyes _ h1
  have hacc' := hno _ h2 ψ hnorm
  have : (2 : ℝ) / 3 ≤ 1 / 3 := le_trans hacc hacc'
  norm_num at this

theorem clause3_clause2 :
    ∀ (Lyes Lno : List Bool → Prop), InPromiseQMA Lyes Lno →
      ∃ (red : List Bool → LhEncoding) (c : ℕ),
        (∀ x : List Bool, lhLocal 3 (red x) ∧ lhHermitian (red x)) ∧
        (∀ x : List Bool, (red x).terms.length ≤ c * (x.length + 1) ^ c + c) ∧
        (∀ x : List Bool, (red x).width ≤ c * (x.length + 1) ^ c + c) ∧
        (∀ x : List Bool, Lyes x → LhYesBits 3 (lhToBits (red x))) ∧
        (∀ x : List Bool, Lno x → LhNoBits 3 (lhToBits (red x))) := by
  intro Lyes Lno hQMA
  have hdisj : ∀ x : List Bool, Lyes x → ¬ Lno x := by
    intro x hy hn
    obtain ⟨V, hyes, hno⟩ := hQMA
    obtain ⟨ψ, hnorm, hacc⟩ := hyes x hy
    have hacc' := hno x hn ψ hnorm
    have : (2 : ℝ) / 3 ≤ 1 / 3 := le_trans hacc hacc'
    norm_num at this
  classical
  refine ⟨fun x => if Lyes x then clause3E1 else clause3E2, 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    beta_reduce
    by_cases h : Lyes x
    · rw [if_pos h]; exact ⟨clause3E1_local, clause3E1_herm⟩
    · rw [if_neg h]; exact ⟨clause3E2_local, clause3E2_herm⟩
  · intro x
    beta_reduce
    by_cases h : Lyes x
    · rw [if_pos h]; show (clause3E1.terms).length ≤ 1 * (x.length + 1) ^ 1 + 1
      simp only [clause3E1, List.length_cons, List.length_nil, pow_one, Nat.one_mul]
      omega
    · rw [if_neg h]; show (clause3E2.terms).length ≤ 1 * (x.length + 1) ^ 1 + 1
      simp only [clause3E2, List.length_cons, List.length_nil, pow_one, Nat.one_mul]
      omega
  · intro x
    beta_reduce
    by_cases h : Lyes x
    · rw [if_pos h]; show (clause3E1).width ≤ 1 * (x.length + 1) ^ 1 + 1
      simp only [clause3E1, pow_one, Nat.one_mul]
      omega
    · rw [if_neg h]; show (clause3E2).width ≤ 1 * (x.length + 1) ^ 1 + 1
      simp only [clause3E2, pow_one, Nat.one_mul]
      omega
  · intro x hx
    beta_reduce
    have h : Lyes x := hx
    rw [if_pos h]
    exact ⟨clause3E1, rfl, clause3E1_local, clause3E1_herm, clause3E1_yes⟩
  · intro x hx
    beta_reduce
    have hne : ¬ Lyes x := fun hh => hdisj x hh hx
    rw [if_neg hne]
    exact ⟨clause3E2, rfl, clause3E2_local, clause3E2_herm, clause3E2_no⟩

theorem clause3_counter : ¬
    (InPromiseQMA (LhYesBits 3) (LhNoBits 3)
    ∧ (∀ (Lyes Lno : List Bool → Prop), InPromiseQMA Lyes Lno →
        ∃ (red : List Bool → LhEncoding) (c : ℕ),
          (∀ x : List Bool, lhLocal 3 (red x) ∧ lhHermitian (red x)) ∧
          (∀ x : List Bool, (red x).terms.length ≤ c * (x.length + 1) ^ c + c) ∧
          (∀ x : List Bool, (red x).width ≤ c * (x.length + 1) ^ c + c) ∧
          (∀ x : List Bool, Lyes x → LhYesBits 3 (lhToBits (red x))) ∧
          (∀ x : List Bool, Lno x → LhNoBits 3 (lhToBits (red x))))) := by
  intro h
  exact clause3_counter_clause1 h.1
end Qatlib.Concepts.QmaCompleteness.HistoryHam
