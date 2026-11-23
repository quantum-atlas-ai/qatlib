/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.PauliPath
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Paths

open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

/-!
# A concrete legal-path count for the two-qubit depth-one architecture

For the smallest non-trivial architecture, the sole two-qubit gate pairs the
two wires.  At the two boundary slices, legality permits only `I` and `Z`,
while the gate condition forces the two wires in each slice to have the same
identity status.  Consequently the paths of weight `d + 1 = 2` are exactly
the two transitions `II → ZZ` and `ZZ → II`.  This concrete count records the
boundary convention used by the formal model, which must be reconciled with
the source paper's separate fixed-terminal path count before that count is
promoted as a general theorem.
-/

/-- The unique two-qubit gate pairs wire `0` with wire `1`. -/
def twoQubitDepthOneArchitecture : Architecture 2 1 where
  mate := fun _ => ![1, 0]
  mate_invol := by
    intro i q
    fin_cases q <;> rfl
  mate_ne := by
    intro i q
    fin_cases q <;> decide

/-- The two possible weight-two boundary transitions. -/
def initialIdentityFinalZ : PauliPath 2 1 :=
  ![![Pauli1.I, Pauli1.I], ![Pauli1.Z, Pauli1.Z]]

/-- The reverse weight-two boundary transition. -/
def initialZFinalIdentity : PauliPath 2 1 :=
  ![![Pauli1.Z, Pauli1.Z], ![Pauli1.I, Pauli1.I]]

/-- `pairLegal` does not depend on the order of the two wires. -/
lemma pairLegal_comm {a b : Pauli1} (h : pairLegal a b) : pairLegal b a := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨hb, ha⟩
  · exact Or.inr ⟨hb, ha⟩

/-- The all-identity two-qubit slice has Hamming weight zero. -/
lemma sliceWeight_identityPair : sliceWeight ![Pauli1.I, Pauli1.I] = 0 := by
  unfold sliceWeight
  have hfilter :
      (Finset.univ.filter fun q : Fin 2 => ![Pauli1.I, Pauli1.I] q ≠ Pauli1.I) = ∅ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases q <;> simp
  rw [hfilter]
  exact Finset.card_empty

/-- The two-qubit slice `ZZ` has Hamming weight two. -/
lemma sliceWeight_zPair : sliceWeight ![Pauli1.Z, Pauli1.Z] = 2 := by
  unfold sliceWeight
  have hfilter :
      (Finset.univ.filter fun q : Fin 2 => ![Pauli1.Z, Pauli1.Z] q ≠ Pauli1.I) = Finset.univ := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    fin_cases q <;> simp
  rw [hfilter, Finset.card_univ, Fintype.card_fin]

/-- A depth-one Pauli path has weight equal to the sum of its two slice weights. -/
lemma pathWeight_twoSlices (s : PauliPath 2 1) :
    pathWeight s = sliceWeight (s 0) + sliceWeight (s 1) := by
  simp [pathWeight, Fin.sum_univ_two]

/-- A two-qubit slice is an `I`/`Z` boundary and a legal gate pair exactly when it is `II` or `ZZ`. -/
lemma boundary_pair_iff (p : Pauli 2) :
    boundaryLegal p ∧ pairLegal (p 0) (p 1) ↔
      p = ![Pauli1.I, Pauli1.I] ∨ p = ![Pauli1.Z, Pauli1.Z] := by
  constructor
  · intro ⟨hb, hp⟩
    rcases hb 0 with h0 | h0 <;> rcases hb 1 with h1 | h1
    · left
      ext q
      fin_cases q <;> simp [h0, h1]
    · exfalso
      rw [h0, h1] at hp
      rcases hp with ⟨_, hz⟩ | ⟨hi, _⟩
      · cases hz
      · exact hi rfl
    · exfalso
      rw [h0, h1] at hp
      rcases hp with ⟨hz, _⟩ | ⟨_, hi⟩
      · cases hz
      · exact hi rfl
    · right
      ext q
      fin_cases q <;> simp [h0, h1]
  · intro hp
    rcases hp with hp | hp <;> rw [hp]
    · constructor
      · intro q
        fin_cases q <;> simp
      · exact Or.inl ⟨rfl, rfl⟩
    · constructor
      · intro q
        fin_cases q <;> simp
      · exact Or.inr ⟨by simp, by simp⟩

/-- Legality for the two-qubit depth-one architecture is the pair condition on each slice
together with the `I`/`Z` boundary condition. -/
lemma isLegal_twoQubit_iff (s : PauliPath 2 1) :
    IsLegal twoQubitDepthOneArchitecture s ↔
      pairLegal (s 0 0) (s 0 1) ∧ pairLegal (s 1 0) (s 1 1) ∧
        boundaryLegal (s 0) ∧ boundaryLegal (s 1) := by
  have hlast : Fin.last 1 = (1 : Fin 2) := by decide
  have hmate0 : twoQubitDepthOneArchitecture.mate 0 0 = 1 := by
    simp [twoQubitDepthOneArchitecture]
  have hmate1 : twoQubitDepthOneArchitecture.mate 0 1 = 0 := by
    simp [twoQubitDepthOneArchitecture]
  constructor
  · rintro ⟨hgate, hb0, hbLast⟩
    have h0 := hgate 0 0
    have h1 := hgate 0 1
    simp only [gateLegal, Fin.castSucc_zero', Fin.succ_zero_eq_one', hmate0, hmate1] at h0 h1
    rw [hlast] at hbLast
    exact ⟨h0.1, h0.2, hb0, hbLast⟩
  · intro ⟨hpIn, hpOut, hb0, hb1⟩
    refine ⟨?_, hb0, ?_⟩
    · intro i q
      fin_cases i
      fin_cases q
      · simp only [gateLegal]
        exact And.intro hpIn hpOut
      · simp only [gateLegal]
        exact And.intro (pairLegal_comm hpIn) (pairLegal_comm hpOut)
    · rw [hlast]
      exact hb1

/-- The exact legal-path count for the two-qubit, one-layer architecture. -/
theorem two_qubit_depth_one_legal_path_count :
    legalPathCount 2 1 twoQubitDepthOneArchitecture 2 = 2 := by
  classical
  unfold legalPathCount
  have hiff : ∀ s : PauliPath 2 1,
      IsLegal twoQubitDepthOneArchitecture s ∧ pathWeight s = 2 ↔
        s = initialIdentityFinalZ ∨ s = initialZFinalIdentity := by
    intro s
    constructor
    · intro ⟨hlegal, hw⟩
      rw [isLegal_twoQubit_iff] at hlegal
      rw [pathWeight_twoSlices] at hw
      rcases hlegal with ⟨hp0, hp1, hb0, hb1⟩
      rcases (boundary_pair_iff (s 0)).mp ⟨hb0, hp0⟩ with hin | hin <;>
        rcases (boundary_pair_iff (s 1)).mp ⟨hb1, hp1⟩ with hout | hout
      · rw [hin, hout, sliceWeight_identityPair] at hw
        norm_num at hw
      · left
        ext i q
        fin_cases i <;> fin_cases q <;> simp [hin, hout, initialIdentityFinalZ]
      · right
        ext i q
        fin_cases i <;> fin_cases q <;> simp [hin, hout, initialZFinalIdentity]
      · rw [hin, hout, sliceWeight_zPair] at hw
        norm_num at hw
    · intro hs
      rcases hs with rfl | rfl
      · have h0 := (boundary_pair_iff ![Pauli1.I, Pauli1.I]).mpr (Or.inl rfl)
        have h1 := (boundary_pair_iff ![Pauli1.Z, Pauli1.Z]).mpr (Or.inr rfl)
        have hs0 : initialIdentityFinalZ 0 = ![Pauli1.I, Pauli1.I] := by
          simp [initialIdentityFinalZ]
        have hs1 : initialIdentityFinalZ 1 = ![Pauli1.Z, Pauli1.Z] := by
          simp [initialIdentityFinalZ]
        refine ⟨?_, ?_⟩
        · rw [isLegal_twoQubit_iff, hs0, hs1]
          exact ⟨h0.2, h1.2, h0.1, h1.1⟩
        · simp [pathWeight_twoSlices, hs0, hs1, sliceWeight_identityPair, sliceWeight_zPair]
      · have h0 := (boundary_pair_iff ![Pauli1.Z, Pauli1.Z]).mpr (Or.inr rfl)
        have h1 := (boundary_pair_iff ![Pauli1.I, Pauli1.I]).mpr (Or.inl rfl)
        have hs0 : initialZFinalIdentity 0 = ![Pauli1.Z, Pauli1.Z] := by
          simp [initialZFinalIdentity]
        have hs1 : initialZFinalIdentity 1 = ![Pauli1.I, Pauli1.I] := by
          simp [initialZFinalIdentity]
        refine ⟨?_, ?_⟩
        · rw [isLegal_twoQubit_iff, hs0, hs1]
          exact ⟨h0.2, h1.2, h0.1, h1.1⟩
        · simp [pathWeight_twoSlices, hs0, hs1, sliceWeight_zPair, sliceWeight_identityPair]
  have hfilter :
      (Finset.univ.filter
        (fun s : PauliPath 2 1 =>
          IsLegal twoQubitDepthOneArchitecture s ∧ pathWeight s = 2)) =
        {initialIdentityFinalZ, initialZFinalIdentity} := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    exact hiff s
  have hne : initialIdentityFinalZ ∉ ({initialZFinalIdentity} : Finset (PauliPath 2 1)) := by
    simp only [Finset.mem_singleton]
    intro h
    have h00 := congr_fun (congr_fun h 0) 0
    simp [initialIdentityFinalZ, initialZFinalIdentity] at h00
  rw [hfilter, Finset.card_insert_of_notMem hne, Finset.card_singleton]

/-- The source Lemma 6 formula needs an additional fixed-terminal convention.

Under the boundary predicate used by `PauliPath`, the two-qubit depth-one
instance has count `2`, whereas the unqualified expression
`n · 2^d · 3^(d-1)` evaluates to `4`.  This theorem prevents silently treating
the two encodings as interchangeable.
-/
theorem source_lemma6_formula_requires_fixed_terminal :
    legalPathCount 2 1 twoQubitDepthOneArchitecture 2 ≠
      2 * 2 ^ 1 * 3 ^ (1 - 1) := by
  rw [two_qubit_depth_one_legal_path_count]
  norm_num

end Qatlib.Papers.NoisyCircuit22.MainResults.Paths
