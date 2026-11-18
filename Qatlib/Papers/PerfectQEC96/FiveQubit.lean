/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerCoreDefs
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDefs
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerDimension
public import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerRun
public import Qatlib.Concepts.ErrorCorrection.ErrorClasses.Stabilizer
public import Qatlib.Concepts.ErrorCorrection.Recovery.Stabilizer
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section

/-!
# The five-qubit code as a non-CSS stabilizer consumer

The four cyclic generators of the perfect five-qubit code, given as a signed
tableau, satisfy the shared stabilizer-component contracts: consistency,
code-space dimension `2 ^ (5 - 4)`, absence of negative identity in the
generated subgroup, exact stabilizer distance three, and recovery of every
signed single-qubit Pauli error as a pure-state outer product.

## References

* [Laflamme, Miquel, Paz and Zurek, 1996][LaflammeMiquelPazZurek1996],
  fixed version `quant-ph/9602019v1`. The cyclic stabilizer presentation models
  the perfect five-qubit code rather than the original encoder circuit.
-/

namespace Qatlib.Papers.PerfectQEC96

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Concepts.ErrorCorrection.Recovery
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open scoped Matrix

/-- The four cyclic generator rows of the five-qubit code, with phase zero. -/
def fiveRow : Fin 4 → Row 5
  | 0 => ⟨![true, false, false, true, false], ![false, true, true, false, false], 0⟩
  | 1 => ⟨![false, true, false, false, true], ![false, false, true, true, false], 0⟩
  | 2 => ⟨![true, false, true, false, false], ![false, false, false, true, true], 0⟩
  | _ => ⟨![false, true, false, true, false], ![true, false, false, false, true], 0⟩

/-- The five-qubit stabilizer tableau with four independent rows. -/
def fiveTab : Tableau 5 4 := fiveRow

/-- The decoded generator Pauli elements of the five-qubit code. -/
def fiveGens : Fin 4 → PauliElem 5 := fun i => (fiveTab i).decode

/-- The generator rows decode to Hermitian, mutually commuting Paulis. -/
theorem five_cons : ConsistentTableau fiveTab := by
  constructor
  · intro a
    simp only [IsHermitianPauli]
    fin_cases a <;> decide
  · intro a b
    rw [op_commute_iff, pauliCommute]
    fin_cases a <;> fin_cases b <;> decide

/-- The generator symplectic vectors are linearly independent over `ZMod 2`. -/
theorem five_indep : LinearIndependent (ZMod 2) (rowSympVec fiveTab) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsnd (j : Fin 5) : ∑ i, g i * (rowSympVec fiveTab i).2 j = 0 := by
    have h1 : (∑ i, g i • rowSympVec fiveTab i).2 j = (0 : BooleanVec 5 × BooleanVec 5).2 j := by
      rw [hg]
    simp only [Prod.smul_def] at h1
    exact h1
  have hfst (j : Fin 5) : ∑ i, g i * (rowSympVec fiveTab i).1 j = 0 := by
    have h1 : (∑ i, g i • rowSympVec fiveTab i).1 j = (0 : BooleanVec 5 × BooleanVec 5).1 j := by
      rw [hg]
    simp only [Prod.smul_def] at h1
    exact h1
  have bits : ∀ i : Fin 4,
      ((rowSympVec fiveTab i).2 (1 : Fin 5), (rowSympVec fiveTab i).1 (4 : Fin 5),
       (rowSympVec fiveTab i).1 (2 : Fin 5), (rowSympVec fiveTab i).2 (0 : Fin 5)) =
      match i with
      | 0 => (1, 0, 0, 0)
      | 1 => (0, 1, 0, 0)
      | 2 => (0, 0, 1, 0)
      | _ => (0, 0, 0, 1) := by
    intro i
    fin_cases i <;> rfl
  have hg0 : g 0 = 0 := by
    have h := hsnd 1
    have hb0 : (rowSympVec fiveTab 0).2 1 = 1 := by rfl
    have hb1 : (rowSympVec fiveTab 1).2 1 = 0 := by rfl
    have hb2 : (rowSympVec fiveTab 2).2 1 = 0 := by rfl
    have hb3 : (rowSympVec fiveTab 3).2 1 = 0 := by rfl
    simpa [Fin.sum_univ_four, hb0, hb1, hb2, hb3] using h
  have hg1 : g 1 = 0 := by
    have h := hfst 4
    have hb0 : (rowSympVec fiveTab 0).1 4 = 0 := by rfl
    have hb1 : (rowSympVec fiveTab 1).1 4 = 1 := by rfl
    have hb2 : (rowSympVec fiveTab 2).1 4 = 0 := by rfl
    have hb3 : (rowSympVec fiveTab 3).1 4 = 0 := by rfl
    simpa [Fin.sum_univ_four, hb0, hb1, hb2, hb3] using h
  have hg2 : g 2 = 0 := by
    have h := hfst 2
    have hb0 : (rowSympVec fiveTab 0).1 2 = 0 := by rfl
    have hb1 : (rowSympVec fiveTab 1).1 2 = 0 := by rfl
    have hb2 : (rowSympVec fiveTab 2).1 2 = 1 := by rfl
    have hb3 : (rowSympVec fiveTab 3).1 2 = 0 := by rfl
    simpa [Fin.sum_univ_four, hb0, hb1, hb2, hb3] using h
  have hg3 : g 3 = 0 := by
    have h := hsnd 0
    have hb0 : (rowSympVec fiveTab 0).2 0 = 0 := by rfl
    have hb1 : (rowSympVec fiveTab 1).2 0 = 0 := by rfl
    have hb2 : (rowSympVec fiveTab 2).2 0 = 0 := by rfl
    have hb3 : (rowSympVec fiveTab 3).2 0 = 1 := by rfl
    simpa [Fin.sum_univ_four, hb0, hb1, hb2, hb3] using h
  intro i
  fin_cases i <;> simp [hg0, hg1, hg2, hg3]

/-- The five-qubit code space has dimension exactly two. -/
theorem five_dim : Module.finrank ℂ (codeSpace fiveTab) = 2 ^ (5 - 4) :=
  finrank_codeSpace_of_independent fiveTab five_cons
    (independent_of_row_linearIndependent fiveTab five_indep)

/-- The generated subgroup of the five-qubit code excludes negative identity. -/
theorem five_minusI : ¬ (minusI 5 ∈ generatedSubgroup (tableauGenerators fiveTab)) := by
  intro h
  have hd := five_dim
  rw [codeSpace_eq_bot_of_generated_minusI fiveTab h, finrank_bot] at hd
  norm_num at hd

/-- The first components of a finite sum are the sum of first components. -/
theorem sum_fst {n k : ℕ} (f : Fin k → BooleanVec n × BooleanVec n) :
    (∑ i, f i).1 = ∑ i, (f i).1 := by
  exact map_sum (show (BooleanVec n × BooleanVec n) →+ BooleanVec n from
    ⟨⟨fun p => p.1, by rfl⟩, by intro x y; rfl⟩) f Finset.univ

/-- The second components of a finite sum are the sum of second components. -/
theorem sum_snd {n k : ℕ} (f : Fin k → BooleanVec n × BooleanVec n) :
    (∑ i, f i).2 = ∑ i, (f i).2 := by
  exact map_sum (show (BooleanVec n × BooleanVec n) →+ BooleanVec n from
    ⟨⟨fun p => p.2, by rfl⟩, by intro x y; rfl⟩) f Finset.univ

/-- Pointwise evaluation distributes over finite sums. -/
theorem sum_pi {n k : ℕ} (f : Fin k → BooleanVec n) (j : Fin n) :
    (∑ i, f i) j = ∑ i, f i j := by
  exact map_sum (show (BooleanVec n) →+ (ZMod 2) from
    ⟨⟨fun g => g j, by rfl⟩, by intro x y; rfl⟩) f Finset.univ

/-- Pair sums match componentwise sums. -/
theorem pairSum_iff {n k : ℕ} (a b : Fin k → BooleanVec n) (c : Fin k → ZMod 2)
    (u w : BooleanVec n) :
    (∑ i, c i • (a i, b i) = (u, w)) ↔
      ((∀ j, ∑ i, c i * a i j = u j) ∧ (∀ j, ∑ i, c i * b i j = w j)) := by
  constructor
  · intro h
    constructor
    · intro j
      have hj0 : (∑ i, c i • (a i, b i)).1 j = (u, w).1 j := by rw [h]
      simpa only [sum_fst, sum_pi, Prod.smul_def, Pi.smul_apply,
        smul_eq_mul] using hj0
    · intro j
      have hj0 : (∑ i, c i • (a i, b i)).2 j = (u, w).2 j := by rw [h]
      simpa only [sum_snd, sum_pi, Prod.smul_def, Pi.smul_apply,
        smul_eq_mul] using hj0
  · rintro ⟨hx, hz⟩
    apply Prod.ext
    · funext j
      have hj0 : (∑ i, c i • (a i, b i)).1 j = (u, w).1 j := by
        simpa only [sum_fst, sum_pi, Prod.smul_def, Pi.smul_apply,
          smul_eq_mul] using hx j
      simpa using hj0
    · funext j
      have hj0 : (∑ i, c i • (a i, b i)).2 j = (u, w).2 j := by
        simpa only [sum_snd, sum_pi, Prod.smul_def, Pi.smul_apply,
          smul_eq_mul] using hz j
      simpa using hj0

set_option maxRecDepth 16384 in
/-- Every zero-syndrome vector of weight below three lies in the span. -/
theorem five_lower : ∀ v : BooleanVec 5 × BooleanVec 5,
    genSyn fiveGens v = 0 → sympWt v < 3 →
    ∃ c : Fin 4 → ZMod 2,
      ((∀ j, ∑ i, c i * symplecticX (fiveGens i).word j = v.1 j) ∧
        (∀ j, ∑ i, c i * symplecticZ (fiveGens i).word j = v.2 j)) := by
  decide

/-- The weight-three logical representative with zero syndrome. -/
def fiveWit : BooleanVec 5 × BooleanVec 5 := (![0, 1, 1, 0, 1], ![0, 1, 1, 0, 0])

/-- The logical representative has zero syndrome against all generators. -/
theorem fiveWit_syn : genSyn fiveGens fiveWit = 0 := by decide

/-- The logical representative is outside the generator span. -/
theorem fiveWit_not : fiveWit ∉ sympSpan fiveGens := by
  rw [mem_sympSpan_iff]
  decide

/-- The logical representative has symplectic weight exactly three. -/
theorem fiveWit_wt : sympWt fiveWit = 3 := by decide

/-- The five-qubit stabilizer distance is exactly three. -/
theorem five_dist : stabDist fiveGens = (3 : ℕ∞) := by
  refine le_antisymm ?_ ((stab_dist_ge_iff fiveGens 3).mpr ?_)
  · have h := stab_dist_le fiveGens fiveWit_syn fiveWit_not
    rw [fiveWit_wt] at h
    exact h
  · intro v hs hw
    obtain ⟨c, hx, hz⟩ := five_lower v hs hw
    refine mem_sympSpan_iff fiveGens v |>.mpr ⟨c, ?_⟩
    have hsum := (pairSum_iff (fun i => symplecticX (fiveGens i).word)
      (fun i => symplecticZ (fiveGens i).word) c v.1 v.2).mpr ⟨hx, hz⟩
    exact hsum.trans (Prod.eta v).symm

/-- The single-site X error label at `j`. -/
def fiveX (j : Fin 5) : BooleanVec 5 × BooleanVec 5 :=
  (Pi.single j (1 : ZMod 2), 0)

/-- The single-site Z error label at `j`. -/
def fiveZ (j : Fin 5) : BooleanVec 5 × BooleanVec 5 :=
  (0, Pi.single j (1 : ZMod 2))

/-- The single-site combined X/Z error label at `j`. -/
def fiveY (j : Fin 5) : BooleanVec 5 × BooleanVec 5 :=
  (Pi.single j (1 : ZMod 2), Pi.single j (1 : ZMod 2))

/-- The zero and fifteen nonidentity weight-at-most-one error labels. -/
def fiveErrs : List (BooleanVec 5 × BooleanVec 5) :=
  0 :: (List.finRange 5).flatMap (fun j => [fiveX j, fiveZ j, fiveY j])

/-- The perfect-code lookup decoder, defaulting to the zero label. -/
def fiveCorr (s : Fin 4 → ZMod 2) : BooleanVec 5 × BooleanVec 5 :=
  (fiveErrs.find? (fun v => decide (tabSyn fiveTab v = s))).getD 0

/-- The concrete five-qubit recovery program. -/
def fiveProg : StabProg fiveTab := ⟨fiveCorr⟩

set_option maxRecDepth 16384 in
/-- The lookup decoder returns exactly every input error of weight at most one. -/
theorem five_decode (v : BooleanVec 5 × BooleanVec 5) (hv : sympWt v ≤ 1) :
    fiveCorr (tabSyn fiveTab v) = v := by
  revert v
  decide

/-- Every weight-at-most-one error has zero, hence stabilizer, residual. -/
theorem five_res (v : BooleanVec 5 × BooleanVec 5) (hv : sympWt v ≤ 1) :
    stabRes fiveProg v ∈ sympSpan fiveGens := by
  change fiveCorr (tabSyn fiveTab v) + v ∈ sympSpan fiveGens
  rw [five_decode v hv]
  have hz : v + v = 0 := by
    apply Prod.ext <;> funext j <;> exact CharTwo.add_self_eq_zero _
  rw [hz]
  exact Submodule.zero_mem _

/-- Every binary single-error label is recovered as a pure-state density. -/
theorem five_rec_label (v : BooleanVec 5 × BooleanVec 5) (hv : sympWt v ≤ 1)
    (ψ : QState (Reg 5)) (hψ : ψ ∈ codeSpace fiveTab) :
    stabRecCh fiveTab fiveProg (outerProduct (op (labelPauli v) *ᵥ ψ)) = outerProduct ψ :=
  stab_recovers fiveTab five_cons
    (independent_of_row_linearIndependent fiveTab five_indep)
    fiveProg v (five_res v hv) ψ hψ

/-- Every signed single-qubit Pauli error, including X, Y and Z, is recovered
as a pure-state density; no arbitrary-noise or dynamic-circuit claim is made. -/
theorem five_recovers (e : PauliElem 5) (he : pauliWt e ≤ 1)
    (ψ : QState (Reg 5)) (hψ : ψ ∈ codeSpace fiveTab) :
    stabRecCh fiveTab fiveProg (outerProduct (op e *ᵥ ψ)) = outerProduct ψ := by
  have hv : sympWt (symplecticVec e.word) ≤ 1 := by
    change sympWt (symplecticX e.word, symplecticZ e.word) ≤ 1
    rw [← pauliWt_symp e]
    exact he
  exact stab_rec_signed fiveTab five_cons
    (independent_of_row_linearIndependent fiveTab five_indep)
    fiveProg e (five_res (symplecticVec e.word) hv) ψ hψ

/-- The exact five-qubit parameters: nontrivial code space and distance three. -/
theorem five_params : Module.finrank ℂ (codeSpace fiveTab) = 2
    ∧ stabDist fiveGens = (3 : ℕ∞) ∧ ¬ (minusI 5 ∈ generatedSubgroup (tableauGenerators fiveTab)) := by
  rw [five_dim]
  exact ⟨by norm_num, five_dist, five_minusI⟩

end Qatlib.Papers.PerfectQEC96
