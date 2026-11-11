/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedSamplingLaw

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Without Replacement Support

Without Replacement Support constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Construction for without Replacement Constant in the without replacement support model. -/
def withoutReplacementConstant : ℕ → ℕ → ℝ
  | _, 0 => 1
  | M, n+1 => withoutReplacementConstant (M-1) n/(M : ℝ)

omit [Fintype S] in
/-- Complete original `without_replacement_mass_valid_eq_constant` guarantee for `WithoutReplacementSupport`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mass_valid_eq_constant
    (R : Finset S) (n : ℕ) (hn : n ≤ R.card) (ω : Fin n → S)
    (hmem : ∀ i, ω i ∈ R) (hinj : Function.Injective ω) :
    withoutReplacementMass R n ω = withoutReplacementConstant R.card n := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    have hhead : ω 0 ∈ R := hmem 0
    have htailmem : ∀ i : Fin n, ω i.succ ∈ R.erase (ω 0) := by
      intro i
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        exact (Fin.succ_ne_zero i) (hinj heq)
      · exact hmem i.succ
    have htailinj : Function.Injective (fun i : Fin n => ω i.succ) := by
      intro i j h
      exact Fin.succ_injective n (hinj h)
    have htailcard : n ≤ (R.erase (ω 0)).card := by
      rw [Finset.card_erase_of_mem hhead]
      omega
    rw [withoutReplacementMass, ite_eq_left hhead, ih (R.erase (ω 0)) htailcard
      (fun i => ω i.succ) htailmem htailinj]
    rw [Finset.card_erase_of_mem hhead]
    rw [withoutReplacementConstant]


omit [Fintype S] in
/-- Complete original `without_replacement_mass_pos_mem` guarantee for `WithoutReplacementSupport`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mass_pos_mem
    (R : Finset S) (n : ℕ) (ω : Fin n → S)
    (hpos : 0 < withoutReplacementMass R n ω) :
    ∀ i, ω i ∈ R := by
  induction n generalizing R with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    by_cases hi : i=0
    · subst i
      by_contra hx
      simp [withoutReplacementMass, hx] at hpos
    · have hhead : ω 0 ∈ R := by
        by_contra hx
        simp [withoutReplacementMass, hx] at hpos
      have htail : 0 < withoutReplacementMass (R.erase (ω 0)) n (fun j => ω j.succ) := by
        have hdiv : 0 < withoutReplacementMass (R.erase (ω 0)) n (fun j => ω j.succ) /
            (R.card : ℝ) := by
          simpa [withoutReplacementMass, hhead] using hpos
        have hden : (0 : ℝ) < R.card := by
          exact_mod_cast (Finset.card_pos.mpr ⟨ω 0,hhead⟩)
        rcases (div_pos_iff.mp hdiv) with hgood | hbad
        · exact hgood.1
        · linarith
      have hs := ih (R.erase (ω 0)) (fun j => ω j.succ) htail
        (i.pred hi)
      have hs' : ω i ∈ R.erase (ω 0) := by simpa using hs
      have hne : ω i ≠ ω 0 := by
        intro heq
        exact (Finset.mem_erase.mp hs').1 heq
      exact (Finset.mem_erase.mp hs').2

omit [Fintype S] in
/-- Complete original `without_replacement_mass_pos_injective` guarantee for `WithoutReplacementSupport`; all source hypotheses and output obligations are retained. -/
theorem without_replacement_mass_pos_injective
    (R : Finset S) (n : ℕ) (ω : Fin n → S)
    (hpos : 0 < withoutReplacementMass R n ω) :
    Function.Injective ω := by
  induction n generalizing R with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have hhead : ω 0 ∈ R := by
      by_contra hx
      simp [withoutReplacementMass, hx] at hpos
    have htail : 0 < withoutReplacementMass (R.erase (ω 0)) n (fun j => ω j.succ) := by
      have hdiv := by simpa [withoutReplacementMass, hhead] using hpos
      have hden : (0 : ℝ) < R.card := by
        exact_mod_cast (Finset.card_pos.mpr ⟨ω 0,hhead⟩)
      rcases (div_pos_iff.mp hdiv) with hgood | hbad
      · exact hgood.1
      · linarith
    have htail_inj := ih (R.erase (ω 0)) (fun j => ω j.succ) htail
    have htail_mem := without_replacement_mass_pos_mem (R.erase (ω 0)) n
      (fun j => ω j.succ) htail
    intro i j hij
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i,rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · rfl
      · have hm := htail_mem j
        exact False.elim ((Finset.mem_erase.mp hm).1 hij.symm)
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
      · have hm := htail_mem i
        exact False.elim ((Finset.mem_erase.mp hm).1 hij)
      · exact congrArg Fin.succ (htail_inj hij)

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_mass_pos_mem
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.without_replacement_mass_pos_injective
