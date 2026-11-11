/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityRefinedDefs

/-!
# Witness accounting and conditional soundness transfer

Uniform witness families have explicit witness-width and oracle-access ledgers. This module
proves their accounting properties and the real linearity of `acceptProb`, then decomposes
diagonal witness matrices into classical witness densities. The quantum-proof setting is
described in [MarriottWatrous2005].

Classical-witness soundness extends to diagonal witness densities. Transfer to arbitrary witness
densities uses the additional conditions `WcClassicalAcceptFunctional` or
`WcDiagonalAcceptFamily`; the final uniform QCMA-to-QMA statements retain these hypotheses.
Register-width transport is handled by `uniformDensity` and `WcWitnessReindex`.

## Main statements

* `wcQCMA_soundness_transfers_diagonal`: soundness for diagonal witness densities.
* `wcQCMA_soundness_transfers_full`: soundness under a classical diagonal acceptance functional.
* `wcInUniformQCMA_subset_QMA`: quantum-witness membership under the family diagonality
  condition.

## References

* [Marriott and Watrous, 2005][MarriottWatrous2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open scoped Classical BigOperators
open scoped ComplexOrder
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexity
open Qatlib.Concepts.LocalMachine.LocalTransport.WitnessComplexityDefs
open Qatlib
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
open Qatlib.Concepts.LocalMachine.LocalTransport.UniformWitness
open Matrix

/-- Every generated verifier has the witness width specified by its uniform family. -/
theorem wcWitnessLengthLedger (f : UniformWitnessFamily) : WcWitnessLengthLedger f := by
  intro x
  unfold WcWitnessWidth
  exact (f.generatorWidths x).1

/-- The input width of the verifier generated from `x` is exactly the length of `x`. -/
theorem wcInputWidthLedger (f : UniformWitnessFamily) (x : List Bool) :
    (f.generator x).inputBits = x.length := by
  exact (f.generatorWidths x).2

/-- The number of oracle accesses in a generated shared-oracle verifier is bounded by its
instruction count. -/
theorem wcOracleAccessBudget (f : SharedOracleUniformFamily) (x : List Bool) :
    WcOracleAccessBudget f x := by
  exact f.accessBound x

/-- The oracle access count is the length of the generated program's access ledger. -/
theorem wcOracleAccessCount_eq (f : SharedOracleUniformFamily) (x : List Bool) :
    WcOracleAccessCount f x = (oracleAccessLedger (f.generator x)).length := rfl

/-- Uniform BQP membership provides a uniform family with no witness and no oracle instructions. -/
theorem wcBQP_no_witness {L : BitLanguage} (h : InUniformBQP L) :
    ∃ f : UniformWitnessFamily, f.NoWitness ∧ f.OracleFree := by
  obtain ⟨f, hnw, hof, _, _⟩ := h
  exact ⟨f, hnw, hof⟩

/-- For every input length, uniform BQP membership provides a uniform family whose witness width
at that length is zero. -/
theorem wcBQP_witness_width_zero {L : BitLanguage} (h : InUniformBQP L) (n : ℕ) :
    ∃ f : UniformWitnessFamily, f.witnessWidth n = 0 := by
  obtain ⟨f, hnw, hof, _, _⟩ := h
  exact ⟨f, hnw n⟩

/-- Uniform QMA membership provides a verifier family satisfying the witness-length ledger. -/
theorem wcQMA_witness_ledger {L : BitLanguage} (h : InUniformQMA L) :
    ∃ f : UniformWitnessFamily, WcWitnessLengthLedger f := by
  obtain ⟨f, _, _, _⟩ := h
  exact ⟨f, wcWitnessLengthLedger f⟩

/-- Uniform QCMA membership provides a verifier family satisfying the witness-length ledger. -/
theorem wcQCMA_witness_ledger {L : BitLanguage} (h : InUniformQCMA L) :
    ∃ f : UniformWitnessFamily, WcWitnessLengthLedger f := by
  obtain ⟨f, _, _, _⟩ := h
  exact ⟨f, wcWitnessLengthLedger f⟩

/-- The oracle access count of a generated shared-oracle verifier is at most its
instruction-list length. -/
theorem wcRelativeOracleAccessBudget (f : SharedOracleUniformFamily) (x : List Bool) :
    WcOracleAccessCount f x ≤ (f.generator x).instructions.length :=
  f.accessBound x

/-- Acceptance is additive in the witness matrix. -/
theorem wcAcceptProb_add (A : ClassicalOracle) (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (σ₁ σ₂ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    acceptProb A p x (σ₁ + σ₂) = acceptProb A p x σ₁ + acceptProb A p x σ₂ := by
  classical
  have hD : verifierInputDensity p x (σ₁ + σ₂) = verifierInputDensity p x σ₁ + verifierInputDensity p x σ₂ := by
    ext z z'
    by_cases h : inputRestrict p z = x ∧ inputRestrict p z' = x ∧
        ancillaZero p z ∧ ancillaZero p z'
    · simp [verifierInputDensity, h]
    · simp [verifierInputDensity, h]
  have hM : (programMatrix A p * (verifierInputDensity p x σ₁ + verifierInputDensity p x σ₂)
        * (programMatrix A p)ᴴ) = (programMatrix A p * verifierInputDensity p x σ₁
        * (programMatrix A p)ᴴ) + (programMatrix A p * verifierInputDensity p x σ₂
        * (programMatrix A p)ᴴ) := by
    rw [Matrix.mul_add, Matrix.add_mul]
  unfold acceptProb
  calc (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * verifierInputDensity p x (σ₁ + σ₂)
          * (programMatrix A p)ᴴ) z z).re)
      = (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * (verifierInputDensity p x σ₁ + verifierInputDensity p x σ₂)
          * (programMatrix A p)ᴴ) z z).re) := by rw [hD]
    _ = (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * verifierInputDensity p x σ₁ * (programMatrix A p)ᴴ
          + programMatrix A p * verifierInputDensity p x σ₂ * (programMatrix A p)ᴴ) z z).re) := by
          rw [hM]
    _ = (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * verifierInputDensity p x σ₁ * (programMatrix A p)ᴴ) z z).re)
        + (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * verifierInputDensity p x σ₂ * (programMatrix A p)ᴴ) z z).re) := by
          have hz : ∀ z : Reg (programQubits p),
              ((programMatrix A p * verifierInputDensity p x σ₁ * (programMatrix A p)ᴴ
                + programMatrix A p * verifierInputDensity p x σ₂ * (programMatrix A p)ᴴ) z z).re
              = ((programMatrix A p * verifierInputDensity p x σ₁ * (programMatrix A p)ᴴ) z z).re
                + ((programMatrix A p * verifierInputDensity p x σ₂ * (programMatrix A p)ᴴ) z z).re := by
            intro z
            rw [Matrix.add_apply, Complex.add_re]
          rw [Finset.sum_congr rfl (fun z _ => hz z)]
          rw [Finset.sum_add_distrib]

/-- Initializing a diagonal witness matrix equals the sum of initialized classical witness
densities weighted by its complex diagonal entries. -/
theorem wcVerifierInputDensity_classical_decomposition {p : WitnessVerifierProgram}
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hdiag : ∀ w w' : Reg p.witnessBits, w ≠ w' → σ w w' = 0) :
    verifierInputDensity p x σ
      = ∑ w : Reg p.witnessBits, σ w w • verifierInputDensity p x (classicalWitnessDensity w) := by
  classical
  have hdelta : ∀ (g : Reg p.witnessBits → ℂ) (a : Reg p.witnessBits),
      (∑ w : Reg p.witnessBits, g w * (if a = w then (1 : ℂ) else 0)) = g a := by
    intro g a
    have hpoint : ∀ w : Reg p.witnessBits,
        g w * (if a = w then (1 : ℂ) else 0) = (if w = a then g w else 0) := by
      intro w
      by_cases h : a = w
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl (fun w _ => hpoint w)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Reg p.witnessBits)) a (fun w => g w)]
    simp
  have hdelta2 : ∀ (g : Reg p.witnessBits → ℂ) (a b : Reg p.witnessBits),
      (∑ w : Reg p.witnessBits,
        g w * ((if a = w then (1 : ℂ) else 0) * (if b = w then (1 : ℂ) else 0)))
        = if a = b then g a else 0 := by
    intro g a b
    by_cases hab : a = b
    · subst hab
      have hpoint : ∀ w : Reg p.witnessBits,
          g w * ((if a = w then (1 : ℂ) else 0) * (if a = w then (1 : ℂ) else 0))
            = g w * (if a = w then (1 : ℂ) else 0) := by
        intro w
        by_cases h : a = w
        · simp [h]
        · simp [h]
      rw [Finset.sum_congr rfl (fun w _ => hpoint w)]
      rw [hdelta g a]
      simp
    · have hpoint : ∀ w : Reg p.witnessBits,
          g w * ((if a = w then (1 : ℂ) else 0) * (if b = w then (1 : ℂ) else 0)) = 0 := by
        intro w
        by_cases h1 : a = w
        · by_cases h2 : b = w
          · exact absurd (h1.trans h2.symm) hab
          · simp [h1, h2]
        · simp [h1]
      rw [Finset.sum_congr rfl (fun w _ => hpoint w)]
      simp only [Finset.sum_const, if_neg hab]
      simp
  have hket : ∀ (w : Reg p.witnessBits) (i j : Reg p.witnessBits),
      classicalWitnessDensity w i j
        = (if i = w then (1 : ℂ) else 0) * (if j = w then (1 : ℂ) else 0) := by
    intro w i j
    by_cases h1 : i = w <;> by_cases h2 : j = w <;>
      simp [classicalWitnessDensity, outerProduct, Qatlib.Foundations.PureStateMath.Ket, h1,
          h2]
  ext z z'
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases hcond : inputRestrict p z = x ∧ inputRestrict p z' = x ∧
      ancillaZero p z ∧ ancillaZero p z'
  · simp [verifierInputDensity, Matrix.of_apply, hcond]
    have hconv : ∀ w : Reg p.witnessBits,
        σ w w * classicalWitnessDensity w (witnessRestrict p z) (witnessRestrict p z')
          = σ w w * ((if witnessRestrict p z = w then (1 : ℂ) else 0)
            * (if witnessRestrict p z' = w then (1 : ℂ) else 0)) := by
      intro w
      rw [hket]
    rw [Finset.sum_congr rfl (fun w _ => hconv w)]
    have hsum := hdelta2 (fun w => σ w w) (witnessRestrict p z) (witnessRestrict p z')
    rw [hsum]
    by_cases hab : witnessRestrict p z = witnessRestrict p z'
    · rw [if_pos hab, hab]
    · rw [if_neg hab]
      exact hdiag _ _ hab
  · simp [verifierInputDensity, Matrix.of_apply, hcond]

/-- Real scalar multiplication of a witness matrix scales acceptance by the same real factor. -/
theorem wcAcceptProb_smul (A : ClassicalOracle) (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    (c : ℝ) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    acceptProb A p x (c • σ) = c * acceptProb A p x σ := by
  classical
  have hD : verifierInputDensity p x (c • σ) = c • verifierInputDensity p x σ := by
    ext z z'
    by_cases h : inputRestrict p z = x ∧ inputRestrict p z' = x ∧
        ancillaZero p z ∧ ancillaZero p z'
    · simp [verifierInputDensity, Matrix.of_apply, h, Matrix.smul_apply]
    · simp [verifierInputDensity, Matrix.of_apply, h]
  have hM : (programMatrix A p * (c • verifierInputDensity p x σ)
        * (programMatrix A p)ᴴ) = c • (programMatrix A p * verifierInputDensity p x σ
        * (programMatrix A p)ᴴ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hz : ∀ z : Reg (programQubits p),
      ((c • (programMatrix A p * verifierInputDensity p x σ
        * (programMatrix A p)ᴴ)) z z).re
      = c * ((programMatrix A p * verifierInputDensity p x σ
        * (programMatrix A p)ᴴ) z z).re := by
    intro z
    simp [Matrix.smul_apply]
  unfold acceptProb
  calc (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * verifierInputDensity p x (c • σ)
          * (programMatrix A p)ᴴ) z z).re)
      = (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * (c • verifierInputDensity p x σ)
          * (programMatrix A p)ᴴ) z z).re) := by rw [hD]
    _ = (∑ z ∈ programOutputEvent p,
        ((c • (programMatrix A p * verifierInputDensity p x σ
          * (programMatrix A p)ᴴ)) z z).re) := by rw [hM]
    _ = c * (∑ z ∈ programOutputEvent p,
        ((programMatrix A p * verifierInputDensity p x σ
          * (programMatrix A p)ᴴ) z z).re) := by
          rw [Finset.sum_congr rfl (fun z _ => hz z)]
          rw [Finset.mul_sum]

/-- Acceptance of a finite real linear combination of witness matrices is the corresponding
linear combination of their acceptance values. -/
theorem wcAcceptProb_sum (A : ClassicalOracle) (p : WitnessVerifierProgram) (x : Reg p.inputBits)
    {ι : Type} [Fintype ι] (c : ι → ℝ)
    (D : ι → Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) :
    acceptProb A p x (∑ w : ι, c w • D w) = ∑ w : ι, c w * acceptProb A p x (D w) := by
  classical
  have h : ∀ s : Finset ι,
      acceptProb A p x (∑ w ∈ s, c w • D w) = ∑ w ∈ s, c w * acceptProb A p x (D w) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty]
        unfold acceptProb
        have hz : verifierInputDensity p x (0 : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ) = 0 := by
          ext i j
          simp [verifierInputDensity, Matrix.of_apply]
        rw [hz, Matrix.mul_zero, Matrix.zero_mul]
        simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [wcAcceptProb_add, wcAcceptProb_smul, ih]
  simpa using h (Finset.univ : Finset ι)

/-- A diagonal witness matrix with real diagonal entries is the real linear combination of
classical witness densities given by those entries. -/
theorem wcDiagonalDensity_classical_decomposition {p : WitnessVerifierProgram}
    (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hdiag : WcDiagonalDensity σ)
    (hreal : ∀ w : Reg p.witnessBits, (σ w w).im = 0) :
    σ = ∑ w : Reg p.witnessBits, ((σ w w).re) • classicalWitnessDensity w := by
  classical
  have hket : ∀ (w : Reg p.witnessBits) (i j : Reg p.witnessBits),
      classicalWitnessDensity w i j
        = (if i = w then (1 : ℂ) else 0) * (if j = w then (1 : ℂ) else 0) := by
    intro w i j
    by_cases h1 : i = w <;> by_cases h2 : j = w <;>
      simp [classicalWitnessDensity, outerProduct, Qatlib.Foundations.PureStateMath.Ket, h1,
          h2]
  have hdelta : ∀ (g : Reg p.witnessBits → ℂ) (a : Reg p.witnessBits),
      (∑ w : Reg p.witnessBits, g w * (if a = w then (1 : ℂ) else 0)) = g a := by
    intro g a
    have hpoint : ∀ w : Reg p.witnessBits,
        g w * (if a = w then (1 : ℂ) else 0) = (if w = a then g w else 0) := by
      intro w
      by_cases h : a = w
      · subst h
        simp
      · simp [h, Ne.symm h]
    rw [Finset.sum_congr rfl (fun w _ => hpoint w)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Reg p.witnessBits)) a (fun w => g w)]
    simp
  have hdelta2 : ∀ (g : Reg p.witnessBits → ℂ) (a b : Reg p.witnessBits),
      (∑ w : Reg p.witnessBits,
        g w * ((if a = w then (1 : ℂ) else 0) * (if b = w then (1 : ℂ) else 0)))
        = if a = b then g a else 0 := by
    intro g a b
    by_cases hab : a = b
    · subst hab
      have hpoint : ∀ w : Reg p.witnessBits,
          g w * ((if a = w then (1 : ℂ) else 0) * (if a = w then (1 : ℂ) else 0))
            = g w * (if a = w then (1 : ℂ) else 0) := by
        intro w
        by_cases h : a = w
        · simp [h]
        · simp [h]
      rw [Finset.sum_congr rfl (fun w _ => hpoint w)]
      rw [hdelta g a]
      simp
    · have hpoint : ∀ w : Reg p.witnessBits,
          g w * ((if a = w then (1 : ℂ) else 0) * (if b = w then (1 : ℂ) else 0)) = 0 := by
        intro w
        by_cases h1 : a = w
        · by_cases h2 : b = w
          · exact absurd (h1.trans h2.symm) hab
          · simp [h1, h2]
        · simp [h1]
      rw [Finset.sum_congr rfl (fun w _ => hpoint w)]
      simp only [Finset.sum_const, if_neg hab]
      simp
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply]
  have hconv : ∀ w : Reg p.witnessBits,
      ((σ w w).re) • classicalWitnessDensity w i j
        = ((σ w w).re : ℂ)
            * ((if i = w then (1 : ℂ) else 0) * (if j = w then (1 : ℂ) else 0)) := by
    intro w
    rw [hket w i j]
    rfl
  rw [Finset.sum_congr rfl (fun w _ => hconv w)]
  have hsum := hdelta2 (fun w => ((σ w w).re : ℂ)) i j
  rw [hsum]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hre : σ i i = ((σ i i).re : ℂ) := by
      rw [Complex.ext_iff]
      exact ⟨rfl, by simpa using hreal i⟩
    rw [hre]
    simp
  · rw [if_neg hij]
    exact hdiag i j hij

/-- For a diagonal witness matrix with real diagonal entries, acceptance is the
diagonal-weighted sum of classical witness acceptance values. -/
theorem wcAcceptProb_diagonal_formula (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hdiag : WcDiagonalDensity σ) (hreal : ∀ w : Reg p.witnessBits, (σ w w).im = 0) :
    acceptProb A p x σ
      = ∑ w : Reg p.witnessBits, (σ w w).re * acceptProb A p x (classicalWitnessDensity w) := by
  have hdec := wcDiagonalDensity_classical_decomposition σ hdiag hreal
  calc acceptProb A p x σ
      = acceptProb A p x (∑ w : Reg p.witnessBits, ((σ w w).re) • classicalWitnessDensity w) := by
        conv_lhs => rw [hdec]
    _ = ∑ w : Reg p.witnessBits, (σ w w).re * acceptProb A p x (classicalWitnessDensity w) :=
      wcAcceptProb_sum A p x (fun w => (σ w w).re) (fun w => classicalWitnessDensity w)

/-- A soundness bound of `1 / 3` on all classical witnesses extends to every diagonal witness
density. -/
theorem wcQCMA_soundness_transfers_diagonal (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hσ : IsWitnessDensity σ) (hdiag : WcDiagonalDensity σ)
    (hsound : ∀ w : Reg p.witnessBits,
      acceptProb A p x (classicalWitnessDensity w) ≤ 1 / 3) :
    acceptProb A p x σ ≤ 1 / 3 := by
  have hpsd : ∀ w : Reg p.witnessBits, 0 ≤ σ w w := by
    intro w
    exact hσ.2.1.diag_nonneg (i := w)
  have hre : ∀ w : Reg p.witnessBits, (σ w w).im = 0 := by
    intro w
    exact (Complex.nonneg_iff.mp (hpsd w)).2.symm
  have hnonneg : ∀ w : Reg p.witnessBits, 0 ≤ (σ w w).re := by
    intro w
    exact (Complex.nonneg_iff.mp (hpsd w)).1
  have hdiag_sum : (∑ w : Reg p.witnessBits, (σ w w).re) ≤ 1 := by
    have htr : Matrix.trace σ = ∑ w : Reg p.witnessBits, σ w w := by
      simp [Matrix.trace, Matrix.diag_apply]
    have htrle := Complex.le_def.mp hσ.2.2
    have hre_sum : (∑ w : Reg p.witnessBits, (σ w w).re) = (Matrix.trace σ).re := by
      rw [htr, Complex.re_sum]
    rw [hre_sum]
    simpa using htrle.1
  rw [wcAcceptProb_diagonal_formula A p x σ hdiag hre]
  have hterm : ∀ w : Reg p.witnessBits,
      (σ w w).re * acceptProb A p x (classicalWitnessDensity w)
        ≤ (σ w w).re * (1 / 3 : ℝ) := by
    intro w
    exact mul_le_mul_of_nonneg_left (hsound w) (hnonneg w)
  have hsum : (∑ w : Reg p.witnessBits,
      (σ w w).re * acceptProb A p x (classicalWitnessDensity w))
      ≤ ∑ w : Reg p.witnessBits, (σ w w).re * (1 / 3 : ℝ) :=
    Finset.sum_le_sum fun w _ => hterm w
  calc (∑ w : Reg p.witnessBits,
      (σ w w).re * acceptProb A p x (classicalWitnessDensity w))
      ≤ ∑ w : Reg p.witnessBits, (σ w w).re * (1 / 3 : ℝ) := hsum
    _ = (∑ w : Reg p.witnessBits, (σ w w).re) * (1 / 3 : ℝ) := by
      rw [Finset.sum_mul]
    _ ≤ 1 * (1 / 3 : ℝ) := by
      have hnonneg : 0 ≤ (1 / 3 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_right hdiag_sum hnonneg
    _ = 1 / 3 := by ring

/-- If the acceptance functional depends only on classical diagonal weights, a classical-witness
soundness bound of `1 / 3` extends to every witness density. -/
theorem wcQCMA_soundness_transfers_full (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hσ : IsWitnessDensity σ) (hclassical : WcClassicalAcceptFunctional A p x)
    (hsound : ∀ w : Reg p.witnessBits,
      acceptProb A p x (classicalWitnessDensity w) ≤ 1 / 3) :
    acceptProb A p x σ ≤ 1 / 3 := by
  have hpsd : ∀ w : Reg p.witnessBits, 0 ≤ σ w w := by
    intro w
    exact hσ.2.1.diag_nonneg (i := w)
  have hnonneg : ∀ w : Reg p.witnessBits, 0 ≤ (σ w w).re := by
    intro w
    exact (Complex.nonneg_iff.mp (hpsd w)).1
  have hdiag_sum : (∑ w : Reg p.witnessBits, (σ w w).re) ≤ 1 := by
    have htr : Matrix.trace σ = ∑ w : Reg p.witnessBits, σ w w := by
      simp [Matrix.trace, Matrix.diag_apply]
    have htrle := Complex.le_def.mp hσ.2.2
    have hre_sum : (∑ w : Reg p.witnessBits, (σ w w).re) = (Matrix.trace σ).re := by
      rw [htr, Complex.re_sum]
    rw [hre_sum]
    simpa using htrle.1
  rw [hclassical σ]
  have hterm : ∀ w : Reg p.witnessBits,
      (σ w w).re * acceptProb A p x (classicalWitnessDensity w)
        ≤ (σ w w).re * (1 / 3 : ℝ) := by
    intro w
    exact mul_le_mul_of_nonneg_left (hsound w) (hnonneg w)
  have hsum : (∑ w : Reg p.witnessBits,
      (σ w w).re * acceptProb A p x (classicalWitnessDensity w))
      ≤ ∑ w : Reg p.witnessBits, (σ w w).re * (1 / 3 : ℝ) :=
    Finset.sum_le_sum fun w _ => hterm w
  calc (∑ w : Reg p.witnessBits,
      (σ w w).re * acceptProb A p x (classicalWitnessDensity w))
      ≤ ∑ w : Reg p.witnessBits, (σ w w).re * (1 / 3 : ℝ) := hsum
    _ = (∑ w : Reg p.witnessBits, (σ w w).re) * (1 / 3 : ℝ) := by
      rw [Finset.sum_mul]
    _ ≤ 1 * (1 / 3 : ℝ) := by
      have hnonneg : 0 ≤ (1 / 3 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_right hdiag_sum hnonneg
    _ = 1 / 3 := by ring

/-- Acceptance of a convex mixture of two pure witness matrices is at most the larger of their
acceptance values. -/
theorem wcMixedWitness_dominated_by_pure (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (ψ₁ ψ₂ : QState (Reg p.witnessBits)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    acceptProb A p x (((t : ℂ) • pureWitnessDensity ψ₁ + ((1 - t : ℝ) : ℂ) • pureWitnessDensity ψ₂))
      ≤ max (acceptProb A p x (pureWitnessDensity ψ₁))
        (acceptProb A p x (pureWitnessDensity ψ₂)) := by
  have hconvex : acceptProb A p x
        (((t : ℂ) • pureWitnessDensity ψ₁ + ((1 - t : ℝ) : ℂ) • pureWitnessDensity ψ₂))
      = t * acceptProb A p x (pureWitnessDensity ψ₁)
        + (1 - t) * acceptProb A p x (pureWitnessDensity ψ₂) := by
    rw [acceptProb_add, acceptProb_smul, acceptProb_smul]
  rw [hconvex]
  set a := acceptProb A p x (pureWitnessDensity ψ₁) with ha
  set b := acceptProb A p x (pureWitnessDensity ψ₂) with hb
  have h₁ : t * a ≤ t * max a b :=
    mul_le_mul_of_nonneg_left (le_max_left a b) ht0
  have h₂ : (1 - t) * b ≤ (1 - t) * max a b := by
    have hnonneg : 0 ≤ 1 - t := by linarith
    exact mul_le_mul_of_nonneg_left (le_max_right a b) hnonneg
  calc t * a + (1 - t) * b ≤ t * max a b + (1 - t) * max a b := add_le_add h₁ h₂
    _ = max a b := by ring

/-- Uniform QCMA membership provides an oracle-free family with a valid quantum witness density
achieving completeness `2 / 3` on every yes input. -/
theorem wcQCMA_completeness_transfers {L : BitLanguage} (h : InUniformQCMA L) :
    ∃ f : UniformWitnessFamily, f.OracleFree ∧
      (∀ x : List Bool, L.yes x = true →
        ∃ σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ,
          IsWitnessDensity σ ∧
            2 / 3 ≤ uniformAcceptProb f (fun _ _ => false) x σ) := by
  obtain ⟨f, hfree, hyes, _⟩ := h
  refine ⟨f, hfree, ?_⟩
  intro x hx
  obtain ⟨w, hw⟩ := hyes x hx
  exact ⟨uniformClassicalDensity f x w, uniformQCMA_witness_isQMA f x w, hw⟩

/-- The identity on the empty witness register is the density of its unique classical witness. -/
theorem wcEmptyWitnessDensity_eq_classical :
    (1 : Matrix (Reg 0) (Reg 0) ℂ) = classicalWitnessDensity (fun _ => false) := by
  simpa [classicalWitnessDensity, pureWitnessDensity] using matrix_one_eq_pure_zero

/-- For a zero-witness program, acceptance of the empty identity equals acceptance of the unique
classical witness density. -/
theorem wcEmptyWitness_acceptProb_eq (A : ClassicalOracle)
    (iB aB oB : ℕ) (instrs : List WitnessInstruction) (x : Reg iB) :
    acceptProb A (WcEmptyWitnessProgram iB aB oB instrs) x (1 : Matrix (Reg 0) (Reg 0) ℂ)
      = acceptProb A (WcEmptyWitnessProgram iB aB oB instrs) x
          (classicalWitnessDensity (fun _ => false)) := by
  rw [wcEmptyWitnessDensity_eq_classical]
  rfl

/-- Classical-witness soundness for a generated family extends to diagonal witness densities on
every no input. -/
theorem wcQCMA_soundness_transfers_diagonal_family {L : BitLanguage}
    (f : UniformWitnessFamily)
    (hsound : ∀ x : List Bool, L.no x = true →
      ∀ w : Reg ((f.generator x).witnessBits),
        acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
          (classicalWitnessDensity w) ≤ 1 / 3) :
    ∀ x : List Bool, L.no x = true →
      ∀ σ : Matrix (Reg ((f.generator x).witnessBits)) (Reg ((f.generator x).witnessBits)) ℂ,
        IsWitnessDensity σ → WcDiagonalDensity σ →
          acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x) σ ≤ 1 / 3 := by
  intro x hx σ hσ hdiag
  exact wcQCMA_soundness_transfers_diagonal (fun _ _ => false) (f.generator x)
    (listToInput (f.generator x) x) σ hσ hdiag (hsound x hx)

/-- The diagonal part of a witness matrix preserves each diagonal entry. -/
theorem wcDiagonalPart_diag {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) (w : Reg m) :
    WcDiagonalPart σ w w = σ w w := by
  simp [WcDiagonalPart]

/-- The diagonal part of a witness matrix vanishes at distinct indices. -/
theorem wcDiagonalPart_offdiag {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) (w w' : Reg m)
    (hne : w ≠ w') : WcDiagonalPart σ w w' = 0 := by
  simp [WcDiagonalPart, hne]

/-- The diagonal part of every witness matrix satisfies `WcDiagonalDensity`. -/
theorem wcDiagonalPart_isDiagonal {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) :
    WcDiagonalDensity (WcDiagonalPart σ) := by
  intro w w' hne
  exact wcDiagonalPart_offdiag σ w w' hne

/-- The off-diagonal part of a witness matrix has zero diagonal. -/
theorem wcOffDiagonalPart_zero_diag {m : ℕ} (σ : Matrix (Reg m) (Reg m) ℂ) (w : Reg m) :
    WcOffDiagonalPart σ w w = 0 := by
  simp [WcOffDiagonalPart]

/-- Classical-witness soundness bounds acceptance of the diagonal part of any witness density by
`1 / 3`. -/
theorem wcDiagonalPart_soundness (A : ClassicalOracle) (p : WitnessVerifierProgram)
    (x : Reg p.inputBits) (σ : Matrix (Reg p.witnessBits) (Reg p.witnessBits) ℂ)
    (hσ : IsWitnessDensity σ)
    (hsound : ∀ w : Reg p.witnessBits,
      acceptProb A p x (classicalWitnessDensity w) ≤ 1 / 3) :
    acceptProb A p x (WcDiagonalPart σ) ≤ 1 / 3 := by
  have hpsd : ∀ w : Reg p.witnessBits, 0 ≤ σ w w := by
    intro w
    exact hσ.2.1.diag_nonneg (i := w)
  have hre : ∀ w : Reg p.witnessBits, (σ w w).im = 0 := by
    intro w
    exact (Complex.nonneg_iff.mp (hpsd w)).2.symm
  have hnonneg : ∀ w : Reg p.witnessBits, 0 ≤ (σ w w).re := by
    intro w
    exact (Complex.nonneg_iff.mp (hpsd w)).1
  have hdiag_sum : (∑ w : Reg p.witnessBits, (σ w w).re) ≤ 1 := by
    have htr : Matrix.trace σ = ∑ w : Reg p.witnessBits, σ w w := by
      simp [Matrix.trace, Matrix.diag_apply]
    have htrle := Complex.le_def.mp hσ.2.2
    have hre_sum : (∑ w : Reg p.witnessBits, (σ w w).re) = (Matrix.trace σ).re := by
      rw [htr, Complex.re_sum]
    rw [hre_sum]
    simpa using htrle.1
  have hre' : ∀ w : Reg p.witnessBits, (WcDiagonalPart σ w w).im = 0 := by
    intro w
    rw [wcDiagonalPart_diag σ w]
    exact hre w
  rw [wcAcceptProb_diagonal_formula A p x (WcDiagonalPart σ) (wcDiagonalPart_isDiagonal σ) hre']
  have hterm : ∀ w : Reg p.witnessBits,
      (WcDiagonalPart σ w w).re * acceptProb A p x (classicalWitnessDensity w)
        ≤ (WcDiagonalPart σ w w).re * (1 / 3 : ℝ) := by
    intro w
    rw [wcDiagonalPart_diag σ w]
    exact mul_le_mul_of_nonneg_left (hsound w) (hnonneg w)
  have hsum : (∑ w : Reg p.witnessBits,
      (WcDiagonalPart σ w w).re * acceptProb A p x (classicalWitnessDensity w))
      ≤ ∑ w : Reg p.witnessBits, (WcDiagonalPart σ w w).re * (1 / 3 : ℝ) :=
    Finset.sum_le_sum fun w _ => hterm w
  have hsum' : (∑ w : Reg p.witnessBits, (WcDiagonalPart σ w w).re)
      = ∑ w : Reg p.witnessBits, (σ w w).re := by
    apply Finset.sum_congr rfl
    intro w _
    rw [wcDiagonalPart_diag σ w]
  calc (∑ w : Reg p.witnessBits,
      (WcDiagonalPart σ w w).re * acceptProb A p x (classicalWitnessDensity w))
      ≤ ∑ w : Reg p.witnessBits, (WcDiagonalPart σ w w).re * (1 / 3 : ℝ) := hsum
    _ = (∑ w : Reg p.witnessBits, (WcDiagonalPart σ w w).re) * (1 / 3 : ℝ) := by
      rw [Finset.sum_mul]
    _ = (∑ w : Reg p.witnessBits, (σ w w).re) * (1 / 3 : ℝ) := by rw [hsum']
    _ ≤ 1 * (1 / 3 : ℝ) := by
      have hnonneg' : 0 ≤ (1 / 3 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_right hdiag_sum hnonneg'
    _ = 1 / 3 := by ring

/-- Casting a finite index along an equality and then its inverse recovers the original index. -/
private theorem wcFinCast_symm_cast {n m : ℕ} (h : n = m) (j : Fin n) :
    Fin.cast h.symm (Fin.cast h j) = j := by
  subst h
  rfl

/-- Casting a register-indexed matrix across a width equality evaluates by casting each register
coordinate back. -/
private theorem wcCastTransport (w g : ℕ) (hw : g = w)
    (σ : Matrix (Reg w) (Reg w) ℂ) (i j : Reg g) :
    (cast (congrArg (fun m => Matrix (Reg m) (Reg m) ℂ) hw.symm) σ) i j
      = σ (fun k => i (Fin.cast hw.symm k)) (fun k => j (Fin.cast hw.symm k)) := by
  subst hw
  rfl

/-- Casting a witness matrix across a width equality preserves the sum of real diagonal entries. -/
private theorem wcCastDiagSum (w g : ℕ) (hw : g = w)
    (σ : Matrix (Reg w) (Reg w) ℂ) :
    (∑ i : Reg g, ((cast (congrArg (fun m => Matrix (Reg m) (Reg m) ℂ) hw.symm) σ) i i).re)
      = (∑ j : Reg w, (σ j j).re) := by
  subst hw
  rfl

/-- Equal classical witness registers determine equal density matrices. -/
private theorem wcClassicalDensity_congr {m : ℕ} {v v' : Reg m} (h : v = v') :
    classicalWitnessDensity v = classicalWitnessDensity v' := by
  rw [h]

/-- Casting a classical witness density across a width equality gives the density of the
reindexed witness. -/
private theorem wcCastClassical (w g : ℕ) (hw : g = w) (v : Reg w) :
    (cast (congrArg (fun m => Matrix (Reg m) (Reg m) ℂ) hw.symm) (classicalWitnessDensity v))
      = classicalWitnessDensity (fun k => v (Fin.cast hw k)) := by
  subst hw
  have hvv : v = (fun k => v (Fin.cast rfl k)) := by
    funext k
    rfl
  exact congrArg classicalWitnessDensity hvv

/-- An entry of `uniformDensity` is obtained by reindexing both registers along the family's
witness-width equality. -/
theorem wcUniformDensity_apply (f : UniformWitnessFamily) (x : List Bool)
    (σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ)
    (i j : Reg (f.generator x).witnessBits) :
    (uniformDensity f x σ) i j
      = σ (fun k => i (Fin.cast (f.generatorWidths x).1.symm k))
          (fun k => j (Fin.cast (f.generatorWidths x).1.symm k)) := by
  exact wcCastTransport (f.witnessWidth x.length) ((f.generator x).witnessBits)
    (f.generatorWidths x).1 σ i j

/-- Transport to the generated verifier's witness width preserves the sum of real diagonal
entries. -/
theorem wcUniformDensity_diagSum (f : UniformWitnessFamily) (x : List Bool)
    (σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ) :
    (∑ i : Reg ((f.generator x).witnessBits), ((uniformDensity f x σ) i i).re)
      = (∑ j : Reg (f.witnessWidth x.length), (σ j j).re) := by
  exact wcCastDiagSum (f.witnessWidth x.length) ((f.generator x).witnessBits)
    (f.generatorWidths x).1 σ

/-- Transport of a classical witness density is the density of its reindexed classical witness. -/
theorem wcUniformDensity_classical (f : UniformWitnessFamily) (x : List Bool)
    (v : Reg (f.witnessWidth x.length)) :
    uniformDensity f x (classicalWitnessDensity v)
      = classicalWitnessDensity (WcWitnessReindex (f.generatorWidths x).1 v) := by
  exact wcCastClassical (f.witnessWidth x.length) ((f.generator x).witnessBits)
    (f.generatorWidths x).1 v

/-- Every classical witness for a generated verifier arises by reindexing a witness at the
family width. -/
theorem wcWitnessReindex_surjective (f : UniformWitnessFamily) (x : List Bool)
    (w' : Reg ((f.generator x).witnessBits)) :
    ∃ v : Reg (f.witnessWidth x.length),
      WcWitnessReindex (f.generatorWidths x).1 v = w' := by
  refine ⟨fun j => w' (Fin.cast (f.generatorWidths x).1.symm j), ?_⟩
  funext k
  have hk : Fin.cast (f.generatorWidths x).1.symm (Fin.cast (f.generatorWidths x).1 k) = k :=
    wcFinCast_symm_cast (f.generatorWidths x).1 k
  show w' (Fin.cast (f.generatorWidths x).1.symm (Fin.cast (f.generatorWidths x).1 k)) = w' k
  rw [hk]

/-- For a family satisfying `WcDiagonalAcceptFamily`, classical-witness soundness extends to all
witness densities on no inputs. -/
theorem wcQCMA_soundness_transfers_class {L : BitLanguage} (f : UniformWitnessFamily)
    (hno : ∀ x : List Bool, L.no x = true →
      ∀ w : Reg (f.witnessWidth x.length),
        uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w) ≤ 1 / 3)
    (hdiag : WcDiagonalAcceptFamily f) :
    ∀ x : List Bool, L.no x = true →
      ∀ σ : Matrix (Reg (f.witnessWidth x.length)) (Reg (f.witnessWidth x.length)) ℂ,
        IsWitnessDensity σ →
          uniformAcceptProb f (fun _ _ => false) x σ ≤ 1 / 3 := by
  intro x hx σ hσ
  have hpsd : ∀ w : Reg (f.witnessWidth x.length), 0 ≤ σ w w := by
    intro w
    exact hσ.2.1.diag_nonneg (i := w)
  have hnonneg : ∀ w : Reg (f.witnessWidth x.length), 0 ≤ (σ w w).re := by
    intro w
    exact (Complex.nonneg_iff.mp (hpsd w)).1
  have hdiag_sum : (∑ w : Reg (f.witnessWidth x.length), (σ w w).re) ≤ 1 := by
    have htr : Matrix.trace σ = ∑ w : Reg (f.witnessWidth x.length), σ w w := by
      simp [Matrix.trace, Matrix.diag_apply]
    have htrle := Complex.le_def.mp hσ.2.2
    have hre_sum : (∑ w : Reg (f.witnessWidth x.length), (σ w w).re) = (Matrix.trace σ).re := by
      rw [htr, Complex.re_sum]
    rw [hre_sum]
    simpa using htrle.1

  have hgen : ∀ w' : Reg ((f.generator x).witnessBits),
      acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
        (classicalWitnessDensity w') ≤ 1 / 3 := by
    intro w'
    obtain ⟨v, hv⟩ := wcWitnessReindex_surjective f x w'
    have hval : uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x v)
        ≤ 1 / 3 := hno x hx v
    have hmat : uniformDensity f x (classicalWitnessDensity v) = classicalWitnessDensity w' := by
      rw [wcUniformDensity_classical f x v, hv]
    unfold uniformAcceptProb uniformClassicalDensity at hval
    rw [hmat] at hval
    exact hval

  have hnonneg' : ∀ w' : Reg ((f.generator x).witnessBits),
      0 ≤ ((uniformDensity f x σ) w' w').re := by
    intro w'
    rw [wcUniformDensity_apply f x σ w' w']
    exact hnonneg (fun k => w' (Fin.cast (f.generatorWidths x).1.symm k))

  have hfun : WcClassicalAcceptFunctional (fun _ _ => false) (f.generator x)
      (listToInput (f.generator x) x) := hdiag x
  have hdecomp : acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
      (uniformDensity f x σ)
      = ∑ w' : Reg ((f.generator x).witnessBits),
          ((uniformDensity f x σ) w' w').re
            * acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
              (classicalWitnessDensity w') := hfun (uniformDensity f x σ)
  have hterm : ∀ w' : Reg ((f.generator x).witnessBits),
      ((uniformDensity f x σ) w' w').re
          * acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
              (classicalWitnessDensity w')
        ≤ ((uniformDensity f x σ) w' w').re * (1 / 3 : ℝ) := by
    intro w'
    exact mul_le_mul_of_nonneg_left (hgen w') (hnonneg' w')
  have hsum : (∑ w' : Reg ((f.generator x).witnessBits),
        ((uniformDensity f x σ) w' w').re
          * acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
            (classicalWitnessDensity w'))
      ≤ ∑ w' : Reg ((f.generator x).witnessBits),
          ((uniformDensity f x σ) w' w').re * (1 / 3 : ℝ) :=
    Finset.sum_le_sum fun w' _ => hterm w'
  unfold uniformAcceptProb
  rw [hdecomp]
  calc (∑ w' : Reg ((f.generator x).witnessBits),
        ((uniformDensity f x σ) w' w').re
          * acceptProb (fun _ _ => false) (f.generator x) (listToInput (f.generator x) x)
            (classicalWitnessDensity w'))
      ≤ ∑ w' : Reg ((f.generator x).witnessBits),
          ((uniformDensity f x σ) w' w').re * (1 / 3 : ℝ) := hsum
    _ = (∑ w' : Reg ((f.generator x).witnessBits),
          ((uniformDensity f x σ) w' w').re) * (1 / 3 : ℝ) := by
      rw [Finset.sum_mul]
    _ = (∑ j : Reg (f.witnessWidth x.length), (σ j j).re) * (1 / 3 : ℝ) := by
      rw [wcUniformDensity_diagSum f x σ]
    _ ≤ 1 * (1 / 3 : ℝ) := by
      have hnonneg'' : 0 ≤ (1 / 3 : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_right hdiag_sum hnonneg''
    _ = 1 / 3 := by ring

/-- An oracle-free family with classical completeness and soundness witnesses uniform QMA
membership when it also satisfies `WcDiagonalAcceptFamily`. -/
theorem wcInUniformQCMA_subset_QMA {L : BitLanguage} (f : UniformWitnessFamily)
    (hfree : f.OracleFree)
    (hyes : ∀ x : List Bool, L.yes x = true →
      ∃ w : Reg (f.witnessWidth x.length),
        2 / 3 ≤ uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w))
    (hno : ∀ x : List Bool, L.no x = true →
      ∀ w : Reg (f.witnessWidth x.length),
        uniformAcceptProb f (fun _ _ => false) x (uniformClassicalDensity f x w) ≤ 1 / 3)
    (hdiag : WcDiagonalAcceptFamily f) :
    InUniformQMA L := by
  refine ⟨f, hfree, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hw⟩ := hyes x hx
    exact ⟨uniformClassicalDensity f x w, uniformQCMA_witness_isQMA f x w, hw⟩
  · intro x hx σ hσ
    exact wcQCMA_soundness_transfers_class f hno hdiag x hx σ hσ

/-- Uniform QCMA membership implies uniform QMA membership under the additional language
condition `WcDiagonalAcceptLanguage`. -/
theorem wcInUniformQCMA_subset_QMA_of {L : BitLanguage} (h : InUniformQCMA L)
    (hdiag : WcDiagonalAcceptLanguage L) :
    InUniformQMA L := by
  obtain ⟨f, hfree, hyes, hno⟩ := h
  exact wcInUniformQCMA_subset_QMA f hfree hyes hno (hdiag f hyes hno)

end Qatlib.Concepts.LocalMachine.LocalTransport
