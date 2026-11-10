/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyEvolutionDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.WalkFind.SearchAlgorithm
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib.Concepts.CopyEvolution.SelfTomography

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution

open Matrix Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator
set_option warningAsError false

theorem indexedLoad_eq_loadedTable {b a aw t m : ℕ} (ψ : Reg b) (ht : t < b) :
    indexedLoad b a aw t m ψ = loadedTable b m ψ (loadAddress b a aw ψ) := by
  simp [indexedLoad, loadedTable, loadAddress, readBit, qramAction, ht]

theorem loadAddress_preserved {b a aw t m ml : ℕ} (ψ : Reg b)
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    loadAddress b a aw (qramAction b a aw t m ψ) = loadAddress b a aw ψ :=
  legal_qram_preserves_address hg ψ

theorem qramAction_involutive {b a aw t m ml : ℕ} (ψ : Reg b)
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    qramAction b a aw t m (qramAction b a aw t m ψ) = ψ :=
  legal_qram_involutive hg ψ

theorem copyEvolutionLoadingProgram_length (n b a aw t m ml : ℕ) :
    (copyEvolutionLoadingProgram n b a aw t m ml).length = n * b := by
  simp [copyEvolutionLoadingProgram]

theorem copyEvolutionLoadingProgram_legal {n b a aw t m ml : ℕ}
    (hg : sourceCodeLegal b (.qram a aw t m ml) = true) :
    (∀ c ∈ copyEvolutionLoadingProgram n b a aw t m ml, sourceCodeLegal b c = true) ∧
    sourceWordLegal b (copyEvolutionLoadingProgram n b a aw t m ml) := by
  constructor
  · intro c hc
    simp only [copyEvolutionLoadingProgram, List.mem_replicate] at hc
    obtain ⟨i, rfl⟩ := hc
    exact hg
  · intro c hc
    simp only [copyEvolutionLoadingProgram, List.mem_replicate] at hc
    obtain ⟨i, rfl⟩ := hc
    exact hg

theorem copyEvolutionLoadingBasicGates_eq (n b : ℕ) :
    copyEvolutionLoadingBasicGates n b = 3 * n * b ∧
      copyEvolutionLoadingBasicGates n b = copyEvolutionBasicGates n b := by
  simp [copyEvolutionLoadingBasicGates, copyEvolutionBasicGates]

theorem copyEvolutionLoadingBitCost_sum (n b a aw t m ml : ℕ) :
    ((copyEvolutionLoadingProgram n b a aw t m ml).map
      (fun _ => copyEvolutionLoadingBitCost a aw t m ml)).sum =
      (n * b) * copyEvolutionLoadingBitCost a aw t m ml := by
  simp [copyEvolutionLoadingProgram, copyEvolutionLoadingBitCost]

theorem normDependentCopyBudget_certified {D r : ℕ} (ρ : Operator D) (t ε R : ℝ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ)
    (hρ : IsDensityOperator ρ) (hX : X.PosSemidef) (hε : 0 < ε) (hR : 0 ≤ R)
    (hres : Matrix.traceNorm (X - TensorGate ρ (Matrix.traceLeft X)) ≤ R)
    {n : ℕ} (hn : normDependentCopyBudget t ε R ≤ n) :
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) r X -
      TensorGate (HamiltonianEvolution ρ t) (1 : Operator r) * X *
        (TensorGate (HamiltonianEvolution ρ t) (1 : Operator r))ᴴ) ≤ ε := by
  have hnpos : 0 < n := by
    have h1 : 1 ≤ normDependentCopyBudget t ε R := by
      simp [normDependentCopyBudget]
    omega
  have herr := copy_state_dependent_fresh_global_error D r ρ t n X hρ hX hnpos
  have hceil : Nat.ceil (8 * t ^ 2 * R / ε) ≤ n := by
    have h := hn
    simp only [normDependentCopyBudget] at h
    omega
  have hle : 8 * t ^ 2 * R / ε ≤ (n : ℝ) := by
    have h1 : 8 * t ^ 2 * R / ε ≤ (Nat.ceil (8 * t ^ 2 * R / ε) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (8 * t ^ 2 * R / ε) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hceil
    exact h1.trans h2
  have hle' : 8 * t ^ 2 * R ≤ ε * (n : ℝ) := by
    have h := (div_le_iff₀ hε).mp hle
    simpa [mul_comm] using! h
  calc
    Matrix.traceNorm (freshCopyReferenceRun ρ (List.replicate n (t / (n : ℝ))) r X -
        TensorGate (HamiltonianEvolution ρ t) (1 : Operator r) * X *
          (TensorGate (HamiltonianEvolution ρ t) (1 : Operator r))ᴴ)
        ≤ 8 * t ^ 2 / (n : ℝ) *
            Matrix.traceNorm (X - TensorGate ρ (Matrix.traceLeft X)) := herr
    _ ≤ 8 * t ^ 2 / (n : ℝ) * R := by
      exact mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ε := by
      have hlast : (8 * t ^ 2 * R) / (n : ℝ) ≤ ε :=
        (div_le_iff₀ (by exact_mod_cast hnpos)).mpr hle'
      rw [show 8 * t ^ 2 / (n : ℝ) * R = (8 * t ^ 2 * R) / (n : ℝ) by ring]
      exact hlast

theorem walkGoal_endpoint : walkGoalEndpointSpec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b a aw t m ψ ht
    exact indexedLoad_eq_loadedTable ψ ht
  · intro b a aw t m ml ψ hg
    exact loadAddress_preserved ψ hg
  · intro b a aw t m ml ψ hg
    exact qramAction_involutive ψ hg
  · intro n b a aw t m ml hg
    exact ⟨copyEvolutionLoadingProgram_length n b a aw t m ml,
      (copyEvolutionLoadingProgram_legal hg).1⟩
  · intro n b
    exact copyEvolutionLoadingBasicGates_eq n b
  · intro n b a aw t m ml
    exact copyEvolutionLoadingBitCost_sum n b a aw t m ml
  · intro b cs hcs
    exact sourceWord_unitary b cs hcs
  · intro D r ρ t ε R X hρ hX hε hR hres n hn
    exact normDependentCopyBudget_certified ρ t ε R X hρ hX hε hR hres hn

private theorem starRingEnd_smul_real (c : ℝ) (w : ℂ) :
    starRingEnd ℂ ((c : ℂ) * w) = (c : ℂ) * starRingEnd ℂ w := by
  have h2 : star (c : ℂ) = (c : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simp only [starRingEnd_apply]
  rw [star_mul, h2]
  ring

private theorem smul_outerProduct (a : ℝ) (ha : 0 ≤ a) {I : Type*} [Fintype I]
    [DecidableEq I] (ψ : I → ℂ) :
    (a : ℂ) • outerProduct ψ = outerProduct ((Real.sqrt a : ℂ) • ψ) := by
  ext j j'
  simp only [Matrix.smul_apply, outerProduct_apply, Pi.smul_apply]
  have hsq : (Real.sqrt a : ℂ) * (Real.sqrt a : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    simpa [pow_two] using! Real.sq_sqrt ha
  calc
    (a : ℂ) * (ψ j * starRingEnd ℂ (ψ j'))
        = ((Real.sqrt a : ℂ) * (Real.sqrt a : ℂ)) * (ψ j * starRingEnd ℂ (ψ j')) := by
          rw [hsq]
    _ = ((Real.sqrt a : ℂ) * ψ j) * ((Real.sqrt a : ℂ) * starRingEnd ℂ (ψ j')) := by ring
    _ = ((Real.sqrt a : ℂ) * ψ j) * starRingEnd ℂ ((Real.sqrt a : ℂ) * ψ j') := by
          rw [starRingEnd_smul_real]

theorem offgridBranch_eq_idealBlock {D M : ℕ} (ρ V : Operator D) (eig : Fin D → ℝ)
    (hM : 0 < M) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hs : ρ = V * Matrix.diagonal (fun i => (eig i : ℂ)) * Vᴴ) (z : Fin M)
    (j j' : Fin D) :
    copyQPEIdealOutput D M ρ ⟨z, (false, j)⟩ ⟨z, (false, j')⟩ =
      offgridBranch D M eig V z j j' := by
  rw [selfTomography_spectral_output D M hM ρ V eig hV hs]
  simp only [offgridBranch, Matrix.sum_apply, Matrix.smul_apply, outerProduct_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem offgridBranch_posSemidef {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D) (z : Fin M)
    (heig : ∀ i, 0 ≤ eig i) : (offgridBranch D M eig V z).PosSemidef := by
  rw [show offgridBranch D M eig V z =
      ∑ i, outerProduct ((Real.sqrt (eig i) : ℂ) • (fun j => qpeKernel M (-eig i / 2) z * V j i)) by
    simp only [offgridBranch]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_outerProduct (eig i) (heig i) (fun j => qpeKernel M (-eig i / 2) z * V j i)]
  exact Matrix.posSemidef_sum Finset.univ (fun i _ => outerProduct_posSemidef _)

theorem offgridBranchMass_nonneg {D M : ℕ} (eig : Fin D → ℝ) (V : Operator D) (z : Fin M)
    (heig : ∀ i, 0 ≤ eig i) : 0 ≤ offgridBranchMass D M eig V z := by
  have hpos : (offgridBranch D M eig V z).PosSemidef :=
    offgridBranch_posSemidef eig V z heig
  exact (RCLike.nonneg_iff.mp (Matrix.PosSemidef.trace_nonneg hpos)).1

private theorem finCons_zero {n : ℕ} {α : Type*} (a : α) (t : Fin n → α) :
    finCons a t 0 = a := rfl

private theorem finCons_succ {n : ℕ} {α : Type*} (a : α) (t : Fin n → α) (i : Fin n) :
    finCons a t i.succ = t i := rfl

private theorem mCopyLaw_split {M m : ℕ} (p : LabelLaw M) (a : Fin M) (t' : Fin m → Fin M) :
    mCopyLaw M (m+1) p (finCons a t') = p.mass a * mCopyLaw M m p t' := by
  simp only [mCopyLaw]
  rw [Fin.prod_univ_succ]
  simp only [finCons_zero, finCons_succ]

private theorem finSuccEquiv_symm (M m : ℕ) (a : Fin M) (t' : Fin m → Fin M) :
    (finSuccEquiv M m).symm (a, t') = finCons a t' := by rfl

theorem mCopyLaw_total (M m : ℕ) (p : LabelLaw M) :
    (∑ t : Fin m → Fin M, mCopyLaw M m p t) = 1 := by
  induction m with
  | zero =>
    haveI : Unique (Fin 0 → Fin M) :=
      Unique.mk (Inhabited.mk (fun i => Fin.elim0 i))
        (fun f => funext (fun i => Fin.elim0 i))
    simp [mCopyLaw, Fintype.sum_unique]
  | succ m ih =>
    calc
      (∑ t : Fin (m+1) → Fin M, mCopyLaw M (m+1) p t)
          = ∑ s : Fin M × (Fin m → Fin M),
              mCopyLaw M (m+1) p ((finSuccEquiv M m).symm s) := by
            exact (Equiv.sum_comp (finSuccEquiv M m).symm (mCopyLaw M (m+1) p)).symm
      _ = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
              mCopyLaw M (m+1) p (finCons a t') := by
            rw [Fintype.sum_prod_type]
            apply Finset.sum_congr rfl
            intro a _
            apply Finset.sum_congr rfl
            intro t' _
            rw [finSuccEquiv_symm]
      _ = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
              (p.mass a * mCopyLaw M m p t') := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_congr rfl (fun t' _ => mCopyLaw_split p a t')]
      _ = ∑ a : Fin M, p.mass a * (∑ t' : Fin m → Fin M, mCopyLaw M m p t') := by
            apply Finset.sum_congr rfl
            intro a _
            rw [← Finset.mul_sum]
      _ = ∑ a : Fin M, p.mass a * 1 := by
            apply Finset.sum_congr rfl
            intro a _
            rw [ih]
      _ = (∑ a : Fin M, p.mass a) * 1 := by rw [← Finset.sum_mul]
      _ = 1 := by rw [p.total]; ring

theorem mCopyLaw_marginal (M m : ℕ) (p : LabelLaw M) (j : Fin m) (z : Fin M) :
    (∑ t : Fin m → Fin M, mCopyLaw M m p t * (if t j = z then 1 else 0)) = p.mass z := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · calc
        (∑ t : Fin (m+1) → Fin M, mCopyLaw M (m+1) p t * (if t 0 = z then 1 else 0))
            = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
                mCopyLaw M (m+1) p (finCons a t') *
                  (if finCons a t' 0 = z then 1 else 0) := by
              rw [← Equiv.sum_comp (finSuccEquiv M m).symm
                  (fun t => mCopyLaw M (m+1) p t * (if t 0 = z then 1 else 0)),
                Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro t' _
              rw [finSuccEquiv_symm]
        _ = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
              (p.mass a * mCopyLaw M m p t') * (if a = z then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_congr rfl (fun t' _ =>
                by rw [mCopyLaw_split p a t', finCons_zero])]
        _ = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
              (p.mass a * (if a = z then 1 else 0)) * mCopyLaw M m p t' := by
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro t' _
              ring
        _ = ∑ a : Fin M, (p.mass a * (if a = z then 1 else 0)) *
              (∑ t' : Fin m → Fin M, mCopyLaw M m p t') := by
              apply Finset.sum_congr rfl
              intro a _
              rw [← Finset.mul_sum]
        _ = ∑ a : Fin M, (p.mass a * (if a = z then 1 else 0)) * 1 := by
              apply Finset.sum_congr rfl
              intro a _
              rw [mCopyLaw_total M m p]
        _ = (∑ a : Fin M, p.mass a * (if a = z then 1 else 0)) * 1 := by
              rw [← Finset.sum_mul]
        _ = p.mass z * 1 := by
              have hz : (∑ a : Fin M, p.mass a * (if a = z then 1 else 0))
                  = ∑ a : Fin M, if a = z then p.mass a else 0 := by
                    apply Finset.sum_congr rfl
                    intro a _
                    by_cases h : a = z <;> simp [h]
              rw [hz]
              simp
        _ = p.mass z := by ring
    · calc
        (∑ t : Fin (m+1) → Fin M, mCopyLaw M (m+1) p t * (if t j'.succ = z then 1 else 0))
            = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
                mCopyLaw M (m+1) p (finCons a t') *
                  (if finCons a t' j'.succ = z then 1 else 0) := by
              rw [← Equiv.sum_comp (finSuccEquiv M m).symm
                  (fun t => mCopyLaw M (m+1) p t * (if t j'.succ = z then 1 else 0)),
                Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro a _
              apply Finset.sum_congr rfl
              intro t' _
              rw [finSuccEquiv_symm]
        _ = ∑ a : Fin M, ∑ t' : Fin m → Fin M,
              (p.mass a * mCopyLaw M m p t') * (if t' j' = z then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_congr rfl (fun t' _ =>
                by rw [mCopyLaw_split p a t', finCons_succ])]
        _ = ∑ a : Fin M, p.mass a *
              (∑ t' : Fin m → Fin M, mCopyLaw M m p t' * (if t' j' = z then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro a _
              calc
                (∑ t' : Fin m → Fin M,
                    (p.mass a * mCopyLaw M m p t') * (if t' j' = z then 1 else 0))
                    = ∑ t' : Fin m → Fin M,
                        p.mass a * (mCopyLaw M m p t' * (if t' j' = z then 1 else 0)) := by
                          apply Finset.sum_congr rfl
                          intro t' _
                          ring
                _ = p.mass a *
                    (∑ t' : Fin m → Fin M, mCopyLaw M m p t' * (if t' j' = z then 1 else 0)) := by
                          rw [Finset.mul_sum]
        _ = ∑ a : Fin M, p.mass a * p.mass z := by
              apply Finset.sum_congr rfl
              intro a _
              rw [ih j']
        _ = (∑ a : Fin M, p.mass a) * p.mass z := by rw [← Finset.sum_mul]
        _ = p.mass z := by rw [p.total]; ring

theorem clause16_endpoint : clause16EndpointSpec := by
  refine ⟨?_, ?_, ?_⟩
  · intro D M ρ V eig hM hρ hV hs heig
    refine ⟨?_, ?_, ?_⟩
    · intro z j j'
      exact offgridBranch_eq_idealBlock ρ V eig hM hV hs z j j'
    · intro z
      exact offgridBranch_posSemidef eig V z heig
    · intro z
      exact offgridBranchMass_nonneg eig V z heig
  · intro M m p
    refine ⟨mCopyLaw_total M m p, ?_⟩
    intro j z
    exact mCopyLaw_marginal M m p j z
  · intro D ρ V eig ε hρ hV hs heig hε hε2
    have h := epsilonCubedSelfTomography D ρ V eig ε hρ hV hs heig hε hε2
    rcases h with ⟨hM2, hεM, h8, h1000, hdecode, hgoodI, hgoodA, hres⟩
    refine ⟨hdecode, hM2, hεM, h8, h1000, hres, hgoodI, hgoodA⟩

end Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution
