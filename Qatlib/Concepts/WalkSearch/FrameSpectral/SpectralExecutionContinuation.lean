/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralExecutionContinuationDefs

/-!
# Spectral estimates with execution and arithmetic bounds

This module augments the spectral bundles with explicit register encodings, paid access
requirements, and the spectrum of the unmarked principal matrix. It proves quadratic form
bounds, existence of an orthonormal eigenfamily, and exclusion of a nonzero +1 eigenvector when
the marked set is nonempty.

The endpoint theorems also include coherent sine envelope filtering, homogeneous diagonal filter
bounds, and resource accounting. The continued fraction estimates bound `cfSteps` using the
Fibonacci sequence `fib`. The quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `clause6_busySpectrumContent`: Amplitudes, frame geometry, and spectral gap content.
* `coreSpectralClause33_endpoint`: The sine envelope bundle with coherent filtering
  requirements.
* `clause39_continuedFraction`: Fibonacci and linear bounds on Euclidean division steps.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Concepts.HspRecovery.SieveLaw

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Qatlib
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

/-- Reading a right-hand coordinate of a concatenated register returns the corresponding
coordinate of the second register. -/
theorem clause6_regCat_right {m n : ℕ} (r : Reg m) (s : Reg n) (i : Fin n) :
    regCat r s (Fin.natAdd m i) = s i := by
  simp only [regCat]
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Padding to a register width at least the original width is injective. -/
theorem clause6_regPad_injective {w a : ℕ} (hle : a ≤ w) {q q' : Reg a}
    (h : regPad w a q = regPad w a q') : q = q' := by
  funext i
  have hi := congrFun h (Fin.castLE hle i)
  simp only [regPad] at hi
  have hcast : (↑(Fin.castLE hle i) : ℕ) = i.val := rfl
  have hlt : (↑(Fin.castLE hle i) : ℕ) < a := by omega
  rw [dif_pos hlt, dif_pos hlt] at hi
  simpa using! hi

/-- The unmarked row frame amplitude at an unmarked row and its own source index is the square
root of the corresponding transition entry. -/
theorem clause6_busyFrame_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (x y : I) (hx : x ∉ S) :
    unmarkedRowFrame P S (x, y) ⟨x, hx⟩ = ((Real.sqrt (P x y) : ℝ) : ℂ) := by
  simp only [unmarkedRowFrame, SzegedyIsometry, Matrix.of_apply]
  simp

/-- For an injective positive-width encoding, the encoded row record amplitude at the
concatenation of the two vertex encodings equals the square root transition amplitude. -/
theorem clause6_paidRow_amplitude {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (x y : I) (b : ℕ) (e : I → Reg b) (hb : 0 < b)
    (henc : Function.Injective e) :
    rowBasisRecordState P b (b + b) e x (regPad (b + b) (b + b) (regCat (e x) (e y)))
      = ((Real.sqrt (P x y) : ℝ) : ℂ) := by
  have hpos : ∀ y' : I,
      regPad (b + b) (b + b) (regCat (e x) (e y'))
        = regPad (b + b) (b + b) (regCat (e x) (e y)) → y' = y := by
    intro y' h
    have hpad : regCat (e x) (e y') = regCat (e x) (e y) :=
      clause6_regPad_injective (le_refl (b + b)) h
    have hcat : e y' = e y := by
      funext i
      have hi := congrFun hpad (Fin.natAdd b i)
      simp only [regCat] at hi
      rw [finSumFinEquiv_symm_apply_natAdd] at hi
      exact hi
    exact henc hcat
  have hket : ∀ y' : I,
      Ket (regPad (b + b) (b + b) (regCat (e x) (e y')))
        (regPad (b + b) (b + b) (regCat (e x) (e y))) = if y' = y then 1 else 0 := by
    intro y'
    by_cases h : y' = y
    · subst h
      rw [Qatlib.Foundations.PureStateMath.Ket]
      simp
    · have hne : ¬ (regPad (b + b) (b + b) (regCat (e x) (e y))
          = regPad (b + b) (b + b) (regCat (e x) (e y'))) := by
        intro hcon
        exact h (hpos y' hcon.symm)
      rw [Qatlib.Foundations.PureStateMath.Ket, if_neg hne, if_neg h]
  have hsum : (∑ y' : I, ((Real.sqrt (P x y') : ℝ) : ℂ) *
        Ket (regPad (b + b) (b + b) (regCat (e x) (e y')))
          (regPad (b + b) (b + b) (regCat (e x) (e y))))
      = ((Real.sqrt (P x y) : ℝ) : ℂ) := by
    calc
      (∑ y' : I, ((Real.sqrt (P x y') : ℝ) : ℂ) *
          Ket (regPad (b + b) (b + b) (regCat (e x) (e y')))
            (regPad (b + b) (b + b) (regCat (e x) (e y))))
          = ∑ y' : I, ((Real.sqrt (P x y') : ℝ) : ℂ) * (if y' = y then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro y' _
            rw [hket y']
      _ = ((Real.sqrt (P x y) : ℝ) : ℂ) := by
            rw [Finset.sum_eq_single y]
            · simp
            · intro y' _ hne
              rw [if_neg hne]
              simp
            · intro hh
              exact absurd (Finset.mem_univ y) hh
  unfold rowBasisRecordState
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact hsum

/-- For a matrix with nonnegative entries, the absolute value of the unmarked principal
quadratic form is bounded by the corresponding sum of entrywise amplitude norms. -/
theorem clause6_busy_quadratic_le {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (hp : ∀ i j, 0 ≤ P i j) (u : QState (busySpace S)) :
    ‖Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S) *ᵥ u)‖ ≤
      ∑ i : busySpace S, ∑ j : busySpace S, ‖u i‖ * P i.1 j.1 * ‖u j‖ := by
  have he : Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S) *ᵥ u)
      = ∑ i : busySpace S, ∑ j : busySpace S, star (u i) * (P i.1 j.1 : ℂ) * u j := by
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply, Matrix.mulVec,
      unmarkedPrincipal, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    ‖∑ i : busySpace S, ∑ j : busySpace S, star (u i) * (P i.1 j.1 : ℂ) * u j‖
        ≤ ∑ i : busySpace S, ‖∑ j : busySpace S, star (u i) * (P i.1 j.1 : ℂ) * u j‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ i : busySpace S, ∑ j : busySpace S, ‖star (u i) * (P i.1 j.1 : ℂ) * u j‖ := by
          apply Finset.sum_le_sum
          intro i _
          exact norm_sum_le _ _
    _ = ∑ i : busySpace S, ∑ j : busySpace S, ‖u i‖ * P i.1 j.1 * ‖u j‖ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hp _ _)]

/-- Under the symmetric chain gap hypotheses, the unmarked principal quadratic form is bounded
in modulus by `1 - δ * markedFraction S` times the squared state norm. -/
theorem clause6_busy_quadratic_gap {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : SymmetricChainGap P δ) (u : QState (busySpace S)) :
    ‖Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S) *ᵥ u)‖
      ≤ (1 - δ * markedFraction S) * (∑ i : busySpace S, ‖u i‖ ^ 2) := by
  have hp : ∀ i j, 0 ≤ P i j := fun i j => hgap.1.1 i j
  have h1 := clause6_busy_quadratic_le P S hp u
  have h2 := symmetric_chain_unmarked_real_quadratic_upper P S δ hδ.le hgap (fun i => ‖u i‖)
  exact h1.trans h2

/-- Embedding a finite real sum into the complex numbers equals the sum of the embedded terms. -/
theorem clause6_sum_ofReal {I : Type} [DecidableEq I] (s : Finset I) (f : I → ℝ) :
    Finset.sum s (fun i => Complex.ofReal (f i)) = Complex.ofReal (Finset.sum s f) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [ih]
      exact (Complex.ofReal_add _ _).symm

/-- A nonempty marked set in a nonempty finite state space has positive marked fraction. -/
theorem clause6_markedFraction_pos {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Finset I) (hS : S.Nonempty) : 0 < markedFraction S := by
  unfold markedFraction
  have hcard : (Fintype.card I : ℝ) > 0 := Nat.cast_pos.mpr Fintype.card_pos
  have hpos : (S.card : ℝ) > 0 := by
    have h1 : 1 ≤ S.card := Finset.card_pos.mpr hS
    exact_mod_cast h1
  exact div_pos hpos hcard

/-- With positive symmetric chain gap and a nonempty marked set, no nonzero unmarked source
state is fixed by the unmarked principal matrix. -/
theorem clause6_busy_no_plus_one {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hgap : SymmetricChainGap P δ) (hS : S.Nonempty) (u : QState (busySpace S)) :
    u ≠ 0 → unmarkedPrincipal P S *ᵥ u ≠ u := by
  intro hu
  by_contra hcon
  have hMu : unmarkedPrincipal P S *ᵥ u = u := hcon
  have hself : Qatlib.Foundations.PureStateMath.Inner u u
      = ∑ i : busySpace S, ((‖u i‖ ^ 2 : ℝ) : ℂ) := inner_self u
  have hre : (∑ i : busySpace S, ((‖u i‖ ^ 2 : ℝ) : ℂ))
      = Complex.ofReal (∑ i : busySpace S, (‖u i‖ ^ 2 : ℝ)) := by
    have h := clause6_sum_ofReal (Finset.univ : Finset (busySpace S)) (fun i => ‖u i‖ ^ 2)
    rw [h]
  have hnorm : ‖Qatlib.Foundations.PureStateMath.Inner u u‖ = ∑ i : busySpace S, ‖u i‖ ^ 2 := by
    rw [hself, hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hquad : Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S) *ᵥ u)
      = Qatlib.Foundations.PureStateMath.Inner u u := by rw [hMu]
  have hbound := clause6_busy_quadratic_gap P S δ hδ hδ1 hgap u
  have ha : 0 < markedFraction S := clause6_markedFraction_pos S hS
  have hnorm' : ‖Qatlib.Foundations.PureStateMath.Inner u ((unmarkedPrincipal P S) *ᵥ u)‖
      = ∑ i : busySpace S, ‖u i‖ ^ 2 := by rw [hquad]; exact hnorm
  have hkey : ∑ i : busySpace S, ‖u i‖ ^ 2
      ≤ (1 - δ * markedFraction S) * (∑ i : busySpace S, ‖u i‖ ^ 2) := by
    have h := hbound
    rw [hnorm'] at h
    exact h
  have hS0 : 0 ≤ ∑ i : busySpace S, ‖u i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hzero : ∑ i : busySpace S, ‖u i‖ ^ 2 = 0 := by
    have hpos : 0 < δ * markedFraction S := mul_pos hδ ha
    have hle : δ * markedFraction S * (∑ i : busySpace S, ‖u i‖ ^ 2) ≤ 0 := by
      have h := hkey
      have heq : (1 - δ * markedFraction S) * (∑ i : busySpace S, ‖u i‖ ^ 2)
          = (∑ i : busySpace S, ‖u i‖ ^ 2)
            - δ * markedFraction S * (∑ i : busySpace S, ‖u i‖ ^ 2) := by ring
      rw [heq] at h
      linarith
    by_contra hne
    have hSpos : 0 < ∑ i : busySpace S, ‖u i‖ ^ 2 :=
      lt_of_le_of_ne hS0 (Ne.symm hne)
    have hmul : 0 < δ * markedFraction S * (∑ i : busySpace S, ‖u i‖ ^ 2) :=
      mul_pos hpos hSpos
    linarith
  have huzero : u = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (f := fun j => ‖u j‖ ^ 2)
      (s := (Finset.univ : Finset (busySpace S)))
      (fun j _ => sq_nonneg (‖u j‖))).mp hzero i (Finset.mem_univ i)
    have : ‖u i‖ = 0 := by simpa using! hi
    exact norm_eq_zero.mp this
  exact hu huzero

/-- For a symmetric transition array, the unmarked principal matrix is Hermitian and possesses
an orthonormal eigenfamily indexed by the unmarked vertices. -/
theorem clause6_busy_eigenfamily {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (hsym : ∀ i j, P i j = P j i) :
    ∃ (hH : (unmarkedPrincipal P S).IsHermitian)
        (fam : busySpace S → QState (busySpace S)),
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (fam i) (fam j) = if i = j then 1 else 0) ∧
      (∀ i, unmarkedPrincipal P S *ᵥ fam i = (hermitianEigenvalue hH i : ℂ) • fam i) := by
  have hH : (unmarkedPrincipal P S).IsHermitian := unmarkedPrincipal_isHermitian P S hsym
  refine ⟨hH, fun j => hermitianEigenfamily hH j, ?_, ?_⟩
  · intro i j
    have hstar : ((hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ)ᴴ
        * (hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ)) = 1 := by
      have hU : (hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ)
          ∈ Matrix.unitaryGroup (busySpace S) ℂ := hH.eigenvectorUnitary.property
      have h := (Matrix.mem_unitaryGroup_iff').mp hU
      rwa [Matrix.star_eq_conjTranspose] at h
    have hfam : ∀ i k, hermitianEigenfamily hH i k
        = (hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ) k i := by
      intro i k
      show (hH.eigenvectorBasis i).ofLp k = _
      exact (Matrix.IsHermitian.eigenvectorUnitary_apply hH k i).symm
    simp only [Qatlib.Foundations.PureStateMath.Inner, dotProduct, Pi.star_apply]
    calc
      (∑ k : busySpace S, star (hermitianEigenfamily hH i k) * hermitianEigenfamily hH j k)
          = ((hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ)ᴴ
              * (hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ)) i j := by
            rw [Matrix.mul_apply]
            apply Finset.sum_congr rfl
            intro k _
            exact congrArg (fun z : ℂ =>
                z * (hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ) k j)
              (Matrix.conjTranspose_apply
                (hH.eigenvectorUnitary : Matrix (busySpace S) (busySpace S) ℂ) k i)
      _ = (1 : Matrix (busySpace S) (busySpace S) ℂ) i j :=
        congrArg (fun M : Matrix (busySpace S) (busySpace S) ℂ => M i j) hstar
      _ = if i = j then 1 else 0 := Matrix.one_apply
  · intro i
    have h := hH.mulVec_eigenvectorBasis i
    have hconv : (hH.eigenvalues i : ℂ) • ((hH.eigenvectorBasis i).ofLp)
        = hH.eigenvalues i • ((hH.eigenvectorBasis i).ofLp) := by
      symm
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) (hH.eigenvalues i) _
    show unmarkedPrincipal P S *ᵥ hermitianEigenfamily hH i
        = (hermitianEigenvalue hH i : ℂ) • hermitianEigenfamily hH i
    simp only [hermitianEigenvalue, hermitianEigenfamily]
    rw [hconv]
    exact h

/-- Paid walk access supplies an injective encoding, legal setup, update, and check words, and
the stated setup length, update length, check length, and workspace bounds. -/
theorem clause6_paidAccessClauses :
    ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (a w : ℕ) (enc : I → Reg a)
      (support : I → Finset I) (idx : ℕ → I) (nbr : I → ℕ → I)
      (setupWord updateWord checkWord : List FiniteGateCode) (C : ℕ → ℕ),
      HasPaidWalkAccess P S a w enc support idx nbr setupWord updateWord checkWord C →
      Function.Injective enc ∧
      finiteWordLegal w setupWord = true ∧
      finiteWordLegal w updateWord = true ∧
      finiteWordLegal w checkWord = true ∧
      (∀ (eps : ℝ), 0 < eps → setupWord.length ≤ C (Nat.ceil ((1 / eps) ^ 2) + 1)) ∧
      updateWord.length ≤ 2 * a + 2 ∧ checkWord.length ≤ 2 * a + 2 ∧ w ≤ 2 * a + 2 := by
  intro I instI instDec instNe P S a w enc support idx nbr setupWord updateWord checkWord C hpaid
  refine ⟨hpaid.1, hpaid.2.1, hpaid.2.2.1, hpaid.2.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro eps heps
    obtain ⟨x0⟩ := instNe
    obtain ⟨φ, hrun, htol, hcost⟩ := hpaid.2.2.2.2.1 x0 eps heps
    exact hcost
  · exact hpaid.2.2.2.2.2.2.2.1
  · exact hpaid.2.2.2.2.2.2.2.2.1
  · exact hpaid.2.2.2.2.2.2.2.2.2.1

/-- Under the gap hypotheses and a nonempty marked set, collects the encoded amplitudes,
unmarked frame identities, norm bound, orthonormal eigenfamily, absence of nonzero fixed
source states, and reversible embedded fixed states. -/
theorem clause6_busySpectrumContent :
    ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (δ : ℝ),
      0 < δ → δ ≤ 1 → SymmetricChainGap P δ → S.Nonempty →
      (∀ (x y : I) (hx : x ∉ S),
        unmarkedRowFrame P S (x, y) ⟨x, hx⟩ = ((Real.sqrt (P x y) : ℝ) : ℂ)) ∧
      (∀ (x y : I) (b : ℕ) (e : I → Reg b) (hb : 0 < b) (henc : Function.Injective e),
        rowBasisRecordState P b (b + b) e x (regPad (b + b) (b + b) (regCat (e x) (e y)))
          = ((Real.sqrt (P x y) : ℝ) : ℂ)) ∧
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (unmarkedRowFrame P S) ∧
      (unmarkedRowFrame P S)ᴴ * (SwapGate : Matrix (I × I) (I × I) ℂ) * (unmarkedRowFrame P S)
        = unmarkedPrincipal P S ∧
      ‖unmarkedPrincipal P S‖ ≤ 1 - δ * markedFraction S ∧
      (∃ (hH : (unmarkedPrincipal P S).IsHermitian)
          (fam : busySpace S → QState (busySpace S)),
        (∀ i j, Qatlib.Foundations.PureStateMath.Inner (fam i) (fam j) = if i = j then 1 else 0) ∧
        (∀ i, unmarkedPrincipal P S *ᵥ fam i = (hermitianEigenvalue hH i : ℂ) • fam i)) ∧
      (∀ u : QState (busySpace S), u ≠ 0 → unmarkedPrincipal P S *ᵥ u ≠ u) ∧
      (∀ (π : I → ℝ) (hπ : (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1) (hrev : IsReversible P π),
        SzegedyWalk P *ᵥ SzegedyEmbedState P π = SzegedyEmbedState P π) := by
  intro I instI instDec instNe P S δ hδ hδ1 hgap hS
  have hsym : ∀ i j, P i j = P j i := hgap.2.1
  have hP : IsTransitionMatrix P := hgap.1
  have hgram := unmarked_principal_gram_and_gap I P S δ hδ hδ1 hgap
  refine ⟨?_, ?_, hgram.1, hgram.2.1, hgram.2.2, ?_, ?_, ?_⟩
  · intro x y hx
    exact clause6_busyFrame_amplitude P S x y hx
  · intro x y b e hb henc
    exact clause6_paidRow_amplitude P x y b e hb henc
  · obtain ⟨hH, fam, hfam, hfam_eq⟩ := clause6_busy_eigenfamily P S hsym
    exact ⟨hH, fam, hfam, hfam_eq⟩
  · intro u hu
    exact clause6_busy_no_plus_one P S δ hδ hδ1 hgap hS u hu
  · intro π hπ hrev
    exact szegedyWalk_fixes_stationary P hP hrev

/-- Establishes `Clause6BusySpectrumTransport`, combining paid access bounds with the unmarked
source spectral content. -/
theorem clause6_busySpectrumTransport : Clause6BusySpectrumTransport :=
  ⟨clause6_paidAccessClauses, clause6_busySpectrumContent⟩

/-- Establishes `coreSpectralClause6Prop`, extending the basic walk spectral bundle by row
access legality and unmarked source spectral transport. -/
theorem coreSpectralClause6_endpoint : coreSpectralClause6Prop := by
  refine ⟨walk_spectral_clause6, ?_, clause6_busySpectrumTransport⟩
  intro I instI instDec instNe P S a w enc support idx nbr setupWord updateWord checkWord C hpaid
  exact ⟨hpaid.1, hpaid.2.1, hpaid.2.2.1, hpaid.2.2.2.1⟩

/-- Establishes `coreSpectralClause32Prop`, combining the amplification bundle with its phase
search schedule identity. -/
theorem coreSpectralClause32_endpoint : coreSpectralClause32Prop := by
  refine ⟨walk_spectral_clause32, ?_⟩
  intro M k t hM
  exact phase_search_fresh_access_ledger M k t hM

/-- Establishes `coreSpectralClause33Prop`, combining sine envelope bounds with coherent
filtering, leakage estimates, and repeated word resource counts. -/
theorem coreSpectralClause33_endpoint : coreSpectralClause33Prop := by
  refine ⟨walk_spectral_clause33, ?_⟩
  intro I J instI instDec instJ instDecJ W M k hM v c φ T η _hW hη hfar hv hc he hT hg
  have hM0 : 0 < M := by omega
  set a : ℝ := ∑ j ∈ T, ‖c j‖ ^ 2
  set ρ : ℝ := clause33Contraction M η
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun j _ => sq_nonneg _
  have ha1 : a ≤ 1 := by
    have hsub : (∑ j ∈ T, ‖c j‖ ^ 2) ≤ ∑ j, ‖c j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun j _ _ => sq_nonneg _)
    rwa [hc] at hsub
  have h1a : 0 ≤ 1 - a := by linarith
  have hρ0 : 0 ≤ ρ := by
    unfold ρ clause33Contraction
    positivity

  have hpass : ∀ j, j ∉ T → ‖clause33Pass M k hM0 (φ j)‖ ≤ ρ ^ k := by
    intro j hj
    have hgap := sin_envelope_zero_label_gap_bound M hM (φ j) η hη hfar (hg j hj)
    have hρ2 : ρ ^ 2 = 10 / ((M : ℝ)^2 * η^2)^2 := by
      unfold ρ clause33Contraction
      rw [div_pow, Real.sq_sqrt (by norm_num)]
    have hsq : ‖sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)‖ ^ 2 ≤ ρ ^ 2 := by
      rw [hρ2]; exact hgap
    have hroot := Real.sqrt_le_sqrt hsq
    have hle : ‖sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)‖ ≤ ρ := by
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hρ0] at hroot
      exact hroot
    rw [clause33Pass, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hle k

  have hmv : ∀ (f : J → QState I), W *ᵥ (∑ j, f j) = ∑ j, W *ᵥ f j := by
    intro f
    induction (Finset.univ : Finset J) using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, Matrix.mulVec_add, ih]
  have hdiag : W *ᵥ clause33FilteredState M k hM0 v c φ
      = ∑ j, (clause33Coeff M k hM0 c φ j *
          Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ))) • v j := by
    unfold clause33FilteredState clause33Coeff
    rw [hmv]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mulVec_smul, he j, smul_smul]

  have hleak : ‖toEuclidean_fromVec (clause33Leakage M k hM0 v c φ T)‖
      ≤ ρ ^ k * Real.sqrt (1 - a) := by
    have hnorm : ‖toEuclidean_fromVec (clause33Leakage M k hM0 v c φ T)‖ ^ 2
        = ∑ j, ‖clause33LeakCoeff M k hM0 c φ T j‖ ^ 2 := by
      unfold clause33Leakage
      exact degenerate_packet_norm_sq v (clause33LeakCoeff M k hM0 c φ T) hv
    have hsum : (∑ j, ‖clause33LeakCoeff M k hM0 c φ T j‖ ^ 2)
        = ∑ j, if j ∈ T then (0:ℝ) else ‖c j * clause33Pass M k hM0 (φ j)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j ∈ T <;> simp [clause33LeakCoeff, clause33Coeff, hj]
    have hbound : (∑ j, if j ∈ T then (0:ℝ) else ‖c j * clause33Pass M k hM0 (φ j)‖ ^ 2)
        ≤ ρ ^ (2 * k) * (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) := by
      have hstep : (∑ j, if j ∈ T then (0:ℝ) else ‖c j * clause33Pass M k hM0 (φ j)‖ ^ 2)
          = ∑ j, (if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) * ‖clause33Pass M k hM0 (φ j)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ T
        · simp [hj]
        · simp only [if_neg hj]
          rw [norm_mul, mul_pow]
      rw [hstep]
      have hle2 : (∑ j, (if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) * ‖clause33Pass M k hM0 (φ j)‖ ^ 2)
          ≤ ∑ j, (if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) * ρ ^ (2 * k) := by
        refine Finset.sum_le_sum (s := Finset.univ) fun j _ => ?_
        by_cases hj : j ∈ T
        · simp [hj]
        · simp only [hj, if_false]
          have hα : ‖clause33Pass M k hM0 (φ j)‖ ≤ ρ ^ k := hpass j hj
          have hα2 : ‖clause33Pass M k hM0 (φ j)‖ ^ 2 ≤ ρ ^ (2 * k) := by
            calc ‖clause33Pass M k hM0 (φ j)‖ ^ 2 ≤ (ρ ^ k) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hα 2
              _ = ρ ^ (2 * k) := by rw [← pow_mul]; congr 1; omega
          exact mul_le_mul_of_nonneg_left hα2 (by simp [hj])
      calc (∑ j, (if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) * ‖clause33Pass M k hM0 (φ j)‖ ^ 2)
          ≤ ∑ j, (if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) * ρ ^ (2 * k) := hle2
        _ = ρ ^ (2 * k) * (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    have hcomp : (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) = 1 - a := by
      have ht : (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) = a := by
        simp [a, Finset.sum_ite_mem]
      have hs : (∑ j, ‖c j‖ ^ 2) =
          (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) +
          ∑ j, if j ∈ T then 0 else ‖c j‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      rw [hc, ht] at hs
      linarith
    have hsq : ‖toEuclidean_fromVec (clause33Leakage M k hM0 v c φ T)‖ ^ 2
        ≤ ρ ^ (2 * k) * (1 - a) := by
      rw [hnorm, hsum]
      refine hbound.trans (by rw [hcomp] <;> ring)
    have hprod : (ρ ^ k * Real.sqrt (1 - a)) ^ 2 = ρ ^ (2 * k) * (1 - a) := by
      rw [mul_pow, Real.sq_sqrt h1a]
      ring
    have hnonneg : 0 ≤ ρ ^ k * Real.sqrt (1 - a) :=
      mul_nonneg (pow_nonneg hρ0 k) (Real.sqrt_nonneg _)
    nlinarith [sq_nonneg (‖toEuclidean_fromVec (clause33Leakage M k hM0 v c φ T)‖
      - ρ ^ k * Real.sqrt (1 - a))]

  have hsplit : clause33FilteredState M k hM0 v c φ
      = clause33TargetPart M k hM0 v c φ T + clause33Leakage M k hM0 v c φ T := by
    unfold clause33FilteredState clause33TargetPart clause33Leakage
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ T <;> simp [clause33TargetCoeff, clause33LeakCoeff, hj]
  have htwo : ‖toEuclidean_fromVec (clause33FilteredState M k hM0 v c φ -
      clause33ReflectedState M k hM0 v c φ T)‖ ≤ 2 * ρ ^ k * Real.sqrt (1 - a) := by
    have heq : clause33FilteredState M k hM0 v c φ - clause33ReflectedState M k hM0 v c φ T
        = (2 : ℂ) • clause33Leakage M k hM0 v c φ T := by
      rw [clause33ReflectedState, hsplit]
      module
    rw [heq, clause33_norm_smul]
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2]
    have hleak' := hleak
    nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg (1 - a))]

  have hzero : ∀ j ∈ T, clause33Pass M k hM0 (φ j)
      = sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k := by
    intro j hj
    have hφ : φ j = (⌊φ j + 1 / 2⌋ : ℤ) := by
      have hz : φ j - 0 - (⌊φ j + 1 / 2⌋ : ℤ) = 0 := by
        have hz' := hT j hj
        simp only [phaseDistance, sub_zero, abs_eq_zero] at hz'
        linarith
      linarith
    have hk := sin_envelope_kernel_int_add M 0 (⟨0, hM0⟩ : Fin M) (⌊φ j + 1 / 2⌋ : ℤ)
    have hz : sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)
        = sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) := by
      rw [hφ, show ((⌊φ j + 1 / 2⌋ : ℤ) : ℝ) = 0 + ((⌊φ j + 1 / 2⌋ : ℤ) : ℝ) by simp, hk]
    rw [clause33Pass, hz]
  have hatt : ∃ (s : ℂ), (∀ j ∈ T, clause33Pass M k hM0 (φ j) = s) ∧
      clause33TargetPart M k hM0 v c φ T = s • spectralTargetState v c T ∧ ‖s‖ ≤ 1 := by
    refine ⟨sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact hzero j hj
    · rw [clause33TargetPart]
      have hstep : (∑ j, clause33TargetCoeff M k hM0 c φ T j • v j)
          = (sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k) •
            (∑ j, (if j ∈ T then c j else 0) • v j) := by
        calc (∑ j, clause33TargetCoeff M k hM0 c φ T j • v j)
            = ∑ j, (if j ∈ T then c j * (sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k) else 0) • v j := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : j ∈ T
              · simp [clause33TargetCoeff, clause33Coeff, hj, hzero j hj]
              · simp [clause33TargetCoeff, hj]
            _ = ∑ j, (sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k) •
                ((if j ∈ T then c j else 0) • v j) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hj : j ∈ T
              · simp only [hj, if_true, if_pos]
                module
              · simp [hj]
            _ = (sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k) •
                (∑ j, (if j ∈ T then c j else 0) • v j) :=
              (Finset.smul_sum (s := Finset.univ)
                (f := fun j => (if j ∈ T then c j else 0) • v j)).symm
      rw [hstep]
      have hkey : (∑ j, (if j ∈ T then c j else 0) • v j) = ∑ j ∈ T, c j • v j := by
        have hmem := Finset.sum_ite_mem Finset.univ T (fun j => c j • v j)
        rw [Finset.univ_inter] at hmem
        rw [← hmem]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ T <;> simp [hj]
      rw [hkey]
      rfl
    · rw [norm_pow]
      have hk1 : ‖sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M)‖ ≤ 1 := by
        have hn := sin_envelope_kernel_normalized M 0 hM
        have hle : ‖sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M)‖ ^ 2
            ≤ ∑ z : Fin M, ‖sinEnvelopeKernel M 0 z‖ ^ 2 :=
          Finset.single_le_sum (f := fun z : Fin M => ‖sinEnvelopeKernel M 0 z‖ ^ 2)
            (s := Finset.univ) (fun z _ => sq_nonneg _) (Finset.mem_univ _)
        rw [hn] at hle
        nlinarith [sq_nonneg (‖sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M)‖ - 1)]
      exact pow_le_one₀ (by positivity) hk1

  have hfid : ‖toEuclidean_fromVec (clause33TargetPart M k hM0 v c φ T -
      spectralTargetState v c T)‖ ≤ 2 * Real.sqrt a := by
    obtain ⟨s, hs, hpart, hsmod⟩ := hatt
    have hdiff : clause33TargetPart M k hM0 v c φ T - spectralTargetState v c T
        = (s - 1) • spectralTargetState v c T := by
      rw [hpart]
      module
    rw [hdiff, clause33_norm_smul]
    have htnorm : ‖toEuclidean_fromVec (spectralTargetState v c T)‖ = Real.sqrt a := by
      have hsq := spectralTargetState_norm_sq v c T hv
      have h1 := Real.sqrt_le_sqrt (le_of_eq hsq)
      rw [Real.sqrt_sq (norm_nonneg _)] at h1
      have h2 := Real.sqrt_le_sqrt (le_of_eq hsq.symm)
      rw [Real.sqrt_sq (norm_nonneg _)] at h2
      have haeq : (∑ j ∈ T, ‖c j‖ ^ 2) = a := rfl
      rw [haeq] at h1 h2
      exact le_antisymm h1 h2
    rw [htnorm]
    have hsm : ‖s - 1‖ ≤ 2 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖1‖ := norm_sub_le _ _
        _ ≤ ‖s‖ + 1 := by rw [norm_one]
        _ ≤ 2 := by linarith [hsmod]
    nlinarith [mul_le_mul_of_nonneg_left hsm (Real.sqrt_nonneg a)]

  have hrep : ∀ (w : List (AdjointStep (Fin M × (Bool × I)))) (n : ℕ),
      adjointQueryCount (repeatWord w n) = n * adjointQueryCount w := by
    intro w n
    induction n with
    | zero => simp [repeatWord, adjointQueryCount]
    | succ n ih =>
      have hrw : repeatWord w (Nat.succ n) = w ++ repeatWord w n := by
        simp [repeatWord]
      rw [hrw, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, ih]
      ring
  have hrepg : ∀ (w : List (AdjointStep (Fin M × (Bool × I)))) (n : ℕ),
      adjointGateCount (repeatWord w n) = n * adjointGateCount w := by
    intro w n
    induction n with
    | zero => simp [repeatWord, adjointGateCount]
    | succ n ih =>
      have hrw : repeatWord w (Nat.succ n) = w ++ repeatWord w n := by
        simp [repeatWord]
      rw [hrw, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, ih]
      ring
  have hfwc := sin_envelope_forward_word_counts (I := I) M hM
  refine ⟨hdiag, hpass, hleak, htwo, hatt, hfid, ?_, ?_, ?_, ?_⟩
  · show adjointQueryCount (clause33ForwardWord (I := I) M k hM) = k * (M - 1)
    rw [clause33ForwardWord, hrep, hfwc.1]
  · show adjointGateCount (clause33ForwardWord (I := I) M k hM) = k * (2 * (M - 1) + 2)
    rw [clause33ForwardWord, hrepg, hfwc.2]
  · show adjointQueryCount (clause33InverseWord (I := I) M k hM) = k * (M - 1)
    rw [clause33InverseWord, adjointQueryCount_swapQueries, clause33ForwardWord, hrep, hfwc.1]
  · show adjointGateCount (clause33InverseWord (I := I) M k hM) = k * (2 * (M - 1) + 2)
    rw [clause33InverseWord, adjointGateCount_swapQueries, clause33ForwardWord, hrepg, hfwc.2]

/-- Establishes `coreSpectralTunableQueryProp`, combining tunable phase band filtering with the
strengthened band classifier requirement. -/
theorem coreSpectralTunableQuery_endpoint : coreSpectralTunableQueryProp := by
  refine ⟨walk_spectral_tunableGoal, ?_⟩
  intro J instF instD M bands phi eta hM hη hη1 hphi hbands hsep
  refine ⟨walk_spectral_tunableGoal.1 J M bands phi eta hM hη hη1 hphi hbands hsep, ?_⟩
  intro j b hb hphi hnot
  rcases hsep j b hb with hinside | houtside
  · refine ⟨b, hb, ?_, ?_⟩
    · linarith [hinside.1]
    · linarith [hinside.2]
  · exact False.elim (hnot houtside)

/-- Establishes `coreSpectralOptimizedTunableProp`, the optimized band reflection and
postselection bundle. -/
theorem coreSpectralOptimizedTunable_endpoint : coreSpectralOptimizedTunableProp :=
    walk_spectral_optGoal

/-- Establishes `coreSpectralClause36Prop`, adding normalized success branch stability and
failure branch trace norm bounds to the selective instrument estimates. -/
theorem coreSpectralClause36_endpoint : coreSpectralClause36Prop := by
  refine ⟨walk_spectral_clause36, ?_⟩
  intro O instO decO D E R J S ρ τ p ε hρ hτ hequal hp hε hε2 hdiff
  have hp0 : 0 < p := by linarith
  have hε0 : 0 ≤ ε := le_of_lt hε

  have hm := selective_joint_mass_error J S ρ τ hρ hτ hequal

  have hposA : 0 < (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re := by
    have h1 : 0 < p := hp0
    have h2 : p ≤ (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re := hp
    linarith

  have hpos : 0 < (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re := by
    have hlow := (abs_le.mp hm).1
    have hhigh := (abs_le.mp hm).2
    have hnn : Matrix.traceNorm (ρ - τ) / 2 ≤ ε / 2 := by
      have hn : 0 ≤ Matrix.traceNorm (ρ - τ) := Matrix.traceNorm_nonneg _
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith

  have hstab := sharp_selective_joint_stability O D E R J S ρ τ hρ hτ hequal hposA hpos
  have hmaxA : (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      ≤ max (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
        (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re := le_max_left _ _
  have hmax : p ≤ max (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re := le_trans hp hmaxA
  have hmain : ε / max (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re ≤ ε / p :=
    div_le_div_of_nonneg_left hε0 hp0 hmax

  have hbud := selective_joint_mass_budget J (clause36FailureSet S) ρ τ hρ hτ hequal
  have hmf := selective_joint_mass_error J (clause36FailureSet S) ρ τ hρ hτ hequal
  refine ⟨hpos, ?_, ?_, ?_⟩
  · have hmax0 : 0 ≤ max (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
        (Matrix.trace (tensorLeft (selectiveMap J S) τ)).re :=
      le_trans (le_of_lt hposA) hmaxA
    exact hstab.trans ((div_le_div_of_nonneg_right hdiff hmax0).trans hmain)
  · rw [tensorLeft_sub]
    have hnonneg : 0 ≤
        |(Matrix.trace (tensorLeft (selectiveMap J (clause36FailureSet S)) ρ)).re
            - (Matrix.trace (tensorLeft (selectiveMap J (clause36FailureSet S)) τ)).re| :=
      abs_nonneg _
    linarith
  · have hnn : Matrix.traceNorm (ρ - τ) / 2 ≤ ε / 2 := by
      have hn : 0 ≤ Matrix.traceNorm (ρ - τ) := Matrix.traceNorm_nonneg _
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have hnonneg : 0 ≤
        |(Matrix.trace (tensorLeft (selectiveMap J (clause36FailureSet S)) ρ)).re
            - (Matrix.trace (tensorLeft (selectiveMap J (clause36FailureSet S)) τ)).re| :=
      abs_nonneg _
    linarith

/-- For an orthonormal family, a diagonal filter equal to one on `T` and bounded by `C`
elsewhere preserves the target mass and bounds total filtered mass and leakage by the
complementary coefficient mass. -/
theorem clause37_diagonal_filter_bounds_homogeneous
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (v : J → QState I) (c α : J → ℂ) (T : Finset J) (C : ℝ)
    (hv : ∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0)
    (hC : 0 ≤ C)
    (hfix : ∀ j ∈ T, α j = 1) (hbound : ∀ j, j ∉ T → ‖α j‖ ≤ C) :
    (∑ j ∈ T, ‖c j‖ ^ 2) ≤ ‖toEuclidean_fromVec (∑ j, (c j * α j) • v j)‖ ^ 2 ∧
      ‖toEuclidean_fromVec (∑ j, (c j * α j) • v j)‖ ^ 2 ≤
        (∑ j ∈ T, ‖c j‖ ^ 2) +
          C ^ 2 * ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2)) ∧
      ‖toEuclidean_fromVec (∑ j, (c j * α j) • v j - spectralTargetState v c T)‖ ≤
        C * Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2)) := by
  set a : ℝ := ∑ j ∈ T, ‖c j‖ ^ 2
  set s : ℝ := ∑ j, ‖c j‖ ^ 2
  set z : QState I := ∑ j, (c j * α j) • v j
  let d : J → ℂ := fun j => if j ∈ T then 0 else c j * α j
  have hz : z - spectralTargetState v c T = ∑ j, d j • v j := by
    have ht : spectralTargetState v c T = ∑ j, (if j ∈ T then c j else 0) • v j := by
      simp [spectralTargetState, ite_smul, Finset.sum_ite_mem]
    rw [ht, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ T
    · simp [d, hj, hfix j hj]
    · simp [d, hj]
  have ha : 0 ≤ a := Finset.sum_nonneg fun j _ => sq_nonneg _
  have has : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsplit : (∑ j, ‖c j * α j‖ ^ 2) = a + ∑ j, ‖d j‖ ^ 2 := by
    have ht : a = ∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0 := by
      simp [a, Finset.sum_ite_mem]
    rw [ht, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ T
    · simp [d, hj, hfix j hj]
    · simp [d, hj]
  have hcomp : (∑ j, if j ∈ T then 0 else ‖c j‖ ^ 2) = s - a := by
    have ht : a = ∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0 := by
      simp [a, Finset.sum_ite_mem]
    have hs : s =
        (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) +
        ∑ j, if j ∈ T then 0 else ‖c j‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    rw [← ht] at hs
    linarith
  have hbad : (∑ j, ‖d j‖ ^ 2) ≤ C ^ 2 * (s - a) := by
    rw [← hcomp, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ T
    · simp [d, hj]
    · simp only [d, if_neg hj, norm_mul, mul_pow]
      simpa only [mul_comm] using! mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hbound j hj) 2) (sq_nonneg ‖c j‖)
  have hnorm : ‖toEuclidean_fromVec z‖ ^ 2 = a + ∑ j, ‖d j‖ ^ 2 := by
    rw [degenerate_packet_norm_sq v _ hv, hsplit]
  have hsa : a ≤ s := by
    have hsub : (∑ j ∈ T, ‖c j‖ ^ 2) ≤ ∑ j, ‖c j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun j _ _ => sq_nonneg _)
    exact hsub
  refine ⟨by rw [hnorm]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => sq_nonneg _),
    by rw [hnorm]; linarith, ?_⟩
  have he : ‖toEuclidean_fromVec (z - spectralTargetState v c T)‖ ^ 2 ≤
      C ^ 2 * (s - a) := by rw [hz, degenerate_packet_norm_sq v _ hv]; exact hbad
  have hs := Real.sq_sqrt (by linarith : 0 ≤ s - a)
  nlinarith [norm_nonneg (toEuclidean_fromVec (z - spectralTargetState v c T)),
    mul_nonneg hC (Real.sqrt_nonneg (s - a))]

/-- Establishes `coreSpectralClause37Prop`, extending degenerate phase detection estimates to
homogeneous coefficient families. -/
theorem coreSpectralClause37_endpoint : coreSpectralClause37Prop := by
  refine ⟨walk_spectral_clause37, ?_⟩
  intro I J instI instDec instJ instDecJ M k hM v c φ T η W hW hη hv he hT hg

  have hf : ∀ j ∈ T, (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k = 1 := by
    intro j hj
    have hk := qpeKernel_zero_distance M (by omega) (φ j) (hT j hj)
    rw [hk]
    simp [Qatlib.Foundations.PureStateMath.Ket]

  have hb : ∀ j, j ∉ T → ‖(qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k‖ ≤
      (1 / (2 * (M : ℝ) * η)) ^ k := by
    intro j hj
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (phase_detection_zero_label_gap_bound M (by omega) (φ j) η hη (hg j hj)) k
  have hC : 0 ≤ (1 / (2 * (M : ℝ) * η)) ^ k := by positivity
  have hhom := clause37_diagonal_filter_bounds_homogeneous v c
    (fun j => (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) T
    ((1 / (2 * (M : ℝ) * η)) ^ k) hv hC hf hb

  have hoff : 0 ≤ (∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2) := by
    have hsub : (∑ j ∈ T, ‖c j‖ ^ 2) ≤ ∑ j, ‖c j‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T) (fun j _ _ => sq_nonneg _)
    linarith

  have hnorm : ‖toEuclidean_fromVec (∑ j, c j • v j)‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 :=
    degenerate_packet_norm_sq v c hv
  have hsqrt : Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2))
      ≤ ‖toEuclidean_fromVec (∑ j, c j • v j)‖ := by
    have hs := Real.sq_sqrt hoff
    have hsq : (Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2))) ^ 2
        = (∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2) := Real.sq_sqrt hoff
    have ha0 : 0 ≤ (∑ j ∈ T, ‖c j‖ ^ 2) := Finset.sum_nonneg fun j _ => sq_nonneg _
    have h2 : (Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2))) ^ 2
        ≤ ‖toEuclidean_fromVec (∑ j, c j • v j)‖ ^ 2 := by
      rw [hnorm]
      linarith
    have h1 := Real.sqrt_le_sqrt h2
    rw [Real.sqrt_sq (Real.sqrt_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1
    exact h1
  refine ⟨hhom.1, hhom.2.1, hhom.2.2, ?_, ?_⟩
  · have h1 : ‖toEuclidean_fromVec
          (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j -
            spectralTargetState v c T)‖
        ≤ (1 / (2 * (M : ℝ) * η)) ^ k *
          Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2)) := hhom.2.2
    have h2 : (1 / (2 * (M : ℝ) * η)) ^ k *
          Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2))
        ≤ (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖ :=
      mul_le_mul_of_nonneg_left hsqrt hC
    exact h1.trans h2
  · have h1 : ‖toEuclidean_fromVec
          (∑ j, (c j * (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j -
            spectralTargetState v c T)‖
        ≤ (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖ := by
      have h2 : (1 / (2 * (M : ℝ) * η)) ^ k *
          Real.sqrt ((∑ j, ‖c j‖ ^ 2) - (∑ j ∈ T, ‖c j‖ ^ 2))
        ≤ (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖ :=
        mul_le_mul_of_nonneg_left hsqrt hC
      exact hhom.2.2.trans h2
    have h2 : (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖
        ≤ 2 * (1 / (2 * (M : ℝ) * η)) ^ k * ‖toEuclidean_fromVec (∑ j, c j • v j)‖ := by
      have hn : 0 ≤ ‖toEuclidean_fromVec (∑ j, c j • v j)‖ := norm_nonneg _
      nlinarith
    exact h1.trans h2

/-- For a positive second argument, the Euclidean step count is one plus the step count after a
single remainder operation. -/
theorem cfSteps_eq {a b : ℕ} (hb : 1 ≤ b) : cfSteps a b = 1 + cfSteps b (a % b) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp [cfSteps]

/-- Each Fibonacci number is at most the next Fibonacci number. -/
theorem fib_succ_mono (n : ℕ) : fib n ≤ fib (n + 1) := by
  induction n with
  | zero => simp [fib]
  | succ n ih =>
    cases n with
    | zero => simp [fib]
    | succ n =>
      show fib (Nat.succ (Nat.succ n)) ≤ fib (Nat.succ (Nat.succ (Nat.succ n)))
      simp only [fib]
      exact Nat.le_add_right _ _

/-- For a positive denominator `b`, the Fibonacci number indexed by `cfSteps a b + 1` is at most
`b`. -/
theorem cfSteps_fib {a b : ℕ} (hb : 1 ≤ b) : fib (cfSteps a b + 1) ≤ b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hm : a % b = 0
    · have hz : cfSteps a b = 1 := by rw [cfSteps_eq hb]; simp [cfSteps, hm]
      rw [hz]
      simpa [fib] using! hb
    · have hmp : 1 ≤ a % b := by omega
      have hmb : a % b < b := Nat.mod_lt _ (by omega : 0 < b)
      have hrem : b % (a % b) < b := by
        have h := Nat.mod_lt b (by omega : 0 < a % b)
        omega
      have h1 : fib (cfSteps b (a % b) + 1) ≤ a % b := ih (a % b) hmb (a := b) hmp
      by_cases hz2 : b % (a % b) = 0
      · have hz3 : cfSteps (a % b) (b % (a % b)) = 0 := by
          simp [cfSteps, hz2]
        have hsteps2 : cfSteps b (a % b) = 1 + cfSteps (a % b) (b % (a % b)) :=
          cfSteps_eq hmp
        have hsteps : cfSteps a b = 1 + cfSteps b (a % b) := cfSteps_eq hb
        rw [hsteps, hsteps2, hz3]
        simp [fib]
        omega
      · have hz2p : 1 ≤ b % (a % b) := by omega
        have h2 : fib (cfSteps (a % b) (b % (a % b)) + 1) ≤ b % (a % b) :=
          ih (b % (a % b)) hrem (a := a % b) hz2p
        have hrel : b ≥ (a % b) + (b % (a % b)) := by
          have hdiv := Nat.div_add_mod b (a % b)
          have hpos : 0 < b / (a % b) :=
            Nat.div_pos (by omega : a % b ≤ b) (by omega : 0 < a % b)
          have hmm : (a % b) * (b / (a % b)) ≥ a % b := by
            have := Nat.mul_le_mul_left (a % b) hpos
            simpa using! this
          omega
        have hsteps : cfSteps a b = 1 + cfSteps b (a % b) := cfSteps_eq hb
        have hsteps2 : cfSteps b (a % b) = 1 + cfSteps (a % b) (b % (a % b)) :=
          cfSteps_eq hmp
        have h2' : fib (cfSteps b (a % b)) ≤ b % (a % b) := by
          have heq : cfSteps (a % b) (b % (a % b)) + 1 = cfSteps b (a % b) := by omega
          rw [← heq]
          exact h2
        have hsum : fib (cfSteps b (a % b) + 1) + fib (cfSteps b (a % b)) ≤ b := by
          calc fib (cfSteps b (a % b) + 1) + fib (cfSteps b (a % b))
              ≤ (a % b) + (b % (a % b)) := Nat.add_le_add h1 h2'
          _ ≤ b := hrel
        have hfib : fib (cfSteps a b + 1)
            = fib (cfSteps b (a % b) + 1) + fib (cfSteps b (a % b)) := by
          have heq : cfSteps a b + 1 = cfSteps b (a % b) + 2 := by omega
          rw [heq]
          show fib (cfSteps b (a % b) + 2)
            = fib (cfSteps b (a % b) + 1) + fib (cfSteps b (a % b))
          rfl
        rw [hfib]
        exact hsum

/-- The Fibonacci number `fib (n + 1)` is at least `2 ^ (n / 2)`. -/
theorem fib_pow_two_le : ∀ n : ℕ, 2 ^ (n / 2) ≤ fib (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [fib]
    | succ m =>
      cases m with
      | zero => simp [fib]
      | succ k =>
        have hdiv : (Nat.succ (Nat.succ k)) / 2 = k / 2 + 1 := by omega
        have hmono : fib (k + 1) ≤ fib (k + 2) := fib_succ_mono (k + 1)
        have hrec : fib (k + 2) + fib (k + 1) ≤ fib (k + 3) := by
          show fib (k + 2) + fib (k + 1) ≤ fib (k + 3)
          have heq : fib (k + 3) = fib (k + 2) + fib (k + 1) := rfl
          rw [heq]
        calc
          2 ^ (Nat.succ (Nat.succ k) / 2) = 2 ^ (k / 2 + 1) := by rw [hdiv]
          _ = 2 ^ (k / 2) * 2 := by rw [pow_succ]
          _ = 2 * 2 ^ (k / 2) := Nat.mul_comm _ _
          _ ≤ 2 * fib (k + 1) := Nat.mul_le_mul_left _ (ih k (by omega))
          _ ≤ fib (k + 2) + fib (k + 1) := by omega
          _ ≤ fib (k + 3) := hrec

/-- If `1 ≤ q ≤ 2 ^ (l + 2)`, then the Euclidean step count `cfSteps p q` is at most `2 * l +
5`. -/
theorem cfSteps_le {p q l : ℕ} (h1 : 1 ≤ q) (h2 : q ≤ 2 ^ (l + 2)) :
    cfSteps p q ≤ 2 * l + 5 := by
  have hfib : fib (cfSteps p q + 1) ≤ q := cfSteps_fib (a := p) (b := q) h1
  have hq : fib (cfSteps p q + 1) ≤ 2 ^ (l + 2) := hfib.trans h2
  have hexp : 2 ^ (cfSteps p q / 2) ≤ fib (cfSteps p q + 1) := fib_pow_two_le _
  have hpow : 2 ^ (cfSteps p q / 2) ≤ 2 ^ (l + 2) := hexp.trans hq
  have hlog : cfSteps p q / 2 ≤ l + 2 := by
    have hmono := Nat.log_mono (c := 2) (b := 2) (m := 2 ^ (cfSteps p q / 2))
      (n := 2 ^ (l + 2)) (by omega) (by omega) hpow
    have h1' : Nat.log 2 (2 ^ (cfSteps p q / 2)) = cfSteps p q / 2 :=
      Nat.log_pow (b := 2) (by omega) _
    have h2' : Nat.log 2 (2 ^ (l + 2)) = l + 2 := Nat.log_pow (b := 2) (by omega) _
    omega
  have hlt : cfSteps p q / 2 < l + 3 := by omega
  have hlt' : cfSteps p q < (l + 3) * 2 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp hlt
  omega

/-- For a denominator between one and `2 ^ (l + 2)`, combines the Fibonacci lower growth
estimate with the bound `cfSteps p q ≤ 2 * l + 5`. -/
theorem clause39_continuedFraction :
    ∀ (p q l : ℕ) (h1 : 1 ≤ q) (h2 : q ≤ 2 ^ (l + 2)),
      fib (cfSteps p q + 1) ≤ q ∧ cfSteps p q ≤ 2 * l + 5 := by
  intro p q l h1 h2
  exact ⟨cfSteps_fib (a := p) (b := q) h1, cfSteps_le (p := p) (q := q) (l := l) h1 h2⟩

/-- Establishes `coreSpectralClause39Prop`, combining phase estimation, uniform sequence
resource counts, and continued fraction step bounds. -/
theorem coreSpectralClause39_endpoint : coreSpectralClause39Prop := by
  refine ⟨walk_spectral_clause39, ?_, clause39_continuedFraction⟩
  intro M s l ε δ I instI instDec U ψ φ hM hε hε1 hδ hδ1 hMeq hδeq hs heig

  have hcount := counted_offgrid_qpe_clean_flag M (by omega) U ψ
  have hcc := phaseCompileCircuit_counts (countedPhaseCircuit (I := I) M)

  have hlen : (clause39UniformWord (I := I) M s).length
      = 2 * s * (phaseCompileCircuit (countedPhaseCircuit (I := I) M)).length := by
    rw [clause39UniformWord, clause39_repeat_length] <;> ring

  have hq : adjointQueryCount (clause39UniformWord (I := I) M s) = 2 * s * (M - 1) := by
    rw [clause39UniformWord, clause39_repeat_queryCount, hcc.1, hcount.2.1] <;> ring

  have hg : adjointGateCount (clause39UniformWord (I := I) M s) = 2 * s * (2 * (M - 1) + 2) := by
    rw [clause39UniformWord, clause39_repeat_gateCount, hcc.2, hcount.2.2.1] <;> ring

  have hprec : (1 / (M : ℝ)) = ((2 : ℝ) ^ (-(l + 2 : ℕ) : ℤ)) := by
    rw [hMeq, one_div, _root_.zpow_neg, zpow_natCast, Nat.cast_pow]
    norm_num

  have hfail := walk_spectral_clause39.2.2 δ ε hδ hδ1 hε hε1 I U ψ φ heig s hs
  refine ⟨hlen, hq, hg, hprec, hfail⟩

end Qatlib.Concepts.WalkSearch.FrameSpectral
