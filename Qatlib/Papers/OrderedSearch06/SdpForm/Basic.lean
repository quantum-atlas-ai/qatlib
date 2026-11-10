/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch06.LaurentDefs
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.ExactLaurentProgramIffSDPTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialCircuit
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialTransitionKernelTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiInvariantProgramCharacterizationTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.TiPolynomialActualAlgorithmTran
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.SdpForm

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Papers.OrderedSearch06.LaurentDefs

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

def revFin (N : ℕ) : Fin N ≃ Fin N where
  toFun i := ⟨N - 1 - i.val, by have := i.isLt; omega⟩
  invFun i := ⟨N - 1 - i.val, by have := i.isLt; omega⟩
  left_inv i := by ext; simp only []; omega
  right_inv i := by ext; simp only []; omega

@[simp] theorem revFin_val (N : ℕ) (i : Fin N) : ((revFin N i : Fin N) : ℕ) = N - 1 - i.val := rfl

theorem revFin_involutive (N : ℕ) (i : Fin N) : revFin N (revFin N i) = i := by
  apply Fin.ext
  simp only [revFin_val]
  have hi := i.isLt
  omega

def counteridentity (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => if j = revFin N i then 1 else 0

theorem counteridentity_transpose (N : ℕ) : (counteridentity N)ᵀ = counteridentity N := by
  ext i j
  rw [Matrix.transpose_apply]
  simp only [counteridentity, Matrix.of_apply]
  by_cases h' : j = revFin N i
  · have h : i = revFin N j := by rw [h', revFin_involutive]
    rw [if_pos h, if_pos h']
  · have h : ¬ (i = revFin N j) := by
      intro hh
      apply h'
      have hh' : revFin N i = j := by rw [hh, revFin_involutive]
      exact hh'.symm
    rw [if_neg h, if_neg h']

theorem counteridentity_conjTranspose (N : ℕ) : (counteridentity N)ᴴ = counteridentity N := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  simp only [counteridentity, Matrix.of_apply]
  by_cases h' : i = revFin N j
  · have h : j = revFin N i := by rw [h', revFin_involutive]
    rw [if_pos h', if_pos h]
    simp
  · have h : ¬ (j = revFin N i) := by
      intro hh
      apply h'
      have hh' : revFin N j = i := by rw [hh, revFin_involutive]
      exact hh'.symm
    rw [if_neg h', if_neg h]
    simp

theorem counteridentity_mul_self (N : ℕ) :
    counteridentity N * counteridentity N = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [counteridentity, Matrix.of_apply]
  rw [Finset.sum_eq_single (revFin N i)]
  · rw [if_pos rfl, one_mul, revFin_involutive]
    by_cases hij : j = i
    · rw [if_pos hij, if_pos hij.symm]
    · rw [if_neg hij, if_neg (fun h => hij h.symm)]
  · intro k _ hk
    rw [if_neg hk, zero_mul]
  · intro hmem
    simp at hmem

theorem counteridentity_isRealSymmetric (N : ℕ) : IsRealSymmetric (counteridentity N) := by
  refine ⟨counteridentity_transpose N, ?_⟩
  intro i j
  simp only [counteridentity, Matrix.of_apply]
  split_ifs <;> simp

theorem counteridentity_mul_apply (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    (counteridentity N * X * counteridentity N) i j = X (revFin N i) (revFin N j) := by
  classical
  simp only [Matrix.mul_apply, counteridentity, Matrix.of_apply]
  have hinner : ∀ b : Fin N,
      (∑ k : Fin N, (if k = revFin N i then 1 else 0) * X k b) = X (revFin N i) b := by
    intro b
    rw [Finset.sum_eq_single (revFin N i)]
    · simp
    · intro k _ hk
      simp [hk]
    · intro hmem
      simp at hmem
  simp only [hinner]
  rw [Finset.sum_eq_single (revFin N j)]
  · rw [revFin_involutive]
    simp
  · intro b _ hb
    have hjb : ¬ (j = revFin N b) := by
      intro h
      apply hb
      rw [h, revFin_involutive]
    simp [hjb]
  · intro hmem
    simp at hmem

theorem counteridentity_conj_isRealSymmetric (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ)
    (hX : IsRealSymmetric X) : IsRealSymmetric (counteridentity N * X * counteridentity N) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, hX.1]
    simp only [counteridentity_transpose]
    rw [Matrix.mul_assoc]
  · intro i j
    rw [counteridentity_mul_apply]
    exact hX.2 _ _

theorem counteridentity_conj_trace (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) :
    (counteridentity N * X * counteridentity N).trace = X.trace := by
  simp only [Matrix.trace, Matrix.diag_apply, counteridentity_mul_apply]
  exact (revFin N).sum_comp (fun i => X i i)

theorem counteridentity_conj_genTrace (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (j : ℤ) :
    genTrace (counteridentity N * X * counteridentity N) j = genTrace X (-j) := by
  classical
  unfold genTrace
  simp only [counteridentity_mul_apply]
  have hprod (f : Fin N → Fin N → ℂ) :
      (∑ a : Fin N, ∑ b : Fin N, f a b) = ∑ p : Fin N × Fin N, f p.1 p.2 := by
    rw [← Finset.sum_product']
    simp
  rw [hprod (fun a b => if ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = j then X (revFin N a) (revFin N b) else 0)]
  rw [hprod (fun a b => if ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = -j then X a b else 0)]
  refine Fintype.sum_equiv ((revFin N).prodCongr (revFin N)) _ _ ?_
  rintro ⟨a, b⟩
  show (if ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) = j then X (revFin N a) (revFin N b) else 0)
      = (if (((revFin N b : Fin N) : ℕ) : ℤ) - (((revFin N a : Fin N) : ℕ) : ℤ) = -j
          then X (revFin N a) (revFin N b) else 0)
  refine if_congr ?_ rfl rfl
  have ha : (a : ℕ) < N := a.isLt
  have hb : (b : ℕ) < N := b.isLt
  simp only [revFin_val]
  constructor
  · intro h
    omega
  · intro h
    omega

theorem genTrace_neg_eq_of_transpose_eq {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ)
    (h : Qᵀ = Q) (j : ℤ) : genTrace Q (-j) = genTrace Q j := by
  rw [← genTrace_transpose, h]

def SolvesPaperSDP (N k : ℕ) (Q : ℕ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (∀ t, (Q t).PosSemidef) ∧
  (∀ t, IsRealSymmetric (Q t)) ∧
  (∀ i j, Q 0 i j = (N : ℂ)⁻¹) ∧
  (∀ t ∈ Finset.Icc 0 k, (Q t).trace = 1) ∧
  (Q k = (N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)) ∧
  (∀ t ∈ Finset.Icc 1 k, ∀ i ∈ Finset.Ioo (0 : ℤ) (N : ℤ),
    genTrace (Q t) i + (-1 : ℂ) ^ t * genTrace (Q t) (i - (N : ℤ))
      = genTrace (Q (t - 1)) i + (-1 : ℂ) ^ t * genTrace (Q (t - 1)) (i - (N : ℤ)))

def PaperSDP (N k : ℕ) : Prop := ∃ Q : ℕ → Matrix (Fin N) (Fin N) ℂ, SolvesPaperSDP N k Q

def PaperPolynomialProgram (N k : ℕ) : Prop :=
  ∃ Q : ℕ → ℤ → ℂ,
    (∀ t ∈ Finset.Icc 0 k, PaperNonnegative N (Q t)) ∧
    (∀ t ∈ Finset.Icc 0 k, PaperSymmetric (Q t)) ∧
    (∀ z : ℂ, paperLaurent N (Q 0) z = paperLaurent N (paperHermite N) z) ∧
    (∀ t ∈ Finset.Icc 1 k, ∀ z : ℂ, z ^ N = (-1 : ℂ) ^ t →
      paperLaurent N (Q t) z = paperLaurent N (Q (t - 1)) z) ∧
    (∀ z : ℂ, paperLaurent N (Q k) z = 1) ∧
    (∀ t ∈ Finset.Icc 0 k, Q t 0 = 1)

theorem lemma3_counteridentity_invariance (N k : ℕ)
    (Q : ℕ → Matrix (Fin N) (Fin N) ℂ) (h : SolvesPaperSDP N k Q) :
    SolvesPaperSDP N k (fun t => counteridentity N * Q t * counteridentity N) := by
  obtain ⟨hPSD, hreal, h0, htr, hk, hstep⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simpa only [counteridentity_conjTranspose] using
      (Matrix.PosSemidef.mul_mul_conjTranspose_same (hPSD t) (counteridentity N))
  · intro t
    exact counteridentity_conj_isRealSymmetric N (Q t) (hreal t)
  · intro i j
    simp only [counteridentity_mul_apply, h0]
  · intro t ht
    rw [counteridentity_conj_trace, htr t ht]
  · change counteridentity N * Q k * counteridentity N = (N : ℂ)⁻¹ • 1
    rw [hk]
    calc counteridentity N * ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)) * counteridentity N
        = (N : ℂ)⁻¹ • (counteridentity N * (1 : Matrix (Fin N) (Fin N) ℂ) * counteridentity N) := by
          rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ) := by
          rw [Matrix.mul_one, counteridentity_mul_self]
  · intro t ht i hi
    have h1 : genTrace (counteridentity N * Q t * counteridentity N) i = genTrace (Q t) i := by
      rw [counteridentity_conj_genTrace, genTrace_neg_eq_of_transpose_eq (Q t) (hreal t).1]
    have h2 : genTrace (counteridentity N * Q t * counteridentity N) (i - (N : ℤ)) =
        genTrace (Q t) (i - (N : ℤ)) := by
      rw [counteridentity_conj_genTrace, genTrace_neg_eq_of_transpose_eq (Q t) (hreal t).1]
    have h3 : genTrace (counteridentity N * Q (t - 1) * counteridentity N) i = genTrace (Q (t - 1)) i := by
      rw [counteridentity_conj_genTrace, genTrace_neg_eq_of_transpose_eq (Q (t-1)) (hreal (t-1)).1]
    have h4 : genTrace (counteridentity N * Q (t - 1) * counteridentity N) (i - (N : ℤ)) =
        genTrace (Q (t - 1)) (i - (N : ℤ)) := by
      rw [counteridentity_conj_genTrace, genTrace_neg_eq_of_transpose_eq (Q (t-1)) (hreal (t-1)).1]
    rw [h1, h2, h3, h4]
    exact hstep t ht i hi

abbrev PaperLaurentProgram (N k : ℕ) [NeZero N] : Prop := exactTIProgram N k

def PaperInvariantAlgorithm (N k : ℕ) [NeZero N] : Prop :=
  ∃ U : ℕ → Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ,
    (∀ t ∈ Finset.Icc 1 k, U t ∈ Matrix.unitaryGroup (Fin (2 * N)) ℂ ∧
      tiTranslation N * U t = U t * tiTranslation N) ∧
    ∀ j : Fin (2 * N),
      1 ≤ Complex.normSq (Qatlib.Foundations.PureStateMath.Inner (tiPolynomialReadoutVector N k (ospFun N j))
        (Run (PhaseOracle (ospBit N j)) (tiInvariantQueryWord N k U) (Uniform (Fin (2 * N)))))

def paperTransitionFamily (N : ℕ) (p : ℕ → Fin N → ℂ) :
    ℕ → Matrix (Fin (2 * N)) (Fin (2 * N)) ℂ :=
  fun t => tiPolynomialTransition N t (p (t - 1)) (p t)

theorem invariantWord_eq_queryWord (N k : ℕ) (p : ℕ → Fin N → ℂ) :
    tiInvariantQueryWord N k (paperTransitionFamily N p) = tiPolynomialQueryWord N k p := by
  simp only [tiInvariantQueryWord, tiPolynomialQueryWord, paperTransitionFamily]
  refine congrArg (fun f => List.flatMap f (List.range k)) ?_
  funext r
  rw [show r + 1 - 1 = r from by omega]

theorem algorithm_implies_program (N k : ℕ) [NeZero N]
    (h : PaperInvariantAlgorithm N k) : PaperLaurentProgram N k := by
  obtain ⟨U, hU, hsucc⟩ := h
  have hch := tiInvariantProgramCharacterization N k 0 U hU (fun j => by
    have := hsucc j
    simpa using this)
  have hsdp : tiSDPFeasible N k 0 := hch.2.2.2.2.2
  exact (exactLaurentProgramIffSDP N k).mpr hsdp

theorem program_implies_algorithm (N k : ℕ) [NeZero N]
    (h : PaperLaurentProgram N k) : PaperInvariantAlgorithm N k := by
  obtain ⟨p, hp0, hnorm1, hnorm0, hpk0, hmatch⟩ :=
    exactLaurentProgram_to_polyConditions N k h
  have hnormall : ∀ t ∈ Finset.Icc 0 k, ∑ i, Complex.normSq (p t i) = 1 := by
    intro t ht
    rcases Finset.mem_Icc.mp ht with ⟨-, hk⟩
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · subst ht0
      exact hnorm0
    · exact hnorm1 t (Finset.mem_Icc.mpr ⟨htpos, hk⟩)
  have hta := tiPolynomialActualAlgorithm N k p hp0 hnormall hmatch
  refine ⟨paperTransitionFamily N p, ?_, ?_⟩
  · intro t ht
    have hpos : 0 < t := by have := (Finset.mem_Icc.mp ht).1; omega
    have hker := tiPolynomialTransitionKernel.2 N t hpos (p (t - 1)) (p t)
      (fun z hz => (hmatch t ht z hz).symm)
    exact ⟨hker.2.1, hker.2.2.1⟩
  · intro j
    have hperj := hta.2.2.2.2.2.2.2.2.2.2 j
    obtain ⟨-, -, hC, -, -, hF, -⟩ := hperj
    rw [invariantWord_eq_queryWord]
    rw [← hC]
    rw [hF]
    simpa using hpk0

theorem theorem1_algorithm_iff_laurentProgram (N k : ℕ) [NeZero N] :
    PaperInvariantAlgorithm N k ↔ PaperLaurentProgram N k :=
  ⟨algorithm_implies_program N k, program_implies_algorithm N k⟩

theorem theorem3_laurentProgram_iff_sdp (N k : ℕ) [NeZero N] :
    PaperLaurentProgram N k ↔ tiSDPFeasible N k 0 :=
  exactLaurentProgramIffSDP N k

end Qatlib.Papers.OrderedSearch06.SdpForm
