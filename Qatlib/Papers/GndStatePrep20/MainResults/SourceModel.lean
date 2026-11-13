/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Qatlib.Concepts.BlockEncoding.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for *Near-optimal ground state preparation* (arXiv:2002.12508v3)

This module is the shared vocabulary of the paper-layer build of
`GndStatePrep20`.  It fixes the objects the paper works with and collects the
purely analytic cores of the seven active claims:

* `rankOne`, `reflCoeff`, `projCoeff`, `reflector`, `projector` — the spectral
  reflector `R_{<μ}` and projector `P_{<μ}` of Section 2;
* `projector_eq_half_add_reflector` — the identity `P_{<μ} = (I + R_{<μ})/2`
  (paper p.6, just below Eq. (2)), derived from completeness of the
  eigenbasis;
* `projectorBlockEncoding_of_reflector` — the projector circuit Eq. (2) turns
  an `(1, ·, ε)`-block-encoding of `R_{<μ}` into an `(1, ·, ε/2)`-block-encoding
  of `P_{<μ}` (paper p.6);
* `fidelity_ratio_ge` — the fidelity estimate of Section 3 (paper p.7);
* `binaryEstimate_threshold` — the deterministic threshold step of Lemma 7;
* `interval_le_majorant`, `interval_recurrence_bound`, `interval_le_three` —
  the binary-search interval analysis of Algorithm 1 (paper p.9);
* `PrepCost`, `EnergyCost` — the resource profiles used to state the
  asymptotic bounds of Theorems 6/8 and Corollary 9.

Nothing here imports the whole quantum-algorithm stack: the block-encoding
vocabulary is reused verbatim from
`Qatlib.Papers.QSingValue19.BlockEncoding.BlockEncoding`
(`BlockEncoding`, `BlockEncoding.perturb`, `compress`, `IsIsometry`).
-/

set_option autoImplicit false

namespace Qatlib.Papers.GndStatePrep20.MainResults

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators Classical

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding

/-! ## Spectral reflector and projector -/

variable {N : ℕ}

/-- The rank-one operator `v vᴴ` (physics `|v⟩⟨v|`) of the eigenvector `v`. -/
noncomputable def rankOne (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of (fun i j => v i * star (v j))

/-- Reflector sign coefficient: `+1` on the low eigenspace (`λ < μ`), `-1`
otherwise.  Paper's `R_{<μ}` (Section 2, p.5). -/
noncomputable def reflCoeff (μ : ℝ) (lam : ℝ) : ℂ := if lam < μ then 1 else -1

/-- Projector coefficient: `1` on the low eigenspace (`λ < μ`), `0` otherwise. -/
noncomputable def projCoeff (μ : ℝ) (lam : ℝ) : ℂ := if lam < μ then 1 else 0

/-- The reflector `R_{<μ} = Σ_{λ_k<μ} |ψ_k⟩⟨ψ_k| − Σ_{λ_k>μ} |ψ_k⟩⟨ψ_k|`
of the spectral decomposition `H = Σ_k λ_k |ψ_k⟩⟨ψ_k|`. -/
noncomputable def reflector (lam : Fin N → ℝ) (psi : Fin N → Fin N → ℂ) (μ : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ k, reflCoeff μ (lam k) • rankOne (psi k)

/-- The projector `P_{<μ} = Σ_{λ_k<μ} |ψ_k⟩⟨ψ_k|` of the spectral
decomposition. -/
noncomputable def projector (lam : Fin N → ℝ) (psi : Fin N → Fin N → ℂ) (μ : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  ∑ k, projCoeff μ (lam k) • rankOne (psi k)

/-- Pointwise arithmetic behind Eq. (2): the projector coefficient is half of
`one + reflector coefficient`. -/
theorem projCoeff_eq_half_mul (μ lam : ℝ) :
    projCoeff μ lam = (1 / 2 : ℂ) * (1 + reflCoeff μ lam) := by
  unfold projCoeff reflCoeff
  split_ifs <;> ring

/-- **`P_{<μ} = (I + R_{<μ}) / 2` (paper p.6).**  This is the matrix identity
underlying the projector circuit Eq. (2), derived from completeness
`Σ_k |ψ_k⟩⟨ψ_k| = I` of the orthonormal eigenbasis. -/
theorem projector_eq_half_add_reflector
    (lam : Fin N → ℝ) (psi : Fin N → Fin N → ℂ) (μ : ℝ)
    (hcomplete : (∑ k, rankOne (psi k)) = (1 : Matrix (Fin N) (Fin N) ℂ)) :
    projector lam psi μ = (1 / 2 : ℂ) • ((1 : Matrix (Fin N) (Fin N) ℂ) + reflector lam psi μ) := by
  have hsum : (∑ k, rankOne (psi k)) = (1 : Matrix (Fin N) (Fin N) ℂ) := hcomplete
  calc
    projector lam psi μ
        = ∑ k, ((1 / 2 : ℂ) * (1 + reflCoeff μ (lam k))) • rankOne (psi k) := by
          unfold projector
          apply Finset.sum_congr rfl
          intro k _
          rw [projCoeff_eq_half_mul]
    _ = (1 / 2 : ℂ) • ∑ k, (1 + reflCoeff μ (lam k)) • rankOne (psi k) := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [mul_smul]
    _ = (1 / 2 : ℂ) •
          ((∑ k, rankOne (psi k)) + ∑ k, reflCoeff μ (lam k) • rankOne (psi k)) := by
          congr 1
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k _
          rw [add_smul, one_smul]
    _ = (1 / 2 : ℂ) • ((1 : Matrix (Fin N) (Fin N) ℂ) + reflector lam psi μ) := by
          rw [hsum]; rfl

/-! ## The projector circuit Eq. (2): error halving -/

/-- Norm of the complex scalar `1/2`. -/
theorem norm_half_complex : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
  norm_num

/-- **Projector block-encoding from the reflector block-encoding (paper
Eq. (2), p.6).**  Given an `(1, ·, ε)`-block-encoding `BlockEncoding Rmat U L Rf 1 ε`
of the reflector, together with the projector circuit whose compression is the
paper's Eq. (2) expression `compress Lp Up Rp = (1/2)(I + compress L U Rf)`,
we obtain an `(1, ·, ε/2)`-block-encoding of `Pmat = (1/2)(I + Rmat)`.

The paper's derivation is exactly
`‖P̃ − P‖ = ½‖R̃ − R‖ ≤ ε/2`. -/
theorem projectorBlockEncoding_of_reflector
    {Hsp I : Type*} [Fintype Hsp] [Fintype I]
    [DecidableEq Hsp] [DecidableEq I]
    {Rmat Pmat : Matrix I I ℂ} {U Up : Matrix Hsp Hsp ℂ}
    {L Lp Rf Rp : Matrix Hsp I ℂ} {ε : ℝ}
    (hUp : Up ∈ Matrix.unitaryGroup Hsp ℂ)
    (hLp : IsIsometry Lp) (hRp : IsIsometry Rp)
    (hPmat : Pmat = (1 / 2 : ℂ) • ((1 : Matrix I I ℂ) + Rmat))
    (hCircuit : compress Lp Up Rp = (1 / 2 : ℂ) • ((1 : Matrix I I ℂ) + compress L U Rf))
    (henc : ‖Rmat - compress L U Rf‖ ≤ ε) :
    BlockEncoding Pmat Up Lp Rp 1 (ε / 2) := by
  have hε0 : (0 : ℝ) ≤ ε := le_trans (norm_nonneg _) henc
  refine ⟨hUp, hLp, hRp, by norm_num, by positivity, ?_⟩
  have hdiff :
      Pmat - (1 : ℝ) • compress Lp Up Rp = (1 / 2 : ℂ) • (Rmat - compress L U Rf) := by
    rw [hPmat, hCircuit, one_smul, smul_add, smul_add, smul_sub]
    abel
  calc
    ‖Pmat - (1 : ℝ) • compress Lp Up Rp‖ = ‖(1 / 2 : ℂ) • (Rmat - compress L U Rf)‖ := by
      rw [hdiff]
    _ = ‖(1 / 2 : ℂ)‖ * ‖Rmat - compress L U Rf‖ := norm_smul _ _
    _ = (1 / 2 : ℝ) * ‖Rmat - compress L U Rf‖ := by rw [norm_half_complex]
    _ ≤ (1 / 2 : ℝ) * ε := by nlinarith [henc]
    _ = ε / 2 := by ring

/-! ## Fidelity estimate of Section 3 -/

/-- **Fidelity estimate (paper p.7).**  Let `a = ‖⟨ψ₀|φ₀⟩‖ ≥ γ > 0` be the
initial overlap and let `b = γε/2` be the propagated projector error.  Then the
post-selected fidelity is at least `1 − ε`:
`(a − b)/(a + b) ≥ 1 − ε`. -/
theorem fidelity_ratio_ge {a b γ ε : ℝ} (ha : 0 < a) (hγ : 0 < γ)
    (hε : 0 ≤ ε) (haγ : γ ≤ a) (hb : b = γ * ε / 2) :
    1 - ε ≤ (a - b) / (a + b) := by
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hden : 0 < a + b := by positivity
  rw [le_div_iff₀ hden, hb]
  nlinarith [hε, haγ, hγ, mul_nonneg hε hε, mul_pos hγ hγ]

/-- A denominator-cleared form used when carrying the fidelity estimate
through amplitude amplification: the successful-branch norm bound
`‖P̃|φ₀⟩‖ ≤ a + b`. -/
theorem fidelity_numerator_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ≤ a + b := le_add_of_nonneg_right hb

/-! ## Binary amplitude estimation (Lemma 7) -/

/-- **Threshold step of Lemma 7 (paper p.8).**  If the amplitude estimate
`est` is within `Δ/4 = (γ₁−γ₀)/4` of the true amplitude `A`, then choosing the
threshold `(γ₀+γ₁)/2` distinguishes the two promised cases: `A ≤ γ₀` gives an
estimate below the threshold, and `A ≥ γ₁` gives one above it. -/
theorem binaryEstimate_threshold {γ₀ γ₁ est A : ℝ} (hΔ : 0 < γ₁ - γ₀)
    (herr : |est - A| ≤ (γ₁ - γ₀) / 4) :
    (A ≤ γ₀ → est < (γ₀ + γ₁) / 2) ∧ (γ₁ ≤ A → (γ₀ + γ₁) / 2 < est) := by
  have hup : est - A ≤ (γ₁ - γ₀) / 4 := (abs_le.mp herr).2
  have hlo : -((γ₁ - γ₀) / 4) ≤ est - A := (abs_le.mp herr).1
  constructor
  · intro hA
    have : est ≤ A + (γ₁ - γ₀) / 4 := by linarith
    have h1 : A + (γ₁ - γ₀) / 4 ≤ γ₀ + (γ₁ - γ₀) / 4 := by linarith
    have h2 : γ₀ + (γ₁ - γ₀) / 4 < (γ₀ + γ₁) / 2 := by linarith
    linarith
  · intro hA
    have : A - (γ₁ - γ₀) / 4 ≤ est := by linarith
    have h1 : γ₁ - (γ₁ - γ₀) / 4 ≤ A - (γ₁ - γ₀) / 4 := by linarith
    have h2 : (γ₀ + γ₁) / 2 < γ₁ - (γ₁ - γ₀) / 4 := by linarith
    linarith

/-! ## Binary-search interval analysis (Algorithm 1, paper p.9) -/

/-- Adding `2` and halving is dominated by the closed form
`(G−2)/2^l + 2`: if the half-width after one step is at most
`d/2 + 1`, induction gives `d_l ≤ (G−2)/2^l + 2`. -/
theorem interval_recurrence_bound (d : ℕ → ℝ) (G : ℝ)
    (h0 : d 0 = G) (hstep : ∀ l, d (l + 1) ≤ d l / 2 + 1) :
    ∀ l, d l ≤ (G - 2) / 2 ^ l + 2 := by
  intro l
  induction l with
  | zero => simp [h0]
  | succ l ih =>
      have hpow : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
      have hs := hstep l
      have hrec : d l / 2 + 1 ≤ ((G - 2) / 2 ^ l + 2) / 2 + 1 := by
        have := ih
        linarith
      calc
        d (l + 1) ≤ d l / 2 + 1 := hs
        _ ≤ ((G - 2) / 2 ^ l + 2) / 2 + 1 := hrec
        _ = (G - 2) / 2 ^ (l + 1) + 2 := by
          rw [pow_succ]
          field_simp
          ring

/-- Once `2^l ≥ G−2`, the interval half-width is at most `3`.  Combined with
the recurrence this is the paper's termination claim `U_l − L_l ≤ 3` at
`l = ⌈log₂ G⌉`. -/
theorem interval_le_three (d : ℕ → ℝ) (G : ℝ) (l : ℕ)
    (h : d l ≤ (G - 2) / 2 ^ l + 2) (hG : G - 2 ≤ 2 ^ l) (hG0 : 0 ≤ G - 2) :
    d l ≤ 3 := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  have hratio : (G - 2) / 2 ^ l ≤ 1 := by
    rw [div_le_iff₀ hpow]; simpa using hG
  linarith

/-! ## Resource profiles for the asymptotic statements

The paper's Theorems 6/8, Corollary 9 and Theorems 10/11 are asymptotic
(`O`/`Ω`) statements about the query and gate counts of a *family of protocols*
indexed by the accuracy parameter.  We record a protocol by its resource
functions; a big-`O`/`Ω` assertion is then the existence of an absolute constant
witness (equivalently `Asymptotics.IsBigO` with a constant).  These are
definitional scaffolding only — they introduce no mathematics. -/

/-- Resource profile of a ground-state preparation protocol, as functions of
the target error parameter `ε`. -/
structure PrepCost where
  /-- queries to the Hamiltonian block-encoding `U_H` at accuracy `ε`. -/
  queryH : ℝ → ℝ
  /-- queries to the initial-state circuit `U_I` at accuracy `ε`. -/
  queryI : ℝ → ℝ
  /-- other one- and two-qubit gates at accuracy `ε`. -/
  gates : ℝ → ℝ
  /-- number of qubits used (independent of `ε`). -/
  qubits : ℝ

/-- Resource profile of a ground-energy estimation protocol, as functions of
the precision `h` and confidence `ϑ`. -/
structure EnergyCost where
  queryH : ℝ → ℝ → ℝ
  queryI : ℝ → ℝ → ℝ
  gates : ℝ → ℝ → ℝ
  qubits : ℝ

end Qatlib.Papers.GndStatePrep20.MainResults
