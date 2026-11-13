/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# MarkovLogic16 — Proposition 1: gate complexity of quantum Gibbs sampling for MLNs

Fixed version: arXiv:1611.08104v1 (stat.ML, 24 Nov 2016),
*Quantum Enhanced Inference in Markov Logic Networks*.
Source read from `assets/1611.08104.pdf` (8 pages) and `assets/1611.08104.txt`;
Proposition 1 is on PDF page 4, §IV (txt line 273).

Proposition 1 (verbatim): "Assuming that the maximum size of the support of the
local terms of the Hamiltonian `H` is constant [32] and that for some constant `α`
the number of terms in `H` is in `O(n^α)`, the overall complexity of the Gibbs
sampling method from [29] is in
`O(√(d^n β/Z) polylog(√(d^n β/Z)/ε))`."

Here `d` is the local dimension (`d = 2` for MLN Gibbs states), `β` the inverse
temperature, `Z = tr(exp(-βH))` the partition function and `ε` the final distance
to the thermal state.  The paper derives this from the thermal-state-preparation
algorithm of Chowdhury–Somma [29] (arXiv:1603.02940): the number of ports of the
local terms equals the maximum clique size (constant, so `H` is `k`-local) and the
number of terms equals the number of cliques (`O(n^α)`); footnote [32] sharpens
the needed structural premise to "the gate complexity of time evolution under the
local terms of `H` scales at most linearly with `n`".

## Lean modelling

`thermalScale d β Z n = √(d^n β/Z)` and `polylogScale x k = (log x)^k` (the paper's
`polylog` is `log`, i.e. `(·)^k` for a fixed exponent `k`).  The displayed bound is
`gibbsComplexityBound d β Z ε k n`.  The proposition's conclusion — "the gate
complexity `T` of the [29] sampler is `O(√(d^n β/Z) polylog(√(d^n β/Z)/ε))`" — is
`Prop1ComplexityStatement T d β Z ε`.

## Status / gap

The MLN side is fully formalized: `GroundedMLN` records the ground atoms, the
cliques (ground-formula supports), the maximum number of atoms per formula, and
the time-evolution cost; `MLNHamiltonian.maxSupport`/`numTerms` prove that the
maximum support is the maximum clique size and the number of terms is the number
of cliques.  `source_prop1_gibbs_complexity` then instantiates the
Chowdhury–Somma guarantee from the paper's assumptions (constant maximum support,
`O(n^α)` cliques, linear time-evolution cost).

The numerical upper bound itself comes from [29] Chowdhury–Somma, whose
thermal-state-preparation gate-complexity theorem is *not* formalized in the
package or Dev (searched `Qatlib.*` and `QuantumAlgorithmDev`).  It is
carried as the explicit, documented hypothesis `ChowdhurySommaGuarantee`; the
elementary scale algebra (positivity, square identity, geometric step in `n`) is
proved outright below.  Completing the unconditional proposition would require
formalizing the [29] algorithm and its complexity accounting; see the gap note at
the end of the file.
-/

set_option autoImplicit false
noncomputable section

open Asymptotics Filter

namespace Qatlib.Papers.MarkovLogic16.MainResults.Proposition1

/-- The scale `√(d^n β/Z)` from Proposition 1 (arXiv:1611.08104v1, p.4):
`d` local dimension, `β` inverse temperature, `Z` the partition function. -/
def thermalScale (d β Z : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (d ^ n * β / Z)

/-- `polylog x` in Proposition 1 read as `(log x)^k` for a fixed exponent `k : ℕ`. -/
def polylogScale (x : ℝ) (k : ℕ) : ℝ :=
  Real.log x ^ k

/-- The displayed upper bound of Proposition 1 (arXiv:1611.08104v1, p.4):
`√(d^n β/Z) · (log(√(d^n β/Z)/ε))^k`, with `ε` the distance to the thermal state. -/
def gibbsComplexityBound (d β Z ε : ℝ) (k n : ℕ) : ℝ :=
  thermalScale d β Z n * polylogScale (thermalScale d β Z n / ε) k

/-- Statement contract for Proposition 1: the gate complexity `T` of the
Chowdhury–Somma [29] Gibbs-sampling method lies in
`O(√(d^n β/Z) polylog(√(d^n β/Z)/ε))` for some fixed polylog exponent `k`. -/
def Prop1ComplexityStatement (T : ℕ → ℝ) (d β Z ε : ℝ) : Prop :=
  ∃ k : ℕ, IsBigO atTop T (gibbsComplexityBound d β Z ε k)

/-- Unfolding the bound gives the paper's literal formula. -/
theorem gibbsComplexityBound_displayed (d β Z ε : ℝ) (k n : ℕ) :
    gibbsComplexityBound d β Z ε k n =
      Real.sqrt (d ^ n * β / Z) *
        (Real.log (Real.sqrt (d ^ n * β / Z) / ε)) ^ k := rfl

/-- Positivity of the scale `√(d^n β/Z)` for positive `d`, `β`, `Z`
(arXiv:1611.08104v1, p.4). -/
lemma thermalScale_pos (d β Z : ℝ) (n : ℕ)
    (hd : 0 < d) (hβ : 0 < β) (hZ : 0 < Z) :
    0 < thermalScale d β Z n := by
  unfold thermalScale
  exact Real.sqrt_pos.mpr (div_pos (mul_pos (pow_pos hd n) hβ) hZ)

/-- The scale squared recovers the Gibbs weight `d^n β/Z`. -/
lemma thermalScale_sq (d β Z : ℝ) (n : ℕ)
    (hd : 0 < d) (hβ : 0 < β) (hZ : 0 < Z) :
    thermalScale d β Z n ^ 2 = d ^ n * β / Z := by
  unfold thermalScale
  exact Real.sq_sqrt (le_of_lt (div_pos (mul_pos (pow_pos hd n) hβ) hZ))

/-- One step of the exponential growth of the scale:
`√(d^(n+1) β/Z) = √d · √(d^n β/Z)` for `d ≥ 0`.  This is the paper's `√(d^n)`
structure (arXiv:1611.08104v1, p.4). -/
lemma thermalScale_succ (d β Z : ℝ) (n : ℕ) (hd : 0 ≤ d) :
    thermalScale d β Z (n + 1) = Real.sqrt d * thermalScale d β Z n := by
  unfold thermalScale
  rw [pow_succ]
  rw [show d ^ n * d * β / Z = d * (d ^ n * β / Z) by ring]
  rw [Real.sqrt_mul hd]

/-- A grounded MLN at scale `n`: ground atoms `Fin n`, the cliques (supports of
ground formulas), a uniform bound on the number of atoms per formula, and the
gate complexity of time evolution under the associated local terms
(arXiv:1611.08104v1, §IV). -/
structure GroundedMLN (n : ℕ) where
  cliques : Finset (Finset (Fin n))
  maxAtoms : ℕ
  maxAtoms_spec : ∀ C ∈ cliques, C.card ≤ maxAtoms
  evolutionCost : ℝ

/-- The local Hamiltonian associated with a grounded MLN: one local term per
clique, supported on that clique. -/
structure MLNHamiltonian (n : ℕ) where
  cliques : Finset (Finset (Fin n))
  evolutionCost : ℝ

/-- The local Hamiltonian of a grounded MLN. -/
def GroundedMLN.toHamiltonian {n : ℕ} (M : GroundedMLN n) : MLNHamiltonian n :=
  { cliques := M.cliques, evolutionCost := M.evolutionCost }

/-- Maximum support size of the local terms (the maximum clique size). -/
def MLNHamiltonian.maxSupport {n : ℕ} (H : MLNHamiltonian n) : ℕ :=
  H.cliques.sup Finset.card

/-- Number of local terms (the number of cliques). -/
def MLNHamiltonian.numTerms {n : ℕ} (H : MLNHamiltonian n) : ℕ :=
  H.cliques.card

/-- The maximum support is at most the maximum number of atoms per formula. -/
theorem maxSupport_toHamiltonian_le {n : ℕ} (M : GroundedMLN n) :
    M.toHamiltonian.maxSupport ≤ M.maxAtoms := by
  unfold MLNHamiltonian.maxSupport GroundedMLN.toHamiltonian
  exact Finset.sup_le (fun C hC => M.maxAtoms_spec C hC)

/-- The number of terms is exactly the number of cliques. -/
theorem numTerms_toHamiltonian {n : ℕ} (M : GroundedMLN n) :
    M.toHamiltonian.numTerms = M.cliques.card := rfl

/-- The Chowdhury–Somma [29] gate-complexity guarantee for a family of MLN
local Hamiltonians: constant maximum support, `O(n^α)` terms and time evolution
at most linear in `n` imply the Gibbs-sampling gate complexity
`O(√(d^n β/Z) polylog(√(d^n β/Z)/ε))`. -/
def ChowdhurySommaGuarantee (d : ℕ) (β Z ε : ℝ) (T : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) (H : ∀ n, MLNHamiltonian n),
    (∀ n, (H n).maxSupport ≤ k) →
    (∃ C α : ℝ, 0 ≤ C ∧ 0 ≤ α ∧
      IsBigO atTop (fun n => ((H n).numTerms : ℝ)) (fun n => (n : ℝ) ^ α)) →
    (∃ c : ℝ, 0 ≤ c ∧ ∀ n, (H n).evolutionCost ≤ c * (n : ℝ)) →
    ∃ k' : ℕ, IsBigO atTop T (gibbsComplexityBound d β Z ε k')

/-- Proposition 1 (arXiv:1611.08104v1, p.4): for a family of grounded MLNs with
constant maximum number of atoms per formula, `O(n^α)` cliques and time evolution
at most linear in `n`, the [29] Gibbs-sampling gate complexity is
`O(√(d^n β/Z) polylog(√(d^n β/Z)/ε))`.

The Chowdhury–Somma bound enters as `ChowdhurySommaGuarantee`; the MLN structural
premises are the paper's own assumptions (p.4: "the maximum size of the supports
of the local terms of H is equal to the maximum clique size, and the number of
terms is the number of cliques in the MLN"). -/
theorem source_prop1_gibbs_complexity
    (M : ∀ n, GroundedMLN n) (d : ℕ) (β Z ε : ℝ) (T : ℕ → ℝ)
    (hChowdhurySomma : ChowdhurySommaGuarantee d β Z ε T)
    (hconst : ∃ k : ℕ, ∀ n, (M n).maxAtoms ≤ k)
    (hterms : ∃ C α : ℝ, 0 ≤ C ∧ 0 ≤ α ∧
      IsBigO atTop (fun n => ((M n).cliques.card : ℝ)) (fun n => (n : ℝ) ^ α))
    (htime : ∃ c : ℝ, 0 ≤ c ∧ ∀ n, (M n).evolutionCost ≤ c * (n : ℝ)) :
    Prop1ComplexityStatement T d β Z ε := by
  obtain ⟨k, hk⟩ := hconst
  have hsupp : ∀ n, (M n).toHamiltonian.maxSupport ≤ k :=
    fun n => le_trans (maxSupport_toHamiltonian_le (M n)) (hk n)
  have hterms' : ∃ C α : ℝ, 0 ≤ C ∧ 0 ≤ α ∧
      IsBigO atTop (fun n => ((M n).toHamiltonian.numTerms : ℝ))
        (fun n => (n : ℝ) ^ α) := by
    obtain ⟨C, α, hC, hα, hO⟩ := hterms
    exact ⟨C, α, hC, hα, by
      simpa [MLNHamiltonian.numTerms, GroundedMLN.toHamiltonian] using hO⟩
  exact hChowdhurySomma k (fun n => (M n).toHamiltonian) hsupp hterms' htime

/-! ## Gap note (for the literal, unconditional Proposition 1)

Fixed version: arXiv:1611.08104v1, Proposition 1, PDF page 4 (§IV).

Original statement and proof route: the paper *does not reprove* the complexity
bound; it applies the thermal-state-preparation algorithm of reference [29]
(Chowdhury & Somma, arXiv:1603.02940, 2016) and observes that in the MLN-generated
Hamiltonian the maximum support of local terms equals the maximum clique size
(= maximum atoms per formula, constant), the number of terms equals the number of
cliques (`O(n^α)`), and time evolution under local terms costs at most linear in
`n` (footnote [32]).  Substituting these into [29]'s bound yields
`O(√(d^n β/Z) polylog(√(d^n β/Z)/ε))`.

`GibbsSampling`
contains only Gibbs *lower*-bound contracts (e.g. `GibbsPreparationTimeLowerBound`
for CKBG 2023 Prop G.5); there is no formalization of the Chowdhury–Somma
gate-complexity *upper* bound.  The MLN side (cliques, maximum support, number of
terms, time-evolution cost) is formalized in `GroundedMLN`/`MLNHamiltonian`, so
the only remaining input is the explicit `ChowdhurySommaGuarantee`.

Candidate reusable dependencies: `Mathlib.Analysis.Asymptotics.*` (`IsBigO`,
`IsBigO.trans`, `IsBigO.const_mul_*`); the `...Stat` contract pattern of
`GibbsSampling.SamplingCost.GibbsPreparationTimeLowerBound`;
Chowdhury–Somma arXiv:1603.02940 Theorem 1 (gate complexity of approximate thermal
state preparation).

The conditional theorem above records the exact statement and the paper's
MLN-specific reduction. -/

end Qatlib.Papers.MarkovLogic16.MainResults.Proposition1
