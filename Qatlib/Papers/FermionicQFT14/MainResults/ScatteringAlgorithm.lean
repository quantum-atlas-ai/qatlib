/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermionicQFT14.MainResults.TotalGateCount

set_option backward.isDefEq.respectTransparency false

/-!
# MainResults: the scattering algorithm and its polynomial run time (claim `c002`)

Claim `c002` of the paper layer is the abstract sentence of arXiv:1404.7115v1
(p. 1):

  "We develop a quantum algorithm to compute relativistic scattering amplitudes
   in fermionic field theories, exemplified by the massive Gross–Neveu model, a
   theory in two spacetime dimensions with quartic interactions. [...] its run
   time is polynomial in the desired precision and the energy."

The formal statement splits into the two checkable halves of that sentence:

* **the algorithm**: the six-step pipeline of §2.2 (prepare the product ground
  state, adiabatically turn on hopping, adiabatically turn on the quartic
  interaction, excite wavepackets, time-evolve under the full Gross–Neveu
  Hamiltonian, measure by phase estimation).  It is represented by
  `paperPipeline`, and a `GrossNeveuSimulator` carries the model data (species,
  mass, quartic coupling) together with its gate-count function;
* **the run time**: the combined gate count of the high-precision and
  high-momentum branches, `combinedGateCount`, is bounded by
  `C * ε ^ (-9) * p ^ 10` for all sufficiently small `ε > 0` and large `p`.
  This is polynomial in the desired precision (`1/ε`) and in the energy
  (momentum `p`), obtained from Eq. (20) by fixing the `o(1)` slack at `δ = 1`.

The semantic half of the sentence — that the circuit's output distribution
equals the relativistic scattering amplitude — is not expressible in this
library (it would require formal QFT scattering theory); the formalization
covers the algorithmic structure and the quantitative run-time guarantee,
following the paper's own reduction of the claim to Eqs. (16), (18), (19).
All theorems in this file are fully proved; there is no `sorry`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermionicQFT14.MainResults

/-! ## 1. The six-step pipeline of §2.2 -/

/-- The six main steps of the algorithm, in the order listed in §2.2 of
arXiv:1404.7115v1 (p. 5–6). -/
inductive PipelineStep where
  /-- Step 1: prepare the ground state with both the interaction and the
  nearest-neighbour lattice-site interactions turned off (a tensor product of
  single-site ground states). -/
  | prepareProductGroundState
  /-- Step 2: adiabatically turn on the nearest-neighbour lattice-site
  interactions by Suzuki–Trotter simulation. -/
  | adiabaticTurnOnHopping
  /-- Step 3: adiabatically turn on the quartic interaction term, adjusting
  `m₀` to compensate the renormalization of the physical mass. -/
  | adiabaticTurnOnInteraction
  /-- Step 4: excite particle wavepackets with a resonant sinusoidal source. -/
  | exciteWavepackets
  /-- Step 5: time-evolve under the full massive Gross–Neveu Hamiltonian by
  Suzuki–Trotter formulae (this is where scattering occurs). -/
  | evolveGrossNeveu
  /-- Step 6: measure local charge observables (or number operators of momentum
  modes after an adiabatic return to the free theory) by phase estimation. -/
  | measureByPhaseEstimation
  deriving DecidableEq, Repr

/-- The paper's algorithm, as its six ordered steps. -/
def paperPipeline : List PipelineStep :=
  [PipelineStep.prepareProductGroundState,
   PipelineStep.adiabaticTurnOnHopping,
   PipelineStep.adiabaticTurnOnInteraction,
   PipelineStep.exciteWavepackets,
   PipelineStep.evolveGrossNeveu,
   PipelineStep.measureByPhaseEstimation]

/-- The pipeline has exactly the six steps of §2.2. -/
theorem paperPipeline_length : paperPipeline.length = 6 := rfl

/-! ## 2. Simulators of the massive Gross–Neveu model -/

/-- A simulator for the 1+1-dimensional massive Gross–Neveu model: its field
content (one fermion species), the physical mass `m`, the quartic coupling
`g₀²`, the six-step pipeline it runs, and the asymptotic gate count `gateCount`
as a function of the desired precision `ε` and the particle momentum `p`. -/
structure GrossNeveuSimulator where
  /-- number of fermion species (one for the Gross–Neveu model) -/
  species : ℕ
  /-- the physical mass `m` -/
  mass : ℝ
  /-- the quartic interaction coupling `g₀²` -/
  coupling : ℝ
  /-- the ordered algorithmic steps -/
  pipeline : List PipelineStep
  /-- the gate count as a function of precision `ε` and momentum `p` -/
  gateCount : ℝ → ℝ → ℝ

/-- The model is the *massive* Gross–Neveu model: positive mass and a nonzero
quartic coupling, in two spacetime dimensions with one fermion species. -/
def IsMassiveGrossNeveuModel (S : GrossNeveuSimulator) : Prop :=
  0 < S.mass ∧ S.coupling ≠ 0

/-- The simulator runs the paper's six-step algorithm verbatim. -/
def ImplementsPaperPipeline (S : GrossNeveuSimulator) : Prop :=
  S.pipeline = paperPipeline

/-! ## 3. Polynomial gate scaling -/

/-- The run-time guarantee of the abstract: the gate count is at most a
constant times `ε ^ (-9) * p ^ 10`, i.e. polynomial in the reciprocal precision
`1/ε` and in the energy (momentum) `p`, uniformly for all sufficiently small
`ε > 0` and all sufficiently large momenta. -/
def PolynomialGateScaling (G : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ p₀ : ℝ, 0 < ε₀ ∧ 1 ≤ p₀ ∧
    ∀ ε p : ℝ, 0 < ε → ε ≤ ε₀ → p₀ ≤ p →
      |G ε p| ≤ C * ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ)

/-- The combined gate count: the high-precision branch Eq. (20a) at precision
`ε` plus the high-momentum branch Eq. (20b) at momentum `p`. -/
def combinedGateCount (cprep cexc : ℝ) (η : ℝ → ℝ) (ε p : ℝ) : ℝ :=
  highPrecisionTotalGateCount cprep cexc η ε
    + highMomentumTotalGateCount cprep cexc η p

/-- **Polynomial run time.**  For nonnegative cost constants and an `o(1)`
correction that vanishes at both ends, the combined gate count obeys
`|G(ε,p)| ≤ C * ε ^ (-9) * p ^ 10`.  The exponents `9` and `10` are the
`δ = 1` instantiations of the Eq. (20) exponents `8 + δ` and `9 + δ`. -/
theorem combinedGateCount_polynomial {cprep cexc : ℝ} (hcprep : 0 ≤ cprep)
    (hcexc : 0 ≤ cexc) {η : ℝ → ℝ} (hη0 : VanishesAtZero η)
    (hηp : VanishesAtTop η) :
    PolynomialGateScaling (combinedGateCount cprep cexc η) := by
  obtain ⟨C₁, hC₁, ε₁, hε₁, hb₁⟩ :=
    eq20_highPrecision hcprep hcexc hη0 1 (by norm_num)
  obtain ⟨C₂, hC₂, p₁, hp₁, hb₂⟩ :=
    eq20_highMomentum hcprep hcexc hηp 1 (by norm_num)
  simp only [show (8 : ℝ) + 1 = 9 by norm_num] at hb₁
  simp only [show (9 : ℝ) + 1 = 10 by norm_num] at hb₂
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, min ε₁ 1, max p₁ 1,
    lt_min hε₁ one_pos, le_max_right _ _, fun ε p hε hεle hpge => ?_⟩
  have hε₁' : ε ≤ ε₁ := le_trans hεle (min_le_left _ _)
  have hεle1 : ε ≤ 1 := le_trans hεle (min_le_right _ _)
  have hp₁' : p₁ ≤ p := le_trans (le_max_left _ _) hpge
  have hp1 : (1 : ℝ) ≤ p := le_trans (le_max_right _ _) hpge
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le one_pos hp1
  have hb₁' := hb₁ ε hε hε₁'
  have hb₂' := hb₂ p hp₁'
  have htri : |combinedGateCount cprep cexc η ε p|
      ≤ C₁ * ε ^ (-(9 : ℝ)) + C₂ * p ^ (10 : ℝ) := by
    rw [combinedGateCount]
    calc |highPrecisionTotalGateCount cprep cexc η ε
          + highMomentumTotalGateCount cprep cexc η p|
        ≤ |highPrecisionTotalGateCount cprep cexc η ε|
          + |highMomentumTotalGateCount cprep cexc η p| := abs_add_le _ _
      _ ≤ C₁ * ε ^ (-(9 : ℝ)) + C₂ * p ^ (10 : ℝ) := add_le_add hb₁' hb₂'
  have hε9nn : 0 ≤ ε ^ (-(9 : ℝ)) := Real.rpow_nonneg (le_of_lt hε) _
  have hε9ge1 : 1 ≤ ε ^ (-(9 : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt hε)]
    rw [one_le_inv₀ (Real.rpow_pos_of_pos hε 9)]
    exact Real.rpow_le_one (le_of_lt hε) hεle1 (by norm_num)
  have hp10nn : 0 ≤ p ^ (10 : ℝ) := Real.rpow_nonneg (le_of_lt hp0) _
  have hp10ge1 : 1 ≤ p ^ (10 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hprodnn : 0 ≤ ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ) := mul_nonneg hε9nn hp10nn
  have hterm1 : C₁ * ε ^ (-(9 : ℝ))
      ≤ C₁ * (ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ)) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hε9nn hp10ge1) hC₁
  have hterm2 : C₂ * p ^ (10 : ℝ)
      ≤ C₂ * (ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ)) := by
    calc C₂ * p ^ (10 : ℝ)
        = C₂ * (p ^ (10 : ℝ) * 1) := by ring
      _ ≤ C₂ * (p ^ (10 : ℝ) * ε ^ (-(9 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hε9ge1 hp10nn) hC₂
      _ = C₂ * (ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ)) := by ring
  calc |combinedGateCount cprep cexc η ε p|
      ≤ C₁ * ε ^ (-(9 : ℝ)) + C₂ * p ^ (10 : ℝ) := htri
    _ ≤ C₁ * (ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ))
          + C₂ * (ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ)) :=
        add_le_add hterm1 hterm2
    _ = (C₁ + C₂) * ε ^ (-(9 : ℝ)) * p ^ (10 : ℝ) := by ring

/-! ## 4. Claim `c002` -/

/-- **Claim `c002`**, abstract p. 1 of arXiv:1404.7115v1: there is a simulator of
the massive Gross–Neveu model (two spacetime dimensions, quartic interaction)
that implements the paper's six-step algorithm and whose gate count is
polynomial in the desired precision and in the energy. -/
theorem grossNeveu_scattering_algorithm_exists {cprep cexc : ℝ}
    (hcprep : 0 ≤ cprep) (hcexc : 0 ≤ cexc) {η : ℝ → ℝ}
    (hη0 : VanishesAtZero η) (hηp : VanishesAtTop η) :
    ∃ S : GrossNeveuSimulator,
      IsMassiveGrossNeveuModel S ∧ ImplementsPaperPipeline S ∧
      PolynomialGateScaling S.gateCount ∧
      S.gateCount = combinedGateCount cprep cexc η := by
  refine ⟨⟨1, 1, 1, paperPipeline, combinedGateCount cprep cexc η⟩,
    ⟨one_pos, one_ne_zero⟩, rfl, combinedGateCount_polynomial hcprep hcexc hη0 hηp,
    rfl⟩

end Qatlib.Papers.FermionicQFT14.MainResults
