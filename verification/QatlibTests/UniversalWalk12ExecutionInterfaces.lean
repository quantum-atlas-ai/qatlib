/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Qatlib.Papers.UniversalWalk12.MainResults.Truncation.SourceProposition1
public import Qatlib.Papers.UniversalWalk12.MainResults.Model.Evolution
public import Qatlib.Papers.UniversalWalk12.MainResults.Fourier.ConcreteEndpoints
public import Qatlib.Papers.UniversalWalk12.MainResults.Truncation.SourceLemma2

@[expose] public section

/-! # Multi-particle walk consumer -/

namespace QatlibTests.UniversalWalk12ExecutionInterfaces

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Papers.UniversalWalk12.MainResults.Model
open Qatlib.Papers.UniversalWalk12.MainResults.Fourier
open Qatlib.Papers.UniversalWalk12.MainResults.Truncation
open Set

example (t p1 p2 : ℝ) : ‖physicalPhase t p1 p2‖ = 1 := phase_norm t p1 p2

example (p1 p2 : ℝ) :
    physicalEnergy p1 p2 = 2 * Real.cos (-p1 / 2 - p2) + 2 * Real.cos (-p1 / 2 + p2) :=
  energy_individual p1 p2

example (M L : ℕ) (u v : ℤ) :
    average₂ (fun p1 p2 =>
      evolvedKernel M L 0 p1 p2 * star (latticeChar u v p1 p2)) =
      if (u, v) ∈ packetSupport M L then ((1 / (L : ℝ) : ℝ) : ℂ) else 0 := by
  exact evolvedKernel_zero_endpoint M L u v

example (M L : ℕ) (hL : 0 < L) (t : ℝ) :
    average₂ (fun p1 p2 =>
      ((‖evolvedKernel M L t p1 p2‖ ^ 2 : ℝ) : ℂ)) = 1 := by
  exact evolvedKernel_energy M L hL t

/-- The consumer invokes the Krylov truncation bound of Lemma 2. -/
theorem krylov_truncation_consumer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H P : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    (hPidem : P * P = P) (hPself : star P = P)
    (Φ : E) (hΦ : ‖Φ‖ = 1)
    (T δ : ℝ) (N₀ : ℕ) (hδ : 0 < δ) (hN₀ : 0 < N₀)
    (W : E →L[ℂ] E) (hW : W = H ∨ W = P * H * P)
    (γ : ℝ → E)
    (hγ : ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • W) Φ - γ t‖ ≤ δ)
    (horth : ∀ t ∈ Icc (0 : ℝ) T, ∀ r : ℕ, r < N₀ → (1 - P) ((H ^ r) (γ t)) = 0) :
    ∀ t ∈ Icc (0 : ℝ) T,
      ‖NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) Φ
        - NormedSpace.exp ((-(t : ℂ) * Complex.I) • (P * H * P)) Φ‖
      ≤ (4 * Real.exp 1 * ‖H‖ * t / (N₀ : ℝ) + 2)
          * (δ + (2 : ℝ) ^ (-(N₀ : ℝ)) * (1 + δ)) :=
  source_lemma2_truncation H P hH hPidem hPself Φ hΦ T δ N₀ hδ hN₀ W hW γ hγ horth

end QatlibTests.UniversalWalk12ExecutionInterfaces
