/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Thermalize11.MainResults.SourceModel.SourceMicrocanonical

@[expose] public section


/-!
# Thermalize11 reviewed Microcanonical

Closed legacy definitions and lemmas, with separately named contract diagnostics.
Coverage and unproved source bridges are recorded in the batch source review.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.Thermalize11.MainResults.Theorem1

open Qatlib.Papers.Thermalize11.MainResults.SourceModel
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- The data of Theorem 1: a system `S` of dimension `dS` coupled to a bath of
dimension `dB`, the two support projectors `G` (for `H = H₀ + V`) and `F` (for
`H₀`) of the dephased states on the energy window `[E, E+Δ]`, their support
dimensions `Ω_G`, `Ω_F`, the boundary count `Ω_ε`, and the coupling norm
`‖V‖∞`. -/
structure MicrocanonicalPair (dS dB : ℕ) where
  /-- Support projector of `ω_u` (dephased with respect to `H`). -/
  G : Matrix (Fin dS × Fin dB) (Fin dS × Fin dB) ℂ
  /-- Support projector of `ω_u^{(0)}` (dephased with respect to `H₀`). -/
  F : Matrix (Fin dS × Fin dB) (Fin dS × Fin dB) ℂ
  /-- Support dimension `rank G`. -/
  ΩG : ℕ
  /-- Support dimension `rank F`. -/
  ΩF : ℕ
  /-- Total number of eigenstates of `H` and `H₀` in the two `ε`-boundary
  windows. -/
  Ωε : ℕ
  /-- `‖V‖∞`, the operator norm of the coupling. -/
  couplingNorm : ℝ
  /-- The energy window width `Δ`. -/
  Delta : ℝ
  /-- The boundary width `ε`. -/
  eps : ℝ

namespace MicrocanonicalPair

variable {dS dB : ℕ} (M : MicrocanonicalPair dS dB)

/-- `Ω_max = max(rank G, rank F)` (paper, p. 2). -/
def Ωmax : ℕ := max M.ΩG M.ΩF

/-- `Ω_min = min(rank G, rank F)` (paper, p. 2). -/
def Ωmin : ℕ := min M.ΩG M.ΩF

/-- `ΔΩ = Ω_max − Ω_min` (paper, p. 2). -/
def ΔΩ : ℕ := M.Ωmax - M.Ωmin

/-- The dephased state `ω_u` belonging to `[E, E+Δ]` with respect to `H`. -/
def ω : Matrix (Fin dS × Fin dB) (Fin dS × Fin dB) ℂ := dephasedState M.G M.ΩG

/-- The dephased state `ω_u^{(0)}` belonging to `[E, E+Δ]` with respect to `H₀`. -/
def ωZero : Matrix (Fin dS × Fin dB) (Fin dS × Fin dB) ℂ := dephasedState M.F M.ΩF

/-- The subsystem state `ω_u^S` of `S`: partial trace of the full dephased state. -/
def ωS : Operator dS := PartialTrace M.ω

/-- The subsystem state `ω_u^{S(0)}`: partial trace of the non-interacting
dephased state. -/
def ωSZero : Operator dS := PartialTrace M.ωZero

/-- The right-hand side of Eq. (1), Eq. (2) of the source, instantiated at `M`.
-/
def bound : ℝ :=
  theorem1Bound M.couplingNorm M.eps (M.Ωmax : ℝ) (M.Ωmin : ℝ) (M.Ωε : ℝ)

end MicrocanonicalPair

/-- **Real-arithmetic assembly of the two proof steps.** If the normalized
projector distance is bounded by `(‖G−F‖₁ + ΔΩ)/(2Ω_max)` and the projector
difference is bounded by `2(Ω_max ‖V‖∞/ε + Ω_ε/2)`, then the paper's Eq. (1)
right-hand side follows. This is the exact combination used on p. 2 of the
paper ("putting everything together gives the desired result"). -/
theorem theorem1_bound_assemble {traceNormGF normV eps Ωmax ΔΩ Ωε boundValue : ℝ}
    (hΩmax : 0 < Ωmax) (heps : 0 < eps)
    (_hNorm : 0 ≤ traceNormGF) (_hΔ : 0 ≤ ΔΩ) (_hΩε : 0 ≤ Ωε) (_hV : 0 ≤ normV)
    (hStep2 : boundValue ≤ (traceNormGF + ΔΩ) / (2 * Ωmax))
    (hStep3 : traceNormGF ≤ 2 * (Ωmax * (normV / eps) + Ωε / 2)) :
    boundValue ≤ normV / eps + (ΔΩ + Ωε) / (2 * Ωmax) := by
  have hden : 0 < 2 * Ωmax := by positivity
  have hChained : (traceNormGF + ΔΩ) / (2 * Ωmax)
      ≤ (2 * (Ωmax * (normV / eps) + Ωε / 2) + ΔΩ) / (2 * Ωmax) := by
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hEq : (2 * (Ωmax * (normV / eps) + Ωε / 2) + ΔΩ) / (2 * Ωmax)
      = normV / eps + (ΔΩ + Ωε) / (2 * Ωmax) := by
    field_simp [hΩmax.ne', heps.ne']
    ring
  linarith [hStep2, hChained, hEq]


/-- Discarding the bath contracts the distance of Hermitian normalized supports. -/
theorem support_distance_contracts {dS dB : ℕ} (M : MicrocanonicalPair dS dB)
    (hG : M.G.IsHermitian) (hF : M.F.IsHermitian) :
    traceDistance M.ωS M.ωSZero ≤ traceDistanceGen M.ω M.ωZero := by
  exact traceDistanceGen_partialTrace_le
    (isHermitian_dephasedState hG M.ΩG) (isHermitian_dephasedState hF M.ΩF)

end Qatlib.Papers.Thermalize11.MainResults.Theorem1
