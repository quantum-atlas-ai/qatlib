/-
Copyright (c) 2026 qatlas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/
module

public import Qatlib.Papers.DynamicProg24.MainResults.SourceModel
public import Mathlib.Tactic.NoncommRing

@[expose] public section


set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace Qatlib.Papers.DynamicProg24.MainResults

open Qatlib.Papers.DynamicProg24.MainResults

/-- Lemma 13 (arXiv:2403.09187, p. 20, Eq. (S76) ⟹ Eq. (S80)).

Suppose the recursion parameter of Eq. (S74) is chosen as `q = δ_n` at every step, so that the
distances obey `δ_{n+1} = sech ((2L+1) arcsech δ_n)` (Eq. (S76)) starting from `δ_0`.  Then the
recursion has the closed form of Eq. (S80),
`δ_N = sech ((2L+1)^N · arcosh (δ_0⁻¹))`.

The proof is the induction of Eq. (S77)–(S79): the inverse of `sech y` is `cosh y`, and
`arcosh (cosh y) = y` for `y ≥ 0`, so each step multiplies the argument by `2L+1`. -/
theorem lemma13_closed_form {L : ℕ} {δ : ℕ → ℝ} {δ0 : ℝ}
    (hδ0 : δ 0 = δ0) (hδpos : 0 < δ0) (hδle : δ0 ≤ 1)
    (hrec : ∀ n : ℕ, δ (n + 1) = sech ((2 * (L : ℝ) + 1) * arcsech (δ n))) :
    ∀ N : ℕ, δ N = sech ((2 * (L : ℝ) + 1) ^ N * Real.arcosh δ0⁻¹) := by
  have hx1 : 1 ≤ δ0⁻¹ := by
    have := (one_le_div (a := (1 : ℝ)) (b := δ0) hδpos).2 hδle
    simpa [one_div] using this
  intro N
  induction N with
  | zero =>
      rw [hδ0]
      unfold sech
      rw [pow_zero, one_mul, Real.cosh_arcosh hx1, inv_inv]
  | succ n ih =>
      rw [hrec n, ih]
      have hM0 : (0 : ℝ) ≤ 2 * (L : ℝ) + 1 := by positivity
      have hy : 0 ≤ (2 * (L : ℝ) + 1) ^ n * Real.arcosh δ0⁻¹ :=
        mul_nonneg (pow_nonneg hM0 n) (Real.arcosh_nonneg hx1)
      have hstep : (2 * (L : ℝ) + 1) *
            arcsech (sech ((2 * (L : ℝ) + 1) ^ n * Real.arcosh δ0⁻¹))
          = (2 * (L : ℝ) + 1) ^ (n + 1) * Real.arcosh δ0⁻¹ := by
        rw [arcsech_sech hy, pow_succ]
        ring
      rw [hstep]

/-- Lemma 13 (arXiv:2403.09187, p. 20, Eq. (S76), (S80)): the distance statement itself.

If the states `ψ_n` realize the recursion of Eq. (S76) with `q = δ_n`, i.e.
`½‖τ - ψ_{n+1}‖₁ = sech ((2L+1) · arcsech (½‖τ - ψ_n‖₁))`, then indeed
`½‖τ - ψ_N‖₁ = δ_N` with the closed form of Eq. (S80). -/
theorem lemma13_grover_distance {d : ℕ} (τ : Matrix (Fin d) (Fin d) ℂ)
    (ψ : ℕ → Matrix (Fin d) (Fin d) ℂ) (L : ℕ)
    {δ0 : ℝ} (hδ0 : traceDistance τ (ψ 0) = δ0) (hδpos : 0 < δ0) (hδle : δ0 ≤ 1)
    (hstep : ∀ n : ℕ, traceDistance τ (ψ (n + 1)) =
      sech ((2 * (L : ℝ) + 1) * arcsech (traceDistance τ (ψ n)))) (N : ℕ) :
    traceDistance τ (ψ N) = sech ((2 * (L : ℝ) + 1) ^ N * Real.arcosh δ0⁻¹) :=
  lemma13_closed_form (δ := fun n => traceDistance τ (ψ n)) hδ0 hδpos hδle hstep N

/-- The relative support subspace `S_rel` of Eq. (S89): the states `ρ` supported inside the
subspace of the projector `P`, i.e. `ρ = P ρ P`. -/
def InSrel {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ρ = P * ρ * P

/-- A scalar-affine combination of matrices that are all invariant under the sandwich
`X ↦ P X P` is again invariant.  This is the algebraic core of Proposition 14. -/
theorem sandwich_affine {d : ℕ} (P X Y Z : Matrix (Fin d) (Fin d) ℂ) (a b c : ℂ)
    (hX : P * X * P = X) (hY : P * Y * P = Y) (hZ : P * Z * P = Z) :
    P * (a • X - b • Y + c • Z) * P = a • X - b • Y + c • Z := by
  have h1 : P * (a • X) * P = a • X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hX]
  have h2 : P * (b • Y) * P = b • Y := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hY]
  have h3 : P * (c • Z) * P = c • Z := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hZ]
  have hexp : P * (a • X - b • Y + c • Z) * P
      = P * (a • X) * P - P * (b • Y) * P + P * (c • Z) * P := by
    rw [mul_add, mul_sub, add_mul, sub_mul]
  rw [hexp, h1, h2, h3]

/-- Proposition 14 (arXiv:2403.09187, p. 22, Eq. (S89)): the DME channel maps `S_rel × S_rel`
into `S_rel`.  If `ρ, σ ∈ S_rel` for the projector `P`, then so is
`E_s[ρ](σ) = cos²s · σ - i sin s cos s · [ρ, σ] + sin²s · ρ`.

Proof: `ρ = P ρ P` gives `P ρ = ρ = ρ P`, and likewise for `σ`, so every term of the DME
channel is invariant under `P · P`. -/
theorem proposition14_dme_preserves_srel {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P * P = P) (s : ℝ) {ρ σ : Matrix (Fin d) (Fin d) ℂ}
    (hρ : InSrel P ρ) (hσ : InSrel P σ) :
    InSrel P (dmeChannel s ρ σ) := by
  have hρl : P * ρ = ρ := by
    calc P * ρ = P * (P * ρ * P) := congrArg (fun X => P * X) hρ
      _ = (P * P) * ρ * P := by noncomm_ring
      _ = P * ρ * P := by rw [hP]
      _ = ρ := hρ.symm
  have hρr : ρ * P = ρ := by
    calc ρ * P = (P * ρ * P) * P := congrArg (fun X => X * P) hρ
      _ = P * ρ * (P * P) := by noncomm_ring
      _ = P * ρ * P := by rw [hP]
      _ = ρ := hρ.symm
  have hσl : P * σ = σ := by
    calc P * σ = P * (P * σ * P) := congrArg (fun X => P * X) hσ
      _ = (P * P) * σ * P := by noncomm_ring
      _ = P * σ * P := by rw [hP]
      _ = σ := hσ.symm
  have hσr : σ * P = σ := by
    calc σ * P = (P * σ * P) * P := congrArg (fun X => X * P) hσ
      _ = P * σ * (P * P) := by noncomm_ring
      _ = P * σ * P := by rw [hP]
      _ = σ := hσ.symm
  have hρσ : P * (ρ * σ) * P = ρ * σ := by
    rw [mul_assoc, mul_assoc, hσr, ← mul_assoc, hρl]
  have hσρ : P * (σ * ρ) * P = σ * ρ := by
    rw [mul_assoc, mul_assoc, hρr, ← mul_assoc, hσl]
  have hcomm : P * (ρ * σ - σ * ρ) * P = ρ * σ - σ * ρ := by
    rw [mul_sub, sub_mul, hρσ, hσρ]
  unfold InSrel dmeChannel
  exact (sandwich_affine P σ (ρ * σ - σ * ρ) ρ _ _ _ hσ.symm hcomm hρ.symm).symm

/-- A unitary channel that commutes with the projector `P` preserves `S_rel`. -/
theorem unitaryChannel_preserves_srel {d : ℕ} (P U X : Matrix (Fin d) (Fin d) ℂ)
    (hPh : Pᴴ = P) (hU : P * U = U * P) (hX : InSrel P X) :
    InSrel P (unitaryChannel U X) := by
  have hU' : P * Uᴴ = Uᴴ * P := by
    have := congrArg Matrix.conjTranspose hU
    simpa [Matrix.conjTranspose_mul, hPh] using this.symm
  unfold InSrel unitaryChannel
  exact (calc P * (U * X * Uᴴ) * P
      = (P * U) * X * (Uᴴ * P) := by noncomm_ring
    _ = (U * P) * X * (P * Uᴴ) := by rw [hU, ← hU']
    _ = U * (P * X * P) * Uᴴ := by noncomm_ring
    _ = U * X * Uᴴ := by rw [← hX]).symm

/-- Corollary 15 (arXiv:2403.09187, p. 22): the QDP implementation of Grover search using DME
generates states `ρ_n ∈ S_rel` for all `n`, provided `ρ_0 ∈ S_rel` and all reference states
`σ_n ∈ S_rel`, and the reflection unitaries commute with the support projector `P`.

Each step applies the DME channel (Proposition 14 preserves `S_rel`) followed by a reflection
unitary (which preserves `S_rel` because it commutes with `P`). -/
theorem corollary15_qdp_grover_in_srel {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (hP : P * P = P) (hPh : Pᴴ = P)
    (ρ σ : ℕ → Matrix (Fin d) (Fin d) ℂ) (s : ℕ → ℝ) (U : ℕ → Matrix (Fin d) (Fin d) ℂ)
    (hU : ∀ n, P * U n = U n * P)
    (hρ0 : InSrel P (ρ 0)) (hσ : ∀ n, InSrel P (σ n))
    (hstep : ∀ n, ρ (n + 1) = unitaryChannel (U n) (dmeChannel (s n) (ρ n) (σ n))) :
    ∀ n, InSrel P (ρ n) := by
  intro n
  induction n with
  | zero => exact hρ0
  | succ k ih =>
      rw [hstep k]
      exact unitaryChannel_preserves_srel P (U k) (dmeChannel (s k) (ρ k) (σ k)) hPh (hU k)
        (proposition14_dme_preserves_srel P hP (s k) ih (hσ k))

/-- Proposition 16 (arXiv:2403.09187, p. 23, Eq. (S94)): a dynamic unitary channel assembled
from `L` DME layers, each built from a mixture `ρ = (1 - 2x) ψ + x · 1_rel` with
`x ≤ ε < 1/2`, is at trace distance at most `L π ε` from the dynamic unitary channel built
from the associated pure state `ψ`.

Formalized as the telescoping of the per-layer bound: if every layer adds at most `π ε` to the
distance to the pure-state channel, then after `L` layers the distance is at most `L π ε`. -/
theorem proposition16_dynamic_channel_distance {d L : ℕ}
    (Φψ Φρ : ℕ → Matrix (Fin d) (Fin d) ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h0 : traceDistance (Φψ 0) (Φρ 0) = 0)
    (hinc : ∀ l : ℕ, traceDistance (Φψ (l + 1)) (Φρ (l + 1))
        ≤ traceDistance (Φψ l) (Φρ l) + Real.pi * ε) :
    traceDistance (Φψ L) (Φρ L) ≤ (L : ℝ) * Real.pi * ε := by
  have hpi : (0 : ℝ) ≤ Real.pi * ε := mul_nonneg Real.pi_pos.le hε
  induction L with
  | zero => rw [h0]; simp
  | succ k ih =>
      have h := hinc k
      have hcast : ((k + 1 : ℕ) : ℝ) * Real.pi * ε
          = ((k : ℝ) * Real.pi * ε) + Real.pi * ε := by
        push_cast
        ring
      rw [hcast]
      linarith

/-- Corollary 18 (arXiv:2403.09187, p. 25, Eq. (S120)): the state `ρ'` of Lemma 17 has an
associated pure state `ψ_n` with `½‖τ - ψ_n‖₁ ≤ δ_n`.

Proof: `½‖τ - ψ_n‖₁ ≤ ½‖τ - ρ'‖₁ + ½‖ρ' - ψ_n‖₁ ≤ (δ_n - ε/4) + ε/4 = δ_n`, where the second
term is the mixedness/association error of the DME subroutine. -/
theorem corollary18_associated_pure_state {d : ℕ} (τ ρ ψ : Matrix (Fin d) (Fin d) ℂ)
    {δ ε : ℝ} (h17 : traceDistance τ ρ ≤ δ - ε / 4) (hmix : traceDistance ρ ψ ≤ ε / 4) :
    traceDistance τ ψ ≤ δ := by
  have h1 : traceDistance τ ψ ≤ traceDistance τ ρ + traceDistance ρ ψ :=
    traceDistance_triangle τ ρ ψ
  linarith

end Qatlib.Papers.DynamicProg24.MainResults
