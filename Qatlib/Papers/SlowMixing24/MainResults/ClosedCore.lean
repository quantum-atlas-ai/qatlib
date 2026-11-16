/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SlowMixing24.MainResults.SourceModel
public import Qatlib.Papers.SlowMixing24.MainResults.FaultLine.Definitions
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


/-! Finite metric transfer and pointwise spin-energy ratio inequalities. No global Gibbs mixing-time theorem is asserted. -/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator Classical ComplexOrder

namespace Qatlib.Papers.SlowMixing24.MainResults.ClosedCore
open Qatlib.Papers.SlowMixing24.MainResults
open Qatlib.Papers.SlowMixing24.MainResults.FaultLine
open Qatlib.Concepts.LindbladFlow.GkslSemigroup
open Qatlib.Concepts.LindbladFlow.GkslSemigroup.LindbladSemigroupCore
open Qatlib.Foundations.PureStateMath

/-! Mathematical identities for the source model. -/

/-- The first-order Euler step `I + δL` of a GKSL generator. -/
noncomputable def eulerStep {n : ℕ} (G : Gksl n) (δ : ℝ) : Op n → Op n :=
  fun ρ => ρ + (δ : ℂ) • lindbladApply G ρ

/-- **Core metric step of Corollary 2.2** (proved).

If, for every `t < K δ`, the continuous evolution is `ε_app`-close to the
`⌊t/δ⌋`-th Euler iterate, and every Euler iterate `k < K` is at distance
`> ε + ε_app` from `ρ` for some density operator, then for every `t < K δ`
the continuous evolution is at distance `> ε` from `ρ`.

This is exactly the triangle-inequality argument in the proof of
Corollary 2.2 (arXiv:2411.04300v2, p. 13): the approximation error cannot be
larger than the gap `ε` left by the discrete sampler. -/
theorem discrete_to_continuous_mixing_transfer {n : ℕ}
    (T : Chan n) (G : Gksl n) (ρ : Op n) (δ : ℝ) (K : ℕ) (ε εapp : ℝ)
    (hδ : 0 < δ)
    (happrox : ∀ t : ℝ, 0 ≤ t → t < (K : ℝ) * δ → ∀ σ : Op n,
      IsDensityOperator σ →
      traceDistance (lindbladSemigroup G t σ)
        (((T : Op n → Op n)^[Nat.floor (t / δ)]) σ) ≤ εapp)
    (hmix : ∀ k : ℕ, k < K → ∃ σ : Op n, IsDensityOperator σ ∧
      ε + εapp < traceDistance (((T : Op n → Op n)^[k]) σ) ρ) :
    ∀ t : ℝ, 0 ≤ t → t < (K : ℝ) * δ →
      ∃ σ : Op n, IsDensityOperator σ ∧
        ε < traceDistance (lindbladSemigroup G t σ) ρ := by
  intro t ht0 htK
  have hratio : t / δ < (K : ℝ) := by
    rw [div_lt_iff₀ hδ]
    exact htK
  have hfloor : Nat.floor (t / δ) < K := by
    rw [Nat.floor_lt]
    · exact_mod_cast hratio
    · exact div_nonneg ht0 hδ.le
  obtain ⟨σ, hσ, hdist⟩ := hmix (Nat.floor (t / δ)) hfloor
  refine ⟨σ, hσ, ?_⟩
  have happ := happrox t ht0 htK σ hσ
  have htri := traceDistance_triangle'
    (((T : Op n → Op n)^[Nat.floor (t / δ)]) σ) ρ (lindbladSemigroup G t σ)
  have hsymm := traceDistance_comm' (lindbladSemigroup G t σ)
    (((T : Op n → Op n)^[Nat.floor (t / δ)]) σ)
  rw [← hsymm] at htri
  linarith

/-! Mathematical identities for the source model. -/

/-- Feynman--Kac energy `Σ_{⟨i,j⟩} σ_i s_i σ_j s_j` of a spin-flip sample `s`
against a reference configuration `σ`. -/
noncomputable def fkEnergy {n : ℕ} (nb : Finset (Fin n × Fin n)) (σ s : St n) : ℝ :=
  ∑ p ∈ nb, spin σ p.1 * spin s p.1 * spin σ p.2 * spin s p.2

/-- The Boltzmann weight `exp(β Σ_{⟨i,j⟩} σ_i s_i σ_j s_j)` appearing in the
Feynman--Kac representation (Eq. (132)), at a fixed time slice. -/
noncomputable def fkWeight {n : ℕ} (nb : Finset (Fin n × Fin n)) (β : ℝ)
    (σ s : St n) : ℝ :=
  Real.exp (β * fkEnergy nb σ s)

/-- `m_∂S(s)`: the number of spins of `∂S` that are flipped in the sample `s`
relative to `σ` (Eq. (124)). -/
noncomputable def boundaryFlipCount {n : ℕ} (_dS : Finset (Fin n)) (σ s : St n) : ℕ :=
  (_dS.filter (fun i => σ i ≠ s i)).card

/-- An abstract spin-flip path measure: an averaging functional over samples,
normalised on constants. This stands for the Poisson-process measure `Ds(t)`
of Lemma 4.9; only positivity and normalisation are used by the statement. -/
structure SpinFlipPathMeasure (n : ℕ) where
  /-- The average over spin-flip samples. -/
  avg : (St n → ℝ) → ℝ
  /-- Averages of nonnegative functionals are nonnegative. -/
  avg_nonneg : ∀ f : St n → ℝ, (∀ s, 0 ≤ f s) → 0 ≤ avg f
  /-- Constants average to themselves. -/
  avg_const : ∀ c : ℝ, avg (fun _ => c) = c

/-- The Feynman--Kac average `f_m` of Lemma 4.9: the sample average of the
Boltzmann weight restricted to samples with exactly `m` boundary flips. -/
noncomputable def fkAverage {n : ℕ} (M : SpinFlipPathMeasure n)
    (nb : Finset (Fin n × Fin n)) (β : ℝ) (σ : St n) (_dS : Finset (Fin n))
    (m : ℕ) : ℝ :=
  M.avg (fun s => if boundaryFlipCount _dS σ s = m then fkWeight nb β σ s else 0)

/--  Fixed arXiv:2411.04300v2. Lemma 4.8, p. 33, Eqs. (124)--(127).

Let `σ` have a fault line of length `ℓ` with at most `k` defects, let `σ'`
be obtained by flipping all spins on one side (`S`) of the fault line, and let
`m` be the number of boundary spins `∂S` flipped in the sample `s`. Then the
ratio of the two Feynman--Kac exponentials is within
`exp[2β(ℓ − 2k ∓ 6m)]`:

`exp[2β(ℓ−2k−6m)] ≤ W(σ',s)/W(σ,s) ≤ exp[2β(ℓ−2k+6m)]`.

Hypotheses `hsign`/`hsignout` encode `σ'_iσ'_j = −σ_iσ_j` on the fault-line
edges and `= σ_iσ_j` elsewhere; `_hdefect` is `Σ_{N∂S} σ_iσ_j = −ℓ+2k`; `hflip`
bounds the change of that sum by `6` per flipped boundary spin. -/
theorem lemma48
    {n : ℕ} (nb NdS : Finset (Fin n × Fin n)) (_dS : Finset (Fin n))
    (σ σ' s : St n) (β : ℝ) (ℓ k m : ℕ)
    (hβ : 0 ≤ β)
    (hsub : NdS ⊆ nb)
    (hsign : ∀ p ∈ NdS,
      spin σ' p.1 * spin σ' p.2 = -(spin σ p.1 * spin σ p.2))
    (hsignout : ∀ p ∈ nb, p ∉ NdS →
      spin σ' p.1 * spin σ' p.2 = spin σ p.1 * spin σ p.2)
    (_hdefect : ∑ p ∈ NdS, spin σ p.1 * spin σ p.2 = -((ℓ : ℝ)) + 2 * (k : ℝ))
    (hflip : |(∑ p ∈ NdS, spin σ p.1 * spin s p.1 * spin σ p.2 * spin s p.2)
        - (-((ℓ : ℝ)) + 2 * (k : ℝ))| ≤ 6 * (m : ℝ)) :
    Real.exp (2 * β * ((ℓ : ℝ) - 2 * (k : ℝ) - 6 * (m : ℝ))) ≤
        fkWeight nb β σ' s / fkWeight nb β σ s ∧
      fkWeight nb β σ' s / fkWeight nb β σ s ≤
        Real.exp (2 * β * ((ℓ : ℝ) - 2 * (k : ℝ) + 6 * (m : ℝ))) := by
  -- Source: arXiv:2411.04300v2, Lemma 4.8, p. 33, Eqs. (125)--(127).
  -- Proof of (126): the `N∂S^c` contributions of `W(σ',s)/W(σ,s)` cancel and
  -- each `N∂S` edge flips sign, giving `R(s) = exp(-2β Σ_{N∂S} σ_i s_i σ_j s_j)`.
  -- Proof of (127): `Σ_{N∂S} σ_iσ_j = -ℓ+2k` and the `6`-per-flipped-spin
  -- energy change give `|Σ_{N∂S} σ_i s_i σ_j s_j - (-ℓ+2k)| ≤ 6m`.
  -- The time integral over `s(t)` is modelled by one time slice (`fkWeight`).
  set T : ℝ := ∑ p ∈ NdS, spin σ p.1 * spin s p.1 * spin σ p.2 * spin s p.2
  have hsplit : ∀ f : Fin n × Fin n → ℝ,
      (∑ p ∈ nb, f p) = (∑ p ∈ nb \ NdS, f p) + ∑ p ∈ NdS, f p := by
    intro f
    rw [← Finset.sum_sdiff hsub]
  -- the edges outside the fault line contribute identically on both sides
  have hout :
      (∑ p ∈ nb \ NdS, spin σ' p.1 * spin s p.1 * spin σ' p.2 * spin s p.2) =
        ∑ p ∈ nb \ NdS, spin σ p.1 * spin s p.1 * spin σ p.2 * spin s p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpnb, hpN⟩ := Finset.mem_sdiff.mp hp
    have hs := hsignout p hpnb hpN
    linear_combination (spin s p.1 * spin s p.2) * hs
  -- the edges on the fault line change sign
  have hin :
      (∑ p ∈ NdS, spin σ' p.1 * spin s p.1 * spin σ' p.2 * spin s p.2) =
        -∑ p ∈ NdS, spin σ p.1 * spin s p.1 * spin σ p.2 * spin s p.2 := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hs := hsign p hp
    linear_combination (spin s p.1 * spin s p.2) * hs
  have hE : fkEnergy nb σ' s - fkEnergy nb σ s = -2 * T := by
    simp only [fkEnergy]
    rw [hsplit (fun p => spin σ' p.1 * spin s p.1 * spin σ' p.2 * spin s p.2),
      hsplit (fun p => spin σ p.1 * spin s p.1 * spin σ p.2 * spin s p.2),
      hout, hin]
    simp only [T]
    ring
  have hratio : fkWeight nb β σ' s / fkWeight nb β σ s =
      Real.exp (β * (fkEnergy nb σ' s - fkEnergy nb σ s)) := by
    simp only [fkWeight]
    rw [← Real.exp_sub]
    congr 1
    ring
  have habs := abs_le.mp hflip
  have hTle : T ≤ -((ℓ : ℝ)) + 2 * (k : ℝ) + 6 * (m : ℝ) := by
    simp only [T]
    linarith [habs.2]
  have hTge : -((ℓ : ℝ)) + 2 * (k : ℝ) - 6 * (m : ℝ) ≤ T := by
    simp only [T]
    linarith [habs.1]
  constructor
  · rw [hratio]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hTle hβ
    rw [hE]
    nlinarith [h1]
  · rw [hratio]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hTge hβ
    rw [hE]
    nlinarith [h1]

/-- The function `g_{β,h}` of Equation (131). We write `sech(βh) = 1/cosh(βh)`. -/
noncomputable def gTFIM (β h : ℝ) (a : ℝ) : ℝ :=
  a + (1 / β) * Real.log (1 + (1 / Real.cosh (β * h)) * (Real.exp (-(a * β)) - 1))

/-- The legacy unconditional average vanishes for an impossible boundary-flip count. -/
theorem impossibleFlipAverage {n : ℕ} (M : SpinFlipPathMeasure n)
    (nb : Finset (Fin n × Fin n)) (β : ℝ) (σ : St n) (_dS : Finset (Fin n)) :
    fkAverage M nb β σ _dS (_dS.card + 1) = 0 := by
  have hf : (fun s => if boundaryFlipCount _dS σ s = _dS.card + 1
      then fkWeight nb β σ s else 0) = (fun _ => (0 : ℝ)) := by
    funext s
    apply ite_eq_right
    have hle : boundaryFlipCount _dS σ s ≤ _dS.card := Finset.card_filter_le _ _
    omega
  rw [fkAverage, hf, M.avg_const]

/-- A positive lower comparison at every flip count is false in the legacy finite model. -/
theorem noPositiveComparison {n : ℕ} (M : SpinFlipPathMeasure n)
    (nb : Finset (Fin n × Fin n)) (σ : St n) (_dS : Finset (Fin n)) (β : ℝ) :
    ¬ (∃ f : ℝ, 0 < f ∧ ∀ m : ℕ,
      Real.exp (-(8 * β * (m : ℝ))) * f ≤ fkAverage M nb β σ _dS m ∧
      fkAverage M nb β σ _dS m ≤ Real.exp (8 * β * (m : ℝ)) * f) := by
  rintro ⟨f, hf, hcompare⟩
  have hle := (hcompare (_dS.card + 1)).1
  rw [impossibleFlipAverage] at hle
  exact (not_le_of_gt (mul_pos (Real.exp_pos _) hf)) hle



end Qatlib.Papers.SlowMixing24.MainResults.ClosedCore
