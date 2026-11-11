/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.SpinChainMix26.RapidMixing
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/-!
# Poisson-clock representation of the Petz block heat-bath dynamics

Paper layer for *Rapid mixing of quantum spin chains at any finite temperature*
(arXiv:2610.01190v1, fixed PDF SHA256
`444509dfd74293454797e2ed9e1a45905a1c463ecc999312ed947c91ab037e29`):

* Proposition 2.9 (§2, Eq. (23) and Eq. (27)): each block update fixes the Gibbs
  state, hence `Lℓ(σβ) = 0` and `σβ` is stationary for the semigroup `e^{tLℓ}`.
* Proposition 6.3 (§6.2, Eq. (118)): with `s = nt/ℓ` and `K ∼ Poisson(s)`, the
  semigroup is the expectation `e^{tLℓ} = E[Φ_{B_K} ∘ ⋯ ∘ Φ_{B_1}]` over `K`
  i.i.d. uniform blocks of length `ℓ`.

The generator is `L = (1/ℓ) Σ_s (Φ_s − I)`; writing `G = (1/ℓ) Σ_s Φ_s` for its
reset part, `L = G − (n/ℓ)·id`, so `e^{tL} = e^{−nt/ℓ} e^{tG}` and the exponential
series of `G` is exactly the Poisson mixture of composed block updates.
-/

namespace Qatlib.Papers.SpinChainMix26.RapidMixing
namespace PoissonClock

set_option autoImplicit false

/-! ## The reset part `G` of the Petz generator -/

/-- Reset part `G = (1/ℓ) Σ_s Φ_s` of the Petz block generator: the average block
update without the constant shift `−(n/ℓ)·id` that makes `L = G − (n/ℓ)·id`. -/
noncomputable def blockResetAvg {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (ρ : Operator (d ^ n)) : Operator (d ^ n) :=
  ((1 : ℂ) / ℓ) • ∑ s : Fin n, petzHeatBath (cuts s) σ ρ

/-- The Petz generator is the reset part minus the constant shift `(n/ℓ)·id`. -/
lemma petzGenerator_eq_blockResetAvg_sub {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (ρ : Operator (d ^ n)) :
    petzGenerator cuts σ ρ = blockResetAvg cuts σ ρ - (((n : ℂ) / ℓ) • ρ) := by
  unfold petzGenerator blockResetAvg
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  have hsum : (∑ _s : Fin n, ρ) = ((n : ℂ) • ρ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact (Nat.cast_smul_eq_nsmul ℂ n ρ).symm
  rw [hsum, smul_smul]
  congr 1
  field_simp

/-- The reset part is additive in the state. -/
lemma blockResetAvg_add {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (ρ τ : Operator (d ^ n)) :
    blockResetAvg cuts σ (ρ + τ) = blockResetAvg cuts σ ρ + blockResetAvg cuts σ τ := by
  unfold blockResetAvg
  simp only [petzHeatBath_add, Finset.sum_add_distrib, smul_add]

/-- The reset part is complex-linear in the state. -/
lemma blockResetAvg_smul {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (k : ℂ) (ρ : Operator (d ^ n)) :
    blockResetAvg cuts σ (k • ρ) = k • blockResetAvg cuts σ ρ := by
  unfold blockResetAvg
  have h1 : ∀ s : Fin n, petzHeatBath (cuts s) σ (k • ρ) = k • petzHeatBath (cuts s) σ ρ :=
    fun s => petzHeatBath_smul (cuts s) σ k ρ
  simp only [h1, Finset.smul_sum, smul_smul]
  congr 1
  funext s
  congr 1
  ring

/-- The reset part annihilates the zero operator. -/
lemma blockResetAvg_zero {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) : blockResetAvg cuts σ 0 = 0 := by
  have h := blockResetAvg_smul cuts σ 0 (0 : Operator (d ^ n))
  rw [zero_smul, zero_smul] at h
  exact h

/-! ## Factorization of `e^{tL}` over the reset part -/

/-- Constant-shift factorization of the semigroup: with `L = G − (n/ℓ)·id`,
`e^{tL}ρ = e^{−nt/ℓ} · e^{tG}ρ`. This is the paper's rewriting `Lℓ = (Nℓ/ℓ)(Φℓ − I)`
of Proposition 2.9 in the block-reset normalization. -/
lemma superExp_petzGenerator_factor {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) :
    superExp (petzGenerator cuts σ) t ρ
      = (((Real.exp (-(t : ℝ) * (n : ℝ) / ℓ) : ℝ) : ℂ))
        • superExp (blockResetAvg cuts σ) t ρ := by
  set G : Operator (d ^ n) → Operator (d ^ n) := blockResetAvg cuts σ
  set c : ℂ := -(((n : ℂ) / ℓ))
  have hmap : petzGenerator cuts σ = fun τ : Operator (d ^ n) => G τ + c • τ := by
    funext τ
    have h1 := petzGenerator_eq_blockResetAvg_sub cuts σ τ
    rw [h1]
    simp only [G, c]
    rw [neg_smul]
    abel
  have hshift := superExp_shift_const G c t ρ
  rw [← hmap] at hshift
  rw [hshift]
  congr 1
  have harg : (t : ℂ) * c = (((-(t : ℝ) * (n : ℝ) / ℓ) : ℝ) : ℂ) := by
    rw [show c = -(((n : ℂ) / ℓ)) from rfl]
    push_cast
    ring_nf
  rw [harg, complex_exp_ofReal]

/-! ## Iterates of the reset part and the exponential series -/

/-- The iterates of the reset part are weighted sums over sequences of block
updates: `G^[k]ρ = (1/ℓ)^k · Σ_s Φ_{s k} ∘ ⋯ ∘ Φ_{s 1}(ρ)`. -/
lemma blockResetAvg_iterate {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (k : ℕ) (ρ : Operator (d ^ n)) :
    (blockResetAvg cuts σ)^[k] ρ
      = (((1 : ℂ) / ℓ) ^ k) •
          ∑ s : Fin k → Fin n, heatBathComp cuts σ k s ρ := by
  induction k with
  | zero =>
    have hsum : ∑ s : Fin 0 → Fin n, heatBathComp cuts σ 0 s ρ = ρ :=
      Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)
    rw [Function.iterate_zero_apply, hsum, pow_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, blockResetAvg_smul]
    have hG : ∀ X : Operator (d ^ n),
        blockResetAvg cuts σ X
          = (((1 : ℂ) / ℓ)) • ∑ j : Fin n, petzHeatBath (cuts j) σ X := fun X => rfl
    rw [hG]
    have hpt : (∑ j : Fin n, petzHeatBath (cuts j) σ
          (∑ s : Fin k → Fin n, heatBathComp cuts σ k s ρ))
        = (∑ j : Fin n, ∑ s : Fin k → Fin n,
            petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact petzHeatBath_sum_univ _ _ _
    have hcomp : ∀ (j : Fin n) (s : Fin k → Fin n),
        petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ)
          = heatBathComp cuts σ (k + 1) (Fin.cons j s) ρ := by
      intro j s
      exact (heatBathComp_cons cuts σ j s ρ).symm
    have hcomp2 :
        (∑ j : Fin n, ∑ s : Fin k → Fin n, petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ))
          = (∑ j : Fin n, ∑ s : Fin k → Fin n,
              heatBathComp cuts σ (k + 1) (Fin.cons j s) ρ) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact Finset.sum_congr rfl (fun s _ => hcomp j s)
    rw [hpt, hcomp2, sum_cons_univ, smul_smul, ← pow_succ]

/-- Operator-valued exponential series of the reset part:
`e^{tG}ρ = Σ_k (t^k/k!) · G^[k]ρ`. -/
lemma superExp_blockResetAvg_eq_tsum {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) :
    superExp (blockResetAvg cuts σ) t ρ
      = ∑' k : ℕ, ((expCoeff t k : ℝ) : ℂ) • (blockResetAvg cuts σ)^[k] ρ := by
  set G : Operator (d ^ n) → Operator (d ^ n) := blockResetAvg cuts σ with hG
  have hadd : ∀ ρ τ : Operator (d ^ n), G (ρ + τ) = G ρ + G τ :=
    fun ρ τ => blockResetAvg_add cuts σ ρ τ
  have hzero : G 0 = 0 := blockResetAvg_zero cuts σ
  have hsmulG : ∀ (k : ℂ) (ρ : Operator (d ^ n)), G (k • ρ) = k • G ρ :=
    fun k ρ => blockResetAvg_smul cuts σ k ρ
  have hsum : Summable (fun k : ℕ => ((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) := by
    have hentry : ∀ i j : Fin (d ^ n),
        Summable (fun k : ℕ => (((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) i j) := by
      intro i j
      have hsm : ∀ k : ℕ, (((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) i j
          = (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((G^[k] ρ) i j) := by
        intro k
        rw [Matrix.smul_apply, expCoeff_eq]
        exact smul_eq_mul _ _
      exact Summable.congr (summable_expCoeff_mul_iterate_gen G hadd hzero hsmulG t ρ i j) hsm
    exact Pi.summable.mpr fun i => Pi.summable.mpr fun j => hentry i j
  ext i j
  rw [tsum_matrix_apply _ hsum i j]
  have hsm : ∀ k : ℕ, (((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) i j
      = (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((G^[k] ρ) i j) := by
    intro k
    rw [Matrix.smul_apply, expCoeff_eq]
    exact smul_eq_mul _ _
  simp only [hsm]
  exact superExp_entry_eq_tsum G hadd hzero hsmulG t ρ i j

/-- The exponential series of the reset part as a sum over sequences of blocks:
`e^{tG}ρ = Σ_k ((t^k/k!)(1/ℓ)^k) · Σ_s Φ_{s k} ∘ ⋯ ∘ Φ_{s 1}(ρ)`. -/
lemma superExp_blockResetAvg_eq_blockSum {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) :
    superExp (blockResetAvg cuts σ) t ρ
      = ∑' k : ℕ, ((((expCoeff t k : ℝ) : ℂ) * ((1 : ℂ) / ℓ) ^ k))
          • ∑ s : Fin k → Fin n, heatBathComp cuts σ k s ρ := by
  rw [superExp_blockResetAvg_eq_tsum]
  refine tsum_congr ?_
  intro k
  rw [blockResetAvg_iterate, smul_smul]

/-! ## The Poisson weights and the uniform block average -/

/-- Poisson weight `P(K = k)` of the block-update count `K ∼ Poisson(s)`:
`e^{−s} s^k / k!`. -/
noncomputable def poissonWeight (s : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-s) * s ^ k / (k.factorial : ℝ)

/-- Uniform average of the composed block updates over `k` i.i.d. uniform blocks of
length `ℓ`: `n^{-k} Σ_{s} Φ_{s k} ∘ ⋯ ∘ Φ_{s 1}`. -/
noncomputable def uniformCompAvg {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (k : ℕ) (ρ : Operator (d ^ n)) : Operator (d ^ n) :=
  (((1 : ℂ) / (n : ℂ)) ^ k) •
    ∑ s : Fin k → Fin n, heatBathComp cuts σ k s ρ

/-- The Poisson weights of the update count sum to one: the Poisson-clock expansion
is a genuine (convex) mixture of composed block updates. -/
lemma poissonWeight_sum_one (s : ℝ) : ∑' k : ℕ, poissonWeight s k = 1 := by
  have hfun : ∀ k : ℕ, poissonWeight s k = Real.exp (-s) * (s ^ k / (k.factorial : ℝ)) := by
    intro k
    unfold poissonWeight
    ring
  calc ∑' k : ℕ, poissonWeight s k
      = ∑' k : ℕ, Real.exp (-s) * (s ^ k / (k.factorial : ℝ)) := tsum_congr hfun
    _ = Real.exp (-s) * ∑' k : ℕ, (s ^ k / (k.factorial : ℝ)) := tsum_mul_left
    _ = Real.exp (-s) * Real.exp s := by
        congr 1
        exact (real_exp_eq_tsum s).symm
    _ = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- **Proposition 6.3 (Poisson-clock representation of `e^{tLℓ}`).** With
`s = nt/ℓ` and `K ∼ Poisson(s)`, and conditioned on `K` the blocks chosen i.i.d.
uniformly from the `n` blocks of length `ℓ`,
`e^{tLℓ} = E[Φ_{B_K} ∘ ⋯ ∘ Φ_{B_1}]`, i.e.
`e^{tL}ρ = Σ_k P(K = k) · n^{-k} Σ_{s} Φ_{s k} ∘ ⋯ ∘ Φ_{s 1}(ρ)`. -/
theorem superExp_petzGenerator_poisson {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) (hn : 0 < n) (hℓ : 0 < ℓ) :
    superExp (petzGenerator cuts σ) t ρ
      = ∑' k : ℕ, ((poissonWeight ((n : ℝ) * t / ℓ) k : ℝ) : ℂ)
          • uniformCompAvg cuts σ k ρ := by
  set s : ℝ := (n : ℝ) * t / ℓ with hs
  have hn' : (n : ℂ) ≠ 0 := by
    have h : (n : ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  have hℓ' : (ℓ : ℂ) ≠ 0 := by
    have h : (ℓ : ℝ) ≠ 0 := by positivity
    exact_mod_cast h
  -- The series coefficient of the shifted expansion is the Poisson weight times the
  -- uniform-block normalization `n^{-k}`.
  have hweight : ∀ k : ℕ,
      (((Real.exp (-s) : ℝ) : ℂ) * (((expCoeff t k : ℝ) : ℂ) * ((1 : ℂ) / (ℓ : ℂ)) ^ k))
        = ((poissonWeight s k : ℝ) : ℂ) * (((1 : ℂ) / (n : ℂ)) ^ k) := by
    intro k
    unfold expCoeff poissonWeight
    rw [hs]
    push_cast
    field_simp
    have hkey : ((t : ℂ) * (1 / (ℓ : ℂ))) ^ k
        = (((n : ℂ) * t / (ℓ : ℂ)) * (1 / (n : ℂ))) ^ k := by
      congr 1
      field_simp
    rw [← mul_pow, ← mul_pow, hkey]
  rw [superExp_petzGenerator_factor, superExp_blockResetAvg_eq_blockSum]
  have harg : (-(t : ℝ) * (n : ℝ) / (ℓ : ℝ)) = -s := by
    rw [hs]
    ring
  rw [harg]
  rw [← tsum_const_smul'']
  refine tsum_congr ?_
  intro k
  rw [smul_smul, hweight]
  unfold uniformCompAvg
  rw [smul_smul]

/-! ## Stationarity of the Gibbs state (Proposition 2.9) -/

/-- **Proposition 2.9, stationarity part.** If the Gibbs reference state `σ` is
positive semidefinite and every kept-factor marginal entering the Petz cut is
positive definite, then every block update fixes `σ`, so the generator annihilates
it: `Lℓ(σβ) = 0`. -/
lemma petzGenerator_stationary {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (hσ : σ.PosSemidef)
    (hσA : ∀ s : Fin n,
      (PartialTrace (Matrix.reindex ((cuts s).matrixEquiv (d := d))
        ((cuts s).matrixEquiv (d := d)) σ)).PosDef) :
    petzGenerator cuts σ σ = 0 := by
  have hterm : ∀ s : Fin n, petzHeatBath (cuts s) σ σ - σ = 0 := by
    intro s
    rw [petzHeatBath_stationary (cuts s) σ hσ (hσA s), sub_self]
  unfold petzGenerator
  rw [Finset.sum_eq_zero (fun s _ => hterm s)]
  simp

/-- **Proposition 2.9, semigroup part.** The Gibbs state is stationary for the
semigroup: `e^{tLℓ}(σβ) = σβ` for every `t`. -/
theorem superExp_petzGenerator_stationary {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (hσ : σ.PosSemidef)
    (hσA : ∀ s : Fin n,
      (PartialTrace (Matrix.reindex ((cuts s).matrixEquiv (d := d))
        ((cuts s).matrixEquiv (d := d)) σ)).PosDef)
    (t : ℝ) : superExp (petzGenerator cuts σ) t σ = σ := by
  have hL : petzGenerator cuts σ σ = 0 := petzGenerator_stationary cuts σ hσ hσA
  have hiter : ∀ k : ℕ, ((petzGenerator cuts σ)^[k]) σ = if k = 0 then σ else 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      cases k with
      | zero =>
        rw [if_pos rfl, hL]
        simp
      | succ k =>
        rw [if_neg (Nat.succ_ne_zero k), petzGenerator_zero]
        simp
  ext i j
  rw [superExp_entry_eq_tsum (petzGenerator cuts σ) (petzGenerator_add cuts σ)
    (petzGenerator_zero cuts σ) (petzGenerator_smul cuts σ) t σ i j]
  have hterm : ∀ k : ℕ,
      (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * (((petzGenerator cuts σ)^[k]) σ) i j
        = if k = 0 then σ i j else 0 := by
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [hiter (k + 1)]
      simp
  rw [tsum_congr hterm, tsum_eq_single 0 (fun b hb => by simp [hb])]
  simp

end PoissonClock
end Qatlib.Papers.SpinChainMix26.RapidMixing
