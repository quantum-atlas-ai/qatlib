/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.NoncommHSP98.MainResults.AbelianGen
public import Qatlib.Papers.ExactSimon97.MainResults.GenExpect
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators Classical

/-!
# Section 6 of [BrassardHoyer1997]: inverse-polylogarithmic success fraction

The source's §6 note: with a suitable efficiently computable marking predicate that
vanishes on the previously generated subgroup and has known success fraction `1/k` on
the hidden annihilator, exact amplification can ensure progress for `k` bounded by a
fixed power of `log |G|`, conditional on exact available Fourier transforms. In the
public library the exact-amplification ingredient is the known-`a` design of
`AmplifyCore` (`zoo_amplitude_amplification_known_a_exact`), which achieves success
probability one at known mass `a` with call count at most a constant multiple of
`1 / √a`.

This module proves conditional probability and arithmetic components. It does not
construct an amplification program or derive the supplied output law or call bound:

* `marked_fraction_mass`: under the exact-sampling interface (Fourier readout of a
  coset state of `K`, uniform on the annihilator by the public
  `bornProb_genCosetState_uniform`), a marking predicate whose marked labels form a
  `1/k` fraction of the hidden annihilator has per-call success mass exactly `1/k`.
* `marked_progress`: a marked label lies outside the previously generated subgroup,
  so a successful amplified output always makes progress.
* `amplified_calls_polylog`: a design that achieves success probability one at known
  mass `a = 1/k` with call count at most `C / √a` — the guarantee of the public
  known-`a` design — uses at most `C * √k ≤ C * (log₂ cG) ^ (e / 2)` calls whenever
  `k ≤ (log₂ cG) ^ e`.
* `polylog_progress`: the composite conditional statement of the source note — a
  success-one design concentrated on marked labels makes progress on every output
  with polylogarithmic calls, conditional on the exact sampling law.

Interface boundary: exact sampling is the uniform annihilator law. The output
law and its marked support, as well as the billed call bound, are independent
explicit hypotheses. No invocation of the public amplification theorem or produced
program bridges these hypotheses here. The hidden subgroup `H` and the generated
subgroup `J ≤ annihilatorGen H` have distinct roles.
-/

namespace Qatlib.Papers.ExactSimon97.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.StabilizerAlg.NearUniformGen
open Qatlib.Papers.ExactSimon97.MainResults
open Qatlib.Papers.NoncommHSP98.MainResults

section PolylogProgress

variable {n : ℕ} {m : Fin n → ℕ} [∀ i, NeZero (m i)]

/-- The marked labels of the marking predicate, as a finite set. -/
noncomputable def markedSet (χ : AbGroup n m → Bool) : Finset (AbGroup n m) :=
  Finset.univ.filter (fun ℓ => χ ℓ = true)

/-- Under the exact-sampling interface, the per-call success mass of a marking
predicate whose marked labels form exactly a `1/k` fraction of the hidden
annihilator is `1/k`: the uniform annihilator-label law gives mass
`|marked| / |ann|`, and the cardinality hypothesis identifies this as `1/k`. -/
theorem marked_fraction_mass (K : AddSubgroup (AbGroup n m)) (χ : AbGroup n m → Bool)
    (k : ℕ) (hk1 : 1 ≤ k)
    (hsub : ∀ ℓ ∈ markedSet χ, ℓ ∈ annihilatorGen K)
    (hcard : Fintype.card ↥(annihilatorGen K) = k * (markedSet χ).card) :
    ∑ ℓ ∈ markedSet χ, (unifOnSub (annihilatorGen K)).prob ℓ = 1 / (k : ℝ) := by
  have hterm : ∀ ℓ ∈ markedSet χ,
      (unifOnSub (annihilatorGen K)).prob ℓ = 1 / (Fintype.card ↥(annihilatorGen K) : ℝ) :=
    fun ℓ hℓ => by simp [unifOnSub, hsub ℓ hℓ]
  have hposcard : (0 : ℕ) < Fintype.card ↥(annihilatorGen K) :=
    Fintype.card_pos_iff.mpr ⟨⟨0, AddSubgroup.zero_mem _⟩⟩
  have hmc : (0 : ℕ) < (markedSet χ).card := by
    rw [hcard] at hposcard
    rcases Nat.eq_zero_or_pos (markedSet χ).card with h0 | hpos
    · rw [h0] at hposcard
      omega
    · exact hpos
  have hmcR : ((markedSet χ).card : ℝ) ≠ 0 := by positivity
  have hkR : ((k : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_congr rfl hterm, sum_one_div, hcard]
  push_cast
  field_simp

/-- A marked label lies outside the previously generated subgroup: the marking
predicate vanishes on the subgroup, so a marked label cannot be a member. -/
theorem marked_progress (K : AddSubgroup (AbGroup n m)) (χ : AbGroup n m → Bool)
    (hvanish : ∀ g ∈ K, χ g = false) (ℓ : AbGroup n m) (hℓ : ℓ ∈ markedSet χ) :
    ℓ ∉ K := by
  intro hmem
  simp only [markedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
  rw [hvanish ℓ hmem] at hℓ
  exact Bool.noConfusion hℓ

/-- A success-one amplification design working at known mass `a = 1/k` with call
count at most `C / √a` — the guarantee of the public
`zoo_amplitude_amplification_known_a_exact` design — uses at most `C * √k` calls,
and this is at most `C * (log₂ cG) ^ (e / 2)` whenever `k ≤ (log₂ cG) ^ e` with
`cG ≥ 2`. -/
theorem amplified_calls_polylog (k e : ℕ) (cG : ℕ) (C : ℝ) (hC : 0 < C)
    (_hk1 : 1 ≤ k) (hcG : 2 ≤ cG)
    (hbound : (k : ℝ) ≤ Real.logb 2 (cG : ℝ) ^ (e : ℝ))
    (calls : ℝ) (hcalls : calls ≤ C / Real.sqrt ((1 : ℝ) / (k : ℝ))) :
    calls ≤ C * Real.logb 2 (cG : ℝ) ^ ((e : ℝ) / 2) := by
  have hLpos : (0 : ℝ) < Real.logb 2 (cG : ℝ) :=
    Real.logb_pos (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (by omega : (1 : ℕ) < cG))
  have hsqrteq : Real.sqrt ((1 : ℝ) / (k : ℝ)) = 1 / Real.sqrt ((k : ℝ)) := by
    rw [one_div, Real.sqrt_inv, one_div]
  have hinv : C / Real.sqrt ((1 : ℝ) / (k : ℝ)) = C * Real.sqrt ((k : ℝ)) := by
    rw [hsqrteq, one_div, div_eq_mul_inv, inv_inv]
  have hspliteq : Real.sqrt (Real.logb 2 (cG : ℝ) ^ (e : ℝ)) =
      Real.logb 2 (cG : ℝ) ^ ((e : ℝ) / 2) := by
    have h1 : (Real.logb 2 (cG : ℝ) ^ (e : ℝ)) ^ ((1 : ℝ) / 2)
        = Real.logb 2 (cG : ℝ) ^ ((e : ℝ) * ((1 : ℝ) / 2)) :=
      (Real.rpow_mul hLpos.le ((e : ℝ)) ((1 : ℝ) / 2)).symm
    rw [Real.sqrt_eq_rpow, h1]
    congr 1
    field_simp
  have hmono : Real.sqrt ((k : ℝ)) ≤ Real.logb 2 (cG : ℝ) ^ ((e : ℝ) / 2) := by
    rw [← hspliteq]
    exact Real.sqrt_le_sqrt hbound
  calc calls ≤ C / Real.sqrt ((1 : ℝ) / (k : ℝ)) := hcalls
    _ = C * Real.sqrt ((k : ℝ)) := hinv
    _ ≤ C * Real.logb 2 (cG : ℝ) ^ ((e : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hmono hC.le

/-- Conditional §6 arithmetic: for hidden subgroup `H` and generated subgroup
`J ≤ annihilatorGen H`, a supplied normalized law supported on marked labels
escapes `J`. The supplied call bound yields the polylogarithmic inequality; the
uniform hidden-annihilator law yields the marked mass. No amplified program is
constructed by this lemma. -/
theorem polylog_progress (H J : AddSubgroup (AbGroup n m))
    (_hJH : J ≤ annihilatorGen H) (χ : AbGroup n m → Bool)
    (k e : ℕ) (hk1 : 1 ≤ k)
    (hvanish : ∀ g ∈ J, χ g = false)
    (hsub : ∀ ℓ ∈ markedSet χ, ℓ ∈ annihilatorGen H)
    (hcard : Fintype.card ↥(annihilatorGen H) = k * (markedSet χ).card)
    (hG2 : 2 ≤ Fintype.card (AbGroup n m))
    (hbound : (k : ℝ) ≤ Real.logb 2 (Fintype.card (AbGroup n m) : ℝ) ^ (e : ℝ))
    (C : ℝ) (hC : 0 < C) (calls : ℝ)
    (hcalls : calls ≤ C / Real.sqrt ((1 : ℝ) / (k : ℝ)))
    (ν : FinDist (AbGroup n m))
    (hν : ∀ ℓ, χ ℓ = false → ν.prob ℓ = 0) :
    (∀ ℓ ∈ J, ν.prob ℓ = 0) ∧
      (calls ≤ C * Real.logb 2 (Fintype.card (AbGroup n m) : ℝ) ^ ((e : ℝ) / 2)) ∧
      (∑ ℓ ∈ markedSet χ, (unifOnSub (annihilatorGen H)).prob ℓ = 1 / (k : ℝ)) := by
  exact ⟨fun ℓ hℓ => hν ℓ (hvanish ℓ hℓ),
    amplified_calls_polylog k e (Fintype.card (AbGroup n m)) C hC hk1 hG2 hbound calls hcalls,
    marked_fraction_mass H χ k hk1 hsub hcard⟩

end PolylogProgress

end Qatlib.Papers.ExactSimon97.MainResults
