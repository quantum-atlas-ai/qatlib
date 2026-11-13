/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecoveryRefinedDefs

/-!
# Algebraic recovery certificates and costs

This module collects algebraic recovery results for compact presentations, modular
exponentiation, local QFT circuits, random base factoring, and verified cyclic discrete
logarithms. The broader algorithmic setting is surveyed in [ChildsVanDam2010].

The endpoint theorems combine decoder agreement and annihilation with exact payload or circuit
formulas, and combine random base success with verification and work bounds. Each result retains
the hypotheses of its underlying recovery component.

## Main statements

* `alg_decoder_cross_checked`: independent and compact decoders agree.
* `clause17_endpoint`: combines annihilation, decoder agreement, and decomposition payload
  accounting.
* `clause18_endpoint`: records exponentiation word length and local QFT costs.
* `clause19_endpoint`: combines random base and verified discrete logarithm guarantees.

## References

* [Childs and van Dam, 2010][ChildsVanDam2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.QftPreparation.LocalQft
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.ReductionCore.CompactPresentation
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.AlgebraicRecovery

open Qatlib
open scoped Classical BigOperators

/-- The independent decoder agrees with the compact decoder on every list of factor labels. -/
theorem alg_decoder_cross_checked {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    independentDecode p L = compactDecode p L :=
  independentDecode_eq_compactDecode p L

/-- With positive Smith coefficients, the independently decoded vector annihilates each input
factor label coordinatewise modulo those coefficients. -/
theorem alg_decode_annihilates {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (hf : ∀ r : Fin m, 0 < p.coeff r) :
    ∀ l ∈ L, ∀ r : Fin m, p.coeff r ∣ l r * independentDecode p L r :=
  independentDecode_annihilates p L hf

/-- Encoding and then decoding reconstructs each presentation class; the empty label list also
satisfies the stated zero divisibility conditions. -/
theorem alg_reconstruction {m n : ℕ} (p : CompactPresentation) (hp : p.isFinite = true) :
    (∀ v : Fin p.generators → ℤ,
      (Submodule.Quotient.mk (normalizedDecode p.smith (normalizedEncode p.smith v)) :
        PresentationModule p.relationMatrix) = Submodule.Quotient.mk v) ∧
      (∀ r : Fin p.generators,
        p.smith.coeff r ∣ 0 * independentDecode p.smith [] r) := by
  refine ⟨?_, ?_⟩
  · intro v
    exact compactPresentation_reconstruct p v
  · intro r
    rw [Nat.zero_mul]
    exact Nat.dvd_zero _

/-- Packages label annihilation, agreement of the two decoders, and the exact binary
decomposition payload formula. -/
theorem clause17_endpoint {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (hf : ∀ r : Fin m, 0 < p.coeff r) :
    (∀ l ∈ L, ∀ r : Fin m, p.coeff r ∣ l r * independentDecode p L r) ∧
      independentDecode p L = compactDecode p L ∧
      algDecompositionPayloadTotal p =
        (p.binaryFactors.map List.length).sum +
          (p.binaryGeneratorWords.map (fun w => ∑ i : Fin m, (1 + w[i.val].2.length))).sum := by
  refine ⟨alg_decode_annihilates p L hf, alg_decoder_cross_checked p L, rfl⟩

/-- The modular exponentiation word has one instruction per set exponent bit, and `algExpBitCost
N e` equals `e * N`. -/
theorem alg_exp_bit_cost {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ)
    (he : e < 2 ^ N) :
    (modexpWord hN a e he).length = e.bitIndices.length ∧
      algExpBitCost N e = e * N := by
  exact ⟨modexpWord_length hN a e he, rfl⟩

/-- The local QFT gate cost is `n + n * (n - 1) / 2 + n / 2`, and its circuit uses no oracle
queries. -/
theorem alg_local_qft_cost (n : ℕ) :
    algLocalQFTGateCost n = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 := by
  refine ⟨rfl, (aqLocalQFT_actual_matrix_and_cost n).2.2⟩

/-- Combines the modular exponentiation word length with the local QFT gate cost and zero query
count. -/
theorem clause18_endpoint {N : ℕ} [NeZero N] (hN : 0 < N) (a : ZMod N) (e : ℕ) (he : e < 2 ^ N)
    (n : ℕ) :
    (modexpWord hN a e he).length = e.bitIndices.length ∧
      algLocalQFTGateCost n = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 := by
  exact ⟨(alg_exp_bit_cost hN a e he).1, (alg_local_qft_cost n).1, (alg_local_qft_cost n).2⟩

/-- For odd `N > 1`, a unit is a good random base exactly when its order is even and its half
order power is not `-1`. -/
theorem alg_random_base_characterization {N : ℕ} [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (hodd : Odd N) :
    randomBaseGood N a ↔ Even (orderOf a) ∧
      ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1 :=
  random_base_exact_order_factor_characterization N a hN hodd

/-- For odd `N > 1` with at least two distinct prime factors, random base success is at least `1
- 2^(-(k - 1))`, where `k` is their number. -/
theorem alg_random_base_success_bound {N : ℕ} [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ randomBaseSuccess N :=
  random_base_crt_success_bound N hN hodd hk

/-- The verified discrete logarithm routine satisfies the stated sample, work, and remainder
bounds, and every returned value solves `d.val • g = h`. -/
theorem alg_composite_dlog_verification {r : ℕ} [NeZero r] (C : Type)
    [AddCommGroup C] [DecidableEq C] (g h : C) (xs : List (ZMod r × ZMod r)) :
    (cyclicDlogVerified g h xs).2.1 ≤ xs.length ∧
      (cyclicDlogVerified g h xs).2.2.1 ≤ xs.length * (2 * r + 1) ∧
      (cyclicDlogVerified g h xs).2.2.2 < r ∧
      ∀ d, (cyclicDlogVerified g h xs).1 = some d → d.val • g = h :=
  composite_dlog_actual_verification_work r C g h xs

/-- Combines the random base characterization and success bound with the resource bounds and
correctness of verified cyclic discrete logarithm recovery. -/
theorem clause19_endpoint {N : ℕ} [NeZero N] {r : ℕ} [NeZero r] (C : Type)
    [AddCommGroup C] [DecidableEq C] (a : (ZMod N)ˣ) (g h : C)
    (xs : List (ZMod r × ZMod r)) (hN : 1 < N) (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    (randomBaseGood N a ↔ Even (orderOf a) ∧
      ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1) ∧
      1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ randomBaseSuccess N ∧
      (cyclicDlogVerified g h xs).2.1 ≤ xs.length ∧
        (cyclicDlogVerified g h xs).2.2.1 ≤ xs.length * (2 * r + 1) ∧
        (cyclicDlogVerified g h xs).2.2.2 < r ∧
        ∀ d, (cyclicDlogVerified g h xs).1 = some d → d.val • g = h := by
  refine ⟨alg_random_base_characterization a hN hodd,
    alg_random_base_success_bound hN hodd hk, ?_⟩
  exact alg_composite_dlog_verification C g h xs

end Qatlib.Concepts.FourierRecovery.ModularFourier.AlgebraicRecovery
