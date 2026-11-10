/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.PrnJump.CompiledJump
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open scoped Classical ENNReal
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Receipts
open Qatlib.Papers.MonteCarloInt20.PrnJump.Compiled

def oddMultiplier (n a : ℕ) (ha : Odd a) : (ZMod (2^n))ˣ :=
  ZMod.unitOfCoprime a ((Nat.coprime_two_right.mpr ha).pow_right n)

theorem oddMultiplier_value (n a : ℕ) (ha : Odd a) :
    (oddMultiplier n a ha : ZMod (2^n)) = (a : ZMod (2^n)) := ZMod.coe_unitOfCoprime _ _

noncomputable def paidNative {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (ψ : QState (Reg (width n k))) (hψ : Normalized ψ) : CostedLaw (Reg (width n k)) :=
  (bornDistribution (Run 1 (reflectionCompile (nativeWord a c qs)) ψ)
    ((native_unitary a c qs).normalized_run
      (show (1 : Matrix (Reg (width n k)) (Reg (width n k)) ℂ) ∈ Matrix.unitaryGroup _ ℂ by simp) hψ)).map
    (fun out => (out,(nativeWord a c qs).length))

theorem paidNative_exact {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (ψ : QState (Reg (width n k))) (hψ : Normalized ψ) :
    CostedLaw.expectedCost (paidNative a c qs ψ hψ) = ((nativeWord a c qs).length : ℝ≥0∞) := by
  simp only [CostedLaw.expectedCost,paidNative,CostedLaw.expectation_map,CostedLaw.expectation_const]

theorem paidNative_budget {n k : ℕ} (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (ψ : QState (Reg (width n k))) (hψ : Normalized ψ) :
    CostedLaw.expectedCost (paidNative a c qs ψ hψ) ≤ (qs.length*rungBound n k : ℕ) := by
  rw [paidNative_exact]
  exact_mod_cast (native_resources a c qs).2.1

theorem native_coherent {n k : ℕ} {S : Type*} [Fintype S]
    (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) (qs : List (Fin k))
    (z : S → ℂ) (bits : S → Reg k) (x : S → ZMod (2^n)) :
    Run 1 (reflectionCompile (nativeWord a c qs)) (∑ s, z s • Ket (frame (bits s) (x s))) =
      ∑ s, z s • Ket (frame (bits s)
        (Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg.lcg (a:ZMod (2^n)) c (x s)
          (Qatlib.Papers.MonteCarloInt20.PrnJump.Affine.exponent qs (bits s)))) := by
  rw [run_reflectionCompile_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [run_reflectionCompile_smul,native_basis]
end Qatlib.Papers.MonteCarloInt20.PrnJump.Receipts
