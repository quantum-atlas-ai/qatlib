/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Lean
import Qatlib.Foundations.ScaledSqrt.SqrtBounds.RationalRootFloor
import Qatlib.Papers.GenerativeAdv25.MainResults.Source.GenerativeAdvantage
import Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor
import Qatlib.Papers.ExactSimon97.SampleStoppingQuantum
import Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse
import Qatlib.Concepts.ErrorCorrection.CssBuild.Constructions
import Qatlib.Papers.CssCodeCS96.Construction.HammingSteane
import Qatlib.Papers.PerfectQEC96.FiveQubit
import Qatlib.Papers.Armillary26.Instances.Routed
meta import Qatlib.Foundations.ScaledSqrt.SqrtBounds.RationalRootFloor

/-!
# Public module interface consumers

Ordinary leaf imports exercise theorem application and exposed definition bodies.
Six executable rounding cases use a meta-stage import of the arithmetic leaf.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.ScaledSqrt.SqrtBounds

-- Theorems remain callable without loading their proof bodies.
example (negative : Bool) (n : ℕ) : (signedCount negative n).natAbs = n :=
  signedCount_natAbs negative n

example (half : ℕ) (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    rootCount half p ≤ half :=
  rootCount_le_half half p hp hp1

example (h : Qatlib.Papers.GenerativeAdv25.MainResults.Conjecture1) :
    Qatlib.Papers.GenerativeAdv25.MainResults.Source.RepFindingFamily :=
  Qatlib.Papers.GenerativeAdv25.MainResults.Source.rep_finding_family_of_conjecture h

-- These rfl checks require the public definitions to expose their bodies.
example (n : ℕ) : signedCount false n = (n : ℤ) := rfl
example (n : ℕ) : signedCount true n = -(n : ℤ) := rfl
example (n : ℕ) :
    Qatlib.Papers.GenerativeAdv25.MainResults.zeroBits n = (fun _ => false) := rfl

#guard signedCount false 7 == 7
#guard signedCount true 7 == -7
#guard rootCount 10 (1 / 4) == 5
#guard rootCount 10 0 == 0
#guard rootCount 10 1 == 10
#guard rootCount 0 (1 / 4) == 0

-- New interfaces are consumed by an ordinary module as public definitions and
-- callable theorems, without importing their private proof data.
example (t : ℝ) (k : ℕ) :
    Qatlib.Papers.TruncTaylor14.PrepareSelectTaylor.taylorWeight t k =
      t ^ k / (k.factorial : ℝ) := rfl

example (V : ℝ → (ℝ →L[ℝ] ℝ)) (lam ψ : ℝ) :
    Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse.ekMap V (-lam)
      (Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse.ekMap V lam ψ) =
      (‖V (-lam) (V lam ψ)‖)⁻¹ • (V (-lam) (V lam ψ)) :=
  Qatlib.Papers.HamLCUSim12.FullSimulation.Lemma10Inverse.ek_composition_all V lam ψ

section FreshQuantumQueries

open Qatlib.Papers.ExactSimon97.SampleStoppingQuantum

variable {G R : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [AddCommGroup R] [Fintype R] [DecidableEq R]

example (e : G ≃ AddChar G ℂ) (N : ℕ) (ω : ℕ → AddChar G ℂ) :
    observedQueries (R := R) e N ω = observedStop N ω := observedQueries_eq e N ω

end FreshQuantumQueries

section ErrorCorrectionInterfaces

open Qatlib.Concepts.ErrorCorrection.CssBuild
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode
open Qatlib.Papers.CssCodeCS96.Construction
open Qatlib.Papers.PerfectQEC96
open Qatlib.Concepts.ErrorCorrection.ErrorClasses
open Qatlib.Papers.Armillary26.Instances
open scoped Matrix

example : (toCss ham3Code ham3_self).encodedQubits = 1 := ham3_css_params.2.1

example (n : ℕ) : codeDim (repCode n) = 1 := (rep_params n).2.1

example (m : ℕ) (hm : 2 ≤ m) : minDist (hamCode m) = (3 : ℕ∞) :=
  (hamParams m hm).2.2

example : stabDist fiveGens = (3 : ℕ∞) := five_params.2.1

example {p q : ℕ} [NeZero p] (a : ArmParam p q)
    (gX gZ : Fin 3 → Fin 12) (rho : Fin 3 → Fin 3 → Fin 12 → Fin 12)
    (h : ShiftPair a gX gZ rho) :
    6 * Fintype.card (ZMod p × Fin q) + 4 ≤
      (routeCode a gX gZ rho h).encodedQubits :=
  (route_shift_pair a gX gZ rho h).2.1

end ErrorCorrectionInterfaces

open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  unless env.header.isModule do
    throwError "public consumer must use the module system"
  IO.println "PUBLIC_MODULE_API_OK executable_cases=6 semantic_sampling=1"
  IO.println "ECC_PUBLIC_MODULE_API_OK css=1 classical_families=2 five_qubit=1 armillary=1"
