/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedianStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators

def SourceAlmostAffineGradient : Prop :=
  ∀ (d : ℕ) (c r ε L : ℝ) (δ : ℚ) (g : Fin d → ℝ),
    0 < r → 0 < ε → ε < L → 0 < δ → δ ≤ 1 → (∀ j, |g j| ≤ L) →
    let nε : ℤ := ⌈Real.logb 2 (4/(r*ε))⌉
    let nL : ℤ := ⌈Real.logb 2 (3*r*L)⌉
    let n : ℕ := (nε+nL).toNat
    let NL : ℝ := (2 : ℝ)^nL
    ∀ (f : GradientGrid d (2^n) → ℝ) (S : Finset (GradientGrid d (2^n))),
      ((Finset.univ \ S).card : ℝ) ≤ ((2 : ℝ)^n)^d/1000 →
      (∀ x ∈ S, |f x-(c+∑ j, g j*(r*sourceGradientGridPoint n (x j)))|
        ≤ ε*r/(8*42*Real.pi)) →
      let φ := fun x => (2 : ℝ)^nε*f x
      let hN : 0 < 2^n := Nat.pow_pos (by decide)
      let k := gradientMedianRepetitions d δ
      (nε+nL = (n : ℤ) ∧ 4 ≤ n) ∧
      (1-(δ : ℝ) ≤
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*k+1) → GradientGrid d (2^n) =>
          ∀ j, |(NL/r)*((gradientMedianCounted k ω j).1 : ℝ)-g j| ≤ ε),
          gradientFreshMass d (2^n) hN φ ω) ∧
      freshDataQueries (gradientFreshWord d (2^n) (2*k+1)) = 2*k+1 ∧
      freshInputQueries (gradientFreshWord d (2^n) (2*k+1)) = 0 ∧
      freshFixedGates (gradientFreshWord d (2^n) (2*k+1)) = 2*d*(2*k+1) ∧
      (∀ ω : Fin (2*k+1) → GradientGrid d (2^n),
        (∑ j, (gradientMedianCounted k ω j).2) ≤ d*10000*(2*k+1))

end Qatlib.Concepts.GradientOracle.GradientAlgo
