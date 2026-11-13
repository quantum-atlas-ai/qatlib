/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineCoordinateReadoutStat

/-!
# Specification of gradient median amplification

`AlmostAffineVectorMedian` specifies independent repeated readout, simultaneous coordinate
medians, and their circuit and comparison costs. It records both the geometric failure bound and
a repetition count for a requested confidence, following the amplification framework of
[GilyenArunachalamWiebe2019].

## Main statements

* `AlmostAffineVectorMedian`: normalized fresh output, product masses, coordinatewise median
  accuracy, and explicit implementation counts.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.HhlAlgorithms.Postselection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators

/-- The proposition collecting product-state sampling, coordinatewise median accuracy with
failure at most `d*(143/144)^r`, and circuit and comparison costs under the almost-affine
hypotheses. It also states that `gradientMedianRepetitions` achieves any allowed confidence
parameter `δ`. -/
def AlmostAffineVectorMedian : Prop :=
  ∀ (d n : ℕ) (hN : 0 < 2^n) (φ : GradientGrid d (2^n) → ℝ)
    (g : Fin d → ℝ) (c : ℝ) (S : Finset (GradientGrid d (2^n))),
    (∀ j, |g j| ≤ 1/3) →
    ((Finset.univ \ S).card : ℝ) ≤ ((2 : ℝ)^n)^d/1000 →
    (∀ x ∈ S, |φ x-(c+∑ j, g j*(x j).val)| ≤ 1/(42*Real.pi)) →
    (∀ r : ℕ,
      let R : ℕ := 2*r+1
      @Normalized (FreshRegister (GradientGrid d (2^n)) R) (instFintypeFreshRegister R)
        (gradientFreshOutput d (2^n) hN φ R) ∧
      (∀ ω : Fin R → GradientGrid d (2^n),
        gradientFreshMass d (2^n) hN φ ω = ∏ t, BornProb (gradientReadout d (2^n) hN φ) (ω t)) ∧
      (∑ ω : Fin R → GradientGrid d (2^n), gradientFreshMass d (2^n) hN φ ω) = 1 ∧
      (1-(d : ℝ)*(143/144 : ℝ)^r ≤
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin R → GradientGrid d (2^n) =>
          ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2 : ℝ)^n),
          gradientFreshMass d (2^n) hN φ ω) ∧
      freshDataQueries (gradientFreshWord d (2^n) R) = R ∧
      freshInputQueries (gradientFreshWord d (2^n) R) = 0 ∧
      freshFixedGates (gradientFreshWord d (2^n) R) = 2*d*R ∧
      (∀ ω : Fin R → GradientGrid d (2^n),
        (∀ j, ((gradientMedianCounted r ω j).1 : ℝ) =
          sortedBlockMedian r (fun t => signedGridValue (2^n) (ω t j))) ∧
        (∑ j, (gradientMedianCounted r ω j).2) ≤ d*10000*R)) ∧
    (∀ δ : ℚ, 0 < δ → δ ≤ 1 →
      let r := gradientMedianRepetitions d δ
      (d : ℝ)*(143/144 : ℝ)^r ≤ (δ : ℝ) ∧
      (1-(δ : ℝ) ≤
        ∑ ω ∈ Finset.univ.filter (fun ω : Fin (2*r+1) → GradientGrid d (2^n) =>
          ∀ j, |((gradientMedianCounted r ω j).1 : ℝ)-g j| ≤ 4/(2 : ℝ)^n),
          gradientFreshMass d (2^n) hN φ ω))

end Qatlib.Concepts.GradientOracle.ReadoutTools
