/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly05.MainResults.PlatAlgorithm

/-!
# Conditional Jones trace and plat approximation

`theorem11_trace_closure_approximation` and `theorem12_plat_closure_approximation` combine the
assumed local compilation of generator matrices with concentration for bounded observations. The
conclusions provide a matrix word, a length bound, and a positive sample count satisfying the
stated approximation guarantee. See [AharonovJonesLandau2009].

## Main statements

* `theorem11_trace_closure_approximation`: Assuming local compilation and bounded observations
  with the specified Markov-trace means, there exist an exact braid-operator implementation with
  the stated polynomial-form length bound and a positive sample count giving failure probability
  at most δ at error threshold ε‖d^(n − 1)‖.
* `theorem12_plat_closure_approximation`: Assuming local compilation, a nonzero scale κ, and
  bounded observations with the specified plat expectation, there exist an exact braid-operator
  implementation with the stated polynomial-form length bound and a positive sample count giving
  error probability at most δ at threshold acc.

## References

* [Aharonov et al., 2009][AharonovJonesLandau2009]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Matrix

namespace Qatlib.Papers.JonesPoly05.MainResults.MainTheorems

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.JonesPoly05.MainResults.Kauffman
open Qatlib.Papers.JonesPoly05.MainResults.CircuitCompilation
open Qatlib.Papers.JonesPoly05.MainResults.Estimator
open Qatlib.Papers.JonesPoly05.MainResults.TraceAlgorithm
open Qatlib.Papers.JonesPoly05.MainResults.PlatAlgorithm

/-- Assuming local compilation and bounded observations with the specified Markov-trace means,
there exist an exact braid-operator implementation with the stated polynomial-form length
bound and a positive sample count giving failure probability at most δ at error threshold
ε‖d^(n − 1)‖; see [AharonovJonesLandau2009]. -/
theorem theorem11_trace_closure_approximation
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} (c k : ℕ) (B : BraidWord n) (h32 : LocalCompiles φ c n k)
    {A d : ℂ} (hd : d ≠ 0) (hA : ‖A‖ = 1)
    (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (re im : X → ℝ)
    (hre : ∀ x, re x ∈ Set.Icc (-1) 1) (him : ∀ x, im x ∈ Set.Icc (-1) 1)
    (hre_mean : p.expect re = (markovTrace A d B).re)
    (him_mean : p.expect im = (markovTrace A d B).im)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ (Q : GateWord (2 ^ n)) (L : ℕ), 0 < L ∧
      wordMatrix Q = braidOperator φ B ∧
      (∃ C : ℕ, Q.length ≤ C * (B.length + n + k + 1) ^ C) ∧
      p.probEvent (fun ω : Fin L → X =>
        ε * ‖d ^ ((n : ℤ) - 1)‖ ≤
          ‖traceClosureOutput A d B re im ω - jonesTrace A d B‖) ≤ δ := by
  obtain ⟨C, Q, hQ, hlen⟩ := corollary31_polynomial_circuit φ c k B h32
  obtain ⟨L, hL, hprob⟩ :=
    theorem31_trace_closure_algorithm hd hA B X p re im hre him hre_mean him_mean hε hδ
  exact ⟨Q, L, hL, hQ, ⟨C, hlen⟩, hprob⟩

/-- Assuming local compilation, a nonzero scale κ, and bounded observations with the specified
plat expectation, there exist an exact braid-operator implementation with the stated
polynomial-form length bound and a positive sample count giving error probability at most δ
at threshold acc; see [AharonovJonesLandau2009]. -/
theorem theorem12_plat_closure_approximation
    (φ : ∀ n : ℕ, Fin (n - 1) → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    {n : ℕ} (c k : ℕ) (B : BraidWord n) (h32 : LocalCompiles φ c n k)
    (κ platExpectation vPl : ℂ) (hV : vPl = κ * platExpectation) (hκ : 0 < ‖κ‖)
    (X : Type) [Fintype X] [DecidableEq X] (p : FinDist X) (re im : X → ℝ)
    (hre : ∀ x, re x ∈ Set.Icc (-1) 1) (him : ∀ x, im x ∈ Set.Icc (-1) 1)
    (hre_mean : p.expect re = platExpectation.re)
    (him_mean : p.expect im = platExpectation.im)
    {acc δ : ℝ} (hacc : 0 < acc) (hδ : 0 < δ) :
    ∃ (Q : GateWord (2 ^ n)) (L : ℕ), 0 < L ∧
      wordMatrix Q = braidOperator φ B ∧
      (∃ C : ℕ, Q.length ≤ C * (B.length + n + k + 1) ^ C) ∧
      p.probEvent (fun ω : Fin L → X =>
        acc ≤ ‖platOutput κ re im ω - vPl‖) ≤ δ := by
  obtain ⟨C, Q, hQ, hlen⟩ := corollary31_polynomial_circuit φ c k B h32
  obtain ⟨L, hL, hprob⟩ :=
    theorem32_plat_closure_algorithm κ platExpectation vPl hV hκ X p re im hre him
      hre_mean him_mean hacc hδ
  exact ⟨Q, L, hL, hQ, ⟨C, hlen⟩, hprob⟩

end Qatlib.Papers.JonesPoly05.MainResults.MainTheorems
