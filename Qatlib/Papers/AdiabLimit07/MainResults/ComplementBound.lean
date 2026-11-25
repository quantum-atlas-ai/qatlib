/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabLimit07.MainResults.EigenspaceConsequence

@[expose] public section

/-!
# Complement dimension for uniform-start adiabatic search

Apply Eq. (21) to normalized uniform-start evolution and solve for the complementary
eigenspace dimension. Positive runtime makes the new denominator nonzero.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.AdiabLimit07.MainResults

namespace Qatlib.Papers.AdiabLimit07.MainResults

/-- Equation (21) bounds the complementary eigenspace dimension from below for a
positive-runtime, normalized Schrödinger evolution from the uniform state. -/
theorem uniform_complement_dim_ge {n q p : ℕ}
    (F : Fin (q + 1) → ℝ) (qIdx : Reg n → Fin (q + 1))
    (E : Fin (p + 1) → ℝ) (pIdx : Reg n → Fin (p + 1)) (K : Fin (q + 1))
    (hmono : ∀ a b : Fin (q + 1), a ≤ b → F a ≤ F b)
    (hF0 : 0 ≤ F 0) (maxF : ℝ) (hmax : ∀ k, F k ≤ maxF)
    (s : ℝ → ℝ) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (ψ : ℝ → QState (Reg n)) (T c : ℝ) (hT : 0 < T)
    (hSchrod : SchrodingerIVP
      (fun t => genHamiltonian (s t) (hadamardHamiltonian F qIdx)
        (computationalHamiltonian E pIdx)) ψ T)
    (hψnorm : ∀ t ∈ Set.Icc 0 T, Normalized (ψ t))
    (hcard : 0 < ((solutionSet pIdx).card : ℝ)) (hmaxF : 0 < maxF)
    (hcomp : 0 < eigenspaceComplementDim qIdx K)
    (hinit : InitialUniform ψ) (hpT : c ≤ solutionProb pIdx (ψ T)) :
    (c * Real.sqrt (((2 : ℕ) ^ n : ℝ)) - ((solutionSet pIdx).card : ℝ) /
        Real.sqrt (((2 : ℕ) ^ n : ℝ))) /
      (2 * ((solutionSet pIdx).card : ℝ) * maxF * T) ≤ eigenspaceComplementDim qIdx K := by
  exact complement_dim_ge (by positivity) hT.le hcard hmaxF hcomp
    (runtime_lower_bound_eq21_initialUniform F qIdx E pIdx K hmono hF0 maxF hmax
      s hs0 hs1 ψ T c hT.le hSchrod hψnorm hcard hmaxF hcomp hinit hpT)

end Qatlib.Papers.AdiabLimit07.MainResults
