/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.MultistepODE.ClockSystem.Recurrence
public import Qatlib.Papers.HighOrderODE10.MainResults.SourceModel

@[expose] public section


/-! # Fixed-source Eqs.(27)-(28) as an actual finite complex system

arXiv:1010.2745v2, with the given real multistep coefficients. This bridge
uses the actual matrix and actual forcing vectors, not the scalar norm,
inverse-norm or call-count proxies of the historical SourceModel. No
invertibility, stability, error or algorithmic cost result is claimed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical
open Matrix

namespace Qatlib.Papers.HighOrderODE10.ClockSystem.Encoding

open Qatlib.Papers.HighOrderODE10.MainResults
open Qatlib.Concepts.MultistepODE.ClockSystem
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Eq.(27) with the fixed method's actual real coefficients embedded in complex matrices. -/
def sourceMatrix (m : SourceMultistepMethod) (N : ℕ) (h : ℝ) (A : Matrix I I ℂ) :
    Matrix (Fin (N+1) × I) (Fin (N+1) × I) ℂ :=
  clockMatrix m.k (fun ell => (m.alpha ell : ℂ)) (fun ell => (m.beta ell : ℂ)) (h : ℂ) A

omit [Fintype I] [DecidableEq I] in
/-- Eq.(28) with distinct startup h and main h times the sum of beta. -/
def sourceRhs (m : SourceMultistepMethod) (N : ℕ) (h : ℝ) (initial forcing : I → ℂ) :
    Fin (N+1) → I → ℂ :=
  rhs m.k (fun ell => (m.beta ell : ℂ)) (h : ℂ) initial forcing

/-- Solving the actual source matrix is exactly enforcing its four vector recurrences. -/
theorem equations27_28 (m : SourceMultistepMethod) {N : ℕ} (hkL : m.k ≤ N/2)
    (h : ℝ) (A : Matrix I I ℂ) (initial forcing : I → ℂ)
    (x : Fin (N+1) → I → ℂ) :
    sourceMatrix m N h A *ᵥ flatVec x = flatVec (sourceRhs m N h initial forcing) ↔
      Recurs m.k (fun ell => (m.alpha ell : ℂ)) (fun ell => (m.beta ell : ℂ))
        (h : ℂ) A initial forcing x :=
  systemIff m.hk hkL _ _ _ _ _ _ _

/-- Every tail block of an actual source solution equals its final-time spatial vector. -/
theorem finalCopies (m : SourceMultistepMethod) {N : ℕ} (hkL : m.k ≤ N/2)
    (h : ℝ) (A : Matrix I I ℂ) (initial forcing : I → ℂ)
    (x : Fin (N+1) → I → ℂ)
    (hsol : sourceMatrix m N h A *ᵥ flatVec x = flatVec (sourceRhs m N h initial forcing))
    (t : Fin (N+1)) (ht : N/2 ≤ t.val) : x t = x ⟨N/2, by omega⟩ :=
  solutionTail m.hk hkL _ _ _ _ _ _ _ hsol t ht

end Qatlib.Papers.HighOrderODE10.ClockSystem.Encoding
