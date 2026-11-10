/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.ExtremalFilter

set_option autoImplicit false
open Qatlib.Concepts.PolynomialCalc.ChebyshevScale
open Qatlib.Concepts.PolynomialCalc.ExtremalFilter
namespace Qatlib.Papers.NonrevMarkov25.ChebyshevMin

theorem source_candidate (ε : ℝ) (k : ℕ) (hε0 : 0<ε) (hε1 : ε<1) (hk : 1≤k) :
    AdmissibleFilter ε k (filterPolynomial ε k) ∧ (filterPolynomial ε k).natDegree=k :=
  candidate_membership ε k hε0 hε1 hk

theorem source_band_edge (ε : ℝ) (k : ℕ) (hε0 : 0<ε) (hk : 1≤k) :
    sSup {x : ℝ | |x|≤1 ∧ filterValue ε k x=ε}=1-bandWidth ε k :=
  candidate_band_edge ε k hε0 hk
end Qatlib.Papers.NonrevMarkov25.ChebyshevMin
