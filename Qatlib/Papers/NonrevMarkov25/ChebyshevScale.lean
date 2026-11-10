/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.ChebyshevScale

set_option autoImplicit false
open Qatlib.Concepts.PolynomialCalc.ChebyshevScale
namespace Qatlib.Papers.NonrevMarkov25.ChebyshevScale

theorem source_interval_max (ε : ℝ) (d : ℕ) (hε0 : 0<ε) (hε1 : ε≤1) (hd : 1≤d) :
    sSup (Set.range (fun x : {x : ℝ // |x|≤1} => |filterValue ε d x.1|))=1 :=
  filter_interval_max ε d hε0 hε1 hd
end Qatlib.Papers.NonrevMarkov25.ChebyshevScale
