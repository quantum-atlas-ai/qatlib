/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLattice03.MainResults.Theorem11

/-!
# Polynomial uniqueness from a DCP solver

The theorem `dhsp_cosetSampling_implies_polyUniqueSVP` specializes the DCP-to-lattice reduction
to failure parameter one. Given a DCP solver and the coefficient-recovery hypothesis, it
produces a solver satisfying `PolyUniqueSVP`. See [Regev2004] for the paper context.

## Main statements

* `dhsp_cosetSampling_implies_polyUniqueSVP`: Assuming coefficient recovery at failure parameter
  one and a DCP solver at that parameter, there exists a lattice solver satisfying
  `PolyUniqueSVP`.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QLattice03.MainResults

/-- Assuming coefficient recovery at failure parameter one and a DCP solver at that parameter,
there exists a lattice solver satisfying `PolyUniqueSVP`. See [Regev2004]. -/
theorem dhsp_cosetSampling_implies_polyUniqueSVP (h312 : twoPoint_recovers_coefficient 1)
    (h : HasDCPSolver 1) :
    ∃ B : ∀ n : ℕ, LatticeBasis n → (Fin n → ℤ), PolyUniqueSVP B := by
  obtain ⟨B, hB⟩ := dcp_implies_uniqueSVP 1 (by norm_num) h312 h
  refine ⟨B, svpExponent 1, ?_, hB⟩
  unfold svpExponent
  norm_num

end Qatlib.Papers.QLattice03.MainResults
