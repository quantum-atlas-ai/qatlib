/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.Proposition412ProductSliceTransferStat
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeSliceTransfer

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA

/-- Establishes the product-slice AA transfer result of Proposition 4.12. -/
theorem proposition412ProductSliceTransfer : Proposition412ProductSliceTransfer := by
  intro p hp0 hp1 S hS
  constructor
  · exact cube_aa_transfer_from_moments (muFamily p) (nuFamily p)
      (nuWeight_cubeWeight hp0 hp1)
      (fun _n _d _f hb hd => cube_product_slice_moment_error hp0 hp1 hb hd)
      (fun _n hn f => cube_nu_exists_large_influence hp0 hp1 hn f) S hS
  · apply cube_aa_transfer_from_moments (nuFamily p) (muFamily p)
      (muWeight_cubeWeight hp0.le hp1.le)
      ?_ (fun _n hn f => cube_mu_exists_large_influence hp0 hp1 hn f) S hS
    intro n d f hb hd
    have h := cube_product_slice_moment_error hp0 hp1 hb hd
    exact ⟨by simpa only [abs_sub_comm] using! h.1,fun i => by simpa only [abs_sub_comm] using! h.2 i⟩

end Qatlib.Concepts.ProbabilityCore.DistributionAA
