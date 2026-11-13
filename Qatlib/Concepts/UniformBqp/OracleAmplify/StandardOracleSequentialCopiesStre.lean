/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleCopyProgram

/-!
# Sequential copies for a standard bit oracle

`standardOracleSequentialCopies` proves the sequential-copy specification by using
`StandardCopiesCircuit`. The construction preserves the shared clean oracle register and
realizes independent execution on each tensor factor with explicit costs. The background is
described in [BennettEtAl1997].

## Main statements

* `standardOracleSequentialCopies`: the sequential-copy existence theorem.

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Qatlib

/-- Every unitary standard bit-oracle circuit satisfies the sequential-copy specification, with
independent tensor-factor execution and the stated routing costs [BennettEtAl1997]. -/
theorem standardOracleSequentialCopies : StandardOracleSequentialCopies := by
  intro n k hn W _ _ _ C hC
  obtain ⟨hu, hq, hg, hr⟩ := standardCopiesCircuit_spec k C hC
  exact ⟨StandardCopiesCircuit k C, hu, hq, hg, fun x ψ => hr x (Ket (⟨0, hn⟩, false)) ψ⟩

end Qatlib.Concepts.UniformBqp.OracleAmplify
