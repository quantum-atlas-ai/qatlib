/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EigTransform26.Representation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# EigTransform26 — WeylCircuit block (§4, Appendix D): proven support lemma

The coherent Weyl-LCHM circuit theorems (Theorem 4.1, Theorem 4.5, Corollary 4.6,
Propositions 4.7-4.8, Theorem D.1) depend on the Weyl-calculus exact-discretization
machinery of the WeylCalculus block and the LCHM representation identities, which face
genuine Mathlib gaps (no residue theorem for Banach-valued integrals, no ready block
encoding composition API); their first-pass statements are preserved in branch history
(see the PR body for the difficulty log).  The self-contained polynomial lifting
identity used by Theorem 4.1 is proved unconditionally below.
-/

set_option autoImplicit false
noncomputable section

open Matrix Polynomial Filter
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Topology
open Qatlib.Papers.EigTransform26.Representation

namespace Qatlib.Papers.EigTransform26.WeylCircuit

variable {n J : Type*} [Fintype n] [DecidableEq n] [Fintype J] [DecidableEq J]

/-! ## c008 — Theorem 4.1: lifted approximation and exact angular realization -/

/-- The lift identity `F_{p_d} = P_d` of Theorem 4.1: with `p_d = (P_d + P_d(0))/2`
(eq. (4.2)), the lift `F_{p_d} = 2 p_d − p_d(0)` recovers `P_d`. -/
theorem lift_liftedPoly (P : Polynomial ℂ) :
    lift (fun z : ℂ => Polynomial.eval z (liftedPoly P))
      = fun z : ℂ => Polynomial.eval z P := by
  funext z
  simp only [lift, liftedPoly, Polynomial.smul_eq_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add]
  ring

end Qatlib.Papers.EigTransform26.WeylCircuit
