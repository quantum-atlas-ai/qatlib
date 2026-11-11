/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodesSupplement
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Subsystem

/-! # Scalar support retained from the original SpacetimeLB26 contribution

This file proves conditional arithmetic or abstract combinatorial implications. Its
hypotheses must be read literally: final overlap, survival, contraction, code existence,
distance or threshold fields are not constructions of the corresponding physical objects.
The paper metadata records these interfaces as partial support, separately from the
new native Bell and adaptive erasure producers. Fixed source: arXiv2608.26272v1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.Subsystem

open Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes
open Qatlib.Papers.SpacetimeLB26.ScalarSupport.Subsystem
open Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes

open scoped BigOperators
open Finset

/-! ## Theorem 25 — subsystem Singleton circuit-size bound -/

/-! ## Finite CSS witness bridge -/

/-- A finite CSS recovery witness can be carried through the scalar Singleton
bound without pretending that the supplied Singleton inequality is derived from
the witness. The code's encoded-qubit field is retained in the conclusion;
the physical codespace and general subsystem Singleton theorem remain inputs. -/
theorem finite_css_singleton_scalar_bound
    (R : FiniteCssRecovery 7 3 3) (hR : R.code.encodedQubits = 1)
    (hAss24 : (7 : ℝ) ≤ (1 : ℝ) * 7)
    (hSingleton : (7 : ℝ) ≥ (1 : ℝ) + (0 : ℝ) + 2 * ((3 : ℝ) - 1)) :
    R.code.encodedQubits = 1 ∧
      (7 : ℝ) ≥ (1 : ℝ) + (0 : ℝ) + 2 * ((3 : ℝ) - 1) ∧
      (7 : ℝ) ≥ ((1 : ℝ) + (0 : ℝ) + 2 * ((3 : ℝ) - 1)) / 1 := by
  have h := subsystem_singleton_circuit_bound 7 1 0 3 1 7
    (by norm_num) (by norm_num) (by norm_num)
    (by exact_mod_cast hAss24) (by exact_mod_cast hSingleton)
  have h1 : (7 : ℝ) ≥ (1 : ℝ) + (0 : ℝ) + 2 * ((3 : ℝ) - 1) := by
    exact_mod_cast h.1
  have h2 : (7 : ℝ) ≥ ((1 : ℝ) + (0 : ℝ) + 2 * ((3 : ℝ) - 1)) / 1 := by
    exact_mod_cast h.2
  exact ⟨hR, h1, h2⟩

/-! ## Corollary 26 — cost of correcting every small Pauli fault -/

/-! ## Theorem 27 — Pauli-pairing bound -/

/-! ## Corollary 30 — accuracy forces distance -/

/-! ## Corollary 31 — vanishing error forces growing protection -/

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.Subsystem
