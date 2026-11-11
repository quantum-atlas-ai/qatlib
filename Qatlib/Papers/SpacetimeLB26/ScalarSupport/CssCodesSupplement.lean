/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpacetimeLB26.ScalarSupport.Defs
import Qatlib.Concepts.CodingDecoding.CssRecovery.CodingDecoding
import Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes

/-! # Scalar support retained from the original SpacetimeLB26 contribution

This file proves conditional arithmetic or abstract combinatorial implications. Its
hypotheses must be read literally: final overlap, survival, contraction, code existence,
distance or threshold fields are not constructions of the corresponding physical objects.
The paper metadata records these interfaces as partial support, separately from the
new native Bell and adaptive erasure producers. Fixed source: arXiv2608.26272v1.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes

open Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes

open scoped BigOperators
open Finset
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib.Concepts.CodingDecoding.CssTesters.CssCode

/-! ## A finite CSS recovery interface

The scalar claims below do not construct a code or a decoder.  This small typed
interface records the finite data that a concrete CSS recovery must provide,
and the Steane instance below supplies those data from the frozen coding layer.
The correction field is an exact statement about binary Pauli labels and
syndromes; it makes no claim about a physical channel, fault model, or circuit
implementation beyond the supplied finite interface.
-/

/-- A finite binary CSS code together with an exact radius-one syndrome decoder.

`correctsWeightOne` is deliberately a label-level contract: it says that the
decoder returns the original Pauli label on every error of Hamming weight at
most one.  Any physical realization, noise model, and logical-state statement
remain separate assumptions.
-/
structure FiniteCssRecovery (n sx sz : ℕ) where
  /-- The finite CSS check tables and their compatibility equation. -/
  code : CssData (Fin n) (Fin sx) (Fin sz)
  /-- The finite map from a measured syndrome to a Pauli correction. -/
  decoder : RecoveryProgram code
  /-- Exact correction of every binary Pauli label of weight at most one. -/
  correctsWeightOne : ∀ e : PauliLabel (Fin n),
    pauliWeight e.1 e.2 ≤ 1 →
      decoder.corr (pauliSyndrome code e) = e

/-- The concrete `[[7,1,3]]` Steane CSS code and its finite syndrome decoder.

This is an inhabited witness for `FiniteCssRecovery 7 3 3`.  Its exact
correction theorem comes from the finite Hamming-check construction; no scalar
assumption in the surrounding SpacetimeLB26 support is used to manufacture it.
-/
def steaneFiniteCssRecovery : FiniteCssRecovery 7 3 3 where
  code := steaneData
  decoder := steaneDecoder
  correctsWeightOne := by
    intro e h
    exact Qatlib.Concepts.CodingDecoding.CssRecovery.steaneDecoder_corrects_weight_one e h

/-- The finite CSS recovery interface is genuinely inhabited by Steane data. -/
theorem steaneFiniteCssRecovery_inhabited :
    Nonempty (FiniteCssRecovery 7 3 3) :=
  ⟨steaneFiniteCssRecovery⟩

/-- The concrete finite CSS code encodes exactly one logical qubit. -/
theorem steaneFiniteCssRecovery_encodedQubits :
    steaneFiniteCssRecovery.code.encodedQubits = 1 := by
  exact steaneData_encodedQubits

/-- The concrete finite decoder exactly recovers every weight-one Pauli label.

This theorem exposes the typed syndrome/recovery compatibility supplied by the
finite interface; it does not promote that compatibility to a physical error
correction claim without a separate channel and implementation model.
-/
theorem steaneFiniteCssRecovery_correctsWeightOne
    (e : PauliLabel (Fin 7)) (h : pauliWeight e.1 e.2 ≤ 1) :
    steaneFiniteCssRecovery.decoder.corr
        (pauliSyndrome steaneFiniteCssRecovery.code e) = e := by
  exact steaneFiniteCssRecovery.correctsWeightOne e h

/-! ## Lemma 17 — binomial Chernoff bound -/

/-! ## Theorem 15 — binary CSS Gilbert–Varshamov bound -/

/-! ## Theorem 18 — CSS-code construction for erasure noise -/

/-! ## Corollary 19 — optimal worst-case circuit size -/

end Qatlib.Papers.SpacetimeLB26.ScalarSupport.CssCodes
