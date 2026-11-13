/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.Phi3Compile.StandardModelDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

/-!
# NegWeights06, Theorem 7 — adversary bound squared is a formula-size lower bound

Source: Høyer–Lee–Špalek, "Negative weights make adversaries stronger",
arXiv:quant-ph/0611054v2 (fixed PDF, SHA256
`8c705081dc3243baa1c83a64ed92870c7cd42fa91dd872c469621158af2c37bb`),
Theorem 7, §4, printed page 10:

`L(f) ≥ C^D(Rf) ≥ (ADV±(f))²`.

Here `L(f)` is the number of leaves of a smallest Boolean formula (AND/OR/NOT,
fan-out one) computing `f`, `Rf = {(x,y,i) : f(x) = 0, f(y) = 1, xᵢ ≠ yᵢ}` is the
Karchmer–Wigderson relation, and `C^D(Rf)` is the number of rectangles in a
smallest decomposition of `{x : f(x) = 0} × {y : f(y) = 1}` into disjoint
rectangles monochromatic with respect to `Rf`.

The paper-layer definitions below are the paper's own objects: `formulaSize`
minimizes the leaf count of the frozen `BoolFormula.size` over formulas
computing `f`, and `rectangleDecompositionSize` minimizes the cardinality over
`IsRectanglePartition`s of the Karchmer–Wigderson relation.

The inequality is recorded as the closed `Prop` contract
`theorem7FormulaSizeSpec`; it is **not** proved in this repository.  Fixed
version: quant-ph/0611054v2.  Source: Theorem 7 on p. 10 (proof on pp. 10–11).
-/

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.NegWeights06.MainResults.FormulaLowerBound

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.UniformBqp.Phi3Compile

noncomputable section

/-- `F` is a Boolean formula computing `f` on all inputs (printed "a formula for
`f`", §4). -/
def IsFormulaFor {n : ℕ} (f : Reg n → Bool) (F : BoolFormula (Fin n)) : Prop :=
  ∀ x : Reg n, F.eval x = f x

/-- **Formula size `L(f)` (printed §4):** the minimal leaf count
`BoolFormula.size` over all Boolean formulas computing `f`. -/
def formulaSize {n : ℕ} (f : Reg n → Bool) : ℕ :=
  sInf {s : ℕ | ∃ F : BoolFormula (Fin n), IsFormulaFor f F ∧ F.size = s}

/-- A rectangle `A × B` of the input square is monochromatic with respect to the
Karchmer–Wigderson relation `Rf`: `A` is a set of zero-inputs, `B` a set of
one-inputs, and the same coordinate `i` witnesses `xᵢ ≠ yᵢ` for every pair
(printed §4, "monochromatic with respect to `R`"). -/
def IsMonochromaticRectangle {n : ℕ} (f : Reg n → Bool)
    (A B : Set (Reg n)) : Prop :=
  A ⊆ {x : Reg n | f x = false} ∧ B ⊆ {y : Reg n | f y = true} ∧
    ∃ i : Fin n, ∀ x ∈ A, ∀ y ∈ B, x i ≠ y i

/-- A rectangle partition of `{x : f(x) = 0} × {y : f(y) = 1}` into disjoint
monochromatic rectangles (printed §4, a decomposition of `Rf`). -/
def IsRectanglePartition {n : ℕ} (f : Reg n → Bool)
    (R : Finset (Set (Reg n) × Set (Reg n))) : Prop :=
  (∀ r ∈ R, IsMonochromaticRectangle f r.1 r.2) ∧
  (∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → Disjoint (r.1 ×ˢ r.2) (r'.1 ×ˢ r'.2)) ∧
  (∀ x y : Reg n, f x = false → f y = true → ∃ r ∈ R, x ∈ r.1 ∧ y ∈ r.2)

/-- **Rectangle decomposition size `C^D(Rf)` (printed §4):** the minimal number
of disjoint monochromatic rectangles covering `{x : f(x) = 0} × {y : f(y) = 1}`. -/
def rectangleDecompositionSize {n : ℕ} (f : Reg n → Bool) : ℕ :=
  sInf {s : ℕ | ∃ R : Finset (Set (Reg n) × Set (Reg n)),
    IsRectanglePartition f R ∧ R.card = s}

/-- **Theorem 7 (adversary bound squared versus formula size), recorded
statement.**  For a Boolean function `f` on `n` bits,
`(ADV±(f))² ≤ C^D(Rf) ≤ L(f)`, where `ADV±` is the frozen `advPmValue` of the
identity input map, `C^D(Rf)` is `rectangleDecompositionSize f`, and `L(f)` is
`formulaSize f`.

This is quant-ph/0611054v2 Theorem 7 (p. 10), recorded as a closed `Prop`; it is
not proved here.  See the module docstring for the fixed version, the proof
route (Lemma 8 rectangle subadditivity of the spectral norm, then the final
display of the printed proof). -/
def theorem7FormulaSizeSpec : Prop :=
  ∀ {n : ℕ} (f : Reg n → Bool),
    (advPmValue (fun x : Reg n => x) f) ^ 2 ≤
        (rectangleDecompositionSize f : ℝ≥0∞) ∧
      rectangleDecompositionSize f ≤ formulaSize f

end

end Qatlib.Papers.NegWeights06.MainResults.FormulaLowerBound
