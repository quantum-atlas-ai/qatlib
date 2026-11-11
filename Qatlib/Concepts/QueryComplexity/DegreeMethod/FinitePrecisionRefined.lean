/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionRefinedDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecision

/-!
# Fixed-point arithmetic interfaces and bounds

This module reexports finite-input and reading-cost properties and specializes the native binary
arithmetic theorems to the fixed-point interface. The results concern the natural values of the
stored bit lists and the unscaled mantissa of `FixedPoint`.

The statements `clause7_endpoint`, `clause8_endpoint`, and `clause9_endpoint` collect the model
properties, arithmetic identities, and bit-length and scale formulas. They form a
finite-encoding interface for numerical computation in the setting of [KitaevShenVyalyi2002].

## Main statements

* `fixed_add_value` and `fixed_mul_value`: arithmetic correctness for stored bit lists.
* `fixed_point_truncation_bound`: the rational mantissa is below the power of two determined by
  its bit length.
* `rounding_scale_eq`: the rounding-scale formula.
* `clause7_endpoint`, `clause8_endpoint`, and `clause9_endpoint`: the collected interface
  properties.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib

set_option autoImplicit false

/-- The finite-precision input model satisfies the finite input boundary property
`FiniteInputBoundary`. -/
theorem input_boundary_is_finite : FiniteInputBoundary := finiteInputBoundary

/-- The finite-precision input model satisfies the explicit-premises property
`PremisesExplicit`. -/
theorem premises_are_explicit : PremisesExplicit := premisesExplicit

/-- The finite-precision input model satisfies `NoExactRealOracle`. -/
theorem no_exact_real_oracle : NoExactRealOracle := noExactRealOracle

/-- The finite-precision input model satisfies the reading-cost accounting property
`InputReadCostCharged`. -/
theorem reading_cost_is_charged : InputReadCostCharged := inputReadCostCharged

/-- Binary addition of the stored bit lists represents the sum of their natural values. -/
theorem fixed_add_value (x y : List Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitAdd x y) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue y :=
  bitAdd_value x y

/-- Binary multiplication of the stored bit lists represents the product of their natural
values. -/
theorem fixed_mul_value (x y : List Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitMul x y) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue y :=
  bitMul_value x y

/-- The numeric value of the binary product is strictly less than two raised to the sum of the
input bit lengths. -/
theorem fixed_mul_length (x y : List Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitMul x y) < 2 ^ (x.length + y.length) :=
  bitMul_value_lt x y

/-- The natural value represented by a bit list is strictly less than two raised to its length. -/
theorem fixed_value_bound (x : List Bool) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x < 2 ^ x.length :=
  binaryValue_lt_pow_length x

/-- The unscaled mantissa of a fixed-point value, viewed as a rational number, is strictly less
than two raised to its bit length. -/
theorem fixed_point_truncation_bound (f : FixedPoint) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue f.bits : ℚ) < 2 ^ f.bits.length := by
  have h := binaryValue_lt_pow_length f.bits
  exact_mod_cast h

/-- The rounding scale is the sum of the stored bit length and the fixed-point scale. -/
theorem rounding_scale_eq (f : FixedPoint) :
    roundingScale f = f.bits.length + f.scale := rfl

/-- Collects the finite input boundary, explicit-premises, and input-reading-cost properties of
the finite-precision model. -/
theorem clause7_endpoint :
    FiniteInputBoundary ∧ PremisesExplicit ∧ InputReadCostCharged := by
  refine ⟨input_boundary_is_finite, premises_are_explicit, reading_cost_is_charged⟩

/-- Collects correctness of binary addition and multiplication together with the numeric bounds
for a product and an arbitrary bit list. -/
theorem clause8_endpoint :
    (∀ (x y : List Bool), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitAdd x y) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue y) ∧
    (∀ (x y : List Bool), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitMul x y) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue y) ∧
    (∀ (x y : List Bool), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitMul x y) < 2 ^ (x.length + y.length)) ∧
    (∀ (x : List Bool), Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x < 2 ^ x.length) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    exact fixed_add_value x y
  · intro x y
    exact fixed_mul_value x y
  · intro x y
    exact fixed_mul_length x y
  · intro x
    exact fixed_value_bound x

/-- Collects the rational mantissa bound, the rounding-scale formula, and the definition of the
fixed-point bit-time count. -/
theorem clause9_endpoint :
    (∀ (f : FixedPoint), (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue f.bits : ℚ) < 2 ^ f.bits.length) ∧
    (∀ (f : FixedPoint), roundingScale f = f.bits.length + f.scale) ∧
    (∀ (x y : FixedPoint), fixedPointBitTime x y = x.bits.length + y.bits.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact fixed_point_truncation_bound f
  · intro f
    exact rounding_scale_eq f
  · intro x y
    rfl

end Qatlib.Concepts.QueryComplexity.DegreeMethod
