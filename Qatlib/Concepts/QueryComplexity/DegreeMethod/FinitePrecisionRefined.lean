/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionRefinedDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecision
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib

set_option autoImplicit false

theorem input_boundary_is_finite : FiniteInputBoundary := finiteInputBoundary

theorem premises_are_explicit : PremisesExplicit := premisesExplicit

theorem no_exact_real_oracle : NoExactRealOracle := noExactRealOracle

theorem reading_cost_is_charged : InputReadCostCharged := inputReadCostCharged

theorem fixed_add_value (x y : List Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitAdd x y) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x + Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue y :=
  bitAdd_value x y

theorem fixed_mul_value (x y : List Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitMul x y) = Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x * Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue y :=
  bitMul_value x y

theorem fixed_mul_length (x y : List Bool) :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue (bitMul x y) < 2 ^ (x.length + y.length) :=
  bitMul_value_lt x y

theorem fixed_value_bound (x : List Bool) : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue x < 2 ^ x.length :=
  binaryValue_lt_pow_length x

theorem fixed_point_truncation_bound (f : FixedPoint) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue f.bits : ℚ) < 2 ^ f.bits.length := by
  have h := binaryValue_lt_pow_length f.bits
  exact_mod_cast h

theorem rounding_scale_eq (f : FixedPoint) :
    roundingScale f = f.bits.length + f.scale := rfl

theorem clause7_endpoint :
    FiniteInputBoundary ∧ PremisesExplicit ∧ InputReadCostCharged := by
  refine ⟨input_boundary_is_finite, premises_are_explicit, reading_cost_is_charged⟩

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
