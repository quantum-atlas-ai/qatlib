/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsTransportDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.ResourceBounds.AsymBounds

open Qatlib

set_option autoImplicit false

structure GrowthFilter where

  inputSize : ℕ

  inverseEpsilon : ℕ

def uniformUpperBound (R : ℕ → ℕ) (C : ℕ) (d : ℕ) : Prop :=
  ∀ n : ℕ, R n ≤ C * (n + 1) ^ d

def uniformLowerBound (R : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, f n ≤ R n

end Qatlib.Concepts.ResourceBounds.AsymBounds
