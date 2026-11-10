/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.SdpDualityDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.DyadicFloor.FloorRounding

def floorDyadic (p : ℕ) (x : ℚ) : ℚ := (⌊x * (2 : ℚ)^p⌋ : ℚ)/(2 : ℚ)^p
def roundMatrix {n : ℕ} (p : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => (floorDyadic p (A i j) + floorDyadic p (A j i))/2
def interpret {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)
end Qatlib.Concepts.DyadicFloor.FloorRounding
