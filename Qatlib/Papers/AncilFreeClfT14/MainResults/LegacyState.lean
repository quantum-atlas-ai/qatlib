/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AncilFreeClfT14.MainResults.CoreModel

@[expose] public section


/-! # Preserved closed legacy mathematics
This module uses the archived coefficient model at the fixed public pin.
It does not identify free operation counts with Clifford+T circuit costs.
-/
set_option autoImplicit false
noncomputable section
open scoped Real
open Complex
namespace Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
open Qatlib.Papers.AncilFreeClfT14.MainResults

namespace Mat2

/-- Transpose of a real `2 × 2` matrix. -/
def transpose (A : Mat2) : Mat2 := ⟨A.m11, A.m21, A.m12, A.m22⟩

/-- Inverse of a real `2 × 2` matrix (meaningful when `det A = ±1`). -/
def inv (A : Mat2) : Mat2 :=
  ⟨A.m22 / A.det, -A.m12 / A.det, -A.m21 / A.det, A.m11 / A.det⟩

/-- Entrywise negation. -/
def neg (A : Mat2) : Mat2 := ⟨-A.m11, -A.m12, -A.m21, -A.m22⟩

/-- Powers of a matrix. -/
def pow (A : Mat2) : ℕ → Mat2
  | 0 => Mat2.one
  | n + 1 => A.mul (pow A n)

end Mat2

namespace State

/-- The pair of matrices obtained by the action `(D,∆) · G = (G†DG, G•†∆G•)`
of a special grid operator (Definition A.3). -/
def apply (S : State) (G Gb : Mat2) : Mat2 × Mat2 :=
  ((Mat2.transpose G).mul (S.matD.mul G),
   (Mat2.transpose Gb).mul (S.matDelta.mul Gb))

/-- The skew of the state obtained after applying `G` (with 2-conjugate `G•`):
`b'² + β'²`, where `b'` and `β'` are the off-diagonal entries of `G†DG` and
`G•†∆G•`. -/
def skewAfter (S : State) (G Gb : Mat2) : ℝ :=
  (State.apply S G Gb).1.m12 ^ 2 + (State.apply S G Gb).2.m12 ^ 2

end State

/-! ## The 2-conjugates of the Figure 6 operators -/

/-- `R•`, the entrywise 2-conjugate of `R`. -/
def opRbullet : Mat2 :=
  ⟨-(1 / Real.sqrt 2), 1 / Real.sqrt 2, -(1 / Real.sqrt 2), -(1 / Real.sqrt 2)⟩

/-- `A• = A`, since `A` has integer entries. -/
def opAbullet : Mat2 := opA

/-- `B• = [[1,-√2],[0,1]]`. -/
def opBbullet : Mat2 := ⟨1, -Real.sqrt 2, 0, 1⟩

/-- `K•`, the entrywise 2-conjugate of `K`. -/
def opKbullet : Mat2 :=
  ⟨-(lam / Real.sqrt 2), 1 / Real.sqrt 2,
   1 / (Real.sqrt 2 * lam), -(1 / Real.sqrt 2)⟩

/-- **Lemma A.8** (arXiv:1403.2975v3, p. 25).  The shift of a state is a state,
and `Skew((D,∆) · Shift^k) = Skew(D,∆)`,
`Bias((D,∆) · Shift^k) = Bias(D,∆) + 2k`.

In the `(b,β,z,ζ,e,ε)` parametrisation of (34) the shift only changes
`z ↦ z − k` and `ζ ↦ ζ + k`, whence both claims follow by `ring`; the state
axioms `e² = b²+1`, `ε² = β²+1` are unchanged. -/
theorem lemma_A_8 (S : State) (k : ℤ) :
    State.skew (S.shift k) = State.skew S ∧
      State.bias (S.shift k) = State.bias S + 2 * (k : ℝ) := by
  constructor
  · simp [State.skew, State.shift]
  · simp [State.bias, State.shift]
    ring

end Qatlib.Papers.AncilFreeClfT14.MainResults.Legacy
