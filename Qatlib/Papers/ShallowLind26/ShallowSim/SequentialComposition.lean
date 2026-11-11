/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.FinCases

/-!
# Sequential composition of local transducers (Lemma 4.2)

Shen--Wu--Yuan--Zhang, fixed arXiv:2610.05362v1, Lemma 4.2, page 17.

Two local transducers `S_1`, `S_2` each satisfy a graph identity on their own
public/private splitting,

`S_j (I, γ_j)ᵀ = (V_j, γ_j)ᵀ`,

i.e. `a_j + b_j γ_j = V_j` and `c_j + d_j γ_j = γ_j` for the blocks
`S_j = [[a_j, b_j], [c_j, d_j]]`.  When `S_1` is the identity on the private
summand of `S_2` (and conversely), the product acts on the three-component
vector

`(x, γ_1 x, γ_2 V_1 x)`

by mapping the public component to `V_2 V_1 x` and leaving both private
components fixed.  Iterating gives the target `V_L ⋯ V_1` and catalyst map
`Γ x = ∑_j γ_j V_{j-1} ⋯ V_1 x`.

We formalize the two-transducer step over an arbitrary associative ring.  The
three block coordinates are public, private `1` and private `2`; the product
`S_2 S_1` is computed explicitly, and the graph identities are used in the
order fixed by the source.  This is the algebraic heart of the sequential
composition lemma; the naturality in the number of transducers is ordinary
induction on the same step.
-/

namespace Qatlib.Papers.ShallowLind26.ShallowSim.SequentialComposition

set_option autoImplicit false

variable {R : Type*} [Ring R]

/-- First local transducer, acting on public ⊕ private `1` and fixing private
`2`. -/
def S1 (a1 b1 c1 d1 : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => a1 | 0, 1 => b1
    | 1, 0 => c1 | 1, 1 => d1
    | 2, 2 => 1
    | _, _ => 0

/-- Second local transducer, acting on public ⊕ private `2` and fixing private
`1`. -/
def S2 (a2 b2 c2 d2 : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => match i, j with
    | 0, 0 => a2 | 0, 2 => b2
    | 1, 1 => 1
    | 2, 0 => c2 | 2, 2 => d2
    | _, _ => 0

/-- The three-component vector `(x, γ₁ x, γ₂ V₁ x)`. -/
def state (x g1 g2 V1 : R) : Fin 3 → R :=
  fun i => match i with
    | 0 => x
    | 1 => g1 * x
    | 2 => g2 * (V1 * x)
    | _ => 0

/-- **Lemma 4.2, two-transducer step.**  Given the two graph identities, the
product `S_2 S_1` maps `(x, γ₁x, γ₂V₁x)` to `(V₂V₁x, γ₁x, γ₂V₁x)`. -/
theorem sequential_composition (a1 b1 c1 d1 a2 b2 c2 d2 x g1 g2 V1 V2 : R)
    (h1a : a1 + b1 * g1 = V1) (h1c : c1 + d1 * g1 = g1)
    (h2a : a2 + b2 * g2 = V2) (h2c : c2 + d2 * g2 = g2) :
    (S2 a2 b2 c2 d2).mulVec ((S1 a1 b1 c1 d1).mulVec (state x g1 g2 V1))
      = fun i => match i with
          | 0 => V2 * (V1 * x)
          | 1 => g1 * x
          | 2 => g2 * (V1 * x)
          | _ => 0 := by
  rw [Matrix.mulVec_mulVec]
  funext i
  fin_cases i <;>
    simp [S1, S2, state, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three]
  · -- public component
    calc a2 * a1 * x + a2 * b1 * (g1 * x) + b2 * (g2 * (V1 * x))
        = a2 * ((a1 + b1 * g1) * x) + b2 * (g2 * (V1 * x)) := by noncomm_ring
      _ = a2 * (V1 * x) + b2 * (g2 * (V1 * x)) := by rw [h1a]
      _ = (a2 + b2 * g2) * (V1 * x) := by noncomm_ring
      _ = V2 * (V1 * x) := by rw [h2a]
  · -- private component one
    calc c1 * x + d1 * (g1 * x) = (c1 + d1 * g1) * x := by noncomm_ring
      _ = g1 * x := by rw [h1c]
  · -- private component two
    calc c2 * a1 * x + c2 * b1 * (g1 * x) + d2 * (g2 * (V1 * x))
        = c2 * ((a1 + b1 * g1) * x) + d2 * (g2 * (V1 * x)) := by noncomm_ring
      _ = c2 * (V1 * x) + d2 * (g2 * (V1 * x)) := by rw [h1a]
      _ = (c2 + d2 * g2) * (V1 * x) := by noncomm_ring
      _ = g2 * (V1 * x) := by rw [h2c]

end Qatlib.Papers.ShallowLind26.ShallowSim.SequentialComposition
