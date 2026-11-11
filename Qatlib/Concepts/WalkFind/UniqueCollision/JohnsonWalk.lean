/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Real.Basic

/-!
# Johnson walk matrices and collision-search states

This module defines the reduced Johnson walk `jwWalk` and the corresponding walk `jwWalkBig` on
subset-address pairs. It specifies the two diffusion steps, the change between subset sizes, and
the type coordinates used to compress the walk in collision search
[Ambainis2007ElementDistinctness].

The starting vectors, marked vectors, phase flips, and iterated search evolution are defined in
both the full state space and the reduced coordinates. Their spectral interpretation is related
to quantum walks built from reflections [Szegedy2004].

## Main statements

* `jwWalk`: the reduced walk on `2*k+1` coordinates.
* `jwWalkBig`: the walk on `JRState N r`.
* `jwRunState`: the state after alternating marked flips with walk powers.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
* [Szegedy, 2004][Szegedy2004]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

/-- Map a reduced coordinate to its subset-intersection count and distinguished-address
membership bit. -/
def jwPsiCoord (k : ℕ) (i : Fin (2 * k + 1)) : ℕ × Bool :=
  (i.val / 2, i.val % 2 == 1)

/-- Map a reduced coordinate to the intersection count and membership bit after adjoining the
distinguished address. -/
def jwPhiCoord (k : ℕ) (i : Fin (2 * k + 1)) : ℕ × Bool :=
  ((i.val + 1) / 2, i.val % 2 == 1)

/-- The entries of the two-dimensional diffusion block with diagonal terms `1-2*ε` and `-1+2*ε`
and off-diagonal term `2*sqrt (ε-ε²)`. -/
noncomputable def jwD2 (ε : ℝ) (l' l : Bool) : ℂ :=
  if l' = l then (if l then (-1 + 2 * ε) else (1 - 2 * ε)) else
    2 * Real.sqrt (ε - ε * ε)

/-- The reduced first diffusion step, expressed from the `jwPsiCoord` basis to the `jwPhiCoord`
basis. -/
noncomputable def jwStep1 (k N r : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  Matrix.of fun i j =>
    let ci := jwPhiCoord k i
    let cj := jwPsiCoord k j
    let ε : ℝ := (k - cj.1 : ℝ) / (N - r)
    if ci.1 = cj.1 ∧ ¬ci.2 then jwD2 ε false cj.2
    else if ci.1 = cj.1 + 1 ∧ ci.2 then jwD2 ε true cj.2
    else 0

/-- The reduced second diffusion step, expressed from the `jwPhiCoord` basis back to the
`jwPsiCoord` basis. -/
noncomputable def jwStep2 (k r : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  Matrix.of fun i j =>
    let ci := jwPsiCoord k i
    let cj := jwPhiCoord k j
    let ε : ℝ := (cj.1 : ℝ) / (r + 1)
    if ci.1 = cj.1 ∧ ¬ci.2 ∧ ¬cj.2 then jwD2 ε false false
    else if ci.1 + 1 = cj.1 ∧ ci.2 ∧ cj.2 then jwD2 ε true true
    else if (ci.1 + 1 = cj.1 ∧ ci.2 ∧ ¬cj.2) ∨ (ci.1 = cj.1 ∧ ¬ci.2 ∧ cj.2) then
      jwD2 ε true false
    else 0

/-- One reduced Johnson-walk step, given by the product of the second and first diffusion
matrices. -/
noncomputable def jwWalk (k N r : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  jwStep2 k r * jwStep1 k N r

/-- The combinatorial population formula for a type with `j` distinguished subset elements and
membership bit `l`. -/
def jwCnt (k N r j : ℕ) (l : Bool) : ℕ :=
  Nat.choose k j * Nat.choose (N - k) (r - j) *
    (if l then k - j else N - r - (k - j))

/-- The unnormalized reduced starting vector whose amplitudes are square roots of the type
populations. -/
noncomputable def jwStart (k N r : ℕ) : Fin (2 * k + 1) → ℂ :=
  fun i => (Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℂ)

/-- The reduced coordinate vector supported on type `(k, false)`. -/
noncomputable def jwGoodTilde (k : ℕ) : Fin (2 * k + 1) → ℂ :=
  fun i => if (jwPsiCoord k i) = (k, false) then 1 else 0

/-- The sum of all type populations over the reduced coordinates. -/
noncomputable def jwStartNormSq (k N r : ℕ) : ℝ :=
  (∑ i : Fin (2 * k + 1), (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ))

/-- The square root of the marked population divided by the square root of the total reduced
population. -/
noncomputable def jwAlpha (k N r : ℕ) : ℝ :=
  Real.sqrt (jwCnt k N r k false) / Real.sqrt (jwStartNormSq k N r)

/-- The ceiling of `π * sqrt (r+1) / (6 * sqrt k)`, used as an inner walk iteration count. -/
noncomputable def jwT2 (k r : ℕ) : ℕ :=
  Nat.ceil (Real.pi * Real.sqrt ((r + 1 : ℝ)) / (6 * Real.sqrt ((k : ℝ))))

/-- The explicit arc-separation parameter `(π-1)/(3*sqrt k) - 1/(π*sqrt (r+1))`. -/
noncomputable def jwEpsArc (k r : ℕ) : ℝ :=
  (Real.pi - 1) / (3 * Real.sqrt ((k : ℝ))) -
    1 / (Real.pi * Real.sqrt ((r + 1 : ℝ)))

/-- Pairs consisting of an `r`-element address subset and a distinguished address outside that
subset. -/
abbrev JRState (N r : ℕ) : Type :=
  {p : Finset (Fin N) × Fin N // p.1.card = r ∧ p.2 ∉ p.1}

/-- Pairs consisting of an `(r+1)`-element address subset and a distinguished address inside
that subset. -/
abbrev JRState' (N r : ℕ) : Type :=
  {p : Finset (Fin N) × Fin N // p.1.card = r + 1 ∧ p.2 ∈ p.1}

instance jrStateFintype (N r : ℕ) : Fintype (JRState N r) :=
  Subtype.fintype (fun p : Finset (Fin N) × Fin N => p.1.card = r ∧ p.2 ∉ p.1)

instance jrState'DecidableEq (N r : ℕ) : DecidableEq (JRState' N r) :=
  inferInstanceAs (DecidableEq {p : Finset (Fin N) × Fin N // p.1.card = r + 1 ∧ p.2 ∈ p.1})

instance jrStateDecidableEq (N r : ℕ) : DecidableEq (JRState N r) :=
  inferInstanceAs (DecidableEq {p : Finset (Fin N) × Fin N // p.1.card = r ∧ p.2 ∉ p.1})

instance jrState'Fintype (N r : ℕ) : Fintype (JRState' N r) :=
  Subtype.fintype (fun p : Finset (Fin N) × Fin N => p.1.card = r + 1 ∧ p.2 ∈ p.1)

/-- The full first diffusion matrix, acting on distinguished addresses outside each fixed
`r`-element subset. -/
noncomputable def jwBigDiff1 (N r : ℕ) : Matrix (JRState N r) (JRState N r) ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 then
      (((2 : ℝ) / (N - r : ℕ) : ℝ) : ℂ) - if p.1.2 = q.1.2 then 1 else 0
    else 0

/-- The incidence matrix that adjoins the distinguished address to the stored subset. -/
def jwEmbedMat (N r : ℕ) : Matrix (JRState' N r) (JRState N r) ℂ :=
  Matrix.of fun p q =>
    if ((p.1.1 : Finset (Fin N)), p.1.2) = (q.1.1 ∪ {q.1.2}, q.1.2) then 1 else 0

/-- The full second diffusion matrix, acting on distinguished addresses within each fixed
`(r+1)`-element subset. -/
noncomputable def jwBigDiff2 (N r : ℕ) : Matrix (JRState' N r) (JRState' N r) ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 then
      (((2 : ℝ) / (r + 1 : ℕ) : ℝ) : ℂ) - if p.1.2 = q.1.2 then 1 else 0
    else 0

/-- The incidence matrix that removes the distinguished address from the stored subset. -/
def jwDropMat (N r : ℕ) : Matrix (JRState N r) (JRState' N r) ℂ :=
  Matrix.of fun p q =>
    if ((p.1.1 : Finset (Fin N)), p.1.2) = (q.1.1.erase q.1.2, q.1.2) then 1 else 0

/-- The full Johnson-walk matrix obtained by first diffusion, adjoining, second diffusion, and
removal. -/
noncomputable def jwWalkBig (N r : ℕ) : Matrix (JRState N r) (JRState N r) ℂ :=
  jwDropMat N r * jwBigDiff2 N r * jwEmbedMat N r * jwBigDiff1 N r

/-- The constant vector with amplitude the reciprocal square root of the number of Johnson
states. -/
noncomputable def jwStartBig (N r : ℕ) : JRState N r → ℂ :=
  fun _ => ((1 / Real.sqrt (Fintype.card (JRState N r) : ℝ) : ℝ) : ℂ)

/-- The type of a Johnson state relative to `I`, recording the subset intersection size and
whether its distinguished address lies in `I`. -/
def jwTypeOf {N r : ℕ} (I : Finset (Fin N)) (p : JRState N r) : ℕ × Bool :=
  ((p.1.1.filter (fun x => decide (x ∈ I))).card, decide (p.1.2 ∈ I))

/-- The scaled indicator of a specified Johnson-state type, with scale the reciprocal square
root of `jwCnt`. -/
noncomputable def jwPsiBig (k N r : ℕ) (I : Finset (Fin N)) (j : ℕ) (l : Bool) :
    JRState N r → ℂ :=
  fun p =>
    if (jwTypeOf I p) = (j, l) then
      ((1 / Real.sqrt (jwCnt k N r j l : ℝ) : ℝ) : ℂ)
    else 0

/-- The full type vector indexed by a reduced `jwPsiCoord` coordinate. -/
noncomputable def jwPsiBigAt (k N r : ℕ) (I : Finset (Fin N)) (i : Fin (2 * k + 1)) :
    JRState N r → ℂ :=
  jwPsiBig k N r I (jwPsiCoord k i).1 (jwPsiCoord k i).2

/-- The scaled indicator of Johnson states whose stored subset contains `I`. -/
noncomputable def jwGoodVec (k N r : ℕ) (I : Finset (Fin N)) :
    JRState N r → ℂ :=
  fun p => if decide (I ⊆ p.1.1) then
      ((1 / Real.sqrt (jwCnt k N r k false : ℝ) : ℝ) : ℂ)
    else 0

/-- The diagonal phase flip on full states whose stored subset contains `I`. -/
noncomputable def jwFlipBig (_k N r : ℕ) (I : Finset (Fin N)) :
    Matrix (JRState N r) (JRState N r) ℂ :=
  Matrix.diagonal fun p => if I ⊆ p.1.1 then -1 else 1

/-- The reduced phase flip that negates the coordinate of type `(k, false)`. -/
noncomputable def jwFlipTilde (k : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  Matrix.of fun i j =>
    if (jwPsiCoord k i) = (k, false) ∧ (jwPsiCoord k j) = (k, false) then -1
    else if i = j then 1 else 0

/-- The search evolution consisting of `t1` repetitions of a marked flip followed by `t2` full
walk steps. -/
noncomputable def jwRunMat (k N r t1 t2 : ℕ) (I : Finset (Fin N)) :
    Matrix (JRState N r) (JRState N r) ℂ :=
  (jwWalkBig N r ^ t2 * jwFlipBig k N r I) ^ t1

/-- Apply the full search evolution to `jwStartBig`. -/
noncomputable def jwRunState (k N r t1 t2 : ℕ) (I : Finset (Fin N)) :
    JRState N r → ℂ := Matrix.mulVec (jwRunMat k N r t1 t2 I) (jwStartBig N r)

/-- The inner product of `jwGoodVec` with the evolved full search state. -/
noncomputable def jwMarkedAmplitude (k N r t1 t2 : ℕ) (I : Finset (Fin N)) : ℂ :=
  ∑ p, star (jwGoodVec k N r I p) * jwRunState k N r t1 t2 I p

end Qatlib.Concepts.WalkFind.UniqueCollision
