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
set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.UniqueCollision

def jwPsiCoord (k : ℕ) (i : Fin (2 * k + 1)) : ℕ × Bool :=
  (i.val / 2, i.val % 2 == 1)

def jwPhiCoord (k : ℕ) (i : Fin (2 * k + 1)) : ℕ × Bool :=
  ((i.val + 1) / 2, i.val % 2 == 1)

noncomputable def jwD2 (ε : ℝ) (l' l : Bool) : ℂ :=
  if l' = l then (if l then (-1 + 2 * ε) else (1 - 2 * ε)) else
    2 * Real.sqrt (ε - ε * ε)

noncomputable def jwStep1 (k N r : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  Matrix.of fun i j =>
    let ci := jwPhiCoord k i
    let cj := jwPsiCoord k j
    let ε : ℝ := (k - cj.1 : ℝ) / (N - r)
    if ci.1 = cj.1 ∧ ¬ci.2 then jwD2 ε false cj.2
    else if ci.1 = cj.1 + 1 ∧ ci.2 then jwD2 ε true cj.2
    else 0

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

noncomputable def jwWalk (k N r : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  jwStep2 k r * jwStep1 k N r

def jwCnt (k N r j : ℕ) (l : Bool) : ℕ :=
  Nat.choose k j * Nat.choose (N - k) (r - j) *
    (if l then k - j else N - r - (k - j))

noncomputable def jwStart (k N r : ℕ) : Fin (2 * k + 1) → ℂ :=
  fun i => (Real.sqrt (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ) : ℂ)

noncomputable def jwGoodTilde (k : ℕ) : Fin (2 * k + 1) → ℂ :=
  fun i => if (jwPsiCoord k i) = (k, false) then 1 else 0

noncomputable def jwStartNormSq (k N r : ℕ) : ℝ :=
  (∑ i : Fin (2 * k + 1), (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2 : ℝ))

noncomputable def jwAlpha (k N r : ℕ) : ℝ :=
  Real.sqrt (jwCnt k N r k false) / Real.sqrt (jwStartNormSq k N r)

noncomputable def jwT2 (k r : ℕ) : ℕ :=
  Nat.ceil (Real.pi * Real.sqrt ((r + 1 : ℝ)) / (6 * Real.sqrt ((k : ℝ))))

noncomputable def jwEpsArc (k r : ℕ) : ℝ :=
  (Real.pi - 1) / (3 * Real.sqrt ((k : ℝ))) -
    1 / (Real.pi * Real.sqrt ((r + 1 : ℝ)))

abbrev JRState (N r : ℕ) : Type :=
  {p : Finset (Fin N) × Fin N // p.1.card = r ∧ p.2 ∉ p.1}

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

noncomputable def jwBigDiff1 (N r : ℕ) : Matrix (JRState N r) (JRState N r) ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 then
      (((2 : ℝ) / (N - r : ℕ) : ℝ) : ℂ) - if p.1.2 = q.1.2 then 1 else 0
    else 0

def jwEmbedMat (N r : ℕ) : Matrix (JRState' N r) (JRState N r) ℂ :=
  Matrix.of fun p q =>
    if ((p.1.1 : Finset (Fin N)), p.1.2) = (q.1.1 ∪ {q.1.2}, q.1.2) then 1 else 0

noncomputable def jwBigDiff2 (N r : ℕ) : Matrix (JRState' N r) (JRState' N r) ℂ :=
  Matrix.of fun p q =>
    if p.1.1 = q.1.1 then
      (((2 : ℝ) / (r + 1 : ℕ) : ℝ) : ℂ) - if p.1.2 = q.1.2 then 1 else 0
    else 0

def jwDropMat (N r : ℕ) : Matrix (JRState N r) (JRState' N r) ℂ :=
  Matrix.of fun p q =>
    if ((p.1.1 : Finset (Fin N)), p.1.2) = (q.1.1.erase q.1.2, q.1.2) then 1 else 0

noncomputable def jwWalkBig (N r : ℕ) : Matrix (JRState N r) (JRState N r) ℂ :=
  jwDropMat N r * jwBigDiff2 N r * jwEmbedMat N r * jwBigDiff1 N r

noncomputable def jwStartBig (N r : ℕ) : JRState N r → ℂ :=
  fun _ => ((1 / Real.sqrt (Fintype.card (JRState N r) : ℝ) : ℝ) : ℂ)

def jwTypeOf {N r : ℕ} (I : Finset (Fin N)) (p : JRState N r) : ℕ × Bool :=
  ((p.1.1.filter (fun x => decide (x ∈ I))).card, decide (p.1.2 ∈ I))

noncomputable def jwPsiBig (k N r : ℕ) (I : Finset (Fin N)) (j : ℕ) (l : Bool) :
    JRState N r → ℂ :=
  fun p =>
    if (jwTypeOf I p) = (j, l) then
      ((1 / Real.sqrt (jwCnt k N r j l : ℝ) : ℝ) : ℂ)
    else 0

noncomputable def jwPsiBigAt (k N r : ℕ) (I : Finset (Fin N)) (i : Fin (2 * k + 1)) :
    JRState N r → ℂ :=
  jwPsiBig k N r I (jwPsiCoord k i).1 (jwPsiCoord k i).2

noncomputable def jwGoodVec (k N r : ℕ) (I : Finset (Fin N)) :
    JRState N r → ℂ :=
  fun p => if decide (I ⊆ p.1.1) then
      ((1 / Real.sqrt (jwCnt k N r k false : ℝ) : ℝ) : ℂ)
    else 0

noncomputable def jwFlipBig (_k N r : ℕ) (I : Finset (Fin N)) :
    Matrix (JRState N r) (JRState N r) ℂ :=
  Matrix.diagonal fun p => if I ⊆ p.1.1 then -1 else 1

noncomputable def jwFlipTilde (k : ℕ) : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) ℂ :=
  Matrix.of fun i j =>
    if (jwPsiCoord k i) = (k, false) ∧ (jwPsiCoord k j) = (k, false) then -1
    else if i = j then 1 else 0

noncomputable def jwRunMat (k N r t1 t2 : ℕ) (I : Finset (Fin N)) :
    Matrix (JRState N r) (JRState N r) ℂ :=
  (jwWalkBig N r ^ t2 * jwFlipBig k N r I) ^ t1

noncomputable def jwRunState (k N r t1 t2 : ℕ) (I : Finset (Fin N)) :
    JRState N r → ℂ := Matrix.mulVec (jwRunMat k N r t1 t2 I) (jwStartBig N r)

noncomputable def jwMarkedAmplitude (k N r t1 t2 : ℕ) (I : Finset (Fin N)) : ℂ :=
  ∑ p, star (jwGoodVec k N r I p) * jwRunState k N r t1 t2 I p

end Qatlib.Concepts.WalkFind.UniqueCollision
