/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option backward.isDefEq.respectTransparency false

/-!
# BoolHidShift11.MainResults.BHSPModel — shared model for the Boolean hidden shift problem

Fixed version: arXiv:1103.3017v1 (2011-03-15, Gavinsky–Roetteler–Roland,
*Quantum algorithm for the Boolean hidden shift problem*).

This file freezes the paper's own notation (Definitions 1 and 2, §2, p.2):

* `Reg n = Fin n → Bool` is the cube `Z_2^n` (Frozen
  `QuantumAlgorithm.Concepts.MbqcFlow.FlowDecision.Reg`); group addition is
  `regXor`, the paper's `x + v`.
* `parityDot u x` is the inner product `⟨u,x⟩ ∈ Z_2`; `chi u x` is the real
  character `χ_u(x) = (-1)^{⟨u,x⟩}`.
* `signedFun f` is the paper's equation (1): `F(x) = (-1)^{f(x)}`.
* `fourierCoef F u` is the Fourier coefficient `F̂(u) = 2^{-n} Σ_x F(x) χ_u(x)`.
* `influence F v` is Definition 2's `γ_{f,v} = Pr_x[F(x) ≠ F(x+v)]` for the
  uniform distribution over the cube (as a normalized finite sum).
* `BHSPInstance n` is Definition 1: an aperiodic Boolean `f`, a second Boolean
  `g`, and the hidden shift `s` with `g(x) = f(x+s)`.

The paper writes the ambient group additively over `Z_2^n`; `regXor` is exactly
that addition, and no new axioms or algorithmic assumptions are introduced here.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

namespace Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel

/-- The uniform counting measure `2^{-n}` on the cube, as a real number. -/
def uniformWeight (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹

/-- Group addition on `Z_2^n`: the paper's `x + v` (coordinatewise XOR). -/
def regXor {n : ℕ} (x v : Reg n) : Reg n := fun i => Bool.xor (x i) (v i)

/-- The paper's inner product `⟨u,x⟩ = Σ_i u_i x_i` over `Z_2`, as a Boolean
parity. -/
def parityDot {n : ℕ} (u x : Reg n) : Bool :=
  decide ((Finset.univ.filter (fun i => u i && x i)).card % 2 = 1)

/-- The standard character `χ_u(x) = (-1)^{⟨u,x⟩}` of `Z_2^n`, real-valued. -/
def chi {n : ℕ} (u x : Reg n) : ℝ :=
  ∏ i, if u i && x i then (-1 : ℝ) else 1

/-- Equation (1) of the paper: the `{+1,-1}`-valued lift `F(x) = (-1)^{f(x)}`
of a Boolean function. -/
def signedFun {n : ℕ} (f : Reg n → Bool) : Reg n → ℝ :=
  fun x => if f x then (-1 : ℝ) else 1

/-- The real Fourier coefficient `F̂(u) = 2^{-n} Σ_x F(x) χ_u(x)`. -/
def fourierCoef {n : ℕ} (F : Reg n → ℝ) (u : Reg n) : ℝ :=
  uniformWeight n * ∑ x, F x * chi u x

/-- Definition 2 of the paper: the influence `γ_{f,v} = Pr_x[F(x) ≠ F(x+v)]`
of the shift `v` on `F`, where `x` is uniform on the cube. -/
def influence {n : ℕ} (F : Reg n → ℝ) (v : Reg n) : ℝ :=
  uniformWeight n * ∑ x, if F x = F (regXor x v) then (0 : ℝ) else 1

/-- Definition 2's minimum influence `γ_f = min_v γ_{f,v}`. The paper minimizes
over `n`-bit `v`; the trivial shift `v = 0` always has influence `0`, so the
nonempty family used here excludes it (this is the quantity that occurs in
Theorem 1, where `γ_f > 0`). -/
def minInfluence {n : ℕ} (F : Reg n → ℝ) : ℝ :=
  sInf (influence F '' {v : Reg n | v ≠ ZeroStr n})

/-- Definition 1 of the paper: a Boolean hidden shift problem instance. The
function `f` is aperiodic (no nonzero period), `g` is the shifted function, and
`shift` is the solution `s` with `g(x) = f(x+s)`. -/
structure BHSPInstance (n : ℕ) where
  /-- The secret-free Boolean function `f : Z_2^n → Z_2`. -/
  f : Reg n → Bool
  /-- The shifted Boolean function `g`. -/
  g : Reg n → Bool
  /-- The hidden shift `s`. -/
  shift : Reg n
  /-- Aperiodicity of `f`: `f(x) ≡ f(x+t)` forces `t = 0`. -/
  aperiodic : ∀ t : Reg n, (∀ x : Reg n, f x = f (regXor x t)) → t = ZeroStr n
  /-- The promise `g(x) ≡ f(x+s)`. -/
  shifted : ∀ x : Reg n, g x = f (regXor x shift)

/-! ### Elementary group facts for `regXor` -/

/-- Reg Xor zero right: the paper model identity or bound. -/
@[simp] theorem regXor_zero_right {n : ℕ} (x : Reg n) : regXor x (ZeroStr n) = x := by
  funext i
  simp [regXor, ZeroStr]

/-- Reg Xor zero left: the paper model identity or bound. -/
@[simp] theorem regXor_zero_left {n : ℕ} (x : Reg n) : regXor (ZeroStr n) x = x := by
  funext i
  simp [regXor, ZeroStr]

/-- Reg Xor self: the paper model identity or bound. -/
@[simp] theorem regXor_self {n : ℕ} (x : Reg n) : regXor x x = ZeroStr n := by
  funext i
  simp [regXor, ZeroStr]

/-- Reg Xor comm: the paper model identity or bound. -/
theorem regXor_comm {n : ℕ} (x y : Reg n) : regXor x y = regXor y x := by
  funext i
  simp [regXor, Bool.xor_comm]

/-- Reg Xor assoc: the paper model identity or bound. -/
theorem regXor_assoc {n : ℕ} (x y z : Reg n) :
    regXor (regXor x y) z = regXor x (regXor y z) := by
  funext i
  simp [regXor]

/-- Reg Xor left cancel: the paper model identity or bound. -/
theorem regXor_left_cancel {n : ℕ} (x y : Reg n) : regXor x (regXor x y) = y := by
  funext i
  simp [regXor]

/-- Reg Xor eq zero iff: the paper model identity or bound. -/
theorem regXor_eq_zero_iff {n : ℕ} (x y : Reg n) :
    regXor x y = ZeroStr n ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp [regXor, ZeroStr] at hi
    exact hi
  · intro h
    subst h
    simp

/-- Reg Xor eq iff: the paper model identity or bound. -/
theorem regXor_eq_iff {n : ℕ} (x y z : Reg n) :
    regXor x y = z ↔ y = regXor x z := by
  constructor
  · intro h
    rw [← h]
    exact (regXor_left_cancel x y).symm
  · intro h
    rw [h, regXor_left_cancel]

end Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
