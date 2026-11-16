/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StabRank21.ExactRank.MagicStateAmplitudeDefs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Paper-level objects for §4 of Peleg–Shpilka–Volk (arXiv:2106.03214v2)

The paper works at the level of amplitude functions on the Boolean cube
`BooleanVec n = Fin n → ZMod 2`.  This module fixes the paper's §4 vocabulary:

* `threshold p n` is the threshold function `THR^{pn}` of §4.1 (`THR(x) = 1`
  iff `|x| ≥ pn`);
* `maj m` is the majority function `Maj_m` of §4.1 (ties counted as `1`, the
  convention used in the proof of Lemma 4.1);
* `layer n k` is the `k`-th Hamming layer `L_k` of §4.1;
* `wrongOn` is the paper's "`ε`-wrong on `L_k`";
* `approximatesThreshold` is the paper's "`(ε,γ)`-approximates `THR^{pn}`",
  with the layer window `[pn − 5√(2pn), pn + 5√(2pn)]` written with real
  distance instead of floor/ceiling;
* `restrict` is the restriction `g_D` obtained by fixing the coordinates
  outside `D` to zero (§4.1);
* `FB`, `eta`, `layerAmp`, `fPsi` are the amplitude function `F_B`, the ratio
  `η = |β|/|α|`, the layer magnitude `m_k = |α|^{n−k}|β|^k` and the Boolean
  function `f_ψ` of Eq. (4) (§4.2);
* `polyApproximates` is the uniform-distribution polynomial approximation
  error of §4.3.

All counting statements are written as integer inequalities
(`den * #errors ≤ num * #all`) so that no division-by-zero convention is
implicit; these are equivalent to the paper's probability inequalities on a
uniform finite cube.

Fixed source: arXiv:2106.03214v2 (Quantum 6, 652, 2022).
-/

set_option autoImplicit false

namespace Qatlib.Papers.StabRank21.MainResults.Section4Model

open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Papers.StabRank21.ExactRank
open scoped Classical BigOperators

noncomputable section

/-- Boolean functions `F_2^n → F_2` of §4, represented on the algebraic cube
`BooleanVec n = Fin n → ZMod 2`. -/
abbrev BoolFun (n : ℕ) := BooleanVec n → ZMod 2

/-- The paper's `pn` (floor of the real `p·n`), used for `THR^{pn}` and the
threshold `m_{pn−1}` in Eq. (4). -/
def pnFloor (p : ℝ) (n : ℕ) : ℕ := Nat.floor (p * (n : ℝ))

/-- `THR^{pn}` of §4.1: `1` iff the Hamming weight is at least `pn`. -/
def threshold (p : ℝ) (n : ℕ) : BoolFun n :=
  fun x => if pnFloor p n ≤ cubeWeight x then 1 else 0

/-- `Maj_m` of §4.1, with the threshold `|x| ≥ m/2` (ties evaluated to `1`,
the convention compatible with `THR^{pn}` at `m = 2pn`). -/
def maj (m : ℕ) : BoolFun m :=
  fun x => if m ≤ 2 * cubeWeight x then 1 else 0

/-- The `k`-th Hamming layer `L_k = {x | |x| = k}` of §4.1. -/
def layer (n k : ℕ) : Finset (BooleanVec n) :=
  Finset.univ.filter (fun x => cubeWeight x = k)

/-- `f` is `ε`-wrong on the layer `L_k` with respect to `T` (§4.1): the
fraction of `x ∈ L_k` with `f x ≠ T x` is at least `ε`. -/
def wrongOn {n : ℕ} (f T : BoolFun n) (k : ℕ) (ε : ℝ) : Prop :=
  ε ≤ ((layer n k).filter (fun x => f x ≠ T x)).card / ((layer n k).card : ℝ)

/-- The layers `k ∈ [pn − 5√(2pn), pn + 5√(2pn)]` used in the definition of
`(ε,γ)`-approximation (§4.1), written with real distance. -/
def windowLayers (p : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter
    (fun k => |(k : ℝ) - p * (n : ℝ)| ≤ 5 * Real.sqrt (2 * p * (n : ℝ)))

/-- `f` `(ε,γ)`-approximates `THR^{pn}` (§4.1): `f` is `ε`-wrong on at most a
`γ` fraction of the layers in the window. -/
def approximatesThreshold {n : ℕ} (f : BoolFun n) (p : ℝ) (ε γ : ℝ) : Prop :=
  (((windowLayers p n).filter (fun k => wrongOn f (threshold p n) k ε)).card : ℝ)
    ≤ γ * ((windowLayers p n).card : ℝ)

/-- The restriction `g_D` of §4.1: coordinates outside `D` are set to zero and
the remaining coordinates are identified with `Fin m` through a bijection
`e : Fin m ≃ {i // i ∈ D}`. -/
def restrict {n m : ℕ} (f : BoolFun n) (D : Finset (Fin n))
    (e : Fin m ≃ {i : Fin n // i ∈ D}) : BoolFun m :=
  fun y => f (fun i => if h : i ∈ D then y (e.symm ⟨i, h⟩) else 0)

/-- Uniform counting form of `Pr_{x ∈ F_2^m}[P x] ≥ num/den`. -/
def uniformAtLeast {m : ℕ} (P : BooleanVec m → Prop) (num den : ℕ) : Prop :=
  den * (Finset.univ.filter P).card ≥ num * Fintype.card (BooleanVec m)

/-- The amplitude function `F_B(x) = α^{n−|x|} β^{|x|}` of a product state
`|B⟩^{⊗n} = (α|0⟩ + β|1⟩)^{⊗n}` (§4.2). -/
def FB (α β : ℝ) (n : ℕ) : BooleanVec n → ℂ :=
  fun x => (α : ℂ) ^ (n - cubeWeight x) * (β : ℂ) ^ cubeWeight x

/-- The ratio `η = |β|/|α|` of §4.2. -/
def eta (α β : ℝ) : ℝ := |β| / |α|

/-- The layer magnitude `m_k = |α|^{n−k}|β|^k` of §4.2. -/
def layerAmp (α β : ℝ) (n k : ℕ) : ℝ := |α| ^ (n - k) * |β| ^ k

/-- The Boolean function `f_ψ` of Eq. (4) (§4.2):
`f_ψ(x) = 1` iff `|ψ(x)| ≤ ((1+η)/2) m_{pn−1}`, and `0` otherwise. -/
def fPsi (α β p : ℝ) (n : ℕ) (ψ : BooleanVec n → ℂ) : BoolFun n :=
  fun x =>
    if ‖ψ x‖ ≤ ((1 + eta α β) / 2) * layerAmp α β n (pnFloor p n - 1)
    then 1 else 0

/-- Uniform-distribution polynomial approximation error of §4.3:
`Pr[g ≠ P] ≤ num/den` on `F_2^m`, written as `den * #errors ≤ num * #points`. -/
def polyApproximates {m : ℕ} (g : BoolFun m) (P : MvPolynomial (Fin m) (ZMod 2))
    (num den : ℕ) : Prop :=
  den * (Finset.univ.filter (fun x : BooleanVec m => MvPolynomial.eval x P ≠ g x)).card
    ≤ num * Fintype.card (BooleanVec m)

/-- Unfolding lemma: `threshold` is the indicator of `pnFloor p n ≤ cubeWeight x`. -/
@[simp] theorem threshold_apply {n : ℕ} (p : ℝ) (x : BooleanVec n) :
    threshold p n x = if pnFloor p n ≤ cubeWeight x then 1 else 0 := rfl

/-- Unfolding lemma: `maj` is the indicator of `m ≤ 2 * cubeWeight x`. -/
@[simp] theorem maj_apply {m : ℕ} (x : BooleanVec m) :
    maj m x = if m ≤ 2 * cubeWeight x then 1 else 0 := rfl

/-- Unfolding lemma: `fPsi` compares `‖ψ x‖` with the threshold layer amplitude. -/
@[simp] theorem fPsi_apply {n : ℕ} (α β p : ℝ) (ψ : BooleanVec n → ℂ)
    (x : BooleanVec n) :
    fPsi α β p n ψ x =
      if ‖ψ x‖ ≤ ((1 + eta α β) / 2) * layerAmp α β n (pnFloor p n - 1)
      then 1 else 0 := rfl

/-- The Boolean cube `F_2^m` has `2^m` points. -/
theorem card_booleanVec (m : ℕ) : Fintype.card (BooleanVec m) = 2 ^ m := by
  simp [BooleanVec, ZMod.card]

end

end Qatlib.Papers.StabRank21.MainResults.Section4Model
