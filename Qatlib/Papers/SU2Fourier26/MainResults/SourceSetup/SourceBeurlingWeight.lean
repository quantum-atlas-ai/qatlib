/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Weighted Wiener algebra `A_w` for strong Beurling weights

Fixed source: arXiv:2603.02021v1 (2026-03-02), G. Mnatsakanyan,
"ℓ¹ mapping properties, smoothness and decay for SU(2)-valued nonlinear Fourier transform".

This file sets up the paper's analytic vocabulary in the paper layer, on the
period-one circle `UnitAddCircle` (the paper's `𝕋`, §1 p.2):

* `StrongBeurlingWeight` — conditions i–iii of p.2;
* `ℓ¹_w` (`MemL1w`, `L1wNorm`) and the weighted Wiener algebra
  `A_w` (`MemAW`, `AWnorm`), defined through the linear Fourier coefficients,
  matching the paper's Gelfand-isometric description on p.2;
* `starFun` — the holomorphic reflection `f*(z) = f(z⁻¹)` on `𝕋`, i.e.
  `f*(x) = f(-x)` (p.1);
* `IsOuterInD` / `IsOuterInDStar` — "outer analytic functions" on the disc /
  exterior disc.  The paper only uses the concrete consequences of outer-ness
  that its proofs need, namely that `f` and `1/f` are in `A_w` and have
  Fourier support on the correct half-line (p.9, proof of Lemma 3).  These are
  bundled here as the working form of "outer", exactly as used in §3.2–§3.3.
* `MemHS`, `sobolevNorm`, `circleDeriv`, `l2Norm`, `linftyNorm` — the Sobolev /
  `L²` / `L∞` vocabulary of Theorem 3 (p.4).

Conventions: functions live on `UnitAddCircle = AddCircle 1`, whose characters
are `fourier n (x) = exp (2πinx)`; `fourierCoeff f n` is the paper's `f̂(n)`.
All statements are mirrored from the fixed PDF version (page numbers refer to
the arXiv v1 page numbers).
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

namespace Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

noncomputable section

/-- The paper's circle `𝕋`, represented as `ℝ / ℤ` (period-one parametrization). -/
abbrev CircleT : Type := UnitAddCircle

/-- A strong Beurling weight on `ℤ` (arXiv:2603.02021v1, p.2, conditions i–iii):
`w ≥ 1`, symmetric, submultiplicative and with `log w(n)/n → 0`. -/
structure StrongBeurlingWeight where
  /-- The weight function `w : ℤ → [1, ∞)`. -/
  w : ℤ → ℝ
  /-- Condition 0 (weights are ≥ 1). -/
  one_le : ∀ n : ℤ, 1 ≤ w n
  /-- Condition i: `w(-n) = w(n)`. -/
  symm : ∀ n : ℤ, w (-n) = w n
  /-- Condition ii: `w(n + m) ≤ w(n) w(m)`. -/
  submultiplicative : ∀ m n : ℤ, w (m + n) ≤ w m * w n
  /-- Condition iii: `log w(n) / n → 0` as `n → +∞`. -/
  log_growth : Tendsto (fun n : ℕ => Real.log (w (n : ℤ)) / (n : ℝ)) atTop (nhds 0)

/-- Membership in the weighted space `ℓ¹_w` (p.2): `∑ |a_n| w(n) < ∞`. -/
def MemL1w (W : StrongBeurlingWeight) (c : ℤ → ℂ) : Prop :=
  Summable fun n : ℤ => ‖c n‖ * W.w n

/-- The weighted `ℓ¹` norm `‖c‖_{ℓ¹_w} = ∑ |c_n| w(n)` (p.2). -/
def L1wNorm (W : StrongBeurlingWeight) (c : ℤ → ℂ) : ℝ :=
  ∑' n : ℤ, ‖c n‖ * W.w n

/-- Membership in `ℓ²(ℤ)` for coefficient sequences. -/
def MemL2 (c : ℤ → ℂ) : Prop := Summable fun n : ℤ => ‖c n‖ ^ 2

/-- The unweighted `ℓ²` norm of a sequence. -/
def L2Norm (c : ℤ → ℂ) : ℝ := Real.sqrt (∑' n : ℤ, ‖c n‖ ^ 2)

/-- The holomorphic reflection `f*(z) = f(z⁻¹)` on `𝕋` (p.1).  On the circle this is
`starFun f x = f (-x)`. -/
def starFun (f : CircleT → ℂ) : CircleT → ℂ := fun x => f (-x)

/-- Membership of a circle function in the weighted Wiener algebra `A_w` (p.2): its
linear Fourier coefficients form an element of `ℓ¹_w`. -/
def MemAW (W : StrongBeurlingWeight) (f : CircleT → ℂ) : Prop :=
  MemL1w W fun n : ℤ => fourierCoeff f n

/-- The algebra norm `‖f‖_{A_w} = ‖f̂‖_{ℓ¹_w}` (p.2). -/
def AWnorm (W : StrongBeurlingWeight) (f : CircleT → ℂ) : ℝ :=
  L1wNorm W fun n : ℤ => fourierCoeff f n

/-- Membership in the fractional Sobolev space `H^s(𝕋)` (p.3):
`∑ (1 + |n|²)^s |f̂(n)|² < ∞`. -/
def MemHS (s : ℝ) (f : CircleT → ℂ) : Prop :=
  Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ s * ‖fourierCoeff f n‖ ^ 2

/-- The Sobolev norm `‖f‖_{H^s(𝕋)}` (p.3), written as the square root of the
Fourier-side sum. -/
def sobolevNorm (s : ℝ) (f : CircleT → ℂ) : ℝ :=
  Real.sqrt (∑' n : ℤ, (1 + (n : ℝ) ^ 2) ^ s * ‖fourierCoeff f n‖ ^ 2)

/-- The `L²(𝕋)` norm of a circle function, via the Fourier coefficients. -/
def l2Norm (f : CircleT → ℂ) : ℝ := Real.sqrt (∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2)

/-- The derivative of a circle function, as a Fourier multiplier:
`f'(x) = ∑ 2πi n · f̂(n) · e^{2πinx}` (paper p.13, the `J^1` multiplier). -/
def circleDeriv (f : CircleT → ℂ) : CircleT → ℂ :=
  fun x => ∑' n : ℤ, (2 * Real.pi * Complex.I * (n : ℂ)) * fourierCoeff f n * fourier n x

/-- The `L∞(𝕋)` norm of a circle function, as a supremum of pointwise norms. -/
def linftyNorm (f : CircleT → ℂ) : ℝ := sSup (Set.range fun x => ‖f x‖)

/-- The pointwise bound `‖b‖_{L∞(𝕋)} < 1` appearing in Theorem 1 / Lemma 2 (p.3, p.8). -/
def MemBallLinfty (f : CircleT → ℂ) : Prop := ∀ x : CircleT, ‖f x‖ < 1

/-- `f` is analytic in the unit disc `𝔻` and in `A_w`: `f̂(n) = 0` for `n < 0` (p.6, (2.6)). -/
def IsAnalyticInD (W : StrongBeurlingWeight) (f : CircleT → ℂ) : Prop :=
  MemAW W f ∧ ∀ n : ℤ, n < 0 → fourierCoeff f n = 0

/-- `f` is outer in `𝔻` (working form used throughout §3.2–§3.3 of the paper): `f`
is analytic in the disc, and so is `1/f`; the paper's outer hypothesis is used
precisely through the analyticity of `1/f` and of its Fourier support (p.9). -/
structure IsOuterInD (W : StrongBeurlingWeight) (f : CircleT → ℂ) : Prop where
  /-- `f ∈ A_w`. -/
  memAW : MemAW W f
  /-- Analyticity in the disc: only nonnegative Fourier modes. -/
  support_nonneg : ∀ n : ℤ, n < 0 → fourierCoeff f n = 0
  /-- `1/f ∈ A_w`. -/
  memAW_inv : MemAW W fun x => (f x)⁻¹
  /-- Analyticity of `1/f` in the disc. -/
  support_nonneg_inv : ∀ n : ℤ, n < 0 → fourierCoeff (fun x => (f x)⁻¹) n = 0

/-- `f` is analytic (with analytic inverse) in the exterior disc `𝔻*`: only
nonpositive Fourier modes.  This is the paper's standing hypothesis on `a` in
§3.2 (`a*` outer in `𝔻` is equivalent, via `f*`). -/
structure IsOuterInDStar (W : StrongBeurlingWeight) (f : CircleT → ℂ) : Prop where
  /-- `f ∈ A_w`. -/
  memAW : MemAW W f
  /-- Analyticity in the exterior disc: only nonpositive Fourier modes. -/
  support_nonpos : ∀ n : ℤ, 0 < n → fourierCoeff f n = 0
  /-- `1/f ∈ A_w`. -/
  memAW_inv : MemAW W fun x => (f x)⁻¹
  /-- Analyticity of `1/f` in the exterior disc. -/
  support_nonpos_inv : ∀ n : ℤ, 0 < n → fourierCoeff (fun x => (f x)⁻¹) n = 0

/-- The §3.2 standing hypothesis set on the NLFT data `(a, b)` (arXiv:2603.02021v1,
p.6: `a*` outer in `𝔻*`, `‖b‖_{L∞(𝕋)} < 1`, and `|a|² + |b|² = 1`), unpacked into
the concrete Fourier-support form that its proofs use.  Namely: `a, a*, 1/a, 1/a*`
all lie in `A_w`, `a` (resp. `1/a`) is analytic in the exterior disc, and `a*`
(resp. `1/a*`) is analytic in the disc.  This is exactly the input of the
projection computations on p.9 (`P₊(1/a)P₋ = 0`, etc.). -/
structure OuterSetup (W : StrongBeurlingWeight) (a b : CircleT → ℂ) : Prop where
  /-- The normalization `|a|² + |b|² = 1` of (1.2). -/
  unit : ∀ x : CircleT, a x * starFun a x + b x * starFun b x = 1
  /-- The paper's standing hypothesis `‖b‖_{L∞(𝕋)} < 1` (p.6). -/
  small_b : ∀ x : CircleT, ‖b x‖ < 1
  /-- `a ∈ A_w`. -/
  a_mem : MemAW W a
  /-- `a* ∈ A_w`. -/
  aStar_mem : MemAW W (starFun a)
  /-- `1/a ∈ A_w`. -/
  inv_a_mem : MemAW W (fun x => (a x)⁻¹)
  /-- `1/a* ∈ A_w`. -/
  inv_aStar_mem : MemAW W (fun x => (starFun a x)⁻¹)
  /-- `a` is analytic in the exterior disc. -/
  a_support : ∀ n : ℤ, 0 < n → fourierCoeff a n = 0
  /-- `a*` is analytic in the disc. -/
  aStar_support : ∀ n : ℤ, n < 0 → fourierCoeff (starFun a) n = 0
  /-- `1/a` is analytic in the exterior disc. -/
  inv_a_support : ∀ n : ℤ, 0 < n → fourierCoeff (fun x => (a x)⁻¹) n = 0
  /-- `1/a*` is analytic in the disc. -/
  inv_aStar_support : ∀ n : ℤ, n < 0 → fourierCoeff (fun x => (starFun a x)⁻¹) n = 0

/-- `starFun` is an involution. -/
@[simp] theorem starFun_starFun (f : CircleT → ℂ) : starFun (starFun f) = f := by
  funext x; simp [starFun]

/-- The sum defining `L1wNorm` is nonnegative. -/
theorem L1wNorm_nonneg (W : StrongBeurlingWeight) (c : ℤ → ℂ) : 0 ≤ L1wNorm W c :=
  tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (W.one_le n))

end

end Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup
