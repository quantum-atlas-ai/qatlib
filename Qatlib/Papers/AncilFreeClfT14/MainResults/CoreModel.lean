/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# AncilFreeClfT14 — shared model

Objects, structures and notation shared by the paper-layer statements of
N. J. Ross and P. Selinger, *Optimal ancilla-free Clifford+T approximation of
z-rotations*, arXiv:1403.2975v3 (15 Jun 2016).

The paper works with the rings of algebraic integers `ℤ[√2]`, `ℤ[ω]`
(`ω = e^{iπ/4}`), the dyadic rings `𝔻`, `𝔻[√2]`, `𝔻[ω]`, the two
conjugations `†` (complex conjugation) and `•` (2-conjugation, `√2 ↦ -√2`),
the one- and two-dimensional (scaled) grid problems, grid operators, ellipses and
the `(b, β, z, ζ, e, ε)` parametrisation of elliptic states from Appendix A.

All definitions are stated in the paper's own coordinates.  Rather than
building the rings as `Subring`s of `ℂ` (whose element predicates would make
the algebraic statements of §3–§6 opaque), we represent `ℤ[√2]` and `ℤ[ω]`
by their integer coefficient vectors; the map `toComplex` (resp. `toReal`)
embeds them into `ℂ` (resp. `ℝ`).  This mirrors Definition 3.1 literally and
keeps the parity arguments of Lemma 5.5 computable.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Real
open Complex

namespace Qatlib.Papers.AncilFreeClfT14.MainResults

/-! ## §0. Basic constants (Definition 3.1, Definition 3.5) -/

/-- `ω = e^{iπ/4} = (1 + i)/√2` (Definition 3.1). -/
noncomputable def omega : ℂ := (1 + Complex.I) / (Real.sqrt 2 : ℂ)

/-- `λ = 1 + √2` (Definition 3.5). -/
noncomputable def lam : ℝ := 1 + Real.sqrt 2

/-- `δ = 1 + ω` (Definition 3.5). -/
noncomputable def deltaC : ℂ := 1 + omega

/-- `λ = 1+√2` is positive (Definition 3.5). -/
theorem lam_pos : 0 < lam := by
  unfold lam
  positivity

/-- `λ = 1+√2` is nonzero (Definition 3.5). -/
theorem lam_ne_zero : lam ≠ 0 := ne_of_gt lam_pos

/-- `ω² = i`; used throughout §5. -/
theorem omega_sq : omega ^ 2 = Complex.I := by
  have h2 : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hexp : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    rw [pow_two]
    linear_combination hI
  unfold omega
  rw [div_pow, hexp, pow_two, h2]
  ring

/-- `ω³ = ω · i`. -/
theorem omega_cube : omega ^ 3 = omega * Complex.I := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, omega_sq]
  ring

/-- `ω - ω³ = √2`; this is the key identity behind Lemma 5.5. -/
theorem omega_sub_omega_cube : omega - omega ^ 3 = (Real.sqrt 2 : ℂ) := by
  have h2 : ((Real.sqrt 2 : ℂ)) * ((Real.sqrt 2 : ℂ)) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have hne : ((Real.sqrt 2 : ℂ)) ≠ 0 := by
    simpa using (show (Real.sqrt 2 : ℝ) ≠ 0 by positivity)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [omega_cube]
  unfold omega
  have hkey : ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) -
      ((1 + Complex.I) / (Real.sqrt 2 : ℂ)) * Complex.I
      = (2 : ℂ) / (Real.sqrt 2 : ℂ) := by
    field_simp [hne]
    linear_combination (-1 : ℂ) * hI
  have hfinal : (2 : ℂ) / (Real.sqrt 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    field_simp [hne]
    linear_combination (-1 : ℂ) * h2
  rw [hkey, hfinal]

/-! ## §1. `ℤ[√2]` -/

/-- An element `a + b√2` of `ℤ[√2]`, represented by its integer coordinates. -/
structure Zsqrt2 where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

namespace Zsqrt2

/-- The real value `a + b√2`. -/
def toReal (x : Zsqrt2) : ℝ := (x.a : ℝ) + (x.b : ℝ) * Real.sqrt 2

/-- The complex value `a + b√2`. -/
def toComplex (x : Zsqrt2) : ℂ := (x.a : ℂ) + (x.b : ℂ) * (Real.sqrt 2 : ℂ)

/-- 2-conjugation `(a + b√2)• = a - b√2` (Definition 3.2). -/
def bullet (x : Zsqrt2) : Zsqrt2 := ⟨x.a, -x.b⟩

/-- `†` is the identity on the real ring `ℤ[√2]`. -/
def dagger (x : Zsqrt2) : Zsqrt2 := x

/-- The `toReal_bullet` result for the AncilFreeClfT14 paper model. -/
@[simp] theorem toReal_bullet (x : Zsqrt2) :
    x.bullet.toReal = (x.a : ℝ) - (x.b : ℝ) * Real.sqrt 2 := by
  simp [bullet, toReal]
  ring

/-- The `toComplex_eq` result for the AncilFreeClfT14 paper model. -/
@[simp] theorem toComplex_eq (x : Zsqrt2) :
    x.toComplex = (x.toReal : ℂ) := by
  simp [toComplex, toReal]

end Zsqrt2

/-! ## §2. `ℤ[ω]` -/

/-- An element `aω³ + bω² + cω + d` of `ℤ[ω]` (Definition 3.1). -/
structure Zomega where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq, Repr

namespace Zomega

/-- The complex value `aω³ + bω² + cω + d`. -/
def toComplex (u : Zomega) : ℂ :=
  (u.a : ℂ) * omega ^ 3 + (u.b : ℂ) * omega ^ 2 + (u.c : ℂ) * omega + (u.d : ℂ)

/-- 2-conjugation `(aω³+bω²+cω+d)• = -aω³ + bω² - cω + d` (Definition 3.2). -/
def bullet (u : Zomega) : Zomega := ⟨-u.a, u.b, -u.c, u.d⟩

/-- Complex conjugation `(aω³+bω²+cω+d)† = -cω³ - bω² - aω + d` (Definition 3.2). -/
def dagger (u : Zomega) : Zomega := ⟨-u.c, -u.b, -u.a, u.d⟩

def zero : Zomega := ⟨0, 0, 0, 0⟩

def one : Zomega := ⟨0, 0, 0, 1⟩

/-- The `toComplex_zero` result for the AncilFreeClfT14 paper model. -/
@[simp] theorem toComplex_zero : zero.toComplex = 0 := by
  simp [zero, toComplex]

/-- The `toComplex_one` result for the AncilFreeClfT14 paper model. -/
@[simp] theorem toComplex_one : one.toComplex = 1 := by
  simp [one, toComplex]

end Zomega

/-! ## §3. Dyadic rings and scaled lattices (Definition 3.1, Definition 3.4) -/

/-- `𝔻 = ℤ[1/2]`, the dyadic rationals. -/
def Dyadic : Set ℝ := {x | ∃ a : ℤ, ∃ k : ℕ, x = (a : ℝ) / 2 ^ k}

/-- `𝔻[√2]` as a subset of `ℂ`. -/
def Dsqrt2 : Set ℂ :=
  {z | ∃ x : Zsqrt2, ∃ k : ℕ, z = x.toComplex / (2 : ℂ) ^ k}

/-- `𝔻[ω]` as a subset of `ℂ`. -/
def Domega : Set ℂ :=
  {z | ∃ u : Zomega, ∃ k : ℕ, z = u.toComplex / (2 : ℂ) ^ k}

/-- The scaled lattice `1/√2^k · ℤ[ω]` (Definition 3.4 / 5.20). -/
def scaledZomega (k : ℕ) : Set ℂ :=
  Set.range (fun u : Zomega => u.toComplex / (Real.sqrt 2 : ℂ) ^ k)

/-- `ℤ[ω]` as a subset of `ℂ`. -/
def ZomegaSet : Set ℂ := Set.range Zomega.toComplex

/-- `ℤ[√2]` as a subset of `ℂ`. -/
def Zsqrt2Set : Set ℂ := Set.range Zsqrt2.toComplex

/-! ## §4. Grid problems (Definition 4.1, 4.3, 5.1, 5.3, 5.20) -/

/-- Membership in the one-dimensional grid problem (3). -/
def OneDimGridProblem (A B : Set ℝ) (α : Zsqrt2) : Prop :=
  α.toReal ∈ A ∧ α.bullet.toReal ∈ B

/-- Membership in the two-dimensional grid problem (5). -/
def TwoDimGridProblem (A B : Set ℂ) (u : Zomega) : Prop :=
  u.toComplex ∈ A ∧ u.bullet.toComplex ∈ B

/-- Membership in the two-dimensional scaled grid problem for fixed `k`
(Definition 5.20). -/
def ScaledGridProblem (k : ℕ) (A B : Set ℂ) (u : Zomega) : Prop :=
  u.toComplex / (Real.sqrt 2 : ℂ) ^ k ∈ A ∧
    u.bullet.toComplex / (Real.sqrt 2 : ℂ) ^ k ∈ B

/-- The real grid `grid(B) = {α ∈ ℤ[√2] | α• ∈ B}` (Definition 4.1). -/
def realGrid (B : Set ℝ) : Set Zsqrt2 := {α | α.bullet.toReal ∈ B}

/-- The complex grid `Grid(B) = {u ∈ ℤ[ω] | u• ∈ B}` (Definition 5.1). -/
def complexGrid (B : Set ℂ) : Set Zomega := {u | u.bullet.toComplex ∈ B}

/-! ## §5. Grid operators (Definition 5.10, Lemma 5.11, Remark 5.12) -/

/-- A real `2 × 2` matrix. -/
structure Mat2 where
  m11 : ℝ
  m12 : ℝ
  m21 : ℝ
  m22 : ℝ

namespace Mat2

/-- Matrix multiplication. -/
def mul (A B : Mat2) : Mat2 :=
  ⟨A.m11 * B.m11 + A.m12 * B.m21, A.m11 * B.m12 + A.m12 * B.m22,
   A.m21 * B.m11 + A.m22 * B.m21, A.m21 * B.m12 + A.m22 * B.m22⟩

/-- The determinant. -/
def det (A : Mat2) : ℝ := A.m11 * A.m22 - A.m12 * A.m21

/-- Action of a `2 × 2` matrix on `ℝ²`, written on `ℂ`. -/
def apply (A : Mat2) (z : ℂ) : ℂ :=
  ((A.m11 * z.re + A.m12 * z.im : ℝ) : ℂ) +
    Complex.I * ((A.m21 * z.re + A.m22 * z.im : ℝ) : ℂ)

/-- The identity matrix. -/
def one : Mat2 := ⟨1, 0, 0, 1⟩

end Mat2

/-- A grid operator (Definition 5.10): a real linear operator preserving `ℤ[ω]`. -/
structure GridOperator where
  mat : Mat2
  mapsZomega : ∀ u : Zomega, ∃ v : Zomega, v.toComplex = mat.apply u.toComplex

/-- A special grid operator: determinant `±1` (Definition 5.10). -/
def GridOperator.special (G : GridOperator) : Prop := G.mat.det = 1 ∨ G.mat.det = -1

/-- The image `G(A) = {G u | u ∈ A}`. -/
def GridOperator.image (G : GridOperator) (A : Set ℂ) : Set ℂ :=
  {z | ∃ u ∈ A, z = G.mat.apply u}

/-! ## §6. Ellipses, bounding boxes, uprightness (Definition 5.7, 5.15) -/

/-- Positive definiteness of the symmetric matrix `[[a,b],[b,d]]`. -/
def IsPosDef2 (a b d : ℝ) : Prop := 0 < a ∧ 0 < a * d - b * b

/-- An ellipse `{u | (u-p)† D (u-p) ≤ 1}` (Definition 5.15). -/
structure Ellipse where
  a : ℝ
  b : ℝ
  d : ℝ
  px : ℝ
  py : ℝ
  posDef : IsPosDef2 a b d

/-- Membership in the ellipse. -/
def Ellipse.member (E : Ellipse) (u : ℂ) : Prop :=
  E.a * (u.re - E.px) ^ 2 + 2 * E.b * (u.re - E.px) * (u.im - E.py) +
    E.d * (u.im - E.py) ^ 2 ≤ 1

/-- The point set of an ellipse. -/
def Ellipse.points (E : Ellipse) : Set ℂ := {u | E.member u}

/-- The area of a planar set (Lebesgue measure of `ℂ ≃ ℝ²`). -/
def area (A : Set ℂ) : ℝ := (MeasureTheory.volume A).toReal

/-- The axis-aligned bounding box of a planar set (Definition 5.7). -/
def bbox (A : Set ℂ) : Set ℂ :=
  {z | z.re ∈ Set.Icc (sInf (Complex.re '' A)) (sSup (Complex.re '' A)) ∧
       z.im ∈ Set.Icc (sInf (Complex.im '' A)) (sSup (Complex.im '' A))}

/-- Uprightness `up(A) = area(A)/area(BBox(A))` (Definition 5.7). -/
def uprightness (A : Set ℂ) : ℝ := area A / area (bbox A)

/-- `A` is `M`-upright (Definition 5.7). -/
def MUpright (A : Set ℂ) (M : ℝ) : Prop := M ≤ uprightness A

/-! ## §7. States and their actions (Definition A.1, A.3, A.7) -/

/-- A state `(D, Δ)` in the paper's parametrisation (34):
`D = [[e λ^{-z}, b], [b, e λ^z]]`, `Δ = [[ε λ^{-ζ}, β], [β, ε λ^ζ]]`,
with `e² = b²+1` and `ε² = β²+1`. -/
structure State where
  b : ℝ
  beta : ℝ
  z : ℝ
  zeta : ℝ
  e : ℝ
  eps : ℝ
  e_pos : 0 < e
  eps_pos : 0 < eps
  e_sq : e ^ 2 = b ^ 2 + 1
  eps_sq : eps ^ 2 = beta ^ 2 + 1

namespace State

/-- The skew `Skew(D,Δ) = b² + β²` (Definition A.1). -/
def skew (S : State) : ℝ := S.b ^ 2 + S.beta ^ 2

/-- The bias `Bias(D,Δ) = ζ - z` (Definition A.1). -/
def bias (S : State) : ℝ := S.zeta - S.z

/-- The matrix `D` of the state. -/
def matD (S : State) : Mat2 :=
  ⟨S.e * lam ^ (-S.z), S.b, S.b, S.e * lam ^ S.z⟩

/-- The matrix `Δ` of the state. -/
def matDelta (S : State) : Mat2 :=
  ⟨S.eps * lam ^ (-S.zeta), S.beta, S.beta, S.eps * lam ^ S.zeta⟩

/-- The `k`-shift `(D,Δ) · Shift^k = (σ^k D σ^k, τ^k Δ τ^k)` written on the
parameters (Definition A.7). -/
def shift (S : State) (k : ℤ) : State where
  b := S.b
  beta := S.beta
  z := S.z - (k : ℝ)
  zeta := S.zeta + (k : ℝ)
  e := S.e
  eps := S.eps
  e_pos := S.e_pos
  eps_pos := S.eps_pos
  e_sq := S.e_sq
  eps_sq := S.eps_sq

end State

/-! ## §8. The specific operators of Figure 6 -/

/-- `R = (1/√2) [[1,-1],[1,1]]`. -/
def opR : Mat2 := ⟨1 / Real.sqrt 2, -(1 / Real.sqrt 2), 1 / Real.sqrt 2, 1 / Real.sqrt 2⟩

/-- `A = [[1,-2],[0,1]]`. -/
def opA : Mat2 := ⟨1, -2, 0, 1⟩

/-- `B = [[1,√2],[0,1]]`. -/
def opB : Mat2 := ⟨1, Real.sqrt 2, 0, 1⟩

/-- `K = (1/√2) [[-λ^{-1},-1],[λ,1]]`. -/
def opK : Mat2 :=
  ⟨-(1 / Real.sqrt 2) * lam⁻¹, -(1 / Real.sqrt 2), (1 / Real.sqrt 2) * lam, 1 / Real.sqrt 2⟩

/-- `X = [[0,1],[1,0]]`. -/
def opX : Mat2 := ⟨0, 1, 1, 0⟩

/-- `Z = [[1,0],[0,-1]]`. -/
def opZ : Mat2 := ⟨1, 0, 0, -1⟩

/-! ## §9. Synthesised unitaries and T-counts (§7, §9) -/

/-- A single-qubit operator of the form (12) `U = [[u, -t†],[t, u†]]`. -/
structure UTForm where
  u : ℂ
  t : ℂ

/-- The matrix (12), as a complex `2 × 2` matrix. -/
def UTForm.mat (U : UTForm) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![U.u, -starRingEnd ℂ U.t; U.t, starRingEnd ℂ U.u]

/-- A single-qubit operator of the form (29) `U = [[u, -t†ω⁻¹],[t, u†ω⁻¹]]`. -/
structure UTOmegaForm where
  u : ℂ
  t : ℂ

/-- The matrix (29). -/
def UTOmegaForm.mat (U : UTOmegaForm) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![U.u, -starRingEnd ℂ U.t * omega⁻¹; U.t, starRingEnd ℂ U.u * omega⁻¹]

/-- `R_z(θ) = diag(e^{-iθ/2}, e^{iθ/2})`. -/
def Rz (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Complex.exp (-(θ : ℂ) * Complex.I / 2)), 0; 0, Complex.exp ((θ : ℂ) * Complex.I / 2)]

/-- The unit disk in the plane. -/
def unitDisk : Set ℂ := {u | Complex.normSq u ≤ 1}

/-- The `ε`-region `R_ε = {u ∈ D | u·z ≥ 1 - ε²/2}` of (14). -/
def epsRegion (θ ε : ℝ) : Set ℂ :=
  {u | Complex.normSq u ≤ 1 ∧
       u.re * (Real.cos (-(θ / 2))) + u.im * (Real.sin (-(θ / 2))) ≥ 1 - ε ^ 2 / 2}

/-- The T-count of a candidate operator, abstractly: we only need the value as
an integer for statements, and the paper computes it via exact synthesis. -/
def tCount (U : UTForm) : ℕ := 0

/-- A Clifford+T operator (single qubit), abstractly represented by a unitary
`2 × 2` complex matrix together with its determinant exponent `k`. -/
structure CliffordTOp where
  mat : Matrix (Fin 2) (Fin 2) ℂ
  detExp : ℤ

/-! ## §10. Matrix norms, form (11), and approximate synthesis (Definition 7.1) -/

/-- Squared Euclidean norm of a length-`2` complex vector. -/
def vecNormSq (v : Fin 2 → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- Squared operator norm (Euclidean) of a `2 × 2` complex matrix, as the
supremum of `‖A v‖²` over unit vectors. -/
def opNormSq (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ v : Fin 2 → ℂ, vecNormSq v = 1 ∧ r = vecNormSq (A.mulVec v)}

/-- The operator norm `‖A‖`. -/
def opNorm (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := Real.sqrt (opNormSq A)

/-- `‖R_z(θ) − U‖ ≤ ε`: the approximation condition (10) of Definition 7.1. -/
def ApproxSynth (θ ε : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  opNorm (Rz θ - U) ≤ ε

/-- The general form (11) `U = [[u, -t†ω^ℓ],[t, u†ω^ℓ]]`. -/
structure UTGeneralForm where
  u : ℂ
  t : ℂ
  l : ℤ

/-- The matrix of (11). -/
def UTGeneralForm.mat (U : UTGeneralForm) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![U.u, -starRingEnd ℂ U.t * omega ^ U.l; U.t, starRingEnd ℂ U.u * omega ^ U.l]

/-- Unitarity of a form-(12) operator. -/
def IsUnitaryUT (U : UTForm) : Prop :=
  U.mat * Matrix.conjTranspose U.mat = 1

/-- Unitarity of a form-(11) operator. -/
def IsUnitaryUTG (U : UTGeneralForm) : Prop :=
  U.mat * Matrix.conjTranspose U.mat = 1

/-- `k` is the least denominator exponent of `u ∈ D[ω]`: `u ∈ (1/√2^k)ℤ[ω]` but
`u ∉ (1/√2^j)ℤ[ω]` for `j < k`. -/
def LeastDenomExp (u : ℂ) (k : ℕ) : Prop :=
  u ∈ scaledZomega k ∧ ∀ j : ℕ, j < k → u ∉ scaledZomega j

/-- `1 − e^{iπ/8}`, whose norm is the threshold of Lemma 7.2 and Lemma 9.6. -/
noncomputable def threshold7 : ℝ :=
  ‖(1 : ℂ) - Complex.exp (Complex.I * ((Real.pi / 8 : ℝ) : ℂ))‖

end Qatlib.Papers.AncilFreeClfT14.MainResults
