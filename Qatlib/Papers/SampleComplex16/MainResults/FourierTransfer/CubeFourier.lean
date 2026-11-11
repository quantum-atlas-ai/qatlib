/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier structure of the PGM kernel

Source: arXiv:1607.00932, *Optimal Quantum Sample Complexity of Learning Algorithms*,
fixed PDF (32 pages), SHA-256 `bd6b6812012f02b7a56114799383f4063208689298783b6cebb77623c2ae5d4e`.
Three source results are formalized here.

* Lemma 20 (pp. 20-22), **lower half**:

> For `β ∈ (0, 1]`, the Fourier coefficients of `f : {0,1}^m → ℝ`, `f(z) = (1 - β|z|/m)^T`,
> satisfy `0 ≤ f̂(S)` for all `S`.

The paper's proof builds the `2^m` real vectors
`u_x = √(1-β)|0,0⟩ + √(β/m) Σ_i |i, x_i⟩`; their `T`-fold tensor powers have Gram entries
`⟨u_x,u_y⟩^T = f(x+y)`.  Positive semidefiniteness of that Gram matrix makes the eigenvalues
`2^m f̂(S)` non-negative.  The matching upper bound of Lemma 20 (the combinatorial Claim 21
sum) is *not* formalized here.

* Claim 18 (p. 19): every character `χ_S` is an eigenvector of `P(x,y) = g(x ⊕ y)` with
  eigenvalue `2^m ĝ(S)`, the diagonalization step of Theorem 17.

* Lemma 11 (p. 14), the two-copy-overlap computation: the pair of one-copy quantum-example
  states `ψ±` has overlap `√(1-ε²)`, so the `T`-copy overlap is `(1-ε²)^{T/2}`.  The
  distribution/learner semantics and the discrimination bound that consume this number are
  not formalized here.

## Encoding

Bits live in `Reg m = Fin m → Bool` with the sign encoding `true ↦ +1`, `false ↦ −1`
(matching the frozen `cubeChar`).  Hence the paper's Hamming weight `|z|` (the number of
`1`-bits) is `cubeWeight z` (the number of `false` coordinates), and the paper's addition on
`F₂^m` is `cubeXnor`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.SampleComplex16.MainResults.FourierTransfer

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier

/-! ## The Boolean-cube group law -/

/-- The paper's addition on `F₂^m` under the sign encoding: pointwise XNOR, which is
multiplication of the corresponding `±1` words. -/
def cubeXnor {m : ℕ} (x y : Reg m) : Reg m := fun i => x i == y i

/-- `cubeXnor x` is an involution of the cube. -/
theorem cubeXnor_invol {m : ℕ} (x y : Reg m) : cubeXnor x (cubeXnor x y) = y := by
  funext i
  cases hx : x i <;> cases hy : y i <;> simp [cubeXnor, hx, hy]

/-- Translation by `x` under `cubeXnor` is a bijection of the cube. -/
def xnorEquiv {m : ℕ} (x : Reg m) : Reg m ≃ Reg m where
  toFun y := cubeXnor x y
  invFun y := cubeXnor x y
  left_inv y := cubeXnor_invol x y
  right_inv y := cubeXnor_invol x y

/-- Reindexing a cube sum by the translation `y ↦ x ⊕ y` leaves it unchanged. -/
theorem sum_xnor_shift {m : ℕ} (x : Reg m) (F : Reg m → ℝ) :
    (∑ y, F (cubeXnor x y)) = ∑ z, F z := by
  classical
  refine Fintype.sum_equiv (xnorEquiv x) (fun y => F (cubeXnor x y)) F ?_
  intro y
  rfl

/-- The paper's kernel `f(z) = (1 - β|z|/m)^T` encoded on the Boolean cube; `cubeWeight`
counts the `false` (that is, `1`-bit) coordinates. -/
def kernel {m : ℕ} (β : ℝ) (T : ℕ) (z : Reg m) : ℝ :=
  (1 - β * (cubeWeight z : ℝ) / m) ^ T

/-! ## Real inner products and tensor powers -/

/-- The real inner product of two real vectors with common finite index type. -/
def realInner {ι : Type*} [Fintype ι] (u v : ι → ℝ) : ℝ := ∑ i, u i * v i

/-- The `T`-fold tensor power of a real vector, indexed by `Fin T → ι`. -/
def tensorPower {ι : Type*} (u : ι → ℝ) (T : ℕ) : (Fin T → ι) → ℝ :=
  fun f => ∏ t, u (f t)

/-- The real inner product of two `T`-fold tensor powers is the `T`-th power of the
one-copy inner product. -/
theorem realInner_tensorPower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (T : ℕ) :
    realInner (tensorPower u T) (tensorPower v T) = (realInner u v) ^ T := by
  classical
  have hterm (f : Fin T → ι) :
      (∏ t, u (f t)) * (∏ t, v (f t)) = ∏ t, (u (f t) * v (f t)) := by
    rw [← Finset.prod_mul_distrib]
  calc
    realInner (tensorPower u T) (tensorPower v T)
        = ∑ f : Fin T → ι, ∏ t, (u (f t) * v (f t)) := by
          unfold realInner tensorPower
          simp_rw [hterm]
    _ = ∏ _t : Fin T, ∑ i, u i * v i := by
          simpa using (Finset.prod_univ_sum (fun _ : Fin T => (Finset.univ : Finset ι))
            (fun _ i => u i * v i)).symm
    _ = (∑ i, u i * v i) ^ T := by
          simp

/-! ## The paper's Gram vector -/

/-- The paper's one-copy Gram vector `u_z`: amplitude `√(1-β)` at the distinguished
coordinate and `√(β/m)` at `(i, z i)` for every coordinate `i`. -/
def gramVector {m : ℕ} (β : ℝ) (z : Reg m) : Option (Fin m × Bool) → ℝ
  | none => Real.sqrt (1 - β)
  | some (i, b) => if z i = b then Real.sqrt (β / m) else 0

/-- The one-copy Gram entry is `1 - β · d_H(x,y)/m`, exactly the paper's computation
`⟨u_x,u_y⟩ = 1 - β + (β/m)(m - |x+y|)`. -/
theorem realInner_gramVector {m : ℕ} (hm : 0 < m) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (x y : Reg m) :
    realInner (gramVector β x) (gramVector β y) = 1 - β * (cubeDist x y : ℝ) / m := by
  classical
  have hmne : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hm)
  have hs0 : Real.sqrt (1 - β) * Real.sqrt (1 - β) = 1 - β :=
    Real.mul_self_sqrt (by linarith)
  have hs1 : Real.sqrt (β / m) * Real.sqrt (β / m) = β / m :=
    Real.mul_self_sqrt (by positivity)
  have hterm (i : Fin m) :
      (∑ b : Bool, gramVector β x (some (i, b)) * gramVector β y (some (i, b))) =
        if x i = y i then β / m else 0 := by
    by_cases h : x i = y i
    · rw [if_pos h, Fintype.sum_bool]
      cases hx : x i <;> cases hy : y i <;> simp_all [gramVector]
    · rw [if_neg h, Fintype.sum_bool]
      cases hx : x i <;> cases hy : y i <;> simp_all [gramVector]
  have hcube : (∑ i : Fin m, (if (x i == y i) then (0 : ℝ) else 1)) =
      (cubeDist x y : ℝ) := by
    unfold cubeDist cubeWeight
    push_cast
    rfl
  have hcount : (∑ i : Fin m, (if x i = y i then (1 : ℝ) else 0)) =
      (m : ℝ) - (cubeDist x y : ℝ) := by
    have hsum : (∑ i : Fin m, ((if x i = y i then (1 : ℝ) else 0) +
        (if (x i == y i) then (0 : ℝ) else 1))) = ∑ i : Fin m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      cases hx : x i <;> cases hy : y i <;> simp
    rw [Finset.sum_add_distrib, hcube] at hsum
    have hcard : (∑ i : Fin m, (1 : ℝ)) = (m : ℝ) := by simp
    rw [hcard] at hsum
    linarith
  have hscale : (∑ i : Fin m, (if x i = y i then β / m else 0)) =
      (β / m) * ∑ i : Fin m, (if x i = y i then (1 : ℝ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i = y i <;> simp [h]
  have hsplit : realInner (gramVector β x) (gramVector β y) =
      gramVector β x none * gramVector β y none +
        ∑ i : Fin m,
          (∑ b : Bool,
            gramVector β x (some (i, b)) * gramVector β y (some (i, b))) := by
    unfold realInner
    rw [Fintype.sum_option, Fintype.sum_prod_type]
  have hnone : gramVector β x none * gramVector β y none = 1 - β := by
    simp only [gramVector, hs0]
  have hcoord : (∑ i : Fin m,
      (∑ b : Bool, gramVector β x (some (i, b)) * gramVector β y (some (i, b)))) =
      ∑ i : Fin m, (if x i = y i then β / m else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hterm i
  rw [hsplit, hnone, hcoord, hscale, hcount]
  field_simp
  ring

/-! ## Bilinear expansion of the Gram form -/

/-- Expanding the real inner product of two finite real combinations of vectors. -/
theorem realInner_sum_mul {ι X : Type*} [Fintype ι] [Fintype X]
    (c : X → ℝ) (g : X → ι → ℝ) :
    realInner (fun j => ∑ x, c x * g x j) (fun j => ∑ y, c y * g y j) =
      ∑ x, ∑ y, (c x * c y) * realInner (g x) (g y) := by
  classical
  calc
    realInner (fun j => ∑ x, c x * g x j) (fun j => ∑ y, c y * g y j)
        = ∑ j, ∑ x, ∑ y, (c x * g x j) * (c y * g y j) := by
          unfold realInner
          simp only [Finset.sum_mul_sum]
    _ = ∑ x, ∑ y, ∑ j, (c x * g x j) * (c y * g y j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, (c x * c y) * ∑ j, g x j * g y j := by
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ x, ∑ y, (c x * c y) * realInner (g x) (g y) := rfl

/-- The real Gram quadratic form of a vector is non-negative. -/
theorem realInner_self_nonneg {ι : Type*} [Fintype ι] (w : ι → ℝ) :
    0 ≤ realInner w w := by
  unfold realInner
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (w j))

/-! ## Lemma 20, non-negativity half -/

/-- **Lemma 20 (non-negativity half).** For `β ∈ [0,1]` and every frequency set `S`, the
uniform Fourier coefficient of `f(z) = (1 - β|z|/m)^T` is non-negative. -/
theorem fourierCoeff_kernel_nonneg {m : ℕ} (hm : 0 < m) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (T : ℕ) (S : Finset (Fin m)) :
    0 ≤ uniformFourierCoeff S (kernel β T) := by
  classical
  set g : Reg m → (Fin T → Option (Fin m × Bool)) → ℝ :=
    fun x => tensorPower (gramVector β x) T with hg
  set χ : Reg m → ℝ := fun x => cubeChar S x with hχ
  have hgramEntry (x y : Reg m) : realInner (g x) (g y) = kernel β T (cubeXnor x y) := by
    rw [hg]
    simp only
    rw [realInner_tensorPower]
    have hb : realInner (gramVector β x) (gramVector β y) =
        1 - β * (cubeDist x y : ℝ) / m :=
      realInner_gramVector hm hβ0 hβ1 x y
    rw [hb]
    rfl
  have hcharXnor (x z : Reg m) : χ x * χ (cubeXnor x z) = χ z := by
    rw [hχ, cubeChar_pair]
    show cubeChar S (cubeXnor x (cubeXnor x z)) = cubeChar S z
    rw [cubeXnor_invol]
  have hrow (x : Reg m) :
      (∑ y, (χ x * χ y) * kernel β T (cubeXnor x y)) = ∑ z, χ z * kernel β T z := by
    have hF : ∀ y : Reg m,
        (χ x * χ y) * kernel β T (cubeXnor x y) =
          (χ x * χ (cubeXnor x (cubeXnor x y))) * kernel β T (cubeXnor x y) := by
      intro y
      rw [cubeXnor_invol]
    rw [show (∑ y, (χ x * χ y) * kernel β T (cubeXnor x y)) =
        ∑ y, (χ x * χ (cubeXnor x (cubeXnor x y))) * kernel β T (cubeXnor x y)
        from Finset.sum_congr rfl (fun y _ => hF y)]
    rw [sum_xnor_shift x (fun z => (χ x * χ (cubeXnor x z)) * kernel β T z)]
    apply Finset.sum_congr rfl
    intro z _
    rw [hcharXnor x z]
  have hdouble :
      (∑ x : Reg m, ∑ y : Reg m, (χ x * χ y) * kernel β T (cubeXnor x y)) =
        (2 : ℝ) ^ m * ∑ z : Reg m, χ z * kernel β T z := by
    simp_rw [hrow]
    calc
      (∑ _x : Reg m, ∑ z, χ z * kernel β T z)
          = (Fintype.card (Reg m) : ℝ) * ∑ z, χ z * kernel β T z := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
      _ = (2 : ℝ) ^ m * ∑ z, χ z * kernel β T z := by
            rw [card_reg]
            push_cast
            ring
  have hquad :
      (∑ x : Reg m, ∑ y : Reg m, (χ x * χ y) * kernel β T (cubeXnor x y)) =
        realInner (fun j => ∑ x, χ x * g x j) (fun j => ∑ y, χ y * g y j) := by
    rw [realInner_sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [hgramEntry x y]
  have hnonneg : 0 ≤ realInner (fun j => ∑ x, χ x * g x j)
      (fun j => ∑ y, χ y * g y j) := realInner_self_nonneg _
  have hcoeff : uniformFourierCoeff S (kernel β T) =
      ((2 : ℝ) ^ m)⁻¹ * ((2 : ℝ) ^ m)⁻¹ *
        (∑ x : Reg m, ∑ y : Reg m, (χ x * χ y) * kernel β T (cubeXnor x y)) := by
    show ((2 : ℝ) ^ m)⁻¹ * ∑ z : Reg m, χ z * kernel β T z = _
    rw [hdouble]
    field_simp
  rw [hcoeff, hquad]
  have hpos : 0 ≤ ((2 : ℝ) ^ m)⁻¹ := by positivity
  exact mul_nonneg (mul_nonneg hpos hpos) hnonneg

/-! ## The character eigenbasis (paper Claim 18) -/

/-- The kernel Gram matrix `P(x,y) = g(x ⊕ y)` attached to a real cube function `g`. -/
def gramMatrix {m : ℕ} (g : Reg m → ℝ) : Matrix (Reg m) (Reg m) ℝ :=
  fun x y => g (cubeXnor x y)

/-- Reindexing a cube sum by the inverse translation `y ↦ x ⊕ y` leaves it unchanged. -/
theorem sum_xnor_shift' {m : ℕ} (x : Reg m) (F : Reg m → ℝ) :
    (∑ y, F y) = ∑ z, F (cubeXnor x z) := by
  classical
  have h := sum_xnor_shift x (fun w => F (cubeXnor x w))
  simpa only [cubeXnor_invol] using h

/-- **Claim 18.** Every character `χ_S` is an eigenvector of `P(x,y) = g(x ⊕ y)`, with
eigenvalue `∑_z χ_S(z) g(z)` — the paper's `2^m ĝ(S)`. -/
theorem gramMatrix_mulVec_cubeChar {m : ℕ} (g : Reg m → ℝ) (S : Finset (Fin m)) (x : Reg m) :
    (gramMatrix g).mulVec (fun y => cubeChar S y) x =
      (∑ z, cubeChar S z * g z) * cubeChar S x := by
  classical
  have hchar (z : Reg m) : cubeChar S (cubeXnor x z) = cubeChar S x * cubeChar S z := by
    show cubeChar S (fun i => x i == z i) = _
    rw [cubeChar_pair]
  have hshift : (∑ y, g (cubeXnor x y) * cubeChar S y) =
      ∑ z, g z * cubeChar S (cubeXnor x z) := by
    have h := sum_xnor_shift' x (fun y => g (cubeXnor x y) * cubeChar S y)
    simpa only [cubeXnor_invol] using h
  rw [Matrix.mulVec, dotProduct]
  change (∑ y, g (cubeXnor x y) * cubeChar S y) = _
  rw [hshift]
  simp_rw [hchar]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The Claim 18 eigenvalue written through the paper's Fourier coefficient: `2^m ĝ(S)`. -/
theorem gramMatrix_mulVec_cubeChar_fourier {m : ℕ} (g : Reg m → ℝ) (S : Finset (Fin m))
    (x : Reg m) :
    (gramMatrix g).mulVec (fun y => cubeChar S y) x =
      ((2 : ℝ) ^ m * uniformFourierCoeff S g) * cubeChar S x := by
  rw [gramMatrix_mulVec_cubeChar]
  congr 1
  unfold uniformFourierCoeff
  field_simp

/-! ## The two-point pair of Lemma 11 -/

/-- One-copy quantum-example state `ψ₊` of the paper's Lemma 11 pair: amplitude `√((1+ε)/2)`
on the `c₁` branch and `√((1-ε)/2)` on the `c₂` branch, i.e. the square roots of the
probabilities `D₊(x, c₁(x)) = (1+ε)/2`, `D₊(x, c₂(x)) = (1-ε)/2`. -/
def agnosticState (ε : ℝ) : Bool → ℝ
  | false => Real.sqrt ((1 + ε) / 2)
  | true => Real.sqrt ((1 - ε) / 2)

/-- The mirrored one-copy state `ψ₋`: the two branch weights are exchanged. -/
def agnosticStateMirror (ε : ℝ) : Bool → ℝ
  | false => Real.sqrt ((1 - ε) / 2)
  | true => Real.sqrt ((1 + ε) / 2)

/-- One-copy overlap of the Lemma 11 pair: `⟨ψ₊|ψ₋⟩ = √(1-ε²)`. -/
theorem realInner_agnosticState {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    realInner (agnosticState ε) (agnosticStateMirror ε) = Real.sqrt (1 - ε ^ 2) := by
  have h1 : 0 ≤ (1 + ε) / 2 := by nlinarith
  have hprod : Real.sqrt ((1 + ε) / 2) * Real.sqrt ((1 - ε) / 2)
      = Real.sqrt ((1 - ε ^ 2) / 4) := by
    rw [← Real.sqrt_mul h1]
    congr 1
    field_simp
    ring
  have hmirror : Real.sqrt ((1 - ε) / 2) * Real.sqrt ((1 + ε) / 2)
      = Real.sqrt ((1 - ε ^ 2) / 4) := by
    rw [mul_comm, hprod]
  have hfour : Real.sqrt ((1 - ε ^ 2) / 4) = Real.sqrt (1 - ε ^ 2) / 2 := by
    rw [Real.sqrt_div (by nlinarith : (0 : ℝ) ≤ 1 - ε ^ 2)]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  unfold realInner
  rw [Fintype.sum_bool]
  simp only [agnosticState, agnosticStateMirror]
  rw [hprod, hmirror, hfour]
  ring

/-- `T`-copy overlap of the Lemma 11 pair: `(√(1-ε²))^T = (1-ε²)^{T/2}`. -/
theorem realInner_agnosticState_tensor {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (T : ℕ) :
    realInner (tensorPower (agnosticState ε) T) (tensorPower (agnosticStateMirror ε) T) =
      (Real.sqrt (1 - ε ^ 2)) ^ T := by
  rw [realInner_tensorPower, realInner_agnosticState hε hε1]
