/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Quantized Markov chain couplings: construction, trace preservation and the fixed point

Temme--Wocjan, *Quantized Markov Chain Couplings that Prepare Qsamples*,
arXiv:2504.02651v2, Quantum 9, 1951 (2025). Fixed source PDF SHA-256
`616a3932dd7120d6c178df5869e910d5891e93396e55f7ccd07c11d3110cabf6`.

The paper quantizes a classical Markov chain coupling into a linear map acting on
quantum states. Source Definition 6 fixes the Heisenberg-picture map

`T*(M) = D^{-1/2} C*(D^{1/2} M D^{1/2}) D^{-1/2}`      (source eq. (24))

built from the *matricization* `C*` of the coupling transition matrix (source
eq. (25)) and the diagonal `D = diag π`. The *quantized coupling* `T` is the
Hilbert--Schmidt dual of `T*`.

This file records the definition of the data (`MarkovChain`, `Coupling`,
`cStar`, `qCoupDual`, `qCoup`, `qsample`) together with

* source (36)--(38): `C*(D) = D`, the classical balance identity;
* source Lemma 7 (30): `T*(I) = I`, so `T` is trace preserving;
* source Lemma 8 (39): `T(|√π⟩⟨√π|) = |√π⟩⟨√π|`.

Everything here is stated over `ℝ`. All data of the construction (`π`, `P`, `C`)
is real valued, and the identities proved are entrywise polynomial identities in
that real data; the square roots only enter through `D^{±1/2}`. Complete positivity
is a genuinely complex-linear property and is treated in `GrandCouplingKraus`
through the explicit Kraus operators of source eq. (55).
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QsampleCoup25.MainResults

open Finset BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {P : Matrix Ω Ω ℝ} {π : Ω → ℝ} {C : Matrix (Ω × Ω) (Ω × Ω) ℝ}

/-! ## Classical data: the Markov chain and the coupling -/

/-- A finite-state Markov chain on `Ω` together with the stationary distribution
`π`: `P` is column stochastic and `π` is a positive probability vector fixed by
`P` (source §1, eq. (1)). -/
structure MarkovChain (P : Matrix Ω Ω ℝ) (π : Ω → ℝ) : Prop where
  /-- Every column of the transition matrix sums to one. -/
  P_column : ∀ x : Ω, ∑ x', P x' x = 1
  /-- The stationary distribution is strictly positive on every state. -/
  pi_pos : ∀ x : Ω, 0 < π x
  /-- The stationary distribution is normalized. -/
  pi_sum : ∑ x, π x = 1
  /-- Stationarity: `P π = π` in column-vector convention. -/
  pi_stationary : ∀ x' : Ω, ∑ x, P x' x * π x = π x'

/-- Source §2, coupling conditions (9)--(13). `C p q` is the transition
probability `c_{p,q}` from the joint state `q = (x,y)` to the joint state
`p = (x',y')`. Both marginals reproduce `P`, a coalesced pair stays together,
and `C` is symmetric under exchanging the two components. -/
structure Coupling (P : Matrix Ω Ω ℝ) (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) : Prop where
  /-- All coupling probabilities are nonnegative. -/
  nonneg : ∀ p q : Ω × Ω, 0 ≤ C p q
  /-- `C` is column stochastic: every column of the coupling matrix sums to one. -/
  column : ∀ q : Ω × Ω, ∑ p, C p q = 1
  /-- Condition (9): the first marginal of `C` is `P`. -/
  marginal_left : ∀ (x' x y : Ω), ∑ y', C (x', y') (x, y) = P x' x
  /-- Condition (10): the second marginal of `C` is `P`. -/
  marginal_right : ∀ (y' x y : Ω), ∑ x', C (x', y') (x, y) = P y' y
  /-- Condition (11): on the diagonal, `C` acts as `P` on the single copy. -/
  meet_diag : ∀ (x' x : Ω), C (x', x') (x, x) = P x' x
  /-- Condition (12): a coalesced pair never splits. -/
  meet_offdiag : ∀ (x' y' x : Ω), x' ≠ y' → C (x', y') (x, x) = 0
  /-- Condition (13): symmetry under exchanging the two components. -/
  swap : ∀ (x' y' x y : Ω), C (x', y') (x, y) = C (y', x') (y, x)

/-! ## The quantized coupling -/

/-- Source eq. (24): the diagonal matrix `D = diag(π_x : x ∈ Ω)`. -/
def Dmat (π : Ω → ℝ) : Matrix Ω Ω ℝ := Matrix.diagonal π

/-- Source eq. (25): the matricization `C*` of the coupling transition matrix,
`C*(M) = ∑ c_{(x',y'),(x,y)} |x'⟩⟨x| M |y⟩⟨y'|`, evaluated entrywise as
`(C* M)_{x'y'} = ∑_{x,y} c_{(x',y'),(x,y)} M_{x,y}`. -/
def cStar (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (M : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ :=
  fun x' y' => ∑ x, ∑ y, C (x', y') (x, y) * M x y

/-- The transposed matricization: it pairs against `C` through the *column* index
`(x,y)`. This is the shape of the Hilbert--Schmidt adjoint of `C*`, because the
pairing `tr(Aᵀ C*(B))` moves the index `(x,y)` into the output slot. -/
def cStarTr (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (M : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ :=
  fun x y => ∑ x', ∑ y', C (x', y') (x, y) * M x' y'

/-- Source eq. (24): the Heisenberg-picture quantized coupling
`T*(M) = D^{-1/2} C*(D^{1/2} M D^{1/2}) D^{-1/2}`. -/
def qCoupDual (π : Ω → ℝ) (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (M : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ :=
  fun x' y' =>
    (Real.sqrt (π x'))⁻¹ * cStar C (fun x y => Real.sqrt (π x) * M x y * Real.sqrt (π y)) x' y' *
      (Real.sqrt (π y'))⁻¹

/-- Source Definition 6: the quantized coupling `T`, defined as the
Hilbert--Schmidt dual of `T*`, that is, the map with `tr((T* A)ᵀ B) = tr(Aᵀ T B)`
for all matrices `A`, `B`. The explicit formula is the one obtained from (24) by
moving the index `(x,y)` of `C` into the output slot. -/
def qCoup (π : Ω → ℝ) (C : Matrix (Ω × Ω) (Ω × Ω) ℝ) (M : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ :=
  fun x y =>
    Real.sqrt (π x) *
      cStarTr C (fun x' y' => (Real.sqrt (π x'))⁻¹ * M x' y' * (Real.sqrt (π y'))⁻¹) x y *
        Real.sqrt (π y)

/-- Source eq. (2) and (60): the qsample projector `|√π⟩⟨√π|`. -/
def qsample (π : Ω → ℝ) : Matrix Ω Ω ℝ := fun x y => Real.sqrt (π x) * Real.sqrt (π y)

/-! ## Elementary square-root facts -/

omit [DecidableEq Ω] in
/-- `√π_x · √π_x = π_x`, valid because the stationary masses are nonnegative. -/
lemma sqrt_mul_self (hmc : MarkovChain P π) (x : Ω) :
    Real.sqrt (π x) * Real.sqrt (π x) = π x :=
  Real.mul_self_sqrt (le_of_lt (hmc.pi_pos x))

omit [DecidableEq Ω] in
/-- `√π_x` is nonzero because `π_x > 0`. -/
lemma sqrt_ne_zero (hmc : MarkovChain P π) (x : Ω) : Real.sqrt (π x) ≠ 0 :=
  (Real.sqrt_pos.2 (hmc.pi_pos x)).ne'

/-- The diagonal rescaling of the identity is `D = diag π`, i.e.
`D^{1/2} I D^{1/2} = D`. -/
lemma halfConj_one (hmc : MarkovChain P π) :
    (fun x y => Real.sqrt (π x) * (1 : Matrix Ω Ω ℝ) x y * Real.sqrt (π y)) = Dmat π := by
  funext x y
  by_cases h : x = y
  · subst h
    simp [Dmat, sqrt_mul_self hmc]
  · simp [Dmat, h]

omit [DecidableEq Ω] in
/-- Cancelling the two `D^{-1/2}` factors against one factor of `π`: this is the
elementary rescaling step used both in Lemma 7 and in the trace computation. -/
lemma inv_sqrt_cancel (hmc : MarkovChain P π) (x : Ω) (a : ℝ) :
    (Real.sqrt (π x))⁻¹ * a * (Real.sqrt (π x))⁻¹ * π x = a := by
  have hp : Real.sqrt (π x) ≠ 0 := sqrt_ne_zero hmc x
  have hsq : Real.sqrt (π x) * Real.sqrt (π x) = π x := sqrt_mul_self hmc x
  have hstep : (Real.sqrt (π x))⁻¹ * (Real.sqrt (π x) * Real.sqrt (π x)) *
      (Real.sqrt (π x))⁻¹ = 1 := by
    rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul, mul_inv_cancel₀ hp]
  calc (Real.sqrt (π x))⁻¹ * a * (Real.sqrt (π x))⁻¹ * π x
      = (Real.sqrt (π x))⁻¹ * a * (Real.sqrt (π x))⁻¹ *
          (Real.sqrt (π x) * Real.sqrt (π x)) := by rw [hsq]
    _ = a * ((Real.sqrt (π x))⁻¹ * (Real.sqrt (π x) * Real.sqrt (π x)) *
          (Real.sqrt (π x))⁻¹) := by ring
    _ = a * 1 := by rw [hstep]
    _ = a := by ring

/-! ## Source (36)--(38): `C*(D) = D` -/

/-- Source (36)--(38): the coupling conditions and stationarity imply
`C*(D) = D`. This is the classical balance identity that makes the quantized
coupling trace preserving. -/
theorem cStar_Dmat (hmc : MarkovChain P π) (hc : Coupling P C) :
    cStar C (Dmat π) = Dmat π := by
  funext x' y'
  have hinner : (∑ x, ∑ y, C (x', y') (x, y) * Dmat π x y)
      = ∑ x, C (x', y') (x, x) * π x := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · simp [Dmat]
    · intro y _ hne
      have hxy : x ≠ y := Ne.symm hne
      simp [Dmat, hxy]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [cStar, hinner]
  rcases eq_or_ne x' y' with h | h
  · subst h
    have hsum : (∑ x, C (x', x') (x, x) * π x) = π x' := by
      rw [Finset.sum_congr rfl (fun x _ => by rw [hc.meet_diag])]
      exact hmc.pi_stationary x'
    rw [hsum]
    simp [Dmat]
  · have hzero : ∀ x, C (x', y') (x, x) * π x = 0 := fun x => by
      rw [hc.meet_offdiag x' y' x h, zero_mul]
    rw [Finset.sum_congr rfl (fun x _ => hzero x), Finset.sum_const_zero]
    simp [Dmat, h]

/-! ## Source Lemma 7: trace preservation -/

/-- Source Lemma 7 (30): `T*(I) = I`, that is, the quantized coupling `T` is
trace preserving. -/
theorem qCoupDual_one (hmc : MarkovChain P π) (hc : Coupling P C) :
    qCoupDual π C 1 = 1 := by
  have hhalf : (fun x y => Real.sqrt (π x) * (1 : Matrix Ω Ω ℝ) x y * Real.sqrt (π y))
      = fun x y => Dmat π x y := halfConj_one hmc
  funext x' y'
  have hc' : cStar C (fun x y => Real.sqrt (π x) * (1 : Matrix Ω Ω ℝ) x y * Real.sqrt (π y)) x' y'
      = Dmat π x' y' := by
    rw [hhalf]
    exact congrFun (congrFun (cStar_Dmat (P := P) (π := π) (C := C) hmc hc) x') y'
  have hval : qCoupDual π C 1 x' y'
      = (Real.sqrt (π x'))⁻¹ * Dmat π x' y' * (Real.sqrt (π y'))⁻¹ := by
    simp only [qCoupDual, hc']
  rw [hval]
  by_cases h : x' = y'
  · subst h
    simp only [Dmat, Matrix.diagonal_apply, if_true, Matrix.one_apply]
    rw [← inv_sqrt_cancel hmc x' 1]
    ring
  · have hne : Real.sqrt (π x') ≠ 0 := sqrt_ne_zero hmc x'
    have hne' : Real.sqrt (π y') ≠ 0 := sqrt_ne_zero hmc y'
    simp [Dmat, h]

omit [DecidableEq Ω] in
/-- Source Lemma 7, Schrödinger picture: the quantized coupling preserves the
trace of every matrix. Proved by evaluating `tr T(ρ)` on the diagonal, where the
coupling conditions force only the coalesced entries `c_{(p,p),(x,x)} = P_{p,x}`
to contribute. -/
theorem trace_qCoup (hmc : MarkovChain P π) (hc : Coupling P C) (ρ : Matrix Ω Ω ℝ) :
    (qCoup π C ρ).trace = ρ.trace := by
  have hdiag : ∀ x : Ω, qCoup π C ρ x x = Real.sqrt (π x) *
      (∑ p, P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹)) * Real.sqrt (π x) := by
    intro x
    have hinner : (∑ p, ∑ q, C (p, q) (x, x) *
          ((Real.sqrt (π p))⁻¹ * ρ p q * (Real.sqrt (π q))⁻¹))
        = ∑ p, P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_eq_single p]
      · rw [hc.meet_diag]
      · intro q _ hne
        have hpq : p ≠ q := Ne.symm hne
        rw [hc.meet_offdiag p q x hpq, zero_mul]
      · intro hp
        exact absurd (Finset.mem_univ p) hp
    simp only [qCoup, cStarTr, hinner]
  have hx : ∀ x : Ω, qCoup π C ρ x x
      = ∑ p, (P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹)) * π x := by
    intro x
    rw [hdiag x]
    rw [show Real.sqrt (π x) *
          (∑ p, P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹)) * Real.sqrt (π x)
        = (∑ p, P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹)) *
            (Real.sqrt (π x) * Real.sqrt (π x)) from by ring]
    rw [sqrt_mul_self hmc x, Finset.sum_mul]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  calc (∑ x, qCoup π C ρ x x)
      = ∑ x, ∑ p, (P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹)) * π x :=
        Finset.sum_congr rfl fun x _ => hx x
    _ = ∑ p, ∑ x, (P p x * ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹)) * π x :=
        Finset.sum_comm
    _ = ∑ p, ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹) * (∑ x, P p x * π x) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = ∑ p, ((Real.sqrt (π p))⁻¹ * ρ p p * (Real.sqrt (π p))⁻¹) * π p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [hmc.pi_stationary p]
    _ = ∑ p, ρ p p := by
        refine Finset.sum_congr rfl fun p _ => ?_
        exact inv_sqrt_cancel hmc p (ρ p p)
    _ = ρ.trace := by
        rw [Matrix.trace]
        simp only [Matrix.diag_apply]

/-! ## Source Lemma 8: the qsample is a fixed point -/

omit [DecidableEq Ω] in
/-- Source Lemma 8 (39): the qsample `|√π⟩⟨√π|` is a fixed point of the
quantized coupling `T`. -/
theorem qCoup_qsample (hmc : MarkovChain P π) (hc : Coupling P C) :
    qCoup π C (qsample π) = qsample π := by
  funext x y
  have hinner : ∀ p q : Ω,
      (Real.sqrt (π p))⁻¹ * qsample π p q * (Real.sqrt (π q))⁻¹ = 1 := by
    intro p q
    have hp : Real.sqrt (π p) ≠ 0 := sqrt_ne_zero hmc p
    have hq : Real.sqrt (π q) ≠ 0 := sqrt_ne_zero hmc q
    rw [show qsample π p q = Real.sqrt (π p) * Real.sqrt (π q) from rfl]
    rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul, mul_inv_cancel₀ hq]
  have hsum : cStarTr C (fun p q => (Real.sqrt (π p))⁻¹ * qsample π p q * (Real.sqrt (π q))⁻¹) x y
      = ∑ p, ∑ q, C (p, q) (x, y) := by
    simp only [cStarTr, hinner, mul_one]
  have hcol : (∑ p, ∑ q, C (p, q) (x, y)) = 1 := by
    have h1 : (∑ p : Ω, ∑ q : Ω, C (p, q) (x, y))
        = ∑ pq ∈ (Finset.univ : Finset Ω) ×ˢ (Finset.univ : Finset Ω), C pq (x, y) :=
      (Finset.sum_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ω)
        (fun pq : Ω × Ω => C pq (x, y))).symm
    rw [h1, Finset.univ_product_univ]
    exact hc.column (x, y)
  rw [qCoup, hsum, hcol, mul_one]
  rfl

end Qatlib.Papers.QsampleCoup25.MainResults
