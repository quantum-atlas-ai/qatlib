/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LiftingWu25.ProtocolSetup.HybridModel
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# WitnessBounds — the witness matrix of Theorem 3.1

Wu--Yang--Yao, fixed arXiv:2511.17227v2, Section 3: Lemma 3.2.

Theorem 3.1 applies the generalized discrepancy method (Theorem 2.6) with the
witness matrix `Ψ(u,v) = 2^{|J|}/|R| · ψ(G^J(x,y))`, where `ψ` is the dual
polynomial of `f` certifying `deg_{1/3}(f) ≥ d` (Lemma 2.1). Lemma 3.2 bounds the
`ℓ₁` norm of `Ψ` by `1.01` and its inner product with `F = f ∘ G^J` from below by
`0.33`.

The two bounds are driven by the density of `G^J(X,Y)`: by Lemma 2.9 the atom
masses lie in `[(1-η)/2^{|J|}, (1+η)/2^{|J|}]` with `η = n⁻²`. We keep both sides
of that bracket as explicit hypotheses; the inner-product bound then follows from
`outDist z ≥ (1-η)/2^{|J|}` on positive terms and `outDist z ≤ (1+η)/2^{|J|}` on
negative ones, which is the rigorous form of the paper's "`≥ 0.99⟨f,ψ⟩`".

Boundary: only the two witness estimates are proved. Lemma 3.3 (spectral norm)
and the trace estimate Proposition 3.4 are in `GadgetTrace`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LiftingWu25.DenseLift

open Finset
open Qatlib.Papers.LiftingWu25.ProtocolSetup

variable {ι U V : Type*}

/-- `|R| = |U|·|V|`, the number of input pairs in the rectangle `R = U × V`. -/
def rectCard (U V : Type*) [Fintype U] [Fintype V] : ℝ :=
  (Fintype.card U : ℝ) * (Fintype.card V : ℝ)

/-- The number of input pairs of the rectangle on which the gadget output is `z`. -/
def outCount [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype V] (J : Finset ι)
    (G : U × V → J → Bool) (z : J → Bool) : ℕ :=
  (Finset.univ.filter (fun p : U × V => G p = z)).card

/-- The distribution of `G^J(X,Y)` when `(X,Y)` is uniform on the rectangle. -/
def outDist [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype V] (J : Finset ι)
    (G : U × V → J → Bool) (z : J → Bool) : ℝ :=
  (outCount J G z : ℝ) / rectCard U V

/-- The witness matrix `Ψ(u,v) = 2^{|J|}/|R| · ψ(G^J(x,y))` of Theorem 3.1. -/
def witness [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype V] (J : Finset ι)
    (ψ : (J → Bool) → ℝ) (G : U × V → J → Bool) (p : U × V) : ℝ :=
  (2 : ℝ) ^ J.card * ψ (G p) / rectCard U V

/-- The gadget output on a rectangle, as the paper's `G^J(x,y)` with `x = x(u)` and
`y = y(v)`. -/
def gadgetOut {b : ℕ} (J : Finset ι) (x : U → ι → Lambda b) (y : V → ι → Lambda b) :
    U × V → J → Bool :=
  fun p i => gadget (x p.1 i) (y p.2 i)

/-- Splitting the rectangle sum by the gadget output: the `ℓ₁` norm of `Ψ` is the
`2^{|J|}`-rescaled `ℓ₁` norm of `ψ` against the output distribution. -/
theorem sum_abs_witness [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype V]
    (J : Finset ι) (ψ : (J → Bool) → ℝ) (G : U × V → J → Bool)
    (hU : 0 < Fintype.card U) (hV : 0 < Fintype.card V) :
    (∑ p : U × V, |witness J ψ G p|)
      = (2 : ℝ) ^ J.card * ∑ z : J → Bool, |ψ z| * outDist J G z := by
  have hCpos : 0 < rectCard U V := by
    unfold rectCard
    exact mul_pos (by exact_mod_cast hU) (by exact_mod_cast hV)
  have hP : (0 : ℝ) ≤ (2 : ℝ) ^ J.card := by positivity
  have hterm : ∀ p : U × V,
      |witness J ψ G p| = (2 : ℝ) ^ J.card * |ψ (G p)| / rectCard U V := by
    intro p
    rw [witness, abs_div, abs_mul, abs_of_nonneg hP, abs_of_pos hCpos]
  have hsplit : (∑ p : U × V, |ψ (G p)|)
      = ∑ z : J → Bool, (outCount J G z : ℝ) * |ψ z| := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (U × V)))
      (t := (Finset.univ : Finset (J → Bool))) (g := G)
      (fun p _ => Finset.mem_univ (G p)) (fun p => |ψ (G p)|)]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hconst : (∑ p ∈ Finset.univ.filter (fun p : U × V => G p = z), |ψ (G p)|)
        = ∑ _p ∈ Finset.univ.filter (fun p : U × V => G p = z), |ψ z| := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    rw [hconst, Finset.sum_const, outCount]
    simp
  calc ∑ p : U × V, |witness J ψ G p|
      = ∑ p : U × V, (2 : ℝ) ^ J.card * |ψ (G p)| / rectCard U V :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = ((2 : ℝ) ^ J.card * ∑ p : U × V, |ψ (G p)|) / rectCard U V := by
        rw [← Finset.sum_div, Finset.mul_sum]
    _ = ((2 : ℝ) ^ J.card
          * ∑ z : J → Bool, (outCount J G z : ℝ) * |ψ z|) / rectCard U V := by rw [hsplit]
    _ = (2 : ℝ) ^ J.card * ∑ z : J → Bool, |ψ z| * outDist J G z := by
        rw [mul_div_assoc]
        congr 1
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [outDist]
        field_simp

/-- Lemma 3.2, first half: `‖Ψ‖₁ ≤ 1.01` for a dual polynomial of `ℓ₁` norm one and
`1.01`-bounded gadget output density. -/
theorem lemma32_l1 [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype V]
    (J : Finset ι) (ψ : (J → Bool) → ℝ) (G : U × V → J → Bool) (η : ℝ)
    (hU : 0 < Fintype.card U) (hV : 0 < Fintype.card V)
    (hhi : ∀ z : J → Bool, outDist J G z ≤ (1 + η) / (2 : ℝ) ^ J.card)
    (hpsi : ∑ z : J → Bool, |ψ z| = 1) (hη0 : 0 ≤ η) (hη : η ≤ 1 / 100) :
    (∑ p : U × V, |witness J ψ G p|) ≤ 1.01 := by
  have hP : (0 : ℝ) < (2 : ℝ) ^ J.card := by positivity
  rw [sum_abs_witness J ψ G hU hV]
  have hle : (∑ z : J → Bool, |ψ z| * outDist J G z)
      ≤ ∑ z : J → Bool, |ψ z| * ((1 + η) / (2 : ℝ) ^ J.card) := by
    refine Finset.sum_le_sum fun z _ => ?_
    exact mul_le_mul_of_nonneg_left (hhi z) (abs_nonneg _)
  have hmul : (2 : ℝ) ^ J.card * ∑ z : J → Bool, |ψ z| * ((1 + η) / (2 : ℝ) ^ J.card)
      = (1 + η) * ∑ z : J → Bool, |ψ z| := by
    rw [← Finset.sum_mul]
    field_simp
  have hstep : (2 : ℝ) ^ J.card * ∑ z : J → Bool, |ψ z| * outDist J G z
      ≤ (1 + η) * ∑ z : J → Bool, |ψ z| := by
    rw [← hmul]
    exact mul_le_mul_of_nonneg_left hle (le_of_lt hP)
  rw [hpsi, mul_one] at hstep
  linarith

/-- Lemma 3.2, second half: `⟨F, Ψ⟩ ≥ 0.33` for a `{±1}`-valued outer function, a dual
polynomial of `ℓ₁` norm one with `⟨f,ψ⟩ ≥ 1/3`, and gadget output density within
`(1 ± η)/2^{|J|}` for `η ≤ 1/300`. -/
theorem lemma32_inner [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype V]
    (J : Finset ι) (f : (J → Bool) → ℝ) (ψ : (J → Bool) → ℝ) (G : U × V → J → Bool) (η : ℝ)
    (hU : 0 < Fintype.card U) (hV : 0 < Fintype.card V)
    (hlo : ∀ z : J → Bool, (1 - η) / (2 : ℝ) ^ J.card ≤ outDist J G z)
    (hhi : ∀ z : J → Bool, outDist J G z ≤ (1 + η) / (2 : ℝ) ^ J.card)
    (hf : ∀ z : J → Bool, |f z| ≤ 1) (hψ1 : ∑ z : J → Bool, |ψ z| = 1)
    (hdual : 1 / 3 ≤ ∑ z : J → Bool, f z * ψ z)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 300) :
    0.33 ≤ ∑ p : U × V, f (G p) * witness J ψ G p := by
  have hCpos : 0 < rectCard U V := by
    unfold rectCard
    exact mul_pos (by exact_mod_cast hU) (by exact_mod_cast hV)
  have hP : (0 : ℝ) < (2 : ℝ) ^ J.card := by positivity
  have hterm : ∀ p : U × V, f (G p) * witness J ψ G p
      = (2 : ℝ) ^ J.card * (f (G p) * ψ (G p)) / rectCard U V := by
    intro p
    rw [witness]
    field_simp
  have hsplit : (∑ p : U × V, f (G p) * ψ (G p))
      = ∑ z : J → Bool, (outCount J G z : ℝ) * (f z * ψ z) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (U × V)))
      (t := (Finset.univ : Finset (J → Bool))) (g := G)
      (fun p _ => Finset.mem_univ (G p)) (fun p => f (G p) * ψ (G p))]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hconst : (∑ p ∈ Finset.univ.filter (fun p : U × V => G p = z), f (G p) * ψ (G p))
        = ∑ _p ∈ Finset.univ.filter (fun p : U × V => G p = z), (f z * ψ z) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [(Finset.mem_filter.mp hp).2]
    rw [hconst, Finset.sum_const, outCount]
    simp
  have hrewrite : (∑ p : U × V, f (G p) * witness J ψ G p)
      = (2 : ℝ) ^ J.card * ∑ z : J → Bool, (f z * ψ z) * outDist J G z := by
    calc ∑ p : U × V, f (G p) * witness J ψ G p
        = ∑ p : U × V, (2 : ℝ) ^ J.card * (f (G p) * ψ (G p)) / rectCard U V :=
          Finset.sum_congr rfl fun p _ => hterm p
      _ = ((2 : ℝ) ^ J.card * ∑ p : U × V, f (G p) * ψ (G p)) / rectCard U V := by
          rw [← Finset.sum_div, Finset.mul_sum]
      _ = ((2 : ℝ) ^ J.card
            * ∑ z : J → Bool, (outCount J G z : ℝ) * (f z * ψ z)) / rectCard U V := by
          rw [hsplit]
      _ = (2 : ℝ) ^ J.card * ∑ z : J → Bool, (f z * ψ z) * outDist J G z := by
          rw [mul_div_assoc]
          congr 1
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [outDist]
          field_simp
  rw [hrewrite]
  -- multiply the two-sided density bracket by `2^{|J|}`
  have hlo' : ∀ z : J → Bool, 1 - η ≤ (2 : ℝ) ^ J.card * outDist J G z := by
    intro z
    have h := mul_le_mul_of_nonneg_left (hlo z) (le_of_lt hP)
    have heq : (1 : ℝ) - η = (2 : ℝ) ^ J.card * ((1 - η) / (2 : ℝ) ^ J.card) := by
      field_simp
    rw [heq]
    exact h
  have hhi' : ∀ z : J → Bool, (2 : ℝ) ^ J.card * outDist J G z ≤ 1 + η := by
    intro z
    have h := mul_le_mul_of_nonneg_left (hhi z) (le_of_lt hP)
    have heq : (1 : ℝ) + η = (2 : ℝ) ^ J.card * ((1 + η) / (2 : ℝ) ^ J.card) := by
      field_simp
    rw [heq]
    exact h
  -- pointwise: the density bracket squeezes `c · (2^{|J|} · outDist)`
  have hpt' : ∀ z : J → Bool, f z * ψ z - |f z * ψ z| * η
      ≤ (f z * ψ z) * ((2 : ℝ) ^ J.card * outDist J G z) := by
    intro z
    set c := f z * ψ z with hc
    by_cases h : 0 ≤ c
    · have h1 : c * (1 - η) ≤ c * ((2 : ℝ) ^ J.card * outDist J G z) :=
        mul_le_mul_of_nonneg_left (hlo' z) h
      nlinarith [abs_of_nonneg h]
    · have hneg : c ≤ 0 := le_of_lt (lt_of_not_ge h)
      have h1 : c * (1 + η) ≤ c * ((2 : ℝ) ^ J.card * outDist J G z) :=
        mul_le_mul_of_nonpos_left (hhi' z) hneg
      nlinarith [abs_of_neg (lt_of_not_ge h)]
  have hsum : ∑ z : J → Bool, (f z * ψ z - |f z * ψ z| * η)
      ≤ (2 : ℝ) ^ J.card * ∑ z : J → Bool, (f z * ψ z) * outDist J G z := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ => ?_
    have := hpt' z
    calc f z * ψ z - |f z * ψ z| * η
        ≤ (f z * ψ z) * ((2 : ℝ) ^ J.card * outDist J G z) := this
      _ = (2 : ℝ) ^ J.card * ((f z * ψ z) * outDist J G z) := by ring
  have habs : (∑ z : J → Bool, |f z * ψ z|) ≤ 1 := by
    calc (∑ z : J → Bool, |f z * ψ z|) ≤ ∑ z : J → Bool, |ψ z| := by
          refine Finset.sum_le_sum fun z _ => ?_
          rw [abs_mul]
          calc |f z| * |ψ z| ≤ 1 * |ψ z| :=
                mul_le_mul_of_nonneg_right (hf z) (abs_nonneg _)
            _ = |ψ z| := one_mul _
      _ = 1 := hψ1
  have hL : 1 / 3 - η ≤ ∑ z : J → Bool, (f z * ψ z - |f z * ψ z| * η) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have h1 : η * (∑ z : J → Bool, |f z * ψ z|) ≤ η * 1 :=
      mul_le_mul_of_nonneg_left habs hη0
    linarith
  have hfinal : 1 / 3 - η ≤ (2 : ℝ) ^ J.card * ∑ z : J → Bool, (f z * ψ z) * outDist J G z :=
    le_trans hL hsum
  linarith

end Qatlib.Papers.LiftingWu25.DenseLift
