/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation.RootOfUnityPin

set_option backward.isDefEq.respectTransparency false

/-!
# MUBProduct12 — Lemma 2: completing states are product states

McNulty–Weigert, fixed arXiv:1203.6887v2, Lemma 2 proof, pp. 9–10, Eqs. (30)–(38).

After reducing the constellation to a pair of MU product bases `P0` or `P1` (Lemma 3) and
localising the four constellation states to `S1` (Eq. (30)) or `S2` (Eq. (31)), the paper
shows that any state completing to a MU product basis is a product state:

* `S1` branch (Eq. (32)): the completing pair is
  `|ψ₁⟩ = α |1_y, B^⊥⟩ + β |1_y, B^⊥⊥⟩ = |1_y⟩ ⊗ (α |B^⊥⟩ + β |B^⊥⊥⟩)`, manifestly a
  product state;
* `S2` branch (Eqs. (33)–(38)): `|ψ₂⟩ = α |0_y, A^⊥⊥⟩ + β |1_y, B^⊥⊥⟩` is a product state
  because `α = 0` or `β = 0` (`s2_completing_state_product`).

This file formalises the two branch conclusions and the general fact that a vector
`α (φ ⊗ Φ) + β (ψ ⊗ Ψ)` with `α = 0` or `β = 0` is a product state.
-/
set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.MUBProduct12.TripleClassify.ProductModel

/-- Bilinearity of the tensor product in its second factor. -/
theorem tensorState_linear_second {I J : Type*} [Fintype I] [Fintype J]
    (a : QState I) (b c : QState J) (s t : ℂ) :
    (fun p => s * TensorState a b p + t * TensorState a c p)
      = TensorState a (fun j => s * b j + t * c j) := by
  funext p
  simp only [TensorState]
  ring

/-- Bilinearity of the tensor product in its first factor. -/
theorem tensorState_linear_first {I J : Type*} [Fintype I] [Fintype J]
    (a c : QState I) (b : QState J) (s t : ℂ) :
    (fun p => s * TensorState a b p + t * TensorState c b p)
      = TensorState (fun i => s * a i + t * c i) b := by
  funext p
  simp only [TensorState]
  ring

/-- **`S1` branch, Eq. (32)**: `α |1_y, B^⊥⟩ + β |1_y, B^⊥⊥⟩` is a product state. -/
theorem s1_completing_state_is_product
    (a : C2State) (b c : C3State) (s t : ℂ) :
    IsProductState (fun p => s * TensorState a b p + t * TensorState a c p) :=
  ⟨a, fun j => s * b j + t * c j, tensorState_linear_second a b c s t⟩

/-- A vector `α (φ ⊗ Φ) + β (ψ ⊗ Ψ)` is a product state whenever `α = 0` or `β = 0`. -/
theorem product_of_amplitude_zero
    (φ ψ : C2State) (Φ Ψ : C3State) (α β : ℂ)
    (h : α = 0 ∨ β = 0) :
    IsProductState (fun p => α * TensorState φ Φ p + β * TensorState ψ Ψ p) := by
  rcases h with h | h
  · refine ⟨ψ, fun j => β * Ψ j, ?_⟩
    funext p
    simp only [TensorState, h]
    ring
  · refine ⟨φ, fun j => α * Φ j, ?_⟩
    funext p
    simp only [TensorState, h]
    ring

/-- **`S2` branch, Eqs. (33)–(38)**: the completing state `α |0_y, A⟩ + β |1_y, B⟩` is a
product state, because the cube-root contradiction forces one of `α, β` to vanish and then
the state is one tensor factor times a scalar multiple of the other. -/
theorem s2_completing_state_is_product
    (φ ψ : C2State) (Φ Ψ : C3State) (α β : ℂ) (u v : Fin 3 → ℂ)
    (hu0 : u 0 = 1) (hv0 : v 0 = 1)
    (hu : ∀ J, u J ^ 3 = 1) (hv : ∀ J, v J ^ 3 = 1)
    (hne : (u 1, u 2) ≠ (v 1, v 2))
    (hαβ : Complex.normSq α + Complex.normSq β = 1)
    (hMU : ∀ J, Complex.normSq (α * u J + β * v J) = 1) :
    IsProductState (fun p => α * TensorState φ Φ p + β * TensorState ψ Ψ p) :=
  product_of_amplitude_zero φ ψ Φ Ψ α β
    (s2_completing_state_product α β u v hu0 hv0 hu hv hne hαβ hMU)

end Qatlib.Papers.MUBProduct12.TripleClassify.Lemma2Constellation
