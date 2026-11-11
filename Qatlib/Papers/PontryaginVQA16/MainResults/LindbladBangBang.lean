/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PontryaginVQA16.MainResults.BangBangOptimal
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Bang-bang protocols for Markovian open systems (claim `c002`)

Source: Zhi-Cheng Yang, Armin Rahmani, Alireza Shabani, Hartmut Neven,
Claudio Chamon, *Optimizing Variational Quantum Algorithms using Pontryagin's
Minimum Principle*, arXiv:1607.06473v3 (11 March 2017), Sec. III.B, p. 3,
Eq. (8):

```
dρ/dt = -i [∑_α g_α(t) H_α, ρ]
        + ∑_β f_β(t) (2 F_β ρ F_β† - {F_β† F_β, ρ})
```

> where the optimal protocol `{g_α(t), f_β(t)}`, if controllable, are of type
> bang-bang.  This is due to the linearity of the dynamical equation (8).

The module formalises the algebraic core of the paper's sentence: the right
hand side of Eq. (8) is *linear* in the control vector `(g, f)`, hence for any
costate pairing `P` the Pontryagin Hamiltonian `P(L(g,f)ρ)` is affine in the
controls with coefficient `P(-i[H_α,ρ])` on `g_α` and `P(D(F_β)ρ)` on `f_β`.
Combining this with the endpoint lemma of claim `c001` gives the bang-bang
conclusion coordinate by coordinate.  Controllability is only needed for the
existence of an optimal protocol; it is not used by the endpoint argument
itself, and the paper's statement is therefore formalised without it.

The GKSL semantics (a Lindblad generator generates a completely positive
trace-preserving semigroup, with semigroup law and KMS adjoint) is the frozen
`QuantumAlgorithm*` concept `LindbladFlow.GkslSemigroup`; this module only reads
that concept and does not redefine or reprove its semigroup theory.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.PontryaginVQA16.MainResults.LindbladBangBang

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutator `[H, ρ] = H ρ - ρ H` appearing in Eq. (8). -/
def commutator (H ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  H * ρ - ρ * H

/-- The Hamiltonian generator term `-i [H, ρ]` of Eq. (8). -/
def generatorTerm (H ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I) • commutator H ρ

/-- The Lindblad dissipator `D(F) ρ = 2 F ρ F† - {F† F, ρ}` of Eq. (8). -/
def dissipator (F ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ) • (F * ρ * Fᴴ) - (Fᴴ * F * ρ + ρ * (Fᴴ * F))

/-- The right hand side of the Lindblad equation (8), split into the pieces
that multiply the two families of independent controls.  With
`u = (g, f)` this is `∑_α g_α (-i[H_α,ρ]) + ∑_β f_β D(F_β)ρ`, which is the
paper's Eq. (8) with the control-linear structure made explicit. -/
def lindbladGenerator {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (g : ι → ℝ) (f : κ → ℝ) (ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  (∑ α, g α • generatorTerm (Hs α) ρ) + ∑ β, f β • dissipator (Fs β) ρ

/-- The generator equals the displayed Lindblad form of Eq. (8): the
Hamiltonian part is `-i [∑_α g_α H_α, ρ]` and the dissipative part carries the
real rates `f_β` inside the dissipator. -/
theorem lindbladGenerator_eq_source {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (g : ι → ℝ) (f : κ → ℝ) (ρ : Matrix n n ℂ) :
    lindbladGenerator Hs Fs g f ρ =
      (-Complex.I) • (∑ α, (g α : ℂ) • commutator (Hs α) ρ)
        + ∑ β, (f β : ℂ) • dissipator (Fs β) ρ := by
  unfold lindbladGenerator generatorTerm
  have h1 : (∑ α, g α • ((-Complex.I) • commutator (Hs α) ρ))
      = ∑ α, (-Complex.I) • ((g α : ℂ) • commutator (Hs α) ρ) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    try module
  have h2 : (∑ β, f β • dissipator (Fs β) ρ)
      = ∑ β, (f β : ℂ) • dissipator (Fs β) ρ := by
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    try module
  rw [h1, h2, ← Finset.smul_sum]

/-- **Linearity of Eq. (8) in the controls, additive form.**  The generator of
the Markovian dynamics is additive in the control vector `(g, f)`. -/
theorem lindbladGenerator_add {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (g₁ g₂ : ι → ℝ) (f₁ f₂ : κ → ℝ) (ρ : Matrix n n ℂ) :
    lindbladGenerator Hs Fs (g₁ + g₂) (f₁ + f₂) ρ =
      lindbladGenerator Hs Fs g₁ f₁ ρ + lindbladGenerator Hs Fs g₂ f₂ ρ := by
  unfold lindbladGenerator
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

/-- **Linearity of Eq. (8) in the controls, homogeneous form.**  Rescaling all
controls rescales the right hand side of Eq. (8). -/
theorem lindbladGenerator_smul {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (c : ℝ) (g : ι → ℝ) (f : κ → ℝ) (ρ : Matrix n n ℂ) :
    lindbladGenerator Hs Fs (c • g) (c • f) ρ =
      c • lindbladGenerator Hs Fs g f ρ := by
  unfold lindbladGenerator
  simp only [Pi.smul_apply, smul_add, smul_smul, Finset.smul_sum]
  module

/-- **The optimal-control Hamiltonian of Eq. (8) is affine in the controls.**
For any real-linear costate pairing `P`, `P (L(g,f) ρ)` is the affine control
cost with coefficient `P (-i[H_α,ρ])` on `g_α` and `P (D(F_β)ρ)` on `f_β`.
This is exactly the "linearity of the dynamical equation (8)" invoked by the
paper as the reason for bang-bang optimality. -/
theorem costate_affine {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (P : Matrix n n ℂ →ₗ[ℝ] ℝ) (g : ι → ℝ) (f : κ → ℝ) (ρ : Matrix n n ℂ) :
    P (lindbladGenerator Hs Fs g f ρ) =
      BangBangOptimal.affineCost (fun α => P (generatorTerm (Hs α) ρ))
        (∑ β, f β * P (dissipator (Fs β) ρ)) g := by
  unfold lindbladGenerator BangBangOptimal.affineCost
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => mul_comm (g x) (P (generatorTerm (Hs x) ρ))

/-- **The optimal-control Hamiltonian of Eq. (8) is affine in the dissipative
rates.**  Complementary to `costate_affine`: pairing the generator against the
costate, `P (L(g,f) ρ)` is also affine with coefficient `P (D(F_β)ρ)` on the
rate `f_β`, which is the form needed to force the dissipative controls to an
endpoint. -/
theorem costate_affine_dissipative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (P : Matrix n n ℂ →ₗ[ℝ] ℝ) (g : ι → ℝ) (f : κ → ℝ) (ρ : Matrix n n ℂ) :
    P (lindbladGenerator Hs Fs g f ρ) =
      BangBangOptimal.affineCost (fun β => P (dissipator (Fs β) ρ))
        (∑ α, g α * P (generatorTerm (Hs α) ρ)) f := by
  unfold lindbladGenerator BangBangOptimal.affineCost
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun x _ => mul_comm (f x) (P (dissipator (Fs x) ρ))

/-- **Claim `c002`: bang-bang optimal protocols for Markovian open systems.**

Consider the Markovian Lindblad dynamics of Eq. (8), with independent controls
`g_α` in `[glo_α, ghi_α]` and `f_β` in `[flo_β, fhi_β]`.  If `(g, f)` is
optimal for a cost that depends on the state only through the costate pairing
`P` of the generator, then every `g_α` with nonzero coefficient
`P(-i[H_α,ρ])` and every `f_β` with nonzero coefficient `P(D(F_β)ρ)` is at an
endpoint of its range: the optimal protocol is bang-bang in exactly the
controllable coordinates. -/
theorem lindblad_bangBang {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (Hs : ι → Matrix n n ℂ) (Fs : κ → Matrix n n ℂ)
    (P : Matrix n n ℂ →ₗ[ℝ] ℝ) (ρ : Matrix n n ℂ)
    (glo ghi : ι → ℝ) (flo fhi : κ → ℝ)
    (g : ι → ℝ) (f : κ → ℝ)
    (hgbox : ∀ α, glo α ≤ g α ∧ g α ≤ ghi α)
    (hfbox : ∀ β, flo β ≤ f β ∧ f β ≤ fhi β)
    (hmin : ∀ (g' : ι → ℝ) (f' : κ → ℝ),
      (∀ α, glo α ≤ g' α ∧ g' α ≤ ghi α) →
      (∀ β, flo β ≤ f' β ∧ f' β ≤ fhi β) →
      P (lindbladGenerator Hs Fs g f ρ) ≤
        P (lindbladGenerator Hs Fs g' f' ρ))
    (hgenG : ∀ α, P (generatorTerm (Hs α) ρ) ≠ 0)
    (hgenF : ∀ β, P (dissipator (Fs β) ρ) ≠ 0) :
    (∀ α, g α = glo α ∨ g α = ghi α) ∧
      (∀ β, f β = flo β ∨ f β = fhi β) := by
  constructor
  · -- vary the Hamiltonian controls `g`, keeping `f` fixed
    have hmin_g : ∀ g' ∈ BangBangOptimal.controlBox glo ghi,
        BangBangOptimal.affineCost
            (fun α => P (generatorTerm (Hs α) ρ))
            (∑ β, f β * P (dissipator (Fs β) ρ)) g ≤
          BangBangOptimal.affineCost
            (fun α => P (generatorTerm (Hs α) ρ))
            (∑ β, f β * P (dissipator (Fs β) ρ)) g' := by
      intro g' hg'
      have h := hmin g' f hg' hfbox
      rw [costate_affine Hs Fs P g f ρ, costate_affine Hs Fs P g' f ρ] at h
      exact h
    exact BangBangOptimal.bangBang_optimal_protocol (fun α => hgbox α) hmin_g hgenG
  · -- vary the dissipative controls `f`, keeping `g` fixed
    have hmin_f : ∀ f' ∈ BangBangOptimal.controlBox flo fhi,
        BangBangOptimal.affineCost
            (fun β => P (dissipator (Fs β) ρ))
            (∑ α, g α * P (generatorTerm (Hs α) ρ)) f ≤
          BangBangOptimal.affineCost
            (fun β => P (dissipator (Fs β) ρ))
            (∑ α, g α * P (generatorTerm (Hs α) ρ)) f' := by
      intro f' hf'
      have h := hmin g f' hgbox hf'
      rw [costate_affine_dissipative Hs Fs P g f ρ,
        costate_affine_dissipative Hs Fs P g f' ρ] at h
      exact h
    exact BangBangOptimal.bangBang_optimal_protocol (fun β => hfbox β) hmin_f hgenF

end Qatlib.Papers.PontryaginVQA16.MainResults.LindbladBangBang
