/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommGibbsSamp14.GibbsStructure.CommutingFamily

@[expose] public section

/-!
# Commuting Gibbs samplers — explicit finite-temperature Gibbs instances

See [KastoryanoBrandao2014], Proposition 10 and Lemma 12
([arXiv v3](https://arxiv.org/abs/1409.3435v3)).

This file instantiates the abstract `ρ`-weighted Hilbert space of `RhoSpace` on genuine
finite Gibbs states:

* `qubitGibbsWeight` normalizes the Boltzmann weights `e^{-β h_i}` of a two-level system;
* `qubitExpect` is the minimal conditional expectation onto the trivial algebra,
  `f ↦ tr[ρ f] · 1`, and is proved to be a projective conditional expectation with all the
  Hilbert-space properties of Definition 8: unitality, state invariance, self-adjointness,
  contractivity and monotonicity;
* `productWeight` and `pairExpectLeft`/`pairExpectRight` give the two-site product Gibbs
  state and its single-site conditional expectations; they commute, so the heat-bath
  generator `L = (E₀ − id) + (E₁ − id)` on two sites has Dirichlet form
  `Var₀ + Var₁` and spectral gap at least `1`.

These constructions give the scalar conditional expectations on the diagonal algebras
of a two-level system and its two-site product. Their weighted reversibility and
unitality support the corresponding parts of Proposition 10 and Lemma 12.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CommGibbsSamp14.GibbsStructure

open scoped InnerProductSpace
open Finset

/-! ## A single Gibbs qubit -/

/-- A strictly positive, normalized distribution on a two-level system. -/
def qubitWeight (p : Fin 2 → ℝ) (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    GibbsWeight (Fin 2) where
  weight := p
  pos := hp
  sum_eq_one := hsum

/-- The normalized diagonal Gibbs weight of a two-level Hamiltonian with energies
`energy` at inverse temperature `β`. -/
noncomputable def qubitGibbsWeight (β : ℝ) (energy : Fin 2 → ℝ) : GibbsWeight (Fin 2) :=
  let boltzmann := fun i => Real.exp (-(β * energy i))
  let Z := ∑ i, boltzmann i
  have hZ : 0 < Z := by
    dsimp [Z, boltzmann]
    rw [Fin.sum_univ_two]
    positivity
  qubitWeight (fun i => boltzmann i / Z)
    (fun i => div_pos (Real.exp_pos _) hZ)
    (by rw [← Finset.sum_div, div_self (ne_of_gt hZ)])

/-- The minimal conditional expectation onto the trivial algebra:
`E(f) = tr[ρ f] · 1`, the single-site case of Proposition 10. -/
noncomputable def qubitExpect (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun _ => rhoInner ρ f (fun _ => (1 : ℝ))

/-- The unit observable has `ρ`-norm one. -/
theorem rhoInner_one_one (ρ : GibbsWeight (Fin 2)) :
    rhoInner ρ (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = 1 := by
  simp [rhoInner, ρ.sum_eq_one]

/-- The minimal conditional expectation is a scalar multiple of the unit observable. -/
theorem qubitExpect_eq_smul (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) :
    qubitExpect ρ f = rhoInner ρ f (fun _ => (1 : ℝ)) • (fun _ => (1 : ℝ)) := by
  funext i
  simp [qubitExpect, Pi.smul_apply]

/-- The two-level weighted average is linear, self-adjoint and idempotent. -/
theorem qubitExpect_isOrthProj (ρ : GibbsWeight (Fin 2)) :
    IsOrthProj ρ (qubitExpect ρ) where
  map_add f g := by
    funext i
    simp only [qubitExpect, rhoInner_add_left, Pi.add_apply]
  map_smul c f := by
    funext i
    simp only [qubitExpect, rhoInner_smul_left, Pi.smul_apply, smul_eq_mul]
  adjoint f g := by
    rw [qubitExpect_eq_smul (f := f), qubitExpect_eq_smul (f := g)]
    rw [rhoInner_smul_left, rhoInner_smul_right,
      rhoInner_symm ρ (fun _ => (1 : ℝ)) g]
    ring
  idem f := by
    rw [qubitExpect_eq_smul, qubitExpect_eq_smul, rhoInner_smul_left,
      rhoInner_one_one, mul_one]

/-- The minimal conditional expectation is unital. -/
theorem qubitExpect_unital (ρ : GibbsWeight (Fin 2)) :
    qubitExpect ρ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  rw [qubitExpect_eq_smul, rhoInner_one_one, one_smul]

/-- Definition 8(2): the conditional expectation preserves the Gibbs expectation. -/
theorem qubitExpect_state (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) :
    rhoInner ρ (qubitExpect ρ f) (fun _ => (1 : ℝ)) =
      rhoInner ρ f (fun _ => (1 : ℝ)) := by
  rw [qubitExpect_eq_smul, rhoInner_smul_left, rhoInner_one_one, mul_one]

/-- Definition 8(4): the iterates of the conditional expectation are monotone. -/
theorem qubitExpect_monotone (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) (n : ℕ) :
    rhoInner ρ ((qubitExpect ρ)^[n] f) f ≥ rhoInner ρ ((qubitExpect ρ)^[n + 1] f) f := by
  rcases n with _ | n
  · show rhoInner ρ f f ≥ rhoInner ρ ((qubitExpect ρ)^[0 + 1] f) f
    rw [show (qubitExpect ρ)^[0 + 1] f = qubitExpect ρ f by simp]
    have h1 : rhoInner ρ (qubitExpect ρ f) f = rhoInner ρ f (qubitExpect ρ f) :=
      (qubitExpect_isOrthProj ρ).adjoint f f
    have h2 : rhoInner ρ (qubitExpect ρ f) (qubitExpect ρ f) =
        rhoInner ρ f (qubitExpect ρ f) := by
      rw [(qubitExpect_isOrthProj ρ).adjoint f (qubitExpect ρ f),
        (qubitExpect_isOrthProj ρ).idem]
    rw [h1, ← h2]
    exact (qubitExpect_isOrthProj ρ).contract f
  · have hiter : ∀ m, (qubitExpect ρ)^[m + 1] f = qubitExpect ρ f := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Function.iterate_succ_apply', ih, (qubitExpect_isOrthProj ρ).idem]
    rw [hiter n, hiter (n + 1)]

/-- The Dirichlet form of the single-site heat-bath generator is exactly the variance. -/
theorem qubit_dirichlet_identity (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) :
    rhoInner ρ f (-(qubitExpect ρ f - f)) =
      rhoInner ρ (f - qubitExpect ρ f) (f - qubitExpect ρ f) := by
  rw [rhoInner_neg_right, rhoInner_sub_right, rhoInner_sub_left, rhoInner_sub_right,
    rhoInner_sub_right, (qubitExpect_isOrthProj ρ).adjoint f f]
  rw [show rhoInner ρ (qubitExpect ρ f) (qubitExpect ρ f) =
      rhoInner ρ f (qubitExpect ρ f) by
    rw [(qubitExpect_isOrthProj ρ).adjoint f (qubitExpect ρ f),
      (qubitExpect_isOrthProj ρ).idem]]
  ring

/-- The single-site heat-bath generator `E − id` has the exact spectral gap `1`. -/
theorem qubit_spectralGap (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) :
    rhoInner ρ f (-(qubitExpect ρ f - f)) ≥
      1 * rhoInner ρ (f - qubitExpect ρ f) (f - qubitExpect ρ f) := by
  rw [qubit_dirichlet_identity, one_mul]

/-- Exponential mixing of the single-site heat-bath flow at the exact rate `1`. -/
theorem qubit_flow_decay (ρ : GibbsWeight (Fin 2)) (f : Fin 2 → ℝ) (t : ℝ) :
    rhoNorm ρ (heatBathFlow ρ (qubitExpect ρ) t f - qubitExpect ρ f) =
      Real.exp (-t) * rhoNorm ρ (f - qubitExpect ρ f) :=
  heatBathFlow_decay ρ (qubitExpect ρ) t f

/-! ## Two-site product Gibbs states -/

/-- The product Gibbs weight `ρ ⊗ ρ` on two sites. -/
noncomputable def productWeight (ρ : GibbsWeight (Fin 2)) :
    GibbsWeight (Fin 2 × Fin 2) where
  weight x := ρ.weight x.1 * ρ.weight x.2
  pos x := mul_pos (ρ.pos x.1) (ρ.pos x.2)
  sum_eq_one := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
    calc ∑ a, ∑ b, ρ.weight a * ρ.weight b
        = ∑ a, ρ.weight a * (∑ b, ρ.weight b) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.mul_sum]
      _ = 1 := by simp [ρ.sum_eq_one]

/-- The single-site conditional expectation on the first coordinate. -/
noncomputable def pairExpectLeft (ρ : GibbsWeight (Fin 2))
    (f : Fin 2 × Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun x => ∑ a : Fin 2, ρ.weight a * f (a, x.2)

/-- The single-site conditional expectation on the second coordinate. -/
noncomputable def pairExpectRight (ρ : GibbsWeight (Fin 2))
    (f : Fin 2 × Fin 2 → ℝ) : Fin 2 × Fin 2 → ℝ :=
  fun x => ∑ b : Fin 2, ρ.weight b * f (x.1, b)

/-- The first-coordinate conditional expectation of a product Gibbs state is projective. -/
theorem pairExpectLeft_isOrthProj (ρ : GibbsWeight (Fin 2)) :
    IsOrthProj (productWeight ρ) (pairExpectLeft ρ) where
  map_add f g := by
    funext x
    simp only [pairExpectLeft, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul c f := by
    funext x
    simp only [pairExpectLeft, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  adjoint f g := by
    simp only [rhoInner, pairExpectLeft, productWeight]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_product, Fin.sum_univ_two]
    ring
  idem f := by
    funext x
    simp only [pairExpectLeft, Fin.sum_univ_two]
    have hsum : ρ.weight 0 + ρ.weight 1 = 1 := by
      simpa [Fin.sum_univ_two] using ρ.sum_eq_one
    rw [← add_mul, hsum, one_mul]

/-- The second-coordinate conditional expectation of a product Gibbs state is projective. -/
theorem pairExpectRight_isOrthProj (ρ : GibbsWeight (Fin 2)) :
    IsOrthProj (productWeight ρ) (pairExpectRight ρ) where
  map_add f g := by
    funext x
    simp only [pairExpectRight, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul c f := by
    funext x
    simp only [pairExpectRight, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  adjoint f g := by
    simp only [rhoInner, pairExpectRight, productWeight]
    rw [← Finset.univ_product_univ, Finset.sum_product]
    simp only [Finset.sum_product, Fin.sum_univ_two]
    ring
  idem f := by
    funext x
    simp only [pairExpectRight, Fin.sum_univ_two]
    have hsum : ρ.weight 0 + ρ.weight 1 = 1 := by
      simpa [Fin.sum_univ_two] using ρ.sum_eq_one
    rw [← add_mul, hsum, one_mul]

/-- The first-coordinate conditional expectation is unital. -/
theorem pairExpectLeft_unital (ρ : GibbsWeight (Fin 2)) :
    pairExpectLeft ρ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  simp only [pairExpectLeft, Fin.sum_univ_two]
  have hsum : ρ.weight 0 + ρ.weight 1 = 1 := by
    simpa [Fin.sum_univ_two] using ρ.sum_eq_one
  simp [hsum]

/-- The second-coordinate conditional expectation is unital. -/
theorem pairExpectRight_unital (ρ : GibbsWeight (Fin 2)) :
    pairExpectRight ρ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext x
  simp only [pairExpectRight, Fin.sum_univ_two]
  have hsum : ρ.weight 0 + ρ.weight 1 = 1 := by
    simpa [Fin.sum_univ_two] using ρ.sum_eq_one
  simp [hsum]

/-- The two single-site conditional expectations commute, as they must for a product
Gibbs state. -/
theorem pairExpect_commute (ρ : GibbsWeight (Fin 2)) (f : Fin 2 × Fin 2 → ℝ) :
    pairExpectLeft ρ (pairExpectRight ρ f) = pairExpectRight ρ (pairExpectLeft ρ f) := by
  funext x
  simp only [pairExpectLeft, pairExpectRight, Fin.sum_univ_two]
  ring

/-- The two-site commuting family of conditional expectations. -/
noncomputable def pairFamily (ρ : GibbsWeight (Fin 2)) :
    CommutingFamily Bool (Fin 2 × Fin 2) where
  weight := productWeight ρ
  E j := if j then pairExpectRight ρ else pairExpectLeft ρ
  proj j := by
    cases j
    · simpa using pairExpectLeft_isOrthProj ρ
    · simpa using pairExpectRight_isOrthProj ρ
  commute i j f := by
    cases i <;> cases j <;> simp [pairExpect_commute]
  unital j := by
    cases j
    · simpa using pairExpectLeft_unital ρ
    · simpa using pairExpectRight_unital ρ

/-- Resampling both coordinates of the product state projects onto the constant observable
whose value is the full Gibbs mean. -/
theorem pair_projList_eq_mean (ρ : GibbsWeight (Fin 2)) (f : Fin 2 × Fin 2 → ℝ) :
    (pairFamily ρ).projList [false, true] f =
      fun _ => rhoInner (productWeight ρ) f (fun _ => 1) := by
  funext x
  simp only [CommutingFamily.projList_cons, CommutingFamily.projList_nil, pairFamily,
    Bool.false_eq_true, ite_false, ite_true, pairExpectLeft, pairExpectRight, rhoInner,
    productWeight, mul_one]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Fin.sum_univ_two]
  ring

/-- The two-site product heat-bath generator satisfies the gap bound with constant `1`,
uniformly in the Gibbs weight. -/
theorem pair_spectralGap (ρ : GibbsWeight (Fin 2)) (f : Fin 2 × Fin 2 → ℝ) :
    rhoInner (productWeight ρ) f (-((pairFamily ρ).gen [false, true] f)) ≥
      1 * rhoInner (productWeight ρ)
        (f - (pairFamily ρ).projList [false, true] f)
        (f - (pairFamily ρ).projList [false, true] f) :=
  (pairFamily ρ).spectralGap_one [false, true] (by simp) f

end Qatlib.Papers.CommGibbsSamp14.GibbsStructure
