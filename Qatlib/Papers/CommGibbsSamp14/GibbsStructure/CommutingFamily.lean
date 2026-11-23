/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.CommGibbsSamp14.GibbsStructure.RhoSpace

@[expose] public section

/-!
# Commuting Gibbs samplers — the heat-bath generator

See [KastoryanoBrandao2014], Eq. (34) and Lemma 12
([arXiv v3](https://arxiv.org/abs/1409.3435v3)).

The paper's heat-bath generator on the region `A` is the finite sum of single-site minimal
conditional expectations minus the identity, `L^H_A = ∑_{k ∈ A} (E_k − id)` (Eq. (34)).
This file uses the same sum for a family of commuting unital orthogonal projections,
enumerating the sites by a list. The following identities apply in particular to the
diagonal product Gibbs expectations in the two-site model:

* the generator is self-adjoint for `⟨·,·⟩_ρ` (detailed balance, Eq. (8));
* its Dirichlet form is the sum of the single-site variances,
  `⟨f, −L_A f⟩_ρ = ∑_{k ∈ A} Var_k(f)`, hence it is negative semidefinite;
* its kernel is the intersection of the fixed spaces of the single-site maps;
* it annihilates the Gibbs expectation (stationarity of `ρ`);
* its gap inequality holds with constant `1` relative to `E_A = ∏_{k ∈ A} E_k`, uniformly
  in the number of sites and in the enumeration.

The single-site heat-bath flow `exp(t (E_k − id))` is constructed explicitly and its exact
exponential decay to the projection is proved. The abstract family has no lattice support
condition or matrix positivity condition. Commutation of the single-site maps is an
additional hypothesis beyond commutation of the Hamiltonian terms.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CommGibbsSamp14.GibbsStructure

open scoped InnerProductSpace
open Finset

universe u

variable {ι : Type*} {X : Type*}

/-- A list of non-negative reals with zero sum is identically zero. -/
theorem list_sum_eq_zero_of_nonneg {l : List ℝ} (h : ∀ x ∈ l, 0 ≤ x) (hs : l.sum = 0) :
    ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.sum_cons] at hs
      have ha : 0 ≤ a := h a (by simp)
      have hl : ∀ x ∈ l, 0 ≤ x := fun x hx => h x (by simp [hx])
      have hln : 0 ≤ l.sum := List.sum_nonneg hl
      have ha0 : a = 0 := by linarith
      have hl0 : l.sum = 0 := by linarith
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha0
      · exact ih hl hl0 x hx'

/-- A commuting family of unital orthogonal projections on a finite configuration space
with a Gibbs weight `ρ`. The projections model single-site expectations when supplied
by a diagonal product Gibbs state. -/
structure CommutingFamily (ι X : Type*) [Fintype X] where
  /-- the Gibbs weight `ρ` -/
  weight : GibbsWeight X
  /-- the site-indexed orthogonal projections `E_k` -/
  E : ι → (X → ℝ) → (X → ℝ)
  /-- each `E_k` is projective -/
  proj : ∀ k, IsOrthProj weight (E k)
  /-- the projections commute pairwise -/
  commute : ∀ i j f, E i (E j f) = E j (E i f)
  /-- each `E_k` is unital (Definition 8(1)) -/
  unital : ∀ k, E k (fun _ => (1 : ℝ)) = fun _ => 1

namespace CommutingFamily

variable [Fintype X] (F : CommutingFamily ι X)

/-! ## The joint orthogonal projection `E_A = ∏_{k ∈ A} E_k` -/

/-- The joint orthogonal projection over the list `l`, obtained by composing
the indexed projections in `l`. -/
noncomputable def projList (l : List ι) (f : X → ℝ) : X → ℝ :=
  l.foldr (fun k acc => F.E k acc) f

/-- The empty region acts as the identity. -/
@[simp] theorem projList_nil (f : X → ℝ) : F.projList [] f = f := rfl

/-- Appending an index at the front composes one more projection. -/
@[simp] theorem projList_cons (a : ι) (l : List ι) (f : X → ℝ) :
    F.projList (a :: l) f = F.E a (F.projList l f) := rfl

/-- Each indexed projection commutes with the joint projection over any list. -/
theorem comm_projList (k : ι) (l : List ι) (f : X → ℝ) :
    F.E k (F.projList l f) = F.projList l (F.E k f) := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih =>
      rw [projList_cons, projList_cons, F.commute k a, ih]

/-- The finite composition of commuting orthogonal projections is
an orthogonal projection. -/
theorem projList_isOrthProj (l : List ι) : IsOrthProj F.weight (F.projList l) := by
  induction l with
  | nil => exact id_isOrthProj F.weight
  | cons a l ih =>
      exact (F.proj a).comp ih (F.comm_projList a l)

/-- The joint projection is unital. -/
theorem projList_unital (l : List ι) :
    F.projList l (fun _ => (1 : ℝ)) = fun _ => 1 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [projList_cons, ih, F.unital a]

/-- The variance of a region is subadditive over its single-site variances:
`Var_A(f) ≤ ∑_{k ∈ A} Var_k(f)`. -/
theorem var_le_sum (l : List ι) (f : X → ℝ) :
    rhoInner F.weight (f - F.projList l f) (f - F.projList l f) ≤
      (l.map (fun k => rhoInner F.weight (f - F.E k f) (f - F.E k f))).sum := by
  induction l with
  | nil =>
      rw [projList_nil, sub_self, List.map_nil, List.sum_nil]
      simp [rhoInner]
  | cons a l ih =>
      rw [projList_cons]
      have hstep := IsOrthProj.var_comp_le (F.proj a) (F.projList_isOrthProj l)
        (F.comm_projList a l) f
      rw [List.map_cons, List.sum_cons]
      linarith [hstep, ih]

/-! ## The heat-bath generator `L_A = ∑_{k ∈ A} (E_k − id)` -/

/-- The abstract analogue of the heat-bath sum in Eq. (34), built from the indexed
orthogonal projections minus the identity. -/
noncomputable def gen (l : List ι) (f : X → ℝ) : X → ℝ :=
  (l.map (fun k => F.E k f - f)).sum

/-- The heat-bath generator of the empty region vanishes. -/
@[simp] theorem gen_nil (f : X → ℝ) : F.gen [] f = 0 := rfl

/-- Adjoining a site adds one single-site generator. -/
@[simp] theorem gen_cons (a : ι) (l : List ι) (f : X → ℝ) :
    F.gen (a :: l) f = (F.E a f - f) + F.gen l f := by
  simp [gen]

/-- Detailed balance: the heat-bath generator is self-adjoint for `⟨·,·⟩_ρ` (Eq. (8)). -/
theorem gen_adjoint (l : List ι) (f g : X → ℝ) :
    rhoInner F.weight (F.gen l f) g = rhoInner F.weight f (F.gen l g) := by
  induction l with
  | nil => simp [rhoInner]
  | cons a l ih =>
      rw [gen_cons, gen_cons, rhoInner_add_left, rhoInner_add_right, rhoInner_sub_left,
        rhoInner_sub_right, (F.proj a).adjoint f g, ih]

/-- The single-site Dirichlet form is the single-site variance:
`⟨f, −(E_k f − f)⟩_ρ = Var_k(f)`. -/
theorem dirichlet_single (k : ι) (f : X → ℝ) :
    -(rhoInner F.weight f (F.E k f - f)) =
      rhoInner F.weight (f - F.E k f) (f - F.E k f) := by
  rw [rhoInner_sub_right, rhoInner_sub_left, rhoInner_sub_right, rhoInner_sub_right,
    (F.proj k).adjoint f f]
  rw [show rhoInner F.weight (F.E k f) (F.E k f) = rhoInner F.weight f (F.E k f) by
    rw [(F.proj k).adjoint f (F.E k f), (F.proj k).idem]]
  ring

/-- The Dirichlet form of the heat-bath generator is the sum of the single-site
variances: `⟨f, −L_A f⟩_ρ = ∑_{k ∈ A} Var_k(f)`. -/
theorem dirichletForm_eq (l : List ι) (f : X → ℝ) :
    rhoInner F.weight f (-(F.gen l f)) =
      (l.map (fun k => rhoInner F.weight (f - F.E k f) (f - F.E k f))).sum := by
  induction l with
  | nil => simp [rhoInner]
  | cons a l ih =>
      rw [gen_cons, neg_add, rhoInner_add_right, rhoInner_neg_right, rhoInner_neg_right,
        F.dirichlet_single a f]
      rw [← rhoInner_neg_right, ih, List.map_cons, List.sum_cons]

/-- The heat-bath Dirichlet form is non-negative. -/
theorem dirichletForm_nonneg (l : List ι) (f : X → ℝ) :
    0 ≤ rhoInner F.weight f (-(F.gen l f)) := by
  rw [dirichletForm_eq]
  refine List.sum_nonneg (fun x hx => ?_)
  rcases List.mem_map.mp hx with ⟨k, _, rfl⟩
  exact rhoInner_self_nonneg _ _

/-- The kernel of the heat-bath sum is the intersection of the fixed spaces of its
single-site projections. -/
theorem gen_eq_zero_iff (l : List ι) (f : X → ℝ) :
    F.gen l f = 0 ↔ ∀ k ∈ l, F.E k f = f := by
  constructor
  · intro h k hk
    have hsum : (l.map (fun k => rhoInner F.weight (f - F.E k f) (f - F.E k f))).sum = 0 := by
      rw [← F.dirichletForm_eq l f, h]
      simp [rhoInner]
    have hnonneg : ∀ x ∈ l.map (fun k => rhoInner F.weight (f - F.E k f) (f - F.E k f)),
        0 ≤ x := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨j, _, rfl⟩
      exact rhoInner_self_nonneg _ _
    have hmem : rhoInner F.weight (f - F.E k f) (f - F.E k f) ∈
        l.map (fun k => rhoInner F.weight (f - F.E k f) (f - F.E k f)) :=
      List.mem_map_of_mem hk
    have hk0 := list_sum_eq_zero_of_nonneg hnonneg hsum _ hmem
    have hz : f - F.E k f = 0 := rhoInner_self_eq_zero F.weight hk0
    exact (sub_eq_zero.mp hz).symm
  · intro h
    induction l with
    | nil => rfl
    | cons a l ih =>
        rw [gen_cons, h a (by simp), sub_self, zero_add, ih (fun k hk => h k (by simp [hk]))]

/-- The Gibbs weight is stationary for the heat-bath generator. -/
theorem gen_stationary (l : List ι) (f : X → ℝ) :
    rhoInner F.weight (F.gen l f) (fun _ => (1 : ℝ)) = 0 := by
  induction l with
  | nil => simp [rhoInner]
  | cons a l ih =>
      rw [gen_cons, rhoInner_add_left, rhoInner_sub_left, (F.proj a).adjoint f (fun _ => 1),
        F.unital a, sub_self, zero_add, ih]

/-- On a nonempty list of sites, the heat-bath sum satisfies the gap inequality with
constant `1` relative to the joint projection. -/
theorem spectralGap_one (l : List ι) (_hl : l ≠ []) (f : X → ℝ) :
    rhoInner F.weight f (-(F.gen l f)) ≥
      1 * rhoInner F.weight (f - F.projList l f) (f - F.projList l f) := by
  rw [F.dirichletForm_eq, one_mul]
  exact F.var_le_sum l f

end CommutingFamily

/-- The gap inequality has the same lower bound `1` for every nonempty index set
`Fin N`, every full enumeration of it, and every commuting projection family.
The constant is chosen outside the universal quantifiers. -/
theorem exists_uniform_spectralGap :
    ∃ lam : ℝ, 0 < lam ∧
      ∀ (N : ℕ), 0 < N → ∀ (l : List (Fin N)), l.Nodup → l.length = N →
        ∀ (X : Type u) [Fintype X] [Nonempty X] (F : CommutingFamily (Fin N) X)
          (f : X → ℝ),
        rhoInner F.weight f (-(F.gen l f)) ≥
          lam * rhoInner F.weight (f - F.projList l f) (f - F.projList l f) := by
  refine ⟨1, one_pos, ?_⟩
  intro N hN l _ hlen X _ _ F f
  have hl : l ≠ [] := by
    rintro rfl
    simp at hlen
    omega
  exact F.spectralGap_one l hl f

/-! ## The single-site heat-bath flow -/

variable [Fintype X]

/-- The formula `e^{-t} id + (1 − e^{-t}) E` for the single-site heat-bath flow.
For an orthogonal projection `E`, it gives the flow of `E − id`. -/
noncomputable def heatBathFlow (_ρ : GibbsWeight X) (P : (X → ℝ) → (X → ℝ)) (t : ℝ)
    (f : X → ℝ) : X → ℝ :=
  Real.exp (-t) • f + (1 - Real.exp (-t)) • P f

/-- The heat-bath flow at time zero is the identity. -/
theorem heatBathFlow_zero (ρ : GibbsWeight X) (P : (X → ℝ) → (X → ℝ)) (f : X → ℝ) :
    heatBathFlow ρ P 0 f = f := by
  simp [heatBathFlow]

/-- The one-step composition identity behind the semigroup law. -/
theorem heatBathFlow_step (ρ : GibbsWeight X) {P : (X → ℝ) → (X → ℝ)}
    (hP : IsOrthProj ρ P) (a b : ℝ) (f : X → ℝ) :
    (a * b) • f + (1 - a * b) • P f
      = a • (b • f + (1 - b) • P f) + (1 - a) • P (b • f + (1 - b) • P f) := by
  have hPlin : P (b • f + (1 - b) • P f) = P f := by
    rw [hP.map_add, hP.map_smul, hP.map_smul, hP.idem, ← add_smul]
    have h : b + (1 - b) = (1 : ℝ) := by ring
    rw [h, one_smul]
  rw [hPlin]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply]
  ring

/-- The flow is a one-parameter semigroup. -/
theorem heatBathFlow_add (ρ : GibbsWeight X) {P : (X → ℝ) → (X → ℝ)}
    (hP : IsOrthProj ρ P) (s t : ℝ) (f : X → ℝ) :
    heatBathFlow ρ P (s + t) f = heatBathFlow ρ P s (heatBathFlow ρ P t f) := by
  have hexp : Real.exp (-(s + t)) = Real.exp (-s) * Real.exp (-t) := by
    rw [show -(s + t) = -s + -t by ring, Real.exp_add]
  unfold heatBathFlow
  rw [hexp]
  exact heatBathFlow_step (P := P) ρ hP (Real.exp (-s)) (Real.exp (-t)) f

/-- The heat-bath flow fixes the unit observable. -/
theorem heatBathFlow_unital (ρ : GibbsWeight X) {P : (X → ℝ) → (X → ℝ)}
    (hunit : P (fun _ => (1 : ℝ)) = fun _ => 1) (t : ℝ) :
    heatBathFlow ρ P t (fun _ => (1 : ℝ)) = fun _ => 1 := by
  unfold heatBathFlow
  rw [hunit, ← add_smul]
  have h : Real.exp (-t) + (1 - Real.exp (-t)) = (1 : ℝ) := by ring
  rw [h, one_smul]

/-- The heat-bath flow is self-adjoint for `⟨·,·⟩_ρ`. -/
theorem heatBathFlow_adjoint (ρ : GibbsWeight X) {P : (X → ℝ) → (X → ℝ)}
    (hP : IsOrthProj ρ P) (t : ℝ) (f g : X → ℝ) :
    rhoInner ρ (heatBathFlow ρ P t f) g = rhoInner ρ f (heatBathFlow ρ P t g) := by
  unfold heatBathFlow
  rw [rhoInner_add_left, rhoInner_smul_left, rhoInner_smul_left, hP.adjoint,
    rhoInner_add_right, rhoInner_smul_right, rhoInner_smul_right]

/-- The heat-bath flow fixes the range of the orthogonal projection. -/
theorem heatBathFlow_fixed (ρ : GibbsWeight X) {P : (X → ℝ) → (X → ℝ)}
    (hP : IsOrthProj ρ P) (t : ℝ) (f : X → ℝ) :
    heatBathFlow ρ P t (P f) = P f := by
  unfold heatBathFlow
  rw [hP.idem, ← add_smul]
  have h : Real.exp (-t) + (1 - Real.exp (-t)) = (1 : ℝ) := by ring
  rw [h, one_smul]

/-- The residual of the heat-bath formula relative to the supplied map is multiplied
by `e^{-t}`. -/
theorem heatBathFlow_sub_eq (ρ : GibbsWeight X) (P : (X → ℝ) → (X → ℝ)) (t : ℝ)
    (f : X → ℝ) :
    heatBathFlow ρ P t f - P f = Real.exp (-t) • (f - P f) := by
  funext x
  simp only [heatBathFlow, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- The square-root gauge is compatible with scalar multiplication. -/
theorem gauge_smul (ρ : GibbsWeight X) (c : ℝ) (f : X → ℝ) :
    ρ.gauge (c • f) = c • ρ.gauge f := by
  unfold GibbsWeight.gauge
  rw [← map_smul]
  congr 1
  funext x
  simp only [Pi.smul_apply]
  ring

/-- The `ρ`-weighted norm is homogeneous. -/
theorem rhoNorm_smul (ρ : GibbsWeight X) (c : ℝ) (f : X → ℝ) :
    rhoNorm ρ (c • f) = |c| * rhoNorm ρ f := by
  unfold rhoNorm
  rw [gauge_smul, norm_smul, Real.norm_eq_abs]

/-- The distance to the projected observable is scaled by exactly `e^{-t}`. -/
theorem heatBathFlow_decay (ρ : GibbsWeight X) (P : (X → ℝ) → (X → ℝ)) (t : ℝ)
    (f : X → ℝ) :
    rhoNorm ρ (heatBathFlow ρ P t f - P f) = Real.exp (-t) * rhoNorm ρ (f - P f) := by
  rw [heatBathFlow_sub_eq ρ P t f, rhoNorm_smul, abs_of_pos (Real.exp_pos _)]

/-- Uniform exponential decay relative to an orthogonal projection:
for every nonempty finite configuration space, every Gibbs weight, and every
orthogonal projection, the distance to the projected observable at `t ≥ 0` is at most
`e^{-t}` times the initial distance (witness `C = 1`). -/
theorem exists_uniform_heatBath_decay :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type u) [Fintype X] [Nonempty X] (ρ : GibbsWeight X)
        (P : (X → ℝ) → (X → ℝ)), IsOrthProj ρ P →
        ∀ (t : ℝ), 0 ≤ t → ∀ f : X → ℝ,
        rhoNorm ρ (heatBathFlow ρ P t f - P f) ≤ C * Real.exp (-t) * rhoNorm ρ (f - P f) := by
  refine ⟨1, one_pos, ?_⟩
  intro X _ _ ρ P _ t _ f
  rw [heatBathFlow_decay, one_mul]

end Qatlib.Papers.CommGibbsSamp14.GibbsStructure
