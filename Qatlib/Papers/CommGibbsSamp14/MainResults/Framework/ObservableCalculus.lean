/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option backward.isDefEq.respectTransparency false

/-!
# Commuting Gibbs samplers — paper-layer observable calculus

Fixed source: M. J. Kastoryano and F. G. S. L. Brandão, *Quantum Gibbs Samplers: the
commuting case*, arXiv:1409.3435v3 (7 June 2016).  Equation and page numbers below refer
to the v3 PDF (local asset `assets/1409.3435.pdf`).

## Modelling scope

The paper works with the real Hilbert space of Hermitian observables equipped with the
`ρ`-weighted inner product `⟨f, g⟩_ρ` of Eq. (2).  Every analytic step of Sections V–VI
that this paper layer needs (the expansion of Eq. (63) in the proof of Proposition 20 and
the expansion of Eq. (95) in the proof of Theorem 26) uses only that Hilbert-space
structure together with the conditional expectations as self-adjoint contractions.  We
therefore model the observable space `𝒜_Λ` as an abstract `InnerProductSpace ℝ V` and
`expect` as the linear functional `f ↦ tr[ρ f]`.

Two ingredients are *not* reconstructed by this Hilbert-space model and are carried as
named data instead:

* complete positivity of maps (Definition 8(1)), through `CPMapData.IsCP`;
* the operator-algebra product — hence commutation `[Φ(i), Φ(j)] = 0` of a commuting
  potential — and the concrete partial trace `tr_A` of Eq. (13)/(26).  Structures such as
  `IsRLocalCommutingPotential` record these as hypotheses on the paper's objects; they are
  part of the definition of the objects, not consequences of the theorems stated over them.

The model is a paper-layer abstraction.  It is faithful to the logical form of every
statement (hypotheses and conclusions are those of the paper) but it does not replace a
concrete matrix/tensor-product instantiation, which is out of scope for this block.
-/

set_option autoImplicit false

namespace Qatlib.Papers.CommGibbsSamp14.MainResults.Framework

open scoped InnerProductSpace
open Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Region : Type*}

/-! ## The `ρ`-weighted covariance and conditional covariance -/

/-- Paper Eq. (5): the `ρ`-covariance
`Cov_ρ(f,g) = ⟨f,g⟩_ρ − tr[ρf] tr[ρg]`. -/
noncomputable def cov (expect : V → ℝ) (f g : V) : ℝ :=
  ⟪f, g⟫_ℝ - expect f * expect g

/-- Paper Eq. (5): the `ρ`-variance `Var_ρ(f) = Cov_ρ(f,f)`. -/
noncomputable def var (expect : V → ℝ) (f : V) : ℝ := cov expect f f

/-- Paper Eq. (36): the conditional covariance `Cov_A(f,g) = ⟨f − E_A f, g − E_A g⟩_ρ`. -/
noncomputable def condCov (E : V → V) (f g : V) : ℝ :=
  ⟪f - E f, g - E g⟫_ℝ

/-- Paper Eq. (36)/(60): the conditional variance `Var_A(f) = ‖f − E_A f‖²_{2,ρ}`. -/
noncomputable def condVar (E : V → V) (f : V) : ℝ := condCov E f f

/-- Cond Var eq norm sq: the paper model identity or bound. -/
@[simp] lemma condVar_eq_norm_sq (E : V → V) (f : V) :
    condVar E f = ‖f - E f‖ ^ 2 := by
  rw [condVar, condCov, real_inner_self_eq_norm_sq]

/-- Cond Var nonneg: the paper model identity or bound. -/
lemma condVar_nonneg (E : V → V) (f : V) : 0 ≤ condVar E f := by
  rw [condVar_eq_norm_sq]; positivity

/-! ## Lattice regions (Section II-A) -/

/-- Region operations on the finite lattice `Λ ⊆ ℤ^d`.

`subset B A` means `B ⊆ A`; `gapDist A B` is the paper's `d(B \ A, A \ B)` appearing in
Eq. (38); `complementDist B A` is `d(B, Λ \ A)` of Eq. (57); `boundary A` is `A_∂ = A ∪ ∂A`
of Eq. (26). -/
class RegionOps (Region : Type*) where
  /-- the full lattice `Λ` -/
  full : Region
  union : Region → Region → Region
  inter : Region → Region → Region
  /-- `A_∂ = A ∪ ∂A` (Eq. (26)) -/
  boundary : Region → Region
  /-- `B ⊆ A` -/
  subset : Region → Region → Prop
  /-- `A ∩ B ≠ ∅` -/
  overlap : Region → Region → Prop
  /-- `d(B \ A, A \ B)` of Eq. (38) -/
  gapDist : Region → Region → ℝ
  /-- `d(B, Λ \ A)` of Eq. (57) -/
  complementDist : Region → Region → ℝ

/-! ## The paper's data bundle -/

/-- The data of one finite lattice system: the `ρ`-expectation functional, the unit
observable `1`, the two families of conditional expectations (`E^ρ` and `E^L`), the two
Gibbs samplers (`L^D` and `L^H`) indexed by subregion, the support distance `d(Σ_f, Σ_g)`
of Section II-A, a radius-`r` neighbourhood map, and the support/identity predicates used
to phrase locality and Eq. (13). -/
structure PaperSetup (V Region : Type*) where
  /-- `f ↦ tr[ρ f]` -/
  expect : V → ℝ
  /-- the unit observable `1` -/
  one : V
  /-- minimal conditional expectations `E^ρ_A` of Eq. (13) -/
  Eρ : Region → V → V
  /-- local Liouvillian projectors `E^L_A` of Eq. (12) -/
  EL : Region → V → V
  /-- Davies generators `L^D_A` of Eq. (30) -/
  LD : Region → V → V
  /-- Heat-Bath generators `L^H_A` of Eq. (34) -/
  LH : Region → V → V
  /-- support distance `d(Σ_f, Σ_g)` of Section II-A -/
  supportDist : V → V → ℝ
  /-- radius-`r` neighbourhood of a region -/
  nbrhd : Region → Region
  /-- `f` has support in the region `R` -/
  supportedIn : Region → V → Prop
  /-- `f` acts as the identity on the subsystem `A` (the range of `E^ρ_A`, Eq. (13)) -/
  actsIdentityOn : Region → V → Prop
  /-- the number of sites `|Λ|` -/
  sites : ℕ

/-! ## Clustering (Definitions 14 and 15) -/

/-- Definition 14, Eq. (37): `ρ` satisfies weak clustering with constants `c, ξ > 0`. -/
def WeakClustering (S : PaperSetup V Region) (c ξ : ℝ) : Prop :=
  0 < c ∧ 0 < ξ ∧
    ∀ f g : V, cov S.expect f g ≤ c * ‖f‖ * ‖g‖ * Real.exp (-(S.supportDist f g) / ξ)

/-- Definition 15, Eq. (38): `ρ` satisfies strong clustering with respect to the
conditional-expectation family `E`. -/
def StrongClustering [RegionOps Region] (E : Region → V → V) (c ξ : ℝ) : Prop :=
  0 < c ∧ 0 < ξ ∧
    ∀ (A B : Region) (f : V), RegionOps.overlap A B →
      condCov (E (RegionOps.union A B)) (E A f) (E B f) ≤
        c * ‖f‖ ^ 2 * Real.exp (-(RegionOps.gapDist A B) / ξ)

/-! ## Spectral gaps (Definitions 7 and 21) -/

/-- Definition 7, Eq. (10) and Definition 21, Eq. (66), in variational form: `λ` is a
spectral gap of `L` with conditional expectation `E` when `λ > 0` and
`⟨f, −L f⟩_ρ ≥ λ Var(f)` for every observable `f`. -/
def IsSpectralGap (L E : V → V) (lam : ℝ) : Prop :=
  0 < lam ∧ ∀ f : V, ⟪f, -(L f)⟫_ℝ ≥ lam * condVar E f

/-- "The gap is independent of the system size": one positive constant works for every
member of a family of lattices. -/
def HasSizeIndependentGap {ι : Type*} (L : ι → V → V) (E : ι → V → V) : Prop :=
  ∃ lam : ℝ, 0 < lam ∧ ∀ i : ι, ∀ f : V, ⟪f, -(L i f)⟫_ℝ ≥ lam * condVar (E i) f

/-- The conditional gap of Eq. (66)/(67) as an infimum. -/
noncomputable def conditionalGap (L E : V → V) : ℝ :=
  sInf {q : ℝ | ∃ f : V, 0 < condVar E f ∧ q = ⟪f, -(L f)⟫_ℝ / condVar E f}

/-! ## Local properties of Liouvillians (Definitions 5 and 6) -/

/-- Definition 5: `L` is locally reversible (satisfies detailed balance, Eq. (8)) with
respect to `ρ` for every restriction `A`. -/
def LocallyReversible (L : Region → V → V) : Prop :=
  ∀ (A : Region) (f g : V), ⟪f, L A g⟫_ℝ = ⟪L A f, g⟫_ℝ

/-- Definition 5: `L` is locally primitive — the kernel of `L_A` agrees with the fixed
space of `E_A`, i.e. `L_A f = 0` forces `f` to act only on the complement of `A`
(encoded as `f = E_A f`). -/
def LocallyPrimitive (L : Region → V → V) (E : Region → V → V) : Prop :=
  ∀ (A : Region) (f : V), L A f = 0 → f - E A f = 0

/-- Definition 6: `L` is frustration free — whenever `ρ` is stationary for the full
generator it is stationary for every restriction.  Stationarity of `ρ` for `L_A` reads
`tr[ρ L_A(g)] = 0` for all observables `g`. -/
def FrustrationFree [RegionOps Region] (expect : V → ℝ) (L : Region → V → V) : Prop :=
  (∀ g : V, expect (L RegionOps.full g) = 0) → ∀ (A : Region) (g : V), expect (L A g) = 0

/-- Locality: `L_A f` lies in the algebra of the radius-`r` neighbourhood of `A`
(condition saying that `E` on that neighbourhood fixes `L_A f`). -/
def IsLocalOn (L : Region → V → V) (E : Region → V → V) (nbrhd : Region → Region) : Prop :=
  ∀ (A : Region) (f : V), E (nbrhd A) (L A f) = L A f

/-! ## Complete positivity and conditional expectations (Definition 8) -/

/-- Carrier for complete positivity in the abstract `L²(ρ)` model: Definition 8(1) is
exposed as the predicate `IsCP`.  A concrete instantiation is expected to set
`IsCP E := CompletelyPositiveMapClass.IsCompletelyPositive E` for a matrix algebra. -/
class CPMapData (V : Type*) where
  IsCP : (V → V) → Prop

/-- Definition 8 of the paper: `E` is a conditional expectation of `ρ`, with complete
positivity (item 1), unitality (item 1), consistency (item 2), reversibility (item 3) and
monotonicity (item 4). -/
structure IsConditionalExpectation [CPMapData V] (expect : V → ℝ) (one : V)
    (E : V → V) : Prop where
  completelyPositive : CPMapData.IsCP E
  unital : E one = one
  consistent : ∀ f : V, expect (E f) = expect f
  reversible : ∀ f g : V, ⟪E f, g⟫_ℝ = ⟪f, E g⟫_ℝ
  monotone : ∀ (f : V) (n : ℕ), ⟪(E^[n]) f, f⟫_ℝ ≥ ⟪(E^[n + 1]) f, f⟫_ℝ

/-- Eq. (12): `E` is the local Liouvillian projector of `L` on `A`, i.e. the pointwise
`t → ∞` limit of a completely positive unital semigroup `t ↦ T t` with generator `L`.
Complete positivity and unitality of the limit are part of this defining data (the paper's
"complete positivity follows by construction"). -/
def IsLiouvillianProjector [CPMapData V] (one : V) (L E : V → V) : Prop :=
  ∃ T : ℝ → V → V,
    (∀ f : V, T 0 f = f) ∧
    (∀ (s t : ℝ) (f : V), T (s + t) f = T s (T t f)) ∧
    (∀ t : ℝ, CPMapData.IsCP (T t)) ∧
    (∀ t : ℝ, T t one = one) ∧
    (∀ f : V, Tendsto (fun t : ℝ => T t f) atTop (𝓝 (E f))) ∧
    (∀ f : V, HasDerivAt (fun t : ℝ => T t f) (L f) 0) ∧
    CPMapData.IsCP E ∧ E one = one

/-- `L` generates a completely positive unital semigroup `t ↦ e^{tL}`: there is a
semigroup of completely positive unital maps whose right derivative at `0` is `L`. -/
def GeneratesCPUnitalSemigroup [CPMapData V] (one : V) (L : V → V) : Prop :=
  ∃ T : ℝ → V → V,
    (∀ f : V, T 0 f = f) ∧
    (∀ (s t : ℝ) (f : V), T (s + t) f = T s (T t f)) ∧
    (∀ t : ℝ, CPMapData.IsCP (T t)) ∧
    (∀ t : ℝ, T t one = one) ∧
    (∀ f : V, HasDerivAt (fun t : ℝ => T t f) (L f) 0)

/-! ## Local indistinguishability (Definition 18) -/

/-- A projective conditional expectation: a conditional expectation that is idempotent
(the paper's `E^L` family, Definition 8 and Section III-A). -/
def IsProjectiveConditionalExpectation [CPMapData V] (expect : V → ℝ) (one : V)
    (E : V → V) : Prop :=
  IsConditionalExpectation expect one E ∧ ∀ f : V, E (E f) = E f

/-- `ρ` is a fixed point of the adjoint `E*` of `E`: `⟨E f, ρ⟩ = ⟨f, ρ⟩` for all `f`. -/
def IsFixedPointOfAdjoint (E : V → V) (ρ : V) : Prop :=
  ∀ f : V, ⟪E f, ρ⟫_ℝ = ⟪f, ρ⟫_ℝ

/-- Definition 18, Eq. (57): local indistinguishability of the conditional expectation
family `E`.  `restrictDist A B ρ σ` is the trace-norm distance `‖(ρ_A)_B − (σ_A)_B‖₁` of
the two restrictions to `B`; it is supplied together with the model. -/
def LocallyIndistinguishable [RegionOps Region] (E : Region → V → V)
    (restrictDist : Region → V → V → ℝ) (c ξ : ℝ) : Prop :=
  0 < c ∧ 0 < ξ ∧
    ∀ (A B : Region) (ρA σA : V), RegionOps.subset B A →
      IsFixedPointOfAdjoint (E A) ρA → IsFixedPointOfAdjoint (E A) σA →
        restrictDist B ρA σA ≤ c * Real.exp (-(RegionOps.complementDist B A) / ξ)

/-! ## Structure of a bounded commuting potential (Section IV) -/

/-- Data of an `r`-local bounded commuting potential `Φ : Λ → 𝒜_Λ` of Section IV.

* `term k` is `Φ(k)`, supported in the radius-`r` ball around `k` and bounded by `K`;
* `commutes` records pairwise commutation `[Φ(i), Φ(j)] = 0`.  Commutation is a
  statement about the operator-algebra product, which the Hilbert-space model does not
  reconstruct; it is carried here as part of the potential's defining data (paper,
  Section IV, immediately above Eq. (25)). -/
structure IsRLocalCommutingPotential (V Region : Type*) where
  /-- the local terms `Φ(k)` -/
  term : Region → V
  /-- the interaction range `r` -/
  range : ℕ
  /-- the bound `K` on `‖Φ(k)‖` -/
  bound : ℝ
  bound_pos : 0 < bound
  /-- pairwise commutation `[Φ(i), Φ(j)] = 0` (carried abstractly, see the docstring) -/
  commutes : Prop

end Qatlib.Papers.CommGibbsSamp14.MainResults.Framework
