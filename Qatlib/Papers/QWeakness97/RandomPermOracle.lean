/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWeakness97.OracleCostBridge
public import Qatlib.Papers.QWeakness97.MainResults.PermCoupling
public import Qatlib.Concepts.CircuitLang.XorOracle
public import Qatlib.Concepts.QPrograms.OracleBridge
public import Qatlib.Concepts.QPrograms.QueryBilling
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

@[expose] public section

/-!
# Theorem 3.6: random permutation-oracle draw and transposition coupling

Second slice of the QWeakness97 line for Theorem 3.6 (Theorem 3.6 of quant-ph/9701001v1):
the random permutation-oracle draw - the uniform law on the bijective truth tables of a
finite oracle domain - together with the first exchange/coupling lemmas around it, in the
repo's public `FinDist` idiom.

* Exchange: composing a fixed update permutation in front of a uniformly drawn oracle
  preserves every expectation (`permOracleDraw_update`) and preserves the uniform law
  itself (`mapDistEquiv_permOracleDraw_update`); the engine is that the update map is a
  bijection of the oracle space (`permUpdateEquiv`, `sum_permUpdate`).
* Coordinate uniformity: every single truth-table entry `σ w` of the drawn oracle, and
  every inverse entry `σ⁻¹ w`, is uniform (`permOracleDraw_expect_coord`,
  `permOracleDraw_expect_coord_symm`).
* Transposition coupling to `Qatlib.Papers.QWeakness97.MainResults.PermCoupling`: the in-place action of a
  `chainPerm`-updated oracle decomposes as the previous oracle action composed with the
  update's action (`permAct_trans`, `permAct_chainPerm_succ`); the chain-order update
  `swap x y ∘ₑ σ` disagrees with `σ` exactly on the two swapped inputs - the atomic form
  of `differScope` (`differSet_updateSwap`) - while the dual output-side update
  `σ ∘ₑ swap x y` disagrees exactly on the preimage of the swapped pair
  (`differSet_updateSwap_preim`, `card_differSet_updateSwap_preim`); and averaged over
  the draw, the mass a fixed state places on that preimage scope is exactly `2/|I|` of
  the state's total mass (`permOracleDraw_hybridCharge`) - the fair-share estimate one
  hybrid step needs.
* Word-layer link to the deterministic cost bridge: under any law on truth tables,
  the query accounting of an execution description is invariant under oracle resampling -
  pointwise for oracle-adaptive descriptions (`adaptiveResampleBill`), and the resampled
  standard-oracle bridge keeps expected bills equal and every drawn oracle's trajectory
  execution unitary (`stdOracleResampleBridge`, `expect_trajQueryCount_inv`).

Everything here is a finite expectation identity or a finite set identity. This is NOT
Theorem 3.6 and no part of it: no probability-one transport to a machine that must succeed
for all oracles, no countable-QTM or all-lengths uniformity, no hybrid chain assembled
over several steps, no mixed-schedule distance estimate, no NP∩coNP or BQTime statement,
and no asymptotic reading of the finite identities (a finite identity is never an
asymptotic statement, per the design document's four-aspect conclusion-type criteria). The
in-place permutation action remains the restricted model of `Qatlib.Papers.QWeakness97.MainResults.PermCoupling`; no
bridge from the source paper's QTM queries to the three-block register `OReg` is claimed,
and no complexity separation is claimed or implied.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CircuitLang.QueryWords
open Qatlib.Concepts.CircuitLang.XorOracle
open Qatlib.Concepts.QPrograms.QueryBilling
open Qatlib.Concepts.QPrograms.OracleBridge
open Qatlib.Papers.QWeakness97.OracleCostBridge
open Qatlib.Papers.QWeakness97.MainResults.PermCoupling
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QWeakness97.RandomPermOracle

/-! ## The uniform law on a finite oracle space -/

/-- The uniform law on a nonempty finite type: every oracle of the space carries the same
mass `|X|⁻¹`. -/
noncomputable def unifDist (X : Type) [Fintype X] [Nonempty X] : FinDist X where
  prob _ := (Fintype.card X : ℝ)⁻¹
  nonneg := fun _ => by positivity
  sum_one := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_inv_cancel₀]
    exact_mod_cast (Fintype.card_pos).ne'

/-- Every single oracle of the space carries the same mass. -/
theorem unifDist_prob {X : Type} [Fintype X] [Nonempty X] (x : X) :
    (unifDist X).prob x = (Fintype.card X : ℝ)⁻¹ := rfl

/-- The pushforward of a finite law along a bijection of the sample space: the mass of a
drawn-and-updated oracle is the mass the original law puts on its unique preimage. -/
def mapDistEquiv {X : Type} [Fintype X] (p : FinDist X) (e : X ≃ X) : FinDist X where
  prob y := p.prob (e.symm y)
  nonneg := fun y => p.nonneg _
  sum_one := by
    show (∑ y : X, p.prob (e.symm y)) = 1
    rw [Equiv.sum_comp e.symm p.prob]
    exact p.sum_one

/-- Finite laws are determined by their point masses. -/
private theorem finDist_eq_of_prob {X : Type} [Fintype X] {p q : FinDist X}
    (h : ∀ x, p.prob x = q.prob x) : p = q := by
  obtain ⟨pp, hpp, hps⟩ := p
  obtain ⟨qq, hqq, hqs⟩ := q
  have hppq : pp = qq := funext h
  subst hppq
  rfl

/-- The uniform law is invariant under any bijective reindexing of its sample space. -/
theorem mapDistEquiv_unifDist {X : Type} [Fintype X] [Nonempty X] (e : X ≃ X) :
    mapDistEquiv (unifDist X) e = unifDist X :=
  finDist_eq_of_prob fun _ => rfl

/-! ## The random permutation-oracle draw and the exchange lemma -/

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The oracle-update map of the transposition chain: composing a fixed update `τ` in front
of a drawn oracle - exactly the operation by which `chainPerm` extends its chain. -/
def permUpdateEquiv (τ : I ≃ I) : Equiv.Perm I ≃ Equiv.Perm I where
  toFun σ := τ.trans σ
  invFun σ := τ.symm.trans σ
  left_inv σ := by
    show τ.symm.trans (τ.trans σ) = σ
    rw [← Equiv.trans_assoc, Equiv.symm_trans_self, Equiv.refl_trans]
  right_inv σ := by
    show τ.trans (τ.symm.trans σ) = σ
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]

/-- Updating is a bijection of the oracle space: summing any real functional over updated
oracles is summing it over all oracles. -/
theorem sum_permUpdate (τ : I ≃ I) (F : Equiv.Perm I → ℝ) :
    ∑ σ, F ((permUpdateEquiv τ) σ) = ∑ σ, F σ :=
  Fintype.sum_equiv (permUpdateEquiv τ) (fun σ => F ((permUpdateEquiv τ) σ)) F fun _ => rfl

/-- The random permutation-oracle draw of Theorem 3.6: the uniform law on the permutation
oracles of the finite space `I`, that is, on the bijective truth tables `y ↦ σ y`. -/
noncomputable def permOracleDraw : FinDist (Equiv.Perm I) :=
  unifDist _

/-- The point-mass formula of the draw. -/
theorem permOracleDraw_prob (σ : Equiv.Perm I) :
    (permOracleDraw (I := I)).prob σ = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹ := rfl

/-- Expectations under the draw are uniform averages: the constant point mass factors out
of the billing sum. -/
theorem permOracleDraw_expect_eq (h : Equiv.Perm I → ℝ) :
    (permOracleDraw (I := I)).expect h
      = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹ * ∑ σ, h σ := by
  show (∑ σ : Equiv.Perm I, (permOracleDraw (I := I)).prob σ * h σ) = _
  have hmass : (∑ σ : Equiv.Perm I, (permOracleDraw (I := I)).prob σ * h σ)
      = ∑ σ : Equiv.Perm I, ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹ * h σ :=
    Finset.sum_congr rfl fun σ _ => by rw [permOracleDraw_prob]
  rw [hmass]
  exact (Finset.mul_sum Finset.univ h _).symm

/-- Expectations of a finite law are invariant under reindexing the sample space by a
bijection that carries the point masses. -/
theorem expect_reindex {X : Type} [Fintype X] (p : FinDist X) (e : X ≃ X)
    (hmass : ∀ σ, p.prob (e σ) = p.prob σ) (F : X → ℝ) :
    p.expect (fun σ => F (e σ)) = p.expect F := by
  show (∑ σ : X, p.prob σ * F (e σ)) = (∑ σ : X, p.prob σ * F σ)
  calc (∑ σ : X, p.prob σ * F (e σ))
      = (∑ σ : X, p.prob (e σ) * F (e σ)) :=
        Finset.sum_congr rfl fun σ _ => by rw [hmass σ]
    _ = (∑ σ : X, p.prob σ * F σ) :=
        Fintype.sum_equiv e (fun σ => p.prob (e σ) * F (e σ))
          (fun σ => p.prob σ * F σ) fun _ => rfl

/-- **Exchange lemma (expectation form).** Averaging any real functional over the uniform
permutation-oracle draw is unchanged by a fixed oracle update `τ`: the updated oracle,
sampled through the original draw, carries the same averages as a fresh draw. -/
theorem permOracleDraw_update (τ : I ≃ I) (F : Equiv.Perm I → ℝ) :
    (permOracleDraw (I := I)).expect (fun σ => F ((permUpdateEquiv τ) σ))
      = (permOracleDraw (I := I)).expect F :=
  expect_reindex (permOracleDraw (I := I)) (permUpdateEquiv τ)
    (fun σ => by rw [permOracleDraw_prob, permOracleDraw_prob]) F

/-- **Exchange lemma (distribution form).** Precomposing a uniformly drawn permutation
oracle with a fixed update permutation yields a uniformly drawn permutation oracle again:
the pushforward of the uniform permutation-oracle draw along the oracle-update map is the
draw itself. This is the measure-preservation step the hybrid argument of Theorem 3.6
attaches to each oracle update. -/
theorem mapDistEquiv_permOracleDraw_update (τ : I ≃ I) :
    mapDistEquiv (permOracleDraw (I := I)) (permUpdateEquiv τ) = permOracleDraw (I := I) :=
  mapDistEquiv_unifDist _

/-- **Coordinate uniformity of the draw.** Every single entry `σ w` of the drawn oracle's
truth table is uniform: the expected value of any real functional of `σ w` under the
permutation-oracle draw is its uniform average over `I`. -/
theorem permOracleDraw_expect_coord [Nonempty I] (w : I) (g : I → ℝ) :
    (permOracleDraw (I := I)).expect (fun σ => g (σ w))
      = (∑ v, g v) / ((Fintype.card I : ℕ) : ℝ) := by
  have hindep : ∀ u v : I, (∑ σ : Equiv.Perm I, g (σ u)) = (∑ σ : Equiv.Perm I, g (σ v)) := by
    intro u v
    by_cases huv : u = v
    · rw [huv]
    · have hpt : ∀ σ : Equiv.Perm I,
          g (((permUpdateEquiv (Equiv.swap u v)) σ) u) = g (σ v) := by
        intro σ
        show g (((Equiv.swap u v).trans σ) u) = g (σ v)
        rw [Equiv.trans_apply, Equiv.swap_apply_left]
      calc (∑ σ : Equiv.Perm I, g (σ u))
          = (∑ σ : Equiv.Perm I, g (((permUpdateEquiv (Equiv.swap u v)) σ) u)) :=
            (sum_permUpdate (Equiv.swap u v) (fun π => g (π u))).symm
        _ = (∑ σ : Equiv.Perm I, g (σ v)) := Finset.sum_congr rfl fun σ _ => hpt σ
  have hNne : ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have hnne : ((Fintype.card I : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos).ne'
  have hcount : ((Fintype.card I : ℕ) : ℝ) * (∑ σ : Equiv.Perm I, g (σ w))
      = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) * (∑ v, g v) := by
    have hsplit : (∑ u : I, ∑ σ : Equiv.Perm I, g (σ u))
        = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) * (∑ v, g v) := by
      rw [Finset.sum_comm]
      calc (∑ σ : Equiv.Perm I, ∑ u : I, g (σ u))
          = (∑ σ : Equiv.Perm I, ∑ v : I, g v) :=
            Finset.sum_congr rfl fun σ _ => Equiv.sum_comp σ g
        _ = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) * (∑ v, g v) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    calc ((Fintype.card I : ℕ) : ℝ) * (∑ σ : Equiv.Perm I, g (σ w))
        = (∑ u : I, ∑ σ : Equiv.Perm I, g (σ w)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = (∑ u : I, ∑ σ : Equiv.Perm I, g (σ u)) :=
            Finset.sum_congr rfl fun u _ => hindep w u
      _ = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) * (∑ v, g v) := hsplit
  have hCsol : (∑ σ : Equiv.Perm I, g (σ w))
      = ((Fintype.card I : ℕ) : ℝ)⁻¹
          * (((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) * (∑ v, g v)) := by
    rw [← hcount, inv_mul_cancel_left₀ hnne]
  have hE : (permOracleDraw (I := I)).expect (fun σ => g (σ w))
      = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹ * (∑ σ : Equiv.Perm I, g (σ w)) :=
    permOracleDraw_expect_eq _
  rw [hE, hCsol]
  calc ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹
          * (((Fintype.card I : ℕ) : ℝ)⁻¹
            * (((Fintype.card (Equiv.Perm I) : ℕ) : ℝ) * (∑ v, g v)))
      = ((Fintype.card I : ℕ) : ℝ)⁻¹ * ((((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹
            * ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)) * (∑ v, g v)) := by
        ring
    _ = ((Fintype.card I : ℕ) : ℝ)⁻¹ * (∑ v, g v) := by
          rw [inv_mul_cancel₀ hNne, one_mul]
    _ = (∑ v, g v) / ((Fintype.card I : ℕ) : ℝ) := (div_eq_inv_mul _ _).symm

/-- The inverse-table involution of the permutation oracle space: reading a drawn oracle
through its inverse truth table is a bijection of the oracle space. -/
def permSymmEquiv : Equiv.Perm I ≃ Equiv.Perm I where
  toFun σ := σ.symm
  invFun σ := σ.symm
  left_inv σ := σ.symm_symm
  right_inv σ := σ.symm_symm

/-- Coordinate uniformity for preimages: every single entry `σ⁻¹ w` of the drawn oracle's
inverse truth table is uniform as well. -/
theorem permOracleDraw_expect_coord_symm [Nonempty I] (w : I) (g : I → ℝ) :
    (permOracleDraw (I := I)).expect (fun σ => g (σ.symm w))
      = (∑ v, g v) / ((Fintype.card I : ℕ) : ℝ) := by
  have hre : (permOracleDraw (I := I)).expect (fun σ => g (σ.symm w))
      = (permOracleDraw (I := I)).expect (fun ρ => g (ρ w)) :=
    expect_reindex (permOracleDraw (I := I)) permSymmEquiv
      (fun σ => by rw [permOracleDraw_prob, permOracleDraw_prob]) (fun ρ => g (ρ w))
  rw [hre]
  exact permOracleDraw_expect_coord w g

/-! ## The transposition coupling of the in-place permutation action -/

omit [Fintype I] [DecidableEq I] in
/-- The transposition-swap identity for the in-place permutation action of
`Qatlib.Papers.QWeakness97.MainResults.PermCoupling`: the action of the updated oracle `ρ₁ ∘ₑ ρ₂` splits into the
action of `ρ₂` followed by the action of `ρ₁` - one oracle update peels off one
permutation layer. This is the hybrid decomposition identity of the transposition
coupling. -/
theorem permAct_trans (ρ₁ ρ₂ : I ≃ I) (ψ : QState I) :
    permAct (ρ₁.trans ρ₂) ψ = permAct ρ₂ (permAct ρ₁ ψ) := by
  funext x
  show ψ ((ρ₁.trans ρ₂).symm x) = ψ (ρ₁.symm (ρ₂.symm x))
  rw [Equiv.symm_trans, Equiv.trans_apply]

omit [Fintype I] in
/-- One `chainPerm` step under the swap identity: the in-place action of the chain's
`k+1`-st oracle decomposes as the `k`-th oracle's action composed with the transposition
action of `swap (xs k) (xs (k+1))`. -/
theorem permAct_chainPerm_succ (π0 : I ≃ I) (xs : ℕ → I) (k : ℕ) (ψ : QState I) :
    permAct (chainPerm π0 xs (k + 1)) ψ
      = permAct (chainPerm π0 xs k) (permAct (Equiv.swap (xs k) (xs (k + 1))) ψ) :=
  permAct_trans _ _ ψ

/-- The disagreement scope of one chain-order transposition update: precomposing the
oracle `σ` with the transposition `swap x y` (with `x ≠ y`) - exactly the update by which
`chainPerm` extends its chain - changes the oracle's answers exactly on the two swapped
inputs `x` and `y`. This is the one-step (atomic) form of the fresh-string scope
`differScope` of the hybrid argument. -/
theorem differSet_updateSwap (σ : I ≃ I) {x y : I} (hxy : x ≠ y) :
    differSet ((Equiv.swap x y).trans σ) σ = {x, y} := by
  ext z
  have hmem : z ∈ differSet ((Equiv.swap x y).trans σ) σ
      ↔ (σ (Equiv.swap x y z) ≠ σ z) := by
    constructor
    · intro h
      have h2 := (Finset.mem_filter.mp h).2
      rw [Equiv.trans_apply] at h2
      exact h2
    · intro h
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.trans_apply]
      exact h
  rw [hmem, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hne
    by_contra hz
    have hx : z ≠ x := fun h => hz (Or.inl h)
    have hy : z ≠ y := fun h => hz (Or.inr h)
    rw [Equiv.swap_apply_of_ne_of_ne hx hy] at hne
    exact hne rfl
  · rintro (hz | hz)
    · subst hz
      rw [Equiv.swap_apply_left]
      exact fun hc => hxy (σ.injective hc).symm
    · subst hz
      rw [Equiv.swap_apply_right]
      exact fun hc => hxy (σ.injective hc)

/-- The disagreement scope of the dual output-side transposition update: postcomposing
the oracle `σ` with the transposition `swap x y` (with `x ≠ y`) - equivalently, updating
the inverse truth table by a transposition on its inputs - changes the oracle's answers
exactly on the preimages of the two swapped points. -/
theorem differSet_updateSwap_preim (σ : I ≃ I) {x y : I} (hxy : x ≠ y) :
    differSet (σ.trans (Equiv.swap x y)) σ = Finset.image σ.symm {x, y} := by
  ext z
  have hmem : z ∈ differSet (σ.trans (Equiv.swap x y)) σ
      ↔ (Equiv.swap x y (σ z) ≠ σ z) := by
    constructor
    · intro h
      have h2 := (Finset.mem_filter.mp h).2
      rw [Equiv.trans_apply] at h2
      exact h2
    · intro h
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.trans_apply]
      exact h
  rw [hmem]
  constructor
  · intro hne
    rcases eq_or_ne (σ z) x with h | h
    · refine Finset.mem_image.mpr ⟨x, Finset.mem_insert.mpr (Or.inl rfl), ?_⟩
      exact (Equiv.symm_apply_eq (e := σ)).2 h.symm
    · refine Finset.mem_image.mpr ⟨y, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl)), ?_⟩
      refine (Equiv.symm_apply_eq (e := σ)).2 ?_
      by_contra h2
      exact hne (Equiv.swap_apply_of_ne_of_ne h (Ne.symm h2))
  · intro hzmem
    obtain ⟨w, hw, hz⟩ := Finset.mem_image.mp hzmem
    rcases Finset.mem_insert.mp hw with hw' | hw'
    · have hxz : σ z = x := by rw [← hz, hw']; exact Equiv.apply_symm_apply σ x
      rw [hxz, Equiv.swap_apply_left]
      exact fun hc => hxy hc.symm
    · have hwy : w = y := Finset.mem_singleton.mp hw'
      have hyz : σ z = y := by rw [← hz, hwy]; exact Equiv.apply_symm_apply σ y
      rw [hyz, Equiv.swap_apply_right]
      exact fun hc => hxy hc

/-- A single output-side transposition update makes the oracle disagree with its old self
on exactly two points. -/
theorem card_differSet_updateSwap_preim (σ : I ≃ I) {x y : I} (hxy : x ≠ y) :
    (differSet (σ.trans (Equiv.swap x y)) σ).card = 2 := by
  rw [differSet_updateSwap_preim σ hxy, Finset.card_image_of_injOn
    (fun u _ v _ h => Equiv.injective σ.symm h),
    Finset.card_insert_of_notMem (fun hc => hxy (Finset.mem_singleton.mp hc)),
    Finset.card_singleton]

/-- **Expected hybrid charge of one transposition update under the random
permutation-oracle draw.** Averaged over a uniform oracle `σ`, the state mass that a fixed
amplitude vector places on the disagreement scope of the output-side update
`σ ∘ₑ swap x y` is exactly `2/|I|` times the vector's total mass - the fair-share estimate
one hybrid step of Theorem 3.6 attaches to a transposition, here sourced from the oracle
draw itself through the uniformity of the inverse truth table. -/
theorem permOracleDraw_hybridCharge [Nonempty I] {x y : I} (hxy : x ≠ y) (ψ : QState I) :
    (permOracleDraw (I := I)).expect (fun σ =>
        ∑ z ∈ differSet (σ.trans (Equiv.swap x y)) σ, ‖ψ z‖ ^ 2)
      = 2 / ((Fintype.card I : ℕ) : ℝ) * (∑ z : I, ‖ψ z‖ ^ 2) := by
  have hper : ∀ σ : Equiv.Perm I,
      ∑ z ∈ differSet (σ.trans (Equiv.swap x y)) σ, ‖ψ z‖ ^ 2
        = ∑ v ∈ ({x, y} : Finset I), ‖ψ (σ.symm v)‖ ^ 2 := by
    intro σ
    rw [differSet_updateSwap_preim σ hxy,
      Finset.sum_image (fun u _ v _ h => Equiv.injective σ.symm h)]
  have hinner : ∀ v ∈ ({x, y} : Finset I),
      ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹
          * (∑ σ : Equiv.Perm I, ‖ψ (σ.symm v)‖ ^ 2)
        = (∑ z : I, ‖ψ z‖ ^ 2) / ((Fintype.card I : ℕ) : ℝ) := by
    intro v _
    have h0 := permOracleDraw_expect_coord_symm (I := I) v (fun z => ‖ψ z‖ ^ 2)
    rw [permOracleDraw_expect_eq] at h0
    exact h0
  have hcard2 : (({x, y} : Finset I).card : ℝ) = 2 := by
    have hc : ({x, y} : Finset I).card = 2 := by
      rw [Finset.card_insert_of_notMem
        (fun hq => hxy (Finset.mem_singleton.mp hq)), Finset.card_singleton]
    exact_mod_cast hc
  calc (permOracleDraw (I := I)).expect (fun σ =>
          ∑ z ∈ differSet (σ.trans (Equiv.swap x y)) σ, ‖ψ z‖ ^ 2)
      = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹
          * (∑ σ : Equiv.Perm I, ∑ v ∈ ({x, y} : Finset I), ‖ψ (σ.symm v)‖ ^ 2) :=
        (permOracleDraw_expect_eq (fun σ =>
          ∑ z ∈ differSet (σ.trans (Equiv.swap x y)) σ, ‖ψ z‖ ^ 2)).trans
          (congrArg (fun S : ℝ => ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹ * S)
            (Finset.sum_congr rfl fun σ _ => hper σ))
    _ = ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹
          * (∑ v ∈ ({x, y} : Finset I), ∑ σ : Equiv.Perm I, ‖ψ (σ.symm v)‖ ^ 2) := by
        rw [Finset.sum_comm]
    _ = (∑ v ∈ ({x, y} : Finset I),
          ((Fintype.card (Equiv.Perm I) : ℕ) : ℝ)⁻¹
            * (∑ σ : Equiv.Perm I, ‖ψ (σ.symm v)‖ ^ 2)) := Finset.mul_sum _ _ _
    _ = (∑ v ∈ ({x, y} : Finset I), (∑ z : I, ‖ψ z‖ ^ 2) / ((Fintype.card I : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun v hv => hinner v hv
    _ = (({x, y} : Finset I).card : ℝ)
          * ((∑ z : I, ‖ψ z‖ ^ 2) / ((Fintype.card I : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 / ((Fintype.card I : ℕ) : ℝ) * (∑ z : I, ‖ψ z‖ ^ 2) := by
          rw [hcard2]
          ring

/-! ## Resampling invariance of the word-layer query bill -/

/-- The random standard-oracle draw at the word layer: the uniform law on the truth tables
`Addr a → Bool` of the standard XOR oracle register `OReg a w`. -/
noncomputable def stdOracleDraw (a : ℕ) : FinDist (Addr a → Bool) :=
  haveI : Nonempty (Addr a → Bool) := ⟨fun _ => true⟩
  unifDist _

/-- Oracle-resampling invariance of the word-side query accounting: for a fixed execution
description (step-word policy and outcome list) the trajectory word's public query count is
a constant of the draw - under ANY law on truth tables, its expected value is the
deterministic count itself. Resampling randomizes the oracle's answers, never the bill. -/
theorem expect_trajQueryCount_inv {O : Type} {a w : ℕ} (μ : FinDist (Addr a → Bool))
    (word : List O → Circuit (OReg a w)) (os : List O) :
    μ.expect (fun _ => (QueryCount (trajWord word [] os) : ℝ))
      = QueryCount (trajWord word [] os) :=
  FinDist.expect_const μ _

/-- Pointwise-bridge transport to expectations for oracle-adaptive executions: when the
execution description itself may react to the drawn truth table - the policy's step words
and the observed outcome list both depend on `f` - and every `f` bills its own trajectory
under the explicit cost model `hmodel`, the expected program-side bill under ANY oracle-draw
law equals the expected word-side public query count of the executed trajectory words. -/
theorem adaptiveResampleBill {O : Type} {a w : ℕ} (μ : FinDist (Addr a → Bool))
    (word : (Addr a → Bool) → List O → Circuit (OReg a w))
    (cost : (Addr a → Bool) → List O → ℕ)
    (hmodel : ∀ f h, cost f h = QueryCount (word f h))
    (os : (Addr a → Bool) → List O) :
    μ.expect (fun f => (progQCost (cost f) (os f) : ℝ))
      = μ.expect (fun f => (QueryCount (trajWord (word f) [] (os f)) : ℝ)) := by
  show (∑ f, μ.prob f * (progQCost (cost f) (os f) : ℝ))
      = (∑ f, μ.prob f * (QueryCount (trajWord (word f) [] (os f)) : ℝ))
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  exact_mod_cast progBill_agreeTrajWord (word f) (cost f) (hmodel f) (os f)

/-- The resampling form of the standard-oracle cost bridge: under an arbitrary
oracle-draw law `μ` on truth tables and the explicit per-word cost model, an oracle-adaptive
execution keeps the expected program-side bill equal to the expected word-side query count
of its trajectory words, and every drawn truth table's trajectory word denotes a unitary
against that drawn `xorOracle f`. Finite bookkeeping identities in expectation form; no
asymptotic or separation statement is implied. -/
theorem stdOracleResampleBridge {O : Type} {a w : ℕ} (μ : FinDist (Addr a → Bool))
    (word : (Addr a → Bool) → List O → Circuit (OReg a w))
    (cost : (Addr a → Bool) → List O → ℕ)
    (hmodel : ∀ f h, cost f h = QueryCount (word f h))
    (hstep : ∀ f h, IsUnitaryCircuit (word f h))
    (os : (Addr a → Bool) → List O) :
    μ.expect (fun f => (progQCost (cost f) (os f) : ℝ))
      = μ.expect (fun f => (QueryCount (trajWord (word f) [] (os f)) : ℝ))
      ∧ ∀ f : Addr a → Bool, Denote (xorOracle f) (trajWord (word f) [] (os f))
          ∈ Matrix.unitaryGroup (OReg a w) ℂ :=
  ⟨adaptiveResampleBill μ word cost hmodel os,
    fun f => xorWord_uni f (trajWord_unitary (word f) (hstep f) [] (os f))⟩

end Qatlib.Papers.QWeakness97.RandomPermOracle
