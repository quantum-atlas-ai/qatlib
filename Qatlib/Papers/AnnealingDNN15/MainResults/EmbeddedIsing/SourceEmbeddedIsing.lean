/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AnnealingDNN15.MainResults.RbmEnergy.SourceRbmEnergy
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Chain embedding and Eq. (22): the ferromagnetic term cancels

Source: *Application of Quantum Annealing to Training of Deep Neural Networks*,
arXiv:1510.06356 (2015), fixed local PDF
`1510.06356.pdf` (SHA-256 `7c273ebf6340223d2ddbc2f0684298e9a16ed3cc89253d212008ae3e3e945f72`).
Section 3.2.2, Eqs. (19)–(22), pages 9–10.

The paper maps every logical RBM node to a *chain* of physical qubits and
penalizes disagreement inside a chain by a ferromagnetic coupling `J_FM > 0`
(Eq. (21)):

`E'' = E' - J_FM Σ_i Σ_{(k,l) ∈ emb{i}} S_i^(k) S_i^(l)`.

If (strict voting, threshold `r = 1`) every sample violating a chain constraint
is discarded before averaging, the only configurations that enter the sample
average are the chain-satisfying ones.  On every such configuration each
`S_i^(k) S_i^(l) = 1`, so the whole ferromagnetic term equals the constant
`-J_FM · (#chain edges)`; a common factor `exp(β J_FM #edges)` factors out of
both the numerator and the restricted partition function `Z`, and cancels:

`⟨v_i h_j⟩^{E''} ≅ ⟨v_i h_j⟩^E`   (Eq. (22)).

This module proves exactly that cancellation: for any observable `f` on the
finite physical configuration space, the Gibbs expectation restricted to the
chain-satisfying set is unchanged by adding any constant to the energy on that
set.  The approximation `≅` of the paper discards the exponentially small mass
of chain-violating configurations; here that is represented by the restriction
of the average to the chain-satisfying set (the paper's `r = 1` strict vote).

No `sorry`, no extra axiom.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AnnealingDNN15.MainResults.EmbeddedIsing

open scoped BigOperators
open Qatlib.Papers.AnnealingDNN15.MainResults.RbmEnergy

/-- The Gibbs expectation restricted to a finite set `A` of accepted
configurations, with inverse temperature `β` and energy `E`:

`(Σ_{x ∈ A} f(x) exp(-β E(x))) / (Σ_{x ∈ A} exp(-β E(x)))`.

This is the target of the sample average when only samples in `A` are retained
(the strict voting threshold `r = 1` of Sec. 3.2.2). -/
noncomputable def restrictedGibbsExpect {Ω : Type} (β : ℝ) (E : Ω → ℝ)
    (A : Finset Ω) (f : Ω → ℝ) : ℝ :=
  (∑ x ∈ A, f x * boltzmannWeightAt β E x) / (∑ x ∈ A, boltzmannWeightAt β E x)

/-- A constant energy shift on the accepted set factors out of both the
numerator and the restricted partition function and cancels from the
expectation.  This is the algebraic content of Eq. (22). -/
theorem restrictedGibbsExpect_const_shift {Ω : Type} (β t : ℝ) (E E' : Ω → ℝ)
    (A : Finset Ω) (f : Ω → ℝ) (h : ∀ x ∈ A, E' x = E x + t) :
    restrictedGibbsExpect β E' A f = restrictedGibbsExpect β E A f := by
  have hw : ∀ x ∈ A,
      boltzmannWeightAt β E' x = Real.exp (-(β * t)) * boltzmannWeightAt β E x := by
    intro x hx
    rw [boltzmannWeightAt, boltzmannWeightAt, h x hx]
    have hring : -(β * (E x + t)) = -(β * t) + -(β * E x) := by ring
    rw [hring, Real.exp_add]
  have hnum : (∑ x ∈ A, f x * boltzmannWeightAt β E' x)
      = Real.exp (-(β * t)) * ∑ x ∈ A, f x * boltzmannWeightAt β E x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x hx => by rw [hw x hx]; ring
  have hden : (∑ x ∈ A, boltzmannWeightAt β E' x)
      = Real.exp (-(β * t)) * ∑ x ∈ A, boltzmannWeightAt β E x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x hx => hw x hx
  unfold restrictedGibbsExpect
  rw [hnum, hden, mul_div_mul_left _ _ (Real.exp_ne_zero _)]

/-- Two energies that agree on the accepted set `A` give the same restricted
Gibbs expectation. -/
theorem restrictedGibbsExpect_congr_on {Ω : Type} (β : ℝ) (E E' : Ω → ℝ)
    (A : Finset Ω) (f : Ω → ℝ) (h : ∀ x ∈ A, E' x = E x) :
    restrictedGibbsExpect β E' A f = restrictedGibbsExpect β E A f := by
  have hw : ∀ x ∈ A, boltzmannWeightAt β E' x = boltzmannWeightAt β E x := by
    intro x hx
    rw [boltzmannWeightAt, boltzmannWeightAt, h x hx]
  have hnum : (∑ x ∈ A, f x * boltzmannWeightAt β E' x)
      = ∑ x ∈ A, f x * boltzmannWeightAt β E x :=
    Finset.sum_congr rfl fun x hx => by rw [hw x hx]
  have hden : (∑ x ∈ A, boltzmannWeightAt β E' x)
      = ∑ x ∈ A, boltzmannWeightAt β E x :=
    Finset.sum_congr rfl fun x hx => hw x hx
  unfold restrictedGibbsExpect
  rw [hnum, hden]

/-- The intra-chain coupling edges of each logical node in the embedding of
Eq. (21): `edges i` is the pair set `emb{i}` of physical qubit indices joined
ferromagnetically inside the chain of logical node `i`. -/
structure ChainEmbedding (n N : ℕ) where
  edges : Fin n → Finset (Fin N × Fin N)

/-- The ferromagnetic chain term of Eq. (21):
`-J_FM Σ_i Σ_{(k,l) ∈ emb{i}} S_k S_l`. -/
noncomputable def chainCoupling {n N : ℕ} (J : ℝ) (emb : ChainEmbedding n N)
    (S : Fin N → ℝ) : ℝ :=
  -J * ∑ i, ∑ e ∈ emb.edges i, S e.1 * S e.2

/-- On a chain-satisfying configuration of `±1` spins, every ferromagnetic
product `S_k S_l` equals `+1`, so the chain term is the constant `-J_FM` times
the total number of chain edges.  This is the step "the remaining
configurations ... should all yield the same energy for the `J_FM` terms" of
Sec. 3.2.2. -/
theorem chainCoupling_of_satisfies {n N : ℕ} (J : ℝ) (emb : ChainEmbedding n N)
    (S : Fin N → ℝ) (hspin : ∀ q, S q = 1 ∨ S q = -1)
    (hsat : ∀ i e, e ∈ emb.edges i → S e.1 = S e.2) :
    chainCoupling J emb S = -J * (∑ i, ((emb.edges i).card : ℝ)) := by
  unfold chainCoupling
  have hinner : ∀ i, (∑ e ∈ emb.edges i, S e.1 * S e.2)
      = ((emb.edges i).card : ℝ) := by
    intro i
    have hprod : ∀ e ∈ emb.edges i, S e.1 * S e.2 = (1 : ℝ) := by
      intro e he
      rcases hspin e.2 with h | h
      · rw [hsat i e he, h]; ring
      · rw [hsat i e he, h]; ring
    rw [Finset.sum_congr rfl hprod]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]

/-- **Eq. (22).**  Let `A` be the set of chain-satisfying configurations of a
finite physical configuration space `Ω`, let `E` be the logical RBM energy
evaluated on `Ω`, and let `E'' = E + chainCoupling J emb S` be the embedded
Ising energy of Eq. (21).  If `A` consists of `±1` spin configurations that
satisfy every chain constraint, then for every observable `f` the restricted
Gibbs expectation under `E''` equals the restricted Gibbs expectation under
`E`: the ferromagnetic contribution is a constant on `A` and cancels from the
numerator and the partition function. -/
theorem eq22_restricted_expect_chain_coupling {Ω : Type} {n N : ℕ}
    (β J : ℝ) (E : Ω → ℝ) (emb : ChainEmbedding n N) (S : Ω → Fin N → ℝ)
    (A : Finset Ω) (f : Ω → ℝ)
    (hspin : ∀ x ∈ A, ∀ q, S x q = 1 ∨ S x q = -1)
    (hsat : ∀ x ∈ A, ∀ i e, e ∈ emb.edges i → S x e.1 = S x e.2) :
    restrictedGibbsExpect β (fun x => E x + chainCoupling J emb (S x)) A f
      = restrictedGibbsExpect β E A f := by
  have hshift : ∀ x ∈ A,
      E x + chainCoupling J emb (S x)
        = E x + (-J * (∑ i, ((emb.edges i).card : ℝ))) := by
    intro x hx
    rw [chainCoupling_of_satisfies J emb (S x) (hspin x hx) (hsat x hx)]
  exact restrictedGibbsExpect_const_shift β (-J * (∑ i, ((emb.edges i).card : ℝ)))
    E (fun x => E x + chainCoupling J emb (S x)) A f hshift

/-- The inverse spin transform of Eq. (19): a `±1` spin `S` is the binary unit
`(S + 1)/2`. -/
noncomputable def bitOfSpin (S : ℝ) : ℝ := (S + 1) / 2

/-- **Eq. (22) for the RBM moment `v_i h_j`.**  Specializing the cancellation to
the observable `v_i h_j = ((S_i + 1)/2) · ((S_j + 1)/2)`: on the
chain-satisfying configurations the embedded model expectation of the visible-
hidden product equals its expectation under the original RBM energy `E`.  The
sample average over strictly accepted (`r = 1`) chain-satisfying samples
therefore targets `⟨v_i h_j⟩_model^E`. -/
theorem eq22_vis_hid_moment {Ω : Type} {n m N : ℕ}
    (β J : ℝ) (E : Ω → ℝ) (emb : ChainEmbedding n N) (S : Ω → Fin N → ℝ)
    (vis : Ω → Fin n → ℝ) (hid : Ω → Fin m → ℝ) (A : Finset Ω)
    (i : Fin n) (j : Fin m)
    (hspin : ∀ x ∈ A, ∀ q, S x q = 1 ∨ S x q = -1)
    (hsat : ∀ x ∈ A, ∀ i e, e ∈ emb.edges i → S x e.1 = S x e.2) :
    restrictedGibbsExpect β (fun x => E x + chainCoupling J emb (S x)) A
        (fun x => bitOfSpin (vis x i) * bitOfSpin (hid x j))
      = restrictedGibbsExpect β E A
        (fun x => bitOfSpin (vis x i) * bitOfSpin (hid x j)) :=
  eq22_restricted_expect_chain_coupling β J E emb S A _ hspin hsat

/-- The set of samples retained by the strict voting threshold `r = 1`: a
sample is kept exactly when it satisfies every chain constraint. -/
noncomputable def strictSampleSet {Ω : Type} [Fintype Ω] (chainSat : Ω → Prop)
    [DecidablePred chainSat] : Finset Ω :=
  Finset.univ.filter chainSat

/-- Membership in the strictly retained sample set is exactly chain
satisfaction. -/
theorem mem_strictSampleSet {Ω : Type} [Fintype Ω] {chainSat : Ω → Prop}
    [DecidablePred chainSat] {x : Ω} :
    x ∈ strictSampleSet chainSat ↔ chainSat x := by
  simp [strictSampleSet]

/-- The probability law obtained by discarding chain-violating samples and
renormalizing: the Boltzmann weight conditioned on the accepted set `A`. -/
noncomputable def conditionalGibbsProb {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (β : ℝ) (E : Ω → ℝ) (A : Finset Ω) (x : Ω) : ℝ :=
  if x ∈ A then boltzmannWeightAt β E x / (∑ y ∈ A, boltzmannWeightAt β E y) else 0

/-- Discarding the chain-violating samples and renormalizing yields a genuine
probability distribution (total mass `1`) on a nonempty accepted set. -/
theorem conditionalGibbsProb_sum_one {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (β : ℝ) (E : Ω → ℝ) (A : Finset Ω) (hA : A.Nonempty) :
    ∑ x : Ω, conditionalGibbsProb β E A x = 1 := by
  have hZ : (∑ y ∈ A, boltzmannWeightAt β E y) ≠ 0 :=
    (Finset.sum_pos (fun y _ => boltzmannWeightAt_pos β E y) hA).ne'
  have h : (∑ x : Ω, conditionalGibbsProb β E A x)
      = ∑ x ∈ A,
          boltzmannWeightAt β E x / (∑ y ∈ A, boltzmannWeightAt β E y) := by
    simp only [conditionalGibbsProb]
    rw [← Finset.sum_filter]
    congr 1
    ext x
    simp
  rw [h, ← Finset.sum_div]
  exact div_self hZ

end Qatlib.Papers.AnnealingDNN15.MainResults.EmbeddedIsing
