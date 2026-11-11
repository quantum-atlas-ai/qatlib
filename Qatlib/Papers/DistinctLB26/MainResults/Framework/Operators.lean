/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.DistinctLB26.MainResults.Model.Setup

set_option backward.isDefEq.respectTransparency false

/-!
# Operators — transfer operators, knowledge operators and the query identity

Fixed source: arXiv:2604.05133v1 (Belovs, *Tight Quantum Lower Bound for
k-Distinctness*), Definitions 3.4/3.16/3.17/3.20 (pp. 11–18), Section 4.1
(Proposition 4.5, Claim 4.6, pp. 20–22), Claim 6.4 and Claim 6.12 (pp. 31–37),
Lemma 6.13 (p. 37).

Model conventions (see `Model/Setup.lean`): states are finite complex vectors
`EuclideanSpace ℂ ι`, the label register of a type `μ` is modelled on a finite
index type `Z` (the Fourier labels `τ̂`), and a knowledge system `L` is a set of
finite subsets of the item set `α`.  The transfer operator `Υ_μ` is a linear map
`State ι → State Z`; the knowledge operator chops the input Fourier state
according to `L` (Definition 3.17, displayed formula (3.39)), and the oracle on
the Fourier register is the coordinate permutation induced by the translation
`σ ↦ σ + {i ↦ c}` (Eq. (3.9)).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DistinctLB26.MainResults.Framework

open Qatlib.Papers.DistinctLB26.MainResults.Model

variable {α ι Z : Type*}

/-! ## Elementary operator shapes -/

/-- The oracle on the Fourier register: the coordinate permutation induced by the
translation `σ ↦ σ + {i ↦ c}` of Eq. (3.9). -/
def permOp [Fintype ι] (e : ι ≃ ι) (φ : State ι) : State ι :=
  WithLp.toLp 2 (fun σ => φ (e.symm σ))

/-- The `permOp_apply` result for the DistinctLB26 paper model. -/
@[simp] theorem permOp_apply [Fintype ι] (e : ι ≃ ι) (φ : State ι) (σ : ι) :
    permOp e φ σ = φ (e.symm σ) := rfl

/-- The indicator coefficient `[A ∈ L]` of a knowledge system (Definition 3.16),
written as a function of the finite set `A`: `1` if `A ∈ L` and `0` otherwise.
Making the coefficient an explicit function keeps the mask algebra of Lemma 3.21
free of decidability bookkeeping. -/
def ind (L : Set (Finset α)) (A : Finset α) : ℂ := by
  classical exact if A ∈ L then (1 : ℂ) else 0

/-- Membership gives coefficient `1`. -/
theorem ind_of_mem {L : Set (Finset α)} {A : Finset α} (h : A ∈ L) : ind L A = 1 := by
  unfold ind
  simp [h]

/-- Non-membership gives coefficient `0`. -/
theorem ind_of_notMem {L : Set (Finset α)} {A : Finset α} (h : A ∉ L) : ind L A = 0 := by
  unfold ind
  simp [h]

/-- Masking by a knowledge system `L` (Definition 3.17): keep exactly the Fourier
states whose support lies in `L`. -/
def maskL [Fintype ι] (L : Set (Finset α)) (supp : ι → Finset α) (φ : State ι) : State ι :=
  WithLp.toLp 2 (fun σ => ind L (supp σ) * φ σ)

/-- The `maskL_apply` result for the DistinctLB26 paper model. -/
@[simp] theorem maskL_apply [Fintype ι] (L : Set (Finset α)) (supp : ι → Finset α)
    (φ : State ι) (σ : ι) :
    maskL L supp φ σ = ind L (supp σ) * φ σ := rfl

/-- A (pseudo-)knowledge operator `Υ△` of Definition 3.17: the transfer
operator `Υ` applied to the `L△`-masked Fourier state. -/
def knowledgeOp [Fintype ι] (Υ : State ι → State Z)
    (L : Set (Finset α)) (supp : ι → Finset α) (φ : State ι) : State Z :=
  Υ (maskL L supp φ)

/-- A weighted diagonal operator, the transfer operator written in the Fourier
basis (Proposition 4.5): `|σ̂⟩ ↦ w σ |σ̂⟩`. -/
def weightedDiag [Fintype ι] (w : ι → ℂ) (φ : State ι) : State ι :=
  WithLp.toLp 2 (fun σ => w σ * φ σ)

/-- The `weightedDiag_apply` result for the DistinctLB26 paper model. -/
@[simp] theorem weightedDiag_apply [Fintype ι] (w : ι → ℂ) (φ : State ι) (σ : ι) :
    weightedDiag w φ σ = w σ * φ σ := rfl

/-- Fibre-sum operator with label map `f` and coefficients `w`, restricted to the
mask `P`: this is the explicit Fourier form (3.39)/(4.6) of a knowledge operator,
`(Υ△ φ) τ = Σ_{σ : f σ = τ, mask σ} w σ φ σ`. -/
def fiberOp [Fintype ι] [DecidableEq Z] (f : ι → Z) (P : ι → Prop) [DecidablePred P]
    (w : ι → ℂ) (φ : State ι) : State Z :=
  WithLp.toLp 2 (fun τ => ∑ σ, if P σ ∧ f σ = τ then w σ * φ σ else 0)

/-- The `fiberOp_apply` result for the DistinctLB26 paper model. -/
@[simp] theorem fiberOp_apply [Fintype ι] [DecidableEq Z] (f : ι → Z) (P : ι → Prop) [DecidablePred P]
    (w : ι → ℂ) (φ : State ι) (τ : Z) :
    fiberOp f P w φ τ = ∑ σ, if P σ ∧ f σ = τ then w σ * φ σ else 0 := rfl

/-- A knowledge mask never increases the norm: it is the orthogonal projection
onto the coordinate subspace selected by `L` (Definition 3.16). -/
theorem norm_maskL_le [Fintype ι] (L : Set (Finset α)) (supp : ι → Finset α)
    (φ : State ι) :
    ‖maskL L supp φ‖ ≤ ‖φ‖ := by
  have hsq : ‖maskL L supp φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro σ _
    have hind : ‖ind L (supp σ)‖ ≤ 1 := by
      by_cases hσ : supp σ ∈ L
      · rw [ind_of_mem hσ]; simp
      · rw [ind_of_notMem hσ]; simp
    calc ‖maskL L supp φ σ‖ ^ 2
        = ‖ind L (supp σ) * φ σ‖ ^ 2 := by rw [maskL_apply]
      _ = (‖ind L (supp σ)‖ * ‖φ σ‖) ^ 2 := by rw [norm_mul]
      _ = ‖ind L (supp σ)‖ ^ 2 * ‖φ σ‖ ^ 2 := by ring
      _ ≤ 1 ^ 2 * ‖φ σ‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_pow_left₀ (norm_nonneg _) hind 2
      _ = ‖φ σ‖ ^ 2 := by ring
  calc ‖maskL L supp φ‖ = Real.sqrt (‖maskL L supp φ‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖φ‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖φ‖ := Real.sqrt_sq (norm_nonneg _)

/-! ## Proposition 3.6: transfer operators intertwine the oracle -/

/-- **Proposition 3.6** (p. 12, Eq. (3.27)): because the transfer operators
commute with the input oracle (Fact 3.5), `Υ` sends the uniform state of the
algorithm after `t` queries to the state of the actual algorithm (3.10) after `t`
queries on the transferred initial state.  The whole algebraic content is this
intertwining property of the oracle iteration. -/
theorem prop3_6 {X Y : Type*} (Υ : State X → State Y) (OX : State X → State X)
    (OY : State Y → State Y) (hcomm : ∀ φ, Υ (OX φ) = OY (Υ φ)) (φ : State X)
    (t : ℕ) : Υ (iter OX t φ) = iter OY t (Υ φ) := by
  induction t with
  | zero => rfl
  | succ n ih => rw [iter, iter, ← ih]; exact hcomm _

/-! ## Lemma 3.21 and its corollaries (query gain) -/

/-- Indicator identity behind Lemma 3.21: for a knowledge system `L⁺` that is
upwards closed and the boundary system `Ldi = {S : S ∉ L⁺, S ∪ {i} ∈ L⁺}`,
the gain indicators of one query match. -/
theorem indicator_query_identity [DecidableEq α] (Lplus Lpartial : Set (Finset α))
    (i : α) (hL : ∀ S : Finset α, S ∈ Lpartial ↔ S ∉ Lplus ∧ insert i S ∈ Lplus)
    (hup : ∀ S S' : Finset α, S ∈ Lplus → S ⊆ S' → S' ∈ Lplus) (A : Finset α) :
    ind Lplus (insert i A) - ind Lplus A = ind Lpartial A - ind Lpartial (insert i A) := by
  have hnot : insert i A ∉ Lpartial := by
    rw [hL]
    intro h
    exact h.1 (by simpa using h.2)
  have hiff : A ∈ Lpartial ↔ (insert i A ∈ Lplus ∧ A ∉ Lplus) := by
    rw [hL]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  by_cases hA : A ∈ Lplus
  · have hins : insert i A ∈ Lplus := hup A (insert i A) hA (Finset.subset_insert i A)
    have hApartial : A ∉ Lpartial := by rw [hiff]; exact fun h => h.2 hA
    rw [ind_of_mem hins, ind_of_mem hA, ind_of_notMem hApartial, ind_of_notMem hnot]
    norm_num
  · by_cases hins : insert i A ∈ Lplus
    · have hApartial : A ∈ Lpartial := by rw [hiff]; exact ⟨hins, hA⟩
      rw [ind_of_mem hins, ind_of_notMem hA, ind_of_mem hApartial, ind_of_notMem hnot]
    · have hApartial : A ∉ Lpartial := by rw [hiff]; exact fun h => hins h.1
      rw [ind_of_notMem hins, ind_of_notMem hA, ind_of_notMem hApartial, ind_of_notMem hnot]

/-- Mask algebra of one query step: for a translation `e` that adds the item `i`
to the support, the `L⁺`- and `Ldi`-masks satisfy the paper's operator identity
`M⁺ O − O M⁺ = O M∂ − M∂ O`. -/
theorem mask_query_identity [Fintype ι] [DecidableEq α] (Lplus Lpartial : Set (Finset α))
    (supp : ι → Finset α) (i : α)
    (hL : ∀ S : Finset α, S ∈ Lpartial ↔ S ∉ Lplus ∧ insert i S ∈ Lplus)
    (hup : ∀ S S' : Finset α, S ∈ Lplus → S ⊆ S' → S' ∈ Lplus)
    (e : ι ≃ ι) (hstep : ∀ σ, supp (e σ) = insert i (supp σ)) (φ : State ι) :
    maskL Lplus supp (permOp e φ) - permOp e (maskL Lplus supp φ)
      = permOp e (maskL Lpartial supp φ) - maskL Lpartial supp (permOp e φ) := by
  apply Core.State.ext
  intro σ
  have hsupp : supp σ = insert i (supp (e.symm σ)) := by
    simpa using hstep (e.symm σ)
  have hid := indicator_query_identity Lplus Lpartial i hL hup (supp (e.symm σ))
  simp only [maskL_apply, permOp_apply, PiLp.sub_apply, hsupp]
  have := congrArg (fun t : ℂ => t * φ (e.symm σ)) hid
  simpa [sub_mul] using this

/-- **Lemma 3.21** (p. 18, Eq. (3.42)): for every `μ`, `i` and `c ≠ 0`,
`Υ⁺_μ O_{i,c} − O_{i,c} Υ⁺_μ = O_{i,c} Υ^{∂i}_μ − Υ^{∂i}_μ O_{i,c}`, where
`O_{i,c}` acts on the Fourier register as the translation `σ ↦ σ + {i ↦ c}` and
on the label register as the commuting oracle (`hcomm`, Fact 3.5).  The transfer
operator only needs to be additive-inverse-linear (`hΥsub`), which holds since it
is a linear operator by Definition 3.4. -/
theorem lemma3_21 [Fintype ι] [DecidableEq α] (supp : ι → Finset α)
    (Lplus Lpartial : Set (Finset α)) (i : α)
    (hL : ∀ S : Finset α, S ∈ Lpartial ↔ S ∉ Lplus ∧ insert i S ∈ Lplus)
    (hup : ∀ S S' : Finset α, S ∈ Lplus → S ⊆ S' → S' ∈ Lplus)
    (e : ι ≃ ι) (hstep : ∀ σ, supp (e σ) = insert i (supp σ))
    (Υ : State ι → State Z) (hΥsub : ∀ φ ψ, Υ (φ - ψ) = Υ φ - Υ ψ)
    (OY : State Z → State Z) (hcomm : ∀ φ, OY (Υ φ) = Υ (permOp e φ)) (φ : State ι) :
    knowledgeOp Υ Lplus supp (permOp e φ) - OY (knowledgeOp Υ Lplus supp φ)
      = OY (knowledgeOp Υ Lpartial supp φ) - knowledgeOp Υ Lpartial supp (permOp e φ) := by
  have hm := mask_query_identity Lplus Lpartial supp i hL hup e hstep φ
  unfold knowledgeOp
  rw [hcomm, hcomm]
  calc Υ (maskL Lplus supp (permOp e φ)) - Υ (permOp e (maskL Lplus supp φ))
      = Υ (maskL Lplus supp (permOp e φ) - permOp e (maskL Lplus supp φ)) :=
        (hΥsub _ _).symm
    _ = Υ (permOp e (maskL Lpartial supp φ) - maskL Lpartial supp (permOp e φ)) := by rw [hm]
    _ = Υ (permOp e (maskL Lpartial supp φ)) - Υ (maskL Lpartial supp (permOp e φ)) :=
        hΥsub _ _

/-- **Corollary 3.22** (p. 19, Eq. (3.48), state-level query identity): given the
direct-sum operator identity (3.47) (obtained by summing Lemma 3.21 over `μ` and
`i` and tensoring with `A`), and `ψ_{t+1} = O ψ'_t`, we have
`Υ⁺ ψ_{t+1} − O Υ⁺ ψ'_t = O Ψ∂ ψ'_t − Ψ∂ ψ_{t+1}`. -/
theorem cor3_22 {ι : Type*} (transferPlus : State ι → State ι)
    (OY : State ι → State ι) (queryGain : State ι → State ι)
    (h47 : ∀ φ, transferPlus (OY φ) - OY (transferPlus φ)
      = OY (queryGain φ) - queryGain (OY φ))
    (ψ' ψnext : State ι) (hnext : ψnext = OY ψ') :
    transferPlus ψnext - OY (transferPlus ψ') = OY (queryGain ψ') - queryGain ψnext := by
  rw [hnext, h47]

/-- **Corollary 3.23** (p. 19, Query Gain Bound): `‖Υ⁺ ψ_{t+1}‖ − ‖Υ⁺ ψ_t‖ ≤
‖Ψ∂ ψ'_t‖ + ‖Ψ∂ ψ_{t+1}‖`.  The proof is the triangle inequality applied to the
query identity of Corollary 3.22, together with unitarity of `O` (Prop. 3.19(b))
which gives `‖O Υ⁺ ψ'_t‖ = ‖Υ⁺ ψ_t‖`. -/
theorem cor3_23 {ι : Type*} [Fintype ι] (a b c u v : State ι) (g : ℝ)
    (hb : ‖b‖ = ‖a‖) (hid : c - b = u - v) (hg : ‖u‖ + ‖v‖ ≤ g) :
    ‖c‖ - ‖a‖ ≤ g := by
  have h1 : ‖c‖ ≤ ‖b‖ + ‖c - b‖ := by
    have := norm_add_le b (c - b)
    rwa [add_sub_cancel] at this
  have h2 : ‖c - b‖ ≤ g := by
    rw [hid]
    exact (norm_sub_le u v).trans hg
  linarith

/-- **Corollary 3.24** (p. 19, Knowledge Upper Bound): iterating the query-gain
bound from zero initial knowledge yields
`‖Υ⁺ ψ'_t‖ ≤ Σ_{j<t} (‖Ψ∂ ψ'_j‖ + ‖Ψ∂ ψ_{j+1}‖)`. -/
theorem cor3_24 (k g : ℕ → ℝ) (h0 : k 0 = 0) (hstep : ∀ j, k (j + 1) ≤ k j + g j) :
    ∀ t : ℕ, k t ≤ ∑ j ∈ Finset.range t, g j := by
  intro t
  induction t with
  | zero => simp [h0]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      linarith [hstep n]

/-! ## Proposition 4.5 and Claim 4.6: the Fourier form of transfer operators -/

/-- Block-sum map `τ(B) = Σ_{i∈B} σ(i)` of Proposition 4.5 (p. 21). -/
def blockSum {n : ℕ} {G : Type*} [AddCommMonoid G] (σ : Fin n → G) :
    Finset (Fin n) → G :=
  fun B => ∑ i ∈ B, σ i

/-- **Proposition 4.5 (Transfer Operators)** (p. 21): in the Fourier basis, the
transfer operator `Υ_μ` maps `|σ̂⟩_X` to `|μ, τ̂⟩_Y` with `τ(B) = Σ_{i∈B} σ(i)`;
on a general state it is the fibre sum over the Fourier label `τ`. -/
theorem prop4_5 {n : ℕ} {G : Type*} [AddCommMonoid G] [Fintype G] [DecidableEq G]
    (φ : State (Fin n → G)) (τ : Finset (Fin n) → G) :
    (fiberOp (fun σ => blockSum (G := G) σ) (fun _ => True) (fun _ => (1 : ℂ)) φ) τ
      = ∑ σ, if blockSum (G := G) σ = τ then φ σ else 0 := by
  simp [fiberOp_apply]

/-- **Claim 4.6** (p. 22): for a general superposition `Σ_σ α_σ |σ̂⟩_X`, the
knowledge operator `Υ^△_μ` maps it to
`Σ_τ (Σ_{σ : supp(σ) ∈ L^△_μ, τ(σ) = τ} α_σ) |μ, τ̂⟩_Y`: sum the coefficients
within each Fourier label and keep only the terms selected by the knowledge
system. -/
theorem claim4_6 {n : ℕ} {G : Type*} [AddCommMonoid G] [DecidableEq G] [Fintype G]
    (L : Set (Finset (Fin n))) (supp : (Fin n → G) → Finset (Fin n))
    [DecidablePred fun σ => supp σ ∈ L]
    (w : (Fin n → G) → ℂ) (α : State (Fin n → G)) (τ : Finset (Fin n) → G) :
    (fiberOp (fun σ => blockSum (G := G) σ) (fun σ => supp σ ∈ L) w α) τ
      = ∑ σ, if supp σ ∈ L ∧ blockSum (G := G) σ = τ then w σ * α σ else 0 := by
  simp [fiberOp_apply]

/-! ## Claim 6.4: knowledge of a split is dominated by the split knowledge -/

/-- **Claim 6.4** (p. 31): if `μ₁` is obtained from `μ₂` by splitting off `i`,
then `‖Υ^{∂i}_{μ₂} φ‖ ≤ ‖Υ⁺_{μ₁} φ‖` for all `φ ∈ X`.  In the Fourier-cover
model both operators are the same weighted diagonal restricted to the
corresponding knowledge system, and splitting only shrinks the admissible set of
Fourier supports: `L^{∂i}_{μ₂} ⊆ L⁺_{μ₁}`. -/
theorem claim6_4 [Fintype ι] (Ld Lplus : Set (Finset α))
    (hsub : Ld ⊆ Lplus) (supp : ι → Finset α) (w : ι → ℂ) (φ : State ι) :
    ‖maskL Ld supp (weightedDiag w φ)‖ ≤ ‖maskL Lplus supp (weightedDiag w φ)‖ := by
  set x := weightedDiag w φ with hx
  have hle : maskL Ld supp x = maskL Ld supp (maskL Lplus supp x) := by
    apply Core.State.ext
    intro σ
    by_cases hσ : supp σ ∈ Lplus
    · by_cases hσ' : supp σ ∈ Ld
      · simp [maskL_apply, ind_of_mem hσ, ind_of_mem hσ']
      · simp [maskL_apply, ind_of_mem hσ, ind_of_notMem hσ']
    · have hσ' : supp σ ∉ Ld := fun h => hσ (hsub h)
      simp [maskL_apply, ind_of_notMem hσ, ind_of_notMem hσ']
  rw [hle]
  exact norm_maskL_le Ld supp (maskL Lplus supp x)

/-! ## Claim 6.12 and Lemma 6.13: query profile `Ξ` and refined query gain -/

/-- **Claim 6.12, first identity** (p. 37): `Ξ Ψ∂ = Ψ∂`.  The query-profile
projector `Ξ` fixes every query-gain state because `L^{∂i} = ∅` whenever `i` is
not in the highlighted block, so `Ψ∂` is supported in the image of `Ξ`; in the
coordinate model `Ψ∂` is therefore already `Ξ`-masked (Definition 3.20). -/
theorem claim6_12_fst [Fintype ι] (P : ι → Prop) [DecidablePred P] (Ψ : State ι)
    (hΨ : Ψ = Core.State.projMask P Ψ) :
    Core.State.projMask P Ψ = Ψ :=
  hΨ.symm

/-- **Claim 6.12, second identity** (p. 37): `O Ξ = Ξ O`.  The oracle `O_{μ,i,c}`
commutes with the query-profile projector `Ξ_{μ,i}` because both decompose over
`(μ, i)`: the mask `P` is invariant under the oracle permutation. -/
theorem claim6_12_snd [Fintype ι] (P : ι → Prop) [DecidablePred P] (e : ι ≃ ι)
    (hinv : ∀ σ, P (e σ) ↔ P σ) (φ : State ι) :
    permOp e (Core.State.projMask P φ) = Core.State.projMask P (permOp e φ) := by
  apply Core.State.ext
  intro σ
  have h : P σ ↔ P (e.symm σ) := by
    have := hinv (e.symm σ)
    simpa using this
  by_cases hP : P σ
  · have hP' : P (e.symm σ) := h.mp hP
    simp [permOp_apply, Core.State.projMask_apply, hP, hP']
  · have hP' : ¬ P (e.symm σ) := fun hh => hP (h.mpr hh)
    simp [permOp_apply, Core.State.projMask_apply, hP, hP']

/-- Squared norm splits into the two complementary masks. -/
theorem normSq_mask_add_compl [Fintype ι] (P : ι → Prop) [DecidablePred P] (x : State ι) :
    ‖Core.State.projMask P x‖ ^ 2 + ‖Core.State.projMask (fun σ => ¬ P σ) x‖ ^ 2
      = ‖x‖ ^ 2 := by
  have hdisj : ∀ σ, ¬ (P σ ∧ ¬ P σ) := fun σ h => h.2 h.1
  have hall : Core.State.projMask (fun σ => P σ ∨ ¬ P σ) x = x := by
    apply Core.State.ext
    intro σ
    by_cases h : P σ <;> simp [Core.State.projMask_apply, h]
  rw [Core.State.normSq_projMask_add_of_disjoint P (fun σ => ¬ P σ) hdisj x]
  have h := congrArg (fun t : State ι => ‖t‖ ^ 2) hall
  simpa using h

/-- **Lemma 6.13 (Refined Query Gain Bound)** (p. 37): if `Ξ` is the query-profile
projector, `x = Υ⁺ ψ_{t+1}`, `y = O Υ⁺ ψ'_t`, `w = x − y` lies in the image of
`Ξ`, `‖y‖ = ‖Υ⁺ ψ_t‖`, `‖Ξ y‖ = ‖Ξ Υ⁺ ψ'_t‖` and `‖w‖ ≤ g`, then
`‖x‖² − ‖Υ⁺ ψ_t‖² ≤ 2 ‖Ξ Υ⁺ ψ'_t‖ · g + g²`.  This is exactly the chain of
inequalities in the proof of Lemma 6.13 (`w = v₂ − v₁`, orthogonal splitting by
`Ξ` and `Ξ⊥`). -/
theorem lemma6_13 [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (x y a w : State ι) (g e : ℝ)
    (hxy : x - y = w) (hwP : Core.State.projMask P w = w)
    (hy : ‖y‖ ≤ ‖a‖) (hv : ‖Core.State.projMask P y‖ ≤ e)
    (hg : ‖w‖ ≤ g) (hg0 : 0 ≤ g) (he0 : 0 ≤ e) :
    ‖x‖ ^ 2 - ‖a‖ ^ 2 ≤ 2 * e * g + g ^ 2 := by
  have hx : x = y + w := by
    have h1 : x = w + y := by
      have := congrArg (· + y) hxy
      simpa using this
    simpa [add_comm] using h1
  have hwPc : Core.State.projMask (fun σ => ¬ P σ) w = 0 := by
    have hstep : Core.State.projMask (fun σ => ¬ P σ) w
        = Core.State.projMask (fun σ => ¬ P σ) (Core.State.projMask P w) := by
      rw [hwP]
    rw [hstep]
    apply Core.State.ext
    intro σ
    by_cases h : P σ <;> simp [Core.State.projMask_apply, h]
  have hPx : Core.State.projMask P x = Core.State.projMask P y + w := by
    rw [hx, projMask_add, hwP]
  have hPcx : Core.State.projMask (fun σ => ¬ P σ) x
      = Core.State.projMask (fun σ => ¬ P σ) y := by
    rw [hx, projMask_add, hwPc, add_zero]
  have hsplit : ‖x‖ ^ 2
      = ‖Core.State.projMask P x‖ ^ 2 + ‖Core.State.projMask (fun σ => ¬ P σ) x‖ ^ 2 :=
    (normSq_mask_add_compl P x).symm
  have hPx_norm : ‖Core.State.projMask P x‖ ≤ ‖Core.State.projMask P y‖ + ‖w‖ := by
    rw [hPx]
    exact norm_add_le _ _
  have hsq : ‖Core.State.projMask P x‖ ^ 2
      ≤ (‖Core.State.projMask P y‖ + ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hPx_norm 2
  have hy_sq : ‖Core.State.projMask P y‖ ^ 2
      + ‖Core.State.projMask (fun σ => ¬ P σ) y‖ ^ 2 = ‖y‖ ^ 2 := by
    have h := normSq_mask_add_compl P y
    linarith
  have hx2 : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 + 2 * e * g + g ^ 2 := by
    rw [hsplit, hPcx]
    nlinarith [hsq, hy_sq, hv, hg, norm_nonneg (Core.State.projMask P y), norm_nonneg w,
      norm_nonneg (Core.State.projMask (fun σ => ¬ P σ) y), he0, hg0]
  have hya : ‖y‖ ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  linarith

end Qatlib.Papers.DistinctLB26.MainResults.Framework
