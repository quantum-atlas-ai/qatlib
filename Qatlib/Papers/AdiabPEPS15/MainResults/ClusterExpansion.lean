/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabPEPS15.MainResults.SourceModel
public import Mathlib.Analysis.Normed.Algebra.Exponential

@[expose] public section


/-!
# Cluster-expansion identities

Source: "Rapid adiabatic preparation of injective PEPS and Gibbs states",
fixed arXiv:1508.00570v2. This module proves the following cluster-expansion identities:

* `mobius_geometric_sum` — the Möbius/binomial identity of Eq. (102),
  `∑_{Λ ⊆ Ω} (−1)^{|Ω|−|Λ|} x^{|Λ|} = (x − 1)^{|Ω|}`;
* `source_lemma12` — Lemma 12 / Eq. (97): the Möbius transform `fˇ_μ` of the
  cluster term `f_μ` vanishes away from its support, i.e.
  `fCheck h P β (Ω ∪ Θ) = 0` whenever every `h_λ` on `Ω ∪ Θ` commutes with the
  idempotent `P_μ`, `Ω` is nonempty and `Θ` is disjoint from it.

Theorem 10, Lemma 13, and Theorem 14 lie outside this module's scope. Here the commutation algebra collapses
`f_μ(Λ)` to the projector `P` for *every* `Λ ⊆ Ω ∪ Θ`, so the Möbius sum is
the pure sign sum, which vanishes on the nonempty index set.

The exponential facts need a `NormedAlgebra ℚ` structure on complex matrices
under the L2 operator norm; `matQnormedAlg` below restricts the canonical
`ℂ`-algebra structure along the isometric embedding `ℚ → ℂ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open Qatlib.Papers.AdiabPEPS15.MainResults

namespace Qatlib.Papers.AdiabPEPS15.MainResults

variable {d : ℕ} {ι : Type*} [DecidableEq ι]

/-- The rational normed-algebra structure on complex matrices: the `ℚ`-action
is the restriction of the `ℂ`-algebra action along `algebraMap ℚ ℂ`, which is
an isometry, so `norm_smul_le` holds. -/
local instance matQnormedAlg : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) where
  toAlgebra := Algebra.compHom _ (algebraMap ℚ ℂ)
  norm_smul_le q x := by
    show ‖(algebraMap ℚ ℂ q : ℂ) • x‖ ≤ ‖q‖ * ‖x‖
    have hcast : (algebraMap ℚ ℂ q : ℂ) = (q : ℚ) := by
      rw [Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast]
    rw [hcast, norm_smul, Complex.norm_ratCast, ← Real.norm_eq_abs,
      Rat.norm_cast_real]

/-! ## §1 The Möbius/binomial identity of Eq. (102) -/

/-- The Möbius sum over the powerset with a geometric weight,
`∑_{Λ ⊆ Ω} (−1)^{|Ω|−|Λ|} x^{|Λ|}`, equals `(x − 1)^{|Ω|}` (Eq. (102) of the
source, with `x = e^{4β}`).

This is the combinatorial heart of Lemma 13.  The proof is an induction on
`Ω`: inserting an element splits the powerset into subsets without `a`
(contributing `−T`) and subsets with `a` (contributing `x • T`), giving the
factor `x − 1`. -/
theorem mobius_geometric_sum {R : Type*} [CommRing R] (Ω : Finset ι) (x : R) :
    (∑ Λ ∈ Ω.powerset, ((-1 : R) ^ (Ω.card - Λ.card)) * x ^ Λ.card)
      = (x - 1) ^ Ω.card := by
  classical
  induction Ω using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    have hsub : ∀ Λ ∈ s.powerset, Λ ⊆ s := fun Λ hΛ => Finset.mem_powerset.mp hΛ
    have hΛcard : ∀ Λ ∈ s.powerset, Λ.card ≤ s.card := fun Λ hΛ =>
      Finset.card_le_card (hsub Λ hΛ)
    have haΛ : ∀ Λ ∈ s.powerset, a ∉ Λ := fun Λ hΛ hx => ha (hsub Λ hΛ hx)
    have hinj : ∀ Λ ∈ s.powerset, ∀ u ∈ s.powerset, insert a Λ = insert a u → Λ = u := by
      intro Λ hΛ u hu heq
      refine Finset.ext fun x => ?_
      have hx := (Finset.ext_iff.mp heq) x
      by_cases hxa : x = a
      · subst hxa
        simp [(haΛ Λ hΛ), (haΛ u hu)]
      · simpa [hxa, Finset.mem_insert] using hx
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      refine Finset.disjoint_left.mpr fun w hw hu => ?_
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hu
      exact haΛ _ hw (Finset.mem_insert_self a u)
    rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj]
    have step1 : ∀ Λ ∈ s.powerset,
        ((-1 : R) ^ ((insert a s).card - Λ.card)) * x ^ Λ.card
          = -((-1 : R) ^ (s.card - Λ.card) * x ^ Λ.card) := by
      intro Λ hΛ
      have hc : Λ.card ≤ s.card := hΛcard Λ hΛ
      have h1 : (insert a s).card - Λ.card = (s.card - Λ.card) + 1 := by omega
      rw [h1, pow_succ]
      ring
    have step2 : ∀ Λ ∈ s.powerset,
        ((-1 : R) ^ ((insert a s).card - (insert a Λ).card)) * x ^ (insert a Λ).card
          = ((-1 : R) ^ (s.card - Λ.card) * x ^ Λ.card) * x := by
      intro Λ hΛ
      have hc : Λ.card ≤ s.card := hΛcard Λ hΛ
      have hcard' : (insert a Λ).card = Λ.card + 1 :=
        Finset.card_insert_of_notMem (haΛ Λ hΛ)
      have h1 : (insert a s).card - (insert a Λ).card = s.card - Λ.card := by omega
      have h2 : x ^ (insert a Λ).card = x ^ Λ.card * x := by rw [hcard', pow_succ]
      rw [h1, h2]
      ring
    rw [Finset.sum_congr rfl step1, Finset.sum_congr rfl step2, Finset.sum_neg_distrib,
      ← Finset.sum_mul, hcard, pow_succ, ← ih]
    ring

/-- The Möbius sign sum vanishes on a nonempty finset: for `S ≠ ∅`,
`∑_{Λ ⊆ S} (−1)^{|S|−|Λ|} = 0`.  This is `mobius_geometric_sum` at `x = 1`,
cast to `ℂ` for the scalar coefficients of `mobiusCheck`. -/
theorem mobius_sign_sum_eq_zero (S : Finset ι) (hS : S.Nonempty) :
    ∑ Λ ∈ S.powerset, ((-1 : ℂ) ^ (S.card - Λ.card)) = 0 := by
  have hcard : 0 < S.card := hS.card_pos
  have h := mobius_geometric_sum S (1 : ℂ)
  rw [Finset.sum_congr rfl (fun Λ _ => by rw [one_pow, mul_one]),
    show (1 : ℂ) - 1 = 0 by norm_num,
    zero_pow (Nat.pos_iff_ne_zero.mp hcard)] at h
  exact h

/-- A finite sum of scalar multiples of a fixed module element factors
through the scalar sum: `∑ i ∈ s, c i • P = (∑ i ∈ s, c i) • P`. -/
theorem sum_smul_const {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (s : Finset ι) (c : ι → R) (P : M) :
    ∑ i ∈ s, c i • P = (∑ i ∈ s, c i) • P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_smul, ih]

/-! ## §2 Commutation algebra for the cluster term -/

/-- If every `h a` with `a ∈ Ω ∪ Θ` commutes with `P`, then `Hsum h S`
commutes with `P` for every `S ⊆ Ω ∪ Θ`. -/
theorem hsum_comm (h : ι → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (Ω Θ : Finset ι) (hcomm : ∀ a ∈ Ω ∪ Θ, h a * P = P * h a)
    (S : Finset ι) (hS : S ⊆ Ω ∪ Θ) :
    Hsum h S * P = P * Hsum h S := by
  simp only [Hsum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a ha => hcomm a (hS ha)

omit [DecidableEq ι] in
/-- The matrix exponential of `r • Hsum h S` commutes with `P` whenever
`Hsum h S` does. -/
theorem exp_hsum_comm (h : ι → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (S : Finset ι) (hc : Hsum h S * P = P * Hsum h S) (r : ℝ) :
    NormedSpace.exp (r • Hsum h S) * P = P * NormedSpace.exp (r • Hsum h S) := by
  have hcom : Commute (r • Hsum h S) P := by
    show (r • Hsum h S) * P = P * (r • Hsum h S)
    rw [smul_mul_assoc, hc, mul_smul_comm]
  exact hcom.exp_left.eq

/-- Under the commutation hypothesis of Lemma 12, the cluster term `fμ h P β S`
collapses to the projector `P` itself, independently of `S ⊆ Ω ∪ Θ`: the
conjugation `e^{βH} P e^{−2βH} P e^{βH}` reduces to `P` because `H` commutes
with `P` and `P` is idempotent. -/
theorem fmu_eq_of_comm (h : ι → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (β : ℝ) (Ω Θ : Finset ι) (hcomm : ∀ a ∈ Ω ∪ Θ, h a * P = P * h a)
    (hidem : P * P = P) (S : Finset ι) (hS : S ⊆ Ω ∪ Θ) :
    fμ h P β S = P := by
  have hc : Hsum h S * P = P * Hsum h S := hsum_comm h P Ω Θ hcomm S hS
  have hPe : NormedSpace.exp (β • Hsum h S) * P
      = P * NormedSpace.exp (β • Hsum h S) := exp_hsum_comm h P S hc β
  have hPg : NormedSpace.exp ((-2 * β) • Hsum h S) * P
      = P * NormedSpace.exp ((-2 * β) • Hsum h S) := exp_hsum_comm h P S hc (-2 * β)
  have hPg' : NormedSpace.exp ((-β) • Hsum h S) * P
      = P * NormedSpace.exp ((-β) • Hsum h S) := exp_hsum_comm h P S hc (-β)
  have cH : Commute (β • Hsum h S) ((-2 * β) • Hsum h S) := by
    show (β • Hsum h S) * ((-2 * β) • Hsum h S) = ((-2 * β) • Hsum h S) * (β • Hsum h S)
    rw [smul_mul_smul, smul_mul_smul, mul_comm]
  have cH2 : Commute ((-β) • Hsum h S) (β • Hsum h S) := by
    show ((-β) • Hsum h S) * (β • Hsum h S) = (β • Hsum h S) * ((-β) • Hsum h S)
    rw [smul_mul_smul, smul_mul_smul, mul_comm]
  have hsumneg : β • Hsum h S + (-2 * β) • Hsum h S = (-β) • Hsum h S := by
    rw [← add_smul]
    congr 1
    ring
  have heg : NormedSpace.exp (β • Hsum h S) * NormedSpace.exp ((-2 * β) • Hsum h S)
      = NormedSpace.exp ((-β) • Hsum h S) := by
    have hx := NormedSpace.exp_add_of_commute cH
    rw [hsumneg] at hx
    exact hx.symm
  have hzero : (-β) • Hsum h S + β • Hsum h S = 0 := by
    rw [← add_smul]
    simp
  have hge1 : NormedSpace.exp ((-β) • Hsum h S) * NormedSpace.exp (β • Hsum h S) = 1 := by
    have hx := NormedSpace.exp_add_of_commute cH2
    rw [hzero] at hx
    simpa using hx.symm
  unfold fμ
  calc NormedSpace.exp (β • Hsum h S) * P * NormedSpace.exp ((-2 * β) • Hsum h S) * P
        * NormedSpace.exp (β • Hsum h S)
      = P * (NormedSpace.exp (β • Hsum h S) * NormedSpace.exp ((-2 * β) • Hsum h S)) * P
        * NormedSpace.exp (β • Hsum h S) := by rw [hPe]; noncomm_ring
    _ = P * NormedSpace.exp ((-β) • Hsum h S) * P
        * NormedSpace.exp (β • Hsum h S) := by rw [heg]
    _ = P * P * (NormedSpace.exp ((-β) • Hsum h S)
        * NormedSpace.exp (β • Hsum h S)) := by
      have hmid : P * NormedSpace.exp ((-β) • Hsum h S) * P
          * NormedSpace.exp (β • Hsum h S)
          = P * (NormedSpace.exp ((-β) • Hsum h S) * P)
            * NormedSpace.exp (β • Hsum h S) := by noncomm_ring
      rw [hmid, hPg']
      noncomm_ring
    _ = P * P * 1 := by rw [hge1]
    _ = P := by rw [hidem, mul_one]

/-! ## §3 Lemma 12 — support of the Möbius transform  -/

/-- **Fixed arXiv:1508.00570v2, Lemma 12, Eq. (97)** (Supplemental p. 15).

Let `μ ∈ Υ`.  If `Ω ⊆ Λ` is nonempty with `μ ∉ Ω` and `Θ` disjoint from `Ω`,
and if every `h_λ` for `λ ∈ Ω ∪ Θ` commutes with the projector `P_μ`
(`hcomm`) and `P_μ` is idempotent (`hidem`), then `fˇ_μ(Ω ∪ Θ) = 0`.

Proof: every `Λ ⊆ Ω ∪ Θ` satisfies `fμ h P β Λ = P` by `fmu_eq_of_comm`, so
the Möbius transform is the pure sign sum `∑ (−1)^{|Ω∪Θ|−|Λ|} • P`; the sign
sum vanishes because `Ω ∪ Θ` is nonempty (`mobius_sign_sum_eq_zero`).  The
hypotheses `μ ∉ Ω` and `Disjoint Θ Ω` of the source statement are kept but
not needed by this argument. -/
theorem source_lemma12
    (h : ι → Matrix (Fin d) (Fin d) ℂ) (P : Matrix (Fin d) (Fin d) ℂ)
    (β : ℝ) (μ : ι) (Ω Θ : Finset ι)
    (hΩne : Ω.Nonempty) (_hμΩ : μ ∉ Ω) (_hΘΩ : Disjoint Θ Ω)
    (hcomm : ∀ a ∈ Ω ∪ Θ, h a * P = P * h a)
    (hidem : P * P = P) :
    fCheck h P β (Ω ∪ Θ) = 0 := by
  have hne : (Ω ∪ Θ).Nonempty :=
    hΩne.mono fun a ha => Finset.mem_union_left Θ ha
  have hfμ : ∀ Λ ∈ (Ω ∪ Θ).powerset, fμ h P β Λ = P := fun Λ hΛ =>
    fmu_eq_of_comm h P β Ω Θ hcomm hidem Λ (Finset.mem_powerset.mp hΛ)
  unfold fCheck mobiusCheck
  rw [Finset.sum_congr rfl fun Λ hΛ => by rw [hfμ Λ hΛ],
    sum_smul_const, mobius_sign_sum_eq_zero _ hne, zero_smul]

end Qatlib.Papers.AdiabPEPS15.MainResults
