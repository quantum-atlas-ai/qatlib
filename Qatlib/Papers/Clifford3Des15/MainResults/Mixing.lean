/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Clifford3Des15.MainResults.Core

set_option backward.isDefEq.respectTransparency false

/-!
# Clifford3Des15 — Pauli mixing infrastructure (paper layer)

Source: Zak Webb, *The Clifford group forms a unitary 3-design*,
fixed arXiv:1510.02769v3 (8 Nov 2016).

This module formalizes the finite-sum content of Section 2.5:

* `subWeight_eq_sum_ite`: the sub-ensemble weight of eq. (27) as an indicator sum.
* `subWeight_marginal`: the decomposition used in the first equality of eq. (36)
  of Lemma 2 — the weight of the sub-ensemble `E_{p₁→q₁}` is the sum over the
  possible images `q₂` of a second Pauli element `p₂`.
* `pauliMixing_of_twoMixing`: the conclusion of Lemma 2 (claim `c009`), obtained
  by combining the marginal decomposition with the uniform class weights supplied
  by Pauli 2-mixing and the class-size count of eq. (35).
* `lemma3_pauliInvariant`: the Pauli-invariance half of Lemma 3 (claim `c010`).
* `fiber_card_eq_of_transitive`: the orbit-counting identity behind eqs. (37)-(39).
* `pauliTwoMixing_of_uniform_fibers`: the Pauli-2-mixing half of Lemma 3 from the
  uniform-fiber count.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Classical

namespace Qatlib.Papers.Clifford3Des15.MainResults

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.ChannelTheory.TwirlChannel
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

variable {ι : Type} [Fintype ι]

/-! ## Sub-ensemble weights as indicator sums -/

/-- The sub-ensemble weight `∑_{(α,U) ∈ E_s} α` of eq. (27), written as an
indicator sum. -/
theorem subWeight_eq_sum_ite {d : ℕ} (E : Ensemble ι d) (s : ι → Prop) [DecidablePred s] :
    subWeight E s = ∑ i, if s i then E.wt i else 0 := by
  rw [subWeight, Finset.sum_filter]

/-- **Lemma 2 marginal decomposition** (eq. (36), first equality): if every member
of the ensemble that maps `p₁` to `q₁` also maps `p₂` to a unique Pauli element,
then the `E_{p₁→q₁}` weight is the sum of the joint weights over the possible
images of `p₂`. -/
theorem subWeight_marginal {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d)
    (p1 p2 q1 : Operator d)
    (hex : ∀ i, conjugatesTo (E.op i) p1 q1 →
      ∃! q2, q2 ∈ S.P ∧ conjugatesTo (E.op i) p2 q2) :
    subWeight E (fun i => conjugatesTo (E.op i) p1 q1)
      = ∑ q2 ∈ S.P, subWeight E (fun i =>
          conjugatesTo (E.op i) p1 q1 ∧ conjugatesTo (E.op i) p2 q2) := by
  classical
  have hinner : ∀ i, (if conjugatesTo (E.op i) p1 q1 then E.wt i else 0)
      = ∑ q2 ∈ S.P, (if conjugatesTo (E.op i) p1 q1 ∧
          conjugatesTo (E.op i) p2 q2 then E.wt i else 0) := by
    intro i
    by_cases hs : conjugatesTo (E.op i) p1 q1
    · obtain ⟨q2, ⟨hq2P, hq2conj⟩, huniq⟩ := hex i hs
      have hcongr : (∑ b ∈ S.P, (if conjugatesTo (E.op i) p1 q1 ∧
            conjugatesTo (E.op i) p2 b then E.wt i else (0:ℝ)))
          = ∑ b ∈ S.P, (if b = q2 then E.wt i else (0:ℝ)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        by_cases hb : b = q2
        · subst hb; simp [hs, hq2conj]
        · have hnot : ¬ (conjugatesTo (E.op i) p1 q1 ∧
              conjugatesTo (E.op i) p2 b) := by
            intro ⟨_, hbconj⟩
            exact hb (huniq b ⟨by assumption, hbconj⟩)
          simp [hnot, hb]
      have hsingle : (∑ b ∈ S.P, (if b = q2 then E.wt i else (0:ℝ))) = E.wt i := by
        rw [Finset.sum_ite_eq']
        simp [hq2P]
      rw [if_pos hs, hcongr, hsingle]
    · rw [if_neg hs]
      refine (Finset.sum_eq_zero (fun q2 _ => ?_)).symm
      simp [hs]
  simp_rw [subWeight_eq_sum_ite, hinner]
  rw [Finset.sum_comm]

/-! ## Lemma 2: Pauli 2-mixing implies Pauli mixing -/

/-- **Lemma 2** (claim `c009`; Webb, arXiv:1510.02769v3, Lemma 2, p. 12): a Pauli
2-mixing `C_n^d`-ensemble is Pauli mixing.

The hypotheses isolate the structural facts the paper uses in eq. (36):

* `hchoice`: for each Pauli element there is a distinct second Pauli element
  (needed to apply 2-mixing).
* `hmap`: members that send `p₁` to `q₁` send `p₂` to a unique Pauli element
  (Clifford elements preserve the Pauli group).
* `hzero`: joint weights of image pairs outside the commutation class `H_{F(p₁,p₂)}`
  vanish (conjugation preserves commutation relations).
* `hcount`: for a fixed `q₁` there are `|H_{F(p₁,p₂)}| / |P|` partner images `q₂`,
  the class-size count of eq. (35).

Under these, the marginal decomposition `subWeight_marginal` and the uniform class
weights of `PauliTwoMixing` give `1 / |P|`, exactly Pauli mixing. -/
theorem pauliMixing_of_twoMixing {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d)
    (h2 : PauliTwoMixing E S)
    (hchoice : ∀ p1 ∈ S.P, ∃ p2 ∈ S.P, p1 ≠ p2)
    (hmap : ∀ p1 ∈ S.P, ∀ q1 ∈ S.P, ∀ p2 ∈ S.P, p1 ≠ p2 → ∀ i,
      conjugatesTo (E.op i) p1 q1 →
        ∃! q2, q2 ∈ S.P ∧ conjugatesTo (E.op i) p2 q2)
    (hzero : ∀ p1 ∈ S.P, ∀ p2 ∈ S.P, ∀ q1 ∈ S.P, ∀ q2 ∈ S.P,
      (q1, q2) ∉ Hclass S.F (S.F p1 p2) S.P →
        subWeight E (fun i => conjugatesTo (E.op i) p1 q1 ∧
          conjugatesTo (E.op i) p2 q2) = 0)
    (hcount : ∀ p1 ∈ S.P, ∀ q1 ∈ S.P, ∀ p2 ∈ S.P,
      ((S.P.filter (fun q2 => (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P)).card : ℝ)
          * ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹ = (S.P.card : ℝ)⁻¹) :
    PauliMixing E S := by
  intro p1 hp1 q1 hq1
  classical
  obtain ⟨p2, hp2, hne⟩ := hchoice p1 hp1
  rw [subWeight_marginal E S p1 p2 q1 (hmap p1 hp1 q1 hq1 p2 hp2 hne)]
  have hstep : ∀ q2 ∈ S.P,
      subWeight E (fun i => conjugatesTo (E.op i) p1 q1 ∧
          conjugatesTo (E.op i) p2 q2)
        = (if (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P
            then ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹ else 0) := by
    intro q2 hq2
    by_cases hmem : (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P
    · rw [if_pos hmem]
      exact h2 p1 hp1 p2 hp2 hne q1 q2 hmem
    · rw [if_neg hmem]
      exact hzero p1 hp1 p2 hp2 q1 hq1 q2 hq2 hmem
  have hsum1 : (∑ q2 ∈ S.P, subWeight E (fun i => conjugatesTo (E.op i) p1 q1 ∧
        conjugatesTo (E.op i) p2 q2))
      = ∑ q2 ∈ S.P, (if (q1, q2) ∈ Hclass S.F (S.F p1 p2) S.P
          then ((Hclass S.F (S.F p1 p2) S.P).card : ℝ)⁻¹ else (0:ℝ)) :=
    Finset.sum_congr rfl (fun q2 hq2 => hstep q2 hq2)
  rw [hsum1]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact hcount p1 hp1 q1 hq1 p2 hp2

/-! ## Lemma 3: Pauli-invariance of the uniform Clifford ensemble -/

/-- **Lemma 3, Pauli-invariance half** (claim `c010`; Webb, arXiv:1510.02769v3,
Lemma 3, p. 13): if `E` is uniform over a finite family `C` closed under right
multiplication by Pauli elements and containing all of its own members' Pauli
right-multiples, then `E` is Pauli-invariant (eq. (26)). -/
theorem lemma3_pauliInvariant {d : ℕ} (E : Ensemble ι d) (S : PauliSystem d)
    (C : Finset (Operator d)) (huni : IsUniformOver E C)
    (hmul : ∀ c ∈ C, ∀ p ∈ S.P, c * p ∈ C) :
    PauliInvariant E S := by
  classical
  intro p hp i
  obtain ⟨hinC, hsurj, hwt⟩ := huni
  have hmem : E.op i * p ∈ C := hmul (E.op i) (hinC i) p hp
  obtain ⟨j, hj⟩ := hsurj _ hmem
  exact ⟨j, by rw [hwt j, hwt i], hj⟩

/-! ## Lemma 3: the orbit-counting identity behind eqs. (37)-(39) -/

/-- If `g₀ • x = y`, then the number of group elements carrying `x` to `y` equals
the number of group elements fixing `x`: the bijection `g ↦ g₀⁻¹ * g` (the orbit-
stabilizer count used in eqs. (37)-(39)). -/
theorem fiber_card_eq_of_transitive {G Ω : Type} [Group G] [Fintype G] [MulAction G Ω]
    (x y : Ω) (g0 : G) (hxy : g0 • x = y) :
    (Finset.univ.filter (fun g : G => g • x = y)).card
      = (Finset.univ.filter (fun g : G => g • x = x)).card := by
  classical
  refine Finset.card_bij (fun g _ => g0⁻¹ * g) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [mul_smul, hg, ← hxy, inv_smul_smul]
  · intro g1 _ g2 _ h
    exact mul_left_cancel h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨g0 * k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mul_smul, hk, hxy]
    · show g0⁻¹ * (g0 * k) = k
      rw [← mul_assoc, inv_mul_cancel, one_mul]

/-- **Eq. (39) core**: for a uniform weight on a finite family whose `f`-fibers all
have cardinality `|C| / |H|`, the total weight over each fiber is exactly `1 / |H|`.

This is the numerical content of the last step of Lemma 3: the uniform Clifford
measure gives each `C_{p→q}` the weight `|C_{p→q}| / |C|`, and the orbit count
`|C_{p→q}| = |C| / |H|` yields `1 / |H|`. -/
theorem fiber_weight_uniform {C H : Type} [Fintype C] [Fintype H]
    (w : C → ℝ) (f : C → H)
    (hw : ∀ c, w c = (Fintype.card C : ℝ)⁻¹)
    (hcard : ∀ h, ((Finset.univ.filter (fun c => f c = h)).card : ℝ)
      * (Fintype.card H : ℝ) = (Fintype.card C : ℝ))
    (hH : 0 < Fintype.card H) (hC : 0 < Fintype.card C) :
    ∀ h, ∑ c ∈ Finset.univ.filter (fun c => f c = h), w c
      = (Fintype.card H : ℝ)⁻¹ := by
  intro h
  have hHne : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hCne : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hsum : ∑ c ∈ Finset.univ.filter (fun c => f c = h), w c
      = ((Finset.univ.filter (fun c => f c = h)).card : ℝ)
        * (Fintype.card C : ℝ)⁻¹ := by
    rw [Finset.sum_congr rfl (fun c _ => hw c), Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hfc : ((Finset.univ.filter (fun c => f c = h)).card : ℝ)
      = (Fintype.card C : ℝ) / (Fintype.card H : ℝ) := by
    rw [eq_div_iff hHne]
    exact hcard h
  rw [hfc]
  field_simp

end Qatlib.Papers.Clifford3Des15.MainResults
