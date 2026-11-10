/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.RectangularBudgetRealizationStat
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.FilteredNorm
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

theorem rectangularWitness_compress
    {R S Q : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype Q]
    {n : ℕ} (u : Fin n → R → Q → ℂ) (v : Fin n → S → Q → ℂ) :
    ∃ (u' : R → Fin n → QState (Fin (Fintype.card R+Fintype.card S)))
      (v' : S → Fin n → QState (Fin (Fintype.card R+Fintype.card S))),
      (∀ j r s, (∑ k, star (u' r j k)*v' s j k) = ∑ q, star (u j r q)*v j s q) ∧
      (∀ r j, ‖toEuclidean_fromVec (u' r j)‖^2 = ∑ q, Complex.normSq (u j r q)) ∧
      (∀ s j, ‖toEuclidean_fromVec (v' s j)‖^2 = ∑ q, Complex.normSq (v j s q)) := by
  let B (j : Fin n) : Matrix Q (R ⊕ S) ℂ := fun q z => Sum.elim (u j) (v j) z q
  have hp (j : Fin n) : ((B j)ᴴ*B j).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  choose V hV using fun j => gram_positive_matrix_actual_factorization (R ⊕ S)
    ((B j)ᴴ*B j) (hp j)
  let e : Fin (Fintype.card R+Fintype.card S) ≃ (R ⊕ S) :=
    (Fintype.equivFinOfCardEq (by simp)).symm
  have hinner (j : Fin n) (a b : R ⊕ S) :
      (∑ k, star (V j (e k) a)*V j (e k) b) = ∑ q, star (B j q a)*B j q b := by
    rw [e.sum_comp (fun q => star (V j q a)*V j q b)]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using!
      congrFun (congrFun (hV j) a) b
  have hmass (j : Fin n) (z : R ⊕ S) :
      ‖toEuclidean_fromVec (fun k => V j (e k) z)‖^2 = ∑ q, Complex.normSq (B j q z) := by
    rw [norm_toEuclidean_fromVec_sq]
    simp only [← Complex.normSq_eq_norm_sq]
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
    exact hinner j z z
  refine ⟨fun r j k => V j (e k) (.inl r), fun s j k => V j (e k) (.inr s), ?_, ?_, ?_⟩
  · intro j r s
    exact hinner j (.inl r) (.inr s)
  · intro r j
    exact hmass j (.inl r)
  · intro s j
    exact hmass j (.inr s)

theorem sourceRectCert_of_lift
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} {A : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (h : gramFilteredCert (sourceRectLift A) (fun j => sourceRectLift (Z j)) w) :
    sourceRectCert n A Z w := by
  obtain ⟨Q, hQ, u, v, hu, hv, heq⟩ := h
  obtain ⟨u', v', hinner, humass, hvmass⟩ := rectangularWitness_compress
    (fun j r => u j (.inl r)) (fun j s => v j (.inr s))
  refine ⟨Fintype.card R+Fintype.card S, u', v', ?_, ?_, ?_⟩
  · intro r s
    have h := heq (.inl r) (.inr s)
    simpa only [sourceRectLift, dotProduct, Pi.star_apply, hinner] using! h
  · intro r
    simp_rw [humass]
    exact hu (.inl r)
  · intro s
    simp_rw [hvmass]
    exact hv (.inr s)

theorem liftCert_of_sourceRectCert
    {R S : Type} {n : ℕ} {A : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (hw : 0 ≤ w) (h : sourceRectCert n A Z w) :
    gramFilteredCert (sourceRectLift A) (fun j => sourceRectLift (Z j)) w := by
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  let u' : Fin n → (R ⊕ S) → Fin m → ℂ := fun j z => Sum.elim (fun r => u r j) (fun _ => 0) z
  let v' : Fin n → (R ⊕ S) → Fin m → ℂ := fun j z => Sum.elim (fun _ => 0) (fun s => v s j) z
  refine ⟨Fin m, inferInstance, u', v', ?_, ?_, ?_⟩
  · intro z
    cases z with
    | inl r => simpa only [u', Sum.elim_inl, Complex.normSq_eq_norm_sq,
        ← norm_toEuclidean_fromVec_sq] using! hu r
    | inr s => simpa [u'] using! hw
  · intro z
    cases z with
    | inl r => simpa [v'] using! hw
    | inr s => simpa only [v', Sum.elim_inr, Complex.normSq_eq_norm_sq,
        ← norm_toEuclidean_fromVec_sq] using! hv s
  · intro r s
    cases r <;> cases s <;>
      simp only [sourceRectLift, u', v', Sum.elim_inl, Sum.elim_inr,
        dotProduct, Pi.star_apply] <;> simp [heq]

theorem sourceRectCert_iff_lift
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} {A : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ} (hw : 0 ≤ w) :
    sourceRectCert n A Z w ↔
      gramFilteredCert (sourceRectLift A) (fun j => sourceRectLift (Z j)) w :=
  ⟨liftCert_of_sourceRectCert hw, sourceRectCert_of_lift⟩

theorem sourceRectValue_eq_lift
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) :
    sourceRectValue A Z = filteredGamma2 (sourceRectLift A) (fun j => sourceRectLift (Z j)) := by
  unfold sourceRectValue filteredGamma2
  congr 1
  ext b
  constructor
  · rintro ⟨w, hw, hb, hcert⟩
    exact ⟨w, hb, liftCert_of_sourceRectCert hw hcert⟩
  · rintro ⟨w, hb, hcert⟩
    refine ⟨max w 0, le_max_right _ _, ?_, sourceRectCert_of_lift
      (gramFilteredCert_mono hcert (le_max_left _ _))⟩
    rw [hb, ENNReal.ofReal_max]
    simp

theorem sourceRectValue_budget_boundary
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ) (w : ℝ) (hw : 0 ≤ w) :
    sourceRectValue A Z ≤ ENNReal.ofReal w ↔ sourceRectCert n A Z w := by
  rw [sourceRectValue_eq_lift]
  exact (filteredGamma2_budget_boundary (R ⊕ S) n (sourceRectLift A)
    (fun j => sourceRectLift (Z j)) w hw).trans (sourceRectCert_iff_lift hw).symm

theorem sourceRectCert_fixed_width
    {R S : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    {n : ℕ} {A : Matrix R S ℂ} {Z : Fin n → Matrix R S ℂ} {w : ℝ}
    (h : sourceRectCert n A Z w) :
    ∃ (u : R → Fin n → QState (Fin (Fintype.card R+Fintype.card S)))
      (v : S → Fin n → QState (Fin (Fintype.card R+Fintype.card S))),
      (∀ r s, A r s = ∑ j, Z j r s * ∑ k, star (u r j k)*v s j k) ∧
      (∀ r, ∑ j, ‖toEuclidean_fromVec (u r j)‖^2 ≤ w) ∧
      (∀ s, ∑ j, ‖toEuclidean_fromVec (v s j)‖^2 ≤ w) := by
  obtain ⟨m, u, v, heq, hu, hv⟩ := h
  obtain ⟨u', v', hinner, humass, hvmass⟩ := rectangularWitness_compress
    (fun j r => u r j) (fun j s => v s j)
  refine ⟨u', v', ?_, ?_, ?_⟩
  · intro r s
    simpa only [hinner] using! heq r s
  · intro r
    simp_rw [humass]
    simpa only [Complex.normSq_eq_norm_sq, norm_toEuclidean_fromVec_sq] using! hu r
  · intro s
    simp_rw [hvmass]
    simpa only [Complex.normSq_eq_norm_sq, norm_toEuclidean_fromVec_sq] using! hv s

theorem rectangularBudgetRealization :
    ∀ (R S : Type) [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
      (n : ℕ) (A : Matrix R S ℂ) (Z : Fin n → Matrix R S ℂ),
      sourceRectValue A Z = filteredGamma2 (sourceRectLift A) (fun j => sourceRectLift (Z j)) ∧
      (∀ w : ℝ, 0 ≤ w →
        (sourceRectValue A Z ≤ ENNReal.ofReal w ↔ sourceRectCert n A Z w)) ∧
      (sourceRectValue A Z < ⊤ → ∃ (w : ℝ) (m : ℕ)
        (u : R → Fin n → QState (Fin m)) (v : S → Fin n → QState (Fin m)),
        0 ≤ w ∧ m ≤ n*(Fintype.card R+Fintype.card S) ∧
        sourceRectValue A Z = ENNReal.ofReal w ∧
        (∀ r s, A r s = ∑ j, Z j r s * ∑ k, star (u r j k)*v s j k) ∧
        (∀ r, ∑ j, ‖toEuclidean_fromVec (u r j)‖^2 ≤ w) ∧
        (∀ s, ∑ j, ‖toEuclidean_fromVec (v s j)‖^2 ≤ w)) := by
  intro R S _ _ _ _ n A Z
  refine ⟨sourceRectValue_eq_lift A Z, sourceRectValue_budget_boundary A Z, ?_⟩
  intro hfinite
  let w := (sourceRectValue A Z).toReal
  have hw : 0 ≤ w := ENNReal.toReal_nonneg
  have hvalue : sourceRectValue A Z = ENNReal.ofReal w := (ENNReal.ofReal_toReal hfinite.ne).symm
  have hcert : sourceRectCert n A Z w :=
    (sourceRectValue_budget_boundary A Z w hw).mp (by rw [hvalue])
  by_cases hn : n = 0
  · subst n
    obtain ⟨m, u, v, heq, _, _⟩ := hcert
    refine ⟨w, 0, (fun _ _ _ => 0), (fun _ _ _ => 0), hw, by simp, hvalue, ?_, ?_, ?_⟩
    · intro r s
      simpa using! heq r s
    · intro r; simpa using! hw
    · intro s; simpa using! hw
  · obtain ⟨u, v, heq, hu, hv⟩ := sourceRectCert_fixed_width hcert
    refine ⟨w, Fintype.card R+Fintype.card S, u, v, hw, ?_, hvalue, heq, hu, hv⟩
    have hn1 : 1 ≤ n := by omega
    simpa only [one_mul] using! Nat.mul_le_mul_right (Fintype.card R+Fintype.card S) hn1

end Qatlib.Concepts.GramQueryCore.FilteredNorm
