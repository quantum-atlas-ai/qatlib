/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.FDeriv.Extend
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.IteratedDerivWithin
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open Set Filter Topology
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {a b : ℝ} {f g : ℝ → F}

theorem hasDerivWithinAt_Icc_of_continuousOn (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) {x : ℝ} (hx : x ∈ Icc a b) :
    HasDerivWithinAt f (g x) (Icc a b) x := by
  have hlim : Tendsto (fderiv ℝ f) (𝓝[Ioo a b] x)
      (𝓝 (ContinuousLinearMap.toSpanSingleton ℝ (g x))) := by
    have h := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := F)).continuous.tendsto (g x)
    apply (h.comp ((hg x hx).mono Ioo_subset_Icc_self)).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).hasFDerivAt.fderiv.symm
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← closure_Ioo hab.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
    (convex_Ioo a b) isOpen_Ioo _ hlim
  intro y hy
  rw [closure_Ioo hab.ne] at hy
  exact (hf y hy).mono Ioo_subset_Icc_self

theorem eqOn_iteratedDerivWithin_Icc_of_continuous_jet (hab : a < b)
    {n : ℕ} {J : ℕ → ℝ → F} (hzero : EqOn (J 0) f (Icc a b))
    (hc : ∀ j ≤ n, ContinuousOn (J j) (Icc a b))
    (hd : ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x)
    {j : ℕ} (hj : j ≤ n) : EqOn (iteratedDerivWithin j f (Icc a b)) (J j) (Icc a b) := by
  induction j with
  | zero => simpa using hzero.symm
  | succ j ih =>
    have hjn : j < n := by omega
    have heq := ih (by omega)
    intro x hx
    rw [iteratedDerivWithin_succ, derivWithin_congr heq (heq hx)]
    exact (hasDerivWithinAt_Icc_of_continuousOn hab (hc j (by omega))
      (hc (j + 1) hj) (hd j hjn) hx).derivWithin (uniqueDiffOn_Icc hab x hx)

theorem contDiffOn_Icc_of_continuous_jet (hab : a < b)
    {n : ℕ} {J : ℕ → ℝ → F} (hzero : EqOn (J 0) f (Icc a b))
    (hc : ∀ j ≤ n, ContinuousOn (J j) (Icc a b))
    (hd : ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x) :
    ContDiffOn ℝ n f (Icc a b) := by
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv
    (uniqueDiffOn_Icc hab)).2
  constructor
  · intro j hj
    exact (hc j hj).congr
      (eqOn_iteratedDerivWithin_Icc_of_continuous_jet hab hzero hc hd hj)
  · intro j hj x hx
    have heq := eqOn_iteratedDerivWithin_Icc_of_continuous_jet hab hzero hc hd
      (Nat.le_of_lt hj)
    exact ((hasDerivWithinAt_Icc_of_continuousOn hab (hc j (by omega))
      (hc (j + 1) (by omega)) (hd j hj) hx).congr heq (heq hx)).differentiableWithinAt

theorem contDiffOn_Icc_iff_exists_continuous_jet (hab : a < b) {n : ℕ} :
    ContDiffOn ℝ n f (Icc a b) ↔
      ∃ J : ℕ → ℝ → F, EqOn (J 0) f (Icc a b) ∧
        (∀ j ≤ n, ContinuousOn (J j) (Icc a b)) ∧
        ∀ j < n, ∀ x ∈ Ioo a b, HasDerivAt (J j) (J (j + 1) x) x := by
  constructor
  · intro hf
    refine ⟨fun j ↦ iteratedDerivWithin j f (Icc a b), ?_, ?_, ?_⟩
    · simp only [iteratedDerivWithin_zero]
      exact eqOn_refl _ _
    · intro j hj
      exact hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hab)
    · intro j hj x hx
      exact ContDiffOn.hasDerivAt_iteratedDerivWithin hf (mod_cast hj) (uniqueDiffOn_Icc hab)
        (Icc_mem_nhds hx.1 hx.2)
  · rintro ⟨J, hzero, hc, hd⟩
    exact contDiffOn_Icc_of_continuous_jet hab hzero hc hd

end TauCeti

theorem ContDiffOn.isBounded_image_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b : ℝ} {n : ℕ∞ω} (hf : ContDiffOn ℝ n f (Icc a b)) (hn : 1 ≤ n) :
    Bornology.IsBounded (deriv f '' Icc a b) := by
  rcases lt_or_ge a b with hab | hba
  swap
  · exact ((subsingleton_Icc_of_ge hba).image _).finite.isBounded
  have hdw : Bornology.IsBounded (derivWithin f (Icc a b) '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn
      (hf.continuousOn_derivWithin (uniqueDiffOn_Icc hab) hn)).isBounded
  refine (hdw.union (Set.toFinite {deriv f a, deriv f b}).isBounded).subset ?_
  rintro y ⟨t, ht, rfl⟩
  rcases eq_or_ne t a with rfl | hta
  · simp
  rcases eq_or_ne t b with rfl | htb
  · simp
  exact Or.inl ⟨t, ht, derivWithin_of_mem_nhds (Icc_mem_nhds (ht.1.lt_of_ne' hta)
    (ht.2.lt_of_ne htb))⟩

end
end Qatlib.Foundations.CbmdAnalysis.Residue
