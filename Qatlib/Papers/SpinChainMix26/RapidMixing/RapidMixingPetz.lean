/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic.NoncommRing
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.SpinChainMix26.RapidMixing

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open scoped ComplexOrder Kronecker MatrixOrder

lemma siteUpdateRate_aux (n i s : ℕ) (hs : s ≤ i + n) :
    (i + n - (i + n - s) % n) % n = s % n := by
  have hsum := Nat.div_add_mod (i + n - s) n
  set u := (i + n - s) / n * n with hu
  set v := (i + n - s) % n with hv
  have hsum' : u + v = i + n - s := by
    rw [hu, hv, Nat.mul_comm]
    exact hsum
  have hcalc : i + n - v = s + u := by omega
  rw [hcalc, hu]
  exact Nat.add_mul_mod_self_right s ((i + n - s) / n) n

lemma siteUpdateRate_eq_one {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (hle : ℓ ≤ n) :
    ∀ i, siteUpdateRate n ℓ i = 1 := by
  intro i
  have hne : (ℓ : ℝ) ≠ 0 := by positivity
  have him : ∀ a < n, (i + n - a) % n < n := fun a _ => Nat.mod_lt _ hn
  have hinv : ∀ a < n, (i + n - (i + n - a) % n) % n = a := by
    intro a ha
    have h := siteUpdateRate_aux n i a (by omega : a ≤ i + n)
    rw [Nat.mod_eq_of_lt ha] at h
    exact h
  have hsum : (∑ s ∈ Finset.range n, if (i + n - s) % n < ℓ then (1 / ℓ : ℝ) else 0)
      = ∑ u ∈ Finset.range n, if u < ℓ then (1 / ℓ : ℝ) else 0 := by
    refine Finset.sum_nbij' (fun s : ℕ => (i + n - s) % n)
      (fun u : ℕ => (i + n - u) % n) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_range.mpr (him a (Finset.mem_range.mp ha))
    · intro a ha
      exact Finset.mem_range.mpr (him a (Finset.mem_range.mp ha))
    · intro a ha
      exact hinv a (Finset.mem_range.mp ha)
    · intro a ha
      exact hinv a (Finset.mem_range.mp ha)
    · intro a ha
      rfl
  have hcount : (∑ u ∈ Finset.range n, if u < ℓ then (1 / ℓ : ℝ) else 0) = 1 := by
    have hfilter : (Finset.range n).filter (fun u => u < ℓ) = Finset.range (min n ℓ) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    calc (∑ u ∈ Finset.range n, if u < ℓ then (1 / ℓ : ℝ) else 0)
        = (1 / ℓ : ℝ) * ∑ u ∈ Finset.range n, if u < ℓ then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          by_cases h : u < ℓ <;> simp [h]
      _ = (1 / ℓ : ℝ) * ((Finset.range n).filter (fun u => u < ℓ)).card := by
          rw [Finset.sum_boole]
      _ = (1 / ℓ : ℝ) * (ℓ : ℝ) := by
          congr 1
          rw [hfilter, Finset.card_range]
          exact_mod_cast min_eq_right hle
      _ = 1 := by field_simp
  unfold siteUpdateRate
  rw [hsum, hcount]

lemma openSiteUpdateRate_eq_one {n ℓ i : ℕ} (hℓ : 0 < ℓ) (hi1 : 1 ≤ i) (hin : i ≤ n) :
    openSiteUpdateRate n ℓ i = 1 := by
  have hne : (ℓ : ℝ) ≠ 0 := by positivity
  have hcard : (Finset.Icc ((i : ℤ) - (ℓ : ℤ) + 1) (i : ℤ)).card = ℓ := by
    rw [Int.card_Icc]
    have hz : ((i : ℤ) + 1 - ((i : ℤ) - (ℓ : ℤ) + 1) : ℤ) = (ℓ : ℤ) := by omega
    rw [hz]
    simp
  have hfilter :
      (openBlockStarts n ℓ).filter
          (fun s => (s : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1)
        = Finset.Icc ((i : ℤ) - (ℓ : ℤ) + 1) (i : ℤ) := by
    ext s
    simp only [Finset.mem_filter, openBlockStarts, Finset.mem_Icc]
    constructor
    · intro ⟨⟨hs1, hs2⟩, h1, h2⟩
      exact ⟨by omega, by omega⟩
    · intro ⟨h1, h2⟩
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hsum : (∑ s ∈ openBlockStarts n ℓ,
        if (s : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1 then (1 / ℓ : ℝ) else 0)
      = (1 / ℓ : ℝ) * (Finset.Icc ((i : ℤ) - (ℓ : ℤ) + 1) (i : ℤ)).card := by
    calc (∑ s ∈ openBlockStarts n ℓ,
          if (s : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1 then (1 / ℓ : ℝ) else 0)
        = (1 / ℓ : ℝ) * ∑ s ∈ openBlockStarts n ℓ,
            if (s : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1 then (1 : ℝ) else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          by_cases h : (s : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1 <;> simp [h]
      _ = (1 / ℓ : ℝ) * ((openBlockStarts n ℓ).filter
            (fun s => (s : ℤ) ≤ (i : ℤ) ∧ (i : ℤ) ≤ s + (ℓ : ℤ) - 1)).card := by
          rw [Finset.sum_boole]
      _ = (1 / ℓ : ℝ) * (Finset.Icc ((i : ℤ) - (ℓ : ℤ) + 1) (i : ℤ)).card := by
          rw [hfilter]
  unfold openSiteUpdateRate
  rw [hsum, hcard]
  field_simp

lemma aEta_eq_two_tsum (η : InfluenceProfile) :
    aEta η = 2 * ∑' r : ℕ, η.eta (r + 1) := rfl

lemma gammaOf_eq (η : InfluenceProfile) (ℓ : ℕ) :
    gammaOf η ℓ = 1 - aEta η / ℓ := rfl

lemma gammaOf_pos {η : InfluenceProfile} {ℓ : ℕ} (hℓ : 0 < ℓ) (h : aEta η < ℓ) :
    0 < gammaOf η ℓ := by
  unfold gammaOf
  have hℓr : (0 : ℝ) < ℓ := by positivity
  have : aEta η / ℓ < 1 := by
    rw [div_lt_one hℓr]
    exact_mod_cast h
  linarith

lemma algebraMap_matrix_smul_one {D : ℕ} (r : ℝ) :
    algebraMap ℝ (Matrix (Fin D) (Fin D) ℂ) r = (((r : ℝ) : ℂ) • 1) := by
  ext i j
  simp only [Matrix.algebraMap_matrix_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j <;> simp [hij]

lemma cfc_real_smul_one {D : ℕ} (f : ℝ → ℝ) (r : ℝ) :
    cfc f (((r : ℝ) : ℂ) • (1 : Operator D)) = (((f r : ℝ) : ℂ) • 1) := by
  rw [← algebraMap_matrix_smul_one, cfc_algebraMap]
  exact algebraMap_matrix_smul_one _

lemma hermSqrt_smul_one {D : ℕ} {r : ℝ} (_hr : 0 ≤ r) :
    hermSqrt (((r : ℝ) : ℂ) • (1 : Operator D)) = (((Real.sqrt r : ℝ) : ℂ) • 1) :=
  cfc_real_smul_one _ _

lemma hermInvSqrt_smul_one {D : ℕ} {r : ℝ} (_hr : 0 < r) :
    hermInvSqrt (((r : ℝ) : ℂ) • (1 : Operator D)) =
      ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • 1) :=
  cfc_real_smul_one _ _

lemma gibbsUnnormalized_zero {D : ℕ} (β : ℝ) :
    gibbsUnnormalized β (0 : Operator D) = 1 := by
  unfold gibbsUnnormalized
  rw [smul_zero, NormedSpace.exp_zero]

lemma trace_one_operator {D : ℕ} :
    Matrix.trace (1 : Operator D) = ((D : ℕ) : ℂ) := by
  simp [Matrix.trace]

lemma gibbsState_zero {D : ℕ} (β : ℝ) :
    gibbsState β (0 : Operator D) = ((((D : ℕ) : ℂ)⁻¹ : ℂ) • 1) := by
  unfold gibbsState
  rw [gibbsUnnormalized_zero, trace_one_operator]

lemma partialTrace_smul_one {D E : ℕ} (c : ℂ) :
    PartialTrace ((c : ℂ) • (1 : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ))
      = (c * (E : ℂ)) • (1 : Operator D) := by
  ext i j
  simp only [PartialTrace, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    have hL : (∑ a : Fin E, c * if (i, a) = (i, a) then 1 else 0) = (E : ℂ) * c := by
      simp [Finset.sum_const, Finset.card_univ]
    have hR : (c * (E : ℂ)) * (if i = i then 1 else 0) = c * (E : ℂ) := by
      simp
    rw [hL, hR, mul_comm]
  · have h1 : ∀ a : Fin E, ((i, a) = (j, a)) = False := fun a => by simp [hij]
    have hL : (∑ a : Fin E, c * if (i, a) = (j, a) then 1 else 0) = 0 := by
      simp [h1]
    have hR : (c * (E : ℂ)) * (if i = j then 1 else 0) = 0 := by
      rw [if_neg hij, mul_zero]
    rw [hL, hR]

lemma reindex_one_gen {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') :
    Matrix.reindex e e (1 : Matrix ι ι ℂ) = (1 : Matrix ι' ι' ℂ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    simp
  · have hne : e.symm i ≠ e.symm j := fun hh => h (e.symm.injective hh)
    simp [h, hne]

lemma reindex_smul_gen {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (c : ℂ) (A : Matrix ι ι ℂ) :
    Matrix.reindex e e (c • A) = c • Matrix.reindex e e A := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma smul_one_mul_smul_one {D : ℕ} (c : ℂ) (M : Operator D) :
    ((c : ℂ) • (1 : Operator D)) * M * ((c : ℂ) • (1 : Operator D)) = (c * c) • M := by
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]

lemma smul_smul_rev {M : Type*} [AddCommMonoid M] [Module ℂ M] (a b : ℂ) (x : M) :
    a • (b • x) = (a * b) • x := by
  rw [smul_smul]

lemma petzHeatBath_smul_one {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) :
    petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ
      = (((d ^ ℓ : ℕ) : ℂ)⁻¹) •
        Matrix.reindex (c.matrixEquiv (d := d)).symm (c.matrixEquiv (d := d)).symm
          (PartialTrace
            (Matrix.reindex (c.matrixEquiv (d := d)) (c.matrixEquiv (d := d)) ρ)
            ⊗ₖ (1 : Operator (d ^ ℓ))) := by
  set e := c.matrixEquiv (d := d) with he
  have hdef : ∀ (σ ρ : Operator (d ^ n)),
      petzHeatBath c σ ρ
        = hermSqrt σ * Matrix.reindex e.symm e.symm
            ((hermInvSqrt (PartialTrace (Matrix.reindex e e σ))
              * PartialTrace (Matrix.reindex e e ρ)
              * hermInvSqrt (PartialTrace (Matrix.reindex e e σ)))
              ⊗ₖ (1 : Operator (d ^ ℓ))) * hermSqrt σ := by
    intro σ ρ
    unfold petzHeatBath
    rfl
  have hre : Matrix.reindex e e (((k : ℝ) : ℂ) • (1 : Operator (d ^ n)))
      = (((k : ℝ) : ℂ) • (1 : Matrix (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ))
          (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) ℂ)) := by
    rw [reindex_smul_gen, reindex_one_gen]
  have hcast : ((((k : ℝ) : ℂ)) * (((d ^ ℓ : ℕ) : ℂ)))
      = ((((k * (d ^ ℓ : ℕ) : ℝ) : ℝ) : ℂ)) := by
    push_cast
    exact_mod_cast rfl
  have hsA : PartialTrace (Matrix.reindex e e (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))))
      = ((((k * (d ^ ℓ : ℕ) : ℝ) : ℝ) : ℂ) • (1 : Operator (d ^ (n - ℓ)))) := by
    rw [hre, partialTrace_smul_one, hcast]
  have hpos : (0 : ℝ) < k * (d ^ ℓ : ℕ) := by positivity
  have hinv : hermInvSqrt ((((k * (d ^ ℓ : ℕ) : ℝ) : ℝ) : ℂ) • (1 : Operator (d ^ (n - ℓ))))
      = ((((Real.sqrt (k * (d ^ ℓ : ℕ)))⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ (n - ℓ)))) :=
    hermInvSqrt_smul_one hpos
  have hsand : ∀ (M : Operator (d ^ (n - ℓ))),
      ((((Real.sqrt (k * (d ^ ℓ : ℕ)))⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ (n - ℓ))))
        * M
        * ((((Real.sqrt (k * (d ^ ℓ : ℕ)))⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ (n - ℓ))))
      = (((((k * (d ^ ℓ : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ : ℂ)) • M := by
    intro M
    rw [smul_one_mul_smul_one]
    congr 1
    have hsq : (Real.sqrt (k * (d ^ ℓ : ℕ)))⁻¹ * (Real.sqrt (k * (d ^ ℓ : ℕ)))⁻¹
        = (k * (d ^ ℓ : ℕ))⁻¹ := by
      have hsm : Real.sqrt (k * (d ^ ℓ : ℕ)) * Real.sqrt (k * (d ^ ℓ : ℕ))
          = k * (d ^ ℓ : ℕ) := Real.mul_self_sqrt (le_of_lt hpos)
      rw [← mul_inv_rev, hsm]
    exact_mod_cast hsq
  have hsqrt : hermSqrt (((k : ℝ) : ℂ) • (1 : Operator (d ^ n)))
      = (((Real.sqrt k : ℝ) : ℂ) • (1 : Operator (d ^ n))) :=
    hermSqrt_smul_one (le_of_lt hk)
  have hmiddle : (hermInvSqrt (PartialTrace
          (Matrix.reindex e e (((k : ℝ) : ℂ) • (1 : Operator (d ^ n)))))
        * PartialTrace (Matrix.reindex e e ρ)
        * hermInvSqrt (PartialTrace
          (Matrix.reindex e e (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))))))
      = ((((((k * (d ^ ℓ : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ : ℂ)) • PartialTrace (Matrix.reindex e e ρ)) := by
    rw [hsA, hinv, hsand]
  rw [hdef, hmiddle, Matrix.smul_kronecker, reindex_smul_gen, hsqrt,
    smul_one_mul_smul_one, smul_smul_rev]
  have hmul : ((Real.sqrt k : ℝ) : ℂ) * ((Real.sqrt k : ℝ) : ℂ) = ((k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact_mod_cast Real.mul_self_sqrt (le_of_lt hk)
  have hscalar : (((Real.sqrt k : ℝ) : ℂ) * ((Real.sqrt k : ℝ) : ℂ))
      * (((((k * (d ^ ℓ : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ : ℂ)) = (((d ^ ℓ : ℕ) : ℂ)⁻¹) := by
    rw [hmul]
    have hk0 : ((k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hk)
    push_cast
    field_simp [hk0]
  rw [hscalar]

lemma cast_inv_nat (m : ℕ) : (((m : ℕ) : ℂ)⁻¹ : ℂ) = ((((m : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
  push_cast
  rfl

lemma petzHeatBath_gibbsState_zero {n ℓ d : ℕ} (c : PetzCut n ℓ) (β : ℝ) (hd : 0 < d) :
    petzHeatBath c (gibbsState β (0 : Operator (d ^ n))) (gibbsState β (0 : Operator (d ^ n)))
      = gibbsState β (0 : Operator (d ^ n)) := by
  set e := c.matrixEquiv (d := d) with he
  have hk : (0 : ℝ) < ((d ^ n : ℕ) : ℝ)⁻¹ := by positivity
  have hσ : gibbsState β (0 : Operator (d ^ n))
      = (((((d ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ n))) := by
    rw [gibbsState_zero, cast_inv_nat]
  rw [hσ, petzHeatBath_smul_one c (((d ^ n : ℕ) : ℝ)⁻¹) hk hd]
  have hτ : PartialTrace (Matrix.reindex e e
        ((((((d ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ n)))))
      = ((((((d ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * ((d ^ ℓ : ℕ) : ℂ)) • (1 : Operator (d ^ (n - ℓ)))) := by
    rw [reindex_smul_gen, reindex_one_gen, partialTrace_smul_one]
  rw [hτ, Matrix.smul_kronecker, Matrix.one_kronecker_one, reindex_smul_gen,
    reindex_one_gen, smul_smul_rev]
  congr 1
  have hne : ((d ^ ℓ : ℕ) : ℂ) ≠ 0 := by positivity
  field_simp [hne]

lemma inv_sqrt_mul_sqrt {x : ℝ} (hx : 0 < x) : (Real.sqrt x)⁻¹ * Real.sqrt x = 1 :=
  inv_mul_cancel₀ (Real.sqrt_pos.mpr hx).ne'

lemma sqrt_mul_inv_sqrt {x : ℝ} (hx : 0 < x) : Real.sqrt x * (Real.sqrt x)⁻¹ = 1 :=
  mul_inv_cancel₀ (Real.sqrt_pos.mpr hx).ne'

lemma hermSqrt_mul_self {D : ℕ} (M : Operator D) (h : M.PosSemidef) :
    hermSqrt M * hermSqrt M = M := by
  have hp : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr h
  unfold hermSqrt
  rw [← cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), ← CFC.sqrt_eq_real_sqrt M hp]
  exact CFC.sqrt_mul_sqrt_self M hp

lemma posDef_spectrum_pos {D : ℕ} {M : Operator D} (h : M.PosDef) :
    ∀ x ∈ spectrum ℝ (M : Matrix (Fin D) (Fin D) ℂ), 0 < x :=
  fun _x hx => h.isStrictlyPositive.spectrum_pos hx

lemma continuousOn_inv_sqrt {s : Set ℝ} (hs : ∀ x ∈ s, 0 < x) :
    ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) s := by
  refine ContinuousOn.inv₀ (Continuous.continuousOn Real.continuous_sqrt) ?_
  intro x hx
  exact (Real.sqrt_pos.mpr (hs x hx)).ne'

lemma hermInvSqrt_mul_hermSqrt {D : ℕ} (M : Operator D) (h : M.PosDef) :
    hermInvSqrt M * hermSqrt M = 1 := by
  have hmul : cfc (fun x : ℝ => (Real.sqrt x)⁻¹) M * cfc (fun x : ℝ => Real.sqrt x) M
      = cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * Real.sqrt x) M :=
    (cfc_mul (fun x : ℝ => (Real.sqrt x)⁻¹) (fun x : ℝ => Real.sqrt x) M
      (continuousOn_inv_sqrt (posDef_spectrum_pos h)) (Continuous.continuousOn Real.continuous_sqrt)).symm
  have hEq : Set.EqOn (fun x : ℝ => (Real.sqrt x)⁻¹ * Real.sqrt x) (fun _ : ℝ => 1)
      (spectrum ℝ (M : Matrix (Fin D) (Fin D) ℂ)) := by
    intro x hx
    exact inv_sqrt_mul_sqrt (posDef_spectrum_pos h x hx)
  have hcongr : cfc (fun x : ℝ => (Real.sqrt x)⁻¹ * Real.sqrt x) M = cfc (fun _ : ℝ => 1) M :=
    cfc_congr (f := fun x : ℝ => (Real.sqrt x)⁻¹ * Real.sqrt x) (g := fun _ : ℝ => 1)
      (a := M) hEq
  have h1 : cfc (fun _ : ℝ => (1 : ℝ)) M = 1 :=
    cfc_const (1 : ℝ) M (h.isHermitian.isSelfAdjoint) |>.trans (map_one _)
  unfold hermSqrt hermInvSqrt
  rw [hmul, hcongr, h1]

lemma hermSqrt_mul_hermInvSqrt {D : ℕ} (M : Operator D) (h : M.PosDef) :
    hermSqrt M * hermInvSqrt M = 1 := by
  have hmul : cfc (fun x : ℝ => Real.sqrt x) M * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) M
      = cfc (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) M :=
    (cfc_mul (fun x : ℝ => Real.sqrt x) (fun x : ℝ => (Real.sqrt x)⁻¹) M
      (Continuous.continuousOn Real.continuous_sqrt) (continuousOn_inv_sqrt (posDef_spectrum_pos h))).symm
  have hEq : Set.EqOn (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) (fun _ : ℝ => 1)
      (spectrum ℝ (M : Matrix (Fin D) (Fin D) ℂ)) := by
    intro x hx
    exact sqrt_mul_inv_sqrt (posDef_spectrum_pos h x hx)
  have hcongr : cfc (fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) M = cfc (fun _ : ℝ => 1) M :=
    cfc_congr (f := fun x : ℝ => Real.sqrt x * (Real.sqrt x)⁻¹) (g := fun _ : ℝ => 1)
      (a := M) hEq
  have h1 : cfc (fun _ : ℝ => (1 : ℝ)) M = 1 :=
    cfc_const (1 : ℝ) M (h.isHermitian.isSelfAdjoint) |>.trans (map_one _)
  unfold hermSqrt hermInvSqrt
  rw [hmul, hcongr, h1]

lemma sandwich_of_inv {D : ℕ} (a b x : Operator D) (hab : a * b = 1) (hba : b * a = 1)
    (hx : x = b * b) : a * x * a = 1 := by
  subst hx
  have hkey : a * (b * b) * a = (a * b) * (b * a) := by noncomm_ring
  rw [hkey, hab, hba, one_mul]

lemma hermInvSqrt_mul_mul_hermInvSqrt {D : ℕ} (M : Operator D) (h : M.PosDef) :
    hermInvSqrt M * M * hermInvSqrt M = 1 :=
  sandwich_of_inv (hermInvSqrt M) (hermSqrt M) M
    (hermInvSqrt_mul_hermSqrt M h) (hermSqrt_mul_hermInvSqrt M h)
    (hermSqrt_mul_self M h.posSemidef).symm

lemma petzHeatBath_stationary {n ℓ d : ℕ} (c : PetzCut n ℓ) (σ : Operator (d ^ n))
    (hσ : σ.PosSemidef)
    (hσA : (PartialTrace (Matrix.reindex (c.matrixEquiv (d := d)) (c.matrixEquiv (d := d)) σ)).PosDef) :
    petzHeatBath c σ σ = σ := by
  set e := c.matrixEquiv (d := d) with he
  have hdef : petzHeatBath c σ σ
      = hermSqrt σ * Matrix.reindex e.symm e.symm
          ((hermInvSqrt (PartialTrace (Matrix.reindex e e σ))
            * PartialTrace (Matrix.reindex e e σ)
            * hermInvSqrt (PartialTrace (Matrix.reindex e e σ)))
            ⊗ₖ (1 : Operator (d ^ ℓ))) * hermSqrt σ := by
    unfold petzHeatBath
    rfl
  rw [hdef, hermInvSqrt_mul_mul_hermInvSqrt _ hσA, Matrix.one_kronecker_one,
    reindex_one_gen, Matrix.mul_one, hermSqrt_mul_self _ hσ]

lemma clause29_rateOne_shape {ellStar : ℕ} (h0 : 0 < ellStar) :
    ∀ (n : ℕ) (_ : ellStar < n) (i : ℕ) (_ : i < n),
      siteUpdateRate n ellStar i = 1 := by
  intro n hn i _
  exact siteUpdateRate_eq_one (n := n) (ℓ := ellStar) (by omega) h0 (by omega) i

lemma clause29_petz_shape {n ℓ d : ℕ} (β : ℝ) (chain : PeriodicChain n d)
    (cuts : Fin n → PetzCut n ℓ)
    (hσ : (gibbsState β chain.H).PosSemidef)
    (hσA : ∀ s : Fin n,
      (PartialTrace (Matrix.reindex (PetzCut.matrixEquiv (d := d) (cuts s))
        (PetzCut.matrixEquiv (d := d) (cuts s))
        (gibbsState β chain.H))).PosDef) :
    (∀ s : Fin n,
      hermInvSqrt (PartialTrace
        (Matrix.reindex (PetzCut.matrixEquiv (d := d) (cuts s))
          (PetzCut.matrixEquiv (d := d) (cuts s)) (gibbsState β chain.H))) *
        hermSqrt (PartialTrace
          (Matrix.reindex (PetzCut.matrixEquiv (d := d) (cuts s))
            (PetzCut.matrixEquiv (d := d) (cuts s)) (gibbsState β chain.H))) = 1)
    ∧
    (∀ s : Fin n,
      petzHeatBath (cuts s) (gibbsState β chain.H) (gibbsState β chain.H)
        = gibbsState β chain.H) :=
  ⟨fun s => hermInvSqrt_mul_hermSqrt _ (hσA s),
    fun s => petzHeatBath_stationary (cuts s) (gibbsState β chain.H) hσ (hσA s)⟩

lemma clause30_static_shape {η : InfluenceProfile} {n ℓ : ℕ} (hℓ : 0 < ℓ) (hη : aEta η < ℓ) :
    (∀ i : ℕ, 1 ≤ i → i ≤ n → openSiteUpdateRate n ℓ i = 1)
    ∧ (aEta η = 2 * ∑' r : ℕ, η.eta (r + 1))
    ∧ (gammaOf η ℓ = 1 - aEta η / ℓ) ∧ (0 < gammaOf η ℓ) :=
  ⟨fun _ hi1 hin => openSiteUpdateRate_eq_one hℓ hi1 hin,
    aEta_eq_two_tsum η, gammaOf_eq η ℓ, gammaOf_pos hℓ hη⟩

lemma isCyclicBlockCut_iff_mem {n ℓ : ℕ} (s : ℕ) (c : PetzCut n ℓ) :
    IsCyclicBlockCut s c ↔
      ∀ i : Fin n, (∃ k : Fin ℓ, c.siteSplit i = Sum.inr k) ↔ i ∈ cyclicBlock n ℓ s := by
  simp only [IsCyclicBlockCut, cyclicBlock, Finset.mem_filter, Finset.mem_univ, true_and]

def cutSplitConfig {n ℓ d : ℕ} (c : PetzCut n ℓ) :
    SiteConfig n d ≃ ((Fin (n - ℓ) → Fin d) × (Fin ℓ → Fin d)) :=
  (c.siteSplit.arrowCongr (Equiv.refl (Fin d))).trans
    (Equiv.sumArrowEquivProdArrow (Fin (n - ℓ)) (Fin ℓ) (Fin d))

def recombine {n ℓ d : ℕ} (c : PetzCut n ℓ) (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d) :
    SiteConfig n d :=
  fun i => match c.siteSplit i with
    | Sum.inl k => u k
    | Sum.inr k => h k

lemma recombine_inl {n ℓ d : ℕ} (c : PetzCut n ℓ) (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d)
    (k : Fin (n - ℓ)) : recombine c u h (c.siteSplit.symm (Sum.inl k)) = u k := by
  simp only [recombine, Equiv.apply_symm_apply]

lemma recombine_inr {n ℓ d : ℕ} (c : PetzCut n ℓ) (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d)
    (k : Fin ℓ) : recombine c u h (c.siteSplit.symm (Sum.inr k)) = h k := by
  simp only [recombine, Equiv.apply_symm_apply]

lemma cutSplitConfig_apply {n ℓ d : ℕ} (c : PetzCut n ℓ) (g : SiteConfig n d) :
    cutSplitConfig c g = (g ∘ c.siteSplit.symm ∘ Sum.inl, g ∘ c.siteSplit.symm ∘ Sum.inr) := by
  simp only [cutSplitConfig, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow]
  rfl

lemma cutSplitConfig_recombine {n ℓ d : ℕ} (c : PetzCut n ℓ)
    (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d) :
    cutSplitConfig c (recombine c u h) = (u, h) := by
  rw [cutSplitConfig_apply]
  refine Prod.ext ?_ ?_
  · funext k
    exact recombine_inl c u h k
  · funext k
    exact recombine_inr c u h k

lemma matrixEquiv_configSplit {n ℓ d : ℕ} (c : PetzCut n ℓ) (g : SiteConfig n d) :
    c.matrixEquiv (d := d) (configEquiv n d g)
      = (configEquiv (n - ℓ) d (cutSplitConfig c g).1,
        configEquiv ℓ d (cutSplitConfig c g).2) := by
  simp only [PetzCut.matrixEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
    cutSplitConfig, Equiv.sumArrowEquivProdArrow, Equiv.prodCongr_apply]
  rfl

lemma matrixEquiv_symm_recombine {n ℓ d : ℕ} (c : PetzCut n ℓ)
    (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d) :
    (c.matrixEquiv (d := d)).symm (configEquiv (n - ℓ) d u, configEquiv ℓ d h)
      = configEquiv n d (recombine c u h) := by
  apply (c.matrixEquiv (d := d)).injective
  rw [Equiv.apply_symm_apply, matrixEquiv_configSplit, cutSplitConfig_recombine]

lemma sum_ite_eval_pi {ℓ d : ℕ} {j0 : Fin ℓ} {out : Fin d} :
    (∑ v : Fin ℓ → Fin d, if v j0 = out then (1 : ℝ) else 0) = (d ^ (ℓ - 1) : ℝ) := by
  have hcard : Fintype.card {j : Fin ℓ // j ≠ j0} = ℓ - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
  have hcardfn : Fintype.card ({j : Fin ℓ // j ≠ j0} → Fin d) = d ^ (ℓ - 1) := by
    rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, hcard, Fintype.card_fin]
  set e := Equiv.funSplitAt j0 (Fin d) with he
  have hsum : (∑ v : Fin ℓ → Fin d, if v j0 = out then (1 : ℝ) else 0)
      = ∑ p : Fin d × ({j : Fin ℓ // j ≠ j0} → Fin d), if p.1 = out then (1 : ℝ) else 0 :=
    Fintype.sum_equiv e
      (fun v : Fin ℓ → Fin d => if v j0 = out then (1 : ℝ) else 0)
      (fun p : Fin d × ({j : Fin ℓ // j ≠ j0} → Fin d) => if p.1 = out then (1 : ℝ) else 0)
      (fun v => by simp [he])
  rw [hsum, Fintype.sum_prod_type]
  have hinner : ∀ a : Fin d,
      (∑ w : {j : Fin ℓ // j ≠ j0} → Fin d, if a = out then (1 : ℝ) else 0)
        = if a = out then (d ^ (ℓ - 1) : ℝ) else 0 := by
    intro a
    rw [Finset.sum_const, Finset.card_univ, hcardfn]
    by_cases ha : a = out
    · subst ha
      simp
    · simp [ha]
  rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  exact Fintype.sum_ite_eq' out (fun _ => (d ^ (ℓ - 1) : ℝ))

lemma petzHeatBath_smul_one_diag {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) (g : SiteConfig n d) :
    (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ)
        (configEquiv n d g) (configEquiv n d g)
      = (((d ^ ℓ : ℕ) : ℂ)⁻¹) *
          ∑ h : Fin ℓ → Fin d,
            ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
              (configEquiv n d (recombine c (cutSplitConfig c g).1 h)) := by
  set e := c.matrixEquiv (d := d) with he
  rw [petzHeatBath_smul_one c k hk hd ρ]
  rw [Matrix.smul_apply]
  have hre : (Matrix.reindex e.symm e.symm
        (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ))))
        (configEquiv n d g) (configEquiv n d g)
      = (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ)))
          (e (configEquiv n d g)) (e (configEquiv n d g)) := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [hre, matrixEquiv_configSplit]
  have hkron : ((PartialTrace (Matrix.reindex e e ρ)) ⊗ₖ (1 : Operator (d ^ ℓ)))
        (configEquiv (n - ℓ) d (cutSplitConfig c g).1, configEquiv ℓ d (cutSplitConfig c g).2)
        (configEquiv (n - ℓ) d (cutSplitConfig c g).1, configEquiv ℓ d (cutSplitConfig c g).2)
      = PartialTrace (Matrix.reindex e e ρ)
          (configEquiv (n - ℓ) d (cutSplitConfig c g).1)
          (configEquiv (n - ℓ) d (cutSplitConfig c g).1) := by
    rw [Matrix.kronecker_apply]
    simp
  rw [hkron]
  have hpt : (PartialTrace (Matrix.reindex e e ρ))
        (configEquiv (n - ℓ) d (cutSplitConfig c g).1)
        (configEquiv (n - ℓ) d (cutSplitConfig c g).1)
      = ∑ b : Fin (d ^ ℓ),
          ρ (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b))
            (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b)) := by
    simp only [PartialTrace, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hpt]
  rw [smul_eq_mul]
  congr 1
  exact (Fintype.sum_equiv (configEquiv ℓ d)
    (fun h : Fin ℓ → Fin d =>
      ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
        (configEquiv n d (recombine c (cutSplitConfig c g).1 h)))
    (fun b : Fin (d ^ ℓ) =>
      ρ (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b))
        (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b)))
    (fun h => by
      beta_reduce
      rw [matrixEquiv_symm_recombine])).symm

lemma cutSplitConfig_symm_apply {n ℓ d : ℕ} (c : PetzCut n ℓ)
    (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d) :
    (cutSplitConfig c).symm (u, h) = recombine c u h := by
  apply (cutSplitConfig c).injective
  rw [Equiv.apply_symm_apply, cutSplitConfig_recombine]

lemma recombine_apply_inl {n ℓ d : ℕ} (c : PetzCut n ℓ) (u : Fin (n - ℓ) → Fin d)
    (v : Fin ℓ → Fin d) {i : Fin n} {k : Fin (n - ℓ)} (hi : c.siteSplit i = Sum.inl k) :
    recombine c u v i = u k := by
  simp [recombine, hi]

lemma recombine_apply_inr {n ℓ d : ℕ} (c : PetzCut n ℓ) (u : Fin (n - ℓ) → Fin d)
    (v : Fin ℓ → Fin d) {i : Fin n} {j : Fin ℓ} (hi : c.siteSplit i = Sum.inr j) :
    recombine c u v i = v j := by
  simp [recombine, hi]

lemma sum_re_diag_configEquiv {n d : ℕ} (ρ : Operator (d ^ n)) :
    (∑ y : SiteConfig n d, (ρ (configEquiv n d y) (configEquiv n d y)).re)
      = (Matrix.trace ρ).re := by
  have h : (∑ y : SiteConfig n d, ρ (configEquiv n d y) (configEquiv n d y))
      = Matrix.trace ρ := by
    rw [Equiv.sum_comp (configEquiv n d) (fun x => ρ x x)]
    simp [Matrix.trace]
  have h2 : (Matrix.trace ρ).re
      = ∑ y : SiteConfig n d, (ρ (configEquiv n d y) (configEquiv n d y)).re := by
    rw [← h]
    have h3 := map_sum Complex.reCLM
      (fun y : SiteConfig n d => ρ (configEquiv n d y) (configEquiv n d y)) Finset.univ
    have h4 : ∀ z : ℂ, ⇑Complex.reCLM z = z.re := fun _ => rfl
    simp only [h4] at h3
    exact h3
  exact h2.symm

lemma cutSplitConfig_symm_prod {n ℓ d : ℕ} (c : PetzCut n ℓ)
    (p : (Fin (n - ℓ) → Fin d) × (Fin ℓ → Fin d)) :
    (cutSplitConfig c).symm p = recombine c p.1 p.2 := by
  rw [← Prod.eta p, cutSplitConfig_symm_apply]

lemma sum_re_diag_recombine {n ℓ d : ℕ} (c : PetzCut n ℓ) (ρ : Operator (d ^ n))
    (i : Fin n) (out : Fin d) :
    (∑ g : SiteConfig n d, ∑ h : Fin ℓ → Fin d,
        (if g i = out then (1 : ℝ) else 0) *
          (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
            (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re)
    = if (∃ j : Fin ℓ, c.siteSplit i = Sum.inr j) then
        (d ^ (ℓ - 1) : ℝ) * (Matrix.trace ρ).re
      else (d ^ ℓ : ℝ) * siteMarginalMass ρ i out := by
  have hgsplit : ∀ (F : SiteConfig n d → ℝ),
      (∑ g : SiteConfig n d, F g)
        = ∑ u : Fin (n - ℓ) → Fin d, ∑ v : Fin ℓ → Fin d,
            F (recombine c u v) := by
    intro F
    have h1 : (∑ u : Fin (n - ℓ) → Fin d, ∑ v : Fin ℓ → Fin d, F (recombine c u v))
        = ∑ p : (Fin (n - ℓ) → Fin d) × (Fin ℓ → Fin d), F (recombine c p.1 p.2) :=
      (Fintype.sum_prod_type (fun p : (Fin (n - ℓ) → Fin d) × (Fin ℓ → Fin d) =>
        F (recombine c p.1 p.2))).symm
    have h2 : (∑ p : (Fin (n - ℓ) → Fin d) × (Fin ℓ → Fin d), F (recombine c p.1 p.2))
        = ∑ p, F ((cutSplitConfig c).symm p) :=
      Finset.sum_congr rfl (fun p _ => by rw [cutSplitConfig_symm_prod])
    rw [h1, h2, Equiv.sum_comp ((cutSplitConfig c).symm) F]
  have huhsplit : ∀ (F : SiteConfig n d → ℝ),
      (∑ u : Fin (n - ℓ) → Fin d, ∑ h : Fin ℓ → Fin d, F (recombine c u h))
        = ∑ y : SiteConfig n d, F y := fun F => (hgsplit F).symm
  have hF : ∀ (u : Fin (n - ℓ) → Fin d) (v : Fin ℓ → Fin d),
      (∑ h : Fin ℓ → Fin d,
          (if recombine c u v i = out then (1 : ℝ) else 0) *
            (ρ (configEquiv n d (recombine c u h))
              (configEquiv n d (recombine c u h))).re)
      = (if recombine c u v i = out then (1 : ℝ) else 0) *
          ∑ h : Fin ℓ → Fin d,
            (ρ (configEquiv n d (recombine c u h))
              (configEquiv n d (recombine c u h))).re := by
    intro u v
    rw [Finset.mul_sum]
  rw [hgsplit (fun g =>
    ∑ h : Fin ℓ → Fin d,
      (if g i = out then (1 : ℝ) else 0) *
        (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
          (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re)]
  have hrew : ∀ (u : Fin (n - ℓ) → Fin d) (v : Fin ℓ → Fin d),
      (cutSplitConfig c (recombine c u v)).1 = u := by
    intro u v
    rw [cutSplitConfig_recombine]
  simp only [hrew]
  rcases hc : c.siteSplit i with k | j
  · have hiu : ∀ (u : Fin (n - ℓ) → Fin d) (v : Fin ℓ → Fin d),
        recombine c u v i = u k := fun u v => recombine_apply_inl c u v hc
    have hih : ∀ (u : Fin (n - ℓ) → Fin d) (h : Fin ℓ → Fin d),
        recombine c u h i = u k := fun u h => recombine_apply_inl c u h hc
    simp only [hF]
    simp only [hiu]
    have hfree : ∀ (u : Fin (n - ℓ) → Fin d),
        (∑ v : Fin ℓ → Fin d, (if u k = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re)
        = (d ^ ℓ : ℝ) * ((if u k = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re) := by
      intro u
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Fintype.card_fin]
    simp only [hfree]
    rw [← Finset.mul_sum]
    have hchain : (∑ u : Fin (n - ℓ) → Fin d,
          (if u k = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re)
        = siteMarginalMass ρ i out := by
      have hmul : ∀ u : Fin (n - ℓ) → Fin d,
          (if u k = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re
          = ∑ h : Fin ℓ → Fin d,
              (if u k = out then (1 : ℝ) else 0) *
                (ρ (configEquiv n d (recombine c u h))
                  (configEquiv n d (recombine c u h))).re := by
        intro u
        rw [Finset.mul_sum]
      simp only [hmul]
      have hstep : (∑ u : Fin (n - ℓ) → Fin d, ∑ h : Fin ℓ → Fin d,
            (if u k = out then (1 : ℝ) else 0) *
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re)
          = ∑ y : SiteConfig n d, (if y i = out then (1 : ℝ) else 0) *
              (ρ (configEquiv n d y) (configEquiv n d y)).re := by
        rw [← huhsplit (fun y : SiteConfig n d =>
          (if y i = out then (1 : ℝ) else 0) * (ρ (configEquiv n d y) (configEquiv n d y)).re)]
        exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun h _ => by
          have hik : recombine c u h i = u k := hih u h
          by_cases hu : u k = out
          · have hy : recombine c u h i = out := by rw [hik]; exact hu
            simp [hu, hy]
          · have hy : ¬ recombine c u h i = out := by rw [hik]; exact hu
            simp [hu, hy]))
      rw [hstep]
      simp only [siteMarginalMass]
      exact Finset.sum_congr rfl (fun y _ => by
        by_cases hy : y i = out <;> simp [hy])
    rw [hchain, if_neg]
    rintro ⟨j, hj⟩
    simp at hj
  · have hiv : ∀ (u : Fin (n - ℓ) → Fin d) (v : Fin ℓ → Fin d),
        recombine c u v i = v j := fun u v => recombine_apply_inr c u v hc
    simp only [hF]
    simp only [hiv]
    have hmul : ∀ (u : Fin (n - ℓ) → Fin d),
        (∑ v : Fin ℓ → Fin d, (if v j = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re)
        = (∑ v : Fin ℓ → Fin d, if v j = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re := by
      intro u
      rw [Finset.sum_mul]
    simp only [hmul]
    have hcount : (∑ v : Fin ℓ → Fin d, if v j = out then (1 : ℝ) else 0) = (d ^ (ℓ - 1) : ℝ) :=
      sum_ite_eval_pi
    have hfact : (∑ u : Fin (n - ℓ) → Fin d,
          (∑ v : Fin ℓ → Fin d, if v j = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c u h))
                (configEquiv n d (recombine c u h))).re)
        = (d ^ (ℓ - 1) : ℝ) *
            ∑ u : Fin (n - ℓ) → Fin d,
              ∑ h : Fin ℓ → Fin d,
                (ρ (configEquiv n d (recombine c u h))
                  (configEquiv n d (recombine c u h))).re := by
      rw [hcount, ← Finset.mul_sum]
    rw [hfact]
    have hsum : (∑ u : Fin (n - ℓ) → Fin d,
          ∑ h : Fin ℓ → Fin d,
            (ρ (configEquiv n d (recombine c u h))
              (configEquiv n d (recombine c u h))).re)
        = (Matrix.trace ρ).re := by
      rw [huhsplit (fun y : SiteConfig n d =>
        (ρ (configEquiv n d y) (configEquiv n d y)).re)]
      exact sum_re_diag_configEquiv ρ
    rw [hsum, if_pos ⟨j, rfl⟩]

lemma siteMarginalMass_petzHeatBath_smul_one {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    siteMarginalMass (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ) i out
      = if (∃ j : Fin ℓ, c.siteSplit i = Sum.inr j) then
          (1 / (d : ℝ)) * (Matrix.trace ρ).re
        else siteMarginalMass ρ i out := by
  have hE : (((d ^ ℓ : ℕ) : ℂ)⁻¹) = ((((d ^ ℓ : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := cast_inv_nat _
  have hterm : ∀ g : SiteConfig n d,
      ((petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ)
        (configEquiv n d g) (configEquiv n d g)).re
      = (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
          ∑ h : Fin ℓ → Fin d,
            (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
              (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re := by
    intro g
    rw [petzHeatBath_smul_one_diag c k hk hd ρ g, hE, Complex.re_ofReal_mul]
    congr 1
    exact map_sum Complex.reCLM (fun h : Fin ℓ → Fin d =>
      ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
        (configEquiv n d (recombine c (cutSplitConfig c g).1 h))) Finset.univ
  simp only [siteMarginalMass, hterm]
  have hterm2 : ∀ g : SiteConfig n d,
      (if g i = out then (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
          ∑ h : Fin ℓ → Fin d,
            (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
              (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re
        else 0)
      = (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
          ((if g i = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
                (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re) := by
    intro g
    by_cases hg : g i = out
    · rw [if_pos hg, if_pos hg]
      simp
    · rw [if_neg hg, if_neg hg]
      simp
  have hA : (∑ g : SiteConfig n d,
        (if g i = out then (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
                (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re
          else 0))
      = ∑ g : SiteConfig n d, (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
          ((if g i = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
                (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re) :=
    Finset.sum_congr rfl (fun g _ => hterm2 g)
  rw [hA]
  have hB : (∑ g : SiteConfig n d, (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
          ((if g i = out then (1 : ℝ) else 0) *
            ∑ h : Fin ℓ → Fin d,
              (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
                (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re))
      = (((d ^ ℓ : ℕ) : ℝ)⁻¹) *
          ∑ g : SiteConfig n d, ∑ h : Fin ℓ → Fin d,
            (if g i = out then (1 : ℝ) else 0) *
              (ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 h))
                (configEquiv n d (recombine c (cutSplitConfig c g).1 h))).re := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun g _ => by rw [Finset.mul_sum])
  rw [hB, sum_re_diag_recombine c ρ i out]
  by_cases hb : ∃ j : Fin ℓ, c.siteSplit i = Sum.inr j
  · obtain ⟨j, hj⟩ := hb
    simp only [if_pos (show ∃ j : Fin ℓ, c.siteSplit i = Sum.inr j from ⟨j, hj⟩)]
    have hL : (d : ℝ) ^ ℓ = (d : ℝ) ^ (ℓ - 1) * d := by
      have h0 : 0 < ℓ := Fin.pos j
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos h0]
      rw [pow_succ]
      rfl
    have hpow0 : (d : ℝ) ^ (ℓ - 1) ≠ 0 := by
      positivity
    have hco : (((d ^ ℓ : ℕ) : ℝ)⁻¹) * (d : ℝ) ^ (ℓ - 1) = (d : ℝ)⁻¹ := by
      rw [Nat.cast_pow, hL, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hpow0, mul_one]
    rw [← mul_assoc, hco, one_div]
  · simp only [if_neg hb]
    have hco2 : (((d ^ ℓ : ℕ) : ℝ)⁻¹) * (d : ℝ) ^ ℓ = 1 := by
      rw [Nat.cast_pow]
      exact inv_mul_cancel₀ (pow_ne_zero _ (by positivity))
    rw [← mul_assoc, hco2, one_mul]
    rfl

lemma siteMarginalMass_add {n d : ℕ} (ρ τ : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    siteMarginalMass (ρ + τ) i out = siteMarginalMass ρ i out + siteMarginalMass τ i out := by
  simp only [siteMarginalMass, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun g _ => by
    by_cases hg : g i = out <;> simp [hg, Complex.add_re])

lemma siteMarginalMass_sub {n d : ℕ} (ρ τ : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    siteMarginalMass (ρ - τ) i out = siteMarginalMass ρ i out - siteMarginalMass τ i out := by
  simp only [siteMarginalMass, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun g _ => by
    by_cases hg : g i = out <;> simp [hg, Complex.sub_re])

lemma siteMarginalMass_smul_real {n d : ℕ} (c : ℝ) (ρ : Operator (d ^ n)) (i : Fin n)
    (out : Fin d) :
    siteMarginalMass (((c : ℝ) : ℂ) • ρ) i out = c * siteMarginalMass ρ i out := by
  simp only [siteMarginalMass, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun g _ => by
    by_cases hg : g i = out <;> simp [hg])

lemma siteMarginalMass_sum {n d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Operator (d ^ n))
    (i : Fin n) (out : Fin d) :
    siteMarginalMass (∑ k ∈ s, f k) i out = ∑ k ∈ s, siteMarginalMass (f k) i out := by
  classical
  induction s using Finset.induction with
  | empty => simp [siteMarginalMass]
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, siteMarginalMass_add, ih]

lemma sum_block_membership {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (hle : ℓ ≤ n) (i : ℕ) :
    (∑ s : Fin n, if (i + n - s) % n < ℓ then (1 : ℝ) else 0) = ℓ := by
  have hne : (ℓ : ℝ) ≠ 0 := by positivity
  have hrate := siteUpdateRate_eq_one hn hℓ hle i
  rw [Fin.sum_univ_eq_sum_range (f := fun t : ℕ => if (i + n - t) % n < ℓ then (1 : ℝ) else 0)]
  have h1 : (∑ s ∈ Finset.range n, if (i + n - s) % n < ℓ then (1 : ℝ) else 0)
      = (ℓ : ℝ) * ∑ s ∈ Finset.range n, if (i + n - s) % n < ℓ then (1 / ℓ : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hh : (i + n - s) % n < ℓ
    · simp [hh]
      field_simp [hne]
    · simp [hh]
  rw [h1]
  have h2 : (∑ s ∈ Finset.range n, if (i + n - s) % n < ℓ then (1 / ℓ : ℝ) else 0)
      = siteUpdateRate n ℓ i := rfl
  rw [h2, hrate, mul_one]

lemma siteMarginalMass_petzGenerator_zero {n ℓ d : ℕ} (β : ℝ) (hd : 0 < d) (hℓ : 0 < ℓ)
    (hle : ℓ ≤ n) (cuts : Fin n → PetzCut n ℓ) (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (ρ : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    siteMarginalMass (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))) ρ) i out
      = (1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out := by
  have hσ : gibbsState β (0 : Operator (d ^ n))
      = (((((d ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ n))) := by
    rw [gibbsState_zero, cast_inv_nat]
  have hk : (0 : ℝ) < ((d ^ n : ℕ) : ℝ)⁻¹ := by positivity
  have hper : ∀ s : Fin n,
      siteMarginalMass (petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ) i out
        = if (∃ j : Fin ℓ, (cuts s).siteSplit i = Sum.inr j) then
            (1 / (d : ℝ)) * (Matrix.trace ρ).re
          else siteMarginalMass ρ i out := by
    intro s
    rw [hσ]
    exact siteMarginalMass_petzHeatBath_smul_one (cuts s) _ hk hd ρ i out
  have hsplit : ∀ s : Fin n,
      siteMarginalMass (petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ - ρ) i out
        = if (i + n - s.val) % n < ℓ then
            (1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out
          else 0 := by
    intro s
    rw [siteMarginalMass_sub, hper]
    by_cases hb : ∃ j : Fin ℓ, (cuts s).siteSplit i = Sum.inr j
    · obtain ⟨j, hj⟩ := hb
      have hmod : (i + n - s.val) % n < ℓ := (hc s i).mp ⟨j, hj⟩
      simp only [if_pos (show ∃ j : Fin ℓ, (cuts s).siteSplit i = Sum.inr j from ⟨j, hj⟩),
        if_pos hmod]
    · have hmod : ¬ (i + n - s.val) % n < ℓ := fun hh => hb ((hc s i).mpr hh)
      simp only [if_neg hb, if_neg hmod, sub_self]
  have hscalar : ((1 : ℂ) / ℓ) = (((((ℓ : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    rw [one_div]
    exact cast_inv_nat _
  have hmain : siteMarginalMass
        (((1 : ℂ) / ℓ) • ∑ s : Fin n,
          (petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ - ρ)) i out
      = (((ℓ : ℕ) : ℝ)⁻¹) *
          ∑ s : Fin n,
            (if (i + n - s.val) % n < ℓ then
              (1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out
            else 0) := by
    rw [hscalar, siteMarginalMass_smul_real]
    rw [siteMarginalMass_sum (s := Finset.univ) (f := fun s : Fin n =>
      petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ - ρ)]
    congr 1
    exact Finset.sum_congr rfl (fun s _ => hsplit s)
  have hpow : (∑ s : Fin n,
        (if (i + n - s.val) % n < ℓ then
          (1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out
        else 0))
      = (ℓ : ℝ) * ((1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out) := by
    have hn : 0 < n := by omega
    have hcount : (∑ s : Fin n, if (i + n - s.val) % n < ℓ then (1 : ℝ) else 0) = ℓ :=
      sum_block_membership hn hℓ hle i
    have hfac : (∑ s : Fin n,
          (if (i + n - s.val) % n < ℓ then
            (1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out
          else 0))
        = (∑ s : Fin n, if (i + n - s.val) % n < ℓ then (1 : ℝ) else 0) *
            ((1 / (d : ℝ)) * (Matrix.trace ρ).re - siteMarginalMass ρ i out) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun s _ => by
        by_cases hh : (i + n - s.val) % n < ℓ <;> simp [hh])
    rw [hfac, hcount]
  have hdef : siteMarginalMass
        (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))) ρ) i out
      = siteMarginalMass
          (((1 : ℂ) / ℓ) • ∑ s : Fin n,
            (petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ - ρ)) i out := rfl
  rw [hdef, hmain, hpow]
  have hne : (ℓ : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

end Qatlib.Papers.SpinChainMix26.RapidMixing

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open scoped ComplexOrder Kronecker MatrixOrder

lemma partialTrace_add {D E : ℕ} (A B : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (A + B) = PartialTrace A + PartialTrace B := by
  ext i j
  simp only [PartialTrace, Matrix.add_apply]
  exact Finset.sum_add_distrib

lemma partialTrace_smul {D E : ℕ} (c : ℂ) (A : Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ) :
    PartialTrace (c • A) = c • PartialTrace A := by
  ext i j
  simp only [PartialTrace, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]

lemma reindex_add_gen {α : Type*} {m l n o : Type*} [Add α]
    (em : m ≃ l) (en : n ≃ o) (A B : Matrix m n α) :
    Matrix.reindex em en (A + B) = Matrix.reindex em en A + Matrix.reindex em en B := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.add_apply]

lemma reindex_smul_gen' {α : Type*} {R : Type*} {m l n o : Type*} [SMul R α]
    (em : m ≃ l) (en : n ≃ o) (c : R) (A : Matrix m n α) :
    Matrix.reindex em en (c • A) = c • Matrix.reindex em en A := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]

lemma petzHeatBath_add {n ℓ d : ℕ} (c : PetzCut n ℓ) (σ ρ τ : Operator (d ^ n)) :
    petzHeatBath c σ (ρ + τ) = petzHeatBath c σ ρ + petzHeatBath c σ τ := by
  set e := c.matrixEquiv (d := d) with he
  set σA := PartialTrace (Matrix.reindex e e σ) with hσA
  have key : ∀ ρ' : Operator (d ^ n),
      petzHeatBath c σ ρ'
        = hermSqrt σ *
            Matrix.reindex e.symm e.symm
              ((hermInvSqrt σA * PartialTrace (Matrix.reindex e e ρ') * hermInvSqrt σA)
                ⊗ₖ (1 : Operator (d ^ ℓ))) * hermSqrt σ := by
    intro ρ'
    rw [he, hσA]
    rfl
  rw [key (ρ + τ), key ρ, key τ]
  have hre : Matrix.reindex e e (ρ + τ)
      = Matrix.reindex e e ρ + Matrix.reindex e e τ := reindex_add_gen _ _ _ _
  have hpt : PartialTrace (Matrix.reindex e e (ρ + τ))
      = PartialTrace (Matrix.reindex e e ρ) + PartialTrace (Matrix.reindex e e τ) := by
    rw [hre, partialTrace_add]
  have hsand : ∀ (X Y : Matrix (Fin (d ^ (n - ℓ))) (Fin (d ^ (n - ℓ))) ℂ),
      hermInvSqrt σA * (X + Y) * hermInvSqrt σA
        = hermInvSqrt σA * X * hermInvSqrt σA + hermInvSqrt σA * Y * hermInvSqrt σA := by
    intro X Y
    rw [mul_add, add_mul]
  rw [hpt, hsand, Matrix.add_kronecker]
  have hre2 : ∀ (X Y : Matrix (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ))
      (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) ℂ),
      Matrix.reindex e.symm e.symm (X + Y)
        = Matrix.reindex e.symm e.symm X + Matrix.reindex e.symm e.symm Y :=
    fun X Y => reindex_add_gen _ _ _ _
  rw [hre2, mul_add, add_mul]

lemma petzHeatBath_smul {n ℓ d : ℕ} (c : PetzCut n ℓ) (σ : Operator (d ^ n)) (k : ℂ)
    (ρ : Operator (d ^ n)) :
    petzHeatBath c σ (k • ρ) = k • petzHeatBath c σ ρ := by
  set e := c.matrixEquiv (d := d) with he
  set σA := PartialTrace (Matrix.reindex e e σ) with hσA
  have key : ∀ ρ' : Operator (d ^ n),
      petzHeatBath c σ ρ'
        = hermSqrt σ *
            Matrix.reindex e.symm e.symm
              ((hermInvSqrt σA * PartialTrace (Matrix.reindex e e ρ') * hermInvSqrt σA)
                ⊗ₖ (1 : Operator (d ^ ℓ))) * hermSqrt σ := by
    intro ρ'
    rw [he, hσA]
    rfl
  rw [key (k • ρ), key ρ]
  have hre : Matrix.reindex e e (k • ρ) = k • Matrix.reindex e e ρ :=
    reindex_smul_gen' _ _ _ _
  have hpt : PartialTrace (Matrix.reindex e e (k • ρ))
      = k • PartialTrace (Matrix.reindex e e ρ) := by
    rw [hre, partialTrace_smul]
  have hsand : ∀ (X : Matrix (Fin (d ^ (n - ℓ))) (Fin (d ^ (n - ℓ))) ℂ),
      hermInvSqrt σA * (k • X) * hermInvSqrt σA
        = k • (hermInvSqrt σA * X * hermInvSqrt σA) := by
    intro X
    rw [mul_smul_comm, smul_mul_assoc]
  rw [hpt, hsand, Matrix.smul_kronecker]
  have hre2 : ∀ (X : Matrix (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ))
      (Fin (d ^ (n - ℓ)) × Fin (d ^ ℓ)) ℂ),
      Matrix.reindex e.symm e.symm (k • X) = k • Matrix.reindex e.symm e.symm X :=
    fun X => reindex_smul_gen' _ _ _ _
  rw [hre2, mul_smul_comm, smul_mul_assoc]

lemma petzGenerator_add {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (σ ρ τ : Operator (d ^ n)) :
    petzGenerator cuts σ (ρ + τ) = petzGenerator cuts σ ρ + petzGenerator cuts σ τ := by
  unfold petzGenerator
  have h1 : ∑ s : Fin n,
        (petzHeatBath (cuts s) σ (ρ + τ) - (ρ + τ))
      = ∑ s : Fin n, ((petzHeatBath (cuts s) σ ρ - ρ) + (petzHeatBath (cuts s) σ τ - τ)) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [petzHeatBath_add, add_sub_add_comm]
  rw [h1, Finset.sum_add_distrib, smul_add]

lemma petzGenerator_smul {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (σ : Operator (d ^ n))
    (k : ℂ) (ρ : Operator (d ^ n)) :
    petzGenerator cuts σ (k • ρ) = k • petzGenerator cuts σ ρ := by
  unfold petzGenerator
  have h1 : ∑ s : Fin n,
        (petzHeatBath (cuts s) σ (k • ρ) - k • ρ)
      = ∑ s : Fin n, (k • (petzHeatBath (cuts s) σ ρ - ρ)) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [petzHeatBath_smul, smul_sub]
  rw [h1, Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm ((1 : ℂ) / ℓ) k, ← Finset.smul_sum]

lemma petzGenerator_zero {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (σ : Operator (d ^ n)) :
    petzGenerator cuts σ 0 = 0 := by
  have h := petzGenerator_add cuts σ 0 0
  rw [add_zero] at h
  have h' : petzGenerator cuts σ 0 + 0
      = petzGenerator cuts σ 0 + petzGenerator cuts σ 0 := by
    rw [add_zero]
    exact h
  exact (add_left_cancel h').symm

lemma petzGenerator_sum {n ℓ d : ℕ} {ι : Type*} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (s : Finset ι) (f : ι → Operator (d ^ n)) :
    petzGenerator cuts σ (∑ i ∈ s, f i) = ∑ i ∈ s, petzGenerator cuts σ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, petzGenerator_zero]
  | insert i s hnot ih =>
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot, petzGenerator_add, ih]

lemma trace_reindex_gen {α : Type*} {m l : Type*} [Fintype m] [Fintype l] [AddCommMonoid α]
    (em : m ≃ l) (A : Matrix m m α) :
    Matrix.trace (Matrix.reindex em em A) = Matrix.trace A := by
  simp only [Matrix.trace, Matrix.reindex_apply]
  exact Equiv.sum_comp em.symm (fun i => A i i)

lemma tensorProductConfig_pureZero_diag {n d : ℕ} (g : SiteConfig n d) :
    tensorProductConfig (fun _ : Fin n => pureZero d) g g
      = if ∀ i : Fin n, (g i).val = 0 then (1 : ℂ) else 0 := by
  simp only [tensorProductConfig, pureZero]
  have h1 : ∀ i : Fin n,
      (if (g i).val = 0 ∧ (g i).val = 0 then (1 : ℂ) else 0)
        = (if (g i).val = 0 then (1 : ℂ) else 0) := by
    intro i
    by_cases hh : (g i).val = 0 <;> simp [hh]
  simp only [h1]
  by_cases h : ∀ i : Fin n, (g i).val = 0
  · have h2 : ∀ i : Fin n, (if (g i).val = 0 then (1 : ℂ) else 0) = 1 :=
      fun i => if_pos (h i)
    simp only [h2, Finset.prod_const_one]
    rw [if_pos h]
  · obtain ⟨i0, hi0⟩ := not_forall.mp h
    rw [if_neg h]
    apply Finset.prod_eq_zero (i := i0)
    · exact Finset.mem_univ i0
    · simp [hi0]

lemma tensorProductOp_pureZero_diag {n d : ℕ} (g : SiteConfig n d) :
    tensorProductOp (fun _ : Fin n => pureZero d) (configEquiv n d g) (configEquiv n d g)
      = if ∀ i : Fin n, (g i).val = 0 then (1 : ℂ) else 0 := by
  simp only [tensorProductOp, Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [Equiv.symm_apply_apply]
  exact tensorProductConfig_pureZero_diag g

lemma sum_ite_all_zero {n d : ℕ} (hd : 0 < d) :
    (∑ g : SiteConfig n d, if ∀ i : Fin n, (g i).val = 0 then (1 : ℂ) else 0) = 1 := by
  haveI : NeZero d := NeZero.of_pos hd
  have hmem : ∀ g : SiteConfig n d,
      (∀ i : Fin n, (g i).val = 0) ↔ g = fun _ => (0 : Fin d) := by
    intro g
    constructor
    · intro h
      funext i
      exact Fin.eq_of_val_eq (h i)
    · intro h i
      rw [h]
      simp
  have h2 : (∑ g : SiteConfig n d, if ∀ i : Fin n, (g i).val = 0 then (1 : ℂ) else 0)
      = ∑ g : SiteConfig n d, if g = (fun _ => (0 : Fin d)) then (1 : ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro g _
    simp only [hmem]
  rw [h2, Fintype.sum_ite_eq']

lemma trace_tensorProductOp_pureZero {n d : ℕ} (hd : 0 < d) :
    Matrix.trace (tensorProductOp (fun _ : Fin n => pureZero d)) = 1 := by
  have hre : Matrix.trace (tensorProductOp (fun _ : Fin n => pureZero d))
      = ∑ g : SiteConfig n d,
          tensorProductConfig (fun _ : Fin n => pureZero d) g g := by
    simp only [tensorProductOp]
    rw [trace_reindex_gen]
    simp only [Matrix.trace, Matrix.diag_apply]
  rw [hre]
  have hcong : ∀ g : SiteConfig n d,
      tensorProductConfig (fun _ : Fin n => pureZero d) g g
        = if ∀ i : Fin n, (g i).val = 0 then (1 : ℂ) else 0 :=
    fun g => tensorProductConfig_pureZero_diag g
  simp only [hcong]
  exact sum_ite_all_zero hd

lemma siteMarginalMass_pureZero {n d : ℕ} (hd : 0 < d) (i : Fin n) (out : Fin d) :
    siteMarginalMass (tensorProductOp (fun _ : Fin n => pureZero d)) i out
      = if out.val = 0 then (1 : ℝ) else 0 := by
  haveI : NeZero d := NeZero.of_pos hd
  simp only [siteMarginalMass]
  have hdiag : ∀ g : SiteConfig n d,
      (tensorProductOp (fun _ : Fin n => pureZero d) (configEquiv n d g) (configEquiv n d g)).re
        = (if ∀ j : Fin n, (g j).val = 0 then (1 : ℂ) else 0).re := by
    intro g
    rw [tensorProductOp_pureZero_diag]
  simp only [hdiag]
  have hre : ∀ g : SiteConfig n d,
      (if ∀ j : Fin n, (g j).val = 0 then (1 : ℂ) else 0).re
        = (if ∀ j : Fin n, (g j).val = 0 then (1 : ℝ) else 0) := by
    intro g
    by_cases hh : ∀ j : Fin n, (g j).val = 0
    · rw [if_pos hh, if_pos hh, Complex.one_re]
    · rw [if_neg hh, if_neg hh, Complex.zero_re]
  simp only [hre]
  have hcom : ∀ g : SiteConfig n d,
      (if g i = out then (if ∀ j : Fin n, (g j).val = 0 then (1 : ℝ) else 0) else 0)
        = (if g i = out ∧ ∀ j : Fin n, (g j).val = 0 then (1 : ℝ) else 0) := by
    intro g
    by_cases h1 : g i = out
    · by_cases h2 : ∀ j : Fin n, (g j).val = 0 <;> simp [h1, h2]
    · simp [h1]
  simp only [hcom]
  by_cases hout : out.val = 0
  · rw [if_pos hout]
    have hC : ∀ g : SiteConfig n d,
        (g i = out ∧ ∀ j : Fin n, (g j).val = 0) ↔ g = fun _ => (0 : Fin d) := by
      intro g
      constructor
      · intro ⟨_, h2⟩
        funext j
        exact Fin.eq_of_val_eq (h2 j)
      · intro h
        subst h
        have hout0 : out = 0 := Fin.eq_of_val_eq hout
        constructor
        · rw [hout0]
        · intro j
          simp
    have h2 : (∑ g : SiteConfig n d, if g i = out ∧ ∀ j : Fin n, (g j).val = 0
          then (1 : ℝ) else 0)
        = ∑ g : SiteConfig n d, if g = (fun _ => (0 : Fin d)) then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      simp only [hC]
    rw [h2, Fintype.sum_ite_eq']
  · rw [if_neg hout]
    have hC : ∀ g : SiteConfig n d, ¬ (g i = out ∧ ∀ j : Fin n, (g j).val = 0) := by
      intro g ⟨h1, h2⟩
      have hgi : (g i).val = 0 := h2 i
      rw [h1] at hgi
      exact hout (by simpa using hgi)
    rw [Finset.sum_eq_zero]
    intro g _
    exact if_neg (hC g)

lemma trace_petzHeatBath_smul_one {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) :
    Matrix.trace (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ)
      = Matrix.trace ρ := by
  rw [petzHeatBath_smul_one c k hk hd ρ]
  rw [Matrix.trace_smul, trace_reindex_gen, Matrix.trace_kronecker, trace_one_operator,
    trace_partialTrace, trace_reindex_gen]
  have hne : (((d ^ ℓ : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (pow_ne_zero ℓ (ne_of_gt hd))
  simp only [smul_eq_mul]
  rw [mul_comm (Matrix.trace ρ), inv_mul_cancel_left₀ hne]

lemma trace_petzGenerator_zero {n ℓ d : ℕ} (β : ℝ) (hd : 0 < d)
    (cuts : Fin n → PetzCut n ℓ) (ρ : Operator (d ^ n)) :
    Matrix.trace (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))) ρ) = 0 := by
  have hk : (0 : ℝ) < ((d ^ n : ℕ) : ℝ)⁻¹ := by positivity
  have hσ : gibbsState β (0 : Operator (d ^ n))
      = (((((d ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Operator (d ^ n))) := by
    rw [gibbsState_zero, cast_inv_nat]
  have hper : ∀ s : Fin n,
      Matrix.trace (petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ)
        = Matrix.trace ρ := by
    intro s
    rw [hσ]
    exact trace_petzHeatBath_smul_one (cuts s) _ hk hd ρ
  unfold petzGenerator
  rw [Matrix.trace_smul]
  have hsum : ∑ s : Fin n,
      Matrix.trace (petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ - ρ) = 0 := by
    rw [Finset.sum_eq_zero]
    intro s _
    rw [Matrix.trace_sub, hper, sub_self]
  rw [Matrix.trace_sum, hsum, smul_zero]

lemma trace_iterate_petzGenerator_zero {n ℓ d : ℕ} (β : ℝ) (hd : 0 < d)
    (cuts : Fin n → PetzCut n ℓ) (ρ : Operator (d ^ n)) (k : ℕ) :
    Matrix.trace
        ((petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))))^[k] ρ)
      = if k = 0 then Matrix.trace ρ else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', trace_petzGenerator_zero β hd cuts,
      if_neg (Nat.succ_ne_zero k)]

lemma siteMarginalMass_iterate_petzGenerator_zero {n ℓ d : ℕ} (β : ℝ) (hd : 0 < d)
    (hℓ : 0 < ℓ) (hle : ℓ ≤ n) (cuts : Fin n → PetzCut n ℓ)
    (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (ρ : Operator (d ^ n)) (htr : Matrix.trace ρ = 1)
    (i : Fin n) (out : Fin d) :
    ∀ k : ℕ,
      siteMarginalMass
          ((petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))))^[k] ρ) i out
        = if k = 0 then siteMarginalMass ρ i out
          else (-1 : ℝ) ^ k * (siteMarginalMass ρ i out - 1 / (d : ℝ)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have htrk : (Matrix.trace
          ((petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))))^[k] ρ)).re
        = if k = 0 then (1 : ℝ) else 0 := by
      rw [trace_iterate_petzGenerator_zero β hd cuts]
      by_cases hk : k = 0 <;> simp [hk, htr]
    rw [Function.iterate_succ_apply',
      siteMarginalMass_petzGenerator_zero β hd hℓ hle cuts hc, htrk, ih,
      if_neg (by omega : ¬(k + 1 = 0))]
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    by_cases hk : k = 0
    · rw [hk]
      simp
    · rw [if_neg hk, if_neg hk, pow_succ]
      ring

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

def stdBasis {D : ℕ} (q : Fin D × Fin D) : Operator D :=
  fun i j => if (i, j) = q then (1 : ℂ) else 0

lemma superMatrix_eq_vecOp_stdBasis {D : ℕ} (L : Operator D → Operator D)
    (p q : Fin D × Fin D) : superMatrix L p q = vecOp (L (stdBasis q)) p :=
  rfl

lemma sum_stdBasis {D : ℕ} (A : Operator D) :
    A = ∑ q : Fin D × Fin D, (vecOp A q) • stdBasis q := by
  ext i j
  rw [Matrix.sum_apply]
  have hs : (∑ q : Fin D × Fin D, (vecOp A q • stdBasis q) i j)
      = ∑ q : Fin D × Fin D, (if (i, j) = q then A q.1 q.2 else 0) := by
    apply Finset.sum_congr rfl
    intro q _
    show (A q.1 q.2) * (if (i, j) = q then (1 : ℂ) else 0)
      = if (i, j) = q then A q.1 q.2 else 0
    by_cases h : (i, j) = q <;> simp [h]
  rw [hs, Fintype.sum_ite_eq (i, j) (fun q => A q.1 q.2)]

lemma map_sum_smul_stdBasis {D : ℕ} (L : Operator D → Operator D)
    (hadd : ∀ ρ τ : Operator D, L (ρ + τ) = L ρ + L τ) (hzero : L 0 = 0)
    (hsmul : ∀ (k : ℂ) (ρ : Operator D), L (k • ρ) = k • L ρ)
    (s : Finset (Fin D × Fin D)) (f : Fin D × Fin D → ℂ) :
    L (∑ q ∈ s, f q • stdBasis q) = ∑ q ∈ s, f q • L (stdBasis q) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, hzero]
  | insert q s hnot ih =>
    rw [Finset.sum_insert hnot, Finset.sum_insert hnot, hadd, hsmul, ih]

lemma superMatrix_mulVec_gen {D : ℕ} (L : Operator D → Operator D)
    (hadd : ∀ ρ τ : Operator D, L (ρ + τ) = L ρ + L τ) (hzero : L 0 = 0)
    (hsmul : ∀ (k : ℂ) (ρ : Operator D), L (k • ρ) = k • L ρ)
    (A : Operator D) :
    superMatrix L *ᵥ vecOp A = vecOp (L A) := by
  have hA : A = ∑ q : Fin D × Fin D, (vecOp A q) • stdBasis q := sum_stdBasis A
  have hL : L A = ∑ q : Fin D × Fin D, (vecOp A q) • L (stdBasis q) := by
    conv_lhs => rw [hA]
    rw [map_sum_smul_stdBasis L hadd hzero hsmul]
  funext p
  simp only [Matrix.mulVec, dotProduct, vecOp]
  rw [hL, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [superMatrix_eq_vecOp_stdBasis, mul_comm]
  show vecOp A q * L (stdBasis q) p.1 p.2 = vecOp A q * L (stdBasis q) p.1 p.2
  rfl

lemma superMatrix_pow_mulVec {D : ℕ} (L : Operator D → Operator D)
    (hadd : ∀ ρ τ : Operator D, L (ρ + τ) = L ρ + L τ) (hzero : L 0 = 0)
    (hsmul : ∀ (k : ℂ) (ρ : Operator D), L (k • ρ) = k • L ρ) :
    ∀ (k : ℕ) (A : Operator D), superMatrix L ^ k *ᵥ vecOp A = vecOp (L^[k] A) := by
  intro k
  induction k with
  | zero => intro A; simp
  | succ k ih =>
    intro A
    rw [pow_succ, ← Matrix.mulVec_mulVec,
      superMatrix_mulVec_gen L hadd hzero hsmul, ih, ← Function.iterate_succ_apply]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma tsum_matrix_apply {m n : Type*} {ι : Type*} [Fintype m] [Fintype n]
    (f : ι → Matrix m n ℂ) (hf : Summable f) (i : m) (j : n) :
    (∑' k, f k) i j = ∑' k, f k i j := by
  have h1 : ((∑' k, f k) i) = (∑' k, f k i) := Pi.tsum_apply hf
  have hs2 : Summable (fun k => (f k : m → n → ℂ) i) := Pi.summable.mp hf i
  have h2 : ((∑' k, f k i) j) = (∑' k, f k i j) := Pi.tsum_apply hs2
  rw [h1, h2]

lemma coeff_eq {t : ℝ} (k : ℕ) :
    (((Nat.factorial k : ℕ) : ℂ)⁻¹ * (((t : ℝ) : ℂ) ^ k))
      = (((t : ℝ) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) := by
  have h1 : (((t : ℝ) : ℂ) ^ k) = (((t : ℝ) ^ k : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
  have h2 : (((Nat.factorial k : ℕ) : ℂ)⁻¹ : ℂ)
      = ((((Nat.factorial k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := cast_inv_nat (Nat.factorial k)
  rw [h1, h2, ← Complex.ofReal_mul, inv_mul_eq_div]

noncomputable local instance instNormedAddCommGroupMatrix (D : ℕ) :
    NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAddCommGroup

noncomputable local instance instNormedRingMatrix (D : ℕ) :
    NormedRing (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedRing

noncomputable local instance instNormedAlgebraMatrix (D : ℕ) :
    NormedAlgebra ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Matrix.linftyOpNormedAlgebra

lemma exp_matrix_entry {D : ℕ} (x : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    NormedSpace.exp x i j
      = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ * (x ^ k) i j) := by
  letI : CompleteSpace (Matrix (Fin D) (Fin D) ℂ) := inferInstance
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • x ^ k)) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) x
  have hexp : NormedSpace.exp x = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • x ^ k) := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  rw [hexp, tsum_matrix_apply _ hsum i j]
  apply tsum_congr
  intro k
  exact Matrix.smul_apply _ _ _ _

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma exp_matrix_entry_gen {m : Type*} [Fintype m] [DecidableEq m]
    (x : Matrix m m ℂ) (i j : m) :
    NormedSpace.exp x i j
      = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ * (x ^ k) i j) := by
  letI : NormedAddCommGroup (Matrix m m ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix m m ℂ) := inferInstance
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • x ^ k)) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) x
  have hexp : NormedSpace.exp x = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • x ^ k) := by
    rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  rw [hexp, tsum_matrix_apply _ hsum i j]
  apply tsum_congr
  intro k
  exact Matrix.smul_apply _ _ _ _

lemma exp_smul_pow_entry {m : Type*} [Fintype m] [DecidableEq m]
    (t : ℝ) (M : Matrix m m ℂ) (p q : m) :
    NormedSpace.exp ((t : ℂ) • M) p q
      = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((M ^ k) p q) := by
  rw [exp_matrix_entry_gen (x := (t : ℂ) • M)]
  apply tsum_congr
  intro k
  rw [smul_pow]
  have hsm : (((t : ℂ) ^ k • (M ^ k)) p q) = (((t : ℂ) ^ k) * ((M ^ k) p q)) :=
    Matrix.smul_apply _ _ _ _
  rw [hsm, ← mul_assoc, coeff_eq]

lemma superExp_petzGenerator_entry_sum_tsum {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n))
    (i j : Fin (d ^ n)) :
    superExp (petzGenerator cuts σ) t ρ i j
      = ∑ q : Fin (d ^ n) × Fin (d ^ n),
          ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
            * (((superMatrix (petzGenerator cuts σ) ^ k) (i, j) q) * vecOp ρ q) := by
  set L := petzGenerator cuts σ
  set M := superMatrix L
  have h1 : superExp L t ρ i j = (NormedSpace.exp ((t : ℂ) • M) *ᵥ vecOp ρ) (i, j) := rfl
  have h2 : (NormedSpace.exp ((t : ℂ) • M) *ᵥ vecOp ρ) (i, j)
      = ∑ q : Fin (d ^ n) × Fin (d ^ n),
          NormedSpace.exp ((t : ℂ) • M) (i, j) q * vecOp ρ q := by
    simp only [Matrix.mulVec, dotProduct]
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro q _
  rw [exp_smul_pow_entry t M (i, j) q, ← tsum_mul_right]
  apply tsum_congr
  intro k
  ring

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma summable_finset_sum {ι β α : Type*} [AddCommMonoid α] [TopologicalSpace α] [ContinuousAdd α]
    (s : Finset ι) (f : ι → β → α) (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun b => ∑ i ∈ s, f i b) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hnot ih =>
    simp only [Finset.sum_insert hnot]
    exact (hf i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

lemma summable_coeff_pow {m : Type*} [Fintype m] [DecidableEq m]
    (t : ℝ) (M : Matrix m m ℂ) (p q : m) :
    Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((M ^ k) p q)) := by
  letI : NormedAddCommGroup (Matrix m m ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedRing (Matrix m m ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix m m ℂ) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix m m ℂ) := inferInstance
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℂ)⁻¹ • ((t : ℂ) • M) ^ k)) :=
    NormedSpace.expSeries_summable' (𝕂 := ℂ) ((t : ℂ) • M)
  have hs1 : Summable (fun k : ℕ =>
      (((k.factorial : ℂ)⁻¹ • ((t : ℂ) • M) ^ k) : m → m → ℂ) p) :=
    Pi.summable.mp hsum p
  have hs2 : Summable (fun k : ℕ =>
      ((((k.factorial : ℂ)⁻¹ • ((t : ℂ) • M) ^ k) : m → m → ℂ) p) q) :=
    Pi.summable.mp hs1 q
  have hterm : ∀ k : ℕ,
      (((k.factorial : ℂ)⁻¹ • ((t : ℂ) • M) ^ k) : m → m → ℂ) p q
        = (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((M ^ k) p q) := by
    intro k
    have hsm1 : (((k.factorial : ℂ)⁻¹ • ((t : ℂ) • M) ^ k) : m → m → ℂ) p q
        = ((k.factorial : ℂ)⁻¹) * ((((t : ℂ) • M) ^ k) p q) :=
      Matrix.smul_apply _ _ _ _
    have hsm2 : (((t : ℂ) • M) ^ k) = ((t : ℂ) ^ k) • (M ^ k) := smul_pow _ _ _
    rw [hsm1, hsm2]
    have hsm3 : (((t : ℂ) ^ k) • (M ^ k)) p q = ((t : ℂ) ^ k) * ((M ^ k) p q) :=
      Matrix.smul_apply _ _ _ _
    rw [hsm3, ← mul_assoc, coeff_eq]
  exact Summable.congr hs2 hterm

noncomputable def expCoeff (t : ℝ) (k : ℕ) : ℝ := (t : ℝ) ^ k / (k.factorial : ℝ)

lemma expCoeff_eq {t : ℝ} (k : ℕ) :
    (expCoeff t k : ℂ) = (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) := rfl

lemma summable_expCoeff_mul_iterate {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) :
    ∀ i j : Fin (d ^ n),
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
        * (((petzGenerator cuts σ)^[k] ρ) i j)) := by
  set L := petzGenerator cuts σ
  set M := superMatrix L
  have hadd : ∀ ρ τ : Operator (d ^ n), L (ρ + τ) = L ρ + L τ :=
    fun ρ τ => petzGenerator_add cuts σ ρ τ
  have hzero : L 0 = 0 := petzGenerator_zero cuts σ
  have hsmulL : ∀ (k : ℂ) (ρ : Operator (d ^ n)), L (k • ρ) = k • L ρ :=
    fun k ρ => petzGenerator_smul cuts σ k ρ
  have hpow : ∀ (k : ℕ) (A : Operator (d ^ n)), M ^ k *ᵥ vecOp A = vecOp (L^[k] A) :=
    superMatrix_pow_mulVec L hadd hzero hsmulL
  intro i j
  have hs : ∀ q : Fin (d ^ n) × Fin (d ^ n),
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
        * (((M ^ k) (i, j) q) * vecOp ρ q)) := by
    intro q
    exact Summable.congr ((summable_coeff_pow t M (i, j) q).mul_right (vecOp ρ q))
      (fun k => by ring)
  have hsum : Summable (fun k : ℕ =>
      ∑ q : Fin (d ^ n) × Fin (d ^ n),
        (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * (((M ^ k) (i, j) q) * vecOp ρ q)) :=
    summable_finset_sum Finset.univ _ (fun q _ => hs q)
  have hterm : ∀ k : ℕ,
      (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((L^[k] ρ) i j)
        = ∑ q : Fin (d ^ n) × Fin (d ^ n),
            (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * (((M ^ k) (i, j) q) * vecOp ρ q) := by
    intro k
    have hL : (L^[k] ρ) i j = (M ^ k *ᵥ vecOp ρ) (i, j) := by
      rw [hpow]
      rfl
    rw [hL]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
  exact Summable.congr hsum (fun k => (hterm k).symm)

lemma superExp_petzGenerator_entry_eq_tsum {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) (i j : Fin (d ^ n)) :
    superExp (petzGenerator cuts σ) t ρ i j
      = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
          * (((petzGenerator cuts σ)^[k] ρ) i j) := by
  set L := petzGenerator cuts σ
  set M := superMatrix L
  have hadd : ∀ ρ τ : Operator (d ^ n), L (ρ + τ) = L ρ + L τ :=
    fun ρ τ => petzGenerator_add cuts σ ρ τ
  have hzero : L 0 = 0 := petzGenerator_zero cuts σ
  have hsmulL : ∀ (k : ℂ) (ρ : Operator (d ^ n)), L (k • ρ) = k • L ρ :=
    fun k ρ => petzGenerator_smul cuts σ k ρ
  have hpow : ∀ (k : ℕ) (A : Operator (d ^ n)), M ^ k *ᵥ vecOp A = vecOp (L^[k] A) :=
    superMatrix_pow_mulVec L hadd hzero hsmulL
  have hentry : superExp L t ρ i j
      = ∑ q : Fin (d ^ n) × Fin (d ^ n),
          ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
            * (((M ^ k) (i, j) q) * vecOp ρ q) :=
    superExp_petzGenerator_entry_sum_tsum cuts σ t ρ i j
  rw [hentry]
  have hs : ∀ q : Fin (d ^ n) × Fin (d ^ n),
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
        * (((M ^ k) (i, j) q) * vecOp ρ q)) := by
    intro q
    exact Summable.congr ((summable_coeff_pow t M (i, j) q).mul_right (vecOp ρ q))
      (fun k => by ring)
  rw [← Summable.tsum_finsetSum (fun q _ => hs q)]
  apply tsum_congr
  intro k
  rw [← Finset.mul_sum]
  have hvec : (∑ q : Fin (d ^ n) × Fin (d ^ n), ((M ^ k) (i, j) q) * vecOp ρ q)
      = (L^[k] ρ) i j := by
    have h1 : (M ^ k *ᵥ vecOp ρ) (i, j)
        = ∑ q : Fin (d ^ n) × Fin (d ^ n), ((M ^ k) (i, j) q) * vecOp ρ q := by
      simp only [Matrix.mulVec, dotProduct]
    rw [← h1, hpow]
    rfl
  rw [hvec]

lemma tsum_ite_const {c : Prop} [Decidable c] {f : ℕ → ℝ} :
    (if c then ∑' k, f k else 0) = ∑' k, (if c then f k else 0) := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]

lemma re_tsum {f : ℕ → ℂ} (hf : Summable f) :
    (∑' k, f k).re = ∑' k, (f k).re := by
  have h4 : ∀ z : ℂ, ⇑Complex.reCLM z = z.re := fun _ => rfl
  have h := Complex.reCLM.map_tsum (f := f) hf
  simp only [h4] at h
  exact h

lemma siteMarginalMass_superExp_petzGenerator_eq_tsum {n ℓ d : ℕ}
    (cuts : Fin n → PetzCut n ℓ) (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n))
    (i : Fin n) (out : Fin d) :
    siteMarginalMass (superExp (petzGenerator cuts σ) t ρ) i out
      = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
          * siteMarginalMass ((petzGenerator cuts σ)^[k] ρ) i out := by
  set L := petzGenerator cuts σ
  simp only [siteMarginalMass]
  have hentry : ∀ g : SiteConfig n d,
      (superExp L t ρ (configEquiv n d g) (configEquiv n d g))
        = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
            * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)) :=
    fun g => superExp_petzGenerator_entry_eq_tsum cuts σ t ρ (configEquiv n d g) (configEquiv n d g)
  have hsumG : ∀ g : SiteConfig n d,
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
        * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g))) :=
    fun g => summable_expCoeff_mul_iterate cuts σ t ρ _ _
  have hre : ∀ g : SiteConfig n d,
      (superExp L t ρ (configEquiv n d g) (configEquiv n d g)).re
        = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
            * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re := by
    intro g
    rw [hentry g, re_tsum (hsumG g)]
    apply tsum_congr
    intro k
    exact Complex.re_ofReal_mul _ _
  have hsumRe : ∀ g : SiteConfig n d,
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
          * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re) := by
    intro g
    have h := summable_expCoeff_mul_iterate cuts σ t ρ (configEquiv n d g) (configEquiv n d g)
    have h4 : ∀ z : ℂ, ⇑Complex.reCLM z = z.re := fun _ => rfl
    refine Summable.congr (Complex.reCLM.summable h) ?_
    intro k
    simp only [h4]
    exact Complex.re_ofReal_mul _ _
  have hmain : (∑ g : SiteConfig n d,
        if g i = out then (superExp L t ρ (configEquiv n d g) (configEquiv n d g)).re else 0)
      = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
          * (∑ g : SiteConfig n d,
              if g i = out then ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re else 0) := by
    have h1 : (∑ g : SiteConfig n d,
          if g i = out then (superExp L t ρ (configEquiv n d g) (configEquiv n d g)).re else 0)
        = (∑ g : SiteConfig n d,
            if g i = out then
              ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
                  * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
            else 0) :=
      Finset.sum_congr rfl (fun g _ => by simp only [hre g])
    rw [h1]
    have hsw : ∀ g : SiteConfig n d,
        (if g i = out then
            ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
                * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
          else 0)
          = ∑' k : ℕ, (if g i = out then
              (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
                * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
            else 0) := by
      intro g
      exact tsum_ite_const
    have h1' : (∑ g : SiteConfig n d,
          if g i = out then
            ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
                * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
          else 0)
        = (∑ g : SiteConfig n d,
            ∑' k : ℕ, (if g i = out then
                (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
                  * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
              else 0)) :=
      Finset.sum_congr rfl (fun g _ => hsw g)
    rw [h1']
    have hite : ∀ g : SiteConfig n d,
        Summable (fun k : ℕ => if g i = out then
            (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
              * ((L^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
          else 0) := by
      intro g
      by_cases hc : g i = out
      · refine Summable.congr (hsumRe g) (fun k => ?_)
        simp [hc]
      · refine Summable.congr (show Summable (fun _ : ℕ => (0 : ℝ)) from ?_) (fun k => ?_)
        · simp
        · simp [hc]
    rw [← Summable.tsum_finsetSum (fun g _ => hite g)]
    apply tsum_congr
    intro k
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun g _ => by by_cases hc : g i = out <;> simp [hc])
  exact hmain

lemma re_tsum' {f : ℕ → ℂ} (hf : Summable f) :
    (∑' k, f k).re = ∑' k, (f k).re := re_tsum hf

lemma neg_pow_div_factorial (t : ℝ) (k : ℕ) :
    (((t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (-1 : ℝ) ^ (k + 1))
      = ((-(t : ℝ)) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
  have h1 : ((-(t : ℝ)) ^ (k + 1)) = ((-1 : ℝ) ^ (k + 1) * (t : ℝ) ^ (k + 1)) := by
    rw [neg_pow]
  rw [h1]
  have hne : (((k + 1).factorial : ℝ)) ≠ 0 := by positivity
  field_simp [hne]

lemma summable_pow_div_factorial (x : ℝ) :
    Summable (fun n : ℕ => (x : ℝ) ^ n / (n.factorial : ℝ)) := by
  have h2 := NormedSpace.expSeries_summable' (𝕂 := ℝ) (𝔸 := ℝ) x
  refine Summable.congr h2 (fun n => ?_)
  simp only [smul_eq_mul]
  rw [inv_mul_eq_div]

lemma real_exp_eq_tsum (x : ℝ) :
    Real.exp x = ∑' n : ℕ, ((x : ℝ) ^ n / (n.factorial : ℝ)) := by
  have h : NormedSpace.exp (x : ℝ) = ∑' n : ℕ, ((x : ℝ) ^ n / (n.factorial : ℝ)) := by
    rw [NormedSpace.exp_eq_tsum_div]
  have h2 : Real.exp x = NormedSpace.exp (x : ℝ) := by
    rw [Real.exp_eq_exp_ℝ]
  rw [h2, h]

lemma summable_coeff_mul_marginal {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (t : ℝ) (ρ : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
        * siteMarginalMass ((petzGenerator cuts σ)^[k] ρ) i out) := by
  simp only [siteMarginalMass]
  have hsumRe : ∀ g : SiteConfig n d,
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
          * (((petzGenerator cuts σ)^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re) := by
    intro g
    have h := summable_expCoeff_mul_iterate cuts σ t ρ (configEquiv n d g) (configEquiv n d g)
    have h4 : ∀ z : ℂ, ⇑Complex.reCLM z = z.re := fun _ => rfl
    refine Summable.congr (Complex.reCLM.summable h) ?_
    intro k
    simp only [h4]
    exact Complex.re_ofReal_mul _ _
  have hite : ∀ g : SiteConfig n d,
      Summable (fun k : ℕ => if g i = out then
          (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ))
            * (((petzGenerator cuts σ)^[k] ρ) (configEquiv n d g) (configEquiv n d g)).re
        else 0) := by
    intro g
    by_cases hc : g i = out
    · refine Summable.congr (hsumRe g) (fun k => ?_)
      simp [hc]
    · refine Summable.congr (show Summable (fun _ : ℕ => (0 : ℝ)) from ?_) (fun k => ?_)
      · simp
      · simp [hc]
  refine Summable.congr
    (summable_finset_sum Finset.univ _ (fun g _ => hite g)) (fun k => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun g _ => by by_cases hc : g i = out <;> simp [hc])

lemma siteMarginalMass_superExp_zero {n ℓ d : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (hle : ℓ ≤ n)
    (β : ℝ) (cuts : Fin n → PetzCut n ℓ)
    (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (t : ℝ) (i : Fin n) (out : Fin d) :
    siteMarginalMass
        (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
          (tensorProductOp (fun _ : Fin n => pureZero d))) i out
      = siteOutputMass d t 0 out.val := by
  set ρ0 : Operator (d ^ n) := tensorProductOp (fun _ : Fin n => pureZero d)
  set L := petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))
  have htr : Matrix.trace ρ0 = 1 := trace_tensorProductOp_pureZero hd
  have hm0 : siteMarginalMass ρ0 i out = if out.val = 0 then (1 : ℝ) else 0 :=
    siteMarginalMass_pureZero hd i out
  have hseries := siteMarginalMass_superExp_petzGenerator_eq_tsum cuts
    (gibbsState β (0 : Operator (d ^ n))) t ρ0 i out
  have hiter := siteMarginalMass_iterate_petzGenerator_zero β hd hℓ hle cuts hc ρ0 htr i out
  have hsum := summable_coeff_mul_marginal cuts (gibbsState β (0 : Operator (d ^ n))) t ρ0 i out
  have hfdiag : (((t : ℝ) ^ 0 / (Nat.factorial 0 : ℝ) : ℝ))
      * siteMarginalMass (L^[0] ρ0) i out
      = siteMarginalMass ρ0 i out := by
    simp
  have hfsucc : ∀ k : ℕ,
      (((t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) : ℝ))
          * siteMarginalMass (L^[k + 1] ρ0) i out
        = (((t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (-1 : ℝ) ^ (k + 1))
            * (siteMarginalMass ρ0 i out - 1 / (d : ℝ)) := by
    intro k
    rw [hiter (k + 1)]
    rw [if_neg (by omega : ¬(k + 1 = 0))]
    ring
  have hg : Summable (fun n : ℕ => ((-(t : ℝ)) ^ n / (n.factorial : ℝ))) :=
    summable_pow_div_factorial (-(t : ℝ))
  have hg0 : ((-(t : ℝ)) ^ 0 / (Nat.factorial 0 : ℝ)) = 1 := by simp
  have hgtot : (∑' n : ℕ, ((-(t : ℝ)) ^ n / (n.factorial : ℝ))) = Real.exp (-(t : ℝ)) :=
    (real_exp_eq_tsum (-(t : ℝ))).symm
  have hshift : (∑' k : ℕ, ((-(t : ℝ)) ^ (k + 1) / ((k + 1).factorial : ℝ)))
      = Real.exp (-(t : ℝ)) - 1 := by
    have hA := hg.tsum_eq_zero_add
    rw [hg0, hgtot] at hA
    linarith
  have hbody : (∑' k : ℕ, (((t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ) : ℝ))
          * siteMarginalMass (L^[k + 1] ρ0) i out)
      = (Real.exp (-(t : ℝ)) - 1) * (siteMarginalMass ρ0 i out - 1 / (d : ℝ)) := by
    rw [tsum_congr hfsucc]
    have h3 : (∑' k : ℕ,
          (((t : ℝ) ^ (k + 1) / ((k + 1).factorial : ℝ)) * (-1 : ℝ) ^ (k + 1))
            * (siteMarginalMass ρ0 i out - 1 / (d : ℝ)))
        = (∑' k : ℕ, ((-(t : ℝ)) ^ (k + 1) / ((k + 1).factorial : ℝ))
            * (siteMarginalMass ρ0 i out - 1 / (d : ℝ))) :=
      tsum_congr (fun k => by rw [neg_pow_div_factorial t k])
    rw [h3, tsum_mul_right, hshift]
  rw [hseries, Summable.tsum_eq_zero_add hsum, hfdiag, hbody]
  rw [hm0]
  simp only [siteOutputMass]
  field_simp
  ring

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable def probeSign {n d : ℕ} (i : Fin n) (out : Fin d) : Operator (d ^ n) :=
  Matrix.diagonal fun j : Fin (d ^ n) =>
    if (configEquiv n d).symm j i = out then (1 : ℂ) else -1

lemma probeSign_apply {n d : ℕ} (i : Fin n) (out : Fin d) (j k : Fin (d ^ n)) :
    probeSign i out j k
      = if j = k then (if (configEquiv n d).symm j i = out then (1 : ℂ) else -1) else 0 :=
  rfl

lemma probeSign_diag_configEquiv {n d : ℕ} (i : Fin n) (out : Fin d) (g : SiteConfig n d) :
    probeSign i out (configEquiv n d g) (configEquiv n d g)
      = if g i = out then (1 : ℂ) else -1 := by
  rw [probeSign_apply, if_pos rfl, Equiv.symm_apply_apply]

lemma probeSign_mul_conjTranspose {n d : ℕ} (i : Fin n) (out : Fin d) :
    (probeSign i out).conjTranspose * probeSign i out = 1 := by
  unfold probeSign
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have hs : ∀ j : Fin (d ^ n),
      star (if (configEquiv n d).symm j i = out then (1 : ℂ) else -1)
        * (if (configEquiv n d).symm j i = out then (1 : ℂ) else -1) = 1 := by
    intro j
    by_cases h : (configEquiv n d).symm j i = out
    · rw [if_pos h]
      norm_num
    · rw [if_neg h]
      norm_num
  rw [← Matrix.diagonal_one, Matrix.diagonal_eq_diagonal_iff]
  intro j
  exact hs j

lemma traceNorm_probeSign_mul {n d : ℕ} (X : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    Matrix.traceNorm (probeSign i out * X) = Matrix.traceNorm X := by
  unfold Matrix.traceNorm
  congr 1
  have h : (probeSign i out * X).conjTranspose * (probeSign i out * X)
      = X.conjTranspose * X := by
    rw [Matrix.conjTranspose_mul]
    have hM := probeSign_mul_conjTranspose i out
    have h1 : X.conjTranspose * (probeSign i out).conjTranspose * (probeSign i out * X)
        = X.conjTranspose * ((probeSign i out).conjTranspose * probeSign i out) * X := by
      noncomm_ring
    rw [h1, hM, Matrix.mul_one]
  rw [h]

lemma trace_probeSign_mul_re {n d : ℕ} (X : Operator (d ^ n)) (i : Fin n) (out : Fin d) :
    ((probeSign i out * X).trace).re
      = 2 * siteMarginalMass X i out - (Matrix.trace X).re := by
  have hdiag : ∀ j : Fin (d ^ n),
      (probeSign i out * X) j j = (probeSign i out) j j * X j j := by
    intro j
    refine Finset.sum_eq_single j (fun k _ hk => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
    show probeSign i out j k * X k j = 0
    rw [probeSign_apply, if_neg (Ne.symm hk), zero_mul]
  have hre : ((probeSign i out * X).trace).re
      = ∑ g : SiteConfig n d,
          ((probeSign i out (configEquiv n d g) (configEquiv n d g))
            * X (configEquiv n d g) (configEquiv n d g)).re := by
    have h4 : ∀ z : ℂ, ⇑Complex.reCLM z = z.re := fun _ => rfl
    have h5 := map_sum Complex.reCLM
      (fun j : Fin (d ^ n) => (probeSign i out * X) j j) Finset.univ
    simp only [h4] at h5
    have hA : ((probeSign i out * X).trace).re
        = (∑ j : Fin (d ^ n), ((probeSign i out * X) j j).re) := by
      show ((∑ j : Fin (d ^ n), (probeSign i out * X) j j)).re = _
      exact h5
    rw [hA, Finset.sum_congr rfl (fun j _ => congrArg Complex.re (hdiag j))]
    rw [← Equiv.sum_comp (configEquiv n d)
      (fun j : Fin (d ^ n) => (probeSign i out j j * X j j).re)]
  have hsign : ∀ g : SiteConfig n d,
      ((probeSign i out (configEquiv n d g) (configEquiv n d g))
        * X (configEquiv n d g) (configEquiv n d g)).re
        = (if g i = out then (1 : ℝ) else 0) * (X (configEquiv n d g) (configEquiv n d g)).re
          - (if g i = out then (0 : ℝ) else 1) * (X (configEquiv n d g) (configEquiv n d g)).re := by
    intro g
    rw [probeSign_diag_configEquiv]
    by_cases hg : g i = out
    · rw [if_pos hg, if_pos hg, if_pos hg]
      simp
    · rw [if_neg hg, if_neg hg, if_neg hg]
      simp
  have hm : siteMarginalMass X i out
      = ∑ g : SiteConfig n d,
          (if g i = out then (1 : ℝ) else 0) * (X (configEquiv n d g) (configEquiv n d g)).re := by
    simp only [siteMarginalMass]
    exact Finset.sum_congr rfl (fun g _ => by by_cases hg : g i = out <;> simp [hg])
  have hrest : (Matrix.trace X).re
      = ∑ g : SiteConfig n d, (X (configEquiv n d g) (configEquiv n d g)).re :=
    (sum_re_diag_configEquiv X).symm
  have hother : (∑ g : SiteConfig n d,
        (if g i = out then (0 : ℝ) else 1) * (X (configEquiv n d g) (configEquiv n d g)).re)
      = (Matrix.trace X).re - siteMarginalMass X i out := by
    have hsplit : ∀ g : SiteConfig n d,
        (if g i = out then (0 : ℝ) else 1) * (X (configEquiv n d g) (configEquiv n d g)).re
          = (X (configEquiv n d g) (configEquiv n d g)).re
            - (if g i = out then (1 : ℝ) else 0)
                * (X (configEquiv n d g) (configEquiv n d g)).re := by
      intro g
      by_cases hg : g i = out <;> simp [hg]
    rw [Finset.sum_congr rfl (fun g _ => hsplit g), Finset.sum_sub_distrib, hrest, hm]
  rw [hre, Finset.sum_congr rfl (fun g _ => hsign g), Finset.sum_sub_distrib, hother, hm]
  ring

lemma abs_siteMarginalMass_le_half_traceNorm {n d : ℕ} (X : Operator (d ^ n))
    (htr : (Matrix.trace X).re = 0) (i : Fin n) (out : Fin d) :
    |siteMarginalMass X i out| ≤ (1 / 2 : ℝ) * Matrix.traceNorm X := by
  have hb := Matrix.abs_trace_le_traceNorm (probeSign i out * X)
  rw [traceNorm_probeSign_mul] at hb
  have hre := trace_probeSign_mul_re X i out
  rw [htr, sub_zero] at hre
  have hle : |((probeSign i out * X).trace).re| ≤ ‖(probeSign i out * X).trace‖ :=
    Complex.abs_re_le_norm _
  rw [hre] at hle
  have hnn : 0 ≤ Matrix.traceNorm X := Matrix.traceNorm_nonneg X
  have h2 : |(2 : ℝ) * siteMarginalMass X i out| = 2 * |siteMarginalMass X i out| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [h2] at hle
  have := le_trans hle hb
  nlinarith [abs_nonneg (siteMarginalMass X i out)]

lemma halfTraceDistance_ge_abs_siteMarginalMass_sub {n d : ℕ} (ρ τ : Operator (d ^ n))
    (htr : (Matrix.trace ρ).re = (Matrix.trace τ).re) (i : Fin n) (out : Fin d) :
    |siteMarginalMass ρ i out - siteMarginalMass τ i out| ≤ halfTraceDistance ρ τ := by
  have hX : (Matrix.trace (ρ - τ)).re = 0 := by
    rw [Matrix.trace_sub, Complex.sub_re, htr, sub_self]
  have h1 : siteMarginalMass (ρ - τ) i out
      = siteMarginalMass ρ i out - siteMarginalMass τ i out :=
    siteMarginalMass_sub ρ τ i out
  have h2 := abs_siteMarginalMass_le_half_traceNorm (ρ - τ) hX i out
  rw [h1] at h2
  rw [halfTraceDistance, Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm]
  exact h2

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma trace_gibbsState_zero {D : ℕ} (β : ℝ) (hD : (D : ℕ) ≠ 0) :
    Matrix.trace (gibbsState β (0 : Operator D)) = 1 := by
  rw [gibbsState_zero, Matrix.trace_smul, trace_one_operator]
  have hne : (((D : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hD
  rw [smul_eq_mul, inv_mul_cancel₀ hne]

lemma siteMarginalMass_gibbsState_zero {n d : ℕ} (hd : 0 < d) (hn : 0 < n) (β : ℝ)
    (i : Fin n) (out : Fin d) :
    siteMarginalMass (gibbsState β (0 : Operator (d ^ n))) i out = 1 / (d : ℝ) := by
  have hσ : gibbsState β (0 : Operator (d ^ n))
      = ((((((d ^ n : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) • (1 : Operator (d ^ n))) := by
    rw [gibbsState_zero, cast_inv_nat]
  rw [hσ, siteMarginalMass_smul_real]
  have hone : siteMarginalMass (1 : Operator (d ^ n)) i out
      = (d ^ (n - 1) : ℝ) := by
    simp only [siteMarginalMass]
    have h1 : ∀ g : SiteConfig n d,
        (if g i = out then ((1 : Operator (d ^ n))
            (configEquiv n d g) (configEquiv n d g)).re else 0)
        = if g i = out then (1 : ℝ) else 0 := by
      intro g
      by_cases hg : g i = out <;> simp [hg]
    rw [Finset.sum_congr rfl (fun g _ => h1 g)]
    exact sum_ite_eval_pi
  rw [hone]
  have hpow : (d : ℝ) ^ n = (d : ℝ) ^ (n - 1) * (d : ℝ) := by
    have h : n = n - 1 + 1 := by omega
    rw [congrArg (fun k : ℕ => (d : ℝ) ^ k) h, pow_succ]
  simp only [Nat.cast_pow]
  rw [hpow]
  field_simp
  try ring

lemma sum_siteMarginalMass {n d : ℕ} (ρ : Operator (d ^ n)) (i : Fin n) :
    (∑ out : Fin d, siteMarginalMass ρ i out) = (Matrix.trace ρ).re := by
  have hsum : ∀ g : SiteConfig n d,
      (∑ out : Fin d, if g i = out then (1 : ℝ) else 0) = 1 := by
    intro g
    rw [Fintype.sum_ite_eq (g i) (fun _ => (1 : ℝ))]
  simp only [siteMarginalMass]
  rw [Finset.sum_comm]
  have hkey : (∑ g : SiteConfig n d,
        ∑ out : Fin d, if g i = out then
          (ρ (configEquiv n d g) (configEquiv n d g)).re else 0)
      = ∑ g : SiteConfig n d, (ρ (configEquiv n d g) (configEquiv n d g)).re := by
    refine Finset.sum_congr rfl (fun g _ => ?_)
    have h2 : (∑ out : Fin d, if g i = out then
          (ρ (configEquiv n d g) (configEquiv n d g)).re else 0)
        = (∑ out : Fin d, (if g i = out then (1 : ℝ) else 0)
            * (ρ (configEquiv n d g) (configEquiv n d g)).re) := by
      refine Finset.sum_congr rfl (fun out _ => ?_)
      by_cases hg : g i = out <;> simp [hg]
    rw [h2, ← Finset.sum_mul, hsum, one_mul]
  rw [hkey]
  exact sum_re_diag_configEquiv ρ

lemma trace_re_superExp_zero {n ℓ d : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (hle : ℓ ≤ n)
    (β : ℝ) (cuts : Fin n → PetzCut n ℓ)
    (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (t : ℝ) :
    (Matrix.trace
        (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
          (tensorProductOp (fun _ : Fin n => pureZero d)))).re = 1 := by
  have hn : 0 < n := by omega
  set zn : Fin n := ⟨0, hn⟩
  have hsum := sum_siteMarginalMass
    (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
      (tensorProductOp (fun _ : Fin n => pureZero d))) zn
  rw [← hsum]
  have hc1 := fun out : Fin d =>
    siteMarginalMass_superExp_zero hd hℓ hle β cuts hc t zn out
  rw [Finset.sum_congr rfl (fun out _ => hc1 out)]
  have hout : ∀ out : Fin d, siteOutputMass d t 0 out.val
      = Real.exp (-t) * (if out.val = 0 then (1 : ℝ) else 0)
          + (1 - Real.exp (-t)) * (1 / (d : ℝ)) := fun _ => rfl
  rw [Finset.sum_congr rfl (fun out _ => hout out)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hite : (∑ out : Fin d, if out.val = 0 then (1 : ℝ) else 0) = 1 := by
    have hz : ∀ out : Fin d, (out.val = 0) ↔ (out = (⟨0, hd⟩ : Fin d)) := by
      intro out
      constructor
      · intro h
        ext
        exact h
      · intro h
        simp [h]
    have h3 : (∑ out : Fin d, if out.val = 0 then (1 : ℝ) else 0)
        = ∑ out : Fin d, if out = (⟨0, hd⟩ : Fin d) then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl (fun out _ => ?_)
      by_cases h : out.val = 0
      · rw [if_pos h, if_pos ((hz out).1 h)]
      · rw [if_neg h, if_neg (fun hh => h ((hz out).2 hh))]
    rw [h3]
    exact Fintype.sum_ite_eq' (⟨0, hd⟩ : Fin d) (fun _ => (1 : ℝ))
  have hconst : (∑ out : Fin d, (1 / (d : ℝ))) = ((d : ℝ) * (1 / (d : ℝ))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hite, hconst]
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  field_simp
  try ring

lemma siteOutputMass_zero_zero (d : ℕ) (t : ℝ) (hd : (d : ℝ) ≠ 0) :
    siteOutputMass d t 0 0 = Real.exp (-t) * (1 - 1 / (d : ℝ)) + 1 / (d : ℝ) := by
  simp only [siteOutputMass]
  rw [if_pos (trivial : True)]
  field_simp
  ring

lemma halfTraceDistance_superExp_zero_ge {n ℓ d : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (hle : ℓ ≤ n)
    (β : ℝ) (cuts : Fin n → PetzCut n ℓ)
    (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (t : ℝ) :
    Real.exp (-t) * (1 - 1 / (d : ℝ))
      ≤ halfTraceDistance
          (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
            (tensorProductOp (fun _ : Fin n => pureZero d)))
          (gibbsState β (0 : Operator (d ^ n))) := by
  set ρt : Operator (d ^ n) :=
    superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
      (tensorProductOp (fun _ : Fin n => pureZero d)) with hρt
  set σ : Operator (d ^ n) := gibbsState β (0 : Operator (d ^ n)) with hσ
  have hn : 0 < n := by omega
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have htr : (Matrix.trace ρt).re = (Matrix.trace σ).re := by
    rw [trace_re_superExp_zero hd hℓ hle β cuts hc t,
      trace_gibbsState_zero β (by positivity : (d ^ n : ℕ) ≠ 0), Complex.one_re]
  have hmt : siteMarginalMass ρt (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d)
      = siteOutputMass d t 0 (0 : ℕ) :=
    siteMarginalMass_superExp_zero hd hℓ hle β cuts hc t (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d)
  have hms : siteMarginalMass σ (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d) = 1 / (d : ℝ) :=
    siteMarginalMass_gibbsState_zero hd hn β (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d)
  have hdual := halfTraceDistance_ge_abs_siteMarginalMass_sub ρt σ htr
    (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d)
  have hgap : siteMarginalMass ρt (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d)
        - siteMarginalMass σ (⟨0, hn⟩ : Fin n) (⟨0, hd⟩ : Fin d)
      = Real.exp (-t) * (1 - 1 / (d : ℝ)) := by
    rw [hmt, hms, siteOutputMass_zero_zero d t hd0]
    ring
  rw [hgap] at hdual
  have hnn : 0 ≤ Real.exp (-t) * (1 - 1 / (d : ℝ)) := by
    have h1 : 0 < Real.exp (-t) := Real.exp_pos _
    have h2 : 0 ≤ 1 - 1 / (d : ℝ) := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have h3 : 1 / (d : ℝ) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact mul_nonneg (le_of_lt h1) h2
  rw [abs_of_nonneg hnn] at hdual
  exact hdual

lemma halfTraceDistance_superExp_zero_gt_eps_of_neg {n ℓ d : ℕ} (hd : 2 ≤ d) (hℓ : 0 < ℓ)
    (hle : ℓ ≤ n) (β : ℝ) (cuts : Fin n → PetzCut n ℓ)
    (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 4) (t : ℝ) (ht : t < 0) :
    ε < halfTraceDistance
        (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
          (tensorProductOp (fun _ : Fin n => pureZero d)))
        (gibbsState β (0 : Operator (d ^ n))) := by
  have hd1 : (2:ℝ) ≤ d := by exact_mod_cast hd
  have h3 : 1 / (d : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : (1 / 2 : ℝ) ≤ 1 - 1 / (d : ℝ) := by linarith
  have hnn : 0 ≤ 1 - 1 / (d : ℝ) := by linarith
  have h1 : 1 < Real.exp (-t) := by
    rw [Real.one_lt_exp_iff]
    linarith
  have hprod : (1 / 2 : ℝ) < Real.exp (-t) * (1 - 1 / (d : ℝ)) := by
    nlinarith [mul_nonneg (le_of_lt (lt_trans (by norm_num : (0:ℝ) < 1) h1)) hnn]
  have hge := halfTraceDistance_superExp_zero_ge (by omega : 0 < d) hℓ hle β cuts hc t
  have : ε < Real.exp (-t) * (1 - 1 / (d : ℝ)) := by linarith
  exact lt_of_lt_of_le this hge

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma mixingTime_nonneg {D : ℕ} (L : Operator D → Operator D) (σ : Operator D) (ε : ℝ) :
    (0 : ℝ) ≤ mixingTime L σ ε := by
  unfold mixingTime
  exact Real.sInf_nonneg (fun t ht => ht.1)

lemma clause31_smallTime_regime {n ℓ d : ℕ} (hd : 2 ≤ d) (hℓ : 1 ≤ ℓ) (hle : 2 * ℓ ≤ n)
    (β : ℝ) (_ : 0 ≤ β) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 4)
    (cuts : Fin n → PetzCut n ℓ) (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (hT : (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d ≤ 0) :
    let σ := gibbsState β (0 : Operator (d ^ n))
    let L := petzGenerator cuts σ
    let ρ0 : Operator (d ^ n) := tensorProductOp (fun _ : Fin n => pureZero d)
    (mixingTime L σ ε ≥ (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d)
    ∧
    (∀ t : ℝ, t < (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d →
      halfTraceDistance (superExp L t ρ0) σ > ε)
    ∧
    (∀ (t : ℝ) (_ : 0 ≤ t) (i : Fin n) (out : Fin d),
      siteMarginalMass (superExp L t ρ0) i out = siteOutputMass d t 0 out.val) := by
  set σ : Operator (d ^ n) := gibbsState β (0 : Operator (d ^ n))
  set L := petzGenerator cuts σ
  set ρ0 : Operator (d ^ n) := tensorProductOp (fun _ : Fin n => pureZero d)
  have hd0 : 0 < d := by omega
  have hℓ0 : 0 < ℓ := by omega
  have hle' : ℓ ≤ n := by omega
  refine ⟨?_, ?_, ?_⟩
  · have hnn := mixingTime_nonneg L σ ε
    exact le_trans hT hnn
  · intro t ht
    have hneg : t < 0 := lt_of_lt_of_le ht hT
    exact halfTraceDistance_superExp_zero_gt_eps_of_neg hd hℓ0 hle' β cuts hc ε hε hε2 t hneg
  · intro t _ i out
    exact siteMarginalMass_superExp_zero hd0 hℓ0 hle' β cuts hc t i out

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma threshold_gap_sq {n ℓ d : ℕ} (hd : 2 ≤ d) (hℓ : 0 < ℓ) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) :
    (Real.exp (-((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))
        * (1 - 1 / (d : ℝ))) ^ 2
      = 16 * (ℓ : ℝ) * ε / (3 * (n : ℝ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hA : (0 : ℝ) < (n : ℝ) / ε := by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hK : (0 : ℝ) < 16 * (ℓ : ℝ) / (3 * (1 - 1 / (d : ℝ)) ^ 2) := by
    have hpos : (0:ℝ) < 1 - 1 / (d : ℝ) := by
      have h3 : 1 / (d : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    positivity
  have hdef : lowerBoundConst ℓ d
      = (1 / 2 : ℝ) * Real.log (16 * (ℓ : ℝ) / (3 * (1 - 1 / (d : ℝ)) ^ 2)) := rfl
  have h2T : (2 : ℝ) * ((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d)
      = Real.log ((n : ℝ) / ε) - Real.log (16 * (ℓ : ℝ) / (3 * (1 - 1 / (d : ℝ)) ^ 2)) := by
    rw [hdef]
    ring
  have hexp : Real.exp (-(2 : ℝ) * ((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))
      = (16 * (ℓ : ℝ) / (3 * (1 - 1 / (d : ℝ)) ^ 2)) / ((n : ℝ) / ε) := by
    have harg : (-(2 : ℝ) * ((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))
        = -((2 : ℝ) * ((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d)) := by ring
    rw [harg, h2T, neg_sub, Real.exp_sub, Real.exp_log hK, Real.exp_log hA]
  have hpow : (Real.exp (-((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))) ^ 2
      = Real.exp (-(2 : ℝ) * ((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d)) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hpow, hexp]
  have hz : (1 - 1 / (d : ℝ)) ^ 2 ≠ 0 := by
    have hpos : (0:ℝ) < 1 - 1 / (d : ℝ) := by
      have h3 : 1 / (d : ℝ) ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    positivity
  have hd1 : (d:ℝ) - 1 ≠ 0 := by nlinarith
  field_simp [hd1]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma halfTraceDistance_superExp_zero_gt_eps_of_thresh {n ℓ d : ℕ} (hd : 2 ≤ d) (hℓ : 0 < ℓ)
    (hle : ℓ ≤ n) (β : ℝ) (cuts : Fin n → PetzCut n ℓ)
    (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (ε : ℝ) (hε : 0 < ε) (hεreg : ε ≤ 16 * (ℓ : ℝ) / (3 * (n : ℝ)))
    (t : ℝ) (ht : t < (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d) :
    ε < halfTraceDistance
        (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t
          (tensorProductOp (fun _ : Fin n => pureZero d)))
        (gibbsState β (0 : Operator (d ^ n))) := by
  have hn : 0 < n := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hgap := threshold_gap_sq hd hℓ hn ε hε
  have hεsq : ε ^ 2 ≤ 16 * (ℓ : ℝ) * ε / (3 * (n : ℝ)) := by
    have hne : (3 : ℝ) * (n : ℝ) ≠ 0 := by positivity
    have hform : (16 * (ℓ : ℝ) * ε) / (3 * (n : ℝ))
        = (16 * (ℓ : ℝ) / (3 * (n : ℝ))) * ε := by
      field_simp [hne]
    rw [hform]
    nlinarith [hεreg, le_of_lt hε]
  have hdv : (0:ℝ) ≤ 1 - 1 / (d : ℝ) := by
    have h3 : 1 / (d : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hdv0 : (0:ℝ) < 1 - 1 / (d : ℝ) := by
    have h3 : 1 / (d : ℝ) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have htnonneg : (0:ℝ) ≤ Real.exp (-((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))
      * (1 - 1 / (d : ℝ)) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hdv0)
  have hthresh : ε ≤ Real.exp (-((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))
      * (1 - 1 / (d : ℝ)) :=
    (sq_le_sq₀ (le_of_lt hε) htnonneg).mp (by nlinarith [hgap])
  have hmono : Real.exp (-((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d))
      < Real.exp (-t) := by
    rw [Real.exp_lt_exp]
    linarith
  have hprod : ε < Real.exp (-t) * (1 - 1 / (d : ℝ)) := by
    have hsub : (0:ℝ) < Real.exp (-t)
        - Real.exp (-((1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d)) := by linarith
    nlinarith [mul_pos hsub hdv0]
  have hge := halfTraceDistance_superExp_zero_ge (by omega : 0 < d) hℓ hle β cuts hc t
  exact lt_of_lt_of_le hprod hge

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma petzGenerator_eq_sub_const {n ℓ d : ℕ} (_hd : 0 < d) (_hℓ : 0 < ℓ) (_hle : ℓ ≤ n)
    (β : ℝ) (cuts : Fin n → PetzCut n ℓ) (ρ : Operator (d ^ n)) :
    petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))) ρ
      = (((1 : ℂ) / ℓ) • ∑ s : Fin n,
            petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ)
        - (((n : ℂ) / ℓ) • ρ) := by
  unfold petzGenerator
  rw [Finset.sum_sub_distrib, smul_sub]
  congr 1
  have hsum : (∑ _s : Fin n, ρ) = ((n : ℂ) • ρ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact (Nat.cast_smul_eq_nsmul ℂ n ρ).symm
  rw [hsum, smul_smul]
  congr 1
  field_simp

lemma superMatrix_add_const {D : ℕ} (G : Operator D → Operator D) (c : ℂ) :
    superMatrix (fun τ : Operator D => G τ + c • τ)
      = superMatrix G + c • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) := by
  ext p q
  have hp : (p.1, p.2) = p := Prod.eta p
  by_cases h : p = q
  · subst h
    simp [superMatrix, hp]
  · have hne : (p.1, p.2) ≠ q := by
      intro hh
      exact h (by rw [← hp]; exact hh)
    simp [superMatrix, hne]

lemma smul_one_eq_diagonal {m : Type*} [Fintype m] [DecidableEq m] (x : ℂ) :
    x • (1 : Matrix m m ℂ) = Matrix.diagonal (fun _ => x) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

lemma tsum_ite_const_coe {c : Prop} [Decidable c] {f : ℕ → ℂ} :
    (if c then ∑' k, f k else 0) = ∑' k, (if c then f k else 0) := by
  by_cases hc : c
  · simp [hc]
  · simp [hc, tsum_zero]

lemma exp_smul_one_matrix {m : Type*} [Fintype m] [DecidableEq m] (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix m m ℂ))
      = (NormedSpace.exp z) • (1 : Matrix m m ℂ) := by
  ext p q
  rw [exp_matrix_entry_gen]
  have hpow : ∀ k : ℕ, ((z • (1 : Matrix m m ℂ)) ^ k) p q
      = if p = q then z ^ k else 0 := by
    intro k
    rw [smul_pow, one_pow, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : p = q <;> simp [h]
  have hterm : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ * ((z • (1 : Matrix m m ℂ)) ^ k) p q)
      = if p = q then ((k.factorial : ℂ)⁻¹ * z ^ k) else 0 := by
    intro k
    rw [hpow]
    by_cases h : p = q <;> simp [h]
  rw [tsum_congr hterm, ← tsum_ite_const_coe]
  have hz : (∑' k : ℕ, ((k.factorial : ℂ)⁻¹ * z ^ k)) = NormedSpace.exp z := by
    have h2 : NormedSpace.exp z = ∑' k : ℕ, ((k.factorial : ℂ)⁻¹ • z ^ k) := by
      rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
    rw [h2]
    apply tsum_congr
    intro k
    rw [smul_eq_mul]
  rw [hz, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : p = q <;> simp [h]

lemma superExp_shift_const {D : ℕ} (G : Operator D → Operator D) (c : ℂ) (t : ℝ)
    (ρ : Operator D) :
    superExp (fun τ : Operator D => G τ + c • τ) t ρ
      = (NormedSpace.exp ((t : ℂ) * c)) • superExp G t ρ := by
  have hM := superMatrix_add_const G c
  have harg : ((t : ℂ) • superMatrix (fun τ : Operator D => G τ + c • τ))
      = ((t : ℂ) • superMatrix G) + (((t : ℂ) * c) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)) := by
    rw [hM, smul_add, smul_smul]
  have hcomm : Commute ((t : ℂ) • superMatrix G)
      (((t : ℂ) * c) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)) :=
    (Commute.one_right _).smul_right _
  have hscal : NormedSpace.exp
        (((t : ℂ) * c) • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ))
      = NormedSpace.exp ((t : ℂ) * c)
        • (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :=
    exp_smul_one_matrix ((t : ℂ) * c)
  have hexp : NormedSpace.exp ((t : ℂ) • superMatrix (fun τ : Operator D => G τ + c • τ))
      = NormedSpace.exp ((t : ℂ) * c)
        • NormedSpace.exp ((t : ℂ) • superMatrix G) := by
    rw [harg, Matrix.exp_add_of_commute _ _ hcomm, hscal]
    simp only [mul_smul_comm, mul_one]
  unfold superExp
  rw [hexp, Matrix.smul_mulVec]
  rfl

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable def blockResetSum {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (β : ℝ)
    (ρ : Operator (d ^ n)) : Operator (d ^ n) :=
  (((1 : ℂ) / ℓ) • ∑ s : Fin n,
    petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ)

lemma blockResetSum_add {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (β : ℝ)
    (ρ τ : Operator (d ^ n)) :
    blockResetSum cuts β (ρ + τ) = blockResetSum cuts β ρ + blockResetSum cuts β τ := by
  unfold blockResetSum
  simp only [petzHeatBath_add, Finset.sum_add_distrib, smul_add]

lemma blockResetSum_smul {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (β : ℝ) (k : ℂ)
    (ρ : Operator (d ^ n)) :
    blockResetSum cuts β (k • ρ) = k • blockResetSum cuts β ρ := by
  unfold blockResetSum
  have h1 : ∀ s : Fin n,
      petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) (k • ρ)
        = k • petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) ρ := by
    intro s
    exact petzHeatBath_smul (cuts s) (gibbsState β (0 : Operator (d ^ n))) k ρ
  simp only [h1, Finset.smul_sum, smul_smul]
  congr 1
  funext s
  congr 1
  ring

lemma petzGenerator_eq_blockResetSum_sub {n ℓ d : ℕ} (hd : 0 < d) (hℓ : 0 < ℓ) (hle : ℓ ≤ n)
    (β : ℝ) (cuts : Fin n → PetzCut n ℓ) (ρ : Operator (d ^ n)) :
    petzGenerator cuts (gibbsState β (0 : Operator (d ^ n))) ρ
      = blockResetSum cuts β ρ - (((n : ℂ) / ℓ) • ρ) := by
  rw [petzGenerator_eq_sub_const hd hℓ hle β cuts ρ, blockResetSum]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma complex_exp_ofReal (r : ℝ) :
    NormedSpace.exp (((r : ℝ) : ℂ)) = (((Real.exp r : ℝ) : ℂ)) := by
  rw [← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]

lemma superExp_petzGenerator_factor {n ℓ d : ℕ} (_hd : 0 < d) (_hℓ : 0 < ℓ) (_hle : ℓ ≤ n)
    (β : ℝ) (cuts : Fin n → PetzCut n ℓ) (t : ℝ) (ρ : Operator (d ^ n)) :
    superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t ρ
      = (((Real.exp (-(t : ℝ) * (n : ℝ) / ℓ) : ℝ) : ℂ))
        • superExp (blockResetSum cuts β) t ρ := by
  set G : Operator (d ^ n) → Operator (d ^ n) := blockResetSum cuts β
  set c : ℂ := -(((n : ℂ) / ℓ))
  have hmap : petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))
      = fun τ : Operator (d ^ n) => G τ + c • τ := by
    funext τ
    have h1 := petzGenerator_eq_blockResetSum_sub _hd _hℓ _hle β cuts τ
    rw [h1]
    simp only [G, c]
    rw [neg_smul]
    abel
  have hshift := superExp_shift_const G c t ρ
  rw [← hmap] at hshift
  rw [hshift]
  congr 1
  have harg : (t : ℂ) * c = (((-(t : ℝ) * (n : ℝ) / ℓ) : ℝ) : ℂ) := by
    rw [show c = -(((n : ℂ) / ℓ)) from rfl]
    push_cast
    ring_nf
  rw [harg, complex_exp_ofReal]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

def zeroWeight {n d : ℕ} (g : SiteConfig n d) : ℂ :=
  ∏ i : Fin n, if (g i).val = 0 then (1 : ℂ) else 0

lemma zeroWeight_real {n d : ℕ} (g : SiteConfig n d) : star (zeroWeight g) = zeroWeight g := by
  unfold zeroWeight
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : (g i).val = 0 <;> simp [h]

lemma tensorProductConfig_pureZero_zeroWeight {n d : ℕ} (g h : SiteConfig n d) :
    tensorProductConfig (fun _ : Fin n => pureZero d) g h
      = zeroWeight g * zeroWeight h := by
  simp only [tensorProductConfig, pureZero, zeroWeight]
  have h1 : ∀ i : Fin n,
      (if (g i).val = 0 ∧ (h i).val = 0 then (1 : ℂ) else 0)
        = (if (g i).val = 0 then (1 : ℂ) else 0) * (if (h i).val = 0 then (1 : ℂ) else 0) := by
    intro i
    by_cases ha : (g i).val = 0 <;> by_cases hb : (h i).val = 0 <;> simp [ha, hb]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_mul_distrib]

lemma posSemidef_tensorProductConfig_pureZero {n d : ℕ} :
    (tensorProductConfig (fun _ : Fin n => pureZero d)).PosSemidef := by
  set A : Matrix Unit (SiteConfig n d) ℂ := fun _ g => star (zeroWeight g)
  have hA : tensorProductConfig (fun _ : Fin n => pureZero d) = A.conjTranspose * A := by
    ext g h
    rw [tensorProductConfig_pureZero_zeroWeight]
    simp only [Matrix.conjTranspose_apply, Matrix.mul_apply]
    rw [show (Finset.univ : Finset Unit) = ({0} : Finset Unit) by simp, Finset.sum_singleton]
    simp only [A]
    rw [star_star, zeroWeight_real]
  rw [hA]
  exact posSemidef_conjTranspose_mul_self A

lemma isDensityOperator_tensorProductOp_pureZero {n d : ℕ} (hd : 0 < d) :
    IsDensityOperator (tensorProductOp (fun _ : Fin n => pureZero d)) := by
  refine ⟨?_, trace_tensorProductOp_pureZero hd⟩
  have hsub : tensorProductOp (fun _ : Fin n => pureZero d)
      = Matrix.submatrix (tensorProductConfig (fun _ : Fin n => pureZero d))
          (configEquiv n d).symm (configEquiv n d).symm := by
    ext i j
    simp only [tensorProductOp, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hsub]
  exact (posSemidef_tensorProductConfig_pureZero).submatrix _

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma clause31_regime_of_nonempty {n ℓ d : ℕ} (hd : 2 ≤ d) (hℓ : 1 ≤ ℓ) (hle : 2 * ℓ ≤ n)
    (β : ℝ) (_ : 0 ≤ β) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 4)
    (cuts : Fin n → PetzCut n ℓ) (hc : ∀ s : Fin n, IsCyclicBlockCut s.val (cuts s))
    (hreg : (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d ≤ 0
        ∨ ε ≤ 16 * (ℓ : ℝ) / (3 * (n : ℝ)))
    (hne : ∃ t : ℝ, 0 ≤ t ∧ ∀ ρ : Operator (d ^ n), IsDensityOperator ρ →
        halfTraceDistance
          (superExp (petzGenerator cuts (gibbsState β (0 : Operator (d ^ n)))) t ρ)
          (gibbsState β (0 : Operator (d ^ n))) ≤ ε) :
    let σ := gibbsState β (0 : Operator (d ^ n))
    let L := petzGenerator cuts σ
    let ρ0 : Operator (d ^ n) := tensorProductOp (fun _ : Fin n => pureZero d)
    (mixingTime L σ ε ≥ (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d)
    ∧
    (∀ t : ℝ, t < (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d →
      halfTraceDistance (superExp L t ρ0) σ > ε)
    ∧
    (∀ (t : ℝ) (_ : 0 ≤ t) (i : Fin n) (out : Fin d),
      siteMarginalMass (superExp L t ρ0) i out = siteOutputMass d t 0 out.val) := by
  set σ : Operator (d ^ n) := gibbsState β (0 : Operator (d ^ n))
  set L := petzGenerator cuts σ
  set ρ0 : Operator (d ^ n) := tensorProductOp (fun _ : Fin n => pureZero d)
  have hd0 : 0 < d := by omega
  have hℓ0 : 0 < ℓ := by omega
  have hle' : ℓ ≤ n := by omega
  have hρ0 : IsDensityOperator ρ0 := isDensityOperator_tensorProductOp_pureZero hd0
  have hb : ∀ t : ℝ, t < (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d →
      halfTraceDistance (superExp L t ρ0) σ > ε := by
    intro t ht
    rcases hreg with hT0 | hεreg
    · exact halfTraceDistance_superExp_zero_gt_eps_of_neg hd hℓ0 hle' β cuts hc ε hε hε2 t
        (lt_of_lt_of_le ht hT0)
    · exact halfTraceDistance_superExp_zero_gt_eps_of_thresh hd hℓ0 hle' β cuts hc ε hε hεreg t ht
  refine ⟨?_, hb, ?_⟩
  · have hsub : ∀ t : ℝ,
        t ∈ {t : ℝ | 0 ≤ t ∧ ∀ ρ : Operator (d ^ n), IsDensityOperator ρ →
            halfTraceDistance (superExp L t ρ) σ ≤ ε} →
          (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d ≤ t := by
      intro t ht
      by_contra hcon
      have hlt : t < (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d := by
        linarith
      have hgt := hb t hlt
      exact not_lt.mpr (ht.2 ρ0 hρ0) hgt
    have hneS : Set.Nonempty {t : ℝ | 0 ≤ t ∧ ∀ ρ : Operator (d ^ n), IsDensityOperator ρ →
        halfTraceDistance (superExp L t ρ) σ ≤ ε} := by
      obtain ⟨t, ht0, ht⟩ := hne
      exact ⟨t, ht0, ht⟩
    have hinf := le_csInf hneS hsub
    show (1 / 2 : ℝ) * Real.log ((n : ℝ) / ε) - lowerBoundConst ℓ d ≤ mixingTime L σ ε
    unfold mixingTime
    exact hinf
  · intro t _ i out
    exact siteMarginalMass_superExp_zero hd0 hℓ0 hle' β cuts hc t i out

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

theorem halfTraceDistance_eq_traceNorm {D : ℕ} (ρ σ : Operator D) :
    halfTraceDistance ρ σ = (1 / 2 : ℝ) * Matrix.traceNorm (ρ - σ) := by
  unfold halfTraceDistance
  rw [Qatlib.Foundations.PureStateMath.BornBridge.schattenOne_eq_physlib_traceNorm]

theorem halfTraceDistance_self {D : ℕ} (ρ : Operator D) : halfTraceDistance ρ ρ = 0 := by
  rw [halfTraceDistance_eq_traceNorm, sub_self, Matrix.traceNorm_zero, mul_zero]

theorem halfTraceDistance_smul {D : ℕ} (k : ℂ) (ρ σ : Operator D) :
    halfTraceDistance (k • ρ) (k • σ) = ‖k‖ * halfTraceDistance ρ σ := by
  have hsm : (k • ρ - k • σ : Operator D) = k • (ρ - σ) := by
    rw [smul_sub]
  rw [halfTraceDistance_eq_traceNorm, halfTraceDistance_eq_traceNorm, hsm,
    Matrix.traceNorm_smul]
  ring

theorem halfTraceDistance_add_le {D : ℕ} (ρ1 σ1 ρ2 σ2 : Operator D) :
    halfTraceDistance (ρ1 + ρ2) (σ1 + σ2)
      ≤ halfTraceDistance ρ1 σ1 + halfTraceDistance ρ2 σ2 := by
  have hsm : (ρ1 + ρ2 - (σ1 + σ2) : Operator D) = (ρ1 - σ1) + (ρ2 - σ2) := by
    abel
  rw [halfTraceDistance_eq_traceNorm, halfTraceDistance_eq_traceNorm,
    halfTraceDistance_eq_traceNorm, hsm]
  have hle := Matrix.traceNorm_add_le (ρ1 - σ1) (ρ2 - σ2)
  have h1 : 0 ≤ Matrix.traceNorm (ρ1 - σ1) := Matrix.traceNorm_nonneg _
  have h2 : 0 ≤ Matrix.traceNorm (ρ2 - σ2) := Matrix.traceNorm_nonneg _
  nlinarith

theorem halfTraceDistance_convex {D : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (ρ1 σ1 ρ2 σ2 : Operator D) :
    halfTraceDistance ((p : ℂ) • ρ1 + (q : ℂ) • ρ2) ((p : ℂ) • σ1 + (q : ℂ) • σ2)
      ≤ p * halfTraceDistance ρ1 σ1 + q * halfTraceDistance ρ2 σ2 := by
  have h1 := halfTraceDistance_smul (p : ℂ) ρ1 σ1
  have h2 := halfTraceDistance_smul (q : ℂ) ρ2 σ2
  have h3 := halfTraceDistance_add_le ((p : ℂ) • ρ1) ((p : ℂ) • σ1)
    ((q : ℂ) • ρ2) ((q : ℂ) • σ2)
  have hn1 : ‖(p : ℂ)‖ = p := Complex.norm_of_nonneg (by exact_mod_cast hp)
  have hn2 : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg (by exact_mod_cast hq)
  rw [hn1] at h1
  rw [hn2] at h2
  rw [h1, h2] at h3
  exact h3

theorem halfTraceDistance_le_one {D : ℕ} {ρ σ : Operator D} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : halfTraceDistance ρ σ ≤ 1 := by
  rw [halfTraceDistance_eq_traceNorm]
  have htr : (Matrix.trace (ρ - σ)).re = 0 := by
    rw [Matrix.trace_sub, Complex.sub_re, hρ.2, hσ.2, Complex.one_re, sub_self]
  have hsub : (ρ - σ : Operator D) = ρ + (-σ) := by abel
  have h1 := Matrix.traceNorm_add_le ρ (-σ)
  rw [← hsub] at h1
  have hnρ : Matrix.traceNorm ρ = 1 := by
    have h := hρ.1.traceNorm_eq_trace
    rw [hρ.2] at h
    have h3 : (((Matrix.traceNorm ρ : ℝ) : ℂ)) = (((1 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_one]
      exact h
    exact Complex.ofReal_inj.mp h3
  have hnσ : Matrix.traceNorm (-σ) = Matrix.traceNorm σ := Matrix.traceNorm_neg σ
  have hnσ' : Matrix.traceNorm σ = 1 := by
    have h := hσ.1.traceNorm_eq_trace
    rw [hσ.2] at h
    have h3 : (((Matrix.traceNorm σ : ℝ) : ℂ)) = (((1 : ℝ) : ℂ)) := by
      rw [Complex.ofReal_one]
      exact h
    exact Complex.ofReal_inj.mp h3
  rw [hnρ, hnσ, hnσ'] at h1
  nlinarith

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable def heatBathComp {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) : (k : ℕ) → (Fin k → Fin n) → Operator (d ^ n) → Operator (d ^ n)
  | 0, _s, ρ => ρ
  | k + 1, s, ρ =>
      petzHeatBath (cuts (s 0)) σ (heatBathComp cuts σ k (fun j : Fin k => s j.succ) ρ)

lemma heatBathComp_zero {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (s : Fin 0 → Fin n) (ρ : Operator (d ^ n)) :
    heatBathComp cuts σ 0 s ρ = ρ := rfl

lemma heatBathComp_succ {n ℓ d k : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (s : Fin (k + 1) → Fin n) (ρ : Operator (d ^ n)) :
    heatBathComp cuts σ (k + 1) s ρ
      = petzHeatBath (cuts (s 0)) σ (heatBathComp cuts σ k (fun j : Fin k => s j.succ) ρ) := rfl

lemma heatBathComp_cons {n ℓ d k : ℕ} (cuts : Fin n → PetzCut n ℓ)
    (σ : Operator (d ^ n)) (j : Fin n) (s : Fin k → Fin n) (ρ : Operator (d ^ n)) :
    heatBathComp cuts σ (k + 1) (Fin.cons j s) ρ
      = petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ) := by
  rw [heatBathComp_succ]
  have h0 : Fin.cons (n := k) (α := fun _ => Fin n) j s 0 = j := by
    simp [Fin.cons]
  have hs : (fun j' : Fin k => Fin.cons (α := fun _ => Fin n) j s j'.succ) = s := by
    ext j'
    simp [Fin.cons]
  rw [h0, hs]

lemma petzHeatBath_sum {n ℓ d : ℕ} {ι : Type*} (c : PetzCut n ℓ) (σ : Operator (d ^ n))
    (s : Finset ι) (f : ι → Operator (d ^ n)) :
    petzHeatBath c σ (∑ i ∈ s, f i) = ∑ i ∈ s, petzHeatBath c σ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : petzHeatBath c σ (0 : Operator (d ^ n)) = 0 := by
      have h := petzHeatBath_smul c σ 0 (0 : Operator (d ^ n))
      rw [zero_smul, zero_smul] at h
      exact h
    simp [h0]
  | insert i s _ ih =>
    rw [Finset.sum_insert ‹_›, Finset.sum_insert ‹_›, petzHeatBath_add, ih]

lemma petzHeatBath_sum_univ {n ℓ d : ℕ} {ι : Type*} [Fintype ι] (c : PetzCut n ℓ)
    (σ : Operator (d ^ n)) (f : ι → Operator (d ^ n)) :
    petzHeatBath c σ (∑ i, f i) = ∑ i, petzHeatBath c σ (f i) :=
  petzHeatBath_sum c σ Finset.univ f

lemma petzHeatBath_zero {n ℓ d : ℕ} (c : PetzCut n ℓ) (σ : Operator (d ^ n)) :
    petzHeatBath c σ (0 : Operator (d ^ n)) = 0 := by
  have h := petzHeatBath_smul c σ 0 (0 : Operator (d ^ n))
  rw [zero_smul, zero_smul] at h
  exact h

lemma blockResetSum_sum {n ℓ d : ℕ} {ι : Type*} (cuts : Fin n → PetzCut n ℓ) (β : ℝ)
    (s : Finset ι) (f : ι → Operator (d ^ n)) :
    blockResetSum cuts β (∑ i ∈ s, f i) = ∑ i ∈ s, blockResetSum cuts β (f i) := by
  classical
  unfold blockResetSum
  have hinner : ∀ j : Fin n,
      petzHeatBath (cuts j) (gibbsState β (0 : Operator (d ^ n))) (∑ i ∈ s, f i)
        = ∑ i ∈ s, petzHeatBath (cuts j) (gibbsState β (0 : Operator (d ^ n))) (f i) :=
    fun j => petzHeatBath_sum _ _ _ _
  rw [Finset.sum_congr rfl (fun j _ => hinner j), Finset.sum_comm]
  simp only [Finset.smul_sum]

lemma blockResetSum_sum_univ {n ℓ d : ℕ} {ι : Type*} [Fintype ι] (cuts : Fin n → PetzCut n ℓ)
    (β : ℝ) (f : ι → Operator (d ^ n)) :
    blockResetSum cuts β (∑ i, f i) = ∑ i, blockResetSum cuts β (f i) :=
  blockResetSum_sum cuts β Finset.univ f

lemma sum_cons_univ {m k D : ℕ} (F : (Fin (k + 1) → Fin m) → Operator D) :
    ∑ t : Fin (k + 1) → Fin m, F t
      = ∑ a : Fin m, ∑ b : Fin k → Fin m, F (Fin.cons a b) := by
  have h := (Fin.consEquiv (fun _ => Fin m)).sum_comp F
  rw [← h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro b _
  rfl

lemma blockResetSum_iterate {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (β : ℝ)
    (k : ℕ) (ρ : Operator (d ^ n)) :
    (blockResetSum cuts β)^[k] ρ
      = (((1 : ℂ) / ℓ) ^ k) •
          ∑ s : Fin k → Fin n,
            heatBathComp cuts (gibbsState β (0 : Operator (d ^ n))) k s ρ := by
  set σ : Operator (d ^ n) := gibbsState β (0 : Operator (d ^ n)) with hσ
  induction k with
  | zero =>
    have hsum : ∑ s : Fin 0 → Fin n, heatBathComp cuts σ 0 s ρ = ρ :=
      Fintype.sum_subsingleton _ (fun i : Fin 0 => i.elim0)
    rw [Function.iterate_zero_apply, hsum, pow_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, blockResetSum_smul]
    have hG : ∀ X : Operator (d ^ n),
        blockResetSum cuts β X = (((1 : ℂ) / ℓ)) • ∑ j : Fin n,
          petzHeatBath (cuts j) σ X := by
      intro X
      show (((1 : ℂ) / ℓ) • ∑ s : Fin n,
        petzHeatBath (cuts s) (gibbsState β (0 : Operator (d ^ n))) X) = _
      rw [hσ]
    rw [hG]
    have hpt : (∑ j : Fin n, petzHeatBath (cuts j) σ
          (∑ s : Fin k → Fin n, heatBathComp cuts σ k s ρ))
        = (∑ j : Fin n, ∑ s : Fin k → Fin n,
            petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ)) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact petzHeatBath_sum_univ _ _ _
    have hcomp : ∀ (j : Fin n) (s : Fin k → Fin n),
        petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ)
          = heatBathComp cuts σ (k + 1) (Fin.cons j s) ρ := by
      intro j s
      exact (heatBathComp_cons cuts σ j s ρ).symm
    have hcomp2 :
        (∑ j : Fin n, ∑ s : Fin k → Fin n, petzHeatBath (cuts j) σ (heatBathComp cuts σ k s ρ))
          = (∑ j : Fin n, ∑ s : Fin k → Fin n,
              heatBathComp cuts σ (k + 1) (Fin.cons j s) ρ) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      exact Finset.sum_congr rfl (fun s _ => hcomp j s)
    rw [hpt, hcomp2, sum_cons_univ, smul_smul, ← pow_succ]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma blockResetSum_zero {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (β : ℝ) :
    blockResetSum cuts β (0 : Operator (d ^ n)) = 0 := by
  have h := blockResetSum_smul cuts β 0 (0 : Operator (d ^ n))
  rw [zero_smul, zero_smul] at h
  exact h

lemma summable_expCoeff_mul_iterate_gen {n d : ℕ}
    (L : Operator (d ^ n) → Operator (d ^ n))
    (hadd : ∀ ρ τ : Operator (d ^ n), L (ρ + τ) = L ρ + L τ)
    (hzero : L 0 = 0)
    (hsmulL : ∀ (k : ℂ) (ρ : Operator (d ^ n)), L (k • ρ) = k • L ρ)
    (t : ℝ) (ρ : Operator (d ^ n)) (i j : Fin (d ^ n)) :
    Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
      * ((L^[k] ρ) i j)) := by
  set M := superMatrix L
  have hpow : ∀ (k : ℕ) (A : Operator (d ^ n)), M ^ k *ᵥ vecOp A = vecOp (L^[k] A) :=
    superMatrix_pow_mulVec L hadd hzero hsmulL
  have hs : ∀ q : Fin (d ^ n) × Fin (d ^ n),
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
        * (((M ^ k) (i, j) q) * vecOp ρ q)) := by
    intro q
    exact Summable.congr ((summable_coeff_pow t M (i, j) q).mul_right (vecOp ρ q))
      (fun k => by ring)
  have hsum : Summable (fun k : ℕ =>
      ∑ q : Fin (d ^ n) × Fin (d ^ n),
        (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * (((M ^ k) (i, j) q) * vecOp ρ q)) :=
    summable_finset_sum Finset.univ _ (fun q _ => hs q)
  have hterm : ∀ k : ℕ,
      (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((L^[k] ρ) i j)
        = ∑ q : Fin (d ^ n) × Fin (d ^ n),
            (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * (((M ^ k) (i, j) q) * vecOp ρ q) := by
    intro k
    have hL : (L^[k] ρ) i j = (M ^ k *ᵥ vecOp ρ) (i, j) := by
      rw [hpow]
      rfl
    rw [hL]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
  exact Summable.congr hsum (fun k => (hterm k).symm)

lemma superExp_entry_eq_tsum {n d : ℕ}
    (L : Operator (d ^ n) → Operator (d ^ n))
    (hadd : ∀ ρ τ : Operator (d ^ n), L (ρ + τ) = L ρ + L τ)
    (hzero : L 0 = 0)
    (hsmulL : ∀ (k : ℂ) (ρ : Operator (d ^ n)), L (k • ρ) = k • L ρ)
    (t : ℝ) (ρ : Operator (d ^ n)) (i j : Fin (d ^ n)) :
    superExp L t ρ i j
      = ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((L^[k] ρ) i j) := by
  set M := superMatrix L
  have hpow : ∀ (k : ℕ) (A : Operator (d ^ n)), M ^ k *ᵥ vecOp A = vecOp (L^[k] A) :=
    superMatrix_pow_mulVec L hadd hzero hsmulL
  have hentry : superExp L t ρ i j
      = ∑ q : Fin (d ^ n) × Fin (d ^ n),
          ∑' k : ℕ, (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
            * (((M ^ k) (i, j) q) * vecOp ρ q) := by
    have h1 : superExp L t ρ i j = (NormedSpace.exp ((t : ℂ) • M) *ᵥ vecOp ρ) (i, j) := rfl
    have h2 : (NormedSpace.exp ((t : ℂ) • M) *ᵥ vecOp ρ) (i, j)
        = ∑ q : Fin (d ^ n) × Fin (d ^ n),
            NormedSpace.exp ((t : ℂ) • M) (i, j) q * vecOp ρ q := by
      simp only [Matrix.mulVec, dotProduct]
    rw [h1, h2]
    apply Finset.sum_congr rfl
    intro q _
    rw [exp_smul_pow_entry t M (i, j) q, ← tsum_mul_right]
    apply tsum_congr
    intro k
    ring
  rw [hentry]
  have hs : ∀ q : Fin (d ^ n) × Fin (d ^ n),
      Summable (fun k : ℕ => (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ)
        * (((M ^ k) (i, j) q) * vecOp ρ q)) := by
    intro q
    exact Summable.congr ((summable_coeff_pow t M (i, j) q).mul_right (vecOp ρ q))
      (fun k => by ring)
  rw [← Summable.tsum_finsetSum (fun q _ => hs q)]
  apply tsum_congr
  intro k
  rw [← Finset.mul_sum]
  have hvec : (∑ q : Fin (d ^ n) × Fin (d ^ n), ((M ^ k) (i, j) q) * vecOp ρ q)
      = (L^[k] ρ) i j := by
    have h1 : (M ^ k *ᵥ vecOp ρ) (i, j)
        = ∑ q : Fin (d ^ n) × Fin (d ^ n), ((M ^ k) (i, j) q) * vecOp ρ q := by
      simp only [Matrix.mulVec, dotProduct]
    rw [← h1, hpow]
    rfl
  rw [hvec]

lemma superExp_blockResetSum_eq_tsum {n ℓ d : ℕ} (cuts : Fin n → PetzCut n ℓ) (β : ℝ)
    (t : ℝ) (ρ : Operator (d ^ n)) :
    superExp (blockResetSum cuts β) t ρ
      = ∑' k : ℕ, ((expCoeff t k : ℝ) : ℂ) • (blockResetSum cuts β)^[k] ρ := by
  set G : Operator (d ^ n) → Operator (d ^ n) := blockResetSum cuts β with hG
  have hadd : ∀ ρ τ : Operator (d ^ n), G (ρ + τ) = G ρ + G τ :=
    fun ρ τ => blockResetSum_add cuts β ρ τ
  have hzero : G 0 = 0 := blockResetSum_zero cuts β
  have hsmulG : ∀ (k : ℂ) (ρ : Operator (d ^ n)), G (k • ρ) = k • G ρ :=
    fun k ρ => blockResetSum_smul cuts β k ρ
  have hsum : Summable (fun k : ℕ => ((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) := by
    have hentry : ∀ i j : Fin (d ^ n),
        Summable (fun k : ℕ => (((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) i j) := by
      intro i j
      have hsm : ∀ k : ℕ, (((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) i j
          = (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((G^[k] ρ) i j) := by
        intro k
        rw [Matrix.smul_apply, expCoeff_eq]
        exact smul_eq_mul _ _
      exact Summable.congr (summable_expCoeff_mul_iterate_gen G hadd hzero hsmulG t ρ i j) hsm
    exact Pi.summable.mpr fun i => Pi.summable.mpr fun j => hentry i j
  ext i j
  rw [tsum_matrix_apply _ hsum i j]
  have hsm : ∀ k : ℕ, (((expCoeff t k : ℝ) : ℂ) • G^[k] ρ) i j
      = (((t : ℝ) ^ k / (k.factorial : ℝ) : ℝ) : ℂ) * ((G^[k] ρ) i j) := by
    intro k
    rw [Matrix.smul_apply, expCoeff_eq]
    exact smul_eq_mul _ _
  simp only [hsm]
  exact superExp_entry_eq_tsum G hadd hzero hsmulG t ρ i j

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma posSemidef_smul_one {D : ℕ} {c : ℝ} (hc : 0 ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Operator D)).PosSemidef := by
  have h1 : (1 : Operator D).PosSemidef := Matrix.PosSemidef.one
  have hsm : (((c : ℝ) : ℂ) • (1 : Operator D)).PosSemidef :=
    h1.smul (by exact_mod_cast hc : (0 : ℂ) ≤ (c : ℂ))
  exact hsm

lemma isDensityOperator_gibbsState_zero {D : ℕ} (β : ℝ) (hD : (D : ℕ) ≠ 0) :
    IsDensityOperator (gibbsState β (0 : Operator D)) := by
  rw [gibbsState_zero]
  have hne : (((D : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast hD
  have htrace : (Matrix.trace (((D : ℕ) : ℂ)⁻¹ • (1 : Operator D)) : ℂ) = 1 := by
    rw [Matrix.trace_smul, trace_one_operator, smul_eq_mul, inv_mul_cancel₀ hne]
  have hpos : (((D : ℕ) : ℂ)⁻¹ • (1 : Operator D)).PosSemidef := by
    rw [cast_inv_nat]
    exact posSemidef_smul_one (by positivity)
  exact ⟨hpos, htrace⟩

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma posSemidef_petzHeatBath_smul_one {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) (hρ : ρ.PosSemidef) :
    (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ).PosSemidef := by
  set e := c.matrixEquiv (d := d) with he
  rw [petzHeatBath_smul_one c k hk hd ρ]
  have hre : (Matrix.reindex e e ρ).PosSemidef := by
    rw [Matrix.reindex_apply]
    exact hρ.submatrix _
  have hpt : (PartialTrace (Matrix.reindex e e ρ)).PosSemidef :=
    partialTrace_posSemidef hre
  have hone : (1 : Operator (d ^ ℓ)).PosSemidef := Matrix.PosSemidef.one
  have hkron : (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ))).PosSemidef :=
    hpt.kronecker hone
  have hnn : (0 : ℂ) ≤ (((d ^ ℓ : ℕ) : ℂ)⁻¹) := by
    rw [cast_inv_nat]
    exact_mod_cast (by positivity : (0 : ℝ) ≤ (((d ^ ℓ : ℕ) : ℝ)⁻¹))
  have hsmul : (((((d ^ ℓ : ℕ) : ℂ)⁻¹) •
      (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ))))).PosSemidef :=
    hkron.smul hnn
  have hfin : (Matrix.reindex e.symm e.symm
      (((((d ^ ℓ : ℕ) : ℂ)⁻¹) •
        (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ)))))).PosSemidef := by
    rw [Matrix.reindex_apply]
    exact hsmul.submatrix _
  have hsmul2 : ((((d ^ ℓ : ℕ) : ℂ)⁻¹) •
      Matrix.reindex e.symm e.symm
        (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ))))
      = Matrix.reindex e.symm e.symm
          (((((d ^ ℓ : ℕ) : ℂ)⁻¹) •
            (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ))))) := by
    rw [reindex_smul_gen]
  rw [hsmul2]
  exact hfin

lemma isDensityOperator_petzHeatBath_smul_one {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ)
    (hk : 0 < k) (hd : 0 < d) (ρ : Operator (d ^ n)) (hρ : IsDensityOperator ρ) :
    IsDensityOperator (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ) := by
  refine ⟨posSemidef_petzHeatBath_smul_one c k hk hd ρ hρ.1, ?_⟩
  exact trace_petzHeatBath_smul_one c k hk hd ρ ▸ hρ.2

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma petzHeatBath_smul_one_entry {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) (g h : SiteConfig n d) :
    (petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ)
        (configEquiv n d g) (configEquiv n d h)
      = if (cutSplitConfig c g).2 = (cutSplitConfig c h).2 then
          (((d ^ ℓ : ℕ) : ℂ)⁻¹) *
            ∑ b : Fin ℓ → Fin d,
              ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 b))
                (configEquiv n d (recombine c (cutSplitConfig c h).1 b))
        else 0 := by
  set e := c.matrixEquiv (d := d) with he
  rw [petzHeatBath_smul_one c k hk hd ρ]
  rw [Matrix.smul_apply, smul_eq_mul]
  have hre : (Matrix.reindex e.symm e.symm
        (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ))))
        (configEquiv n d g) (configEquiv n d h)
      = (PartialTrace (Matrix.reindex e e ρ) ⊗ₖ (1 : Operator (d ^ ℓ)))
          (e (configEquiv n d g)) (e (configEquiv n d h)) := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  rw [hre, matrixEquiv_configSplit, matrixEquiv_configSplit]
  have hkron : ((PartialTrace (Matrix.reindex e e ρ)) ⊗ₖ (1 : Operator (d ^ ℓ)))
        (configEquiv (n - ℓ) d (cutSplitConfig c g).1, configEquiv ℓ d (cutSplitConfig c g).2)
        (configEquiv (n - ℓ) d (cutSplitConfig c h).1, configEquiv ℓ d (cutSplitConfig c h).2)
      = (PartialTrace (Matrix.reindex e e ρ)
          (configEquiv (n - ℓ) d (cutSplitConfig c g).1)
          (configEquiv (n - ℓ) d (cutSplitConfig c h).1))
          * ((1 : Operator (d ^ ℓ))
              (configEquiv ℓ d (cutSplitConfig c g).2)
              (configEquiv ℓ d (cutSplitConfig c h).2)) := by
    rw [Matrix.kronecker_apply]
  rw [hkron]
  have hone : ((1 : Operator (d ^ ℓ))
        (configEquiv ℓ d (cutSplitConfig c g).2)
        (configEquiv ℓ d (cutSplitConfig c h).2))
      = (if (cutSplitConfig c g).2 = (cutSplitConfig c h).2 then (1 : ℂ) else 0) := by
    rw [Matrix.one_apply]
    by_cases heq : (cutSplitConfig c g).2 = (cutSplitConfig c h).2
    · rw [if_pos ((configEquiv ℓ d).injective.eq_iff.mpr heq), if_pos heq]
    · rw [if_neg (fun hcon => heq ((configEquiv ℓ d).injective.eq_iff.mp hcon)),
        if_neg heq]
  rw [hone]
  have hpt : (PartialTrace (Matrix.reindex e e ρ))
        (configEquiv (n - ℓ) d (cutSplitConfig c g).1)
        (configEquiv (n - ℓ) d (cutSplitConfig c h).1)
      = ∑ b : Fin (d ^ ℓ),
          ρ (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b))
            (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c h).1, b)) := by
    simp only [PartialTrace, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [hpt]
  have hsum : (∑ b : Fin (d ^ ℓ),
        ρ (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b))
          (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c h).1, b)))
      = ∑ b : Fin ℓ → Fin d,
          ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 b))
            (configEquiv n d (recombine c (cutSplitConfig c h).1 b)) :=
    (Fintype.sum_equiv (configEquiv ℓ d)
      (fun b : Fin ℓ → Fin d =>
        ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 b))
          (configEquiv n d (recombine c (cutSplitConfig c h).1 b)))
      (fun b : Fin (d ^ ℓ) =>
        ρ (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c g).1, b))
          (e.symm (configEquiv (n - ℓ) d (cutSplitConfig c h).1, b)))
      (fun b => by
        beta_reduce
        rw [matrixEquiv_symm_recombine, matrixEquiv_symm_recombine])).symm
  rw [hsum]
  by_cases heq : (cutSplitConfig c g).2 = (cutSplitConfig c h).2
  · rw [if_pos heq, if_pos heq, mul_one]
  · rw [if_neg heq, if_neg heq]
    simp [mul_zero]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable def resetOn {n d : ℕ} (U : Finset (Fin n)) (ρ : Operator (d ^ n)) :
    Operator (d ^ n) :=
  fun j k =>
    let g := (configEquiv n d).symm j
    let h := (configEquiv n d).symm k
    if (∀ i ∈ U, g i = h i) then
      (((d ^ U.card : ℕ) : ℂ)⁻¹) *
        ∑ a : SiteConfig n d,
          (if (∀ i ∉ U, a i = g i) then
            ρ (configEquiv n d a) (configEquiv n d (fun i => if i ∈ U then a i else h i))
          else 0)
    else 0

lemma resetOn_apply {n d : ℕ} (U : Finset (Fin n)) (ρ : Operator (d ^ n))
    (g h : SiteConfig n d) :
    resetOn U ρ (configEquiv n d g) (configEquiv n d h)
      = if (∀ i ∈ U, g i = h i) then
          (((d ^ U.card : ℕ) : ℂ)⁻¹) *
            ∑ a : SiteConfig n d,
              (if (∀ i ∉ U, a i = g i) then
                ρ (configEquiv n d a) (configEquiv n d (fun i => if i ∈ U then a i else h i))
              else 0)
        else 0 := by
  unfold resetOn
  simp only [Equiv.symm_apply_apply]

def cutBlockSites {n ℓ : ℕ} (c : PetzCut n ℓ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ∃ k : Fin ℓ, c.siteSplit i = Sum.inr k)

lemma cutBlockSites_card {n ℓ : ℕ} (c : PetzCut n ℓ) : (cutBlockSites c).card = ℓ := by
  classical
  have h : cutBlockSites c
      = Finset.univ.map ⟨fun k : Fin ℓ => c.siteSplit.symm (Sum.inr k),
          fun a b hab => Sum.inr_injective (c.siteSplit.symm.injective hab)⟩ := by
    ext i
    simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro hex
      obtain ⟨k, hk⟩ := hex
      refine ⟨k, ?_⟩
      rw [← hk]
      simp
    · intro hex
      obtain ⟨k, hk⟩ := hex
      refine ⟨k, ?_⟩
      rw [← hk]
      simp
  rw [h, Finset.card_map]
  show Fintype.card (Fin ℓ) = ℓ
  exact Fintype.card_fin ℓ

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma cutSplitConfig_fst_apply {n ℓ d : ℕ} (c : PetzCut n ℓ) (g : SiteConfig n d)
    (k : Fin (n - ℓ)) : (cutSplitConfig c g).1 k = g (c.siteSplit.symm (Sum.inl k)) := by
  rw [cutSplitConfig_apply]
  rfl

lemma cutSplitConfig_snd_apply {n ℓ d : ℕ} (c : PetzCut n ℓ) (g : SiteConfig n d)
    (k : Fin ℓ) : (cutSplitConfig c g).2 k = g (c.siteSplit.symm (Sum.inr k)) := by
  rw [cutSplitConfig_apply]
  rfl

lemma recombine_apply_eq {n ℓ d : ℕ} (c : PetzCut n ℓ) (u : Fin (n - ℓ) → Fin d)
    (v : Fin ℓ → Fin d) (i : Fin n) :
    recombine c u v i = (match c.siteSplit i with
      | Sum.inl k => u k
      | Sum.inr j => v j) := by
  cases h : c.siteSplit i with
  | inl k => rw [recombine_apply_inl c u v h]
  | inr j => rw [recombine_apply_inr c u v h]

lemma exists_recombine_iff {n ℓ d : ℕ} (c : PetzCut n ℓ) (g : SiteConfig n d)
    (a : SiteConfig n d) :
    (∀ i ∉ cutBlockSites c, a i = g i) ↔
      ∃ b : Fin ℓ → Fin d, a = recombine c (cutSplitConfig c g).1 b := by
  constructor
  · intro hex
    refine ⟨fun k => a (c.siteSplit.symm (Sum.inr k)), ?_⟩
    funext i
    cases h : c.siteSplit i with
    | inl k =>
      have hi : i ∉ cutBlockSites c := by
        intro hmem
        simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        obtain ⟨j, hj⟩ := hmem
        rw [h] at hj
        exact Sum.inl_ne_inr hj
      have hag := hex i hi
      have hi2 : c.siteSplit.symm (Sum.inl k) = i := by
        rw [← h, Equiv.symm_apply_apply]
      rw [recombine_apply_inl _ _ _ h, cutSplitConfig_fst_apply, hi2]
      exact hag
    | inr j =>
      rw [recombine_apply_inr _ _ _ h]
      have hi2 : c.siteSplit.symm (Sum.inr j) = i := by
        rw [← h, Equiv.symm_apply_apply]
      rw [hi2]
  · intro hex
    obtain ⟨b, rfl⟩ := hex
    intro i hi
    simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    cases h : c.siteSplit i with
    | inl k =>
      rw [recombine_apply_inl _ _ _ h, cutSplitConfig_fst_apply]
      have hi2 : c.siteSplit.symm (Sum.inl k) = i := by
        rw [← h, Equiv.symm_apply_apply]
      rw [hi2]
    | inr j =>
      exact absurd ⟨j, h⟩ hi

lemma petzHeatBath_smul_one_eq_resetOn {n ℓ d : ℕ} (c : PetzCut n ℓ) (k : ℝ) (hk : 0 < k)
    (hd : 0 < d) (ρ : Operator (d ^ n)) :
    petzHeatBath c (((k : ℝ) : ℂ) • (1 : Operator (d ^ n))) ρ
      = resetOn (cutBlockSites c) ρ := by
  ext j l
  rw [← Equiv.apply_symm_apply (configEquiv n d) j, ← Equiv.apply_symm_apply (configEquiv n d) l]
  set g : SiteConfig n d := (configEquiv n d).symm j
  set h : SiteConfig n d := (configEquiv n d).symm l
  rw [petzHeatBath_smul_one_entry c k hk hd ρ g h, resetOn_apply (cutBlockSites c) ρ g h]
  have hδ : ((cutSplitConfig c g).2 = (cutSplitConfig c h).2) ↔
      (∀ i ∈ cutBlockSites c, g i = h i) := by
    constructor
    · intro heq i hi
      simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      obtain ⟨k', hk'⟩ := hi
      have hg : g i = (cutSplitConfig c g).2 k' := by
        rw [cutSplitConfig_snd_apply, ← hk', Equiv.symm_apply_apply]
      have hh : h i = (cutSplitConfig c h).2 k' := by
        rw [cutSplitConfig_snd_apply, ← hk', Equiv.symm_apply_apply]
      rw [hg, hh, heq]
    · intro hall
      funext k'
      have hi : c.siteSplit.symm (Sum.inr k') ∈ cutBlockSites c := by
        simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨k', by simp⟩
      have := hall _ hi
      rw [cutSplitConfig_snd_apply, cutSplitConfig_snd_apply]
      exact this
  by_cases hδg : ∀ i ∈ cutBlockSites c, g i = h i
  · rw [if_pos (hδ.mpr hδg), if_pos hδg, cutBlockSites_card]
    congr 1
    have hsum : (∑ b : Fin ℓ → Fin d,
          ρ (configEquiv n d (recombine c (cutSplitConfig c g).1 b))
            (configEquiv n d (recombine c (cutSplitConfig c h).1 b)))
        = ∑ a : SiteConfig n d,
            (if (∀ i ∉ cutBlockSites c, a i = g i) then
              ρ (configEquiv n d a)
                (configEquiv n d (fun i => if i ∈ cutBlockSites c then a i else h i))
            else 0) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij
        (fun b _ => recombine c (cutSplitConfig c g).1 b) ?_ ?_ ?_ ?_
      · intro b _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        cases hh : c.siteSplit i with
        | inl kk =>
          rw [recombine_apply_inl _ _ _ hh, cutSplitConfig_fst_apply]
          have hi2 : c.siteSplit.symm (Sum.inl kk) = i := by
            rw [← hh, Equiv.symm_apply_apply]
          rw [hi2]
        | inr jj =>
          exact absurd ⟨jj, hh⟩ hi
      · intro b₁ _ b₂ _ heq
        have heq' : recombine c (cutSplitConfig c g).1 b₁
            = recombine c (cutSplitConfig c g).1 b₂ := heq
        funext k'
        have hsp : c.siteSplit (c.siteSplit.symm (Sum.inr k')) = Sum.inr k' :=
          Equiv.apply_symm_apply _ _
        have h1 := congrFun heq' (c.siteSplit.symm (Sum.inr k'))
        rw [recombine_apply_inr _ _ _ hsp, recombine_apply_inr _ _ _ hsp] at h1
        exact h1
      · intro a ha
        have hmatch : ∀ i ∉ cutBlockSites c, a i = g i := by
          simpa [Finset.mem_filter] using ha
        obtain ⟨b, rfl⟩ := exists_recombine_iff c g a |>.mp hmatch
        exact ⟨b, Finset.mem_univ _, rfl⟩
      · intro b _
        congr 1
        congr 1
        funext i
        cases hh : c.siteSplit i with
        | inl kk =>
          rw [recombine_apply_inl _ _ _ hh]
          have hmem : i ∉ cutBlockSites c := by
            intro hm
            simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and] at hm
            obtain ⟨j', hj'⟩ := hm
            rw [hh] at hj'
            exact absurd hj' (by simp)
          rw [if_neg hmem, cutSplitConfig_fst_apply]
          rw [← hh, Equiv.symm_apply_apply]
        | inr jj =>
          rw [recombine_apply_inr _ _ _ hh]
          have hmem : i ∈ cutBlockSites c := by
            simp only [cutBlockSites, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨jj, by simp [hh]⟩
          rw [if_pos hmem]
          show b jj = recombine c (cutSplitConfig c g).1 b i
          rw [recombine_apply_inr _ _ _ hh]
    rw [hsum]
  · rw [if_neg (fun heq => hδg (hδ.mp heq)), if_neg hδg]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

noncomputable def matchEquivInv {n d : ℕ} (U B : Finset (Fin n)) (g a : SiteConfig n d)
    (_hval : ∀ i ∉ (U ∪ B), a i = g i) (f : ↥(U ∩ B) → Fin d) : SiteConfig n d :=
  fun i => if hiU : i ∈ U then
    (if hiB : i ∈ B then f ⟨i, Finset.mem_inter.mpr ⟨hiU, hiB⟩⟩ else g i)
  else a i

lemma matchEquivInv_mem {n d : ℕ} (U B : Finset (Fin n)) (g a : SiteConfig n d)
    (hval : ∀ i ∉ (U ∪ B), a i = g i) (f : ↥(U ∩ B) → Fin d) :
    (∀ i ∉ B, matchEquivInv U B g a hval f i = g i) ∧
      (∀ i ∉ U, matchEquivInv U B g a hval f i = a i) := by
  constructor
  · intro i hiB
    unfold matchEquivInv
    by_cases hiU : i ∈ U
    · rw [dif_pos hiU, dif_neg hiB]
    · rw [dif_neg hiU]
      exact hval i (by simp [Finset.mem_union, hiU, hiB])
  · intro i hiU
    unfold matchEquivInv
    rw [dif_neg hiU]

lemma card_configs_match {n d : ℕ} (U B : Finset (Fin n)) (g a : SiteConfig n d) :
    (Finset.univ.filter (fun c : SiteConfig n d =>
      (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i))).card
    = if (∀ i ∉ (U ∪ B), a i = g i) then d ^ (U ∩ B).card else 0 := by
  classical
  by_cases hval : ∀ i ∉ (U ∪ B), a i = g i
  · rw [if_pos hval]
    have e : {c : SiteConfig n d // (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i)}
        ≃ (↥(U ∩ B) → Fin d) :=
      { toFun := fun c i => c.1 i
        invFun := fun f => ⟨matchEquivInv U B g a hval f, matchEquivInv_mem U B g a hval f⟩
        left_inv := by
          intro c
          obtain ⟨c0, hc⟩ := c
          apply Subtype.ext
          funext i
          by_cases hiU : i ∈ U
          · by_cases hiB : i ∈ B
            · have hi : i ∈ U ∩ B := Finset.mem_inter.mpr ⟨hiU, hiB⟩
              simp only [matchEquivInv, dif_pos hiU, dif_pos hiB]
            · simp only [matchEquivInv, dif_pos hiU, dif_neg hiB]
              exact (hc.1 i hiB).symm
          · simp only [matchEquivInv, dif_neg hiU]
            by_cases hiB : i ∈ B
            · exact (hc.2 i hiU).symm
            · have hi : i ∉ U ∪ B := by simp [Finset.mem_union, hiU, hiB]
              exact (hval i hi).trans (hc.1 i hiB).symm
        right_inv := by
          intro f
          funext i
          obtain ⟨i0, hi⟩ := i
          have hi' := Finset.mem_inter.mp hi
          have hiU : i0 ∈ U := hi'.1
          have hiB : i0 ∈ B := hi'.2
          simp only [matchEquivInv, dif_pos hiU, dif_pos hiB] }
    have hcard1 : (Finset.univ.filter (fun c : SiteConfig n d =>
        (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i))).card
        = Fintype.card {c : SiteConfig n d // (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i)} := by
      have e1 : ↥(Finset.univ.filter (fun c : SiteConfig n d =>
          (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i)))
          ≃ {c : SiteConfig n d // (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i)} :=
        Equiv.mk
          (fun x => ⟨x.1, by
            have h := x.2
            rw [Finset.mem_filter] at h
            exact h.2⟩)
          (fun x => ⟨x.1, by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, x.2⟩⟩)
          (fun x => Subtype.ext rfl)
          (fun x => Subtype.ext rfl)
      rw [← Fintype.card_coe]
      exact Fintype.card_congr e1
    have hcard2 : Fintype.card {c : SiteConfig n d // (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i)}
        = Fintype.card (↥(U ∩ B) → Fin d) := Fintype.card_congr e
    have hcard3 : Fintype.card (↥(U ∩ B) → Fin d) = d ^ (U ∩ B).card := by
      rw [Fintype.card_pi, Fintype.card_fin]
      rw [Finset.prod_const]
      have hcoe : (Finset.univ : Finset ↥(U ∩ B)).card = (U ∩ B).card :=
        Fintype.card_coe _
      rw [hcoe]
    rw [hcard1, hcard2, hcard3]
  · rw [if_neg hval]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hc1, hc2⟩ := hc
    apply hval
    intro i hi
    have hiB : i ∉ B := by
      intro hib
      simp [Finset.mem_union, hib] at hi
    have hiU : i ∉ U := by
      intro hiu
      simp [Finset.mem_union, hiu] at hi
    exact (hc2 i hiU).symm.trans (hc1 i hiB)

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma comp_second_arg {n d : ℕ} (U B : Finset (Fin n)) (a c h : SiteConfig n d)
    (hmatch : ∀ i ∉ U, a i = c i) :
    (fun i => if i ∈ U then a i else if i ∈ B then c i else h i)
      = (fun i => if i ∈ U ∪ B then a i else h i) := by
  funext i
  by_cases hiU : i ∈ U
  · rw [if_pos hiU, if_pos (by simp [Finset.mem_union, hiU] : i ∈ U ∪ B)]
  · by_cases hiB : i ∈ B
    · rw [if_neg hiU, if_pos hiB, if_pos (by simp [Finset.mem_union, hiB] : i ∈ U ∪ B)]
      exact (hmatch i hiU).symm ▸ rfl
    · rw [if_neg hiU, if_neg hiB, if_neg (by simp [Finset.mem_union, hiU, hiB] : i ∉ U ∪ B)]

lemma delta_comp {n d : ℕ} (U B : Finset (Fin n)) (g c h : SiteConfig n d)
    (hcg : ∀ i ∉ B, c i = g i) :
    ((∀ i ∈ U, c i = (fun j => if j ∈ B then c j else h j) i) ↔
      ∀ i ∈ U, i ∉ B → g i = h i) := by
  constructor
  · intro hall i hiU hiB
    have hc : c i = (if i ∈ B then c i else h i) := by
      show c i = (fun j => if j ∈ B then c j else h j) i
      exact hall i hiU
    rw [if_neg hiB] at hc
    rw [← hc, hcg i hiB]
  · intro hall i hiU
    show c i = if i ∈ B then c i else h i
    by_cases hiB : i ∈ B
    · rw [if_pos hiB]
    · rw [if_neg hiB]
      rw [hcg i hiB]
      exact hall i hiU hiB

lemma delta_union {n d : ℕ} (U B : Finset (Fin n)) (g h : SiteConfig n d) :
    ((∀ i ∈ B, g i = h i) ∧ (∀ i ∈ U, i ∉ B → g i = h i) ↔
      ∀ i ∈ U ∪ B, g i = h i) := by
  constructor
  · intro ⟨hB, hU⟩ i hi
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · by_cases hiB : i ∈ B
      · exact hB i hiB
      · exact hU i hi hiB
    · exact hB i hi
  · intro hall
    constructor
    · intro i hi
      exact hall i (by simp [Finset.mem_union, hi])
    · intro i hiU hiB
      exact hall i (by simp [Finset.mem_union, hiU])

lemma card_union_add_inter {n : ℕ} (U B : Finset (Fin n)) :
    U.card + B.card = (U ∪ B).card + (U ∩ B).card := by
  classical
  rw [← Finset.card_union_add_card_inter]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma ite_and_pair {α : Type*} {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂]
    [Decidable (c₁ ∧ c₂)] (t e : α) :
    (if c₁ ∧ c₂ then t else e) = (if c₁ then (if c₂ then t else e) else e) := by
  by_cases h1 : c₁ <;> by_cases h2 : c₂ <;> simp [h1, h2]

lemma sum_sum_count {n d : ℕ} (U B : Finset (Fin n)) (g : SiteConfig n d)
    (F : SiteConfig n d → ℂ) :
    (∑ c : SiteConfig n d, (if ∀ i ∉ B, c i = g i then
       (∑ a : SiteConfig n d, (if ∀ i ∉ U, a i = c i then F a else 0)) else 0))
    = (((d ^ (U ∩ B).card : ℕ) : ℂ)) *
      ∑ a : SiteConfig n d, (if ∀ i ∉ (U ∪ B), a i = g i then F a else 0) := by
  classical
  have hswap : (∑ c : SiteConfig n d, (if ∀ i ∉ B, c i = g i then
        (∑ a : SiteConfig n d, (if ∀ i ∉ U, a i = c i then F a else 0)) else 0))
      = (∑ c : SiteConfig n d, ∑ a : SiteConfig n d,
          (if (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i) then F a else 0)) := by
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : ∀ i ∉ B, c i = g i
    · rw [if_pos hc]
      have hq : (Finset.univ.filter
            (fun a : SiteConfig n d => (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i)))
          = (Finset.univ.filter (fun a : SiteConfig n d => (∀ i ∉ U, a i = c i))) := by
        apply Finset.filter_congr
        intro a _
        exact ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩
      rw [← Finset.sum_filter, ← Finset.sum_filter, hq]
    · rw [if_neg hc]
      have hz : (∑ a : SiteConfig n d,
          (if (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i) then F a else 0)) = 0 := by
        rw [Finset.sum_eq_zero]
        intro a _
        rw [if_neg (fun hconj => hc hconj.1)]
      rw [hz]
  rw [hswap, Finset.sum_comm]
  have hper : ∀ a : SiteConfig n d,
      (∑ c : SiteConfig n d,
        (if (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i) then F a else 0))
      = F a * ((∑ c : SiteConfig n d,
          (if (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i) then (1 : ℂ) else 0))) := by
    intro a
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hconj : (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i)
    · rw [if_pos hconj, if_pos hconj, mul_one]
    · rw [if_neg hconj, if_neg hconj, mul_zero]
  simp only [hper]
  have hcount : ∀ a : SiteConfig n d,
      (∑ c : SiteConfig n d,
        (if (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i) then (1 : ℂ) else 0))
      = (if (∀ i ∉ (U ∪ B), a i = g i) then (((d ^ (U ∩ B).card : ℕ) : ℂ)) else 0) := by
    intro a
    rw [← Finset.sum_filter]
    have h1 : (∑ c ∈ Finset.univ.filter
          (fun c : SiteConfig n d => (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i)),
          (1 : ℂ))
        = (((Finset.univ.filter
          (fun c : SiteConfig n d => (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i))).card : ℕ) : ℂ) := by
      rw [Finset.sum_const, nsmul_one]
    have hp : (Finset.univ.filter
          (fun c : SiteConfig n d => (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, a i = c i)))
        = (Finset.univ.filter
          (fun c : SiteConfig n d => (∀ i ∉ B, c i = g i) ∧ (∀ i ∉ U, c i = a i))) := by
      apply Finset.filter_congr
      intro c _
      simp only [eq_comm]
    rw [h1, hp, card_configs_match]
    by_cases hval : ∀ i ∉ (U ∪ B), a i = g i
    · rw [if_pos hval, if_pos hval]
    · rw [if_neg hval, if_neg hval]
      simp
  simp only [hcount]
  have hz : (∑ a : SiteConfig n d,
      F a * (if ∀ i ∉ (U ∪ B), a i = g i then (((d ^ (U ∩ B).card : ℕ) : ℂ)) else 0))
      = (((d ^ (U ∩ B).card : ℕ) : ℂ)) *
        (∑ a : SiteConfig n d, (if ∀ i ∉ (U ∪ B), a i = g i then F a else 0)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hval : ∀ i ∉ (U ∪ B), a i = g i
    · rw [if_pos hval, if_pos hval, mul_comm]
    · rw [if_neg hval, if_neg hval]
      simp [mul_zero]
  rw [hz]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

namespace Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz

set_option autoImplicit false

open Qatlib Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetzCoreDefs
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder

lemma cast_pow_inv_scalar {d Uc Bc Ic Kc : ℕ} (hcard : Uc + Bc = Kc + Ic)
    (hd : 0 < d) :
    (((d ^ Bc : ℕ) : ℂ))⁻¹ * (((d ^ Uc : ℕ) : ℂ))⁻¹ * (((d ^ Ic : ℕ) : ℂ))
      = (((d ^ Kc : ℕ) : ℂ))⁻¹ := by
  have hpow : ∀ m : ℕ, (((d ^ m : ℕ) : ℂ)) = ((d : ℂ) ^ m) := by
    intro m
    rw [Nat.cast_pow]
  have hne : ∀ m : ℕ, ((d : ℂ) ^ m) ≠ 0 := by
    intro m
    exact pow_ne_zero _ (by exact_mod_cast (ne_of_gt hd))
  simp only [hpow]
  have h1 : (((d : ℂ) ^ Bc)⁻¹ * ((d : ℂ) ^ Uc)⁻¹) = (((d : ℂ) ^ (Uc + Bc))⁻¹) := by
    rw [← _root_.mul_inv_rev, ← pow_add]
  rw [h1, hcard, pow_add, _root_.mul_inv_rev,
    mul_comm (((d : ℂ) ^ Ic)⁻¹) (((d : ℂ) ^ Kc)⁻¹),
    mul_assoc, inv_mul_cancel₀ (hne Ic), mul_one]

lemma resetOn_comp {n d : ℕ} (U B : Finset (Fin n)) (ρ : Operator (d ^ n)) (hd : 0 < d) :
    resetOn B (resetOn U ρ) = resetOn (U ∪ B) ρ := by
  classical
  ext j l
  rw [← Equiv.apply_symm_apply (configEquiv n d) j, ← Equiv.apply_symm_apply (configEquiv n d) l]
  set g : SiteConfig n d := (configEquiv n d).symm j
  set h : SiteConfig n d := (configEquiv n d).symm l
  rw [resetOn_apply B (resetOn U ρ) g h, resetOn_apply (U ∪ B) ρ g h]
  set F : SiteConfig n d → ℂ := fun a =>
    ρ (configEquiv n d a) (configEquiv n d (fun i => if i ∈ U ∪ B then a i else h i)) with hF
  have hsplit : ∀ c : SiteConfig n d,
      (resetOn U ρ) (configEquiv n d c) (configEquiv n d (fun i => if i ∈ B then c i else h i))
      = (if (∀ i ∈ U, c i = (fun j => if j ∈ B then c j else h j) i) then
          (((d ^ U.card : ℕ) : ℂ)⁻¹) *
            ∑ a : SiteConfig n d,
              (if (∀ i ∉ U, a i = c i) then
                ρ (configEquiv n d a)
                  (configEquiv n d
                    (fun i => if i ∈ U then a i else (fun j => if j ∈ B then c j else h j) i))
              else 0)
        else 0) := by
    intro c
    exact resetOn_apply U ρ c (fun i => if i ∈ B then c i else h i)
  by_cases hδUB : ∀ i ∈ U ∪ B, g i = h i
  · have hδB : ∀ i ∈ B, g i = h i := fun i hi => hδUB i (by simp [Finset.mem_union, hi])
    have hD : ∀ i ∈ U, i ∉ B → g i = h i := by
      intro i hiU hiB
      exact hδUB i (by simp [Finset.mem_union, hiU])
    rw [if_pos hδB, if_pos hδUB]
    have hsumform : ∀ c : SiteConfig n d, (∀ i ∉ B, c i = g i) →
        (resetOn U ρ) (configEquiv n d c) (configEquiv n d (fun i => if i ∈ B then c i else h i))
          = (((d ^ U.card : ℕ) : ℂ)⁻¹) *
            ∑ a : SiteConfig n d, (if (∀ i ∉ U, a i = c i) then F a else 0) := by
      intro c hc
      rw [hsplit c]
      have hδ : (∀ i ∈ U, c i = (fun j => if j ∈ B then c j else h j) i) :=
        (delta_comp U B g c h hc).mpr hD
      rw [if_pos hδ]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      by_cases hpa : ∀ i ∉ U, a i = c i
      · rw [if_pos hpa, if_pos hpa]
        rw [hF]
        congr 1
        exact congrArg (configEquiv n d) (comp_second_arg U B a c h hpa)
      · rw [if_neg hpa, if_neg hpa]
    have hrew : (∑ c : SiteConfig n d,
          (if ∀ i ∉ B, c i = g i then
            (resetOn U ρ) (configEquiv n d c)
              (configEquiv n d (fun i => if i ∈ B then c i else h i)) else 0))
        = (((d ^ U.card : ℕ) : ℂ)⁻¹) *
          (∑ c : SiteConfig n d,
            (if ∀ i ∉ B, c i = g i then
              (∑ a : SiteConfig n d, (if (∀ i ∉ U, a i = c i) then F a else 0)) else 0)) := by
      have h1 : (∑ c : SiteConfig n d,
            (if ∀ i ∉ B, c i = g i then
              (resetOn U ρ) (configEquiv n d c)
                (configEquiv n d (fun i => if i ∈ B then c i else h i)) else 0))
          = (∑ c : SiteConfig n d,
            (if ∀ i ∉ B, c i = g i then
              (((d ^ U.card : ℕ) : ℂ)⁻¹) *
                (∑ a : SiteConfig n d, (if (∀ i ∉ U, a i = c i) then F a else 0)) else 0)) := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : ∀ i ∉ B, c i = g i
        · rw [if_pos hc, if_pos hc, hsumform c hc]
        · rw [if_neg hc, if_neg hc]
      rw [h1]
      have hL : (∑ c : SiteConfig n d,
            (if ∀ i ∉ B, c i = g i then
              (((d ^ U.card : ℕ) : ℂ)⁻¹) *
                (∑ a : SiteConfig n d, (if (∀ i ∉ U, a i = c i) then F a else 0)) else 0))
          = (∑ c ∈ Finset.univ.filter (fun c : SiteConfig n d => ∀ i ∉ B, c i = g i),
              (((d ^ U.card : ℕ) : ℂ)⁻¹) *
                (∑ a : SiteConfig n d, (if (∀ i ∉ U, a i = c i) then F a else 0))) := by
        rw [Finset.sum_filter]
      rw [hL, ← Finset.mul_sum]
      rw [← Finset.sum_filter]
    rw [hrew]
    have hsum := sum_sum_count U B g F
    rw [hsum]
    have hkey : (((d ^ B.card : ℕ) : ℂ))⁻¹ * (((d ^ U.card : ℕ) : ℂ))⁻¹ *
        (((d ^ (U ∩ B).card : ℕ) : ℂ)) = (((d ^ (U ∪ B).card : ℕ) : ℂ))⁻¹ := by
      have hcards : U.card + B.card = (U ∪ B).card + (U ∩ B).card := card_union_add_inter U B
      have hsc := cast_pow_inv_scalar hcards hd
      exact hsc
    rw [← mul_assoc, ← mul_assoc, hkey]
  · rw [if_neg hδUB]
    by_cases hδB : ∀ i ∈ B, g i = h i
    · rw [if_pos hδB]
      have hDneg : ¬∀ i ∈ U, i ∉ B → g i = h i := by
        intro hall
        apply hδUB
        exact (delta_union U B g h).mp ⟨hδB, hall⟩
      have hz : (∑ c : SiteConfig n d,
          (if ∀ i ∉ B, c i = g i then
            (resetOn U ρ) (configEquiv n d c)
              (configEquiv n d (fun i => if i ∈ B then c i else h i)) else 0)) = 0 := by
        rw [Finset.sum_eq_zero]
        intro c hc
        by_cases hpc : ∀ i ∉ B, c i = g i
        · have hδ : ¬(∀ i ∈ U, c i = (fun j => if j ∈ B then c j else h j) i) := by
            intro hall
            apply hDneg
            exact (delta_comp U B g c h hpc).mp hall
          rw [if_pos hpc, hsplit c, if_neg hδ]
        · rw [if_neg hpc]
      rw [hz, mul_zero]
    · rw [if_neg hδB]

end Qatlib.Papers.SpinChainMix26.RapidMixing.RapidMixingPetz
