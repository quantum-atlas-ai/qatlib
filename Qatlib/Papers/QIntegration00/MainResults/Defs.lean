/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

set_option autoImplicit false

namespace Qatlib.Papers.QIntegration00.MainResults.Defs

def gamma (d k : ℕ) (α : ℝ) : ℝ := ((k : ℝ) + α) / (d : ℝ)

theorem gamma_pos {d k : ℕ} {α : ℝ} (hd : 0 < d) (hα : 0 < α) : 0 < gamma d k α := by
  unfold gamma
  positivity

theorem gamma_nonneg {d k : ℕ} {α : ℝ} (hd : 0 < d) (hα : 0 ≤ α) : 0 ≤ gamma d k α := by
  unfold gamma
  positivity

theorem gamma_le_gamma_of_le {d k : ℕ} {α α' : ℝ} (hd : 0 < d) (hα : α ≤ α') :
    gamma d k α ≤ gamma d k α' := by
  unfold gamma
  gcongr

def unitCube (d : ℕ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

def HolderClass (d k : ℕ) (α : ℝ) : Set ((Fin d → ℝ) → ℝ) :=
  {f | (∀ x ∈ unitCube d, |f x| ≤ 1) ∧
       ContDiff ℝ (k : ℕ∞) f ∧
       ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
         ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ ≤ ‖x - y‖ ^ α}

def complexityOf (cost error : ℝ → ℝ) (ε : ℝ) : ℝ :=
  ⨅ t : {t : ℝ // 0 < t ∧ error t ≤ ε}, cost t.1

theorem complexityOf_le {cost error : ℝ → ℝ} (hcost : ∀ t, 0 ≤ cost t)
    {t ε : ℝ} (ht : 0 < t) (herr : error t ≤ ε) :
    complexityOf cost error ε ≤ cost t := by
  unfold complexityOf
  refine ciInf_le (f := fun s : {u : ℝ // 0 < u ∧ error u ≤ ε} => cost s.1) ?_
    ⟨t, ht, herr⟩
  refine ⟨0, ?_⟩
  rintro _ ⟨s, rfl⟩
  exact hcost s.1

def queryExponent (γ : ℝ) : ℝ := -1 / (1 + γ)

def bitExponent (γ : ℝ) : ℝ := -1 / (1 + γ)

def bitLogExponent (γ : ℝ) : ℝ := 1 / (1 + γ)

def coinExponent (γ : ℝ) : ℝ := -2 / (1 + 2 * γ)

def coinLogExponent (γ : ℝ) : ℝ := 1 / (1 + 2 * γ)

def IsThetaQuantumQuery (γ c C ε₀ : ℝ) (comp : ℝ → ℝ) : Prop :=
  0 < c ∧ 0 < C ∧
    ∀ ε ∈ Set.Ioc (0 : ℝ) ε₀,
      c * ε ^ queryExponent γ ≤ comp ε ∧ comp ε ≤ C * ε ^ queryExponent γ

def IsQuantumBitUpper (γ C : ℝ) (comp : ℝ → ℝ) : Prop :=
  ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
    comp ε ≤ C * ε ^ bitExponent γ * (Real.log ε⁻¹) ^ bitLogExponent γ

def IsCoinUpper (γ C : ℝ) (comp : ℝ → ℝ) : Prop :=
  ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
    comp ε ≤ C * ε ^ coinExponent γ * (Real.log ε⁻¹) ^ coinLogExponent γ

def BitSelection (γ c : ℝ) : Prop :=
  ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ t : ℝ,
    0 < t ∧ t ≤ 1 ∧ 1 ≤ Real.log t⁻¹ ∧
      c * t ^ (1 + γ) * (Real.log t⁻¹) ^ (-γ) = ε ∧ ε ≤ 1 / c

def CoinSelection (γ c : ℝ) : Prop :=
  ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), ∃ t : ℝ,
    0 < t ∧ t ≤ 1 ∧ 1 ≤ Real.log t⁻¹ ∧
      c * t ^ (1 + 2 * γ) * (Real.log t⁻¹) ^ (-γ) = ε ∧ ε ≤ 1 / c

theorem sel_exists (s γ c : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hc : 0 < c) :
    ∀ ε ∈ Set.Ioc (0 : ℝ) (c * Real.exp (-s)), ∃ t : ℝ,
      0 < t ∧ t ≤ 1 ∧ 1 ≤ Real.log t⁻¹ ∧
        c * t ^ s * (Real.log t⁻¹) ^ (-γ) = ε := by
  intro ε hε
  obtain ⟨hε0, hεc⟩ := hε
  set tmax : ℝ := Real.exp (-1) with htmaxdef
  have htmax0 : 0 < tmax := Real.exp_pos _
  have htmax1 : tmax ≤ 1 := by rw [htmaxdef]; exact Real.exp_le_one_iff.mpr (by norm_num)
  have hLmax : Real.log tmax⁻¹ = 1 := by
    rw [htmaxdef, Real.exp_neg, inv_inv, Real.log_exp]
  have htmaxpow : tmax ^ s = Real.exp (-s) := by
    rw [htmaxdef, Real.rpow_def_of_pos (Real.exp_pos (-1)), Real.log_exp]; ring_nf
  set δ : ℝ := (ε / (2 * c)) ^ (1 / s) with hδdef
  have hx : 0 < ε / (2 * c) := by positivity
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hx _
  have hδs : δ ^ s = ε / (2 * c) := by
    rw [hδdef, ← Real.rpow_mul (le_of_lt hx)]
    have h1 : (1 / s) * s = 1 := by field_simp
    rw [h1, Real.rpow_one]
  have hδmax : δ ≤ tmax := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : tmax ^ s < δ ^ s := Real.rpow_lt_rpow (le_of_lt htmax0) hgt hs
    rw [htmaxpow, hδs] at h1
    have h2 : ε / (2 * c) ≤ Real.exp (-s) / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hεc]
    linarith [Real.exp_pos (-s)]
  set F : ℝ → ℝ := fun t => c * t ^ s * (Real.log t⁻¹) ^ (-γ) with hFdef
  have hlog1 : ∀ x ∈ Set.Icc δ tmax, 1 ≤ Real.log x⁻¹ := by
    intro x hxmem
    have hx0 : 0 < x := lt_of_lt_of_le hδ0 hxmem.1
    have hinv : tmax⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hxmem.2
    calc (1:ℝ) = Real.log tmax⁻¹ := hLmax.symm
      _ ≤ Real.log x⁻¹ := Real.log_le_log (inv_pos.mpr htmax0) hinv
  have hcont : ContinuousOn F (Set.Icc δ tmax) := by
    have hbase : ContinuousOn (fun t : ℝ => c * t ^ s) (Set.Icc δ tmax) :=
      continuousOn_const.mul
        (continuousOn_id.rpow_const (fun x _ => Or.inr (le_of_lt hs)))
    have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc δ tmax) :=
      continuousOn_inv₀.mono (fun x hxmem => ne_of_gt (lt_of_lt_of_le hδ0 hxmem.1))
    have hlogc : ContinuousOn (fun t : ℝ => Real.log t⁻¹) (Set.Icc δ tmax) :=
      Real.continuousOn_log.comp hinv
        (fun x hxmem => inv_ne_zero (ne_of_gt (lt_of_lt_of_le hδ0 hxmem.1)))
    have hlogp : ContinuousOn (fun t : ℝ => (Real.log t⁻¹) ^ (-γ)) (Set.Icc δ tmax) :=
      hlogc.rpow_const (fun x hxmem =>
        Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (hlog1 x hxmem))))
    exact hbase.mul hlogp
  have hFδ : F δ ≤ ε / 2 := by
    have hp : (Real.log δ⁻¹) ^ (-γ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hlog1 δ ⟨le_refl _, hδmax⟩) (by linarith)
    calc F δ = c * δ ^ s * (Real.log δ⁻¹) ^ (-γ) := rfl
      _ ≤ c * δ ^ s * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = c * (ε / (2 * c)) := by rw [hδs]; ring
      _ = ε / 2 := by field_simp
  have hFtmax : ε ≤ F tmax := by
    have hLm : (Real.log tmax⁻¹) ^ (-γ) = 1 := by rw [hLmax, Real.one_rpow]
    calc ε ≤ c * Real.exp (-s) := hεc
      _ = c * tmax ^ s := by rw [htmaxpow]
      _ = F tmax := by
            show c * tmax ^ s = c * tmax ^ s * (Real.log tmax⁻¹) ^ (-γ)
            simp only [hLm, mul_one]
  have hεmem : ε ∈ Set.Icc (F δ) (F tmax) := ⟨le_trans hFδ (by linarith), hFtmax⟩
  obtain ⟨t, htI, hFt⟩ := intermediate_value_Icc hδmax hcont hεmem
  refine ⟨t, lt_of_lt_of_le hδ0 htI.1, le_trans htI.2 htmax1, ?_, ?_⟩
  · exact hlog1 t htI
  · simpa only [hFdef] using hFt

theorem bit_sel_exists (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∀ ε ∈ Set.Ioc (0 : ℝ) (c * Real.exp (-(1 + γ))), ∃ t : ℝ,
      0 < t ∧ t ≤ 1 ∧ 1 ≤ Real.log t⁻¹ ∧
        c * t ^ (1 + γ) * (Real.log t⁻¹) ^ (-γ) = ε :=
  fun ε hε => sel_exists (1 + γ) γ c (by linarith) hγ hc ε hε

theorem coin_sel_exists (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∀ ε ∈ Set.Ioc (0 : ℝ) (c * Real.exp (-(1 + 2 * γ))), ∃ t : ℝ,
      0 < t ∧ t ≤ 1 ∧ 1 ≤ Real.log t⁻¹ ∧
        c * t ^ (1 + 2 * γ) * (Real.log t⁻¹) ^ (-γ) = ε :=
  fun ε hε => sel_exists (1 + 2 * γ) γ c (by linarith) hγ hc ε hε

end Qatlib.Papers.QIntegration00.MainResults.Defs
