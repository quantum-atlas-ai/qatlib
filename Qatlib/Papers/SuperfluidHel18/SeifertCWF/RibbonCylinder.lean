/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.NormalRibbon
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# The embedded cylinder of a narrow closed ribbon

[Kedia2018SuperfluidHelicity], Section IV and Eq. (5),
[DOI](https://doi.org/10.1103/PhysRevFluids.3.104702).
The normal strip descends to the actual parameter circle. Restricting
the width to a sufficiently small closed interval gives a topological
embedding of the compact cylinder with its centerline at width zero.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open Qatlib.Papers.KnottedLight08.HopfField (dot3)
open Set Topology
open scoped Real

/-- The normal strip written on the actual additive parameter circle
and the real signed width. -/
def normalRibbonCylinder (γ N : ℝ → Fin 3 → ℝ)
    (p : AddCircle (2 * π) × ℝ) : Fin 3 → ℝ := by
  letI : Fact (0 < (2 * π : ℝ)) := ⟨Real.two_pi_pos⟩
  exact AddCircle.liftIco (2 * π) 0 γ p.1 + p.2 • AddCircle.liftIco (2 * π) 0 N p.1

/-- On the half-open period the cylinder map evaluates to its genuine
normal offset in real coordinates. -/
theorem normalRibbonCylinder_apply_coe (γ N : ℝ → Fin 3 → ℝ) {s : ℝ}
    (hs : s ∈ Ico 0 (2 * π)) (a : ℝ) :
    normalRibbonCylinder γ N ((s : AddCircle (2 * π)), a) = normalRibbonPoint γ N a s := by
  let _ : Fact (0 < (2 * π : ℝ)) := ⟨Real.two_pi_pos⟩
  unfold normalRibbonCylinder normalRibbonPoint
  rw [AddCircle.liftIco_zero_coe_apply hs, AddCircle.liftIco_zero_coe_apply hs]

/-- The cylinder map is continuous because its two periodic components
descend continuously through the identified endpoints. -/
theorem continuous_normalRibbonCylinder {γ N : ℝ → Fin 3 → ℝ}
    (hγ : Continuous γ) (hN : Continuous N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π)) :
    Continuous (normalRibbonCylinder γ N) := by
  let _ : Fact (0 < (2 * π : ℝ)) := ⟨Real.two_pi_pos⟩
  have hγ' : Continuous (AddCircle.liftIco (2 * π) 0 γ) :=
    AddCircle.liftIco_continuous (hpγ 0).symm hγ.continuousOn
  have hN' : Continuous (AddCircle.liftIco (2 * π) 0 N) :=
    AddCircle.liftIco_continuous (hpN 0).symm hN.continuousOn
  exact (hγ'.comp continuous_fst).add (continuous_snd.smul (hN'.comp continuous_fst))

/-- A regular simple closed curve with a continuously differentiable
periodic nonvanishing normal admits an embedded compact ribbon. The
topology of the image is that of the parameter circle times the
closed width interval. -/
theorem exists_closedEmbedding_normalRibbonCylinder {γ N : ℝ → Fin 3 → ℝ}
    (hγ : ContDiff ℝ 2 γ) (hN : ContDiff ℝ 1 N)
    (hpγ : Function.Periodic γ (2 * π)) (hpN : Function.Periodic N (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hreg : ∀ s, deriv γ s ≠ 0)
    (hNnz : ∀ s, N s ≠ 0) (horth : ∀ s, dot3 (deriv γ s) (N s) = 0) :
    ∃ w : ℝ, 0 < w ∧ IsClosedEmbedding
      (fun p : AddCircle (2 * π) × Icc (-w) w =>
        normalRibbonCylinder γ N (p.1, (p.2 : ℝ))) := by
  let _ : Fact (0 < (2 * π : ℝ)) := ⟨Real.two_pi_pos⟩
  obtain ⟨ε, hε, hstrip⟩ := exists_normalRibbon_injective hγ hN hpγ hpN hinj hreg hNnz horth
  let w := ε / 2
  have hw : 0 < w := by dsimp only [w]; positivity
  have hwε : w < ε := by dsimp only [w]; linarith
  refine ⟨w, hw, ?_⟩
  have hcont : Continuous (fun p : AddCircle (2 * π) × Icc (-w) w =>
      normalRibbonCylinder γ N (p.1, (p.2 : ℝ))) :=
    (continuous_normalRibbonCylinder hγ.continuous hN.continuous hpγ hpN).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  apply hcont.isClosedEmbedding
  intro p q he
  obtain ⟨s, hs, hs'⟩ := AddCircle.eq_coe_Ico p.1
  obtain ⟨t, ht, ht'⟩ := AddCircle.eq_coe_Ico q.1
  have hpw : |(p.2 : ℝ)| < ε := (abs_le.mpr p.2.property).trans_lt hwε
  have hqw : |(q.2 : ℝ)| < ε := (abs_le.mpr q.2.property).trans_lt hwε
  have he' : normalRibbonPoint γ N (p.2 : ℝ) s = normalRibbonPoint γ N (q.2 : ℝ) t := by
    rw [← normalRibbonCylinder_apply_coe γ N hs, ← normalRibbonCylinder_apply_coe γ N ht, hs', ht']
    exact he
  obtain ⟨hbase, hwidth⟩ := hstrip _ _ s t hpw hqw he'
  have hst := hinj hs ht hbase
  exact Prod.ext (hs'.symm.trans (hst ▸ ht')) (Subtype.ext hwidth)

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
