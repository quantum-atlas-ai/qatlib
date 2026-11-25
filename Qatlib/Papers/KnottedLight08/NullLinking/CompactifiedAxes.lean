/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.ElectricCircles
public import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# Compactification of the zero-label electric and magnetic fibers

The zero labels are unbounded in physical space. Their closures
in the one-point compactification are circles, obtained by extending
the proper embeddings of the physical axes by their common end at
infinity.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnotLight13.TorusFamily (batemanSliceHomeomorph batemanRay)
open Filter Set Topology

/-- A closed embedded real line extends to an embedded copy of the
one-point compactification of the real line. -/
theorem closedEmbedding_onePoint_line {Y : Type*} [TopologicalSpace Y]
    [LocallyCompactSpace Y] [T2Space Y] {f : ℝ → Y} (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (OnePoint.map f) := by
  have hcont : Continuous (OnePoint.map f) :=
    OnePoint.continuous_map hf.continuous (by
      simpa only [coclosedCompact_eq_cocompact] using hf.tendsto_cocompact)
  apply hcont.isClosedEmbedding
  intro x y h
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp only [OnePoint.map_infty, OnePoint.map_some] at h
  · rfl
  · exact (OnePoint.infty_ne_coe _ h).elim
  · exact (OnePoint.coe_ne_infty _ h).elim
  · rw [OnePoint.coe_eq_coe] at h ⊢
    exact hf.injective h

/-- The range of the extended embedding is exactly the closure of the
unbounded physical line in the one-point compactification. -/
theorem closure_coe_image_eq_range_onePoint_line {Y : Type*} [TopologicalSpace Y]
    [LocallyCompactSpace Y] [T2Space Y] {f : ℝ → Y} (hf : IsClosedEmbedding f) :
    closure (((↑) : Y → OnePoint Y) '' Set.range f) = Set.range (OnePoint.map f) := by
  have h := closedEmbedding_onePoint_line hf
  have himage :
      ((↑) : Y → OnePoint Y) '' Set.range f =
        OnePoint.map f '' Set.range ((↑) : ℝ → OnePoint ℝ) := by
    rw [← Set.range_comp, ← Set.range_comp]
    rfl
  rw [himage]
  refine le_antisymm (closure_minimal (Set.image_subset_range _ _) h.isClosed_range) ?_
  rintro _ ⟨p, rfl⟩
  exact image_closure_subset_closure_image h.continuous
    ⟨p, OnePoint.denseRange_coe p, rfl⟩

/-- The compactification of a properly embedded real line is a circle. -/
def lineClosureHomeomorph {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
    [T2Space Y] {f : ℝ → Y} (hf : IsClosedEmbedding f) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closure (((↑) : Y → OnePoint Y) '' Set.range f) :=
  let ec : OnePoint ℝ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  ec.symm.trans ((closedEmbedding_onePoint_line hf).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (closure_coe_image_eq_range_onePoint_line hf).symm))

/-- The magnetic zero fiber is a closed embedded line on each slice. -/
theorem closedEmbedding_reflected_axis (t : ℝ) :
    IsClosedEmbedding (fun s : ℝ => batemanRay (-t) (s, 0, 0)) := by
  let f : ℝ → ℝ × ℝ × ℝ := fun s => (s, 0, 0)
  have h : Function.LeftInverse Prod.fst f := fun _ => rfl
  have hf : IsClosedEmbedding f :=
    h.isClosedEmbedding continuous_fst (continuous_id.prodMk continuous_const)
  exact (batemanSliceHomeomorph (-t)).isClosedEmbedding.comp hf

/-- The actual magnetic zero fiber has circular closure in the
one-point compactification at each time. -/
def compactifiedMagneticZeroFiberHomeo (t : ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closure (((↑) : ℝ × ℝ × ℝ → OnePoint (ℝ × ℝ × ℝ)) '' magneticFiberAt t 0) := by
  rw [magnetic_zero_fiber_eq_reflected_axis]
  exact lineClosureHomeomorph (closedEmbedding_reflected_axis t)

/-- The true electric zero fiber is the inverse quarter-turn of the
actual magnetic zero axis at every time. -/
theorem electric_zero_fiber_eq_reflected_axis (t : ℝ) :
    electricFiberAt t 0 =
      Set.range (fun s : ℝ => electricToMagnetic.symm (batemanRay (-t) (s, 0, 0))) := by
  ext s
  rw [mem_electricFiberAt_iff, mul_zero, magnetic_zero_fiber_eq_reflected_axis]
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, electricToMagnetic.symm_apply_eq.mpr hq⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, electricToMagnetic.symm_apply_eq.mp hq⟩

/-- The actual electric zero fiber has circular closure in the
one-point compactification at each time. -/
def compactifiedElectricZeroFiberHomeo (t : ℝ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      closure (((↑) : ℝ × ℝ × ℝ → OnePoint (ℝ × ℝ × ℝ)) '' electricFiberAt t 0) := by
  rw [electric_zero_fiber_eq_reflected_axis]
  exact lineClosureHomeomorph
    (electricToMagnetic.symm.toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.comp
      (closedEmbedding_reflected_axis t))

end Qatlib.Papers.KnottedLight08.NullLinking
