/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CollarGluing

@[expose] public section

/-!
# Periodic extension of a field constant on a positive cube collar

The floor projection is used only to define the exact periodic field.
Smoothness is proved locally: away from seams it is an affine translate;
at a seam the output is locally constant, including edges and corners.
No continuity or computability of the floor projection is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Quaternion RealInnerProductSpace Topology ContDiff
open Set Metric
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of wrap Coordinate in the Hopf Atlas construction. -/
def wrapCoordinate (x : ℝ) : ℝ := x-physicalPeriod*(⌊x/physicalPeriod⌋ : ℝ)

/-- Wrapping a real coordinate puts it in the half-open interval from zero to the physical
period. -/
theorem wrapCoordinate_bounds (x : ℝ) : 0 ≤ wrapCoordinate x ∧ wrapCoordinate x < physicalPeriod := by
  have hlo := (le_div_iff₀ physicalPeriod_pos).mp (Int.floor_le (x/physicalPeriod))
  have hhi := (div_lt_iff₀ physicalPeriod_pos).mp (Int.lt_floor_add_one (x/physicalPeriod))
  dsimp [wrapCoordinate]
  constructor <;> nlinarith

/-- Wrapping is invariant under adding an integer multiple of the physical period. -/
theorem wrapCoordinate_add_period (x : ℝ) (n : ℤ) :
    wrapCoordinate (x+physicalPeriod*(n : ℝ))=wrapCoordinate x := by
  have hd : (x+physicalPeriod*(n : ℝ))/physicalPeriod=x/physicalPeriod+(n : ℝ) := by
    field_simp [physicalPeriod_pos.ne']
  unfold wrapCoordinate
  rw [hd,Int.floor_add_intCast]
  push_cast
  ring

/-- Definition of wrap Point in the Hopf Atlas construction. -/
def wrapPoint (x : SpatialPoint) : SpatialPoint := WithLp.toLp 2 (fun j => wrapCoordinate (x j))

/-- Wrapping each coordinate puts a spatial point in the fundamental cube. -/
theorem wrapPoint_cube (x : SpatialPoint) : InFundamentalCube (wrapPoint x) :=
  fun j => ⟨(wrapCoordinate_bounds (x j)).1,(wrapCoordinate_bounds (x j)).2.le⟩

/-- A wrapped point differs from the input by the lattice shift whose `j`-th integer is the
negative floor of `x j / physicalPeriod`. -/
theorem wrapPoint_shift (x : SpatialPoint) :
    wrapPoint x=x+latticeShift (fun j => -⌊x j/physicalPeriod⌋) := by
  ext j
  change x j-physicalPeriod*(⌊x j/physicalPeriod⌋ : ℝ)=
    x j+physicalPeriod*((-⌊x j/physicalPeriod⌋ : ℤ) : ℝ)
  push_cast
  ring

/-- The coordinatewise wrapping map is invariant under lattice shifts. -/
theorem wrapPoint_periodic : IsPeriodicField wrapPoint := by
  intro x n
  ext j
  exact wrapCoordinate_add_period (x j) (n j)

/-- Definition of periodic Extension in the Hopf Atlas construction. -/
def periodicExtension (f : QuaternionField) (x : SpatialPoint) : ℍ := f (wrapPoint x)

/-- Composing any quaternion field with coordinatewise wrapping makes it periodic. -/
theorem periodicExtension_periodic (f : QuaternionField) : IsPeriodicField (periodicExtension f) := by
  intro x n
  exact congrArg f (wrapPoint_periodic x n)

/-- Wrapping the spatial origin fixes it. -/
@[simp] theorem wrapPoint_zero : wrapPoint 0=0 := by
  ext j
  simp [wrapPoint,wrapCoordinate]

/-- The exact extension also agrees at upper faces, where wrap sends a
coordinate from L to 0; both values are the same collar constant. -/
theorem periodicExtension_eq_on_cube (f : QuaternionField) (delta : ℝ) (hd : 0<delta) (q₀ : ℍ)
    (hc : HasConstantCollar f delta q₀) (x : SpatialPoint) (hx : InFundamentalCube x) :
    periodicExtension f x=f x := by
  by_cases ht : ∃ j, x j=physicalPeriod
  · rcases ht with ⟨j,hj⟩
    have hfx : f x=q₀ := hc x hx ⟨j,Or.inr (by rw [hj]; linarith)⟩
    have hwj : wrapPoint x j=0 := by
      change wrapCoordinate (x j)=0
      rw [hj]
      simp [wrapCoordinate,physicalPeriod_pos.ne']
    have hfw : f (wrapPoint x)=q₀ := hc _ (wrapPoint_cube x)
      ⟨j,Or.inl (by rw [hwj]; exact hd.le)⟩
    exact hfw.trans hfx.symm
  · have hw : wrapPoint x=x := by
      ext j
      have hj : x j<physicalPeriod := lt_of_le_of_ne (hx j).2 (fun h => ht ⟨j,h⟩)
      have hf : ⌊x j/physicalPeriod⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr
        ⟨div_nonneg (hx j).1 physicalPeriod_pos.le,(div_lt_one physicalPeriod_pos).mpr hj⟩
      change x j-physicalPeriod*(⌊x j/physicalPeriod⌋ : ℝ)=x j
      simp only [hf,Int.cast_zero,mul_zero,sub_zero]
    exact congrArg f hw

/-- If the wrapped coordinate is strictly positive, the period index stays equal to the index at
`x` in a neighbourhood of `x`. -/
private theorem floor_eventual {x : ℝ} (hx : 0<wrapCoordinate x) :
    ∀ᶠ y in 𝓝 x, ⌊y/physicalPeriod⌋=⌊x/physicalPeriod⌋ := by
  have hlo : physicalPeriod*(⌊x/physicalPeriod⌋ : ℝ)<x := by dsimp [wrapCoordinate] at hx; linarith
  have hhi : x<physicalPeriod*((⌊x/physicalPeriod⌋ : ℝ)+1) := by
    have h := (div_lt_iff₀ physicalPeriod_pos).mp (Int.lt_floor_add_one (x/physicalPeriod))
    nlinarith
  filter_upwards [Ioi_mem_nhds hlo,Iio_mem_nhds hhi] with y hylo hyhi
  change physicalPeriod*(⌊x/physicalPeriod⌋ : ℝ)<y at hylo
  change y<physicalPeriod*((⌊x/physicalPeriod⌋ : ℝ)+1) at hyhi
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ physicalPeriod_pos).mpr
    nlinarith
  · apply (div_lt_iff₀ physicalPeriod_pos).mpr
    nlinarith

/-- Within distance `delta` of a wrapping seam, the wrapped coordinate lies within `delta` of an
endpoint, for `0 < delta ≤ physicalPeriod / 8`. -/
private theorem wrap_near_seam (delta x y : ℝ) (hd : 0<delta) (hL : delta ≤ physicalPeriod/8)
    (hx : wrapCoordinate x=0) (hy : |y-x|<delta) :
    wrapCoordinate y ≤ delta ∨ physicalPeriod-delta ≤ wrapCoordinate y := by
  let n : ℤ := ⌊x/physicalPeriod⌋
  let d := y-x
  have hx' : x=physicalPeriod*(n : ℝ) := by dsimp [wrapCoordinate] at hx; dsimp [n]; linarith
  have hdlo : -delta<d := (abs_lt.mp hy).1
  have hdhi : d<delta := (abs_lt.mp hy).2
  have hsmall : delta<physicalPeriod := by linarith [physicalPeriod_pos]
  have heq : wrapCoordinate y=wrapCoordinate d := by
    have hp : y=d+physicalPeriod*(n : ℝ) := by dsimp [d]; rw [hx']; ring
    rw [hp,wrapCoordinate_add_period]
  rw [heq]
  by_cases hpos : 0 ≤ d
  · have hf : ⌊d/physicalPeriod⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr
      ⟨div_nonneg hpos physicalPeriod_pos.le,(div_lt_one physicalPeriod_pos).mpr (hdhi.trans hsmall)⟩
    left
    simpa only [wrapCoordinate,hf,Int.cast_zero,mul_zero,sub_zero] using hdhi.le
  · have hf : ⌊d/physicalPeriod⌋=(-1 : ℤ) := by
      apply Int.floor_eq_iff.mpr
      constructor
      · apply (le_div_iff₀ physicalPeriod_pos).mpr
        norm_num
        linarith
      · have hn : d/physicalPeriod<0 := div_neg_of_neg_of_pos (lt_of_not_ge hpos) physicalPeriod_pos
        simpa using hn
    right
    simp only [wrapCoordinate,hf,Int.cast_neg,Int.cast_one,mul_neg,mul_one,sub_neg_eq_add]
    linarith

/-- At a seam the extension is constant on a full ambient neighbourhood,
including both sides of every face, edge and corner. -/
theorem periodicExtension_eventually_constant_of_seam (f : QuaternionField)
    (delta : ℝ) (hd : 0<delta) (hL : delta ≤ physicalPeriod/8) (q₀ : ℍ)
    (hc : HasConstantCollar f delta q₀) (x : SpatialPoint)
    (hx : ∃ j, wrapCoordinate (x j)=0) :
    periodicExtension f =ᶠ[𝓝 x] fun _ => q₀ := by
  rcases hx with ⟨j,hj⟩
  have hcoord : Continuous (fun y : SpatialPoint => |y j-x j|) :=
    ((EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).continuous.sub continuous_const).abs
  have hnear : ∀ᶠ y in 𝓝 x, |y j-x j|<delta := by
    exact hcoord.continuousAt.eventually_lt continuousAt_const (by simpa using hd)
  filter_upwards [hnear] with y hy
  exact hc (wrapPoint y) (wrapPoint_cube y)
    ⟨j,wrap_near_seam delta (x j) (y j) hd hL hj hy⟩

/-- Wrapping preserves smoothness of a quaternion field constant on a fundamental-cube collar of
width `delta` with `0 < delta ≤ physicalPeriod / 8`. -/
theorem contDiff_periodicExtension (f : QuaternionField) (hf : ContDiff ℝ ∞ f)
    (delta : ℝ) (hd : 0<delta) (hL : delta ≤ physicalPeriod/8) (q₀ : ℍ)
    (hc : HasConstantCollar f delta q₀) : ContDiff ℝ ∞ (periodicExtension f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hseam : ∃ j, wrapCoordinate (x j)=0
  · rcases hseam with ⟨j,hj⟩
    have hcoord : Continuous (fun y : SpatialPoint => |y j-x j|) :=
      ((EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).continuous.sub continuous_const).abs
    have hnear : ∀ᶠ y in 𝓝 x, |y j-x j|<delta := by
      exact hcoord.continuousAt.eventually_lt continuousAt_const (by simpa using hd)
    have heq : periodicExtension f =ᶠ[𝓝 x] fun _ => q₀ := by
      filter_upwards [hnear] with y hy
      exact hc (wrapPoint y) (wrapPoint_cube y) ⟨j,wrap_near_seam delta (x j) (y j) hd hL hj hy⟩
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hn : ∀ j, 0<wrapCoordinate (x j) := by
      intro j
      exact lt_of_le_of_ne (wrapCoordinate_bounds (x j)).1 (Ne.symm (fun hj => hseam ⟨j,hj⟩))
    have hj : ∀ j, ∀ᶠ y in 𝓝 x, ⌊y j/physicalPeriod⌋=⌊x j/physicalPeriod⌋ := by
      intro j
      exact (EuclideanSpace.proj j : SpatialPoint →L[ℝ] ℝ).continuous.continuousAt.eventually (floor_eventual (hn j))
    have hall : ∀ᶠ y in 𝓝 x, ∀ j, ⌊y j/physicalPeriod⌋=⌊x j/physicalPeriod⌋ := by
      filter_upwards [hj 0,hj 1,hj 2] with y h0 h1 h2
      intro j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
    let n : Fin 3 → ℤ := fun j => -⌊x j/physicalPeriod⌋
    have heq : periodicExtension f =ᶠ[𝓝 x] fun y => f (y+latticeShift n) := by
      filter_upwards [hall] with y hy
      apply congrArg f
      ext j
      change y j-physicalPeriod*(⌊y j/physicalPeriod⌋ : ℝ)=y j+physicalPeriod*((-⌊x j/physicalPeriod⌋ : ℤ) : ℝ)
      rw [hy j]
      push_cast
      ring
    exact (hf.comp (contDiff_id.add contDiff_const)).contDiffAt.congr_of_eventuallyEq heq

/-- If a field smoothly lifts a periodic spin with unit norm and is constant on a
fundamental-cube collar of width `delta` with `0 < delta ≤ physicalPeriod / 8`, its periodic
extension is again a smooth unit lift of the same spin. -/
theorem periodicExtension_isSmoothUnitLift (s f : QuaternionField) (hp : IsPeriodicField s)
    (hf : IsSmoothUnitLift s f) (delta : ℝ) (hd : 0<delta) (hL : delta ≤ physicalPeriod/8)
    (q₀ : ℍ) (hc : HasConstantCollar f delta q₀) : IsSmoothUnitLift s (periodicExtension f) := by
  refine ⟨contDiff_periodicExtension f hf.1 delta hd hL q₀ hc,fun x => ⟨(hf.2 (wrapPoint x)).1,?_⟩⟩
  exact (hf.2 (wrapPoint x)).2.trans (by rw [wrapPoint_shift,hp])

/-- Definition of periodic Reference in the Hopf Atlas construction. -/
def periodicReference (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q₀ : ℍ) (h₀ : ‖q₀‖=1) (eta : ℝ) : QuaternionField :=
  periodicExtension (correctedReference v hv q₀ h₀ eta)

/-- For a smooth unit vector source with periodic spin constant on a positive-width collar, a
unit seed lifting the collar spin gives a periodic smooth unit reference lift. -/
theorem periodicReference_spec (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) :
    IsPeriodicField (periodicReference v hv q₀ h₀ eta) ∧
      IsSmoothUnitLift (sourceQuaternion v) (periodicReference v hv q₀ h₀ eta) := by
  exact ⟨periodicExtension_periodic _,periodicExtension_isSmoothUnitLift _ _ hp
    (correctedReference_isSmoothUnitLift v hv hu q₀ h₀ hp eta he sc hc hi)
    (gluingWidth eta) (gluingWidth_pos he) (gluingWidth_le_period eta) q₀
    (correctedReference_collar v hv hu q₀ h₀ hp eta he sc hc hi)⟩

/-- For a smooth unit vector source with periodic spin constant on a positive-width collar and a
unit seed over that spin value, the periodic reference is equal to the seed on the collar of
gluing width. -/
theorem periodicReference_collar (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) :
    HasConstantCollar (periodicReference v hv q₀ h₀ eta) (gluingWidth eta) q₀ := by
  have hr := correctedReference_collar v hv hu q₀ h₀ hp eta he sc hc hi
  intro x hx hb
  rw [show periodicReference v hv q₀ h₀ eta x=periodicExtension (correctedReference v hv q₀ h₀ eta) x from rfl,
    periodicExtension_eq_on_cube _ _ (gluingWidth_pos he) q₀ hr x hx]
  exact hr x hx hb

/-- For a smooth unit vector source with periodic spin constant on a positive-width collar, the
periodic reference takes its initial unit seed value at the origin when the seed lifts the
collar spin. -/
theorem periodicReference_origin (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (hu : ∀ x, ‖v x‖=1) (q₀ : ℍ) (h₀ : ‖q₀‖=1)
    (hp : IsPeriodicField (sourceQuaternion v)) (eta : ℝ) (he : 0<eta) (sc : ℍ)
    (hc : HasConstantCollar (sourceQuaternion v) eta sc) (hi : hopf q₀=sc) :
    periodicReference v hv q₀ h₀ eta 0=q₀ := by
  exact periodicReference_collar v hv hu q₀ h₀ hp eta he sc hc hi 0
    (fun _ => ⟨le_rfl,physicalPeriod_pos.le⟩) ⟨0,Or.inl (gluingWidth_pos he).le⟩

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
