/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.SourceMeanSector

set_option backward.isDefEq.respectTransparency false

/-!
# Original bound-program projection and finite mean preprocessing

The original physical bound values are rounded upwards to the same fixed
eight-bit dyadic grid as the producer. The zero-first-bound branch is taken
before requesting the second bound. These functional executions do not yet
model the running time of the supplied bound program.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.RationalFlow
open Qatlib.Concepts.EffectiveGauge.HopfAtlas

/-- Definition of source Mean Compressed Bound in the Rational Flow construction. -/
def sourceMeanCompressedBound (m : ℚ) : ℚ := (Int.ceil (256*m) : ℚ)/256

/-- The actual frame derives a zero second bound on its zero-first branch.
The cached first value is supplied here, so evaluating this helper need not
request bound 1 again. -/
def sourceMeanEffectiveSecondBound (m1 : ℚ) (bounds : ℕ → ℚ) : ℚ :=
  if m1=0 then 0 else sourceMeanCompressedBound (bounds 2)

/-- Original `sourceMeanCompressedBound_encloses` guarantee for the `SourceMeanBounds` construction; the complete source hypotheses are retained. -/
theorem sourceMeanCompressedBound_encloses (m : ℚ) :
    m ≤ sourceMeanCompressedBound m ∧ sourceMeanCompressedBound m < m+1/256 := by
  have hlo := Int.le_ceil (256*m)
  have hhi := Int.ceil_lt_add_one (256*m)
  dsimp only [sourceMeanCompressedBound]
  constructor <;> linarith

/-- Original `sourceMeanCompressedBound_nonneg` guarantee for the `SourceMeanBounds` construction; the complete source hypotheses are retained. -/
theorem sourceMeanCompressedBound_nonneg (m : ℚ) (hm : 0 ≤ m) :
    0 ≤ sourceMeanCompressedBound m := hm.trans (sourceMeanCompressedBound_encloses m).1

/-- The actual original-bound callback, evaluated in the prescribed order. -/
def sourceMeanBoundsPhysicalExecution (source : RationalJetSource) (bounds : ℕ → ℚ)
    (tolerance : ℚ) : Option (Fin 3 → RationalMeanInterval) :=
  let m1 := sourceMeanCompressedBound (bounds 1)
  if m1=0 then some (fun _ => ⟨0,0⟩) else
    let m2 := sourceMeanCompressedBound (bounds 2)
    sourceMeanPhysicalExecution source m1 m2 tolerance

/-- Definition of source Mean Bounds Sector Execution in the Rational Flow construction. -/
def sourceMeanBoundsSectorExecution (source : RationalJetSource) (bounds : ℕ → ℚ) :
    Option SourceMeanSectorResult :=
  (sourceMeanBoundsPhysicalExecution source bounds (1/64)).map (fun intervals =>
    ⟨intervals,selectMeanSector (fun j => (intervals j).midpoint) (fun j => (intervals j).radius)⟩)

/-- Extensional numerical equality does not change the zero branch's actual
callback dependencies. In particular the program's first branch reads no bound 2. -/
theorem sourceMeanBoundsPhysicalExecution_eq (source : RationalJetSource) (bounds : ℕ → ℚ)
    (tolerance : ℚ) :
    sourceMeanBoundsPhysicalExecution source bounds tolerance=
      sourceMeanPhysicalExecution source (sourceMeanCompressedBound (bounds 1))
        (sourceMeanCompressedBound (bounds 2)) tolerance := by
  dsimp only [sourceMeanBoundsPhysicalExecution]
  split_ifs with hz
  · rw [sourceMeanPhysicalExecution,if_pos hz]
  · rfl

/-- A numerical comparison using the raw second bound. This equality of
returned mean packets does not identify differently seeded reference fields. -/
theorem sourceMeanBoundsSectorExecution_eq (source : RationalJetSource) (bounds : ℕ → ℚ) :
    sourceMeanBoundsSectorExecution source bounds=
      sourceMeanSectorExecution source (sourceMeanCompressedBound (bounds 1))
        (sourceMeanCompressedBound (bounds 2)) := by
  rw [sourceMeanBoundsSectorExecution,sourceMeanBoundsPhysicalExecution_eq]
  rfl

/-- Numerical equality with the effective frame parameters. This is an
execution equality, not an equality of differently seeded reference fields. -/
theorem sourceMeanBoundsSectorExecution_effective_eq (source : RationalJetSource) (bounds : ℕ → ℚ) :
    sourceMeanBoundsSectorExecution source bounds=
      sourceMeanSectorExecution source (sourceMeanCompressedBound (bounds 1))
        (sourceMeanEffectiveSecondBound (sourceMeanCompressedBound (bounds 1)) bounds) := by
  rw [sourceMeanBoundsSectorExecution_eq]
  by_cases h : sourceMeanCompressedBound (bounds 1)=0
  · simp only [h,sourceMeanEffectiveSecondBound,ite_true,sourceMeanSectorExecution_zero]
  · simp only [sourceMeanEffectiveSecondBound,if_neg h]

/-- Original `sourceMeanBoundsPhysicalExecution_zero` guarantee for the `SourceMeanBounds` construction; the complete source hypotheses are retained. -/
theorem sourceMeanBoundsPhysicalExecution_zero (source : RationalJetSource) (bounds : ℕ → ℚ)
    (hz : sourceMeanCompressedBound (bounds 1)=0) (tolerance : ℚ) :
    sourceMeanBoundsPhysicalExecution source bounds tolerance=some (fun _ => ⟨0,0⟩) := by
  simp only [sourceMeanBoundsPhysicalExecution,hz,ite_true]

noncomputable section
open Set
open scoped ContDiff

/-- Original `sourceMeanCompressedBounds_valid` guarantee for the `SourceMeanBounds` construction; the complete source hypotheses are retained. -/
theorem sourceMeanCompressedBounds_valid (v : SpatialPoint → SpatialPoint) (bounds : ℕ → ℚ)
    (hb : SourceAllRescalingBounds v (bounds 1 : ℝ) (bounds 2 : ℝ)) :
    SourceAllRescalingBounds v (sourceMeanCompressedBound (bounds 1) : ℝ)
      (sourceMeanCompressedBound (bounds 2) : ℝ) := by
  have h1 : (bounds 1 : ℝ) ≤ sourceMeanCompressedBound (bounds 1) :=
    (Rat.cast_le (K := ℝ)).mpr (sourceMeanCompressedBound_encloses (bounds 1)).1
  have h2 : (bounds 2 : ℝ) ≤ sourceMeanCompressedBound (bounds 2) :=
    (Rat.cast_le (K := ℝ)).mpr (sourceMeanCompressedBound_encloses (bounds 2)).1
  exact ⟨fun x hx i => (hb.1 x hx i).trans h1,fun i x hx j => (hb.2 i x hx j).trans h2⟩

/-- The same bound callback supplies the physical all-direction moduli;
neither their normalized versions nor a reference mean are extra inputs. -/
theorem sourceMeanBoundsSectorExecution_correct (v : SpatialPoint → SpatialPoint)
    (hv : ContDiff ℝ ∞ v) (hu : ∀ x, ‖v x‖=1) (hp : IsPeriodicField v)
    (source : RationalJetSource) (hs : OriginalFirstJetAccurate v source)
    (bounds : ℕ → ℚ) (hb1 : 0 ≤ bounds 1) (hb2 : 0 ≤ bounds 2)
    (hb : SourceAllRescalingBounds v (bounds 1 : ℝ) (bounds 2 : ℝ))
    (eta : ℚ) (he : 0<eta) (B : Set SpatialPoint)
    (hB : ∀ w ∈ B, InFundamentalCube w) (mu : ℝ) (hm : 0<mu)
    (hg : ∀ w ∈ B, ∀ a, OnCubeBoundary a → mu ≤ ‖w-a‖)
    (hoff : ∀ a b, InFundamentalCube a → InFundamentalCube b → a ∉ B → b ∉ B → v a=v b)
    (hmargin : 7*(eta : ℝ) ≤ mu/2) :
    let mean := fun j => physicalCubeMean (fun x => connection
      (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source hs)
        (sourceMeanCompressedBound (bounds 1))
        (sourceMeanEffectiveSecondBound (sourceMeanCompressedBound (bounds 1)) bounds) eta) x j)
    ∃ result, sourceMeanBoundsSectorExecution source bounds=some result ∧
      SourceMeanSectorCertificate mean result := by
  obtain ⟨result,hex,hcert⟩ := sourceMeanSectorExecution_correct v hv hu hp source hs
    (sourceMeanCompressedBound (bounds 1)) (sourceMeanCompressedBound (bounds 2)) eta
    (sourceMeanCompressedBound_nonneg _ hb1) (sourceMeanCompressedBound_nonneg _ hb2) he
    (sourceMeanCompressedBounds_valid v bounds hb) B hB mu hm hg hoff hmargin
  refine ⟨result,?_,?_⟩
  · rw [sourceMeanBoundsSectorExecution_eq]
    exact hex
  · have hmean : (fun j => physicalCubeMean (fun x => connection
        (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
          (OriginalFirstJetAccurate.legacy v source hs)
          (sourceMeanCompressedBound (bounds 1))
          (sourceMeanEffectiveSecondBound (sourceMeanCompressedBound (bounds 1)) bounds) eta) x j))=
        (fun j => physicalCubeMean (fun x => connection
          (sourcePeriodicReference v hv hu (originalFirstJetPair source 0)
            (OriginalFirstJetAccurate.legacy v source hs)
            (sourceMeanCompressedBound (bounds 1)) (sourceMeanCompressedBound (bounds 2)) eta) x j)) := by
      funext j
      rw [sourcePeriodicReference_unit_mean v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source hs) (sourceMeanCompressedBound (bounds 1))
        (sourceMeanEffectiveSecondBound (sourceMeanCompressedBound (bounds 1)) bounds) eta
        he B hB mu hm hg hoff hmargin (sourceMeanMomentAxis j) j (sourceMeanMomentAxis_ne j),
        sourcePeriodicReference_unit_mean v hv hu hp (originalFirstJetPair source 0)
        (OriginalFirstJetAccurate.legacy v source hs) (sourceMeanCompressedBound (bounds 1))
        (sourceMeanCompressedBound (bounds 2)) eta
        he B hB mu hm hg hoff hmargin (sourceMeanMomentAxis j) j (sourceMeanMomentAxis_ne j)]
    rw [hmean]
    exact hcert

end
end Qatlib.Concepts.EffectiveGauge.RationalFlow
