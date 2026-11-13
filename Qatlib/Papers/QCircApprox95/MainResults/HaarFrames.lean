/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.MetricCore
import Qatlib.Foundations.FrameMeasures.HaarFrames.OuterContent
import Qatlib.Papers.Trainability23.HaarAverages.HaarMeasure
import Mathlib.MeasureTheory.Measure.Comap

/-!
# Haar frame measures and image contents

`prefixColumns` maps a unitary matrix to its first k columns, and `frameProb` is the pushforward
of normalized Haar measure along this map. The module proves concentration on orthonormal frames
and defines image outer contents for both frames and their measurement probability vectors.

`sphereFrameContent` and `densityFrameContent` measure images of sets under these maps; their
evaluation formulas make this construction explicit. See [Knill1995].

## Main statements

* `frameProb_nonorthonormal`: assigns zero measure to nonorthonormal frames.
* `sphereFrameContent_apply`: evaluates frame content through the image of the prefix-column
  map.
* `densityFrameContent_apply`: evaluates probability-vector content through a product simplex
  measure.

## References

* [Knill, 1995][Knill1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Qatlib.Foundations.BornMetrics.FiniteStats
open scoped BigOperators
open Qatlib.Papers.Trainability23.HaarAverages

open Qatlib.Foundations.FrameMeasures.HaarFrames

namespace Qatlib.Papers.QCircApprox95.MainResults

local instance matrixMeasurable (m n : Type*) [Fintype m] [Fintype n] :
    MeasurableSpace (Matrix m n ℂ) := inferInstanceAs (MeasurableSpace (m → n → ℂ))

local instance matrixBorel (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

local instance haarProbability (M : ℕ) : IsProbabilityMeasure (haarUnitaryGroup (Fin M)) :=
  ⟨haarUnitaryGroup_univ _⟩

/-- The first `k` columns of an `M`-dimensional unitary matrix, using the inclusion determined
by `hk : k ≤ M`. -/
def prefixColumns {M k : ℕ} (hk : k ≤ M) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    Fin k → Fin M → ℂ :=
  fun i a => (U : Matrix (Fin M) (Fin M) ℂ) a (Fin.castLE hk i)

/-- Extracting the first `k` columns is a continuous map on the unitary group. -/
theorem prefixColumns_continuous {M k : ℕ} (hk : k ≤ M) :
    Continuous (prefixColumns hk) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro a
  have hrow : Continuous fun r : Fin M → Fin M → ℂ => r a := continuous_apply a
  have hcol : Continuous fun s : Fin M → ℂ => s (Fin.castLE hk i) := continuous_apply _
  exact (hcol.comp hrow).comp continuous_subtype_val

/-- The first `k` columns of a unitary matrix form an orthonormal frame. -/
theorem prefixColumns_orthonormal {M k : ℕ} (hk : k ≤ M)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Orthonormal M k (prefixColumns hk U) := by
  intro i j
  have h := congrArg (fun V : Matrix (Fin M) (Fin M) ℂ =>
    V (Fin.castLE hk i) (Fin.castLE hk j)) (Matrix.mem_unitaryGroup_iff'.mp U.property)
  simpa [prefixColumns, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply, Fin.ext_iff] using h

/-- The pushforward of normalized Haar measure on the unitary group under `prefixColumns hk`. -/
def frameProb (M k : ℕ) (hk : k ≤ M) : Measure (Fin k → Fin M → ℂ) :=
  Measure.map (prefixColumns hk) (haarUnitaryGroup (Fin M))

instance frameProb_isProbability (M k : ℕ) (hk : k ≤ M) :
    IsProbabilityMeasure (frameProb M k hk) :=
  by unfold frameProb; infer_instance

/-- The range of the prefix-column map is compact. -/
theorem prefixColumns_range_compact {M k : ℕ} (hk : k ≤ M) :
    IsCompact (Set.range (prefixColumns hk)) := by
  simpa only [Set.image_univ] using
    (isCompact_univ : IsCompact (Set.univ : Set (Matrix.unitaryGroup (Fin M) ℂ))).image
      (prefixColumns_continuous hk)

/-- The range of `prefixColumns hk` has full `frameProb M k hk` measure. -/
theorem frameProb_range (M k : ℕ) (hk : k ≤ M) :
    frameProb M k hk (Set.range (prefixColumns hk)) = 1 := by
  change (haarUnitaryGroup (Fin M)).map (prefixColumns hk) _ = 1
  calc
    _ = haarUnitaryGroup (Fin M) ((prefixColumns hk) ⁻¹' Set.range (prefixColumns hk)) :=
      Measure.map_apply (μ := haarUnitaryGroup (Fin M))
        (prefixColumns_continuous hk).measurable (prefixColumns_range_compact hk).isClosed.measurableSet
    _ = 1 := by simp

/-- The set of frames that are not orthonormal has `frameProb M k hk` measure zero. -/
theorem frameProb_nonorthonormal (M k : ℕ) (hk : k ≤ M) :
    frameProb M k hk {v | ¬ Orthonormal M k v} = 0 := by
  have hc : frameProb M k hk (Set.range (prefixColumns hk))ᶜ = 0 := by
    rw [measure_compl (prefixColumns_range_compact hk).isClosed.measurableSet
      (measure_ne_top _ _), frameProb_range, measure_univ]
    simp
  apply measure_mono_null ?_ hc
  rintro v hv ⟨U, rfl⟩
  exact hv (prefixColumns_orthonormal hk U)

/-- The outer content of a set of unitaries obtained by measuring its prefix-column image with
`frameProb`. -/
def sphereFrameContent {M k : ℕ} (hk : k ≤ M) :
    OuterMeasure (Matrix.unitaryGroup (Fin M) ℂ) :=
  imageContent (prefixColumns hk) (frameProb M k hk).toOuterMeasure

/-- The sphere frame content of `X` equals the frame measure of its image under `prefixColumns
hk`. -/
theorem sphereFrameContent_apply {M k : ℕ} (hk : k ≤ M)
    (X : Set (Matrix.unitaryGroup (Fin M) ℂ)) :
    sphereFrameContent hk X = frameProb M k hk (prefixColumns hk '' X) :=
  imageContent_apply _ _ _

/-- The sphere frame content of the entire unitary group is one. -/
theorem sphereFrameContent_univ {M k : ℕ} (hk : k ≤ M) :
    sphereFrameContent hk Set.univ = 1 := by
  rw [sphereFrameContent_apply, Set.image_univ, frameProb_range]

/-- For zero selected columns, every nonempty set of unitaries has sphere frame content one. -/
theorem sphereFrameContent_zero_nonempty {M : ℕ}
    (X : Set (Matrix.unitaryGroup (Fin M) ℂ)) (hX : X.Nonempty) :
    sphereFrameContent (k := 0) (Nat.zero_le M) X = 1 := by
  have hi : prefixColumns (k := 0) (Nat.zero_le M) '' X = Set.univ := by
    ext v
    constructor
    · intro _
      trivial
    · intro _
      obtain ⟨U, hU⟩ := hX
      exact ⟨U, hU, Subsingleton.elim _ _⟩
  rw [sphereFrameContent_apply, hi, measure_univ]

/-- The measurement probability vectors for the first `k` columns of a unitary, with outcomes
grouped by `p`. -/
def probabilityColumns {M A k : ℕ} (hk : k ≤ M) (p : Fin M → Fin A)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Fin k → simplex A :=
  fun i => probabilityVector p ((U : Matrix (Fin M) (Fin M) ℂ) *ᵥ ket (Fin.castLE hk i))
    (unitary_column_mass U.property (Fin.castLE hk i))

/-- The product of `k` copies of `simplexProb A` on families of simplex points. -/
def simplexProduct (A k : ℕ) : Measure (Fin k → simplex A) :=
  Measure.pi (fun _ : Fin k => simplexProb A)

/-- The outer content obtained by measuring the image under `probabilityColumns hk p` with
`simplexProduct A k`. -/
def densityFrameContent {M A k : ℕ} (hk : k ≤ M) (p : Fin M → Fin A) :
    OuterMeasure (Matrix.unitaryGroup (Fin M) ℂ) :=
  imageContent (probabilityColumns hk p) (simplexProduct A k).toOuterMeasure

/-- The density frame content of `X` equals the product simplex measure of its
probability-column image. -/
theorem densityFrameContent_apply {M A k : ℕ} (hk : k ≤ M) (p : Fin M → Fin A)
    (X : Set (Matrix.unitaryGroup (Fin M) ℂ)) :
    densityFrameContent hk p X = simplexProduct A k (probabilityColumns hk p '' X) :=
  imageContent_apply _ _ _

end Qatlib.Papers.QCircApprox95.MainResults
