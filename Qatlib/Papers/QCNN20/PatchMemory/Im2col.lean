/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.AmplitudeAccess.Preparation
public import Qatlib.Concepts.QRAM.WordAccess.Lookup

@[expose] public section

/-!
# Scatter writes to convolution patch memory

In [KerenidisLandmanPrakash2020], Section D.2.1, an output pixel written to
the next layer may occur in several overlapping windows. The occurrence list
indexes every alias of that pixel so a write refreshes the appropriate leaves
and their ancestor masses. Each patch is a subtree and can be prepared
independently. Layouts can include padding by reserving a zero-valued pixel.

[ICLR paper](https://openreview.net/forum?id=Hygab1rKDS)
-/

set_option autoImplicit false

namespace Qatlib.Papers.QCNN20.PatchMemory

open Qatlib.Foundations.QramData.SquaredNormTree
open Qatlib.Concepts.QRAM.AmplitudeAccess
open Matrix

/-- Pixel aliases in a flattened patch table, indexed in both directions. -/
structure Layout (Pixel : Type*) (positions window : ℕ) where
  /-- The input pixel represented by a flattened patch-table entry. -/
  pixelAt : Address (window + positions) → Pixel
  /-- The flattened slots to update when a pixel is overwritten. -/
  occurrences : Pixel → List (Address (window + positions))
  /-- An address is listed exactly when it represents the pixel. -/
  mem_occurrences : ∀ pixel address, address ∈ occurrences pixel ↔ pixelAt address = pixel

variable {Pixel : Type*} {positions window : ℕ}

/-- Standard im2col indexing for a valid cross-correlation with spatial stride. -/
def windowPixel (stride : ℕ × ℕ) (position : ℕ × ℕ) (offset : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (position.1 * stride.1 + offset.1, position.2 * stride.2 + offset.2.1, offset.2.2)

/-- Form all patches by reading the appropriate image pixel at each slot. -/
def initializePatches (layout : Layout Pixel positions window) (image : Pixel → ℝ) :
    Tree ℝ (window + positions) :=
  ofFn _ (image ∘ layout.pixelAt)

/-- Read a patch at its leading position bits. -/
def patchTree (memory : Tree ℝ (window + positions)) (position : Address positions) :
    Tree ℝ window :=
  subtree positions memory position

/-- Store a sampled output value in every alias of its pixel in the next layer. -/
def scatterPixel (layout : Layout Pixel positions window) (memory : Tree ℝ (window + positions))
    (pixel : Pixel) (value : ℝ) : Tree ℝ (window + positions) :=
  refresh memory (layout.occurrences pixel) (fun _ => value)

/-- Scatter writes preserve every cached patch and supertree mass. -/
theorem valid_scatter_pixel (layout : Layout Pixel positions window)
    (memory : Tree ℝ (window + positions)) (h : Valid memory) (pixel : Pixel) (value : ℝ) :
    Valid (scatterPixel layout memory pixel value) :=
  valid_refresh memory h _ _

/-- A pixel overwrite changes every alias and leaves all other patch entries intact. -/
theorem read_scatter_pixel [DecidableEq Pixel] (layout : Layout Pixel positions window)
    (memory : Tree ℝ (window + positions)) (pixel : Pixel) (value : ℝ)
    (address : Address (window + positions)) :
    read (scatterPixel layout memory pixel value) address =
      if layout.pixelAt address = pixel then value else read memory address := by
  simp only [scatterPixel, read_refresh, layout.mem_occurrences]

/-- Starting with implicit zeros, write sampled activations to the next-layer patch table. -/
def loadSampledOutput (layout : Layout Pixel positions window)
    (samples : List (Pixel × ℝ)) : Tree ℝ (window + positions) :=
  samples.foldl (fun current sample => scatterPixel layout current sample.1 sample.2)
    (.vacant (window + positions))

/-- Every prefix of the forward sampling stream gives consistent cached patch norms. -/
theorem valid_load_sampled_output (layout : Layout Pixel positions window)
    (samples : List (Pixel × ℝ)) : Valid (loadSampledOutput layout samples) := by
  have hFold (pending : List (Pixel × ℝ)) (tree : Tree ℝ (window + positions)) (h : Valid tree) :
      Valid (pending.foldl (fun current sample => scatterPixel layout current sample.1 sample.2)
        tree) := by
    induction pending generalizing tree with
    | nil => exact h
    | cons sample pending ih => exact ih _ (valid_scatter_pixel layout tree h sample.1 sample.2)
  exact hFold samples _ (by trivial)

/-- A sampled pixel writes one path in memory for each occurrence in a patch. -/
theorem scatter_cell_count (layout : Layout Pixel positions window)
    (memory : Tree ℝ (window + positions)) (pixel : Pixel) (value : ℝ) :
    (refreshWithCount memory (layout.occurrences pixel) (fun _ => value)).2 =
      (layout.occurrences pixel).length * (window + positions + 1) :=
  refresh_cell_count _ _ _

/-- The unitary addressed word read from the paper's patch layout. -/
noncomputable def patchQuery {width : ℕ} (encode : ℝ → BitVec width)
    (memory : Tree ℝ (window + positions)) :
    Matrix (Address (window + positions) × BitVec width)
      (Address (window + positions) × BitVec width) ℂ :=
  Qatlib.Concepts.QRAM.WordAccess.query (encode ∘ read memory)

end Qatlib.Papers.QCNN20.PatchMemory
