/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LaurentPolys.ProfileFftBound.CanonicalComplementFFTConsumers

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.LaurentPolys.ProfileFftBound Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Concepts.LaurentPolys.BoundaryCanon
open Polynomial
open scoped Classical

def canonicalComplementAlgorithmTwoDownscaleSlots (d m : ℕ) : Finset (Fin (2^m)) :=
  Finset.univ.filter (fun l => l.val ≤ d)

/-- The number of downscale slots is the minimum of `d+1` and the Fourier grid size. -/
theorem canonicalComplementAlgorithmTwoDownscaleSlots_card (d m : ℕ) :
    (canonicalComplementAlgorithmTwoDownscaleSlots d m).card = min (d+1) (2^m) := by
  classical
  calc
    _ = (Finset.range (min (d+1) (2^m))).card := by
      apply Finset.card_bij (fun l _ => l.val)
      · intro l hl
        have hld := (Finset.mem_filter.mp hl).2
        have hlN := l.isLt
        apply Finset.mem_range.mpr
        omega
      · intro a _ b _ hab
        exact Fin.ext hab
      · intro k hk
        have hk' := Finset.mem_range.mp hk
        have hkN : k < 2^m := by omega
        refine ⟨⟨k, hkN⟩, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by dsimp; omega⟩
    _ = _ := Finset.card_range _

/-- There are exactly `d+1` downscale slots if and only if the Fourier grid has at least that
many points. -/
theorem canonicalComplementAlgorithmTwoDownscaleSlots_card_eq_iff (d m : ℕ) :
    (canonicalComplementAlgorithmTwoDownscaleSlots d m).card = d+1 ↔ d+1 ≤ 2^m := by
  rw [canonicalComplementAlgorithmTwoDownscaleSlots_card]
  omega

def canonicalComplementAlgorithmTwoSlotRun (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    CanonicalComplementAlgorithmTwoRun m :=
  let run := canonicalComplementAlgorithmTwoRun P₀ d m ε
  { run with multiplications := run.multiplications - (d+1) +
      (canonicalComplementAlgorithmTwoDownscaleSlots d m).card }

/-- The slot based Algorithm 2 run has the same coefficient and grid value outputs as the
original run. -/
theorem canonicalComplementAlgorithmTwoSlotRun_outputs
    (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).coefficients =
        (canonicalComplementAlgorithmTwoRun P₀ d m ε).coefficients ∧
      (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).gridValues =
        (canonicalComplementAlgorithmTwoRun P₀ d m ε).gridValues := ⟨rfl, rfl⟩

/-- Gives the exact multiplication, addition, logarithm, and exponential counts of the slot
based Algorithm 2 run. -/
theorem canonicalComplementAlgorithmTwoSlotRun_cost
    (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).multiplications =
        5*(m*2^m/2)+2*2^m+1+min (d+1) (2^m) ∧
      (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).additions = 5*m*2^m ∧
      (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).logarithms = 2^m ∧
      (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).exponentials = 2^m := by
  have h := canonicalComplementAlgorithmTwoRun_cost P₀ d m ε
  refine ⟨?_, h.2⟩
  change (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications - (d+1) +
    (canonicalComplementAlgorithmTwoDownscaleSlots d m).card = _
  rw [h.1, Nat.add_sub_cancel, canonicalComplementAlgorithmTwoDownscaleSlots_card]

/-- The slot based and original Algorithm 2 runs agree when the grid has at least `d+1` points. -/
theorem canonicalComplementAlgorithmTwoSlotRun_eq_of_valid_grid
    (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) (hgrid : d+1 ≤ 2^m) :
    canonicalComplementAlgorithmTwoSlotRun P₀ d m ε =
      canonicalComplementAlgorithmTwoRun P₀ d m ε := by
  have hcard := (canonicalComplementAlgorithmTwoDownscaleSlots_card_eq_iff d m).mpr hgrid
  have hbook := (canonicalComplementAlgorithmTwoRun_cost P₀ d m ε).1
  have hfix : (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications - (d+1) +
      (canonicalComplementAlgorithmTwoDownscaleSlots d m).card =
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications := by
    rw [hcard, hbook]
    omega
  simp only [canonicalComplementAlgorithmTwoSlotRun, hfix]

/-- The original multiplication count exceeds the slot based count by the excess of `d+1` over
the grid size. -/
theorem canonicalComplementAlgorithmTwoSlotRun_booked_gap
    (P₀ : Polynomial ℂ) (d m : ℕ) (ε : ℝ) :
    (canonicalComplementAlgorithmTwoSlotRun P₀ d m ε).multiplications + ((d+1) - 2^m) =
      (canonicalComplementAlgorithmTwoRun P₀ d m ε).multiplications := by
  rw [(canonicalComplementAlgorithmTwoSlotRun_cost P₀ d m ε).1,
    (canonicalComplementAlgorithmTwoRun_cost P₀ d m ε).1]
  omega

end Qatlib.Concepts.LaurentPolys.BoundaryCanon
