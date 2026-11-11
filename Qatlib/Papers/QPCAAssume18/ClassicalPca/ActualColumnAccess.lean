/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ActualSketch

/-!
# Column sampling from actual PCA sketches

Builds column access for the sampled-row sketch used in the classical PCA construction of
[Tang2021]. Cached row energies and explicit column entry reads recover the sketch energies,
while a mixture of original-row coordinate laws has the same probabilities as `pcaColumnLaw`.

## Main statements

* `pcaColumnMixture_entry`: A sketch row's energy times the original row's coordinate
  probability equals the squared modulus of the corresponding sketch entry.
* `pcaColumnMixture_probability`: The row-mixture construction and `pcaColumnLaw` assign the
  same probability to each column.

## References

* [Tang, 2021][Tang2021]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Qatlib.Papers.QPCAAssume18.ClassicalPca
open Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw

/-- The squared-modulus coordinate distribution of a positive-energy row of `A`, with
`pcaPointLaw` as the fallback for a zero-energy row. -/
def pcaRawCoordinateLaw {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hd : 0 < d) (i : Fin n) : FinDist (Fin d) :=
  if h : 0 < sketchRowSquared A i then {
    prob j := Complex.normSq (A i j) / sketchRowSquared A i
    nonneg j := div_nonneg (Complex.normSq_nonneg _) h.le
    sum_one := by
      rw [← Finset.sum_div]
      change sketchRowSquared A i / sketchRowSquared A i = 1
      exact div_self h.ne'
  } else pcaPointLaw hd

/-- The energy of a sampled row computed from its cached rescaling factor and the corresponding
original row energy. -/
def pcaCachedRowEnergy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) (t : Fin q) : ℝ :=
  ((compactSketchData (pcaRowLaw A hA) q rows t).2) ^ 2 * sketchRowSquared A (rows t)

/-- The cached row energy equals the actual energy of the corresponding row of `pcaRowSketch`. -/
theorem pcaCachedRowEnergy_spec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) (t : Fin q) :
    pcaCachedRowEnergy A hA q rows t = sketchRowSquared (pcaRowSketch A hA q rows) t := by
  simp only [pcaCachedRowEnergy, sketchRowSquared, pcaRowSketch, compactSketched,
    compactSketchEntry, compactSketchData, Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
  ring

/-- The sum of the cached energies of the sampled sketch rows. -/
def pcaCachedTotalEnergy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) : ℝ :=
  ∑ t, pcaCachedRowEnergy A hA q rows t

/-- The cached total energy equals the squared Frobenius norm of the actual row sketch. -/
theorem pcaCachedTotalEnergy_spec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) :
    pcaCachedTotalEnergy A hA q rows = sketchSquared (pcaRowSketch A hA q rows) := by
  simp only [pcaCachedTotalEnergy, pcaCachedRowEnergy_spec, sketchSquared]

/-- The column energy computed by reading each compact sketch entry, together with the
accumulated entry-read count. -/
def pcaColumnEnergyRead {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) (j : Fin d) : ℝ × ℕ :=
  let points :=
      List.ofFn fun t => compactSketchEntry (compactSketchData (pcaRowLaw A hA) q rows) A t j
  ((points.map fun z => Complex.normSq z.1).sum, (points.map Prod.snd).sum)

/-- The column-energy read returns the corresponding row energy of the adjoint sketch and has
entry-read count `q`. -/
theorem pcaColumnEnergyRead_spec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) (j : Fin d) :
    (pcaColumnEnergyRead A hA q rows j).1 = sketchRowSquared (pcaRowSketch A hA q rows)ᴴ j ∧
      (pcaColumnEnergyRead A hA q rows j).2 = q := by
  constructor
  · simp only [pcaColumnEnergyRead, List.map_ofFn, List.sum_ofFn, Function.comp_def,
      sketchRowSquared, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj,
      pcaRowSketch, compactSketched]
  · simp [pcaColumnEnergyRead, compactSketchEntry, Function.comp_def, List.sum_ofFn]

/-- The coordinate law obtained by sampling a sketch row by energy and then a coordinate from
its original row, with `pcaPointLaw` as the zero-energy fallback. -/
def pcaColumnMixture {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) (rows : Fin q → Fin n) : FinDist (Fin d) :=
  if hR : 0 < sketchSquared (pcaRowSketch A hA q rows) then {
    prob j := ∑ t, (pcaRowLaw (pcaRowSketch A hA q rows) hR).prob t *
      (pcaRawCoordinateLaw A hd (rows t)).prob j
    nonneg j := Finset.sum_nonneg fun t _ => mul_nonneg ((pcaRowLaw _ hR).nonneg t)
      ((pcaRawCoordinateLaw A hd (rows t)).nonneg j)
    sum_one := by
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, (pcaRawCoordinateLaw _ _ _).sum_one, mul_one,
        (pcaRowLaw _ hR).sum_one]
  } else pcaPointLaw hd

/-- A sketch row's energy times the original row's coordinate probability equals the squared
modulus of the corresponding sketch entry. -/
theorem pcaColumnMixture_entry {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) (rows : Fin q → Fin n)
    (t : Fin q) (j : Fin d) :
    sketchRowSquared (pcaRowSketch A hA q rows) t * (pcaRawCoordinateLaw A hd (rows t)).prob j =
      Complex.normSq (pcaRowSketch A hA q rows t j) := by
  rw [← pcaCachedRowEnergy_spec]
  have hentry : Complex.normSq (pcaRowSketch A hA q rows t j) =
      ((compactSketchData (pcaRowLaw A hA) q rows t).2) ^ 2 * Complex.normSq (A (rows t) j) := by
    simp only [pcaRowSketch, compactSketched, compactSketchEntry, compactSketchData,
        Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  rw [hentry]
  by_cases hrow : 0 < sketchRowSquared A (rows t)
  · simp only [pcaRawCoordinateLaw, dif_pos hrow, pcaCachedRowEnergy]
    field_simp
  · have hzero : sketchRowSquared A (rows t) = 0 :=
      le_antisymm (le_of_not_gt hrow) (sketchRowSquared_nonneg A _)
    have hz := sketchRowSquared_eq_zero_entry A (rows t) hzero j
    simp only [pcaCachedRowEnergy, hzero, mul_zero, zero_mul, hz, Complex.normSq_zero]

/-- The row-mixture construction and `pcaColumnLaw` assign the same probability to each column. -/
theorem pcaColumnMixture_probability {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) (rows : Fin q → Fin n) (j : Fin d) :
    (pcaColumnMixture A hA hd q rows).prob j = (pcaColumnLaw A hA hd q rows).prob j := by
  by_cases hR : 0 < sketchSquared (pcaRowSketch A hA q rows)
  · have hRH : 0 < sketchSquared (pcaRowSketch A hA q rows)ᴴ := by
      rwa [sketchSquared_adjoint]
    simp only [pcaColumnMixture, dif_pos hR, pcaColumnLaw, dif_pos hRH, pcaRowLaw]
    rw [sketchSquared_adjoint]
    calc
      _ = (∑ t, sketchRowSquared (pcaRowSketch A hA q rows) t *
          (pcaRawCoordinateLaw A hd (rows t)).prob j) / sketchSquared (pcaRowSketch A hA q rows) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := by
        simp_rw [pcaColumnMixture_entry]
        simp only [sketchRowSquared, Matrix.conjTranspose_apply, Complex.star_def,
            Complex.normSq_conj]
  · have hRH : ¬ 0 < sketchSquared (pcaRowSketch A hA q rows)ᴴ := by
      simpa only [sketchSquared_adjoint] using! hR
    simp only [pcaColumnMixture, dif_neg hR, pcaColumnLaw, dif_neg hRH]

end Qatlib.Papers.QPCAAssume18.ClassicalPca
