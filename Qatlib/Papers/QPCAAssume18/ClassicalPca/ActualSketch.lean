/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPCAAssume18.ClassicalPca.ClassicalPCA
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchSingularValueL2StabilitySamp
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QPCAAssume18.ClassicalPca

open Matrix

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SketchSpectral.SketchAnalysis

def pcaRowLaw {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) : FinDist (Fin n) where
  prob i := sketchRowSquared A i / sketchSquared A
  nonneg i := div_nonneg (sketchRowSquared_nonneg A i) hA.le
  sum_one := by
    rw [← Finset.sum_div]
    change sketchSquared A / sketchSquared A = 1
    exact div_self hA.ne'

def pcaPointLaw {d : ℕ} (hd : 0 < d) : FinDist (Fin d) where
  prob j := if j = ⟨0, hd⟩ then 1 else 0
  nonneg j := by split_ifs <;> norm_num
  sum_one := by simp

def pcaRowSketch {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (rows : Fin q → Fin n) :
    Matrix (Fin q) (Fin d) ℂ :=
  compactSketched (compactSketchData (pcaRowLaw A hA) q rows) A

def pcaColumnLaw {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) (rows : Fin q → Fin n) :
    FinDist (Fin d) :=
  if hR : 0 < sketchSquared (pcaRowSketch A hA q rows)ᴴ then
    pcaRowLaw (pcaRowSketch A hA q rows)ᴴ hR else pcaPointLaw hd

def pcaSmallMatrix {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ)
    (rows : Fin q → Fin n) (cols : Fin q → Fin d) : Matrix (Fin q) (Fin q) ℂ :=
  (compactSketched (compactSketchData (pcaColumnLaw A hA hd q rows) q cols)
    (pcaRowSketch A hA q rows)ᴴ)ᴴ

def pcaSketchLaw {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) :
    FinDist ((Fin q → Fin n) × (Fin q → Fin d)) :=
  twoSketchRecordLaw (pcaRowLaw A hA) q q (pcaColumnLaw A hA hd q)

theorem pcaColumnLaw_spec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (hd : 0 < d) (q : ℕ) (rows : Fin q → Fin n)
    (hR : 0 < sketchSquared (pcaRowSketch A hA q rows)ᴴ) (j : Fin d) :
    (pcaColumnLaw A hA hd q rows).prob j =
      sketchRowSquared (pcaRowSketch A hA q rows)ᴴ j /
        sketchSquared (pcaRowSketch A hA q rows)ᴴ := by
  simp only [pcaColumnLaw, dif_pos hR, pcaRowLaw]

theorem pcaRowLaw_domination {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (i : Fin n) :
    sketchRowSquared A i / (1 * sketchSquared A) ≤ (pcaRowLaw A hA).prob i := by
  simp [pcaRowLaw]

theorem pcaRowSketch_energy {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (hq : 0 < q) (rows : Fin q → Fin n) :
    sketchSquared (pcaRowSketch A hA q rows) ≤ sketchSquared A := by
  simpa only [one_mul] using! (compact_sketch_frobenius_norm_bounds_and_tail (Fin n) (Fin d)
    (pcaRowLaw A hA) q A 1 hq (by norm_num) hA (pcaRowLaw_domination A hA)).2.1 rows

theorem pcaRowProductMass_self {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ) :
    sketchRowProductMass A A = sketchSquared A := by
  unfold sketchRowProductMass sketchSquared
  apply Finset.sum_congr rfl
  intro i _
  exact Real.mul_self_sqrt (sketchRowSquared_nonneg A i)

theorem pca_gram_tail {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℂ)
    (hA : 0 < sketchSquared A) (q : ℕ) (hq : 0 < q)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    (pcaRowLaw A hA).probEvent (fun rows : Fin q → Fin n =>
      Real.sqrt (8 * Real.log (2 / delta) / (q : ℝ)) * sketchSquared A ≤
        spectralFrobenius ((pcaRowSketch A hA q rows)ᴴ * pcaRowSketch A hA q rows - Aᴴ * A))
      ≤ delta := by
  have ht := compact_sketch_two_sided_source_frobenius_tail (Fin n) (Fin d) (Fin d)
    (pcaRowLaw A hA) q A A 1 delta hq (by norm_num)
      (by simpa only [pcaRowProductMass_self] using! hA) hdelta hdelta1 (by
        intro i
        simpa only [pcaRowProductMass_self, Real.mul_self_sqrt (sketchRowSquared_nonneg A i)]
          using! pcaRowLaw_domination A hA i)
  simp only [pcaRowProductMass_self, one_pow, mul_one] at ht
  simp_rw [(compact_sketch_actual_pairs_entries_and_queries (Fin n) (Fin d) (Fin d)
    (pcaRowLaw A hA) q A A _).2.2.2.2.2,
    ← spectralFrobenius_eq_sampling_norm] at ht
  exact ht

def pcaGramSamples (K e delta : ℝ) : ℕ :=
  ⌈K⌉₊ + ⌈80000 * K ^ 4 / e ^ 2 * Real.log (4 / delta)⌉₊ + 1

def pcaGramTolerance (K e : ℝ) : ℝ := e / (100 * K ^ 2)

theorem pcaGramSamples_rank (K e delta : ℝ) :
    0 < pcaGramSamples K e delta ∧ K ≤ (pcaGramSamples K e delta : ℝ) := by
  constructor
  · unfold pcaGramSamples
    omega
  · have h := Nat.le_ceil K
    unfold pcaGramSamples
    push_cast
    have hN := Nat.cast_nonneg (α := ℝ) ⌈80000 * K ^ 4 / e ^ 2 * Real.log (4 / delta)⌉₊
    linarith

theorem pcaGramSamples_budget (K e delta : ℝ) (hK : 0 < K) (he : 0 < e) :
    8 * Real.log (4 / delta) ≤
      (pcaGramSamples K e delta : ℝ) * pcaGramTolerance K e ^ 2 := by
  have hceil := Nat.le_ceil (80000 * K ^ 4 / e ^ 2 * Real.log (4 / delta))
  have hq : 80000 * K ^ 4 / e ^ 2 * Real.log (4 / delta) ≤
      (pcaGramSamples K e delta : ℝ) := by
    unfold pcaGramSamples
    push_cast
    have hN := Nat.cast_nonneg (α := ℝ) ⌈K⌉₊
    linarith
  have ht : 0 ≤ pcaGramTolerance K e ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hq ht
  have hid : (80000 * K ^ 4 / e ^ 2 * Real.log (4 / delta)) * pcaGramTolerance K e ^ 2 =
      8 * Real.log (4 / delta) := by
    unfold pcaGramTolerance
    field_simp
    ring
  rwa [hid] at hmul

theorem pcaGramSamples_scale (K e delta : ℝ) (hK : 0 < K) (he : 0 < e) :
    Real.sqrt (8 * Real.log (4 / delta) / (pcaGramSamples K e delta : ℝ)) ≤
      pcaGramTolerance K e := by
  have hq : 0 < (pcaGramSamples K e delta : ℝ) := by
    exact_mod_cast (pcaGramSamples_rank K e delta).1
  have ht : 0 < pcaGramTolerance K e := by unfold pcaGramTolerance; positivity
  apply (Real.sqrt_le_iff).mpr
  refine ⟨ht.le, ?_⟩
  exact (div_le_iff₀ hq).mpr (by nlinarith [pcaGramSamples_budget K e delta hK he])

end Qatlib.Papers.QPCAAssume18.ClassicalPca
