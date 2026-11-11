/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration

/-!
# Transpose access for compact sketches

`compactTransposeWeights` computes squared column entries and counts source queries, while
`compactTransposeRowMass` and `compactTransposeColumnMass` describe sampling access to the
transpose. Exact row-energy sampling produces normalized transpose laws and preserves domination
by a source envelope, as required for compact sketch access in [ChiaEtAl2022].

## Main statements

* `compactTransposeWeights_eq`: The transpose-weight computation returns the squared sketched
  column entries in order and query count `r`.
* `compact_sketch_transpose_actual_access`: Under exact supported row-energy sampling, the
  envelope sketch has equal row energies and unchanged total energy, possesses the specified
  transpose sampling laws, and computes each column's weights using exactly `r` entry queries.
  See [ChiaEtAl2022].

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false
namespace Qatlib.Concepts.SketchArith.TransposeAccess
open Matrix
open scoped Classical BigOperators Matrix.Norms.Frobenius

/-- The squared entry weights of a sketched column, paired with the number of source-entry
queries. -/
noncomputable def compactTransposeWeights {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (Ah : Matrix K C ℂ) (j : C) : List ℝ×ℕ :=
  let a:=(List.ofFn (fun t : Fin r=> t)).foldl (fun a t =>
    (Complex.normSq ((compactSketchEntry d Ah t j).1)::a.1,a.2+1)) ([],0);
  (a.1.reverse,a.2)

/-- The average of the conditional column probabilities along the sampled source rows. -/
noncomputable def compactTransposeRowMass {K C : Type} [Fintype C] {r : ℕ} (q : K→FinDist C)
    (ω : Fin r→K) (j : C) : ℝ := (∑ t,(q (ω t)).prob j)/(r:ℝ)

/-- The normalized squared-entry mass within a sketched column, using a point mass at `t0` when
its total weight is zero. -/
noncomputable def compactTransposeColumnMass {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (Ah : Matrix K C ℂ) (t0 : Fin r) (j : C) (t : Fin r) : ℝ :=
  let e:=(compactTransposeWeights d Ah j).1.sum;
  if e=0 then if t= t0 then 1 else 0 else Complex.normSq ((compactSketchEntry d Ah t j).1)/e

/-- Evaluates the column-weight fold as a reversed mapped list and a counter increased by the
list length. -/
private theorem compact_transpose_fold {T : Type} (xs : List T) (f : T→ℝ) (a : List ℝ) (b : ℕ) :
    xs.foldl (fun a t=>(f t::a.1,a.2+1)) (a,b)=((xs.map f).reverse++a,b+xs.length) := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The transpose-weight computation returns the squared sketched column entries in order and
query count `r`. -/
theorem compactTransposeWeights_eq {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (A : Matrix K C ℂ) (j : C) :
    compactTransposeWeights d A j=(List.ofFn (fun t=>Complex.normSq (compactSketched d A t j)),r) := by
  unfold compactTransposeWeights
  rw [compact_transpose_fold]
  simp [List.map_ofFn,Function.comp_def,compactSketched]

/-- Every compact transpose-column mass is nonnegative. -/
private theorem compact_column_mass_nonneg {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (A : Matrix K C ℂ) (t0 t : Fin r) (j : C) :
    0≤compactTransposeColumnMass d A t0 j t := by
  unfold compactTransposeColumnMass
  (try dsimp only)
  split_ifs <;> try positivity
  apply div_nonneg (Complex.normSq_nonneg _)
  rw [compactTransposeWeights_eq]
  simp only [List.sum_ofFn]
  exact Finset.sum_nonneg fun _ _=>Complex.normSq_nonneg _

/-- The compact transpose-column masses sum to one, including the zero-energy fallback case. -/
private theorem compact_column_mass_sum {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (A : Matrix K C ℂ) (t0 : Fin r) (j : C) :
    (∑ t : Fin r,compactTransposeColumnMass d A t0 j t)=1 := by
  unfold compactTransposeColumnMass
  (try dsimp only)
  split_ifs with he
  · simp
  · rw [← Finset.sum_div]
    have hs : (∑ t : Fin r,Complex.normSq (compactSketchEntry d A t j).1)=
        (compactTransposeWeights d A j).1.sum := by
      rw [compactTransposeWeights_eq]
      simp only [List.sum_ofFn,compactSketched]
    rw [hs,div_self he]

/-- Applying the same compact sketch preserves entrywise domination of squared entry norms. -/
theorem compactSketched_normSq_mono {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (A B : Matrix K C ℂ) (h : ∀ i j,Complex.normSq (A i j)≤Complex.normSq (B i j)) :
    ∀ t j,Complex.normSq (compactSketched d A t j)≤Complex.normSq (compactSketched d B t j) := by
  intro t j
  simp only [compactSketched,compactSketchEntry,Complex.normSq_mul,Complex.normSq_ofReal]
  exact mul_le_mul_of_nonneg_left (h _ _) (mul_self_nonneg _)

/-- Under exact supported row-energy sampling, the envelope sketch has equal row energies and
unchanged total energy, possesses the specified transpose sampling laws, and computes each
column's weights using exactly `r` entry queries. See [ChiaEtAl2022]. -/
theorem compact_sketch_transpose_actual_access : ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (p : FinDist K) (q : K→FinDist C) (r : ℕ)
    (A Ah : Matrix K C ℂ) (ω : Fin r→K) (t0 : Fin r),
  0< sketchSquared Ah → (∀ i j,Complex.normSq (A i j)≤ Complex.normSq (Ah i j)) →
  (∀ i,p.prob i= sketchRowSquared Ah i/sketchSquared Ah) →
  (∀ i,0< sketchRowSquared Ah i → ∀ j,(q i).prob j= Complex.normSq (Ah i j)/sketchRowSquared Ah i) →
  (∀ t,0< p.prob (ω t)) →
  let d:= compactSketchData p r ω;
  sketchSquared (compactSketched d Ah)= sketchSquared Ah ∧
  (∀ t,sketchRowSquared (compactSketched d Ah) t= sketchSquared Ah/(r:ℝ)) ∧
  (∀ i j,Complex.normSq (compactSketched d A i j)≤ Complex.normSq (compactSketched d Ah i j)) ∧
  (∃ (rows : FinDist C) (cols : C→FinDist (Fin r)),
    (∀ j,rows.prob j= compactTransposeRowMass q ω j) ∧
    (∀ j t,(cols j).prob t= compactTransposeColumnMass d Ah t0 j t) ∧
    (∀ j,rows.prob j=(∑ t,Complex.normSq (compactSketched d Ah t j))/sketchSquared Ah)) ∧
  (∀ j,(compactTransposeWeights d Ah j).2= r ∧
    (compactTransposeWeights d Ah j).1= List.ofFn (fun t=> Complex.normSq (compactSketched d Ah t j))) := by
  intro K C _ _ _ _ p q r A Ah ω t0 hE hdom hp hq hsupp
  have hr : 0<r := by have := t0.isLt; omega
  have hrp : 0<(r : ℝ) := Nat.cast_pos.mpr hr
  let d := compactSketchData p r ω
  have hroweq (t : Fin r) : sketchRowSquared Ah (ω t)=sketchSquared Ah*p.prob (ω t) := by
    rw [hp]
    field_simp
  have hrowpos (t : Fin r) : 0<sketchRowSquared Ah (ω t) := by
    rw [hroweq]; exact mul_pos hE (hsupp t)
  have hrows (t : Fin r) : sketchRowSquared (compactSketched d Ah) t=sketchSquared Ah/(r : ℝ) := by
    rw [compactSketched_row_energy,hroweq]
    field_simp [(hsupp t).ne']
  have htotal : sketchSquared (compactSketched d Ah)=sketchSquared Ah := by
    change (∑ t : Fin r,sketchRowSquared (compactSketched d Ah) t)=sketchSquared Ah
    simp only [hrows,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
    field_simp
  have hqentry (t : Fin r) (j : C) :
      (q (ω t)).prob j = (r : ℝ)*Complex.normSq (compactSketched d Ah t j)/sketchSquared Ah := by
    rw [hq (ω t) (hrowpos t) j,hroweq]
    simp only [compactSketched,compactSketchEntry,Complex.normSq_mul,Complex.normSq_ofReal,← pow_two,
      ]
    rw [show (d t).2^2=((r : ℝ)*p.prob (ω t))⁻¹ from compactSketch_scale_sq p r ω t]
    change Complex.normSq (Ah (ω t) j)/(sketchSquared Ah*p.prob (ω t)) =
      (r : ℝ)*(((r : ℝ)*p.prob (ω t))⁻¹*Complex.normSq (Ah (ω t) j))/sketchSquared Ah
    field_simp
  have hrowlaw (j : C) : compactTransposeRowMass q ω j =
      (∑ t : Fin r,Complex.normSq (compactSketched d Ah t j))/sketchSquared Ah := by
    unfold compactTransposeRowMass
    simp only [hqentry,← Finset.sum_div,← Finset.mul_sum]
    field_simp
  let rows : FinDist C := {
    prob := compactTransposeRowMass q ω
    nonneg := fun j=>div_nonneg (Finset.sum_nonneg (fun t _=>(q (ω t)).nonneg j)) hrp.le
    sum_one := by
      unfold compactTransposeRowMass
      rw [← Finset.sum_div,Finset.sum_comm]
      simp only [FinDist.sum_one,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin]
      field_simp }
  let cols : C→FinDist (Fin r) := fun j=>{
    prob := compactTransposeColumnMass d Ah t0 j
    nonneg := fun t=>compact_column_mass_nonneg d Ah t0 t j
    sum_one := compact_column_mass_sum d Ah t0 j }
  refine ⟨htotal,hrows,compactSketched_normSq_mono d A Ah hdom,⟨rows,cols,?_,?_,?_⟩,?_⟩
  · intro j; rfl
  · intro j t; rfl
  · exact hrowlaw
  · intro j
    rw [compactTransposeWeights_eq]
    exact ⟨rfl,rfl⟩

end Qatlib.Concepts.SketchArith.TransposeAccess
