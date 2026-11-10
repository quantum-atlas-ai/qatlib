/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Analysis.Matrix.Normed
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Concepts.SketchArith.SketchBuild
open Matrix
open scoped Classical BigOperators Matrix.Norms.Frobenius

noncomputable def sketchRowSquared {K C : Type} [Fintype C] (A : Matrix K C ℂ) (i : K) : ℝ :=
  ∑ j,Complex.normSq (A i j)

noncomputable def sketchSquared {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) : ℝ :=
  ∑ i,sketchRowSquared A i

noncomputable def sketchRowProductMass {K C D : Type} [Fintype K] [Fintype C] [Fintype D]
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) : ℝ :=
  ∑ i,Real.sqrt (sketchRowSquared X i)*Real.sqrt (sketchRowSquared Y i)

noncomputable def compactSketchData {K : Type} [Fintype K] (p : FinDist K) (r : ℕ)
    (ω : Fin r→K) : Fin r→K×ℝ := fun t=>(ω t,(Real.sqrt ((r:ℝ)*p.prob (ω t)))⁻¹)

noncomputable def compactSketchBuild {K : Type} [Fintype K] (p : FinDist K) (r : ℕ)
    (ω : Fin r→K) : List (K×ℝ)×ℕ×ℕ :=
  let a:=(List.ofFn (fun t : Fin r=> t)).foldl (fun a t =>
    (compactSketchData p r ω t::a.1,a.2.1+1,a.2.2+1)) ([],0,0);
  (a.1.reverse,a.2.1,a.2.2)

noncomputable def compactSketchMatrix {K : Type} [DecidableEq K] {r : ℕ}
    (d : Fin r→K×ℝ) : Matrix (Fin r) K ℂ := fun t i=> if i=(d t).1 then ((d t).2:ℂ) else 0

noncomputable def compactSketchEntry {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (A : Matrix K C ℂ) (t : Fin r) (j : C) : ℂ×ℕ :=
  (((d t).2:ℂ)*A (d t).1 j,1)

noncomputable def compactSketched {K C : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (A : Matrix K C ℂ) : Matrix (Fin r) C ℂ := fun t j=>(compactSketchEntry d A t j).1

noncomputable def compactProductEntry {K C D : Type} {r : ℕ}
    (d : Fin r→K×ℝ) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (i : C) (j : D) : ℂ×ℕ :=
  (List.ofFn (fun t : Fin r=> t)).foldl (fun a t =>
    (a.1+star ((compactSketchEntry d X t i).1)*(compactSketchEntry d Y t j).1,a.2+2)) (0,0)

noncomputable def compactProduct {K C D : Type} {r : ℕ}
    (d : Fin r→K×ℝ) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) : Matrix C D ℂ :=
  fun i j=>(compactProductEntry d X Y i j).1

noncomputable def sketchProduct {K C D : Type} [Fintype K]
    (p : FinDist K) (r : ℕ) (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (ω : Fin r→K) : Matrix C D ℂ :=
  compactProduct (compactSketchData p r ω) X Y

private theorem compact_build_fold {T K : Type} (xs : List T) (d : T→K×ℝ)
    (a : List (K×ℝ)) (b c : ℕ) :
    xs.foldl (fun a t => (d t::a.1,a.2.1+1,a.2.2+1)) (a,b,c) =
      ((xs.map d).reverse++a,b+xs.length,c+xs.length) := by
  induction xs generalizing a b c with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem compact_product_fold {T : Type} (xs : List T) (f : T→ℂ) (a : ℂ) (b : ℕ) :
    xs.foldl (fun a t => (a.1+f t,a.2+2)) (a,b) =
      (a+(xs.map f).sum,b+2*xs.length) := by
  induction xs generalizing a b with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons,ih,Nat.mul_add,Nat.add_comm,add_assoc]

theorem compactSketchBuild_eq {K : Type} [Fintype K] (p : FinDist K) (r : ℕ) (ω : Fin r→K) :
    compactSketchBuild p r ω = (List.ofFn (compactSketchData p r ω),r,r) := by
  unfold compactSketchBuild
  rw [compact_build_fold]
  simp [List.map_ofFn,Function.comp_def]

theorem compactProductEntry_eq {K C D : Type} {r : ℕ} (d : Fin r→K×ℝ)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (i : C) (j : D) :
    compactProductEntry d X Y i j =
      (∑ t : Fin r,star ((compactSketchEntry d X t i).1)*(compactSketchEntry d Y t j).1,2*r) := by
  unfold compactProductEntry
  rw [compact_product_fold]
  simp [List.map_ofFn,List.sum_ofFn]

theorem compact_sketch_actual_pairs_entries_and_queries : ∀ (K C D : Type) [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] [Fintype D] [DecidableEq D] (p : FinDist K) (r : ℕ)
    (X : Matrix K C ℂ) (Y : Matrix K D ℂ) (ω : Fin r→K),
  (compactSketchBuild p r ω).1= List.ofFn (compactSketchData p r ω) ∧
  (compactSketchBuild p r ω).2.1= r ∧ (compactSketchBuild p r ω).2.2= r ∧
  compactSketched (compactSketchData p r ω) X= compactSketchMatrix (compactSketchData p r ω)*X ∧
  (∀ i j,(compactProductEntry (compactSketchData p r ω) X Y i j).2=2*r) ∧
  sketchProduct p r X Y ω=(compactSketched (compactSketchData p r ω) X)ᴴ*
    compactSketched (compactSketchData p r ω) Y := by
  intro K C D _ _ _ _ _ _ p r X Y ω
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [compactSketchBuild_eq]
  · rw [compactSketchBuild_eq]
  · rw [compactSketchBuild_eq]
  · ext t j
    simp [compactSketched,compactSketchEntry,compactSketchMatrix,Matrix.mul_apply,
      ite_mul,Finset.sum_ite_eq']
  · intro i j
    rw [compactProductEntry_eq]
  · ext i j
    simp [sketchProduct,compactProduct,compactProductEntry_eq,compactSketched,
      Matrix.mul_apply,Matrix.conjTranspose_apply]

end Qatlib.Concepts.SketchArith.SketchBuild
