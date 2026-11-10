/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox.RankBias
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox

attribute [local instance] Classical.propDecidable

def rowsInS {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) : Type :=
  {i : Fin k // dot (p i) s = 1}

instance rowsInS.fintype {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    Fintype (rowsInS p s) :=
  Subtype.fintype _

def Ps {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    Matrix (rowsInS p s) (Fin n) (ZMod 2) :=
  fun i j => p i.1 j

def Qs {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  (Ps p s)ᵀ * Ps p s

def ySample {n k : ℕ} (p : Fin k → F2Vec n) (d e : F2Vec n) : F2Vec n :=
  ∑ i, (dot (p i) d * dot (p i) e) • p i

theorem dot_mulVec_transpose {ι : Type} [Fintype ι] {n : ℕ} (A : Matrix ι (Fin n) (ZMod 2))
    (d e : F2Vec n) :
    dot d ((Aᵀ * A).mulVec e) = dot (A.mulVec d) (A.mulVec e) := by
  change d ⬝ᵥ ((Aᵀ * A).mulVec e) = (A.mulVec d) ⬝ᵥ (A.mulVec e)
  rw [← Matrix.mulVec_mulVec (v := e) (M := Aᵀ) (N := A), Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem dot_ySample {n k : ℕ} (p : Fin k → F2Vec n) (s d e : F2Vec n) :
    dot (ySample p d e) s = dot d ((Qs p s).mulVec e) := by
  have hterm : ∀ i : Fin k,
      (dot (p i) d * dot (p i) e) * dot (p i) s =
        if dot (p i) s = 1 then dot (p i) d * dot (p i) e else 0 := by
    intro i
    rcases zmod2_eq_zero_or_one (dot (p i) s) with h | h <;> simp [h]
  have hfilter :
      (∑ i : Fin k, if dot (p i) s = 1 then dot (p i) d * dot (p i) e else 0) =
        ∑ i : rowsInS p s, dot (p i.1) d * dot (p i.1) e := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun i => dot (p i) s = 1)
      (Finset.univ.filter (fun i => dot (p i) s = 1)) (fun x => by simp) _
  have hform : dot d ((Qs p s).mulVec e) =
      ∑ i : rowsInS p s, dot (p i.1) d * dot (p i.1) e := by
    rw [Qs, dot_mulVec_transpose]
    rfl
  calc
    dot (ySample p d e) s =
        ∑ i : Fin k, (dot (p i) d * dot (p i) e) * dot (p i) s := by
      simp [ySample, dot_sum, dot_smul]
    _ = ∑ i : Fin k,
        if dot (p i) s = 1 then dot (p i) d * dot (p i) e else 0 := by
      exact Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ i : rowsInS p s, dot (p i.1) d * dot (p i.1) e := hfilter
    _ = dot d ((Qs p s).mulVec e) := hform.symm

theorem yBias_eq_rank {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    pairProb (fun d e => dot (ySample p d e) s = 0) =
      (1 + 1 / (2 : ℝ) ^ Matrix.rank (Qs p s)) / 2 := by
  rw [pairProb_congr (fun d e => by rw [dot_ySample])]
  exact pairProb_bilinear_eq_rank (Qs p s)

theorem yBias_eq_codePair {n k : ℕ} (p : Fin k → F2Vec n) (s : F2Vec n) :
    pairProb (fun d e => dot (ySample p d e) s = 0) =
      pairProb (fun d e => dot ((Ps p s).mulVec d) ((Ps p s).mulVec e) = 0) := by
  rw [pairProb_congr (fun d e => by rw [dot_ySample])]
  rw [pairProb_congr (fun d e => by
    rw [Qs, dot_mulVec_transpose (A := Ps p s) d e])]

end Qatlib.Papers.Instantaneous08.MainResults.ClassicalApprox
