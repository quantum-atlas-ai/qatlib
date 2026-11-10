/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
namespace Qatlib.Concepts.PepsTransfer.OpenGridPeps
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

abbrev Tensor (a b d D : ℕ) := Fin a→Fin b→Fin d→Fin D→Fin D→Fin D→Fin D→ℂ

def value {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d)
    (h : Fin a×Fin (b-1)→Fin D) (v : Fin (a-1)×Fin b→Fin D) (i : Fin a) (j : Fin b) : ℂ :=
  let z : Fin D := ⟨0,hD⟩
  let up : Fin D := if hi : 0 < i.val then v (⟨i.val-1,by omega⟩,j) else z
  let dn : Fin D := if hi : i.val+1 < a then v (⟨i.val,by omega⟩,j) else z
  let lf : Fin D := if hj : 0 < j.val then h (i,⟨j.val-1,by omega⟩) else z
  let rt : Fin D := if hj : j.val+1 < b then h (i,⟨j.val,by omega⟩) else z
  A i j (x i j) up dn lf rt

noncomputable def amplitude {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d) : ℂ :=
  ∑ h : Fin a×Fin (b-1)→Fin D, ∑ v : Fin (a-1)×Fin b→Fin D, ∏ i, ∏ j, value hD A x h v i j

noncomputable def rowMatrix {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D)
    (x : Fin a→Fin b→Fin d) (i : Fin a) : Matrix (Fin b→Fin D) (Fin b→Fin D) ℂ := fun up dn=>
  ∑ h : Fin (b-1)→Fin D, ∏ j : Fin b,
    A i j (x i j) (up j) (dn j)
      (if hj : 0 < j.val then h ⟨j.val-1,by omega⟩ else ⟨0,hD⟩)
      (if hj : j.val+1 < b then h ⟨j.val,by omega⟩ else ⟨0,hD⟩)

noncomputable def rowAmplitude {a b d D : ℕ} (hD : 0 < D) (A : Tensor a b d D) (x : Fin a→Fin b→Fin d) : ℂ :=
  ((List.ofFn (rowMatrix hD A x)).prod) (fun _=>⟨0,hD⟩) (fun _=>⟨0,hD⟩)

end Qatlib.Concepts.PepsTransfer.OpenGridPeps
