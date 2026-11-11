/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.GaussianPrimitives

set_option backward.isDefEq.respectTransparency false

/-! CFD uses a highest-coefficient seed, whereas the existing shared-denominator
Horner starts from zero. The latter has one extra common D factor. This thin
bridge preserves the actual Python numerator convention and reuses the existing
integer arithmetic and polynomial semantics. Reference scan charges are not
silently assigned to the Python implementation. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open scoped BigOperators

/-- Same compact numerator/denominator convention as homogeneous_value:
ascending coefficients, highest coefficient seeded without an extra D. -/
def rootCompactHorner (z : GaussianDyadicScalar) (D : ℕ) : List ℤ → GaussianIntegerFraction
  | [] => ⟨(0,0),1⟩
  | [a] => ⟨(a,0),1⟩
  | a::b::cs =>
    let r := rootCompactHorner z D (b::cs)
    ⟨gaussianScalarAdd (gaussianIntegerScale (r.denominator*D) (a,0))
      (gaussianIntegerMul r.numerator z),r.denominator*D⟩

/-- Exact reference-state relation, not just equality of interpreted values. -/
theorem rootCompactHorner_reference (z : GaussianDyadicScalar) (D : ℕ) :
    ∀ cs : List ℤ, cs≠[] →
      (gaussianPointHorner z D (cs.map (fun a => (a,0)))).value=
        ⟨gaussianIntegerScale D (rootCompactHorner z D cs).numerator,
          D*(rootCompactHorner z D cs).denominator⟩ := by
  intro cs
  induction cs with
  | nil => simp
  | cons a cs ih =>
    intro _
    cases cs with
    | nil =>
      rw [List.map_cons,List.map_nil,gaussian_point_horner_cons]
      simp [gaussianPointHorner,rootCompactHorner,gaussianScalarAdd,
        gaussianIntegerScale,gaussianIntegerMul]
    | cons b tail =>
      rw [List.map_cons,gaussian_point_horner_cons,ih (by simp)]
      change (⟨gaussianScalarAdd (gaussianIntegerScale ((D*(rootCompactHorner z D (b::tail)).denominator)*D) (a,0))
          (gaussianIntegerMul (gaussianIntegerScale D (rootCompactHorner z D (b::tail)).numerator) z),
          (D*(rootCompactHorner z D (b::tail)).denominator)*D⟩ : GaussianIntegerFraction) = _
      dsimp only [rootCompactHorner]
      congr 1
      · apply Prod.ext <;>
          simp [gaussianScalarAdd,gaussianIntegerScale,gaussianIntegerMul,Nat.cast_mul] <;> ring
      · ring

/-- The finite construction in `NativeRootIntegerHorner` satisfies `rootCompactHorner_denominator` under the displayed hypotheses. -/
theorem rootCompactHorner_denominator (z : GaussianDyadicScalar) (D : ℕ) :
    ∀ cs : List ℤ,(rootCompactHorner z D cs).denominator=D^(cs.length-1) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    cases cs with
    | nil => rfl
    | cons b tail =>
      change (rootCompactHorner z D (b::tail)).denominator*D=_
      rw [ih]
      simp [pow_succ]

/-- The finite construction in `NativeRootIntegerHorner` satisfies `rootCompactHorner_denominator_pos` under the displayed hypotheses. -/
theorem rootCompactHorner_denominator_pos (z : GaussianDyadicScalar) (D : ℕ)
    (cs : List ℤ) (hD : 0<D) : 0<(rootCompactHorner z D cs).denominator := by
  rw [rootCompactHorner_denominator]
  exact Nat.pow_pos hD

/-- The extra D cancels using the existing exact fraction theorem. -/
theorem rootCompactHorner_value (z : GaussianDyadicScalar) (D : ℕ)
    (cs : List ℤ) (hD : 0<D) (hcs : cs≠[]) :
    gaussianPointValue (gaussianPointHorner z D (cs.map (fun a => (a,0)))).value=
      gaussianPointValue (rootCompactHorner z D cs) := by
  rw [rootCompactHorner_reference z D cs hcs]
  rw [gaussian_point_value_fraction,gaussian_point_value_fraction,
    gaussian_fraction_scale _ D _ hD]

/-- The complete original ascending integer coefficient array, with its actual
common-denominator point. Correctness is consumed from main's existing Horner. -/
theorem rootCompactHorner_correct (n : ℕ) (c : Fin (n+1) → ℤ)
    (z : GaussianDyadicScalar) (D : ℕ) (hD : 0<D) :
    gaussianPointValue (rootCompactHorner z D (List.ofFn c))=
      ∑ i : Fin (n+1),gaussianScalarDecode 0 (c i,0)*(gaussianPointValue ⟨z,D⟩)^i.val := by
  have hcs : List.ofFn c≠[] := by
    intro h
    have hl := congrArg List.length h
    simp at hl
  have h := gaussian_point_horner_correct (n+1) (fun i => (c i,0)) z D hD
  have he := rootCompactHorner_value z D (List.ofFn c) hD hcs
  simp only [List.map_ofFn,Function.comp_def] at he
  exact he.symm.trans h.2

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
