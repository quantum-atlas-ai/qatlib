/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.FieldSimp

@[expose] public section


/-! # The full aligned-basis transporter trace identity

Fixed source1012.2112v1, Lemma27. The actual matrices from the historical
target are retained, with explicit identity-tensor transport. No final
trace factorization, projector equation or source query bound is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Kronecker
namespace Qatlib.Papers.SymmetryAdv10.MainResults.AlignedTrace

/-- The exact aligned isotypic matrix in the original trace target. -/
def PiIso (d m : ℕ) : Matrix (Fin d × Fin (m+1)) (Fin d × Fin (m+1)) ℂ :=
  fun p q => if p.1=q.1 ∧ p.2=0 ∧ q.2=0 then 1 else 0

/-- The exact aligned rank-one multiplicity matrix in the original target. -/
def PiMu (d : ℕ) {m : ℕ} (a : Fin (m+1) → ℂ) :
    Matrix (Fin d × Fin (m+1)) (Fin d × Fin (m+1)) ℂ :=
  fun p q => if p.1=q.1 then a p.2*star (a q.2) else 0

/-- The exact aligned transporter, with arbitrary original complex coefficients. -/
def PiTrans (d : ℕ) {m : ℕ} (b c : Fin (m+1) → ℂ) :
    Matrix (Fin d × Fin (m+1)) (Fin d × Fin (m+1)) ℂ :=
  fun p q => if p.1=q.1 then b p.2*star (c q.2) else 0

/-- Tensor an actual multiplicity matrix with the d-dimensional identity. -/
def lift {m : ℕ} (d : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :=
  (1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ A

/-- Select the distinguished multiplicity coordinate zero. -/
def e00 (m : ℕ) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  fun i j => if i=0 ∧ j=0 then 1 else 0

/-- The actual rank-one multiplicity entries. -/
def outer {m : ℕ} (a b : Fin (m+1) → ℂ) : Matrix (Fin (m+1)) (Fin (m+1)) ℂ :=
  fun i j => a i*star (b j)

/-- Identity-tensor lifting preserves actual matrix multiplication. -/
theorem liftMul {m : ℕ} (d : ℕ) (A B : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    lift d A*lift d B=lift d (A*B) := by
  simp only [lift,←Matrix.mul_kronecker_mul,Matrix.one_mul]

/-- The actual lifted trace is dimension times multiplicity trace. -/
theorem liftTrace {m : ℕ} (d : ℕ) (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    (lift d A).trace=(d : ℂ)*A.trace := by
  simp [lift,Matrix.trace_kronecker]

/-- The original isotypic entries are exactly the lifted coordinate projector. -/
theorem isoLift (d m : ℕ) : PiIso d m=lift d (e00 m) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : i=k <;> simp [PiIso,lift,e00,h]

/-- The original middle entries are the lifted actual rank-one matrix. -/
theorem muLift {m : ℕ} (d : ℕ) (a : Fin (m+1) → ℂ) : PiMu d a=lift d (outer a a) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : i=k <;> simp [PiMu,lift,outer,h]

/-- The original transporter entries are exactly the lifted multiplicity transporter. -/
theorem transLift {m : ℕ} (d : ℕ) (b c : Fin (m+1) → ℂ) :
    PiTrans d b c=lift d (outer b c) := by
  ext ⟨i,j⟩ ⟨k,l⟩
  by_cases h : i=k <;> simp [PiTrans,lift,outer,h]

/-- Coordinate selection computes the full actual matrix sandwich. -/
theorem select {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    e00 m*A*e00 m=A 0 0 • e00 m := by
  ext i j
  by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    simp [e00,Matrix.mul_apply,Matrix.smul_apply,hi,hj]

/-- The actual selected trace is the zero-coordinate entry. -/
theorem selectedTrace {m : ℕ} (A : Matrix (Fin (m+1)) (Fin (m+1)) ℂ) :
    (e00 m*A).trace=A 0 0 := by
  simp [Matrix.trace,Matrix.mul_apply,e00,ite_and]

/-- The entire historical aligned-basis Lemma27 formula holds for every original dimension and coefficient vector. -/
theorem wholeOriginal {d m : ℕ} (hd : (d : ℂ)≠0) (a b c : Fin (m+1) → ℂ) :
    (PiIso d m*PiMu d a*PiIso d m*PiTrans d b c).trace=
      (1/(d : ℂ))*(PiIso d m*PiMu d a).trace*(PiIso d m*PiTrans d b c).trace := by
  simp only [isoLift,muLift,transLift,liftMul]
  rw [liftTrace,liftTrace,liftTrace,select,Matrix.smul_mul,Matrix.trace_smul]
  simp only [selectedTrace,smul_eq_mul]
  field_simp [hd]

end Qatlib.Papers.SymmetryAdv10.MainResults.AlignedTrace
