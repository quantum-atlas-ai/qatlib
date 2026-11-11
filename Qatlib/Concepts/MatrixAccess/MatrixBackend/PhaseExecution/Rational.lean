/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Trace
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.GaussianResponseData

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Operand-traced finite rational arithmetic and Gaussian-rational arrays.
The operations below produce their value and ledger together. Power uses
explicit repeated multiplication; it is never a constant-cost exact-complex
oracle. List-cell allocation and abstract indexed visits are charged in the
declared model. List traversal/control and logging overhead do not thereby
receive a host-runtime bound.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- Construction for add in the rational model. -/
def add (a b : ℚ) : Run ℚ := emit (.add a b) (a+b)
/-- Construction for sub in the rational model. -/
def sub (a b : ℚ) : Run ℚ := emit (.sub a b) (a-b)
/-- Construction for mul in the rational model. -/
def mul (a b : ℚ) : Run ℚ := emit (.mul a b) (a*b)
/-- Construction for div in the rational model. -/
def div (a b : ℚ) : Run ℚ := emit (.div a b) (a/b)
/-- Construction for neg in the rational model. -/
def neg (a : ℚ) : Run ℚ := emit (.neg a) (-a)
/-- Construction for abs in the rational model. -/
def abs (a : ℚ) : Run ℚ := emit (.abs a) |a|
/-- Construction for compare in the rational model. -/
def compare (a b : ℚ) : Run Bool := emit (.compare a b) (decide (a≤b))
/-- Construction for cast in the rational model. -/
def cast (n : ℕ) : Run ℚ := emit (.cast n) n
/-- Construction for allocate in the rational model. -/
def allocate {α : Type} (x : α) (xs : List α) : Run (List α) := emit (.allocate 1) (x::xs)
/-- Construction for visit in the rational model. -/
def visit {α : Type} (xs : List α) (i : ℕ) (fallback : α) : Run α :=
  emit (.visit i xs.length) (xs.getD i fallback)

/-- Traced rational addition has the value of the recorded operation. -/
@[simp] theorem add_value (a b : ℚ) : (add a b).value = a+b := by
  simp [add]
/-- Traced rational subtraction has the value of the recorded operation. -/
@[simp] theorem sub_value (a b : ℚ) : (sub a b).value = a-b := by
  simp [sub]
/-- Traced rational multiplication has the value of the recorded operation. -/
@[simp] theorem mul_value (a b : ℚ) : (mul a b).value = a*b := by
  simp [mul]
/-- Traced rational division retains the original total rational semantics. -/
@[simp] theorem div_value (a b : ℚ) : (div a b).value = a/b := by
  simp [div]
/-- Traced rational negation has the value of the recorded operation. -/
@[simp] theorem neg_value (a : ℚ) : (neg a).value = -a := by
  simp [neg]
/-- Traced absolute value has the value of the recorded operation. -/
@[simp] theorem abs_value (a : ℚ) : (abs a).value = |a| := by
  simp [abs]
/-- Traced comparison uses the actual rational operands. -/
@[simp] theorem compare_value (a b : ℚ) : (compare a b).value = decide (a≤b) := by
  simp [compare]
/-- Traced casting preserves the actual natural-number operand. -/
@[simp] theorem cast_value (n : ℕ) : (cast n).value = (n : ℚ) := by
  simp [cast]
/-- One traced allocation returns its actual new finite list cell. -/
@[simp] theorem allocate_value {α : Type} (x : α) (xs : List α) :
    (allocate x xs).value = x::xs := by
  simp [allocate]
/-- A traced finite lookup keeps zero-extension and out-of-range fallback. -/
@[simp] theorem visit_value {α : Type} (xs : List α) (i : ℕ) (fallback : α) :
    (visit xs i fallback).value = xs.getD i fallback := by
  simp [visit]

/-- Construction for power in the rational model. -/
def power (a : ℚ) : ℕ → Run ℚ
  | 0 => pure 1
  | n+1 => do
    let x ← power a n
    mul x a

/-- Explicit repeated rational multiplication computes the original exact power. -/
@[simp] theorem power_value (a : ℚ) (n : ℕ) : (power a n).value = a^n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, mul, pow_succ]

/-- Construction for gaussian Add in the rational model. -/
def gaussianAdd (a b : GaussianRat) : Run GaussianRat := do
  let x ← add a.1 b.1
  let y ← add a.2 b.2
  pure (x,y)

/-- Construction for gaussian Sub in the rational model. -/
def gaussianSub (a b : GaussianRat) : Run GaussianRat := do
  let x ← sub a.1 b.1
  let y ← sub a.2 b.2
  pure (x,y)

/-- Construction for gaussian Mul in the rational model. -/
def gaussianMul (a b : GaussianRat) : Run GaussianRat := do
  let ac ← mul a.1 b.1
  let bd ← mul a.2 b.2
  let ad ← mul a.1 b.2
  let bc ← mul a.2 b.1
  let x ← sub ac bd
  let y ← add ad bc
  pure (x,y)

/-- Construction for gaussian Conj in the rational model. -/
def gaussianConj (a : GaussianRat) : Run GaussianRat := do
  let y ← neg a.2
  pure (a.1,y)

/-- Traced Gaussian addition preserves the exact pinned rational-pair value. -/
@[simp] theorem gaussianAdd_value (a b : GaussianRat) :
    (gaussianAdd a b).value = gadd a b := by
  simp [gaussianAdd, gadd]

/-- Traced Gaussian subtraction preserves the exact pinned rational-pair value. -/
@[simp] theorem gaussianSub_value (a b : GaussianRat) :
    (gaussianSub a b).value = gsub a b := by
  simp [gaussianSub, gsub]

/-- Traced Gaussian multiplication preserves the exact pinned rational-pair value. -/
@[simp] theorem gaussianMul_value (a b : GaussianRat) :
    (gaussianMul a b).value = gmul a b := by
  simp [gaussianMul, gmul]

/-- Traced Gaussian conjugation preserves the exact pinned rational-pair value. -/
@[simp] theorem gaussianConj_value (a : GaussianRat) :
    (gaussianConj a).value = gconj a := by
  simp [gaussianConj, gconj]

/-- Each actual Gaussian multiplication emits its six rational operations. -/
theorem gaussianMul_events_length (a b : GaussianRat) :
    (gaussianMul a b).events.length = 6 := by
  simp [gaussianMul, mul, sub, add]

/-- Construction for map Run in the rational model. -/
def mapRun {α β : Type} (f : α → Run β) : List α → Run (List β)
  | [] => pure []
  | a::rest => do
    let b ← f a
    let bs ← mapRun f rest
    allocate b bs

/-- Traced mapping performs the same finite value transformation. -/
@[simp] theorem mapRun_value {α β : Type} (f : α → Run β) (xs : List α) :
    (mapRun f xs).value = xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => simp [mapRun]
  | cons x xs ih => simp [mapRun, ih, allocate]

/-- Construction for add Arrays in the rational model. -/
def addArrays : List GaussianRat → List GaussianRat → Run (List GaussianRat)
  | [],ys => pure ys
  | xs,[] => pure xs
  | x::xs,y::ys => do
    let z ← gaussianAdd x y
    let rest ← addArrays xs ys
    allocate z rest

/-- Construction for sub Arrays in the rational model. -/
def subArrays : List GaussianRat → List GaussianRat → Run (List GaussianRat)
  | [],ys => mapRun (gaussianSub gzero) ys
  | xs,[] => pure xs
  | x::xs,y::ys => do
    let z ← gaussianSub x y
    let rest ← subArrays xs ys
    allocate z rest

/-- Construction for shift Array in the rational model. -/
def shiftArray (xs : List GaussianRat) : Run (List GaussianRat) := allocate gzero xs
/-- Construction for scale Array in the rational model. -/
def scaleArray (z : GaussianRat) (xs : List GaussianRat) : Run (List GaussianRat) :=
  mapRun (gaussianMul z) xs

/-- Traced zero-extended array addition preserves the original finite algorithm. -/
@[simp] theorem addArrays_value (xs ys : List GaussianRat) :
    (addArrays xs ys).value = gaddList xs ys := by
  induction xs generalizing ys with
  | nil => simp [addArrays, gaddList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addArrays, gaddList]
    | cons y ys => simp [addArrays, gaddList, ih, allocate]

/-- Traced zero-extended subtraction includes every original tail operation. -/
@[simp] theorem subArrays_value (xs ys : List GaussianRat) :
    (subArrays xs ys).value = gsubList xs ys := by
  induction xs generalizing ys with
  | nil => simp [subArrays, gsubList]
  | cons x xs ih =>
    cases ys with
    | nil => simp [subArrays, gsubList]
    | cons y ys => simp [subArrays, gsubList, ih, allocate]

/-- Traced shifting allocates the actual leading zero. -/
@[simp] theorem shiftArray_value (xs : List GaussianRat) :
    (shiftArray xs).value = gshift xs := by simp [shiftArray, gshift]

/-- Traced scaling evaluates and charges every actual Gaussian product. -/
@[simp] theorem scaleArray_value (z : GaussianRat) (xs : List GaussianRat) :
    (scaleArray z xs).value = gscale z xs := by
  simp [scaleArray, gscale]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
