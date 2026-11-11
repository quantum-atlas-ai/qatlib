/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.L2Dynamics.PhaseShears.Word
import Qatlib.Papers.NonhomogPDE18.WaveModel.Defs

/-!
# Native phase and shear primitives

Connects polynomial phase gates and controlled shear gates to their wave-function
interpretations. The constructors `pg` and `sg` supply the native primitives used in the cubic
and quartic decompositions. See [ArrazolaEtAl2019].

## Main statements

* `pg_wave`: a polynomial phase gate acts by phase multiplication.
* `sg_pos`: a unit linear shear gate acts by the corresponding substitution.
* `sg_square_neg`: a negative quadratic shear realizes the inverse substitution.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
namespace Qatlib.Papers.NonhomogPDE18.WaveModel
open Qatlib.Papers.NonhomogPDE18
open Qatlib.Papers.NonhomogPDE18.WaveModel
/-- The L2 Hilbert space used for native phase and shear gate words. -/
abbrev H := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.H

/-- The native phase gate with real exponent `c * (x i) ^ d`. -/
def pg (c : ℝ) (i : Mode) (d : ℕ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  .phase (fun x=>c*(x i)^d) (by fun_prop)

/-- The native shear gate targeting mode `i` with the degree-`d` control from mode `m` and
coefficient `s`. -/
def sg (i m : Mode) (d : ℕ) (s : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  .shift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m d s) (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control_measurable i m d s)

/-- For distinct modes, the positive unit linear shear gate has wave interpretation `subOp (sh i
m)`. -/
theorem sg_pos (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 1 1)=subOp (sh i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 1 1) x)=f (sh i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [sh]

/-- For distinct modes, the negative unit linear shear gate has wave interpretation `subOp
(shInv i m)`. -/
theorem sg_neg (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 1 (-1))=subOp (shInv i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 1 (-1)) x)=f (shInv i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [shInv,sub_eq_add_neg]

/-- For distinct modes, the positive unit quadratic shear gate has wave interpretation `subOp
(shSq i m)`. -/
theorem sg_square_pos (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 2 1)=subOp (shSq i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 2 1) x)=f (shSq i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [shSq]

/-- For distinct modes, the negative unit quadratic shear gate has wave interpretation `subOp
(shSqInv i m)`. -/
theorem sg_square_neg (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 2 (-1))=subOp (shSqInv i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 2 (-1)) x)=f (shSqInv i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [shSqInv,sub_eq_add_neg]

/-- The wave interpretation of a polynomial phase gate is multiplication by its complex phase
function. -/
theorem pg_wave (c : ℝ) (i : Mode) (d : ℕ) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (pg c i d)=multOp (cexpI (fun x=>c*(x i)^d)) := rfl
end Qatlib.Papers.NonhomogPDE18.WaveModel
