/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.L2Dynamics.PhaseShears.Word
import Qatlib.Papers.NonhomogPDE18.WaveModel.Defs
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory
namespace Qatlib.Papers.NonhomogPDE18.WaveModel
open Qatlib.Papers.NonhomogPDE18
open Qatlib.Papers.NonhomogPDE18.WaveModel
abbrev H := Qatlib.Foundations.L2Dynamics.PhaseShears.Word.H

def pg (c : ℝ) (i : Mode) (d : ℕ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  .phase (fun x=>c*(x i)^d) (by fun_prop)

def sg (i m : Mode) (d : ℕ) (s : ℝ) : Qatlib.Foundations.L2Dynamics.PhaseShears.Word.Gate :=
  .shift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m d s) (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control_measurable i m d s)

theorem sg_pos (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 1 1)=subOp (sh i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 1 1) x)=f (sh i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [sh]

theorem sg_neg (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 1 (-1))=subOp (shInv i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 1 (-1)) x)=f (shInv i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [shInv,sub_eq_add_neg]

theorem sg_square_pos (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 2 1)=subOp (shSq i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 2 1) x)=f (shSq i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [shSq]

theorem sg_square_neg (i m : Mode) (h : m≠i) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (sg i m 2 (-1))=subOp (shSqInv i m) := by
  funext f x
  change f (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift i (Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.control i m 2 (-1)) x)=f (shSqInv i m x)
  rw [Qatlib.Foundations.L2Dynamics.PhaseShears.Shear.coordinateShift_control i m h]
  simp [shSqInv,sub_eq_add_neg]

theorem pg_wave (c : ℝ) (i : Mode) (d : ℕ) :
    Qatlib.Foundations.L2Dynamics.PhaseShears.Word.waveGate (pg c i d)=multOp (cexpI (fun x=>c*(x i)^d)) := rfl
end Qatlib.Papers.NonhomogPDE18.WaveModel
