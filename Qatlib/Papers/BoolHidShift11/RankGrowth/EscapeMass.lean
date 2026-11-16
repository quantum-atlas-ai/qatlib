/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.SampleCircuit
public import Qatlib.Papers.BoolHidShift11.InputModel.SupportMath

@[expose] public section


/-! # Actual Born mass escaping an orthogonal set

A nonzero orthogonal direction supplies the influence lower bound for the
real two-query output distribution. Selection of that direction from an
arbitrary proper linear span and expected amplified stopping cost are separate.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.RankGrowth.EscapeMass
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample
open Qatlib.Papers.BoolHidShift11.InputModel.SupportMath
open scoped BigOperators

/-- The real Born mass of input samples outside a finite collected set. -/
def escapeProb {n : ℕ} (inst : BHSPInstance n) (W : Finset (Reg n)) : ℝ :=
  ∑ u ∈ Finset.univ.filter (fun u => u∉W),
    ∑ b : Bool, BornProb (GateModel.output inst.f inst.g) (b,u)

/-- Aperiodicity makes every nonzero direction have strictly positive actual influence. -/
theorem directionPos {n : ℕ} (inst : BHSPInstance n) (v : Reg n)
    (hv : v≠ZeroStr n) : 0 < influence (signedFun inst.f) v := by
  have hn : influence (signedFun inst.f) v≠0 := by
    intro h
    exact hv (inst.aperiodic v ((influenceZero inst.f v).mp h))
  exact lt_of_le_of_ne (SampleMath.influenceNonneg _ _) (Ne.symm hn)

/-- Samples odd on an orthogonal direction are outside the collected set. -/
theorem directionMass {n : ℕ} (inst : BHSPInstance n) (W : Finset (Reg n))
    (v : Reg n) (hW : ∀ u∈W, parityDot v u=false) :
    influence (signedFun inst.f) v≤escapeProb inst W := by
  classical
  unfold escapeProb
  simp_rw [SampleCircuit.marginalLaw]
  rw [← SampleMath.crossInfluence _ (SampleMath.signedSquare inst.f) v]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    have ho := (Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro hm
    have he := hW u hm
    rw [ho] at he
    contradiction
  · intro u _ _
    exact sq_nonneg _

/-- The actual circuit's escape mass is at least the nonzero-direction minimum influence. -/
theorem minimumMass {n : ℕ} (inst : BHSPInstance n) (W : Finset (Reg n))
    (v : Reg n) (hv : v≠ZeroStr n) (hW : ∀ u∈W, parityDot v u=false) :
    minInfluence (signedFun inst.f)≤escapeProb inst W :=
  le_trans (SampleMath.minBound _ hv) (directionMass inst W v hW)

/-- An aperiodic input really has positive chance to escape each such orthogonal set. -/
theorem escapePositive {n : ℕ} (inst : BHSPInstance n) (W : Finset (Reg n))
    (v : Reg n) (hv : v≠ZeroStr n) (hW : ∀ u∈W, parityDot v u=false) :
    0<escapeProb inst W :=
  lt_of_lt_of_le (directionPos inst v hv) (directionMass inst W v hW)

end Qatlib.Papers.BoolHidShift11.RankGrowth.EscapeMass
