/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.ActualWord
import Qatlib.Foundations.TimeEvolution.DysonError.DiscreteGronwall
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ProjectorQAOA26.StageStability
open scoped Matrix Matrix.Norms.L2Operator
open Qatlib.Foundations.TimeEvolution.DysonError
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

inductive MixerChoice (I : Type) [DecidableEq I] where
  | learned
  | fixed (generator : Matrix I I ℂ) (hermitian : generatorᴴ=generator)

structure StageData (I : Type) [DecidableEq I] where
  cost : Matrix I I ℂ
  hermitian : costᴴ=cost
  layers : List MixerLayer
  mixer : MixerChoice I

def stageGenerator (stage : StageData I) (previous : I → ℂ) : Matrix I I ℂ :=
  match stage.mixer with
  | .learned => learnedGenerator previous
  | .fixed generator _ => generator

omit [Fintype I] [Nonempty I] in

theorem stageGenerator_hermitian (stage : StageData I) (previous : I → ℂ) :
    (stageGenerator stage previous)ᴴ=stageGenerator stage previous := by
  cases hm : stage.mixer with
  | learned => simpa only [stageGenerator,hm] using! learnedGenerator_hermitian previous
  | fixed generator h => simpa only [stageGenerator,hm] using! h

def stageWord (stage : StageData I) (previous : I → ℂ) : Matrix I I ℂ :=
  chronologicalWord stage.layers (stageGenerator stage previous) stage.cost

omit [Nonempty I] in

theorem stageWord_unitary (stage : StageData I) (previous : I → ℂ) :
    stageWord stage previous∈Matrix.unitaryGroup I ℂ :=
  chronologicalWord_unitary stage.layers _ _ (stageGenerator_hermitian stage previous) stage.hermitian

def stageGain (stage : StageData I) : ℝ := match stage.mixer with
  | .learned => (stage.layers.map (fun layer => |layer.β|)).sum
  | .fixed _ _ => 0

omit [Fintype I] [Nonempty I] in

theorem stageGain_nonneg (stage : StageData I) : 0 ≤ stageGain stage := by
  cases hm : stage.mixer with
  | fixed generator h => simp only [stageGain,hm,le_refl]
  | learned =>
    simp only [stageGain,hm]
    exact List.sum_nonneg (fun x hx => by obtain ⟨l,_,rfl⟩:=List.mem_map.mp hx;exact abs_nonneg _)

theorem stageWord_error (stage : StageData I) (u v : I → ℂ)
    (hu : l2norm u=1) (hv : l2norm v=1) :
    ‖stageWord stage u-stageWord stage v‖ ≤ stageGain stage*phaseDist u v := by
  cases hm : stage.mixer with
  | learned => simpa only [stageWord,stageGenerator,stageGain,hm] using!
      learned_word_error stage.layers stage.cost stage.hermitian u v hu hv
  | fixed generator h => simp [stageWord,stageGenerator,stageGain,hm]

def actualStates (stages : ℕ → StageData I) (initial : I → ℂ) : ℕ → I → ℂ
  | 0 => initial
  | n+1 => stageWord (stages n) (actualStates stages initial n)*ᵥactualStates stages initial n

omit [Nonempty I] in

theorem actualStates_normalized (stages : ℕ → StageData I) (initial : I → ℂ) (hi : l2norm initial=1) :
    ∀ n,l2norm (actualStates stages initial n)=1
  | 0 => hi
  | n+1 => by rw [actualStates,l2norm_mulVec (stageWord_unitary _ _),actualStates_normalized stages initial hi n]

theorem actual_stage_error (stage : StageData I) (u v target : I → ℂ)
    (hu : l2norm u=1) (hv : l2norm v=1) (eps : ℝ)
    (hideal : phaseDist (stageWord stage v*ᵥv) target≤eps) :
    phaseDist (stageWord stage u*ᵥu) target≤(1+stageGain stage)*phaseDist u v+eps := by
  have htri:=phaseDist_triangle (stageWord stage u*ᵥu) (stageWord stage u*ᵥv) target
  have htri2:=phaseDist_triangle (stageWord stage u*ᵥv) (stageWord stage v*ᵥv) target
  rw [phaseDist_mulVec (stageWord_unitary stage u)] at htri
  have hop:=(phaseDist_mulVec_perturb (stageWord stage u) (stageWord stage v) v hv).trans
    (stageWord_error stage u v hu hv)
  linarith

theorem actual_frozen_stage_stability (stages : ℕ → StageData I) (initial : I → ℂ)
    (hi : l2norm initial=1) (ideal : ℕ → I → ℂ) (hnorm : ∀ n,l2norm (ideal n)=1)
    (hstart : ideal 0=initial) (eps : ℕ → ℝ)
    (hideal : ∀ n,phaseDist (stageWord (stages n) (ideal n)*ᵥideal n) (ideal (n+1))≤eps (n+1))
    (m : ℕ) :
    phaseDist (actualStates stages initial m) (ideal m)≤
      propagatedError eps (fun j => stageGain (stages (j-1))) m := by
  apply error_le_propagated (fun n => phaseDist (actualStates stages initial n) (ideal n)) eps
    (fun j => stageGain (stages (j-1)))
  · rw [hstart,actualStates]
    have h:=phaseDist_sq initial initial
    have habs : l2abs initial initial=1 := by rw [l2abs,l2inner_self_of_norm hi];norm_num
    rw [hi,habs] at h
    nlinarith [phaseDist_nonneg initial initial]
  · intro j
    exact stageGain_nonneg _
  · intro n
    simpa only [actualStates,Nat.add_sub_cancel] using! actual_stage_error (stages n)
      (actualStates stages initial n) (ideal n) (ideal (n+1))
      (actualStates_normalized stages initial hi n) (hnorm n) (eps (n+1)) (hideal n)
end Qatlib.Papers.ProjectorQAOA26.StageStability
