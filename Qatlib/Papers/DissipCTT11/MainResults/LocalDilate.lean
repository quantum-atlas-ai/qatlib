/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring

@[expose] public section


/-! # A local channel's unitary dilation with the same bounded environment

Theorem 8 uses a local dimension D=d^k and an environment of dimension at
most D^2. The generic public clean completion permits additional padding;
here equal input/output dimensions allow unitary completion on the very
same D-by-environment space. No Solovay--Kitaev gate budget is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Papers.DissipCTT11.MainResults.LocalDilate
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring

/-- A positive-dimensional channel has an actual unitary dilation using its
original environment of dimension at most D squared, with no further padding. -/
theorem localDilation {D : ℕ} [NeZero D] (T : QuantumChannel D D) :
    ∃ (env : ℕ) (V : Matrix (Fin D × Fin env) (Fin D) ℂ)
      (e0 : Fin env) (U : Matrix (Fin D × Fin env) (Fin D × Fin env) ℂ),
      env ≤ D * D ∧ StinespringDilation T.map env V ∧
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      ∀ ψ : Fin D → ℂ,
        U *ᵥ (fun x => if x.2 = e0 then ψ x.1 else 0) = V *ᵥ ψ := by
  classical
  obtain ⟨env,V,henv,hV,_⟩ := g2.1 D D T
  have hpos : 0 < env := by
    by_contra! h
    have hz : env = 0 := Nat.eq_zero_of_le_zero h
    subst env
    have h1 := congrArg (fun M : Operator D => M 0 0) hV.1
    simp [Matrix.mul_apply] at h1
  let e0 : Fin env := ⟨0,hpos⟩
  let emb : Fin D → Fin D × Fin env := fun j => (j,e0)
  have hemb : Function.Injective emb := by
    intro i j h
    exact congrArg Prod.fst h
  obtain ⟨U,hU,hU',hcol⟩ := exists_unitary_extend_cols V emb hemb hV.1
  refine ⟨env,V,e0,U,henv,hV,hU,hU',?_⟩
  intro ψ
  funext x
  simp only [emb] at hcol
  simp [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,mul_ite,hcol]

end Qatlib.Papers.DissipCTT11.MainResults.LocalDilate
