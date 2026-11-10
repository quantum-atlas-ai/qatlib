/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesDiscriminationSubgoalStat
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.FreshCopyExec.QpeConsumers

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Qatlib.Concepts.CopyEvolution.Discriminate
open Matrix
open scoped Classical ComplexOrder
set_option warningAsError false

private theorem discrimination_basis (d : ℕ) (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (χ : QState (Fin d)) :
    outerProduct χ=V*Matrix.of (fun j k => Inner (fun a => V a j) χ*star (Inner (fun a => V a k) χ))*Vᴴ := by
  have hC : Matrix.of (fun j k => Inner (fun a => V a j) χ*star (Inner (fun a => V a k) χ))=Vᴴ*outerProduct χ*V := by
    ext j k
    exact (twoSpecies_outer_basis d V χ j k).symm
  have hVV : V*Vᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (Matrix.mem_unitaryGroup_iff).mp hV
  rw [hC]
  symm
  calc
    _ = (V*Vᴴ)*outerProduct χ*(V*Vᴴ) := by noncomm_ring
    _ = _ := by rw [hVV]; simp

private theorem discrimination_weight (d : ℕ) (V : Operator d) (χ : QState (Fin d)) (j : Fin d) :
    ((Vᴴ*outerProduct χ*V) j j).re=‖Inner (fun a => V a j) χ‖^2 := by
  rw [twoSpecies_outer_basis]
  rw [mul_comm,RCLike.star_def,← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.ofReal_re,Complex.normSq_eq_norm_sq]

private theorem discrimination_projector_form (d : ℕ) (V : Operator d) (S : Finset (Fin d)) :
    (∑ j ∈ S, outerProduct (fun a => V a j))=
      V*Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0)*Vᴴ := by
  ext a b
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,outerProduct_apply,Matrix.sum_apply,
    Matrix.diagonal_apply,mul_ite,mul_one]
  simp [Finset.sum_ite_mem,Finset.univ_inter]

private theorem discrimination_projector (d : ℕ) (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (S : Finset (Fin d)) :
    (∑ j ∈ S, outerProduct (fun a => V a j))*(∑ j ∈ S, outerProduct (fun a => V a j))=
        (∑ j ∈ S, outerProduct (fun a => V a j)) ∧
      (∑ j ∈ S, outerProduct (fun a => V a j))ᴴ=(∑ j ∈ S, outerProduct (fun a => V a j)) := by
  have hVV : Vᴴ*V=1 := by
    ext j k
    simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,inner_apply,RCLike.star_def]
      using! unitaryColumn_inner d V hV j k
  let A : Operator d := Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0)
  have hA : A*A=A := by
    dsimp only [A]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hs : j ∈ S <;> simp [hs]
  have hAH : Aᴴ=A := by
    dsimp only [A]
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext j
    by_cases hs : j ∈ S <;> simp [hs]
  rw [discrimination_projector_form]
  change (V*A*Vᴴ)*(V*A*Vᴴ)=V*A*Vᴴ ∧ (V*A*Vᴴ)ᴴ=V*A*Vᴴ
  constructor
  · calc
      _ = V*A*(Vᴴ*V)*A*Vᴴ := by noncomm_ring
      _ = V*(A*A)*Vᴴ := by rw [hVV,Matrix.mul_one]; noncomm_ring
      _ = _ := by rw [hA]
  · rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hAH,Matrix.mul_assoc]

private theorem discrimination_born (d : ℕ) (V : Operator d)
    (S : Finset (Fin d)) (χ : QState (Fin d)) :
    (Matrix.trace ((∑ j ∈ S, outerProduct (fun a => V a j))*outerProduct χ)).re=
      ∑ j ∈ S, ‖Inner (fun a => V a j) χ‖^2 := by
  rw [discrimination_projector_form]
  have he : Matrix.trace (V*Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0)*Vᴴ*outerProduct χ)=
      Matrix.trace (Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0)*(Vᴴ*outerProduct χ*V)) := by
    rw [Matrix.mul_assoc (V*Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0)) Vᴴ
        (outerProduct χ),
      Matrix.trace_mul_comm (V*Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0))
        (Vᴴ*outerProduct χ),
      Matrix.trace_mul_comm (Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0))
        (Vᴴ*outerProduct χ*V),
      Matrix.mul_assoc (Vᴴ*outerProduct χ) V
        (Matrix.diagonal (fun j => if j ∈ S then (1 : ℂ) else 0))]
  rw [he]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul,Complex.re_sum]
  have hh (j : Fin d) : ((if j ∈ S then (1 : ℂ) else 0)*(Vᴴ*outerProduct χ*V) j j).re=
      if j ∈ S then ‖Inner (fun a => V a j) χ‖^2 else 0 := by
    split_ifs <;> simp [discrimination_weight]
  simp only [hh,Finset.sum_ite_mem,Finset.univ_inter]

theorem twoSpeciesDiscriminationSubgoal : TwoSpeciesDiscriminationSubgoal := by
  intro d m M n φ ψ hφ hψ hm hM hn V hV x hs χ hχ E
  have hρ := pureStateMixture_density d m φ hφ hm
  have hσ := pureStateMixture_density d m ψ hψ hm
  have hinput := outerProduct_density hχ
  have hevent :=
      two_species_qpe_actual_spectral_label_event d M n hM hn _ _ V x hρ hσ hV hs
      (outerProduct χ) hinput E
  have hprojector := discrimination_projector d V hV (Finset.univ.filter (fun j => 0 < x j))
  refine ⟨hevent.1,hevent.2,discrimination_basis d V hV χ,discrimination_weight d V χ,
    hprojector.1,hprojector.2,discrimination_born d V _ χ,
    twoSpeciesDifference_eigenvalue_abs_le_one d m φ ψ hφ hψ hm V hV x hs,
    twoSpecies_eigenvalue_one_orthogonal d m φ ψ hφ hψ hm V hV x hs,
    twoSpecies_eigenvalue_neg_one_orthogonal d m φ ψ hφ hψ hm V hV x hs⟩

end Qatlib.Concepts.CopyEvolution.Discriminate
