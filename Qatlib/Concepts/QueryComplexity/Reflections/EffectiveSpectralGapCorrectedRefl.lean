/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.Reflections.EffectiveSpectralGapCorrectedStat
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.BlockEncoding.LinearCombination

/-!
# Effective spectral gap with a nonzero witness

Proves `EffectiveSpectralGapCorrected` using a nonzero vector in the kernel of the adjoint
biadjacency and a lower bound on its target overlap. The module establishes complete-frame
Parseval, the Hermitian adjacency identity, and the image of the extended witness at the root.

The resulting root spectral-mass bound is the corrected effective-gap formulation associated
with [Reichardt2011].

## Main statements

* `complete_frame_parseval`: complete frame coefficients preserve squared norm.
* `effective_gap_witness_image`: the extended kernel witness maps to its target overlap times
  the root ket.
* `effectiveSpectralGapCorrected`: root mass below energy `γ` is at most `8 * γ^2 / δ`.

## References

* [Reichardt, 2011][Reichardt2011]
-/

open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.Reflections
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators

/-- A complete frame satisfying `V * Vᴴ = 1` preserves squared norm when taking frame
coefficients with `Vᴴ`. -/
theorem complete_frame_parseval {S J : Type} [Fintype S] [DecidableEq S]
    [Fintype J] [DecidableEq J] (V : Matrix S J ℂ) (hV : V*Vᴴ=1) (z : QState S) :
    ∑ i,‖(Vᴴ*ᵥz) i‖^2=∑ r,‖z r‖^2 := by
  have hi : IsIsometry Vᴴ := by simpa [IsIsometry] using hV
  simpa [MeasureProb,BornProb] using
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.measureProb_mulVec hi z

/-- The effective-gap adjacency matrix is Hermitian. -/
theorem effective_gap_adjacency_hermitian {T U : Type} [DecidableEq T] [DecidableEq U]
    (B : Matrix T U ℂ) (t : QState T) : (effectiveGapAdjacency B t).IsHermitian := by
  ext p q
  cases p with
  | inl p=>cases q with
    | inl q=>simp [effectiveGapAdjacency,Matrix.conjTranspose_apply]
    | inr q=>cases q <;> simp [effectiveGapAdjacency,Matrix.conjTranspose_apply]
  | inr p=>cases p <;> cases q <;> simp [effectiveGapAdjacency,Matrix.conjTranspose_apply]

/-- If `Bᴴ` annihilates `ψ`, the effective-gap adjacency sends its row-side embedding to the
root basis vector scaled by `Inner t ψ`. -/
theorem effective_gap_witness_image {T U : Type} [Fintype T] [DecidableEq T]
    [Fintype U] [DecidableEq U] (B : Matrix T U ℂ) (t ψ : QState T) (hψ : Bᴴ*ᵥψ=0) :
    effectiveGapAdjacency B t*ᵥSum.elim ψ 0=Qatlib.Foundations.PureStateMath.Inner t ψ • Ket (Sum.inr (Sum.inl ())) := by
  ext p
  cases p with
  | inl p=>simp [effectiveGapAdjacency,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Ket]
  | inr p=>cases p with
    | inl p=>cases p;simp [effectiveGapAdjacency,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Qatlib.Foundations.PureStateMath.Inner,Ket]
    | inr p=>
      have he:=congrFun hψ p
      simpa [effectiveGapAdjacency,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
        Matrix.conjTranspose_apply,Ket] using he

/-- A nonzero kernel witness with the specified overlap lower bound yields root spectral mass at
energies at most `γ` bounded by `8 * γ^2 / δ`. This is the corrected effective-gap
formulation associated with [Reichardt2011]. -/
theorem effectiveSpectralGapCorrected : EffectiveSpectralGapCorrected := by
  intro T U _ _ _ _ B t ψ δ hδ hn hker hover γ hγ k V ρ _hV hVV hEV
  let M:=effectiveGapAdjacency B t
  let z : QState (T ⊕ (Unit ⊕ U)):=Sum.elim ψ 0
  let α:=Qatlib.Foundations.PureStateMath.Inner t ψ
  let q:=Vᴴ*ᵥz
  let low:=∑ i : Fin k,if |ρ i| ≤ γ then ‖V (Sum.inr (Sum.inl ())) i‖^2 else 0
  have hlow : 0 ≤ low := Finset.sum_nonneg fun i _=>by split_ifs <;> positivity
  have hVE : Vᴴ*M=Matrix.diagonal (fun i=>(ρ i : ℂ))*Vᴴ := by
    have he:=congrArg Matrix.conjTranspose hEV
    simpa [M,Matrix.conjTranspose_mul,Matrix.diagonal_conjTranspose,
      (effective_gap_adjacency_hermitian B t).eq,Pi.star_def] using he
  have hMq : Matrix.diagonal (fun i=>(ρ i : ℂ))*ᵥq=α • (Vᴴ*ᵥKet (Sum.inr (Sum.inl ()))) := by
    dsimp only [q]
    rw [Matrix.mulVec_mulVec,← hVE,← Matrix.mulVec_mulVec]
    rw [show M*ᵥz=α • Ket (Sum.inr (Sum.inl ())) from effective_gap_witness_image B t ψ hker]
    rw [Matrix.mulVec_smul]
  have hcoeff (i : Fin k) : (ρ i : ℂ)*q i=α*star (V (Sum.inr (Sum.inl ())) i) := by
    have he:=congrFun hMq i
    have hk : (Vᴴ*ᵥKet (Sum.inr (Sum.inl ()))) i=star (V (Sum.inr (Sum.inl ())) i) := by
      simp [Matrix.mulVec,dotProduct,Ket,Matrix.conjTranspose_apply]
    simpa only [Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul,hk] using he
  have hterm (i : Fin k) :
      ‖α‖^2*(if |ρ i| ≤ γ then ‖V (Sum.inr (Sum.inl ())) i‖^2 else 0) ≤ γ^2*‖q i‖^2 := by
    by_cases hi : |ρ i| ≤ γ
    · rw [if_pos hi]
      have he:=congrArg (fun x : ℂ=>‖x‖^2) (hcoeff i)
      simp only [norm_mul,mul_pow,norm_star,Complex.norm_real,Real.norm_eq_abs,sq_abs] at he
      have hρ : (ρ i)^2 ≤ γ^2 := by nlinarith [sq_abs (ρ i),abs_nonneg (ρ i)]
      rw [← he]
      exact mul_le_mul_of_nonneg_right hρ (sq_nonneg _)
    · rw [if_neg hi,mul_zero]
      positivity
  have htotal : ‖α‖^2*low ≤ γ^2*(∑ r : T,‖ψ r‖^2) := by
    have hp : ∑ i : Fin k,‖q i‖^2=∑ r : T,‖ψ r‖^2 := by
      simpa [q,z,Fintype.sum_sum_type] using complete_frame_parseval V hVV z
    calc
      _ = ∑ i : Fin k,‖α‖^2*(if |ρ i| ≤ γ then ‖V (Sum.inr (Sum.inl ())) i‖^2 else 0) := Finset.mul_sum _ _ _
      _ ≤ ∑ i : Fin k,γ^2*‖q i‖^2 := Finset.sum_le_sum fun i _=>hterm i
      _ = _ := by rw [← Finset.mul_sum,hp]
  have hnorm : 0 < ∑ r : T,‖ψ r‖^2 := by
    have hex : ∃ r,ψ r≠0 := by
      by_contra hh
      push Not at hh
      exact hn (funext hh)
    obtain ⟨r,hr⟩:=hex
    have hpos : 0 < ‖ψ r‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
    have hs:=Finset.single_le_sum (f := fun r : T=>‖ψ r‖^2)
      (fun r _=>sq_nonneg _) (Finset.mem_univ r)
    exact hpos.trans_le hs
  have hb : δ*low ≤ γ^2 := by
    apply (mul_le_mul_iff_right₀ hnorm).mp
    have hh:=mul_le_mul_of_nonneg_right hover hlow
    dsimp only [α] at htotal
    nlinarith
  apply (le_div_iff₀ hδ).mpr
  change low*δ ≤ 8*γ^2
  nlinarith [sq_nonneg γ]
end Qatlib.Concepts.QueryComplexity.Reflections
