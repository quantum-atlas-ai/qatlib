/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteSpectrumConsumers

/-!
# Bipartite τ maps and eigenspace correspondence

This module defines `bipartiteTauLinear` and proves the source-to-walk correspondence for two
isometric frames. For `0 < lam < 1`, each signed τ map gives a linear equivalence from the
discriminant eigenspace to the corresponding walk eigenspace on the combined frame range, and
the distinct signs contribute twice the source dimension.

Endpoint transport uses the combined-frame map at discriminant eigenvalues one and zero. These
equivalences produce `bipartite_labeled_busy_spectral_frame`, an orthonormal eigenframe labeled
by its source vectors, in the spectral framework of [Szegedy2004].

## Main statements

* `bipartite_interior_tau_preimage`: nonzero interior sources for walk eigenvectors.
* `bipartite_tau_eigenspace_pair_equivalence`: signed equivalences and dimension formula.
* `bipartite_labeled_busy_spectral_frame`: complete source-labeled frame on the combined range.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralFilter.BusySpectrum

namespace Qatlib.Concepts.WalkSearch.TauEmbedding
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The signed linear τ map combining the left frame image with the right frame image scaled by
`-lam ± i * sqrt (1 - lam^2)`. -/
noncomputable def bipartiteTauLinear {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ) (s : Bool) :
    QState (I⊕J) →ₗ[ℂ] QState H :=
  (Matrix.mulVecLin A).comp (LinearMap.funLeft ℂ ℂ Sum.inl) +
    (-(lam:ℂ)+(if s then Complex.I else -Complex.I)*(Real.sqrt (1-lam^2):ℂ)) •
      ((Matrix.mulVecLin B).comp (LinearMap.funLeft ℂ ℂ Sum.inr))

variable {H I J : Type} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The signed complex coefficient `-lam ± i * sqrt (1 - lam^2)` in the bipartite τ map. -/
private def tauCoeff (lam : ℝ) (s : Bool) : ℂ :=
  -(lam : ℂ) + (if s then Complex.I else -Complex.I) * (Real.sqrt (1-lam^2) : ℂ)

/-- For `0 < lam < 1`, the τ coefficient squares to the associated walk phase, satisfies the
stated quadratic identity, is nonzero, and gives a phase different from one. -/
private theorem tau_coeff_laws (lam : ℝ) (s : Bool) (hl : 0 < lam) (hu : lam < 1) :
    tauCoeff lam s * tauCoeff lam s = bipartitePhase lam s ∧
    2 * (lam : ℂ) * tauCoeff lam s + 1 = -bipartitePhase lam s ∧
    tauCoeff lam s ≠ 0 ∧ bipartitePhase lam s ≠ 1 := by
  have hp : 0 < 1-lam^2 := by nlinarith
  have hr2 := Real.sq_sqrt hp.le
  simp only [pow_two] at hr2
  have hr : 0 < Real.sqrt (1-lam^2) := Real.sqrt_pos.mpr hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases s <;> apply Complex.ext <;>
      simp [tauCoeff, bipartitePhase, Complex.mul_re, Complex.mul_im, pow_two] <;>
      nlinarith only [hr2]
  · cases s <;> apply Complex.ext <;>
      simp [tauCoeff, bipartitePhase, Complex.mul_re, Complex.mul_im, pow_two] <;> ring
  · intro he
    have hh := congrArg Complex.re he
    cases s <;> simp [tauCoeff, Complex.mul_re] at hh <;> linarith
  · intro he
    have hh := congrArg Complex.im he
    cases s <;> simp [bipartitePhase, pow_two, Complex.mul_im, Complex.mul_re] at hh
    all_goals
      simp only [pow_two] at hr
      rcases hh with he | he <;> linarith

/-- Evaluate the linear τ map as the left frame image plus the τ coefficient times the right
frame image. -/
private theorem tau_apply (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (lam : ℝ) (s : Bool) (u : QState (I⊕J)) :
    bipartiteTauLinear A B lam s u =
      A*ᵥ(fun i => u (.inl i)) + tauCoeff lam s • (B*ᵥ(fun j => u (.inr j))) := rfl

/-- Every vector in an interior signed-phase walk eigenspace has a discriminant eigenvector
preimage under the corresponding τ map. -/
private theorem tau_interior_preimage (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (w : QState H) (lam : ℝ) (s : Bool)
    (hl : 0 < lam) (hu : lam < 1)
    (hw : bipartiteWalk A B*ᵥw = bipartitePhase lam s • w) :
    ∃ u : QState (I⊕J), bipartiteDiscriminant A B*ᵥu = (lam : ℂ) • u ∧
      bipartiteTauLinear A B lam s u = w := by
  let z := bipartitePhase lam s
  let c := tauCoeff lam s
  let x := Aᴴ*ᵥw
  let y := Bᴴ*ᵥw
  let p := (A*Aᴴ)*ᵥw
  let q := (B*Bᴴ)*ᵥw
  have hc := tau_coeff_laws lam s hl hu
  have hcz : c*c=z := hc.1
  have hline : 2*(lam:ℂ)*c+1=-z := hc.2.1
  have hc0 : c ≠ 0 := hc.2.2.1
  have hz1 : 1-z ≠ 0 := sub_ne_zero.mpr hc.2.2.2.symm
  have hQ : IsOrthogonalProjector (B*Bᴴ) := rangeProjector_isOrthogonalProjector hB
  have hr : ReflectionAbout (B*Bᴴ)*ᵥ(bipartiteWalk A B*ᵥw) =
      ReflectionAbout (A*Aᴴ)*ᵥw := by
    rw [Matrix.mulVec_mulVec,bipartiteWalk,← Matrix.mul_assoc,
      reflectionAbout_mul_self hQ,Matrix.one_mul]
  rw [hw, Matrix.mulVec_smul, reflectionAbout_mulVec, reflectionAbout_mulVec] at hr
  have hproj : (2:ℂ)•p - (2*z)•q = (1-z)•w := by
    calc
      _ = ((2:ℂ)•p-w)-z•((2:ℂ)•q-w)+(1-z)•w := by module
      _ = _ := by rw [← hr]; module
  have hax : Aᴴ*ᵥp=x := by
    rw [Matrix.mulVec_mulVec,show Aᴴ*(A*Aᴴ)=Aᴴ from by
      rw [← Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.one_mul]]
  have hby : Bᴴ*ᵥq=y := by
    rw [Matrix.mulVec_mulVec,show Bᴴ*(B*Bᴴ)=Bᴴ from by
      rw [← Matrix.mul_assoc,show Bᴴ*B=1 from hB,Matrix.one_mul]]
  have hAeq := congrArg (fun v : QState H => Aᴴ*ᵥv) hproj
  have hBeq := congrArg (fun v : QState H => Bᴴ*ᵥv) hproj
  (try dsimp only at hAeq hBeq)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hax] at hAeq
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, hby] at hBeq
  have hAy : Aᴴ*ᵥq=(Aᴴ*B)*ᵥy := by
    change Aᴴ*ᵥ((B*Bᴴ)*ᵥw)=(Aᴴ*B)*ᵥ(Bᴴ*ᵥw)
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
  have hBx : Bᴴ*ᵥp=(Bᴴ*A)*ᵥx := by
    change Bᴴ*ᵥ((A*Aᴴ)*ᵥw)=(Bᴴ*A)*ᵥ(Aᴴ*ᵥw)
    simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
  rw [hAy] at hAeq
  rw [hBx] at hBeq
  have ha : (2*z)•((Aᴴ*B)*ᵥy) = (1+z)•x := by
    calc
      _ = (2:ℂ)•x - ((2:ℂ)•x-(2*z)•((Aᴴ*B)*ᵥy)) := by module
      _ = _ := by rw [hAeq]; module
  have hb : (2:ℂ)•((Bᴴ*A)*ᵥx) = (1+z)•y := by
    calc
      _ = ((2:ℂ)•((Bᴴ*A)*ᵥx)-(2*z)•y)+(2*z)•y := by module
      _ = _ := by rw [hBeq]; module
  have hcoef : 1+z = -2*(lam:ℂ)*c := by linear_combination hline
  have hab : (Aᴴ*B)*ᵥ(-c•y)=(lam:ℂ)•x := by
    rw [Matrix.mulVec_smul]
    apply smul_right_injective (QState I) (mul_ne_zero (by norm_num : (2:ℂ)≠0) hc0)
    calc
      (2*c)•(-c•((Aᴴ*B)*ᵥy)) = -((2*z)•((Aᴴ*B)*ᵥy)) := by
        rw [smul_smul,← hcz]
        module
      _ = (2*c)•((lam:ℂ)•x) := by rw [ha,hcoef]; module
  have hba : (Bᴴ*A)*ᵥx=(lam:ℂ)•(-c•y) := by
    apply smul_right_injective (QState J) (by norm_num : (2:ℂ)≠0)
    change (2:ℂ)•((Bᴴ*A)*ᵥx)=(2:ℂ)•((lam:ℂ)•(-c•y))
    rw [hb,hcoef]
    module
  let u := (2/(1-z):ℂ) • Sum.elim x (-c•y)
  refine ⟨u, ?_, ?_⟩
  · dsimp only [u]
    rw [Matrix.mulVec_smul, bipartiteDiscriminant, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, zero_add, add_zero,
      hab,hba]
    ext (i | j) <;> simp [smul_smul, mul_comm] <;> ring
  · rw [tau_apply]
    change A*ᵥ((2/(1-z):ℂ)•x)+c•(B*ᵥ((2/(1-z):ℂ)•(-c•y)))=w
    simp only [Matrix.mulVec_smul]
    have hAx : A*ᵥx=p := (Matrix.mulVec_mulVec _ _ _)
    have hBy : B*ᵥy=q := (Matrix.mulVec_mulVec _ _ _)
    rw [hAx,hBy]
    have hh : (2:ℂ)•(p-z•q)=(1-z)•w := by simpa only [smul_sub,smul_smul] using! hproj
    calc
      _ = (1-z)⁻¹ • ((2:ℂ)•(p-z•q)) := by
        rw [← hcz]
        simp only [div_eq_mul_inv]
        module
      _ = w := by rw [hh,smul_smul,inv_mul_cancel₀ hz1,one_smul]

/-- Every nonzero walk eigenvector at an interior signed phase is the τ image of a nonzero
discriminant eigenvector at `lam` [Szegedy2004]. -/
theorem bipartite_interior_tau_preimage :
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (w : QState H) (lam : ℝ) (s : Bool),
    IsIsometry A → IsIsometry B → 0 < lam → lam < 1 →
    w ≠ 0 → bipartiteWalk A B*ᵥw = bipartitePhase lam s•w →
    ∃ u : QState (I⊕J), u ≠ 0 ∧ bipartiteDiscriminant A B*ᵥu = (lam:ℂ)•u ∧
      bipartiteTauLinear A B lam s u = w := by
  intro H I J _ _ _ _ _ _ A B w lam s hA hB hl hu hw0 hw
  obtain ⟨u,hu,huw⟩ := tau_interior_preimage A B hA hB w lam s hl hu hw
  refine ⟨u, ?_, hu, huw⟩
  intro he
  rw [he,map_zero] at huw
  exact hw0 huw.symm

/-- A bipartite discriminant eigenvector satisfies the two cross-Gram equations for its left and
right components. -/
private theorem tau_disc_blocks (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (u : QState (I⊕J)) (lam : ℝ) (hd : bipartiteDiscriminant A B*ᵥu=(lam:ℂ)•u) :
    (Aᴴ*B)*ᵥ(fun j => u (.inr j))=(lam:ℂ)•(fun i => u (.inl i)) ∧
    (Bᴴ*A)*ᵥ(fun i => u (.inl i))=(lam:ℂ)•(fun j => u (.inr j)) := by
  constructor
  · have hh := congrArg (fun v : QState (I⊕J) => fun i => v (.inl i)) hd
    simpa [bipartiteDiscriminant,Matrix.fromBlocks_mulVec] using! hh
  · have hh := congrArg (fun v : QState (I⊕J) => fun j => v (.inr j)) hd
    simpa [bipartiteDiscriminant,Matrix.fromBlocks_mulVec] using! hh

/-- The τ image of an interior discriminant eigenvector is a walk eigenvector at the
corresponding signed phase and lies in the combined frame range. -/
private theorem tau_forward (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (u : QState (I⊕J)) (lam : ℝ) (s : Bool)
    (hl : 0 < lam) (hu : lam < 1) (hd : bipartiteDiscriminant A B*ᵥu=(lam:ℂ)•u) :
    bipartiteWalk A B*ᵥbipartiteTauLinear A B lam s u =
      bipartitePhase lam s • bipartiteTauLinear A B lam s u ∧
    bipartiteTauLinear A B lam s u ∈ LinearMap.range (bipartiteTilde A B).toLin' := by
  let a := fun i => u (.inl i)
  let b := fun j => u (.inr j)
  let x := A*ᵥa
  let y := B*ᵥb
  let c := tauCoeff lam s
  obtain ⟨hab,hba⟩ := tau_disc_blocks A B u lam hd
  have hPAx : (A*Aᴴ)*ᵥx=x := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.mul_one]
  have hPBy : (B*Bᴴ)*ᵥy=y := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,show Bᴴ*B=1 from hB,Matrix.mul_one]
  have hPAy : (A*Aᴴ)*ᵥy=(lam:ℂ)•x := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,← Matrix.mulVec_mulVec,hab,Matrix.mulVec_smul]
  have hPBx : (B*Bᴴ)*ᵥx=(lam:ℂ)•y := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,← Matrix.mulVec_mulVec,hba,Matrix.mulVec_smul]
  have hwx : bipartiteWalk A B*ᵥx = -x+(2*(lam:ℂ))•y := by
    rw [bipartiteWalk,← Matrix.mulVec_mulVec,reflectionAbout_mulVec (A*Aᴴ) x,hPAx]
    have hh : (2:ℂ)•x-x=x := by module
    rw [hh,reflectionAbout_mulVec,hPBx]
    module
  have hwy : bipartiteWalk A B*ᵥy = (-2*(lam:ℂ))•x+(4*(lam:ℂ)^2-1)•y := by
    rw [bipartiteWalk,← Matrix.mulVec_mulVec,reflectionAbout_mulVec (A*Aᴴ) y,hPAy,
      Matrix.mulVec_sub,Matrix.mulVec_smul,reflectionAbout_mulVec,reflectionAbout_mulVec,
      Matrix.mulVec_smul,hPBx,hPBy]
    module
  have hc := tau_coeff_laws lam s hl hu
  have hc1 : -1-2*(lam:ℂ)*c=bipartitePhase lam s := by linear_combination -hc.2.1
  have hc2 : 2*(lam:ℂ)+(4*(lam:ℂ)^2-1)*c=bipartitePhase lam s*c := by
    linear_combination (2*(lam:ℂ)-c)*hc.2.1 + (2*(lam:ℂ))*hc.1
  constructor
  · rw [tau_apply]
    change bipartiteWalk A B*ᵥ(x+c•y)=bipartitePhase lam s•(x+c•y)
    rw [Matrix.mulVec_add,Matrix.mulVec_smul,hwx,hwy]
    calc
      _ = (-1-2*(lam:ℂ)*c)•x+(2*(lam:ℂ)+(4*(lam:ℂ)^2-1)*c)•y := by module
      _ = _ := by rw [hc1,hc2]; module
  · refine ⟨Sum.elim a (c•b), ?_⟩
    change bipartiteTilde A B*ᵥ(Sum.elim a (c•b))=bipartiteTauLinear A B lam s u
    rw [bipartiteTilde,Matrix.fromCols_mulVec_sumElim,Matrix.mulVec_smul,tau_apply]

/-- The τ map has trivial kernel on an interior discriminant eigenspace when the left frame is
isometric. -/
private theorem tau_kernel_trivial (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (u : QState (I⊕J)) (lam : ℝ) (s : Bool)
    (hl : 0 < lam) (hu : lam < 1) (hd : bipartiteDiscriminant A B*ᵥu=(lam:ℂ)•u)
    (ht : bipartiteTauLinear A B lam s u=0) : u=0 := by
  let a := fun i => u (.inl i)
  let b := fun j => u (.inr j)
  let c := tauCoeff lam s
  obtain ⟨hab,hba⟩ := tau_disc_blocks A B u lam hd
  have hc := tau_coeff_laws lam s hl hu
  have hcoef : 2*(1+c*(lam:ℂ))=1-bipartitePhase lam s := by linear_combination hc.2.1
  have hcoef0 : 1+c*(lam:ℂ) ≠ 0 := by
    intro he
    rw [he,mul_zero] at hcoef
    exact hc.2.2.2 (sub_eq_zero.mp hcoef.symm).symm
  have hproj : Aᴴ*ᵥbipartiteTauLinear A B lam s u=(1+c*(lam:ℂ))•a := by
    rw [tau_apply,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_mulVec,
      show Aᴴ*A=1 from hA,Matrix.one_mulVec,Matrix.mulVec_mulVec,hab]
    module
  have ha : a=0 := by
    have hh : (1+c*(lam:ℂ))•a=0 := by rw [← hproj,ht,Matrix.mulVec_zero]
    exact (smul_eq_zero.mp hh).resolve_left hcoef0
  have hb : b=0 := by
    change (Bᴴ*A)*ᵥa=(lam:ℂ)•b at hba
    rw [ha,Matrix.mulVec_zero] at hba
    exact (smul_eq_zero.mp hba.symm).resolve_left (by exact_mod_cast hl.ne')
  ext (i | j)
  · exact congrFun ha i
  · exact congrFun hb j

/-- For `0 < lam < 1`, the two walk phases are distinct and each corresponding eigenspace in the
combined frame range is linearly equivalent to the discriminant eigenspace at `lam`. Their
sum has twice the source dimension [Szegedy2004]. -/
theorem bipartite_tau_eigenspace_pair_equivalence :
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (lam : ℝ),
    IsIsometry A → IsIsometry B → 0 < lam → lam < 1 →
    bipartitePhase lam true ≠ bipartitePhase lam false ∧
    (∀ s : Bool,
      ∃ e : ↥(LinearMap.ker
            ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) ≃ₗ[ℂ]
          ↥(LinearMap.ker
              ((bipartiteWalk A B-bipartitePhase lam s•(1 : Matrix H H ℂ)).toLin') ⊓
            LinearMap.range (bipartiteTilde A B).toLin'),
        ∀ u, (e u).1 = bipartiteTauLinear A B lam s u.1) ∧
    Module.finrank ℂ ↥((LinearMap.ker
          ((bipartiteWalk A B-bipartitePhase lam true•(1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin') ⊔
      (LinearMap.ker
          ((bipartiteWalk A B-bipartitePhase lam false•(1 : Matrix H H ℂ)).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin')) =
      2*Module.finrank ℂ ↥(LinearMap.ker
        ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) := by
  intro H I J _ _ _ _ _ _ A B lam hA hB hl hu
  let K := LinearMap.ker ((bipartiteDiscriminant A B-(lam:ℂ)•(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')
  let E := fun s => LinearMap.ker
    ((bipartiteWalk A B-bipartitePhase lam s•(1 : Matrix H H ℂ)).toLin') ⊓
      LinearMap.range (bipartiteTilde A B).toLin'
  have hdistinct : bipartitePhase lam true ≠ bipartitePhase lam false := by
    intro he
    have hh := congrArg Complex.im he
    have hr : 0 < Real.sqrt (1-lam^2) := Real.sqrt_pos.mpr (by nlinarith)
    simp [bipartitePhase,pow_two,Complex.mul_im,Complex.mul_re] at hh
    simp only [pow_two] at hr
    nlinarith [mul_pos hl hr]
  have hequiv (s : Bool) : ∃ e : K ≃ₗ[ℂ] E s,
      ∀ u, (e u).1=bipartiteTauLinear A B lam s u.1 := by
    have hdu (u : K) : bipartiteDiscriminant A B*ᵥu.val=(lam:ℂ)•u.val := by
      have hh := u.property
      change (bipartiteDiscriminant A B-(lam:ℂ)•1)*ᵥu.val=0 at hh
      simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero] using! hh
    have hmem (u : K) : bipartiteTauLinear A B lam s u.val ∈ E s := by
      have hh := tau_forward A B hA hB u.val lam s hl hu (hdu u)
      refine ⟨?_,hh.2⟩
      change (bipartiteWalk A B-bipartitePhase lam s•1)*ᵥbipartiteTauLinear A B lam s u.val=0
      simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hh.1,sub_self]
    let f : K →ₗ[ℂ] E s := {
      toFun := fun u => ⟨bipartiteTauLinear A B lam s u.val,hmem u⟩
      map_add' := by intro u v; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c u; apply Subtype.ext; exact map_smul _ _ _ }
    have hinj : Function.Injective f := by
      intro u v huv
      have hh : f (u-v)=0 := by rw [map_sub,huv,sub_self]
      have hz : bipartiteTauLinear A B lam s (u-v).val=0 := congrArg Subtype.val hh
      apply sub_eq_zero.mp
      apply Subtype.ext
      exact tau_kernel_trivial A B hA (u-v).val lam s hl hu (hdu (u-v)) hz
    have hsurj : Function.Surjective f := by
      intro w
      have hw : bipartiteWalk A B*ᵥw.val=bipartitePhase lam s•w.val := by
        have hh := w.property.1
        change (bipartiteWalk A B-bipartitePhase lam s•1)*ᵥw.val=0 at hh
        simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero] using! hh
      obtain ⟨u,hd,ht⟩ := tau_interior_preimage A B hA hB w.val lam s hl hu hw
      have huK : u ∈ K := by
        change (bipartiteDiscriminant A B-(lam:ℂ)•1)*ᵥu=0
        simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hd,sub_self]
      exact ⟨⟨u,huK⟩,Subtype.ext ht⟩
    exact ⟨LinearEquiv.ofBijective f ⟨hinj,hsurj⟩,fun u => rfl⟩
  refine ⟨hdistinct,hequiv,?_⟩
  obtain ⟨ep,hp⟩ := hequiv true
  obtain ⟨em,hm⟩ := hequiv false
  have hdisjoint : Disjoint (E true) (E false) := by
    apply disjoint_iff.mpr
    apply le_antisymm ?_ bot_le
    intro w hw
    change w=0
    have hp := hw.1.1
    have hm := hw.2.1
    change (bipartiteWalk A B-bipartitePhase lam true•1)*ᵥw=0 at hp
    change (bipartiteWalk A B-bipartitePhase lam false•1)*ᵥw=0 at hm
    simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero] at hp hm
    have hh : (bipartitePhase lam true-bipartitePhase lam false)•w=0 := by
      rw [sub_smul,← hp,← hm,sub_self]
    exact (smul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hdistinct)
  change Module.finrank ℂ ↥(E true ⊔ E false)=2*Module.finrank ℂ K
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (E true) (E false)
  rw [hdisjoint.eq_bot,finrank_bot,add_zero,← ep.finrank_eq,← em.finrank_eq] at hdim
  omega

/-- A walk fixed vector in the combined frame range is the combined-frame image of a
discriminant fixed vector. -/
private theorem tau_endpoint_plus_preimage (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (w : QState H)
    (hw : bipartiteWalk A B*ᵥw=w)
    (hv : w ∈ LinearMap.range (bipartiteTilde A B).toLin') :
    ∃ u, bipartiteDiscriminant A B*ᵥu=u ∧ bipartiteTilde A B*ᵥu=w := by
  have hp := bipartite_busy_fixed_in_both_ranges A B hA hB w hw hv
  let x := Aᴴ*ᵥw
  let y := Bᴴ*ᵥw
  have hx : (Aᴴ*B)*ᵥy=x := by
    change (Aᴴ*B)*ᵥ(Bᴴ*ᵥw)=Aᴴ*ᵥw
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,← Matrix.mulVec_mulVec,hp.2]
  have hy : (Bᴴ*A)*ᵥx=y := by
    change (Bᴴ*A)*ᵥ(Aᴴ*ᵥw)=Bᴴ*ᵥw
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,← Matrix.mulVec_mulVec,hp.1]
  refine ⟨(1/2:ℂ)•Sum.elim x y, ?_, ?_⟩
  · rw [Matrix.mulVec_smul,bipartiteDiscriminant,Matrix.fromBlocks_mulVec]
    simp [hx,hy]
  · rw [Matrix.mulVec_smul,bipartiteTilde,Matrix.fromCols_mulVec_sumElim,
      Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hp.1,hp.2]
    module

/-- A minus-one walk eigenvector is the combined-frame image of a vector in the discriminant
kernel. -/
private theorem tau_endpoint_zero_preimage (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (w : QState H)
    (hw : bipartiteWalk A B*ᵥw=-w) :
    ∃ u, bipartiteDiscriminant A B*ᵥu=0 ∧ bipartiteTilde A B*ᵥu=w := by
  have hs := (bipartite_endpoint_projectors A B hA hB w).2.mp hw
  have hga : (Bᴴ*A)*ᵥ(Aᴴ*ᵥw)=0 := by
    have hh := congrArg (fun x : QState H => Bᴴ*ᵥx) hs
    (try dsimp only at hh)
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      show Bᴴ*(B*Bᴴ)=Bᴴ from by rw [← Matrix.mul_assoc,show Bᴴ*B=1 from hB,Matrix.one_mul]] at hh
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    exact add_eq_right.mp hh
  have hgb : (Aᴴ*B)*ᵥ(Bᴴ*ᵥw)=0 := by
    have hh := congrArg (fun x : QState H => Aᴴ*ᵥx) hs
    (try dsimp only at hh)
    rw [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
      show Aᴴ*(A*Aᴴ)=Aᴴ from by rw [← Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.one_mul]] at hh
    rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    exact add_eq_left.mp hh
  refine ⟨Sum.elim (Aᴴ*ᵥw) (Bᴴ*ᵥw), ?_, ?_⟩
  · rw [bipartiteDiscriminant,Matrix.fromBlocks_mulVec]
    simp [hga,hgb]
  · simpa only [bipartiteTilde,Matrix.fromCols_mulVec_sumElim,Matrix.mulVec_mulVec] using! hs

/-- The combined-frame map has trivial kernel on a discriminant eigenspace whose eigenvalue is
different from minus one. -/
private theorem tau_tilde_kernel_trivial (A : Matrix H I ℂ) (B : Matrix H J ℂ)
    (hA : IsIsometry A) (hB : IsIsometry B) (u : QState (I⊕J)) (a : ℂ)
    (ha : 1+a ≠ 0) (hd : bipartiteDiscriminant A B*ᵥu=a•u)
    (ht : bipartiteTilde A B*ᵥu=0) : u=0 := by
  have hgram := (bipartite_discriminant_tilde_bridge H I J A B hA hB).2.1
  have hh : (1+bipartiteDiscriminant A B)*ᵥu=0 := by
    rw [← hgram,← Matrix.mulVec_mulVec,ht,Matrix.mulVec_zero]
  rw [Matrix.add_mulVec,Matrix.one_mulVec,hd] at hh
  have hz : (1+a)•u=0 := by simpa only [add_smul,one_smul] using! hh
  exact (smul_eq_zero.mp hz).resolve_left ha

/-- The combined-frame map gives linear equivalences from the discriminant eigenspaces at one
and zero to the walk eigenspaces at one and minus one within the combined frame range
[Szegedy2004]. -/
theorem bipartite_endpoint_eigenspace_transport :
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    (∃ e₁ : ↥(LinearMap.ker
          ((bipartiteDiscriminant A B-(1 : Matrix (I⊕J) (I⊕J) ℂ)).toLin')) ≃ₗ[ℂ]
        ↥(LinearMap.ker ((bipartiteWalk A B-(1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin'),
      ∀ u, (e₁ u).1 = bipartiteTilde A B*ᵥu.1) ∧
    ∃ e₀ : ↥(LinearMap.ker (bipartiteDiscriminant A B).toLin') ≃ₗ[ℂ]
        ↥(LinearMap.ker ((bipartiteWalk A B+(1 : Matrix H H ℂ)).toLin') ⊓
          LinearMap.range (bipartiteTilde A B).toLin'),
      ∀ u, (e₀ u).1 = bipartiteTilde A B*ᵥu.1 := by
  intro H I J _ _ _ _ _ _ A B hA hB
  let K₁ := LinearMap.ker ((bipartiteDiscriminant A B-1).toLin')
  let K₀ := LinearMap.ker (bipartiteDiscriminant A B).toLin'
  let E₁ :=
      LinearMap.ker ((bipartiteWalk A B-1).toLin') ⊓ LinearMap.range (bipartiteTilde A B).toLin'
  let E₀ :=
      LinearMap.ker ((bipartiteWalk A B+1).toLin') ⊓ LinearMap.range (bipartiteTilde A B).toLin'
  have hdu₁ (u : K₁) : bipartiteDiscriminant A B*ᵥu.val=u.val := by
    have hh := u.property
    change (bipartiteDiscriminant A B-1)*ᵥu.val=0 at hh
    simpa only [Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero] using! hh
  have hdu₀ (u : K₀) : bipartiteDiscriminant A B*ᵥu.val=0 := u.property
  have hf₁ (u : K₁) : bipartiteTilde A B*ᵥu.val ∈ E₁ := by
    refine ⟨?_,⟨u.val,rfl⟩⟩
    change (bipartiteWalk A B-1)*ᵥ(bipartiteTilde A B*ᵥu.val)=0
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,
      (bipartite_endpoint_kernel_transport H I J A B u.val hA hB).1 (hdu₁ u),sub_self]
  have hf₀ (u : K₀) : bipartiteTilde A B*ᵥu.val ∈ E₀ := by
    refine ⟨?_,⟨u.val,rfl⟩⟩
    change (bipartiteWalk A B+1)*ᵥ(bipartiteTilde A B*ᵥu.val)=0
    rw [Matrix.add_mulVec,Matrix.one_mulVec,
      (bipartite_endpoint_kernel_transport H I J A B u.val hA hB).2.2 (hdu₀ u),neg_add_cancel]
  let f₁ : K₁ →ₗ[ℂ] E₁ := {
    toFun := fun u => ⟨bipartiteTilde A B*ᵥu.val,hf₁ u⟩
    map_add' := by intro u v; apply Subtype.ext; exact Matrix.mulVec_add _ _ _
    map_smul' := by intro c u; apply Subtype.ext; exact Matrix.mulVec_smul _ _ _ }
  let f₀ : K₀ →ₗ[ℂ] E₀ := {
    toFun := fun u => ⟨bipartiteTilde A B*ᵥu.val,hf₀ u⟩
    map_add' := by intro u v; apply Subtype.ext; exact Matrix.mulVec_add _ _ _
    map_smul' := by intro c u; apply Subtype.ext; exact Matrix.mulVec_smul _ _ _ }
  have hinj₁ : Function.Injective f₁ := by
    intro u v huv
    have hh : f₁ (u-v)=0 := by rw [map_sub,huv,sub_self]
    apply sub_eq_zero.mp
    apply Subtype.ext
    exact tau_tilde_kernel_trivial A B hA hB (u-v).val 1 (by norm_num)
      (by simpa only [one_smul] using! hdu₁ (u-v)) (congrArg Subtype.val hh)
  have hinj₀ : Function.Injective f₀ := by
    intro u v huv
    have hh : f₀ (u-v)=0 := by rw [map_sub,huv,sub_self]
    apply sub_eq_zero.mp
    apply Subtype.ext
    exact tau_tilde_kernel_trivial A B hA hB (u-v).val 0 (by norm_num)
      (by simpa only [zero_smul] using! hdu₀ (u-v)) (congrArg Subtype.val hh)
  have hsurj₁ : Function.Surjective f₁ := by
    intro w
    have hw : bipartiteWalk A B*ᵥw.val=w.val := by
      have hh := w.property.1
      change (bipartiteWalk A B-1)*ᵥw.val=0 at hh
      simpa only [Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero] using! hh
    obtain ⟨u,hd,ht⟩ := tau_endpoint_plus_preimage A B hA hB w.val hw w.property.2
    have hu : u ∈ K₁ := by
      change (bipartiteDiscriminant A B-1)*ᵥu=0
      rw [Matrix.sub_mulVec,Matrix.one_mulVec,hd,sub_self]
    exact ⟨⟨u,hu⟩,Subtype.ext ht⟩
  have hsurj₀ : Function.Surjective f₀ := by
    intro w
    have hw : bipartiteWalk A B*ᵥw.val=-w.val := by
      have hh := w.property.1
      change (bipartiteWalk A B+1)*ᵥw.val=0 at hh
      rw [Matrix.add_mulVec,Matrix.one_mulVec] at hh
      exact eq_neg_of_add_eq_zero_left hh
    obtain ⟨u,hd,ht⟩ := tau_endpoint_zero_preimage A B hA hB w.val hw
    exact ⟨⟨u,hd⟩,Subtype.ext ht⟩
  exact ⟨⟨LinearEquiv.ofBijective f₁ ⟨hinj₁,hsurj₁⟩,fun u => rfl⟩,
    ⟨LinearEquiv.ofBijective f₀ ⟨hinj₀,hsurj₀⟩,fun u => rfl⟩⟩

/-- Construct an orthonormal walk eigenframe spanning the combined frame range, with dimension
equal to its rank and every column labeled by a nonzero endpoint or signed interior
discriminant source [Szegedy2004]. -/
theorem bipartite_labeled_busy_spectral_frame :
  ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    ∃ (m : ℕ) (V : Matrix H (Fin m) ℂ) (z : Fin m→ℂ),
      IsIsometry V ∧
      V*Vᴴ = bipartiteTilde A B*matrixPseudoinverse (bipartiteTilde A B) ∧
      bipartiteWalk A B*V = V*Matrix.diagonal z ∧
      m = Matrix.rank (bipartiteTilde A B) ∧
      ∀ i : Fin m,
        (z i = 1 ∧ ∃ u : QState (I⊕J), u ≠ 0 ∧ bipartiteDiscriminant A B*ᵥu = u ∧
          (fun h => V h i) = bipartiteTilde A B*ᵥu) ∨
        (z i = -1 ∧ ∃ u : QState (I⊕J), u ≠ 0 ∧ bipartiteDiscriminant A B*ᵥu = 0 ∧
          (fun h => V h i) = bipartiteTilde A B*ᵥu) ∨
        (∃ lam : ℝ, 0 < lam ∧ lam < 1 ∧ ∃ (s : Bool) (u : QState (I⊕J)),
          u ≠ 0 ∧ bipartiteDiscriminant A B*ᵥu = (lam:ℂ)•u ∧
          z i = bipartitePhase lam s ∧
          (fun h => V h i) = bipartiteTauLinear A B lam s u) := by
  intro H I J _ _ _ _ _ _ A B hA hB
  obtain ⟨m,V,z,hV,hVV,hWV,hm,hlabels⟩ :=
    bipartite_complete_busy_spectral_frame H I J A B hA hB
  obtain ⟨⟨e₁,he₁⟩,⟨e₀,he₀⟩⟩ := bipartite_endpoint_eigenspace_transport H I J A B hA hB
  refine ⟨m,V,z,hV,hVV,hWV,hm,?_⟩
  intro i
  let w : QState H := fun h => V h i
  have hn : Qatlib.Foundations.PureStateMath.Inner w w=1 := by
    have hh := congrFun (congrFun (show Vᴴ*V=1 from hV) i) i
    simpa [w,Qatlib.Foundations.PureStateMath.Inner,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using! hh
  have hw0 : w ≠ 0 := by
    intro he
    rw [he] at hn
    simp [Qatlib.Foundations.PureStateMath.Inner] at hn
  have hw : bipartiteWalk A B*ᵥw=z i•w := by
    ext h
    have hh := congrFun (congrFun hWV h) i
    rw [Matrix.mul_diagonal] at hh
    simpa [w,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using! hh
  have hprojV : (bipartiteTilde A B*matrixPseudoinverse (bipartiteTilde A B))*V=V := by
    rw [← hVV,Matrix.mul_assoc,show Vᴴ*V=1 from hV,Matrix.mul_one]
  have hbusy : w ∈ LinearMap.range (bipartiteTilde A B).toLin' := by
    refine ⟨matrixPseudoinverse (bipartiteTilde A B)*ᵥw,?_⟩
    change bipartiteTilde A B*ᵥ(matrixPseudoinverse (bipartiteTilde A B)*ᵥw)=w
    rw [Matrix.mulVec_mulVec]
    ext h
    have hh := congrFun (congrFun hprojV h) i
    simpa [w,Matrix.mul_apply,Matrix.mulVec,dotProduct] using! hh
  rcases hlabels i with hp | hm | ⟨lam,hl,hu,hphase⟩
  · left
    refine ⟨hp,?_⟩
    have hmem : w ∈ LinearMap.ker ((bipartiteWalk A B-1).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin' := by
      refine ⟨?_,hbusy⟩
      change (bipartiteWalk A B-1)*ᵥw=0
      rw [Matrix.sub_mulVec,Matrix.one_mulVec,hw,hp,one_smul,sub_self]
    let v := e₁.symm ⟨w,hmem⟩
    have ht : bipartiteTilde A B*ᵥv.val=w := by
      rw [← he₁ v]
      exact congrArg Subtype.val (e₁.apply_symm_apply ⟨w,hmem⟩)
    have hd : bipartiteDiscriminant A B*ᵥv.val=v.val := by
      have hh := v.property
      change (bipartiteDiscriminant A B-1)*ᵥv.val=0 at hh
      simpa only [Matrix.sub_mulVec,Matrix.one_mulVec,sub_eq_zero] using! hh
    refine ⟨v.val,?_,hd,ht.symm⟩
    intro he
    rw [he,Matrix.mulVec_zero] at ht
    exact hw0 ht.symm
  · right; left
    refine ⟨hm,?_⟩
    have hmem : w ∈ LinearMap.ker ((bipartiteWalk A B+1).toLin') ⊓
        LinearMap.range (bipartiteTilde A B).toLin' := by
      refine ⟨?_,hbusy⟩
      change (bipartiteWalk A B+1)*ᵥw=0
      rw [Matrix.add_mulVec,Matrix.one_mulVec,hw,hm,neg_one_smul,neg_add_cancel]
    let v := e₀.symm ⟨w,hmem⟩
    have ht : bipartiteTilde A B*ᵥv.val=w := by
      rw [← he₀ v]
      exact congrArg Subtype.val (e₀.apply_symm_apply ⟨w,hmem⟩)
    refine ⟨v.val,?_,v.property,ht.symm⟩
    intro he
    rw [he,Matrix.mulVec_zero] at ht
    exact hw0 ht.symm
  · right; right
    rcases hphase with ht | hf
    · rw [ht] at hw
      obtain ⟨u,hu0,hd,huw⟩ :=
          bipartite_interior_tau_preimage H I J A B w lam true hA hB hl hu hw0 hw
      exact ⟨lam,hl,hu,true,u,hu0,hd,ht,huw.symm⟩
    · rw [hf] at hw
      obtain ⟨u,hu0,hd,huw⟩ :=
          bipartite_interior_tau_preimage H I J A B w lam false hA hB hl hu hw0 hw
      exact ⟨lam,hl,hu,false,u,hu0,hd,hf,huw.symm⟩

end Qatlib.Concepts.WalkSearch.TauEmbedding
