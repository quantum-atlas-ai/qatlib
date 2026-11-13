/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BoundarySpectralSectors
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# Discriminant spectra of bipartite reflection walks

This module defines the block discriminant and concatenated coordinate map for two finite
rectangular frames, together with the associated product of reflections. For isometric frames,
it proves the discriminant Gram identity and constructs the two normalized, orthogonal walk
eigenvectors associated with an interior discriminant eigenpair. These constructions follow the
spectral correspondence of [Szegedy2004].

The endpoint transport statements handle discriminant eigenvalues 1, -1, and 0. A complete
orthonormal eigenframe spans the range of the concatenated frame, with dimension equal to its
rank and eigenvalues classified by the endpoint phases and the interior `bipartitePhase` family.

## Main statements

* `bipartite_discriminant_tilde_bridge`: the Hermitian discriminant, Gram identity, and walk
  unitarity.
* `bipartite_normalized_tau_pair`: the normalized orthogonal pair of walk eigenvectors.
* `bipartite_endpoint_kernel_transport`: transport at the endpoint and zero eigenvalues.
* `bipartite_complete_busy_spectral_frame`: a complete eigenframe on the concatenated frame's
  range.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.AmplitudeCore.InvFreePhase

namespace Qatlib.Concepts.SpectralFilter.BusySpectrum
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The finite-state inner product is additive in its left argument. -/
private theorem bipartite_inner_add_left {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner (u+v) w=Qatlib.Foundations.PureStateMath.Inner u w+Qatlib.Foundations.PureStateMath.Inner v w := by simp [Qatlib.Foundations.PureStateMath.Inner,star_add,add_dotProduct]

/-- The finite-state inner product is additive in its right argument. -/
private theorem bipartite_inner_add_right {K : Type} [Fintype K] (u v w : QState K) :
    Qatlib.Foundations.PureStateMath.Inner u (v+w)=Qatlib.Foundations.PureStateMath.Inner u v+Qatlib.Foundations.PureStateMath.Inner u w := by simp [Qatlib.Foundations.PureStateMath.Inner,dotProduct_add]

/-- Reversing the two arguments of the finite-state inner product complex conjugates its value. -/
private theorem bipartite_inner_rev {K : Type} [Fintype K] (u v : QState K) :
    Qatlib.Foundations.PureStateMath.Inner v u=(starRingEnd ℂ) (Qatlib.Foundations.PureStateMath.Inner u v) := by
  exact star_dotProduct (v:=v) (w:=u)

/-- The block discriminant with zero diagonal blocks and off-diagonal blocks AᴴB and BᴴA. -/
noncomputable def bipartiteDiscriminant {H I J : Type} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (A : Matrix H I ℂ) (B : Matrix H J ℂ) : Matrix (I⊕J) (I⊕J) ℂ :=
  Matrix.fromBlocks 0 (Aᴴ*B) (Bᴴ*A) 0

/-- The matrix formed by concatenating the columns of `A` and `B`, mapping their direct-sum
coordinates into the ambient state space. -/
noncomputable def bipartiteTilde {H I J : Type} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (A : Matrix H I ℂ) (B : Matrix H J ℂ) : Matrix H (I⊕J) ℂ := Matrix.fromCols A B

/-- The product of the reflection about BBᴴ with the reflection about AAᴴ. -/
noncomputable def bipartiteWalk {H I J : Type} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (A : Matrix H I ℂ) (B : Matrix H J ℂ) : Matrix H H ℂ :=
  ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ)

/-- The candidate walk eigenvector formed from `A *ᵥ a` and `B *ᵥ b` with the Boolean-selected
complex coefficient and reciprocal sqrt(1 - lam²) scaling. -/
noncomputable def bipartiteTau {H I J : Type} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (A : Matrix H I ℂ) (B : Matrix H J ℂ) (a : QState I) (b : QState J) (lam : ℝ) (s : Bool) : QState H :=
  (Real.sqrt (1-lam^2):ℂ)⁻¹•(A*ᵥa+(-(lam:ℂ)+(if s then Complex.I else -Complex.I)*(Real.sqrt (1-lam^2):ℂ))•(B*ᵥb))

/-- The complex expression 2lam² - 1 minus the Boolean-selected sign of i times 2lam sqrt(1 -
lam²). -/
noncomputable def bipartitePhase (lam : ℝ) (s : Bool) : ℂ :=
  (2*lam^2-1:ℝ)-(if s then Complex.I else -Complex.I)*(2*lam*Real.sqrt (1-lam^2):ℝ)

/-- For two isometries, the discriminant is Hermitian, the Gram matrix of their concatenated
frame is the identity plus the discriminant, and the bipartite walk is unitary. See
[Szegedy2004]. -/
theorem bipartite_discriminant_tilde_bridge :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    (bipartiteDiscriminant A B).IsHermitian ∧
    (bipartiteTilde A B)ᴴ*bipartiteTilde A B=1+bipartiteDiscriminant A B ∧
    bipartiteWalk A B∈Matrix.unitaryGroup H ℂ := by
  intro H I J _ _ _ _ _ _ A B hA hB
  refine ⟨?_, ?_, ?_⟩
  · change (Matrix.fromBlocks 0 (Aᴴ*B) (Bᴴ*A) 0)ᴴ = _
    simp [bipartiteDiscriminant, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_mul]
  · simp only [bipartiteTilde, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
      Matrix.fromRows_mul_fromCols, show Aᴴ*A=1 from hA, show Bᴴ*B=1 from hB]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [bipartiteDiscriminant, Matrix.one_apply]
  · exact (Matrix.unitaryGroup H ℂ).mul_mem
      (reflectionAbout_unitary (rangeProjector_isOrthogonalProjector hB))
      (reflectionAbout_unitary (rangeProjector_isOrthogonalProjector hA))

/-- For isometries and a normalized discriminant eigenpair with 0 < lam < 1, the two
`bipartiteTau` vectors are normalized, mutually orthogonal walk eigenvectors with the
corresponding `bipartitePhase` eigenvalues. See [SommaBoixoBarnum2007] and [Szegedy2004]. -/
theorem bipartite_normalized_tau_pair :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ)
      (a : QState I) (b : QState J) (lam : ℝ),
    IsIsometry A → IsIsometry B → 0 < lam → lam < 1 →
    Normalized (Sum.elim a b) → (Aᴴ*B)*ᵥb=(lam:ℂ)•a → (Bᴴ*A)*ᵥa=(lam:ℂ)•b →
    ∀ s : Bool, Normalized (bipartiteTau A B a b lam s) ∧
      bipartiteWalk A B*ᵥbipartiteTau A B a b lam s=
        bipartitePhase lam s•bipartiteTau A B a b lam s ∧
      Qatlib.Foundations.PureStateMath.Inner (bipartiteTau A B a b lam true) (bipartiteTau A B a b lam false)=0 := by
  intro H I J _ _ _ _ _ _ A B a b lam hA hB hl hu hn hab hba
  let x := A*ᵥa
  let y := B*ᵥb
  let r := Real.sqrt (1-lam^2)
  let c : Bool → ℂ := fun s => -(lam:ℂ)+(if s then Complex.I else -Complex.I)*(r:ℂ)
  have hrpos : 0 < 1-lam^2 := by nlinarith
  have hr : r≠0 := ne_of_gt (Real.sqrt_pos.mpr hrpos)
  have hrC : (r:ℂ)≠0 := by exact_mod_cast hr
  have hr2 : r^2=1-lam^2 := Real.sq_sqrt (le_of_lt hrpos)
  have hr2scaled : lam*(Real.sqrt (1-lam*lam)*Real.sqrt (1-lam*lam))=lam*(1-lam*lam) := by
    simpa only [r,pow_two] using! congrArg (fun t : ℝ => lam*t) hr2
  have hxy : Qatlib.Foundations.PureStateMath.Inner x y=(lam:ℂ)*Qatlib.Foundations.PureStateMath.Inner a a := by
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,hab,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right]
  have hyx : Qatlib.Foundations.PureStateMath.Inner y x=(lam:ℂ)*Qatlib.Foundations.PureStateMath.Inner b b := by
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,hba,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right]
  have heq : Qatlib.Foundations.PureStateMath.Inner a a=Qatlib.Foundations.PureStateMath.Inner b b := by
    apply mul_left_cancel₀ (show (lam:ℂ)≠0 by exact_mod_cast ne_of_gt hl)
    rw [← hxy,bipartite_inner_rev,hyx,map_mul,starRingEnd_ofReal,← bipartite_inner_rev b b]
  have hsum : Qatlib.Foundations.PureStateMath.Inner a a+Qatlib.Foundations.PureStateMath.Inner b b=1 := by
    have h := (normalized_iff_inner_self _).mp hn
    simpa [Qatlib.Foundations.PureStateMath.Inner,dotProduct,Fintype.sum_sum_type] using! h
  have haa : Qatlib.Foundations.PureStateMath.Inner a a=(1/2:ℂ) := by
    linear_combination (1/2:ℂ)*hsum+(1/2:ℂ)*heq
  have hbb : Qatlib.Foundations.PureStateMath.Inner b b=(1/2:ℂ) := heq.symm.trans haa
  have hxx : Qatlib.Foundations.PureStateMath.Inner x x=(1/2:ℂ) := by
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,show Aᴴ*A=1 from hA,Matrix.one_mulVec,haa]
  have hyy : Qatlib.Foundations.PureStateMath.Inner y y=(1/2:ℂ) := by
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,show Bᴴ*B=1 from hB,Matrix.one_mulVec,hbb]
  rw [haa] at hxy
  rw [hbb] at hyx
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
      Matrix.mulVec_sub,Matrix.mulVec_smul,reflectionAbout_mulVec,reflectionAbout_mulVec,Matrix.mulVec_smul,hPBx,hPBy]
    module
  have hgram (s t : Bool) :
      Qatlib.Foundations.PureStateMath.Inner (x+c s•y) (x+c t•y) =
        (1/2:ℂ)+c t*((lam:ℂ)/2)+star (c s)*((lam:ℂ)/2)+star (c s)*c t/2 := by
    rw [bipartite_inner_add_left,bipartite_inner_add_right,bipartite_inner_add_right,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,
      Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,hxx,hyy,hxy,hyx]
    simp only [RCLike.star_def]
    ring
  have hself (s : Bool) : Qatlib.Foundations.PureStateMath.Inner (x+c s•y) (x+c s•y)=(r:ℂ)^2 := by
    rw [hgram]
    cases s <;> apply Complex.ext <;>
      simp [c,Complex.mul_re,Complex.mul_im,pow_two] <;>
      nlinarith only [hr2]
  have horth : Qatlib.Foundations.PureStateMath.Inner (x+c true•y) (x+c false•y)=0 := by
    rw [hgram]
    apply Complex.ext <;>
      simp [c,Complex.mul_re,Complex.mul_im] <;> nlinarith only [hr2]
  intro s
  change Normalized ((r:ℂ)⁻¹•(x+c s•y)) ∧
    bipartiteWalk A B*ᵥ((r:ℂ)⁻¹•(x+c s•y)) =
      bipartitePhase lam s•((r:ℂ)⁻¹•(x+c s•y)) ∧
    Qatlib.Foundations.PureStateMath.Inner ((r:ℂ)⁻¹•(x+c true•y)) ((r:ℂ)⁻¹•(x+c false•y))=0
  refine ⟨?_,?_,?_⟩
  · rw [normalized_iff_inner_self,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,hself]
    simp only [map_inv₀,starRingEnd_ofReal]
    field_simp
  · have hc1 : -1-2*(lam:ℂ)*c s=bipartitePhase lam s := by
      cases s <;> simp [c,bipartitePhase,r] <;> ring
    have hc2 : 2*(lam:ℂ)+(4*(lam:ℂ)^2-1)*c s=bipartitePhase lam s*c s := by
      cases s <;> apply Complex.ext <;>
        simp [c,bipartitePhase,pow_two,Complex.mul_re,Complex.mul_im,r] <;> nlinarith only
            [hr2scaled]
    rw [Matrix.mulVec_smul,Matrix.mulVec_add,Matrix.mulVec_smul,hwx,hwy]
    have hh : -x+(2*(lam:ℂ))•y+c s•((-2*(lam:ℂ))•x+(4*(lam:ℂ)^2-1)•y)=
        (-1-2*(lam:ℂ)*c s)•x+(2*(lam:ℂ)+(4*(lam:ℂ)^2-1)*c s)•y := by module
    rw [hh,hc1,hc2]
    module
  · rw [Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,horth]
    simp

/-- For isometries, the concatenated frame sends discriminant eigenvectors with eigenvalues 1
and 0 to walk eigenvectors with eigenvalues 1 and -1, respectively, and annihilates
discriminant eigenvectors with eigenvalue -1. See [Szegedy2004]. -/
theorem bipartite_endpoint_kernel_transport :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ) (v : QState (I⊕J)),
    IsIsometry A → IsIsometry B →
    ((bipartiteDiscriminant A B*ᵥv=v → bipartiteWalk A B*ᵥ(bipartiteTilde A B*ᵥv)=bipartiteTilde A B*ᵥv)) ∧
    ((bipartiteDiscriminant A B*ᵥv=-v → bipartiteTilde A B*ᵥv=0)) ∧
    ((bipartiteDiscriminant A B*ᵥv=0 → bipartiteWalk A B*ᵥ(bipartiteTilde A B*ᵥv)=-(bipartiteTilde A B*ᵥv))) := by
  intro H I J _ _ _ _ _ _ A B v hA hB
  let a : QState I := fun i => v (.inl i)
  let b : QState J := fun j => v (.inr j)
  have hv : v=Sum.elim a b := by ext (i | j) <;> rfl
  have ht : bipartiteTilde A B*ᵥv=A*ᵥa+B*ᵥb := by
    rw [hv,bipartiteTilde,Matrix.fromCols_mulVec_sumElim]
  have hd : bipartiteDiscriminant A B*ᵥv=Sum.elim ((Aᴴ*B)*ᵥb) ((Bᴴ*A)*ᵥa) := by
    rw [hv,bipartiteDiscriminant,Matrix.fromBlocks_mulVec]
    simp
  refine ⟨?_,?_,?_⟩
  · intro he
    rw [hd] at he
    have hab : (Aᴴ*B)*ᵥb=a := by
      have hh := congrArg (fun w : QState (I⊕J) => fun i => w (.inl i)) he
      simpa only [hv,Sum.elim_inl] using! hh
    have hba : (Bᴴ*A)*ᵥa=b := by
      have hh := congrArg (fun w : QState (I⊕J) => fun j => w (.inr j)) he
      simpa only [hv,Sum.elim_inr] using! hh
    have hi := two_isometry_intersection_gram_and_fixed I J H A B a b hA hB
    have hxy := hi.1.mpr ⟨hab,hba⟩
    have hw := hi.2 hxy
    rw [ht,← hxy,Matrix.mulVec_add,show bipartiteWalk A B*ᵥ(A*ᵥa)=A*ᵥa from hw]
  · intro he
    have hh : Qatlib.Foundations.PureStateMath.Inner (bipartiteTilde A B*ᵥv) (bipartiteTilde A B*ᵥv)=0 := by
      rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,
        (bipartite_discriminant_tilde_bridge H I J A B hA hB).2.1,
        Matrix.add_mulVec,Matrix.one_mulVec,he,add_neg_cancel]
      simp [Qatlib.Foundations.PureStateMath.Inner]
    exact dotProduct_star_self_eq_zero.mp hh
  · intro he
    have hab : (Aᴴ*B)*ᵥb=0 := by
      have hh := congrArg (fun w : QState (I⊕J) => fun i => w (.inl i)) he
      simpa only [hd,Sum.elim_inl,Pi.zero_apply] using! hh
    have hba : (Bᴴ*A)*ᵥa=0 := by
      have hh := congrArg (fun w : QState (I⊕J) => fun j => w (.inr j)) he
      simpa only [hd,Sum.elim_inr,Pi.zero_apply] using! hh
    have hPAx : (A*Aᴴ)*ᵥ(A*ᵥa)=A*ᵥa := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,show Aᴴ*A=1 from hA,Matrix.mul_one]
    have hPBy : (B*Bᴴ)*ᵥ(B*ᵥb)=B*ᵥb := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,show Bᴴ*B=1 from hB,Matrix.mul_one]
    have hPAy : (A*Aᴴ)*ᵥ(B*ᵥb)=0 := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,← Matrix.mulVec_mulVec,hab,Matrix.mulVec_zero]
    have hPBx : (B*Bᴴ)*ᵥ(A*ᵥa)=0 := by
      rw [Matrix.mulVec_mulVec,Matrix.mul_assoc,← Matrix.mulVec_mulVec,hba,Matrix.mulVec_zero]
    rw [ht,bipartiteWalk,← Matrix.mulVec_mulVec,reflectionAbout_mulVec (A*Aᴴ),
      Matrix.mulVec_add,hPAx,hPAy,add_zero]
    have hh : (2:ℂ)•(A*ᵥa)-(A*ᵥa+B*ᵥb)=A*ᵥa-B*ᵥb := by module
    rw [hh,reflectionAbout_mulVec,Matrix.mulVec_sub,hPBx,hPBy]
    module

/-- Matrix multiplication over a finite intermediate index type. -/
private noncomputable abbrev bipartiteMatMul {M N K : Type} [Fintype N]
    (A : Matrix M N ℂ) (B : Matrix N K ℂ) : Matrix M K ℂ :=
  @HMul.hMul (Matrix M N ℂ) (Matrix N K ℂ) (Matrix M K ℂ)
    Matrix.instHMulOfFintypeOfMulOfAddCommMonoid A B

set_option maxHeartbeats 1200000 in

/-- A unitary matrix commuting with an orthogonal projector has an orthonormal eigenframe for
the projector's range, with frame size equal to the projector rank. -/
private theorem bipartite_unitary_projector_frame {H : Type} [Fintype H] [DecidableEq H]
    (W L : Matrix H H ℂ) (hW : W∈unitaryGroup H ℂ)
    (hL : IsOrthogonalProjector L) (hc : W*L=L*W) :
    ∃ (m : ℕ) (F : Matrix H (Fin m) ℂ) (z : Fin m→ℂ),
      IsIsometry F ∧ F*Fᴴ=L ∧ W*F=F*diagonal z ∧ m=L.rank := by
  classical
  let R : Matrix H H ℂ := (1/2:ℂ)•(W+Wᴴ)
  let S : Matrix H H ℂ := (-Complex.I/2:ℂ)•(W-Wᴴ)
  have hRs : R.IsHermitian := by
    change Rᴴ=R
    simp [R,add_comm]
  have hSs : S.IsHermitian := by
    change Sᴴ=S
    simp only [S,Matrix.conjTranspose_smul,Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    norm_num
    module
  have hW1 : Wᴴ*W=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hW.1
  have hW2 : W*Wᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hW.2
  have hcs : Wᴴ*L=L*Wᴴ := by
    have h := congrArg Matrix.conjTranspose hc
    simpa only [Matrix.conjTranspose_mul,show Lᴴ=L from hL.2] using! h.symm
  have hLR : L*R=R*L := by
    simp only [R,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_add,Matrix.add_mul]
    rw [← hc,← hcs]
  have hLS : L*S=S*L := by
    simp only [S,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sub,Matrix.sub_mul]
    rw [← hc,← hcs]
  have hRS : R*S=S*R := by
    simp only [R,S,Matrix.mul_smul,Matrix.smul_mul,Matrix.add_mul,Matrix.sub_mul,
      Matrix.mul_add,Matrix.mul_sub,hW1,hW2]
    module
  let M : Fin 3→Matrix H H ℂ := ![L,R,S]
  let T : Fin 3→Module.End ℂ (EuclideanSpace ℂ H) := fun i => (M i).toEuclideanLin
  have ht : ∀ i,(T i).IsSymmetric := by
    intro i
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    fin_cases i
    · exact hL.2
    · exact hRs
    · exact hSs
  have hmc : ∀ i j,M i*M j=M j*M i := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp [M]
    all_goals first | rfl | exact hLR | exact hLR.symm | exact hLS | exact hLS.symm | exact hRS | exact hRS.symm
  have htc : Pairwise (fun i j => Commute (T i) (T j)) := by
    intro i j _
    change (T i).comp (T j)=(T j).comp (T i)
    simpa only [T,← Matrix.toLpLin_mul_same] using! congrArg Matrix.toEuclideanLin (hmc i j)
  let E := (j : Fin 3) → (T j).Eigenvalues
  let vals : E → (Fin 3→ℂ) := fun e j => (e j).val
  let joint : E → Submodule ℂ (EuclideanSpace ℂ H) := fun e => ⨅ j,(T j).eigenspace (vals e j)
  have hvals : Function.Injective vals := by
    intro e f h
    funext j
    exact Subtype.ext (congrFun h j)
  let ho := (LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces ht).comp hvals
  have htop : (⨆ e,joint e)=⊤ := by
    apply le_antisymm le_top
    rw [← LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute ht htc]
    refine iSup_le fun c => ?_
    by_cases hh : ∀ j,(T j).HasEigenvalue (c j)
    · exact le_iSup joint (fun j=>⟨c j,hh j⟩)
    · obtain ⟨j,hj⟩ := not_forall.mp hh
      have hz : (T j).eigenspace (c j)=⊥ := not_ne_iff.mp hj
      exact (iInf_le _ j).trans (by rw [hz]; exact bot_le)
  have hv : DirectSum.IsInternal joint :=
      ho.isInternal_iff.mpr (by rw [htop,Submodule.top_orthogonal_eq_bot])
  let b :=
      hv.subordinateOrthonormalBasis
      (by simp : Module.finrank ℂ (EuclideanSpace ℂ H)=Fintype.card H) ho
  let chi := fun i : Fin (Fintype.card H) => vals (hv.subordinateOrthonormalBasisIndex
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ H)=Fintype.card H) i ho)
  let U := basisColumns b
  have hU1 : Uᴴ*U=1 := basisColumns_adjoint_mul b
  have hU2 : U*Uᴴ=1 := basisColumns_mul_adjoint b
  have he (i : Fin (Fintype.card H)) (j : Fin 3) :
      M j*ᵥ(fun h => U h i)=chi i j•(fun h => U h i) := by
    have hall := hv.subordinateOrthonormalBasis_subordinate
      (by simp : Module.finrank ℂ (EuclideanSpace ℂ H)=Fintype.card H) i ho
    have h := (Submodule.mem_iInf _).mp hall j
    have hh := Module.End.mem_eigenspace_iff.mp h
    simpa only [T,U,basisColumns_apply,Matrix.ofLp_toLpLin] using!
        congrArg (fun v : EuclideanSpace ℂ H => (⇑v : QState H)) hh
  have hne (i : Fin (Fintype.card H)) : (fun h => U h i)≠0 := by
    intro h
    have hb : b i=0 := by ext j; exact congrFun h j
    exact b.orthonormal.ne_zero i hb
  have hlbin (i : Fin (Fintype.card H)) : chi i 0=0 ∨ chi i 0=1 := by
    have h := congrArg (fun X : Matrix H H ℂ => X*ᵥ(fun h => U h i)) hL.1
    (try dsimp only at h)
    rw [← Matrix.mulVec_mulVec,show L*ᵥ(fun h => U h i)=chi i 0•(fun h => U h i) from he i 0,
      Matrix.mulVec_smul,show L*ᵥ(fun h => U h i)=chi i 0•(fun h => U h i) from he i 0,smul_smul] at h
    have hs := (smul_left_injective ℂ (hne i)) h
    rcases mul_eq_zero.mp (show chi i 0*(chi i 0-1)=0 by linear_combination hs) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  have hLU : L*U=U*diagonal (fun i=>chi i 0) := by
    ext h i
    rw [Matrix.mul_diagonal]
    have hh := congrFun (he i 0) h
    change (L*ᵥ(fun h=>U h i)) h=chi i 0*U h i at hh
    change (L*ᵥ(fun h=>U h i)) h=U h i*chi i 0
    exact hh.trans (mul_comm _ _)
  have hWU : W*U=U*diagonal (fun i=>chi i 1+Complex.I*chi i 2) := by
    have hw : W=R+Complex.I•S := by
      dsimp only [R,S]
      rw [smul_add,smul_smul]
      have hi : Complex.I*(-Complex.I/2)=(1/2:ℂ) := by
        calc
          _ = -(Complex.I*Complex.I)/2 := by ring
          _ = _ := by rw [← pow_two,Complex.I_sq]; norm_num
      rw [hi]
      module
    ext h i
    change (W*ᵥ(fun h=>U h i)) h = _
    rw [hw,Matrix.add_mulVec]
    rw [Matrix.smul_mulVec Complex.I S]
    rw [show R*ᵥ(fun h=>U h i)=chi i 1•(fun h=>U h i) from he i 1,
      show S*ᵥ(fun h=>U h i)=chi i 2•(fun h=>U h i) from he i 2,Matrix.mul_diagonal]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  let K := {i : Fin (Fintype.card H) // chi i 0=1}
  letI : Fintype K := inferInstance
  letI : DecidableEq K := inferInstance
  let F : Matrix H K ℂ := U.submatrix id Subtype.val
  have hF : IsIsometry F := by
    ext i j
    have h := congrFun (congrFun hU1 i.1) j.1
    simpa only [F,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,Matrix.submatrix_apply,id_eq,Subtype.val_inj] using! h
  have hFF : F*Fᴴ=L := by
    have hs : L=U*diagonal (fun i=>chi i 0)*Uᴴ := by
      rw [← hLU,Matrix.mul_assoc,hU2,Matrix.mul_one]
    rw [hs]
    ext h k
    change (bipartiteMatMul F Fᴴ) h k =
        (bipartiteMatMul (bipartiteMatMul U (diagonal (fun i=>chi i 0))) Uᴴ) h k
    simp only [bipartiteMatMul]
    rw [Matrix.mul_apply (M:=F) (N:=Fᴴ),Matrix.mul_apply (M:=U*diagonal (fun i=>chi i 0)) (N:=Uᴴ)]
    simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply,F,Matrix.submatrix_apply,id_eq]
    have hsub := Finset.sum_subtype (F:=inferInstance) (p:=fun i : Fin (Fintype.card H)=>chi i 0=1)
      (Finset.univ.filter (fun i=>chi i 0=1)) (by intro i; simp)
      (fun i=>U h i*star (U k i))
    rw [← hsub,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases hlbin i with h0 | h1
    · simp [h0]
    · simp [h1]
  have hWF : W*F=F*diagonal (fun i=>chi i.1 1+Complex.I*chi i.1 2) := by
    ext h i
    have hh := congrFun (congrFun hWU h) i.1
    change (bipartiteMatMul W F) h i =
        (bipartiteMatMul F (diagonal (fun i=>chi i.1 1+Complex.I*chi i.1 2))) h i
    rw [Matrix.mul_diagonal] at hh
    dsimp only [bipartiteMatMul]
    unfold Matrix.diagonal
    simp only [Matrix.mul_apply,Matrix.of_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    simpa only [F,Matrix.mul_apply,Matrix.submatrix_apply,id_eq] using! hh
  have hcard : Fintype.card K=L.rank := by
    rw [← hFF,Matrix.rank_self_mul_conjTranspose,← Matrix.rank_conjTranspose_mul_self F,
      show Fᴴ*F=1 from hF,Matrix.rank_one]
  let e := (Fintype.equivFin K).symm
  let V : Matrix H (Fin (Fintype.card K)) ℂ := F.submatrix id e
  refine ⟨Fintype.card K,V,fun i=>chi (e i).1 1+Complex.I*chi (e i).1 2,?_,?_,?_,hcard⟩
  · ext i j
    have h := congrFun (congrFun (show Fᴴ*F=1 from hF) (e i)) (e j)
    simpa [V,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,e.injective.eq_iff] using! h
  · have h := Matrix.submatrix_mul F Fᴴ id e id e.bijective
    simp [V,Matrix.conjTranspose_submatrix,hFF]
  · ext h i
    have hh := congrFun (congrFun hWF h) (e i)
    change (bipartiteMatMul W V) h i =
        (bipartiteMatMul V (diagonal (fun i=>chi (e i).1 1+Complex.I*chi (e i).1 2))) h i
    change (∑ j,W h j*F j (e i))=(∑ j : K,F h j*(if j=e i then chi j.1 1+Complex.I*chi j.1 2 else 0)) at hh
    simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hh
    dsimp only [bipartiteMatMul]
    unfold Matrix.diagonal
    simp only [Matrix.mul_apply,Matrix.of_apply,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    simpa only [V,Matrix.mul_apply,Matrix.submatrix_apply,id_eq] using! hh

/-- The orthogonal projector onto the concatenated frame's range commutes with the bipartite
walk and has rank equal to that frame's rank. -/
private theorem bipartite_busy_projector_commutes {H I J : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix H I ℂ) (B : Matrix H J ℂ) :
    let L := bipartiteTilde A B*matrixPseudoinverse (bipartiteTilde A B)
    bipartiteWalk A B*L=L*bipartiteWalk A B ∧ L.rank=(bipartiteTilde A B).rank := by
  let T := bipartiteTilde A B
  let L := T*matrixPseudoinverse T
  have hL : IsOrthogonalProjector L := (matrixPseudoinverse_projectors T).1
  have hLT : L*T=T := mul_matrixPseudoinverse_mul T
  have hLA : L*A=A := by
    ext h i
    have hh := congrFun (congrFun hLT h) (.inl i)
    simpa [T,bipartiteTilde,Matrix.mul_apply] using! hh
  have hLB : L*B=B := by
    ext h j
    have hh := congrFun (congrFun hLT h) (.inr j)
    simpa [T,bipartiteTilde,Matrix.mul_apply] using! hh
  have hLP : L*(A*Aᴴ)=A*Aᴴ := by rw [← Matrix.mul_assoc,hLA]
  have hLQ : L*(B*Bᴴ)=B*Bᴴ := by rw [← Matrix.mul_assoc,hLB]
  have hPL : (A*Aᴴ)*L=A*Aᴴ := by
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,show Lᴴ=L from hL.2]
      using! congrArg Matrix.conjTranspose hLP
  have hQL : (B*Bᴴ)*L=B*Bᴴ := by
    simpa only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,show Lᴴ=L from hL.2]
      using! congrArg Matrix.conjTranspose hLQ
  have hRA : ReflectionAbout (A*Aᴴ)*L=L*ReflectionAbout (A*Aᴴ) := by
    simp [ReflectionAbout,Matrix.sub_mul,Matrix.mul_sub,hLP,hPL]
  have hRB : ReflectionAbout (B*Bᴴ)*L=L*ReflectionAbout (B*Bᴴ) := by
    simp [ReflectionAbout,Matrix.sub_mul,Matrix.mul_sub,hLQ,hQL]
  refine ⟨?_,le_antisymm (Matrix.rank_mul_le_left T (matrixPseudoinverse T)) ?_⟩
  · change (ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))*L=L*(ReflectionAbout (B*Bᴴ)*ReflectionAbout (A*Aᴴ))
    rw [Matrix.mul_assoc,hRA,← Matrix.mul_assoc,hRB,Matrix.mul_assoc]
  · calc
      T.rank=(L*T).rank := congrArg Matrix.rank hLT.symm
      _ ≤ L.rank := Matrix.rank_mul_le_left L T

/-- A complex number satisfying star z times z = 1 is 1, -1, or one of the two `bipartitePhase`
values for some parameter strictly between zero and one. -/
private theorem bipartite_unit_phase_classification (z : ℂ) (hz : star z*z=1) :
    z=1 ∨ z=-1 ∨ ∃ lam : ℝ,0<lam ∧ lam<1 ∧
      (z=bipartitePhase lam true ∨ z=bipartitePhase lam false) := by
  by_cases hp : z=1
  · exact Or.inl hp
  by_cases hm : z=-1
  · exact Or.inr (Or.inl hm)
  have hsq : z.re^2+z.im^2=1 := by
    have h := congrArg Complex.re hz
    simpa [Complex.mul_re,pow_two] using! h
  have hrelo : -1<z.re := by
    have hle : -1≤z.re := by nlinarith [sq_nonneg z.im]
    by_contra hn
    have he : z.re=-1 := by linarith
    have hi : z.im=0 := by nlinarith [sq_nonneg z.im]
    exact hm (by apply Complex.ext <;> simp [he,hi])
  have hrehi : z.re<1 := by
    have hle : z.re≤1 := by nlinarith [sq_nonneg z.im]
    by_contra hn
    have he : z.re=1 := by linarith
    have hi : z.im=0 := by nlinarith [sq_nonneg z.im]
    exact hp (by apply Complex.ext <;> simp [he,hi])
  let lam := Real.sqrt ((z.re+1)/2)
  have hl : 0<lam := Real.sqrt_pos.mpr (by linarith)
  have hl2 : lam^2=(z.re+1)/2 := Real.sq_sqrt (by linarith)
  have hu : lam<1 := by nlinarith [Real.sqrt_nonneg ((z.re+1)/2)]
  let r := Real.sqrt (1-lam^2)
  have hr : 0<r := Real.sqrt_pos.mpr (by nlinarith)
  have hr2 : r^2=1-lam^2 := Real.sq_sqrt (by nlinarith)
  have ht : (2*lam*r)^2=z.im^2 := by
    calc
      _ = 4*lam^2*r^2 := by ring
      _ = 4*((z.re+1)/2)*(1-(z.re+1)/2) := by rw [hr2,hl2]
      _ = z.im^2 := by nlinarith only [hsq]
  have htpos : 0<2*lam*r := by positivity
  refine Or.inr (Or.inr ⟨lam,hl,hu,?_⟩)
  by_cases hi : z.im<0
  · left
    have hie : z.im=-(2*lam*r) := by nlinarith only [ht,htpos,hi]
    apply Complex.ext
    · simp only [bipartitePhase,ite_true,Complex.sub_re,
        Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
        Complex.ofReal_im,mul_zero,zero_mul,sub_zero]
      nlinarith only [hl2]
    · simpa only [bipartitePhase,if_pos rfl,ite_true,Complex.sub_im,Complex.ofReal_im,
        Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,mul_zero,mul_one,one_mul,
        zero_mul,zero_add,zero_sub,r] using! hie
  · right
    have hie : z.im=2*lam*r := by nlinarith only [ht,htpos,hi]
    apply Complex.ext
    · simp only [bipartitePhase,Bool.false_eq_true,ite_false,Complex.sub_re,
        Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
        Complex.ofReal_im,mul_zero,zero_mul,sub_zero,neg_zero]
      nlinarith only [hl2]
    · simpa only [bipartitePhase,Bool.false_eq_true,ite_false,Complex.sub_im,Complex.ofReal_im,
        Complex.mul_im,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
        mul_zero,neg_one_mul,mul_neg_one,zero_mul,zero_add,zero_sub,neg_zero,neg_neg,r] using! hie

/-- For two isometries, the bipartite walk has an orthonormal eigenframe spanning the
concatenated frame's range, of size equal to its rank, with each eigenvalue equal to 1, -1,
or a `bipartitePhase` value for a parameter in (0, 1). See [SommaBoixoBarnum2007] and
[Szegedy2004]. -/
theorem bipartite_complete_busy_spectral_frame :
    ∀ (H I J : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype J] [DecidableEq J] (A : Matrix H I ℂ) (B : Matrix H J ℂ),
    IsIsometry A → IsIsometry B →
    ∃ (m : ℕ) (V : Matrix H (Fin m) ℂ) (z : Fin m→ℂ),
      IsIsometry V ∧ V*Vᴴ=bipartiteTilde A B*matrixPseudoinverse (bipartiteTilde A B) ∧
      bipartiteWalk A B*V=V*Matrix.diagonal z ∧
      m=Matrix.rank (bipartiteTilde A B) ∧
      ∀ i, z i=1 ∨ z i=-1 ∨ ∃ lam : ℝ,0 < lam ∧ lam < 1 ∧
        (z i=bipartitePhase lam true ∨ z i=bipartitePhase lam false) := by
  intro H I J _ _ _ _ _ _ A B hA hB
  let W := bipartiteWalk A B
  let L := bipartiteTilde A B*matrixPseudoinverse (bipartiteTilde A B)
  have hW := (bipartite_discriminant_tilde_bridge H I J A B hA hB).2.2
  have hc := bipartite_busy_projector_commutes A B
  obtain ⟨m,V,z,hV,hVV,hWV,hm⟩ := bipartite_unitary_projector_frame W L hW
    (matrixPseudoinverse_projectors (bipartiteTilde A B)).1 hc.1
  refine ⟨m,V,z,hV,hVV,hWV,hm.trans hc.2,?_⟩
  intro i
  apply bipartite_unit_phase_classification
  let v : QState H := fun h=>V h i
  have hn : Qatlib.Foundations.PureStateMath.Inner v v=1 := by
    have h := congrFun (congrFun (show Vᴴ*V=1 from hV) i) i
    simpa [v,Qatlib.Foundations.PureStateMath.Inner,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using! h
  have he : W*ᵥv=z i•v := by
    ext j
    have hh := congrFun (congrFun hWV j) i
    rw [Matrix.mul_diagonal] at hh
    simpa [v,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm] using! hh
  have hi : Qatlib.Foundations.PureStateMath.Inner (W*ᵥv) (W*ᵥv)=Qatlib.Foundations.PureStateMath.Inner v v := by
    rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,
      show Wᴴ*W=1 from by simpa only [Matrix.star_eq_conjTranspose] using! hW.1,Matrix.one_mulVec]
  rw [he,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_left,Qatlib.Concepts.AmplitudeCore.InvFreePhase.inner_smul_right,hn] at hi
  simpa only [mul_one,RCLike.star_def] using! hi

end Qatlib.Concepts.SpectralFilter.BusySpectrum
