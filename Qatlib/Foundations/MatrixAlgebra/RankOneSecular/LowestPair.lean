/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# Identifying the two lowest Hermitian eigenvalues

`hasRealEigenvalue` expresses the existence of a nonzero eigenvector at a real eigenvalue, while
`nativeBasis` connects explicit eigenpairs to Mathlib's ordered Hermitian spectrum. The module
identifies the two lowest eigenvalues from a classification below a cutoff and a one-dimensional
lowest eigenspace.

The arguments use finite Hermitian spectral theory as developed in [Bhatia1997].

## Main statements

* `eigenvalue_index`: every real eigenvalue occurs in the ordered spectrum.
* `simple_eigenvalue_index`: a one-dimensional eigenspace has a unique spectral index.
* `lowest_pair_of_eigenpairs`: a classified pair below a cutoff is the lowest pair.

## References

* [Bhatia, 1997][Bhatia1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.MatrixAlgebra.RankOneSecular
open scoped Classical Matrix
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The matrix has a nonzero complex eigenvector with real eigenvalue `z`. -/
def hasRealEigenvalue (A : Matrix I I ℂ) (z : ℝ) : Prop :=
  ∃ x : I → ℂ,x≠0 ∧ A*ᵥx=(z:ℂ)•x

/-- The orthonormal eigenvector basis of a Hermitian matrix, indexed compatibly with its ordered
eigenvalues. -/
def nativeBasis {A : Matrix I I ℂ} (hA : A.IsHermitian) :
    OrthonormalBasis (Fin (Fintype.card I)) ℂ (EuclideanSpace ℂ I) :=
  (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace

/-- The matrix acts on each vector of `nativeBasis` by its corresponding ordered eigenvalue. -/
theorem nativeBasis_action {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin (Fintype.card I)) :
    A*ᵥ(⇑(nativeBasis hA i))=(hA.eigenvalues₀ i:ℂ)•(⇑(nativeBasis hA i)) := by
  simpa only [nativeBasis,Matrix.IsHermitian.eigenvalues₀,Matrix.toLpLin_apply,
    RCLike.real_smul_eq_coe_smul] using!
    congr(⇑$((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis finrank_euclideanSpace i))

/-- Every entry of the ordered Hermitian spectrum is a real eigenvalue with a nonzero
eigenvector. -/
theorem native_eigenvalue {A : Matrix I I ℂ} (hA : A.IsHermitian) (i : Fin (Fintype.card I)) :
    hasRealEigenvalue A (hA.eigenvalues₀ i) := by
  refine ⟨⇑(nativeBasis hA i),?_,nativeBasis_action hA i⟩
  intro h
  apply (nativeBasis hA).toBasis.ne_zero i
  apply WithLp.ofLp_injective 2
  exact h

/-- Every real eigenvalue of a Hermitian matrix equals an entry of its ordered spectrum. -/
theorem eigenvalue_index {A : Matrix I I ℂ} (hA : A.IsHermitian) (z : ℝ)
    (hz : hasRealEigenvalue A z) : ∃ i : Fin (Fintype.card I),hA.eigenvalues₀ i=z := by
  obtain ⟨x,hx,he⟩:=hz
  let v : EuclideanSpace ℂ I:=WithLp.toLp 2 x
  have hv : v≠0 := by
    intro hz
    apply hx
    exact congrArg WithLp.ofLp hz
  have hvEq : A.toEuclideanLin v=(z:ℂ)•v := by
    apply WithLp.ofLp_injective 2
    exact he
  have hEigen : Module.End.HasEigenvalue A.toEuclideanLin (z:ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hvEq,hv⟩
  obtain ⟨i,hi⟩:=(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).exists_eigenvalues_eq
    finrank_euclideanSpace hEigen
  exact ⟨i,Complex.ofReal_injective hi⟩

/-- If every eigenvector at `z` is a scalar multiple of one fixed vector, any two ordered
spectral indices with eigenvalue `z` coincide. -/
theorem simple_eigenvalue_index {A : Matrix I I ℂ} (hA : A.IsHermitian) (z : ℝ)
    (w : I → ℂ) (hsimple : ∀ x,A*ᵥx=(z:ℂ)•x → ∃ c : ℂ,x=c•w)
    (i j : Fin (Fintype.card I)) (hi : hA.eigenvalues₀ i=z) (hj : hA.eigenvalues₀ j=z) : i=j := by
  by_contra hij
  obtain ⟨ci,hci⟩:=hsimple (⇑(nativeBasis hA i)) (by rw [← hi];exact nativeBasis_action hA i)
  obtain ⟨cj,hcj⟩:=hsimple (⇑(nativeBasis hA j)) (by rw [← hj];exact nativeBasis_action hA j)
  have hcj0 : cj≠0 := by
    intro hz
    have hbj : (⇑(nativeBasis hA j) : I → ℂ)≠0 := by
      intro h
      apply (nativeBasis hA).toBasis.ne_zero j
      apply WithLp.ofLp_injective 2
      exact h
    apply hbj
    simpa only [hz,zero_smul] using hcj
  have he : nativeBasis hA i=(ci/cj)•nativeBasis hA j := by
    apply WithLp.ofLp_injective 2
    change (⇑(nativeBasis hA i) : I → ℂ)=(ci/cj)•(⇑(nativeBasis hA j))
    rw [hcj,smul_smul,div_mul_cancel₀ ci hcj0]
    exact hci
  have hcoord:=congrArg (fun v : EuclideanSpace ℂ I => (nativeBasis hA).repr v i) he
  simp [hij] at hcoord

/-- If the only real eigenvalues below a cutoff are `lo < hi`, both occur below that cutoff, and
the eigenspace at `lo` is spanned by one vector, then they are the two lowest ordered
eigenvalues. -/
theorem lowest_pair_of_eigenpairs {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (hL : 2≤Fintype.card I) (lo hi cutoff : ℝ) (hlt : lo<hi) (hcut : hi<cutoff)
    (hlo : hasRealEigenvalue A lo) (hhi : hasRealEigenvalue A hi)
    (hclassify : ∀ z,hasRealEigenvalue A z → z<cutoff → z=lo ∨ z=hi)
    (w : I → ℂ) (hsimple : ∀ x,A*ᵥx=(lo:ℂ)•x → ∃ c : ℂ,x=c•w) :
    hA.eigenvalues₀ ⟨Fintype.card I-1,by omega⟩=lo ∧
      hA.eigenvalues₀ ⟨Fintype.card I-2,by omega⟩=hi := by
  let last : Fin (Fintype.card I):=⟨Fintype.card I-1,by omega⟩
  let penult : Fin (Fintype.card I):=⟨Fintype.card I-2,by omega⟩
  obtain ⟨i,hiLo⟩:=eigenvalue_index hA lo hlo
  have hlower : hA.eigenvalues₀ last≤lo := by
    rw [← hiLo]
    apply hA.eigenvalues₀_antitone
    change i.val≤Fintype.card I-1
    omega
  have hlast : hA.eigenvalues₀ last=lo := by
    rcases hclassify _ (native_eigenvalue hA last) (by linarith) with h|h
    · exact h
    · linarith
  obtain ⟨j,hjHi⟩:=eigenvalue_index hA hi hhi
  have hjlast : j≠last := by intro hj;rw [hj,hlast] at hjHi;linarith
  have hupper : hA.eigenvalues₀ penult≤hi := by
    rw [← hjHi]
    apply hA.eigenvalues₀_antitone
    change j.val≤Fintype.card I-2
    have hjbound:=j.isLt
    have hne : j.val≠Fintype.card I-1 := fun he => hjlast (Fin.ext he)
    omega
  have hpenult : hA.eigenvalues₀ penult=hi := by
    rcases hclassify _ (native_eigenvalue hA penult) (by linarith) with h|h
    · have he:=simple_eigenvalue_index hA lo w hsimple penult last h hlast
      have hv:=congrArg Fin.val he
      dsimp [penult,last] at hv
      omega
    · exact h
  exact ⟨hlast,hpenult⟩
end Qatlib.Foundations.MatrixAlgebra.RankOneSecular
