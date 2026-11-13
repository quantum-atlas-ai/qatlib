/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureStinespring
import Qatlib.Concepts.Execution.KnownKraus.KrausUnitaryDilation
import Qatlib.Concepts.DimInstruments.DimTreeExec.DimInstrumentTreeExecution
import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
# Adaptive binary compilation of Kraus families

`compileTree` recursively factors a complete Kraus family into binary instruments, using unitary
transport between matrices with equal Gram matrices. `compileFamily` pads an arbitrary finite
family with zero operators and produces leaves preserving the original Kraus branches with
exactly `Nat.clog 2 s` measurements. The constructions relate to finite Kraus implementations in
[CaiEtAl2026].

## Main statements

* `actual_binary_instrument_implementation`: unitary realization with one auxiliary qubit.
* `compiledLeaf_apply`: exact Kraus action at every indexed leaf.
* `compileFamily_depth`: the measurement count after padding.

## References

* [Cai et al., 2026][CaiEtAl2026]
* [Kraus, 1983][Kraus1983]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.Execution.KnownKraus
open Qatlib.Concepts.DimInstruments.DimTreeExec
open scoped ComplexOrder MatrixOrder

namespace Qatlib.Concepts.KrausCompile.BinaryTree

noncomputable section

/-- Matrices with equal Gram matrices induce equal inner products on all pairs of input vectors. -/
theorem gram_equal_inner_action {H X : Type} [Fintype H] [DecidableEq H]
    [Fintype X] [DecidableEq X] (V W : Matrix H X ℂ) (h : Vᴴ * V = Wᴴ * W)
    (a b : EuclideanSpace ℂ X) :
    inner ℂ (Matrix.toEuclideanLin V a) (Matrix.toEuclideanLin V b) =
      inner ℂ (Matrix.toEuclideanLin W a) (Matrix.toEuclideanLin W b) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, Matrix.star_mulVec]
  rw [dotProduct_comm (V *ᵥ b.ofLp), dotProduct_comm (W *ᵥ b.ofLp)]
  simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency true in

/-- For two finite matrices with equal Gram matrices, there exists a unitary on the output space
carrying the first matrix to the second. -/
theorem gram_equal_actual_unitary_transport :
    ∀ (H X : Type) [Fintype H] [DecidableEq H] [Fintype X] [DecidableEq X]
      (V W : Matrix H X ℂ), Vᴴ * V = Wᴴ * W →
      ∃ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ ∧ U * V = W := by
  intro H X _ _ _ _ V W hGram
  letI : InnerProductSpace ℂ (EuclideanSpace ℂ H) := inferInstance
  let v := Matrix.toEuclideanLin V
  let w := Matrix.toEuclideanLin W
  have hinner (a b : EuclideanSpace ℂ X) : inner ℂ (v a) (v b) = inner ℂ (w a) (w b) :=
    gram_equal_inner_action V W hGram a b
  have hker : v.ker ≤ w.ker := by
    intro a ha
    change v a = 0 at ha
    change w a = 0
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    simpa only [ha, inner_zero_left] using (hinner a a).symm
  let L : v.range →ₗ[ℂ] EuclideanSpace ℂ H :=
    (v.ker.liftQ w hker).comp v.quotKerEquivRange.symm.toLinearMap
  letI : InnerProductSpace ℂ v.range := Submodule.innerProductSpace v.range
  have hL (a : EuclideanSpace ℂ X) (ha : v a ∈ v.range) : L ⟨v a, ha⟩ = w a := by
    change (v.ker.liftQ w hker) (v.quotKerEquivRange.symm ⟨v a, ha⟩) = w a
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  have hLis : ∀ a b : v.range, inner ℂ (L a) (L b) = inner ℂ a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [hL a' ⟨a', rfl⟩, hL b' ⟨b', rfl⟩]
    exact (hinner a' b').symm
  let e := (L.isometryOfInner hLis).extend
  have he : Function.Surjective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := e.toLinearMap) rfl).mp e.injective
  let E := LinearIsometryEquiv.ofSurjective e he
  let U : Matrix H H ℂ := Matrix.toEuclideanLin.symm E.toLinearEquiv.toLinearMap
  have hu : U ∈ Matrix.unitaryGroup H ℂ := by
    exact E.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun H ℂ) (EuclideanSpace.basisFun H ℂ)
  refine ⟨U, hu, ?_⟩
  apply Matrix.toEuclideanLin.injective
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.toLin_mul (EuclideanSpace.basisFun X ℂ).toBasis
      (EuclideanSpace.basisFun H ℂ).toBasis (EuclideanSpace.basisFun H ℂ).toBasis]
  rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  have hUmap : Matrix.toEuclideanLin U = E.toLinearEquiv.toLinearMap :=
    Matrix.toEuclideanLin.apply_symm_apply _
  rw [hUmap]
  change E.toLinearEquiv.toLinearMap.comp v = w
  apply LinearMap.ext
  intro a
  change e (v a) = w a
  rw [LinearIsometry.extend_apply (L.isometryOfInner hLis) ⟨v a, LinearMap.mem_range_self v a⟩]
  exact hL a _

/-- The matrix of the Hermitian positive semidefinite square root of `R`. -/
noncomputable def psdRoot {d : ℕ} (R : Operator d) (hR : R.PosSemidef) : Operator d :=
  (HermitianMat.sqrt (⟨R, hR.1⟩ : HermitianMat (Fin d) ℂ)).mat

/-- The Gram matrix of `psdRoot R hR` is `R`. -/
theorem psdRoot_gram {d : ℕ} (R : Operator d) (hR : R.PosSemidef) :
    (psdRoot R hR).conjTranspose * psdRoot R hR = R := by
  unfold psdRoot
  rw [HermitianMat.conjTranspose_mat]
  exact HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hR)

/-- Embeds `ρ` into the data-qubit space with the auxiliary qubit in the zero state. -/
noncomputable def cleanQubitInput {d : ℕ} (ρ : Operator d) :
    Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ :=
  fun x y => if x.2 = 0 ∧ y.2 = 0 then ρ x.1 y.1 else 0

/-- The unnormalized data branch obtained by applying `W` to `cleanQubitInput ρ` and selecting
qubit outcome `b`. -/
noncomputable def measuredQubitBranch {d : ℕ}
    (W : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) (b : Fin 2) (ρ : Operator d) :
    Operator d := fun i j => (W * cleanQubitInput ρ * W.conjTranspose) (i,b) (j,b)

/-- If `W` realizes the binary Kraus action on pure inputs with a clean qubit, its measured
branch on every matrix `ρ` equals `K b * ρ * (K b)ᴴ`. -/
theorem binary_dilation_branch {d : ℕ} (K : Fin 2 → Operator d)
    (W : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)
    (hact : ∀ ψ : QState (Fin d), ApplyGate W (TensorState ψ (Ket (0 : Fin 2))) =
      fun x => ApplyGate (K x.2) ψ x.1) (b : Fin 2) (ρ : Operator d) :
    measuredQubitBranch W b ρ = K b * ρ * (K b).conjTranspose := by
  have hentry (i j : Fin d) (e : Fin 2) : W (i,e) (j,0) = K e i j := by
    have h := congrFun (hact (Ket j)) (i,e)
    simpa [ApplyGate, TensorState, Qatlib.Foundations.PureStateMath.Ket, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type] using h
  ext i j
  rw [kraus_mul_apply]
  simp only [measuredQubitBranch, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, cleanQubitInput, Finset.sum_mul]
  simp only [ite_and]
  simp [hentry]
  rw [Finset.sum_comm]

/-- Every complete binary Kraus family has a unitary realization on the data space and one
auxiliary qubit whose measured branches equal its instrument branches. -/
theorem actual_binary_instrument_implementation {d : ℕ} (K : Fin 2 → Operator d)
    (hK : ∑ b, (K b).conjTranspose * K b = 1) :
    ∃ W : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ,
      W ∈ Matrix.unitaryGroup (Fin d × Fin 2) ℂ ∧
      ∀ b ρ, (Instrument.ofKraus K hK).branch b ρ = measuredQubitBranch W b ρ := by
  obtain ⟨W, hW, hact⟩ := kraus_unitary_dilation K hK 0
  exact ⟨W, hW, fun b ρ => (binary_dilation_branch K W hact b ρ).symm⟩

/-- Factors a nonempty finite Kraus family as `K i = F i * B`, where the Gram matrix of `B` is
the original Gram sum and `F` is a complete Kraus family. -/
theorem group_factor_complete {d m : ℕ} (K : Fin m → Operator d) (seed : Fin m) :
    ∃ (B : Operator d) (F : Fin m → Operator d),
      B.conjTranspose * B = ∑ i, (K i).conjTranspose * K i ∧
      (∑ i, (F i).conjTranspose * F i = 1) ∧ ∀ i, F i * B = K i := by
  classical
  let S := ∑ i, (K i).conjTranspose * K i
  have hS : S.PosSemidef := Matrix.posSemidef_sum _
    (fun i _ => Matrix.posSemidef_conjTranspose_mul_self (K i))
  let B := psdRoot S hS
  have hB : B.conjTranspose * B = S := psdRoot_gram S hS
  let V : Matrix (Fin d × Fin m) (Fin d) ℂ :=
    fun x j => if x.2 = seed then B x.1 j else 0
  let W : Matrix (Fin d × Fin m) (Fin d) ℂ := fun x j => K x.2 x.1 j
  have hgram : V.conjTranspose * V = W.conjTranspose * W := by
    ext i j
    have hv : (V.conjTranspose * V) i j = S i j := by
      simpa [V, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
        using congrArg (fun M => M i j) hB
    rw [hv]
    simp only [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp [S, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  obtain ⟨U, hU, hUV⟩ :=
    gram_equal_actual_unitary_transport
      (Fin d × Fin m) (Fin d) V W hgram
  let F : Fin m → Operator d := fun e i j => U (i,e) (j,seed)
  have hF : ∑ e, (F e).conjTranspose * F e = 1 := by
    ext i j
    have h := congrArg (fun M => M (i,seed) (j,seed))
      (Matrix.mem_unitaryGroup_iff'.mp hU)
    simp only [Matrix.mul_apply, Fintype.sum_prod_type] at h
    rw [Finset.sum_comm] at h
    simpa [F, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, Prod.mk.injEq] using h
  refine ⟨B, F, hB, hF, ?_⟩
  intro e
  ext i j
  have h := congrArg (fun M => M (i,e) j) hUV
  simpa [F, V, W, Matrix.mul_apply, Fintype.sum_prod_type] using h

/-- The quantum channel associated with a complete finite Kraus family. -/
def familyChannel {d r : ℕ} (K : Fin r → Operator d) (hK : KrausComplete K) :
    QuantumChannel d d where
  map := krausMap K
  completelyPositive := completelyPositive_of_krausForm (K := K) (by
    intro ρ
    simp only [krausMap, LinearMap.sum_apply, conjBranch_apply])
  tracePreserving := tracePreserving_of_krausComplete (K := K) (by
    intro ρ
    simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]) hK

/-- The channel of a singleton Kraus family acts by conjugation with its sole Kraus operator. -/
theorem singleton_map {d : ℕ} (K : Fin 1 → Operator d) (hK : KrausComplete K)
    (ρ : Operator d) :
    (familyChannel K hK).map ρ = K 0 * ρ * (K 0).conjTranspose := by
  simp [familyChannel, krausMap]

/-- An equivalence splitting an index in a family of size `2^(n+1)` into a binary branch and an
index of size `2^n`. -/
def splitEquiv (n : ℕ) : Fin 2 × Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm]))

/-- A chosen common right factor whose Gram matrix equals the Gram sum of the nonempty family
`K`. -/
def groupB {d m : ℕ} (K : Fin m → Operator d) (seed : Fin m) : Operator d :=
  Classical.choose (group_factor_complete K seed)

/-- A chosen complete Kraus family factoring `K` through the common right factor `groupB K
seed`. -/
def groupF {d m : ℕ} (K : Fin m → Operator d) (seed : Fin m) : Fin m → Operator d :=
  Classical.choose (Classical.choose_spec (group_factor_complete K seed))

/-- The Gram matrix of the chosen group factor equals the sum of the original Kraus Gram
matrices. -/
theorem groupB_gram {d m : ℕ} (K : Fin m → Operator d) (seed : Fin m) :
    (groupB K seed).conjTranspose * groupB K seed = ∑ i, (K i).conjTranspose * K i :=
  (Classical.choose_spec (Classical.choose_spec (group_factor_complete K seed))).1

/-- The chosen residual family `groupF K seed` is Kraus complete. -/
theorem groupF_complete {d m : ℕ} (K : Fin m → Operator d) (seed : Fin m) :
    KrausComplete (groupF K seed) :=
  (Classical.choose_spec (Classical.choose_spec (group_factor_complete K seed))).2.1

/-- Each original Kraus operator equals its chosen residual operator multiplied by the common
group factor. -/
theorem groupF_factor {d m : ℕ} (K : Fin m → Operator d) (seed : Fin m) (i : Fin m) :
    groupF K seed i * groupB K seed = K i :=
  (Classical.choose_spec (Classical.choose_spec (group_factor_complete K seed))).2.2 i

/-- The zero index in the nonempty family `Fin (2 ^ n)`. -/
def groupSeed (n : ℕ) : Fin (2 ^ n) := ⟨0, by positivity⟩

/-- The common group factor for the half of `K` selected by binary branch `b`. -/
def nodeB {d : ℕ} (n : ℕ) (K : Fin (2 ^ (n+1)) → Operator d) (b : Fin 2) : Operator d :=
  groupB (fun j => K (splitEquiv n (b,j))) (groupSeed n)

/-- The complete residual Kraus family for the half of `K` selected by binary branch `b`. -/
def nodeF {d : ℕ} (n : ℕ) (K : Fin (2 ^ (n+1)) → Operator d) (b : Fin 2) :
    Fin (2 ^ n) → Operator d :=
  groupF (fun j => K (splitEquiv n (b,j))) (groupSeed n)

/-- Splitting a complete family into two groups produces a complete binary family of group
factors. -/
theorem node_complete {d : ℕ} (n : ℕ) (K : Fin (2 ^ (n+1)) → Operator d)
    (hK : KrausComplete K) : KrausComplete (nodeB n K) := by
  change ∑ b, (nodeB n K b).conjTranspose * nodeB n K b = 1
  simp only [nodeB, groupB_gram]
  have hs : (∑ b : Fin 2, ∑ j : Fin (2 ^ n),
      (K (splitEquiv n (b,j))).conjTranspose * K (splitEquiv n (b,j))) =
        ∑ i, (K i).conjTranspose * K i := by
    simpa only [Fintype.sum_prod_type] using
      (splitEquiv n).sum_comp (fun i => (K i).conjTranspose * K i)
  exact hs.trans hK

/-- Recursively compiles a complete family of `2^n` Kraus operators into a depth-`n` binary
measurement program with singleton channels at its leaves. -/
def compileTree {d : ℕ} :
    (n : ℕ) → (K : Fin (2 ^ n) → Operator d) → KrausComplete K → Program d d
  | 0, K, hK => .halt (familyChannel K hK)
  | n+1, K, hK => .measure (Instrument.ofKraus (nodeB n K) (node_complete n K hK))
      (fun b => compileTree n (nodeF n K b)
        (groupF_complete (fun j => K (splitEquiv n (b,j))) (groupSeed n)))

/-- The leaf associated with an original Kraus index in the recursive binary compilation,
including its branch map, measurement record, and measurement count. -/
def compiledLeaf {d : ℕ} : (n : ℕ) → (K : Fin (2 ^ n) → Operator d) →
    (hK : KrausComplete K) → Fin (2 ^ n) → Leaf d d
  | 0, K, hK, _ => ⟨(familyChannel K hK).map, [], 0⟩
  | n+1, K, hK, i =>
    let b := (splitEquiv n).symm i
    let t := compiledLeaf n (nodeF n K b.1)
      (groupF_complete (fun j => K (splitEquiv n (b.1,j))) (groupSeed n)) b.2
    ⟨t.map.comp ((Instrument.ofKraus (nodeB n K) (node_complete n K hK)).branch b.1),
      (2,b.1.val) :: t.record, t.measurements+1⟩

/-- Every indexed `compiledLeaf` belongs to the leaves of the corresponding compiled tree. -/
theorem compiledLeaf_mem {d : ℕ} (n : ℕ) (K : Fin (2 ^ n) → Operator d)
    (hK : KrausComplete K) (i : Fin (2 ^ n)) :
    compiledLeaf n K hK i ∈ leaves (compileTree n K hK) := by
  induction n with
  | zero => simp [compiledLeaf, compileTree, leaves]
  | succ n ih =>
    simp only [compileTree, leaves]
    rw [List.mem_flatten]
    refine ⟨_, List.mem_ofFn.mpr ⟨((splitEquiv n).symm i).1, rfl⟩, ?_⟩
    apply List.mem_map.mpr
    exact ⟨_, ih _ _ _, rfl⟩

/-- The map at the leaf indexed by `i` is exactly conjugation by the original Kraus operator `K
i`. -/
theorem compiledLeaf_apply {d : ℕ} (n : ℕ) (K : Fin (2 ^ n) → Operator d)
    (hK : KrausComplete K) (i : Fin (2 ^ n)) (ρ : Operator d) :
    (compiledLeaf n K hK i).map ρ = K i * ρ * (K i).conjTranspose := by
  induction n generalizing ρ with
  | zero =>
    have hi : i = 0 := by
      have h := i.isLt
      simp only [pow_zero] at h
      apply Fin.ext
      omega
    subst i
    exact singleton_map K hK ρ
  | succ n ih =>
    simp only [compiledLeaf, LinearMap.comp_apply]
    rw [ih]
    change nodeF n K ((splitEquiv n).symm i).1 ((splitEquiv n).symm i).2 *
      (nodeB n K ((splitEquiv n).symm i).1 * ρ *
        (nodeB n K ((splitEquiv n).symm i).1).conjTranspose) *
        (nodeF n K ((splitEquiv n).symm i).1 ((splitEquiv n).symm i).2).conjTranspose = _
    have hf := groupF_factor (fun j => K (splitEquiv n (((splitEquiv n).symm i).1,j)))
      (groupSeed n) ((splitEquiv n).symm i).2
    have hfac : nodeF n K ((splitEquiv n).symm i).1 ((splitEquiv n).symm i).2 *
      nodeB n K ((splitEquiv n).symm i).1 = K i := by
        simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using! hf
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hfac, Matrix.mul_assoc,
      ← Matrix.conjTranspose_mul, hfac]

/-- Every leaf of a compiled tree is equal to `compiledLeaf n K hK i` for some original index
`i`. -/
theorem leaves_compiledLeaf {d : ℕ} (n : ℕ) (K : Fin (2 ^ n) → Operator d)
    (hK : KrausComplete K) (t : Leaf d d) :
    t ∈ leaves (compileTree n K hK) → ∃ i, t = compiledLeaf n K hK i := by
  induction n generalizing t with
  | zero =>
    intro ht
    simp only [compileTree, leaves, List.mem_singleton] at ht
    exact ⟨0, ht⟩
  | succ n ih =>
    intro ht
    simp only [compileTree, leaves] at ht
    rw [List.mem_flatten] at ht
    obtain ⟨ys, hys, htys⟩ := ht
    rw [List.mem_ofFn] at hys
    obtain ⟨b, rfl⟩ := hys
    rw [List.mem_map] at htys
    obtain ⟨u, hu, rfl⟩ := htys
    obtain ⟨j, rfl⟩ := ih _ _ u hu
    exact ⟨splitEquiv n (b,j), by simp [compiledLeaf]⟩

/-- Every leaf of the compilation of a complete family of size `2^n` records exactly `n`
measurements. -/
theorem compileTree_depth {d : ℕ} (n : ℕ) (K : Fin (2 ^ n) → Operator d)
    (hK : KrausComplete K) :
    ∀ t ∈ leaves (compileTree n K hK), t.measurements = n := by
  induction n with
  | zero =>
    intro t ht
    simp only [compileTree, leaves, List.mem_singleton] at ht
    subst t
    rfl
  | succ n ih =>
    intro t ht
    simp only [compileTree, leaves] at ht
    rw [List.mem_flatten] at ht
    obtain ⟨ys, hys, htys⟩ := ht
    rw [List.mem_ofFn] at hys
    obtain ⟨b, rfl⟩ := hys
    rw [List.mem_map] at htys
    obtain ⟨u, hu, rfl⟩ := htys
    simp only [ih _ _ u hu]

/-- The finite-index equivalence induced by `s + (t - s) = t` when `s ≤ t`. -/
def paddingEquiv {s t : ℕ} (h : s ≤ t) : Fin (s + (t-s)) ≃ Fin t :=
  finCongr (Nat.add_sub_of_le h)

/-- Extends a finite operator family from size `s` to size `t` by assigning zero operators to
the added indices. -/
def padFamily {d s t : ℕ} (h : s ≤ t) (K : Fin s → Operator d) : Fin t → Operator d :=
  fun i => Fin.addCases K (fun _ => 0) ((paddingEquiv h).symm i)

/-- Zero padding preserves every original family entry under the canonical index embedding. -/
theorem padFamily_original {d s t : ℕ} (h : s ≤ t) (K : Fin s → Operator d)
    (i : Fin s) : padFamily h K (paddingEquiv h (Fin.castAdd (t-s) i)) = K i := by
  simp [padFamily]

/-- Every added entry of the padded family is the zero operator. -/
theorem padFamily_extra {d s t : ℕ} (h : s ≤ t) (K : Fin s → Operator d)
    (i : Fin (t-s)) : padFamily h K (paddingEquiv h (Fin.natAdd s i)) = 0 := by
  simp [padFamily]

/-- Padding a Kraus-complete family with zero operators preserves Kraus completeness. -/
theorem padFamily_complete {d s t : ℕ} (h : s ≤ t) (K : Fin s → Operator d)
    (hK : KrausComplete K) : KrausComplete (padFamily h K) := by
  change ∑ i, (padFamily h K i).conjTranspose * padFamily h K i = 1
  rw [← (paddingEquiv h).sum_comp]
  simp only [padFamily, Equiv.symm_apply_apply, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, Matrix.conjTranspose_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  exact hK

/-- Pads a complete finite Kraus family to size `2^(Nat.clog 2 s)` and compiles it into a binary
measurement program. -/
def compileFamily {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K) : Program d d :=
  compileTree (Nat.clog 2 s) (padFamily (Nat.le_pow_clog (by norm_num) s) K)
    (padFamily_complete _ K hK)

/-- Every leaf of `compileFamily K hK` records exactly `Nat.clog 2 s` measurements. -/
theorem compileFamily_depth {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K) :
    ∀ t ∈ leaves (compileFamily K hK), t.measurements = Nat.clog 2 s :=
  compileTree_depth _ _ _

/-- Each original Kraus branch is realized exactly by some leaf of `compileFamily K hK`. -/
theorem compileFamily_original {d s : ℕ} (K : Fin s → Operator d) (hK : KrausComplete K)
    (i : Fin s) : ∃ t ∈ leaves (compileFamily K hK),
      ∀ ρ, t.map ρ = K i * ρ * (K i).conjTranspose := by
  let h := Nat.le_pow_clog (by norm_num : 1 < 2) s
  let j := paddingEquiv h (Fin.castAdd (2^(Nat.clog 2 s)-s) i)
  refine ⟨compiledLeaf _ (padFamily h K) _ j, compiledLeaf_mem _ _ _ _, ?_⟩
  intro ρ
  rw [compiledLeaf_apply, show padFamily h K j = K i from padFamily_original h K i]

end
end Qatlib.Concepts.KrausCompile.BinaryTree
