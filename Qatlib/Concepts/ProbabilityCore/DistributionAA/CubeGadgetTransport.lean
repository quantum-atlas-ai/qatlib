/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeProductPoincare
public import Qatlib.Concepts.ProbabilityCore.DistributionAA.CubeMvPolynomial

@[expose] public section
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Expresses a weighted product expectation after a Boolean map as a biased cube expectation. -/
theorem cube_product_bool_map {α : Type} [Fintype α] (w : α → ℝ) (hw : ∑ a, w a=1)
    (g : α → Bool) (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (∑ z : Fin n → α, (∏ i, w (z i))*f (fun i => g (z i))) =
      cubeExpect n (muWeight (∑ a, w a*(if g a then (1 : ℝ) else 0)) n) f := by
  let r := ∑ a, w a*(if g a then (1 : ℝ) else 0)
  have hbool (H : Bool → ℝ) : (∑ a, w a*H (g a))=(1-r)*H false+r*H true := by
    have he (a) : w a*H (g a)=w a*(if g a then (1 : ℝ) else 0)*H true+
        (w a-w a*(if g a then (1 : ℝ) else 0))*H false := by cases g a <;> simp
    simp_rw [he]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,← Finset.sum_mul,Finset.sum_sub_distrib,hw]
    dsimp [r]
    ring
  induction n with
  | zero =>
    simp only [cubeExpect,muWeight,Finset.univ_eq_empty,Finset.prod_empty,one_mul]
    simp only [Fintype.sum_unique]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih =>
    have he := Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => α))
      (fun z => (∏ i, w (z i))*f (fun i => g (z i)))
    rw [← he,Fintype.sum_prod_type,cube_mu_expect_cons]
    change (∑ a : α, ∑ z : Fin n → α, (∏ i : Fin (n+1), w ((Fin.cons a z : Fin (n+1) → α) i))*
      f (fun i : Fin (n+1) => g ((Fin.cons a z : Fin (n+1) → α) i))) = _
    have hc (a : α) (z : Fin n → α) : (fun i : Fin (n+1) => g ((Fin.cons a z : Fin (n+1) → α) i))=
        (Fin.cons (g a) (fun i => g (z i)) : Fin (n+1) → Bool) := by
      ext i; refine Fin.cases rfl (fun _ => rfl) i
    simp_rw [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,hc,mul_assoc,← Finset.mul_sum]
    have ht (a : α) := ih (fun y => f (Fin.cons (g a) y))
    simp_rw [ht]
    exact hbool (fun b => cubeExpect n (muWeight r n) (fun x => f (Fin.cons b x)))

def cubeBlocksEquiv (n m : ℕ) : (Fin (n*m) → Bool) ≃ (Fin n → Fin m → Bool) where
  toFun := fun z i j => z (finProdFinEquiv (i,j))
  invFun := fun z k => z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv z := by ext k; exact congrArg z (finProdFinEquiv.apply_symm_apply k)
  right_inv z := by ext i j; simp

def cubeBlockMap {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin (n*m) → Bool) : Fin n → Bool :=
  fun i => g (cubeBlocksEquiv n m z i)

/-- Factors the product weight of a block-encoded vector into the weights of its blocks. -/
theorem cube_block_weight (p : ℝ) (n m : ℕ) (z : Fin n → Fin m → Bool) :
    muWeight p (n*m) ((cubeBlocksEquiv n m).symm z)=∏ i, muWeight p m (z i) := by
  have he := Equiv.prod_comp (@finProdFinEquiv n m) (fun k : Fin (n*m) =>
    if (cubeBlocksEquiv n m).symm z k then p else 1-p)
  unfold muWeight
  rw [← he,Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  change (if z (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 then p else 1-p) = _
  rw [finProdFinEquiv.symm_apply_apply]

/-- Transports a block-composed product expectation to the cube with bias equal to the block
acceptance probability. -/
theorem cube_block_expectation {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n m : ℕ}
    (g : (Fin m → Bool) → Bool) (f : (Fin n → Bool) → ℝ) :
    cubeExpect (n*m) (muWeight p (n*m)) (fun z => f (cubeBlockMap g z)) =
      cubeExpect n (muWeight (cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0)) n) f := by
  have he := Equiv.sum_comp (cubeBlocksEquiv n m).symm
    (fun z => muWeight p (n*m) z*f (cubeBlockMap g z))
  rw [cubeExpect,← he]
  simp only [cube_block_weight]
  have hg (z : Fin n → Fin m → Bool) : cubeBlockMap g ((cubeBlocksEquiv n m).symm z)=fun i => g (z i) := by
    ext i
    change g (cubeBlocksEquiv n m ((cubeBlocksEquiv n m).symm z) i)=g (z i)
    rw [(cubeBlocksEquiv n m).apply_symm_apply]
  simp only [hg]
  exact cube_product_bool_map (muWeight p m) (muWeight_cubeWeight hp0 hp1 m).2 g n f

/-- Transports a block-composed product variance to the cube with bias equal to the block
acceptance probability. -/
theorem cube_block_variance {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n m : ℕ}
    (g : (Fin m → Bool) → Bool) (f : (Fin n → Bool) → ℝ) :
    cubeVar (n*m) (muWeight p (n*m)) (fun z => f (cubeBlockMap g z)) =
      cubeVar n (muWeight (cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0)) n) f := by
  unfold cubeVar
  rw [cube_block_expectation hp0 hp1 g f]
  exact cube_block_expectation hp0 hp1 g (fun y => (f y-cubeExpect n
    (muWeight (cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0)) n) f)^2)

/-- Shows that two Boolean vectors differing only at one coordinate are equal or related by
flipping that coordinate. -/
theorem cube_single_coordinate_change {n : ℕ} (x y : Fin n → Bool) (i : Fin n)
    (h : ∀ k, k ≠ i → y k=x k) : y=x ∨ y=cubeFlip x i := by
  by_cases hi : y i=x i
  · left
    ext k
    by_cases hk : k=i
    · subst k; exact hi
    · exact h k hk
  · right
    ext k
    by_cases hk : k=i
    · subst k
      cases hx : x i <;> cases hy : y i <;> simp_all [cubeFlip]
    · simp [cubeFlip,hk,h k hk]

/-- Shows that flipping a bit in one block leaves every other block output unchanged. -/
theorem cube_block_flip_other {n m : ℕ} (g : (Fin m → Bool) → Bool) (z : Fin (n*m) → Bool)
    (i : Fin n) (j : Fin m) (k : Fin n) (hk : k ≠ i) :
    cubeBlockMap g (cubeFlip z (finProdFinEquiv (i,j))) k=cubeBlockMap g z k := by
  change g (cubeBlocksEquiv n m (cubeFlip z (finProdFinEquiv (i,j))) k)=g (cubeBlocksEquiv n m z k)
  apply congrArg g
  funext l
  have hkl : finProdFinEquiv (k,l) ≠ finProdFinEquiv (i,j) := by
    intro he
    have hp := finProdFinEquiv.injective he
    exact hk (congrArg Prod.fst hp)
  exact ite_eq_right hkl

/-- Bounds a bit influence of a block composition by the corresponding outer-function influence
at the induced bias. -/
theorem cube_block_influence {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {n m : ℕ}
    (g : (Fin m → Bool) → Bool) (f : (Fin n → Bool) → ℝ) (i : Fin n) (j : Fin m) :
    cubeInf (n*m) (muWeight p (n*m)) (fun z => f (cubeBlockMap g z)) (finProdFinEquiv (i,j)) ≤
      cubeInf n (muWeight (cubeExpect m (muWeight p m) (fun z => if g z then (1 : ℝ) else 0)) n) f i := by
  have hpnt (z) : (f (cubeBlockMap g z)-f (cubeBlockMap g (cubeFlip z (finProdFinEquiv (i,j)))))^2 ≤
      (f (cubeBlockMap g z)-f (cubeFlip (cubeBlockMap g z) i))^2 := by
    obtain he | he := cube_single_coordinate_change (cubeBlockMap g z)
      (cubeBlockMap g (cubeFlip z (finProdFinEquiv (i,j)))) i (cube_block_flip_other g z i j)
    · rw [he,sub_self,zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · rw [he]
  change cubeExpect (n*m) (muWeight p (n*m)) _ ≤ _
  calc
    _ ≤ cubeExpect (n*m) (muWeight p (n*m)) (fun z =>
        (f (cubeBlockMap g z)-f (cubeFlip (cubeBlockMap g z) i))^2) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hpnt z) ((muWeight_cubeWeight hp0 hp1 (n*m)).1 z)
    _ = _ := cube_block_expectation hp0 hp1 g (fun y => (f y-f (cubeFlip y i))^2)

end Qatlib.Concepts.ProbabilityCore.DistributionAA
