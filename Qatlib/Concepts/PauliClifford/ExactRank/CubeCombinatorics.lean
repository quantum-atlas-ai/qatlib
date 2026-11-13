/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank

/-!
# Hamming weights and affine subspaces of the Boolean cube

This module develops counting and dimension estimates for `cubeWeight` on `BooleanVec n`. It
counts weight layers and balls, bounds a small Hamming ball by a power of two, and finds a
small-weight vector in an affine subspace of positive specified dimension. Binary coding and
Hamming-weight background appears in [NielsenChuang2010].

## Main statements

* `cubeWeight_add_le` gives the triangle inequality for Boolean Hamming weight.
* `card_ball_lt` bounds the radius-`8 * r` ball when `1 ≤ n` and `100 * r ≤ n`.
* `exists_small_weight_mem_affine` finds weight at most `k` when the affine direction has
  positive dimension `n - k`.
* `card_cubeWeight_eq` and `card_cubeWeight_le` count exact-weight layers and bounded-weight
  sets by binomial coefficients.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.PauliClifford.ExactRank
open scoped Classical BigOperators

/-- The Hamming weight of the sum of two Boolean vectors is at most the sum of their Hamming
weights. -/
theorem cubeWeight_add_le {n : ℕ} (x y : BooleanVec n) :
    cubeWeight (x+y) ≤ cubeWeight x+cubeWeight y := by
  simpa [cubeWeight,hammingDist_eq_hammingNorm] using
    hammingDist_triangle (0 : BooleanVec n) x (x+y)

/-- Bounds `5 ^ n` by `2 ^ (3 * n - n / 2)`, with division and subtraction taken in the natural
numbers. -/
private theorem five_pow_bound (n : ℕ) : 5^n ≤ 2^(3*n-n/2) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n ih _ =>
    have hexp : 3*(n+2)-(n+2)/2=(3*n-n/2)+5 := by omega
    rw [hexp,pow_add,pow_add]
    norm_num
    exact Nat.mul_le_mul ih (by norm_num : (25 : ℕ) ≤ 32)

/-- The weighted binomial sum of `n.choose j * 4 ^ (n - j)` for `0 ≤ j ≤ n` equals `5 ^ n`. -/
private theorem weighted_binomial_sum (n : ℕ) :
    (∑ j ∈ Finset.range (n+1), n.choose j*4^(n-j))=5^n := by
  simpa [Nat.mul_comm] using (add_pow (1 : ℕ) 4 n).symm

/-- If `1 ≤ n` and `100 * r ≤ n`, the sum of binomial coefficients through weight `8 * r` is
strictly less than `2 ^ (n - 4 * r)`. -/
theorem card_ball_lt {n r : ℕ} (hn : 1 ≤ n) (hrn : 100*r ≤ n) :
    (∑ j ∈ Finset.range (8*r+1), Nat.choose n j) < 2^(n-4*r) := by
  by_cases hr : r=0
  · subst r
    have h := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (by omega : 0 < n)
    simpa using h
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have h8 : 8*r ≤ n := by omega
  have h4 : 4*r ≤ n := by omega
  have hweighted : (∑ j ∈ Finset.range (8*r+1), n.choose j)*4^(n-8*r) ≤ 5^n := by
    calc
      _ = ∑ j ∈ Finset.range (8*r+1), n.choose j*4^(n-8*r) := Finset.sum_mul _ _ _
      _ ≤ ∑ j ∈ Finset.range (8*r+1), n.choose j*4^(n-j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjr : j ≤ 8*r := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide : 1 ≤ (4 : ℕ)) (by omega))
      _ ≤ ∑ j ∈ Finset.range (n+1), n.choose j*4^(n-j) :=
        Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
      _ = 5^n := weighted_binomial_sum n
  have hExp : 3*n-n/2 < 3*n-20*r := by omega
  have hp := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hExp
  have hfactor : 2^(n-4*r)*4^(n-8*r)=2^(3*n-20*r) := by
    rw [show (4 : ℕ)=2^2 from rfl,← pow_mul,← pow_add]
    congr 1
    omega
  have hh : (∑ j ∈ Finset.range (8*r+1), n.choose j)*4^(n-8*r) <
      2^(n-4*r)*4^(n-8*r) := by
    rw [hfactor]
    exact (hweighted.trans (five_pow_bound n)).trans_lt hp
  exact Nat.lt_of_mul_lt_mul_right hh

/-- Returns the finite set of coordinates where the Boolean vector is nonzero. -/
private def cubeSupport {n : ℕ} (x : BooleanVec n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ 0)

/-- Defines the submodule of Boolean vectors that vanish wherever `x` vanishes. -/
private def supportedSubmodule {n : ℕ} (x : BooleanVec n) : Submodule (ZMod 2) (BooleanVec n) where
  carrier := {v | ∀ i, x i=0 → v i=0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro v w hv hw i hi; simp [hv i hi,hw i hi]
  smul_mem' := by intro c v hv i hi; simp [hv i hi]

/-- Identifies vectors supported inside `cubeSupport x` with arbitrary `ZMod 2`-valued functions
on that support, by restriction and extension by zero. -/
private noncomputable def supportedEquiv {n : ℕ} (x : BooleanVec n) :
    supportedSubmodule x ≃ₗ[ZMod 2] (cubeSupport x → ZMod 2) where
  toFun v i := v.1 i
  invFun w := ⟨fun i => if hi : i ∈ cubeSupport x then w ⟨i,hi⟩ else 0,by
    intro i hi
    have hn : i ∉ cubeSupport x := by simp [cubeSupport,hi]
    simp [hn]⟩
  left_inv v := by
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ cubeSupport x
    · simp [hi]
    · have hx : x i=0 := by simpa [cubeSupport] using hi
      simp [hi,v.2 i hx]
  right_inv w := by
    ext i
    simp [i.property]
  map_add' v w := rfl
  map_smul' c v := rfl

/-- The dimension of the submodule supported inside `x` is the Hamming weight of `x`. -/
private theorem supported_finrank {n : ℕ} (x : BooleanVec n) :
    Module.finrank (ZMod 2) ↥(supportedSubmodule x)=cubeWeight x := by
  rw [(supportedEquiv x).finrank_eq,Module.finrank_pi,Fintype.card_coe]
  rfl

/-- Every nonzero element of `ZMod 2` equals one. -/
private theorem zmod_two_nonzero (a : ZMod 2) (ha : a ≠ 0) : a=1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

/-- Adding a nonzero Boolean vector supported inside `x` strictly decreases the Hamming weight
of `x`. -/
private theorem supported_weight_drop {n : ℕ} (x v : BooleanVec n)
    (hv : v ∈ supportedSubmodule x) (hv0 : v ≠ 0) : cubeWeight (x+v) < cubeWeight x := by
  have hsub : cubeSupport v ⊆ cubeSupport x := by
    intro i hi
    have hvi : v i ≠ 0 := by simpa [cubeSupport] using hi
    simp only [cubeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
    exact fun hx => hvi (hv i hx)
  have hs : cubeSupport (x+v)=cubeSupport x \ cubeSupport v := by
    ext i
    simp only [cubeSupport,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,Pi.add_apply]
    by_cases hx : x i=0
    · have hvz := hv i hx
      simp [hx,hvz]
    · by_cases hvz : v i=0
      · simp [hx,hvz]
      · rw [zmod_two_nonzero (x i) hx,zmod_two_nonzero (v i) hvz]
        simp only [CharTwo.add_self_eq_zero]
        simp
  have hpos : 0 < (cubeSupport v).card := hammingNorm_pos_iff.mpr hv0
  have hle := Finset.card_le_card hsub
  change (cubeSupport (x+v)).card < (cubeSupport x).card
  rw [hs,Finset.card_sdiff_of_subset hsub]
  omega

/-- An affine subspace whose direction has positive dimension `n - k` contains a Boolean vector
of Hamming weight at most `k`. -/
theorem exists_small_weight_mem_affine {n k : ℕ}
    (A : AffineSubspace (ZMod 2) (BooleanVec n))
    (hdim : Module.finrank (ZMod 2) ↥(A.direction)=n-k) (hk : 0 < n-k) :
    ∃ u ∈ A, cubeWeight u ≤ k := by
  have hA : (A : Set (BooleanVec n)).Nonempty := by
    apply (AffineSubspace.nonempty_iff_ne_bot A).mpr
    intro he
    have hb : Module.finrank (ZMod 2) ↥(A.direction)=0 := by simp [he]
    rw [hb] at hdim
    omega
  obtain ⟨p,hp⟩ := hA
  have hex : ∃ w : ℕ, ∃ u ∈ A, cubeWeight u=w := ⟨cubeWeight p,p,hp,rfl⟩
  obtain ⟨u,hu,hwu⟩ := Nat.find_spec hex
  have hmin : ∀ v ∈ A, cubeWeight u ≤ cubeWeight v := by
    intro v hv
    rw [hwu]
    exact Nat.find_min' hex ⟨v,hv,rfl⟩
  have hdis : Disjoint (supportedSubmodule u) A.direction := by
    apply Submodule.disjoint_def.mpr
    intro v hv hD
    by_contra hv0
    have huv : u+v ∈ A := by
      simpa only [vadd_eq_add,add_comm] using A.vadd_mem_of_mem_direction hD hu
    exact (not_le_of_gt (supported_weight_drop u v hv hv0)) (hmin _ huv)
  have hd := Submodule.finrank_add_finrank_le_of_disjoint hdis
  have hn : Module.finrank (ZMod 2) (BooleanVec n)=n := by simp [BooleanVec]
  rw [supported_finrank,hdim,hn] at hd
  exact ⟨u,hu,by omega⟩

/-- Every Boolean vector of length `n` has Hamming weight at most `n`. -/
theorem cubeWeight_le_n {n : ℕ} (x : BooleanVec n) : cubeWeight x ≤ n := by
  simpa [cubeWeight] using (hammingNorm_le_card_fintype (x := x))

/-- Identifies Boolean vectors with finite subsets of their coordinate set through support and
the corresponding indicator vector. -/
private noncomputable def cubeSupportEquiv (n : ℕ) : BooleanVec n ≃ Finset (Fin n) where
  toFun := cubeSupport
  invFun s := fun i => if i ∈ s then 1 else 0
  left_inv x := by
    ext i
    by_cases hx : x i=0
    · simp [cubeSupport,hx]
    · simp [cubeSupport,zmod_two_nonzero (x i) hx]
  right_inv s := by
    ext i
    simp [cubeSupport]

/-- The number of Boolean vectors of length `n` and Hamming weight exactly `k` is `n.choose k`. -/
theorem card_cubeWeight_eq (n k : ℕ) :
    Fintype.card {x : BooleanVec n // cubeWeight x=k}=n.choose k := by
  let e := cubeSupportEquiv n
  let E : {x : BooleanVec n // cubeWeight x=k} ≃ {s : Finset (Fin n) // s.card=k} :=
    { toFun := fun x => ⟨e x.1,x.2⟩
      invFun := fun s => ⟨e.symm s.1,by
        change (e (e.symm s.1)).card=k
        rw [e.apply_symm_apply]
        exact s.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun s => Subtype.ext (e.apply_symm_apply s.1) }
  let E2 : {s : Finset (Fin n) // s.card=k} ≃ (Finset.univ.powersetCard k : Finset (Finset (Fin n))) :=
    { toFun := fun s => ⟨s.1,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,s.2⟩⟩
      invFun := fun s => ⟨s.1,(Finset.mem_powersetCard.mp s.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun s => Subtype.ext rfl }
  rw [Fintype.card_congr E,Fintype.card_congr E2,Fintype.card_coe,Finset.card_powersetCard]
  simp

/-- The number of Boolean vectors of length `n` and Hamming weight at most `t` is the sum of
`n.choose j` over `0 ≤ j ≤ t`. -/
theorem card_cubeWeight_le (n t : ℕ) :
    Fintype.card {x : BooleanVec n // cubeWeight x ≤ t}=
      ∑ j ∈ Finset.range (t+1), n.choose j := by
  let E : {x : BooleanVec n // cubeWeight x ≤ t} ≃
      Σ k : Fin (t+1), {x : BooleanVec n // cubeWeight x=k.val} :=
    { toFun := fun x => ⟨⟨cubeWeight x.1,Nat.lt_succ_of_le x.2⟩,⟨x.1,rfl⟩⟩
      invFun := fun y => ⟨y.2.1,by rw [y.2.2]; exact Nat.le_of_lt_succ y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun y => by
        rcases y with ⟨⟨k,hk⟩,x,hx⟩
        (try dsimp only)
        cases hx
        rfl }
  rw [Fintype.card_congr E,Fintype.card_sigma]
  simp only [card_cubeWeight_eq]
  exact Fin.sum_univ_eq_sum_range _ _

end Qatlib.Concepts.PauliClifford.ExactRank
