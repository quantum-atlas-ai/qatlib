/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.ExactRank.CubeCombinatorics

/-!
# Unequal-weight collisions for functions of small stabilizer rank

This module combines affine dimension estimates, quadratic Boolean derivatives, and Hamming-ball
counting to prove `exact_rank_collision`. For the function class measured by `stabilizerRank`,
rank at most `r` with `1 ≤ n` and `100 * r ≤ n` forces equal function values at two Boolean
vectors of different Hamming weights. The linear, quadratic, and affine-support representation
of stabilizer data is motivated by [DehaeneDeMoor2003].

## Main statements

* `stabilizer_constant_affine_region` makes finitely many Boolean linear forms and
  affine-support membership conditions constant with dimension loss at most `2 * r`.
* `quadFun_directional_affine` expresses a directional difference of a Boolean quadratic
  function as an affine function.
* `exact_rank_collision` produces an unequal-weight pair with equal values under the rank and
  dimension bounds.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.PauliClifford.ExactRank.StabilizerRank

namespace Qatlib.Concepts.PauliClifford.ExactRank
open scoped Classical BigOperators

/-- The vector space `BooleanVec n` has dimension `n` over `ZMod 2`. -/
private theorem cube_finrank (n : ℕ) : Module.finrank (ZMod 2) (BooleanVec n)=n := by
  simp [BooleanVec]

/-- Intersecting a submodule with the kernel of a linear map loses at most the dimension of the
codomain. -/
private theorem inf_ker_codim {V W : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) V]
    [FiniteDimensional (ZMod 2) W] (D : Submodule (ZMod 2) V) (L : V →ₗ[ZMod 2] W) :
    Module.finrank (ZMod 2) ↥D ≤ Module.finrank (ZMod 2) ↥(D ⊓ LinearMap.ker L)+
      Module.finrank (ZMod 2) W := by
  have hi := Submodule.finrank_sup_add_finrank_inf_eq D (LinearMap.ker L)
  have hs := (D ⊔ LinearMap.ker L).finrank_le
  have hn := L.finrank_range_add_finrank_ker
  have hr := (LinearMap.range L).finrank_le
  omega

/-- The affine space through `p` with direction `D` is contained in `U` when `p` belongs to `U`
and `D` is contained in its direction. -/
private theorem affine_subregion {n : ℕ} (U : AffineSubspace (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) (hp : p ∈ U) (D : Submodule (ZMod 2) (BooleanVec n)) (hD : D ≤ U.direction) :
    AffineSubspace.mk' p D ≤ U := by
  intro x hx
  have hv : x-p ∈ D := AffineSubspace.mem_mk'.mp hx
  have he := AffineSubspace.vadd_mem_of_mem_direction (hD hv) hp
  simpa only [vadd_eq_add,sub_add_cancel] using he

/-- Through any point of `U`, there is an affine subspace contained in `U` on which the given
Boolean linear form is constant. The direction dimension loss is at most one. -/
private theorem linear_level_region {n : ℕ} (U : AffineSubspace (ZMod 2) (BooleanVec n))
    (p : BooleanVec n) (hp : p ∈ U) (L : BooleanVec n →ₗ[ZMod 2] ZMod 2) :
    ∃ W : AffineSubspace (ZMod 2) (BooleanVec n),
      p ∈ W ∧ W ≤ U ∧
      Module.finrank (ZMod 2) ↥U.direction ≤ Module.finrank (ZMod 2) ↥W.direction+1 ∧
      ∀ x ∈ W, ∀ y ∈ W, L x=L y := by
  let D := U.direction ⊓ LinearMap.ker L
  let W := AffineSubspace.mk' p D
  have hW : W ≤ U := affine_subregion U p hp D inf_le_left
  have hd : W.direction=D := AffineSubspace.direction_mk' p D
  refine ⟨W,AffineSubspace.self_mem_mk' _ _,hW,?_,?_⟩
  · rw [hd]
    simpa using inf_ker_codim U.direction L
  · intro x hx y hy
    have hx0 : L (x-p)=0 := (AffineSubspace.mem_mk'.mp hx).2
    have hy0 : L (y-p)=0 := (AffineSubspace.mem_mk'.mp hy).2
    have hxp : L x=L p := sub_eq_zero.mp (by simpa only [map_sub] using hx0)
    have hyp : L y=L p := sub_eq_zero.mp (by simpa only [map_sub] using hy0)
    exact hxp.trans hyp.symm

/-- A nonempty affine space `U` contains a nonempty affine subspace on which membership in `A`
is constant, with direction dimension loss at most one. -/
private theorem support_constant_region {n : ℕ}
    (U A : AffineSubspace (ZMod 2) (BooleanVec n)) (hU : (U : Set (BooleanVec n)).Nonempty) :
    ∃ W : AffineSubspace (ZMod 2) (BooleanVec n),
      (W : Set (BooleanVec n)).Nonempty ∧ W ≤ U ∧
      Module.finrank (ZMod 2) ↥U.direction ≤ Module.finrank (ZMod 2) ↥W.direction+1 ∧
      ∀ x ∈ W, ∀ y ∈ W, (x ∈ A ↔ y ∈ A) := by
  by_cases hUA : U ≤ A
  · refine ⟨U,hU,le_rfl,by omega,?_⟩
    intro x hx y hy
    exact iff_of_true (hUA hx) (hUA hy)
  obtain ⟨q,hq,hqA⟩ : ∃ q ∈ U, q ∉ A := by
    by_contra he
    apply hUA
    intro q hq
    by_contra hqa
    exact he ⟨q,hq,hqa⟩
  by_cases hA : (A : Set (BooleanVec n)).Nonempty
  · obtain ⟨p,hp⟩ := hA
    have hqp : q-p ∉ A.direction := by
      intro h
      have he := AffineSubspace.vadd_mem_of_mem_direction h hp
      exact hqA (by simpa using he)
    obtain ⟨L,hL,hker⟩ := Submodule.exists_le_ker_of_notMem hqp
    obtain ⟨W,hqW,hWU,hd,hconst⟩ := linear_level_region U q hq L
    refine ⟨W,⟨q,hqW⟩,hWU,hd,?_⟩
    intro x hx y hy
    have hnone (z : BooleanVec n) (hz : z ∈ W) : z ∉ A := by
      intro hzA
      have hzp : z-p ∈ A.direction := AffineSubspace.vsub_mem_direction hzA hp
      have hzero : L (z-p)=0 := hker hzp
      have hvalue : L z=L q := hconst z hz q hqW
      apply hL
      simpa only [map_sub,hvalue] using hzero
    exact iff_of_false (hnone x hx) (hnone y hy)
  · refine ⟨U,hU,le_rfl,by omega,?_⟩
    intro x _ y _
    exact iff_of_false (fun hx => hA ⟨x,hx⟩) (fun hy => hA ⟨y,hy⟩)

/-- Packages the Boolean dot product with `a` as a linear map over `ZMod 2`. -/
private def dotLinear {n : ℕ} (a : BooleanVec n) : BooleanVec n →ₗ[ZMod 2] ZMod 2 where
  toFun := booleanDot a
  map_add' x y := (Qatlib.Concepts.PauliClifford.ExactRank.booleanDotHom a).map_add x y
  map_smul' c x := by
    simp only [booleanDot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- A nonempty affine space contains a nonempty affine subspace where all `r` specified dot
products and affine-support membership conditions are constant. The direction dimension loss
is at most `2 * r`. -/
theorem stabilizer_constant_affine_region {n r : ℕ} (a : Fin r → BooleanVec n)
    (A : Fin r → AffineSubspace (ZMod 2) (BooleanVec n))
    (U : AffineSubspace (ZMod 2) (BooleanVec n)) (hU : (U : Set (BooleanVec n)).Nonempty) :
    ∃ W : AffineSubspace (ZMod 2) (BooleanVec n),
      (W : Set (BooleanVec n)).Nonempty ∧ W ≤ U ∧
      Module.finrank (ZMod 2) ↥U.direction ≤ Module.finrank (ZMod 2) ↥W.direction+2*r ∧
      ∀ j, ∀ x ∈ W, ∀ y ∈ W,
        booleanDot (a j) x=booleanDot (a j) y ∧ (x ∈ A j ↔ y ∈ A j) := by
  induction r generalizing U with
  | zero =>
    refine ⟨U,hU,le_rfl,by simp,?_⟩
    intro j
    exact Fin.elim0 j
  | succ r ih =>
    obtain ⟨p,hp⟩ := hU
    obtain ⟨V,hpV,hVU,hdV,hphase⟩ := linear_level_region U p hp (dotLinear (a 0))
    obtain ⟨T,hT,hTV,hdT,hsupport⟩ := support_constant_region V (A 0) ⟨p,hpV⟩
    obtain ⟨W,hW,hWT,hdW,hrest⟩ := ih (fun j => a j.succ) (fun j => A j.succ) T hT
    refine ⟨W,hW,hWT.trans (hTV.trans hVU),by omega,?_⟩
    intro j x hx y hy
    refine Fin.cases ?_ (fun k => hrest k x hx y hy) j
    exact ⟨hphase x (hTV (hWT hx)) y (hTV (hWT hy)),
      hsupport x (hWT hx) y (hWT hy)⟩

/-- Defines the linear cross-term map associated with `Q` and direction `v`, summing `Q i j * (x
i * v j + v i * x j)` over both coordinates. -/
private def derivativeLinear {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (v : BooleanVec n) :
    BooleanVec n →ₗ[ZMod 2] ZMod 2 where
  toFun x := ∑ i, ∑ j, Q i j*(x i*v j+v i*x j)
  map_add' x y := by
    change (∑ i, ∑ j, Q i j*((x i+y i)*v j+v i*(x j+y j)))=
      (∑ i, ∑ j, Q i j*(x i*v j+v i*x j))+(∑ i, ∑ j, Q i j*(y i*v j+v i*y j))
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  map_smul' c x := by
    change (∑ i, ∑ j, Q i j*((c*x i)*v j+v i*(c*x j)))=
      c*(∑ i, ∑ j, Q i j*(x i*v j+v i*x j))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- For any direction `v`, the sum of a Boolean quadratic function at `x` and `x + v` is an
affine function of `x`. -/
theorem quadFun_directional_affine {n : ℕ} (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (b : BooleanVec n) (c : ZMod 2) (v : BooleanVec n) :
    ∃ L : BooleanVec n →ₗ[ZMod 2] ZMod 2, ∃ d : ZMod 2,
      ∀ x, quadFun Q b c x+quadFun Q b c (x+v)=L x+d := by
  refine ⟨derivativeLinear Q v,quadFun Q b 0 v,?_⟩
  intro x
  let AA := ∑ i, ∑ j, Q i j*x i*x j
  let BB := ∑ i, ∑ j, Q i j*(x i*v j+v i*x j)
  let CC := ∑ i, ∑ j, Q i j*v i*v j
  let DD := ∑ i, b i*x i
  let EE := ∑ i, b i*v i
  have hq : (∑ i, ∑ j, Q i j*(x i+v i)*(x j+v j))=AA+BB+CC := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hl : (∑ i, b i*(x i+v i))=DD+EE := by
    simp only [mul_add,Finset.sum_add_distrib,DD,EE]
  have he : quadFun Q b c (x+v)=AA+BB+CC+DD+EE+c := by
    simp only [quadFun,Pi.add_apply,hq,hl]
    abel
  change (AA+DD+c)+quadFun Q b c (x+v)=BB+(CC+EE+0)
  rw [he]
  calc
    _ = (AA+AA)+(DD+DD)+(c+c)+(BB+CC+EE) := by abel
    _ = BB+(CC+EE+0) := by
      simp only [CharTwo.add_self_eq_zero AA,CharTwo.add_self_eq_zero DD,
        CharTwo.add_self_eq_zero c,zero_add,add_zero,add_assoc]

/-- Translation by a chosen point `p` identifies the points of an affine subspace with the
vectors in its direction subspace. -/
private noncomputable def affine_direction_equiv {n : ℕ}
    (U : AffineSubspace (ZMod 2) (BooleanVec n)) (p : BooleanVec n) (hp : p ∈ U) :
    ↥U ≃ ↥U.direction where
  toFun x := ⟨x.1-p,AffineSubspace.vsub_mem_direction x.2 hp⟩
  invFun v := ⟨v.1+p,AffineSubspace.vadd_mem_of_mem_direction v.2 hp⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

/-- A nonempty Boolean affine subspace has cardinality two raised to the dimension of its
direction. -/
private theorem affine_card {n : ℕ} (U : AffineSubspace (ZMod 2) (BooleanVec n))
    (hU : (U : Set (BooleanVec n)).Nonempty) :
    Fintype.card ↥U=2^(Module.finrank (ZMod 2) ↥U.direction) := by
  obtain ⟨p,hp⟩ := hU
  rw [Fintype.card_congr (affine_direction_equiv U p hp),Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card]

/-- A map between finite types with nonempty codomain has a fiber whose size, multiplied by the
codomain cardinality, is at least the domain cardinality. -/
private theorem largest_fiber {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Nonempty Y] (f : X → Y) :
    ∃ y, Fintype.card X ≤ Fintype.card Y*Fintype.card {x : X // f x=y} := by
  obtain ⟨y,hy⟩ := Finite.exists_max (fun y : Y => Fintype.card {x : X // f x=y})
  refine ⟨y,?_⟩
  calc
    _ = ∑ z : Y, Fintype.card {x : X // f x=z} := by
      rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f),Fintype.card_sigma]
    _ ≤ ∑ _ : Y, Fintype.card {x : X // f x=y} := Finset.sum_le_sum (fun z _ => hy z)
    _ = _ := by simp

/-- If a nonempty affine subspace has direction dimension at least `n - 2 * r`, with `1 ≤ n` and
`100 * r ≤ n`, it contains two vectors at Hamming distance greater than `8 * r` on which all
`r` specified quadratic functions agree. -/
private theorem quadratic_far_pair {n r : ℕ} (U : AffineSubspace (ZMod 2) (BooleanVec n))
    (hU : (U : Set (BooleanVec n)).Nonempty)
    (hdim : n-2*r ≤ Module.finrank (ZMod 2) ↥U.direction)
    (Q : Fin r → Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin r → BooleanVec n)
    (c : Fin r → ZMod 2) (hn : 1 ≤ n) (hrn : 100*r ≤ n) :
    ∃ x ∈ U, ∃ y ∈ U, 8*r < cubeWeight (x+y) ∧
      ∀ j, quadFun (Q j) (b j) (c j) x=quadFun (Q j) (b j) (c j) y := by
  let Γ : ↥U → BooleanVec r := fun x j => quadFun (Q j) (b j) (c j) x.1
  obtain ⟨α,hlarge⟩ := largest_fiber Γ
  have hcardU : 2^(n-2*r) ≤ Fintype.card ↥U := by
    rw [affine_card U hU]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hdim
  have hmass : 2^r*2^(n-3*r) ≤ 2^r*Fintype.card {x : ↥U // Γ x=α} := by
    calc
      _ = 2^(n-2*r) := by rw [← pow_add]; congr 1; omega
      _ ≤ Fintype.card ↥U := hcardU
      _ ≤ _ := by simpa [BooleanVec] using hlarge
  have hcard : 2^(n-3*r) ≤ Fintype.card {x : ↥U // Γ x=α} := by
    exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℕ) < 2^r)).mp hmass
  have hpos : 0 < Fintype.card {x : ↥U // Γ x=α} :=
    (pow_pos (by decide : (0 : ℕ) < 2) _).trans_le hcard
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
  by_contra hfar
  have hdist (x : {x : ↥U // Γ x=α}) : cubeWeight (x.1.1+p.1.1) ≤ 8*r := by
    by_contra h
    apply hfar
    refine ⟨x.1.1,x.1.2,p.1.1,p.1.2,by omega,?_⟩
    intro j
    exact congrFun (x.2.trans p.2.symm) j
  let f : {x : ↥U // Γ x=α} → {z : BooleanVec n // cubeWeight z ≤ 8*r} :=
    fun x => ⟨x.1.1+p.1.1,hdist x⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact add_right_cancel (congrArg Subtype.val he)
  have hball := Fintype.card_le_of_injective f hf
  rw [card_cubeWeight_le] at hball
  have hlower : 2^(n-4*r) ≤ Fintype.card {x : ↥U // Γ x=α} :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans hcard
  exact (not_le_of_gt (card_ball_lt hn hrn)) (hlower.trans hball)

/-- Adding any Boolean vector to itself gives the zero vector. -/
private theorem cube_add_self {n : ℕ} (x : BooleanVec n) : x+x=0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

/-- Under `1 ≤ n` and `100 * r ≤ n`, two Boolean vectors of different Hamming weights agree on
every specified dot product, quadratic value, and affine-support membership condition. -/
private theorem stabilizer_data_collision {n r : ℕ} (a : Fin r → BooleanVec n)
    (Q : Fin r → Matrix (Fin n) (Fin n) (ZMod 2)) (b : Fin r → BooleanVec n)
    (c : Fin r → ZMod 2) (A : Fin r → AffineSubspace (ZMod 2) (BooleanVec n))
    (hn : 1 ≤ n) (hrn : 100*r ≤ n) :
    ∃ y z : BooleanVec n, cubeWeight y ≠ cubeWeight z ∧
      ∀ j, booleanDot (a j) y=booleanDot (a j) z ∧
        quadFun (Q j) (b j) (c j) y=quadFun (Q j) (b j) (c j) z ∧
        (y ∈ A j ↔ z ∈ A j) := by
  obtain ⟨U,hU,_,hUd,hconst⟩ := stabilizer_constant_affine_region a A ⊤
    ⟨0,AffineSubspace.mem_top _ _ _⟩
  have htop : n ≤ Module.finrank (ZMod 2) ↥U.direction+2*r := by
    have he : Module.finrank (ZMod 2) ↥((⊤ : AffineSubspace (ZMod 2) (BooleanVec n)).direction)=n := by
      rw [AffineSubspace.direction_top (ZMod 2) (BooleanVec n) (BooleanVec n),finrank_top]
      exact cube_finrank n
    simpa only [he] using hUd
  obtain ⟨x1,hx1,x2,hx2,hfar,hquad⟩ := quadratic_far_pair U hU (by omega) Q b c hn hrn
  let v : BooleanVec n := x1+x2
  have hv : v ∈ U.direction := by
    have h := AffineSubspace.vsub_mem_direction hx1 hx2
    have hneg : -x2=x2 := neg_eq_iff_add_eq_zero.mpr (cube_add_self x2)
    simpa only [v,vsub_eq_sub,sub_eq_add_neg,hneg] using h
  have hxv : x1+v=x2 := by
    dsimp only [v]
    rw [← add_assoc,cube_add_self,zero_add]
  choose L d hder using (fun j => quadFun_directional_affine (Q j) (b j) (c j) v)
  let DL : BooleanVec n →ₗ[ZMod 2] BooleanVec r := LinearMap.pi L
  have hzero (j : Fin r) : L j x1+d j=0 := by
    rw [← hder j x1,hxv,hquad j]
    exact CharTwo.add_self_eq_zero _
  let D := U.direction ⊓ LinearMap.ker DL
  let W := AffineSubspace.mk' x1 D
  have hWdir : W.direction=D := AffineSubspace.direction_mk' x1 D
  have hWU : W ≤ U := affine_subregion U x1 hx1 D inf_le_left
  have hD : Module.finrank (ZMod 2) ↥U.direction ≤ Module.finrank (ZMod 2) ↥D+r := by
    simpa only [cube_finrank] using inf_ker_codim U.direction DL
  have hDn : Module.finrank (ZMod 2) ↥D ≤ n := by
    simpa only [cube_finrank] using D.finrank_le
  let k := n-Module.finrank (ZMod 2) ↥D
  have hdim : Module.finrank (ZMod 2) ↥W.direction=n-k := by rw [hWdir]; dsimp only [k]; omega
  have hk : 0 < n-k := by dsimp only [k]; omega
  obtain ⟨y,hy,hyw⟩ := exists_small_weight_mem_affine W hdim hk
  have hy3 : cubeWeight y ≤ 3*r := by dsimp only [k] at hyw; omega
  let z := y+v
  have hyU : y ∈ U := hWU hy
  have hzU : z ∈ U := by
    simpa only [z,vadd_eq_add,add_comm] using AffineSubspace.vadd_mem_of_mem_direction hv hyU
  have hDL : DL (y-x1)=0 := (AffineSubspace.mem_mk'.mp hy).2
  have hL (j : Fin r) : L j y=L j x1 := by
    have he := congrFun hDL j
    apply sub_eq_zero.mp
    simpa only [DL,LinearMap.pi_apply,map_sub,Pi.zero_apply] using he
  have hq (j : Fin r) : quadFun (Q j) (b j) (c j) y=quadFun (Q j) (b j) (c j) z := by
    have he : quadFun (Q j) (b j) (c j) y+quadFun (Q j) (b j) (c j) z=0 := by
      change quadFun (Q j) (b j) (c j) y+quadFun (Q j) (b j) (c j) (y+v)=0
      rw [hder j y,hL j]
      exact hzero j
    rwa [add_eq_zero_iff_eq_neg,CharTwo.neg_eq] at he
  have hw := cubeWeight_add_le y z
  have hyz : y+z=v := by dsimp only [z]; rw [← add_assoc,cube_add_self,zero_add]
  rw [hyz] at hw
  refine ⟨y,z,by change 8*r < cubeWeight v at hfar; omega,?_⟩
  intro j
  exact ⟨(hconst j y hyU z hzU).1,hq j,(hconst j y hyU z hzU).2⟩

/-- If `stabilizerRank F ≤ r`, `1 ≤ n`, and `100 * r ≤ n`, then `F` takes the same value at two
Boolean vectors of different Hamming weights. -/
theorem exact_rank_collision {n r : ℕ} (F : BooleanVec n → ℂ) (hn : 1 ≤ n)
    (hrn : 100*r ≤ n) (hF : stabilizerRank F ≤ r) :
    ∃ y z : BooleanVec n, cubeWeight y ≠ cubeWeight z ∧ F y=F z := by
  by_cases hχ : stabilizerRank F=0
  · have hzero : F=0 := (stabilizerRank_eq_zero F).mp hχ
    let i : Fin n := ⟨0,by omega⟩
    let z : BooleanVec n := Pi.single i 1
    refine ⟨0,z,?_,by simp [hzero]⟩
    have hz : cubeWeight z ≠ 0 := hammingNorm_ne_zero_iff.mpr (by
      intro h
      have he := congrFun h i
      simp [z] at he)
    simpa [cubeWeight] using hz.symm
  let S : Set ℕ := {m | ∃ (coeff : Fin m → ℂ) (φ : Fin m → BooleanVec n → ℂ),
    (∀ j, IsStabilizerFun (φ j)) ∧ F=fun x => ∑ j, coeff j*φ j x}
  have hS : S.Nonempty := by
    by_contra h
    have hs : S=∅ := by
      ext m
      constructor
      · intro hm; exact h ⟨m,hm⟩
      · intro hm; exact hm.elim
    apply hχ
    change sInf S=0
    simp [hs]
  have hm := Nat.sInf_mem hS
  change stabilizerRank F ∈ S at hm
  obtain ⟨coeff,φ,hφ,hrep⟩ := hm
  simp only [IsStabilizerFun] at hφ
  choose a Q b c A hdata using hφ
  have h100 : 100*stabilizerRank F ≤ n := (Nat.mul_le_mul_left 100 hF).trans hrn
  obtain ⟨y,z,hweights,hall⟩ := stabilizer_data_collision a Q b c A hn h100
  refine ⟨y,z,hweights,?_⟩
  rw [hrep]
  change (∑ j, coeff j*φ j y)=(∑ j, coeff j*φ j z)
  apply Finset.sum_congr rfl
  intro j _
  have hp : φ j y=φ j z := by
    rw [hdata j]
    simp only [(hall j).1,(hall j).2.1,propext (hall j).2.2]
  rw [hp]

end Qatlib.Concepts.PauliClifford.ExactRank
