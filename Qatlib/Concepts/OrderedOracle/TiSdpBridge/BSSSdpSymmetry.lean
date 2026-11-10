/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.BSSSdp
import Mathlib.GroupTheory.Perm.Finite
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped Classical BigOperators ComplexOrder
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [Fintype X] [Fintype Y] in

theorem bssDelta_transport {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y)
    (h : IsBssSymmetry bit f π ρ σ) (y : Y) (x x' : X) :
    bssDelta f (σ y) (π x) (π x')=bssDelta f y x x' := by
  have hfx : f (π x)=σ (f x) := (h.2 x).symm
  simp only [bssDelta,Matrix.of_apply,hfx,σ.injective.eq_iff,π.injective.eq_iff]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in

theorem bss_hadamard_sum_transport {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y)
    (h : IsBssSymmetry bit f π ρ σ) (M : Fin m → Matrix X X ℂ) (x x' : X) :
    (∑ i : Fin m,bssE bit i x x'*M (ρ.symm i) (π x) (π x'))=
      ∑ i : Fin m,bssE bit i (π x) (π x')*M i (π x) (π x') := by
  rw [← Equiv.sum_comp ρ (fun i => bssE bit i x x'*M (ρ.symm i) (π x) (π x'))]
  simp only [ρ.symm_apply_apply,h.1]

theorem bssFamilyFeasible_conjugate {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (k : ℕ) (ε : ℝ) (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y)
    (hs : IsBssSymmetry bit f π ρ σ)
    (M : Fin m → ℕ → Matrix X X ℂ) (N : ℕ → Matrix X X ℂ) (Γ : Y → Matrix X X ℂ)
    (h : bssFamilyFeasible bit f k ε M N Γ) :
    bssFamilyFeasible bit f k ε
      (fun i t => (M (ρ.symm i) t).submatrix π π)
      (fun t => (N t).submatrix π π) (fun y => (Γ (σ y)).submatrix π π) := by
  obtain ⟨hM,hN,hΓ,hinit,hstep,hfinal,hsuccess⟩ := h
  refine ⟨(fun i t => (hM _ _).submatrix π),(fun t => (hN _).submatrix π),
    (fun y => (hΓ _).submatrix π),?_,?_,?_,?_⟩
  · intro x x'
    simp only [Matrix.submatrix_apply]
    rw [Equiv.sum_comp ρ.symm (fun i => M i 0 (π x) (π x'))]
    exact hinit (π x) (π x')
  · intro t ht x x'
    simp only [Matrix.submatrix_apply,Matrix.hadamard_apply]
    rw [bss_hadamard_sum_transport bit f π ρ σ hs (fun i => M i t) x x',
      Equiv.sum_comp ρ.symm (fun i => M i (t+1) (π x) (π x'))]
    exact hstep t ht (π x) (π x')
  · intro hk x x'
    simp only [Matrix.submatrix_apply,Matrix.hadamard_apply]
    rw [bss_hadamard_sum_transport bit f π ρ σ hs (fun i => M i (k-1)) x x',
      Equiv.sum_comp σ (fun y => Γ y (π x) (π x'))]
    exact hfinal hk (π x) (π x')
  · intro y
    have he : Matrix.hadamard (bssDelta f y) ((Γ (σ y)).submatrix π π)-
        (1-ε : ℂ) • bssDelta f y=
        (Matrix.hadamard (bssDelta f (σ y)) (Γ (σ y))-(1-ε : ℂ) • bssDelta f (σ y)).submatrix π π := by
      ext x x'
      simp only [Matrix.submatrix_apply,Matrix.sub_apply,Matrix.hadamard_apply,Matrix.smul_apply,smul_eq_mul,
        bssDelta_transport bit f π ρ σ hs]
    rw [he]
    exact (hsuccess (σ y)).submatrix π

def bssTransportGroup {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y) :
    Subgroup (Equiv.Perm X × (Equiv.Perm (Fin m) × Equiv.Perm Y)) where
  carrier := {g | (∀ i x x',bssE bit i x x'=bssE bit (g.2.1 i) (g.1 x) (g.1 x')) ∧
    ∀ x,g.2.2 (f x)=f (g.1 x)}
  one_mem' := by constructor <;> intros <;> rfl
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro i x x'
      exact (hh.1 i x x').trans (hg.1 (h.2.1 i) (h.1 x) (h.1 x'))
    · intro x
      change g.2.2 (h.2.2 (f x))=f (g.1 (h.1 x))
      rw [hh.2 x,hg.2 (h.1 x)]
  inv_mem' := by
    intro g hg
    constructor
    · intro i x x'
      have h := hg.1 (g.2.1.symm i) (g.1.symm x) (g.1.symm x')
      simpa only [Equiv.apply_symm_apply] using! h.symm
    · intro x
      apply g.2.2.injective
      change g.2.2 (g.2.2.symm (f x))=g.2.2 (f (g.1.symm x))
      rw [Equiv.apply_symm_apply,hg.2 (g.1.symm x),Equiv.apply_symm_apply]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in

theorem bssTransportGroup_mem {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y)
    (h : IsBssSymmetry bit f π ρ σ) : (π,(ρ.symm,σ))∈bssTransportGroup bit f := by
  refine ⟨?_,h.2⟩
  intro i x x'
  simpa only [Equiv.apply_symm_apply] using h.1 (ρ.symm i) x x'

def bssAverageScalar {I : Type} [Fintype I] (a : I → ℂ) : ℂ :=
  (Fintype.card I : ℂ)⁻¹*∑ i : I,a i

def bssAverage {I : Type} [Fintype I] (A : I → Matrix X X ℂ) : Matrix X X ℂ :=
  (Fintype.card I : ℝ)⁻¹ • ∑ i : I,A i

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] in

theorem bssAverage_apply {I : Type} [Fintype I] (A : I → Matrix X X ℂ) (x x' : X) :
    bssAverage A x x'=bssAverageScalar (fun i => A i x x') := by
  simp only [bssAverage,bssAverageScalar,Matrix.smul_apply,Matrix.sum_apply,
    RCLike.real_smul_eq_coe_mul]
  push_cast
  rfl

theorem bssAverageScalar_add {I : Type} [Fintype I] (a b : I → ℂ) :
    bssAverageScalar (fun i => a i+b i)=bssAverageScalar a+bssAverageScalar b := by
  simp only [bssAverageScalar,Finset.sum_add_distrib,mul_add]

theorem bssAverageScalar_sub {I : Type} [Fintype I] (a b : I → ℂ) :
    bssAverageScalar (fun i => a i-b i)=bssAverageScalar a-bssAverageScalar b := by
  simp only [bssAverageScalar,Finset.sum_sub_distrib,mul_sub]

theorem bssAverageScalar_mul_left {I : Type} [Fintype I] (c : ℂ) (a : I → ℂ) :
    c*bssAverageScalar a=bssAverageScalar (fun i => c*a i) := by
  unfold bssAverageScalar
  rw [← Finset.mul_sum]
  ring

theorem bssAverageScalar_sum {I Z : Type} [Fintype I] [Fintype Z] (a : Z → I → ℂ) :
    (∑ z : Z,bssAverageScalar (a z))=bssAverageScalar (fun i => ∑ z : Z,a z i) := by
  unfold bssAverageScalar
  rw [← Finset.mul_sum,Finset.sum_comm]

theorem bssAverageScalar_const {I : Type} [Fintype I] [Nonempty I] (c : ℂ) :
    bssAverageScalar (fun _ : I => c)=c := by
  have hI : (Fintype.card I : ℂ)≠0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0<Fintype.card I))
  simp only [bssAverageScalar,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ hI,one_mul]

omit [Fintype X] [DecidableEq X] in

theorem bssAverage_posSemidef {I : Type} [Fintype I] (A : I → Matrix X X ℂ)
    (hA : ∀ i,(A i).PosSemidef) : (bssAverage A).PosSemidef := by
  have hsum (s : Finset I) : (∑ i∈s,A i).PosSemidef := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (Matrix.PosSemidef.zero : (0 : Matrix X X ℂ).PosSemidef)
    | @insert i s hi ih => rw [Finset.sum_insert hi]; exact (hA i).add ih
  exact (hsum Finset.univ).smul (inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card I)))

theorem bssFamilyFeasible_average {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] {m : ℕ} {I : Type} [Fintype I] [Nonempty I]
    (bit : X → Fin m → Bool) (f : X → Y) (k : ℕ) (ε : ℝ)
    (M : I → Fin m → ℕ → Matrix X X ℂ) (N : I → ℕ → Matrix X X ℂ)
    (Γ : I → Y → Matrix X X ℂ) (h : ∀ g,bssFamilyFeasible bit f k ε (M g) (N g) (Γ g)) :
    bssFamilyFeasible bit f k ε (fun i t => bssAverage (fun g => M g i t))
      (fun t => bssAverage (fun g => N g t)) (fun y => bssAverage (fun g => Γ g y)) := by
  refine ⟨(fun i t => bssAverage_posSemidef _ (fun g => (h g).1 i t)),
    (fun t => bssAverage_posSemidef _ (fun g => (h g).2.1 t)),
    (fun y => bssAverage_posSemidef _ (fun g => (h g).2.2.1 y)),?_,?_,?_,?_⟩
  · intro x x'
    simp only [bssAverage_apply]
    rw [bssAverageScalar_sum,← bssAverageScalar_add]
    have he : (fun g => (∑ i,M g i 0 x x')+N g 0 x x')=(fun _ : I => (1 : ℂ)) := by
      funext g
      exact (h g).2.2.2.1 x x'
    rw [he,bssAverageScalar_const]
  · intro t ht x x'
    simp only [Matrix.hadamard_apply,bssAverage_apply]
    simp_rw [bssAverageScalar_mul_left]
    rw [bssAverageScalar_sum,bssAverageScalar_sum,← bssAverageScalar_add,← bssAverageScalar_add]
    congr 1
    funext g
    exact (h g).2.2.2.2.1 t ht x x'
  · intro hk x x'
    simp only [Matrix.hadamard_apply,bssAverage_apply]
    simp_rw [bssAverageScalar_mul_left]
    rw [bssAverageScalar_sum,bssAverageScalar_sum,← bssAverageScalar_add]
    congr 1
    funext g
    exact (h g).2.2.2.2.2.1 hk x x'
  · intro y
    have he : Matrix.hadamard (bssDelta f y) (bssAverage (fun g => Γ g y))-
        (1-ε : ℂ) • bssDelta f y=
        bssAverage (fun g => Matrix.hadamard (bssDelta f y) (Γ g y)-(1-ε : ℂ) • bssDelta f y) := by
      ext x x'
      simp only [Matrix.sub_apply,Matrix.hadamard_apply,Matrix.smul_apply,smul_eq_mul,bssAverage_apply]
      rw [bssAverageScalar_sub,← bssAverageScalar_mul_left,bssAverageScalar_const]
    rw [he]
    exact bssAverage_posSemidef _ (fun g => (h g).2.2.2.2.2.2 y)

theorem bssFeasible_exists_symmetry_invariant {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (k : ℕ) (ε : ℝ) (h : bssFeasible bit f k ε) :
    ∃ M : Fin m → ℕ → Matrix X X ℂ,∃ N : ℕ → Matrix X X ℂ,∃ Γ : Y → Matrix X X ℂ,
      bssFamilyFeasible bit f k ε M N Γ ∧
      ∀ (π : Equiv.Perm X) (ρ : Equiv.Perm (Fin m)) (σ : Equiv.Perm Y),
        IsBssSymmetry bit f π ρ σ →
        (∀ i t x x',M (ρ.symm i) t (π x) (π x')=M i t x x') ∧
        (∀ t x x',N t (π x) (π x')=N t x x') ∧
        (∀ y x x',Γ (σ y) (π x) (π x')=Γ y x x') := by
  obtain ⟨M,N,Γ,hf⟩ := h
  let S := ↥(bssTransportGroup bit f)
  letI : Fintype S := Fintype.ofFinite S
  have hsym (g : S) : IsBssSymmetry bit f g.val.1 g.val.2.1.symm g.val.2.2 := by
    refine ⟨?_,g.property.2⟩
    intro i x x'
    have hh := g.property.1 (g.val.2.1.symm i) x x'
    simpa only [Equiv.apply_symm_apply] using hh
  let Mg := fun (g : S) (i : Fin m) (t : ℕ) => (M (g.val.2.1 i) t).submatrix g.val.1 g.val.1
  let Ng := fun (g : S) (t : ℕ) => (N t).submatrix g.val.1 g.val.1
  let Γg := fun (g : S) (y : Y) => (Γ (g.val.2.2 y)).submatrix g.val.1 g.val.1
  have hfg (g : S) : bssFamilyFeasible bit f k ε (Mg g) (Ng g) (Γg g) := by
    simpa only [Mg,Ng,Γg,Equiv.symm_symm] using
      bssFamilyFeasible_conjugate bit f k ε g.val.1 g.val.2.1.symm g.val.2.2 (hsym g) M N Γ hf
  let AM := fun i t => bssAverage (fun g : S => Mg g i t)
  let AN := fun t => bssAverage (fun g : S => Ng g t)
  let AΓ := fun y => bssAverage (fun g : S => Γg g y)
  refine ⟨AM,AN,AΓ,bssFamilyFeasible_average bit f k ε Mg Ng Γg hfg,?_⟩
  intro π ρ σ hs
  let z : S := ⟨(π,(ρ.symm,σ)),bssTransportGroup_mem bit f π ρ σ hs⟩
  constructor
  · intro i t x x'
    simp only [AM,bssAverage_apply]
    unfold bssAverageScalar
    congr 1
    change (∑ g : S,Mg (g*z) i t x x')=∑ g : S,Mg g i t x x'
    exact Equiv.sum_comp (Equiv.mulRight z) (fun g : S => Mg g i t x x')
  · constructor
    · intro t x x'
      simp only [AN,bssAverage_apply]
      unfold bssAverageScalar
      congr 1
      change (∑ g : S,Ng (g*z) t x x')=∑ g : S,Ng g t x x'
      exact Equiv.sum_comp (Equiv.mulRight z) (fun g : S => Ng g t x x')
    · intro y x x'
      simp only [AΓ,bssAverage_apply]
      unfold bssAverageScalar
      congr 1
      change (∑ g : S,Γg (g*z) y x x')=∑ g : S,Γg g y x x'
      exact Equiv.sum_comp (Equiv.mulRight z) (fun g : S => Γg g y x x')

theorem bssFeasible_exists_invariant {m : ℕ} (bit : X → Fin m → Bool) (f : X → Y)
    (k : ℕ) (ε : ℝ) (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (π : G →* Equiv.Perm X) (ρ : G →* Equiv.Perm (Fin m)) (σ : G →* Equiv.Perm Y)
    (hs : ∀ g,IsBssSymmetry bit f (π g) (ρ g) (σ g)) (h : bssFeasible bit f k ε) :
    ∃ M : Fin m → ℕ → Matrix X X ℂ,∃ N : ℕ → Matrix X X ℂ,∃ Γ : Y → Matrix X X ℂ,
      bssFamilyFeasible bit f k ε M N Γ ∧
      (∀ g i t x x',M ((ρ g).symm i) t (π g x) (π g x')=M i t x x') ∧
      (∀ g t x x',N t (π g x) (π g x')=N t x x') ∧
      (∀ g y x x',Γ (σ g y) (π g x) (π g x')=Γ y x x') := by
  obtain ⟨M,N,Γ,hf,hinv⟩ := bssFeasible_exists_symmetry_invariant bit f k ε h
  refine ⟨M,N,Γ,hf,(fun g => (hinv (π g) (ρ g) (σ g) (hs g)).1),
    (fun g => (hinv (π g) (ρ g) (σ g) (hs g)).2.1),
    (fun g => (hinv (π g) (ρ g) (σ g) (hs g)).2.2)⟩
end Qatlib.Concepts.OrderedOracle.TiSdpBridge
