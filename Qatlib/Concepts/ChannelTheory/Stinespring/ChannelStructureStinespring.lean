/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureDefs
import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Qatlib.Concepts.ChannelTheory.Stinespring.ChannelStructureKraus
import Qatlib.Concepts.ChannelTheory.Naimark.ChannelStructureMeasurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.ChannelTheory.Naimark
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

open Matrix
open Qatlib
open scoped Classical ComplexOrder BigOperators

variable {D E : ℕ}

namespace Qatlib.Concepts.ChannelTheory.Stinespring

theorem exists_unitary_extend_cols {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (W : Matrix ι (Fin d) ℂ) (emb : Fin d → ι) (hemb : Function.Injective emb)
    (hW : W.conjTranspose * W = 1) :
    ∃ U : Matrix ι ι ℂ, U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧
      ∀ (x : ι) (j : Fin d), U x (emb j) = W x j := by
  classical
  let w : Fin d → EuclideanSpace ℂ ι := fun j => WithLp.toLp 2 (fun x => W x j)
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    show inner ℂ (WithLp.toLp 2 (fun x => W x i)) (WithLp.toLp 2 (fun x => W x j))
      = if i = j then (1 : ℂ) else 0
    rw [EuclideanSpace.inner_toLp_toLp]
    show (fun x => W x j) ⬝ᵥ star (fun x => W x i) = if i = j then (1 : ℂ) else 0
    rw [dotProduct_comm]
    have h1 : (star fun x => W x i) ⬝ᵥ (fun x => W x j) = (W.conjTranspose * W) i j := rfl
    rw [h1, hW, Matrix.one_apply]
  let equiv : Fin d ≃ Set.range emb := Equiv.ofInjective emb hemb
  let v : ι → EuclideanSpace ℂ ι := fun y =>
    if hy : y ∈ Set.range emb then w (equiv.symm ⟨y, hy⟩) else 0
  have hvapp (j : Fin d) : v (emb j) = w j := by
    have he : equiv j = (⟨emb j, Set.mem_range_self j⟩ : Set.range emb) :=
      Equiv.ofInjective_apply emb hemb j
    show (if h : emb j ∈ Set.range emb then w (equiv.symm ⟨emb j, h⟩) else 0) = w j
    rw [dif_pos (Set.mem_range_self j)]
    have h2 : (⟨emb j, _⟩ : Set.range emb) = equiv j := he.symm
    rw [h2]
    exact congrArg w (equiv.symm_apply_apply j)
  have hv : Orthonormal ℂ ((Set.range emb).restrict v) := by
    have hre : (Set.range emb).restrict v = w ∘ equiv.symm := by
      funext x
      show (if x.val ∈ Set.range emb then w (equiv.symm ⟨x.val, x.property⟩) else 0)
        = w (equiv.symm x)
      exact dif_pos x.property
    rw [hre]
    exact Orthonormal.comp hw equiv.symm (Equiv.injective equiv.symm)
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (ι := ι) (card_ι := finrank_euclideanSpace (𝕜 := ℂ) (ι := ι)) hv
  refine ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b, ?_, ?_, ?_⟩
  · exact OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self
      (EuclideanSpace.basisFun ι ℂ) b
  · exact OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose
      (EuclideanSpace.basisFun ι ℂ) b
  · intro x j
    have hj : emb j ∈ Set.range emb := Set.mem_range_self j
    have hcol : ((EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b) x (emb j)
        = ⇑(b (emb j)) x := rfl
    rw [hcol, hb (emb j) hj, hvapp j]

theorem sum_fin_lt {env dOut : ℕ} (henv : env ≤ dOut) {β : Type} [AddCommMonoid β]
    (G : (k : Fin dOut) → k.val < env → β) :
    (∑ k : Fin dOut, if hk : k.val < env then G k hk else 0)
      = ∑ k : Fin env, G ⟨k.val, lt_of_lt_of_le k.isLt henv⟩ k.isLt := by
  classical
  have hsub : (∑ k ∈ Finset.univ.filter (fun k : Fin dOut => k.val < env),
        if hk : k.val < env then G k hk else 0)
      = ∑ k : Fin dOut, if hk : k.val < env then G k hk else 0 :=
    Finset.sum_subset (Finset.filter_subset _ _) (fun k _ hnk => by
      have : ¬ (k.val < env) := fun hp => hnk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hp⟩)
      exact dif_neg this)
  rw [← hsub]
  symm
  refine Finset.sum_bij (fun k _ => (⟨k.val, lt_of_lt_of_le k.isLt henv⟩ : Fin dOut)) ?_ ?_ ?_ ?_
  · intro k _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩
  · intro k₁ _ k₂ _ h
    have h2 : (k₁ : ℕ) = k₂ := congrArg (fun z : Fin dOut => (z : ℕ)) h
    exact Fin.ext h2
  · intro k hk
    obtain ⟨_, hlt⟩ := Finset.mem_filter.mp hk
    exact ⟨⟨k.val, hlt⟩, Finset.mem_univ _, rfl⟩
  · intro k _
    exact (dif_pos k.isLt).symm

noncomputable def padV {D E env dOut : ℕ} (_henv : env ≤ dOut)
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) : Matrix (Fin E × Fin dOut) (Fin D) ℂ :=
  fun x j => if hx : x.2.val < env then V (x.1, ⟨x.2.val, hx⟩) j else 0

theorem padV_apply {D E env dOut : ℕ} (henv : env ≤ dOut)
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) (x : Fin E × Fin dOut) (j : Fin D) :
    padV henv V x j = if hx : x.2.val < env then V (x.1, ⟨x.2.val, hx⟩) j else 0 := rfl

theorem envPad_apply {E env dOut : ℕ} (henv : env ≤ dOut)
    (w : Fin E × Fin env → ℂ) (x : Fin E × Fin dOut) :
    envPad henv w x = if hx : x.2.val < env then w (x.1, ⟨x.2.val, hx⟩) else 0 := rfl

theorem padV_mulVec {D E env dOut : ℕ} (henv : env ≤ dOut)
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) (ψ : Fin D → ℂ) :
    padV henv V *ᵥ ψ = envPad henv (V *ᵥ ψ) := by
  funext x
  show (∑ j, padV henv V x j * ψ j) = envPad henv (V *ᵥ ψ) x
  by_cases hx : x.2.val < env
  · have h1 : ∀ j : Fin D, padV henv V x j = V (x.1, ⟨x.2.val, hx⟩) j := fun j => by
      rw [padV_apply, dif_pos hx]
    have h2 : envPad henv (V *ᵥ ψ) x = (V *ᵥ ψ) (x.1, ⟨x.2.val, hx⟩) := by
      rw [envPad_apply, dif_pos hx]
    rw [show (∑ j, padV henv V x j * ψ j) = (∑ j, V (x.1, ⟨x.2.val, hx⟩) j * ψ j) by
      simp only [h1], h2]
    rfl
  · have h1 : ∀ j : Fin D, padV henv V x j = 0 := fun j => by
      rw [padV_apply, dif_neg hx]
    have h2 : envPad henv (V *ᵥ ψ) x = 0 := by
      rw [envPad_apply, dif_neg hx]
    rw [show (∑ j, padV henv V x j * ψ j) = 0 by simp [h1], h2]

theorem padV_conjTranspose_mul {D E env dOut : ℕ} (henv : env ≤ dOut)
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) :
    (padV henv V).conjTranspose * padV henv V = V.conjTranspose * V := by
  ext i j
  show (∑ x, star (padV henv V x i) * padV henv V x j) = (∑ x, star (V x i) * V x j)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hterm : ∀ k : Fin dOut,
      star (padV henv V (a, k) i) * padV henv V (a, k) j
        = if hk : k.val < env then star (V (a, ⟨k.val, hk⟩) i) * V (a, ⟨k.val, hk⟩) j else 0 := by
    intro k
    rw [padV_apply, padV_apply]
    by_cases hk : k.val < env
    · rw [dif_pos hk, dif_pos hk, dif_pos hk]
    · rw [dif_neg hk, dif_neg hk, dif_neg hk, star_zero, zero_mul]
  simp only [hterm]
  exact sum_fin_lt henv (fun k hk => star (V (a, ⟨k.val, hk⟩) i) * V (a, ⟨k.val, hk⟩) j)

theorem kraus_mul_apply {D E : ℕ} (K : Matrix (Fin E) (Fin D) ℂ) (A : Operator D)
    (a b : Fin E) :
    (K * A * K.conjTranspose) a b
      = ∑ i : Fin D, ∑ j : Fin D, K a i * A i j * star (K b j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h1 : ∀ c : Fin D, (∑ i : Fin D, K a i * A i c) * star (K b c)
      = ∑ i : Fin D, K a i * A i c * star (K b c) := fun c => Finset.sum_mul _ _ _
  simp only [h1]
  rw [Finset.sum_comm]

theorem stinespring_of_kraus {D E n : ℕ} {T : Operator D →ₗ[ℂ] Operator E}
    (K : Fin n → Matrix (Fin E) (Fin D) ℂ) (hK : KrausForm T K) (hC : KrausComplete K) :
    StinespringDilation T n (fun x j => K x.2 x.1 j) := by
  constructor
  · ext i j
    show (∑ x : Fin E × Fin n, star (K x.2 x.1 i) * K x.2 x.1 j) = (1 : Operator D) i j
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h1 : ∀ k : Fin n,
        (∑ a : Fin E, star (K k a i) * K k a j) = ((K k).conjTranspose * K k) i j := by
      intro k
      show (∑ a : Fin E, star (K k a i) * K k a j)
        = (∑ c : Fin E, star (K k c i) * K k c j)
      rfl
    simp only [h1]
    rw [← Matrix.sum_apply, hC, Matrix.one_apply]
  · intro R X
    ext u v
    set A : Operator D := fun i j => X (u.1, i) (v.1, j) with hA
    show (∑ e : Fin n, ∑ i : Fin D, ∑ j : Fin D,
        K e u.2 i * A i j * star (K e v.2 j)) = T A u.2 v.2
    rw [hK]
    have hterm : ∀ k : Fin n,
        (K k * A * (K k).conjTranspose) u.2 v.2
          = ∑ i : Fin D, ∑ j : Fin D, K k u.2 i * A i j * star (K k v.2 j) :=
      fun k => kraus_mul_apply (K k) A u.2 v.2
    rw [Matrix.sum_apply]
    simp only [hterm]

theorem cleanEnv_zero_env {D E env : ℕ}
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) (hV : V.conjTranspose * V = 1)
    (henv : env = 0) : CleanEnvUnitaryCompletion V := by
  classical
  subst henv
  have hD : D = 0 := by
    by_contra hD
    have h0 : 0 < D := Nat.pos_of_ne_zero hD
    have hz : V.conjTranspose * V = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
      exact Finset.sum_eq_zero (fun x _ => Fin.elim0 x.2)
    rw [hz] at hV
    have h1 : (1 : Operator D) ⟨0, h0⟩ ⟨0, h0⟩ = (1 : ℂ) := by simp
    have h2 : (0 : Operator D) ⟨0, h0⟩ ⟨0, h0⟩ = (0 : ℂ) := by simp
    rw [← hV] at h1
    exact absurd h1 (by norm_num)
  subst hD
  refine ⟨1, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · exact Nat.le_refl 0
  · ext i j; exact Fin.elim0 i.1
  · ext i j; exact Fin.elim0 i.2
  · intro ψ; funext x; exact Fin.elim0 x.2

theorem cleanEnv_zero_out {D E env : ℕ}
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) (hV : V.conjTranspose * V = 1)
    (hE : E = 0) : CleanEnvUnitaryCompletion V := by
  classical
  subst hE
  have hD : D = 0 := by
    by_contra hD
    have h0 : 0 < D := Nat.pos_of_ne_zero hD
    have hz : V.conjTranspose * V = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
      exact Finset.sum_eq_zero (fun x _ => Fin.elim0 x.1)
    rw [hz] at hV
    have h1 : (1 : Operator D) ⟨0, h0⟩ ⟨0, h0⟩ = (1 : ℂ) := by simp
    have h2 : (0 : Operator D) ⟨0, h0⟩ ⟨0, h0⟩ = (0 : ℂ) := by simp
    rw [← hV] at h1
    exact absurd h1 (by norm_num)
  subst hD
  refine ⟨1, max env 1, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · ring
  · exact le_max_left env 1
  · ext i j; exact Fin.elim0 i.1
  · ext i j; exact Fin.elim0 i.1
  · intro ψ; funext x; exact Fin.elim0 x.1

theorem cleanEnv_pos_dim {D E env : ℕ}
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) (hV : V.conjTranspose * V = 1)
    (hD : 0 < D) : CleanEnvUnitaryCompletion V := by
  classical
  have hE : 0 < E := by
    rcases Nat.eq_zero_or_pos E with hE | hE
    · exfalso
      subst hE
      have hz : V.conjTranspose * V = 0 := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply]
        exact Finset.sum_eq_zero (fun x _ => Fin.elim0 x.1)
      rw [hz] at hV
      have h1 : (1 : Operator D) ⟨0, hD⟩ ⟨0, hD⟩ = (1 : ℂ) := by simp [Matrix.one_apply]
      have h2 : (0 : Operator D) ⟨0, hD⟩ ⟨0, hD⟩ = (0 : ℂ) := by simp
      rw [← hV] at h1
      exact absurd h1 (by norm_num)
    · exact hE
  have hdim : D * (E * max 1 env) = E * (D * max 1 env) := by ring
  have hdOut : env ≤ D * max 1 env := by
    have h1 : env ≤ max 1 env := le_max_right _ _
    have h2 : max 1 env ≤ D * max 1 env := by
      have : 1 ≤ D := Nat.succ_le_of_lt hD
      calc max 1 env = 1 * max 1 env := (one_mul _).symm
        _ ≤ D * max 1 env := Nat.mul_le_mul_right _ this
    exact le_trans h1 h2
  have hdIn : 0 < E * max 1 env :=
    Nat.mul_pos hE (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hW : (padV hdOut V).conjTranspose * padV hdOut V = 1 := by
    rw [padV_conjTranspose_mul hdOut V, hV]
  let e : (Fin D × Fin (E * max 1 env)) ≃ (Fin E × Fin (D * max 1 env)) :=
    (finProdFinEquiv (m := D) (n := E * max 1 env)).trans
      ((finCongr hdim).trans (finProdFinEquiv (m := E) (n := D * max 1 env)).symm)
  let emb : Fin D → Fin E × Fin (D * max 1 env) := fun j => e (j, ⟨0, hdIn⟩)
  have hemb : Function.Injective emb := by
    intro j₁ j₂ h
    have h2 : (j₁, (⟨0, hdIn⟩ : Fin (E * max 1 env)))
        = (j₂, (⟨0, hdIn⟩ : Fin (E * max 1 env))) := e.injective h
    exact congrArg Prod.fst h2
  obtain ⟨U₀, hU0a, hU0b, hU0c⟩ := exists_unitary_extend_cols (padV hdOut V) emb hemb hW
  refine ⟨E * max 1 env, D * max 1 env, ⟨0, hdIn⟩, (fun x y => U₀ x (e y)), hdim, hdOut,
    ?_, ?_, ?_⟩
  · ext y y'
    show (∑ x : Fin E × Fin (D * max 1 env), star (U₀ x (e y)) * U₀ x (e y'))
      = (1 : Matrix (Fin D × Fin (E * max 1 env)) (Fin D × Fin (E * max 1 env)) ℂ) y y'
    have h1 : (∑ x, star (U₀ x (e y)) * U₀ x (e y'))
        = (U₀.conjTranspose * U₀) (e y) (e y') := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h1, hU0a, Matrix.one_apply, Matrix.one_apply]
    by_cases h : y = y'
    · simp [h]
    · have hne : e y ≠ e y' := fun he => h (e.injective he)
      simp [h, hne]
  · ext x x'
    show (∑ y : Fin D × Fin (E * max 1 env), U₀ x (e y) * star (U₀ x' (e y)))
      = (1 : Matrix (Fin E × Fin (D * max 1 env)) (Fin E × Fin (D * max 1 env)) ℂ) x x'
    have h1 : (∑ y, U₀ x (e y) * star (U₀ x' (e y)))
        = (U₀ * U₀.conjTranspose) x x' := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
      exact Equiv.sum_comp e (fun z => U₀ x z * star (U₀ x' z))
    rw [h1, hU0b, Matrix.one_apply]
  · intro ψ
    funext x
    show (∑ y : Fin D × Fin (E * max 1 env),
        (U₀ x (e y)) * (if y.2 = ⟨0, hdIn⟩ then ψ y.1 else 0))
      = envPad hdOut (V *ᵥ ψ) x
    rw [Fintype.sum_prod_type]
    have hsum : ∀ i : Fin D,
        (∑ k : Fin (E * max 1 env), U₀ x (e (i, k)) * (if k = ⟨0, hdIn⟩ then ψ i else 0))
          = U₀ x (e (i, ⟨0, hdIn⟩)) * ψ i := by
      intro i
      rw [Finset.sum_eq_single (⟨0, hdIn⟩ : Fin (E * max 1 env))]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    simp only [hsum]
    have hcol : ∀ i : Fin D, U₀ x (e (i, ⟨0, hdIn⟩)) = padV hdOut V x i :=
      fun i => hU0c x i
    simp only [hcol]
    rw [← padV_mulVec hdOut V ψ]
    rfl

theorem cleanEnv_of_isometry {D E env : ℕ}
    (V : Matrix (Fin E × Fin env) (Fin D) ℂ) (hV : V.conjTranspose * V = 1)
    (hok : 0 < D ∨ env = 0 ∨ E = 0) : CleanEnvUnitaryCompletion V := by
  rcases hok with hD | h | hE
  · exact cleanEnv_pos_dim V hV hD
  · exact cleanEnv_zero_env V hV h
  · exact cleanEnv_zero_out V hV hE

theorem matrixUnit_zero_zero_eq_diagonal :
    matrixUnit (D := 2) 0 0 = Matrix.diagonal ![1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixUnit, Matrix.single, Matrix.diagonal]

set_option maxHeartbeats 800000

theorem g2 :
    (∀ (D E : ℕ) (T : QuantumChannel D E),
      ∃ (env : ℕ) (V : Matrix (Fin E × Fin env) (Fin D) ℂ),
        env ≤ D * E ∧
        StinespringDilation T.map env V ∧
        CleanEnvUnitaryCompletion V) ∧
    (∀ D : ℕ, ∃ V : Matrix (Fin D × Fin 1) (Fin D) ℂ,
        StinespringDilation (QuantumChannel.id D).map 1 V ∧
        CleanEnvUnitaryCompletion V) ∧
    (∃ (T : QuantumChannel 2 2) (V : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ),
        (∀ ρ : Operator 2, T.map ρ = Matrix.trace ρ • (Matrix.diagonal ![1, 0])) ∧
        StinespringDilation T.map 2 V ∧
        CleanEnvUnitaryCompletion V ∧
        ¬ ∃ U : Matrix (Fin 2) (Fin 2) ℂ, IsUnitaryMatrix U ∧
          ∀ ρ : Operator 2, T.map ρ = U * ρ * U.conjTranspose) := by
  refine ⟨?_, ?_, ?_⟩
  · intro D E T
    obtain ⟨_, n, K, hK, hC, hn⟩ := clause2_conj11 T
    have hst : StinespringDilation T.map n (fun x j => K x.2 x.1 j) :=
      stinespring_of_kraus K hK hC
    refine ⟨n, (fun x j => K x.2 x.1 j), hn, hst, ?_⟩
    refine cleanEnv_of_isometry _ hst.1 ?_
    rcases Nat.eq_zero_or_pos D with hD | hD
    · right; left
      have : n ≤ 0 := by simpa [hD] using hn
      exact Nat.le_zero.mp this
    · exact Or.inl hD
  · intro D
    let K : Fin 1 → Matrix (Fin D) (Fin D) ℂ := fun _ => 1
    have hKf : KrausForm (LinearMap.id : Operator D →ₗ[ℂ] Operator D) K := by
      intro A
      show LinearMap.id A = ∑ k : Fin 1, K k * A * (K k).conjTranspose
      rw [Fin.sum_univ_one]
      simp [K]
    have hKc : KrausComplete K := by
      show ∑ k : Fin 1, (K k).conjTranspose * K k = 1
      rw [Fin.sum_univ_one]
      simp [K]
    have hst : StinespringDilation (QuantumChannel.id D).map 1
        (fun x j => K x.2 x.1 j) :=
      stinespring_of_kraus K hKf hKc
    refine ⟨(fun x j => K x.2 x.1 j), hst, ?_⟩
    refine cleanEnv_of_isometry _ hst.1 ?_
    rcases Nat.eq_zero_or_pos D with hD | hD
    · right; right; exact hD
    · exact Or.inl hD
  · set T : QuantumChannel 2 2 := krausChannel kDrop krausDrop_complete
    have hmap : ∀ ρ : Operator 2,
        T.map ρ = Matrix.trace ρ • Matrix.diagonal ![1, 0] := by
      intro ρ
      show krausMap kDrop ρ = Matrix.trace ρ • Matrix.diagonal ![1, 0]
      have h : krausMap kDrop ρ = ∑ k : Fin 2, kDrop k * ρ * (kDrop k).conjTranspose := by
        simp only [krausMap, LinearMap.sum_apply, conjBranch_apply]
      rw [h, krausDrop_apply, matrixUnit_zero_zero_eq_diagonal]
    have hst : StinespringDilation T.map 2 (fun x j => kDrop x.2 x.1 j) :=
      stinespring_of_kraus kDrop (krausForm_krausMap kDrop) krausDrop_complete
    refine ⟨T, (fun x j => kDrop x.2 x.1 j), hmap, hst, ?_, ?_⟩
    · refine cleanEnv_of_isometry _ hst.1 ?_
      exact Or.inl (by norm_num)
    · rintro ⟨U, hU, hT⟩
      have h1 : T.map (1 : Operator 2) = 1 := by
        rw [hT 1, Matrix.mul_one, hU.2]
      have h2 : T.map (1 : Operator 2) = ((2 : ℂ) • Matrix.diagonal ![1, 0]) := by
        rw [hmap 1]
        congr 1
        norm_num [Matrix.trace, Fin.sum_univ_two, Matrix.one_apply]
      have h3 : (((2 : ℂ) • Matrix.diagonal ![1, 0] : Operator 2)) = 1 := h2.symm.trans h1
      have h4 := congrFun (congrFun h3 (0 : Fin 2)) (0 : Fin 2)
      simp [Matrix.smul_apply, Matrix.diagonal] at h4
end Qatlib.Concepts.ChannelTheory.Stinespring
