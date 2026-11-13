/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.WeightedAdvComp

/-!
# Optimized weighted adversary bounds

`advPlus` and `advNonneg` optimize weighted norm-ratio expressions over Hermitian complex
witnesses and entrywise nonnegative symmetric real witnesses, respectively. `minimaxAlpha`
defines the corresponding inverse overlap optimization over coordinate distributions, and the
module proves the weak inequality from the nonnegative adversary value to this minimax quantity
in the framework of [HoyerLeeSpalek2007].

Further results bound the nonnegative value using intersecting certificates, show monotonicity
under injective input-domain embeddings, and derive a lower bound for the optimized value of a
block composition. Approximate witnesses allow the composition argument to work with suprema
without assuming that optimizers are attained.

## Main statements

* `advNonneg_le_minimaxAlpha`: establish the nonnegative weak duality inequality.
* `advNonneg_le_of_certificates`: bound the unit-cost value by a certificate size bound.
* `advPlus_mono_of_injective`: enlarge the input domain along a compatible injection.
* `advPlus_composition_ge`: transfer inner optimized bounds to a composed function.

## References

* [Hoyer, Lee, and Spalek, 2007][HoyerLeeSpalek2007]
-/

set_option autoImplicit false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.WeightedAdvComp
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.AdversaryBounds.OptimizedAdv

open Matrix

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The real adversary matrix obtained by retaining entries whose inputs differ at coordinate
`c` and replacing all other entries by zero. -/
def advFilterR {X : Type} {κ : Type} [DecidableEq κ]
    (input : X → κ → Bool) (Γ : Matrix X X ℝ) (c : κ) : Matrix X X ℝ :=
  fun x y => if input x c ≠ input y c then Γ x y else 0

/-- The real infimum over coordinates of `α i * ‖Γ‖ / ‖weightedAdvFilter input Γ i‖`, using
ordinary real division. -/
noncomputable def advWitnessValue {X : Type} [Fintype X] [DecidableEq X]
    {κ : Type} [DecidableEq κ] (input : X → κ → Bool) (α : κ → ℝ)
    (Γ : Matrix X X ℂ) : ℝ :=
  ⨅ i : κ, α i * ‖Γ‖ / ‖weightedAdvFilter input Γ i‖

/-- The extended nonnegative supremum of `advWitnessValue` over Hermitian complex matrices that
vanish on equal-output input pairs. -/
noncomputable def advPlus {X : Type} [Fintype X] [DecidableEq X]
    {κ : Type} [DecidableEq κ] (input : X → κ → Bool) (g : X → Bool)
    (α : κ → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℂ // Γ.IsHermitian ∧ ∀ x y, g x = g y → Γ x y = 0},
    ENNReal.ofReal (advWitnessValue input α Γ)

/-- The real infimum over coordinates of `α i * ‖Γ‖ / ‖advFilterR input Γ i‖`, using ordinary
real division. -/
noncomputable def advWitnessValueR {X : Type} [Fintype X] [DecidableEq X]
    {κ : Type} [DecidableEq κ] (input : X → κ → Bool) (α : κ → ℝ)
    (Γ : Matrix X X ℝ) : ℝ :=
  ⨅ i : κ, α i * ‖Γ‖ / ‖advFilterR input Γ i‖

/-- The extended nonnegative supremum of `advWitnessValueR` over symmetric entrywise nonnegative
real matrices that vanish on equal-output pairs. -/
noncomputable def advNonneg {X : Type} [Fintype X] [DecidableEq X]
    {κ : Type} [DecidableEq κ] (input : X → κ → Bool) (g : X → Bool)
    (α : κ → ℝ) : ℝ≥0∞ :=
  ⨆ Γ : {Γ : Matrix X X ℝ //
    Γ.IsSymm ∧ (∀ x y, 0 ≤ Γ x y) ∧ ∀ x y, g x = g y → Γ x y = 0},
    ENNReal.ofReal (advWitnessValueR input α Γ)

/-- The weighted overlap sum `sqrt (p x i * p y i) / α i` over coordinates on which inputs `x`
and `y` differ. -/
noncomputable def advMinimaxTerm {X : Type} {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (α : κ → ℝ) (p : X → κ → ℝ) (x y : X) : ℝ :=
  ∑ i, if input x i ≠ input y i then Real.sqrt (p x i * p y i) / α i else 0

/-- The inverse of the supremum over input-indexed coordinate distributions of the extended
nonnegative conversion of the least overlap term among unequal-output pairs. -/
noncomputable def minimaxAlpha {X : Type} {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) : ℝ≥0∞ :=
  (⨆ p : {p : X → κ → ℝ // (∀ x i, 0 ≤ p x i) ∧ (∀ x, ∑ i, p x i = 1)},
      ENNReal.ofReal
        (⨅ xy : {xy : X × X // g xy.1 ≠ g xy.2},
          advMinimaxTerm input α p xy.val.1 xy.val.2))⁻¹

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

section DomainEmbedding
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The coordinate embedding matrix whose `(y, x)` entry is one exactly when `φ x = y`. -/
private def advDomainEmbedding (φ : X → Y) : Matrix Y X ℂ := fun y x => if φ x = y then 1 else 0
omit [Fintype X] in

/-- For injective `φ`, the conjugate-transpose Gram matrix of `advDomainEmbedding φ` is the
identity. -/
private theorem advDomainEmbedding_gram (φ : X → Y) (hφ : Function.Injective φ) : (advDomainEmbedding φ)ᴴ * advDomainEmbedding φ = 1 := by
  classical
  ext x x'
  simp [advDomainEmbedding, Matrix.mul_apply, Matrix.conjTranspose_apply, hφ.eq_iff,
      Matrix.one_apply]

/-- The operator norm of the coordinate embedding associated with an injection is at most one. -/
private theorem advDomainEmbedding_norm_le (φ : X → Y) (hφ : Function.Injective φ) : ‖advDomainEmbedding φ‖ ≤ 1 := by
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self (advDomainEmbedding φ)
  rw [advDomainEmbedding_gram φ hφ] at hs
  have hn := l2_norm_one_le (I := X)
  nlinarith [norm_nonneg (advDomainEmbedding φ)]

/-- Padding a matrix by an injective coordinate embedding and its conjugate transpose preserves
its operator norm. -/
private theorem advDomainEmbedding_pad_norm (φ : X → Y) (hφ : Function.Injective φ) (A : Matrix X X ℂ) :
    ‖advDomainEmbedding φ * A * (advDomainEmbedding φ)ᴴ‖ = ‖A‖ := by
  have hn := advDomainEmbedding_norm_le φ hφ
  have he : (advDomainEmbedding φ)ᴴ * (advDomainEmbedding φ*A*(advDomainEmbedding φ)ᴴ) * advDomainEmbedding φ = A := by
    calc
      _ = ((advDomainEmbedding φ)ᴴ * advDomainEmbedding φ) * A * ((advDomainEmbedding φ)ᴴ * advDomainEmbedding φ) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [advDomainEmbedding_gram φ hφ]; simp
  have hb (B : Matrix X X ℂ) : ‖advDomainEmbedding φ*B*(advDomainEmbedding φ)ᴴ‖ ≤ ‖B‖ := by
    calc
      _ ≤ (‖advDomainEmbedding φ‖*‖B‖)*‖(advDomainEmbedding φ)ᴴ‖ := (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      _ ≤ (1*‖B‖)*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
      _ = _ := by ring
  apply le_antisymm (hb A)
  calc
    ‖A‖ = ‖(advDomainEmbedding φ)ᴴ * (advDomainEmbedding φ*A*(advDomainEmbedding φ)ᴴ) * advDomainEmbedding φ‖ := by rw [he]
    _ ≤ (‖(advDomainEmbedding φ)ᴴ‖*‖advDomainEmbedding φ*A*(advDomainEmbedding φ)ᴴ‖)*‖advDomainEmbedding φ‖ := (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*‖advDomainEmbedding φ*A*(advDomainEmbedding φ)ᴴ‖)*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = _ := by ring

omit [DecidableEq X] [Fintype Y] in

/-- When the input maps agree along `φ`, coordinate filtering commutes with padding by
`advDomainEmbedding φ`. -/
private theorem advDomainEmbedding_filter {κ : Type} [DecidableEq κ]
    (φ : X → Y) (inputX : X → κ → Bool) (inputY : Y → κ → Bool)
    (hinput : ∀ x, inputY (φ x) = inputX x) (A : Matrix X X ℂ) (i : κ) :
    weightedAdvFilter inputY (advDomainEmbedding φ*A*(advDomainEmbedding φ)ᴴ) i =
      advDomainEmbedding φ * weightedAdvFilter inputX A i * (advDomainEmbedding φ)ᴴ := by
  classical
  ext u v
  by_cases hd : inputY u i ≠ inputY v i
  · simp only [weightedAdvFilter, if_pos hd, Matrix.mul_apply, Finset.sum_mul,
      Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : φ x = u <;> by_cases hy : φ y = v
    · have he : inputX x i ≠ inputX y i := by
        rw [← congrFun (hinput x) i, ← congrFun (hinput y) i, hx, hy]
        exact hd
      simp [advDomainEmbedding, hx, hy, he]
    all_goals simp [advDomainEmbedding, hx, hy]
  · simp only [weightedAdvFilter, if_neg hd, Matrix.mul_apply, Finset.sum_mul,
      Matrix.conjTranspose_apply]
    symm
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : φ x = u <;> by_cases hy : φ y = v
    · have he : inputX x i = inputX y i := by
        rw [← congrFun (hinput x) i, ← congrFun (hinput y) i, hx, hy]
        exact not_ne_iff.mp hd
      simp [advDomainEmbedding, hx, hy, he]
    all_goals simp [advDomainEmbedding, hx, hy]

/-- A compatible injective embedding that preserves input strings and output labels cannot
decrease the optimized complex adversary value. -/
theorem advPlus_mono_of_injective {κ : Type} [Fintype κ] [DecidableEq κ] (α : κ → ℝ)
    (φ : X → Y) (hφ : Function.Injective φ)
    (inputX : X → κ → Bool) (gX : X → Bool)
    (inputY : Y → κ → Bool) (gY : Y → Bool)
    (hinput : ∀ x, inputY (φ x) = inputX x) (hg : ∀ x, gY (φ x) = gX x) :
    advPlus inputX gX α ≤ advPlus inputY gY α := by
  classical
  unfold advPlus
  apply iSup_le
  intro A
  let B : Matrix Y Y ℂ := advDomainEmbedding φ*A.val*(advDomainEmbedding φ)ᴴ
  have hB : B.IsHermitian :=
      Matrix.isHermitian_mul_mul_conjTranspose (advDomainEmbedding φ) A.property.1
  have hz : ∀ u v, gY u = gY v → B u v = 0 := by
    intro u v huv
    dsimp [B]
    simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.conjTranspose_apply]
    apply Finset.sum_eq_zero
    intro y _
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : φ x = u <;> by_cases hy : φ y = v
    · have he : gX x = gX y := by rw [← hg x, ← hg y, hx, hy]; exact huv
      simp [advDomainEmbedding, hx, hy, A.property.2 x y he]
    all_goals simp [advDomainEmbedding, hx, hy]
  let AB : {B : Matrix Y Y ℂ // B.IsHermitian ∧ ∀ u v, gY u = gY v → B u v = 0} :=
    ⟨B, hB, hz⟩
  have he : advWitnessValue inputX α A.val = advWitnessValue inputY α AB.val := by
    dsimp only [advWitnessValue, AB, B]
    apply congrArg iInf
    funext i
    rw [advDomainEmbedding_pad_norm φ hφ,
      advDomainEmbedding_filter φ inputX inputY hinput,
      advDomainEmbedding_pad_norm φ hφ]
  rw [he]
  exact le_iSup (fun (A : {A : Matrix Y Y ℂ // A.IsHermitian ∧ ∀ u v, gY u = gY v → A u v = 0}) =>
    ENNReal.ofReal (advWitnessValue inputY α A.val)) AB

end DomainEmbedding

section RealWeakDuality
variable {X : Type} [Fintype X] [DecidableEq X]

/-- The absolute quadratic form of a real matrix at `v` is bounded by its operator norm times
the sum of squared coordinates of `v`. -/
private theorem advReal_rayleigh_bound (A : Matrix X X ℝ) (v : X → ℝ) :
    |dotProduct v (A *ᵥ v)| ≤ ‖A‖ * ∑ x, (v x)^2 := by
  let u : EuclideanSpace ℝ X := WithLp.toLp 2 v
  have he : dotProduct v (A *ᵥ v) = inner ℝ u ((EuclideanSpace.equiv X ℝ).symm (A*ᵥu)) := by
    simp [PiLp.inner_apply, RCLike.inner_apply, u, dotProduct, mul_comm]
  rw [he]
  calc
    _ ≤ ‖u‖*‖(EuclideanSpace.equiv X ℝ).symm (A*ᵥu)‖ := by
      simpa only [Real.norm_eq_abs] using!
          norm_inner_le_norm (𝕜 := ℝ) u ((EuclideanSpace.equiv X ℝ).symm (A*ᵥu))
    _ ≤ ‖u‖*(‖A‖*‖u‖) := mul_le_mul_of_nonneg_left (A.l2_opNorm_mulVec u) (norm_nonneg u)
    _ = _ := by rw [← EuclideanSpace.real_norm_sq_eq u]; ring

/-- A Hermitian real matrix on a nonempty finite index type possesses a unit vector whose
absolute quadratic form equals its operator norm. -/
private theorem advReal_extreme [Nonempty X] (A : Matrix X X ℝ) (hA : A.IsHermitian) :
    ∃ v : X → ℝ, (∑ x, (v x)^2) = 1 ∧ |dotProduct v (A*ᵥv)| = ‖A‖ := by
  classical
  let ev : X → ℝ := hA.eigenvalues
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |ev i|) Finset.univ_nonempty
  have hn : ‖ev‖ = |ev i| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro j
      simpa only [Real.norm_eq_abs] using! hi j (Finset.mem_univ j)
    · simpa only [Real.norm_eq_abs] using! norm_le_pi_norm ev i
  have hnorm : ‖A‖ = ‖ev‖ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    change ‖(hA.eigenvectorUnitary : Matrix X X ℝ)*Matrix.diagonal ev*
      (star hA.eigenvectorUnitary : unitary (Matrix X X ℝ))‖ = ‖ev‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  let v : EuclideanSpace ℝ X := hA.eigenvectorBasis i
  have hv : ∑ x, (v x)^2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hA.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have he : A *ᵥ v = ev i • (v : X → ℝ) := hA.mulVec_eigenvectorBasis i
  refine ⟨v, hv, ?_⟩
  rw [he, dotProduct_smul]
  have hs : dotProduct (v : X → ℝ) v = 1 := by simpa only [dotProduct, ← pow_two] using! hv
  rw [hs, smul_eq_mul, mul_one, ← hn, ← hnorm]

/-- A Hermitian entrywise nonnegative real matrix on a nonempty finite index type possesses a
nonnegative unit vector whose quadratic form is at least its operator norm. -/
private theorem advReal_nonnegative_extreme [Nonempty X] (A : Matrix X X ℝ)
    (hA : A.IsHermitian) (hnn : ∀ x y, 0 ≤ A x y) :
    ∃ δ : X → ℝ, (∀ x, 0 ≤ δ x) ∧ (∑ x, (δ x)^2) = 1 ∧
      ‖A‖ ≤ ∑ x, ∑ y, A x y * δ x * δ y := by
  obtain ⟨v, hv, he⟩ := advReal_extreme A hA
  refine ⟨fun x => |v x|, fun x => abs_nonneg _, ?_, ?_⟩
  · simpa only [sq_abs] using! hv
  · rw [← he]
    unfold dotProduct Matrix.mulVec
    simp only [dotProduct, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro x _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro y _
    rw [abs_mul, abs_mul, abs_of_nonneg (hnn x y)]
    exact le_of_eq (by ring)

/-- For a nonzero symmetric nonnegative witness and positive coordinate costs, every family of
coordinate distributions has an unequal-output pair whose overlap term is at most the
supremum of the normalized filter norms. -/
theorem advNonneg_witness_le_minimaxTerm
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (hα : ∀ i, 0 < α i)
    (Γ : Matrix X X ℝ) (hsymm : Γ.IsSymm) (hnn : ∀ x y, 0 ≤ Γ x y)
    (hz : ∀ x y, g x = g y → Γ x y = 0) (hpos : 0 < ‖Γ‖)
    (p : X → κ → ℝ) (hp0 : ∀ x i, 0 ≤ p x i) (hp1 : ∀ x, ∑ i, p x i = 1) :
    ∃ x y, g x ≠ g y ∧ advMinimaxTerm input α p x y ≤
      ⨆ i, ‖advFilterR input Γ i‖ / (‖Γ‖ * α i) := by
  classical
  have hne : Γ ≠ 0 := by intro he; simp [he] at hpos
  obtain ⟨x₀, hx⟩ := Function.ne_iff.mp hne
  letI : Nonempty X := ⟨x₀⟩
  have hκ : Nonempty κ := by
    by_contra he
    letI : IsEmpty κ := not_nonempty_iff.mp he
    have hh := hp1 x₀
    simp at hh
  letI : Nonempty κ := hκ
  have hΓ : Γ.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x y
    simpa only [star_trivial] using! congrFun (congrFun hsymm x) y
  obtain ⟨δ, hδ0, hδ1, hδΓ⟩ := advReal_nonnegative_extreme Γ hΓ hnn
  let t := ⨆ i, ‖advFilterR input Γ i‖ / (‖Γ‖*α i)
  have ht0 : 0 ≤ t := by
    let i₀ := Classical.arbitrary κ
    calc
      0 ≤ ‖advFilterR input Γ i₀‖/(‖Γ‖*α i₀) :=
        div_nonneg (norm_nonneg _) (mul_nonneg hpos.le (hα i₀).le)
      _ ≤ t := le_ciSup (Set.finite_range (fun i => ‖advFilterR input Γ i‖/(‖Γ‖*α i))).bddAbove i₀
  let v (i : κ) (x : X) := δ x * Real.sqrt (p x i)
  let E (i : κ) := ∑ x, (δ x)^2*p x i
  have hE0 (i : κ) : 0 ≤ E i := Finset.sum_nonneg (fun x _ => mul_nonneg (sq_nonneg _) (hp0 x i))
  have hE1 : ∑ i, E i = 1 := by
    dsimp [E]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hp1, mul_one, hδ1]
  let M := ∑ i, dotProduct (v i) (advFilterR input Γ i *ᵥ v i) / α i
  have hM : M ≤ t*‖Γ‖ := by
    calc
      _ ≤ ∑ i, (‖advFilterR input Γ i‖/α i)*E i := by
        apply Finset.sum_le_sum
        intro i _
        have hb := (le_abs_self _).trans (advReal_rayleigh_bound (advFilterR input Γ i) (v i))
        have hev : (∑ x, (v i x)^2) = E i := by
          dsimp [v, E]
          simp_rw [mul_pow, Real.sq_sqrt (hp0 _ i)]
        rw [hev] at hb
        exact (div_le_div_of_nonneg_right hb (hα i).le).trans_eq (by ring)
      _ ≤ ∑ i, (t*‖Γ‖)*E i := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_right _ (hE0 i)
        apply (div_le_iff₀ hpos).mp
        convert! le_ciSup (Set.finite_range (fun i => ‖advFilterR input Γ i‖/(‖Γ‖*α i))).bddAbove i using 1
        ring
      _ = t*‖Γ‖ := by rw [← Finset.mul_sum, hE1, mul_one]
  let Z (xy : X×X) := Γ xy.1 xy.2 * δ xy.1 * δ xy.2
  have hZ0 (xy : X×X) : 0 ≤ Z xy :=
    mul_nonneg (mul_nonneg (hnn _ _) (hδ0 _)) (hδ0 _)
  have hZsum : ‖Γ‖ ≤ ∑ xy : X×X, Z xy := by
    simpa only [Fintype.sum_prod_type, Z] using! hδΓ
  have hMZ : M = ∑ xy : X×X, Z xy * advMinimaxTerm input α p xy.1 xy.2 := by
    calc
      M = ∑ i, ∑ x, ∑ y, (Γ x y*δ x*δ y)*
          (if input x i ≠ input y i then Real.sqrt (p x i*p y i)/α i else 0) := by
        dsimp [M, v]
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        by_cases hi : input x i ≠ input y i
        · rw [if_pos hi, Real.sqrt_mul (hp0 x i)]
          simp only [advFilterR, if_pos hi]
          ring
        · simp [advFilterR, hi]
      _ = ∑ x, ∑ y, ∑ i, (Γ x y*δ x*δ y)*
          (if input x i ≠ input y i then Real.sqrt (p x i*p y i)/α i else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
      _ = _ := by simp only [Fintype.sum_prod_type, Z, advMinimaxTerm, Finset.mul_sum]
  by_contra hbad
  have hbad' : ∀ x y, g x ≠ g y → t < advMinimaxTerm input α p x y := by
    intro x y hg
    by_contra hh
    exact hbad ⟨x,y,hg,not_lt.mp hh⟩
  have hzpos : ∃ xy : X×X, 0 < Z xy := by
    by_contra hh
    have hzero (xy : X×X) : Z xy = 0 := le_antisymm (not_lt.mp (fun he => hh ⟨xy,he⟩)) (hZ0 xy)
    simp_rw [hzero] at hZsum
    simp only [Finset.sum_const_zero] at hZsum
    exact hpos.not_ge hZsum
  obtain ⟨xy₀,hxy₀⟩ := hzpos
  have hcross : g xy₀.1 ≠ g xy₀.2 := by
    intro he
    have hz' := hz _ _ he
    have : Z xy₀ = 0 := by dsimp [Z]; rw [hz']; ring
    rw [this] at hxy₀
    exact lt_irrefl _ hxy₀
  have hlt : (∑ xy : X×X, t*Z xy) < ∑ xy : X×X, Z xy*advMinimaxTerm input α p xy.1 xy.2 := by
    apply Finset.sum_lt_sum
    · intro xy _
      by_cases he : g xy.1 = g xy.2
      · have : Z xy = 0 := by dsimp [Z]; rw [hz _ _ he]; ring
        simp [this]
      · have hh := mul_le_mul_of_nonneg_left (hbad' _ _ he).le (hZ0 xy)
        simpa only [mul_comm] using! hh
    · refine ⟨xy₀,Finset.mem_univ _,?_⟩
      simpa only [mul_comm] using! mul_lt_mul_of_pos_left (hbad' _ _ hcross) hxy₀
  rw [← Finset.mul_sum, ← hMZ] at hlt
  have hb := mul_le_mul_of_nonneg_left hZsum ht0
  exact (hb.trans_lt hlt).not_ge hM

/-- With nonnegative coordinate costs, the real witness value is nonnegative. -/
private theorem advWitnessValueR_nonneg {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (α : κ → ℝ) (hα : ∀ i, 0 ≤ α i) (Γ : Matrix X X ℝ) :
    0 ≤ advWitnessValueR input α Γ := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · letI := hκ
    simp [advWitnessValueR]
  · letI := hκ
    exact le_ciInf (fun i => div_nonneg (mul_nonneg (hα i) (norm_nonneg Γ)) (norm_nonneg _))

/-- A real witness with zero operator norm has witness value zero. -/
private theorem advWitnessValueR_norm_zero {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (α : κ → ℝ) (Γ : Matrix X X ℝ) (hΓ : ‖Γ‖ = 0) :
    advWitnessValueR input α Γ = 0 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ <;> letI := hκ <;>
    simp [advWitnessValueR, hΓ]

/-- For positive coordinate costs and positive witness norm, the product of the real witness
value and the supremum of normalized filter norms is at most one. -/
private theorem advWitnessValueR_mul_filter_sup_le_one {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (α : κ → ℝ) (hα : ∀ i, 0 < α i)
    (Γ : Matrix X X ℝ) (hΓ : 0 < ‖Γ‖) :
    advWitnessValueR input α Γ * (⨆ i, ‖advFilterR input Γ i‖/(‖Γ‖*α i)) ≤ 1 := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · letI := hκ
    simp [advWitnessValueR]
  · letI := hκ
    let f (i : κ) := ‖advFilterR input Γ i‖/(‖Γ‖*α i)
    obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    have he : (⨆ i, f i) = f j := le_antisymm
      (ciSup_le (fun i => hj i (Finset.mem_univ i)))
      (le_ciSup (Set.finite_range f).bddAbove j)
    change advWitnessValueR input α Γ * (⨆ i, f i) ≤ 1
    rw [he]
    by_cases hz : ‖advFilterR input Γ j‖ = 0
    · simp [f, hz]
    · have hp : 0 < ‖advFilterR input Γ j‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hv : advWitnessValueR input α Γ ≤ α j*‖Γ‖/‖advFilterR input Γ j‖ :=
        ciInf_le (Set.finite_range _).bddBelow j
      have hf : 0 ≤ f j := div_nonneg (norm_nonneg _) (mul_nonneg hΓ.le (hα j).le)
      apply (mul_le_mul_of_nonneg_right hv hf).trans_eq
      dsimp [f]
      field_simp [(hα j).ne']

/-- For strictly positive coordinate costs, the optimized nonnegative adversary value is at most
`minimaxAlpha`. -/
theorem advNonneg_le_minimaxAlpha {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (α : κ → ℝ) (hα : ∀ i, 0 < α i) :
    advNonneg input g α ≤ minimaxAlpha input g α := by
  classical
  unfold advNonneg
  refine iSup_le fun Γ => ?_
  by_cases hzero : ‖Γ.val‖ = 0
  · rw [advWitnessValueR_norm_zero input α Γ.val hzero]
    simp
  · have hpos : 0 < ‖Γ.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    rw [minimaxAlpha, ENNReal.le_inv_iff_mul_le, ENNReal.mul_iSup]
    refine iSup_le fun p => ?_
    obtain ⟨x,y,hxy,hbound⟩ := advNonneg_witness_le_minimaxTerm input g α hα Γ.val
      Γ.property.1 Γ.property.2.1 Γ.property.2.2 hpos p.val p.property.1 p.property.2
    let r := ⨆ i, ‖advFilterR input Γ.val i‖/(‖Γ.val‖*α i)
    have hk : (⨅ xy : {xy : X×X // g xy.1 ≠ g xy.2},
        advMinimaxTerm input α p.val xy.val.1 xy.val.2) ≤ r := by
      exact (ciInf_le (Set.finite_range _).bddBelow ⟨(x,y),hxy⟩).trans hbound
    calc
      _ ≤ ENNReal.ofReal (advWitnessValueR input α Γ.val)*ENNReal.ofReal r :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hk) (bot_le : 0 ≤ ENNReal.ofReal (advWitnessValueR input α Γ.val))
      _ = ENNReal.ofReal (advWitnessValueR input α Γ.val*r) :=
        (ENNReal.ofReal_mul (advWitnessValueR_nonneg input α (fun i => (hα i).le) Γ.val)).symm
      _ ≤ 1 := ENNReal.ofReal_le_one.mpr (advWitnessValueR_mul_filter_sup_le_one input α hα Γ.val hpos)

/-- If every unequal-output pair has a differing coordinate in the intersection of its
certificates and all certificate sizes are at most a nonnegative `C`, the unit-cost
nonnegative adversary value is at most `ENNReal.ofReal C`. -/
theorem advNonneg_le_of_certificates {κ : Type} [Fintype κ] [DecidableEq κ]
    (input : X → κ → Bool) (g : X → Bool) (c : X → Finset κ) (C : ℝ) (hC : 0 ≤ C)
    (hcard : ∀ x, (c x).card ≤ C)
    (hc : ∀ x y, g x ≠ g y → ∃ j ∈ c x ∩ c y, input x j ≠ input y j) :
    advNonneg input g (fun _ => 1) ≤ ENNReal.ofReal C := by
  classical
  by_cases hnc : ∃ a b, g a ≠ g b
  · obtain ⟨a,b,hab⟩ := hnc
    have hd (x : X) : ∃ y, g x ≠ g y := by
      by_cases he : g x = g a
      · exact ⟨b,fun hh => hab (he.symm.trans hh)⟩
      · exact ⟨a,he⟩
    have hcpos (x : X) : 0 < (c x).card := by
      obtain ⟨y,hxy⟩ := hd x
      obtain ⟨j,hj,_⟩ := hc x y hxy
      exact Finset.card_pos.mpr ⟨j,(Finset.mem_inter.mp hj).1⟩
    have hcposR (x : X) : 0 < ((c x).card : ℝ) := by exact_mod_cast hcpos x
    have hCpos : 0 < C := (hcposR a).trans_le (hcard a)
    obtain ⟨j₀,hj₀,_⟩ := hc a b hab
    letI : Nonempty κ := ⟨j₀⟩
    let p (x : X) (i : κ) : ℝ := if i ∈ c x then 1/((c x).card : ℝ) else 0
    have hp0 (x : X) (i : κ) : 0 ≤ p x i := by dsimp [p]; split_ifs <;> positivity
    have hp1 (x : X) : ∑ i, p x i = 1 := by
      simp [p, Finset.sum_ite_mem, (hcposR x).ne']
    have hk (x y : X) (hxy : g x ≠ g y) : 1/C ≤ advMinimaxTerm input (fun _ => 1) p x y := by
      obtain ⟨j,hj,hdiff⟩ := hc x y hxy
      have hjx := (Finset.mem_inter.mp hj).1
      have hjy := (Finset.mem_inter.mp hj).2
      have hx := one_div_le_one_div_of_le (hcposR x) (hcard x)
      have hy := one_div_le_one_div_of_le (hcposR y) (hcard y)
      have hprod : (1/C)^2 ≤ (1/((c x).card : ℝ))*(1/((c y).card : ℝ)) := by
        simpa only [pow_two] using!
            mul_le_mul hx hy (by positivity : 0 ≤ 1/C) (by positivity : 0 ≤ 1/((c x).card : ℝ))
      calc
        _ ≤ Real.sqrt ((1/((c x).card : ℝ))*(1/((c y).card : ℝ))) := Real.le_sqrt_of_sq_le hprod
        _ = (if input x j ≠ input y j then Real.sqrt (p x j*p y j)/(1:ℝ) else 0) := by simp [p,hjx,hjy,hdiff]
        _ ≤ _ := by
          change (if input x j ≠ input y j then Real.sqrt (p x j*p y j)/(1:ℝ) else 0) ≤
            ∑ i : κ, if input x i ≠ input y i then Real.sqrt (p x i*p y i)/(1:ℝ) else 0
          exact Finset.single_le_sum (f := fun (i : κ) =>
            if input x i ≠ input y i then Real.sqrt (p x i*p y i)/(1:ℝ) else 0)
            (fun i _ => by (try dsimp only); split_ifs <;> positivity) (Finset.mem_univ j)
    unfold advNonneg
    refine iSup_le fun Γ => ?_
    by_cases hzero : ‖Γ.val‖ = 0
    · rw [advWitnessValueR_norm_zero input (fun _ => 1) Γ.val hzero]
      simp
    · have hpos : 0 < ‖Γ.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      obtain ⟨x,y,hxy,hbound⟩ := advNonneg_witness_le_minimaxTerm input g (fun _ => 1)
        (by intro i; norm_num) Γ.val Γ.property.1 Γ.property.2.1 Γ.property.2.2 hpos p hp0 hp1
      let f (i : κ) := ‖advFilterR input Γ.val i‖/‖Γ.val‖
      obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
      have he : (⨆ i, f i) = f j := le_antisymm
        (ciSup_le (fun i => hj i (Finset.mem_univ i)))
        (le_ciSup (Set.finite_range f).bddAbove j)
      have hr : 1/C ≤ f j := by
        have hb := (hk x y hxy).trans hbound
        simp only [mul_one] at hb
        change 1/C ≤ (⨆ i, f i) at hb
        rw [he] at hb
        exact hb
      have hn : ‖Γ.val‖/C ≤ ‖advFilterR input Γ.val j‖ := by
        have hh := (le_div_iff₀ hpos).mp hr
        convert! hh using 1
        ring
      have hfpos : 0 < ‖advFilterR input Γ.val j‖ := (div_pos hpos hCpos).trans_le hn
      have hv : advWitnessValueR input (fun _ => 1) Γ.val ≤ C := by
        calc
          _ ≤ ‖Γ.val‖/‖advFilterR input Γ.val j‖ := by
            simpa only [advWitnessValueR, one_mul] using!
                ciInf_le (Set.finite_range (fun i : κ => (1:ℝ)*‖Γ.val‖/‖advFilterR input Γ.val i‖)).bddBelow j
          _ ≤ C := (div_le_iff₀ hfpos).mpr (by
            have hh := (div_le_iff₀ hCpos).mp hn
            nlinarith [hh])
      exact ENNReal.ofReal_le_ofReal hv
  · unfold advNonneg
    refine iSup_le fun Γ => ?_
    have hz : Γ.val = 0 := by
      ext x y
      exact Γ.property.2.2 x y (by by_contra hh; exact hnc ⟨x,y,hh⟩)
    rw [hz, advWitnessValueR_norm_zero input (fun _ => 1) 0 (norm_zero)]
    exact ENNReal.ofReal_le_ofReal hC

end RealWeakDuality

/-- A complex witness with zero operator norm has witness value zero. -/
private theorem advWitnessValue_norm_zero {Z κ : Type} [Fintype Z] [DecidableEq Z]
    [Fintype κ] [DecidableEq κ] (input : Z → κ → Bool) (α : κ → ℝ)
    (A : Matrix Z Z ℂ) (hA : ‖A‖ = 0) : advWitnessValue input α A = 0 := by
  rcases isEmpty_or_nonempty κ with hκ | hκ <;> letI := hκ <;> simp [advWitnessValue,hA]

/-- For positive `β` and `δ`, if `ENNReal.ofReal β` is below the optimized adversary value,
there is a Hermitian output-zero witness of positive norm with value at least `β - δ`. -/
private theorem advPlus_approximate_witness {Z κ : Type} [Fintype Z] [DecidableEq Z]
    [Fintype κ] [DecidableEq κ] (input : Z → κ → Bool) (g : Z → Bool) (α : κ → ℝ)
    (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) (hS : ENNReal.ofReal β ≤ advPlus input g α) :
    ∃ A : {A : Matrix Z Z ℂ // A.IsHermitian ∧ ∀ x y, g x = g y → A x y = 0},
      0 < ‖A.val‖ ∧ β-δ ≤ advWitnessValue input α A.val := by
  let b := max (β-δ) (β/2)
  have hb0 : 0 < b := (by positivity : 0 < β/2).trans_le (le_max_right _ _)
  have hbb : b < β := max_lt (by linarith) (by linarith)
  have hs : ENNReal.ofReal b < advPlus input g α :=
    ((ENNReal.ofReal_lt_ofReal_iff hβ).mpr hbb).trans_le hS
  change ENNReal.ofReal b < ⨆ A : {A : Matrix Z Z ℂ // A.IsHermitian ∧ ∀ x y, g x = g y → A x y = 0},
    ENNReal.ofReal (advWitnessValue input α A.val) at hs
  obtain ⟨A,hA⟩ := (lt_iSup_iff).mp hs
  have hv : b < advWitnessValue input α A.val :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb0.le).mp hA
  have hn : 0 < ‖A.val‖ := by
    apply lt_of_le_of_ne (norm_nonneg _)
    intro hh
    have hz := advWitnessValue_norm_zero input α A.val hh.symm
    rw [hz] at hv
    exact (hb0.trans hv).false
  exact ⟨A,hn,(le_max_left _ _).trans hv.le⟩

/-- With positive block lengths, nonconstant inner Boolean functions, and nonnegative coordinate
costs, any inner optimized lower bounds `β` yield a composed adversary value at least the
outer value with costs `β`, as in [HoyerLeeSpalek2007]. -/
theorem advPlus_composition_ge
    (k : ℕ) (X : Fin k → Type) [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    (n : Fin k → ℕ) (hne : ∀ i, 0 < n i)
    (g : ∀ i, X i → Bool) (_hnc : ∀ i, ∃ u v, g i u ≠ g i v)
    (f : (Fin k → Bool) → Bool) (gin : ∀ i, X i → Fin (n i) → Bool)
    (α : (i : Fin k) × Fin (n i) → ℝ) (hα : ∀ c, 0 ≤ α c)
    (β : Fin k → ℝ)
    (hβ : ∀ i, ENNReal.ofReal (β i) ≤ advPlus (gin i) (g i) (fun q => α ⟨i,q⟩)) :
    advPlus (weightedAdvInput gin) (fun x => f (fun i => g i (x i))) α ≥ advPlus (fun t => t) f β := by
  classical
  let S := advPlus (weightedAdvInput gin) (fun x => f (fun i => g i (x i))) α
  by_cases hS : S = ∞
  · simp only [show advPlus (weightedAdvInput gin) (fun x => f (fun i => g i (x i))) α = ∞ from hS]
    exact le_top
  unfold advPlus
  refine iSup_le fun A => ?_
  let v := advWitnessValue (fun t => t) β A.val
  by_cases hv0 : v ≤ 0
  · change ENNReal.ofReal v ≤ S
    rw [ENNReal.ofReal_of_nonpos hv0]
    exact bot_le
  have hv : 0 < v := not_le.mp hv0
  have hk : Nonempty (Fin k) := by
    by_contra hh
    letI : IsEmpty (Fin k) := not_nonempty_iff.mp hh
    simp [v,advWitnessValue] at hv
  letI : Nonempty (Fin k) := hk
  have hβpos (i : Fin k) : 0 < β i := by
    have hb : v ≤ β i*‖A.val‖/‖weightedAdvFilter (fun t => t) A.val i‖ :=
      ciInf_le (Set.finite_range (fun i : Fin k => β i*‖A.val‖/‖weightedAdvFilter (fun t => t) A.val i‖)).bddBelow i
    by_contra hh
    have hn : β i*‖A.val‖/‖weightedAdvFilter (fun t => t) A.val i‖ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hh) (norm_nonneg _)) (norm_nonneg _)
    exact hv.not_ge (hb.trans hn)
  let r (i : Fin k) := ‖A.val‖/‖advFilter id A.val i‖
  let R := ⨆ i, r i
  have hr0 (i : Fin k) : 0 ≤ r i := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hR0 : 0 ≤ R := (hr0 (Classical.arbitrary _)).trans (le_ciSup (Set.finite_range r).bddAbove _)
  have happrox (ε : ℝ) (hε : 0 < ε) : v ≤ S.toReal+ε := by
    let δ := ε/(R+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hblock (i : Fin k) := advPlus_approximate_witness (gin i) (g i) (fun q => α ⟨i,q⟩)
      (β i) δ (hβpos i) hδ (hβ i)
    choose W hWnorm hWnear using hblock
    let Gg := fun i => (W i).val
    let B := weightedAdvGamma g f A.val Gg
    have hB : B.IsHermitian :=
        weightedAdvGamma_isHermitian g f A.val Gg A.property.1 (fun i => (W i).property.1)
    have hz : ∀ x y, f (fun i => g i (x i)) = f (fun i => g i (y i)) → B x y = 0 :=
      fun x y he => weightedAdvGamma_same_output_zero g f A.val Gg A.property.2 x y he
    let WB : {B : Matrix ((i : Fin k) → X i) ((i : Fin k) → X i) ℂ //
      B.IsHermitian ∧ ∀ x y, f (fun i => g i (x i)) = f (fun i => g i (y i)) → B x y = 0} := ⟨B,hB,hz⟩
    letI : Nonempty ((i : Fin k) × Fin (n i)) := ⟨⟨Classical.arbitrary _,⟨0,hne _⟩⟩⟩
    have hval : v-δ*R ≤ advWitnessValue (weightedAdvInput gin) α B := by
      apply le_ciInf
      intro c
      obtain ⟨i,q⟩ := c
      have hcom := weightedAdvGamma_composition_value g f A.val Gg gin A.property.1
        (fun i => (W i).property.1) A.property.2 (fun i => (W i).property.2)
        (fun i q => α ⟨i,q⟩) (fun i q => hα ⟨i,q⟩) hWnorm
        (fun i => advWitnessValue (gin i) (fun q => α ⟨i,q⟩) (W i).val)
        (fun i q => ciInf_le (Set.finite_range (fun q : Fin (n i) => α ⟨i,q⟩*‖(W i).val‖/‖advFilter (gin i) (W i).val q‖)).bddBelow q) i q
      have hb : v ≤ β i*r i := by
        simpa only [v,advWitnessValue,r,advFilter,weightedAdvFilter,mul_div_assoc] using!
          ciInf_le (Set.finite_range (fun i : Fin k => β i*‖A.val‖/‖advFilter id A.val i‖)).bddBelow i
      have hp := mul_le_mul_of_nonneg_left (hWnear i) (hr0 i)
      have hri : r i ≤ R := le_ciSup (Set.finite_range r).bddAbove i
      have hδR := mul_le_mul_of_nonneg_left hri hδ.le
      change r i*advWitnessValue (gin i) (fun q => α ⟨i,q⟩) (W i).val ≤
        α ⟨i,q⟩*‖B‖/‖weightedAdvFilter (weightedAdvInput gin) B ⟨i,q⟩‖ at hcom
      nlinarith [hp,hcom,hb,hδR]
    have hsup : ENNReal.ofReal (advWitnessValue (weightedAdvInput gin) α B) ≤ S := by
      apply le_iSup_of_le WB
      exact le_rfl
    have hlower : v-δ*R ≤ S.toReal := (ENNReal.ofReal_le_iff_le_toReal hS).mp
      ((ENNReal.ofReal_le_ofReal hval).trans hsup)
    have herror : δ*R ≤ ε := by
      dsimp [δ]; rw [div_mul_eq_mul_div]; apply
        (div_le_iff₀ (by positivity : 0 < R+1)).mpr; nlinarith
    linarith
  have hvS : v ≤ S.toReal := by
    by_contra hh
    have hε : 0 < (v-S.toReal)/2 := by linarith
    have he := happrox ((v-S.toReal)/2) hε
    linarith
  exact ENNReal.ofReal_le_of_le_toReal hvS

end

end Qatlib.Concepts.AdversaryBounds.OptimizedAdv
