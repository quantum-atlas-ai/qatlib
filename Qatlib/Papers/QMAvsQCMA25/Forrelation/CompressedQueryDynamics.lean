/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamicsDefs
public import Qatlib.Concepts.WalshMoment.Forrelation.StrongYesInstancePropertyStat
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.WalshMoment.Forrelation Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PauliClifford.ExactRank Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.BosonFock.BosonOperators
open Qatlib.Concepts.FreshFallback.BitScanLedger
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- Summing multinomial coefficients over the finite antidiagonal equals summing them over
occupation profiles of the same total size. -/
theorem sum_multinomial_piAntidiag (N t : ℕ) :
    (Finset.sum (Finset.piAntidiag (Finset.univ : Finset (Fin N)) t)
        (fun k => (Nat.multinomial (Finset.univ : Finset (Fin N)) k : ℝ)))
      = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
        (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
          (fun x => (v.1 x : ℕ)) : ℝ)) := by
  classical
  refine Finset.sum_bij
    (fun k (hk : k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin N)) t) =>
      profileOf k (Finset.mem_piAntidiag.mp hk).1) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_univ _
  · intro k₁ hk₁ k₂ hk₂ heq
    have hval : (profileOf k₁ (Finset.mem_piAntidiag.mp hk₁).1).1
        = (profileOf k₂ (Finset.mem_piAntidiag.mp hk₂).1).1 := congrArg Subtype.val heq
    funext x
    exact congrArg Fin.val (congrFun hval x)
  · intro v hv
    refine ⟨fun x => (v.1 x : ℕ), ?_⟩
    refine ⟨?_, ?_⟩
    · refine Finset.mem_piAntidiag.mpr ⟨?_, ?_⟩
      · exact v.property
      · intro x hx
        exact Finset.mem_univ x
    · have hprof : profileOf (fun x => (v.1 x : ℕ)) v.property = v := by
        apply Subtype.ext
        funext x
        apply Fin.ext
        simp [profileOf]
      exact hprof
  · intro k hk
    have hval : (fun x => ((profileOf k (Finset.mem_piAntidiag.mp hk).1).1 x : ℕ))
        = (fun x => k x) := by
      funext x
      simp [profileOf]
    rw [hval]

/-- The sum of multinomial coefficients over all occupation profiles with total `t` is `N` to
the power `t`. -/
theorem sum_multinomial_eq (N t : ℕ) :
    Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
        (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
          (fun x => (v.1 x : ℕ)) : ℝ))
      = (N : ℝ) ^ t := by
  rw [← sum_multinomial_piAntidiag N t]
  calc (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin N)) t,
          (Nat.multinomial (Finset.univ : Finset (Fin N)) k : ℝ))
      = (∑ i ∈ (Finset.univ : Finset (Fin N)), (1 : ℝ)) ^ t := by
        symm
        have h := Finset.sum_pow_eq_sum_piAntidiag (s := (Finset.univ : Finset (Fin N)))
          (f := fun _ => (1 : ℝ)) t
        simpa [Finset.sum_const, Fintype.card_fin] using! h
    _ = (N : ℝ) ^ t := by simp

/-- For a positive number of modes, the uniform multiset probabilities sum to one. -/
theorem uniformMultisetProb_sum_eq_one (N t : ℕ) (hN : 0 < N) :
    ∑ v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t v = 1 := by
  have hmul : ∀ v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      uniformMultisetProb N t v
        = ((Nat.multinomial (Finset.univ : Finset (Fin N))
          (fun x => (v.1 x : ℕ)) : ℝ)) * ((N : ℝ) ^ t)⁻¹ := by
    intro v
    simp [uniformMultisetProb, div_eq_mul_inv]
  have hmain : Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
      (fun v => uniformMultisetProb N t v) = 1 := by
    calc Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
            (fun v => uniformMultisetProb N t v)
        = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
            (fun v => ((Nat.multinomial (Finset.univ : Finset (Fin N))
              (fun x => (v.1 x : ℕ)) : ℝ)) * ((N : ℝ) ^ t)⁻¹) := by
              rw [Finset.sum_congr rfl]
              intro v _
              exact hmul v
        _ = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
            (fun v => ((Nat.multinomial (Finset.univ : Finset (Fin N))
              (fun x => (v.1 x : ℕ)) : ℝ))) * ((N : ℝ) ^ t)⁻¹ := by
              rw [← Finset.sum_mul]
        _ = (N : ℝ) ^ t * ((N : ℝ) ^ t)⁻¹ := by rw [sum_multinomial_eq N t]
        _ = 1 := by
              rw [mul_inv_cancel₀]
              positivity
  exact hmain

/-- The multinomial coefficient of an occupation profile is the factorial of its total divided
by the product of the occupation factorials. -/
theorem natMultinomial_eq (N t : ℕ) (v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    Nat.multinomial (Finset.univ : Finset (Fin N)) (fun x => (v.1 x : ℕ))
      = Nat.factorial t / ∏ x : Fin N, Nat.factorial (v.1 x : ℕ) := by
  rw [Nat.multinomial]
  have hsum : ∑ x : Fin N, (v.1 x : ℕ) = t := v.property
  rw [hsum]

/-- The uniform multiset probability equals the total factorial divided by the number of ordered
placements times the occupation factorial product. -/
theorem uniformMultisetProb_eq (N t : ℕ) (v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    uniformMultisetProb N t v
      = (Nat.factorial t : ℝ)
        / ((N : ℝ) ^ t * ∏ x : Fin N, (Nat.factorial (v.1 x : ℕ) : ℝ)) := by
  rw [uniformMultisetProb, natMultinomial_eq]
  have hdiv : (∏ x : Fin N, Nat.factorial (v.1 x : ℕ)) ∣ Nat.factorial t := by
    have h := Nat.prod_factorial_dvd_factorial_sum (Finset.univ : Finset (Fin N))
      (fun x => (v.1 x : ℕ))
    have h' : (∑ x ∈ (Finset.univ : Finset (Fin N)), (v.1 x : ℕ)) = t := v.property
    rw [h'] at h
    exact h
  have hpos : (0 : ℕ)
      < ∏ x ∈ (Finset.univ : Finset (Fin N)), Nat.factorial (v.1 x : ℕ) :=
    Finset.prod_pos (fun x _ => Nat.factorial_pos _)
  have hne : (Nat.cast (∏ x : Fin N, Nat.factorial (v.1 x : ℕ)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
  rw [Nat.cast_div hdiv hne]
  rw [Nat.cast_prod]
  ring

/-- A placement profile records the fibre count at each mode. -/
theorem placementProfile_val {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) :
    ((placementProfile f).1 x : ℕ) = fibreCount f x := rfl

/-- Two placements have equal occupation profiles exactly when all their fibre counts agree. -/
theorem placementProfile_eq_iff_fibreCount {N t : ℕ} (f g : Fin t → Fin N) :
    placementProfile f = placementProfile g
      ↔ ∀ x : Fin N, fibreCount f x = fibreCount g x := by
  constructor
  · intro h x
    have h' : (placementProfile f : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t)
        = (placementProfile g : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) := h
    have hval :=
        congrArg (fun v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t => (v.1 x : ℕ)) h'
    simpa using! hval
  · intro h
    apply Subtype.ext
    funext x
    apply Fin.ext
    exact h x

/-- The probability of a placement profile is its multinomial ordering count divided by the
total number of ordered placements. -/
theorem multisetProb_eq_orderings {N t : ℕ} (f : Fin t → Fin N) :
    uniformMultisetProb N t (placementProfile f)
      = (Nat.multinomial (Finset.univ : Finset (Fin N))
          (fun x => fibreCount f x) : ℝ) / (N : ℝ) ^ t := by
  simp [uniformMultisetProb, placementProfile_val]

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds

/-- Every natural power of the inverse square-root-of-two Hadamard prefactor is fixed by complex
conjugation. -/
theorem hadamard_prefactor_real (k : ℕ) :
    star ((Real.sqrt 2 : ℂ)⁻¹ ^ k) = (Real.sqrt 2 : ℂ)⁻¹ ^ k := by
  rw [star_pow]
  have hpre : star ((Real.sqrt 2 : ℂ)⁻¹) = (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [star_inv₀]
    simp
  rw [hpre]

/-- Every entry of the Fock-mode Hadamard matrix is fixed by complex conjugation. -/
theorem hadamardFock_real (n : ℕ) (x y : Fin (2 ^ n)) :
    star (hadamardFock n x y) = hadamardFock n x y := by
  rw [hadamardFock_apply]
  rw [star_mul', hadamard_prefactor_real n, star_prod]
  apply congrArg (fun u : ℂ => (Real.sqrt 2 : ℂ)⁻¹ ^ n * u)
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : (momentumMode n x i && momentumMode n y i) = true
  · simp [h]
  · simp [h]

/-- The Fock-mode Hadamard matrix is symmetric. -/
theorem hadamardFock_symm (n : ℕ) (x y : Fin (2 ^ n)) :
    hadamardFock n x y = hadamardFock n y x := by
  rw [hadamardFock_apply, hadamardFock_apply]
  have key : ∀ i : Fin n,
      (if momentumMode n x i && momentumMode n y i then (-1 : ℂ) else 1)
        = (if momentumMode n y i && momentumMode n x i then (-1 : ℂ) else 1) := by
    intro i
    by_cases hx : momentumMode n x i = true
    · by_cases hy : momentumMode n y i = true
      · simp [hx, hy]
      · simp [hx, hy]
    · by_cases hy : momentumMode n y i = true
      · simp [hx, hy]
      · simp [hx, hy]
  rw [Finset.prod_congr rfl (fun i _ => key i)]

/-- The bilinear pairing of two rows of the Fock-mode Hadamard matrix is one for equal rows and
zero otherwise. -/
theorem hadamardFock_orthogonal (n : ℕ) (z x : Fin (2 ^ n)) :
    (∑ y : Fin (2 ^ n), hadamardFock n z y * hadamardFock n x y)
      = if z = x then 1 else 0 := by
  have hunit : star (hadamardFock n) * hadamardFock n = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp (hadamardFock_unitary n)
  have hsum : (∑ y : Fin (2 ^ n), hadamardFock n z y * hadamardFock n x y)
      = (star (hadamardFock n) * hadamardFock n) x z := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.star_apply]
    rw [hadamardFock_real n y x]
    rw [hadamardFock_symm n z y]
    rw [hadamardFock_symm n x y]
    ring
  rw [hsum, hunit, Matrix.one_apply]
  by_cases h : x = z
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- The square of the Hadamard normalization prefactor is the corresponding power of one half. -/
theorem hadamardFock_prefactor_sq (n : ℕ) :
    ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n = (2 : ℂ)⁻¹ ^ n := by
  have hsq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
    have h2 : (Real.sqrt 2 : ℂ) ^ 2 = (2 : ℂ) := by
      rw [← Complex.ofReal_pow]
      norm_num [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [inv_pow, h2]
  calc ((Real.sqrt 2 : ℂ)⁻¹) ^ n * ((Real.sqrt 2 : ℂ)⁻¹) ^ n
      = ((Real.sqrt 2 : ℂ)⁻¹) ^ (n + n) := by rw [pow_add]
    _ = ((Real.sqrt 2 : ℂ)⁻¹) ^ (2 * n) := by rw [show n + n = 2 * n by omega]
    _ = (((Real.sqrt 2 : ℂ)⁻¹) ^ 2) ^ n := by rw [← pow_mul]
    _ = (2 : ℂ)⁻¹ ^ n := by rw [hsq]

/-- Each row indexed by `x` of the Fock-mode Hadamard matrix has squared norm one. -/
theorem hadamardFock_column_norm (n : ℕ) (x : Fin (2 ^ n)) :
    (∑ y : Fin (2 ^ n), (star (hadamardFock n x y)) * hadamardFock n x y) = 1 := by
  have hunit : star (hadamardFock n) * hadamardFock n = 1 := by
    exact Matrix.mem_unitaryGroup_iff'.mp (hadamardFock_unitary n)
  have hsum : (∑ y : Fin (2 ^ n), (star (hadamardFock n x y)) * hadamardFock n x y)
      = (star (hadamardFock n) * hadamardFock n) x x := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.star_apply]
    rw [hadamardFock_symm n x y]
  rw [hsum, hunit, Matrix.one_apply]
  simp

/-- A Fock number operator is diagonal with entries equal to the occupation of its mode. -/
theorem fockNumber_apply {N t : ℕ} (x : Fin N) (p q : FockBasis N t) :
    fockNumber N t x p q = if p = q then ((p.1 x : ℕ) : ℂ) else 0 := by
  simp [fockNumber, Matrix.of_apply, Complex.ofReal_natCast]

/-- A list product of Fock number operators is diagonal with entries equal to the corresponding
occupation products. -/
theorem prod_fockNumber_apply {N t : ℕ} :
    ∀ (l : List (Fin N)) (p q : FockBasis N t),
      (l.map (fun x => fockNumber N t x)).prod p q
        = if p = q then (l.map (fun x => ((p.1 x : ℕ) : ℂ))).prod else 0 := by
  intro l
  induction l with
  | nil =>
      intro p q
      by_cases hpq : p = q
      · subst hpq
        simp
      · simp [hpq]
  | cons x l ih =>
      intro p q
      simp only [List.map_cons, List.prod_cons]
      by_cases hpq : p = q
      · subst hpq
        rw [Matrix.mul_apply, Finset.sum_eq_single p]
        · simp [fockNumber_apply, ih]
        · intro k _ hk
          rw [fockNumber_apply]
          have hne : ¬(p = k) := fun h => hk (h ▸ rfl)
          simp [hne]
        · intro h
          exact absurd h (by simp)
      · rw [ite_eq_right hpq, Matrix.mul_apply, Finset.sum_eq_single p]
        · rw [fockNumber_apply]
          simp [ih p q, hpq]
        · intro k _ hk
          rw [fockNumber_apply]
          have hne : ¬(p = k) := fun h => hk (h ▸ rfl)
          simp [hne]
        · intro h
          exact absurd h (by simp)

noncomputable def positionSuccessBlock {N t v : ℕ} (z : Fin v → Fin N) :
    Matrix (FockBasis N t) (FockBasis N t) ℂ :=
  (List.ofFn (fun i => fockNumber N t (z i))).prod

/-- Each diagonal entry of a position success block is the product of the guessed modes'
occupations. -/
theorem positionSuccessBlock_apply {N t v : ℕ} (z : Fin v → Fin N)
    (p : FockBasis N t) :
    positionSuccessBlock z p p = ∏ i, ((p.1 (z i) : ℕ) : ℂ) := by
  have keyM : (List.ofFn z).map (fun x => fockNumber N t x)
      = List.ofFn (fun i => fockNumber N t (z i)) := by
    rw [List.ofFn_eq_map, List.map_map, List.ofFn_eq_map]
    have heq : (fun x => fockNumber N t x) ∘ z = fun i => fockNumber N t (z i) := by
      funext i; rfl
    rw [heq]
  have keyC : (List.ofFn z).map (fun x => ((p.1 x : ℕ) : ℂ))
      = List.ofFn (fun i => ((p.1 (z i) : ℕ) : ℂ)) := by
    rw [List.ofFn_eq_map, List.map_map, List.ofFn_eq_map]
    have heq : (fun x => ((p.1 x : ℕ) : ℂ)) ∘ z = fun i => ((p.1 (z i) : ℕ) : ℂ) := by
      funext i; rfl
    rw [heq]
  have h := prod_fockNumber_apply (N := N) (t := t) (List.ofFn z) p p
  rw [ite_eq_left rfl] at h
  rw [positionSuccessBlock, ← keyM, ← Fin.prod_ofFn, ← keyC]
  exact h

/-- Every off-diagonal entry of a position success block vanishes. -/
theorem positionSuccessBlock_offDiagonal {N t v : ℕ} (z : Fin v → Fin N)
    (p q : FockBasis N t) (h : p ≠ q) :
    positionSuccessBlock z p q = 0 := by
  have keyM : (List.ofFn z).map (fun x => fockNumber N t x)
      = List.ofFn (fun i => fockNumber N t (z i)) := by
    rw [List.ofFn_eq_map, List.map_map, List.ofFn_eq_map]
    have heq : (fun x => fockNumber N t x) ∘ z = fun i => fockNumber N t (z i) := by
      funext i; rfl
    rw [heq]
  have hh := prod_fockNumber_apply (N := N) (t := t) (List.ofFn z) p q
  rw [ite_eq_right h] at hh
  rw [positionSuccessBlock, ← keyM]
  exact hh

/-- A position success block acts by multiplying each amplitude by the corresponding occupation
product. -/
theorem positionSuccessBlock_mulVec {N t v : ℕ} (z : Fin v → Fin N)
    (ψ : FockBasis N t → ℂ) :
    Matrix.mulVec (positionSuccessBlock z) ψ
      = fun p => (∏ i, ((p.1 (z i) : ℕ) : ℂ)) * ψ p := by
  funext p
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single p]
  · rw [positionSuccessBlock_apply]
  · intro q _ hqp
    rw [positionSuccessBlock_offDiagonal z p q (Ne.symm hqp)]
    simp
  · intro h
    exact absurd h (by simp)

/-- The product of two Fock number operators is diagonal with entries equal to the product of
their occupations. -/
theorem fockNumber_mul_apply {N t : ℕ} (x y : Fin N) (p q : FockBasis N t) :
    (fockNumber N t x * fockNumber N t y) p q
      = if p = q then ((p.1 x : ℕ) : ℂ) * ((p.1 y : ℕ) : ℂ) else 0 := by
  rw [Matrix.mul_apply]
  by_cases hpq : p = q
  · rw [Finset.sum_eq_single p]
    · simp [fockNumber_apply]
    · intro k _ hk
      simp [fockNumber_apply, Ne.symm hk]
    · intro h
      exact absurd h (by simp)
  · rw [ite_eq_right hpq, Finset.sum_eq_single p]
    · simp [fockNumber_apply, hpq]
    · intro k _ hk
      simp [fockNumber_apply, Ne.symm hk]
    · intro h
      exact absurd h (by simp)

/-- The position success block for an empty guess list is the identity. -/
theorem positionSuccessBlock_zeroQuery {N t : ℕ} (z : Fin 0 → Fin N) :
    positionSuccessBlock z = (1 : Matrix (FockBasis N t) (FockBasis N t) ℂ) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    rw [positionSuccessBlock_apply]
    simp
  · rw [positionSuccessBlock_offDiagonal z p q hpq]
    simp [hpq]

/-- A position success block for one guess is the number operator of that guessed mode. -/
theorem positionSuccessBlock_oneQuery {N t : ℕ} (z : Fin 1 → Fin N) :
    positionSuccessBlock z = fockNumber N t (z 0) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    rw [positionSuccessBlock_apply, fockNumber_apply, ite_eq_left rfl]
    rw [Fin.prod_univ_succ]
    simp
  · rw [positionSuccessBlock_offDiagonal z p q hpq,
      fockNumber_apply, ite_eq_right hpq]

/-- A position success block for two guesses is the product of their number operators. -/
theorem positionSuccessBlock_twoQuery {N t : ℕ} (z : Fin 2 → Fin N) :
    positionSuccessBlock z = fockNumber N t (z 0) * fockNumber N t (z 1) := by
  ext p q
  by_cases hpq : p = q
  · subst hpq
    rw [positionSuccessBlock_apply, fockNumber_mul_apply, ite_eq_left rfl]
    exact Fin.prod_univ_two (fun i : Fin 2 => ((p.1 (z i) : ℕ) : ℂ))
  · rw [positionSuccessBlock_offDiagonal z p q hpq,
      fockNumber_mul_apply, ite_eq_right hpq]

/-- A two-guess success block has diagonal entries equal to the product of the two guessed
occupations. -/
theorem positionSuccessBlock_twoQuery_apply {N t : ℕ} (z : Fin 2 → Fin N)
    (p : FockBasis N t) :
    positionSuccessBlock z p p = ((p.1 (z 0) : ℕ) : ℂ) * ((p.1 (z 1) : ℕ) : ℂ) := by
  rw [positionSuccessBlock_apply]
  exact Fin.prod_univ_two _

/-- When two guesses coincide, the success block's diagonal entry is the square of that mode's
occupation. -/
theorem positionSuccessBlock_twoQuery_collision {N t : ℕ} (z : Fin 2 → Fin N)
    (p : FockBasis N t) (h : z 0 = z 1) :
    positionSuccessBlock z p p = ((p.1 (z 0) : ℕ) : ℂ) ^ 2 := by
  rw [positionSuccessBlock_twoQuery_apply]
  have hz : ((p.1 (z 1) : ℕ) : ℂ) = ((p.1 (z 0) : ℕ) : ℂ) := by
    simp only [h]
  rw [hz]
  ring

/-- Updating a valued database records the supplied value at the updated index. -/
theorem valuedUpdate_at {I V : Type} [DecidableEq I] (db : ValuedDatabase I V) (x : I) (v : V) :
    valuedUpdate db x v x = some v := by simp [valuedUpdate]

/-- Updating a valued database leaves every other index unchanged. -/
theorem valuedUpdate_ne {I V : Type} [DecidableEq I] (db : ValuedDatabase I V) (x : I) (v : V)
    {y : I} (h : y ≠ x) : valuedUpdate db x v y = db y := by simp [valuedUpdate, h]

/-- A recorded value at an index either duplicates a value elsewhere or satisfies the
new-element condition. -/
theorem duplicateValueQuery_or_newElement {I V : Type} [Fintype I] [DecidableEq I]
    [DecidableEq V] (db : ValuedDatabase I V) (x : I) (v : V) (h : db x = some v) :
    duplicateValueQuery db x v ∨ newElement db x v := by
  by_cases hex : ∃ y : I, y ≠ x ∧ db y = some v
  · exact Or.inl ⟨h, hex⟩
  · refine Or.inr ⟨h, fun y hy hc => hex ⟨y, hy, hc⟩⟩

/-- Updating at a duplicate-value query produces a value collision. -/
theorem valuedUpdate_valueCollision {I V : Type} [Fintype I] [DecidableEq I]
    [DecidableEq V] (db : ValuedDatabase I V) (x : I) (v : V) (h : duplicateValueQuery db x v) :
    valueCollision (valuedUpdate db x v) := by
  obtain ⟨-, y, hy, dbv⟩ := h
  refine ⟨x, y, Ne.symm hy, v, valuedUpdate_at db x v, ?_⟩
  rw [valuedUpdate_ne db x v hy]
  exact dbv

/-- Updating an existing new element with its recorded value preserves the new-element
condition. -/
theorem valuedUpdate_newElement {I V : Type} [Fintype I] [DecidableEq I]
    [DecidableEq V] (db : ValuedDatabase I V) (x : I) (v : V) (h : newElement db x v) :
    newElement (valuedUpdate db x v) x v := by
  refine ⟨valuedUpdate_at db x v, fun y hy => ?_⟩
  rw [valuedUpdate_ne db x v hy]
  exact h.2 y hy

/-- Compressing and then decompressing a Boolean valued database recovers the original database. -/
theorem decompressCompressBlock {N : ℕ} (d : Fin N → Bool) :
    decompressBlock (compressBlock (booleanValuedDatabase d)) = booleanValuedDatabase d := by
  funext x
  by_cases h : d x
  · simp [decompressBlock, compressBlock, booleanValuedDatabase, h]
  · simp [decompressBlock, compressBlock, booleanValuedDatabase, h]

/-- Every mode used by a placement has strictly positive occupation in its profile. -/
theorem placementProfile_newElement {N t : ℕ} (f : Fin t → Fin N) (i : Fin t) :
    (0 : ℕ) < ((placementProfile f).1 (f i) : ℕ) := by
  have hmem : i ∈ (Finset.univ : Finset (Fin t)).filter (fun k => f k = f i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, (rfl : f i = f i)⟩
  have hpos : 0 < ((Finset.univ : Finset (Fin t)).filter (fun k => f k = f i)).card :=
    Finset.card_pos.mpr ⟨i, hmem⟩
  change 0 < fibreCount f (f i)
  exact hpos

/-- A mode hit by two distinct placement indices has occupation at least two. -/
theorem placementProfile_collision {N t : ℕ} (f : Fin t → Fin N) (x : Fin N)
    (h : ∃ i j : Fin t, i ≠ j ∧ f i = x ∧ f j = x) :
    (2 : ℕ) ≤ ((placementProfile f).1 x : ℕ) := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  have h1 : i ∈ (Finset.univ : Finset (Fin t)).filter (fun k => f k = x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have h2 : j ∈ (Finset.univ : Finset (Fin t)).filter (fun k => f k = x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hsub : ({i, j} : Finset (Fin t))
      ⊆ (Finset.univ : Finset (Fin t)).filter (fun k => f k = x) := by
    intro k hk
    rw [Finset.mem_insert] at hk
    rcases hk with hki | hkj
    · subst hki
      exact h1
    · rw [Finset.mem_singleton.mp hkj]
      exact h2
  have hne : i ≠ j := hij
  have hcard : 2 ≤ ((Finset.univ : Finset (Fin t)).filter (fun k => f k = x)).card := by
    calc 2 = ({i, j} : Finset (Fin t)).card := by simp [hne]
      _ ≤ ((Finset.univ : Finset (Fin t)).filter (fun k => f k = x)).card :=
        Finset.card_le_card hsub
  change 2 ≤ fibreCount f x
  exact hcard

/-- An element of a nonempty finite ordinal is nonzero exactly when its natural-number value is
nonzero. -/
lemma fin_succ_ne_zero_iff {m : ℕ} (a : Fin (m + 1)) : a ≠ 0 ↔ (a : ℕ) ≠ 0 := by
  constructor
  · intro h hval
    exact h (Fin.ext hval)
  · intro h hz
    have hval : (a : ℕ) = 0 := by simpa using! congrArg Fin.val hz
    exact h hval

/-- The oracle realized by a placement agrees with the corresponding multiset indicator after
converting indices to bit vectors. -/
theorem realisedOracle_eq_multisetInd {n t : ℕ} (f : Fin t → Fin (2 ^ n)) (x : Fin (2 ^ n)) :
    realisedOracle f x
      = multisetInd (fun i => (bitVecEquiv n).symm (f i)) ((bitVecEquiv n).symm x) := by
  unfold realisedOracle
  have h1 : (0 < fibreCount f x) ↔ ∃ i : Fin t, f i = x := by
    constructor
    · intro h
      have hne : (Finset.univ.filter (fun i => f i = x)).card ≠ 0 :=
        Nat.ne_of_gt h
      obtain ⟨i, hi⟩ := Finset.card_ne_zero.mp hne
      exact ⟨i, (Finset.mem_filter.mp hi).2⟩
    · rintro ⟨i, hi⟩
      have hmem : i ∈ Finset.univ.filter (fun j => f j = x) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      have hpos : 0 < (Finset.univ.filter (fun j => f j = x)).card :=
        Finset.card_pos.mpr ⟨i, hmem⟩
      simpa [fibreCount] using! hpos
  have h2 : (∃ i : Fin t, f i = x)
      ↔ ∃ i : Fin t, (bitVecEquiv n).symm (f i) = (bitVecEquiv n).symm x := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, congrArg (bitVecEquiv n).symm hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by simpa using! congrArg (bitVecEquiv n) hi⟩
  unfold multisetInd
  rw [decide_eq_decide]
  exact h1.trans h2

/-- Multiset success holds exactly when every guessed mode has nonzero occupation in the
placement profile. -/
theorem multisetSuccess_iff_guessesOccupied {N t v : ℕ} (z : Fin v → Fin N)
    (f : Fin t → Fin N) :
    multisetSuccess z f ↔ ∀ i, (placementProfile f).1 (z i) ≠ 0 := by
  constructor
  · intro h i
    have hpos : 0 < fibreCount f (z i) := h i
    have hne : ((placementProfile f).1 (z i) : ℕ) ≠ 0 := by
      have hlt : (0 : ℕ) < ((placementProfile f).1 (z i) : ℕ) := by
        simpa [placementProfile_val] using! hpos
      exact Nat.ne_of_gt hlt
    exact (fin_succ_ne_zero_iff _).mpr hne
  · intro h i
    have hne : ((placementProfile f).1 (z i) : ℕ) ≠ 0 :=
      (fin_succ_ne_zero_iff _).mp (h i)
    have hpos : (0 : ℕ) < ((placementProfile f).1 (z i) : ℕ) := Nat.pos_of_ne_zero hne
    simpa [placementProfile_val] using! hpos

/-- For a positive number of modes, multiset success probability lies between zero and one. -/
theorem multisetSuccessProb_bounds {N t v : ℕ} (z : Fin v → Fin N) (hN : 0 < N) :
    0 ≤ multisetSuccessProb N t v z ∧ multisetSuccessProb N t v z ≤ 1 := by
  have hsum : ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w = 1 :=
    uniformMultisetProb_sum_eq_one N t hN
  have hnonneg : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, 0 ≤ uniformMultisetProb N t w := by
    intro w
    unfold uniformMultisetProb
    positivity
  constructor
  · unfold multisetSuccessProb
    show (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
      (fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)) ≥ 0
    apply Finset.sum_nonneg
    intro w _
    exact mul_nonneg (by split <;> norm_num) (hnonneg w)
  · have hle : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
      ≤ ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w := by
      show (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w))
        ≤ Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => uniformMultisetProb N t w)
      apply Finset.sum_le_sum
        (f := fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
        (g := fun w => uniformMultisetProb N t w)
      intro w _
      by_cases h : ∀ i, (w.1 (z i) : ℕ) ≠ 0
      · simp only [ite_eq_left h, one_mul]
        exact le_refl _
      · simp only [ite_eq_right h, zero_mul]
        exact hnonneg w
    unfold multisetSuccessProb
    exact le_trans hle hsum.le

/-- Multiset success probability is bounded by the uniform multiset expectation of the guessed
occupation product. -/
theorem multisetSuccessProb_le_numberProduct {N t v : ℕ} (z : Fin v → Fin N) :
    multisetSuccessProb N t v z
      ≤ ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          uniformMultisetProb N t w * ((∏ i, (w.1 (z i) : ℕ)) : ℝ) := by
  have hkey : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      ((if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0 : ℝ))
        ≤ ∏ i, ((w.1 (z i) : ℕ) : ℝ) := by
    intro w
    have h := fockGuessesOccupied_le_numberProduct z w
    have hre : (fockGuessesOccupied z w w).re
        = ((if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0 : ℝ)) := by
      by_cases hc : ∀ i, (w.1 (z i) : ℕ) ≠ 0
      · have hc' : ∀ i, w.1 (z i) ≠ 0 := fun i => (fin_succ_ne_zero_iff _).mpr (hc i)
        simp [fockGuessesOccupied, Matrix.of_apply, hc']
      · have hc' : ¬ (∀ i, w.1 (z i) ≠ 0) := by
          intro hh
          exact hc (fun i => (fin_succ_ne_zero_iff _).mp (hh i))
        simp [fockGuessesOccupied, Matrix.of_apply, hc']
    rw [hre] at h
    simpa [fockNumber, Matrix.of_apply, Complex.ofReal_re] using! h
  have hnonneg : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, 0 ≤ uniformMultisetProb N t w := by
    intro w
    unfold uniformMultisetProb
    positivity
  unfold multisetSuccessProb
  show (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
      (fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w))
    ≤ Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
      (fun w => uniformMultisetProb N t w * ((∏ i, (w.1 (z i) : ℕ)) : ℝ))
  apply Finset.sum_le_sum
    (f := fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
    (g := fun w => uniformMultisetProb N t w * ((∏ i, (w.1 (z i) : ℕ)) : ℝ))
  intro w _
  calc (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w
      = uniformMultisetProb N t w
          * (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) := by ring
    _ ≤ uniformMultisetProb N t w * ∏ i, ((w.1 (z i) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (hkey w) (hnonneg w)
    _ = uniformMultisetProb N t w * ((∏ i, (w.1 (z i) : ℕ)) : ℝ) := by
        simp

/-- A placement's fibre count equals the occurrence count in its associated list. -/
theorem fibreCount_eq_listCount {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) :
    fibreCount f x = listCount x (List.ofFn f) := by
  classical
  induction t with
  | zero =>
      simp [fibreCount, listCount]
  | succ t ih =>
      have hsplit : List.ofFn f = f 0 :: List.ofFn (fun i : Fin t => f i.succ) := by
        rw [List.ofFn_succ]
      have hcount : listCount x (List.ofFn f)
          = (if f 0 = x then 1 else 0)
            + listCount x (List.ofFn (fun i : Fin t => f i.succ)) := by
        rw [hsplit]
        rfl
      have hcard1 :
          ((Finset.univ : Finset (Fin (t + 1))).filter (fun i : Fin (t + 1) => f i = x)).card
            = ∑ i : Fin (t + 1), if f i = x then 1 else 0 := by
        rw [Finset.card_eq_sum_ones]
        simp
      have hcard2 :
          ((Finset.univ : Finset (Fin t)).filter (fun i : Fin t => f i.succ = x)).card
            = ∑ i : Fin t, if f i.succ = x then 1 else 0 := by
        rw [Finset.card_eq_sum_ones]
        simp
      have hfib : fibreCount f x
          = (if f 0 = x then 1 else 0)
            + fibreCount (fun i : Fin t => f i.succ) x := by
        simp only [fibreCount]
        rw [hcard1, Fin.sum_univ_succ, hcard2]
      have hih := ih (fun i : Fin t => f i.succ)
      rw [hih] at hfib
      rw [hcount]
      exact hfib

/-- The occupation of the list associated with a placement equals its fibre count. -/
theorem scheduleOccupation_eq_fibreCount {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) :
    scheduleOccupation (List.ofFn f) x = fibreCount f x := by
  rw [scheduleOccupation]
  exact (fibreCount_eq_listCount f x).symm

/-- Placement profiles and the schedule profiles of their associated lists agree at every mode. -/
theorem placementProfile_val_eq_scheduleProfile_val {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) :
    ((placementProfile f).1 x : ℕ) = ((scheduleProfile (List.ofFn f)).1 x : ℕ) := by
  rw [placementProfile_val, scheduleProfile_val]
  exact (scheduleOccupation_eq_fibreCount f x).symm

/-- The placement profile equals the placement's compressed register. -/
theorem placementProfile_eq_placementCompressedRegister {N t : ℕ} (f : Fin t → Fin N) :
    placementProfile f = placementCompressedRegister f := by
  apply Subtype.ext
  funext x
  apply Fin.ext
  rw [placementProfile_val, placementCompressedRegister_val]
  exact (scheduleOccupation_eq_fibreCount f x).symm

/-- The compressed register of a schedule viewed as an indexed placement equals its schedule
profile. -/
theorem placementCompressedRegister_eq_scheduleProfile {N : ℕ} (sch : QuerySchedule N) :
    placementCompressedRegister (fun i : Fin sch.length => sch.get i) = scheduleProfile sch := by
  apply Subtype.ext
  funext x
  apply Fin.ext
  have hlist : List.ofFn (fun i : Fin sch.length => sch.get i) = sch := List.ofFn_get sch
  simp only [placementCompressedRegister, scheduleProfile]
  rw [hlist]

/-- A schedule's Fock register state has amplitude one at its own profile. -/
theorem fockRegisterState_apply_scheduleProfile {N : ℕ} (sch : QuerySchedule N) :
    fockRegisterState sch (scheduleProfile sch) = 1 := by
  simp [fockRegisterState]

/-- A schedule's Fock register state vanishes at every profile different from its own. -/
theorem fockRegisterState_apply_of_ne {N : ℕ} (sch : QuerySchedule N)
    (v : FockBasis N sch.length) (hv : v ≠ scheduleProfile sch) :
    fockRegisterState sch v = 0 := by
  simp [fockRegisterState, hv]

/-- The total occupation of a schedule profile equals the schedule length. -/
theorem scheduleProfile_total_eq_length {N : ℕ} (sch : QuerySchedule N) :
    (∑ x : Fin N, ((scheduleProfile sch).1 x : ℕ)) = sch.length := by
  show (Finset.sum (Finset.univ : Finset (Fin N))
      (fun x => ((scheduleProfile sch).1 x : ℕ))) = sch.length
  calc (Finset.sum (Finset.univ : Finset (Fin N))
        (fun x => ((scheduleProfile sch).1 x : ℕ)))
      = Finset.sum (Finset.univ : Finset (Fin N))
        (fun x => scheduleOccupation sch x) := by
          refine Finset.sum_congr rfl (fun x _ => scheduleProfile_val sch x)
    _ = sch.length := scheduleOccupation_total sch

/-- At a schedule's profile, the compressed joint state formed with its Fock register state has
the original query amplitude. -/
theorem compressedJointState_fockRegisterState_apply {I W : Type} [Fintype I]
    [DecidableEq I] [Fintype W] [DecidableEq W] {N : ℕ} (sch : QuerySchedule N)
    (ψ : QState (((I × Bool) × W) × (I → Bool)))
    (q : ((I × Bool) × W) × (I → Bool)) :
    compressedJointState (fockRegisterState sch) ψ (scheduleProfile sch, q) = ψ q := by
  simp [compressedJointState, fockRegisterState]

/-- The avoidance weight is the product of the complement indicator raised to each mode's
occupation. -/
theorem avoidWeight_eq_prod {N : ℕ} (T : Finset (Fin N)) (k : Fin N → ℕ) :
    avoidWeight T (fun x => k x)
      = ∏ i ∈ (Finset.univ : Finset (Fin N)),
          (if i ∈ T then (0 : ℝ) else 1) ^ (k i) := by
  classical
  have hsplit :
      (∏ i ∈ (Finset.univ : Finset (Fin N)),
          (if i ∈ T then (0 : ℝ) else 1) ^ (k i))
        = (∏ i ∈ (Finset.univ : Finset (Fin N)) \ T,
            (if i ∈ T then (0 : ℝ) else 1) ^ (k i))
          * (∏ i ∈ T, (if i ∈ T then (0 : ℝ) else 1) ^ (k i)) := by
    symm
    exact Finset.prod_sdiff (Finset.subset_univ T)
  rw [hsplit]
  have hout : (∏ i ∈ (Finset.univ : Finset (Fin N)) \ T,
      (if i ∈ T then (0 : ℝ) else 1) ^ (k i)) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    have hi' : i ∉ T := (Finset.mem_sdiff.mp hi).2
    simp [hi']
  rw [hout, one_mul]
  have hin : (∏ i ∈ T, (if i ∈ T then (0 : ℝ) else 1) ^ (k i))
      = ∏ i ∈ T, (if k i = 0 then 1 else 0) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [ite_eq_left hi]
    by_cases hk : k i = 0
    · rw [hk, pow_zero, ite_eq_left rfl]
    · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk
      rw [hm]
      simp
  rw [hin]
  by_cases h : ∀ x ∈ T, k x = 0
  · have h1 : (∏ i ∈ T, (if k i = 0 then 1 else 0) : ℝ) = 1 := by
      have h2 : (∏ i ∈ T, (if k i = 0 then 1 else 0) : ℝ) = ∏ i ∈ T, (1 : ℝ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        simp [h i hi]
      rw [h2]
      simp
    rw [h1]
    unfold avoidWeight
    rw [ite_eq_left h]
  · have hex : ∃ i ∈ T, k i ≠ 0 := by
      by_contra hcon
      refine h ?_
      intro x hx
      by_contra hxk
      exact hcon ⟨x, hx, hxk⟩
    obtain ⟨i, hi, hki⟩ := hex
    have hz : (∏ j ∈ T, (if k j = 0 then 1 else 0) : ℝ) = 0 := by
      rw [Finset.prod_eq_zero_iff]
      exact ⟨i, hi, by simp [hki]⟩
    rw [hz]
    unfold avoidWeight
    rw [ite_eq_right h]

/-- The avoidance-weighted multinomial sum agrees when indexed by the finite antidiagonal or by
occupation profiles. -/
theorem sum_multinomial_piAntidiag_avoid {N : ℕ} (t : ℕ) (T : Finset (Fin N)) :
    (Finset.sum (Finset.piAntidiag (Finset.univ : Finset (Fin N)) t)
        (fun k => (Nat.multinomial (Finset.univ : Finset (Fin N)) k : ℝ)
          * avoidWeight T (fun x => k x)))
      = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
        (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
            (fun x => (v.1 x : ℕ)) : ℝ)
          * avoidWeight T (fun x => (v.1 x : ℕ))) := by
  classical
  refine Finset.sum_bij
    (fun k (hk : k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin N)) t) =>
      profileOf k (Finset.mem_piAntidiag.mp hk).1) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_univ _
  · intro k₁ hk₁ k₂ hk₂ heq
    have hval : (profileOf k₁ (Finset.mem_piAntidiag.mp hk₁).1).1
        = (profileOf k₂ (Finset.mem_piAntidiag.mp hk₂).1).1 := congrArg Subtype.val heq
    funext x
    exact congrArg Fin.val (congrFun hval x)
  · intro v hv
    refine ⟨fun x => (v.1 x : ℕ), ?_⟩
    refine ⟨?_, ?_⟩
    · refine Finset.mem_piAntidiag.mpr ⟨?_, ?_⟩
      · exact v.property
      · intro x hx
        exact Finset.mem_univ x
    · have hprof : profileOf (fun x => (v.1 x : ℕ)) v.property = v := by
        apply Subtype.ext
        funext x
        apply Fin.ext
        simp [profileOf]
      exact hprof
  · intro k hk
    have hval : (fun x => ((profileOf k (Finset.mem_piAntidiag.mp hk).1).1 x : ℕ))
        = (fun x => k x) := by
      funext x
      simp [profileOf]
    rw [hval]

/-- The avoidance-weighted multinomial sum is the number of allowed modes raised to the total
occupation. -/
theorem sum_multinomial_avoid {N : ℕ} (t : ℕ) (T : Finset (Fin N)) :
    (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
        (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
            (fun x => (v.1 x : ℕ)) : ℝ)
          * avoidWeight T (fun x => (v.1 x : ℕ))))
      = (((Finset.univ : Finset (Fin N)) \ T).card : ℝ) ^ t := by
  classical
  calc (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
        (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
            (fun x => (v.1 x : ℕ)) : ℝ)
          * avoidWeight T (fun x => (v.1 x : ℕ))))
      = Finset.sum (Finset.piAntidiag (Finset.univ : Finset (Fin N)) t)
          (fun k => (Nat.multinomial (Finset.univ : Finset (Fin N)) k : ℝ)
            * avoidWeight T (fun x => k x)) :=
        (sum_multinomial_piAntidiag_avoid (N := N) t T).symm
    _ = Finset.sum (Finset.piAntidiag (Finset.univ : Finset (Fin N)) t)
          (fun k => (Nat.multinomial (Finset.univ : Finset (Fin N)) k : ℝ)
            * ∏ i ∈ (Finset.univ : Finset (Fin N)),
                (if i ∈ T then (0 : ℝ) else 1) ^ (k i)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        exact congrArg (fun z => (Nat.multinomial (Finset.univ : Finset (Fin N)) k : ℝ) * z)
          (avoidWeight_eq_prod T k)
    _ = (∑ i ∈ (Finset.univ : Finset (Fin N)), (if i ∈ T then (0 : ℝ) else 1)) ^ t := by
        symm
        exact Finset.sum_pow_eq_sum_piAntidiag (s := (Finset.univ : Finset (Fin N)))
          (f := fun x : Fin N => if x ∈ T then (0 : ℝ) else 1) t
    _ = (((Finset.univ : Finset (Fin N)) \ T).card : ℝ) ^ t := by
      have hcard : (∑ i ∈ (Finset.univ : Finset (Fin N)),
            (if i ∈ T then (0 : ℝ) else 1))
          = ((Finset.univ : Finset (Fin N)) \ T).card := by
        have h1 : (∑ i ∈ (Finset.univ : Finset (Fin N)),
            (if i ∈ T then (0 : ℝ) else 1))
            = ∑ i ∈ (Finset.univ : Finset (Fin N)),
                (if i ∉ T then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i ∈ T
          · simp [hi]
          · simp [hi]
        rw [h1, ← Finset.sum_filter]
        have hfilter : (Finset.univ : Finset (Fin N)).filter (fun i => i ∉ T)
            = (Finset.univ : Finset (Fin N)) \ T := by
          ext x
          simp
        rw [hfilter]
        rw [Finset.card_eq_sum_ones]
        norm_cast
      rw [hcard]

/-- Multiset avoidance probability is the fraction of allowed modes raised to the number of
placements. -/
theorem multisetAvoidProb_eq {N : ℕ} (t : ℕ) (T : Finset (Fin N)) :
    multisetAvoidProb N t T
      = ((((Finset.univ : Finset (Fin N)) \ T).card : ℝ) / (N : ℝ)) ^ t := by
  classical
  have hmul : ∀ v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      uniformMultisetProb N t v
        = ((Nat.multinomial (Finset.univ : Finset (Fin N))
            (fun x => (v.1 x : ℕ)) : ℝ)) * ((N : ℝ) ^ t)⁻¹ := by
    intro v
    simp [uniformMultisetProb, div_eq_mul_inv]
  calc multisetAvoidProb N t T
      = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun v => ((Nat.multinomial (Finset.univ : Finset (Fin N))
                (fun x => (v.1 x : ℕ)) : ℝ)
            * avoidWeight T (fun x => (v.1 x : ℕ))) * ((N : ℝ) ^ t)⁻¹) := by
        unfold multisetAvoidProb
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [hmul]
        ring
    _ = (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
                (fun x => (v.1 x : ℕ)) : ℝ)
            * avoidWeight T (fun x => (v.1 x : ℕ)))) * ((N : ℝ) ^ t)⁻¹ := by
        have hfactor :
            (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
              (fun v => ((Nat.multinomial (Finset.univ : Finset (Fin N))
                    (fun x => (v.1 x : ℕ)) : ℝ)
                * avoidWeight T (fun x => (v.1 x : ℕ))) * ((N : ℝ) ^ t)⁻¹))
            = (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
              (fun v => (Nat.multinomial (Finset.univ : Finset (Fin N))
                    (fun x => (v.1 x : ℕ)) : ℝ)
                * avoidWeight T (fun x => (v.1 x : ℕ)))) * ((N : ℝ) ^ t)⁻¹ := by
          induction (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
            using Finset.induction_on with
          | empty => simp
          | @insert a s ha ih =>
              simp only [Finset.sum_insert ha]
              rw [ih]
              ring
        exact hfactor
    _ = (((Finset.univ : Finset (Fin N)) \ T).card : ℝ) ^ t * ((N : ℝ) ^ t)⁻¹ := by
        rw [sum_multinomial_avoid (N := N) t T]
    _ = ((((Finset.univ : Finset (Fin N)) \ T).card : ℝ) / (N : ℝ)) ^ t := by
      rw [← inv_pow, ← mul_pow]
      apply congrArg (fun z : ℝ => z ^ t)
      rw [div_eq_mul_inv]

/-- Multiset avoidance probability is the power of the ratio of the total modes minus the
forbidden modes to the total modes. -/
theorem multisetAvoidProb_eq_sub {N : ℕ} (t : ℕ) (T : Finset (Fin N)) :
    multisetAvoidProb N t T = (((N : ℝ) - (T.card : ℝ)) / (N : ℝ)) ^ t := by
  rw [multisetAvoidProb_eq]
  have hinter : T ∩ (Finset.univ : Finset (Fin N)) = T := by
    ext x
    simp
  have hle : T.card ≤ N := by
    have hsub : T ⊆ (Finset.univ : Finset (Fin N)) := Finset.subset_univ T
    have := Finset.card_le_card hsub
    simpa [Fintype.card_fin] using! this
  have hcardNat : ((Finset.univ : Finset (Fin N)) \ T).card = N - T.card := by
    rw [Finset.card_sdiff, hinter]
    simp [Fintype.card_fin]
  have hcard : ((Finset.univ : Finset (Fin N)) \ T).card
      = (N : ℝ) - (T.card : ℝ) := by
    rw [hcardNat, Nat.cast_sub hle]
  rw [hcard]

/-- Hadamard-weighting and summing momentum creation entries recovers the ordinary creation
entry. -/
theorem sum_momentumCreation_eq_create (n ℓ : ℕ) (x : Fin (2 ^ n))
    (r : MomentumFock n (ℓ + 1)) (s : MomentumFock n ℓ) :
    (∑ y, hadamardFock n y x * (momentumCreation n ℓ y r s))
      = Qatlib.Concepts.BosonFock.BosonOperators.create (2 ^ n) ℓ x r s := by
  classical
  set c : Fin (2 ^ n) → ℂ := fun w =>
    if ∀ j, (r.val j : ℕ) = (s.val j : ℕ) + if j = w then 1 else 0
      then (Real.sqrt ((s.val w : ℕ) + 1) : ℂ) else 0 with hc
  have horth : ∀ w : Fin (2 ^ n),
      (∑ y, hadamardFock n y x * hadamardFock n w y : ℂ)
        = if w = x then 1 else 0 := by
    intro w
    have h := hadamardFock_orthogonal n x w
    have heq : (∑ y, hadamardFock n y x * hadamardFock n w y : ℂ)
        = ∑ y, hadamardFock n x y * hadamardFock n w y := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hadamardFock_symm n y x]
    rw [heq, h]
    by_cases hxw : x = w
    · rw [ite_eq_left hxw, ite_eq_left hxw.symm]
    · rw [ite_eq_right hxw, ite_eq_right (Ne.symm hxw)]
  have hmc : ∀ y : Fin (2 ^ n),
      momentumCreation n ℓ y r s = ∑ w, hadamardFock n w y * c w := by
    intro y
    rw [momentumCreation_apply]
  calc (∑ y, hadamardFock n y x * (momentumCreation n ℓ y r s))
      = ∑ y, ∑ w, (hadamardFock n y x * hadamardFock n w y) * c w := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hmc y]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
    _ = ∑ w, (∑ y, hadamardFock n y x * hadamardFock n w y) * c w := by
        rw [Finset.sum_comm (f := fun y w =>
          (hadamardFock n y x * hadamardFock n w y) * c w)]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_mul]
    _ = ∑ w, (if w = x then 1 else 0) * c w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [horth]
    _ = c x := by
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb
          rw [ite_eq_right hb]
          simp
        · intro h
          exact absurd h (by simp)
    _ = Qatlib.Concepts.BosonFock.BosonOperators.create (2 ^ n) ℓ x r s := by
      rw [hc]
      rfl

/-- The product of guessed occupations is at most the total occupation raised to the number of
guesses. -/
theorem positionSuccessBlock_apply_le {N t v : ℕ} (z : Fin v → Fin N)
    (p : FockBasis N t) :
    ∏ i, (((p.1 (z i) : ℕ) : ℕ) : ℝ) ≤ (t : ℝ) ^ v := by
  have hocc : ∀ x : Fin N, (p.1 x : ℕ) ≤ t := by
    intro x
    have h1 := Finset.single_le_sum (f := fun i => (p.1 i : ℕ))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have h2 : (p.1 x : ℕ) ≤ ∑ x : Fin N, (p.1 x : ℕ) := h1
    rw [p.property] at h2
    exact h2
  have hnonneg : ∀ i : Fin v, (0 : ℝ) ≤ (((p.1 (z i) : ℕ) : ℕ) : ℝ) := by
    intro i
    positivity
  have hle : ∀ i : Fin v, (((p.1 (z i) : ℕ) : ℕ) : ℝ) ≤ (t : ℝ) := by
    intro i
    exact_mod_cast hocc (z i)
  have hprod : (∏ i : Fin v, (((p.1 (z i) : ℕ) : ℕ) : ℝ))
      ≤ ∏ _i : Fin v, (t : ℝ) := by
    refine Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => hle i)
  have hconst : (∏ _i : Fin v, (t : ℝ)) = (t : ℝ) ^ v := by
    simp
  rw [← hconst]
  exact hprod

/-- The product of one minus each value over a finite set expands as an alternating sum of
products over its subsets. -/
theorem sum_powerset_expand_aux {ι : Type} [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) :
    (∏ i ∈ S, (1 - x i))
      = ∑ J ∈ S.powerset, ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hsplit :
          (∑ J ∈ (insert a s).powerset, ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j))
            = (∑ J ∈ s.powerset, ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j))
              + (∑ J ∈ s.powerset,
                  ((-1 : ℝ) ^ (insert a J).card) * (∏ j ∈ insert a J, x j)) :=
        Finset.sum_powerset_insert (α := ι) (β := ℝ) ha
          (f := fun J : Finset ι => ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j))
      have hsecond :
          (∑ J ∈ s.powerset, ((-1 : ℝ) ^ (insert a J).card) * (∏ j ∈ insert a J, x j))
            = -(x a) * (∑ J ∈ s.powerset, ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j)) := by
        have hcong :
            (∑ J ∈ s.powerset, ((-1 : ℝ) ^ (insert a J).card) * (∏ j ∈ insert a J, x j))
              = ∑ J ∈ s.powerset,
                  (-(x a)) * (((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j)) := by
          refine Finset.sum_congr
            (f := fun J : Finset ι =>
              ((-1 : ℝ) ^ (insert a J).card) * (∏ j ∈ insert a J, x j))
            (g := fun J : Finset ι =>
              (-(x a)) * (((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j)))
            rfl (fun J hJ => ?_)
          have hJ' : J ⊆ s := (Finset.mem_powerset.mp hJ)
          have haJ : a ∉ J := fun h => ha (hJ' h)
          have hcard : (insert a J).card = J.card + 1 := Finset.card_insert_of_notMem haJ
          have hprod : (∏ j ∈ insert a J, x j) = x a * (∏ j ∈ J, x j) :=
            Finset.prod_insert haJ
          rw [hcard, hprod]
          ring
        rw [hcong, Finset.mul_sum]
      rw [Finset.prod_insert ha, hsplit, hsecond, ← ih]
      ring

/-- The product of one minus each value over a finite type expands as an alternating sum over
all subsets. -/
theorem sum_powerset_expand {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    (∏ i ∈ (Finset.univ : Finset ι), (1 - x i))
      = ∑ J ∈ (Finset.univ : Finset ι).powerset,
          ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, x j) := by
  classical
  exact sum_powerset_expand_aux (S := (Finset.univ : Finset ι)) x

/-- The product of occupation indicators is the indicator that all guessed modes are occupied. -/
theorem occupiedIndicator_eq_prod {N t v : ℕ} (z : Fin v → Fin N)
    (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    (∏ i ∈ (Finset.univ : Finset (Fin v)), (if (w.1 (z i) : ℕ) ≠ 0 then (1 : ℝ) else 0))
      = if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then (1 : ℝ) else 0 := by
  by_cases h : ∀ i, (w.1 (z i) : ℕ) ≠ 0
  · rw [ite_eq_left h]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [ite_eq_left (h i)]
  · rw [ite_eq_right h]
    have hex : ∃ i : Fin v, (w.1 (z i) : ℕ) = 0 := by
      by_contra hcon
      apply h
      intro i
      by_contra hi
      exact hcon ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hi]

/-- The product of emptiness indicators over selected guesses equals the avoidance weight of
their image. -/
theorem avoidIndicator_eq_prod {N t v : ℕ} (z : Fin v → Fin N)
    (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) (J : Finset (Fin v)) :
    (∏ j ∈ J, (if (w.1 (z j) : ℕ) = 0 then (1 : ℝ) else 0))
      = avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)) := by
  show (∏ j ∈ J, (if (w.1 (z j) : ℕ) = 0 then (1 : ℝ) else 0))
    = (if ∀ x ∈ Finset.image z J, (w.1 x : ℕ) = 0 then (1 : ℝ) else 0)
  by_cases h : ∀ x ∈ Finset.image z J, (w.1 x : ℕ) = 0
  · rw [ite_eq_left h]
    refine Finset.prod_eq_one fun j hj => ?_
    rw [ite_eq_left (h (z j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩))]
  · rw [ite_eq_right h]
    have hex : ∃ j ∈ J, (w.1 (z j) : ℕ) ≠ 0 := by
      by_contra hcon
      apply h
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      by_contra hxj
      exact hcon ⟨j, hj, hxj⟩
    obtain ⟨j, hj, hne⟩ := hex
    refine Finset.prod_eq_zero hj ?_
    simp [hne]

/-- The indicator that every guessed mode is occupied has an inclusion-exclusion expansion in
avoidance weights. -/
theorem successIndicator_eq_inclusionExclusion {N t v : ℕ} (z : Fin v → Fin N)
    (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0)
      = ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
          ((-1 : ℝ) ^ J.card) * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)) := by
  let miss : Fin v → ℝ := fun i => if (w.1 (z i) : ℕ) = 0 then 1 else 0
  have hmiss : ∀ i : Fin v, miss i = (if (w.1 (z i) : ℕ) = 0 then 1 else 0) := fun _ => rfl
  have hexp := sum_powerset_expand (ι := Fin v) miss
  have hone : ∀ i : Fin v,
      (1 - miss i) = (if (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) := by
    intro i
    by_cases hc : (w.1 (z i) : ℕ) = 0
    · have h1 : miss i = 1 := by rw [hmiss i]; rw [ite_eq_left hc]
      simp [h1, hc]
    · have h1 : miss i = 0 := by rw [hmiss i]; rw [ite_eq_right hc]
      simp [h1, hc]
  have hprod : ∀ J : Finset (Fin v),
      (∏ j ∈ J, miss j) = avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)) := by
    intro J
    refine avoidIndicator_eq_prod z w J
  calc (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0)
      = (∏ i ∈ (Finset.univ : Finset (Fin v)),
          (if (w.1 (z i) : ℕ) ≠ 0 then (1 : ℝ) else 0)) := by
        symm
        exact occupiedIndicator_eq_prod z w
    _ = (∏ i ∈ (Finset.univ : Finset (Fin v)), (1 - miss i)) := by
        refine Finset.prod_congr
          (f := fun i : Fin v => (if (w.1 (z i) : ℕ) ≠ 0 then (1 : ℝ) else 0))
          (g := fun i : Fin v => 1 - miss i)
          rfl (fun i _ => (hone i).symm)
    _ = (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
          ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, miss j)) := hexp
    _ = (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
          ((-1 : ℝ) ^ J.card) * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))) := by
        refine Finset.sum_congr
          (f := fun J : Finset (Fin v) => ((-1 : ℝ) ^ J.card) * (∏ j ∈ J, miss j))
          (g := fun J : Finset (Fin v) =>
            ((-1 : ℝ) ^ J.card) * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
          rfl (fun J _ => congrArg (fun u => ((-1 : ℝ) ^ J.card) * u) (hprod J))

end Qatlib.Papers.QMAvsQCMA25.Forrelation

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- Multiset success probability is the alternating sum of the expected avoidance weights over
subsets of guesses. -/
theorem multisetSuccessProb_eq_inclusionExclusion {N t v : ℕ} (z : Fin v → Fin N) :
    multisetSuccessProb N t v z
      = ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
          ((-1 : ℝ) ^ J.card)
            * (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
                avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
                  * uniformMultisetProb N t w) := by
  unfold multisetSuccessProb
  show (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
      (fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w))
    = ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
        ((-1 : ℝ) ^ J.card)
          * (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
              (fun w => avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
                * uniformMultisetProb N t w))
  have hstep1 :
      (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w))
        = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
              ((-1 : ℝ) ^ J.card)
                * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w) := by
      refine Finset.sum_congr
        (f := fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
          (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
        (g := fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
          (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
              ((-1 : ℝ) ^ J.card)
                * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w)
        rfl (fun w _ => ?_)
      rw [successIndicator_eq_inclusionExclusion z w]
  rw [hstep1]
  have hstep2 :
      (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
              ((-1 : ℝ) ^ J.card)
                * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w))
        = Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
            (((-1 : ℝ) ^ J.card)
              * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w) := by
      refine Finset.sum_congr
        (f := fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
          (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
              ((-1 : ℝ) ^ J.card)
                * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w)
        (g := fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
          ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
            (((-1 : ℝ) ^ J.card)
              * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w)
        rfl (fun w _ => ?_)
      rw [Finset.sum_mul]
  rw [hstep2]
  have hstep3 :
      (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
          (fun w => ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
            (((-1 : ℝ) ^ J.card)
              * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w))
        = Finset.sum (Finset.univ : Finset (Fin v)).powerset
          (fun J => ((-1 : ℝ) ^ J.card)
            * (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
                (fun w => avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
                  * uniformMultisetProb N t w))) := by
      rw [Finset.sum_comm (f := fun w J =>
        (((-1 : ℝ) ^ J.card)
          * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
        * uniformMultisetProb N t w)]
      refine Finset.sum_congr
        (f := fun J : Finset (Fin v) =>
          ∑ w ∈ (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t)),
            (((-1 : ℝ) ^ J.card)
              * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
            * uniformMultisetProb N t w)
        (g := fun J : Finset (Fin v) => ((-1 : ℝ) ^ J.card)
            * (Finset.sum (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t))
                (fun w => avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
                  * uniformMultisetProb N t w)))
        rfl (fun J _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr
        (f := fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
          (((-1 : ℝ) ^ J.card)
            * avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ)))
          * uniformMultisetProb N t w)
        (g := fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t => ((-1 : ℝ) ^ J.card)
            * (avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
              * uniformMultisetProb N t w))
        rfl (fun w _ => ?_)
      simp only [mul_assoc]
  rw [hstep3]

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- Multiset success probability has a closed inclusion-exclusion formula using the
cardinalities of images of guess subsets. -/
theorem multisetSuccessProb_eq_inclusionExclusion_closed {N t v : ℕ}
    (z : Fin v → Fin N) :
    multisetSuccessProb N t v z
      = ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
          ((-1 : ℝ) ^ J.card)
            * ((((N : ℝ) - ((Finset.image z J).card : ℝ)) / (N : ℝ)) ^ t) := by
  have h := multisetSuccessProb_eq_inclusionExclusion (N := N) (t := t) (v := v) z
  rw [h]
  refine Finset.sum_congr
    (f := fun J : Finset (Fin v) => ((-1 : ℝ) ^ J.card)
      * (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
            * uniformMultisetProb N t w))
    (g := fun J : Finset (Fin v) => ((-1 : ℝ) ^ J.card)
      * ((((N : ℝ) - ((Finset.image z J).card : ℝ)) / (N : ℝ)) ^ t))
    rfl (fun J _ => ?_)
  have hsum : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        avoidWeight (Finset.image z J) (fun x => (w.1 x : ℕ))
          * uniformMultisetProb N t w)
      = multisetAvoidProb N t (Finset.image z J) := rfl
  rw [hsum, multisetAvoidProb_eq_sub]

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- For one guessed mode, success probability is one minus the probability that every placement
avoids that mode. -/
theorem multisetSuccessProb_oneQuery_eq {N t : ℕ} (hN : 0 < N) (x : Fin N) :
    multisetSuccessProb N t 1 (fun _ => x) = 1 - ((((N : ℝ) - 1) / (N : ℝ)) ^ t) := by
  rw [multisetSuccessProb_eq_inclusionExclusion_closed]
  rw [show (Finset.univ : Finset (Fin 1)).powerset = ({∅, {0}} : Finset (Finset (Fin 1))) by
    decide]
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp [Finset.sum_insert, hNne]
  ring

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- An element has occurrence count zero exactly when it is absent from the list. -/
theorem listCount_eq_zero_iff {α : Type} [DecidableEq α] (x : α) (l : List α) :
    listCount x l = 0 ↔ x ∉ l := by
  induction l with
  | nil => simp [listCount]
  | cons a l ih =>
      by_cases ha : a = x
      · subst ha
        simp [listCount]
      · simp only [listCount, ite_eq_right ha, zero_add]
        constructor
        · intro h hmem
          simp only [List.mem_cons] at hmem
          rcases hmem with h1 | h2
          · exact ha h1.symm
          · exact absurd h2 (ih.mp h)
        · intro h
          exact ih.mpr (fun hmem => h (by simp [hmem]))

/-- An element has positive occurrence count exactly when it belongs to the list. -/
theorem listCount_pos_iff_mem {α : Type} [DecidableEq α] (x : α) (l : List α) :
    0 < listCount x l ↔ x ∈ l := by
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro h
    by_contra hn
    exact h ((listCount_eq_zero_iff x l).mpr hn)
  · intro h hz
    exact absurd h ((listCount_eq_zero_iff x l).mp hz)

/-- Decompressing a placement's compressed register gives the query record of its associated
list. -/
theorem decompressBlock_placementCompressedRegister {N t : ℕ} (f : Fin t → Fin N) :
    decompressBlock (placementCompressedRegister f) = queryRecord (List.ofFn f) := by
  funext x
  simp only [decompressBlock, booleanValuedDatabase, queryRecord]
  by_cases hx : x ∈ List.ofFn f
  · have hpos : 0 < ((placementCompressedRegister f).1 x : ℕ) := by
      rw [placementCompressedRegister_val, scheduleOccupation_eq_fibreCount,
        fibreCount_eq_listCount]
      exact (listCount_pos_iff_mem x (List.ofFn f)).mpr hx
    simp [hx, hpos]
  · have hzero : ((placementCompressedRegister f).1 x : ℕ) = 0 := by
      rw [placementCompressedRegister_val, scheduleOccupation_eq_fibreCount,
        fibreCount_eq_listCount]
      exact (listCount_eq_zero_iff x (List.ofFn f)).mpr hx
    simp [hx, hzero]

/-- Recording a query in a list's query record gives the query record of the list with that
query appended. -/
theorem recordQuery_queryRecord_append {N : ℕ} (l : List (Fin N)) (x : Fin N) :
    recordQuery (queryRecord l) x = queryRecord (l ++ [x]) := by
  funext y
  by_cases hy : y = x
  · rw [hy]
    simp [recordQuery, queryRecord, valuedUpdate]
  · simp [recordQuery, queryRecord, valuedUpdate, hy]

/-- Appending a query updates register occupation by Fock creation at the queried mode. -/
theorem compressedRegister_append_eq_creation {N : ℕ} (l : List (Fin N)) (x y : Fin N) :
    registerOccupation (l ++ [x]) y = fockCreation x (registerOccupation l) y := by
  have hval := scheduleProfile_append_val l x y
  have hsch := scheduleProfile_val l y
  by_cases hy : y = x
  · rw [hy] at hval hsch ⊢
    have hcr := (fockCreation_occupation x (registerOccupation l)).1
    simp only [registerOccupation] at hcr ⊢
    rw [hval, hcr, ← hsch]
    simp
  · have hcr := (fockCreation_occupation x (registerOccupation l)).2 y hy
    simp only [registerOccupation] at hcr ⊢
    rw [hval, hcr, ← hsch]
    simp [hy]

/-- A schedule's register occupation is zero at a mode exactly when the mode is absent from the
schedule. -/
theorem registerOccupation_eq_zero_iff {N : ℕ} (sch : QuerySchedule N) (x : Fin N) :
    registerOccupation sch x = 0 ↔ x ∉ sch := by
  rw [registerOccupation, scheduleProfile_val, scheduleOccupation]
  exact listCount_eq_zero_iff x sch

/-- A schedule's register occupation is positive at a mode exactly when the mode belongs to the
schedule. -/
theorem registerOccupation_pos_iff_mem {N : ℕ} (sch : QuerySchedule N) (x : Fin N) :
    0 < registerOccupation sch x ↔ x ∈ sch := by
  rw [registerOccupation, scheduleProfile_val, scheduleOccupation]
  exact listCount_pos_iff_mem x sch

/-- Appending a mode already present in a schedule makes its occupation at least two. -/
theorem registerOccupation_append_collision {N : ℕ} (l : List (Fin N)) (x : Fin N)
    (hx : x ∈ l) :
    2 ≤ registerOccupation (l ++ [x]) x := by
  have hpos : 0 < registerOccupation l x :=
    (registerOccupation_pos_iff_mem l x).mpr hx
  have hval : registerOccupation (l ++ [x]) x = registerOccupation l x + 1 := by
    rw [compressedRegister_append_eq_creation]
    exact (fockCreation_occupation x (registerOccupation l)).1
  omega

/-- A placement's query record stores true at a mode exactly when its realized oracle returns
true there. -/
theorem queryRecord_eq_realisedOracle {n t : ℕ} (f : Fin t → Fin (2 ^ n)) (x : Fin (2 ^ n)) :
    queryRecord (List.ofFn f) x = some true ↔ realisedOracle f x = true := by
  have hmem : (x ∈ List.ofFn f) ↔ (0 < fibreCount f x) := by
    have h1 : (0 < fibreCount f x) ↔ (0 < scheduleOccupation (List.ofFn f) x) := by
      rw [scheduleOccupation_eq_fibreCount]
    have h2 : (0 < scheduleOccupation (List.ofFn f) x) ↔ (x ∈ List.ofFn f) := by
      rw [scheduleOccupation]
      exact listCount_pos_iff_mem x (List.ofFn f)
    exact h2.symm.trans h1.symm
  rw [queryRecord, realisedOracle]
  simp only [decide_eq_true_eq]
  by_cases hx : x ∈ List.ofFn f
  · simp [hx, hmem.mp hx]
  · have hnot : ¬(0 < fibreCount f x) := fun h => hx (hmem.mpr h)
    simp [hx, hnot]

/-- Every schedule's Fock register state has squared norm one. -/
theorem compressedRegisterState_normalized {N : ℕ} (sch : QuerySchedule N) :
    ∑ v, ‖fockRegisterState sch v‖ ^ 2 = 1 :=
  fockRegisterState_norm_sq sch

/-- A compressed joint state formed from two states of squared norm one also has squared norm
one. -/
theorem compressedJointState_normalized {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {N t : ℕ} (reg : FockBasis N t → ℂ)
    (ψ : QState (((I × Bool) × W) × (I → Bool)))
    (hreg : ∑ v, ‖reg v‖ ^ 2 = 1) (hψ : ∑ q, ‖ψ q‖ ^ 2 = 1) :
    ∑ q, ‖compressedJointState reg ψ q‖ ^ 2 = 1 := by
  have h := compressedJointState_norm_sq reg ψ
  rw [hreg, hψ] at h
  simpa using! h

/-- Tensoring a decompressed XOR run with a schedule's Fock register state preserves the run's
squared norm. -/
theorem compressedJointState_xor_transport {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] {N : ℕ} (p : ℝ) (sch : QuerySchedule N)
    (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) :
    ∑ q, ‖compressedJointState (fockRegisterState sch)
        (Qatlib.Concepts.QueryComplexity.DegreeMethod.decompressedXorRun p C ψ) q‖ ^ 2
      = ∑ q, ‖Qatlib.Concepts.QueryComplexity.DegreeMethod.decompressedXorRun p C ψ q‖ ^ 2 :=
  compressedJointState_xor_norm p sch C ψ

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- The position success block is diagonal with entries given by products of guessed
occupations. -/
theorem positionSuccessBlock_eq_diagonal {N t v : ℕ} (z : Fin v → Fin N) :
    positionSuccessBlock (t := t) z
      = Matrix.diagonal (fun p : FockBasis N t => ∏ i, ((p.1 (z i) : ℕ) : ℂ)) := by
  ext p q
  by_cases h : p = q
  · subst h
    rw [Matrix.diagonal_apply, ite_eq_left rfl]
    exact positionSuccessBlock_apply z p
  · rw [Matrix.diagonal_apply, ite_eq_right h]
    exact positionSuccessBlock_offDiagonal z p q h

/-- The operator norm of a position success block is at most the particle number raised to the
number of guesses. -/
theorem positionSuccessBlock_opNorm_le {N t v : ℕ} (z : Fin v → Fin N) :
    ‖positionSuccessBlock (t := t) z‖ ≤ (t : ℝ) ^ v := by
  rw [positionSuccessBlock_eq_diagonal, l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro p
  rw [norm_prod]
  simp only [Complex.norm_natCast]
  have hocc : ∀ x : Fin N, (p.1 x : ℕ) ≤ t := by
    intro x
    have h1 := Finset.single_le_sum (f := fun i => (p.1 i : ℕ))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
    have h2 : (p.1 x : ℕ) ≤ ∑ x : Fin N, (p.1 x : ℕ) := h1
    rw [p.property] at h2
    exact h2
  have hnonneg : ∀ i : Fin v, (0 : ℝ) ≤ ((p.1 (z i) : ℕ) : ℝ) := by
    intro i
    positivity
  have hle : ∀ i : Fin v, ((p.1 (z i) : ℕ) : ℝ) ≤ (t : ℝ) := by
    intro i
    exact_mod_cast hocc (z i)
  have hprod : (∏ i : Fin v, ((p.1 (z i) : ℕ) : ℝ)) ≤ ∏ _i : Fin v, (t : ℝ) := by
    refine Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => hle i)
  have hconst : (∏ _i : Fin v, (t : ℝ)) = (t : ℝ) ^ v := by
    simp
  rw [← hconst]
  exact hprod

/-- The operator norm of a position success block is bounded by `positionMultiQueryBound`. -/
theorem positionSuccessBlock_opNorm_le_bound {N t v : ℕ} (z : Fin v → Fin N) :
    ‖positionSuccessBlock (t := t) z‖ ≤ positionMultiQueryBound N t v := by
  rw [positionMultiQueryBound, positionPerQueryNorm]
  exact positionSuccessBlock_opNorm_le z

/-- The position multi-query recurrence holds for every number of modes and particles. -/
theorem positionMultiQueryRecurrence_holds (N t : ℕ) :
    positionMultiQueryRecurrence N t := by
  constructor
  · simp [positionMultiQueryBound, positionPerQueryNorm]
  · intro q
    simp [positionMultiQueryBound, positionPerQueryNorm, pow_succ, mul_comm]

/-- The avoidance weight of a singleton is one exactly when its mode has zero occupation, and
zero otherwise. -/
theorem avoidWeight_singleton {N : ℕ} (x : Fin N) (k : Fin N → ℕ) :
    avoidWeight {x} k = if k x = 0 then 1 else 0 := by
  by_cases h : k x = 0 <;> simp [avoidWeight, h]

/-- The avoidance weight of a pair is the product of the two zero-occupation indicators. -/
theorem avoidWeight_pair {N : ℕ} (x y : Fin N) (k : Fin N → ℕ) :
    avoidWeight {x, y} k = (if k x = 0 then 1 else 0) * (if k y = 0 then 1 else 0) := by
  by_cases h1 : k x = 0
  · by_cases h2 : k y = 0
    · simp [avoidWeight, h1, h2]
    · simp [avoidWeight, h1, h2]
  · by_cases h2 : k y = 0
    · simp [avoidWeight, h1, h2]
    · simp [avoidWeight, h1, h2]

/-- The probability of avoiding one mode is the fraction of remaining modes raised to the number
of placements. -/
theorem multisetAvoidProb_singleton {N t : ℕ} (x : Fin N) :
    multisetAvoidProb N t {x} = ((((N : ℝ) - 1) / (N : ℝ)) ^ t) := by
  rw [multisetAvoidProb_eq_sub]
  have hcard : ({x} : Finset (Fin N)).card = 1 := by simp
  rw [hcard]
  ring

/-- The probability of avoiding two distinct modes is the fraction of remaining modes raised to
the number of placements. -/
theorem multisetAvoidProb_pair {N t : ℕ} (x y : Fin N) (hxy : x ≠ y) :
    multisetAvoidProb N t {x, y} = ((((N : ℝ) - 2) / (N : ℝ)) ^ t) := by
  rw [multisetAvoidProb_eq_sub]
  have hcard : ({x, y} : Finset (Fin N)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr hxy
  rw [hcard]
  ring

/-- Success on all guesses is bounded by the inclusion-exclusion expression for occupying two
specified distinct guessed modes. -/
theorem multisetSuccessProb_le_bonferroni2 {N t v : ℕ} (hN : 0 < N) (z : Fin v → Fin N)
    (i j : Fin v) (_hz : z i ≠ z j) :
    multisetSuccessProb N t v z
      ≤ 1 - multisetAvoidProb N t {z i} - multisetAvoidProb N t {z j}
          + multisetAvoidProb N t {z i, z j} := by
  have hper : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      ((if ∀ k, (w.1 (z k) : ℕ) ≠ 0 then (1 : ℝ) else 0)
        ≤ (1 : ℝ) - (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
              - (if (w.1 (z j) : ℕ) = 0 then 1 else 0)
              + (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                  * (if (w.1 (z j) : ℕ) = 0 then 1 else 0)) := by
    intro w
    by_cases h0 : (w.1 (z i) : ℕ) = 0
    · by_cases h1 : (w.1 (z j) : ℕ) = 0
      · have hne : ¬(∀ k, (w.1 (z k) : ℕ) ≠ 0) := fun h => h i h0
        simp only [ite_eq_left h0, ite_eq_left h1, ite_eq_right hne]
        norm_num
      · have hne : ¬(∀ k, (w.1 (z k) : ℕ) ≠ 0) := fun h => h i h0
        simp only [ite_eq_left h0, ite_eq_right h1, ite_eq_right hne]
        norm_num
    · by_cases h1 : (w.1 (z j) : ℕ) = 0
      · have hne : ¬(∀ k, (w.1 (z k) : ℕ) ≠ 0) := fun h => h j h1
        simp only [ite_eq_right h0, ite_eq_left h1, ite_eq_right hne]
        norm_num
      · by_cases hall : ∀ k, (w.1 (z k) : ℕ) ≠ 0
        · simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_left hall]
          norm_num
        · simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_right hall]
          norm_num
  have hnonneg : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, 0 ≤ uniformMultisetProb N t w := by
    intro w
    unfold uniformMultisetProb
    positivity
  have hsum : ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w = 1 :=
    uniformMultisetProb_sum_eq_one N t hN
  have hA : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        (if (w.1 (z i) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
      = multisetAvoidProb N t {z i} := by
    have hkey : (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
        (if (w.1 (z i) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
      = (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
        avoidWeight {z i} (fun x => (w.1 x : ℕ)) * uniformMultisetProb N t w) := by
      funext w
      rw [avoidWeight_singleton]
    unfold multisetAvoidProb
    rw [hkey]
  have hB : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        (if (w.1 (z j) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
      = multisetAvoidProb N t {z j} := by
    have hkey : (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
        (if (w.1 (z j) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
      = (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
        avoidWeight {z j} (fun x => (w.1 x : ℕ)) * uniformMultisetProb N t w) := by
      funext w
      rw [avoidWeight_singleton]
    unfold multisetAvoidProb
    rw [hkey]
  have hC : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
          * (if (w.1 (z j) : ℕ) = 0 then 1 else 0)) * uniformMultisetProb N t w)
      = multisetAvoidProb N t {z i, z j} := by
    have hkey : (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
        ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
          * (if (w.1 (z j) : ℕ) = 0 then 1 else 0)) * uniformMultisetProb N t w)
      = (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
        avoidWeight {z i, z j} (fun x => (w.1 x : ℕ)) * uniformMultisetProb N t w) := by
      funext w
      rw [avoidWeight_pair (z i) (z j)]
    unfold multisetAvoidProb
    rw [hkey]
  have hmain : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        (if ∀ k, (w.1 (z k) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
      ≤ ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        ((1 : ℝ) - (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
             - (if (w.1 (z j) : ℕ) = 0 then 1 else 0)
             + (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                 * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
          * uniformMultisetProb N t w := by
    apply Finset.sum_le_sum
    intro w _
    exact mul_le_mul_of_nonneg_right (hper w) (hnonneg w)
  have hexpand : (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        ((1 : ℝ) - (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
             - (if (w.1 (z j) : ℕ) = 0 then 1 else 0)
             + (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                 * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
          * uniformMultisetProb N t w)
      = (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w)
        - (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            (if (w.1 (z i) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
        - (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            (if (w.1 (z j) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
        + (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
              * (if (w.1 (z j) : ℕ) = 0 then 1 else 0)) * uniformMultisetProb N t w) := by
    have key : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        ((1 : ℝ) - (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
             - (if (w.1 (z j) : ℕ) = 0 then 1 else 0)
             + (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                 * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
            * uniformMultisetProb N t w
        = uniformMultisetProb N t w
          - ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
            * uniformMultisetProb N t w)
          - ((if (w.1 (z j) : ℕ) = 0 then 1 else 0)
            * uniformMultisetProb N t w)
          + ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
            * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
            * uniformMultisetProb N t w := by
      intro w
      ring
    calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        ((1 : ℝ) - (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
             - (if (w.1 (z j) : ℕ) = 0 then 1 else 0)
             + (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                 * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
          * uniformMultisetProb N t w)
        = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            (uniformMultisetProb N t w
              - ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                * uniformMultisetProb N t w)
              - ((if (w.1 (z j) : ℕ) = 0 then 1 else 0)
                * uniformMultisetProb N t w)
              + ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
                * uniformMultisetProb N t w) := by
            have hkey : (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
                ((1 : ℝ) - (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                     - (if (w.1 (z j) : ℕ) = 0 then 1 else 0)
                     + (if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                         * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
                * uniformMultisetProb N t w)
              = (fun w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t =>
                (uniformMultisetProb N t w
                  - ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                    * uniformMultisetProb N t w)
                  - ((if (w.1 (z j) : ℕ) = 0 then 1 else 0)
                    * uniformMultisetProb N t w)
                  + ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                    * (if (w.1 (z j) : ℕ) = 0 then 1 else 0))
                    * uniformMultisetProb N t w)) := by
              funext w
              exact key w
            rw [hkey]
      _ = (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w)
          - (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
              (if (w.1 (z i) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
          - (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
              (if (w.1 (z j) : ℕ) = 0 then 1 else 0) * uniformMultisetProb N t w)
          + (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
              ((if (w.1 (z i) : ℕ) = 0 then 1 else 0)
                * (if (w.1 (z j) : ℕ) = 0 then 1 else 0)) * uniformMultisetProb N t w) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold multisetSuccessProb
  exact hmain.trans (by
    rw [hexpand, hsum, hA, hB, hC])

/-- Success on all guesses is bounded by the two-mode inclusion-exclusion expression with the
pair-avoidance probability evaluated explicitly. -/
theorem multisetSuccessProb_le_bonferroni2_pair {N t v : ℕ} (hN : 0 < N)
    (z : Fin v → Fin N) (i j : Fin v) (hz : z i ≠ z j) :
    multisetSuccessProb N t v z
      ≤ 1 - multisetAvoidProb N t {z i} - multisetAvoidProb N t {z j}
          + ((((N : ℝ) - 2) / (N : ℝ)) ^ t) := by
  exact (multisetSuccessProb_le_bonferroni2 hN z i j hz).trans (by
    rw [multisetAvoidProb_pair (z i) (z j) hz])

/-- Establishes uniform multiset normalization, database update and compression identities,
placement and schedule profile agreement, and normalization and norm transport for
compressed joint states. -/
theorem clause1_complete :
    (∀ (N t : ℕ) (_hN : 0 < N),
      ∑ v : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t v = 1)
    ∧ (∀ {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
        (db : ValuedDatabase I V) (x : I) (v : V), db x = some v →
        duplicateValueQuery db x v ∨ newElement db x v)
    ∧ (∀ {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
        (db : ValuedDatabase I V) (x : I) (v : V),
        duplicateValueQuery db x v → valueCollision (valuedUpdate db x v))
    ∧ (∀ {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V]
        (db : ValuedDatabase I V) (x : I) (v : V),
        newElement db x v → newElement (valuedUpdate db x v) x v)
    ∧ (∀ (N : ℕ) (d : Fin N → Bool),
        decompressBlock (compressBlock (booleanValuedDatabase d)) = booleanValuedDatabase d)
    ∧ (∀ {N t : ℕ} (f : Fin t → Fin N),
        placementProfile f = placementCompressedRegister f)
    ∧ (∀ {N : ℕ} (sch : QuerySchedule N),
        placementCompressedRegister (fun i : Fin sch.length => sch.get i) = scheduleProfile sch)
    ∧ (∀ {N : ℕ} (sch : QuerySchedule N),
        ∑ v, ‖fockRegisterState sch v‖ ^ 2 = 1)
    ∧ (∀ {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
        {N t : ℕ} (reg : FockBasis N t → ℂ) (ψ : QState (((I × Bool) × W) × (I → Bool))),
        (∑ v, ‖reg v‖ ^ 2 = 1) → (∑ q, ‖ψ q‖ ^ 2 = 1) →
          ∑ q, ‖compressedJointState reg ψ q‖ ^ 2 = 1)
    ∧ (∀ {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
        {N : ℕ} (p : ℝ) (sch : QuerySchedule N)
        (C : Qatlib.Foundations.QueryWordCore.Circuit.Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)),
        ∑ q, ‖compressedJointState (fockRegisterState sch)
            (Qatlib.Concepts.QueryComplexity.DegreeMethod.decompressedXorRun p C ψ) q‖ ^ 2
          = ∑ q, ‖Qatlib.Concepts.QueryComplexity.DegreeMethod.decompressedXorRun p C ψ q‖ ^ 2) :=
  ⟨fun N t hN => uniformMultisetProb_sum_eq_one N t hN,
   fun db x v h => duplicateValueQuery_or_newElement db x v h,
   fun db x v h => valuedUpdate_valueCollision db x v h,
   fun db x v h => valuedUpdate_newElement db x v h,
   fun _ d => decompressCompressBlock d,
   fun f => placementProfile_eq_placementCompressedRegister f,
   fun sch => placementCompressedRegister_eq_scheduleProfile sch,
   fun sch => compressedRegisterState_normalized sch,
   fun reg ψ hreg hψ => compressedJointState_normalized reg ψ hreg hψ,
   fun p sch C ψ => compressedJointState_xor_transport p sch C ψ⟩

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- For injective guesses, multiset success probability is the alternating binomial sum of the
avoidance probabilities for each possible subset size. -/
theorem multisetSuccessProb_injective_eq {N t v : ℕ} (z : Fin v → Fin N)
    (hz : Function.Injective z) :
    multisetSuccessProb N t v z
      = ∑ m ∈ Finset.range (v + 1),
          ((v.choose m : ℝ) * ((-1 : ℝ) ^ m) * ((((N : ℝ) - m) / (N : ℝ)) ^ t)) := by
  rw [multisetSuccessProb_eq_inclusionExclusion_closed]
  classical
  have hcard : ∀ J : Finset (Fin v), (Finset.image z J).card = J.card := by
    intro J
    exact Finset.card_image_of_injective J hz
  have hstep : (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
      ((-1 : ℝ) ^ J.card)
        * ((((N : ℝ) - ((Finset.image z J).card : ℝ)) / (N : ℝ)) ^ t))
      = (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
        ((-1 : ℝ) ^ J.card) * ((((N : ℝ) - (J.card : ℝ)) / (N : ℝ)) ^ t)) := by
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hcard J]
  rw [hstep]
  have hone : (∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
      ((-1 : ℝ) ^ J.card) * ((((N : ℝ) - (J.card : ℝ)) / (N : ℝ)) ^ t))
      = ∑ J ∈ (Finset.univ : Finset (Fin v)).powerset,
        (fun m : ℕ => ((-1 : ℝ) ^ m) * ((((N : ℝ) - (m : ℝ)) / (N : ℝ)) ^ t)) J.card := by
    refine Finset.sum_congr rfl fun J _ => rfl
  rw [hone]
  rw [Finset.sum_powerset_apply_card
      (f := fun m : ℕ => ((-1 : ℝ) ^ m) * ((((N : ℝ) - (m : ℝ)) / (N : ℝ)) ^ t))
      (x := (Finset.univ : Finset (Fin v)))]
  have hcardu : ((Finset.univ : Finset (Fin v)).card) = v := by simp
  rw [hcardu]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- Any two injective guess maps with the same domain and codomain have equal multiset success
probability. -/
theorem multisetSuccessProb_injective_congr {N t v : ℕ} (z z' : Fin v → Fin N)
    (hz : Function.Injective z) (hz' : Function.Injective z') :
    multisetSuccessProb N t v z = multisetSuccessProb N t v z' := by
  rw [multisetSuccessProb_injective_eq z hz, multisetSuccessProb_injective_eq z' hz']

def injectiveGuessTerm (N t v m : ℕ) : ℝ :=
  (v.choose m : ℝ) * ((-1 : ℝ) ^ m) * ((((N : ℝ) - m) / (N : ℝ)) ^ t)

/-- For injective guesses, multiset success probability is the sum of `injectiveGuessTerm` over
all subset sizes. -/
theorem multisetSuccessProb_injective_eq_term {N t v : ℕ} (z : Fin v → Fin N)
    (hz : Function.Injective z) :
    multisetSuccessProb N t v z = ∑ m ∈ Finset.range (v + 1), injectiveGuessTerm N t v m := by
  rw [multisetSuccessProb_injective_eq z hz]
  refine Finset.sum_congr rfl fun m _ => rfl

/-- For a positive number of modes, the success probability of injective guesses lies between
zero and one. -/
theorem multisetSuccessProb_injective_bounds {N t v : ℕ} (z : Fin v → Fin N)
    (_hz : Function.Injective z) (hN : 0 < N) :
    0 ≤ multisetSuccessProb N t v z ∧ multisetSuccessProb N t v z ≤ 1 := by
  exact multisetSuccessProb_bounds (N := N) (t := t) (v := v) z hN

/-- Every basis prefix in the uniform prefix state has Born probability equal to the reciprocal
of the number of prefixes. -/
theorem uniformPrefixState_bornProb (N k : ℕ) (p : PrefixBasis N k) :
    Qatlib.Foundations.PureStateMath.BornProb (uniformPrefixState N k) p = ((N ^ k : ℕ) : ℝ)⁻¹ := by
  have hpos : 0 ≤ ((N ^ k : ℕ) : ℝ)⁻¹ := by positivity
  unfold Qatlib.Foundations.PureStateMath.BornProb uniformPrefixState
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im]
  rw [← pow_two, Real.sq_sqrt hpos]
  simp

/-- The uniform prefix state is normalized when the number of modes is positive. -/
theorem uniformPrefixState_normalized {N k : ℕ} (hN : 0 < N) :
    Qatlib.Foundations.PureStateMath.Normalized (uniformPrefixState N k) := by
  have hcard : Fintype.card (PrefixBasis N k) = N ^ k := by
    simp [PrefixBasis, Fintype.card_pi]
  have hsum : (∑ i, ‖uniformPrefixState N k i‖ ^ 2)
      = ∑ i, Qatlib.Foundations.PureStateMath.BornProb (uniformPrefixState N k) i :=
    rfl
  unfold Qatlib.Foundations.PureStateMath.Normalized
  rw [hsum]
  calc ∑ i, Qatlib.Foundations.PureStateMath.BornProb (uniformPrefixState N k) i
      = ∑ _i : PrefixBasis N k, ((N ^ k : ℕ) : ℝ)⁻¹ :=
        Finset.sum_congr rfl (fun i _ => uniformPrefixState_bornProb N k i)
    _ = (Fintype.card (PrefixBasis N k) : ℝ) * ((N ^ k : ℕ) : ℝ)⁻¹ := by
        rw [Finset.sum_const, Finset.card_univ]
        norm_num
    _ = 1 := by
        rw [hcard]
        field_simp [Nat.ne_of_gt hN]

/-- The number of prefixes avoiding a forbidden set is the number of allowed modes raised to the
prefix length. -/
theorem prefixAvoidFinset_card (N k : ℕ) (T : Finset (Fin N)) :
    (prefixAvoidFinset N k T).card = (N - T.card) ^ k := by
  classical
  rw [prefixAvoidFinset, Fintype.card_piFinset_const]
  have hcompl : ((Finset.univ : Finset (Fin N)) \ T).card = N - T.card := by
    rw [Finset.card_sdiff]
    simp
  rw [hcompl]

/-- In the uniform prefix state, the probability of avoiding a set is the allowed-mode fraction
raised to the prefix length. -/
theorem uniformPrefixState_avoid {N k : ℕ} (_hN : 0 < N) (T : Finset (Fin N)) :
    Qatlib.Foundations.PureStateMath.MeasureProb (uniformPrefixState N k) (prefixAvoidFinset N k T)
      = (((N : ℝ) - (T.card : ℝ)) / N) ^ k := by
  classical
  calc Qatlib.Foundations.PureStateMath.MeasureProb (uniformPrefixState N k) (prefixAvoidFinset N k T)
      = ∑ _p ∈ prefixAvoidFinset N k T, ((N ^ k : ℕ) : ℝ)⁻¹ := by
        rw [Qatlib.Foundations.PureStateMath.MeasureProb, Finset.sum_congr rfl]
        intro p hp
        rw [uniformPrefixState_bornProb]
    _ = ((prefixAvoidFinset N k T).card : ℝ) * ((N ^ k : ℕ) : ℝ)⁻¹ := by
        rw [Finset.sum_const]
        norm_num
    _ = (((N : ℝ) - (T.card : ℝ)) / N) ^ k := by
        have h1 : ((N ^ k : ℕ) : ℝ) = (N : ℝ) ^ k := Nat.cast_pow N k
        have h3 : (((N - T.card) ^ k : ℕ) : ℝ) = ((N - T.card : ℕ) : ℝ) ^ k := Nat.cast_pow _ _
        have hle : T.card ≤ N := by
          have h := Finset.card_le_univ (s := T)
          simpa [Fintype.card_fin] using! h
        have h2 : ((N - T.card : ℕ) : ℝ) = (N : ℝ) - (T.card : ℝ) := by
          rw [Nat.cast_sub hle]
        rw [prefixAvoidFinset_card, h1, ← inv_pow, h3, h2, div_eq_mul_inv, ← mul_pow, mul_comm]

/-- Uniform-prefix avoidance probability equals the corresponding multiset avoidance
probability. -/
theorem uniformPrefixState_avoid_eq_multisetAvoidProb {N k : ℕ} (hN : 0 < N)
    (T : Finset (Fin N)) :
    Qatlib.Foundations.PureStateMath.MeasureProb (uniformPrefixState N k) (prefixAvoidFinset N k T)
      = multisetAvoidProb N k T := by
  rw [uniformPrefixState_avoid hN T, multisetAvoidProb_eq_sub]

/-- Uniform-prefix avoidance probability is the single-position avoidance probability raised to
the prefix length. -/
theorem uniformPrefixState_avoid_pow {N k : ℕ} (hN : 0 < N) (T : Finset (Fin N)) :
    Qatlib.Foundations.PureStateMath.MeasureProb (uniformPrefixState N k) (prefixAvoidFinset N k T)
      = (Qatlib.Foundations.PureStateMath.MeasureProb (uniformPrefixState N 1) (prefixAvoidFinset N 1 T)) ^ k := by
  rw [uniformPrefixState_avoid hN T, uniformPrefixState_avoid hN T]
  simp [pow_one]

/-- An empty uniform prefix avoids every forbidden set with probability one when the number of
modes is positive. -/
theorem uniformPrefixState_avoid_zero {N : ℕ} (hN : 0 < N) (T : Finset (Fin N)) :
    Qatlib.Foundations.PureStateMath.MeasureProb (uniformPrefixState N 0) (prefixAvoidFinset N 0 T) = 1 := by
  rw [uniformPrefixState_avoid hN T]
  simp

/-- With no modes and positive prefix length, the uniform prefix state is zero. -/
theorem uniformPrefixState_zero {k : ℕ} (hk : 0 < k) :
    uniformPrefixState 0 k = 0 := by
  funext p
  simp [uniformPrefixState, hk]

/-- The number of occupied modes is at most the total particle number. -/
theorem occupiedModeCount_le {N t : ℕ} (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    occupiedModeCount w ≤ t := by
  classical
  have hcard : occupiedModeCount w
      = ∑ x ∈ (Finset.univ : Finset (Fin N)),
          (if 0 < (w.1 x : ℕ) then (1 : ℕ) else 0) := by
    unfold occupiedModeCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcard]
  have h1 : (∑ x ∈ (Finset.univ : Finset (Fin N)),
        (if 0 < (w.1 x : ℕ) then (1 : ℕ) else 0))
      ≤ ∑ x ∈ (Finset.univ : Finset (Fin N)), (w.1 x : ℕ) := by
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h : 0 < (w.1 x : ℕ)
    · simp [h]; omega
    · have hz : (w.1 x : ℕ) = 0 := by omega
      simp [hz]
  have h2 : ∑ x ∈ (Finset.univ : Finset (Fin N)), (w.1 x : ℕ) = t := w.property
  omega

/-- The number of occupied modes is at most the total number of modes. -/
theorem occupiedModeCount_le_card {N t : ℕ} (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    occupiedModeCount w ≤ N := by
  classical
  unfold occupiedModeCount
  have h := Finset.card_le_univ (s := (Finset.univ : Finset (Fin N)).filter
    (fun x => 0 < (w.1 x : ℕ)))
  simpa [Fintype.card_fin] using! h

/-- The number of occupied modes equals the sum of their nonzero-occupation indicators. -/
theorem occupiedModeCount_eq_sum_indicator {N t : ℕ}
    (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    (occupiedModeCount w : ℝ)
      = ∑ x : Fin N, (if (w.1 x : ℕ) ≠ 0 then (1 : ℝ) else 0) := by
  classical
  have hcard : occupiedModeCount w
      = ∑ x ∈ (Finset.univ : Finset (Fin N)),
          (if 0 < (w.1 x : ℕ) then (1 : ℕ) else 0) := by
    unfold occupiedModeCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hcard, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : (w.1 x : ℕ) ≠ 0
  · simp [Nat.pos_of_ne_zero h, h]
  · have hz : (w.1 x : ℕ) = 0 := by omega
    simp [hz]

/-- The uniform multiset probability that a mode is occupied equals one minus its avoidance
probability. -/
theorem sum_uniformMultisetProb_occupied {N t : ℕ} (x : Fin N) (hN : 0 < N) :
    (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w
        * (if (w.1 x : ℕ) ≠ 0 then (1 : ℝ) else 0))
      = 1 - multisetAvoidProb N t {x} := by
  classical
  have hone : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      (if (w.1 x : ℕ) ≠ 0 then (1 : ℝ) else 0)
        = 1 - avoidWeight {x} (fun y => (w.1 y : ℕ)) := by
    intro w
    by_cases h : (w.1 x : ℕ) = 0
    · have hne : ¬ ((w.1 x : ℕ) ≠ 0) := by simp [h]
      rw [ite_eq_right hne]
      simp [avoidWeight_singleton, h]
    · have hne : (w.1 x : ℕ) ≠ 0 := by simp [h]
      rw [ite_eq_left hne]
      simp [avoidWeight_singleton, hne]
  calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w
        * (if (w.1 x : ℕ) ≠ 0 then (1 : ℝ) else 0))
      = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          (uniformMultisetProb N t w
            * (1 - avoidWeight {x} (fun y => (w.1 y : ℕ)))) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [hone w]
    _ = (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w)
        - ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            (uniformMultisetProb N t w * avoidWeight {x} (fun y => (w.1 y : ℕ))) := by
        have hsplit : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            uniformMultisetProb N t w
                * (1 - avoidWeight {x} (fun y => (w.1 y : ℕ)))
              = uniformMultisetProb N t w
                - uniformMultisetProb N t w * avoidWeight {x} (fun y => (w.1 y : ℕ)) := by
          intro w
          ring
        rw [Finset.sum_congr rfl (fun w _ => hsplit w)]
        exact Finset.sum_sub_distrib
          (s := (Finset.univ : Finset (Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t)))
          (f := fun w => uniformMultisetProb N t w)
          (g := fun w => uniformMultisetProb N t w * avoidWeight {x} (fun y => (w.1 y : ℕ)))
    _ = 1 - multisetAvoidProb N t {x} := by
        rw [uniformMultisetProb_sum_eq_one N t hN]
        congr 1
        unfold multisetAvoidProb
        exact Finset.sum_congr rfl (fun w _ => mul_comm _ _)

/-- The expected number of occupied modes is the total number of modes times the single-mode
occupation probability. -/
theorem sum_uniformMultisetProb_occupiedModeCount {N t : ℕ} (hN : 0 < N) :
    (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * (occupiedModeCount w : ℝ))
      = (N : ℝ) * (1 - (((N : ℝ) - 1) / (N : ℝ)) ^ t) := by
  classical
  calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * (occupiedModeCount w : ℝ))
      = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, ∑ x : Fin N,
          (uniformMultisetProb N t w * (if (w.1 x : ℕ) ≠ 0 then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [occupiedModeCount_eq_sum_indicator]
        rw [Finset.mul_sum]
    _ = ∑ x : Fin N, ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          (uniformMultisetProb N t w * (if (w.1 x : ℕ) ≠ 0 then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
    _ = ∑ x : Fin N, (1 - multisetAvoidProb N t {x}) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact sum_uniformMultisetProb_occupied x hN
    _ = (N : ℝ) * (1 - (((N : ℝ) - 1) / (N : ℝ)) ^ t) := by
        simp only [multisetAvoidProb_singleton]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp [Fintype.card_fin]

/-- A mode's multiset occupation probability is one minus the probability of avoiding it in
every placement. -/
theorem multisetOccupiedProb_eq {N t : ℕ} (x : Fin N) :
    multisetOccupiedProb N t x = 1 - (((N : ℝ) - 1) / (N : ℝ)) ^ t := by
  rw [multisetOccupiedProb, multisetAvoidProb_singleton]

/-- A mode's multiset occupation probability is the complement of its singleton avoidance
probability. -/
theorem multisetOccupiedProb_eq_avoid {N t : ℕ} (x : Fin N) :
    multisetOccupiedProb N t x = 1 - multisetAvoidProb N t {x} := rfl

/-- The coupled occupation probability for one guess equals the single-mode occupation
probability. -/
theorem coupledOccupiedProb_one_eq {N t : ℕ} (hN : 0 < N) :
    coupledOccupiedProb N t 1 = 1 - (((N : ℝ) - 1) / (N : ℝ)) ^ t := by
  have hone : coupledOccupiedProb N t 1
      = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ 1 := by
    rfl
  rw [hone]
  calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ 1)
      = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          (uniformMultisetProb N t w * (occupiedModeCount w : ℝ)) * (N : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro w _
        simp only [pow_one]
        rw [div_eq_mul_inv]
        ring
    _ = (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          uniformMultisetProb N t w * (occupiedModeCount w : ℝ)) * (N : ℝ)⁻¹ := by
        rw [← Finset.sum_mul]
    _ = ((N : ℝ) * (1 - (((N : ℝ) - 1) / (N : ℝ)) ^ t)) * (N : ℝ)⁻¹ := by
        rw [sum_uniformMultisetProb_occupiedModeCount (N := N) (t := t) hN]
    _ = 1 - (((N : ℝ) - 1) / (N : ℝ)) ^ t := by
        have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
        field_simp

/-- Coupled occupation probability is nonnegative. -/
theorem coupledOccupiedProb_nonneg {N t k : ℕ} :
    0 ≤ coupledOccupiedProb N t k := by
  classical
  unfold coupledOccupiedProb
  refine Finset.sum_nonneg fun w _ => ?_
  have hP : 0 ≤ uniformMultisetProb N t w := by
    unfold uniformMultisetProb
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg N) t)
  have hbase : 0 ≤ (occupiedModeCount w : ℝ) / (N : ℝ) := by
    positivity
  exact mul_nonneg hP (pow_nonneg hbase k)

/-- Coupled occupation probability is at most one when the number of modes is positive. -/
theorem coupledOccupiedProb_le_one {N t k : ℕ} (hN : 0 < N) :
    coupledOccupiedProb N t k ≤ 1 := by
  classical
  have hP : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, 0 ≤ uniformMultisetProb N t w := by
    intro w
    unfold uniformMultisetProb
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg N) t)
  have hpoint : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k ≤ 1 := by
    intro w
    have hcard : (occupiedModeCount w : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (occupiedModeCount_le_card w)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hle : (occupiedModeCount w : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact hcard
    have hnonneg : 0 ≤ (occupiedModeCount w : ℝ) / (N : ℝ) := by positivity
    have h : ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k ≤ (1 : ℝ) ^ k :=
      pow_le_pow_left₀ hnonneg hle k
    simpa using! h
  unfold coupledOccupiedProb
  calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k)
      ≤ ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w := by
        refine Finset.sum_le_sum fun w _ => ?_
        simpa using! mul_le_mul_of_nonneg_left (hpoint w) (hP w)
    _ = 1 := uniformMultisetProb_sum_eq_one N t hN

/-- Coupled occupation probability is at most the particle-to-mode ratio raised to the number of
guesses. -/
theorem coupledOccupiedProb_le_pow {N t k : ℕ} (hN : 0 < N) :
    coupledOccupiedProb N t k ≤ ((t : ℝ) / (N : ℝ)) ^ k := by
  classical
  have hP : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, 0 ≤ uniformMultisetProb N t w := by
    intro w
    unfold uniformMultisetProb
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg N) t)
  have hpoint : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k ≤ ((t : ℝ) / (N : ℝ)) ^ k := by
    intro w
    have hocc : (occupiedModeCount w : ℝ) ≤ (t : ℝ) := by
      exact_mod_cast (occupiedModeCount_le w)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have hle : (occupiedModeCount w : ℝ) / (N : ℝ) ≤ (t : ℝ) / (N : ℝ) := by
      apply (div_le_iff₀ hNpos).2
      rw [div_mul_cancel₀ (t : ℝ) hNne]
      exact hocc
    have hnonneg : 0 ≤ (occupiedModeCount w : ℝ) / (N : ℝ) := by positivity
    exact pow_le_pow_left₀ hnonneg hle k
  unfold coupledOccupiedProb
  calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k)
      ≤ ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * ((t : ℝ) / (N : ℝ)) ^ k := by
        refine Finset.sum_le_sum fun w _ => ?_
        exact mul_le_mul_of_nonneg_left (hpoint w) (hP w)
    _ = (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w)
        * ((t : ℝ) / (N : ℝ)) ^ k := by rw [Finset.sum_mul]
    _ = 1 * ((t : ℝ) / (N : ℝ)) ^ k := by
        rw [uniformMultisetProb_sum_eq_one N t hN]
    _ = ((t : ℝ) / (N : ℝ)) ^ k := by ring

/-- Coupled occupation probability is bounded by the normalized position per-query norm raised
to the number of guesses. -/
theorem coupledOccupiedProb_le_positionBound {N t k : ℕ} (hN : 0 < N) :
    coupledOccupiedProb N t k ≤ (positionPerQueryNorm N t / (N : ℝ)) ^ k := by
  rw [positionPerQueryNorm]
  exact coupledOccupiedProb_le_pow hN

/-- The one-guess coupled occupation probability is bounded by the normalized position per-query
norm. -/
theorem coupledOccupiedProb_one_le {N t : ℕ} (hN : 0 < N) :
    coupledOccupiedProb N t 1 ≤ positionPerQueryNorm N t / (N : ℝ) := by
  rw [positionPerQueryNorm]
  have h : coupledOccupiedProb N t 1 ≤ ((t : ℝ) / (N : ℝ)) ^ 1 :=
    coupledOccupiedProb_le_pow hN
  rw [pow_one] at h
  exact h

/-- With positive guess count and at least twice the product of particles and guesses many
modes, coupled occupation probability is at most one half. -/
theorem coupledOccupiedProb_le_half {N t k : ℕ} (hN : 0 < N) (hk : 0 < k)
    (hkt : 2 * t * k ≤ N) :
    coupledOccupiedProb N t k ≤ 1 / 2 := by
  have ht : t ≤ N := by
    have h2 : 2 * (t * k) ≤ N := by simpa [Nat.mul_assoc] using! hkt
    have h3 : t * k ≤ N := by omega
    have h4 : t ≤ t * k := by
      have hraw := Nat.mul_le_mul_right t (by omega : 1 ≤ k)
      simpa [Nat.mul_comm] using! hraw
    omega
  have htN : (t : ℝ) / (N : ℝ) ≤ 1 / 2 := by
    have h2t : 2 * t ≤ N := by
      have hstep : 2 * t ≤ 2 * t * k := by
        have h := Nat.mul_le_mul_right (2 * t) (by omega : 1 ≤ k)
        simpa [Nat.mul_comm] using! h
      omega
    have h1 : (2 : ℝ) * (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2t
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos]
    linarith
  have hnonneg : 0 ≤ (t : ℝ) / (N : ℝ) := by positivity
  have hpow : ((t : ℝ) / (N : ℝ)) ^ k ≤ (1 / 2 : ℝ) ^ k :=
    pow_le_pow_left₀ hnonneg htN k
  have hhalf : (1 / 2 : ℝ) ^ k ≤ 1 / 2 := by
    have hk0 : 0 ≤ k - 1 := by omega
    have hone : (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ (k - 1) * (1 / 2 : ℝ) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hone]
    have hle : (1 / 2 : ℝ) ^ (k - 1) ≤ 1 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (k - 1)
      simpa using! h
    linarith
  calc coupledOccupiedProb N t k
      ≤ ((t : ℝ) / (N : ℝ)) ^ k := coupledOccupiedProb_le_pow hN
    _ ≤ (1 / 2 : ℝ) ^ k := hpow
    _ ≤ 1 / 2 := hhalf

/-- The number of guess maps taking values only in occupied modes is the occupied-mode count
raised to the number of guesses. -/
theorem card_occupiedGuess {N t v : ℕ} (w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t) :
    ((Finset.univ : Finset (Fin v → Fin N)).filter
        (fun z => ∀ i, (w.1 (z i) : ℕ) ≠ 0)).card = (occupiedModeCount w) ^ v := by
  classical
  let s : Finset (Fin v → Fin N) :=
    (Finset.univ : Finset (Fin v → Fin N)).filter (fun z => ∀ i, (w.1 (z i) : ℕ) ≠ 0)
  let t : Finset (Fin v → Fin N) :=
    Fintype.piFinset (fun _ : Fin v =>
      (Finset.univ : Finset (Fin N)).filter (fun x => (w.1 x : ℕ) ≠ 0))
  have hcard : s.card = t.card := by
    refine Finset.card_bij' (s := s) (t := t) (i := fun z _ => z) (j := fun g _ => g) ?_ ?_ ?_ ?_
    · intro a ha
      dsimp [s] at ha
      have hpa : ∀ i, (w.1 (a i) : ℕ) ≠ 0 := (Finset.mem_filter.mp ha).2
      dsimp [t]
      exact Fintype.mem_piFinset.mpr fun i =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ (a i), hpa i⟩
    · intro a ha
      dsimp [t] at ha
      have hmem : ∀ i, a i ∈
          (Finset.univ : Finset (Fin N)).filter (fun x => (w.1 x : ℕ) ≠ 0) :=
        Fintype.mem_piFinset.mp ha
      dsimp [s]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun i => (Finset.mem_filter.mp (hmem i)).2⟩
    · intro a ha
      rfl
    · intro a ha
      rfl
  have hcardpi : t.card
      = ((Finset.univ : Finset (Fin N)).filter (fun x => (w.1 x : ℕ) ≠ 0)).card ^ v := by
    dsimp [t]
    simp
  have hS : ((Finset.univ : Finset (Fin N)).filter (fun x => (w.1 x : ℕ) ≠ 0)).card
      = occupiedModeCount w := by
    unfold occupiedModeCount
    congr 1
    ext x
    simp [Nat.pos_iff_ne_zero]
  dsimp [s]
  rw [hcard, hcardpi, hS]

/-- Random-guess success probability equals coupled occupation probability. -/
theorem randomGuessSuccessProb_eq_coupled {N t v : ℕ} :
    randomGuessSuccessProb N t v = coupledOccupiedProb N t v := by
  classical
  have hswap : (∑ z : Fin v → Fin N, ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
      = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, ∑ z : Fin v → Fin N,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w := by
    rw [Finset.sum_comm]
  have hinner : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
      (∑ z : Fin v → Fin N,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
        = (occupiedModeCount w) ^ v * uniformMultisetProb N t w := by
    intro w
    have hcard := card_occupiedGuess (v := v) w
    have hcardR : ((Finset.univ : Finset (Fin v → Fin N)).filter
        (fun z => ∀ i, (w.1 (z i) : ℕ) ≠ 0)).card = ((occupiedModeCount w : ℝ) ^ v) := by
      rw [hcard, Nat.cast_pow]
    have hind : (∑ z : Fin v → Fin N,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then (1 : ℕ) else 0))
        = ((Finset.univ : Finset (Fin v → Fin N)).filter
            (fun z => ∀ i, (w.1 (z i) : ℕ) ≠ 0)).card := by
      rw [← Finset.sum_filter, Finset.card_eq_sum_ones]
    have hindR : (∑ z : Fin v → Fin N,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then (1 : ℝ) else 0))
        = (((Finset.univ : Finset (Fin v → Fin N)).filter
            (fun z => ∀ i, (w.1 (z i) : ℕ) ≠ 0)).card : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      simp
    calc (∑ z : Fin v → Fin N,
        (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w)
        = uniformMultisetProb N t w *
            (∑ z : Fin v → Fin N, (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0)) := by
          rw [mul_comm, Finset.sum_mul]
        _ = uniformMultisetProb N t w * (occupiedModeCount w) ^ v := by
          rw [← hcardR]
          exact congrArg (fun s => uniformMultisetProb N t w * s) hindR
        _ = (occupiedModeCount w) ^ v * uniformMultisetProb N t w := by ring
  unfold randomGuessSuccessProb multisetSuccessProb coupledOccupiedProb
  calc (∑ z : Fin v → Fin N, ((N : ℝ) ^ v)⁻¹ *
          (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w))
      = ((N : ℝ) ^ v)⁻¹ * (∑ z : Fin v → Fin N, ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
            (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w) := by
        rw [← Finset.mul_sum]
    _ = ((N : ℝ) ^ v)⁻¹ * (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, ∑ z : Fin v → Fin N,
          (if ∀ i, (w.1 (z i) : ℕ) ≠ 0 then 1 else 0) * uniformMultisetProb N t w) := by
        rw [hswap]
    _ = ((N : ℝ) ^ v)⁻¹ * (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          (occupiedModeCount w) ^ v * uniformMultisetProb N t w) := by
        rw [Finset.sum_congr rfl (fun w _ => hinner w)]
    _ = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          ((N : ℝ) ^ v)⁻¹ * ((occupiedModeCount w) ^ v * uniformMultisetProb N t w) := by
        rw [Finset.mul_sum]
    _ = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
          uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ v := by
        refine Finset.sum_congr rfl fun w _ => ?_
        have h1 : ((N : ℝ) ^ v)⁻¹ * ((occupiedModeCount w) ^ v * uniformMultisetProb N t w)
            = ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ v * uniformMultisetProb N t w := by
          have h2 : ((N : ℝ) ^ v)⁻¹ * (occupiedModeCount w) ^ v
              = ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ v := by
            rw [div_pow, div_eq_mul_inv]
            ring
          rw [← mul_assoc, h2]
        rw [h1, mul_comm]

/-- With positive mode count, coupled occupation probability for zero guesses is one. -/
theorem coupledOccupiedProb_zero {N t : ℕ} (hN : 0 < N) :
    coupledOccupiedProb N t 0 = 1 := by
  unfold coupledOccupiedProb
  calc (∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t,
        uniformMultisetProb N t w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ 0)
      = ∑ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N t, uniformMultisetProb N t w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [pow_zero]
    _ = 1 := uniformMultisetProb_sum_eq_one N t hN

/-- With no particles and positive guess count, coupled occupation probability is zero. -/
theorem coupledOccupiedProb_noBoson {N k : ℕ} (hk : 0 < k) :
    coupledOccupiedProb N 0 k = 0 := by
  have hz : (0 : ℝ) ^ k = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    simp
  have hcard : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N 0,
      occupiedModeCount w
        = ∑ x ∈ (Finset.univ : Finset (Fin N)),
            (if 0 < (w.1 x : ℕ) then (1 : ℕ) else 0) := by
    intro w
    unfold occupiedModeCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hinner : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N 0,
      (∑ x ∈ (Finset.univ : Finset (Fin N)),
          (if 0 < (w.1 x : ℕ) then (1 : ℕ) else 0)) = 0 := by
    intro w
    have hterms : ∀ x ∈ (Finset.univ : Finset (Fin N)),
        (if 0 < (w.1 x : ℕ) then (1 : ℕ) else 0) = 0 := by
      intro x _
      have hx0 : (w.1 x : ℕ) = 0 := by
        have := w.property
        omega
      rw [ite_eq_right (by omega)]
    rw [Finset.sum_congr rfl hterms]
    simp
  have hterms : ∀ w : Qatlib.Concepts.BosonFock.BosonOperators.Occupation N 0,
      uniformMultisetProb N 0 w * ((occupiedModeCount w : ℝ) / (N : ℝ)) ^ k = 0 := by
    intro w
    rw [hcard w, hinner w]
    simp [hz]
  unfold coupledOccupiedProb
  rw [Finset.sum_congr rfl (fun w _ => hterms w)]
  simp

/-- A list's query record stores true at a mode exactly when the mode appears in the list. -/
theorem queryRecord_eq_some_true_iff {N : ℕ} (l : List (Fin N)) (x : Fin N) :
    queryRecord l x = some true ↔ x ∈ l := by
  simp [queryRecord]

/-- A placement's query record stores true exactly at the modes where its realized oracle
returns true. -/
theorem clause1_clause3_joint_oracle {N t : ℕ} (f : Fin t → Fin N) (x : Fin N) :
    (queryRecord (List.ofFn f)) x = some true ↔ realisedOracle f x = true := by
  have hmem : (x ∈ List.ofFn f) ↔ (0 < fibreCount f x) := by
    have h1 : (0 < fibreCount f x) ↔ (0 < scheduleOccupation (List.ofFn f) x) := by
      rw [scheduleOccupation_eq_fibreCount]
    have h2 : (0 < scheduleOccupation (List.ofFn f) x) ↔ (x ∈ List.ofFn f) := by
      rw [scheduleOccupation]
      exact listCount_pos_iff_mem x (List.ofFn f)
    exact h2.symm.trans h1.symm
  rw [queryRecord, realisedOracle]
  simp only [decide_eq_true_eq]
  by_cases hx : x ∈ List.ofFn f
  · simp [hx, hmem.mp hx]
  · have hnot : ¬(0 < fibreCount f x) := fun h => hx (hmem.mpr h)
    simp [hx, hnot]

/-- Multiset success is equivalent to every guessed mode being recorded as true in the
placement's query record. -/
theorem clause1_clause3_joint_success {N t v : ℕ} (f : Fin t → Fin N) (z : Fin v → Fin N) :
    multisetSuccess z f ↔ ∀ i, (queryRecord (List.ofFn f)) (z i) = some true := by
  rw [multisetSuccess]
  constructor
  · intro h i
    have hpos : 0 < fibreCount f (z i) := h i
    have hlc : 0 < listCount (z i) (List.ofFn f) := by
      rw [← fibreCount_eq_listCount f (z i)]
      exact hpos
    exact (queryRecord_eq_some_true_iff (List.ofFn f) (z i)).mpr
      ((listCount_pos_iff_mem (z i) (List.ofFn f)).mp hlc)
  · intro h i
    have hmem : z i ∈ List.ofFn f :=
      (queryRecord_eq_some_true_iff (List.ofFn f) (z i)).mp (h i)
    rw [fibreCount_eq_listCount f (z i)]
    exact (listCount_pos_iff_mem (z i) (List.ofFn f)).mpr hmem

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics

open Matrix
open scoped BigOperators
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonic
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBosonicDefs
open Qatlib
open Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedOracleBounds
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

/-- The Forrelation phase oracle for `S` is unitary. -/
theorem forrPhaseOracleS_unitary (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    forrPhaseOracleS n S W ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ :=
  tensorGate_unitary (phaseOracle_unitary _) (Submonoid.one_mem _)

/-- The Forrelation phase oracle for `U` is unitary. -/
theorem forrPhaseOracleU_unitary (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    forrPhaseOracleU n U W ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ := by
  unfold forrPhaseOracleU
  exact tensorGate_unitary (Submonoid.one_mem _)
    (tensorGate_unitary (phaseOracle_unitary _) (Submonoid.one_mem _))

/-- Every state at an `S` query in a unitary Forrelation circuit run from a normalized input is
normalized. -/
theorem sQueryStates_normalized {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hψ : Normalized ψ) :
    ∀ φ ∈ sQueryStates (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C ψ,
      Normalized φ := by
  induction C generalizing ψ with
  | nil =>
      intro φ hφ
      simp [sQueryStates] at hφ
  | cons s C ih =>
      have htail : IsUnitaryTOCircuit C := by
        intro U hU
        exact hC U (List.mem_cons_of_mem _ hU)
      cases s with
      | gate U' =>
          intro φ hφ
          have hU' : U' ∈ Matrix.unitaryGroup (ForrSpace n W) ℂ := hC U' (by simp)
          rw [sQueryStates] at hφ
          exact ih (ApplyGate U' ψ) htail (normalized_applyGate hU' hψ) φ hφ
      | queryS =>
          intro φ hφ
          rw [sQueryStates] at hφ
          rcases List.mem_cons.mp hφ with rfl | hφ
          · exact hψ
          · exact ih (ApplyGate (forrPhaseOracleS n S W) ψ) htail
              (normalized_applyGate (forrPhaseOracleS_unitary n S W) hψ) φ hφ
      | queryU =>
          intro φ hφ
          rw [sQueryStates] at hφ
          exact ih (ApplyGate (forrPhaseOracleU n U W) ψ) htail
            (normalized_applyGate (forrPhaseOracleU_unitary n U W) hψ) φ hφ

/-- Summing the `S`-query Born mass over query positions gives the state's total Born mass. -/
theorem sum_sQueryBornMass_eq (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (φ : QState (ForrSpace n W)) :
    (∑ x : Reg n, sQueryBornMass n W φ x) = ∑ p : ForrSpace n W, BornProb φ p := by
  classical
  unfold sQueryBornMass MeasureProb
  calc (∑ x : Reg n, ∑ p ∈ (Finset.univ.filter fun p : ForrSpace n W => p.1.1 = x),
          BornProb φ p)
      = ∑ x ∈ (Finset.univ : Finset (Reg n)),
          ∑ p ∈ (Finset.univ : Finset (ForrSpace n W)),
            if p.1.1 = x then BornProb φ p else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_filter]
    _ = ∑ p ∈ (Finset.univ : Finset (ForrSpace n W)),
          ∑ x ∈ (Finset.univ : Finset (Reg n)),
            if p.1.1 = x then BornProb φ p else 0 :=
        Finset.sum_comm
    _ = ∑ p : ForrSpace n W, BornProb φ p := by
        apply Finset.sum_congr rfl
        intro p _
        have h1 : (∑ x ∈ (Finset.univ : Finset (Reg n)),
              (if p.1.1 = x then BornProb φ p else 0)) = BornProb φ p := by
          rw [Finset.sum_eq_single_of_mem (p.1.1) (Finset.mem_univ _)]
          · simp
          · intro b _ hb
            simp [Ne.symm hb]
        exact h1

/-- The `S`-query Born mass at each position is nonnegative. -/
theorem sQueryBornMass_nonneg (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (φ : QState (ForrSpace n W)) (x : Reg n) :
    0 ≤ sQueryBornMass n W φ x := by
  classical
  unfold sQueryBornMass MeasureProb
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

/-- The total `S`-query Born mass of a normalized state is at most one. -/
theorem sum_sQueryBornMass_le_one (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (φ : QState (ForrSpace n W)) (hφ : Normalized φ) :
    (∑ x : Reg n, sQueryBornMass n W φ x) ≤ 1 := by
  rw [sum_sQueryBornMass_eq]
  have htot : (∑ p : ForrSpace n W, BornProb φ p) = 1 := by
    unfold BornProb
    exact hφ
  linarith

/-- A finite sum over query positions commutes with summing a mapped list. -/
private theorem sum_swap_list {n : ℕ} {α : Type} (l : List α) (g : α → Reg n → ℝ) :
    (∑ x : Reg n, (l.map (fun a => g a x)).sum) =
      (l.map (fun a => ∑ x : Reg n, g a x)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      show (∑ x : Reg n, (g a x + (l.map (fun a => g a x)).sum)) =
        (∑ x : Reg n, g a x) + (l.map (fun a => ∑ x : Reg n, g a x)).sum
      rw [Finset.sum_add_distrib, ih]

/-- The sum of a list mapped to real ones equals its length. -/
private theorem list_sum_map_one {α : Type} (l : List α) :
    (l.map (fun _ => (1 : ℝ))).sum = (l.length : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      have h2 : ((a :: l).length : ℝ) = (l.length : ℝ) + 1 := by
        rw [List.length_cons, Nat.cast_add]
        norm_num
      rw [h2, add_comm]

/-- For a unitary circuit and normalized input, total direct transition mass is at most one for
every history. -/
theorem sum_directTransitionMass_le_one {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hψ : Normalized ψ) (hist : List (Reg n)) :
    (∑ x : Reg n, directTransitionMass n W S U C ψ hist x) ≤ 1 := by
  classical
  set pre := sQueryStates (forrPhaseOracleS n (regOfList n hist) W)
    (forrPhaseOracleU n U W) C ψ with hpre
  have hlen : pre.length = TOQueryCountS C := sQueryStates_length _ _ C _
  have hnorm : ∀ φ ∈ pre, Normalized φ :=
    sQueryStates_normalized (regOfList n hist) U C ψ hC hψ
  have hswap : (∑ x : Reg n, directTransitionMass n W S U C ψ hist x)
      = (1 / (TOQueryCountS C : ℝ)) *
          (pre.map (fun φ => ∑ x : Reg n, sQueryBornMass n W φ x)).sum := by
    unfold directTransitionMass
    rw [← Finset.mul_sum]
    congr 1
    exact sum_swap_list _ _
  have hinner : (pre.map (fun φ => ∑ x : Reg n, sQueryBornMass n W φ x)).sum
      = (pre.length : ℝ) := by
    have hstep : ∀ φ ∈ pre, (∑ x : Reg n, sQueryBornMass n W φ x) = 1 := by
      intro φ hφ
      rw [sum_sQueryBornMass_eq]
      exact hnorm φ hφ
    have hmap : pre.map (fun φ => ∑ x : Reg n, sQueryBornMass n W φ x) = pre.map (fun _ => 1) := by
      apply List.map_congr_left
      intro φ hφ
      exact hstep φ hφ
    rw [hmap, list_sum_map_one]
  rw [hswap, hinner, hlen]
  by_cases ht : TOQueryCountS C = 0
  · rw [ht]
    simp [div_zero]
  · have hinv : (1 / (TOQueryCountS C : ℝ)) * (TOQueryCountS C : ℝ) = 1 := by
      field_simp
    rw [hinv]

/-- Direct transition mass is nonnegative for every history and next position. -/
theorem directTransitionMass_nonneg {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (hist : List (Reg n)) (x : Reg n) :
    0 ≤ directTransitionMass n W S U C ψ hist x := by
  classical
  unfold directTransitionMass
  refine mul_nonneg (div_nonneg (by positivity) (by positivity)) ?_
  refine List.sum_nonneg ?_
  intro m hm
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hm
  exact sQueryBornMass_nonneg n W φ x

/-- For a unitary circuit and normalized input, cumulative direct success is at most one at
every depth and history. -/
theorem cumDirectSuccess_le_one {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (C : TOCircuit (ForrSpace n W)) (ψ : QState (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hψ : Normalized ψ) :
    ∀ v hist, cumDirectSuccess n W S U C ψ v hist ≤ 1 := by
  intro v
  induction v with
  | zero =>
      intro hist
      simp [cumDirectSuccess]
  | succ v ih =>
      intro hist
      have hmass : ∀ x : Reg n, 0 ≤ directTransitionMass n W S U C ψ hist x :=
        fun x => directTransitionMass_nonneg S U C ψ hist x
      have hsum : (∑ x : Reg n, directTransitionMass n W S U C ψ hist x) ≤ 1 :=
        sum_directTransitionMass_le_one S U C ψ hC hψ hist
      simp only [cumDirectSuccess]
      calc (∑ x : Reg n,
            (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0) *
              cumDirectSuccess n W S U C ψ v (x :: hist))
          ≤ ∑ x : Reg n,
            (if S x ∧ x ∉ hist then directTransitionMass n W S U C ψ hist x else 0) * 1 := by
            apply Finset.sum_le_sum
            intro x _
            exact mul_le_mul_of_nonneg_left (ih (x :: hist)) (by
              by_cases hc : S x ∧ x ∉ hist <;> simp [hc, hmass x])
        _ ≤ ∑ x : Reg n, directTransitionMass n W S U C ψ hist x := by
            apply Finset.sum_le_sum
            intro x _
            by_cases hc : S x ∧ x ∉ hist
            · simp [hc]
            · simp [hc, hmass x]
        _ ≤ 1 := hsum

/-- A unitary circuit with normalized witness states has cumulative sampler success at most one. -/
theorem cumulativeSamplerSuccess_le_one {n q : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (C : TOCircuit (ForrSpace n W))
    (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w)) (v : ℕ) :
    cumulativeSamplerSuccess n q W S U C ψfam v ≤ 1 := by
  classical
  have hround : ∀ w : Fin q → Bool, cumDirectSuccess n W S U C (ψfam w) v [] ≤ 1 := by
    intro w
    exact cumDirectSuccess_le_one S U C (ψfam w) hC (hnorm w) v []
  unfold cumulativeSamplerSuccess
  have hcard : (Fintype.card (Fin q → Bool) : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card (Fin q → Bool) := Fintype.card_pos
    exact_mod_cast (ne_of_gt hpos)
  calc (1 / (Fintype.card (Fin q → Bool) : ℝ)) *
          ∑ w : Fin q → Bool, cumDirectSuccess n W S U C (ψfam w) v []
      ≤ (1 / (Fintype.card (Fin q → Bool) : ℝ)) * ∑ _w : Fin q → Bool, 1 := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hround w) (by positivity)
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        field_simp

/-- For nonnegative `κ`, the strong average of cumulative sampler success is at most one for a
unitary circuit with normalized witnesses. -/
theorem strongAverage_cumulativeSamplerSuccess_le_one {n q ℓ : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (κ : ℝ) (hκ : 0 ≤ κ)
    (C : TOCircuit (ForrSpace n W))
    (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w)) (v : ℕ) :
    Qatlib.Concepts.FreshFallback.BitScanLedger.strongAverage n ℓ κ
        (fun s U => cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v) ≤ 1 := by
  have hle : ∀ (s : Fin ℓ → Reg n) (U : Reg n → Bool),
      cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v ≤ 1 := by
    intro s U
    exact cumulativeSamplerSuccess_le_one (multisetInd s) U C ψfam hC hnorm v
  exact (Qatlib.Concepts.FreshFallback.BitScanLedger.strongAverage_mono n ℓ κ hκ
    (fun s U => cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v)
    (fun _ _ => 1) hle).trans
    (Qatlib.Concepts.FreshFallback.BitScanLedger.strongAverage_one n ℓ κ).le

/-- When `ℓ` and `r` are at least one, the strong average of cumulative sampler success is
bounded by the displayed occupation-product expression. -/
theorem strongAverage_cumulativeSamplerSuccess_le {n q ℓ : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (κ : ℝ) (hκ : 0 ≤ κ) (r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (C : TOCircuit (ForrSpace n W))
    (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w)) (v : ℕ) :
    Qatlib.Concepts.FreshFallback.BitScanLedger.strongAverage n ℓ κ
        (fun s U => cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
  have h1 : Qatlib.Concepts.FreshFallback.BitScanLedger.strongAverage n ℓ κ
        (fun s U => cumulativeSamplerSuccess n q W (multisetInd s) U C ψfam v) ≤ 1 :=
    strongAverage_cumulativeSamplerSuccess_le_one κ hκ C ψfam hC hnorm v
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) ^ (v - 1) := one_le_pow₀ hrR
  have hℓR : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hprod : (1 : ℝ) ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := by
    have h1 : (1 : ℝ) * 1 ≤ (ℓ : ℝ) * 1 := mul_le_mul_of_nonneg_right hℓR (by norm_num)
    have h2 : (ℓ : ℝ) * 1 ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) :=
      mul_le_mul_of_nonneg_left hr1 (by positivity)
    have h : (1 : ℝ) * (1 : ℝ) ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) := h1.trans h2
    simpa using! h
  exact h1.trans hprod

/-- The stated verifier completeness, soundness, and query bounds imply the failure-adjusted
query inequality when `ℓ` and `r` are at least one. -/
theorem clause3_queryLowerBound_hupper {n ℓ q t v : ℕ} (κ : ℝ) (hκ : 0 ≤ κ)
    (W : Type) [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)) (r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w))
    (hS : TOQueryCountS C ≤ t) (hU : TOQueryCountU C ≤ t)
    (hyes : ∀ S U : Reg n → Bool, (59 / 100 : ℝ) ≤ spectralForrelation n S U →
      ∃ w, (2 / 3 : ℝ) ≤ MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E)
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E ≤ (1 / 3 : ℝ)) :
    (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) *
        ((1 / (2 ^ q : ℝ)) * (1 / (36 * (t : ℝ) ^ 2)) ^ v)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) :=
  clause3_queryLowerBound κ hκ W C ψfam E r hC hnorm hS hU hyes hno
    (strongAverage_cumulativeSamplerSuccess_le κ hκ r hℓ hr C ψfam hC hnorm v)

/-- The stated verifier assumptions and positive parameter bounds imply the displayed lower
bound on the number of classical witnesses. -/
theorem clause3_queryExponentialLowerBound_hupper {n ℓ q t v : ℕ} (κ : ℝ) (hκ : 0 ≤ κ)
    (W : Type) [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (E : Finset (ForrSpace n W)) (r : ℕ)
    (hℓ : 0 < ℓ) (hr : 1 ≤ r) (hrℓ : r ≤ ℓ) (ht : 0 < t)
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w))
    (hS : TOQueryCountS C ≤ t) (hU : TOQueryCountU C ≤ t)
    (hyes : ∀ S U : Reg n → Bool, (59 / 100 : ℝ) ≤ spectralForrelation n S U →
      ∃ w, (2 / 3 : ℝ) ≤ MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E)
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w)) E ≤ (1 / 3 : ℝ)) :
    (2 : ℝ) ^ q ≥ (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) /
        ((ℓ : ℝ) * (r : ℝ) ^ (v - 1) * (36 * (t : ℝ) ^ 2) ^ v) :=
  clause3_queryExponentialLowerBound κ hκ W C ψfam E r hℓ hr hrℓ ht hC hnorm hS hU hyes hno
    (strongAverage_cumulativeSamplerSuccess_le κ hκ r (Nat.succ_le_iff.mp hℓ) hr
      C ψfam hC hnorm v)

/-- Summing `S`-query Born mass over a position set equals the probability that the query
register lies in that set. -/
theorem sum_sQueryBornMass_eq_measureProb {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (T : Finset (Reg n)) (φ : QState (ForrSpace n W)) :
    (∑ x ∈ T, sQueryBornMass n W φ x)
      = MeasureProb φ (Finset.univ.filter fun p : ForrSpace n W => p.1.1 ∈ T) := by
  classical
  have hL : (∑ x ∈ T, sQueryBornMass n W φ x)
      = ∑ x ∈ T, ∑ p ∈ (Finset.univ : Finset (ForrSpace n W)),
          (if p.1.1 = x then BornProb φ p else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    unfold sQueryBornMass MeasureProb
    rw [Finset.sum_filter]
  have hR : MeasureProb φ (Finset.univ.filter fun p : ForrSpace n W => p.1.1 ∈ T)
      = ∑ p ∈ (Finset.univ : Finset (ForrSpace n W)),
          (if p.1.1 ∈ T then BornProb φ p else 0) := by
    unfold MeasureProb
    rw [Finset.sum_filter]
  rw [hL, Finset.sum_comm, hR]
  refine Finset.sum_congr rfl ?_
  intro p hp
  rw [Finset.sum_ite_eq]

/-- Collision-success probability equals the sum of `S`-query Born masses over collision
positions. -/
theorem measureProb_collisionSuccessEvent {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool) (φ : QState (ForrSpace n W)) :
    MeasureProb φ (collisionSuccessEvent W S U)
      = ∑ x ∈ collisionPositions S U, sQueryBornMass n W φ x := by
  rw [collisionSuccessEvent]
  exact (sum_sQueryBornMass_eq_measureProb (collisionPositions S U) φ).symm

/-- An oracle collision supplies a nonempty set of collision positions. -/
theorem collisionPositions_nonempty {n : ℕ} (S U : Reg n → Bool) (x y : Reg n)
    (h : oracleCollision S U x y) : collisionPositions S U ≠ ∅ := by
  classical
  intro hE
  have hx : x ∈ collisionPositions S U := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    exact ⟨y, h⟩
  rw [hE] at hx
  simp at hx

/-- If the two oracles agree at at most one position, the set of collision positions is empty. -/
theorem collisionPositions_eq_empty {n : ℕ} (S U : Reg n → Bool)
    (h : ∀ x y : Reg n, S x = U x → S y = U y → x = y) :
    collisionPositions S U = ∅ := by
  classical
  ext x
  simp only [collisionPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx
    exact (hy.2.2 (h x y hy.1 hy.2.1)).elim
  · intro hx
    simp at hx

/-- If the two oracles agree at at most one position, the collision-success event is empty. -/
theorem collisionSuccessEvent_eq_empty {n : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    (S U : Reg n → Bool)
    (h : ∀ x y : Reg n, S x = U x → S y = U y → x = y) :
    collisionSuccessEvent W S U = ∅ := by
  classical
  have hpos := collisionPositions_eq_empty S U h
  ext p
  simp [collisionSuccessEvent, hpos]

/-- The verifier assumptions with the fixed collision-success event imply the displayed
failure-adjusted query inequality. -/
theorem clause3_collisionTask_queryLowerBound {n ℓ q t v : ℕ} (κ : ℝ) (hκ : 0 ≤ κ)
    {W : Type} [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (S₀ U₀ : Reg n → Bool)
    (r : ℕ) (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r)
    (hC : IsUnitaryTOCircuit C) (hnorm : ∀ w, Normalized (ψfam w))
    (hS : TOQueryCountS C ≤ t) (hU : TOQueryCountU C ≤ t)
    (hyes : ∀ S U : Reg n → Bool, (59 / 100 : ℝ) ≤ spectralForrelation n S U →
      ∃ w, (2 / 3 : ℝ) ≤ MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w))
        (collisionSuccessEvent W S₀ U₀))
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w))
        (collisionSuccessEvent W S₀ U₀) ≤ (1 / 3 : ℝ)) :
    (1 - strongFailProb n ℓ κ (57 / 100) (59 / 100) v) *
        ((1 / (2 ^ q : ℝ)) * (1 / (36 * (t : ℝ) ^ 2)) ^ v)
      ≤ (ℓ : ℝ) * (r : ℝ) ^ (v - 1) :=
  clause3_queryLowerBound_hupper κ hκ W C ψfam (collisionSuccessEvent W S₀ U₀) r hℓ hr
    hC hnorm hS hU hyes hno

/-- The assumed soundness bound implies collision-success probability at most
`qmaqcmaBaselineConstant` on instances below `qmaqcmaNoThreshold`. -/
theorem clause3_collisionTask_noInstance_bound {n q : ℕ}
    {W : Type} [Fintype W] [DecidableEq W]
    (C : TOCircuit (ForrSpace n W)) (ψfam : (Fin q → Bool) → QState (ForrSpace n W))
    (S₀ U₀ S U : Reg n → Bool)
    (hno : ∀ S U : Reg n → Bool, spectralForrelation n S U ≤ (57 / 100 : ℝ) →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w))
        (collisionSuccessEvent W S₀ U₀) ≤ (1 / 3 : ℝ)) :
    spectralForrelation n S U ≤ qmaqcmaNoThreshold →
      ∀ w, MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w))
        (collisionSuccessEvent W S₀ U₀) ≤ qmaqcmaBaselineConstant := by
  intro hNO w
  have h1 : MeasureProb
        (TORun (forrPhaseOracleS n S W) (forrPhaseOracleU n U W) C (ψfam w))
        (collisionSuccessEvent W S₀ U₀) ≤ (1 / 3 : ℝ) :=
    hno S U (le_trans hNO (by unfold qmaqcmaNoThreshold; norm_num)) w
  have h2 : (1 / 3 : ℝ) ≤ qmaqcmaBaselineConstant := by
    unfold qmaqcmaBaselineConstant
    norm_num
  linarith

end Qatlib.Papers.QMAvsQCMA25.Forrelation.CompressedQueryDynamics
