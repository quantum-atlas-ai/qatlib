/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.ShadowModels.BooleanCubeFourier
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
public import Qatlib.Papers.Trainability23.VarianceScaling.CorrelationMass

@[expose] public section
open Qatlib.Concepts.ShadowModels.BooleanCubeFourier Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.Trainability23.VarianceScaling

namespace Qatlib.Papers.MixednessTest26.PauliShadow

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

noncomputable def krawtchoukStatistic {N : ℕ} (k n : ℕ) (xs ys : Fin n → Reg N) : ℝ :=
  (∑ i, ∑ j, krawtchouk N k (cubeDist (xs i) (ys j))) / (n : ℝ) ^ 2

noncomputable def krawtCheckMass {N : ℕ} (p : FinDist (Reg N)) (n M : ℕ)
    (s : Fin M → (Fin n → Reg N) × (Fin n → Reg N)) : ℝ :=
  ∏ m, p.probOf (s m).1 * p.probOf (s m).2

noncomputable def krawtCheckHalfCount (N k : ℕ) (Δ β : ℝ) : ℕ :=
  ⌈400 * Real.sqrt (2 * (Nat.choose N k : ℝ)) / (β * Δ)⌉₊

noncomputable def krawtCheckBlockCount (δ : ℝ) : ℕ := ⌈16 * Real.log (1 / δ)⌉₊

noncomputable def krawtCheckAccepts {N : ℕ} (k n M : ℕ) (Δ β : ℝ)
    (s : Fin M → (Fin n → Reg N) × (Fin n → Reg N)) : Prop :=
  M - M / 2 ≤ ∑ m, if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0

/-- Expresses a Krawtchouk polynomial evaluated at cube distance as a sum of products of
weight-`k` characters. -/
private theorem krawtchouk_char_pair {N k : ℕ} (a b : Reg N) :
    krawtchouk N k (cubeDist a b)
      = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          cubeChar S a * cubeChar S b := by
  show krawtchouk N k (cubeWeight fun i => a i == b i) = _
  rw [← krawtchouk_char_sum (fun i => a i == b i)]
  exact Finset.sum_congr rfl fun S _ => (cubeChar_pair S a b).symm

/-- Rewrites the pairwise Krawtchouk sum as a sum of products of sample character sums. -/
private theorem statistic_sum_eq {N k n : ℕ} (xs ys : Fin n → Reg N) :
    (∑ i, ∑ j, krawtchouk N k (cubeDist (xs i) (ys j)))
      = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          (∑ i, cubeChar S (xs i)) * (∑ j, cubeChar S (ys j)) := by
  classical
  have h1 : ∀ i j : Fin n, krawtchouk N k (cubeDist (xs i) (ys j))
      = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          cubeChar S (xs i) * cubeChar S (ys j) :=
    fun i j => krawtchouk_char_pair (xs i) (ys j)
  calc (∑ i, ∑ j, krawtchouk N k (cubeDist (xs i) (ys j)))
      = ∑ i, ∑ j, ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          cubeChar S (xs i) * cubeChar S (ys j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h1 i j
    _ = ∑ i : Fin n, ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          ∑ j : Fin n, cubeChar S (xs i) * cubeChar S (ys j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          ∑ i : Fin n, ∑ j : Fin n, cubeChar S (xs i) * cubeChar S (ys j) :=
        Finset.sum_comm
    _ = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          (∑ i, cubeChar S (xs i)) * (∑ j, cubeChar S (ys j)) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        exact (Finset.sum_mul_sum (Finset.univ : Finset (Fin n))
          (Finset.univ : Finset (Fin n))
          (fun i => cubeChar S (xs i)) (fun j => cubeChar S (ys j))).symm

/-- Shows that the Krawtchouk statistic is an unbiased estimator of the weight-`k` squared
correlation mass for positive sample size. -/
theorem krawtchoukStatistic_unbiased {N k : ℕ} (p : FinDist (Reg N)) {n : ℕ} (hn : 0 < n) :
    ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (p.probOf b.1 * p.probOf b.2) * krawtchoukStatistic k n b.1 b.2
      = cubeAlphaWeightMass p k := by
  classical

  have hmarg : ∀ (S : Finset (Fin N)) (i : Fin n),
      ∑ xs : Fin n → Reg N, p.probOf xs * cubeChar S (xs i) = cubeAlpha p S :=
    fun S i => expect_coord p i (cubeChar S)

  have hmargA : ∀ S : Finset (Fin N),
      ∑ xs : Fin n → Reg N, p.probOf xs * (∑ i, cubeChar S (xs i))
        = (n : ℝ) * cubeAlpha p S := by
    intro S
    have h1 : ∀ xs : Fin n → Reg N, p.probOf xs * (∑ i : Fin n, cubeChar S (xs i))
        = ∑ i : Fin n, p.probOf xs * cubeChar S (xs i) :=
      fun xs => Finset.mul_sum ..
    rw [Finset.sum_congr rfl fun xs _ => h1 xs, Finset.sum_comm,
      Finset.sum_congr rfl fun i _ => hmarg S i, Finset.sum_const, nsmul_eq_mul',
      Finset.card_univ, Fintype.card_fin, mul_comm]

  have hsplit : ∀ S : Finset (Fin N),
      ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (p.probOf b.1 * p.probOf b.2)
            * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
        = ((n : ℝ) * cubeAlpha p S) * ((n : ℝ) * cubeAlpha p S) := by
    intro S
    have hfac : ∀ xs ys : Fin n → Reg N,
        (p.probOf (xs, ys).1 * p.probOf (xs, ys).2)
            * ((∑ i, cubeChar S ((xs, ys).1 i)) * (∑ j, cubeChar S ((xs, ys).2 j)))
          = (p.probOf xs * (∑ i, cubeChar S (xs i)))
              * (p.probOf ys * (∑ j, cubeChar S (ys j))) := by
      intro xs ys
      show (p.probOf xs * p.probOf ys)
          * ((∑ i, cubeChar S (xs i)) * (∑ j, cubeChar S (ys j)))
          = (p.probOf xs * (∑ i, cubeChar S (xs i)))
              * (p.probOf ys * (∑ j, cubeChar S (ys j)))
      ring
    calc ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (p.probOf b.1 * p.probOf b.2)
            * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
        = ∑ xs : Fin n → Reg N, ∑ ys : Fin n → Reg N,
            (p.probOf xs * (∑ i, cubeChar S (xs i)))
              * (p.probOf ys * (∑ j, cubeChar S (ys j))) := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun xs _ =>
            Finset.sum_congr rfl fun ys _ => hfac xs ys
      _ = (∑ xs : Fin n → Reg N, p.probOf xs * (∑ i, cubeChar S (xs i)))
            * (∑ ys : Fin n → Reg N, p.probOf ys * (∑ j, cubeChar S (ys j))) :=
            (Finset.sum_mul_sum (Finset.univ : Finset (Fin n → Reg N))
              (Finset.univ : Finset (Fin n → Reg N))
              (fun xs => p.probOf xs * (∑ i, cubeChar S (xs i)))
              (fun ys => p.probOf ys * (∑ j, cubeChar S (ys j)))).symm
      _ = ((n : ℝ) * cubeAlpha p S) * ((n : ℝ) * cubeAlpha p S) := by
          rw [hmargA S]

  calc ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (p.probOf b.1 * p.probOf b.2) * krawtchoukStatistic k n b.1 b.2
      = ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (p.probOf b.1 * p.probOf b.2)
            * ((∑ i, ∑ j, krawtchouk N k (cubeDist (b.1 i) (b.2 j))) / (n : ℝ) ^ 2) :=
        Finset.sum_congr rfl fun b _ => rfl
    _ = (∑ b : (Fin n → Reg N) × (Fin n → Reg N), (p.probOf b.1 * p.probOf b.2)
          * (∑ i, ∑ j, krawtchouk N k (cubeDist (b.1 i) (b.2 j)))) / (n : ℝ) ^ 2 := by
        have hps : ∀ b : (Fin n → Reg N) × (Fin n → Reg N),
            (p.probOf b.1 * p.probOf b.2)
              * ((∑ i, ∑ j, krawtchouk N k (cubeDist (b.1 i) (b.2 j))) / (n : ℝ) ^ 2)
            = (p.probOf b.1 * p.probOf b.2)
                * (∑ i, ∑ j, krawtchouk N k (cubeDist (b.1 i) (b.2 j))) / (n : ℝ) ^ 2 :=
          fun b => (mul_div_assoc _ _ _).symm
        rw [Finset.sum_congr rfl (fun b _ => hps b)]
        exact (Finset.sum_div (Finset.univ :
          Finset ((Fin n → Reg N) × (Fin n → Reg N)))
          (fun b => (p.probOf b.1 * p.probOf b.2)
            * (∑ i, ∑ j, krawtchouk N k (cubeDist (b.1 i) (b.2 j)))) ((n : ℝ) ^ 2)).symm
    _ = (∑ b : (Fin n → Reg N) × (Fin n → Reg N), (p.probOf b.1 * p.probOf b.2)
          * ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
              (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))) / (n : ℝ) ^ 2 := by
        refine congrArg (fun t : ℝ => t / (n : ℝ) ^ 2) ?_
        exact Finset.sum_congr rfl fun b _ => by rw [statistic_sum_eq b.1 b.2]
    _ = (∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          ∑ b : (Fin n → Reg N) × (Fin n → Reg N), (p.probOf b.1 * p.probOf b.2)
            * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))) / (n : ℝ) ^ 2 := by
        refine congrArg (fun t : ℝ => t / (n : ℝ) ^ 2) ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_comm
    _ = (∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          ((n : ℝ) * cubeAlpha p S) * ((n : ℝ) * cubeAlpha p S)) / (n : ℝ) ^ 2 := by
        refine congrArg (fun t : ℝ => t / (n : ℝ) ^ 2) ?_
        exact Finset.sum_congr rfl fun S _ => hsplit S
    _ = ((n : ℝ) ^ 2 * ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
          (cubeAlpha p S) ^ 2) / (n : ℝ) ^ 2 := by
        refine congrArg (fun t : ℝ => t / (n : ℝ) ^ 2) ?_
        have h6 : ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
              ((n : ℝ) * cubeAlpha p S) * ((n : ℝ) * cubeAlpha p S)
            = (n : ℝ) ^ 2 * ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
                (cubeAlpha p S) ^ 2 := by
          calc ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
                ((n : ℝ) * cubeAlpha p S) * ((n : ℝ) * cubeAlpha p S)
              = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
                  (n : ℝ) ^ 2 * (cubeAlpha p S) ^ 2 :=
                Finset.sum_congr rfl fun S _ => by ring
            _ = (n : ℝ) ^ 2 * ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k),
                  (cubeAlpha p S) ^ 2 := (Finset.mul_sum _ _ _).symm
        rw [h6]
    _ = ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k), (cubeAlpha p S) ^ 2 := by
        rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 (by exact_mod_cast hn.ne'))]

end Qatlib.Papers.MixednessTest26.PauliShadow

namespace Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

open scoped Classical symmDiff

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open scoped Classical symmDiff

private noncomputable def cubeBlockDist {N : ℕ} (p : FinDist (Reg N)) (n : ℕ) :
    FinDist ((Fin n → Reg N) × (Fin n → Reg N)) where
  prob b := p.probOf b.1 * p.probOf b.2
  nonneg b := mul_nonneg (Finset.prod_nonneg fun i _ => p.nonneg _)
    (Finset.prod_nonneg fun i _ => p.nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    have hsplit : (∑ xs : Fin n → Reg N, ∑ ys : Fin n → Reg N,
          p.probOf (xs, ys).1 * p.probOf (xs, ys).2)
        = (∑ xs : Fin n → Reg N, p.probOf xs) * (∑ ys : Fin n → Reg N, p.probOf ys) := by
      rw [← Finset.sum_mul_sum]
    rw [hsplit, p.sum_probOf, one_mul]

/-- Identifies the Krawtchouk check sample mass with the product probability under
`cubeBlockDist`. -/
private theorem krawtCheckMass_eq {N : ℕ} (p : FinDist (Reg N)) (n M : ℕ)
    (s : Fin M → (Fin n → Reg N) × (Fin n → Reg N)) :
    krawtCheckMass p n M s = (cubeBlockDist p n).probOf s := rfl

/-- Evaluates a finite product whose only potentially nonunit factors occur at two distinct
indices. -/
private theorem prod_univ_two {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ)
    (F : Fin n → ℝ) (hi : F i = a) (hj : F j = b)
    (hrest : ∀ m, m ≠ i → m ≠ j → F m = 1) : ∏ m, F m = a * b := by
  classical
  have hmem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
  have hsplit : ∏ m, F m = (∏ m ∈ Finset.univ.erase i, F m) * F i := by
    conv_lhs => rw [← Finset.insert_erase
      (Finset.mem_univ i : i ∈ (Finset.univ : Finset (Fin n)))]
    rw [Finset.prod_insert
      (Finset.notMem_erase i (Finset.univ : Finset (Fin n)))]
    ring
  have hjmem : j ∈ Finset.univ.erase i := by
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hij, Finset.mem_univ j⟩
  have hinner : ∏ m ∈ Finset.univ.erase i, F m = F j :=
    Finset.prod_eq_single (s := (Finset.univ : Finset (Fin n)).erase i)
      (f := F) (a := j)
      (fun m hm hmn => hrest m (Finset.mem_erase.mp hm).1 hmn)
      (fun hnj => absurd hjmem hnj)
  rw [hsplit, hinner, hj, hi]
  exact mul_comm b a

/-- Factors the expectation of functions of two distinct independent sample coordinates into
their individual expectations. -/
private theorem expect_two_coord {X : Type*} [Fintype X] [DecidableEq X] {L : ℕ}
    (p : FinDist X) (f g : X → ℝ) (i j : Fin L) (hij : i ≠ j) :
    ∑ ω : Fin L → X, p.probOf ω * f (ω i) * g (ω j)
      = (∑ x, p.prob x * f x) * (∑ x, p.prob x * g x) := by
  classical
  set G : Fin L → X → ℝ :=
    fun m x => if m = i then f x else if m = j then g x else 1 with hGdef
  have hGi : ∀ x : X, G i x = f x := by
    intro x
    show (if i = i then f x else if i = j then g x else 1) = f x
    rw [ite_eq_left rfl]
  have hGj : ∀ x : X, G j x = g x := by
    intro x
    show (if j = i then f x else if j = j then g x else 1) = g x
    rw [ite_eq_right (Ne.symm hij), ite_eq_left rfl]
  have hGm : ∀ m : Fin L, m ≠ i → m ≠ j → ∀ x : X, G m x = 1 := by
    intro m hmi hmj x
    show (if m = i then f x else if m = j then g x else 1) = 1
    rw [ite_eq_right hmi, ite_eq_right hmj]
  have hprodω : ∀ ω : Fin L → X, ∏ m, G m (ω m) = f (ω i) * g (ω j) := by
    intro ω
    refine prod_univ_two i j hij (f (ω i)) (g (ω j)) (fun m => G m (ω m)) ?_ ?_ ?_
    · exact hGi (ω i)
    · exact hGj (ω j)
    · intro m hmi hmj; exact hGm m hmi hmj (ω m)
  have hfactor : ∀ m : Fin L,
      (∑ x, p.prob x * G m x)
        = if m = i then ∑ x, p.prob x * f x
          else if m = j then ∑ x, p.prob x * g x else 1 := by
    intro m
    by_cases hmi : m = i
    · rw [ite_eq_left hmi]
      exact Finset.sum_congr rfl fun x _ => by rw [hmi, hGi x]
    · by_cases hmj : m = j
      · rw [ite_eq_right hmi, ite_eq_left hmj]
        exact Finset.sum_congr rfl fun x _ => by rw [hmj, hGj x]
      · rw [ite_eq_right hmi, ite_eq_right hmj]
        rw [Finset.sum_congr rfl fun x _ => by rw [hGm m hmi hmj x, mul_one], p.sum_one]
  have hprodF : (∏ m, ∑ x, p.prob x * G m x)
      = (∑ x, p.prob x * f x) * (∑ x, p.prob x * g x) := by
    refine prod_univ_two i j hij _ _ (fun m => ∑ x, p.prob x * G m x) ?_ ?_ ?_
    · show (∑ x, p.prob x * G i x) = (∑ x, p.prob x * f x)
      exact Finset.sum_congr rfl fun x _ => by rw [hGi x]
    · show (∑ x, p.prob x * G j x) = (∑ x, p.prob x * g x)
      exact Finset.sum_congr rfl fun x _ => by rw [hGj x]
    · intro m hmi hmj
      show (∑ x, p.prob x * G m x) = 1
      rw [hfactor m, ite_eq_right hmi, ite_eq_right hmj]
  calc ∑ ω : Fin L → X, p.probOf ω * f (ω i) * g (ω j)
      = ∑ ω : Fin L → X, p.probOf ω * ∏ m, G m (ω m) :=
        Finset.sum_congr rfl fun ω _ => by rw [hprodω ω]; ring
    _ = ∏ m, ∑ x, p.prob x * G m x := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod p G
    _ = (∑ x, p.prob x * f x) * (∑ x, p.prob x * g x) := hprodF

end Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

namespace Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

/-- Bounds the probability of an absolute-value tail by the second moment divided by the squared
positive threshold. -/
private theorem markov_abs_tail {X : Type*} [Fintype X] (q : FinDist X)
    (f : X → ℝ) (t : ℝ) (ht : 0 < t) :
    ∑ x ∈ Finset.univ.filter (fun x => t ≤ |f x|), q.prob x
      ≤ (∑ x, q.prob x * f x ^ 2) / t ^ 2 := by
  have hnn : ∀ x : X, 0 ≤ q.prob x := q.nonneg
  have hstep1 : ∀ x ∈ Finset.univ.filter (fun x => t ≤ |f x|),
      q.prob x ≤ q.prob x * f x ^ 2 / t ^ 2 := by
    intro x hx
    have hlt : t ≤ |f x| := (Finset.mem_filter.mp hx).2
    have hxnn : 0 ≤ |f x| := abs_nonneg _
    have hd : t ^ 2 ≤ f x ^ 2 := by nlinarith [hlt, hxnn, sq_abs (f x)]
    calc q.prob x = q.prob x * 1 := by ring
      _ ≤ q.prob x * (f x ^ 2 / t ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hnn x)
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < t ^ 2), one_mul]
          exact hd
      _ = q.prob x * f x ^ 2 / t ^ 2 := by ring
  have hsplit : (∑ x ∈ Finset.univ.filter (fun x => t ≤ |f x|), q.prob x * f x ^ 2)
      ≤ ∑ x, q.prob x * f x ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => mul_nonneg (hnn x) (sq_nonneg _))
  calc ∑ x ∈ Finset.univ.filter (fun x => t ≤ |f x|), q.prob x
      ≤ ∑ x ∈ Finset.univ.filter (fun x => t ≤ |f x|), q.prob x * f x ^ 2 / t ^ 2 :=
        Finset.sum_le_sum fun x hx => hstep1 x hx
    _ = (∑ x ∈ Finset.univ.filter (fun x => t ≤ |f x|), q.prob x * f x ^ 2) / t ^ 2 :=
        (Finset.sum_div _ _ _).symm
    _ ≤ (∑ x, q.prob x * f x ^ 2) / t ^ 2 := by
        exact div_le_div_of_nonneg_right hsplit (sq_nonneg t)

end Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

namespace Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

/-- Computes uniform cube correlations as one for the empty set and zero for every nonempty set. -/
theorem cubeAlpha_uniform_eq {N : ℕ} (S : Finset (Fin N)) :
    cubeAlpha (cubeUniformDist N) S = if S = ∅ then 1 else 0 := by
  classical
  set r : FinDist Bool :=
    ⟨fun _ => 1 / 2, fun _ => by positivity, by
      show (∑ _b : Bool, (1 / 2 : ℝ)) = 1
      simp only [Fintype.sum_bool]
      norm_num⟩ with hrdef
  have hrprob : ∀ b : Bool, r.prob b = 1 / 2 := by
    intro b; rw [hrdef]
  have hprob : ∀ x : Reg N, (cubeUniformDist N).prob x = r.probOf x := by
    intro x
    rw [hrdef, Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf]
    show ((1 / 2 : ℝ)) ^ N = ∏ i : Fin N, (1 / 2 : ℝ)
    rw [Finset.prod_const]
    simp [Fintype.card_fin]
  have hchar : ∀ x : Reg N, cubeChar S x
      = ∏ i : Fin N, (if i ∈ S then (if x i then (1 : ℝ) else -1) else 1) := by
    intro x
    show (∏ i ∈ S, (if x i then (1 : ℝ) else -1))
        = ∏ i : Fin N, (if i ∈ S then (if x i then (1 : ℝ) else -1) else 1)
    calc (∏ i ∈ S, (if x i then (1 : ℝ) else -1))
        = ∏ i ∈ S, (if i ∈ S then (if x i then (1 : ℝ) else -1) else 1) :=
          Finset.prod_congr rfl fun i hi => by rw [ite_eq_left hi]
      _ = ∏ i : Fin N, (if i ∈ S then (if x i then (1 : ℝ) else -1) else 1) :=
          Finset.prod_subset (S.subset_univ) (fun i _ hi => ite_eq_right hi)
  have hrw : ∀ i : Fin N, (∑ b : Bool, r.prob b *
        (if i ∈ S then (if b then (1 : ℝ) else -1) else 1))
      = ∑ b : Bool, (1 / 2 : ℝ) *
          (if i ∈ S then (if b then (1 : ℝ) else -1) else 1) :=
    fun i => Finset.sum_congr rfl fun b _ => by rw [hrprob b]
  have hval : ∀ i : Fin N, (∑ b : Bool, (1 / 2 : ℝ) *
        (if i ∈ S then (if b then (1 : ℝ) else -1) else 1))
      = if i ∈ S then 0 else 1 := by
    intro i
    by_cases hiS : i ∈ S
    · have heq : ∀ b : Bool,
          ((if i ∈ S then (if b then (1 : ℝ) else -1) else 1))
            = (if b then (1 : ℝ) else -1) := fun b => ite_eq_left hiS
      rw [Finset.sum_congr rfl (fun b _ => by rw [heq b]), ite_eq_left hiS]
      show (∑ b : Bool, (1 / 2 : ℝ) * (if b then (1 : ℝ) else -1)) = 0
      simp only [Fintype.sum_bool]
      norm_num
    · have heq : ∀ b : Bool,
          ((if i ∈ S then (if b then (1 : ℝ) else -1) else 1))
            = (1 : ℝ) := fun b => ite_eq_right hiS
      rw [Finset.sum_congr rfl (fun b _ => by rw [heq b]), ite_eq_right hiS]
      show (∑ b : Bool, (1 / 2 : ℝ) * (1 : ℝ)) = 1
      simp only [Fintype.sum_bool, mul_one]
      norm_num
  calc cubeAlpha (cubeUniformDist N) S
      = ∑ x : Reg N, (cubeUniformDist N).prob x * cubeChar S x := rfl
    _ = ∑ x : Reg N, r.probOf x * cubeChar S x :=
        Finset.sum_congr rfl fun x _ => by rw [hprob x]
    _ = ∑ x : Reg N, r.probOf x
          * ∏ i : Fin N, (if i ∈ S then (if x i then (1 : ℝ) else -1) else 1) :=
        Finset.sum_congr rfl fun x _ => by rw [hchar x]
    _ = ∏ i : Fin N, ∑ b : Bool, r.prob b *
          (if i ∈ S then (if b then (1 : ℝ) else -1) else 1) :=
        Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod r (fun i b => if i ∈ S then (if b then 1 else -1) else 1)
    _ = ∏ i : Fin N, (if i ∈ S then (0 : ℝ) else 1) :=
        Finset.prod_congr rfl fun i _ => (hrw i).trans (hval i)
    _ = if S = ∅ then 1 else 0 := by
        rcases Finset.eq_empty_or_nonempty S with hS | hne
        · subst hS
          have hall : ∀ i : Fin N,
              (if i ∈ (∅ : Finset (Fin N)) then (0 : ℝ) else 1) = 1 :=
            fun i => ite_eq_right (Finset.notMem_empty i)
          rw [ite_eq_left rfl, Finset.prod_congr rfl (fun i _ => hall i),
            Finset.prod_const_one]
        · obtain ⟨i₀, hi₀⟩ := hne
          have hSne : S ≠ ∅ := fun h => Finset.notMem_empty i₀ (h ▸ hi₀)
          rw [ite_eq_right hSne,
            Finset.prod_eq_zero (f := fun i => if i ∈ S then (0 : ℝ) else 1)
              (Finset.mem_univ i₀) (ite_eq_left hi₀)]

end Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

namespace Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

open scoped symmDiff

/-- Computes the mixed second moment of two sample character sums using their
symmetric-difference correlation. -/
private theorem char_pair_moment {N : ℕ} (p : FinDist (Reg N))
    (S T : Finset (Fin N)) (n : ℕ) :
    ∑ xs : Fin n → Reg N, p.probOf xs
        * (∑ i, cubeChar S (xs i)) * (∑ j, cubeChar T (xs j))
      = (n : ℝ) * cubeAlpha p (S ∆ T)
        + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T := by
  classical
  have hmul : ∀ xs : Fin n → Reg N,
      p.probOf xs * (∑ i, cubeChar S (xs i)) * (∑ j, cubeChar T (xs j))
        = ∑ i, ∑ j, p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs j)) := by
    intro xs
    have hassoc : p.probOf xs * (∑ i, cubeChar S (xs i)) * (∑ j, cubeChar T (xs j))
        = p.probOf xs * ((∑ i, cubeChar S (xs i)) * (∑ j, cubeChar T (xs j))) := by
      ring
    rw [hassoc, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.mul_sum (Finset.univ : Finset (Fin n))
        (fun j => cubeChar S (xs i) * cubeChar T (xs j)) (p.probOf xs)
  have hdiag : ∀ i : Fin n, ∑ xs : Fin n → Reg N,
      p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs i))
        = cubeAlpha p (S ∆ T) := by
    intro i
    have hch : ∀ x : Reg N, cubeChar S x * cubeChar T x = cubeChar (S ∆ T) x :=
      fun x => cubeChar_mul S T x
    calc ∑ xs : Fin n → Reg N, p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs i))
        = ∑ xs : Fin n → Reg N, p.probOf xs * cubeChar (S ∆ T) (xs i) :=
          Finset.sum_congr rfl fun xs _ => by rw [hch (xs i)]
      _ = ∑ x : Reg N, p.prob x * cubeChar (S ∆ T) x := Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_coord p i _
      _ = cubeAlpha p (S ∆ T) := rfl
  have hoff : ∀ i : Fin n, ∀ j : Fin n, i ≠ j →
      (∑ xs : Fin n → Reg N, p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs j)))
        = cubeAlpha p S * cubeAlpha p T := by
    intro i j hij
    have h2 := expect_two_coord p (cubeChar S) (cubeChar T) i j hij
    calc (∑ xs : Fin n → Reg N, p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs j)))
        = ∑ xs : Fin n → Reg N,
            p.probOf xs * cubeChar S (xs i) * cubeChar T (xs j) :=
          Finset.sum_congr rfl fun xs _ => by ring
      _ = (∑ x : Reg N, p.prob x * cubeChar S x) * (∑ x : Reg N, p.prob x * cubeChar T x) :=
          h2
      _ = cubeAlpha p S * cubeAlpha p T := rfl
  have hcount : ∀ (A B : ℝ), (∑ i : Fin n, ∑ j : Fin n, (if i = j then A else B))
      = (n : ℝ) * A + ((n : ℝ) ^ 2 - (n : ℝ)) * B := by
    intro A B
    have hsplit : ∀ i j : Fin n,
        ((if i = j then A else B) : ℝ) = ((if i = j then A - B else 0) : ℝ) + B := by
      intro i j
      by_cases h : i = j <;> simp only [h, ite_true, ite_false] <;> ring
    have h1 : ∀ i : Fin n,
        (∑ j : Fin n, ((if i = j then A - B else 0) : ℝ)) = A - B := by
      intro i
      rw [Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => if i = j then A - B else 0) (a := i)
        (fun j _ hji => ite_eq_right (fun h => hji h.symm))
        (fun hni => absurd (Finset.mem_univ i) hni), ite_eq_left rfl]
    have hnb : ∑ i : Fin n, ∑ j : Fin n, B = (n : ℝ) * ((n : ℝ) * B) := by
      rw [Finset.sum_const, Finset.sum_const]
      simp [Finset.card_univ, Fintype.card_fin]
    calc (∑ i : Fin n, ∑ j : Fin n, (if i = j then A else B))
        = ∑ i : Fin n, ∑ j : Fin n,
            (((if i = j then A - B else 0) : ℝ) + B) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
      _ = (∑ i : Fin n, ∑ j : Fin n, ((if i = j then A - B else 0) : ℝ))
            + (∑ i : Fin n, ∑ j : Fin n, B) := by
            simp only [Finset.sum_add_distrib]
      _ = (∑ i : Fin n, (A - B)) + ((n : ℝ) * ((n : ℝ) * B)) := by
          rw [Finset.sum_congr rfl fun i _ => h1 i, hnb]
      _ = (n : ℝ) * A + ((n : ℝ) ^ 2 - (n : ℝ)) * B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul']
          ring
  calc (∑ xs : Fin n → Reg N, p.probOf xs * (∑ i, cubeChar S (xs i))
          * (∑ j, cubeChar T (xs j)))
      = ∑ xs : Fin n → Reg N, ∑ i, ∑ j,
          p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs j)) :=
        Finset.sum_congr rfl fun xs _ => hmul xs
    _ = ∑ i, ∑ j, ∑ xs : Fin n → Reg N,
          p.probOf xs * (cubeChar S (xs i) * cubeChar T (xs j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j,
          (if i = j then cubeAlpha p (S ∆ T) else cubeAlpha p S * cubeAlpha p T) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        by_cases hij : i = j
        · rw [ite_eq_left hij, hij]
          exact hdiag j
        · rw [ite_eq_right hij, hoff i j hij]
    _ = (n : ℝ) * cubeAlpha p (S ∆ T)
          + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T :=
        (hcount (cubeAlpha p (S ∆ T)) (cubeAlpha p S * cubeAlpha p T)).trans (by ring)

end Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

namespace Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube

open scoped symmDiff

/-- Expresses the second moment of the block Krawtchouk statistic as a normalized sum of squared
character moment expressions. -/
private theorem block_second_moment {N k n : ℕ} (p : FinDist (Reg N)) :
    ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist p n).prob b * krawtchoukStatistic k n b.1 b.2 ^ 2
      = (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
          ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
          ((n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2)
        / (n : ℝ) ^ 4 := by
  classical
  have hW : ∀ b : (Fin n → Reg N) × (Fin n → Reg N),
      krawtchoukStatistic k n b.1 b.2
        = (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
            (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))) / (n : ℝ) ^ 2 := by
    intro b
    show (∑ i, ∑ j, krawtchouk N k (cubeDist (b.1 i) (b.2 j))) / (n : ℝ) ^ 2 = _
    rw [statistic_sum_eq]
  have hfix : ∀ S T : Finset (Fin N),
      (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (cubeBlockDist p n).prob b
            * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
            * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))
        = ((n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2 := by
    intro S T
    have hm := char_pair_moment p S T n
    have hA : (∑ xs : Fin n → Reg N, p.probOf xs
          * ((∑ i, cubeChar S (xs i)) * (∑ i, cubeChar T (xs i))))
        = (n : ℝ) * cubeAlpha p (S ∆ T)
          + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T := by
      calc (∑ xs : Fin n → Reg N, p.probOf xs
            * ((∑ i, cubeChar S (xs i)) * (∑ i, cubeChar T (xs i))))
          = (∑ xs : Fin n → Reg N,
              p.probOf xs * (∑ i, cubeChar S (xs i)) * (∑ i, cubeChar T (xs i))) :=
            Finset.sum_congr rfl fun xs _ => by ring
        _ = (n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T := hm
    calc (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (cubeBlockDist p n).prob b
            * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
            * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))
        = (∑ xs : Fin n → Reg N, ∑ ys : Fin n → Reg N,
            (p.probOf xs * p.probOf ys)
              * ((∑ i, cubeChar S (xs i)) * (∑ j, cubeChar S (ys j)))
              * ((∑ i, cubeChar T (xs i)) * (∑ j, cubeChar T (ys j)))) := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun xs _ => Finset.sum_congr rfl fun ys _ => rfl
      _ = (∑ xs : Fin n → Reg N, p.probOf xs
              * ((∑ i, cubeChar S (xs i)) * (∑ i, cubeChar T (xs i))))
            * (∑ ys : Fin n → Reg N, p.probOf ys
              * ((∑ j, cubeChar S (ys j)) * (∑ j, cubeChar T (ys j)))) := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun xs _ => Finset.sum_congr rfl fun ys _ => by ring
      _ = ((n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2 := by
          rw [hA]
          ring
  calc ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist p n).prob b * krawtchoukStatistic k n b.1 b.2 ^ 2
      = (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (cubeBlockDist p n).prob b
            * ((∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
              * (∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                (∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j)))))
          / (n : ℝ) ^ 4 := by
        have hE : ∀ b : (Fin n → Reg N) × (Fin n → Reg N),
            (cubeBlockDist p n).prob b * krawtchoukStatistic k n b.1 b.2 ^ 2
              = (cubeBlockDist p n).prob b
                  * ((∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                      (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
                    * (∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                      (∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))
                  / (n : ℝ) ^ 4 := by
          intro b
          rw [hW b, div_pow, sq]
          ring
        rw [Finset.sum_congr rfl (fun b _ => hE b), Finset.sum_div]
    _ = (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
          ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
          ((n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2)
        / (n : ℝ) ^ 4 := by
        have hinner : ∀ b : (Fin n → Reg N) × (Fin n → Reg N),
            (cubeBlockDist p n).prob b
              * ((∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                  (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
                * (∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                  (∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))
              = ∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                  ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                  (cubeBlockDist p n).prob b
                    * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))
                      * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j)))) := by
          intro b
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun S _ =>
            Finset.mul_sum (Finset.univ.powerset.filter (fun s => s.card = k))
              (fun T => (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))
                * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))
              ((cubeBlockDist p n).prob b)
        congr 1
        calc (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
              (cubeBlockDist p n).prob b
                * ((∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                    (∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
                  * (∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                    (∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j)))))
            = (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
                ∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
                (cubeBlockDist p n).prob b
                  * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))
                    * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))) :=
              Finset.sum_congr rfl fun b _ => hinner b
          _ = (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
              ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
              ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
                (cubeBlockDist p n).prob b
                  * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))
                    * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j))))) := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun S _ => Finset.sum_comm
          _ = (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
              ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
              ((n : ℝ) * cubeAlpha p (S ∆ T)
                + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2) := by
              refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
              calc (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
                    (cubeBlockDist p n).prob b
                      * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j))
                        * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j)))))
                  = (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
                      (cubeBlockDist p n).prob b
                        * ((∑ i, cubeChar S (b.1 i)) * (∑ j, cubeChar S (b.2 j)))
                        * ((∑ i, cubeChar T (b.1 i)) * (∑ j, cubeChar T (b.2 j)))) :=
                    Finset.sum_congr rfl fun b _ => by ring
                _ = ((n : ℝ) * cubeAlpha p (S ∆ T)
                      + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2 :=
                    hfix S T

/-- Computes the block Krawtchouk statistic's mean as the weight-`k` squared correlation mass
for positive sample size. -/
private theorem block_mean {N k n : ℕ} (p : FinDist (Reg N)) (hn : 0 < n) :
    ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist p n).prob b * krawtchoukStatistic k n b.1 b.2
      = cubeAlphaWeightMass p k :=
  krawtchoukStatistic_unbiased p hn

/-- Computes the uniform block statistic's second moment as the binomial coefficient divided by
the squared sample size for positive `k`. -/
private theorem uniform_second_moment {N k n : ℕ} (hk : 1 ≤ k) :
    ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist (cubeUniformDist N) n).prob b
          * krawtchoukStatistic k n b.1 b.2 ^ 2
      = (Nat.choose N k : ℝ) / (n : ℝ) ^ 2 := by
  classical
  have hsecond : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist (cubeUniformDist N) n).prob b
          * krawtchoukStatistic k n b.1 b.2 ^ 2)
      = (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
          ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
          ((n : ℝ) * cubeAlpha (cubeUniformDist N) (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ))
                * cubeAlpha (cubeUniformDist N) S * cubeAlpha (cubeUniformDist N) T) ^ 2)
        / (n : ℝ) ^ 4 :=
    block_second_moment (cubeUniformDist N)
  set Lv : Finset (Finset (Fin N)) :=
    Finset.univ.powerset.filter (fun s => s.card = k) with hLv
  have hne : ∀ S ∈ Lv, S ≠ ∅ := by
    intro S hS hempty
    have : S.card = 0 := Finset.card_eq_zero.mpr hempty
    rw [(Finset.mem_filter.mp hS).2] at this
    omega
  have hm : ∀ S ∈ Lv, ∀ T ∈ Lv,
      ((n : ℝ) * cubeAlpha (cubeUniformDist N) (S ∆ T)
        + ((n : ℝ) ^ 2 - (n : ℝ))
            * cubeAlpha (cubeUniformDist N) S * cubeAlpha (cubeUniformDist N) T)
        = if S = T then (n : ℝ) else 0 := by
    intro S hS T hT
    have h1 : cubeAlpha (cubeUniformDist N) (S ∆ T)
        = if S = T then 1 else 0 := by
      rw [cubeAlpha_uniform_eq]
      by_cases hST : S ∆ T = ∅
      · rw [ite_eq_left hST, ite_eq_left (Finset.symmDiff_eq_empty.mp hST)]
      · rw [ite_eq_right hST, ite_eq_right (fun h => hST (Finset.symmDiff_eq_empty.mpr h))]
    by_cases hST : S = T
    · rw [h1, ite_eq_left hST, cubeAlpha_uniform_eq, ite_eq_right (hne S hS),
        cubeAlpha_uniform_eq, ite_eq_right (hne T hT), ite_eq_left hST]
      ring
    · rw [h1, ite_eq_right hST, cubeAlpha_uniform_eq, ite_eq_right (hne S hS),
        cubeAlpha_uniform_eq, ite_eq_right (hne T hT), ite_eq_right hST]
      ring
  have hcard : Lv.card = Nat.choose N k := by
    rw [hLv, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  have hsum : (∑ S ∈ Lv, ∑ T ∈ Lv,
        (if S = T then (n : ℝ) else 0) ^ 2) = (n : ℝ) ^ 2 * (Nat.choose N k : ℝ) := by
    have hin : ∀ S ∈ Lv, (∑ T ∈ Lv, (if S = T then (n : ℝ) else 0) ^ 2)
        = (n : ℝ) ^ 2 := by
      intro S hS
      rw [Finset.sum_eq_single (s := Lv) (f := fun T => (if S = T then (n : ℝ) else 0) ^ 2)
        (a := S) (fun T _ hTS => by
          show (if S = T then (n : ℝ) else 0) ^ 2 = 0
          rw [ite_eq_right (fun h => hTS h.symm)]
          ring) (fun hS' => absurd hS hS')]
      rw [ite_eq_left rfl]
    calc (∑ S ∈ Lv, ∑ T ∈ Lv, (if S = T then (n : ℝ) else 0) ^ 2)
        = (∑ S ∈ Lv, (n : ℝ) ^ 2) := Finset.sum_congr rfl fun S hS => hin S hS
      _ = (n : ℝ) ^ 2 * (Nat.choose N k : ℝ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul']
  calc ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist (cubeUniformDist N) n).prob b
          * krawtchoukStatistic k n b.1 b.2 ^ 2
      = (∑ S ∈ Lv, ∑ T ∈ Lv,
          ((n : ℝ) * cubeAlpha (cubeUniformDist N) (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ))
                * cubeAlpha (cubeUniformDist N) S * cubeAlpha (cubeUniformDist N) T) ^ 2)
        / (n : ℝ) ^ 4 := hsecond
    _ = (∑ S ∈ Lv, ∑ T ∈ Lv, (if S = T then (n : ℝ) else 0) ^ 2) / (n : ℝ) ^ 4 := by
        refine congrArg (fun t => t / (n : ℝ) ^ 4) ?_
        exact Finset.sum_congr rfl fun S hS =>
          Finset.sum_congr rfl fun T hT => by rw [hm S hS T hT]
    _ = ((n : ℝ) ^ 2 * (Nat.choose N k : ℝ)) / (n : ℝ) ^ 4 := by rw [hsum]
    _ = (Nat.choose N k : ℝ) / (n : ℝ) ^ 2 := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · rw [div_eq_div_iff (by positivity) (by positivity)]
          ring

/-- Shows that the empty-set cube correlation is one. -/
private theorem cubeAlpha_empty {N : ℕ} (p : FinDist (Reg N)) :
    cubeAlpha p ∅ = 1 := by
  show (∑ x : Reg N, p.prob x * cubeChar ∅ x) = 1
  have hchar : ∀ x : Reg N, cubeChar ∅ x = 1 := fun x => by
    show (∏ i ∈ (∅ : Finset (Fin N)), (if x i then (1 : ℝ) else -1)) = 1
    rw [Finset.prod_empty]
  rw [Finset.sum_congr rfl fun x _ => by rw [hchar x, mul_one], p.sum_one]

/-- Bounds a row sum of squared symmetric-difference correlations by one plus the total
correlation mass. -/
private theorem alpha_sd_row_bound {N k : ℕ} (p : FinDist (Reg N))
    (S : Finset (Fin N)) :
    (∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        (cubeAlpha p (S ∆ T)) ^ 2)
      ≤ 1 + cubeAlphaTotalMass p := by
  classical
  set Lv : Finset (Finset (Fin N)) :=
    Finset.univ.powerset.filter (fun s => s.card = k) with hLv
  have hcancel : ∀ (A B : Finset (Fin N)), A ∆ B ∆ A = B := by
    intro A B
    ext x
    simp only [Finset.mem_symmDiff]
    by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;> simp [hA, hB]
  have hinj : Set.InjOn (fun T => S ∆ T) (↑Lv : Set (Finset (Fin N))) := by
    intro T₁ _ T₂ _ heq
    have h1 : (S ∆ T₁) ∆ S = (S ∆ T₂) ∆ S := by rw [congrArg (fun U => U ∆ S) heq]
    rw [hcancel S T₁, hcancel S T₂] at h1
    exact h1
  have himg : (Finset.image (fun T => S ∆ T) Lv) ⊆ Finset.univ.powerset := by
    intro U hU
    rw [Finset.mem_image] at hU
    obtain ⟨T, _, hT⟩ := hU
    rw [← hT]
    refine Finset.mem_powerset.mpr ?_
    intro x _
    exact Finset.mem_univ x
  calc (∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2)
      = ∑ U ∈ Finset.image (fun T => S ∆ T) Lv, (cubeAlpha p U) ^ 2 :=
        (Finset.sum_image (f := fun U => (cubeAlpha p U) ^ 2) hinj).symm
    _ ≤ ∑ U ∈ Finset.univ.powerset, (cubeAlpha p U) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun U _ _ => sq_nonneg _)
    _ = (cubeAlpha p ∅) ^ 2 + cubeAlphaTotalMass p := by
        have hempt : (∅ : Finset (Fin N)) ∈ (Finset.univ : Finset (Fin N)).powerset :=
          Finset.mem_powerset.mpr (Finset.empty_subset _)
        have hrw := Finset.sum_erase_add
          (s := (Finset.univ : Finset (Fin N)).powerset)
          (f := fun U => (cubeAlpha p U) ^ 2) hempt
        calc (∑ U ∈ Finset.univ.powerset, (cubeAlpha p U) ^ 2)
            = (∑ U ∈ Finset.univ.powerset.erase ∅, (cubeAlpha p U) ^ 2)
                + (cubeAlpha p ∅) ^ 2 := hrw.symm
          _ = (cubeAlpha p ∅) ^ 2 + cubeAlphaTotalMass p := by
              rw [add_comm]
              exact rfl
    _ = 1 + cubeAlphaTotalMass p := by rw [cubeAlpha_empty, one_pow]

/-- Shows that the weight-`k` squared correlation mass is nonnegative. -/
private theorem weightMass_nonneg {N k : ℕ} (p : FinDist (Reg N)) :
    0 ≤ cubeAlphaWeightMass p k :=
  Finset.sum_nonneg fun _S _ => sq_nonneg _

/-- Bounds the total squared symmetric-difference correlation sum by the binomial coefficient
times one plus the total correlation mass. -/
private theorem alpha_sd_mass_bound {N k : ℕ} (p : FinDist (Reg N)) :
    (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        (cubeAlpha p (S ∆ T)) ^ 2)
      ≤ (Nat.choose N k : ℝ) * (1 + cubeAlphaTotalMass p) := by
  classical
  set Lv : Finset (Finset (Fin N)) :=
    Finset.univ.powerset.filter (fun s => s.card = k) with hLv
  have hcard : Lv.card = Nat.choose N k := by
    rw [hLv, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  calc (∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2)
      ≤ (∑ S ∈ Lv, (1 + cubeAlphaTotalMass p)) :=
        Finset.sum_le_sum fun S _ => alpha_sd_row_bound p S
    _ = (Nat.choose N k : ℝ) * (1 + cubeAlphaTotalMass p) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul']
        exact mul_comm _ _

/-- Bounds the mixed correlation cross term by the square root of the product of its two squared
masses. -/
private theorem cross_term_bound {N k : ℕ} (p : FinDist (Reg N)) :
    (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
      ≤ Real.sqrt ((∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
            ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
            (cubeAlpha p (S ∆ T)) ^ 2)
          * (cubeAlphaWeightMass p k) ^ 2) := by
  classical
  set Lv : Finset (Finset (Fin N)) :=
    Finset.univ.powerset.filter (fun s => s.card = k) with hLv
  set f : Finset (Fin N) × Finset (Fin N) → ℝ :=
    fun ST => cubeAlpha p (ST.1 ∆ ST.2) with hf
  set g : Finset (Fin N) × Finset (Fin N) → ℝ :=
    fun ST => cubeAlpha p ST.1 * cubeAlpha p ST.2 with hg
  have hprod : ∀ (h : Finset (Fin N) × Finset (Fin N) → ℝ),
      (∑ S ∈ Lv, ∑ T ∈ Lv, h (S, T)) = ∑ x ∈ Lv ×ˢ Lv, h x := by
    intro h
    rw [Finset.sum_product]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Lv ×ˢ Lv) f g

  have hg2 : (∑ x ∈ Lv ×ˢ Lv, (g x) ^ 2) = (cubeAlphaWeightMass p k) ^ 2 := by
    have hsplit : ∀ x ∈ Lv ×ˢ Lv, (g x) ^ 2
        = (cubeAlpha p x.1) ^ 2 * (cubeAlpha p x.2) ^ 2 := by
      intro x _
      rw [hg, mul_pow]
    rw [Finset.sum_congr rfl (fun x hx => hsplit x hx), Finset.sum_product]
    have hstep : (∑ S ∈ Lv, ∑ T ∈ Lv,
        (cubeAlpha p (S, T).1) ^ 2 * (cubeAlpha p (S, T).2) ^ 2)
      = (∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p S) ^ 2 * (cubeAlpha p T) ^ 2) :=
      Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => rfl
    rw [hstep, ← Finset.sum_mul_sum]
    show (cubeAlphaWeightMass p k) * (cubeAlphaWeightMass p k)
      = (cubeAlphaWeightMass p k) ^ 2
    ring
  have hV : (∑ S ∈ Lv, ∑ T ∈ Lv, cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
      = ∑ x ∈ Lv ×ˢ Lv, f x * g x := by
    rw [hprod (fun ST => cubeAlpha p (ST.1 ∆ ST.2) * (cubeAlpha p ST.1 * cubeAlpha p ST.2))]
  have hfa : (∑ x ∈ Lv ×ˢ Lv, (f x) ^ 2)
      = ∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2 :=
    (hprod (fun ST => (cubeAlpha p (ST.1 ∆ ST.2)) ^ 2)).symm
  rw [hg2] at hcs
  rw [hV]
  calc (∑ x ∈ Lv ×ˢ Lv, f x * g x)
      ≤ |∑ x ∈ Lv ×ˢ Lv, f x * g x| := le_abs_self _
    _ = Real.sqrt ((∑ x ∈ Lv ×ˢ Lv, f x * g x) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ x ∈ Lv ×ˢ Lv, (f x) ^ 2) * (cubeAlphaWeightMass p k) ^ 2) := by
        exact Real.sqrt_le_sqrt hcs
    _ = Real.sqrt ((∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2)
        * (cubeAlphaWeightMass p k) ^ 2) := by rw [hfa]

/-- Converts the natural sample-count assumption into the stated real lower bound on the
half-block sample size. -/
private theorem halfCount_real {N k : ℕ} (_hk : 1 ≤ k) (_hkN : k ≤ N)
    {Δ β : ℝ} (_hΔ : 0 < Δ) (_hβ : 0 < β)
    (n : ℕ) (hnc : krawtCheckHalfCount N k Δ β ≤ n) :
    400 * Real.sqrt (2 * (Nat.choose N k : ℝ)) / (β * Δ) ≤ (n : ℝ) :=
  Nat.ceil_le.mp hnc

/-- Factors the double sum of squared correlation products into the square of the weight-`k`
correlation mass. -/
private theorem product_mass_eq {N k : ℕ} (p : FinDist (Reg N)) :
    (∑ S ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        ∑ T ∈ Finset.univ.powerset.filter (fun s => s.card = k),
        (cubeAlpha p S * cubeAlpha p T) ^ 2)
      = (cubeAlphaWeightMass p k) ^ 2 := by
  classical
  set Lv : Finset (Finset (Fin N)) :=
    Finset.univ.powerset.filter (fun s => s.card = k) with hLv
  have hsplit : (∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p S * cubeAlpha p T) ^ 2)
      = (∑ S ∈ Lv, (cubeAlpha p S) ^ 2) * (∑ T ∈ Lv, (cubeAlpha p T) ^ 2) := by
    calc (∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p S * cubeAlpha p T) ^ 2)
        = (∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p S) ^ 2 * (cubeAlpha p T) ^ 2) :=
          Finset.sum_congr rfl fun S _ =>
            Finset.sum_congr rfl fun T _ => mul_pow (cubeAlpha p S) (cubeAlpha p T) 2
      _ = (∑ S ∈ Lv, (cubeAlpha p S) ^ 2) * (∑ T ∈ Lv, (cubeAlpha p T) ^ 2) :=
          (Finset.sum_mul_sum Lv Lv (fun S => (cubeAlpha p S) ^ 2)
            (fun T => (cubeAlpha p T) ^ 2)).symm
  rw [hsplit]
  exact (sq (cubeAlphaWeightMass p k)).symm

set_option maxHeartbeats 1000000 in

/-- Bounds the centered second moment of the statistic by one forty-ninth of the squared
weight-`k` mass under correlation concentration and the sample bounds. -/
private theorem concentrated_variance {N k n : ℕ} (p : FinDist (Reg N))
    {Δ β : ℝ} (hconc : IsCorrelationConcentrated p Δ k β)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hβ : 0 < β) (_hβ1 : β ≤ 1)
    (hnc : krawtCheckHalfCount N k Δ β ≤ n) (hn : 0 < n) :
    ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        (cubeBlockDist p n).prob b
          * (krawtchoukStatistic k n b.1 b.2 - cubeAlphaWeightMass p k) ^ 2
      ≤ (cubeAlphaWeightMass p k) ^ 2 / 49 := by
  classical
  set q := cubeBlockDist p n with hqdef
  set W := cubeAlphaWeightMass p k with hWdef
  set Lv : Finset (Finset (Fin N)) :=
    Finset.univ.powerset.filter (fun s => s.card = k) with hLv
  have hW0 : 0 ≤ W := weightMass_nonneg p
  have hconc2 : β * Δ ≤ W := hconc.2
  set C : ℝ := (Nat.choose N k : ℝ) with hCdef
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    exact Nat.one_le_cast.mpr (Nat.choose_pos hkN)
  have hC0 : 0 ≤ C := by linarith
  set a : ℝ := (∑ S ∈ Lv, ∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2) with hAdef
  set V1 : ℝ := (∑ S ∈ Lv, ∑ T ∈ Lv,
    cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T)) with hV1def
  have ha0 : 0 ≤ a := Finset.sum_nonneg fun S _ =>
    Finset.sum_nonneg fun T _ => sq_nonneg _
  have hxsqrt : 0 ≤ Real.sqrt (2 * C) := Real.sqrt_nonneg _
  have h2C0 : 0 < 2 * C := by positivity
  have hx := halfCount_real hk hkN hΔ hβ n hnc
  have hβΔ2 : 0 < β * Δ := mul_pos hβ hΔ

  have hkey : (β ^ 2 + β * W) * Δ ^ 2 ≤ 2 * W ^ 2 := by
    have h1 : (β * Δ) ^ 2 ≤ W ^ 2 := by
      nlinarith [hconc2, mul_nonneg hβ.le hΔ.le, hW0]
    have h2 : β * W * Δ ^ 2 ≤ W ^ 2 := by
      have hWD : W * Δ ≤ W := by nlinarith [hW0, hΔ1, hΔ.le]
      nlinarith [hconc2, hWD, hW0, hΔ.le, hβ.le]
    have h1' : β ^ 2 * Δ ^ 2 ≤ W ^ 2 := by
      have h := h1
      rwa [mul_pow] at h
    have hexp : (β ^ 2 + β * W) * Δ ^ 2 = β ^ 2 * Δ ^ 2 + β * W * Δ ^ 2 := by ring
    rw [hexp]
    exact (add_le_add h1' h2).trans_eq (by ring : W ^ 2 + W ^ 2 = 2 * W ^ 2)

  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn2 : 320000 * C / (β * Δ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have hx0 : 0 ≤ 400 * Real.sqrt (2 * C) / (β * Δ) := by positivity
    have hxsq : (400 * Real.sqrt (2 * C) / (β * Δ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith [hx, hx0, hn0, sq_nonneg (400 * Real.sqrt (2 * C) / (β * Δ)),
        sq_nonneg (n : ℝ)]
    have hxval : (400 * Real.sqrt (2 * C) / (β * Δ)) ^ 2
        = 320000 * C / (β * Δ) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * C), mul_pow]
      norm_num
      ring
    rw [hxval] at hxsq
    exact hxsq

  have haC : a ≤ C * (1 + W / β) := by
    have h1 := alpha_sd_mass_bound (k := k) p
    have h2 : cubeAlphaTotalMass p ≤ W / β := by
      rw [le_div_iff₀ hβ, mul_comm]
      exact hconc.1
    have h3 : C * (1 + cubeAlphaTotalMass p) ≤ C * (1 + W / β) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) h2) hC0
    exact h1.trans h3

  have hcore : 160000 * a ≤ W ^ 2 * (n : ℝ) ^ 2 := by
    have hd : 0 < (β * Δ) ^ 2 := by positivity
    have hclear : C * (1 + W / β) * (β * Δ) ^ 2 = C * ((β ^ 2 + β * W) * Δ ^ 2) := by
      field_simp
    have hP1 : a * (β * Δ) ^ 2 ≤ C * ((β ^ 2 + β * W) * Δ ^ 2) := by
      calc a * (β * Δ) ^ 2 ≤ C * (1 + W / β) * (β * Δ) ^ 2 :=
          mul_le_mul_of_nonneg_right haC hd.le
        _ = C * ((β ^ 2 + β * W) * Δ ^ 2) := hclear
    have hP2 : C * ((β ^ 2 + β * W) * Δ ^ 2) ≤ 2 * (W ^ 2 * C) := by
      have h := mul_le_mul_of_nonneg_left hkey hC0
      calc C * ((β ^ 2 + β * W) * Δ ^ 2) ≤ C * (2 * W ^ 2) := h
        _ = 2 * (W ^ 2 * C) := by ring
    have hkey2 : 320000 * (W ^ 2 * C) ≤ W ^ 2 * (n : ℝ) ^ 2 * (β * Δ) ^ 2 := by
      have hstep : 320000 * C / (β * Δ) ^ 2 * W ^ 2 ≤ (n : ℝ) ^ 2 * W ^ 2 :=
        mul_le_mul_of_nonneg_right hn2 (sq_nonneg W)
      have hstep2 : 320000 * C / (β * Δ) ^ 2 * W ^ 2 * (β * Δ) ^ 2
          ≤ (n : ℝ) ^ 2 * W ^ 2 * (β * Δ) ^ 2 :=
        mul_le_mul_of_nonneg_right hstep hd.le
      have hcancel : 320000 * C / (β * Δ) ^ 2 * W ^ 2 * (β * Δ) ^ 2
          = 320000 * (W ^ 2 * C) := by
        field_simp
      rw [hcancel] at hstep2
      calc 320000 * (W ^ 2 * C) ≤ (n : ℝ) ^ 2 * W ^ 2 * (β * Δ) ^ 2 := hstep2
        _ = W ^ 2 * (n : ℝ) ^ 2 * (β * Δ) ^ 2 := by ring
    have hfinal : 160000 * a * (β * Δ) ^ 2 ≤ W ^ 2 * (n : ℝ) ^ 2 * (β * Δ) ^ 2 := by
      calc 160000 * a * (β * Δ) ^ 2 = 160000 * (a * (β * Δ) ^ 2) := by ring
        _ ≤ 160000 * (C * ((β ^ 2 + β * W) * Δ ^ 2)) :=
            mul_le_mul_of_nonneg_left hP1 (by norm_num : (0 : ℝ) ≤ 160000)
        _ ≤ 160000 * (2 * (W ^ 2 * C)) :=
            mul_le_mul_of_nonneg_left hP2 (by norm_num : (0 : ℝ) ≤ 160000)
        _ = 320000 * (W ^ 2 * C) := by ring
        _ ≤ W ^ 2 * (n : ℝ) ^ 2 * (β * Δ) ^ 2 := hkey2
    exact (mul_le_mul_iff_of_pos_right hd).mp hfinal

  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hc0 : 0 ≤ (n : ℝ) ^ 2 - (n : ℝ) := by nlinarith [hn0, hn1]
  have hc_le : (n : ℝ) ^ 2 - (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith [hn0]
  have hc2_le : ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 ≤ (n : ℝ) ^ 4 := by
    have hcert : 0 ≤ (n : ℝ) ^ 2 * (2 * (n : ℝ) - 1) :=
      mul_nonneg (sq_nonneg _) (by nlinarith [hn1])
    nlinarith [hcert]

  have hV1_le : V1 ≤ W * Real.sqrt a := by
    have h := cross_term_bound (k := k) p
    rw [← hLv, ← hV1def, ← hAdef, ← hWdef] at h
    rw [Real.sqrt_mul ha0 (W ^ 2), Real.sqrt_sq hW0] at h
    exact h.trans_eq (mul_comm (Real.sqrt a) W)

  have hMsum : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
      q.prob b * krawtchoukStatistic k n b.1 b.2) = W := by
    rw [hqdef]
    exact block_mean p hn
  have hcentral : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2)
      = (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          q.prob b * krawtchoukStatistic k n b.1 b.2 ^ 2) - W ^ 2 := by
    have hzero : ∀ b : (Fin n → Reg N) × (Fin n → Reg N),
        q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2
          + 2 * W * (q.prob b * krawtchoukStatistic k n b.1 b.2) - q.prob b * W ^ 2
          = q.prob b * krawtchoukStatistic k n b.1 b.2 ^ 2 := fun b => by ring
    have hsum : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2)
        + 2 * W * (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
            q.prob b * krawtchoukStatistic k n b.1 b.2)
        - (∑ b : (Fin n → Reg N) × (Fin n → Reg N), q.prob b) * W ^ 2
        = ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
            (q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2
              + 2 * W * (q.prob b * krawtchoukStatistic k n b.1 b.2) - q.prob b * W ^ 2) := by
      have h1 : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
            (q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2
              + 2 * W * (q.prob b * krawtchoukStatistic k n b.1 b.2) - q.prob b * W ^ 2))
          = ((∑ b : (Fin n → Reg N) × (Fin n → Reg N),
                q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2)
              + ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
                  2 * W * (q.prob b * krawtchoukStatistic k n b.1 b.2))
            - ∑ b : (Fin n → Reg N) × (Fin n → Reg N), q.prob b * W ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hfactor : 2 * W * (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
            q.prob b * krawtchoukStatistic k n b.1 b.2)
          = ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
              2 * W * (q.prob b * krawtchoukStatistic k n b.1 b.2) :=
        Finset.mul_sum Finset.univ
          (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
            q.prob b * krawtchoukStatistic k n b.1 b.2) (2 * W)
      have hfactor2 : (∑ b : (Fin n → Reg N) × (Fin n → Reg N), q.prob b) * W ^ 2
          = ∑ b : (Fin n → Reg N) × (Fin n → Reg N), q.prob b * W ^ 2 :=
        Finset.sum_mul Finset.univ
          (fun b : (Fin n → Reg N) × (Fin n → Reg N) => q.prob b) (W ^ 2)
      rw [h1, hfactor, hfactor2]
    have h3 : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2
            + 2 * W * (q.prob b * krawtchoukStatistic k n b.1 b.2) - q.prob b * W ^ 2))
        = ∑ b : (Fin n → Reg N) × (Fin n → Reg N),
            q.prob b * krawtchoukStatistic k n b.1 b.2 ^ 2 :=
      Finset.sum_congr rfl fun b _ => hzero b
    rw [← h3, ← hsum, hMsum, q.sum_one]
    have hww : 2 * W * W = 2 * W ^ 2 := by ring
    rw [hww]
    linarith

  have hE2 : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        q.prob b * krawtchoukStatistic k n b.1 b.2 ^ 2)
      = ((n : ℝ) ^ 2 * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
          + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * W ^ 2) / (n : ℝ) ^ 4 := by
    have h0 := block_second_moment (k := k) (n := n) p
    rw [← hqdef, ← hLv] at h0
    have hitem : ∀ S ∈ Lv, ∀ T ∈ Lv,
        ((n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2
          = ((n : ℝ) ^ 2) * (cubeAlpha p (S ∆ T)) ^ 2
            + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ))
              * (cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
            + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * (cubeAlpha p S * cubeAlpha p T) ^ 2 :=
      fun S _ T _ => by ring
    have hsplit : (∑ S ∈ Lv, ∑ T ∈ Lv,
          ((n : ℝ) * cubeAlpha p (S ∆ T)
            + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2)
        = ((n : ℝ) ^ 2) * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
          + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * W ^ 2 := by
      have hinner : ∀ S ∈ Lv,
          (∑ T ∈ Lv,
              (((n : ℝ) ^ 2) * (cubeAlpha p (S ∆ T)) ^ 2
                + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ))
                  * (cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
                + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * (cubeAlpha p S * cubeAlpha p T) ^ 2))
          = ((n : ℝ) ^ 2) * (∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2)
            + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ))
              * (∑ T ∈ Lv, cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
            + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * (∑ T ∈ Lv, (cubeAlpha p S * cubeAlpha p T) ^ 2) := by
        intro S _
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
          Finset.mul_sum, Finset.mul_sum]
      calc (∑ S ∈ Lv, ∑ T ∈ Lv,
            ((n : ℝ) * cubeAlpha p (S ∆ T)
              + ((n : ℝ) ^ 2 - (n : ℝ)) * cubeAlpha p S * cubeAlpha p T) ^ 2)
          = ∑ S ∈ Lv, ∑ T ∈ Lv,
              (((n : ℝ) ^ 2) * (cubeAlpha p (S ∆ T)) ^ 2
                + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ))
                  * (cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
                + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * (cubeAlpha p S * cubeAlpha p T) ^ 2) :=
            Finset.sum_congr rfl fun S hS => Finset.sum_congr rfl fun T hT => hitem S hS T hT
        _ = ∑ S ∈ Lv,
              (((n : ℝ) ^ 2) * (∑ T ∈ Lv, (cubeAlpha p (S ∆ T)) ^ 2)
              + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ))
                * (∑ T ∈ Lv, cubeAlpha p (S ∆ T) * (cubeAlpha p S * cubeAlpha p T))
              + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * (∑ T ∈ Lv, (cubeAlpha p S * cubeAlpha p T) ^ 2)) :=
            Finset.sum_congr rfl hinner
        _ = ((n : ℝ) ^ 2) * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
            + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * W ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.mul_sum, ← Finset.mul_sum, ← hAdef, ← hV1def, hLv,
              product_mass_eq p, ← hWdef]
    rw [h0, hsplit]

  have hf1 : 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
      ≤ 2 * (n : ℝ) * ((n : ℝ) ^ 2) * (W * Real.sqrt a) := by
    have hmid : 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ))
        ≤ 2 * (n : ℝ) * ((n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hc_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnR.le)
    calc 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
        ≤ 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * (W * Real.sqrt a) :=
          mul_le_mul_of_nonneg_left hV1_le
            (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnR.le) hc0)
      _ ≤ 2 * (n : ℝ) * ((n : ℝ) ^ 2) * (W * Real.sqrt a) :=
          mul_le_mul_of_nonneg_right hmid (mul_nonneg hW0 (Real.sqrt_nonneg a))
  have hf2 : ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * W ^ 2 ≤ (n : ℝ) ^ 4 * W ^ 2 :=
    mul_le_mul_of_nonneg_right hc2_le (sq_nonneg W)
  have hfin : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
        q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2)
      ≤ a / (n : ℝ) ^ 2 + 2 * W * Real.sqrt a / (n : ℝ) := by
    have hcomb : (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          q.prob b * (krawtchoukStatistic k n b.1 b.2 - W) ^ 2)
        = ((n : ℝ) ^ 2 * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
            + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * W ^ 2) / (n : ℝ) ^ 4 - W ^ 2 := by
      rw [hcentral, hE2]
    have hnum : ((n : ℝ) ^ 2 * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2 - (n : ℝ)) * V1
          + ((n : ℝ) ^ 2 - (n : ℝ)) ^ 2 * W ^ 2)
        ≤ ((n : ℝ) ^ 2 * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2) * (W * Real.sqrt a)
          + (n : ℝ) ^ 4 * W ^ 2) := by
      linarith [hf1, hf2]
    have hd2 := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 4)
    have hval : ((n : ℝ) ^ 2 * a + 2 * (n : ℝ) * ((n : ℝ) ^ 2) * (W * Real.sqrt a)
          + (n : ℝ) ^ 4 * W ^ 2) / (n : ℝ) ^ 4
        = a / (n : ℝ) ^ 2 + 2 * W * Real.sqrt a / (n : ℝ) + W ^ 2 := by
      field_simp
    rw [hval] at hd2
    rw [hcomb]
    linarith

  have htA : a / (n : ℝ) ^ 2 ≤ W ^ 2 / 160000 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hnR) (by norm_num : (0 : ℝ) < 160000)]
    calc a * 160000 = 160000 * a := mul_comm a 160000
      _ ≤ W ^ 2 * (n : ℝ) ^ 2 := hcore
  have htB : 2 * W * Real.sqrt a / (n : ℝ) ≤ W ^ 2 / 200 := by
    have hX : (0 : ℝ) ≤ 2 * W * Real.sqrt a / (n : ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW0) (Real.sqrt_nonneg a)) hnR.le
    have hY : (0 : ℝ) ≤ W ^ 2 / 200 :=
      div_nonneg (sq_nonneg W) (by norm_num : (0 : ℝ) ≤ 200)
    have hsq : (2 * W * Real.sqrt a / (n : ℝ)) ^ 2 ≤ (W ^ 2 / 200) ^ 2 := by
      have h1 : (2 * W * Real.sqrt a / (n : ℝ)) ^ 2 = 4 * W ^ 2 * (a / (n : ℝ) ^ 2) := by
        have hs : (2 * W * Real.sqrt a) ^ 2 = 4 * W ^ 2 * a := by
          rw [mul_pow, mul_pow, Real.sq_sqrt ha0]
          ring
        calc (2 * W * Real.sqrt a / (n : ℝ)) ^ 2
            = (2 * W * Real.sqrt a) ^ 2 / (n : ℝ) ^ 2 := by rw [div_pow]
          _ = 4 * W ^ 2 * a / (n : ℝ) ^ 2 := by rw [hs]
          _ = 4 * W ^ 2 * (a / (n : ℝ) ^ 2) := by ring
      have hlast : 4 * W ^ 2 * (W ^ 2 / 160000) = (W ^ 2 / 200) ^ 2 := by
        rw [div_pow]
        ring
      rw [h1]
      calc 4 * W ^ 2 * (a / (n : ℝ) ^ 2) ≤ 4 * W ^ 2 * (W ^ 2 / 160000) :=
            mul_le_mul_of_nonneg_left htA (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg W))
        _ = (W ^ 2 / 200) ^ 2 := hlast
    exact (sq_le_sq₀ hX hY).mp hsq
  have hfinal2 : a / (n : ℝ) ^ 2 + 2 * W * Real.sqrt a / (n : ℝ) ≤ W ^ 2 / 49 := by
    have h1 := add_le_add htA htB
    have h2 : W ^ 2 / 160000 + W ^ 2 / 200 ≤ W ^ 2 / 49 := by
      have hcoef : ((1 : ℝ) / 160000 + (1 : ℝ) / 200) ≤ (1 : ℝ) / 49 := by norm_num
      calc W ^ 2 / 160000 + W ^ 2 / 200
          = W ^ 2 * ((1 : ℝ) / 160000 + (1 : ℝ) / 200) := by ring
        _ ≤ W ^ 2 * ((1 : ℝ) / 49) := mul_le_mul_of_nonneg_left hcoef (sq_nonneg W)
        _ = W ^ 2 / 49 := by ring
    exact h1.trans h2
  exact hfin.trans hfinal2

/-- Bounds the probability of at least `r` bad samples by three to the number of remaining
samples divided by two to the total sample count. -/
private theorem exp_markov_count {X : Type*} [Fintype X] [DecidableEq X]
    (q : FinDist X) (E : X → Prop) [DecidablePred E] (M r : ℕ) (hr : r ≤ M)
    (hbad : (∑ x ∈ Finset.univ.filter (fun x => E x), q.prob x) ≤ 1 / 4) :
    ∑ s ∈ Finset.univ.filter
        (fun s : Fin M → X => r ≤ ∑ m, if E (s m) then 1 else 0),
      ∏ m, q.prob (s m) ≤ 3 ^ (M - r) / 2 ^ M := by
  classical
  have hcnt : ∀ s : Fin M → X,
      (∑ m, if E (s m) then 1 else 0) = (Finset.univ.filter (fun m => E (s m))).card := by
    intro s
    rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  have : (x : X) → Decidable ¬E x := fun x => Classical.propDecidable (¬E x)
  simp only [hcnt]

  have hprob : ∀ s : Fin M → X,
      (if r ≤ (Finset.univ.filter (fun m => E (s m))).card then (1 : ℝ) else 0)
        ≤ (3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card / (3 : ℝ) ^ r := by
    intro s
    by_cases h : r ≤ (Finset.univ.filter (fun m => E (s m))).card
    · rw [ite_eq_left h, le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 3) _), one_mul]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) h
    · rw [ite_eq_right h]
      positivity

  have hpow : ∀ s : Fin M → X,
      (3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card
        = ∏ m : Fin M, if E (s m) then (3 : ℝ) else 1 := by
    intro s
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

  have hfactor : (∑ b : X, q.prob b * (if E b then (3 : ℝ) else 1))
      = 1 + 2 * (∑ x ∈ Finset.univ.filter (fun x => E x), q.prob x) := by
    have h2 : ∀ b : X, q.prob b * (if E b then (3 : ℝ) else 1)
        = q.prob b + (if E b then 2 * q.prob b else 0) := by
      intro b
      by_cases h : E b <;> simp only [h, ite_true, ite_false] <;> ring
    have htot : (∑ x ∈ Finset.univ.filter (fun x => E x), q.prob x)
        + (∑ x ∈ Finset.univ.filter (fun x => ¬E x), q.prob x) = 1 := by
      rw [Finset.sum_filter_add_sum_filter_not]
      exact q.sum_one
    have hnot : (∑ x ∈ Finset.univ.filter (fun x => ¬E x), q.prob x)
        = 1 - (∑ x ∈ Finset.univ.filter (fun x => E x), q.prob x) := by
      linarith [htot]
    have h3 : (∑ b : X, if E b then 2 * q.prob b else 0)
        = 2 * (∑ x ∈ Finset.univ.filter (fun x => E x), q.prob x) := by
      rw [← Finset.sum_filter (fun x : X => E x) (fun x : X => 2 * q.prob x)]
      exact (Finset.mul_sum (Finset.univ.filter (fun x => E x))
        (fun x => q.prob x) 2).symm
    calc (∑ b : X, q.prob b * (if E b then (3 : ℝ) else 1))
        = (∑ b : X, q.prob b) + (∑ b : X, if E b then 2 * q.prob b else 0) := by
          rw [Finset.sum_congr rfl fun b _ => h2 b, Finset.sum_add_distrib]
      _ = 1 + 2 * (∑ x ∈ Finset.univ.filter (fun x => E x), q.prob x) := by
          rw [q.sum_one, h3]

  have hprod : ∏ m : Fin M, (∑ b : X, q.prob b * (if E b then (3 : ℝ) else 1))
      ≤ ((3 : ℝ) / 2) ^ M := by
    have hnn : 0 ≤ ∑ b : X, q.prob b * (if E b then (3 : ℝ) else 1) :=
      Finset.sum_nonneg fun b _ =>
        mul_nonneg (q.nonneg b) (by split <;> norm_num)
    calc ∏ m : Fin M, (∑ b : X, q.prob b * (if E b then (3 : ℝ) else 1))
        ≤ ∏ _m : Fin M, (3 : ℝ) / 2 := by
          refine Finset.prod_le_prod₀ (fun _m _ => hnn) fun m _ => ?_
          rw [hfactor]
          linarith [hbad]
      _ = ((3 : ℝ) / 2) ^ M := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

  calc ∑ s ∈ Finset.univ.filter
          (fun s : Fin M → X => r ≤ (Finset.univ.filter (fun m => E (s m))).card),
        ∏ m, q.prob (s m)
      = ∑ s ∈ Finset.univ.filter
          (fun s : Fin M → X => r ≤ (Finset.univ.filter (fun m => E (s m))).card),
          q.probOf s := Finset.sum_congr rfl fun s _ => rfl
    _ = ∑ s : Fin M → X, q.probOf s *
          (if r ≤ (Finset.univ.filter (fun m => E (s m))).card then (1 : ℝ) else 0) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun s _ => by rw [mul_ite, mul_one, mul_zero]
    _ ≤ ∑ s : Fin M → X, q.probOf s *
          ((3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card / (3 : ℝ) ^ r) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hprob s)
          (Finset.prod_nonneg fun i _ => q.nonneg _)
    _ = (∑ s : Fin M → X, q.probOf s *
          (3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card) / (3 : ℝ) ^ r := by
        have step : ∀ s : Fin M → X,
            q.probOf s
              * ((3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card / (3 : ℝ) ^ r)
              = (q.probOf s * (3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card)
                / (3 : ℝ) ^ r :=
          fun _ => (mul_div_assoc _ _ _).symm
        rw [Finset.sum_congr rfl fun s _ => step s, Finset.sum_div]
    _ = (∏ m : Fin M, ∑ b : X, q.prob b * (if E b then (3 : ℝ) else 1)) / (3 : ℝ) ^ r := by
        congr 1
        have step : ∀ s : Fin M → X,
            q.probOf s * (3 : ℝ) ^ (Finset.univ.filter (fun m => E (s m))).card
              = q.probOf s * ∏ m : Fin M, if E (s m) then (3 : ℝ) else 1 :=
          fun s => by rw [hpow s]
        rw [Finset.sum_congr rfl fun s _ => step s]
        exact Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect_prod q
            (fun _ b => if E b then (3 : ℝ) else 1)
    _ ≤ ((3 : ℝ) / 2) ^ M / (3 : ℝ) ^ r :=
        div_le_div_of_nonneg_right hprod (pow_nonneg (by norm_num) _)
    _ = (3 : ℝ) ^ (M - r) / (2 : ℝ) ^ M := by
        have h3M : (3 : ℝ) ^ M = (3 : ℝ) ^ (M - r) * (3 : ℝ) ^ r := by
          rw [← pow_add]
          congr 1
          omega
        rw [div_pow, div_div, h3M]
        field_simp

/-- Gives explicit lower bounds for the logarithms of four thirds and two. -/
private theorem log_lower_bounds : 1 / 8 ≤ Real.log (4 / 3 : ℝ) ∧ 1 / 16 ≤ Real.log 2 := by
  have hexp8 : Real.exp (1 / 8) ≤ 8 / 7 := by
    have h := Real.add_one_le_exp (-(1 / 8))
    have h78 : (7 : ℝ) / 8 ≤ Real.exp (-(1 / 8)) := by
      linarith [h]
    have hkey : (7 : ℝ) / 8 * Real.exp (1 / 8) ≤ 1 := by
      calc (7 : ℝ) / 8 * Real.exp (1 / 8)
          ≤ Real.exp (-(1 / 8)) * Real.exp (1 / 8) :=
            mul_le_mul_of_nonneg_right h78 (by positivity)
        _ = 1 := by
            rw [← Real.exp_add]
            norm_num
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 7)]
    linarith [hkey]
  have hexp16 : Real.exp (1 / 16) ≤ 16 / 15 := by
    have h := Real.add_one_le_exp (-(1 / 16))
    have h1516 : (15 : ℝ) / 16 ≤ Real.exp (-(1 / 16)) := by
      linarith [h]
    have hkey : (15 : ℝ) / 16 * Real.exp (1 / 16) ≤ 1 := by
      calc (15 : ℝ) / 16 * Real.exp (1 / 16)
          ≤ Real.exp (-(1 / 16)) * Real.exp (1 / 16) :=
            mul_le_mul_of_nonneg_right h1516 (by positivity)
        _ = 1 := by
            rw [← Real.exp_add]
            norm_num
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 15)]
    linarith [hkey]
  have h1 : 1 / 8 ≤ Real.log (4 / 3 : ℝ) := by
    have h43 : Real.exp (1 / 8) ≤ 4 / 3 := hexp8.trans (by norm_num : (8 : ℝ) / 7 ≤ 4 / 3)
    have := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp (1 / 8)) h43
    rwa [Real.log_exp] at this
  have h2 : 1 / 16 ≤ Real.log 2 := by
    have h2le : Real.exp (1 / 16) ≤ 2 := hexp16.trans (by norm_num : (16 : ℝ) / 15 ≤ 2)
    have := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp (1 / 16)) h2le
    rwa [Real.log_exp] at this
  exact ⟨h1, h2⟩

/-- Bounds the majority-error power expression by the target error when the block count meets
its prescribed threshold. -/
private theorem majority_pow_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (M : ℕ)
    (hM : krawtCheckBlockCount δ ≤ M) : (3 : ℝ) ^ (M / 2) / (2 : ℝ) ^ M ≤ δ := by
  have hone : (1 : ℝ) ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]
    linarith
  have hL : 0 ≤ Real.log (1 / δ) := Real.log_nonneg hone
  have hM16 : 16 * Real.log (1 / δ) ≤ (M : ℝ) := Nat.ceil_le.mp hM
  have hlog1 := log_lower_bounds.1
  have hlog2 := log_lower_bounds.2
  have hx0 : (0 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ ((M - 2 * (M / 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hs1 : ((M - 2 * (M / 2) : ℕ) : ℝ) ≤ 1 := by
    have : M - 2 * (M / 2) ≤ 1 := by omega
    exact_mod_cast this
  have hMs : 2 * ((M / 2 : ℕ) : ℝ) + ((M - 2 * (M / 2) : ℕ) : ℝ) = (M : ℝ) := by
    have hn : 2 * (M / 2) + (M - 2 * (M / 2)) = M := by omega
    calc 2 * ((M / 2 : ℕ) : ℝ) + ((M - 2 * (M / 2) : ℕ) : ℝ)
        = (((2 * (M / 2) + (M - 2 * (M / 2)) : ℕ) : ℕ) : ℝ) := by push_cast; ring
      _ = (M : ℝ) := by rw [hn]
  have hlog43 : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0), hlog4]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (M / 2) / (2 : ℝ) ^ M := by positivity
  refine (Real.log_le_log_iff hpos hδ).mp ?_
  have hlogratio : Real.log ((3 : ℝ) ^ (M / 2) / (2 : ℝ) ^ M)
      = ((M / 2 : ℕ) : ℝ) * Real.log 3 - (M : ℝ) * Real.log 2 := by
    rw [Real.log_div (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
      Real.log_pow, Real.log_pow]
  rw [hlogratio]
  have hkey : (M : ℝ) / 16
      ≤ ((M / 2 : ℕ) : ℝ) * Real.log (4 / 3 : ℝ)
        + ((M - 2 * (M / 2) : ℕ) : ℝ) * Real.log 2 := by
    have h1 : ((1 : ℝ) / 8) * ((M / 2 : ℕ) : ℝ)
        ≤ Real.log (4 / 3 : ℝ) * ((M / 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hlog1 hx0
    have h2 : ((1 : ℝ) / 16) * ((M - 2 * (M / 2) : ℕ) : ℝ)
        ≤ Real.log 2 * ((M - 2 * (M / 2) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hlog2 hs0
    linarith [h1, h2, hMs]
  have hlogδ : Real.log δ = -Real.log (1 / δ) := by
    have h1 : Real.log (δ * (1 / δ)) = Real.log 1 := by
      rw [mul_one_div, div_self hδ.ne']
    rw [Real.log_mul hδ.ne' (one_div_ne_zero hδ.ne'), Real.log_one] at h1
    linarith [h1]
  have hsymm : ((M / 2 : ℕ) : ℝ) * Real.log 3 - (M : ℝ) * Real.log 2
      = -(((M / 2 : ℕ) : ℝ) * Real.log (4 / 3 : ℝ)
        + ((M - 2 * (M / 2) : ℕ) : ℝ) * Real.log 2) := by
    rw [← hMs, hlog43]
    ring
  rw [hsymm, hlogδ]
  linarith [hkey, hM16]

/-- Bounds the probability that a uniform block statistic exceeds the acceptance threshold by
one quarter. -/
private theorem uniform_block_bad {N k n : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    {Δ β : ℝ} (hΔ : 0 < Δ) (hβ : 0 < β)
    (hnc : krawtCheckHalfCount N k Δ β ≤ n) :
    (∑ b ∈ Finset.univ.filter
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2),
      (cubeBlockDist (cubeUniformDist N) n).prob b) ≤ 1 / 4 := by
  have hβΔ : 0 < β * Δ := mul_pos hβ hΔ
  have hC1 : 1 ≤ (Nat.choose N k : ℝ) := Nat.one_le_cast.mpr (Nat.choose_pos hkN)
  have hsqrt : 0 < Real.sqrt (2 * (Nat.choose N k : ℝ)) :=
    Real.sqrt_pos.mpr (by nlinarith [hC1])
  have hhc : 0 < krawtCheckHalfCount N k Δ β :=
    Nat.ceil_pos.mpr (div_pos (mul_pos (by norm_num : (0 : ℝ) < 400) hsqrt) hβΔ)
  have hn0 : 0 < n := lt_of_lt_of_le hhc hnc
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hE2 := uniform_second_moment (N := N) (k := k) (n := n) hk
  have hn2' : 320000 * (Nat.choose N k : ℝ) ≤ (n : ℝ) ^ 2 * (β * Δ) ^ 2 := by
    have hx := halfCount_real hk hkN hΔ hβ n hnc
    have hx0 : 0 ≤ 400 * Real.sqrt (2 * (Nat.choose N k : ℝ)) / (β * Δ) := by positivity
    have hnR0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hxsq : (400 * Real.sqrt (2 * (Nat.choose N k : ℝ)) / (β * Δ)) ^ 2
        ≤ (n : ℝ) ^ 2 := by
      nlinarith [hx, hx0, hnR0,
        sq_nonneg (400 * Real.sqrt (2 * (Nat.choose N k : ℝ)) / (β * Δ)),
        sq_nonneg ((n : ℝ))]
    have hxval : (400 * Real.sqrt (2 * (Nat.choose N k : ℝ)) / (β * Δ)) ^ 2
        = 320000 * (Nat.choose N k : ℝ) / (β * Δ) ^ 2 := by
      rw [div_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * (Nat.choose N k : ℝ)), mul_pow]
      norm_num
      ring
    rw [hxval] at hxsq
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (β * Δ) ^ 2)] at hxsq
    linarith [hxsq]
  have hsub : (Finset.univ.filter
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2))
      ⊆ (Finset.univ.filter
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          β * Δ / 50 ≤ |krawtchoukStatistic k n b.1 b.2|)) := by
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1, hb.2.trans (le_abs_self (krawtchoukStatistic k n b.1 b.2))⟩
  have hmark := markov_abs_tail (cubeBlockDist (cubeUniformDist N) n)
    (fun b : (Fin n → Reg N) × (Fin n → Reg N) => krawtchoukStatistic k n b.1 b.2)
    (β * Δ / 50) (by positivity)
  have hval : ((Nat.choose N k : ℝ) / (n : ℝ) ^ 2) / (β * Δ / 50) ^ 2
      = (Nat.choose N k : ℝ) * 2500 / ((n : ℝ) ^ 2 * (β * Δ) ^ 2) := by
    rw [div_pow, div_div]
    field_simp
    ring
  calc (∑ b ∈ Finset.univ.filter
          (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
            β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2),
        (cubeBlockDist (cubeUniformDist N) n).prob b)
      ≤ ∑ b ∈ Finset.univ.filter
          (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
            β * Δ / 50 ≤ |krawtchoukStatistic k n b.1 b.2|),
          (cubeBlockDist (cubeUniformDist N) n).prob b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun b _ _ => (cubeBlockDist (cubeUniformDist N) n).nonneg b)
    _ ≤ (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (cubeBlockDist (cubeUniformDist N) n).prob b
            * krawtchoukStatistic k n b.1 b.2 ^ 2) / (β * Δ / 50) ^ 2 := hmark
    _ = ((Nat.choose N k : ℝ) / (n : ℝ) ^ 2) / (β * Δ / 50) ^ 2 := by rw [hE2]
    _ = (Nat.choose N k : ℝ) * 2500 / ((n : ℝ) ^ 2 * (β * Δ) ^ 2) := hval
    _ ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2 * (β * Δ) ^ 2)]
        linarith [hn2']

/-- Bounds the probability that a correlation-concentrated block statistic falls below the
acceptance threshold by one quarter. -/
private theorem concentrated_block_bad {N k n : ℕ} (p : FinDist (Reg N))
    {Δ β : ℝ} (hconc : IsCorrelationConcentrated p Δ k β)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hnc : krawtCheckHalfCount N k Δ β ≤ n) (hn : 0 < n) :
    (∑ b ∈ Finset.univ.filter
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          ¬ β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2),
      (cubeBlockDist p n).prob b) ≤ 1 / 4 := by
  have hW0 : 0 ≤ cubeAlphaWeightMass p k := weightMass_nonneg p
  have hWpos : 0 < cubeAlphaWeightMass p k :=
    lt_of_lt_of_le (mul_pos hβ hΔ) hconc.2
  have hvar := concentrated_variance p hconc hk hkN hΔ hΔ1 hβ hβ1 hnc hn
  have hmark := markov_abs_tail (cubeBlockDist p n)
    (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
      krawtchoukStatistic k n b.1 b.2 - cubeAlphaWeightMass p k)
    (49 * cubeAlphaWeightMass p k / 50) (by positivity)
  have hsub : (Finset.univ.filter
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          ¬ β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2))
      ⊆ (Finset.univ.filter
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          49 * cubeAlphaWeightMass p k / 50
            ≤ |krawtchoukStatistic k n b.1 b.2 - cubeAlphaWeightMass p k|)) := by
    intro b hb
    rw [Finset.mem_filter] at hb ⊢
    refine ⟨hb.1, ?_⟩
    have hfb : krawtchoukStatistic k n b.1 b.2 < β * Δ / 50 := not_le.mp hb.2
    have hWt : β * Δ / 50 ≤ cubeAlphaWeightMass p k / 50 := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 50)
        (by norm_num : (0 : ℝ) < 50)]
      nlinarith [hconc.2]
    have h49 : 49 * cubeAlphaWeightMass p k / 50
        ≤ cubeAlphaWeightMass p k - β * Δ / 50 := by
      nlinarith [hconc.2, hW0]
    have hge0 : (0 : ℝ) ≤ cubeAlphaWeightMass p k - krawtchoukStatistic k n b.1 b.2 := by
      nlinarith [hfb.le, hWt, hW0]
    calc 49 * cubeAlphaWeightMass p k / 50
        ≤ cubeAlphaWeightMass p k - β * Δ / 50 := h49
      _ ≤ cubeAlphaWeightMass p k - krawtchoukStatistic k n b.1 b.2 :=
          sub_le_sub_left hfb.le _
      _ = |krawtchoukStatistic k n b.1 b.2 - cubeAlphaWeightMass p k| := by
          rw [abs_sub_comm, abs_of_nonneg hge0]
  have hWne : cubeAlphaWeightMass p k ≠ 0 := hWpos.ne'
  have hval : (cubeAlphaWeightMass p k ^ 2 / 49) / (49 * cubeAlphaWeightMass p k / 50) ^ 2
      = 2500 / 117649 := by
    rw [div_pow, div_div]
    field_simp
    norm_num
  calc (∑ b ∈ Finset.univ.filter
          (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
            ¬ β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2),
        (cubeBlockDist p n).prob b)
      ≤ ∑ b ∈ Finset.univ.filter
          (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
            49 * cubeAlphaWeightMass p k / 50
              ≤ |krawtchoukStatistic k n b.1 b.2 - cubeAlphaWeightMass p k|),
          (cubeBlockDist p n).prob b :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b _ _ => (cubeBlockDist p n).nonneg b)
    _ ≤ (∑ b : (Fin n → Reg N) × (Fin n → Reg N),
          (cubeBlockDist p n).prob b
            * (krawtchoukStatistic k n b.1 b.2 - cubeAlphaWeightMass p k) ^ 2)
        / (49 * cubeAlphaWeightMass p k / 50) ^ 2 := hmark
    _ ≤ (cubeAlphaWeightMass p k ^ 2 / 49)
        / (49 * cubeAlphaWeightMass p k / 50) ^ 2 :=
        div_le_div_of_nonneg_right hvar (by positivity)
    _ = 2500 / 117649 := hval
    _ ≤ 1 / 4 := by norm_num

open scoped Classical in

/-- Shows that the Krawtchouk tester accepts the uniform distribution and rejects a
correlation-concentrated distribution with probabilities at most the target error under the
prescribed sample bounds. -/
theorem krawtchouk_tester_correct {N k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N)
    {Δ β δ : ℝ} (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (n : ℕ) (hn : krawtCheckHalfCount N k Δ β ≤ n) (M : ℕ) (hM : krawtCheckBlockCount δ ≤ M)
    (p : FinDist (Reg N)) :
    (p = cubeUniformDist N →
      (∑ s ∈ Finset.univ.filter (fun s => krawtCheckAccepts k n M Δ β s),
          krawtCheckMass p n M s) ≤ δ) ∧
    (IsCorrelationConcentrated p Δ k β →
      (∑ s ∈ Finset.univ.filter (fun s => ¬ krawtCheckAccepts k n M Δ β s),
          krawtCheckMass p n M s) ≤ δ) := by
  constructor
  · intro hp
    subst hp
    rw [Finset.sum_congr rfl
      (fun s _ => krawtCheckMass_eq (cubeUniformDist N) n M s)]
    have hfe : Finset.univ.filter (fun s => krawtCheckAccepts k n M Δ β s)
        = Finset.univ.filter
            (fun s : Fin M → (Fin n → Reg N) × (Fin n → Reg N) =>
              M - M / 2 ≤ ∑ m,
                if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0) :=
      Finset.filter_congr fun s _ => Iff.rfl
    rw [hfe, Finset.sum_congr rfl
      (fun s _ =>
        (rfl : (cubeBlockDist (cubeUniformDist N) n).probOf s
          = ∏ m, (cubeBlockDist (cubeUniformDist N) n).prob (s m)))]
    have hE := exp_markov_count (cubeBlockDist (cubeUniformDist N) n)
      (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
        β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2)
      M (M - M / 2) (Nat.sub_le M (M / 2)) (uniform_block_bad hk hkN hΔ hβ hn)
    rw [show M - (M - M / 2) = M / 2 by omega] at hE
    exact hE.trans (majority_pow_le hδ hδ1 M hM)
  · intro hconc
    by_cases hM0 : M = 0
    · subst hM0
      have hempty : (Finset.univ.filter
          (fun s : Fin 0 → (Fin n → Reg N) × (Fin n → Reg N) =>
            ¬ krawtCheckAccepts k n 0 Δ β s)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro s hs
        rw [Finset.mem_filter] at hs
        simp only [krawtCheckAccepts, Fin.sum_univ_zero] at hs
        exact absurd (Nat.zero_le 0) hs.2
      rw [hempty, Finset.sum_empty]
      exact hδ.le
    · have hM1 : 1 ≤ M := by omega
      have hC1' : 1 ≤ (Nat.choose N k : ℝ) := Nat.one_le_cast.mpr (Nat.choose_pos hkN)
      have hsqrt' : 0 < Real.sqrt (2 * (Nat.choose N k : ℝ)) :=
        Real.sqrt_pos.mpr (by nlinarith [hC1'])
      have hhc' : 0 < krawtCheckHalfCount N k Δ β :=
        Nat.ceil_pos.mpr (div_pos (mul_pos (by norm_num : (0 : ℝ) < 400) hsqrt')
          (mul_pos hβ hΔ))
      have hn0' : 0 < n := lt_of_lt_of_le hhc' hn
      have hsub : (Finset.univ.filter (fun s => ¬ krawtCheckAccepts k n M Δ β s))
          ⊆ (Finset.univ.filter
              (fun s : Fin M → (Fin n → Reg N) × (Fin n → Reg N) =>
                M / 2 + 1 ≤ ∑ m,
                  if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)) := by
        intro s hs
        rw [Finset.mem_filter] at hs ⊢
        refine ⟨hs.1, ?_⟩
        have hna : (∑ m, if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
            < M - M / 2 := by
          simp only [krawtCheckAccepts] at hs
          exact not_le.mp hs.2
        have hsplit : ∀ m : Fin M,
            ((if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
              + (if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0))
              = 1 := by
          intro m
          by_cases h : β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 <;>
            simp [h]
        have hsum : (∑ m : Fin M,
              if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
            + (∑ m : Fin M,
                if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
              = M := by
          calc (∑ m : Fin M,
                  if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
                + (∑ m : Fin M,
                    if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
              = ∑ m : Fin M,
                  ((if β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)
                    + (if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0)) :=
                (Finset.sum_add_distrib ..).symm
            _ = ∑ m : Fin M, 1 := Finset.sum_congr rfl fun m _ => hsplit m
            _ = M := by simp
        omega
      have hE' := exp_markov_count (cubeBlockDist p n)
        (fun b : (Fin n → Reg N) × (Fin n → Reg N) =>
          ¬ β * Δ / 50 ≤ krawtchoukStatistic k n b.1 b.2)
        M (M / 2 + 1) (by omega)
        (concentrated_block_bad p hconc hk hkN hΔ hΔ1 hβ hβ1 hn hn0')
      rw [Finset.sum_congr rfl (fun s _ => krawtCheckMass_eq p n M s)]
      calc (∑ s ∈ Finset.univ.filter (fun s => ¬ krawtCheckAccepts k n M Δ β s),
              (cubeBlockDist p n).probOf s)
          ≤ ∑ s ∈ Finset.univ.filter
              (fun s : Fin M → (Fin n → Reg N) × (Fin n → Reg N) =>
                M / 2 + 1 ≤ ∑ m,
                  if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0),
              (cubeBlockDist p n).probOf s :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub
              (fun s _ _ => Finset.prod_nonneg fun m _ => (cubeBlockDist p n).nonneg _)
        _ = ∑ s ∈ Finset.univ.filter
              (fun s : Fin M → (Fin n → Reg N) × (Fin n → Reg N) =>
                M / 2 + 1 ≤ ∑ m,
                  if ¬ β * Δ / 50 ≤ krawtchoukStatistic k n (s m).1 (s m).2 then 1 else 0),
              ∏ m, (cubeBlockDist p n).prob (s m) :=
            Finset.sum_congr rfl fun s _ => rfl
        _ ≤ (3 : ℝ) ^ (M - (M / 2 + 1)) / (2 : ℝ) ^ M := hE'
        _ ≤ (3 : ℝ) ^ (M / 2) / (2 : ℝ) ^ M :=
            div_le_div_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega))
              (pow_nonneg (by norm_num) _)
        _ ≤ δ := majority_pow_le hδ hδ1 M hM

end Qatlib.Papers.MixednessTest26.PauliShadow.BooleanCube
