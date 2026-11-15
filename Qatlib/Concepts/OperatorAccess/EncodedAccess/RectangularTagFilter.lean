/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
public import Qatlib.Foundations.InstrumentCore.Measurement.Basic
public import Qatlib.Concepts.BlockEncoding.Postselection

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement


namespace Qatlib.Concepts.OperatorAccess.EncodedAccess

open Matrix Qatlib.Concepts.BlockEncoding
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false

abbrev RectangularData (I M O : Type) := I ⊕ (M ⊕ O)

abbrev RectangularWorkspace (I M O J K : Type) := Bool × ((J × K) × RectangularData I M O)

def rectInputTagFrame {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] : Matrix (RectangularData I M O) I ℂ :=
  Matrix.of fun d i => if d = Sum.inl i then (1 : ℂ) else 0

def rectMiddleTagFrame {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] : Matrix (RectangularData I M O) M ℂ :=
  Matrix.of fun d m => if d = Sum.inr (Sum.inl m) then (1 : ℂ) else 0

def rectOutputTagFrame {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] : Matrix (RectangularData I M O) O ℂ :=
  Matrix.of fun d o => if d = Sum.inr (Sum.inr o) then (1 : ℂ) else 0

def rectOutsideMiddle {I M O : Type} : RectangularData I M O → Bool
  | .inr (.inl _) => false
  | _ => true

def rectTagSwap {I M O J K : Type} :
    RectangularWorkspace I M O J K → RectangularWorkspace I M O J K :=
  fun x => (x.1 ^^ rectOutsideMiddle x.2.2, x.2)

/-- Applying the rectangular tag swap twice returns the original workspace element. -/
theorem rectTagSwap_involutive {I M O J K : Type} :
    Function.Involutive (rectTagSwap (I := I) (M := M) (O := O) (J := J) (K := K)) := by
  intro ⟨b, u⟩
  show (b ^^ rectOutsideMiddle u.2 ^^ rectOutsideMiddle u.2, u) = (b, u)
  congr 1
  cases rectOutsideMiddle u.2 <;> simp

def rectInputFrame {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {J K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (j₀ : J) (k₀ : K) : Matrix (RectangularWorkspace I M O J K) I ℂ :=
  Matrix.of fun x i => if x = (false, ((j₀, k₀), Sum.inl i)) then (1 : ℂ) else 0

def rectOutputFrame {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {J K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (j₀ : J) (k₀ : K) : Matrix (RectangularWorkspace I M O J K) O ℂ :=
  Matrix.of fun x o => if x = (false, ((j₀, k₀), Sum.inr (Sum.inr o))) then (1 : ℂ) else 0

noncomputable def rectSuccessEvent {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {J K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (j₀ : J) (k₀ : K) : Finset (RectangularWorkspace I M O J K) :=
  Finset.univ.filter fun x =>
    x.1 = false ∧ x.2.1 = (j₀, k₀) ∧ ∃ o, x.2.2 = Sum.inr (Sum.inr o)

noncomputable def rectMiddleFilter {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {J K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] :
    Matrix (RectangularWorkspace I M O J K) (RectangularWorkspace I M O J K) ℂ :=
  permMatrix (rectTagSwap (I := I) (M := M) (O := O) (J := J) (K := K))

noncomputable def rectFilteredProduct {I M O : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
    [Fintype O] [DecidableEq O] {J K : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    (U : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ)
    (V : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) :
    Matrix (RectangularWorkspace I M O J K) (RectangularWorkspace I M O J K) ℂ :=
  TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight V) * rectMiddleFilter *
    TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U)

/-- A matrix embedding basis vectors along an injective map is an isometry. -/
private theorem isIsometry_of_delta {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] {f : Y → X} (hf : Function.Injective f) (V : Matrix X Y ℂ)
    (hV : ∀ x y, V x y = if x = f y then (1 : ℂ) else 0) : IsIsometry V := by
  unfold IsIsometry
  ext y₁ y₂
  simp only [Matrix.conjTranspose_apply, Matrix.mul_apply, hV, Matrix.one_apply]
  by_cases h : y₁ = y₂
  · subst h
    rw [Finset.sum_eq_single (f y₁)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro x _
      have hne : f y₁ ≠ f y₂ := fun hh => h (hf hh)
      by_cases hx : x = f y₁
      · rw [hx]
        simp [hne]
      · by_cases hx' : x = f y₂
        · rw [hx']
          simp [Ne.symm hne]
        · simp [hx]

/-- A finite sum weighted by the delta at `p₀` evaluates the summand at `p₀`. -/
theorem sum_fiber_eq_left {X : Type*} [Fintype X] [DecidableEq X] (p₀ : X) (F : X → ℂ) :
    ∑ x, (if p₀ = x then (1 : ℂ) else 0) * F x = F p₀ := by
  rw [Finset.sum_eq_single p₀]
  · simp
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb), zero_mul]
  · simp

/-- Right multiplication distributes over a finite sum of complex numbers. -/
theorem sum_mul_bridge {X : Type*} [Fintype X] (g : X → ℂ) (c : ℂ) :
    (∑ y : X, g y) * c = ∑ y : X, g y * c := Finset.sum_mul _ _ _

/-- Left multiplication distributes over a finite sum of complex numbers. -/
theorem mul_sum_bridge {X : Type*} [Fintype X] (g : X → ℂ) (c : ℂ) :
    c * ∑ y : X, g y = ∑ y : X, c * g y := Finset.mul_sum _ _ _

/-- A sum over a product type with two delta constraints evaluates at the selected pair. -/
theorem sum_prod_collapse {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] (x₀ : X) (y₀ : Y) (H : X × Y → ℂ) :
    ∑ q : X × Y, (if x₀ = q.1 then (1 : ℂ) else 0) * ((if q.2 = y₀ then (1 : ℂ) else 0) * H q)
      = H (x₀, y₀) := by
  rw [Finset.sum_eq_single (x₀, y₀)]
  · simp
  · intro q _ hq
    by_cases h1 : x₀ = q.1
    · have h2 : ¬(q.2 = y₀) := fun h2 => hq (Prod.ext h1.symm h2)
      simp [h1, h2]
    · simp [h1]
  · simp

/-- A sum over the rectangular workspace splits into sums over the flag, data, and auxiliary
pair. -/
theorem sum_workspace_split {Γ : Type*} [AddCommMonoid Γ] {I M O J K : Type}
    [Fintype J] [Fintype K] [Fintype I] [Fintype M] [Fintype O]
    (F : RectangularWorkspace I M O J K → Γ) :
    ∑ z : RectangularWorkspace I M O J K, F z
      = ∑ b : Bool, ∑ d : RectangularData I M O, ∑ q : J × K, F (b, (q, d)) := by
  have h1 : ∑ z : RectangularWorkspace I M O J K, F z
      = ∑ b : Bool, ∑ t : (J × K) × RectangularData I M O, F (b, t) :=
    Fintype.sum_prod_type F
  have h2 : ∀ b : Bool, ∑ t : (J × K) × RectangularData I M O, F (b, t)
      = ∑ d : RectangularData I M O, ∑ q : J × K, F (b, (q, d)) := fun b =>
    (Fintype.sum_prod_type fun t => F (b, t)).trans Finset.sum_comm
  rw [h1]
  exact Finset.sum_congr rfl fun b _ => h2 b

/-- A sum over the auxiliary-data product splits into sums over its two components. -/
theorem sum_aux_split {Γ : Type*} [AddCommMonoid Γ] {J K I M O : Type}
    [Fintype J] [Fintype K] [Fintype I] [Fintype M] [Fintype O]
    (F : (J × K) × RectangularData I M O → Γ) :
    ∑ t : (J × K) × RectangularData I M O, F t
      = ∑ q : J × K, ∑ d : RectangularData I M O, F (q, d) :=
  Fintype.sum_prod_type F

/-- Compression by delta embedding matrices selects the corresponding matrix entry. -/
private theorem compress_delta_entry {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype Z] [DecidableEq Z] {c : Y → X} {e : Z → X}
    (L : Matrix X Y ℂ) (M : Matrix X X ℂ) (R : Matrix X Z ℂ)
    (hL : ∀ x a, L x a = if x = c a then (1 : ℂ) else 0)
    (hR : ∀ x b, R x b = if x = e b then (1 : ℂ) else 0) (a : Y) (b : Z) :
    compress L M R a b = M (c a) (e b) := by
  have hMR : ∀ x : X, (M * R) x b = M x (e b) := by
    intro x
    simp only [Matrix.mul_apply, hR]
    exact sum_fiber_mul_right (e b) fun y => M x y
  have hLc : ∀ x : X, (Lᴴ) a x = if x = c a then (1 : ℂ) else 0 := by
    intro x
    rw [Matrix.conjTranspose_apply, hL x a]
    by_cases h : x = c a <;> simp [h]
  have step1 : compress L M R a b = ∑ x : X, (Lᴴ) a x * (M * R) x b := by
    show (Lᴴ * M * R) a b = _
    rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [step1]
  refine (Finset.sum_congr rfl fun x _ => ?_).trans (sum_fiber_mul_left (c a) fun x => M x (e b))
  rw [hMR x, hLc x]

section
variable {I M O J K : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
  [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

/-- The rectangular input frame is the delta embedding at the false flag and selected input
tags. -/
private theorem inputFrame_delta (j₀ : J) (k₀ : K) (x : RectangularWorkspace I M O J K) (i : I) :
    rectInputFrame j₀ k₀ x i = if x = (false, ((j₀, k₀), Sum.inl i)) then (1 : ℂ) else 0 := rfl

/-- The rectangular output frame is the delta embedding at the false flag and selected output
tags. -/
private theorem outputFrame_delta (j₀ : J) (k₀ : K) (x : RectangularWorkspace I M O J K) (o : O) :
    rectOutputFrame j₀ k₀ x o =
      if x = (false, ((j₀, k₀), Sum.inr (Sum.inr o))) then (1 : ℂ) else 0 := rfl

/-- The input tag frame is the delta embedding of the input summand. -/
private theorem rectInputTagFrame_delta (d : RectangularData I M O) (i : I) :
    rectInputTagFrame (I := I) (M := M) (O := O) d i =
      if d = Sum.inl i then (1 : ℂ) else 0 := rfl

/-- The middle tag frame is the delta embedding of the middle summand. -/
private theorem rectMiddleTagFrame_delta (d : RectangularData I M O) (m : M) :
    rectMiddleTagFrame (I := I) (M := M) (O := O) d m =
      if d = Sum.inr (Sum.inl m) then (1 : ℂ) else 0 := rfl

/-- The output tag frame is the delta embedding of the output summand. -/
private theorem rectOutputTagFrame_delta (d : RectangularData I M O) (o : O) :
    rectOutputTagFrame (I := I) (M := M) (O := O) d o =
      if d = Sum.inr (Sum.inr o) then (1 : ℂ) else 0 := rfl

/-- Composing an encoding fiber with the output tag frame gives the delta embedding at the
chosen fiber and output tag. -/
private theorem fiberOutputTag_delta (k₀ : K) (x : K × RectangularData I M O) (o : O) :
    (encodingFiber (I := RectangularData I M O) k₀ * rectOutputTagFrame (I := I) (M := M) (O := O)) x o =
      if x = (k₀, Sum.inr (Sum.inr o)) then (1 : ℂ) else 0 := by
  obtain ⟨k, d⟩ := x
  simp only [Matrix.mul_apply, encodingFiber_apply, rectOutputTagFrame_delta]
  by_cases hk : k = k₀
  · rw [hk]
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb
      have hne : ¬((k₀, d) = (k₀, b)) := by
        intro h
        apply hb
        injection h with _ h2
        exact h2.symm
      rw [ite_eq_right hne, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ d) h
  · rw [Finset.sum_eq_zero]
    · have hne : ¬((k, d) = (k₀, Sum.inr (Sum.inr o))) := fun h => hk (congrArg Prod.fst h)
      rw [ite_eq_right hne]
    · intro b _
      have hne : ¬((k, d) = (k₀, b)) := fun h => hk (congrArg Prod.fst h)
      rw [ite_eq_right hne, zero_mul]

/-- Composing an encoding fiber with the middle tag frame gives the delta embedding at the
chosen fiber and middle tag. -/
private theorem fiberMiddleTag_delta (k₀ : K) (x : K × RectangularData I M O) (m : M) :
    (encodingFiber (I := RectangularData I M O) k₀ * rectMiddleTagFrame (I := I) (M := M) (O := O)) x m =
      if x = (k₀, Sum.inr (Sum.inl m)) then (1 : ℂ) else 0 := by
  obtain ⟨k, d⟩ := x
  simp only [Matrix.mul_apply, encodingFiber_apply, rectMiddleTagFrame_delta]
  by_cases hk : k = k₀
  · rw [hk]
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb
      have hne : ¬((k₀, d) = (k₀, b)) := by
        intro h
        apply hb
        injection h with _ h2
        exact h2.symm
      rw [ite_eq_right hne, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ d) h
  · rw [Finset.sum_eq_zero]
    · have hne : ¬((k, d) = (k₀, Sum.inr (Sum.inl m))) := fun h => hk (congrArg Prod.fst h)
      rw [ite_eq_right hne]
    · intro b _
      have hne : ¬((k, d) = (k₀, b)) := fun h => hk (congrArg Prod.fst h)
      rw [ite_eq_right hne, zero_mul]

/-- The middle tag embedding in the `J` fiber has the stated delta entries. -/
private theorem fiberMiddleTag_delta' (j₀ : J) (x : J × RectangularData I M O) (m : M) :
    (encodingFiber (I := RectangularData I M O) j₀ * rectMiddleTagFrame (I := I) (M := M) (O := O)) x m =
      if x = (j₀, Sum.inr (Sum.inl m)) then (1 : ℂ) else 0 :=
  fiberMiddleTag_delta (K := J) j₀ x m

/-- Composing an encoding fiber with the input tag frame gives the delta embedding at the chosen
fiber and input tag. -/
private theorem fiberInputTag_delta (j₀ : J) (x : J × RectangularData I M O) (i : I) :
    (encodingFiber (I := RectangularData I M O) j₀ * rectInputTagFrame (I := I) (M := M) (O := O)) x i =
      if x = (j₀, Sum.inl i) then (1 : ℂ) else 0 := by
  obtain ⟨k, d⟩ := x
  simp only [Matrix.mul_apply, encodingFiber_apply, rectInputTagFrame_delta]
  by_cases hk : k = j₀
  · rw [hk]
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb
      have hne : ¬((j₀, d) = (j₀, b)) := by
        intro h
        apply hb
        injection h with _ h2
        exact h2.symm
      rw [ite_eq_right hne, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ d) h
  · rw [Finset.sum_eq_zero]
    · have hne : ¬((k, d) = (j₀, Sum.inl i)) := fun h => hk (congrArg Prod.fst h)
      rw [ite_eq_right hne]
    · intro b _
      have hne : ¬((k, d) = (j₀, b)) := fun h => hk (congrArg Prod.fst h)
      rw [ite_eq_right hne, zero_mul]

/-- The compressed right rectangular corner selects the output-to-middle entry at the chosen
fiber. -/
theorem rectRightCorner_entry (k₀ : K)
    (V : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) (o : O) (m : M) :
    compress (encodingFiber k₀ * rectOutputTagFrame (I := I) (M := M) (O := O)) V
        (encodingFiber k₀ * rectMiddleTagFrame) o m
      = V (k₀, Sum.inr (Sum.inr o)) (k₀, Sum.inr (Sum.inl m)) :=
  compress_delta_entry _ V _ (fiberOutputTag_delta k₀) (fiberMiddleTag_delta k₀) o m

/-- The compressed left rectangular corner selects the middle-to-input entry at the chosen
fiber. -/
theorem rectLeftCorner_entry (j₀ : J)
    (U : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ) (m : M) (i : I) :
    compress (encodingFiber j₀ * rectMiddleTagFrame (I := I) (M := M) (O := O)) U
        (encodingFiber j₀ * rectInputTagFrame) m i
      = U (j₀, Sum.inr (Sum.inl m)) (j₀, Sum.inl i) :=
  compress_delta_entry _ U _ (fiberMiddleTag_delta' j₀) (fiberInputTag_delta j₀) m i

/-- The rectangular tag and workspace frames are isometries, and the output range projector is
the success-event projector. -/
theorem rectangularTagFilter_frames_and_projector (j₀ : J) (k₀ : K) :
    IsIsometry (rectInputTagFrame (I := I) (M := M) (O := O)) ∧
    IsIsometry (rectMiddleTagFrame (I := I) (M := M) (O := O)) ∧
    IsIsometry (rectOutputTagFrame (I := I) (M := M) (O := O)) ∧
    IsIsometry (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) ∧
    IsIsometry (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀) ∧
    rangeProjector (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀) =
      Projector (rectSuccessEvent (I := I) (M := M) (O := O) j₀ k₀) := by
  have h1 : IsIsometry (rectInputTagFrame (I := I) (M := M) (O := O)) :=
    isIsometry_of_delta (f := Sum.inl) Sum.inl_injective _ fun _ _ => rfl
  have h2 : IsIsometry (rectMiddleTagFrame (I := I) (M := M) (O := O)) :=
    isIsometry_of_delta (f := Sum.inr ∘ Sum.inl)
      (Function.Injective.comp Sum.inr_injective Sum.inl_injective) _ fun _ _ => rfl
  have h3 : IsIsometry (rectOutputTagFrame (I := I) (M := M) (O := O)) :=
    isIsometry_of_delta (f := Sum.inr ∘ Sum.inr)
      (Function.Injective.comp Sum.inr_injective Sum.inr_injective) _ fun _ _ => rfl
  have h4 : IsIsometry (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) :=
    isIsometry_of_delta (f := fun i => (false, ((j₀, k₀), Sum.inl i)))
      (fun a b h => by
        injection h with _ h1
        injection h1 with _ h2
        injection h2 with h3) _ fun _ _ => rfl
  have h5 : IsIsometry (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀) :=
    isIsometry_of_delta (f := fun o => (false, ((j₀, k₀), Sum.inr (Sum.inr o))))
      (fun a b h => by
        injection h with _ h1
        injection h1 with _ h2
        injection h2 with h3
        injection h3 with h4) _
        fun _ _ => rfl
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  have hinj : Function.Injective
      (fun o : O => (false, ((j₀, k₀), (Sum.inr (Sum.inr o) : RectangularData I M O)))) :=
    fun a b h => by
        injection h with _ h1
        injection h1 with _ h2
        injection h2 with h3
        injection h3 with h4
  ext x y
  simp only [rangeProjector, Matrix.mul_apply, Matrix.conjTranspose_apply, outputFrame_delta,
    apply_ite, Projector, Matrix.diagonal_apply,
    rectSuccessEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxy : x = y
  · subst y
    by_cases hx : ∃ o : O, x = (false, ((j₀, k₀), Sum.inr (Sum.inr o)))
    · obtain ⟨o₀, hx₀⟩ := hx
      subst x
      rw [Finset.sum_eq_single o₀]
      · simp
      · intro b _ hb
        have hne : ¬(((false, ((j₀, k₀), Sum.inr (Sum.inr o₀))) :
              RectangularWorkspace I M O J K) =
            (false, ((j₀, k₀), Sum.inr (Sum.inr b)))) := by
          intro h
          injection h with _ h1
          injection h1 with _ h2
          injection h2 with h3
          injection h3 with h4
          exact absurd h4.symm hb
        simp [hne]
      · simp
    · rw [Finset.sum_eq_zero]
      · have hc : ¬(x.1 = false ∧ x.2.1 = (j₀, k₀) ∧ ∃ o, x.2.2 = Sum.inr (Sum.inr o)) := by
          rintro ⟨hb, hq, o, hd⟩
          exact hx ⟨o, by exact Prod.ext hb (Prod.ext hq hd)⟩
        simp [hc]
      · intro o _
        have hxo : ¬(x = (false, ((j₀, k₀), Sum.inr (Sum.inr o)))) := fun h => hx ⟨o, h⟩
        simp [hxo]
  · rw [Finset.sum_eq_zero]
    · simp [hxy]
    · intro o _
      by_cases hx : x = (false, ((j₀, k₀), Sum.inr (Sum.inr o)))
      · subst x
        simp [Ne.symm hxy]
      · simp [hx]

/-- The middle filter is a self-adjoint unitary that flips the flag exactly outside the middle
data summand. -/
theorem rectangularTagFilter_reversible_flag_semantics :
    rectMiddleFilter (I := I) (M := M) (O := O) (J := J) (K := K) ∈
      Matrix.unitaryGroup (RectangularWorkspace I M O J K) ℂ ∧
    (∀ (b : Bool) (p : J × K) (d : RectangularData I M O),
      ApplyGate (rectMiddleFilter (I := I) (M := M) (O := O)) (Ket (b,(p,d))) =
        Ket (b ^^ (match d with | .inr (.inl _) => false | _ => true), (p,d))) ∧
    (rectMiddleFilter (I := I) (M := M) (O := O) (J := J) (K := K))ᴴ =
      rectMiddleFilter (I := I) (M := M) (O := O) (J := J) (K := K) :=
  ⟨permMatrix_unitary rectTagSwap_involutive, fun b p d => by
    rw [show rectMiddleFilter (I := I) (M := M) (O := O) (J := J) (K := K) =
        permMatrix (rectTagSwap (I := I) (M := M) (O := O) (J := J) (K := K)) from rfl,
      applyGate_permMatrix_ket rectTagSwap_involutive]
    cases d with
    | inl i => rfl
    | inr m =>
      cases m with
      | inl m => rfl
      | inr o => rfl, permMatrix_conjTranspose rectTagSwap_involutive⟩

/-- The filtered product entry between selected input and output tags sums only over middle
tags. -/
private theorem rectFilteredProduct_delta_entry (j₀ : J) (k₀ : K)
    (U : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ)
    (V : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) (o : O) (i : I) :
    rectFilteredProduct U V (false, ((j₀, k₀), Sum.inr (Sum.inr o)))
        (false, ((j₀, k₀), Sum.inl i)) =
      ∑ m : M, V (k₀, Sum.inr (Sum.inr o)) (k₀, Sum.inr (Sum.inl m))
        * U (j₀, Sum.inr (Sum.inl m)) (j₀, Sum.inl i) := by
  have hB : ∀ z : RectangularWorkspace I M O J K,
      TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) z
          (false, ((j₀, k₀), Sum.inl i)) =
        (if z.1 = false then (1 : ℂ) else 0) *
          (U (z.2.1.1, z.2.2) (j₀, Sum.inl i) * (if z.2.1.2 = k₀ then (1 : ℂ) else 0)) := by
    intro z
    obtain ⟨b, u⟩ := z
    obtain ⟨q, d⟩ := u
    simp only [TensorGate, Matrix.kronecker_apply, Matrix.one_apply, independentLiftLeft,
      Matrix.of_apply]
  have hA : ∀ z : RectangularWorkspace I M O J K,
      TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
          (false, ((j₀, k₀), Sum.inr (Sum.inr o))) (rectTagSwap z) =
        (if (false : Bool) = z.1 ^^ rectOutsideMiddle z.2.2 then (1 : ℂ) else 0) *
          (if j₀ = z.2.1.1 then (1 : ℂ) else 0) *
          V (k₀, Sum.inr (Sum.inr o)) (z.2.1.2, z.2.2) := by
    intro z
    obtain ⟨bz, uz⟩ := z
    obtain ⟨qz, dz⟩ := uz
    simp only [TensorGate, Matrix.kronecker_apply, Matrix.one_apply, independentLiftRight,
      Matrix.of_apply, rectTagSwap]
    cases bz <;> cases rectOutsideMiddle dz <;> simp
  have hreshape : ∀ (b : Bool) (d : RectangularData I M O) (q : J × K),
      ((if (false : Bool) = b ^^ rectOutsideMiddle d then (1 : ℂ) else 0) *
            ((if j₀ = q.1 then (1 : ℂ) else 0) * V (k₀, Sum.inr (Sum.inr o)) (q.2, d)) *
          ((if b = false then (1 : ℂ) else 0) *
            (U (q.1, d) (j₀, Sum.inl i) * (if q.2 = k₀ then (1 : ℂ) else 0)))) =
        (if b = false then (1 : ℂ) else 0) *
          ((if (false : Bool) = rectOutsideMiddle d then (1 : ℂ) else 0) *
            ((if j₀ = q.1 then (1 : ℂ) else 0) *
              ((if q.2 = k₀ then (1 : ℂ) else 0) *
                (V (k₀, Sum.inr (Sum.inr o)) (q.2, d) * U (q.1, d) (j₀, Sum.inl i))))) := by
    intro b d q
    cases b <;> cases rectOutsideMiddle d <;> simp
  show ((TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V) *
      rectMiddleFilter (I := I) (M := M) (O := O) (J := J) (K := K) :
      Matrix (RectangularWorkspace I M O J K) (RectangularWorkspace I M O J K) ℂ) *
      TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) :
      Matrix (RectangularWorkspace I M O J K) (RectangularWorkspace I M O J K) ℂ)
      (false, ((j₀, k₀), Sum.inr (Sum.inr o))) (false, ((j₀, k₀), Sum.inl i)) = _
  have hFull :
      ((TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V) *
      rectMiddleFilter (I := I) (M := M) (O := O) (J := J) (K := K) :
      Matrix (RectangularWorkspace I M O J K) (RectangularWorkspace I M O J K) ℂ) *
      TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) :
      Matrix (RectangularWorkspace I M O J K) (RectangularWorkspace I M O J K) ℂ)
      (false, ((j₀, k₀), Sum.inr (Sum.inr o))) (false, ((j₀, k₀), Sum.inl i)) =
      ∑ j : RectangularWorkspace I M O J K,
        (∑ y : RectangularWorkspace I M O J K,
          (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
            (false, ((j₀, k₀), Sum.inr (Sum.inr o))) y) * rectMiddleFilter y j) *
        TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) j
          (false, ((j₀, k₀), Sum.inl i)) := rfl
  rw [hFull]
  rw [Finset.sum_congr rfl fun j _ =>
    sum_mul_bridge (fun y : RectangularWorkspace I M O J K =>
      TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
        (false, ((j₀, k₀), Sum.inr (Sum.inr o))) y * rectMiddleFilter y j)
      (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) j
        (false, ((j₀, k₀), Sum.inl i)))]
  simp only [rectMiddleFilter, permMatrix, Matrix.of_apply]
  have hresh : ∀ (j y : RectangularWorkspace I M O J K),
      ((TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
          (false, ((j₀, k₀), Sum.inr (Sum.inr o))) y *
            (if y = rectTagSwap j then (1 : ℂ) else 0)) *
          TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) j
            (false, ((j₀, k₀), Sum.inl i))) =
        ((TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
            (false, ((j₀, k₀), Sum.inr (Sum.inr o))) y *
          TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) j
            (false, ((j₀, k₀), Sum.inl i))) *
          (if y = rectTagSwap j then (1 : ℂ) else 0)) := fun _ _ => by ring
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => hresh j y]
  rw [Finset.sum_congr rfl fun j _ =>
    sum_fiber_mul_right (rectTagSwap j) fun y : RectangularWorkspace I M O J K =>
      (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
        (false, ((j₀, k₀), Sum.inr (Sum.inr o))) y *
        TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) j
          (false, ((j₀, k₀), Sum.inl i)))]
  have hper : ∀ j : RectangularWorkspace I M O J K,
      (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight (J := J) V)
          (false, ((j₀, k₀), Sum.inr (Sum.inr o))) (rectTagSwap j)) *
        TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft U) j
          (false, ((j₀, k₀), Sum.inl i)) =
        ((if (false : Bool) = j.1 ^^ rectOutsideMiddle j.2.2 then (1 : ℂ) else 0) *
            ((if j₀ = j.2.1.1 then (1 : ℂ) else 0) *
              V (k₀, Sum.inr (Sum.inr o)) (j.2.1.2, j.2.2))) *
          ((if j.1 = false then (1 : ℂ) else 0) *
            (U (j.2.1.1, j.2.2) (j₀, Sum.inl i) *
              (if j.2.1.2 = k₀ then (1 : ℂ) else 0))) := by
    intro j
    rw [hA j, hB j]
    ring
  rw [Finset.sum_congr rfl fun j _ => hper j]
  rw [sum_workspace_split]
  (try dsimp only)
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun q _ => hreshape b d q]
  have hcollapse : ∀ (b : Bool) (d : RectangularData I M O),
      (∑ q : J × K,
          (if b = false then (1 : ℂ) else 0) *
            ((if (false : Bool) = rectOutsideMiddle d then (1 : ℂ) else 0) *
              ((if j₀ = q.1 then (1 : ℂ) else 0) *
                ((if q.2 = k₀ then (1 : ℂ) else 0) *
                  (V (k₀, Sum.inr (Sum.inr o)) (q.2, d) *
                    U (q.1, d) (j₀, Sum.inl i)))))) =
        (if b = false then (1 : ℂ) else 0) *
          ((if (false : Bool) = rectOutsideMiddle d then (1 : ℂ) else 0) *
            (V (k₀, Sum.inr (Sum.inr o)) (k₀, d) * U (j₀, d) (j₀, Sum.inl i))) := by
    intro b d
    rw [← mul_sum_bridge (X := J × K) (c := if b = false then (1 : ℂ) else 0),
      ← mul_sum_bridge (X := J × K)
        (c := if (false : Bool) = rectOutsideMiddle d then (1 : ℂ) else 0),
      sum_prod_collapse j₀ k₀ fun q : J × K =>
        V (k₀, Sum.inr (Sum.inr o)) (q.2, d) * U (q.1, d) (j₀, Sum.inl i)]
  rw [Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => hcollapse b d]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun d _ =>
    sum_fiber_mul_left false fun _ : Bool =>
      (if (false : Bool) = rectOutsideMiddle d then (1 : ℂ) else 0) *
        (V (k₀, Sum.inr (Sum.inr o)) (k₀, d) * U (j₀, d) (j₀, Sum.inl i))]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [rectOutsideMiddle]

/-- Compression of the filtered product equals the product of the rectangular corners, and
unitary factors yield a unitary filtered product. -/
theorem rectangularTagFilter_exact_compressed_product (j₀ : J) (k₀ : K)
    (U : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ)
    (V : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀)
        (rectFilteredProduct U V) (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) =
      Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber k₀ * rectOutputTagFrame) V
          (encodingFiber k₀ * rectMiddleTagFrame) *
        Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber j₀ * rectMiddleTagFrame) U
          (encodingFiber j₀ * rectInputTagFrame) ∧
    (U ∈ Matrix.unitaryGroup (J × RectangularData I M O) ℂ →
      V ∈ Matrix.unitaryGroup (K × RectangularData I M O) ℂ →
      rectFilteredProduct U V ∈ Matrix.unitaryGroup (RectangularWorkspace I M O J K) ℂ) := by
  refine ⟨?_, fun hU hV => ?_⟩
  · ext o i
    rw [compress_delta_entry _ (rectFilteredProduct U V) _ (outputFrame_delta j₀ k₀)
      (inputFrame_delta j₀ k₀), rectFilteredProduct_delta_entry j₀ k₀ U V o i,
      Matrix.mul_apply]
    simp only [rectRightCorner_entry, rectLeftCorner_entry]
  · exact (Matrix.unitaryGroup _ ℂ).mul_mem
      ((Matrix.unitaryGroup _ ℂ).mul_mem
        (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem (independentLiftRight_unitary hV))
        (permMatrix_unitary rectTagSwap_involutive))
      (tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem (independentLiftLeft_unitary hU))

/-- The unfiltered compressed product sums over all data tags, including tags outside the middle
summand. -/
theorem rectangularTagFilter_unfiltered_corner (j₀ : J) (k₀ : K)
    (U : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ)
    (V : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) (o : O) (i : I) :
    Qatlib.Concepts.Execution.WorkspaceCP.compress (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀)
        (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight V * independentLiftLeft U))
        (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) o i
      = ∑ d : RectangularData I M O,
          V (k₀, Sum.inr (Sum.inr o)) (k₀, d) * U (j₀, d) (j₀, Sum.inl i) := by
  have hZ : ∀ (x y : RectangularWorkspace I M O J K),
      (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight V * independentLiftLeft U)) x y =
        (if x.1 = y.1 then (1 : ℂ) else 0) *
          (∑ t : (J × K) × RectangularData I M O,
            (if x.2.1.1 = t.1.1 then (1 : ℂ) else 0) *
              (V (x.2.1.2, x.2.2) (t.1.2, t.2) *
                (U (t.1.1, t.2) (y.2.1.1, y.2.2) * (if t.1.2 = y.2.1.2 then (1 : ℂ) else 0)))) := by
    intro x y
    obtain ⟨bx, ux⟩ := x
    obtain ⟨qx, dx⟩ := ux
    obtain ⟨bw, uy⟩ := y
    obtain ⟨qy, dy⟩ := uy
    simp only [TensorGate, Matrix.kronecker_apply, Matrix.one_apply, Matrix.mul_apply,
      independentLiftRight, independentLiftLeft, Matrix.of_apply]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [compress_delta_entry _ _ _ (outputFrame_delta j₀ k₀) (inputFrame_delta j₀ k₀), hZ]
  (try dsimp only)
  simp only [ite_true, one_mul]
  rw [sum_aux_split]
  (try dsimp only)
  have hresh : ∀ (q : J × K) (d : RectangularData I M O),
      ((if j₀ = q.1 then (1 : ℂ) else 0) *
            (V (k₀, Sum.inr (Sum.inr o)) (q.2, d) *
              (U (q.1, d) (j₀, Sum.inl i) * (if q.2 = k₀ then (1 : ℂ) else 0)))) =
        (if j₀ = q.1 then (1 : ℂ) else 0) *
          ((if q.2 = k₀ then (1 : ℂ) else 0) *
            (V (k₀, Sum.inr (Sum.inr o)) (q.2, d) * U (q.1, d) (j₀, Sum.inl i))) :=
    fun q d => by ring
  simp only [hresh]
  have hq : ∀ q : J × K,
      (∑ d : RectangularData I M O,
          (if j₀ = q.1 then (1 : ℂ) else 0) *
            ((if q.2 = k₀ then (1 : ℂ) else 0) *
              (V (k₀, Sum.inr (Sum.inr o)) (q.2, d) * U (q.1, d) (j₀, Sum.inl i)))) =
      (if j₀ = q.1 then (1 : ℂ) else 0) *
        ((if q.2 = k₀ then (1 : ℂ) else 0) *
          ∑ d : RectangularData I M O,
            V (k₀, Sum.inr (Sum.inr o)) (q.2, d) * U (q.1, d) (j₀, Sum.inl i)) := by
    intro q
    rw [← mul_sum_bridge (X := RectangularData I M O)
        (c := if j₀ = q.1 then (1 : ℂ) else 0),
      ← mul_sum_bridge (X := RectangularData I M O)
        (c := if q.2 = k₀ then (1 : ℂ) else 0)]
  rw [Finset.sum_congr rfl fun q _ => hq q]
  rw [sum_prod_collapse j₀ k₀ fun q : J × K =>
    ∑ d : RectangularData I M O,
      V (k₀, Sum.inr (Sum.inr o)) (q.2, d) * U (q.1, d) (j₀, Sum.inl i)]

/-- The rectangular filtered product block-encodes `B * A` with multiplied scale and the stated
combined error bound. -/
theorem rectangularTagFilter_approximate_block_product (j₀ : J) (k₀ : K) (A : Matrix M I ℂ)
    (B : Matrix O M ℂ) (U : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ)
    (V : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) (α β ε η : ℝ)
    (h1 : BlockEncoding A U (encodingFiber j₀ * rectMiddleTagFrame)
        (encodingFiber j₀ * rectInputTagFrame) α ε)
    (h2 : BlockEncoding B V (encodingFiber k₀ * rectOutputTagFrame)
        (encodingFiber k₀ * rectMiddleTagFrame) β η) :
    BlockEncoding (B * A) (rectFilteredProduct U V)
      (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀)
      (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) (α * β) (β * ε + α * η + ε * η) := by
  have hmid : IsIsometry (rectMiddleTagFrame (I := I) (M := M) (O := O)) :=
    isIsometry_of_delta (f := Sum.inr ∘ Sum.inl)
      (Function.Injective.comp Sum.inr_injective Sum.inl_injective) _ fun _ _ => rfl
  have hout : IsIsometry (rectOutputTagFrame (I := I) (M := M) (O := O)) :=
    isIsometry_of_delta (f := Sum.inr ∘ Sum.inr)
      (Function.Injective.comp Sum.inr_injective Sum.inr_injective) _ fun _ _ => rfl
  have hin : IsIsometry (rectInputTagFrame (I := I) (M := M) (O := O)) :=
    isIsometry_of_delta (f := Sum.inl) Sum.inl_injective _ fun _ _ => rfl
  have h4 : IsIsometry (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) :=
    isIsometry_of_delta (f := fun i => (false, ((j₀, k₀), Sum.inl i)))
      (fun a b h => by
        injection h with _ h1
        injection h1 with _ h2
        injection h2 with h3) _ fun _ _ => rfl
  have h5 : IsIsometry (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀) :=
    isIsometry_of_delta (f := fun o => (false, ((j₀, k₀), Sum.inr (Sum.inr o))))
      (fun a b h => by
        injection h with _ h1
        injection h1 with _ h2
        injection h2 with h3
        injection h3 with h4) _
        fun _ _ => rfl
  have hLU : IsIsometry (encodingFiber j₀ * rectMiddleTagFrame (I := I) (M := M) (O := O)) :=
    IsIsometry.mul (encodingFiber_isIsometry j₀) hmid
  have hRU : IsIsometry (encodingFiber j₀ * rectInputTagFrame (I := I) (M := M) (O := O)) :=
    IsIsometry.mul (encodingFiber_isIsometry j₀) hin
  have hLV : IsIsometry (encodingFiber k₀ * rectOutputTagFrame (I := I) (M := M) (O := O)) :=
    IsIsometry.mul (encodingFiber_isIsometry k₀) hout
  have hRV : IsIsometry (encodingFiber k₀ * rectMiddleTagFrame (I := I) (M := M) (O := O)) :=
    IsIsometry.mul (encodingFiber_isIsometry k₀) hmid
  have hcU : ‖compress (encodingFiber j₀ * rectMiddleTagFrame) U
      (encodingFiber j₀ * rectInputTagFrame)‖ ≤ 1 :=
    l2_norm_compress_le_one hLU h1.unitary hRU
  have hcV : ‖compress (encodingFiber k₀ * rectOutputTagFrame) V
      (encodingFiber k₀ * rectMiddleTagFrame)‖ ≤ 1 :=
    l2_norm_compress_le_one hLV h2.unitary hRV
  have hAnorm : ‖A‖ ≤ ε + α := by
    calc ‖A‖ = ‖(A - α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
            (encodingFiber j₀ * rectInputTagFrame)) +
          α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
            (encodingFiber j₀ * rectInputTagFrame)‖ := by rw [sub_add_cancel]
      _ ≤ ‖A - α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
            (encodingFiber j₀ * rectInputTagFrame)‖ +
          ‖α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
            (encodingFiber j₀ * rectInputTagFrame)‖ := norm_add_le _ _
      _ ≤ ε + α := by
          refine add_le_add h1.error_le ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos h1.normalization_pos]
          exact (mul_le_mul_of_nonneg_left hcU (le_of_lt h1.normalization_pos)).trans_eq
            (mul_one α)
  have hexpr : (α * β) • compress (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀)
        (rectFilteredProduct U V) (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀) =
      (β • compress (encodingFiber k₀ * rectOutputTagFrame) V
          (encodingFiber k₀ * rectMiddleTagFrame)) *
        (α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
          (encodingFiber j₀ * rectInputTagFrame)) := by
    rw [(rectangularTagFilter_exact_compressed_product j₀ k₀ U V).1]
    ext o i
    simp only [Matrix.smul_apply, Matrix.mul_apply, Complex.real_smul, Complex.ofReal_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  refine ⟨(rectangularTagFilter_exact_compressed_product j₀ k₀ U V).2 h1.unitary h2.unitary,
    h5, h4, mul_pos h1.normalization_pos h2.normalization_pos,
    add_nonneg (add_nonneg (mul_nonneg (le_of_lt h2.normalization_pos) h1.error_nonneg)
        (mul_nonneg (le_of_lt h1.normalization_pos) h2.error_nonneg))
      (mul_nonneg h1.error_nonneg h2.error_nonneg), ?_⟩
  calc ‖B * A - (α * β) • compress (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀)
          (rectFilteredProduct U V) (rectInputFrame (I := I) (M := M) (O := O) j₀ k₀)‖
      = ‖B * A - (β • compress (encodingFiber k₀ * rectOutputTagFrame) V
              (encodingFiber k₀ * rectMiddleTagFrame)) *
            (α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
              (encodingFiber j₀ * rectInputTagFrame))‖ := by rw [hexpr]
    _ ≤ ‖B - β • compress (encodingFiber k₀ * rectOutputTagFrame) V
            (encodingFiber k₀ * rectMiddleTagFrame)‖ * ‖A‖ +
          ‖β • compress (encodingFiber k₀ * rectOutputTagFrame) V
            (encodingFiber k₀ * rectMiddleTagFrame)‖ *
          ‖A - α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
            (encodingFiber j₀ * rectInputTagFrame)‖ :=
        l2_norm_rect_mul_sub_mul_le B
          (β • compress (encodingFiber k₀ * rectOutputTagFrame) V
            (encodingFiber k₀ * rectMiddleTagFrame)) A
          (α • compress (encodingFiber j₀ * rectMiddleTagFrame) U
            (encodingFiber j₀ * rectInputTagFrame))
    _ ≤ η * (ε + α) + β * ε := by
        refine add_le_add (mul_le_mul h2.error_le hAnorm (norm_nonneg A) h2.error_nonneg) ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos h2.normalization_pos]
        exact mul_le_mul
          ((mul_le_mul_of_nonneg_left hcV (le_of_lt h2.normalization_pos)).trans_eq (mul_one β))
          h1.error_le (norm_nonneg _) (le_of_lt h2.normalization_pos)
    _ = β * ε + α * η + ε * η := by ring

end

end Qatlib.Concepts.OperatorAccess.EncodedAccess
