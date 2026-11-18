/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.MainResults.GenExpect
public import Qatlib.Papers.ExactSimon97.MainResults.TotalQuery
public import Qatlib.Papers.ExactSimon97.MainResults.PolylogProgress
public import Qatlib.Papers.ExactSimon97.MainResults.Cor10Assembly

@[expose] public section

/-!
# Regression instances for the ExactSimon97 ALG fill modules

Concrete satisfiable checks on small groups:

* `GenExpect` (§2 expectation): the `2·log₂|H|` truncated-tail bound instantiated at
  `H = ⊤` of `ZMod 2 × ZMod 2`; a two-step strict subgroup chain realizing the
  chain-length reason; the single-sample stall bound at a proper subgroup.
* `TotalQuery` (§4.3 optimization): an all-zero probe interface with its permanence
  witness, the one-pass schedule performing exactly `n = 2` experiments, a terminal
  naive run, and the agreement instance at `k = 0`.
* `PolylogProgress` (§6 fraction): a marking predicate on `AbGroup 2` vanishing on
  the trivial subgroup with the progress instance, the numeric polylog call bound
  `6 ≤ 3 * log₂ 16`, and the fraction-mass interface instantiation.
* `Cor10Assembly`: genuinely satisfiable fair-coin scale qualifications and an
  explicit rejection of the success-one cheating profile. This tests conditional
  assembly, not the full oracle separation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped BigOperators Classical

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Papers.ExactSimon97.MainResults
open Qatlib.Papers.NoncommHSP98.MainResults
open Qatlib.Papers.ExactSimon97.MainResults

section GenExpectInst

/-- The ambient group `ZMod 2 × ZMod 2` has four elements, and so does its top
subgroup. -/
private theorem cardTop4 :
    Fintype.card ↥(⊤ : AddSubgroup (ZMod 2 × ZMod 2)) = 4 := by
  have h2 := Fintype.card_congr
    (AddSubgroup.topEquiv (G := ZMod 2 × ZMod 2)).toEquiv
  have h3 : Fintype.card (ZMod 2 × ZMod 2) = 4 := by decide
  omega

/-- The §2 expectation bound instantiated at `H = ⊤` of `ZMod 2 × ZMod 2`. -/
example (K' : ℕ) :
    ∑ k ∈ Finset.range K',
      failProbAt (⊤ : AddSubgroup (ZMod 2 × ZMod 2)) k ≤
      2 * Real.logb 2 ((Fintype.card ↥(⊤ : AddSubgroup (ZMod 2 × ZMod 2)) : ℕ) : ℝ) :=
  expected_le_two_log ⊤ (by simp) K'

/-- The bottom subgroup of `ZMod 2 × ZMod 2` is proper. -/
private theorem botLtTop : (⊥ : AddSubgroup (ZMod 2 × ZMod 2)) < ⊤ := by
  refine ⟨bot_le, ?_⟩
  intro h
  have h1 : ((1 : ZMod 2), (0 : ZMod 2)) ∈ (⊥ : AddSubgroup (ZMod 2 × ZMod 2)) :=
    h (by simp)
  simp only [AddSubgroup.mem_bot] at h1
  exact absurd h1 (by decide)

/-- A two-step strict subgroup chain in `ZMod 2 × ZMod 2` realizes the
chain-length reason: `1 ≤ log₂ 4`. -/
example :
    (1 : ℕ) ≤ Nat.log 2 (Fintype.card ↥(⊤ : AddSubgroup (ZMod 2 × ZMod 2))) := by
  refine chain_le_log
    (fun s => if s = 0 then (⊥ : AddSubgroup (ZMod 2 × ZMod 2)) else ⊤) 1 ?_ ⊤ ?_
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      show (⊥ : AddSubgroup (ZMod 2 × ZMod 2)) < ⊤
      exact botLtTop
    · omega
  · intro s _; exact le_top

/-- The single-sample stall bound instantiated at a proper subgroup. -/
example :
    FinDist.probEvent (L := 1) (unifOnSub (⊤ : AddSubgroup (ZMod 2 × ZMod 2)))
        (fun ω => (ω 0 : ZMod 2 × ZMod 2) ∈ (⊥ : AddSubgroup (ZMod 2 × ZMod 2))) ≤
      1 / 2 :=
  stallProb_le_half ⊤ ⊥ bot_le botLtTop

end GenExpectInst

section TotalQueryInst

/-- The terminal fixture returns no output on any coordinate. -/
private abbrev zeroProbe : CoordProbe 2 := fun _ _ => none

/-- Zero probes remain zero along every reachable update. -/
private theorem zeroPerm : Permanence zeroProbe :=
  ⟨fun _ _ _ _ h => h⟩

/-- The one-pass schedule performs exactly two experiments on two coordinates. -/
example (p : Fin 2 → Bool) : onePassCalls zeroProbe 0 p = 2 :=
  onePass_total zeroProbe p

/-- A terminal naive run on the all-zero probe interface. -/
private example (p : Fin 2 → Bool) : NaiveRun zeroProbe p ∅ :=
  NaiveRun.stop (q := zeroProbe) p ∅ (fun _ _ => rfl)

/-- The naive probe bound instantiated. -/
example (p : Fin 2 → Bool) (t : NaiveRun zeroProbe p ∅) :
    (t.depth + 1) * 2 ≤ (2 + 1) * 2 :=
  naive_probes_le t

/-- The agreement theorem instantiated at the terminal run from position zero. -/
example (p : Fin 2 → Bool) :
    onePassFrom zeroProbe 0 p = p :=
  onePass_agrees_naive zeroPerm (NaiveRun.stop (q := zeroProbe) p ∅ (fun _ _ => rfl))
    0 (by omega) (fun j hmem => absurd hmem (by simp))
    (fun j _ _ => ⟨p, .refl, rfl⟩)

/-- A nondegenerate probe: coordinate zero sets the pivot before the terminal scan. -/
private def pivotProbe : CoordProbe 2 := fun p i =>
  if i = 0 ∧ p 0 = false then some (fun _ => true) else none

/-- Zero outcomes are permanent on the actual reachable pivot states in this
nondegenerate fixture, even though they need not be permanent at unrelated states. -/
private theorem pivotPerm : Permanence pivotProbe := by
  constructor
  intro p p' hreach i hz
  cases hreach with
  | refl => exact hz
  | tail _ hstep =>
    obtain ⟨j, hj⟩ := hstep
    unfold pivotProbe at hj
    split at hj
    · rcases Option.some.inj hj with rfl
      simp [pivotProbe]
    · simp at hj

/-- The one-pass schedule actually changes the pivot on this fixture. -/
example : onePassFrom pivotProbe 0 (fun _ => false) = fun _ => true := by
  simp [onePassFrom, pivotProbe]

/-- The same fixture has a successful naive step followed by a terminal round. -/
private def pivotTrace : NaiveRun pivotProbe (fun _ => false) ∅ :=
  NaiveRun.step _ _ 0 (fun _ => true) (by simp)
    (by intro j hj; omega) (by simp [pivotProbe])
    (NaiveRun.stop _ _ (by intro i _; simp [pivotProbe]))

/-- The nondegenerate trace has one successful round and the correct final pivot. -/
example : pivotTrace.depth = 1 ∧ pivotTrace.final = fun _ => true := by
  exact ⟨rfl, rfl⟩

/-- Reachable permanence validates scheduler equivalence on a genuinely
successful pivot trace, rather than only on the terminal zero-probe fixture. -/
example : onePassFrom pivotProbe 0 (fun _ => false) = pivotTrace.final :=
  onePass_agrees_naive pivotPerm pivotTrace 0 (by omega)
    (by intro j hj; simp at hj)
    (by intro j hj _; omega)

/-- Three oracle calls per coordinate experiment give six charged calls, not two. -/
example : 3 * onePassCalls pivotProbe 0 (fun _ => false) = 6 := by
  rw [onePass_total]

end TotalQueryInst

section PolylogInst

/-- Both factors of the four-element fixture have order two. -/
private abbrev m2 : Fin 2 → ℕ := fun _ => 2

/-- Each cyclic component has nonzero order two. -/
private theorem nz2 (i : Fin 2) : NeZero (m2 i) :=
  ZeroLEOneClass.neZero.two (α := ℕ)

attribute [local instance] nz2

/-- A marking predicate on `AbGroup 2` vanishing on the trivial subgroup. -/
private abbrev nzPred : AbGroup 2 m2 → Bool := fun g => g ≠ 0

/-- The nonzero-label marker vanishes on the generated trivial subgroup. -/
private theorem nzVanish : ∀ g ∈ (⊥ : AddSubgroup (AbGroup 2 m2)), nzPred g = false := by
  intro g hg
  have h0 : g = 0 := AddSubgroup.mem_bot.mp hg
  simp [nzPred, h0]

/-- The progress instance: a marked label of `AbGroup 2` lies outside the trivial
subgroup. -/
example (ℓ : AbGroup 2 m2) (hℓ : ℓ ∈ markedSet nzPred) :
    ℓ ∉ (⊥ : AddSubgroup (AbGroup 2 m2)) :=
  marked_progress ⊥ nzPred nzVanish ℓ hℓ

/-- The numeric polylog call bound: six calls at `k = 4`, `C = 3` stay below
`3 * log₂ 16 ^ (2 / 2)`. -/
example :
    (6 : ℝ) ≤ 3 * Real.logb 2 ((16 : ℕ) : ℝ) ^ ((2 : ℝ) / 2) := by
  have hlog : Real.logb 2 ((16 : ℕ) : ℝ) = 4 := by
    have h16 : ((16 : ℕ) : ℝ) = ((2 : ℝ) ^ (4 : ℕ)) := by norm_num
    rw [h16, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  refine amplified_calls_polylog 4 2 16 3 (by norm_num) (by omega) (by omega) ?_ 6 ?_
  · rw [hlog]
    norm_num
  · have h4 : ((1 : ℝ) / ((4 : ℕ) : ℝ)) = ((1 : ℝ) / (2 : ℝ)) ^ 2 := by norm_num
    rw [h4, Real.sqrt_sq (by norm_num)]
    norm_num

/-- The fraction-mass theorem instantiated at its interface hypotheses. -/
example (K : AddSubgroup (AbGroup 2 m2)) (χ : AbGroup 2 m2 → Bool) (k : ℕ) (hk1 : 1 ≤ k)
    (hsub : ∀ ℓ ∈ markedSet χ, ℓ ∈ annihilatorGen K)
    (hcard : Fintype.card ↥(annihilatorGen K) = k * (markedSet χ).card) :
    ∑ ℓ ∈ markedSet χ, (unifOnSub (annihilatorGen K)).prob ℓ = 1 / (k : ℝ) :=
  marked_fraction_mass K χ k hk1 hsub hcard

/-- A normalized nonzero output law concentrated on a marked label. -/
private noncomputable def labelLaw : FinDist (AbGroup 2 m2) where
  prob x := if x = (fun _ => 1) then 1 else 0
  nonneg x := by split <;> norm_num
  sum_one := by
    classical
    simp

/-- The concentrated output really carries positive probability. -/
example : labelLaw.prob (fun _ => 1) = 1 := by simp [labelLaw]

/-- This normalized output has no mass in the generated trivial subgroup. -/
example : ∀ ℓ ∈ (⊥ : AddSubgroup (AbGroup 2 m2)), labelLaw.prob ℓ = 0 := by
  intro ℓ hℓ
  have hz : ℓ = 0 := AddSubgroup.mem_bot.mp hℓ
  subst ℓ
  have hne : (0 : AbGroup 2 m2) ≠ (fun _ => 1) := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num at h0
  simp [labelLaw, hne]

/-- The hidden trivial subgroup has the full ambient annihilator. -/
private theorem annBot_mem (g : AbGroup 2 m2) :
    g ∈ annihilatorGen (⊥ : AddSubgroup (AbGroup 2 m2)) := by
  rw [mem_annihilatorGen,
    Qatlib.Concepts.QuditTeleport.TeleportCore.mem_characterAnnihilator]
  intro x
  have hx : (x : AbGroup 2 m2) = 0 := AddSubgroup.mem_bot.mp x.2
  change charPair (m := m2) g (x : AbGroup 2 m2) = 1
  rw [hx]
  simp [charPair]

/-- Marking the first bit gives a nontrivial half-mass subset. -/
private abbrev firstMarked : AbGroup 2 m2 → Bool := fun g => decide (g 0 = 1)

/-- The marked set has two of the four labels. -/
private theorem markedCard : (markedSet firstMarked).card = 2 := by decide

/-- A concrete hidden/tracked subgroup fixture has exact marked mass one half. -/
example : ∑ ℓ ∈ markedSet firstMarked,
    (unifOnSub (annihilatorGen (⊥ : AddSubgroup (AbGroup 2 m2)))).prob ℓ = 1 / 2 := by
  apply marked_fraction_mass ⊥ firstMarked 2 (by omega)
  · intro g _
    exact annBot_mem g
  · have hcard := card_annihilatorGen_mul (⊥ : AddSubgroup (AbGroup 2 m2))
    simpa [markedCard, m2] using hcard

/-- The positive normalized output law is concentrated on these marked labels. -/
example : ∀ ℓ, firstMarked ℓ = false → labelLaw.prob ℓ = 0 := by
  intro ℓ hℓ
  have hne : ℓ ≠ (fun _ => 1) := by
    intro heq
    subst ℓ
    simp [firstMarked] at hℓ
  simp [labelLaw, hne]

/-- Distinct hidden and generated subgroup roles in the composite conditional lemma.
The supplied output law is normalized by its type; no circuit is constructed here. -/
example (H J : AddSubgroup (AbGroup 2 m2)) (hJH : J ≤ annihilatorGen H)
    (χ : AbGroup 2 m2 → Bool) (k e : ℕ) (hk1 : 1 ≤ k)
    (hvanish : ∀ g ∈ J, χ g = false)
    (hsub : ∀ ℓ ∈ markedSet χ, ℓ ∈ annihilatorGen H)
    (hcard : Fintype.card ↥(annihilatorGen H) = k * (markedSet χ).card)
    (hG2 : 2 ≤ Fintype.card (AbGroup 2 m2))
    (hbound : (k : ℝ) ≤ Real.logb 2 (Fintype.card (AbGroup 2 m2) : ℝ) ^ (e : ℝ))
    (C : ℝ) (hC : 0 < C) (calls : ℝ)
    (hcalls : calls ≤ C / Real.sqrt ((1 : ℝ) / (k : ℝ)))
    (ν : FinDist (AbGroup 2 m2)) (hν : ∀ ℓ, χ ℓ = false → ν.prob ℓ = 0) :
    (∀ ℓ ∈ J, ν.prob ℓ = 0) ∧
      (calls ≤ C * Real.logb 2 (Fintype.card (AbGroup 2 m2) : ℝ) ^ ((e : ℝ) / 2)) ∧
      (∑ ℓ ∈ markedSet χ, (unifOnSub (annihilatorGen H)).prob ℓ = 1 / (k : ℝ)) :=
  polylog_progress H J hJH χ k e hk1 hvanish hsub hcard hG2 hbound C hC calls hcalls ν hν

end PolylogInst

section Cor10Inst

/-- The fair-coin profile is a concrete admissible raw profile in this fixture. -/
private noncomputable def fairProfile : ClProc := ⟨fun _ => 0, fun _ => 1 / 2⟩

/-- The success-one profile records the hard-coded cheating specification. -/
private noncomputable def cheatProfile : ClProc := ⟨fun _ => 0, fun _ => 1⟩

/-- This fixture admits one fair-coin profile, not all classical oracle machines. -/
private def fairValid (A : ClProc) : Prop := A = fairProfile

/-- An explicit sequence places the fair profile first and the cheating profile later. -/
private noncomputable def toyProcs (i : ℕ) : ClProc :=
  if i = 0 then fairProfile else cheatProfile

/-- The admissible class is nonempty without assuming a scale qualification. -/
example : fairValid fairProfile := rfl

/-- The success-one zero-query cheating profile is rejected by this fixture. -/
example : ¬ fairValid cheatProfile := by
  intro h
  have h0 := congrArg (fun A : ClProc => A.success (⟨0, 0⟩ : ClInput)) h
  norm_num [fairProfile, cheatProfile] at h0

/-- A hard-coded success-one profile is outside the current one-entry prefix. -/
example : cheatProfile ∉ procPrefix toyProcs 0 := by
  rintro ⟨i, hi, heq⟩
  have hi0 : i = 0 := by
    have := Set.mem_Iic.mp hi
    omega
  subst i
  have h0 := congrArg (fun A : ClProc => A.success (⟨0, 0⟩ : ClInput)) heq
  norm_num [toyProcs, fairProfile, cheatProfile] at h0

/-- The omitted cheating profile really appears at a later enumeration index. -/
example : toyProcs 1 = cheatProfile := by simp [toyProcs]

/-- Every local prefix is finite, independently of the raw profile type's size. -/
example (n : ℕ) : (procPrefix toyProcs n).Finite := prefix_finite toyProcs n

/-- The explicit enumeration covers every member of the admissible class. -/
private theorem fairCovers (A : ClProc) (h : fairValid A) : ∃ i, toyProcs i = A := by
  refine ⟨0, ?_⟩
  simpa only [toyProcs, reduceIte] using h.symm

/-- The quantum witness fixture supplies only a trivial witness for conditional assembly. -/
private abbrev toyQW (n : ℕ) (_ρ : BoolVec n → BoolVec (n - 1))
    (_L : BoolVec n → Bool) : Type := Unit

/-- Each scale has an actual qualification for its enumerated admissible prefix. -/
private noncomputable def fairQual (n : ℕ) : ScaleQual n toyProcs fairValid toyQW where
  ρ := fun _ => 0
  L := fun _ => false
  qw := ()
  defeat i _ hvalid _ := by
    change toyProcs i = fairProfile at hvalid
    refine ⟨0, ?_⟩
    rw [hvalid]
    change (1 / 2 : ℝ) ≤ 1 / 2 + 2 * ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹
    exact le_add_of_nonneg_right (by positivity)

/-- Conditional assembly has a concrete covered enumeration and satisfiable finite
qualifications; it does not quantify a local defeat over all classical machines. -/
example : ∃ (O : (n : ℕ) → BoolVec n → BoolVec (n - 1)) (L : ClInput → Bool),
    (∀ n (_hn : 4 ≤ n), ∀ x : BoolVec n,
      L ⟨n, x⟩ = (fairQual n).L x ∧ O n = (fairQual n).ρ) ∧
    (∀ n (_hn : 4 ≤ n), Nonempty (toyQW n (O n) (fun x => L ⟨n, x⟩))) ∧
    ∀ A : ClProc, fairValid A →
      (∀ x : ClInput, (A.queries x) ^ 3 ≤ 2 ^ x.1) →
      {x : ClInput | 4 ≤ x.1 ∧
        A.success x ≤ 1 / 2 + 2 * ((2 : ℝ) ^ ((x.1 : ℝ) / 3))⁻¹}.Infinite :=
  corollary10_assembly fairValid toyProcs fairCovers toyQW (fun n _ => fairQual n)

end Cor10Inst
