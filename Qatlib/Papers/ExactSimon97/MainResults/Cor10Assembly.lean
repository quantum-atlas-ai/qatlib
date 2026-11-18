/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ExactSimon97.MainResults.OracleSeparation
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped BigOperators Classical

/-!
# Conditional scale assembly for Corollary 10 of [BrassardHoyer1997]

The module combines supplied scale qualifications into one scale-tagged oracle
family and language. `ClProc` is a raw cost/success profile, not an executable
classical machine. An external `valid` relation specifies semantic admissibility;
a sequence `procs` enumerates all admissible profiles. At scale `n`, the defeat
hypothesis concerns only indices `i ≤ n`, whose image is genuinely finite.

Defeating all classical machines simultaneously at one fixed scale would be an
impossible interface: a machine can hard-code that finite scale's language. The
finite-prefix restriction avoids that universal local premise. For each enumerated
profile `procs i`, all scales above `max 4 i` are available for the assembly proof.

Quantum witness types depend on the actual local oracle and language. Constructing
those witnesses, the actual machine enumeration and admissibility semantics,
Theorem 9's transcript estimate and the source oracle diagonalization remain open.
In particular, the raw classical success/cost fields are not execution semantics
indexed by the constructed oracle and language: only the quantum witness type
has those indices here. This is conditional finite-prefix-to-infinite-scale
transport, not a proof of the full oracle separation.
-/

namespace Qatlib.Papers.ExactSimon97.MainResults

open Qatlib.Papers.ExactSimon97.MainResults

section Cor10Assembly

/-- Inputs of the assembled decision problem, tagged by their scale. -/
abbrev ClInput : Type := (n : ℕ) × BoolVec n

/-- A raw scale-uniform cost/success profile. It represents a procedure only when
an external semantic admissibility relation certifies it. -/
structure ClProc where
  /-- Oracle queries used by the procedure on the given input. -/
  queries : ClInput → ℕ
  /-- Probability of a correct membership answer on the given input. -/
  success : ClInput → ℝ

/-- The image of the first `n+1` enumerated profiles, with duplicate entries allowed. -/
def procPrefix (procs : ℕ → ClProc) (n : ℕ) : Set ClProc :=
  procs '' Set.Iic n

/-- The local qualification always concerns a finite collection of profiles. -/
theorem prefix_finite (procs : ℕ → ClProc) (n : ℕ) :
    (procPrefix procs n).Finite :=
  (Set.finite_Iic n).image procs

/-- A conditional scale qualification for the explicitly admissible profiles.
The witness type is indexed by the supplied oracle and language. -/
structure ScaleQual (n : ℕ) (procs : ℕ → ClProc) (valid : ClProc → Prop)
    (QW : (n : ℕ) → (BoolVec n → BoolVec (n - 1)) → (BoolVec n → Bool) → Type) where
  /-- The scale-`n` oracle. -/
  ρ : BoolVec n → BoolVec (n - 1)
  /-- The scale-`n` decision problem. -/
  L : BoolVec n → Bool
  /-- The quantum-solver witness (abstract `QP^ρ` membership). -/
  qw : QW n ρ L
  /-- Defeat only the admissible profiles in the finite index prefix at this scale. -/
  defeat : ∀ i : ℕ, i ≤ n → valid (procs i) →
      (∀ x : BoolVec n, ((procs i).queries (⟨n, x⟩ : ClInput)) ^ 3 ≤ 2 ^ n) →
      ∃ x : BoolVec n,
        (procs i).success (⟨n, x⟩ : ClInput) ≤
          1 / 2 + 2 * ((2 : ℝ) ^ ((n : ℝ) / 3))⁻¹

/-- Supplied local qualifications give one oracle family and language, indexed
quantum witnesses, and infinitely many defeated inputs for every admissible profile
satisfying the global cube budget. This is a conditional assembly statement. -/
theorem corollary10_assembly (valid : ClProc → Prop) (procs : ℕ → ClProc)
    (covers : ∀ A, valid A → ∃ i, procs i = A)
    (QW : (n : ℕ) → (BoolVec n → BoolVec (n - 1)) → (BoolVec n → Bool) → Type)
    (qual : ∀ n, 4 ≤ n → ScaleQual n procs valid QW) :
    ∃ (O : (n : ℕ) → BoolVec n → BoolVec (n - 1)) (L : ClInput → Bool),
      (∀ n (hn : 4 ≤ n), ∀ x : BoolVec n,
        L (⟨n, x⟩ : ClInput) = (qual n hn).L x ∧
          O n = (qual n hn).ρ) ∧
      (∀ n (_hn : 4 ≤ n), Nonempty (QW n (O n) (fun x => L ⟨n, x⟩))) ∧
      ∀ A : ClProc, valid A →
        (∀ x : ClInput, (A.queries x) ^ 3 ≤ 2 ^ x.1) →
        {x : ClInput | 4 ≤ x.1 ∧
          A.success x ≤ 1 / 2 + 2 * ((2 : ℝ) ^ ((x.1 : ℝ) / 3))⁻¹}.Infinite := by
  classical
  refine ⟨fun n => if h : 4 ≤ n then (qual n h).ρ else fun _ => 0,
    fun x => if h : 4 ≤ x.1 then (qual x.1 h).L x.2 else false, ?_, ?_, ?_⟩
  · intro n hn x
    have hdef : (dite (4 ≤ n) (fun h => (qual n h).ρ) fun _ => fun _ => 0) = (qual n hn).ρ :=
      dite_eq_left hn
    exact ⟨dite_eq_left hn, hdef⟩
  · intro n hn
    simpa only [dite_eq_left hn] using (show Nonempty (QW n (qual n hn).ρ (qual n hn).L)
      from ⟨(qual n hn).qw⟩)
  · intro A hvalid hA
    obtain ⟨i, hi⟩ := covers A hvalid
    let N : ℕ := max 4 i
    by_contra hfin
    have hfinite : {x : ClInput | 4 ≤ x.1 ∧
        A.success x ≤ 1 / 2 + 2 * ((2 : ℝ) ^ ((x.1 : ℝ) / 3))⁻¹}.Finite := by
      rcases Set.finite_or_infinite
          {x : ClInput | 4 ≤ x.1 ∧
            A.success x ≤ 1 / 2 + 2 * ((2 : ℝ) ^ ((x.1 : ℝ) / 3))⁻¹} with hfinite | hinf
      · exact hfinite
      · exact absurd hinf hfin
    have himg : (Set.Ici N) ⊆
        Sigma.fst '' {x : ClInput | 4 ≤ x.1 ∧
          A.success x ≤ 1 / 2 + 2 * ((2 : ℝ) ^ ((x.1 : ℝ) / 3))⁻¹} := by
      intro n hnm
      have hNn : N ≤ n := Set.mem_Ici.mp hnm
      have hn : 4 ≤ n := (le_max_left 4 i).trans hNn
      have hin : i ≤ n := (le_max_right 4 i).trans hNn
      obtain ⟨x, hx⟩ := (qual n hn).defeat i hin
        (by simpa only [hi] using hvalid)
        (fun y => by simpa only [hi] using hA (⟨n, y⟩ : ClInput))
      rw [hi] at hx
      exact ⟨⟨n, x⟩, ⟨hn, hx⟩, rfl⟩
    have hsub := hfinite.image Sigma.fst
    have hIci : (Set.Ici N).Finite := hsub.subset himg
    have hinj : Function.Injective (fun k : ℕ => N + k) := fun a b hab =>
      Nat.add_left_cancel hab
    have hrange : (Set.range fun k : ℕ => N + k).Infinite :=
      Set.infinite_range_of_injective hinj
    have hsub2 : (Set.range fun k : ℕ => N + k) ⊆ Set.Ici N := by
      rintro k ⟨k', rfl⟩
      exact Set.mem_Ici.2 (by
        show N ≤ N + k'
        omega)
    exact absurd hIci (Set.Infinite.mono hsub2 hrange)

end Cor10Assembly

end Qatlib.Papers.ExactSimon97.MainResults
