/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.StaticLchs.BitSampledPreparedSearch
set_option warningAsError false

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.WalkSearch.QuantumAccess

open Matrix
open scoped ENNReal Classical

structure CappedSearchTrace (I : Type) where
  result : Option I
  windows : List ℕ
  iterations : List ℕ
  candidates : List I
  bits : ℕ
  phaseQueries : ℕ
  validationQueries : ℕ
  prepareCalls : ℕ
  macroGates : ℕ

def geometricWindow (M j : ℕ) : ℕ :=
  max 1 (min M ((6^j + 5^j - 1) / 5^j))

def geometricSearchSchedule (M T : ℕ) : List ℕ :=
  List.ofFn fun i : Fin T => geometricWindow M i.val

def emptySearchTrace {I : Type} : CappedSearchTrace I where
  result := none
  windows := []
  iterations := []
  candidates := []
  bits := 0
  phaseQueries := 0
  validationQueries := 0
  prepareCalls := 0
  macroGates := 0

def prependSearchReceipt {I : Type} (m : ℕ) (out : Option (I × ℕ) × ℕ × ℕ)
    (tr : CappedSearchTrace I) : CappedSearchTrace I where
  result := tr.result
  windows := m :: tr.windows
  iterations := out.2.2 :: tr.iterations
  candidates :=
    match out.1 with | none => tr.candidates | some (y, _) => y :: tr.candidates
  bits := out.2.1 + tr.bits
  phaseQueries := out.2.2 + tr.phaseQueries
  validationQueries := (if out.1.isSome then 1 else 0) + tr.validationQueries
  prepareCalls := (if out.1.isSome then 2 * out.2.2 + 1 else 0) + tr.prepareCalls
  macroGates := (out.1.map fun p => p.2).getD 0 + tr.macroGates

noncomputable def searchForSchedule {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (j₀ : I) (S : Finset I)
    (valid : I → Bool) : List ℕ → PMF (CappedSearchTrace I) :=
  List.rec (PMF.pure emptySearchTrace) fun m _ms ih =>
    (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).bind fun out =>
      match out.1 with
      | none => ih.map (prependSearchReceipt m out)
      | some (y, _) =>
          if valid y then
            PMF.pure
              (prependSearchReceipt m out {(emptySearchTrace (I := I)) with result := some y})
          else ih.map (prependSearchReceipt m out)

variable {I : Type} [Fintype I] [DecidableEq I]

theorem sampled_attempt_shape (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (j₀ : I) (S : Finset I) (m : ℕ) (out : Option (I × ℕ) × ℕ × ℕ)
    (hout : out ∈ (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).support) :
    out.2.2 ≤ m ∧ out.2.1 ≤ 3 * Nat.clog 2 m ∧ (out.1 = none → out.2.2 = 0) ∧
      ∀ y g, out.1 = some (y, g) → g = 3 * out.2.2 + 1 := by
  have hbind : preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3
      = PMF.bind (finiteCoinRun (Nat.clog 2 m) m 3) (fun x =>
          match x.1 with
          | Sum.inl i => (preparedAATrial A hA j₀ S i).map fun y => (some y.1, x.2, y.2)
          | Sum.inr _ => PMF.pure (none, x.2, 0)) := rfl
  have hle2 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num : 1 < 2) m
  have hbits : ∀ x ∈ (finiteCoinRun (Nat.clog 2 m) m 3).support, x.2 ≤ 3 * Nat.clog 2 m := by
    intro x hx
    have h := (finite_coin_actual_bit_cost (Nat.clog 2 m) m 3 hle2).1 x hx
    simpa using h
  rw [hbind] at hout
  obtain ⟨x, hx, hxo⟩ := (PMF.mem_support_bind_iff _ _ _).mp hout
  obtain ⟨cfg, bits⟩ := x
  cases cfg with
  | inl i =>
      obtain ⟨z, hz, hxz⟩ := (PMF.mem_support_map_iff _ _ _).mp hxo
      obtain ⟨rfl⟩ := hxz
      have hmeta := (prepared_aa_trial_actual_metadata A j₀ S hA i).2.1 z hz
      refine ⟨?_, hbits _ hx, ?_, ?_⟩
      · show z.2 ≤ m
        rw [hmeta.1]
        exact_mod_cast i.isLt.le
      · intro h
        exact absurd h (by simp)
      · intro y g hg
        have hz1 : z.1 = (y, g) := Option.some.inj hg
        rw [hz1] at hmeta
        show g = 3 * z.2 + 1
        omega
  | inr t =>
      cases t
      have hpin : out = (none, bits, 0) := by
        simpa [PMF.mem_support_pure_iff] using hxo
      obtain ⟨rfl⟩ := hpin
      exact ⟨Nat.zero_le _, hbits _ hx, fun _ => rfl, by rintro y g hg; exact absurd hg (by simp)⟩

theorem geometric_search_actual_integer_schedule :
    ∀ (M T j : ℕ),
      geometricWindow M j = max 1 (min M ((6^j+5^j-1)/5^j)) ∧
      geometricSearchSchedule M T = List.ofFn (fun i : Fin T => geometricWindow M i.val) ∧
      0<geometricWindow M j ∧ geometricWindow M j≤geometricWindow M (j+1) ∧
      (0<M → geometricWindow M j≤M) := by
  intro M T j
  have h5 : (0:ℕ) < 5^j := Nat.pow_pos (by norm_num)
  have h5' : (0:ℕ) < 5^(j+1) := Nat.pow_pos (by norm_num)
  have h6 : (0:ℕ) < 6^j := Nat.pow_pos (by norm_num : (0:ℕ) < 6)
  have h5j : (5:ℕ)^j ≤ 5^(j+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ (by norm_num : (0:ℕ) < 5)
  have hsplitj : 6^j + 5^j - 1 = (6^j - 1) + 5^j * 1 := by omega
  have hsplitj' : 6^(j+1) + 5^(j+1) - 1 = (6^(j+1) - 1) + 5^(j+1) * 1 := by
    have : (0:ℕ) < 6^(j+1) := Nat.pow_pos (by norm_num : (0:ℕ) < 6)
    omega
  have hfj : (6^j+5^j-1)/5^j = 1 + (6^j-1)/5^j := by
    rw [hsplitj, Nat.add_mul_div_left _ _ h5]
    exact Nat.add_comm _ 1
  have hfj' : (6^(j+1)+5^(j+1)-1)/5^(j+1) = 1 + (6^(j+1)-1)/5^(j+1) := by
    rw [hsplitj', Nat.add_mul_div_left _ _ h5']
    exact Nat.add_comm _ 1
  have hcore : (6^j-1)/5^j ≤ (6^(j+1)-1)/5^(j+1) := by
    rw [Nat.le_div_iff_mul_le h5']
    have hexp : (5:ℕ)^(j+1) = 5 * 5^j := by rw [pow_succ]; ring
    have hexp6 : (6:ℕ)^(j+1) = 6 * 6^j := by rw [pow_succ]; ring
    rw [hexp, hexp6]
    calc ((6^j-1)/5^j) * (5 * 5^j) = 5 * (((6^j-1)/5^j) * 5^j) := by ring
      _ ≤ 5 * (6^j-1) := Nat.mul_le_mul_left 5 (Nat.div_mul_le_self _ _)
      _ ≤ 6 * 6^j - 1 := by omega
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · show 0 < max 1 (min M _)
    omega
  · show max 1 (min M ((6^j+5^j-1)/5^j)) ≤ max 1 (min M ((6^(j+1)+5^(j+1)-1)/5^(j+1)))
    omega
  · intro hM
    show max 1 (min M _) ≤ M
    omega

theorem geometric_search_actual_fresh_attempt_recursion :
    ∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
      (j₀ : I) (S : Finset I) (valid : I → Bool) (m : ℕ) (ms : List ℕ),
      searchForSchedule A hA j₀ S valid [] = PMF.pure emptySearchTrace ∧
      searchForSchedule A hA j₀ S valid (m::ms) =
        (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).bind (fun out =>
          match out.1 with
          | none => (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out)
          | some (y,_) => if valid y then
              PMF.pure (prependSearchReceipt m out { (emptySearchTrace (I:=I)) with result := some y })
            else (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out)) := by
  intro A hA j₀ S valid m ms
  exact ⟨rfl, rfl⟩

theorem geometric_search_receipt_actual_ledger_updates :
    ∀ (m : ℕ) (out : Option (I × ℕ) × ℕ × ℕ) (tr : CappedSearchTrace I),
      (prependSearchReceipt m out tr).result = tr.result ∧
      (prependSearchReceipt m out tr).windows = m::tr.windows ∧
      (prependSearchReceipt m out tr).iterations = out.2.2::tr.iterations ∧
      (prependSearchReceipt m out tr).candidates = (match out.1 with | none => tr.candidates | some (y,_) => y::tr.candidates) ∧
      (prependSearchReceipt m out tr).bits = out.2.1+tr.bits ∧
      (prependSearchReceipt m out tr).phaseQueries = out.2.2+tr.phaseQueries ∧
      (prependSearchReceipt m out tr).validationQueries = (if out.1.isSome then 1 else 0)+tr.validationQueries ∧
      (prependSearchReceipt m out tr).prepareCalls = (if out.1.isSome then 2*out.2.2+1 else 0)+tr.prepareCalls ∧
      (prependSearchReceipt m out tr).macroGates = (out.1.map (fun p => p.2)).getD 0+tr.macroGates := by
  intro m out tr
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem geometric_search_actual_support_soundness_and_metadata :
    ∀ (A : Matrix I I ℂ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
      (j₀ : I) (S : Finset I) (valid : I → Bool) (M T : ℕ), (∀ y, valid y=true ↔ y∈S) →
      ∀ tr ∈ (searchForSchedule A hA j₀ S valid (geometricSearchSchedule M T)).support,
        (∀ y, tr.result=some y → y∈S) ∧ tr.windows.IsPrefix (geometricSearchSchedule M T) ∧
        tr.phaseQueries = tr.iterations.sum ∧ tr.validationQueries = tr.candidates.length ∧
        tr.prepareCalls = 2*tr.phaseQueries+tr.validationQueries ∧
        tr.macroGates = 3*tr.phaseQueries+tr.validationQueries := by
  intro A hA j₀ S valid M T hvs
  have key : ∀ (ms : List ℕ) (tr : CappedSearchTrace I),
      tr ∈ (searchForSchedule A hA j₀ S valid ms).support →
        (∀ y, tr.result = some y → y ∈ S) ∧ tr.windows.IsPrefix ms ∧
        tr.phaseQueries = tr.iterations.sum ∧ tr.validationQueries = tr.candidates.length ∧
        tr.prepareCalls = 2 * tr.phaseQueries + tr.validationQueries ∧
        tr.macroGates = 3 * tr.phaseQueries + tr.validationQueries := by
    intro ms
    induction ms with
    | nil =>
        intro tr htr
        have hrw : searchForSchedule A hA j₀ S valid [] = PMF.pure emptySearchTrace := rfl
        rw [hrw] at htr
        have htr' : tr = emptySearchTrace := by
          simpa [PMF.mem_support_pure_iff] using htr
        subst htr'
        refine ⟨fun y hy => ?_, ⟨[], rfl⟩, rfl, rfl, rfl, rfl⟩
        have hres : (emptySearchTrace : CappedSearchTrace I).result = none := rfl
        rw [hres] at hy
        exact absurd hy (by simp)
    | cons m ms ih =>
        intro tr htr
        have hrun : searchForSchedule A hA j₀ S valid (m :: ms) =
            (preparedAASampled A hA j₀ S (Nat.clog 2 m) m 3).bind fun out =>
              match out.1 with
              | none => (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out)
              | some (y, _) =>
                  if valid y then
                    PMF.pure (prependSearchReceipt m out
                      {(emptySearchTrace (I := I)) with result := some y})
                  else (searchForSchedule A hA j₀ S valid ms).map (prependSearchReceipt m out) :=
          rfl
        rw [hrun] at htr
        obtain ⟨out, hout, htr⟩ := (PMF.mem_support_bind_iff _ _ _).mp htr
        obtain ⟨-, -, hnone, hsome⟩ := sampled_attempt_shape A hA j₀ S m out hout
        cases ho : out.1 with
        | none =>
            rw [ho] at htr
            obtain ⟨tr', htr', htr''⟩ := (PMF.mem_support_map_iff _ _ _).mp htr
            obtain ⟨hres, hpre, hph, hva, hpr, hma⟩ := ih tr' htr'
            obtain ⟨rfl⟩ := htr''
            obtain ⟨-, gf_win, gf_it, gf_can, -, gf_ph, gf_val, gf_pre, gf_mac⟩ :=
              geometric_search_receipt_actual_ledger_updates m out tr'
            have hq0 : out.2.2 = 0 := hnone ho
            have gf_can' : (prependSearchReceipt m out tr').candidates = tr'.candidates := by
              rw [gf_can, ho]
            have gf_val' : (prependSearchReceipt m out tr').validationQueries
                = 0 + tr'.validationQueries := by rw [gf_val, ho]; simp
            have gf_pre' : (prependSearchReceipt m out tr').prepareCalls
                = 0 + tr'.prepareCalls := by rw [gf_pre, ho]; simp
            have gf_mac' : (prependSearchReceipt m out tr').macroGates
                = 0 + tr'.macroGates := by rw [gf_mac, ho]; simp
            refine ⟨fun y' => ?_, ?_, ?_, ?_, ?_, ?_⟩
            · intro hy'
              exact hres y' hy'
            · obtain ⟨t, ht⟩ := hpre
              exact ⟨t, by simp [gf_win, ht]⟩
            · simp only [gf_ph, gf_it, hph, List.sum_cons]
            · simp only [gf_val', gf_can', hva, Nat.zero_add]
            · simp only [gf_pre', gf_ph, gf_val']
              omega
            · simp only [gf_mac', gf_ph, gf_val']
              omega
        | some pair =>
            obtain ⟨y, g⟩ := pair
            have htr2 : tr ∈ (if valid y = true then
                PMF.pure (prependSearchReceipt m out
                  {(emptySearchTrace (I := I)) with result := some y})
                else (searchForSchedule A hA j₀ S valid ms).map
                  (prependSearchReceipt m out)).support := by
              rw [ho] at htr
              exact htr
            have hg : g = 3 * out.2.2 + 1 := hsome y g ho
            by_cases hv : valid y = true
            · rw [hv] at htr2
              have htr' : tr = prependSearchReceipt m out
                  {(emptySearchTrace (I := I)) with result := some y} := by
                simpa [PMF.mem_support_pure_iff] using htr2
              subst htr'
              simp only [prependSearchReceipt, emptySearchTrace, ho, hg,
                Option.isSome_some, if_true, Option.map_some, Option.getD_some,
                List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
                Nat.add_zero]
              refine ⟨fun y' hy' => ?_, ⟨ms, by simp⟩, ?_, ?_, ?_, ?_⟩
              · have hy2 : (some (y : I)) = some y' := hy'
                have hyy : y = y' := Option.some.inj hy2
                subst hyy
                exact (hvs y).mp hv
              · trivial
              · trivial
              · trivial
              · trivial
            · rw [if_neg hv] at htr2
              obtain ⟨tr', htr', htr''⟩ := (PMF.mem_support_map_iff _ _ _).mp htr2
              obtain ⟨hres, hpre, hph, hva, hpr, hma⟩ := ih tr' htr'
              obtain ⟨rfl⟩ := htr''
              obtain ⟨-, gf_win, gf_it, gf_can, -, gf_ph, gf_val, gf_pre, gf_mac⟩ :=
                geometric_search_receipt_actual_ledger_updates m out tr'
              have gf_can' : (prependSearchReceipt m out tr').candidates
                  = y :: tr'.candidates := by rw [gf_can, ho]
              have gf_val' : (prependSearchReceipt m out tr').validationQueries
                  = 1 + tr'.validationQueries := by rw [gf_val, ho]; simp
              have gf_pre' : (prependSearchReceipt m out tr').prepareCalls
                  = (2 * out.2.2 + 1) + tr'.prepareCalls := by rw [gf_pre, ho]; simp
              have gf_mac' : (prependSearchReceipt m out tr').macroGates
                  = g + tr'.macroGates := by rw [gf_mac, ho]; simp
              refine ⟨fun y' => ?_, ?_, ?_, ?_, ?_, ?_⟩
              · intro hy'
                exact hres y' hy'
              · obtain ⟨t, ht⟩ := hpre
                exact ⟨t, by simp [gf_win, ht]⟩
              · simp only [gf_ph, gf_it, hph, List.sum_cons]
              · simp only [gf_val', gf_can', hva, List.length_cons]
                omega
              · simp only [gf_pre', gf_ph, gf_val']
                omega
              · simp only [gf_mac', gf_ph, gf_val', hg]
                omega
  intro tr htr
  exact key _ tr htr

end Qatlib.Concepts.WalkSearch.QuantumAccess
