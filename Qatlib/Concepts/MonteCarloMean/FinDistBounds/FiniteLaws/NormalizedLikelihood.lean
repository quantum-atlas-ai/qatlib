/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteLaws.RationalTableProducer
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds.NormalizedLikelihood

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
open FiniteSelection RationalNormalization
open FiniteRationalLikelihood FiniteInformationDivergence
open scoped BigOperators

variable {c m n : ℕ}

def table (r : Vector (Result m) (c + 1)) (j : Fin (c + 1)) (i : Fin m) : ℚ :=
  r[j.val].values[i.val]

def referenceValue (a : Vector (Vector ℚ m) (c + 1)) (j : Fin (c + 1)) (i : Fin m) : ℚ :=
  a[j.val][i.val] / (∑ k : Fin m, a[j.val][k.val])

def normalizationCharge (r : Vector (Result m) (c + 1)) : ℕ :=
  (List.ofFn fun j : Fin (c + 1) => r[j.val].gates).sum

def run (a : Vector (Vector ℚ m) (c + 1)) (w : Fin n → Fin m) :
    Option (Selection (Fin (c + 1)) × ℕ) :=
  (normalizeFamily a).map fun r =>
    let selected := decode (table r) w
    (selected, normalizationCharge r + selected.gates)

def outputWidth (m B : ℕ) : ℕ := B + (1 + m * (B + 1))

def totalGateCap (c m n B : ℕ) : ℕ :=
  (c + 1) * (m * (binomialRatAddGateCap (1 + m * (B + 1)) +
    binomialRatOpGateCap (outputWidth m B))) +
  (c + 1) * (2 * (n * binomialRatOpGateCap (1 + n * outputWidth m B)) +
    24 * (1 + n * outputWidth m B) ^ 2 + 20 * (1 + n * outputWidth m B))

theorem run_eq (a : Vector (Vector ℚ m) (c + 1)) (r : Vector (Result m) (c + 1))
    (hr : normalizeFamily a = some r) (w : Fin n → Fin m) :
    run a w = some (decode (table r) w, normalizationCharge r + (decode (table r) w).gates) := by
  simp only [run, hr, Option.map_some]

theorem table_reference (a : Vector (Vector ℚ m) (c + 1)) (r : Vector (Result m) (c + 1))
    (hr : normalizeFamily a = some r) (j : Fin (c + 1)) (i : Fin m) :
    table r j i = referenceValue a j i :=
  normalize_value a[j.val] r[j.val] (normalizeFamily_column a r hr j) i

section Theory
open scoped Classical

theorem family_success (a : Vector (Vector ℚ m) (c + 1))
    (actual : Fin (c + 1) → FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ j : Fin (c + 1), ∀ i : Fin m,
      |(a[j.val][i.val] : ℝ) - (actual j).prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1) :
    ∃ r : Vector (Result m) (c + 1), normalizeFamily a = some r := by
  dsimp only [normalizeFamily]
  split_ifs with hz
  · exact ⟨_, rfl⟩
  · exfalso
    apply hz
    intro j
    simp only [Vector.getElem_map, sum_value, List.sum_ofFn]
    exact (RationalTableProducer.raw_total_positive a[j.val] (actual j) eps (herr j) hsmall).ne'

theorem family_legality (a : Vector (Vector ℚ m) (c + 1))
    (r : Vector (Result m) (c + 1)) (hr : normalizeFamily a = some r)
    (ha : ∀ j : Fin (c + 1), ∀ i : Fin m, 0 ≤ a[j.val][i.val])
    (actual : Fin (c + 1) → FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ j : Fin (c + 1), ∀ i : Fin m,
      |(a[j.val][i.val] : ℝ) - (actual j).prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1) :
    (∀ j i, 0 ≤ table r j i) ∧ (∀ j, ∑ i, table r j i = 1) := by
  have h (j : Fin (c + 1)) := RationalTableProducer.table_legality a[j.val] r[j.val]
    (normalizeFamily_column a r hr j) (ha j)
    (RationalTableProducer.raw_total_positive a[j.val] (actual j) eps (herr j) hsmall)
  exact ⟨fun j => (h j).1, fun j => (h j).2⟩

theorem normalization_charge_bound (a : Vector (Vector ℚ m) (c + 1))
    (r : Vector (Result m) (c + 1)) (hr : normalizeFamily a = some r)
    (B : ℕ) (hB : ∀ j : Fin (c + 1), ∀ i : Fin m, width a[j.val][i.val] ≤ B) :
    normalizationCharge r ≤ (c + 1) * (m *
      (binomialRatAddGateCap (1 + m * (B + 1)) + binomialRatOpGateCap (outputWidth m B))) := by
  rw [normalizationCharge, List.sum_ofFn]
  calc
    _ ≤ ∑ _j : Fin (c + 1), m *
        (binomialRatAddGateCap (1 + m * (B + 1)) + binomialRatOpGateCap (outputWidth m B)) :=
      Finset.sum_le_sum fun j _ => (normalize_bounds a[j.val] r[j.val]
        (normalizeFamily_column a r hr j) B (hB j)).2
    _ = _ := by simp

theorem run_gate_bound (a : Vector (Vector ℚ m) (c + 1))
    (r : Vector (Result m) (c + 1)) (hr : normalizeFamily a = some r)
    (B : ℕ) (hB : ∀ j : Fin (c + 1), ∀ i : Fin m, width a[j.val][i.val] ≤ B)
    (w : Fin n → Fin m) (out : Selection (Fin (c + 1)) × ℕ) (hout : run a w = some out) :
    out.2 ≤ totalGateCap c m n B := by
  have hw (j : Fin (c + 1)) (i : Fin m) : width (table r j i) ≤ outputWidth m B :=
    (normalize_bounds a[j.val] r[j.val] (normalizeFamily_column a r hr j) B (hB j)).1 i
  have hn := normalization_charge_bound a r hr B hB
  have hd := decode_gates (table r) w (outputWidth m B) hw
  rw [run_eq a r hr w] at hout
  have ho := Option.some.inj hout
  subst out
  exact Nat.add_le_add hn hd

theorem program_support_risk (a : Vector (Vector ℚ m) (c + 1))
    (ha : ∀ j : Fin (c + 1), ∀ i : Fin m, 0 ≤ a[j.val][i.val])
    (actual : Fin (c + 1) → FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ j : Fin (c + 1), ∀ i : Fin m,
      |(a[j.val][i.val] : ℝ) - (actual j).prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1) (truth : Fin (c + 1)) (B : ℕ)
    (hB : ∀ j : Fin (c + 1), ∀ i : Fin m, width a[j.val][i.val] ≤ B) :
    ∃ (r : Vector (Result m) (c + 1)) (_hr : normalizeFamily a = some r)
      (hq : ∀ j i, 0 ≤ table r j i) (hsum : ∀ j, ∑ i, table r j i = 1),
      (actual truth).probEvent (fun w : Fin n → Fin m =>
        (run a w).map (fun out => out.1.candidate) ≠ some truth) ≤
        (∑ j with j ≠ truth,
          (∑ i with (distribution (table r j) (hq j) (hsum j)).prob i ≠ 0,
            (distribution (table r truth) (hq truth) (hsum truth)).prob i) ^ n) +
          (n : ℝ) * ((m : ℝ) * eps) ∧
      ∀ (w : Fin n → Fin m) (out : Selection (Fin (c + 1)) × ℕ),
        run a w = some out → out.2 ≤ totalGateCap c m n B := by
  obtain ⟨r, hr⟩ := family_success a actual eps herr hsmall
  obtain ⟨hq, hsum⟩ := family_legality a r hr ha actual eps herr hsmall
  have ht := RationalTableProducer.table_tv a[truth.val] r[truth.val]
    (normalizeFamily_column a r hr truth) (ha truth) (actual truth) eps (herr truth) hsmall
    (hq truth) (hsum truth)
  have risk := RationalLikelihoodTransport.support_risk (actual truth) (table r) hq hsum truth
    (n := n) ((m : ℝ) * eps) ht
  refine ⟨r, hr, hq, hsum, ?_, fun w out hout => run_gate_bound a r hr B hB w out hout⟩
  have he (w : Fin n → Fin m) :
      ((run a w).map (fun out => out.1.candidate) ≠ some truth) ↔
        (decode (table r) w).candidate ≠ truth := by
    rw [run_eq a r hr w]
    simp only [Option.map_some, ne_eq, Option.some.injEq]
  simpa only [he] using risk

theorem program_log_risk (a : Vector (Vector ℚ m) (c + 1))
    (ha : ∀ j : Fin (c + 1), ∀ i : Fin m, 0 < a[j.val][i.val])
    (actual : Fin (c + 1) → FinDist (Fin m)) (eps : ℝ)
    (herr : ∀ j : Fin (c + 1), ∀ i : Fin m,
      |(a[j.val][i.val] : ℝ) - (actual j).prob i| ≤ eps)
    (hsmall : (m : ℝ) * eps < 1) (truth : Fin (c + 1))
    (lo hi gap : Fin (c + 1) → ℝ) (hn : 0 < n)
    (hab : ∀ j, j ≠ truth → lo j < hi j) (hgap : ∀ j, j ≠ truth → 0 < gap j)
    (hrange : ∀ j, j ≠ truth → ∀ i,
      Real.log (referenceValue a j i : ℝ) - Real.log (referenceValue a truth i : ℝ) ∈
        Set.Icc (lo j) (hi j))
    (hmean : ∀ j, j ≠ truth →
      (∑ i : Fin m, (referenceValue a truth i : ℝ) *
        (Real.log (referenceValue a j i : ℝ) - Real.log (referenceValue a truth i : ℝ))) = -gap j)
    (B : ℕ) (hB : ∀ j : Fin (c + 1), ∀ i : Fin m, width a[j.val][i.val] ≤ B) :
    (actual truth).probEvent (fun w : Fin n → Fin m =>
      (run a w).map (fun out => out.1.candidate) ≠ some truth) ≤
      (∑ j with j ≠ truth, Real.exp (-2 * (n : ℝ) * (gap j) ^ 2 / (hi j - lo j) ^ 2)) +
        (n : ℝ) * ((m : ℝ) * eps) ∧
    ∀ (w : Fin n → Fin m) (out : Selection (Fin (c + 1)) × ℕ),
      run a w = some out → out.2 ≤ totalGateCap c m n B := by
  obtain ⟨r, hr⟩ := family_success a actual eps herr hsmall
  obtain ⟨hq, hsum⟩ := family_legality a r hr (fun j i => (ha j i).le) actual eps herr hsmall
  have hp (j : Fin (c + 1)) (i : Fin m) : (0 : ℝ) < (table r j i : ℝ) := by
    have h : 0 < table r j i := by
      rw [table_reference a r hr j i]
      exact div_pos (ha j i) (RationalTableProducer.raw_total_positive a[j.val]
        (actual j) eps (herr j) hsmall)
    exact_mod_cast h
  have ht := RationalTableProducer.table_tv a[truth.val] r[truth.val]
    (normalizeFamily_column a r hr truth) (fun i => (ha truth i).le) (actual truth) eps
    (herr truth) hsmall (hq truth) (hsum truth)
  have hR (j : Fin (c + 1)) (hj : j ≠ truth) (i : Fin m) := hrange j hj i
  have hM (j : Fin (c + 1)) (hj : j ≠ truth) :
      (distribution (table r truth) (hq truth) (hsum truth)).expect
        (fun i => Real.log (table r j i : ℝ) - Real.log (table r truth i : ℝ)) = -gap j := by
    simpa only [FinDist.expect, distribution, table_reference a r hr] using hmean j hj
  have risk := RationalLikelihoodTransport.log_risk (actual truth) (table r) hq hsum truth
    lo hi gap hp hn hab hgap
    (fun j hj i => by simpa only [table_reference a r hr] using hR j hj i)
    hM ((m : ℝ) * eps) ht
  refine ⟨?_, fun w out hout => run_gate_bound a r hr B hB w out hout⟩
  have he (w : Fin n → Fin m) :
      ((run a w).map (fun out => out.1.candidate) ≠ some truth) ↔
        (decode (table r) w).candidate ≠ truth := by
    rw [run_eq a r hr w]
    simp only [Option.map_some, ne_eq, Option.some.injEq]
  simpa only [he] using risk

end Theory
end Qatlib.Concepts.MonteCarloMean.FinDistBounds.NormalizedLikelihood
