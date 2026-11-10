/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.ModularReversibleWord
import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecoveryDefs
import Qatlib.Concepts.HspRecovery.BackendAudit.CountedCharacterTableDecoder
import Qatlib.Concepts.HspRecovery.BackendAudit.CharacterTableRecoveryProbability
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.HspRecovery.ReductionCore.Guarded
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.HspRecovery.ReductionCore.CompactPresentation
open Qatlib.Concepts.HspRecovery.ReductionCore.InPlace
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical
open Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib
open Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib
open Qatlib
open Qatlib

theorem exists_mul_of_dvd {a b : ℕ} (h : a ∣ b) : ∃ c, b = a * c := by
  have hmod : b % a = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  refine ⟨b / a, ?_⟩
  have h1 := Nat.mod_add_div b a
  rw [hmod, zero_add] at h1
  exact h1.symm

theorem mul_swap (c x t : ℕ) : c * (x * t) = x * (c * t) := by
  calc c * (x * t) = (c * x) * t := by exact (Nat.mul_assoc c x t).symm
    _ = (x * c) * t := by rw [Nat.mul_comm c x]
    _ = x * (c * t) := by exact Nat.mul_assoc x c t

theorem gcdList_dvd_d (d : ℕ) (cs : List ℕ) : gcdList d cs ∣ d := by
  induction cs with
  | nil => simp [gcdList]
  | cons c cs ih =>
      rw [gcdList]
      exact (Nat.gcd_dvd_left (gcdList d cs) c).trans ih

theorem gcdList_pos {d : ℕ} (hd : 0 < d) (cs : List ℕ) : 0 < gcdList d cs := by
  exact Nat.pos_of_dvd_of_pos (gcdList_dvd_d d cs) hd

theorem gcdList_dvd_of_mem (d : ℕ) (cs : List ℕ) {c : ℕ} (hc : c ∈ cs) :
    gcdList d cs ∣ c := by
  induction cs with
  | nil => cases hc
  | cons c' cs ih =>
      rw [gcdList]
      rcases List.mem_cons.mp hc with h | h
      · rw [← h]
        exact Nat.gcd_dvd_right _ _
      · exact (Nat.gcd_dvd_left _ _).trans (ih h)

theorem coprime_step {h c t : ℕ} (hh : 0 < h) (hct : h ∣ c * t) :
    (h / Nat.gcd h c) ∣ t ∧ Nat.gcd (h / Nat.gcd h c) (c / Nat.gcd h c) = 1 := by
  have hg : Nat.gcd h c ∣ h := Nat.gcd_dvd_left h c
  have hgc : Nat.gcd h c ∣ c := Nat.gcd_dvd_right h c
  have hgn : 0 < Nat.gcd h c := Nat.pos_of_dvd_of_pos hg hh
  have hcop : Nat.gcd (h / Nat.gcd h c) (c / Nat.gcd h c) = 1 := by
    have h2 := Nat.gcd_mul_left (Nat.gcd h c) (h / Nat.gcd h c) (c / Nat.gcd h c)
    rw [Nat.mul_comm (Nat.gcd h c) (h / Nat.gcd h c), Nat.div_mul_cancel hg,
      Nat.mul_comm (Nat.gcd h c) (c / Nat.gcd h c), Nat.div_mul_cancel hgc] at h2
    have h1 : Nat.gcd (h / Nat.gcd h c) (c / Nat.gcd h c) * Nat.gcd h c
        = 1 * Nat.gcd h c := by
      calc
        Nat.gcd (h / Nat.gcd h c) (c / Nat.gcd h c) * Nat.gcd h c
            = Nat.gcd h c * Nat.gcd (h / Nat.gcd h c) (c / Nat.gcd h c) := by
              exact Nat.mul_comm _ _
        _ = Nat.gcd h c := by exact h2.symm
        _ = 1 * Nat.gcd h c := by exact (Nat.one_mul _).symm
    exact Nat.mul_right_cancel hgn h1
  refine ⟨?_, hcop⟩
  obtain ⟨k, hk⟩ := exists_mul_of_dvd hct
  have hh' : (h / Nat.gcd h c) * Nat.gcd h c = h := Nat.div_mul_cancel hg
  have hc' : (c / Nat.gcd h c) * Nat.gcd h c = c := Nat.div_mul_cancel hgc
  have hcancel : (c / Nat.gcd h c) * t = (h / Nat.gcd h c) * k := by
    have hmain : Nat.gcd h c * ((c / Nat.gcd h c) * t)
        = Nat.gcd h c * ((h / Nat.gcd h c) * k) := by
      calc
        Nat.gcd h c * ((c / Nat.gcd h c) * t)
            = (Nat.gcd h c * (c / Nat.gcd h c)) * t := by
              exact (Nat.mul_assoc (Nat.gcd h c) (c / Nat.gcd h c) t).symm
        _ = ((c / Nat.gcd h c) * Nat.gcd h c) * t := by
              rw [Nat.mul_comm (Nat.gcd h c) (c / Nat.gcd h c)]
        _ = c * t := by rw [hc']
        _ = h * k := hk
        _ = ((h / Nat.gcd h c) * Nat.gcd h c) * k := by rw [hh']
        _ = (Nat.gcd h c * (h / Nat.gcd h c)) * k := by
              rw [← Nat.mul_comm (Nat.gcd h c) (h / Nat.gcd h c)]
        _ = Nat.gcd h c * ((h / Nat.gcd h c) * k) := by
              exact Nat.mul_assoc (Nat.gcd h c) (h / Nat.gcd h c) k
    exact Nat.mul_left_cancel hgn hmain
  have hdiv : (h / Nat.gcd h c) ∣ (c / Nat.gcd h c) * t := by
    rw [hcancel]
    exact Nat.dvd_mul_right _ _
  have hco : Nat.Coprime (h / Nat.gcd h c) (c / Nat.gcd h c) :=
    Nat.Coprime.gcd_eq_one hcop
  exact hco.dvd_of_dvd_mul_left hdiv

theorem ann_iff (d : ℕ) (hd : 0 < d) (cs : List ℕ) (x : ℕ) :
    (∀ c ∈ cs, d ∣ c * x) ↔ (d / gcdList d cs) ∣ x := by
  induction cs with
  | nil =>
      constructor
      · intro _
        simp [gcdList, Nat.div_self hd]
      · intro _ c hc
        cases hc
  | cons c cs ih =>
      have hhd : 0 < gcdList d cs := gcdList_pos hd cs
      have hdivd : gcdList d cs ∣ d := gcdList_dvd_d d cs
      have hδ : 0 < d / gcdList d cs := Nat.div_pos (Nat.le_of_dvd hd hdivd) hhd
      have hg : Nat.gcd (gcdList d cs) c = gcdList d (c :: cs) := by rw [gcdList]
      have hd' : (d / gcdList d cs) * gcdList d cs = d := Nat.div_mul_cancel hdivd
      have hgdd : Nat.gcd (gcdList d cs) c ∣ d := (Nat.gcd_dvd_left _ _).trans hdivd
      constructor
      · intro h
        have hrest : d / gcdList d cs ∣ x :=
          ih.mp (fun l hl => h l (List.mem_cons_of_mem c hl))
        obtain ⟨t, rfl⟩ := exists_mul_of_dvd hrest
        have hct : gcdList d cs ∣ c * t := by
          have h4 : (d / gcdList d cs) * (gcdList d cs) ∣ (d / gcdList d cs) * (c * t) := by
            calc
              (d / gcdList d cs) * gcdList d cs = d := hd'
              _ ∣ c * ((d / gcdList d cs) * t) := h c List.mem_cons_self
              _ = (d / gcdList d cs) * (c * t) := by
                exact mul_swap c (d / gcdList d cs) t
          exact (Nat.mul_dvd_mul_iff_left hδ).mp h4
        obtain ⟨hstep, _⟩ := coprime_step hhd hct
        have heq : d / gcdList d (c :: cs)
            = (d / gcdList d cs) * (gcdList d cs / Nat.gcd (gcdList d cs) c) := by
          rw [← hg]
          have hmul : Nat.gcd (gcdList d cs) c * (gcdList d cs / Nat.gcd (gcdList d cs) c)
              = gcdList d cs := by
            calc
              Nat.gcd (gcdList d cs) c * (gcdList d cs / Nat.gcd (gcdList d cs) c)
                  = (gcdList d cs / Nat.gcd (gcdList d cs) c) * Nat.gcd (gcdList d cs) c := by
                    exact Nat.mul_comm _ _
              _ = gcdList d cs := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
          have hpos : 0 < Nat.gcd (gcdList d cs) c :=
            Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hhd
          have hd'' : Nat.gcd (gcdList d cs) c
              * ((d / gcdList d cs) * (gcdList d cs / Nat.gcd (gcdList d cs) c)) = d := by
            calc
              Nat.gcd (gcdList d cs) c
                  * ((d / gcdList d cs) * (gcdList d cs / Nat.gcd (gcdList d cs) c))
                  = (d / gcdList d cs)
                      * (Nat.gcd (gcdList d cs) c * (gcdList d cs / Nat.gcd (gcdList d cs) c)) := by
                    calc
                      Nat.gcd (gcdList d cs) c
                          * ((d / gcdList d cs) * (gcdList d cs / Nat.gcd (gcdList d cs) c))
                          = (Nat.gcd (gcdList d cs) c * (d / gcdList d cs))
                              * (gcdList d cs / Nat.gcd (gcdList d cs) c) := by
                            exact (Nat.mul_assoc (Nat.gcd (gcdList d cs) c) (d / gcdList d cs)
                              (gcdList d cs / Nat.gcd (gcdList d cs) c)).symm
                      _ = ((d / gcdList d cs) * Nat.gcd (gcdList d cs) c)
                              * (gcdList d cs / Nat.gcd (gcdList d cs) c) := by
                            rw [Nat.mul_comm (Nat.gcd (gcdList d cs) c) (d / gcdList d cs)]
                      _ = (d / gcdList d cs)
                              * (Nat.gcd (gcdList d cs) c
                                  * (gcdList d cs / Nat.gcd (gcdList d cs) c)) := by
                            exact Nat.mul_assoc (d / gcdList d cs) (Nat.gcd (gcdList d cs) c)
                              (gcdList d cs / Nat.gcd (gcdList d cs) c)
              _ = (d / gcdList d cs) * gcdList d cs := by rw [hmul]
              _ = d := hd'
          have hmain : Nat.gcd (gcdList d cs) c * (d / Nat.gcd (gcdList d cs) c)
              = Nat.gcd (gcdList d cs) c
                  * ((d / gcdList d cs) * (gcdList d cs / Nat.gcd (gcdList d cs) c)) := by
            calc
              Nat.gcd (gcdList d cs) c * (d / Nat.gcd (gcdList d cs) c)
                  = (d / Nat.gcd (gcdList d cs) c) * Nat.gcd (gcdList d cs) c := by
                    exact Nat.mul_comm _ _
              _ = d := Nat.div_mul_cancel hgdd
              _ = Nat.gcd (gcdList d cs) c
                  * ((d / gcdList d cs) * (gcdList d cs / Nat.gcd (gcdList d cs) c)) := hd''.symm
          exact Nat.mul_left_cancel hpos hmain
        rw [heq]
        exact Nat.mul_dvd_mul_left _ hstep
      · intro h
        have hgpos : 0 < Nat.gcd (gcdList d cs) c :=
          Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left _ _) hhd
        have hδ' : 0 < d / gcdList d (c :: cs) := by
          rw [← hg]
          exact Nat.div_pos (Nat.le_of_dvd hd hgdd) hgpos
        have hd_g : (d / gcdList d (c :: cs)) * gcdList d (c :: cs) = d := by
          rw [← hg]
          exact Nat.div_mul_cancel hgdd
        obtain ⟨t, rfl⟩ := exists_mul_of_dvd h
        intro c' hc'
        rcases List.mem_cons.mp hc' with hcc | hcc
        · rw [hcc]
          have hgdc : gcdList d (c :: cs) ∣ c := by
            rw [← hg]
            exact Nat.gcd_dvd_right _ _
          calc
            d = (d / gcdList d (c :: cs)) * gcdList d (c :: cs) := hd_g.symm
            _ ∣ (d / gcdList d (c :: cs)) * (c * t) := by
              refine (Nat.mul_dvd_mul_iff_left hδ').mpr ?_
              exact dvd_mul_of_dvd_left hgdc t
            _ = c * ((d / gcdList d (c :: cs)) * t) := by
              exact (mul_swap c (d / gcdList d (c :: cs)) t).symm
        · have hgl : gcdList d cs ∣ c' := gcdList_dvd_of_mem d cs hcc
          have hgdc : gcdList d (c :: cs) ∣ c' := by
            rw [← hg]
            exact (Nat.gcd_dvd_left _ _).trans hgl
          calc
            d = (d / gcdList d (c :: cs)) * gcdList d (c :: cs) := hd_g.symm
            _ ∣ (d / gcdList d (c :: cs)) * (c' * t) := by
              refine (Nat.mul_dvd_mul_iff_left hδ').mpr ?_
              exact dvd_mul_of_dvd_left hgdc t
            _ = c' * ((d / gcdList d (c :: cs)) * t) := by
              exact (mul_swap c' (d / gcdList d (c :: cs)) t).symm

theorem labelGcdScan_gcd {m : ℕ} (r : Fin m) (L : List (Fin m → ℕ)) (d : ℕ) :
    (labelGcdScan r L d).1 = gcdList d (L.map (fun l => l r)) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      rw [labelGcdScan]
      show Nat.gcd (labelGcdScan r L d).1 (l r) = _
      rw [ih]
      rfl

theorem labelGcd_eq_gcdList {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (r : Fin m) :
    labelGcd p L r = gcdList (p.coeff r) (L.map (fun l => l r)) := by
  rw [labelGcd]
  exact labelGcdScan_gcd r L (p.coeff r)

theorem coeff_pos_of_finite {m n : ℕ} (p : NormalizedSmithData m n) (hf : p.isFinite = true)
    (r : Fin m) : 0 < p.coeff r := by
  have hne : p.coeff r ≠ 0 := (of_decide_eq_true hf) r
  exact Nat.pos_of_ne_zero hne

theorem labelAnn_iff {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (r : Fin m) (hd : 0 < p.coeff r) (x : ℕ) :
    (∀ l ∈ L, p.coeff r ∣ l r * x) ↔ (p.coeff r / labelGcd p L r) ∣ x := by
  rw [labelGcd_eq_gcdList]
  have hiff := ann_iff (p.coeff r) hd (L.map (fun l => l r)) x
  constructor
  · intro h
    refine hiff.mp ?_
    intro c hc
    obtain ⟨l, hl, hcl⟩ := List.mem_map.mp hc
    rw [← hcl]
    exact h l hl
  · intro h
    have hall : ∀ c ∈ L.map (fun l => l r), p.coeff r ∣ c * x := hiff.mpr h
    intro l hl
    exact hall (l r) (List.mem_map.mpr ⟨l, hl, rfl⟩)

theorem compactDecode_iff_recordAnn {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (hf : ∀ r : Fin m, 0 < p.coeff r) (x : Fin m → ℕ) :
    decodedSet p L x ↔ recordAnn p L x := by
  constructor
  · intro h l hl r
    have hann : ∀ l' ∈ L, p.coeff r ∣ l' r * x r :=
      (labelAnn_iff p L r (hf r) (x r)).mpr (h r)
    exact hann l hl
  · intro h r
    exact (labelAnn_iff p L r (hf r) (x r)).mp (fun l hl => h l hl r)

theorem compactDecode_annihilates {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) (hf : ∀ r : Fin m, 0 < p.coeff r) :
    ∀ l ∈ L, ∀ r, p.coeff r ∣ l r * compactDecode p L r := by
  intro l hl r
  have hann : ∀ l' ∈ L, p.coeff r ∣ l' r * compactDecode p L r :=
    (labelAnn_iff p L r (hf r) (compactDecode p L r)).mpr (by
      show (p.coeff r / labelGcd p L r) ∣ compactDecode p L r
      exact Nat.dvd_refl _)
  exact hann l hl

theorem compactDecodeOriginal_encode {m n : ℕ} (p : CompactPresentation)
    (L : List (FactorLabel p.smith)) :
    normalizedEncode p.smith (compactDecodeOriginal p.smith L) = compactDecodeNormalized p.smith L := by
  exact normalizedEncode_decode (smithDecodeRelations p.table) (compactDecodeNormalized p.smith L)

theorem labelGcdScan_reads {m : ℕ} (r : Fin m) (L : List (Fin m → ℕ)) (d : ℕ) :
    (labelGcdScan r L d).2.1 = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      rw [labelGcdScan]
      simp only
      rw [ih]
      rfl

theorem labelGcdScan_reductions {m : ℕ} (r : Fin m) (L : List (Fin m → ℕ)) (d : ℕ) :
    (labelGcdScan r L d).2.2 = L.length := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      rw [labelGcdScan]
      simp only
      rw [ih]
      rfl

theorem compactDecodeLedger_reads {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    (compactDecodeLedger p L).labelReads = m * L.length := by
  simp [compactDecodeLedger, labelGcdScan_reads]

theorem compactDecodeLedger_reductions {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    (compactDecodeLedger p L).gcdReductions = m * L.length := by
  simp [compactDecodeLedger, labelGcdScan_reads, labelGcdScan_reductions]

theorem compactDecodeLedger_no_enumeration {m n : ℕ} (p : NormalizedSmithData m n)
    (L : List (FactorLabel p)) :
    (compactDecodeLedger p L).groupEnumeration = 0 := rfl

theorem compactDecodeLedger_vs_table {G : Type} [Fintype G] [DecidableEq G]
    {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (tab : G → G → Bool) (g : G) (k : ℕ) (hk : L.length = k) :
    (compactDecodeLedger p L).labelReads = m * k ∧
      (tableKernelDecode tab (List.replicate k g)).2 = Fintype.card G * k := by
  constructor
  · rw [compactDecodeLedger_reads, hk]
  · rw [tableKernelDecode_reads, List.length_replicate]

theorem compactDecodeLedger_lt_table {G : Type} [Fintype G] [DecidableEq G]
    {m n : ℕ} (p : NormalizedSmithData m n) (L : List (FactorLabel p))
    (tab : G → G → Bool) (g : G) (k : ℕ) (hk : L.length = k) (hk0 : 0 < k)
    (hlt : m < Fintype.card G) :
    (compactDecodeLedger p L).labelReads < (tableKernelDecode tab (List.replicate k g)).2 := by
  rw [compactDecodeLedger_reads, hk, tableKernelDecode_reads, List.length_replicate]
  exact Nat.mul_lt_mul_of_pos_right hlt hk0

theorem compactPresentation_factors_canonical {p p' : CompactPresentation}
    (hp : p.isFinite = true)
    (e : PresentationModule (p.relationMatrix) ≃+ PresentationModule (p'.relationMatrix)) :
    p.factors = p'.factors := by
  exact normalizedSmith_factors_invariant (smithDecodeRelations p.table)
    (smithDecodeRelations p'.table) hp e

theorem compactPresentation_generatorWord (p : CompactPresentation)
    (r : Fin p.generators) :
    Submodule.Quotient.mk (fun i : Fin p.generators =>
      (Vector.ofFn (fun j : Fin p.generators =>
        (normalizedSmith (smithDecodeRelations p.table)).reduction.leftInverse j r)).get i)
      = smithGenerator (p.relationMatrix) r := by
  exact normalizedSmith_generatorWord (smithDecodeRelations p.table) r

theorem compactPresentation_reconstruct (p : CompactPresentation)
    (v : Fin p.generators → ℤ) :
    (Submodule.Quotient.mk (normalizedDecode p.smith (normalizedEncode p.smith v)) :
      PresentationModule (p.relationMatrix)) = Submodule.Quotient.mk v := by
  exact normalizedDecode_encode (smithDecodeRelations p.table) v

theorem compactPresentation_encode_decode (p : CompactPresentation)
    (z : NormalizedCoordinates p.smith) :
    normalizedEncode p.smith (normalizedDecode p.smith z) = z := by
  exact normalizedEncode_decode (smithDecodeRelations p.table) z

theorem compactPresentation_wordEq (p : CompactPresentation)
    (u v : Fin p.generators → ℤ) :
    normalizedWordEq p.smith u v = true ↔
      u - v ∈ LinearMap.range (p.relationMatrix).mulVecLin := by
  exact normalizedWordEq_true_iff (smithDecodeRelations p.table) u v

theorem compactPresentation_output_size (p : CompactPresentation) :
    p.generatorWords.length = p.factors.length := by
  exact (normalizedSmith_output_size (smithDecodeRelations p.table)).2

theorem clause1_endpoint {m n m' n' : ℕ}
    (p : CompactPresentation) (p' : CompactPresentation)
    (hp : p.isFinite = true)
    (e : PresentationModule (p.relationMatrix) ≃+ PresentationModule (p'.relationMatrix)) :
    p.factors = p'.factors ∧
      p.generatorWords.length = p.factors.length ∧
      (∀ v : Fin p.generators → ℤ,
        (Submodule.Quotient.mk (normalizedDecode p.smith (normalizedEncode p.smith v)) :
          PresentationModule (p.relationMatrix)) = Submodule.Quotient.mk v) ∧
      (∀ u v : Fin p.generators → ℤ,
        normalizedWordEq p.smith u v = true ↔
          u - v ∈ LinearMap.range (p.relationMatrix).mulVecLin) := by
  refine ⟨compactPresentation_factors_canonical hp e, ?_, ?_, ?_⟩
  · exact compactPresentation_output_size p
  · intro v
    exact compactPresentation_reconstruct p v
  · intro u v
    exact compactPresentation_wordEq p u v

def cyclicTable {N : ℕ} (a x : ZMod N) : Bool := decide (a * x = 0)

theorem cyclic_mul_eq_zero_iff {N : ℕ} [NeZero N] (a x : ZMod N) :
    a * x = 0 ↔ N ∣ a.val * x.val := by
  rw [← ZMod.val_eq_zero, ZMod.val_mul, Nat.dvd_iff_mod_eq_zero]

theorem cyclicRecordLabels_map {N : ℕ} (xs : List (ZMod N)) :
    (cyclicRecordLabels xs).map (fun l => l 0) = xs.map (fun l => l.val) := by
  induction xs with
  | nil => rfl
  | cons l xs ih =>
      simp [cyclicRecordLabels, cyclicLabel]

theorem compact_cyclic_decode {N : ℕ} (p : NormalizedSmithData 1 1)
    (hp : p.coeff 0 = N) (xs : List (ZMod N)) :
    compactDecode p (cyclicRecordLabels xs) 0 = cyclicAnnGenerator xs := by
  have hmap : (cyclicRecordLabels xs).map (fun l => l 0) = xs.map (fun l => l.val) :=
    cyclicRecordLabels_map xs
  have hg : labelGcd p (cyclicRecordLabels xs) 0
      = gcdList N (xs.map (fun l => l.val)) := by
    rw [labelGcd_eq_gcdList, hp, hmap]
  rw [compactDecode, annGenerator, hg, hp, cyclicAnnGenerator]

theorem cyclic_table_decoder_agrees {N : ℕ} [NeZero N] (xs : List (ZMod N)) :
    (tableKernelDecode cyclicTable xs).1 = cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) xs := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  ext x
  rw [mem_tableKernelDecode]
  simp only [cyclicDecodedSet, Finset.mem_filter, Finset.mem_univ, true_and,
    cyclicAnnGenerator]
  have hann : (∀ c ∈ xs.map (fun l => l.val), N ∣ c * x.val) ↔
      (N / gcdList N (xs.map (fun l => l.val))) ∣ x.val :=
    ann_iff N hN (xs.map (fun l => l.val)) x.val
  constructor
  · intro h
    refine hann.mp ?_
    intro c hc
    obtain ⟨a, ha, hca⟩ := List.mem_map.mp hc
    rw [← hca]
    have hz : cyclicTable a x = true := h a ha
    simp only [cyclicTable, decide_eq_true_eq] at hz
    exact (cyclic_mul_eq_zero_iff a x).mp hz
  · intro h
    have hall : ∀ c ∈ xs.map (fun l => l.val), N ∣ c * x.val := hann.mpr h
    intro a ha
    have hz : N ∣ a.val * x.val :=
      hall (a.val) (List.mem_map.mpr ⟨a, ha, rfl⟩)
    simp only [cyclicTable, decide_eq_true_eq]
    exact (cyclic_mul_eq_zero_iff a x).mpr hz

theorem compact_cyclic_recovery_probability {N : ℕ} [NeZero N]
    {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : ZMod N → R) (e : ZMod N ≃ AddChar (ZMod N) ℂ) (H : AddSubgroup (ZMod N))
    (hf : HidesSubgroup f H) (m : ℕ)
    (he : ∀ a y : ZMod N, e a y = 1 ↔ a * y = 0) :
    1 - (Fintype.card (ZMod N) : ℝ) * ((2 : ℝ)⁻¹)^m ≤
      (tableGroupRecordDist f e).probEvent (fun xs : Fin m → ZMod N =>
        (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) (List.ofFn xs) : Set (ZMod N))
          = (H : Set (ZMod N))) := by
  have hagree : ∀ ys : List (ZMod N),
      cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) ys
        = (tableKernelDecode cyclicTable ys).1 := by
    intro ys
    exact (cyclic_table_decoder_agrees ys).symm
  have hagreeS : ∀ ys : List (ZMod N),
      (cyclicDecodedSet (Nat.pos_of_ne_zero (NeZero.ne N)) ys : Set (ZMod N))
        = ((tableKernelDecode cyclicTable ys).1 : Set (ZMod N)) := by
    intro ys
    rw [hagree ys]
  simp only [hagreeS]
  refine character_table_actual_subgroup_recovery_probability f e cyclicTable H m hf ?_
  intro a y
  simp only [cyclicTable, decide_eq_true_eq]
  exact (he a y).symm

theorem compact_cyclic_quantum_ledger {N : ℕ} [NeZero N]
    {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : ZMod N → R) (e : ZMod N ≃ AddChar (ZMod N) ℂ)
    (A : Matrix (ZMod N) (ZMod N) ℂ) :
    QueryCount (tableSamplingCircuit (R := R) e A) = 1 ∧
      GateCount (tableSamplingCircuit (R := R) e A) = 2 := by
  exact tableSamplingCircuit_resources e A

end Qatlib.Concepts.HspRecovery.ReductionCore
