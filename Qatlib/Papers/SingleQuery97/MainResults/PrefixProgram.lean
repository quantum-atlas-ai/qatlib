/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.WalshProgram

/-!
# Truncated prefix-code database recovery

This module defines a prefix-free binary code family and decodes codewords whose lengths fit
within a chosen truncation. The experiment uses the single-query linear-code circuit and bounds
prior-weighted decoding error by the tail of the code-length distribution, formalizing a
prefix-code recovery mechanism for [TerhalSmolin1998].

## Main statements

* `decoder_short`: The prefix-code decoder recovers each label of length at most `m` under
  prefix-freeness, supporting the coding construction of [TerhalSmolin1998].
* `experiment_error_le_tail`: Under prefix-freeness, the experiment's decoding error is bounded
  by the prior probability of code lengths exceeding `m`.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.PrefixProgram

open Qatlib.Foundations.QueryWordCore.Circuit
open LinearCodeProgram WalshProgram
open Qatlib.Concepts.LinearLearning.ConcisePipeline

variable {N : ℕ}

/-- The property that distinct codewords differ at some coordinate below both code lengths. -/
def PrefixFree (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) : Prop :=
  ∀ x y, x ≠ y → ∃ i, i < min (length x) (length y) ∧ bits x i ≠ bits y i

/-- The first `m` bits of each infinite binary code sequence. -/
def truncated (bits : Fin N → ℕ → ZMod 2) (m : ℕ) : Fin N → Fin m → ZMod 2 :=
  fun t i => bits t i

/-- For a prefix-free code, a codeword of length at most `m` is uniquely determined among all
labels by its first `m` bits. -/
theorem short_leaf_unique (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ)
    (hprefix : PrefixFree bits length) (m : ℕ) (x y : Fin N)
    (hx : length x ≤ m) (hcode : truncated bits m y = truncated bits m x) : y = x := by
  by_contra hne
  obtain ⟨i, hi, hdiff⟩ := hprefix x y (Ne.symm hne)
  have him : i < m := lt_of_lt_of_le (lt_of_lt_of_le hi (min_le_left _ _)) hx
  have he := congrFun hcode ⟨i,him⟩
  exact hdiff he.symm

/-- The decoder selecting a label of length at most `m` with truncated codeword `z`, and
returning `0` if none exists. -/
noncomputable def decoder [NeZero N] (bits : Fin N → ℕ → ZMod 2)
    (length : Fin N → ℕ) (m : ℕ) (z : Fin m → ZMod 2) : Fin N := by
  classical
  exact if h : ∃ t, truncated bits m t = z ∧ length t ≤ m then Classical.choose h else 0

/-- The prefix-code decoder recovers each label of length at most `m` under prefix-freeness,
supporting the coding construction of [TerhalSmolin1998]. -/
theorem decoder_short [NeZero N] (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ)
    (hprefix : PrefixFree bits length) (m : ℕ) (t : Fin N) (ht : length t ≤ m) :
    decoder bits length m (truncated bits m t) = t := by
  classical
  have hex : ∃ x, truncated bits m x = truncated bits m t ∧ length x ≤ m := ⟨t,rfl,ht⟩
  rw [decoder, dif_pos hex]
  exact short_leaf_unique bits length hprefix m t _ ht (Classical.choose_spec hex).1

/-- The joint law of the prior label and its decoded output after the one-query circuit for the
truncated code. -/
noncomputable def experiment [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) (m : ℕ) : PMF (Fin N × Fin N) :=
  prior.bind fun t =>
    (outputLaw (generators (truncated bits m)) (database t)).map
      (fun p => (t, decoder bits length m p.1.1))

/-- The quantum prefix-code experiment equals the prior pushed forward by deterministic decoding
of each truncated codeword. -/
theorem experiment_eq [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ) (m : ℕ) :
    experiment prior bits length m =
      prior.map (fun t => (t,decoder bits length m (truncated bits m t))) := by
  unfold experiment PMF.map
  apply congrArg (PMF.bind prior)
  funext t
  have h := outputLaw_decoded (generators (truncated bits m)) (database t)
    (fun z => (t, decoder bits length m z))
  simpa only [response_database, PMF.map, Function.comp_apply] using h

/-- Under prefix-freeness, the experiment's decoding error is bounded by the prior probability
of code lengths exceeding `m`. -/
theorem experiment_error_le_tail [NeZero N] (prior : PMF (Fin N))
    (bits : Fin N → ℕ → ZMod 2) (length : Fin N → ℕ)
    (hprefix : PrefixFree bits length) (m : ℕ) :
    CostedLaw.event (experiment prior bits length m) (fun p => p.2 ≠ p.1) ≤
      CostedLaw.event prior (fun t => m < length t) := by
  rw [experiment_eq]
  have h := FourierReadout.prior_decoder_error_le_tail prior (truncated bits m)
    (decoder bits length m) (fun t => length t ≤ m)
    (fun t ht => decoder_short bits length hprefix m t ht)
  simpa only [not_le] using h

/-- The circuit used for truncated prefix-code recovery makes exactly one oracle query. -/
theorem experiment_queries (bits : Fin N → ℕ → ZMod 2) (m : ℕ) :
    QueryCount (word (generators (truncated bits m))) = 1 := (word_resources _).1

end Qatlib.Papers.SingleQuery97.MainResults.PrefixProgram
