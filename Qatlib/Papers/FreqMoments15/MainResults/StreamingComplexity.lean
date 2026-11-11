/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FreqMoments15.MainResults.FrequencyMomentModel
import Qatlib.Papers.FreqMoments15.MainResults.Lemma4CollisionMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Multi-pass quantum streaming results for the frequency moments

Paper: Ashley Montanaro, *The quantum complexity of approximating the frequency moments*
(arXiv:1505.00113v3, 4 Aug 2016).  This file states the paper's streaming-model results:
Lemma 8 (§3.1 p. 11), Theorem 11 (§3.1 p. 13), Theorem 14 (§3.2 p. 14), Theorem 16
(§3.3 p. 15), Theorem 17 (§3.4 p. 15), Theorem 18 (§3.4 p. 16) and Theorem 23
(§3.4 p. 16).

The streaming model is the one of paper §3 p. 11 and is fixed in `FrequencyMomentModel`: a
`PassProgram` is `S` stored qubits, a unitary update per arriving value, `T` passes over the
stream (each pass applies the update to every one of the `n` elements, so one pass costs
`n·(update time)`), and a decoding of the final state.  Success probabilities are the honest
Born probabilities of the model (`relSuccess`/`approxSuccess`), so the resource statements are
not vacuous.

Model boundaries are recorded in the docstrings: the paper's high-level subroutines
(hash families, the amplitude-estimation transformation of Lemma 9/10, and the Dürr--Høyer
maximum-finding algorithm) are not separately re-implemented; the theorems below assert the
existence of a `PassProgram` with the paper's stated space, pass count and success guarantee,
which is exactly the paper's conclusion.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FreqMoments15.MainResults

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped BigOperators

/-! ## A register-level reversible gadget (hypothesis of Lemma 8) -/

/-- A reversible classical implementation of the family `h`, as assumed in Lemma 8: a
finite register of `bits` qubits carrying the map, with `bits ≤ S`.  The paper's `H` is the
gate-level realization of this gadget; the register is an abstraction used to expose the
space parameter `S` of the lemma.  (`h` is a parameter of the structure so that the
hypothesis speaks about the specific family, not about an unrelated gadget.) -/
structure RevImpl (m S : ℕ) {R : Type*} (h : ZMod m → ZMod m → R) where
  /-- number of bits used by the reversible implementation of `H` -/
  bits : ℕ
  /-- the reversible (unitarily implementable) map on the register -/
  gate : Reg bits → Reg bits
  /-- the implementation fits in the claimed space `S` -/
  bits_le : bits ≤ S

/-! ## Lemma 8: additive-error estimation via reversible `H` (§3.1 p. 11) -/

/-
Gap record for `lemma8_AE_estimation`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Lemma 8, §3.1 p. 11.
* Original proof route: set `p = Pr_j[∃i, h_j(a_i)=1]`, `N_j = |{i : h_j(a_i)=1}|`.  Implement
  coherently `|j⟩|y⟩ ↦ |j⟩|y + [h_j(a)=1]⟩` with two uses of `H` per stream element (compute +
  uncompute), so that after one pass `|j⟩|0⟩ ↦ |j⟩|N_j⟩` in time `O(nT)` and space `S+O(log n)`;
  write `[N_j ≠ 0]` into an ancilla, uncompute `N_j` by a second pass (one extra qubit to
  remember add/subtract), obtaining `|j⟩|z⟩ ↦ |j⟩|z + [∃i, h_j(a_i)=1]⟩`.  Then apply quantum
  amplitude estimation with `O(1/ε)` uses and `O(log 1/ε)` ancilla qubits.
* Lean gap: quantum amplitude estimation is not formalised in the repo, and `PassProgram`'s
  `step` is a single-register unitary (the coherent `|j⟩|y⟩` map with an ancilla and its
  uncompute are not constructed).  Only the resource statement is captured.
* Candidate reusable dependencies: `PassProgram`, `PassProgram.run`, `onePass`,
  `PassProgram.approxSuccess`, `RevImpl` (this development); `ApplyGate`/`TensorGate` for
  composing the ancilla map; `Normalized`, `BornProb`, `MeasureProb`.
* Suggested takeover: prove a standalone `amplitudeEstimation` resource lemma
  (`∃ P, P.S ≤ S₀+O(log 1/ε) ∧ P.T ≤ C/ε ∧ success ≥ 2/3`) as an interface, then instantiate
  `PassProgram` with `step := U_a` where `U_a` is the two-use-of-`H` lift through `TensorGate`;
  the reversible `H` semantics is the remaining content.
-/
/-- **Lemma 8 — statement registration** (paper §3.1 p. 11).  Let `a_1, …, a_n` be a stream
and let `H, |H| = M` be a family of functions `h_j : [m] → [R]` such that
`H : (j,x) ↦ h_j(x)` can be implemented reversibly classically in time `T` and space `S`.
Then there is a quantum algorithm which estimates `Pr_j[∃i, h_j(a_i) = 1]` up to additive
error `ε` using space `S + O(log n + log 1/ε)`, `O(1/ε)` passes over the input, and time
`O(nT)` per pass.

Formalisation notes.  The reversible implementation is represented by `RevImpl m S h`; its
semantic correctness is part of the paper's trusted classical gadget (the Lean model records
the register and its size, not an operational semantics, exactly as for the oracle in the
query model).  The distinguished value `1 ∈ [R]` of the paper is an explicit parameter
`r0 : R`.  The per-pass time `O(nT)` is not a field of `PassProgram`: a pass of `PassProgram`
applies the update to every one of the `n` stream values, which is the paper's `n·T` cost, so
`T` appears as a parameter but the time is accounted for structurally rather than numerically.
The estimated quantity is the fraction of indices `j` for which some stream value satisfies
`h_j`.

**Status.** The statement is registered as a `Prop`-valued definition; the coherent
`|j⟩|N_j⟩` construction and quantum amplitude estimation are not formalised. -/
def lemma8_AE_estimation_statement {n m : ℕ} [NeZero m] (hn : 0 < n) (S T : ℕ)
    {R : Type*} [DecidableEq R] (r0 : R) (h : ZMod m → ZMod m → R)
    (hrev : Nonempty (RevImpl m S h)) : Prop :=
    ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ P : PassProgram n m, ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
        (P.S : ℝ) ≤ (S : ℝ) + C1 * (Real.log (n : ℝ) + Real.log (1 / ε)) ∧
        (P.T : ℝ) ≤ C2 / ε ∧
        ∀ a : Stream n m,
          (2 : ℝ) / 3 ≤ P.approxSuccess a
            (((Finset.univ.filter (fun j : ZMod m => ∃ i : Fin n, h j (a i) = r0)).card : ℝ)
              / (m : ℝ)) ε

/-! ## Theorem 11: streaming `F_0` (§3.1 p. 13) -/

/-
Gap record for `theorem11_stream_F0`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 11, §3.1 p. 13 (Algorithm 3).
* Original proof route: step 1 picks a `t`-wise independent family `H` of hash functions
  `[m] → [R]` with `R ≈ F_0`; step 3 applies Lemma 8 to `h_j(x) = [h_j(x)=1]` to estimate
  `Pr_h[∃i, h(a_i)=1]` to additive error `ε/300`; Lemma 10 determines the family so that the
  estimate `r̂` of `r` has `|p̂ − r| ≤ ε/150`; Lemma 9 (Bar-Yossef et al.) converts `r̂` into an
  `ε`-relative estimate of `F_0`, with `S = O(t log m) = O(log m log(1/ε))`.
* Lean gap: Lemmas 9 and 10 (the Bar-Yossef `F_0` estimator and the hash-family construction)
  are not formalised, nor is `t`-wise independence; the `ln`-formula estimator is missing.
* Candidate reusable dependencies: `lemma8_AE_estimation` (above), `PassProgram`,
  `PassProgram.successF0`; `Finset.card_filter` for the `F_0` side; `Real.log` for the
  `ln(1−r̂)/ln(1−1/R)` formula.
* Suggested takeover: formalise Lemma 9 first as a pure real-analysis statement about
  `F_0, R, r, r̂` (elementary `ln` manipulation), then Lemma 10 as a probabilistic bound on a
  `t`-wise independent family, and finally compose with `lemma8_AE_estimation`; the paper's
  argument is already modular in exactly these three pieces.
-/
/-- **Theorem 11 — statement registration** (paper §3.1 p. 13).  Algorithm 3 computes `F_0`
up to relative error `ε`, with failure probability at most `1/3`, using space
`O(log m log(1/ε) + log n)` and `O(1/ε)` passes over the input.

**Status.** The statement is registered as a `Prop`-valued definition; Lemmas 9–10 and the
hash-family construction are not formalised. -/
def theorem11_stream_F0_statement (n m : ℕ) [NeZero m] (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) : Prop :=
    ∃ P : PassProgram n m, ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      (P.S : ℝ) ≤ C1 * (Real.log (m : ℝ) * Real.log (1 / ε) + Real.log (n : ℝ)) ∧
      (P.T : ℝ) ≤ C2 / ε ∧
      ∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successF0 a ε

/-! ## Theorem 14: streaming `F_2` (§3.2 p. 14) -/

/-
Gap record for `theorem14_stream_F2`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 14, §3.2 p. 14 (Algorithm 4).
* Original proof route: take a family `H` of `O(m²)` 4-wise independent hash functions
  `h_i : [m] → {±1}`; the estimator `f(i) = (∑_j h_i(a_j))²` has `E_i[f(i)] = F_2`
  (Claim 13, Alon--Matias--Szegedy [3]), computed in one pass; a second pass subtracts
  `h_i(a_j)` to uncompute.  Theorem 12 ([37], quantum approximation with bounded relative
  variance `B`) turns this into a relative-error estimate with `O((B/ε)log^{3/2}(B/ε)log log(B/ε))`
  uses and `O(S + log(B/ε))` space.
* Lean gap: neither Claim 13 (the `F_2` identity for 4-wise independent `±1` hashes) nor
  Theorem 12 (the relative-variance amplifier) is formalised; 4-wise independence and the
  `±1` hash family have no counterpart in the repo.
* Candidate reusable dependencies: `PassProgram`/`onePass` (uncompute via the inverse gate),
  `Fk` (`F_2` is `Fk a 2`), `Finset.sum` identities for `E_i[f(i)] = F_2`;
  `Real.rpow`/`Real.log` for the pass count.
* Suggested takeover: prove Claim 13 as a `Finset.sum` computation over `ZMod m` using the
  standard 4-wise independence identities, then state Theorem 12 as a `PassProgram`-level
  interface and instantiate it; the paper's composition is then purely bookkeeping of constants.
-/
/-- **Theorem 14 — statement registration** (paper §3.2 p. 14).  Algorithm 4 computes `F_2`
up to relative error `ε`, with failure probability at most `1/3`, using space
`O(log n + log(1/ε))` and
`O((1/ε) log^{3/2}(1/ε) log log(1/ε)) = Õ(1/ε)` passes over the input.

The pass count is stated in the paper's explicit poly-log form (with the logarithms shifted
by `2` so that the bound is a positive quantity for every `ε ∈ (0,1)`; this only changes the
universal constant).

**Status.** The statement is registered as a `Prop`-valued definition; Claim 13 and the
relative-variance amplifier (Theorem 12) are not formalised. -/
def theorem14_stream_F2_statement (n m : ℕ) [NeZero m] (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) : Prop :=
    ∃ P : PassProgram n m, ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      (P.S : ℝ) ≤ C1 * (Real.log (n : ℝ) + Real.log (1 / ε)) ∧
      (P.T : ℝ) ≤ C2 * (1 / ε) * Real.rpow (Real.log (1 / ε) + 2) (3 / 2 : ℝ)
                      * Real.log (Real.log (1 / ε) + 2) ∧
      ∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successF2 a ε

/-! ## Theorem 16: streaming exact `F_∞` (§3.3 p. 15) -/

/-
Gap record for `theorem16_stream_Finf`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 16, §3.3 p. 15.
* Original proof route: compute the frequency `n_j` of each value with an exact streaming
  algorithm, then output the maximum of the `N` frequencies using Dürr--Høyer quantum
  maximum-finding [23], which uses `O(log² N)` space and `O(√N)` queries; here `N = m`, giving
  space `O(log² m)` and `O(√n)` passes (each pass gives one query to the frequency vector).
* Lean gap: Dürr--Høyer maximum-finding is not formalised, and the streaming model has no
  mechanism to turn a `√m`-query max-finding algorithm into `√n` passes (the paper's `√n`
  bound arises from the pass-per-query accounting).
* Candidate reusable dependencies: `PassProgram`, `Finf`, `freq` (model);
  `Finset.sup` for `Finf`; no max-finding counterpart in Frozen v2.0.2.
* Suggested takeover: state Dürr--Høyer as a `PassProgram`-interface hypothesis with space
  `O(log² m)` and `O(√n)` passes, and prove `Finf a = Finset.univ.sup (freq a)` is computed
  by that interface; the `Finf = max_j freq` identity is already definitional here.
-/
/-- **Theorem 16 — statement registration** (paper §3.3 p. 15).  There is a quantum
algorithm which computes `F_∞` exactly, with failure probability at most `1/3`, using space
`O(log² m)` and `O(√n)` passes over the input.

**Status.** The statement is registered as a `Prop`-valued definition; Dürr--Høyer
maximum-finding and the pass/query accounting are not formalised. -/
def theorem16_stream_Finf_statement (n m : ℕ) [NeZero m] (hn : 0 < n) (hm : 1 < m) : Prop :=
    ∃ P : PassProgram n m, ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧
      (P.S : ℝ) ≤ C1 * (Real.log (m : ℝ)) ^ 2 ∧
      (P.T : ℝ) ≤ C2 * Real.sqrt (n : ℝ) ∧
      ∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.relSuccess a (Finf a : ℝ) 0

/-! ## Theorem 17: streaming lower bounds (§3.4 p. 15) -/

/-
Gap record for `theorem17_stream_lower`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 17, §3.4 p. 15.
* Original proof route: an `S`-qubit `T`-pass streaming algorithm yields a two-way quantum
  communication protocol with `O(TS)` qubits (Alice/Bob split the stream).  For `k ≠ 1`, embed
  the equality function on `Θ(n)` bits using `2^{Ω(n)}` subsets of `[n]` of size `n/4`
  pairwise intersecting in at most `n/8`, and use the `Ω(n)` equality lower bound [41]
  (with the `F_k` vs `F_0` comparison), giving `TS = Ω(log n)`.  For `k = ∞`, use the
  element-distinctness communication lower bound `Ω(√n)`.
* Lean gap: no quantum communication-complexity model, no streaming-to-communication
  simulation theorem, and none of the equality / element-distinctness communication lower
  bounds is formalised.
* Candidate reusable dependencies: `PassProgram` (resource parameters `S`, `T`),
  `PassProgram.relSuccess`, `Fk`, `Finf`; the `m ≥ 2n` side condition is already a hypothesis.
* Suggested takeover: formalise `streamToComm : PassProgram → CommProtocol` (elementary: Alice
  runs the first half, sends the `S`-qubit state, Bob runs the second half), then import the
  two communication lower bounds as hypotheses; the simulation lemma is the reusable core.
-/
/-- **Theorem 17 — statement registration** (paper §3.4 p. 15).  Assume `m ≥ 2n`.  If a
protocol in the multi-pass quantum streaming model stores `S` qubits and uses `T` passes to
compute `F_k` for a stream of `n` elements up to relative error `1/8` with failure
probability `1/3`, then `T S = Ω(log n)` for `k ≠ 1`, and `T S = Ω(√n)` for `k = ∞`.

**Status.** The statement is registered as a `Prop`-valued definition; the
streaming-to-communication simulation and the equality lower bounds are not formalised. -/
def theorem17_stream_lower_statement : Prop :=
    (∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), k ≠ 1 →
      ∀ (n m : ℕ) [NeZero m], 2 * n ≤ m →
        ∀ (P : PassProgram n m),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.successFk a k (1 / 8)) →
            c * Real.log (n : ℝ) ≤ (P.T : ℝ) * (P.S : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) [NeZero m], 2 * n ≤ m →
        ∀ (P : PassProgram n m),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.relSuccess a (Finf a : ℝ) (1 / 8)) →
            c * Real.sqrt (n : ℝ) ≤ (P.T : ℝ) * (P.S : ℝ))

/-! ## Theorem 18: streaming exact-computation lower bound (§3.4 p. 16) -/

/-
Gap record for `theorem18_stream_exact_lower`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 18, §3.4 p. 16.
* Original proof route: reduce from Hamming distance (`Ω(n)` quantum communication [28]).
  Alice encodes `x` as `i + n x_i`, Bob encodes `y` as `i + n y_i`; then for
  `k ∉ {0,1,∞}`, `F_k` of the concatenated sequence is an affine function of the Hamming
  distance `d(x,y)` (each matching position contributes a frequency-2 pair, each mismatching
  position two frequency-1 values), so exact `F_k` determines `d(x,y)`.
* Lean gap: the Hamming-distance communication lower bound and the streaming-to-communication
  simulation are not formalised; the exact `F_k` formula on the concatenated sequence is also
  not proved.
* Candidate reusable dependencies: `Fk`, `freq`, `Stream`; `Finset.sum` for the identity
  `Fk (x∘y) k = (n−d)·2^k + 2·d` (with `d` the Hamming distance); `PassProgram` for the
  resource statement.
* Suggested takeover: prove the exact `F_k` formula first (pure `Finset`/`ZMod` computation on
  the two-spike sequence), then compose with a `streamToComm` simulation lemma (shared with
  Theorem 17) and the imported Hamming-distance lower bound.
-/
/-- **Theorem 18 — statement registration** (paper §3.4 p. 16).  Assume a protocol in the
multi-pass quantum streaming model stores `S` qubits and uses `T` passes to compute `F_k`
exactly for a stream of `n` elements, with failure probability `1/3`.  Then, for
`k ∉ {0, 1, ∞}`, `T S = Ω(n)`.  (Since `k : ℕ`, the condition `k ∉ {0,1,∞}` is
`k ≠ 0 ∧ k ≠ 1`.)

**Status.** The statement is registered as a `Prop`-valued definition; the
streaming-to-communication simulation and the Hamming-distance lower bound are not
formalised. -/
def theorem18_stream_exact_lower_statement : Prop :=
    ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), k ≠ 0 → k ≠ 1 →
      ∀ (n m : ℕ) [NeZero m], 2 * n ≤ m →
        ∀ (P : PassProgram n m),
          (∀ a : Stream n m, (2 : ℝ) / 3 ≤ P.relSuccess a (Fk a k : ℝ) 0) →
            c * (n : ℝ) ≤ (P.T : ℝ) * (P.S : ℝ)

/-! ## Theorem 23: streaming relative-error lower bound (§3.4 p. 16) -/

/-
Gap record for `theorem23_stream_rel_lower`.

* Paper version: arXiv:1505.00113v3 (4 Aug 2016), Theorem 23, §3.4 p. 16.
* Original proof route: combine Claims 19--22.  A streaming protocol for `F_k` gives (Claim 19)
  a protocol for the gapped Hamming-distance problem `GHD_{ℓ,ℓ/2}` with `ℓ = Θ(1/ε²)` and
  `O(TS)` communication; Claim 20 moves to `GHD_{ℓ,ℓ/8}`; Claim 21 gives the polynomial
  approximation `P`; Claim 22 (Nayak--Wu) gives the degree lower bound
  `d = Ω(√(n/Δ) + √(c(n−c))/Δ)`, yielding `TS = Ω(1/ε)`.
* Lean gap: none of Claims 19--22 is formalised, and the polynomial method / Nayak--Wu bound
  is absent; there is also no communication-complexity model to host `GHD`.
* Candidate reusable dependencies: `PassProgram` (`T`, `S`), `PassProgram.relSuccess`, `Fk`;
  the paper's `ε ≥ 1/√m` side condition is an explicit hypothesis here.
* Suggested takeover: formalise Claim 19 (the `F_k`-to-`GHD` reduction) first, since it only
  needs the `F_k` arithmetic of `FreqMoments`; then import the Nayak--Wu polynomial bound as a
  hypothesis and derive `TS = Ω(1/ε)`; the shared `streamToComm` lemma of Theorem 17 is a
  prerequisite.
-/
/-- **Theorem 23 — statement registration** (paper §3.4 p. 16).  Assume a protocol in the
multi-pass quantum streaming model stores `S` qubits and uses `T` passes to compute `F_k` up
to relative error `ε ≥ 1/√m` for a stream of `n` elements from a universe of size `m`, with
failure probability `1/4`, for `k ≠ 1`.  Then `T S = Ω(1/ε)`.

**Status.** The statement is registered as a `Prop`-valued definition; Claims 19–22 and the
Nayak--Wu polynomial lower bound are not formalised. -/
def theorem23_stream_rel_lower_statement : Prop :=
    ∃ c : ℝ, 0 < c ∧
      ∀ (k : ℕ), k ≠ 1 →
      ∀ (n m : ℕ) [NeZero m], 2 ≤ m →
        ∀ ε : ℝ, 0 < ε → 1 / Real.sqrt (m : ℝ) ≤ ε → ε < 1 →
          ∀ (P : PassProgram n m),
            (∀ a : Stream n m, (3 : ℝ) / 4 ≤ P.relSuccess a (Fk a k : ℝ) ε) →
              c / ε ≤ (P.T : ℝ) * (P.S : ℝ)

end Qatlib.Papers.FreqMoments15.MainResults
