/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 3: linear classical-feedback lower bound for DLP

Fixed version: arXiv:2608.15545v1 (2026-08-16), Theorem 3 (p.5) and its proof
in Appendix K (p.36-40, Eq. (K1)).  Paper: *Quantum Advantage with Adaptive
Shallow Circuits*.

**Paper statement.**  Let `p > 2` be prime and `n = ⌈log₂ p⌉`.  Any
input-oblivious CRAS protocol of constant round and constant coherent depth
that solves DLP with success probability at least `2/3` needs `Ω(n)` classical
feedback outcomes.

**Proof structure (Appendix K).**

1. Input-obliviousness makes the output a Boolean function of the classical
   feedback transcript whose distribution does not depend on the DLP instance,
   so the protocol's observable is a fixed function of the `N = n` input bits.
2. The light-cone / Pauli-weight bound of Appendix D gives that this function
   depends on at most `(M + 1) 2^d` input bits when the coherent depth is `d`
   and the protocol uses `M` feedback outcomes.
3. The DLP output has *full* effective input support: no proper subset of the
   input bits determines it (this is the Fourier-degree/degree barrier of
   Appendix K, step 2, combined with Gyarmati's correlation bound, Eq. (K1)).
4. Combining 2 and 3: `(M + 1) 2^d ≥ N`.  For constant `d` this is
   `M ≥ N / 2^d - 1 = Ω(N) = Ω(n)`, the theorem.

**What is formalized here.**

* `EssentialSupport` — the statement that no proper subset of input bits
  determines the output function; this is step 3's combinatorial content.
* `support_le_budget` (from the `LightCone` module, Appendix D) — step 2.
* `budget_ge_linear` — the arithmetic core: from `N ≤ (M+1) 2^d` and
  `2^{d+1} ≤ N` (only a logarithmic input-size hypothesis, satisfied for
  `n = ⌈log₂ p⌉` and any fixed `d`), one gets `N / 2^{d+1} ≤ M`.
* `feedback_lower_bound_depth_fixed` — **Theorem 3 in the paper's uniform
  form**: for every fixed coherent depth `d` there is an absolute constant
  `c = 2^{-(d+1)} > 0` such that every depth-`d`, `M`-feedback protocol whose
  output has full effective support on an `N`-bit input with `N ≥ 2^{d+1}`
  uses at least `c N` feedback outcomes.
* `theorem3_feedback_lower_bound` — the same bound stated on a protocol
  structure carrying the DLP-style data.
* `no_protocol_below_budget` — the contrapositive `(M+1) 2^d < N` rules out a
  full-support output, which is the strict form used in the paper.

**Residual gap.**  Step 3 for the *specific* DLP output (that it has full
effective support, via the Gyarmati correlation bound and the DLP Fourier
mass estimate) is the only part not formalized; it enters as the explicit
hypothesis `EssentialSupport` (and as the field `essential` of `Protocol`).
No hypothesis restates the conclusion: `EssentialSupport` says the function
has no proper dependence set, while the thesis of Theorem 3 is a numeric
bound on `M`.  Nothing in this file is assumed beyond that documented step.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ShallowAdvWu26.ShallowPower.FeedbackLowerBound

open Qatlib.Papers.ShallowAdvWu26.ShallowPower.LightCone

/-- **Full effective input support.**  No proper subset of the input bits
determines `f`: every dependence set is the whole input.  This is the
paper's step 3 (the DLP output has full Fourier degree, Appendix K). -/
def EssentialSupport {N : ℕ} (f : (Fin N → Bool) → Bool) : Prop :=
  ∀ S : Finset (Fin N), DependsOn f S → S = Finset.univ

/-- **Arithmetic core of Theorem 3.**  If a full-support output is computable
by a depth-`d`, `M`-feedback protocol on `N` input bits, then
`N ≤ (M + 1) * 2^d`; if in addition `N ≥ 2^{d+1}`, then
`N / 2^{d+1} ≤ M`.  The constant `1/2^{d+1}` is the `Ω(n)` constant of
Theorem 3 for fixed coherent depth `d`. -/
theorem budget_ge_linear {N d M : ℕ} (hbudget : N ≤ (M + 1) * 2 ^ d)
    (hN : 2 ^ (d + 1) ≤ N) : (N : ℝ) / 2 ^ (d + 1) ≤ (M : ℝ) := by
  have hpow : 0 < 2 ^ d := Nat.two_pow_pos d
  have h2d : 2 ^ (d + 1) = 2 * 2 ^ d := by
    rw [pow_succ]
    ring
  have hle : 2 * 2 ^ d ≤ (M + 1) * 2 ^ d := by
    calc 2 * 2 ^ d = 2 ^ (d + 1) := h2d.symm
      _ ≤ N := hN
      _ ≤ (M + 1) * 2 ^ d := hbudget
  have h2le : 2 ≤ M + 1 := Nat.le_of_mul_le_mul_right hle hpow
  have hM1 : 1 ≤ M := by omega
  have hNle : N ≤ M * 2 ^ (d + 1) := by
    calc N ≤ (M + 1) * 2 ^ d := hbudget
      _ = M * 2 ^ d + 2 ^ d := by ring
      _ ≤ M * 2 ^ d + M * 2 ^ d := by
          have hle' : 2 ^ d ≤ M * 2 ^ d := by
            calc 2 ^ d = 1 * 2 ^ d := (one_mul _).symm
              _ ≤ M * 2 ^ d := Nat.mul_le_mul_right _ hM1
          omega
      _ = M * 2 ^ (d + 1) := by rw [h2d]; ring
  have hcast : (N : ℝ) ≤ (M : ℝ) * (2 : ℝ) ^ (d + 1) := by
    exact_mod_cast hNle
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (d + 1) :=
    pow_pos (by norm_num : (0 : ℝ) < 2) (d + 1)
  rw [div_le_iff₀ hpos]
  exact hcast

/-- **Theorem 3, depth-fixed uniform form.**  For every fixed coherent depth
`d` there is an absolute constant `c = 2^{-(d+1)} > 0` such that every
depth-`d`, `M`-feedback protocol computing a full-effective-support output on
`N` input bits with `N ≥ 2^{d+1}` uses at least `c * N` classical feedback
outcomes.

The quantifier structure matches the paper: `d` is fixed first (constant
depth), the constant depends only on `d`, and the bound is linear in the input
length `N = n`. -/
theorem feedback_lower_bound_depth_fixed (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (N M : ℕ) (Ls : List (LayerGate N)) (readout : Finset (Fin N))
        (g : (Fin N → Bool) → Bool),
        Ls.length = d → readout.card ≤ M + 1 → DependsOn g readout →
          EssentialSupport (g ∘ composeMap Ls) → 2 ^ (d + 1) ≤ N →
            c * (N : ℝ) ≤ (M : ℝ) := by
  refine ⟨1 / 2 ^ (d + 1), ?_, ?_⟩
  · exact one_div_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 2) (d + 1))
  intro N M Ls readout g hlen hread hg hess hN
  have hbudget : N ≤ (M + 1) * 2 ^ Ls.length :=
    support_le_budget Ls readout M hread g hg hess
  rw [hlen] at hbudget
  have hlin : (N : ℝ) / 2 ^ (d + 1) ≤ (M : ℝ) := budget_ge_linear hbudget hN
  have heq : (1 / (2 : ℝ) ^ (d + 1)) * (N : ℝ) = (N : ℝ) / 2 ^ (d + 1) := by
    rw [one_div, div_eq_mul_inv]
    ring
  rw [heq]
  exact hlin

/-- A protocol in the paper's sense, over a Boolean model of its
computational-basis action: `N` input bits, a depth-`d` layer stack, a
readout of `M + 1` wires (the output wire plus `M` feedback outcomes), and an
output function of full effective support.

The field `essential` is the documented Appendix-K step 3 (DLP has full
effective support); every other field is the protocol's structural data. -/
structure Protocol where
  /-- Number of input bits `N = n = ⌈log₂ p⌉`. -/
  N : ℕ
  /-- Coherent circuit depth `d`. -/
  depth : ℕ
  /-- Layer stack implementing the circuit. -/
  layers : List (LayerGate N)
  /-- The stack's length is the depth. -/
  length_eq : layers.length = depth
  /-- Wire set read out: the output wire and the `M` feedback outcomes. -/
  readout : Finset (Fin N)
  /-- Number of classical feedback outcomes `M`. -/
  feedback : ℕ
  /-- The readout has `M + 1` wires. -/
  hread : readout.card ≤ feedback + 1
  /-- Output function of the protocol. -/
  out : (Fin N → Bool) → Bool
  /-- The output depends only on the readout wires. -/
  hout : DependsOn out readout
  /-- Full effective input support (Appendix K, step 3). -/
  essential : EssentialSupport (out ∘ composeMap layers)

/-- **Theorem 3 on protocol data.**  For every fixed coherent depth `d` there
is `c = 2^{-(d+1)} > 0` such that every depth-`d` protocol with
`2^{d+1} ≤ N` uses at least `c * N` feedback outcomes. -/
theorem theorem3_feedback_lower_bound (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ P : Protocol, P.depth = d → 2 ^ (d + 1) ≤ P.N →
      c * (P.N : ℝ) ≤ (P.feedback : ℝ) := by
  obtain ⟨c, hc, h⟩ := feedback_lower_bound_depth_fixed d
  refine ⟨c, hc, ?_⟩
  intro P hd hN
  exact h P.N P.feedback P.layers P.readout P.out (P.length_eq.trans hd) P.hread
    P.hout P.essential hN

/-- **Contrapositive form.**  A depth-`d` protocol with `(M + 1) 2^d < N`
cannot compute a full-effective-support output on `N` input bits; this is the
strict exclusion used to separate the feedback classes. -/
theorem no_protocol_below_budget {N d M : ℕ} (Ls : List (LayerGate N))
    (readout : Finset (Fin N)) (g : (Fin N → Bool) → Bool)
    (hlen : Ls.length = d) (hread : readout.card ≤ M + 1)
    (hg : DependsOn g readout) (hess : EssentialSupport (g ∘ composeMap Ls))
    (hsmall : (M + 1) * 2 ^ d < N) : False := by
  rw [← hlen] at hsmall
  exact feedback_budget_needed Ls readout M hread g hg hess hsmall

/-- **The `Ω(n)` conclusion.**  For a fixed depth `d` and input length `N`,
any full-support protocol needs at least one feedback outcome once
`(M+1) 2^d ≥ N` fails, i.e. the feedback count is at least
`N / 2^d - 1`.  This is the integer form of the linear bound. -/
theorem feedback_count_ge {N d M : ℕ} (hbudget : N ≤ (M + 1) * 2 ^ d) :
    N / 2 ^ d ≤ M + 1 := by
  rw [Nat.mul_comm (M + 1) (2 ^ d)] at hbudget
  exact Nat.div_le_of_le_mul hbudget

end Qatlib.Papers.ShallowAdvWu26.ShallowPower.FeedbackLowerBound
