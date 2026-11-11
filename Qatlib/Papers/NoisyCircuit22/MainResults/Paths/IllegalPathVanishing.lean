/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.PauliPath

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Lemma 5 (illegal Pauli paths vanish)

Fixed arXiv:2211.03999v1, Lemma 5, p.13, Eqs. (31)--(32).

Any illegal Pauli path gives `f(C,s,x) = 0` for all `C,x`.  The paper splits into the two
conditions of Definition 6:

* boundary condition violated: the inner product `⟨⟨x|s₀⟩⟩` or `⟨⟨s_d|x⟩⟩` vanishes because
  `⟨x|P|x⟩ = 0` for `P ∈ {X,Y}` (Eq. (31)); and
* gate condition violated: the transition amplitude `⟨⟨q|U|p⟩⟩ = Tr(q U p U†)` vanishes
  when exactly one of `p,q` is `II`, by trace preservation (Eq. (32)).

The Lean statement models the Pauli-path integral as a product of the two boundary factors
and the gate factor, and asks for the two vanishing facts (Eqs. (31), (32)) as hypotheses.
The case analysis of the proof is carried out in full below.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Paths

open BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

variable {Ω : Type*}

/-- Fixed arXiv:2211.03999v1, Lemma 5, p.13: any illegal Pauli path has zero Fourier
coefficient.  `bnd0`/`bndd` are the first/last boundary inner products and `gateFactor`
is the product of the transition amplitudes; the hypotheses `hbnd0`, `hbndd`, `hgate` are
Eqs. (31) and (32). -/
theorem source_lemma5_illegal_path_vanishing
    (n d : ℕ) (A : Architecture n d)
    (bnd0 bndd : (Fin n → Bool) → Pauli n → ℂ)
    (gateFactor : Ω → PauliPath n d → ℂ)
    (f : Ω → PauliPath n d → (Fin n → Bool) → ℂ)
    (hfac : ∀ (C : Ω) (s : PauliPath n d) (x : Fin n → Bool),
      f C s x = bndd x (s (Fin.last d)) * gateFactor C s * bnd0 x (s 0))
    (hbnd0 : ∀ (x : Fin n → Bool) (s : Pauli n), ¬ boundaryLegal s → bnd0 x s = 0)
    (hbndd : ∀ (x : Fin n → Bool) (s : Pauli n), ¬ boundaryLegal s → bndd x s = 0)
    (hgate : ∀ (C : Ω) (s : PauliPath n d),
      (∃ (i : Fin d) (q : Fin n),
        ¬ gateLegal (s i.castSucc q) (s i.castSucc (A.mate i q))
          (s i.succ q) (s i.succ (A.mate i q))) →
      gateFactor C s = 0)
    (s : PauliPath n d) (h : ¬ IsLegal A s) :
    ∀ (C : Ω) (x : Fin n → Bool), f C s x = 0 := by
  intro C x
  rw [hfac C s x]
  unfold IsLegal at h
  by_cases h1 : ∀ (i : Fin d) (q : Fin n),
      gateLegal (s i.castSucc q) (s i.castSucc (A.mate i q))
        (s i.succ q) (s i.succ (A.mate i q))
  · by_cases h0 : boundaryLegal (s 0)
    · have hd : ¬ boundaryLegal (s (Fin.last d)) := by
        intro hd
        exact h ⟨h1, h0, hd⟩
      simp [hbndd x (s (Fin.last d)) hd]
    · simp [hbnd0 x (s 0) h0]
  · push_neg at h1
    simp [hgate C s h1]

end Qatlib.Papers.NoisyCircuit22.MainResults.Paths
