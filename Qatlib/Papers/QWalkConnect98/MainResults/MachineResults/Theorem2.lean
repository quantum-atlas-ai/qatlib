/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkConnect98.MainResults.MachineResults.MachineDefs

/-!
# QWalkConnect98 — Theorem 2 (reversible simulation with input-dependent step count)

Watrous, arXiv:cs/9812012v1 (1998), Theorem 2, pp. 3–4.

Theorem 2 (verbatim): "Let `f(n) = O(log n)` and let `M` be a deterministic
Turing machine that, on each input `x`, performs reversible transformation
`Φ_x` on `W_{f(|x|)}(Γ)` in space `O(log |x|)`.  Then there exists a reversible
Turing machine `M'` that, on each input `x`, performs `Φ_x` on `W_{f(|x|)}(Γ)`
in space `O(log |x|)`.  Furthermore, the number of steps required for `M'` to
perform `Φ_x` depends only on `x` and not on the particular argument of `Φ_x`."

The paper notes (p. 4) that this is based on Lange–McKenzie–Tapp [7], with an
added consideration of the number of steps.

The formalization uses `ReversibleMachine W`, whose `transform x : W ≃ W` is the
transformation `Φ_x` and whose `space` profile is the paper's function `f`
(bounded by `LogSpace`).

**This file does not state Theorem 2 as a theorem.**  In the abstract record
`ReversibleMachine` the `steps` field is an unconstrained function
`List Bool → W → ℕ`: no field ties it to `transform`.  Consequently the
existential conclusion of Theorem 2 would be trivially provable by replacing
`steps` with a constant — a "proof" with no bearing on the paper's
Lange–McKenzie–Tapp simulation, which is what actually produces an oblivious
schedule performing the same transformation.  Recording that tautology as a
proved theorem would inflate coverage, so the paper's Theorem 2 is instead
recorded faithfully as the predicate `ReversibleSimulation`, and `theorem2` is
left as a target for a future formal machine model.
-/

namespace Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

open Qatlib.Papers.QWalkConnect98.MainResults.MachineResults

set_option autoImplicit false

/-- **Theorem 2 as a predicate** (paper pp. 3–4): every logspace reversible
machine `M` can be simulated by a reversible machine `M'` with the same
transformation on every input, logarithmic space, and a number of steps that
depends only on the input `x`, not on the argument of `Φ_x`.

Faithful statement of the paper's Theorem 2 over the abstract
`ReversibleMachine` record.  It is a `def`, not a theorem: see the module
docstring for why the record makes the statement trivially true and why
proving it here would not represent the Lange–McKenzie–Tapp simulation.

* **Fixed paper version.** Watrous, arXiv:cs/9812012v1 (1998).
* **Original statement.** Theorem 2, p. 4: quoted in full in the module
  docstring above.
* **Key proof steps (not formalized).** Follows the Lange–McKenzie–Tapp
  simulation [7] (also [12], [13]): the reversible machine sweeps the work tape
  a fixed number of times, computing auxiliary information reversibly so that
  the total number of sweeps depends only on the input, not on the tape
  contents; the simulation adds only a constant factor in space.
* **Current Lean gap.** The libraries contain no formal Turing machine model
  (neither deterministic nor reversible, and no closure under the LMT
  simulation), so neither the simulated machine nor the oblivious schedule can
  be constructed.  The statement is nonetheless faithful: `W`, `transform`,
  and `space` are the paper's data.
* **Candidate reusable dependencies.** A future formalization of reversible
  Turing machines and of the Lange–McKenzie–Tapp simulation; the abstract
  `ReversibleMachine` record of `MachineModel.lean`.
* **Suggested takeover tactic.** Define reversible machines concretely
  (transition function + tape alphabet), prove the LMT simulation theorem, then
  instantiate `M'` with the simulated machine's `transform`; the step-count
  independence is the LMT "oblivious" schedule, whose length depends only on
  `|x|` and the space bound. -/
def ReversibleSimulation : Prop :=
  ∀ {W : Type*} (M : ReversibleMachine W), M.LogSpace →
    ∃ M' : ReversibleMachine W,
      M'.LogSpace ∧
        (∀ x : List Bool, M'.transform x = M.transform x) ∧
        (∃ steps : List Bool → ℕ, ∀ (x : List Bool) (w : W), M'.steps x w = steps x)

end Qatlib.Papers.QWalkConnect98.MainResults.MachineResults
