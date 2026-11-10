/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.WalkAlgorithms.WalkFreshValidationContracts
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.WalkAlgorithms
open scoped Classical

theorem triCheckAmpExtract_sound {n m : ℕ}
    (adj : Fin n → Fin n → Bool) (e : Fin m → Fin n) (kcs : KCollisionSolver)
    (r' : ℕ) (subR : (Fin 2 → Fin m) → Bool) (v : Fin n) (c₀ : ℕ)
    (stape : ℕ → kcs.seed) (t : Fin 2 → Fin m)
    (hout : (triCheckAmpExtract adj e kcs r' subR v c₀ stape).1 = some t) :
    subR t = true := by
  let step := fun (acc : Option (Fin 2 → Fin m) × ℕ) (i : ℕ) =>
    match acc with
    | (some a, q) => (some a, q)
    | (none, q) =>
        let qi := kcs.cost r' subR r' 1 0 (stape (v.val*c₀+i))
        match kcs.run r' subR r' 1 0 (stape (v.val*c₀+i)) with
        | some a => if adj v (e (a 0)) && adj v (e (a 1)) then
            (some a, q+qi) else (none, q+qi)
        | none => (none, q+qi)
  have hscan : ∀ l : List ℕ, ∀ acc : Option (Fin 2 → Fin m) × ℕ,
      (∀ a, acc.1 = some a → subR a = true) →
      ∀ a, (l.foldl step acc).1 = some a → subR a = true := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      intro acc ha
      apply ih (step acc i)
      intro a h
      rcases acc with ⟨o,q⟩
      cases o with
      | some b => exact ha a h
      | none =>
        cases hr : kcs.run r' subR r' 1 0 (stape (v.val*c₀+i)) with
        | none => simp [step, hr] at h
        | some b =>
          by_cases hv : (adj v (e (b 0)) && adj v (e (b 1))) = true
          · simp only [step, hr, hv, ↓reduceIte, Option.some.injEq] at h
            subst a
            exact kcs.sound r' subR r' 1 0 (stape (v.val*c₀+i)) hr
          · simp only [step, hr, hv, Bool.false_eq_true, ↓reduceIte] at h
            cases h
  exact hscan (List.range c₀) (none,0) (by simp) t hout

theorem triCheckFresh_sound {n : ℕ} (adj : Fin n → Fin n → Bool) (U : Finset (Fin n))
    (kcs : KCollisionSolver) (ncs : NoisySearch) (r' c₀ : ℕ)
    (stape : ℕ → kcs.seed) (ntape : ncs.seed) :
    (match triCheckFresh adj U kcs ncs r' c₀ stape ntape with
    | (some (u₁,u₂),_) => u₁∈U ∧ u₂∈U ∧ u₁≠u₂ ∧
        ∃ v : Fin n,adj v u₁=true ∧ adj v u₂=true ∧ adj u₁ u₂=true
    | (none,_) => True) := by
  let m := Fintype.card ↥U
  let e : Fin m → Fin n := fun i => ((Fintype.equivFin ↥U).symm i : Fin n)
  have he (i : Fin m) : e i∈U := ((Fintype.equivFin ↥U).symm i).property
  have hinj : Function.Injective e := by
    intro a b hab
    exact (Fintype.equivFin ↥U).symm.injective (Subtype.ext hab)
  unfold triCheckFresh
  (try dsimp only)
  split
  · rename_i u₁ u₂ q houtput
    split at houtput
    · simp at houtput
    · rename_i v hsearch
      split at houtput
      · rename_i t hrun
        cases houtput
        have h := triCheckAmpExtract_sound adj e kcs r'
          (fun t => decide (t 0≠t 1 ∧ adj v (e (t 0)) ∧ adj v (e (t 1)) ∧ adj (e (t 0)) (e (t 1))))
          v c₀ (fun i => stape (n*c₀+i)) t hrun
        have ht : t 0≠t 1 ∧ adj v (e (t 0))=true ∧ adj v (e (t 1))=true ∧
            adj (e (t 0)) (e (t 1))=true := of_decide_eq_true h
        exact ⟨he _,he _,fun hEq => ht.1 (hinj hEq),v,ht.2⟩
      · simp at houtput
  · trivial
end Qatlib.Concepts.WalkSearch.WalkAlgorithms
