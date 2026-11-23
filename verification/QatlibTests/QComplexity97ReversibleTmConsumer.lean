module

public import Qatlib.Papers.QComplexity97.ReversibleTm.ReversibleStep

@[expose] public section

/-!
# Consumer regression for the reversible-machine increment of QComplexity97

This ordinary-module consumer specializes the new reversible-machine results to a concrete
two-state, two-symbol machine: the control register is flipped, the scanned symbol is preserved,
and the head always moves right. The cell map `(p, a) ↦ (a, flip p)` is a bijection of the
nonempty four-element cell type, so the machine satisfies both local conditions and the increment
applies on a non-degenerate instance. The consumer checks bijectivity of the global update, the
exactly-one-predecessor corollary, global well-formedness of the amplitude-one rule, the Euclidean
L2 operator norm of the local permutation matrix, and the uniform norm bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace QatlibTests.QComplexity97ReversibleTmConsumer

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Papers.QComplexity97.ReversibleTm.ReversibleStep
open scoped Matrix.Norms.L2Operator

/-- Flipping the two-element control register. -/
def flipState (p : Fin 2) : Fin 2 := if p = 0 then 1 else 0

/-- Flipping a two-element control register is involutive. -/
theorem flipState_involutive (p : Fin 2) : flipState (flipState p) = p := by
  fin_cases p <;> rfl

/-- A concrete reversible machine: it writes the scanned symbol, flips the control state, and moves
the head right. -/
def flipSwap : Machine (Fin 2) (Fin 2) where
  blank := 0
  step p a := ⟨a, flipState p, .right⟩

/-- Every destination state of `flipSwap` is entered moving right, so the incoming direction is
unique. -/
theorem flipSwap_incomingDirectionUnique : IncomingDirectionUnique flipSwap := by
  intro p₁ a₁ p₂ a₂ _
  rfl

/-- The cell map of `flipSwap` is injective. -/
theorem flipSwap_cellMap_injective : CellMapInjective flipSwap := by
  intro x y h
  have hwrite : x.2 = y.2 := congrArg Prod.fst h
  have hnext : flipState x.1 = flipState y.1 := congrArg Prod.snd h
  have hstate : x.1 = y.1 := by
    have h := congrArg flipState hnext
    simpa only [flipState_involutive] using h
  exact Prod.ext hstate hwrite

/-- The cell map of `flipSwap` is bijective on the nonempty four-element cell type. -/
theorem flipSwap_cellMap_bijective : Function.Bijective (CellMap flipSwap) := by
  refine ⟨flipSwap_cellMap_injective, ?_⟩
  intro y
  refine ⟨(flipState y.2, y.1), ?_⟩
  change (y.1, flipState (flipState y.2)) = y
  simp only [flipState_involutive]

/-- The global configuration update of `flipSwap` is bijective. -/
theorem flipSwap_bijective : Function.Bijective (targetCfg flipSwap) :=
  targetCfg_bijective flipSwap flipSwap_incomingDirectionUnique flipSwap_cellMap_injective

/-- Every configuration of `flipSwap` has exactly one predecessor. -/
theorem flipSwap_unique_predecessor (c : Config (Fin 2) (Fin 2) flipSwap.blank) :
    ∃! d, targetCfg flipSwap d = c :=
  existsUnique_predecessor flipSwap flipSwap_incomingDirectionUnique flipSwap_cellMap_injective c

/-- Assigning amplitude one to the deterministic transitions of `flipSwap` gives a globally
well-formed quantum rule. -/
theorem flipSwap_globallyWellformed : (rule flipSwap).GloballyWellformed :=
  rule_globallyWellformed flipSwap flipSwap_incomingDirectionUnique flipSwap_cellMap_injective

/-- The local transition matrix of `flipSwap` has Euclidean L2 operator norm one. -/
theorem flipSwap_cell_opNorm :
    ‖(cellPerm flipSwap flipSwap_cellMap_injective).permMatrix ℂ‖ = 1 :=
  cellPermMatrix_opNorm flipSwap flipSwap_cellMap_injective

/-- The uniform norm bound from the increment specializes to `flipSwap`. -/
theorem flipSwap_uniform_norm_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ ψ : State (Fin 2) (Fin 2) flipSwap.blank,
        ‖stepUnitary flipSwap flipSwap_incomingDirectionUnique flipSwap_cellMap_injective ψ‖ ≤
          C * ‖ψ‖ := by
  obtain ⟨C, hC, h⟩ := step_norm_bound_uniform
  exact ⟨C, hC, fun ψ =>
    h flipSwap flipSwap_incomingDirectionUnique flipSwap_cellMap_injective ψ⟩

/-- The start configuration with control state `0`, head at cell `0`, and the symbol `1` written
there. -/
def startCfg : Config (Fin 2) (Fin 2) flipSwap.blank :=
  ⟨0, (Tape.empty 0).write 0 1, 0⟩

/-- One step of `flipSwap` from the concrete start configuration. -/
theorem startCfg_step :
    (rule flipSwap).column startCfg =
      ket (⟨1, (Tape.empty 0).write 0 1, 1⟩ : Config (Fin 2) (Fin 2) flipSwap.blank) := by
  rw [rule_column]
  congr 1
  apply Config.ext
  · rfl
  · simp [targetCfg, startCfg, flipSwap, Tape.write_write]
  · simp [targetCfg, startCfg, flipSwap, Dir.offset]

/-- The amplitude-one rule of `flipSwap` has normalized local transition amplitudes. -/
theorem flipSwap_local_norm (p a : Fin 2) :
    ∑ t : Move × Fin 2 × Fin 2,
      ‖(rule flipSwap).amplitude p a t.1 t.2.1 t.2.2‖ ^ 2 = 1 :=
  (rule flipSwap).local_norm_of_global flipSwap_globallyWellformed p a

/-- The cell type of `flipSwap` is nonempty; this records the non-degeneracy of the instance. -/
theorem register_nondegenerate : 0 < Fintype.card (Fin 2 × Fin 2) := by
  simp

/-- The cell permutation of `flipSwap` is not the identity, so the instance is non-vacuous. -/
theorem flipSwap_cellPerm_nontrivial :
    cellPerm flipSwap flipSwap_cellMap_injective ≠ Equiv.refl (Fin 2 × Fin 2) := by
  intro h
  have h0 : cellPerm flipSwap flipSwap_cellMap_injective (0, 0) = (0, 0) := by
    simpa using
      congrFun (congrArg (fun e : Equiv.Perm (Fin 2 × Fin 2) =>
        (e : (Fin 2 × Fin 2) → (Fin 2 × Fin 2))) h) (0, 0)
  rw [cellPerm_apply] at h0
  simp only [flipSwap, flipState, Prod.mk.injEq] at h0
  exact absurd h0.1 (by decide)

end QatlibTests.QComplexity97ReversibleTmConsumer
