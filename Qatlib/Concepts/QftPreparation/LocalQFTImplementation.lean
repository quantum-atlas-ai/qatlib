/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.OperatorErrors.OperatorError
set_option warningAsError false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.QftPreparation.LocalQFTImplementation

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false

variable {n : ℕ}

def regValue (n : ℕ) (x : Reg n) : ℕ := ∑ i, (if x i then 1 else 0) * 2 ^ (n - 1 - i.val)

def regValueLsb (n : ℕ) (x : Reg n) : ℕ := ∑ i, (if x i then 1 else 0) * 2 ^ i.val

def regCastSucc {n : ℕ} (x : Reg (n + 1)) : Reg n := fun i => x i.castSucc

theorem regValue_succ (x : Reg (n + 1)) :
    regValue (n + 1) x = regValue n (regCastSucc x) * 2 + (if x (Fin.last n) then 1 else 0) := by
  have hcast : ∀ i : Fin n, ((i.castSucc : Fin (n + 1)) : ℕ) = i.val := fun i => rfl
  simp only [regValue, Fin.sum_univ_castSucc, regCastSucc, hcast]
  rw [Finset.sum_congr rfl (fun i _ => by
    have hexp : n + 1 - 1 - i.val = (n - 1 - i.val) + 1 := by omega
    rw [hexp, pow_succ]), Finset.sum_mul]
  have hlast : ((Fin.last n : Fin (n + 1)) : ℕ) = n := rfl
  have hexp2 : n + 1 - 1 - n = 0 := by omega
  rw [hlast, hexp2, pow_zero, mul_one]
  have hsum : (∑ i : Fin n, (if x i.castSucc then 1 else 0) * (2 ^ (n - 1 - i.val) * 2))
      = ∑ i : Fin n, (if x i.castSucc then 1 else 0) * 2 ^ (n - 1 - i.val) * 2 :=
    Finset.sum_congr rfl (fun i _ => (mul_assoc _ _ _).symm)
  rw [hsum]
  rfl

theorem bitVecEquiv_val_eq_regValue :
    ∀ (m : ℕ) (x : Reg m), (bitVecEquiv m x).val = regValue m x := by
  intro m
  induction m with
  | zero =>
      intro x
      haveI : Subsingleton (Fin (2 ^ 0)) := by rw [pow_zero]; infer_instance
      have hz : (bitVecEquiv 0 x) = 0 := Subsingleton.elim _ _
      rw [hz, Fin.val_zero]
      simp [regValue]
  | succ m ih =>
      intro x
      have h2 : bitVecEquiv (m + 1) x
          = Equiv.cast (congrArg Fin (Nat.pow_succ 2 m).symm)
              (finProdFinEquiv ((Equiv.prodCongr (bitVecEquiv m) boolEquivFin2)
                (regSuccEquiv m x))) := rfl
      have h1 : regSuccEquiv m x = (regCastSucc x, x (Fin.natAdd m 0)) := rfl
      have hcast : ∀ (e : 2 ^ m * 2 = 2 ^ (m + 1)) (y : Fin (2 ^ m * 2)),
          ((Equiv.cast (congrArg Fin e)) y).val = y.val := by
        intro e y; cases e; rfl
      rw [h2, h1, hcast (Nat.pow_succ 2 m).symm]
      simp only [Equiv.prodCongr_apply, Prod.map_apply]
      have hfp : (finProdFinEquiv (bitVecEquiv m (regCastSucc x),
          boolEquivFin2 (x (Fin.natAdd m 0)))).val
          = (boolEquivFin2 (x (Fin.natAdd m 0)) : ℕ)
            + 2 * (bitVecEquiv m (regCastSucc x)).val := rfl
      rw [hfp, ih, regValue_succ]
      show (boolEquivFin2 (x (Fin.natAdd m 0)) : ℕ) + 2 * regValue m (regCastSucc x)
        = regValue m (regCastSucc x) * 2 + (if x (Fin.last m) then 1 else 0)
      have hbf : (boolEquivFin2 (x (Fin.natAdd m 0)) : ℕ)
          = (if x (Fin.natAdd m 0) then 1 else 0) := by
        cases h : x (Fin.natAdd m 0) <;> simp [boolEquivFin2]
      rw [hbf, show x (Fin.natAdd m 0) = x (Fin.last m) from rfl]
      ring

theorem bitVecEquiv_binary_msb_expansion :
    ∀ (m : ℕ) (x : Reg m),
      (bitVecEquiv m x).val = ∑ i : Fin m, (if x i then 1 else 0) * 2 ^ (m - 1 - i.val) :=
  fun m x => bitVecEquiv_val_eq_regValue m x

def localHadamard (n : ℕ) : List (LocalQFTGate n) := (List.finRange n).map LocalQFTGate.h

@[simp] theorem localHadamard_length (n : ℕ) : (localHadamard n).length = n := by
  simp [localHadamard]

theorem localProgramMatrix_map_h (ws : List (Fin n)) (hnd : ws.Nodup) :
    ∀ (x y : Reg n), localProgramMatrix (ws.map LocalQFTGate.h) x y =
      if (∀ k : Fin n, k ∉ ws → x k = y k)
      then (ws.map fun w => Hadamard (x w) (y w)).prod
      else 0 := by
  induction ws with
  | nil =>
      intro x y
      show (1 : Matrix (Reg n) (Reg n) ℂ) x y = _
      rw [Matrix.one_apply]
      by_cases hxy : x = y
      · subst hxy; simp
      · rw [if_neg hxy, if_neg]
        exact fun h => hxy (funext fun k => h k (by simp))
  | cons w ws ih =>
      rcases List.nodup_cons.mp hnd with ⟨hw, hws⟩
      intro x y
      rw [List.map_cons, localProgramMatrix_cons, Matrix.mul_apply]
      have hIH : ∀ z : Reg n, localProgramMatrix (ws.map LocalQFTGate.h) x z *
          localGateMatrix (.h w) z y =
            (if (∀ k : Fin n, k ∉ ws → x k = z k)
              then (ws.map fun w' => Hadamard (x w') (z w')).prod else 0) *
            (if (∀ k : Fin n, k ≠ w → z k = y k) then Hadamard (z w) (y w) else 0) := by
        intro z
        rw [ih hws x z, localGateMatrix_h]
      rw [Finset.sum_congr rfl (fun z _ => hIH z)]
      by_cases hcond : ∀ k : Fin n, k ∉ (w :: ws) → x k = y k
      · set z₀ : Reg n := Function.update y w (x w) with hz₀
        have hsupp : ∀ k : Fin n, k ∉ ws → x k = z₀ k := by
          intro k hk
          by_cases hkw : k = w
          · subst hkw; rw [hz₀, Function.update_self]
          · rw [hz₀, Function.update_of_ne hkw]
            exact hcond k (by simp [List.mem_cons, hkw, hk])
        have hmap : (ws.map fun w' => Hadamard (x w') (z₀ w'))
            = (ws.map fun w' => Hadamard (x w') (y w')) :=
          List.map_congr_left fun w' hw' => by
            have hne : w' ≠ w := by
              intro h
              subst h
              exact hw hw'
            rw [hz₀, Function.update_of_ne hne]
        have hterm : (if (∀ k : Fin n, k ∉ ws → x k = z₀ k)
              then (ws.map fun w' => Hadamard (x w') (z₀ w')).prod else 0) *
            (if (∀ k : Fin n, k ≠ w → z₀ k = y k) then Hadamard (z₀ w) (y w) else 0)
            = (ws.map fun w' => Hadamard (x w') (y w')).prod * Hadamard (x w) (y w) := by
          rw [if_pos hsupp, hmap,
            if_pos (fun k hk => by rw [hz₀, Function.update_of_ne hk]),
            hz₀, Function.update_self]
        rw [Finset.sum_eq_single z₀]
        · rw [hterm, if_pos hcond, List.map_cons, List.prod_cons, mul_comm]
        · intro z _ hz
          by_cases hzsupp : ∀ k : Fin n, k ≠ w → z k = y k
          · have hzw : z w ≠ x w := by
              intro h
              apply hz
              funext k
              by_cases hkw : k = w
              · subst hkw; rw [hz₀, Function.update_self]; exact h
              · rw [hz₀, Function.update_of_ne hkw]; exact hzsupp k hkw
            rw [if_neg (fun h => hzw (h w hw).symm), zero_mul]
          · rw [if_neg hzsupp, mul_zero]
        · intro h; exact absurd (Finset.mem_univ z₀) h
      · rw [if_neg hcond]
        refine Finset.sum_eq_zero fun z _ => ?_
        by_cases hzsupp : ∀ k : Fin n, k ≠ w → z k = y k
        · obtain ⟨k₀, hk₀, hne⟩ : ∃ k : Fin n, k ∉ (w :: ws) ∧ x k ≠ y k := by
            by_contra h
            push Not at h
            exact absurd h hcond
          have hk₀w : k₀ ≠ w := by
            intro hw'
            subst hw'
            exact hk₀ List.mem_cons_self
          have hk₀ws : k₀ ∉ ws := fun h => hk₀ (List.mem_cons_of_mem w h)
          rw [if_neg (fun h => hne ((h k₀ hk₀ws).trans (hzsupp k₀ hk₀w))), zero_mul]
        · rw [if_neg hzsupp, mul_zero]

theorem localProgramMatrix_localHadamard (n : ℕ) :
    localProgramMatrix (localHadamard n) = HadamardN n := by
  ext x y
  rw [localHadamard, localProgramMatrix_map_h _ (List.nodup_finRange n) x y,
    if_pos (fun k hk => absurd (List.mem_finRange k) hk)]
  show (List.map (fun w => Hadamard (x w) (y w)) (List.finRange n)).prod = _
  rw [← List.ofFn_eq_map, List.prod_ofFn]
  rfl

theorem localHadamard_actual_implementation (n : ℕ) :
    localProgramMatrix (localHadamard n) = HadamardN n ∧
    (localHadamard n).length = n ∧
    Run (1 : Matrix (Reg n) (Reg n) ℂ) (localProgramCircuit (localHadamard n))
      (Ket (ZeroStr n)) = Uniform (Reg n) ∧
    GateCount (localProgramCircuit (localHadamard n)) = n ∧
    QueryCount (localProgramCircuit (localHadamard n)) = 0 := by
  obtain ⟨run, _, _, _, _, qc, gc, _, _⟩ :=
    localDyadicProgram_run_adjoint_cost n (localHadamard n) (Ket (ZeroStr n))
  exact ⟨localProgramMatrix_localHadamard n, localHadamard_length n,
    by rw [run, localProgramMatrix_localHadamard n]; exact applyGate_hadamardN_ket_zero n,
    by rw [gc, localHadamard_length], qc⟩

theorem sqrt_two_pow (n : ℕ) : (Real.sqrt 2) ^ n = Real.sqrt ((2 : ℝ) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Real.sqrt_mul (by positivity), ← ih]

theorem primRoot_two_pow_pow (n m : ℕ) :
    primRoot (2 ^ n) ^ m
      = Complex.exp (((2 * Real.pi * m / ((2 ^ n : ℕ) : ℝ)) : ℝ) * Complex.I) := by
  rw [primRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem primRoot_two_pow_pow_half (n : ℕ) (hn : 0 < n) :
    primRoot (2 ^ n) ^ (2 ^ (n - 1)) = -1 := by
  rw [primRoot_two_pow_pow]
  have hne : ((2 ^ (n - 1) : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((2 ^ n : ℕ) : ℝ) = 2 * ((2 ^ (n - 1) : ℕ) : ℝ) := by
    norm_cast
    rw [← pow_succ', Nat.sub_add_cancel hn]
  have h1 : (2 * Real.pi * (2 ^ (n - 1) : ℕ) / ((2 ^ n : ℕ) : ℝ)) = Real.pi := by
    rw [h2]
    field_simp
  rw [h1, Complex.exp_pi_mul_I]

theorem hadamard_entry_eq (n : ℕ) (hn : 0 < n) (p q : Bool) :
    Hadamard p q = (Real.sqrt 2 : ℂ)⁻¹ *
      primRoot (2 ^ n) ^ (p.toNat * q.toNat * 2 ^ (n - 1)) := by
  show (Real.sqrt 2 : ℂ)⁻¹ * (if p && q then -1 else 1) = _
  cases p <;> cases q <;> simp [primRoot_two_pow_pow_half n hn]

theorem cp_phase_eq (n a c : ℕ) (hac : a ≤ c) (hc : c < n) :
    Complex.exp (dyadicPhaseAngle (c - a + 1) false * Complex.I)
      = primRoot (2 ^ n) ^ (2 ^ (n - 1 - c + a)) := by
  have hdef : dyadicPhaseAngle (c - a + 1) false
      = 2 * Real.pi / (2 ^ (c - a + 1) : ℝ) := rfl
  rw [hdef, primRoot_two_pow_pow]
  congr 1
  congr 1
  norm_cast
  push_cast
  have h1 : (2 : ℝ) ^ n = (2 : ℝ) ^ (c - a + 1) * (2 : ℝ) ^ (n - 1 - c + a) := by
    rw [← pow_add]; congr 1; omega
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination 2 * Real.pi * h1

theorem primRoot_two_pow_pow_self (n : ℕ) : primRoot (2 ^ n) ^ (2 ^ n) = 1 :=
  (isPrimitiveRoot_primRoot (pow_ne_zero n (by norm_num : (2 : ℕ) ≠ 0))).pow_eq_one

def localQFTRow (n a : ℕ) (ha : a < n) : List (LocalQFTGate n) :=
  .h ⟨a, ha⟩ :: (List.range' (a + 1) (n - 1 - a)).pmap
    (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false)
    (fun c hc => by
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc
      omega)

theorem list_prod_pow_eq_pow_sum (x : ℂ) (m : ℕ → ℕ) :
    ∀ l : List ℕ, (l.map fun c => x ^ m c).prod = x ^ (l.map m).sum := by
  intro l
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, ih, pow_add]

theorem localProgramMatrix_diagonal (gs : List (LocalQFTGate n)) (f : LocalQFTGate n → Reg n → ℂ)
    (h : ∀ g ∈ gs, localGateMatrix g = Matrix.diagonal (f g)) :
    localProgramMatrix gs = Matrix.diagonal (fun u => (gs.map fun g => f g u).prod) := by
  induction gs with
  | nil =>
    show (1 : Matrix (Reg n) (Reg n) ℂ) = Matrix.diagonal _
    rw [← Matrix.diagonal_one]
    rfl
  | cons g gs ih =>
    have hgs : ∀ g' ∈ gs, localGateMatrix g' = Matrix.diagonal (f g') :=
      fun g' hg' => h g' (List.mem_cons_of_mem g hg')
    rw [localProgramMatrix_cons, ih hgs, h g List.mem_cons_self,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext u
    show (List.map (fun g' => f g' u) gs).prod * f g u
      = (List.map (fun g' => f g' u) (g :: gs)).prod
    rw [List.map_cons, List.prod_cons]
    exact mul_comm _ _

theorem localGateMatrix_cp_eq_diagonal_pow (n a c : ℕ) (ha : a < n) (hac : a ≤ c)
    (hc : c < n) :
    localGateMatrix (LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false)
      = Matrix.diagonal (fun u => primRoot (2 ^ n) ^
          ((u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a))) := by
  show Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext u
  show (if u ⟨a, ha⟩ && u ⟨c, hc⟩
      then Complex.exp (dyadicPhaseAngle (c - a + 1) false * Complex.I) else 1) = _
  cases hu1 : u ⟨a, ha⟩ <;> cases hu2 : u ⟨c, hc⟩ <;>
    simp [cp_phase_eq n a c hac hc]

def localQFTCpListPhaseSum (n : ℕ) (a : Fin n) (u : Reg n) (s l : ℕ)
    (H : ∀ c ∈ List.range' s l, c < n) : ℕ :=
  ((List.range' s l).pmap (fun c hc =>
    (u a).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a.val)) H).sum

theorem localProgramMatrix_cps (n a : ℕ) (ha : a < n) :
    ∀ (s l : ℕ) (_hs : a < s) (_hl : s + l ≤ n) (H : ∀ c ∈ List.range' s l, c < n),
    localProgramMatrix ((List.range' s l).pmap
        (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) H)
      = Matrix.diagonal (fun u => primRoot (2 ^ n) ^
          localQFTCpListPhaseSum n ⟨a, ha⟩ u s l H) := by
  intro s l
  induction l generalizing s with
  | zero =>
    intro _ _ H
    show localProgramMatrix ([] : List (LocalQFTGate n)) = _
    rw [localProgramMatrix_nil]
    show (1 : Matrix (Reg n) (Reg n) ℂ) = Matrix.diagonal _
    rw [← Matrix.diagonal_one]
    rfl
  | succ l ih =>
    intro hs hl H
    have Hs : s < n := H s List.mem_cons_self
    have Hrest : ∀ c ∈ List.range' (s + 1) l, c < n :=
      fun c hc => H c (List.mem_cons_of_mem s hc)
    have hs' : a < s + 1 := by omega
    have hl' : s + 1 + l ≤ n := by omega
    show localProgramMatrix ((s :: List.range' (s + 1) l).pmap
        (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) H) = _
    rw [show (s :: List.range' (s + 1) l).pmap
          (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) H
        = LocalQFTGate.cp ⟨a, ha⟩ ⟨s, Hs⟩ (s - a + 1) false ::
          (List.range' (s + 1) l).pmap
            (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) Hrest from rfl,
      localProgramMatrix_cons, ih (s + 1) hs' hl' Hrest,
      localGateMatrix_cp_eq_diagonal_pow n a s ha (by omega) Hs,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext u
    show primRoot (2 ^ n) ^ ((List.range' (s + 1) l).pmap (fun c hc =>
        (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) Hrest).sum
      * primRoot (2 ^ n) ^ ((u ⟨a, ha⟩).toNat * (u ⟨s, Hs⟩).toNat * 2 ^ (n - 1 - s + a))
      = primRoot (2 ^ n) ^ ((s :: List.range' (s + 1) l).pmap (fun c hc =>
        (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) H).sum
    rw [← pow_add]
    congr 1
    show ((List.range' (s + 1) l).pmap (fun c hc =>
        (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) Hrest).sum
      + (u ⟨a, ha⟩).toNat * (u ⟨s, Hs⟩).toNat * 2 ^ (n - 1 - s + a)
      = ((s :: List.range' (s + 1) l).pmap (fun c hc =>
        (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) H).sum
    rw [show ((s :: List.range' (s + 1) l).pmap (fun c hc =>
          (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) H).sum
        = (u ⟨a, ha⟩).toNat * (u ⟨s, Hs⟩).toNat * 2 ^ (n - 1 - s + a)
          + ((List.range' (s + 1) l).pmap (fun c hc =>
            (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) Hrest).sum from rfl]
    exact add_comm _ _

def localQFTRows (n : ℕ) : (r : ℕ) → List (LocalQFTGate n)
  | 0 => []
  | r + 1 => if h : r < n then localQFTRows n r ++ localQFTRow n r h else []

theorem localQFTRows_zero (n : ℕ) : localQFTRows n 0 = [] := rfl

theorem localQFTRows_succ (n r : ℕ) (hr : r < n) :
    localQFTRows n (r + 1) = localQFTRows n r ++ localQFTRow n r hr :=
  dif_pos hr

def localQFTSwapPrefix (n : ℕ) : (m : ℕ) → List (LocalQFTGate n)
  | 0 => []
  | m + 1 => if h : m + 1 ≤ n / 2 then
      localQFTSwapPrefix n m ++ [LocalQFTGate.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩]
    else []

theorem localQFTSwapPrefix_succ (n m : ℕ) (hm : m + 1 ≤ n / 2) :
    localQFTSwapPrefix n (m + 1)
      = localQFTSwapPrefix n m ++ [LocalQFTGate.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩] :=
  dif_pos hm

def localQFTSwaps (n : ℕ) : List (LocalQFTGate n) := localQFTSwapPrefix n (n / 2)

def localQFT (n : ℕ) : List (LocalQFTGate n) := localQFTRows n n ++ localQFTSwaps n

def cpExpSummand (n : ℕ) (a : Fin n) (u : Reg n) (c : ℕ) : ℕ :=
  (u a).toNat * (if hc : c < n then (u ⟨c, hc⟩).toNat else 0) * 2 ^ (n - 1 - c + a.val)

theorem list_sum_map_range' (m : ℕ → ℕ) (s : ℕ) :
    ∀ l : ℕ, ((List.range' s l).map m).sum = ∑ i ∈ Finset.Ico s (s + l), m i := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    have hrw : List.range' s (l + 1) = List.range' s l ++ [s + l] := by
      have h := List.range'_append_1 (s := s) (m := l) (n := 1)
      have h1 : List.range' (s + l) 1 = [s + l] := rfl
      rw [h1] at h
      exact h.symm
    rw [hrw, List.map_append, List.map_cons, List.map_nil, List.sum_append, ih,
      List.sum_cons, List.sum_nil, add_zero,
      show s + (l + 1) = s + l + 1 from by omega,
      Finset.sum_Ico_succ_top (Nat.le_add_right s l)]

def localQFTCpPhaseSum (n : ℕ) (a : Fin n) (u : Reg n) : ℕ :=
  ∑ j : Fin n, if a.val < j.val then (u a).toNat * (u j).toNat * 2 ^ (n - 1 - j.val + a.val) else 0

theorem localQFTCpPhaseSum_eq_filter_range (n : ℕ) (a : Fin n) (u : Reg n) :
    localQFTCpPhaseSum n a u
      = ∑ c ∈ (Finset.range n).filter (fun c => a.val < c), cpExpSummand n a u c := by
  have hpoint : ∀ j : Fin n,
      (if a < j then (u a).toNat * (u j).toNat * 2 ^ (n - 1 - j.val + a.val) else 0)
      = (fun c => if a.val < c then cpExpSummand n a u c else 0) j.val := by
    intro j
    show (if a.val < j.val then _ else 0) = if a.val < j.val then _ else 0
    by_cases h : a.val < j.val
    · rw [if_pos h, if_pos h]
      show (u a).toNat * (u j).toNat * 2 ^ _
        = (u a).toNat * (if hc : j.val < n then (u ⟨j.val, hc⟩).toNat else 0) * 2 ^ _
      rw [dif_pos j.isLt]
    · rw [if_neg h, if_neg h]
  show ∑ j : Fin n, (if a.val < j.val then (u a).toNat * (u j).toNat * 2 ^ (n - 1 - j.val + a.val)
      else 0) = _
  rw [Finset.sum_filter, ← Fin.sum_univ_eq_sum_range
    (fun c => if a.val < c then cpExpSummand n a u c else 0) n]
  exact Finset.sum_congr rfl fun j _ => hpoint j

theorem filter_range_lt_eq_Ico (n a : ℕ) :
    (Finset.range n).filter (fun c => a < c) = Finset.Ico (a + 1) n := by
  rw [Finset.range_eq_Ico]
  rw [show (Finset.Ico 0 n).filter (fun c => a < c)
      = (Finset.Ico 0 n).filter (fun c => a + 1 ≤ c) from
    Finset.filter_congr (fun c _ => (Nat.succ_le_iff).symm)]
  exact Finset.Ico_filter_le_of_left_le (Nat.zero_le _)

theorem pmap_phase_sum_eq_map_sum (n a : ℕ) (ha : a < n) (u : Reg n)
    (s l : ℕ) (H : ∀ c ∈ List.range' s l, c < n) :
    ((List.range' s l).pmap (fun c hc =>
        (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) H).sum
      = ((List.range' s l).map (fun c => cpExpSummand n ⟨a, ha⟩ u c)).sum := by
  rw [List.pmap_eq_map_attach]
  have hx : ∀ x ∈ (List.range' s l).attach,
      (u ⟨a, ha⟩).toNat * (u ⟨x.1, H x.1 x.2⟩).toNat * 2 ^ (n - 1 - x.1 + a)
        = cpExpSummand n ⟨a, ha⟩ u x.1 := by
    intro x _
    show _ = (u ⟨a, ha⟩).toNat * (if hc : x.1 < n then (u ⟨x.1, hc⟩).toNat else 0) * 2 ^ _
    rw [dif_pos (H x.1 x.2)]
  rw [List.map_congr_left hx, List.attach_map_val]

theorem localQFTCpListPhaseSum_eq (n a : ℕ) (ha : a < n) (u : Reg n)
    (H : ∀ c ∈ List.range' (a + 1) (n - 1 - a), c < n) :
    localQFTCpListPhaseSum n ⟨a, ha⟩ u (a + 1) (n - 1 - a) H
      = localQFTCpPhaseSum n ⟨a, ha⟩ u := by
  show ((List.range' (a + 1) (n - 1 - a)).pmap (fun c hc =>
      (u ⟨a, ha⟩).toNat * (u ⟨c, hc⟩).toNat * 2 ^ (n - 1 - c + a)) H).sum = _
  rw [pmap_phase_sum_eq_map_sum n a ha u _ _ H, list_sum_map_range',
    localQFTCpPhaseSum_eq_filter_range, filter_range_lt_eq_Ico,
    show a + 1 + (n - 1 - a) = n from by omega]

def localQFTPhaseNum (n r : ℕ) (z x : Reg n) : ℕ :=
  ∑ i : Fin n, if i.val < r then (z i).toNat *
    (∑ j : Fin n, if i ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + i.val) else 0) else 0

theorem localQFTPhaseNum_zero (n : ℕ) (z x : Reg n) : localQFTPhaseNum n 0 z x = 0 :=
  Finset.sum_eq_zero fun i _ => if_neg (Nat.not_lt_zero i.val)

theorem localQFTPhaseNum_succ (n r : ℕ) (hr : r < n) (z x : Reg n) :
    localQFTPhaseNum n (r + 1) z x
      = localQFTPhaseNum n r z x + (z ⟨r, hr⟩).toNat *
        (∑ j : Fin n, if ⟨r, hr⟩ ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0) := by
  have hsplit : ∀ i : Fin n,
      (if i.val < r + 1 then (z i).toNat *
          (∑ j : Fin n, if i ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + i.val) else 0)
        else 0)
      = (if i.val < r then (z i).toNat *
          (∑ j : Fin n, if i ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + i.val) else 0)
        else 0)
        + (if i = ⟨r, hr⟩ then (z ⟨r, hr⟩).toNat *
          (∑ j : Fin n, if ⟨r, hr⟩ ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0)
        else 0) := by
    intro i
    by_cases h1 : i.val < r
    · have hne : i ≠ ⟨r, hr⟩ := fun h => by rw [h] at h1; simp at h1
      rw [if_pos (by omega), if_pos h1, if_neg hne, add_zero]
    · by_cases h2 : i = ⟨r, hr⟩
      · subst h2
        rw [if_pos (Nat.lt_succ_self r),
          if_neg (Nat.lt_irrefl r), if_pos rfl, zero_add]
      · have h3 : i.val ≠ r := fun h => h2 (Fin.ext h)
        rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]
  show (∑ i : Fin n, if i.val < r + 1 then _ else 0) = _
  rw [show localQFTPhaseNum n r z x = ∑ i : Fin n, (if i.val < r then (z i).toNat *
      (∑ j : Fin n, if i ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + i.val) else 0) else 0)
    from rfl]
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem localQFTPhaseNum_inner_split (n r : ℕ) (hr : r < n) (x : Reg n) :
    (∑ j : Fin n, if ⟨r, hr⟩ ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0)
      = (x ⟨r, hr⟩).toNat * 2 ^ (n - 1)
        + ∑ j : Fin n, if r < j.val then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0 := by
  have hsplit : ∀ j : Fin n,
      (if ⟨r, hr⟩ ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0)
      = (if j = ⟨r, hr⟩ then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0)
        + (if r < j.val then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0) := by
    intro j
    by_cases h1 : r < j.val
    · have hne : j ≠ ⟨r, hr⟩ := fun h => by rw [h] at h1; simp at h1
      have hle : ⟨r, hr⟩ ≤ j := by show r ≤ j.val; omega
      rw [if_pos hle, if_neg hne, if_pos h1, zero_add]
    · by_cases h2 : j = ⟨r, hr⟩
      · subst h2
        rw [if_pos (le_refl _), if_pos rfl, if_neg h1, add_zero]
      · have h3 : j.val ≠ r := fun h => h2 (Fin.ext h)
        have hle : ¬ ⟨r, hr⟩ ≤ j := by show ¬ r ≤ j.val; omega
        rw [if_neg hle, if_neg h2, if_neg h1, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show (x ⟨r, hr⟩).toNat * 2 ^ (n - 1 - r + r) + _ = _
  rw [show n - 1 - r + r = n - 1 from by omega]

theorem localQFT_h_step_sum (n r : ℕ) (hr : r < n) (z x : Reg n) (g : Reg n → ℂ)
    (hg : g (Function.update z ⟨r, hr⟩ (x ⟨r, hr⟩)) = g z) :
    (∑ w : Reg n, localGateMatrix (.h ⟨r, hr⟩) z w *
        (if (∀ i : Fin n, r ≤ i.val → w i = x i) then g w else 0))
      = if (∀ i : Fin n, r + 1 ≤ i.val → z i = x i)
        then Hadamard (z ⟨r, hr⟩) (x ⟨r, hr⟩) * g z else 0 := by
  by_cases hsupp : ∀ i : Fin n, r + 1 ≤ i.val → z i = x i
  · set w₀ : Reg n := Function.update z ⟨r, hr⟩ (x ⟨r, hr⟩) with hw₀
    have hMsupp : ∀ i : Fin n, r ≤ i.val → w₀ i = x i := by
      intro i hi
      by_cases hir : i = ⟨r, hr⟩
      · subst hir; rw [hw₀, Function.update_self]
      · have hiv : i.val ≠ r := fun h => hir (Fin.ext h)
        have hi' : r + 1 ≤ i.val := by omega
        rw [hw₀, Function.update_of_ne hir]
        exact hsupp i hi'
    have hHsupp : ∀ k : Fin n, k ≠ ⟨r, hr⟩ → z k = w₀ k := fun k hk => by
      rw [hw₀, Function.update_of_ne hk]
    rw [Finset.sum_eq_single w₀]
    · rw [localGateMatrix_h, if_pos hHsupp, hw₀, Function.update_self, if_pos hMsupp, hg,
        if_pos hsupp]
    · intro w _ hw
      by_cases hH : ∀ k : Fin n, k ≠ ⟨r, hr⟩ → z k = w k
      · have hwr : w ⟨r, hr⟩ ≠ x ⟨r, hr⟩ := by
          intro h
          apply hw
          funext k
          by_cases hkr : k = ⟨r, hr⟩
          · subst hkr; rw [hw₀, Function.update_self]; exact h
          · rw [hw₀, Function.update_of_ne hkr]; exact (hH k hkr).symm
        rw [if_neg (fun hM => hwr (hM ⟨r, hr⟩ (le_refl _))), mul_zero]
      · rw [localGateMatrix_h, if_neg hH, zero_mul]
    · intro h; exact absurd (Finset.mem_univ w₀) h
  · rw [if_neg hsupp]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases hH : ∀ k : Fin n, k ≠ ⟨r, hr⟩ → z k = w k
    · obtain ⟨i₀, hi₀, hne⟩ : ∃ i : Fin n, r + 1 ≤ i.val ∧ z i ≠ x i := by
        by_contra h
        push Not at h
        exact absurd h hsupp
      have hi₀r : i₀ ≠ ⟨r, hr⟩ := fun h => by rw [h] at hi₀; simp at hi₀
      rw [if_neg (fun hM => hne ((hH i₀ hi₀r).trans (hM i₀ (by omega)))), mul_zero]
    · rw [localGateMatrix_h, if_neg hH, zero_mul]

theorem localProgramMatrix_localQFTRows (n : ℕ) :
    ∀ (r : ℕ) (_hr : r ≤ n) (z x : Reg n),
    localProgramMatrix (localQFTRows n r) z x
      = if (∀ i : Fin n, r ≤ i.val → z i = x i)
        then ((Real.sqrt 2 : ℂ)⁻¹) ^ r * primRoot (2 ^ n) ^ localQFTPhaseNum n r z x
        else 0 := by
  intro r
  induction r with
  | zero =>
    intro hr z x
    show (1 : Matrix (Reg n) (Reg n) ℂ) z x = _
    rw [Matrix.one_apply, localQFTPhaseNum_zero, pow_zero, pow_zero, one_mul]
    by_cases hz : z = x
    · subst hz; rw [if_pos rfl, if_pos (fun i _ => rfl)]
    · rw [if_neg hz, if_neg (fun h => hz (funext fun i => h i (Nat.zero_le _)))]
  | succ r ih =>
    intro hr z x
    have hrlt : r < n := by omega
    have hrle : r ≤ n := by omega
    have H : ∀ c ∈ List.range' (r + 1) (n - 1 - r), c < n := fun c hc => by
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc
      omega
    have hcps := localProgramMatrix_cps n r hrlt (r + 1) (n - 1 - r) (by omega) (by omega) H
    have hIH : ∀ w : Reg n, localProgramMatrix (localQFTRows n r) w x
        = if (∀ i : Fin n, r ≤ i.val → w i = x i)
          then ((Real.sqrt 2 : ℂ)⁻¹) ^ r * primRoot (2 ^ n) ^ localQFTPhaseNum n r w x
          else 0 :=
      fun w => ih hrle w x
    rw [localQFTRows_succ n r hrlt, localProgramMatrix_append]
    show (localProgramMatrix (localQFTRow n r hrlt) * localProgramMatrix (localQFTRows n r)) z x
      = _
    rw [show localQFTRow n r hrlt
        = .h ⟨r, hrlt⟩ :: (List.range' (r + 1) (n - 1 - r)).pmap
            (fun c hc => LocalQFTGate.cp ⟨r, hrlt⟩ ⟨c, hc⟩ (c - r + 1) false) H from rfl,
      localProgramMatrix_cons, hcps, Matrix.mul_apply]
    have hterm : ∀ w : Reg n,
        (Matrix.diagonal (fun u => primRoot (2 ^ n) ^
            localQFTCpListPhaseSum n ⟨r, hrlt⟩ u (r + 1) (n - 1 - r) H)
          * localGateMatrix (.h ⟨r, hrlt⟩)) z w * localProgramMatrix (localQFTRows n r) w x
        = primRoot (2 ^ n) ^ localQFTCpListPhaseSum n ⟨r, hrlt⟩ z (r + 1) (n - 1 - r) H *
          (localGateMatrix (.h ⟨r, hrlt⟩) z w * localProgramMatrix (localQFTRows n r) w x) := by
      intro w
      rw [Matrix.diagonal_mul]
      ring
    rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.mul_sum]
    have hphase : localQFTPhaseNum n r (Function.update z ⟨r, hrlt⟩ (x ⟨r, hrlt⟩)) x
        = localQFTPhaseNum n r z x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < r
      · rw [if_pos hi, if_pos hi]
        have hne : i ≠ ⟨r, hrlt⟩ := fun h => by rw [h] at hi; simp at hi
        rw [Function.update_of_ne hne]
      · rw [if_neg hi, if_neg hi]
    have hcollapse := localQFT_h_step_sum n r hrlt z x
      (fun w => ((Real.sqrt 2 : ℂ)⁻¹) ^ r * primRoot (2 ^ n) ^ localQFTPhaseNum n r w x)
      (by
        show ((Real.sqrt 2 : ℂ)⁻¹) ^ r * primRoot (2 ^ n) ^
            localQFTPhaseNum n r (Function.update z ⟨r, hrlt⟩ (x ⟨r, hrlt⟩)) x
          = ((Real.sqrt 2 : ℂ)⁻¹) ^ r * primRoot (2 ^ n) ^ localQFTPhaseNum n r z x
        rw [hphase])
    rw [Finset.sum_congr rfl (fun w _ => congrArg
      (fun t => localGateMatrix (LocalQFTGate.h ⟨r, hrlt⟩) z w * t) (hIH w)), hcollapse]
    by_cases hsupp : ∀ i : Fin n, r + 1 ≤ i.val → z i = x i
    · rw [if_pos hsupp, if_pos hsupp, hadamard_entry_eq n (by omega) (z ⟨r, hrlt⟩) (x ⟨r, hrlt⟩)]
      have hexp : localQFTCpListPhaseSum n ⟨r, hrlt⟩ z (r + 1) (n - 1 - r) H
          + (z ⟨r, hrlt⟩).toNat * (x ⟨r, hrlt⟩).toNat * 2 ^ (n - 1)
          + localQFTPhaseNum n r z x
        = localQFTPhaseNum n (r + 1) z x := by
        rw [localQFTPhaseNum_succ n r hrlt z x, localQFTPhaseNum_inner_split n r hrlt x,
          mul_add, Finset.mul_sum]
        have hD : localQFTCpListPhaseSum n ⟨r, hrlt⟩ z (r + 1) (n - 1 - r) H
            = ∑ j : Fin n, if r < j.val then
              (z ⟨r, hrlt⟩).toNat * (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0 := by
          rw [localQFTCpListPhaseSum_eq n r hrlt z H]
          show localQFTCpPhaseSum n ⟨r, hrlt⟩ z = _
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : r < j.val
          · rw [if_pos hj, if_pos hj, hsupp j (by omega)]
          · rw [if_neg hj, if_neg hj]
        have hdistrib : (∑ j : Fin n, (z ⟨r, hrlt⟩).toNat *
            (if r < j.val then (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0))
            = ∑ j : Fin n, if r < j.val then
              (z ⟨r, hrlt⟩).toNat * (x j).toNat * 2 ^ (n - 1 - j.val + r) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : r < j.val
          · rw [mul_ite, if_pos hj, if_pos hj, mul_assoc]
          · rw [mul_ite, if_neg hj, if_neg hj, mul_zero]
        rw [hD, hdistrib]
        ring
      have hscal : primRoot (2 ^ n) ^ localQFTCpListPhaseSum n ⟨r, hrlt⟩ z (r + 1) (n - 1 - r) H
          * (((Real.sqrt 2 : ℂ)⁻¹ * primRoot (2 ^ n) ^
              ((z ⟨r, hrlt⟩).toNat * (x ⟨r, hrlt⟩).toNat * 2 ^ (n - 1)))
            * (((Real.sqrt 2 : ℂ)⁻¹) ^ r * primRoot (2 ^ n) ^ localQFTPhaseNum n r z x))
        = ((Real.sqrt 2 : ℂ)⁻¹) ^ (r + 1) * primRoot (2 ^ n) ^
          (localQFTCpListPhaseSum n ⟨r, hrlt⟩ z (r + 1) (n - 1 - r) H
            + (z ⟨r, hrlt⟩).toNat * (x ⟨r, hrlt⟩).toNat * 2 ^ (n - 1)
            + localQFTPhaseNum n r z x) := by
        have hcomm : ∀ (a b c d e : ℂ), a * ((b * c) * (e * d)) = (e * b) * (a * c * d) := by
          intro a b c d e; ring
        rw [hcomm, ← pow_succ, ← pow_add, ← pow_add]
      rw [hscal, hexp]
    · rw [if_neg hsupp, mul_zero, if_neg hsupp]

theorem permMatrix_mul (σ τ : Reg n → Reg n) :
    permMatrix σ * permMatrix τ = permMatrix (σ ∘ τ) := by
  ext i j
  simp only [permMatrix, Matrix.mul_apply, Matrix.of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (τ j)]
  · simp
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem permMatrix_mul_apply (σ : Reg n → Reg n) (hσ : Function.Involutive σ)
    (M : Matrix (Reg n) (Reg n) ℂ) (y x : Reg n) :
    (permMatrix σ * M) y x = M (σ y) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ y)]
  · simp only [permMatrix, Matrix.of_apply]
    rw [show σ (σ y) = y from hσ y, if_pos rfl, one_mul]
  · intro w _ hw
    show (if y = σ w then (1 : ℂ) else 0) * M w x = 0
    rw [if_neg (fun h => hw (((congrArg σ h).trans (hσ w)).symm)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

def qftSwapPerm (n m : ℕ) (i : Fin n) : Fin n :=
  if i.val < m ∨ n - 1 - i.val < m then ⟨n - 1 - i.val, by have h := i.isLt; omega⟩ else i

theorem qftSwapPerm_val (n m : ℕ) (i : Fin n) :
    (qftSwapPerm n m i).val
      = if i.val < m ∨ n - 1 - i.val < m then n - 1 - i.val else i.val := by
  show (if i.val < m ∨ n - 1 - i.val < m then (⟨n - 1 - i.val, by omega⟩ : Fin n) else i).val
    = _
  by_cases h : i.val < m ∨ n - 1 - i.val < m
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem qftSwapPerm_zero (n : ℕ) (i : Fin n) : qftSwapPerm n 0 i = i := by
  show (if i.val < 0 ∨ n - 1 - i.val < 0 then _ else i) = i
  rw [if_neg (by simp)]

theorem qftSwapPerm_step (n m : ℕ) (hm : m + 1 ≤ n / 2) (i : Fin n) :
    qftSwapPerm n m (Equiv.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩ i)
      = qftSwapPerm n (m + 1) i := by
  have hi := i.isLt
  have hmn : m < n := by omega
  have hne_of_val : ∀ {v : ℕ} (hv : v < n), i.val ≠ v → i ≠ (⟨v, hv⟩ : Fin n) := by
    intro v hv h hval
    exact h (congrArg Fin.val hval)
  apply Fin.ext
  rw [qftSwapPerm_val, qftSwapPerm_val]
  by_cases h1 : i.val < m
  · rw [Equiv.swap_apply_of_ne_of_ne (hne_of_val _ (by omega)) (hne_of_val _ (by omega)),
      if_pos (Or.inl h1), if_pos (by omega)]
  · by_cases h2 : n - 1 - i.val < m
    · rw [Equiv.swap_apply_of_ne_of_ne (hne_of_val _ (by omega)) (hne_of_val _ (by omega)),
        if_pos (Or.inr h2), if_pos (by omega)]
    · by_cases h3 : i.val = m
      · have hi3 : i = (⟨m, by omega⟩ : Fin n) := Fin.ext h3
        rw [hi3, Equiv.swap_apply_left]
        show (if n - 1 - m < m ∨ n - 1 - (n - 1 - m) < m then n - 1 - (n - 1 - m)
              else n - 1 - m)
          = if m < m + 1 ∨ n - 1 - m < m + 1 then n - 1 - m else m
        rw [if_neg (by omega), if_pos (by omega)]
      · by_cases h4 : n - 1 - i.val = m
        · have hi4v : i.val = n - 1 - m := by omega
          have hi4 : i = (⟨n - 1 - m, by omega⟩ : Fin n) := Fin.ext hi4v
          rw [hi4, Equiv.swap_apply_right]
          show (if m < m ∨ n - 1 - m < m then n - 1 - m else m)
            = if n - 1 - m < m + 1 ∨ n - 1 - (n - 1 - m) < m + 1 then n - 1 - (n - 1 - m)
              else n - 1 - m
          rw [if_neg (by omega), if_pos (by omega)]
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne (hne_of_val _ h3) (hne_of_val _ (by omega)),
            if_neg (fun h => h.elim h1 h2), if_neg (by omega)]

theorem qftSwapPerm_half (n : ℕ) (i : Fin n) : qftSwapPerm n (n / 2) i = Fin.rev i := by
  apply Fin.ext
  rw [qftSwapPerm_val, Fin.val_rev]
  by_cases h : i.val < n / 2 ∨ n - 1 - i.val < n / 2
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    have hi := i.isLt
    have h1 : ¬ i.val < n / 2 := fun h1 => h (Or.inl h1)
    have h2 : ¬ n - 1 - i.val < n / 2 := fun h2 => h (Or.inr h2)
    omega

theorem localProgramMatrix_swapPrefix (n : ℕ) :
    ∀ (m : ℕ) (_hm : m ≤ n / 2),
    localProgramMatrix (localQFTSwapPrefix n m)
      = permMatrix (fun (w : Reg n) (i : Fin n) => w (qftSwapPerm n m i)) := by
  intro m
  induction m with
  | zero =>
    intro _
    show localProgramMatrix ([] : List (LocalQFTGate n)) = _
    rw [localProgramMatrix_nil]
    show (1 : Matrix (Reg n) (Reg n) ℂ)
      = permMatrix (fun (w : Reg n) (i : Fin n) => w (qftSwapPerm n 0 i))
    have hid : (fun (w : Reg n) (i : Fin n) => w (qftSwapPerm n 0 i))
      = (fun w : Reg n => w) := by
      funext w i
      rw [qftSwapPerm_zero]
    rw [hid]
    ext i j
    simp [permMatrix, Matrix.one_apply]
  | succ m ih =>
    intro hm
    have hmle : m ≤ n / 2 := by omega
    rw [localQFTSwapPrefix_succ n m hm, localProgramMatrix_append, ih hmle,
      localProgramMatrix_cons, localProgramMatrix_nil, Matrix.one_mul]
    have hmn' : m < n := by omega
    have hnm' : n - 1 - m < n := by omega
    show (localGateMatrix (LocalQFTGate.swap ⟨m, hmn'⟩ ⟨n - 1 - m, hnm'⟩) *
      permMatrix (fun (w : Reg n) (i : Fin n) => w (qftSwapPerm n m i))) = _
    rw [show localGateMatrix (LocalQFTGate.swap ⟨m, hmn'⟩ ⟨n - 1 - m, hnm'⟩)
        = permMatrix (fun (w : Reg n) (i : Fin n) =>
          w (Equiv.swap ⟨m, hmn'⟩ ⟨n - 1 - m, hnm'⟩ i))
      from rfl, permMatrix_mul]
    congr 1
    funext w i
    show w (qftSwapPerm n m (Equiv.swap ⟨m, hmn'⟩ ⟨n - 1 - m, hnm'⟩ i))
      = w (qftSwapPerm n (m + 1) i)
    rw [qftSwapPerm_step n m hm]

theorem localProgramMatrix_localQFTSwaps (n : ℕ) :
    localProgramMatrix (localQFTSwaps n)
      = permMatrix (fun (w : Reg n) (i : Fin n) => w (Fin.rev i)) := by
  show localProgramMatrix (localQFTSwapPrefix n (n / 2)) = _
  rw [localProgramMatrix_swapPrefix n (n / 2) (le_refl _)]
  congr 1
  funext w i
  rw [qftSwapPerm_half]

theorem regValueLsb_comp_rev (n : ℕ) (w : Reg n) :
    regValueLsb n (fun i => w (Fin.rev i)) = regValue n w := by
  have hpoint : ∀ i : Fin n, (if w (Fin.rev i) then 1 else 0) * 2 ^ i.val
      = (if w (Fin.rev i) then 1 else 0) * 2 ^ (n - 1 - (Fin.rev i).val) := by
    intro i
    rw [Fin.val_rev, show n - 1 - (n - (i.val + 1)) = i.val from by have := i.isLt; omega]
  show ∑ i : Fin n, (if w (Fin.rev i) then 1 else 0) * 2 ^ i.val
    = ∑ i : Fin n, (if w i then 1 else 0) * 2 ^ (n - 1 - i.val)
  rw [Finset.sum_congr rfl (fun i _ => hpoint i)]
  exact Equiv.sum_comp (Fin.rev_involutive.toPerm Fin.rev)
    (fun j => (if w j then 1 else 0) * 2 ^ (n - 1 - j.val))

theorem localQFTPhaseNum_full (n : ℕ) (z x : Reg n) :
    localQFTPhaseNum n n z x
      = ∑ i : Fin n, (z i).toNat *
        (∑ j : Fin n, if i ≤ j then (x j).toNat * 2 ^ (n - 1 - j.val + i.val) else 0) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [if_pos i.isLt]

theorem regValue_mul_regValueLsb (n : ℕ) (x z : Reg n) :
    regValue n x * regValueLsb n z
      = localQFTPhaseNum n n z x + 2 ^ n *
        (∑ a : Fin n, ∑ c : Fin n, if a < c then
          (x a).toNat * (z c).toNat * 2 ^ (c.val - 1 - a.val) else 0) := by
  have hprod : regValue n x * regValueLsb n z
      = ∑ a : Fin n, ∑ c : Fin n, (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val) := by
    show (∑ a : Fin n, (if x a then 1 else 0) * 2 ^ (n - 1 - a.val)) *
        (∑ c : Fin n, (if z c then 1 else 0) * 2 ^ c.val) = _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    show (if x a then 1 else 0) * 2 ^ (n - 1 - a.val) *
        ((if z c then 1 else 0) * 2 ^ c.val)
      = (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val)
    cases hx : x a <;> cases hz : z c <;> simp [pow_add]
  have hsplit : ∀ a c : Fin n, (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val)
      = (if c ≤ a then (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val) else 0)
        + (if a < c then (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val) else 0) := by
    intro a c
    by_cases h : c ≤ a
    · rw [if_pos h, if_neg (by omega), add_zero]
    · rw [if_neg h, if_pos (by omega), zero_add]
  have hB : (∑ a : Fin n, ∑ c : Fin n, if c ≤ a then
      (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val) else 0)
      = localQFTPhaseNum n n z x := by
    rw [Finset.sum_comm, localQFTPhaseNum_full]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : c ≤ a
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h, mul_zero]
  have hG : (∑ a : Fin n, ∑ c : Fin n, if a < c then
      (x a).toNat * (z c).toNat * 2 ^ (n - 1 - a.val + c.val) else 0)
      = 2 ^ n * (∑ a : Fin n, ∑ c : Fin n, if a < c then
        (x a).toNat * (z c).toNat * 2 ^ (c.val - 1 - a.val) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : a < c
    · rw [if_pos h, mul_ite, if_pos h,
        show n - 1 - a.val + c.val = n + (c.val - 1 - a.val) from by omega, pow_add]
      ring
    · rw [if_neg h, mul_ite, if_neg h, mul_zero]
  rw [hprod, Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => hsplit a c)),
    Finset.sum_congr rfl (fun a _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    hB, hG]

theorem primRoot_pow_regValue_mul_lsb (n : ℕ) (x z : Reg n) :
    primRoot (2 ^ n) ^ (regValue n x * regValueLsb n z)
      = primRoot (2 ^ n) ^ localQFTPhaseNum n n z x := by
  rw [regValue_mul_regValueLsb, pow_add, pow_mul, primRoot_two_pow_pow_self, one_pow,
    mul_one]

theorem reg_rev_involutive (n : ℕ) :
    Function.Involutive (fun w : Reg n => fun i => w (Fin.rev i)) := by
  intro w
  funext i
  show w (Fin.rev (Fin.rev i)) = w i
  rw [Fin.rev_rev]

theorem localProgramMatrix_localQFT (n : ℕ) :
    localProgramMatrix (localQFT n) = relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) := by
  ext y x
  rw [localQFT, localProgramMatrix_append]
  show (localProgramMatrix (localQFTSwaps n) * localProgramMatrix (localQFTRows n n)) y x = _
  rw [localProgramMatrix_localQFTSwaps,
    permMatrix_mul_apply _ (reg_rev_involutive n) _ y x,
    localProgramMatrix_localQFTRows n n (le_refl n) _ x,
    if_pos (fun i hi => by have := i.isLt; omega)]
  show ((Real.sqrt 2 : ℂ)⁻¹) ^ n * primRoot (2 ^ n) ^ localQFTPhaseNum n n _ x = _
  rw [← primRoot_pow_regValue_mul_lsb n x (fun i => y (Fin.rev i)),
    regValueLsb_comp_rev n y]
  show ((Real.sqrt 2 : ℂ)⁻¹) ^ n * primRoot (2 ^ n) ^ (regValue n x * regValue n y) = _
  rw [← bitVecEquiv_val_eq_regValue n x, ← bitVecEquiv_val_eq_regValue n y]
  show ((Real.sqrt 2 : ℂ)⁻¹) ^ n * primRoot (2 ^ n) ^ ((bitVecEquiv n x).val * (bitVecEquiv n y).val)
    = relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) y x
  rw [relabelGate, Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply,
    qftMatrix_apply]
  show ((Real.sqrt 2 : ℂ)⁻¹) ^ n * primRoot (2 ^ n) ^ ((bitVecEquiv n x).val * (bitVecEquiv n y).val)
    = ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℂ))⁻¹ *
      primRoot (2 ^ n) ^ (((bitVecEquiv n y).val : ℤ) * ((bitVecEquiv n x).val : ℤ))
  rw [← Nat.cast_mul, zpow_natCast, mul_comm (bitVecEquiv n y).val (bitVecEquiv n x).val,
    inv_pow, ← Complex.ofReal_pow, sqrt_two_pow, Nat.cast_pow, Nat.cast_ofNat]

theorem localQFT_exact_positive_matrix (n : ℕ) :
    localProgramMatrix (localQFT n) = relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)) ∧
    localProgramMatrix (localProgramAdjoint (localQFT n)) =
      (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ := by
  obtain ⟨-, adj, -⟩ := localDyadicProgram_run_adjoint_cost n (localQFT n) (Ket (ZeroStr n))
  exact ⟨localProgramMatrix_localQFT n, by rw [adj, localProgramMatrix_localQFT n]⟩

def approxLocalQFT (n b : ℕ) : List (LocalQFTGate n) :=
  (localQFT n).filter fun g => match g with
    | .cp _ _ k _ => decide (k ≤ b + 2)
    | _ => true

noncomputable def localGridReadoutCircuit (n b : ℕ) : Circuit (Reg n) :=
  localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))

theorem countP_cpPmap_false (n a : ℕ) (ha : a < n) (p : LocalQFTGate n → Bool)
    (H : ∀ c ∈ List.range' (a + 1) (n - 1 - a), c < n)
    (hp : ∀ (c : ℕ) (hc : c < n), p (LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) = false) :
    ((List.range' (a + 1) (n - 1 - a)).pmap
        (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) H).countP p = 0 := by
  rw [List.pmap_eq_map_attach, List.countP_map,
    List.countP_eq_zero.mpr (fun x _ => by
      obtain ⟨c, hc⟩ := x
      show ¬ p (LocalQFTGate.cp ⟨a, ha⟩ ⟨c, _⟩ (c - a + 1) false)
      rw [hp c (by obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc; omega)]
      exact Bool.false_ne_true)]

theorem countP_cpPmap_true (n a : ℕ) (ha : a < n) (p : LocalQFTGate n → Bool)
    (H : ∀ c ∈ List.range' (a + 1) (n - 1 - a), c < n)
    (hp : ∀ (c : ℕ) (hc : c < n), p (LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) = true) :
    ((List.range' (a + 1) (n - 1 - a)).pmap
        (fun c hc => LocalQFTGate.cp ⟨a, ha⟩ ⟨c, hc⟩ (c - a + 1) false) H).countP p = n - 1 - a := by
  rw [List.pmap_eq_map_attach, List.countP_map,
    List.countP_eq_length.mpr (fun x _ => by
      obtain ⟨c, hc⟩ := x
      exact hp c (by obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc; omega)),
    List.length_attach, List.length_range']

theorem localQFTRows_class_counts (n : ℕ) :
    ∀ (r : ℕ) (_hr : r ≤ n),
    (localQFTRows n r).countP (fun g => match g with | .h _ => true | _ => false) = r ∧
    (localQFTRows n r).countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = ∑ a ∈ Finset.range r, (n - 1 - a) ∧
    (localQFTRows n r).countP (fun g => match g with | .swap _ _ => true | _ => false) = 0 := by
  intro r
  induction r with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ r ih =>
    intro hr
    have hrlt : r < n := by omega
    obtain ⟨ihH, ihCp, ihSwap⟩ := ih (by omega)
    have H : ∀ c ∈ List.range' (r + 1) (n - 1 - r), c < n := fun c hc => by
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc; omega
    have hrowH : (localQFTRow n r hrlt).countP (fun g => match g with
        | .h _ => true | _ => false) = 1 := by
      show (LocalQFTGate.h ⟨r, hrlt⟩ :: _).countP _ = 1
      rw [List.countP_cons, countP_cpPmap_false n r hrlt _ H (fun c _ => rfl)]
      simp
    have hrowCp : (localQFTRow n r hrlt).countP (fun g => match g with
        | .cp _ _ _ _ => true | _ => false) = n - 1 - r := by
      show (LocalQFTGate.h ⟨r, hrlt⟩ :: _).countP _ = n - 1 - r
      rw [List.countP_cons, countP_cpPmap_true n r hrlt _ H (fun c _ => rfl)]
      simp
    have hrowSwap : (localQFTRow n r hrlt).countP (fun g => match g with
        | .swap _ _ => true | _ => false) = 0 := by
      show (LocalQFTGate.h ⟨r, hrlt⟩ :: _).countP _ = 0
      rw [List.countP_cons, countP_cpPmap_false n r hrlt _ H (fun c _ => rfl)]
      simp
    rw [localQFTRows_succ n r hrlt]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.countP_append, hrowH, ihH]
    · rw [List.countP_append, hrowCp, ihCp, Finset.sum_range_succ]
    · rw [List.countP_append, hrowSwap, ihSwap]

theorem localQFTSwapPrefix_class_counts (n : ℕ) :
    ∀ (m : ℕ) (_hm : m ≤ n / 2),
    (localQFTSwapPrefix n m).countP (fun g => match g with | .h _ => true | _ => false) = 0 ∧
    (localQFTSwapPrefix n m).countP (fun g => match g with | .cp _ _ _ _ => true | _ => false) = 0 ∧
    (localQFTSwapPrefix n m).countP (fun g => match g with | .swap _ _ => true | _ => false) = m := by
  intro m
  induction m with
  | zero => intro _; exact ⟨rfl, rfl, rfl⟩
  | succ m ih =>
    intro hm
    have hmle : m ≤ n / 2 := by omega
    obtain ⟨ihH, ihCp, ihSwap⟩ := ih hmle
    rw [localQFTSwapPrefix_succ n m hm]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.countP_append, ihH, List.countP_cons, List.countP_nil]
      simp
    · rw [List.countP_append, ihCp, List.countP_cons, List.countP_nil]
      simp
    · rw [List.countP_append, ihSwap, List.countP_cons, List.countP_nil]
      simp

theorem localQFT_class_counts (n : ℕ) :
    (localQFT n).countP (fun g => match g with | .h _ => true | _ => false) = n ∧
    (localQFT n).countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = n * (n - 1) / 2 ∧
    (localQFT n).countP (fun g => match g with | .swap _ _ => true | _ => false) = n / 2 := by
  obtain ⟨hH, hCp, hSwap⟩ := localQFTRows_class_counts n n (le_refl n)
  obtain ⟨sH, sCp, sSwap⟩ := localQFTSwapPrefix_class_counts n (n / 2) (le_refl _)
  have hsum : (∑ a ∈ Finset.range n, (n - 1 - a)) = n * (n - 1) / 2 := by
    rw [Finset.sum_range_reflect (fun a => a) n, Finset.sum_range_id]
  show ((localQFTRows n n ++ localQFTSwaps n).countP _ = n) ∧
    ((localQFTRows n n ++ localQFTSwaps n).countP _ = n * (n - 1) / 2) ∧
    ((localQFTRows n n ++ localQFTSwaps n).countP _ = n / 2)
  rw [localQFTSwaps]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.countP_append, hH, sH]
    rfl
  · rw [List.countP_append, hCp, sCp, hsum]
    rfl
  · rw [List.countP_append, hSwap, sSwap, Nat.zero_add]

theorem length_eq_countP_add (l : List (LocalQFTGate n)) :
    l.length = l.countP (fun g => match g with | .h _ => true | _ => false)
      + l.countP (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      + l.countP (fun g => match g with | .swap _ _ => true | _ => false) := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    rw [List.length_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    cases g <;> simp <;> omega

theorem mem_localQFTRows_cp (n r : ℕ) (hr : r ≤ n) (a c : Fin n) (k : ℕ) (neg : Bool)
    (hg : LocalQFTGate.cp a c k neg ∈ localQFTRows n r) :
    a.val < c.val ∧ k = c.val - a.val + 1 ∧ neg = false := by
  induction r with
  | zero => exact absurd hg (by simp [localQFTRows_zero])
  | succ r ih =>
    have hrlt : r < n := by omega
    rw [localQFTRows_succ n r hrlt, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih (by omega) hg
    · rw [localQFTRow, List.mem_cons] at hg
      rcases hg with h | hg
      · nomatch h
      · rw [List.mem_pmap] at hg
        obtain ⟨c', hc', h⟩ := hg
        injection h with ha' hc2 hk hneg
        obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc'
        subst ha' hc2 hk hneg
        show r < r + 1 + 1 * i ∧ r + 1 + 1 * i - r + 1 = r + 1 + 1 * i - r + 1 ∧ false = false
        exact ⟨by omega, rfl, rfl⟩

theorem no_swap_mem_localQFTRows (n r : ℕ) (hr : r ≤ n) (a c : Fin n)
    (hg : LocalQFTGate.swap a c ∈ localQFTRows n r) : False := by
  induction r with
  | zero => exact absurd hg (by simp [localQFTRows_zero])
  | succ r ih =>
    have hrlt : r < n := by omega
    rw [localQFTRows_succ n r hrlt, List.mem_append] at hg
    rcases hg with hg | hg
    · exact ih (by omega) hg
    · rw [localQFTRow, List.mem_cons] at hg
      rcases hg with h | hg
      · nomatch h
      · rw [List.mem_pmap] at hg
        obtain ⟨c', hc', h⟩ := hg
        nomatch h

theorem mem_localQFTSwapPrefix_swap (n m : ℕ) (a c : Fin n)
    (hg : LocalQFTGate.swap a c ∈ localQFTSwapPrefix n m) :
    a.val < c.val ∧ a.val < n / 2 ∧ c.val = n - 1 - a.val := by
  induction m with
  | zero => exact absurd hg (by simp [localQFTSwapPrefix])
  | succ m ih =>
    by_cases hm : m + 1 ≤ n / 2
    · rw [localQFTSwapPrefix_succ n m hm, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | h
      · exact ih hg
      · injection h with ha' hc'
        subst ha' hc'
        show m < n - 1 - m ∧ m < n / 2 ∧ n - 1 - m = n - 1 - m
        exact ⟨by omega, by omega, rfl⟩
    · rw [show localQFTSwapPrefix n (m + 1) = (if h : m + 1 ≤ n / 2 then
          localQFTSwapPrefix n m ++ [LocalQFTGate.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩]
        else []) from rfl, dif_neg hm] at hg
      exact absurd hg (by simp)

theorem no_cp_mem_localQFTSwapPrefix (n m : ℕ) (a c : Fin n) (k : ℕ) (neg : Bool)
    (hg : LocalQFTGate.cp a c k neg ∈ localQFTSwapPrefix n m) : False := by
  induction m with
  | zero => exact absurd hg (by simp [localQFTSwapPrefix])
  | succ m ih =>
    by_cases hm : m + 1 ≤ n / 2
    · rw [localQFTSwapPrefix_succ n m hm, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | h
      · exact ih hg
      · nomatch h
    · rw [show localQFTSwapPrefix n (m + 1) = (if h : m + 1 ≤ n / 2 then
          localQFTSwapPrefix n m ++ [LocalQFTGate.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩]
        else []) from rfl, dif_neg hm] at hg
      exact absurd hg (by simp)

theorem mem_localQFT_cp (n : ℕ) (a c : Fin n) (k : ℕ) (neg : Bool)
    (hg : LocalQFTGate.cp a c k neg ∈ localQFT n) :
    a.val < c.val ∧ k = c.val - a.val + 1 ∧ neg = false := by
  rw [localQFT, List.mem_append] at hg
  rcases hg with hg | hg
  · exact mem_localQFTRows_cp n n (le_refl n) a c k neg hg
  · exact absurd hg (no_cp_mem_localQFTSwapPrefix n (n / 2) a c k neg)

theorem mem_localQFT_swap (n : ℕ) (a c : Fin n)
    (hg : LocalQFTGate.swap a c ∈ localQFT n) :
    a.val < c.val ∧ a.val < n / 2 ∧ c.val = n - 1 - a.val := by
  rw [localQFT, List.mem_append] at hg
  rcases hg with hg | hg
  · exact absurd hg (no_swap_mem_localQFTRows n n (le_refl n) a c)
  · exact mem_localQFTSwapPrefix_swap n (n / 2) a c hg

theorem localQFT_exact_gate_counts_and_wires (n : ℕ) :
    ((localQFT n).filter (fun g => match g with | .h _ => true | _ => false)).length = n ∧
    ((localQFT n).filter (fun g => match g with | .cp _ _ _ _ => true | _ => false)).length
      = n * (n - 1) / 2 ∧
    ((localQFT n).filter (fun g => match g with | .swap _ _ => true | _ => false)).length = n / 2 ∧
    GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
    QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
    (∀ g ∈ localQFT n, match g with
      | .h _ => True
      | .cp a c k neg => a.val < c.val ∧ k = c.val - a.val + 1 ∧ neg = false
      | .swap a c => a.val < c.val ∧ a.val < n / 2 ∧ c.val = n - 1 - a.val) := by
  obtain ⟨hH, hCp, hSwap⟩ := localQFT_class_counts n
  obtain ⟨-, -, -, -, -, qc, gc, -, -⟩ :=
    localDyadicProgram_run_adjoint_cost n (localQFT n) (Ket (ZeroStr n))
  have hlen : (localQFT n).length = n + n * (n - 1) / 2 + n / 2 := by
    rw [length_eq_countP_add, hH, hCp, hSwap]
  rw [List.countP_eq_length_filter] at hH hCp hSwap
  refine ⟨hH, hCp, hSwap, by rw [gc, hlen], qc, fun g hg => ?_⟩
  cases g with
  | h a => trivial
  | cp a c k neg => exact mem_localQFT_cp n a c k neg hg
  | swap a c => exact mem_localQFT_swap n a c hg

theorem countP_range'_sub_le (l : ℕ) (s r b : ℕ) :
    (List.range' s l).countP (fun c => decide (c - r + 1 ≤ b + 2))
      = min l (r + b + 2 - s) := by
  induction l generalizing s with
  | zero => simp
  | succ l ih =>
    show (List.countP _ (s :: List.range' (s + 1) l)) = min (l + 1) (r + b + 2 - s)
    rw [List.countP_cons, ih (s + 1)]
    by_cases h : s - r + 1 ≤ b + 2
    · rw [if_pos ((decide_eq_true_iff).mpr h)]
      omega
    · rw [if_neg (fun hd => absurd ((decide_eq_true_iff).mp hd) h)]
      omega

theorem countP_keep_cpPmap (n r b : ℕ) (hr : r < n) :
    ∀ (s l : ℕ) (_hl : s + l ≤ n) (H : ∀ c ∈ List.range' s l, c < n),
    ((List.range' s l).pmap
        (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H).countP
      (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)
      = min l (r + b + 2 - s) := by
  intro s l
  induction l generalizing s with
  | zero => intro _ _; simp
  | succ l ih =>
    intro hl H
    have Hs : s < n := H s List.mem_cons_self
    have Hrest : ∀ c ∈ List.range' (s + 1) l, c < n :=
      fun c hc => H c (List.mem_cons_of_mem s hc)
    show ((s :: List.range' (s + 1) l).pmap
        (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H).countP _
      = min (l + 1) (r + b + 2 - s)
    rw [show ((s :: List.range' (s + 1) l).pmap
          (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H)
        = LocalQFTGate.cp ⟨r, hr⟩ ⟨s, Hs⟩ (s - r + 1) false ::
          (List.range' (s + 1) l).pmap
            (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) Hrest from rfl,
      List.countP_cons, ih (s + 1) (by omega) Hrest]
    by_cases h : s - r + 1 ≤ b + 2
    · rw [if_pos ((decide_eq_true_iff).mpr h)]
      omega
    · rw [if_neg (fun hd => absurd ((decide_eq_true_iff).mp hd) h)]
      omega

theorem countP_isCp_filter_keep_cpPmap (n r b : ℕ) (hr : r < n)
    (H : ∀ c ∈ List.range' (r + 1) (n - 1 - r), c < n) :
    (((List.range' (r + 1) (n - 1 - r)).pmap
        (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H).filter
      (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)).countP
      (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = min (n - 1 - r) (b + 1) := by
  have h1 : (((List.range' (r + 1) (n - 1 - r)).pmap
        (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H).filter
      (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)).countP
      (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = (((List.range' (r + 1) (n - 1 - r)).pmap
        (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H).filter
        (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)).length := by
    apply List.countP_eq_length.mpr
    intro g hg
    rw [List.mem_filter] at hg
    rw [List.mem_pmap] at hg
    obtain ⟨c, hc, rfl⟩ := hg.1
    rfl
  rw [h1, ← List.countP_eq_length_filter,
    countP_keep_cpPmap n r b hr (r + 1) (n - 1 - r) (by omega) H,
    show r + b + 2 - (r + 1) = b + 1 from by omega]

theorem countP_keep_localQFTRow (n r b : ℕ) (hr : r < n) :
    (localQFTRow n r hr).countP (fun g => match g with
        | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)
      = 1 + min (n - 1 - r) (b + 1) := by
  have H : ∀ c ∈ List.range' (r + 1) (n - 1 - r), c < n := fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc; omega
  show (LocalQFTGate.h ⟨r, hr⟩ :: _).countP _ = 1 + min (n - 1 - r) (b + 1)
  rw [List.countP_cons, countP_keep_cpPmap n r b hr (r + 1) (n - 1 - r) (by omega) H,
    show r + b + 2 - (r + 1) = b + 1 from by omega]
  show min (n - 1 - r) (b + 1) + 1 = 1 + min (n - 1 - r) (b + 1)
  omega

theorem countP_isCp_filter_keep_localQFTRow (n r b : ℕ) (hr : r < n) :
    ((localQFTRow n r hr).filter (fun g => match g with
        | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)).countP
      (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = min (n - 1 - r) (b + 1) := by
  have H : ∀ c ∈ List.range' (r + 1) (n - 1 - r), c < n := fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc; omega
  show (List.countP _ ((LocalQFTGate.h ⟨r, hr⟩ :: _).filter _)) = min (n - 1 - r) (b + 1)
  rw [List.filter_cons]
  show (List.countP _ (LocalQFTGate.h ⟨r, hr⟩ :: _)) = min (n - 1 - r) (b + 1)
  rw [List.countP_cons, countP_isCp_filter_keep_cpPmap n r b hr H]
  show min (n - 1 - r) (b + 1) + 0 = min (n - 1 - r) (b + 1)
  omega

theorem countP_keep_localQFTRows (n b : ℕ) :
    ∀ (r : ℕ) (_hr : r ≤ n),
    (localQFTRows n r).countP (fun g => match g with
        | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)
      = r + ∑ a ∈ Finset.range r, min (n - 1 - a) (b + 1) := by
  intro r
  induction r with
  | zero =>
    intro _
    show (List.countP _ ([] : List (LocalQFTGate n)))
      = 0 + ∑ a ∈ Finset.range 0, min (n - 1 - a) (b + 1)
    simp
  | succ r ih =>
    intro hr
    have hrlt : r < n := by omega
    rw [localQFTRows_succ n r hrlt, List.countP_append, countP_keep_localQFTRow n r b hrlt,
      ih (by omega), Finset.sum_range_succ]
    ring

theorem countP_isCp_filter_keep_localQFTRows (n b : ℕ) :
    ∀ (r : ℕ) (_hr : r ≤ n),
    ((localQFTRows n r).filter (fun g => match g with
        | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)).countP
      (fun g => match g with | .cp _ _ _ _ => true | _ => false)
      = ∑ a ∈ Finset.range r, min (n - 1 - a) (b + 1) := by
  intro r
  induction r with
  | zero =>
    intro _
    show (List.countP _ (([] : List (LocalQFTGate n)).filter _))
      = ∑ a ∈ Finset.range 0, min (n - 1 - a) (b + 1)
    simp
  | succ r ih =>
    intro hr
    have hrlt : r < n := by omega
    rw [localQFTRows_succ n r hrlt, List.filter_append, List.countP_append,
      countP_isCp_filter_keep_localQFTRow n r b hrlt, ih (by omega), Finset.sum_range_succ]

theorem localQFTSwapPrefix_length (n m : ℕ) (hm : m ≤ n / 2) :
    (localQFTSwapPrefix n m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [localQFTSwapPrefix_succ n m hm, List.length_append, List.length_singleton,
      ih (by omega)]

theorem keep_mem_localQFTSwapPrefix (n m b : ℕ) (g : LocalQFTGate n)
    (hg : g ∈ localQFTSwapPrefix n m) :
    (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) g = true := by
  cases g with
  | h a => rfl
  | cp a c k neg => exact absurd hg (no_cp_mem_localQFTSwapPrefix n m a c k neg)
  | swap a c => rfl

theorem approxLocalQFT_actual_filter_and_cost (n b : ℕ) :
    approxLocalQFT n b = (localQFT n).filter (fun g => match g with
      | .cp _ _ k _ => decide (k ≤ b + 2)
      | _ => true) ∧
    ((approxLocalQFT n b).filter (fun g => match g with | .cp _ _ _ _ => true | _ => false)).length =
      ∑ i ∈ Finset.range n, min (n - 1 - i) (b + 1) ∧
    GateCount (localProgramCircuit (approxLocalQFT n b)) =
      n + (∑ i ∈ Finset.range n, min (n - 1 - i) (b + 1)) + n / 2 ∧
    GateCount (localProgramCircuit (approxLocalQFT n b)) ≤ n + n * (b + 1) + n / 2 ∧
    (n ≤ b + 2 → approxLocalQFT n b = localQFT n) := by
  obtain ⟨-, -, -, -, -, qc, gc, -, -⟩ :=
    localDyadicProgram_run_adjoint_cost n (approxLocalQFT n b) (Ket (ZeroStr n))
  have hswapkeep : (localQFTSwaps n).filter (fun g => match g with
        | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true)
      = localQFTSwaps n :=
    List.filter_eq_self.mpr (keep_mem_localQFTSwapPrefix n (n / 2) b)
  have hswapCp : ((localQFTSwaps n).filter (fun g => match g with
        | .cp _ _ _ _ => true | _ => false)).length = 0 := by
    rw [← List.countP_eq_length_filter]
    exact (localQFTSwapPrefix_class_counts n (n / 2) (le_refl _)).2.1
  have hswaplen : (localQFTSwaps n).length = n / 2 :=
    localQFTSwapPrefix_length n (n / 2) (le_refl _)
  have happrox : approxLocalQFT n b = (localQFTRows n n).filter (fun g => match g with
        | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) ++ localQFTSwaps n := by
    show (localQFT n).filter _ = _
    rw [localQFT, List.filter_append, hswapkeep]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show ((approxLocalQFT n b).filter _).length = _
    rw [happrox, List.filter_append, List.length_append, ← List.countP_eq_length_filter,
      countP_isCp_filter_keep_localQFTRows n b n (le_refl n), hswapCp, Nat.add_zero]
  · show GateCount (localProgramCircuit (approxLocalQFT n b)) = _
    rw [gc, happrox, List.length_append, ← List.countP_eq_length_filter,
      countP_keep_localQFTRows n b n (le_refl n), hswaplen]
  · show GateCount (localProgramCircuit (approxLocalQFT n b)) ≤ n + n * (b + 1) + n / 2
    rw [gc, happrox, List.length_append, ← List.countP_eq_length_filter,
      countP_keep_localQFTRows n b n (le_refl n), hswaplen]
    have hle : (∑ i ∈ Finset.range n, min (n - 1 - i) (b + 1)) ≤ n * (b + 1) := by
      rw [show n * (b + 1) = ∑ i ∈ Finset.range n, (b + 1) from by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id]]
      exact Finset.sum_le_sum fun i _ => min_le_right _ _
    omega
  · intro hn
    show (localQFT n).filter _ = localQFT n
    rw [List.filter_eq_self]
    intro g hg
    cases g with
    | h a => rfl
    | cp a c k neg =>
      obtain ⟨hac, hk, -⟩ := mem_localQFT_cp n a c k neg hg
      show decide (k ≤ b + 2) = true
      rw [decide_eq_true_iff, hk]
      have := c.isLt
      omega
    | swap a c => rfl

theorem l2_opNorm_of_mem_unitaryGroup (U : Matrix (Reg n) (Reg n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) : ‖U‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h0
  have h2 := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [h1] at h2
  have h3 : ‖(1 : Matrix (Reg n) (Reg n) ℂ)‖ = 1 := norm_one
  rw [h3] at h2
  have h4 : 0 ≤ ‖U‖ := norm_nonneg _
  have h5 : ‖U‖ ^ 2 = 1 := by
    rw [pow_two]
    exact h2.symm
  rcases sq_eq_one_iff.mp h5 with h | h
  · exact h
  · linarith

theorem localDyadicPhase_omission_operator_error (n : ℕ) (a c : Fin n) (k : ℕ) (neg : Bool) :
    ‖localGateMatrix (.cp a c k neg) - (1 : Matrix (Reg n) (Reg n) ℂ)‖ ≤
      2 * Real.pi / (2 ^ k : ℝ) := by
  have hdiag : localGateMatrix (.cp a c k neg) - (1 : Matrix (Reg n) (Reg n) ℂ)
      = Matrix.diagonal (fun x : Reg n =>
        if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) - 1 else 0) := by
    show Matrix.diagonal _ - 1 = Matrix.diagonal _
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext x
    show (if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) else 1) - 1
      = if x a && x c then Complex.exp (dyadicPhaseAngle k neg * Complex.I) - 1 else 0
    by_cases h : x a && x c
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, sub_self]
  rw [hdiag, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg (by positivity)]
  intro x
  by_cases h : x a && x c
  · rw [if_pos h,
      show (↑(dyadicPhaseAngle k neg) : ℂ) * Complex.I
        = Complex.I * ↑(dyadicPhaseAngle k neg) from mul_comm _ _,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    have hθ : |dyadicPhaseAngle k neg| = 2 * Real.pi / (2 ^ k : ℝ) := by
      cases neg
      · show |dyadicPhaseAngle k false| = _
        rw [show dyadicPhaseAngle k false = 2 * Real.pi / (2 ^ k : ℝ) from rfl,
          abs_of_nonneg (by positivity)]
      · show |dyadicPhaseAngle k true| = _
        rw [show dyadicPhaseAngle k true = -(2 * Real.pi / (2 ^ k : ℝ)) from rfl, abs_neg,
          abs_of_nonneg (by positivity)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc 2 * |Real.sin (dyadicPhaseAngle k neg / 2)|
        ≤ 2 * |dyadicPhaseAngle k neg / 2| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
      _ = |dyadicPhaseAngle k neg| := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp
      _ = 2 * Real.pi / (2 ^ k : ℝ) := hθ
  · rw [if_neg h, norm_zero]
    positivity

theorem prod_filter_reverse (P : LocalQFTGate n → Bool) (gs : List (LocalQFTGate n)) :
    ((gs.filter P).reverse.map localGateMatrix).prod
      = (gs.reverse.map fun g => if P g then localGateMatrix g else 1).prod := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    by_cases hg : P g
    · rw [List.filter_cons_of_pos hg, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, ih,
        List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, if_pos hg]
    · rw [List.filter_cons_of_neg hg, ih, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one, if_neg hg,
        mul_one]

theorem sum_range'_omitted_phase_le (l : ℕ) (s r b : ℕ) :
    ((List.range' s l).map fun c =>
        if decide (c - r + 1 ≤ b + 2) then (0 : ℝ) else 2 * Real.pi / 2 ^ (c - r + 1)).sum
      ≤ 2 * Real.pi / 2 ^ (max (s - r + 1) (b + 3) - 1) := by
  induction l generalizing s with
  | zero =>
    simp only [List.range'_zero, List.map_nil, List.sum_nil]
    positivity
  | succ l ih =>
    rw [show List.range' s (l + 1) = s :: List.range' (s + 1) l from rfl, List.map_cons,
      List.sum_cons]
    by_cases h : s - r + 1 ≤ b + 2
    · rw [if_pos ((decide_eq_true_iff).mpr h)]
      have hmax : max (s - r + 1) (b + 3) = b + 3 := by omega
      have hmax' : max (s + 1 - r + 1) (b + 3) = b + 3 := by omega
      rw [hmax, show b + 3 - 1 = b + 2 from by omega]
      have hiht := ih (s + 1)
      rw [hmax', show b + 3 - 1 = b + 2 from by omega] at hiht
      linarith [hiht]
    · rw [if_neg (fun hd => absurd ((decide_eq_true_iff).mp hd) h)]
      have hmax : max (s - r + 1) (b + 3) = s - r + 1 := by omega
      have hmax' : max (s + 1 - r + 1) (b + 3) = s + 1 - r + 1 := by omega
      have hiht := ih (s + 1)
      rw [hmax', show s + 1 - r + 1 - 1 = s - r + 1 from by omega] at hiht
      rw [hmax, show s - r + 1 - 1 = s - r from by omega]
      have hhalf : 2 * Real.pi / (2:ℝ) ^ (s - r)
          = 2 * Real.pi / 2 ^ (s - r + 1) + 2 * Real.pi / 2 ^ (s - r + 1) := by
        rw [show (2:ℝ) ^ (s - r + 1) = 2 ^ (s - r) * 2 from pow_succ _ _]
        field_simp
        ring
      rw [hhalf]
      linarith [hiht]

theorem gate_error_le (n b : ℕ) (a c : Fin n) (k : ℕ) :
    ‖localGateMatrix (.cp a c k false) -
      (if decide (k ≤ b + 2) then localGateMatrix (.cp a c k false) else 1)‖
      ≤ if decide (k ≤ b + 2) then (0 : ℝ) else 2 * Real.pi / 2 ^ k := by
  by_cases h : k ≤ b + 2
  · rw [if_pos ((decide_eq_true_iff).mpr h), if_pos ((decide_eq_true_iff).mpr h), sub_self,
      norm_zero]
  · rw [if_neg (fun hd => absurd ((decide_eq_true_iff).mp hd) h),
      if_neg (fun hd => absurd ((decide_eq_true_iff).mp hd) h)]
    exact localDyadicPhase_omission_operator_error n a c k false

theorem sum_gate_errors_cpPmap_le (n r b : ℕ) (hr : r < n) :
    ∀ (s l : ℕ) (_hl : s + l ≤ n) (H : ∀ c ∈ List.range' s l, c < n),
    (((List.range' s l).pmap (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H).map
        fun g => ‖localGateMatrix g -
          (if (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) g
            then localGateMatrix g else 1)‖).sum
      ≤ ((List.range' s l).map fun c =>
        if decide (c - r + 1 ≤ b + 2) then (0 : ℝ) else 2 * Real.pi / 2 ^ (c - r + 1)).sum := by
  intro s l
  induction l generalizing s with
  | zero => intro _ _; simp
  | succ l ih =>
    intro hl H
    have Hs : s < n := H s List.mem_cons_self
    have Hrest : ∀ c ∈ List.range' (s + 1) l, c < n :=
      fun c hc => H c (List.mem_cons_of_mem s hc)
    show (((s :: List.range' (s + 1) l).pmap
        (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H |>.map _).sum) ≤ _
    rw [show ((s :: List.range' (s + 1) l).pmap
          (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) H)
        = LocalQFTGate.cp ⟨r, hr⟩ ⟨s, Hs⟩ (s - r + 1) false ::
          (List.range' (s + 1) l).pmap
            (fun c hc => LocalQFTGate.cp ⟨r, hr⟩ ⟨c, hc⟩ (c - r + 1) false) Hrest from rfl,
      List.map_cons, List.sum_cons,
      show ((List.range' s (l + 1)).map fun c =>
          if decide (c - r + 1 ≤ b + 2) then (0 : ℝ) else 2 * Real.pi / 2 ^ (c - r + 1))
        = (if decide (s - r + 1 ≤ b + 2) then (0 : ℝ) else 2 * Real.pi / 2 ^ (s - r + 1)) ::
          ((List.range' (s + 1) l).map fun c =>
            if decide (c - r + 1 ≤ b + 2) then (0 : ℝ) else 2 * Real.pi / 2 ^ (c - r + 1))
      from rfl, List.sum_cons]
    have hhead := gate_error_le n b ⟨r, hr⟩ ⟨s, Hs⟩ (s - r + 1)
    have htail := ih (s + 1) (by omega) Hrest
    linarith

theorem sum_gate_errors_row_le (n r b : ℕ) (hr : r < n) :
    ((localQFTRow n r hr).map fun g =>
        ‖localGateMatrix g - (if (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) g
          then localGateMatrix g else 1)‖).sum
      ≤ Real.pi / 2 ^ (b + 1) := by
  have H : ∀ c ∈ List.range' (r + 1) (n - 1 - r), c < n := fun c hc => by
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hc; omega
  have hh : ‖localGateMatrix (LocalQFTGate.h ⟨r, hr⟩) -
      (if (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) (LocalQFTGate.h ⟨r, hr⟩)
        then localGateMatrix (LocalQFTGate.h ⟨r, hr⟩) else 1)‖ = 0 := by
    show ‖localGateMatrix (LocalQFTGate.h ⟨r, hr⟩) - localGateMatrix (LocalQFTGate.h ⟨r, hr⟩)‖ = 0
    rw [sub_self, norm_zero]
  show ((LocalQFTGate.h ⟨r, hr⟩ :: _).map _).sum ≤ Real.pi / 2 ^ (b + 1)
  rw [List.map_cons, List.sum_cons, hh, zero_add]
  have hgeom := sum_gate_errors_cpPmap_le n r b hr (r + 1) (n - 1 - r) (by omega) H
  have htail := sum_range'_omitted_phase_le (n - 1 - r) (r + 1) r b
  have hmax : max (r + 1 - r + 1) (b + 3) = b + 3 := by omega
  have hhalf : 2 * Real.pi / (2:ℝ) ^ (b + 2) = Real.pi / 2 ^ (b + 1) := by
    rw [show (2:ℝ) ^ (b + 2) = 2 ^ (b + 1) * 2 from pow_succ _ _]
    field_simp
  rw [hmax, show b + 3 - 1 = b + 2 from by omega, hhalf] at htail
  exact hgeom.trans htail

theorem sum_gate_errors_rows_le (n b : ℕ) :
    ∀ (r : ℕ) (_hr : r ≤ n),
    ((localQFTRows n r).map fun g =>
        ‖localGateMatrix g - (if (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) g
          then localGateMatrix g else 1)‖).sum
      ≤ (r : ℝ) * Real.pi / 2 ^ (b + 1) := by
  intro r
  induction r with
  | zero =>
    intro _
    simp [localQFTRows_zero]
  | succ r ih =>
    intro hr
    have hrlt : r < n := by omega
    rw [localQFTRows_succ n r hrlt, List.map_append, List.sum_append]
    have hrow := sum_gate_errors_row_le n r b hrlt
    have hiht := ih (by omega)
    have hcast : ((r + 1 : ℕ) : ℝ) * Real.pi / 2 ^ (b + 1)
      = (r : ℝ) * Real.pi / 2 ^ (b + 1) + Real.pi / 2 ^ (b + 1) := by
      push_cast
      ring
    rw [hcast]
    exact add_le_add hiht hrow

theorem sum_gate_errors_swaps (n m b : ℕ) :
    ((localQFTSwapPrefix n m).map fun g =>
        ‖localGateMatrix g - (if (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) g
          then localGateMatrix g else 1)‖).sum
      = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    by_cases hm : m + 1 ≤ n / 2
    · have hmn' : m < n := by omega
      have hnm' : n - 1 - m < n := by omega
      rw [localQFTSwapPrefix_succ n m hm, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, ih]
      show 0 + (‖localGateMatrix (LocalQFTGate.swap ⟨m, hmn'⟩ ⟨n - 1 - m, hnm'⟩) -
          localGateMatrix (LocalQFTGate.swap ⟨m, hmn'⟩ ⟨n - 1 - m, hnm'⟩)‖ + 0) = 0
      rw [sub_self, norm_zero, zero_add, add_zero]
    · rw [show localQFTSwapPrefix n (m + 1) = (if h : m + 1 ≤ n / 2 then
          localQFTSwapPrefix n m ++ [LocalQFTGate.swap ⟨m, by omega⟩ ⟨n - 1 - m, by omega⟩]
        else []) from rfl, dif_neg hm]
      rfl

theorem sum_gate_errors_le (n b : ℕ) :
    ((localQFT n).map fun g =>
        ‖localGateMatrix g - (if (fun g => match g with | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true) g
          then localGateMatrix g else 1)‖).sum
      ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) := by
  show (((localQFTRows n n ++ localQFTSwapPrefix n (n / 2)).map _).sum) ≤ _
  rw [List.map_append, List.sum_append, sum_gate_errors_swaps]
  have hrows := sum_gate_errors_rows_le n b n (le_refl n)
  rw [add_zero, show Real.pi * (n : ℝ) / 2 ^ (b + 1)
      = (n : ℝ) * Real.pi / 2 ^ (b + 1) from by ring]
  exact hrows

theorem approxLocalQFT_operator_error_forward (n b : ℕ) :
    ‖localProgramMatrix (approxLocalQFT n b) - localProgramMatrix (localQFT n)‖
      ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) := by
  set P : LocalQFTGate n → Bool := fun g => match g with
    | .cp _ _ k _ => decide (k ≤ b + 2) | _ => true
  have happrox : approxLocalQFT n b = (localQFT n).filter P := rfl
  have hpair := l2_norm_list_prod_sub_prod_le
    ((localQFT n).reverse.map fun g =>
      (localGateMatrix g, if P g then localGateMatrix g else 1))
    (fun p hp => by
      rw [List.mem_map] at hp
      obtain ⟨g, -, rfl⟩ := hp
      show ‖localGateMatrix g‖ ≤ 1 ∧ ‖if P g then localGateMatrix g else 1‖ ≤ 1
      rw [l2_opNorm_of_mem_unitaryGroup _ (localGateMatrix_unitary g)]
      refine ⟨le_refl 1, ?_⟩
      by_cases hg : P g
      · rw [if_pos hg, l2_opNorm_of_mem_unitaryGroup _ (localGateMatrix_unitary g)]
      · rw [if_neg hg]
        exact norm_one.le)
  have hfst : ((List.map Prod.fst ((localQFT n).reverse.map fun g =>
        (localGateMatrix g, if P g then localGateMatrix g else 1))).prod)
      = localProgramMatrix (localQFT n) := by
    rw [List.map_map,
      show (Prod.fst ∘ (fun g => (localGateMatrix g, if P g then localGateMatrix g else 1)))
        = localGateMatrix from rfl,
      localProgramMatrix_eq_reverse_prod]
  have hsnd : ((List.map Prod.snd ((localQFT n).reverse.map fun g =>
        (localGateMatrix g, if P g then localGateMatrix g else 1))).prod)
      = localProgramMatrix (approxLocalQFT n b) := by
    rw [List.map_map,
      show (Prod.snd ∘ (fun g => (localGateMatrix g, if P g then localGateMatrix g else 1)))
        = (fun g => if P g then localGateMatrix g else 1) from rfl,
      ← prod_filter_reverse P (localQFT n), ← localProgramMatrix_eq_reverse_prod, happrox]
  rw [hfst, hsnd, norm_sub_rev] at hpair
  refine hpair.trans ?_
  show ((List.map (fun p => ‖p.1 - p.2‖) ((localQFT n).reverse.map fun g =>
      (localGateMatrix g, if P g then localGateMatrix g else 1))).sum)
    ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1)
  rw [List.map_map,
    show ((fun p => ‖p.1 - p.2‖) ∘ (fun g =>
        (localGateMatrix g, if P g then localGateMatrix g else 1)))
      = (fun g => ‖localGateMatrix g - (if P g then localGateMatrix g else 1)‖) from rfl,
    List.map_reverse, List.sum_reverse]
  exact sum_gate_errors_le n b

theorem approxLocalQFT_operator_error (n b : ℕ) :
    ‖localProgramMatrix (approxLocalQFT n b) - relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))‖ ≤
      Real.pi * (n : ℝ) / (2 ^ (b + 1) : ℝ) ∧
    ‖localProgramMatrix (localProgramAdjoint (approxLocalQFT n b)) -
        (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ‖ ≤
      Real.pi * (n : ℝ) / (2 ^ (b + 1) : ℝ) := by
  have hfwd := approxLocalQFT_operator_error_forward n b
  rw [localProgramMatrix_localQFT n] at hfwd
  obtain ⟨-, adj, -⟩ := localDyadicProgram_run_adjoint_cost n (approxLocalQFT n b) (Ket (ZeroStr n))
  have hadj : localProgramMatrix (localProgramAdjoint (approxLocalQFT n b)) -
        (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ
      = (localProgramMatrix (approxLocalQFT n b) -
        relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ := by
    rw [adj, ← localProgramMatrix_localQFT n, Matrix.conjTranspose_sub]
  refine ⟨hfwd, ?_⟩
  rw [hadj, Matrix.l2_opNorm_conjTranspose]
  exact hfwd

end Qatlib.Concepts.QftPreparation.LocalQFTImplementation
