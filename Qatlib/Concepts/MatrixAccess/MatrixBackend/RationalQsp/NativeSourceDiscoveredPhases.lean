/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourcePhaseStructure
import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceFirstDeflation
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

/-! Original-input, accepted-certificate nonconstant source packet: DiscoveredPhases.
Value and physical-word guarantees here do not certify a root proposer, Python interpreter or total costs. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section IdealDiscovered

open scoped Matrix.Norms.L2Operator

/-- Construction for source Ideal Discovered in the native source discovered phases model. -/
def sourceIdealDiscovered : {d : ℕ} → (Fin (d+1) → Matrix Bool Bool ℂ) → List ℂ
  | 0,_ => []
  | m+1,G => (2*sourceComplexGramNormalize (G (Fin.last (m+1))) false true)::sourceIdealDiscovered (sourceIdealDeflationStep G)

/-- The same emitted instruction list satisfies `sourceIdealDiscovered_length` with the displayed gate and query accounting. -/
theorem sourceIdealDiscovered_length {d : ℕ} (G : Fin (d+1) → Matrix Bool Bool ℂ) :
    (sourceIdealDiscovered G).length=d := by
  induction d with
  | zero => rfl
  | succ m ih => simp only [sourceIdealDiscovered,List.length_cons,ih]

/-- The finite construction in `NativeSourceDiscoveredPhases` satisfies `sourceIdealDiscovered_unit` under the displayed hypotheses. -/
theorem sourceIdealDiscovered_unit {d : ℕ} (G : Fin (d+1) → Matrix Bool Bool ℂ)
    (h : ℝ) (hh : 0<h) (hinv : SourceIdealDeflationInvariant G h)
    (hfixed : ∀ j,sourceConjugateSwap (G j)=G j) :
    ∀ z∈sourceIdealDiscovered G,‖z‖=1 := by
  induction d with
  | zero => simp only [sourceIdealDiscovered,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | succ m ih =>
    have hl : G 0≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.1)
    have hr : G (Fin.last (m+1))≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.2)
    obtain ⟨_,_,_,hPP,_,_,_,_,_⟩ := sourceIdealDeflation_endpoints G hinv.1 hl hr
    intro z hz
    simp only [sourceIdealDiscovered,List.mem_cons] at hz
    rcases hz with hz|hz
    · subst z
      exact sourceIdealDiscoveredPhase_norm _ hr (hfixed _) hPP
    · exact ih (sourceIdealDeflationStep G) (sourceIdealDeflation_invariant G h hh hinv) (sourceIdealDeflation_fixed G hfixed) z hz

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput

/-- The finite construction in `NativeSourceDiscoveredPhases` satisfies `source_ideal_discovered_unit` under the displayed hypotheses. -/
theorem source_ideal_discovered_unit (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1) :
    ∀ z∈sourceIdealDiscovered (sourceIdealMatrixArray cs N E),‖z‖=1 := by
  let h := sourceGrid N (sourceInputU cs N E)
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hinv : SourceIdealDeflationInvariant (sourceIdealMatrixArray cs N E) (h : ℝ) :=
    ⟨sourceIdealArray_circle_unitary cs N E hE htail hparity hd hnorm,
      source_ideal_extreme_lower cs N E hd 0 (Or.inl rfl),
      source_ideal_extreme_lower cs N E hd _ (Or.inr rfl)⟩
  exact sourceIdealDiscovered_unit _ (h : ℝ) hh hinv (sourceIdealArray_fixed cs N E)

end IdealDiscovered

section DiscoveredError

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- Construction for source Discovered in the native source discovered phases model. -/
def sourceDiscovered : {d : ℕ} → (Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) → ℚ → List ℂ
  | 0,_,_ => []
  | m+1,F,eta => (2*sourceDecodeCompletionMatrix (sourceGramNormalize (F (Fin.last (m+1))) eta) false true)::
      sourceDiscovered (sourceDeflationStep F eta) eta

/-- The same emitted instruction list satisfies `sourceDiscovered_length` with the displayed gate and query accounting. -/
theorem sourceDiscovered_length {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) :
    (sourceDiscovered F eta).length=d := by
  induction d with
  | zero => rfl
  | succ m ih => simp only [sourceDiscovered,List.length_cons,ih]

/-- The estimate `raw_phase_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem raw_phase_error (C : Matrix Bool Bool (ℚ×ℚ)) (B : Matrix Bool Bool ℂ)
    (eta : ℚ) (heta : 0<eta) (delta h : ℝ) (hh : 0<h)
    (he : ‖sourceDecodeCompletionMatrix C-B‖≤delta) (hcap : delta≤h/4)
    (hlower : h≤‖B‖) (hrank : (B.conjTranspose*B).trace.re=‖B‖^2) :
    ‖2*sourceDecodeCompletionMatrix (sourceGramNormalize C eta) false true-2*sourceComplexGramNormalize B false true‖≤
      24*delta/h+2*(eta : ℝ) := by
  have hd : 0≤delta := (norm_nonneg _).trans he
  have hn := sourceGramNormalize_stability C B delta eta heta (hh.trans_le hlower) he (by linarith) hrank
  have hb : ‖sourceDecodeCompletionMatrix (sourceGramNormalize C eta)-sourceComplexGramNormalize B‖≤12*delta/h+(eta : ℝ) :=
    hn.2.2.2.trans (add_le_add
      (div_le_div_of_nonneg_left (by positivity) hh hlower) (le_refl _))
  have hentry := (sourceCompletionMatrix_entry_norm (sourceDecodeCompletionMatrix (sourceGramNormalize C eta)-sourceComplexGramNormalize B)
    false true).trans hb
  change ‖sourceDecodeCompletionMatrix (sourceGramNormalize C eta) false true-sourceComplexGramNormalize B false true‖≤
    12*delta/h+(eta : ℝ) at hentry
  calc
    _ = 2*‖sourceDecodeCompletionMatrix (sourceGramNormalize C eta) false true-sourceComplexGramNormalize B false true‖ := by
      rw [← mul_sub,norm_mul]
      norm_num
    _ ≤ 2*(12*delta/h+(eta : ℝ)) := mul_le_mul_of_nonneg_left hentry (by norm_num)
    _ = _ := by ring

/-- The estimate `sourceDiscovered_error` retains the actual parameter, input-error and normalization budgets. -/
theorem sourceDiscovered_error {d : ℕ}
    (F : Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) (G : Fin (d+1) → Matrix Bool Bool ℂ)
    (eta : ℚ) (heta : 0<eta) (delta M h : ℝ) (hh : 0<h) (hh1 : h≤1)
    (heta_delta : (eta : ℝ)≤delta) (hinv : SourceIdealDeflationInvariant G h)
    (he : ∀ j,‖sourceDecodeCompletionMatrix (F j)-G j‖≤delta)
    (hMcap : M≤h/4) (hbudget : delta*(30/h)^d≤M*(30/h)) :
    List.Forall₂ (fun z w : ℂ => ‖z-w‖≤24*M/h+2*(eta : ℝ))
      (sourceDiscovered F eta) (sourceIdealDiscovered G) := by
  induction d generalizing delta with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
    have hd : 0≤delta := (norm_nonneg _).trans (he 0)
    have ha : 1≤30/h := (le_div_iff₀ hh).mpr (by linarith)
    have hapos : 0<30/h := by positivity
    have hhead : delta*(30/h)^m≤M := (mul_le_mul_iff_left₀ hapos).mp
      (by simpa only [pow_succ,mul_assoc] using hbudget)
    have hdM : delta≤M := (le_mul_of_one_le_right hd (one_le_pow₀ ha)).trans hhead
    have hcap : delta≤h/4 := hdM.trans hMcap
    have hl : G 0≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.1)
    have hr : G (Fin.last (m+1))≠0 := norm_pos_iff.mp (hh.trans_le hinv.2.2)
    have hdet := sourceCompletionCircle_extreme_determinants_zero (by omega : 0 < m + 1) G hinv.1 hl hr
    have hs := sourceDeflationStep_error F G eta heta delta h hh hh1 hcap heta_delta he
      (sourceCompletionCircle_coefficient_norm G hinv.1) hinv.2.1 hinv.2.2
      (sourceGram_trace_eq_norm_sq _ hdet.1) (sourceGram_trace_eq_norm_sq _ hdet.2)
    have hphase := (raw_phase_error (F (Fin.last (m+1))) (G (Fin.last (m+1)))
      eta heta delta h hh (he _) hcap hinv.2.2 (sourceGram_trace_eq_norm_sq _ hdet.2)).trans
        (add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdM (by norm_num)) hh.le) (le_refl _))
    have hnext : ∀ j,‖sourceDecodeCompletionMatrix (sourceDeflationStep F eta j)-sourceIdealDeflationStep G j‖≤delta*(30/h) := by
      intro j
      convert hs.2.2 j using 1; ring
    have hetanext : (eta : ℝ)≤delta*(30/h) :=
      heta_delta.trans (by simpa using mul_le_mul_of_nonneg_left ha hd)
    have hbudgetnext : (delta*(30/h))*(30/h)^m≤M*(30/h) := by
      convert hbudget using 1; rw [pow_succ]; ring
    exact List.Forall₂.cons hphase
      (ih (sourceDeflationStep F eta) (sourceIdealDeflationStep G) (delta*(30/h)) hetanext
        (sourceIdealDeflation_invariant G h hh hinv) hnext hbudgetnext)

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- Construction for source Discovered Gaussian in the native source discovered phases model. -/
def sourceDiscoveredGaussian : {d : ℕ} → (Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) → ℚ → List (ℚ×ℚ)
  | 0,_,_ => []
  | m+1,F,eta =>
      let z := sourceGramNormalize (F (Fin.last (m+1))) eta false true
      (2*z.1,2*z.2)::sourceDiscoveredGaussian (sourceDeflationStep F eta) eta

/-- The finite construction in `NativeSourceDiscoveredPhases` satisfies `gaussian_twice_decode` under the displayed hypotheses. -/
private theorem gaussian_twice_decode (z : ℚ×ℚ) :
    rootRationalCoordinate (2*z.1,2*z.2)=2*rootRationalCoordinate z := by
  apply Complex.ext <;> norm_num [rootRationalCoordinate,Complex.mul_re,Complex.mul_im]

/-- The finite construction in `NativeSourceDiscoveredPhases` satisfies `sourceDiscovered_decode` under the displayed hypotheses. -/
theorem sourceDiscovered_decode {d : ℕ} (F : Fin (d+1) → Matrix Bool Bool (ℚ×ℚ)) (eta : ℚ) :
    (sourceDiscoveredGaussian F eta).map rootRationalCoordinate=sourceDiscovered F eta := by
  induction d with
  | zero => rfl
  | succ m ih =>
    simp only [sourceDiscoveredGaussian,List.map_cons,sourceDiscovered,ih]
    congr 1
    exact gaussian_twice_decode _

end DiscoveredError

section OriginalDiscovered

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceDiscoveredPhases` satisfies `paired_nonzero` under the displayed hypotheses. -/
private theorem paired_nonzero {xs ys : List ℂ}
    (hp : List.Forall₂ (fun z w : ℂ => ‖z-w‖≤(7/40 : ℝ)) xs ys)
    (hy : ∀ y∈ys,‖y‖=1) : ∀ x∈xs,x≠0 := by
  induction hp with
  | nil => simp
  | @cons a b xs ys hab htail ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hx|hx
    · subst x
      intro hz
      have hb := hy b (List.mem_cons_self)
      rw [hz,zero_sub,norm_neg,hb] at hab
      norm_num at hab
    · exact ih (fun y hmem => hy y (List.mem_cons_of_mem _ hmem)) x hx

/-- The estimate `source_discovered_error_grid` retains the actual parameter, input-error and normalization budgets. -/
theorem source_discovered_error_grid (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
 :
    let F := sourceRoundedMatrix cs N E f
    let G := sourceIdealMatrixArray cs N E
    let eta := sourceInputEta cs N E
    List.Forall₂ (fun z w : ℂ => ‖z-w‖≤7*(sourceGrid N (sourceInputU cs N E) : ℝ)/40) (sourceDiscovered F eta) (sourceIdealDiscovered G) ∧
      (∀ z∈sourceIdealDiscovered G,‖z‖=1) ∧ (∀ z∈sourceDiscovered F eta,z≠0) := by
  let F := sourceRoundedMatrix cs N E f
  let G := sourceIdealMatrixArray cs N E
  let eta := sourceInputEta cs N E
  let h := sourceGrid N (sourceInputU cs N E)
  let K := sourceK N (sourceInputU cs N E)
  let delta : ℝ := (K : ℝ)*(eta : ℝ)
  have hb := source_initial_error_budget cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hh : (0 : ℝ)<(h : ℝ) := by exact_mod_cast sourceGrid_pos N (sourceInputU cs N E)
  have hh1 : (h : ℝ)≤1 := by
    dsimp [h,sourceGrid]
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have he : (0 : ℝ)<(eta : ℝ) := by dsimp [eta,sourceInputEta]; positivity
  have hd0 : 0≤delta := he.le.trans hb.1
  have hlarge : (1 : ℝ)≤128/(h : ℝ) := (le_div_iff₀ hh).mpr (by linarith)
  have hpower : (30/(h : ℝ))^(sourceDegree cs N E)≤(128/(h : ℝ))^(N+1) :=
    (pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_right (by norm_num : (30 : ℝ)≤128) hh.le) _).trans
      (pow_le_pow_right₀ hlarge (Nat.le_succ_of_le (sourceDegree_le cs N E)))
  have hbudget : delta*(128/(h : ℝ))^(N+1)≤(h : ℝ)/16 := by
    dsimp only [delta,K,eta,h]
    exact_mod_cast (source_input_budget cs N E hE).1
  have hfinal : delta*(30/(h : ℝ))^(sourceDegree cs N E)≤(h : ℝ)/16 :=
    (mul_le_mul_of_nonneg_left hpower hd0).trans hbudget
  have hinv : SourceIdealDeflationInvariant G (h : ℝ) :=
    ⟨sourceIdealArray_circle_unitary cs N E hE htail hparity hd hnorm,
      source_ideal_extreme_lower cs N E hd 0 (Or.inl rfl),
      source_ideal_extreme_lower cs N E hd _ (Or.inr rfl)⟩
  let M : ℝ := (h : ℝ)^2/480
  have hMcap : M≤(h : ℝ)/4 := by
    have hs : (h : ℝ)^2≤(h : ℝ) := by nlinarith
    dsimp [M]
    linarith
  have hbudgetM : delta*(30/(h : ℝ))^(sourceDegree cs N E)≤M*(30/(h : ℝ)) := by
    convert hfinal using 1
    dsimp [M]
    field_simp [hh.ne']
    ring
  have hs := sourceDiscovered_error F G eta (by dsimp [eta,sourceInputEta]; positivity)
    delta M (h : ℝ) hh hh1 hb.1 hinv hb.2.2 hMcap hbudgetM
  have heta_h : (eta : ℝ)≤(h : ℝ)/16 := hb.1.trans hb.2.1
  have hphase : 24*M/(h : ℝ)+2*(eta : ℝ)≤7*(h : ℝ)/40 := by
    have hid : 24*M/(h : ℝ)=(h : ℝ)/20 := by
      dsimp [M]
      field_simp [hh.ne']
      ring
    rw [hid]
    linarith
  have hpair := List.Forall₂.imp (fun _ _ hz => hz.trans hphase) hs
  have hunit := source_ideal_discovered_unit cs N E hE htail hparity hd hnorm
  have hcoarse := List.Forall₂.imp (fun _ _ hz => hz.trans
    (show 7*(h : ℝ)/40≤(7/40 : ℝ) by linarith)) hpair
  exact ⟨hpair,hunit,paired_nonzero hcoarse hunit⟩


/-- The estimate `source_discovered_error` retains the actual parameter, input-error and normalization budgets. -/
theorem source_discovered_error (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hd : 0<sourceDegree cs N E)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcontent : content≠0)
    (hguard : rootIntegerFactorProduct content
      (List.ofFn (fun j => (List.ofFn (f j).coefficients,(f j).exponent)))=
        rootCanonicalCoefficients (sourceIntegerComplement cs N E))
    (haccepted : ∀ j,RootIntegerFactorGuards (f j) (sourceInputEta cs N E))
 :
    let F := sourceRoundedMatrix cs N E f
    let G := sourceIdealMatrixArray cs N E
    let eta := sourceInputEta cs N E
    List.Forall₂ (fun z w : ℂ => ‖z-w‖≤(7/40 : ℝ)) (sourceDiscovered F eta) (sourceIdealDiscovered G) ∧
      (∀ z∈sourceIdealDiscovered G,‖z‖=1) ∧ (∀ z∈sourceDiscovered F eta,z≠0) := by
  have hs := source_discovered_error_grid cs N E hE htail hparity hd hnorm m content f hcontent hguard haccepted
  have hh1 : (sourceGrid N (sourceInputU cs N E) : ℝ)≤1 := by
    unfold sourceGrid
    push_cast
    exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  have hc := List.Forall₂.imp (fun _ _ hz => hz.trans
    (show 7*(sourceGrid N (sourceInputU cs N E) : ℝ)/40≤(7/40 : ℝ) by linarith)) hs.1
  exact ⟨hc,hs.2⟩

end OriginalDiscovered

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
