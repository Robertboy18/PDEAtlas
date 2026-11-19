/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Duhamel.Profile
public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Interval
public import PDE.Analysis.Integration.ParametricInterval
public import PDE.Analysis.Operator.FiniteRankCorrection

/-!
# Validating approximate responses to linear evolution

A response kernel `G(t)` maps coefficients to spatial fields. Convolving it with a
continuous coefficient trajectory gives a forced trajectory. Its error has two parts:
the mismatch of `G(0)` with the prescribed initial response, and the convolution of
the evolution residual with the coefficients.

The spatial fields belong to a regularity space `E`, while the equation holds in `H`.
The maps `J, A : E →L[ℝ] H` represent value and generator evaluation. Thus the generator
need not be bounded on the space in which the equation holds. Neither a full semigroup
nor differentiability of the coefficient trajectory is required.

For finite-dimensional coefficient spaces this treats all response columns together.
The algebra and integration do not require finite dimension. The differentiation theorem
assumes continuous response derivatives; piecewise representations must establish these
hypotheses for their represented functions.

A trace map `Q` and reconstruction `Ψ` with `Q ∘ J ∘ Ψ = id` also allow exact
analytic correction of an approximate trajectory. A proposed reconstruction whose
coordinate residual has norm below one gives such a right inverse by Neumann correction,
with quantitative control of the reconstruction and its generator image.
Solving the coefficient ODE
`a' = Q A Ψ a - Q(g' - Ag)` cancels the initial and evolution errors under `Q`.
The coefficients are given by variation of constants, with quantitative bounds
from supplied propagator and extracted-residual envelopes. Closed-interval data suffice
for the correction, with one-sided time derivatives at the endpoints.
The reconstruction fields need not be eigenvectors; their spatial evolution error
remains in `responseJetResidual`. For derivative traces, a separate Taylor estimate
converts zero traces into a vanishing order and a singularly weighted bound.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Sections 2.8.1 and 2.8.2.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Interval Topology

namespace PDE.Analysis.Evolution

variable {F E H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- The trajectory obtained by applying a response kernel to time-dependent coefficients. -/
def responseIntegral (G : ℝ → F →L[ℝ] E) (a : ℝ → F) (t : ℝ) : E :=
  ∫ s in 0..t, G (t - s) (a s)

omit [CompleteSpace E] [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] in
/-- The forced response starts from zero, independently of the kernel's initial error. -/
@[simp] theorem responseIntegral_zero (G : ℝ → F →L[ℝ] E) (a : ℝ → F) :
    responseIntegral G a 0 = 0 := by
  simp [responseIntegral]

/-- The forcing error of an approximate response: its initial mismatch plus its
convolved evolution residual. The supplied `G'` must separately be proved to be the
time derivative after applying the value map `J`. -/
def responseError (J A : E →L[ℝ] H) (G : ℝ → F →L[ℝ] E)
    (G' : ℝ → F →L[ℝ] H) (χ : F →L[ℝ] E) (a : ℝ → F) (t : ℝ) : H :=
  J ((G 0 - χ) (a t)) +
    ∫ s in 0..t, (G' (t - s) - A.comp (G (t - s))) (a s)

/-- A bounded spatial map commutes with the response integral. -/
theorem map_responseIntegral (L : E →L[ℝ] H) (G : ℝ → F →L[ℝ] E) (a : ℝ → F)
    (hG : Continuous fun p : ℝ × F ↦ G p.1 p.2) (ha : Continuous a) (t : ℝ) :
    L (responseIntegral G a t) = responseIntegral (fun s ↦ L.comp (G s)) a t := by
  have hint : IntervalIntegrable (fun s ↦ G (t - s) (a s)) volume 0 t :=
    (hG.comp ((continuous_const.sub continuous_id).prodMk ha)).intervalIntegrable 0 t
  rw [responseIntegral, ← L.intervalIntegral_comp_comm hint]
  rfl

omit [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H] in
/-- Differentiating a response convolution needs only continuous coefficients.
The derivative of the kernel is taken at each fixed coefficient vector. -/
theorem hasDerivAt_responseIntegral (G G' : ℝ → F →L[ℝ] E) (a : ℝ → F)
    (hG : Continuous fun p : ℝ × F ↦ G p.1 p.2)
    (hG' : Continuous fun p : ℝ × F ↦ G' p.1 p.2)
    (hd : ∀ r v, HasDerivAt (fun q ↦ G q v) (G' r v) r)
    (ha : Continuous a) (t : ℝ) :
    HasDerivAt (responseIntegral G a) (G 0 (a t) + responseIntegral G' a t) t := by
  let K : ℝ → ℝ → E := fun q s ↦ G (q - s) (a s)
  let K' : ℝ → ℝ → ℝ →L[ℝ] E := fun q s ↦
    (ContinuousLinearMap.id ℝ ℝ).smulRight (G' (q - s) (a s))
  have hK : Continuous fun p : ℝ × ℝ ↦ K p.1 p.2 :=
    hG.comp ((continuous_fst.sub continuous_snd).prodMk (ha.comp continuous_snd))
  have hK' : Continuous fun p : ℝ × ℝ ↦ K' p.1 p.2 :=
    (ContinuousLinearMap.smulRightL ℝ ℝ E (ContinuousLinearMap.id ℝ ℝ)).continuous.comp
      (hG'.comp ((continuous_fst.sub continuous_snd).prodMk (ha.comp continuous_snd)))
  have hdK (q s : ℝ) : HasFDerivAt (fun r ↦ K r s) (K' q s) q := by
    simpa [K, K', Function.comp_def, ContinuousLinearMap.smulRight_id] using
      ((hd (q - s) (a s)).scomp q ((hasDerivAt_id q).sub_const s)).hasFDerivAt
  have hdint := hasFDerivAt_intervalIntegral_moving_right_of_continuous
    K K' 0 id hK hK' hdK t (hasFDerivAt_id t)
  have hint : IntervalIntegrable (K' t) volume 0 t :=
    (hK'.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
  rw [show responseIntegral G a = (fun q ↦ ∫ s in 0..q, G (q - s) (a s)) by rfl]
  simpa [responseIntegral, K, K', ContinuousLinearMap.intervalIntegral_apply hint,
    ContinuousLinearMap.smulRight_apply] using hdint.hasDerivAt

/-- The response convolution satisfies the forced evolution equation with its
explicit initial-value and evolution errors retained. -/
theorem hasDerivAt_map_responseIntegral (J A : E →L[ℝ] H)
    (G : ℝ → F →L[ℝ] E) (G' : ℝ → F →L[ℝ] H) (χ : F →L[ℝ] E) (a : ℝ → F)
    (hG : Continuous fun p : ℝ × F ↦ G p.1 p.2)
    (hG' : Continuous fun p : ℝ × F ↦ G' p.1 p.2)
    (hd : ∀ r v, HasDerivAt (fun q ↦ J (G q v)) (G' r v) r)
    (ha : Continuous a) (t : ℝ) :
    HasDerivAt (fun q ↦ J (responseIntegral G a q))
      (A (responseIntegral G a t) + J (χ (a t)) + responseError J A G G' χ a t) t := by
  have hJG : Continuous fun p : ℝ × F ↦ (J.comp (G p.1)) p.2 := J.continuous.comp hG
  have hderiv := hasDerivAt_responseIntegral (fun r ↦ J.comp (G r)) G' a
    hJG hG' hd ha t
  have hintG : IntervalIntegrable (fun s ↦ G (t - s) (a s)) volume 0 t :=
    (hG.comp ((continuous_const.sub continuous_id).prodMk ha)).intervalIntegrable 0 t
  have hintA : IntervalIntegrable (fun s ↦ A (G (t - s) (a s))) volume 0 t :=
    (A.continuous.comp
      (hG.comp ((continuous_const.sub continuous_id).prodMk ha))).intervalIntegrable 0 t
  have hintG' : IntervalIntegrable (fun s ↦ G' (t - s) (a s)) volume 0 t :=
    (hG'.comp ((continuous_const.sub continuous_id).prodMk ha)).intervalIntegrable 0 t
  have herr : responseError J A G G' χ a t =
      J (G 0 (a t)) - J (χ (a t)) +
        responseIntegral G' a t - A (responseIntegral G a t) := by
    simp only [responseError, sub_apply, map_sub,
      ContinuousLinearMap.comp_apply]
    rw [intervalIntegral.integral_sub hintG' hintA,
      A.intervalIntegral_comp_comm hintG]
    simp only [responseIntegral]
    abel
  have hvalue : responseIntegral (fun r ↦ J.comp (G r)) a =
      fun q ↦ J (responseIntegral G a q) :=
    funext fun q ↦ (map_responseIntegral J G a hG ha q).symm
  rw [hvalue] at hderiv
  convert hderiv using 1
  simp only [herr, ContinuousLinearMap.comp_apply]
  abel

/-- Subtracting the response error from the complementary trajectory leaves an
exact solution after the two trajectories are added. -/
theorem hasDerivAt_map_add_responseIntegral (J A : E →L[ℝ] H)
    (G : ℝ → F →L[ℝ] E) (G' : ℝ → F →L[ℝ] H) (χ : F →L[ℝ] E) (a : ℝ → F)
    (hG : Continuous fun p : ℝ × F ↦ G p.1 p.2)
    (hG' : Continuous fun p : ℝ × F ↦ G' p.1 p.2)
    (hd : ∀ r v, HasDerivAt (fun q ↦ J (G q v)) (G' r v) r)
    (ha : Continuous a) {u : ℝ → E} {t : ℝ}
    (hu : HasDerivAt (fun q ↦ J (u q))
      (A (u t) - J (χ (a t)) - responseError J A G G' χ a t) t) :
    HasDerivAt (fun q ↦ J (u q + responseIntegral G a q))
      (A (u t + responseIntegral G a t)) t := by
  have hdresponse := hasDerivAt_map_responseIntegral J A G G' χ a hG hG' hd ha t
  convert hu.fun_add hdresponse using 1
  · simp only [map_add]
  · simp only [map_add]
    abel

omit [CompleteSpace E] [CompleteSpace H] in
/-- Bounds on the response columns give a forcing-error bound for any coefficient
trajectory. A time-dependent residual bound keeps decay and localization estimates
available to applications. -/
theorem norm_responseError_le (J A : E →L[ℝ] H)
    (G : ℝ → F →L[ℝ] E) (G' : ℝ → F →L[ℝ] H) (χ : F →L[ℝ] E) (a : ℝ → F)
    {t η : ℝ} {ε : ℝ → ℝ} (ht : 0 ≤ t)
    (hzero : ‖J.comp (G 0 - χ)‖ ≤ η)
    (hresidual : ∀ s ∈ Set.Ioc 0 t, ‖G' (t - s) - A.comp (G (t - s))‖ ≤ ε (t - s))
    (hbound : IntervalIntegrable (fun s ↦ ‖a s‖ * ε (t - s)) volume 0 t) :
    ‖responseError J A G G' χ a t‖ ≤
      η * ‖a t‖ + ∫ s in 0..t, ‖a s‖ * ε (t - s) := by
  have hinit : ‖J ((G 0 - χ) (a t))‖ ≤ η * ‖a t‖ :=
    ((J.comp (G 0 - χ)).le_opNorm (a t)).trans
      (mul_le_mul_of_nonneg_right hzero (norm_nonneg _))
  have hint : ‖∫ s in 0..t, (G' (t - s) - A.comp (G (t - s))) (a s)‖ ≤
      ∫ s in 0..t, ‖a s‖ * ε (t - s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht _ hbound
    exact Filter.Eventually.of_forall fun s hs ↦
      ((G' (t - s) - A.comp (G (t - s))).le_opNorm (a s)).trans <|
        (mul_le_mul_of_nonneg_right (hresidual s hs) (norm_nonneg _)).trans_eq
          (mul_comm _ _)
  exact (norm_add_le _ _).trans (add_le_add hinit hint)

/-- The part of the corrected evolution error left after removing its extracted
traces. The generator is applied to the full corrected field, so errors in the
spatial correction functions remain in this residual. -/
def responseJetResidual (J A : E →L[ℝ] H) (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E)
    (g : ℝ → E) (g' : ℝ → H) (a : ℝ → F) (t : ℝ) : H :=
  (ContinuousLinearMap.id ℝ H - (J.comp Ψ).comp Q) (g' t - A (g t + Ψ (a t)))

omit [CompleteSpace E] [CompleteSpace H] in
/-- The residual after jet cancellation retains the evolution of the correction
fields. Both the projection and generator bounds can be sharpened independently. -/
theorem norm_responseJetResidual_le (J A : E →L[ℝ] H) (Q : H →L[ℝ] F)
    (Ψ : F →L[ℝ] E) (g : ℝ → E) (g' : ℝ → H) (a : ℝ → F) (t : ℝ) :
    ‖responseJetResidual J A Q Ψ g g' a t‖ ≤
      ‖ContinuousLinearMap.id ℝ H - (J.comp Ψ).comp Q‖ *
        (‖g' t - A (g t)‖ + ‖A.comp Ψ‖ * ‖a t‖) := by
  apply ((ContinuousLinearMap.id ℝ H - (J.comp Ψ).comp Q).le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [map_add, ← sub_sub]
  exact (norm_sub_le _ _).trans
    (add_le_add_right ((A.comp Ψ).le_opNorm _) _)

omit [CompleteSpace E] [CompleteSpace H] in
/-- Exact coefficient correction from a supplied fundamental solution. Its forcing
is the negative extracted residual, and its initial value cancels the initial traces. -/
def responseJetCoefficients (J A : E →L[ℝ] H) (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E)
    (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0) : ℝ → F :=
  S.solution (fun t ↦ -Q (g' t - A (g t))) 0 (-Q (J (g 0 - χ)))

omit [CompleteSpace E] [CompleteSpace H] in
/-- The coefficient correction cancels the initial traces exactly. -/
@[simp] theorem responseJetCoefficients_zero (J A : E →L[ℝ] H) (Q : H →L[ℝ] F)
    (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0) :
    responseJetCoefficients J A Q Ψ χ g g' S 0 = -Q (J (g 0 - χ)) :=
  S.solution_initial _ 0 _

omit [CompleteSpace E] [CompleteSpace H] in
/-- The exact coefficient correction solves the extracted residual equation. -/
theorem hasDerivAt_responseJetCoefficients [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0)
    (hresidual : Continuous fun t ↦ Q (g' t - A (g t))) (t : ℝ) :
    HasDerivAt (responseJetCoefficients J A Q Ψ χ g g' S)
      (Q (A (Ψ (responseJetCoefficients J A Q Ψ χ g g' S t))) -
        Q (g' t - A (g t))) t := by
  simpa only [responseJetCoefficients, ContinuousLinearMap.comp_apply, sub_eq_add_neg] using
    S.hasDerivAt_solution (f := fun s ↦ -Q (g' s - A (g s)))
      hresidual.neg 0 (-Q (J (g 0 - χ))) t

omit [CompleteSpace E] [CompleteSpace H] in
/-- Quantitative coefficient control from the same exact propagator used in the
correction. The envelopes remain inputs, so improved numerical estimates change
the bound without changing the analytic argument. -/
theorem norm_responseJetCoefficients_le [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0)
    {t : ℝ} (ht : 0 ≤ t) (hresidual : ContinuousOn (fun s ↦ Q (g' s - A (g s)))
      (Set.Icc 0 t)) {C ε : ℝ → ℝ}
    (hS : ∀ s ∈ Set.Icc 0 t, ‖S.propagator t s‖ ≤ C s)
    (hresidual_bound : ∀ s ∈ Set.Icc 0 t, ‖Q (g' s - A (g s))‖ ≤ ε s)
    (hbound : IntervalIntegrable (fun s ↦ C s * ε s) volume 0 t) :
    ‖responseJetCoefficients J A Q Ψ χ g g' S t‖ ≤
      C 0 * ‖Q (J (g 0 - χ))‖ + ∫ s in 0..t, C s * ε s := by
  simpa only [responseJetCoefficients, norm_neg] using
    S.norm_solution_le_integral (f := fun s ↦ -Q (g' s - A (g s)))
      ht hresidual.neg (-Q (J (g 0 - χ))) hS
      (fun s hs ↦ (norm_neg _).trans_le (hresidual_bound s hs)) hbound

omit [CompleteSpace E] [CompleteSpace H] in
/-- Variation of constants solves the coefficient equation on a closed time interval.
No continuity of the extracted residual outside that interval is required. -/
theorem hasDerivWithinAt_responseJetCoefficients [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0) {T t : ℝ}
    (hresidual : ContinuousOn (fun r ↦ Q (g' r - A (g r))) (Set.Icc 0 T))
    (ht : t ∈ Set.Icc 0 T) :
    HasDerivWithinAt (responseJetCoefficients J A Q Ψ χ g g' S)
      (Q (A (Ψ (responseJetCoefficients J A Q Ψ χ g g' S t))) -
        Q (g' t - A (g t))) (Set.Icc 0 T) t := by
  have hd := (S.restrict (Set.subset_univ (Set.Icc 0 T))).hasDerivWithinAt_solution
    (f := fun r ↦ -Q (g' r - A (g r))) hresidual.neg
    (show 0 ∈ Set.Icc 0 T from ⟨le_rfl, ht.1.trans ht.2⟩) ht (-Q (J (g 0 - χ)))
  change HasDerivWithinAt (responseJetCoefficients J A Q Ψ χ g g' S)
    (((Q.comp A).comp Ψ) (responseJetCoefficients J A Q Ψ χ g g' S t) +
      -Q (g' t - A (g t))) (Set.Icc 0 T) t at hd
  simpa only [ContinuousLinearMap.comp_apply, sub_eq_add_neg] using hd

omit [CompleteSpace E] [CompleteSpace H] in
/-- Any coefficient trajectory solving the extracted residual equation gives exact
trace cancellation. This algebraic statement is independent of how the ODE is solved
and allows derivatives within an arbitrary time domain. -/
theorem response_jet_correction_spec (J A : E →L[ℝ] H) (Q : H →L[ℝ] F)
    (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H) (a : ℝ → F)
    (hright : ∀ v, Q (J (Ψ v)) = v) {times : Set ℝ}
    (ha0 : a 0 = -Q (J (g 0 - χ)))
    (hg : ∀ t ∈ times, HasDerivWithinAt (fun r ↦ J (g r)) (g' t) times t)
    (ha : ∀ t ∈ times, HasDerivWithinAt a
      (Q (A (Ψ (a t))) - Q (g' t - A (g t))) times t) :
    Q (J (g 0 + Ψ (a 0) - χ)) = 0 ∧
      ∀ t ∈ times, HasDerivWithinAt (fun r ↦ J (g r + Ψ (a r)))
          (A (g t + Ψ (a t)) + responseJetResidual J A Q Ψ g g' a t) times t ∧
        Q (responseJetResidual J A Q Ψ g g' a t) = 0 := by
  refine ⟨?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [show g 0 + Ψ (a 0) - χ = (g 0 - χ) + Ψ (a 0) by abel]
    simp only [map_add, hright, ha0, add_neg_cancel]
  · have hcorrection := (J.comp Ψ).hasFDerivAt.comp_hasDerivWithinAt t (ha t ht)
    convert (hg t ht).fun_add hcorrection using 1
    · simp only [map_add, Function.comp_def, ContinuousLinearMap.comp_apply]
    · simp only [responseJetResidual, sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply, map_add, map_sub]
      abel
  · simp only [responseJetResidual, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_sub, hright, sub_self]

omit [CompleteSpace E] [CompleteSpace H] in
/-- The constructed coefficients cancel the prescribed traces in the initial and
evolution errors. The same coefficients can be bounded using the supplied propagator. -/
theorem responseJetCoefficients_spec [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0)
    (hright : ∀ v, Q (J (Ψ v)) = v)
    (hg : ∀ t, HasDerivAt (fun r ↦ J (g r)) (g' t) t)
    (hresidual : Continuous fun t ↦ Q (g' t - A (g t))) :
    let a := responseJetCoefficients J A Q Ψ χ g g' S
    Q (J (g 0 + Ψ (a 0) - χ)) = 0 ∧
      ∀ t, HasDerivAt (fun r ↦ J (g r + Ψ (a r)))
          (A (g t + Ψ (a t)) + responseJetResidual J A Q Ψ g g' a t) t ∧
        Q (responseJetResidual J A Q Ψ g g' a t) = 0 := by
  simpa only [hasDerivWithinAt_univ, Set.mem_univ, forall_const] using
    response_jet_correction_spec J A Q Ψ χ g g' (times := Set.univ)
      (responseJetCoefficients J A Q Ψ χ g g' S) hright
      (responseJetCoefficients_zero J A Q Ψ χ g g' S)
      (fun t _ ↦ (hg t).hasDerivWithinAt)
      (fun t _ ↦ (hasDerivAt_responseJetCoefficients J A Q Ψ χ g g' S
        hresidual t).hasDerivWithinAt)

omit [CompleteSpace E] [CompleteSpace H] in
/-- Exact trace cancellation on a finite time interval uses only data on that interval.
The derivatives are taken within the interval, including both endpoints. -/
theorem responseJetCoefficients_spec_on [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (S : FundamentalSolution (fun _ ↦ (Q.comp A).comp Ψ) 0)
    (hright : ∀ v, Q (J (Ψ v)) = v) {T : ℝ}
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun r ↦ J (g r)) (g' t) (Set.Icc 0 T) t)
    (hresidual : ContinuousOn (fun t ↦ Q (g' t - A (g t))) (Set.Icc 0 T)) :
    let a := responseJetCoefficients J A Q Ψ χ g g' S
    Q (J (g 0 + Ψ (a 0) - χ)) = 0 ∧
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun r ↦ J (g r + Ψ (a r)))
          (A (g t + Ψ (a t)) + responseJetResidual J A Q Ψ g g' a t) (Set.Icc 0 T) t ∧
        Q (responseJetResidual J A Q Ψ g g' a t) = 0 :=
  response_jet_correction_spec J A Q Ψ χ g g'
    (responseJetCoefficients J A Q Ψ χ g g' S) hright
    (responseJetCoefficients_zero J A Q Ψ χ g g' S) hg
    (fun _ ht ↦ hasDerivWithinAt_responseJetCoefficients J A Q Ψ χ g g' S hresidual ht)

omit [CompleteSpace E] [CompleteSpace H] in
/-- A coefficient ODE cancels the prescribed traces exactly, both in the initial
error and in the evolution residual. The coefficient space may contain any number
of traces; no numerical approximation of this ODE is used. -/
theorem exists_response_jet_correction [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (hright : ∀ v, Q (J (Ψ v)) = v)
    (hg : ∀ t, HasDerivAt (fun r ↦ J (g r)) (g' t) t)
    (hresidual : Continuous fun t ↦ Q (g' t - A (g t))) :
    ∃ a : ℝ → F,
      Q (J (g 0 + Ψ (a 0) - χ)) = 0 ∧
        ∀ t, HasDerivAt (fun r ↦ J (g r + Ψ (a r)))
            (A (g t + Ψ (a t)) + responseJetResidual J A Q Ψ g g' a t) t ∧
          Q (responseJetResidual J A Q Ψ g g' a t) = 0 := by
  obtain ⟨S⟩ := nonempty_fundamentalSolution (B := fun _ ↦ (Q.comp A).comp Ψ)
    continuous_const (K := ‖(Q.comp A).comp Ψ‖₊) (fun _ ↦ le_rfl) 0
  exact ⟨responseJetCoefficients J A Q Ψ χ g g' S,
    responseJetCoefficients_spec J A Q Ψ χ g g' S hright hg hresidual⟩

omit [CompleteSpace E] [CompleteSpace H] in
/-- A correction exists for an approximate trajectory specified only on a closed
interval. The coefficient ODE cancels its initial and evolution traces exactly. -/
theorem exists_response_jet_correction_on [CompleteSpace F] (J A : E →L[ℝ] H)
    (Q : H →L[ℝ] F) (Ψ : F →L[ℝ] E) (χ : E) (g : ℝ → E) (g' : ℝ → H)
    (hright : ∀ v, Q (J (Ψ v)) = v) {T : ℝ}
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun r ↦ J (g r)) (g' t) (Set.Icc 0 T) t)
    (hresidual : ContinuousOn (fun t ↦ Q (g' t - A (g t))) (Set.Icc 0 T)) :
    ∃ a : ℝ → F,
      Q (J (g 0 + Ψ (a 0) - χ)) = 0 ∧
        ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun r ↦ J (g r + Ψ (a r)))
            (A (g t + Ψ (a t)) + responseJetResidual J A Q Ψ g g' a t) (Set.Icc 0 T) t ∧
          Q (responseJetResidual J A Q Ψ g g' a t) = 0 := by
  obtain ⟨S⟩ := nonempty_fundamentalSolution (B := fun _ ↦ (Q.comp A).comp Ψ)
    continuous_const (K := ‖(Q.comp A).comp Ψ‖₊) (fun _ ↦ le_rfl) 0
  exact ⟨responseJetCoefficients J A Q Ψ χ g g' S,
    responseJetCoefficients_spec_on J A Q Ψ χ g g' S hright hg hresidual⟩

omit [CompleteSpace E] [CompleteSpace H] in
/-- A certified approximate trace reconstruction suffices for exact correction on a closed
interval. Neumann correction first makes the spatial coordinates exact, and the coefficient
ODE then cancels the initial and evolution traces. No exact inverse matrix is an input. -/
theorem exists_response_jet_correction_on_of_norm_sub_le [CompleteSpace F]
    (J A : E →L[ℝ] H) (Q : H →L[ℝ] F) (Φ : F →L[ℝ] E)
    (χ : E) (g : ℝ → E) (g' : ℝ → H) {δ T : ℝ}
    (hres : ‖ContinuousLinearMap.id ℝ F - (Q.comp J).comp Φ‖ ≤ δ) (hδ : δ < 1)
    (hg : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun r ↦ J (g r)) (g' t) (Set.Icc 0 T) t)
    (hresidual : ContinuousOn (fun t ↦ Q (g' t - A (g t))) (Set.Icc 0 T)) :
    let Ψ := ContinuousLinearMap.exactRightInverse (Q.comp J) Φ
    ∃ a : ℝ → F,
      Q (J (g 0 + Ψ (a 0) - χ)) = 0 ∧
        ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun r ↦ J (g r + Ψ (a r)))
            (A (g t + Ψ (a t)) + responseJetResidual J A Q Ψ g g' a t) (Set.Icc 0 T) t ∧
          Q (responseJetResidual J A Q Ψ g g' a t) = 0 := by
  let Ψ := ContinuousLinearMap.exactRightInverse (Q.comp J) Φ
  have hright (v : F) : Q (J (Ψ v)) = v := by
    have h := ContinuousLinearMap.comp_exactRightInverse (Q.comp J) Φ hres hδ
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : F →L[ℝ] F ↦ L v) h
  exact exists_response_jet_correction_on J A Q Ψ χ g g' hright hg hresidual

end PDE.Analysis.Evolution
