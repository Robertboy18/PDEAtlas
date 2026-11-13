/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Cauchy

/-!
# Uniform time control from the initial data and forcing

The characteristic endpoint formula bounds the time derivative by the initial
displacement derivative, the initial velocity, and elapsed time times a forcing
bound. A bound on the displacement itself does not bound its derivative; that
additional initial-data hypothesis is explicit here.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis MeasureTheory Set
open scoped BoundedContinuousFunction

namespace WaveEquation

private theorem hasDerivAt_dAlembert_zero_time {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (x : ℝ^1) (t : ℝ) :
    HasDerivAt (fun s ↦ dAlembertFormula (fun _ ↦ 0) h (x 0) s)
      ((1 / 2 : ℝ) * (h (x 0 + t) + h (x 0 - t))) t := by
  have hd := PDE.hasDerivAt_timeSpaceCons
    (fun p : ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0) h (p 1) (p 0)) t x
    ((contDiff_two_dAlembertFormula (fun _ ↦ 0) h contDiff_const hh).differentiable
      (by norm_num) _)
  rw [partialDeriv_dAlembert_time (fun _ ↦ 0) h contDiff_const hh] at hd
  simpa [timeSpaceCons] using hd

/-- Differentiating the retarded field in time integrates the two characteristic
endpoint values of the forcing. No forcing derivative occurs in the formula. -/
theorem hasDerivAt_dAlembertDuhamelSolution_time {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ^1)
    (t : ℝ) :
    HasDerivAt (fun r ↦ dAlembertDuhamelSolution f (timeSpaceCons r x))
      (∫ s in (0 : ℝ)..t, (1 / 2 : ℝ) *
        (f (timeSpaceCons (max 0 s) (EuclideanSpace.single 0 (x 0 + (t - s)))) +
          f (timeSpaceCons (max 0 s) (EuclideanSpace.single 0 (x 0 - (t - s)))))) t := by
  let h (s y : ℝ) := f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y))
  let H (r s : ℝ) := dAlembertFormula (fun _ ↦ 0) (h s) (x 0) (r - s)
  let D (r s : ℝ) := (1 / 2 : ℝ) * (h s (x 0 + (r - s)) + h s (x 0 - (r - s)))
  have hc : Continuous (fun q : ℝ × ℝ ↦ h q.1 q.2) := by
    apply hf.continuous.comp
    exact (contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous.comp
      ((continuous_const.max continuous_fst).prodMk
        ((PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
          (continuous_pi fun i ↦ by
            fin_cases i
            simpa using (continuous_snd : Continuous (fun p : ℝ × ℝ ↦ p.2)))))
  have hD : Continuous (fun q : ℝ × ℝ ↦ D q.1 q.2) := continuous_const.mul
      ((hc.comp (continuous_snd.prodMk
        (continuous_const.add (continuous_fst.sub continuous_snd)))).add
        (hc.comp (continuous_snd.prodMk
          (continuous_const.sub (continuous_fst.sub continuous_snd)))))
  have hH : Continuous (fun q : ℝ × ℝ ↦ H q.1 q.2) := by
    exact (continuous_dAlembert_source_kernel hf.continuous).comp (continuous_snd.prodMk
        ((contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous.comp
          ((continuous_fst.sub continuous_snd).prodMk continuous_const)))
  have hd (r s : ℝ) : HasDerivAt (fun q ↦ H q s) (D r s) r := by
    simpa [H, D, h, Function.comp_def] using (hasDerivAt_dAlembert_zero_time
        (contDiff_dAlembert_forward_velocity hf.contDiffOn s) x (r - s)).comp r
          ((hasDerivAt_id r).sub_const s)
  have he := hasFDerivAt_intervalIntegral_moving_right_of_continuous
    H (fun r s ↦ D r s • (1 : ℝ →L[ℝ] ℝ)) 0 id hH
    (hD.smul continuous_const) (fun r s ↦ by
      convert (hd r s).hasFDerivAt using 1
      ext
      simp [smul_eq_mul, mul_comm]) t (hasFDerivAt_id t)
  have hz : H t t = 0 := by simp [H, dAlembertFormula]
  simp only [id_eq, hz, ContinuousLinearMap.smulRight_zero, zero_add,
    intervalIntegral.integral_smul_const] at he
  have ht := he.hasDerivAt
  simp only [smul_apply, one_apply_eq_self, smul_eq_mul, mul_one] at ht
  simpa [dAlembertDuhamelSolution_eq_doubleIntegral, timeSpaceCons, h, H, D] using ht

/-- A bounded forcing controls the time derivative of its retarded field,
independently of its spatial derivatives. -/
theorem norm_partialDeriv_dAlembertDuhamelSolution_time_le {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f)
    {C : ℝ} (hbound : ∀ p : ℝ^2, ‖f p‖ ≤ C) {p : ℝ^2} (hp : 0 ≤ p 0) :
    ‖(∂[0] (dAlembertDuhamelSolution f)) p‖ ≤ p 0 * C := by
  have hd := hasDerivAt_dAlembertDuhamelSolution_time hf (spatialPart p) (p 0)
  have he := PDE.hasDerivAt_timeSpaceCons (dAlembertDuhamelSolution f) (p 0) (spatialPart p)
    ((contDiff_two_dAlembertDuhamelSolution hf.contDiffOn).differentiable
      (by norm_num) _)
  have hv := he.unique hd
  rw [timeSpaceCons_spatialPart] at hv
  rw [hv]
  calc
    _ ≤ C * |p 0 - 0| := intervalIntegral.norm_integral_le_of_norm_le_const fun s _ ↦ by
      rw [norm_mul]
      simp only [norm_div, norm_one, Real.norm_ofNat]
      linarith [norm_add_le (f (timeSpaceCons (max 0 s) (EuclideanSpace.single 0
          (spatialPart p 0 + (p 0 - s))))) (f (timeSpaceCons (max 0 s) (EuclideanSpace.single 0
          (spatialPart p 0 - (p 0 - s))))), hbound (timeSpaceCons (max 0 s) (EuclideanSpace.single 0
          (spatialPart p 0 + (p 0 - s)))), hbound (timeSpaceCons (max 0 s) (EuclideanSpace.single 0
          (spatialPart p 0 - (p 0 - s))))]
    _ = p 0 * C := by rw [sub_zero, abs_of_nonneg hp, mul_comm]

/-- Bounded initial displacement derivative and velocity, together with bounded
reaction, control the constructed wave's time derivative on the whole line. -/
theorem norm_partialDeriv_nonlinearClassicalSolution_time_le {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) {D C : ℝ} (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) (hC : ∀ z : ℝ, ‖f z‖ ≤ C)
    {p : ℝ^2} (hp : 0 ≤ p 0) :
    ‖(∂[0] (nonlinearClassicalSolution hf g h)) p‖ ≤ D + ‖h‖ + p 0 * C := by
  obtain ⟨A, he, _⟩ := nonlinearClassicalSolution_locally_eq_extension hf g h p
  have hj : (∂[0] (nonlinearClassicalSolution hf g h)) p =
      (∂[0] (classicalStripExtension hf g h A)) p :=
    congrArg (fun B : ℝ^2 →L[ℝ] ℝ ↦ B (EuclideanSpace.single 0 1)) he.fderiv_eq
  let F : ℝ^2 → ℝ := fun q ↦ f (firstStripExtension hf g h A q)
  have hF : ContDiff ℝ 1 F := hf₁.comp (contDiff_one_firstStripExtension hf hg hh A)
  have hfree : ‖(∂[0] (fun q : ℝ^2 ↦ dAlembertFormula g h (q 1) (q 0))) p‖ ≤
      D + ‖h‖ := by
    rw [partialDeriv_dAlembert_time g h hg hh]
    calc
      _ ≤ ‖(1 / 2 : ℝ) * (deriv g (p 1 + p 0) - deriv g (p 1 - p 0))‖ +
          ‖(1 / 2 : ℝ) * (h (p 1 + p 0) + h (p 1 - p 0))‖ := norm_add_le _ _
      _ ≤ D + ‖h‖ := by
        simp only [norm_mul, norm_div, norm_one, Real.norm_ofNat]
        linarith [norm_sub_le (deriv g (p 1 + p 0)) (deriv g (p 1 - p 0)),
          norm_add_le (h (p 1 + p 0)) (h (p 1 - p 0)), hD (p 1 + p 0), hD (p 1 - p 0),
          h.norm_coe_le_norm (p 1 + p 0), h.norm_coe_le_norm (p 1 - p 0)]
  rw [hj]
  change ‖(∂[0] (fun q : ℝ^2 ↦
    dAlembertFormula g h (q 1) (q 0) - dAlembertDuhamelSolution F q)) p‖ ≤ _
  rw [PDE.partialDeriv_sub (contDiff_two_dAlembertFormula g h hg hh |>.differentiable
    (by norm_num) _) ((contDiff_two_dAlembertDuhamelSolution hF.contDiffOn).differentiable
      (by norm_num) _)]
  exact (norm_sub_le _ _).trans (add_le_add hfree
    (norm_partialDeriv_dAlembertDuhamelSolution_time_le hF (fun q ↦ hC _) hp))

/-- On a finite strip the constructed wave is Lipschitz in time uniformly in
space. Only the initial displacement derivative, initial velocity, and forcing
are bounded; no second derivatives of the data are bounded. -/
theorem norm_nonlinearClassicalSolution_time_sub_le {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) {D C S s t : ℝ} (hD : ∀ x : ℝ, ‖deriv g x‖ ≤ D) (hC : ∀ z : ℝ, ‖f z‖ ≤ C)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ S) (x : ℝ^1) :
    ‖nonlinearClassicalSolution hf g h (timeSpaceCons t x) -
      nonlinearClassicalSolution hf g h (timeSpaceCons s x)‖ ≤ (D + ‖h‖ + S * C) * (t - s) := by
  have hv := (contDiff_two_nonlinearClassicalSolution hf hf₁ hg hh).differentiable
    (by norm_num)
  have hC₀ : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  apply norm_image_sub_le_of_norm_deriv_le_segment'
    (fun r _ ↦ (PDE.hasDerivAt_timeSpaceCons _ r x (hv _)).hasDerivWithinAt) ?_ t ⟨hst, le_rfl⟩
  intro r hr
  have hr₀ : 0 ≤ (timeSpaceCons r x) 0 := by simpa using hs.trans hr.1
  exact (norm_partialDeriv_nonlinearClassicalSolution_time_le hf hf₁ hg hh hD hC hr₀).trans
    (by simp only [timeSpaceCons_zero]; gcongr; exact hr.2.le.trans ht)

end WaveEquation
