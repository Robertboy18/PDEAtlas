/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.SecondVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PDE.Analysis.Calculus.PartialRegularity
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Transport along the flow of a time-dependent field

Let `v` be a field on a finite-dimensional real normed space `E` over the times `[a, b] ∋ 0`,
with a jointly continuous bounded spatial derivative, and let `flowOn v a b s t` be its flow.
The label at time `0` of the particle at `x` at time `t` is `flowOn v a b 0 t x`, and the
particle with label `y` is at `flowOn v a b t 0 y` at time `t`.

* A quantity carried by the particles, `θ x t = θ₀ (flowOn v a b 0 t x)`, is jointly `C¹` on
  `E × (a, b)` and solves `θ_t + Dθ v = 0` at every point; its gradient at the particle
  composed with the first variation is the gradient of `θ₀`. It is `C²` in space when `θ₀`
  and `v` are `C²`.
* A Lagrangian amplitude `Ω` read at the label, `w x t = Ω (flowOn v a b 0 t x) t`, solves the
  forced transport equation `w_t + Dw v = G`, where `G` is the time derivative of `Ω` at fixed
  label.
* `forcedAmplitude Ω₀ G y t = Ω₀ y + ∫₀ᵗ G y r dr` is jointly `C¹` when `G` and its derivative in
  the label are jointly continuous (differentiation under the integral sign).
* The forcing `G y r = Dθ₀(y) (J⁻¹ e)`, `J` the first variation along the particle of label `y`,
  is the derivative in direction `e` of the carried quantity at the particle, and it is `C¹` in
  the label with jointly continuous derivative for `C²` fields and `C²` data. This is the
  Lagrangian form of the forcing `∂₀θ` of the Boussinesq vorticity equation.

## Main results

* `contDiffOn_comp_flowOn`, `hasDerivAt_comp_flowOn_time`, `fderiv_comp_flowOn_comp_variationOn`,
  `contDiff_comp_flowOn`: the carried quantity.
* `contDiffOn_comp_flowOn_label`, `hasDerivAt_comp_flowOn_label_time`: forced transport.
* `hasDerivAt_forcedAmplitude`, `hasFDerivAt_forcedAmplitude`, `contDiffOn_forcedAmplitude`.
* `continuousOn_labelForcing`, `hasFDerivAt_labelForcing`, `continuousOn_labelForcingDeriv`,
  `labelForcing_eq`, `labelForcing_flowOn`.
* `contDiffOn_forcedAmplitude_labelForcing`, `hasDerivAt_forcedAmplitude_labelForcing`: the field
  read at the label from `Ω₀ + ∫ labelForcing` is jointly `C¹` and solves `w_t + Dw v = Dθ e`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric
open scoped NNReal Topology Interval

namespace PDE.Hyperbolic.Transport

open PDE.Analysis.ODE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}

/-! ### Quantities carried by the particles -/

section Carried

/-- The particle of label `y` at time `t` has label `y`. -/
theorem flowOn_zero_flowOn (hv : IsLipschitzFieldOn v a b K) (h0 : (0 : ℝ) ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Icc a b) (y : E) : flowOn v a b 0 t (flowOn v a b t 0 y) = y :=
  hv.flowOn_flowOn_self ht h0 y

/-- The label map `x ↦ flowOn v a b 0 t x` is jointly `C¹` in the point and the time. -/
theorem contDiffOn_flowOn_label (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ flowOn v a b 0 p.2 p.1) (univ ×ˢ Ioo a b) :=
  hv.contDiffOn_flowOn_initial h0

/-- **A carried quantity is jointly `C¹`.** -/
theorem contDiffOn_comp_flowOn (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    {θ₀ : E → F} (hθ₀ : ContDiff ℝ 1 θ₀) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ θ₀ (flowOn v a b 0 p.2 p.1)) (univ ×ˢ Ioo a b) :=
  hθ₀.comp_contDiffOn (contDiffOn_flowOn_label hv h0)

/-- The spatial derivative of a carried quantity is the derivative of `θ₀` at the label
composed with the first variation of the label map. -/
theorem hasFDerivAt_comp_flowOn (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    {θ₀ : E → F} (hθ₀ : Differentiable ℝ θ₀) {t : ℝ} (ht : t ∈ Icc a b) (x : E) :
    HasFDerivAt (fun y ↦ θ₀ (flowOn v a b 0 t y))
      ((fderiv ℝ θ₀ (flowOn v a b 0 t x)).comp (variationOn v Dv a b 0 t x)) x :=
  (hθ₀ _).hasFDerivAt.comp x (hv.hasFDerivAt_flowOn h0 ht x)

/-- The label of the particle at `x` moves with velocity `-J (v t x)` in the time `t`, `J` the
first variation of the label map. -/
theorem hasDerivAt_flowOn_label (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b) {t : ℝ}
    (ht : t ∈ Ioo a b) (x : E) :
    HasDerivAt (fun s ↦ flowOn v a b 0 s x) (-(variationOn v Dv a b 0 t x (v t x))) t :=
  (hv.hasDerivWithinAt_flowOn_initial h0 (Ioo_subset_Icc_self ht) x).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)

/-- **The transport equation.** A carried quantity `θ x t = θ₀ (flowOn v a b 0 t x)` satisfies
`θ_t + Dθ v = 0` at every point and every time of `(a, b)`. -/
theorem hasDerivAt_comp_flowOn_time (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    {θ₀ : E → F} (hθ₀ : Differentiable ℝ θ₀) {t : ℝ} (ht : t ∈ Ioo a b) (x : E) :
    HasDerivAt (fun s ↦ θ₀ (flowOn v a b 0 s x))
      (-(fderiv ℝ (fun y ↦ θ₀ (flowOn v a b 0 t y)) x (v t x))) t := by
  rw [(hasFDerivAt_comp_flowOn hv h0 hθ₀ (Ioo_subset_Icc_self ht) x).fderiv]
  have h := (hθ₀ (flowOn v a b 0 t x)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_flowOn_label hv h0 ht x)
  simpa only [map_neg, ContinuousLinearMap.comp_apply, Function.comp_def] using h

/-- **The gradient identity.** The spatial derivative of a carried quantity at the particle of
label `y`, composed with the first variation along that particle, is the derivative of `θ₀`
at `y`. -/
theorem fderiv_comp_flowOn_comp_variationOn (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    {θ₀ : E → F} (hθ₀ : Differentiable ℝ θ₀) {t : ℝ} (ht : t ∈ Icc a b) (y : E) :
    (fderiv ℝ (fun z ↦ θ₀ (flowOn v a b 0 t z)) (flowOn v a b t 0 y)).comp
      (variationOn v Dv a b t 0 y) = fderiv ℝ θ₀ y := by
  have hL := hv.isLipschitzFieldOn
  have hθ := hasFDerivAt_comp_flowOn hv h0 hθ₀ ht (flowOn v a b t 0 y)
  have hcomp := hθ.comp y (hv.hasFDerivAt_flowOn ht h0 y)
  have hfun : ((fun z ↦ θ₀ (flowOn v a b 0 t z)) ∘ flowOn v a b t 0) = θ₀ :=
    funext fun z ↦ by simp only [Function.comp_apply, flowOn_zero_flowOn hL h0 ht]
  rw [hfun] at hcomp
  rw [hθ.fderiv]
  exact hcomp.unique (hθ₀ y).hasFDerivAt

/-- A carried quantity is `C²` in space when the data and the field are `C²`. -/
theorem contDiff_comp_flowOn {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E} {K₂ : ℝ≥0}
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) {θ₀ : E → F}
    (hθ₀ : ContDiff ℝ 2 θ₀) {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiff ℝ 2 (fun y ↦ θ₀ (flowOn v a b 0 t y)) :=
  hθ₀.comp (hv.contDiff_flowOn h0 ht)

end Carried

/-! ### Forced transport -/

section Forced

variable {Ω : E → ℝ → F} {G : E → ℝ → F}

/-- **A Lagrangian amplitude read at the label is jointly `C¹`.** -/
theorem contDiffOn_comp_flowOn_label (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hΩ : ContDiffOn ℝ 1 (fun p : E × ℝ ↦ Ω p.1 p.2) (univ ×ˢ Ioo a b)) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ Ω (flowOn v a b 0 p.2 p.1) p.2) (univ ×ˢ Ioo a b) :=
  hΩ.comp ((contDiffOn_flowOn_label hv h0).prodMk contDiffOn_snd) fun _ hp ↦ ⟨mem_univ _, hp.2⟩

/-- **The forced transport equation.** If `G y t` is the time derivative of `Ω y` at fixed
label `y`, then `w x t = Ω (flowOn v a b 0 t x) t` satisfies `w_t + Dw v = G` at the label:
`w_t = G (flowOn v a b 0 t x) t - Dw (v t x)`. -/
theorem hasDerivAt_comp_flowOn_label_time (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hΩ : ContDiffOn ℝ 1 (fun p : E × ℝ ↦ Ω p.1 p.2) (univ ×ˢ Ioo a b))
    (hG : ∀ y, ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ Ω y s) (G y t) t) {t : ℝ} (ht : t ∈ Ioo a b)
    (x : E) :
    HasDerivAt (fun s ↦ Ω (flowOn v a b 0 s x) s)
      (G (flowOn v a b 0 t x) t - fderiv ℝ (fun y ↦ Ω (flowOn v a b 0 t y) t) x (v t x)) t := by
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (E × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hdiff : DifferentiableAt ℝ (fun p : E × ℝ ↦ Ω p.1 p.2) (flowOn v a b 0 t x, t) :=
    ((hΩ.contDiffAt (hopen.mem_nhds ⟨mem_univ _, ht⟩)).differentiableAt one_ne_zero)
  obtain ⟨L, hL⟩ : ∃ L, HasFDerivAt (fun p : E × ℝ ↦ Ω p.1 p.2) L (flowOn v a b 0 t x, t) :=
    ⟨_, hdiff.hasFDerivAt⟩
  -- the time derivative of `Ω` at the label is `L (0, 1)`
  have htime : L (0, 1) = G (flowOn v a b 0 t x) t := by
    have h₁ : HasDerivAt (fun s ↦ Ω (flowOn v a b 0 t x) s) (L (0, 1)) t := by
      have h := hL.comp_hasDerivAt (f := fun s ↦ (flowOn v a b 0 t x, s)) t
        (HasDerivAt.prodMk (hasDerivAt_const t (flowOn v a b 0 t x)) (hasDerivAt_id' t))
      simpa only [Function.comp_def] using h
    exact h₁.unique (hG _ t ht)
  -- the spatial derivative of `w t` at `x` is `L (J ·, 0)`
  have hspace : HasFDerivAt (fun z ↦ Ω (flowOn v a b 0 t z) t)
      (L.comp ((ContinuousLinearMap.inl ℝ E ℝ).comp (variationOn v Dv a b 0 t x))) x := by
    have hy : HasFDerivAt (fun z ↦ (flowOn v a b 0 t z, t))
        ((ContinuousLinearMap.inl ℝ E ℝ).comp (variationOn v Dv a b 0 t x)) x := by
      have h := (hv.hasFDerivAt_flowOn h0 (Ioo_subset_Icc_self ht) x).prodMk (hasFDerivAt_const t x)
      convert h using 1
      ext h' <;> simp
    exact hL.comp x hy
  have h : HasDerivAt (fun s ↦ Ω (flowOn v a b 0 s x) s)
      (L (-(variationOn v Dv a b 0 t x (v t x)), 1)) t :=
    hL.comp_hasDerivAt (f := fun s ↦ (flowOn v a b 0 s x, s)) t
      (HasDerivAt.prodMk (hasDerivAt_flowOn_label hv h0 ht x) (hasDerivAt_id' t))
  rw [hspace.fderiv]
  convert h using 1
  have hsplit : ((-(variationOn v Dv a b 0 t x (v t x)), (1 : ℝ)) : E × ℝ) =
      -((variationOn v Dv a b 0 t x (v t x), (0 : ℝ))) + (0, 1) := by simp
  rw [hsplit, map_add, map_neg, htime]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  abel

end Forced

/-! ### Amplitudes integrated along the particles -/

section Amplitude

variable {G : E → ℝ → F} {DG : E → ℝ → E →L[ℝ] F} {Ω₀ : E → F}

/-- The amplitude `Ω₀ y + ∫₀ᵗ G y r dr` of the particle of label `y`, for a forcing `G` given at
the label. -/
def forcedAmplitude (Ω₀ : E → F) (G : E → ℝ → F) (y : E) (t : ℝ) : F :=
  Ω₀ y + ∫ r in (0)..t, G y r

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- A family jointly continuous on `X × [a, b]`, with time clamped to `[a, b]`, is jointly
continuous on `X × ℝ`. -/
private theorem continuous_comp_projIcc {X : Type*} [TopologicalSpace X] {f : X → ℝ → F}
    (hf : ContinuousOn (Function.uncurry f) (univ ×ˢ Icc a b)) (hab : a ≤ b) :
    Continuous fun p : X × ℝ ↦ f p.1 (projIcc a b hab p.2) :=
  hf.comp_continuous (continuous_fst.prodMk
    (continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp continuous_snd)))
    fun p ↦ ⟨mem_univ _, (projIcc a b hab p.2).2⟩

omit [FiniteDimensional ℝ E] in
/-- For `0, t ∈ [a, b]`, composing the integrand with the projection onto `[a, b]` does not change
`∫₀ᵗ f`. -/
private theorem integral_comp_projIcc {f : ℝ → F} (hab : a ≤ b) (h0 : (0 : ℝ) ∈ Icc a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∫ r in (0)..t, f (projIcc a b hab r) = ∫ r in (0)..t, f r :=
  intervalIntegral.integral_congr fun r hr ↦ by
    rw [projIcc_of_mem hab (uIcc_subset_Icc h0 ht hr)]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
/-- **The amplitude solves `∂ₜ Ω = G` at fixed label.** -/
theorem hasDerivAt_forcedAmplitude [CompleteSpace F]
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ Icc a b))
    (h0 : (0 : ℝ) ∈ Icc a b) {t : ℝ} (ht : t ∈ Ioo a b) (y : E) :
    HasDerivAt (fun s ↦ forcedAmplitude Ω₀ G y s) (G y t) t := by
  have hab : a ≤ b := h0.1.trans h0.2
  have hg : Continuous fun r ↦ G y (projIcc a b hab r) :=
    (continuous_comp_projIcc hG hab).comp (continuous_const.prodMk continuous_id)
  have h := (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (Ω₀ y)
  rw [projIcc_of_mem hab (Ioo_subset_Icc_self ht)] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  simp only [forcedAmplitude]
  rw [integral_comp_projIcc (f := G y) hab h0 (Ioo_subset_Icc_self hs)]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ F] in
/-- A function continuous on `[a, b]` is a.e. strongly measurable on the interval between `0` and
`t` when both lie in `[a, b]`. -/
private theorem aestronglyMeasurable_restrict_uIoc {f : ℝ → F} (hf : ContinuousOn f (Icc a b))
    (h0 : (0 : ℝ) ∈ Icc a b) {t : ℝ} (ht : t ∈ Icc a b) :
    MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Ι (0 : ℝ) t)) :=
  (hf.aestronglyMeasurable measurableSet_Icc).mono_set
    (uIoc_subset_uIcc.trans (uIcc_subset_Icc h0 ht))

/-- **Differentiation under the integral sign.** If `G` and its derivative `DG` in the label are
jointly continuous on `E × [a, b]`, the amplitude is differentiable in the label with
derivative `DΩ₀ + ∫₀ᵗ DG`. -/
theorem hasFDerivAt_forcedAmplitude (hΩ₀ : Differentiable ℝ Ω₀)
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ Icc a b))
    (hDG : ∀ r ∈ Icc a b, ∀ y, HasFDerivAt (fun z ↦ G z r) (DG y r) y)
    (hDGc : ContinuousOn (Function.uncurry DG) (univ ×ˢ Icc a b)) (h0 : (0 : ℝ) ∈ Icc a b)
    {t : ℝ} (ht : t ∈ Icc a b) (y : E) :
    HasFDerivAt (fun z ↦ forcedAmplitude Ω₀ G z t) (fderiv ℝ Ω₀ y + ∫ r in (0)..t, DG y r) y := by
  have hsub : uIcc (0 : ℝ) t ⊆ Icc a b := uIcc_subset_Icc h0 ht
  have hGy (z : E) : ContinuousOn (G z) (Icc a b) :=
    hG.comp (continuous_const.prodMk continuous_id).continuousOn fun r hr ↦ ⟨mem_univ _, hr⟩
  have hDGy (z : E) : ContinuousOn (DG z) (Icc a b) :=
    hDGc.comp (continuous_const.prodMk continuous_id).continuousOn fun r hr ↦ ⟨mem_univ _, hr⟩
  obtain ⟨C, hC⟩ := ((isCompact_closedBall y 1).prod isCompact_Icc).exists_bound_of_continuousOn
    (hDGc.mono fun p hp ↦ ⟨mem_univ _, hp.2⟩)
  have hint := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := MeasureTheory.volume) (a := 0) (b := t) (F := G) (F' := DG) (x₀ := y)
    (bound := fun _ ↦ C) (ball_mem_nhds y one_pos)
    (Eventually.of_forall fun z ↦ aestronglyMeasurable_restrict_uIoc (hGy z) h0 ht)
    ((hGy y).mono hsub).intervalIntegrable (aestronglyMeasurable_restrict_uIoc (hDGy y) h0 ht)
    (Eventually.of_forall fun r hr z hz ↦
      hC (z, r) ⟨ball_subset_closedBall hz, hsub (uIoc_subset_uIcc hr)⟩) intervalIntegrable_const
    (Eventually.of_forall fun r hr z _ ↦ hDG r (hsub (uIoc_subset_uIcc hr)) z)
  exact (hΩ₀ y).hasFDerivAt.add hint

/-- **The amplitude is jointly `C¹`** on `E × (a, b)` when `Ω₀` is `C¹` and `G`, `DG` are jointly
continuous on `E × [a, b]`. -/
theorem contDiffOn_forcedAmplitude [CompleteSpace F] (hΩ₀ : ContDiff ℝ 1 Ω₀)
    (hG : ContinuousOn (Function.uncurry G) (univ ×ˢ Icc a b))
    (hDG : ∀ r ∈ Icc a b, ∀ y, HasFDerivAt (fun z ↦ G z r) (DG y r) y)
    (hDGc : ContinuousOn (Function.uncurry DG) (univ ×ˢ Icc a b)) (h0 : (0 : ℝ) ∈ Icc a b) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ forcedAmplitude Ω₀ G p.1 p.2) (univ ×ˢ Ioo a b) := by
  have hab : a ≤ b := h0.1.trans h0.2
  have hprim : Continuous fun p : E × ℝ ↦ ∫ r in (0)..p.2, DG p.1 (projIcc a b hab r) :=
    intervalIntegral.continuous_parametric_primitive_of_continuous
      (f := fun z r ↦ DG z (projIcc a b hab r)) (continuous_comp_projIcc hDGc hab)
  have hD₁ : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ Ω₀ p.1 + ∫ r in (0)..p.2, DG p.1 r)
      (univ ×ˢ Ioo a b) := by
    refine ((hΩ₀.continuous_fderiv one_ne_zero).comp continuous_fst).continuousOn.add ?_
    refine hprim.continuousOn.congr fun p hp ↦ ?_
    exact (integral_comp_projIcc (f := DG p.1) hab h0 (Ioo_subset_Icc_self hp.2)).symm
  have hD₂ : ContinuousOn (fun p : E × ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ (G p.1 p.2))
      (univ ×ˢ Ioo a b) := (ContinuousLinearMap.toSpanSingletonLIE ℝ F).continuous.comp_continuousOn
      (hG.mono fun p hp ↦ ⟨mem_univ _, Ioo_subset_Icc_self hp.2⟩)
  refine PDE.Analysis.contDiffOn_one_of_partial_derivatives (isOpen_univ.prod isOpen_Ioo)
    hD₁ hD₂ (fun p hp ↦ ?_) (fun p hp ↦ ?_)
  · exact hasFDerivAt_forcedAmplitude hΩ₀.differentiable_one hG hDG hDGc h0
      (Ioo_subset_Icc_self hp.2) p.1
  · have h := (hasDerivAt_forcedAmplitude (Ω₀ := Ω₀) hG h0 hp.2 p.1).hasFDerivAt
    exact h

end Amplitude

/-! ### The forcing by the derivative of a carried quantity -/

section LabelForcing

variable {θ₀ : E → F} {e : E}

/-- The forcing at the label `y` and time `r`: the derivative of `θ₀` at `y` applied to `W e`,
where `W = variationOn v Dv a b 0 r (flowOn v a b r 0 y)` inverts the first variation along the
particle of label `y`. It is the derivative in the direction `e` of the carried quantity
`θ₀ (flowOn v a b 0 r ·)` at that particle (`labelForcing_flowOn`). -/
def labelForcing (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E) (a b : ℝ) (θ₀ : E → F) (e y : E)
    (r : ℝ) : F :=
  fderiv ℝ θ₀ y (variationOn v Dv a b 0 r (flowOn v a b r 0 y) e)

/-- The forcing is the derivative in the direction `e` of the carried quantity at the particle
of label `y`. -/
theorem labelForcing_flowOn (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hθ₀ : Differentiable ℝ θ₀) {r : ℝ} (hr : r ∈ Icc a b) (y : E) :
    labelForcing v Dv a b θ₀ e y r =
      fderiv ℝ (fun z ↦ θ₀ (flowOn v a b 0 r z)) (flowOn v a b r 0 y) e := by
  rw [(hasFDerivAt_comp_flowOn hv h0 hθ₀ hr _).fderiv, ContinuousLinearMap.comp_apply,
    flowOn_zero_flowOn hv.isLipschitzFieldOn h0 hr]
  rfl

/-- **The Eulerian form of the forcing**: at the label of the particle at `x`, the forcing is the
derivative of the carried quantity at `x` in the direction `e`. -/
theorem labelForcing_eq (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hθ₀ : Differentiable ℝ θ₀) {r : ℝ} (hr : r ∈ Icc a b) (x : E) :
    labelForcing v Dv a b θ₀ e (flowOn v a b 0 r x) r =
      fderiv ℝ (fun z ↦ θ₀ (flowOn v a b 0 r z)) x e := by
  rw [labelForcing_flowOn hv h0 hθ₀ hr, hv.isLipschitzFieldOn.flowOn_flowOn_self h0 hr]

/-- `(y, r) ↦ variationOn v Dv a b 0 r (flowOn v a b r 0 y)` is jointly continuous. -/
theorem continuousOn_variationOn_label (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b) :
    ContinuousOn (fun p : E × ℝ ↦ variationOn v Dv a b 0 p.2 (flowOn v a b p.2 0 p.1))
      (univ ×ˢ Icc a b) := by
  have hX : ContinuousOn (fun p : E × ℝ ↦ flowOn v a b p.2 0 p.1) (univ ×ˢ Icc a b) :=
    hv.isLipschitzFieldOn.continuousOn_flowOn.comp (f := fun p : E × ℝ ↦ (p.2, 0, p.1))
      (continuous_snd.prodMk (continuous_const.prodMk continuous_fst)).continuousOn
      fun p hp ↦ ⟨hp.2, h0, mem_univ _⟩
  exact hv.continuousOn_variationOn.comp (f := fun p : E × ℝ ↦ (0, p.2, flowOn v a b p.2 0 p.1))
    (continuousOn_const.prodMk (continuousOn_snd.prodMk hX)) fun p hp ↦ ⟨h0, hp.2, mem_univ _⟩

/-- The forcing is jointly continuous on `E × [a, b]`. -/
theorem continuousOn_labelForcing (hv : IsC1FieldOn v Dv a b K) (h0 : (0 : ℝ) ∈ Icc a b)
    (hθ₀ : ContDiff ℝ 1 θ₀) :
    ContinuousOn (fun p : E × ℝ ↦ labelForcing v Dv a b θ₀ e p.1 p.2) (univ ×ˢ Icc a b) :=
  ((hθ₀.continuous_fderiv one_ne_zero).comp continuous_fst).continuousOn.clm_apply
    ((continuousOn_variationOn_label hv h0).clm_apply continuousOn_const)

/-- The derivative of the forcing in the label: with `W` the inverse first variation and `S` the
second variation `secondVariationOn v Dv D2v a b r 0 y`,
`h ↦ D²θ₀(y) h (W e) - Dθ₀(y) (W (S h (W e)))`. -/
def labelForcingDeriv (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E)
    (D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E) (a b : ℝ) (θ₀ : E → F) (e y : E) (r : ℝ) :
    E →L[ℝ] F :=
  (ContinuousLinearMap.apply ℝ F (variationOn v Dv a b 0 r (flowOn v a b r 0 y) e)).comp
      (fderiv ℝ (fderiv ℝ θ₀) y) -
    (fderiv ℝ θ₀ y).comp ((variationOn v Dv a b 0 r (flowOn v a b r 0 y)).comp
      ((ContinuousLinearMap.apply ℝ E (variationOn v Dv a b 0 r (flowOn v a b r 0 y) e)).comp
        (secondVariationOn v Dv D2v a b r 0 y)))

/-- **The forcing is `C¹` in the label**, with derivative `labelForcingDeriv`, for a `C²` field
and `C²` data. -/
theorem hasFDerivAt_labelForcing {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E} {K₂ : ℝ≥0}
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hθ₀ : ContDiff ℝ 2 θ₀)
    {r : ℝ} (hr : r ∈ Icc a b) (y : E) :
    HasFDerivAt (fun z ↦ labelForcing v Dv a b θ₀ e z r)
      (labelForcingDeriv v Dv D2v a b θ₀ e y r) y := by
  have hv1 := hv.toIsC1FieldOn
  have hL := hv1.isLipschitzFieldOn
  have hJ : HasFDerivAt (fun z ↦ variationOn v Dv a b r 0 z)
      (secondVariationOn v Dv D2v a b r 0 y) y := hv.hasFDerivAt_variationOn hr h0 y
  obtain ⟨DW, hW⟩ : ∃ DW, HasFDerivAt (fun z ↦ variationOn v Dv a b 0 r (flowOn v a b r 0 z))
      DW y := ⟨_, (hv.hasFDerivAt_variationOn h0 hr _).comp y (hv1.hasFDerivAt_flowOn hr h0 y)⟩
  have hid (z : E) : (variationOn v Dv a b 0 r (flowOn v a b r 0 z)).comp
      (variationOn v Dv a b r 0 z) = ContinuousLinearMap.id ℝ E :=
    hv1.variationOn_flowOn_comp_variationOn hr h0 z
  have hJW : (variationOn v Dv a b r 0 y).comp
      (variationOn v Dv a b 0 r (flowOn v a b r 0 y)) = ContinuousLinearMap.id ℝ E := by
    have h := hv1.variationOn_flowOn_comp_variationOn h0 hr (flowOn v a b r 0 y)
    rwa [hL.flowOn_flowOn_self hr h0 y] at h
  have hconst : HasFDerivAt (fun z ↦ (variationOn v Dv a b 0 r (flowOn v a b r 0 z)).comp
      (variationOn v Dv a b r 0 z)) (0 : E →L[ℝ] E →L[ℝ] E) y := by
    simp_rw [hid]
    exact hasFDerivAt_const _ _
  have hzero := (hW.clm_comp hJ).unique hconst
  have hDW (h : E) : DW h = -((variationOn v Dv a b 0 r (flowOn v a b r 0 y)).comp
      ((secondVariationOn v Dv D2v a b r 0 y h).comp
        (variationOn v Dv a b 0 r (flowOn v a b r 0 y)))) := by
    have h1 := congrArg (fun L : E →L[ℝ] E →L[ℝ] E ↦ L h) hzero
    simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, zero_apply] at h1
    calc DW h = (DW h).comp ((variationOn v Dv a b r 0 y).comp
          (variationOn v Dv a b 0 r (flowOn v a b r 0 y))) := by
          rw [hJW, ContinuousLinearMap.comp_id]
      _ = ((DW h).comp (variationOn v Dv a b r 0 y)).comp
          (variationOn v Dv a b 0 r (flowOn v a b r 0 y)) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = _ := by
          rw [eq_neg_of_add_eq_zero_right h1, ContinuousLinearMap.neg_comp,
            ContinuousLinearMap.comp_assoc]
  have hD : HasFDerivAt (fderiv ℝ θ₀) (fderiv ℝ (fderiv ℝ θ₀) y) y :=
    ((hθ₀.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero y).hasFDerivAt
  have hG := hD.clm_apply (hW.clm_apply (hasFDerivAt_const e y))
  refine hG.congr_fderiv ?_
  ext h
  simp only [labelForcingDeriv, add_apply, sub_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.apply_apply, hDW, neg_apply, map_neg]
  abel

/-- The derivative of the forcing in the label is jointly continuous on `E × [a, b]`. -/
theorem continuousOn_labelForcingDeriv {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E} {K₂ : ℝ≥0}
    (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hθ₀ : ContDiff ℝ 2 θ₀) :
    ContinuousOn (fun p : E × ℝ ↦ labelForcingDeriv v Dv D2v a b θ₀ e p.1 p.2)
      (univ ×ˢ Icc a b) := by
  have hW := continuousOn_variationOn_label hv.toIsC1FieldOn h0
  have hWe : ContinuousOn (fun p : E × ℝ ↦ variationOn v Dv a b 0 p.2 (flowOn v a b p.2 0 p.1) e)
      (univ ×ˢ Icc a b) := hW.clm_apply continuousOn_const
  have hS : ContinuousOn (fun p : E × ℝ ↦ secondVariationOn v Dv D2v a b p.2 0 p.1)
      (univ ×ˢ Icc a b) :=
    (hv.continuousOn_secondVariationOn_final h0).comp (f := fun p : E × ℝ ↦ (p.2, p.1))
      (continuous_snd.prodMk continuous_fst).continuousOn fun p hp ↦ ⟨hp.2, mem_univ _⟩
  have hD₁ : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ θ₀ p.1) (univ ×ˢ Icc a b) :=
    ((hθ₀.continuous_fderiv two_ne_zero).comp continuous_fst).continuousOn
  have hD₂ : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ (fderiv ℝ θ₀) p.1) (univ ×ˢ Icc a b) :=
    (((hθ₀.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero).comp
      continuous_fst).continuousOn
  have hAF := (ContinuousLinearMap.apply ℝ F).continuous.comp_continuousOn hWe
  have hAE := (ContinuousLinearMap.apply ℝ E).continuous.comp_continuousOn hWe
  exact (hAF.clm_comp hD₂).sub (hD₁.clm_comp (hW.clm_comp (hAE.clm_comp hS)))

/-! ### The forced transport equation with the label forcing -/

/-- **The Eulerian amplitude is jointly `C¹`.** With the label forcing of a `C²` datum `θ₀`
and a `C¹` initial amplitude `Ω₀`, the field
`w x t = Ω₀ (Y) + ∫₀ᵗ labelForcing Y r dr`, `Y = flowOn v a b 0 t x`, is jointly `C¹` on
`E × (a, b)`. -/
theorem contDiffOn_forcedAmplitude_labelForcing [CompleteSpace F]
    {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E} {K₂ : ℝ≥0} (hv : IsC2FieldOn v Dv D2v a b K K₂)
    (h0 : (0 : ℝ) ∈ Icc a b) (hθ₀ : ContDiff ℝ 2 θ₀) {Ω₀ : E → F} (hΩ₀ : ContDiff ℝ 1 Ω₀) :
    ContDiffOn ℝ 1 (fun p : E × ℝ ↦ forcedAmplitude Ω₀ (labelForcing v Dv a b θ₀ e)
      (flowOn v a b 0 p.2 p.1) p.2) (univ ×ˢ Ioo a b) :=
  contDiffOn_comp_flowOn_label hv.toIsC1FieldOn h0
    (contDiffOn_forcedAmplitude (G := labelForcing v Dv a b θ₀ e) hΩ₀
      (continuousOn_labelForcing hv.toIsC1FieldOn h0
      (hθ₀.of_le (by norm_num))) (fun r hr y ↦ hasFDerivAt_labelForcing hv h0 hθ₀ hr y)
      (continuousOn_labelForcingDeriv hv h0 hθ₀) h0)

/-- **The forced transport equation.** The Eulerian amplitude of
`contDiffOn_forcedAmplitude_labelForcing` solves `w_t + Dw v = Dθ e` at every point and every
time of `(a, b)`, where `θ x t = θ₀ (flowOn v a b 0 t x)` is the carried quantity. -/
theorem hasDerivAt_forcedAmplitude_labelForcing [CompleteSpace F] {D2v : ℝ → E → E →L[ℝ] E →L[ℝ] E}
    {K₂ : ℝ≥0} (hv : IsC2FieldOn v Dv D2v a b K K₂) (h0 : (0 : ℝ) ∈ Icc a b) (hθ₀ : ContDiff ℝ 2 θ₀)
    {Ω₀ : E → F} (hΩ₀ : ContDiff ℝ 1 Ω₀) {t : ℝ} (ht : t ∈ Ioo a b) (x : E) :
    HasDerivAt
      (fun s ↦ forcedAmplitude Ω₀ (labelForcing v Dv a b θ₀ e) (flowOn v a b 0 s x) s)
      (fderiv ℝ (fun z ↦ θ₀ (flowOn v a b 0 t z)) x e -
        fderiv ℝ (fun z ↦ forcedAmplitude Ω₀ (labelForcing v Dv a b θ₀ e)
          (flowOn v a b 0 t z) t) x (v t x)) t := by
  have hv1 := hv.toIsC1FieldOn
  have hGc := continuousOn_labelForcing (e := e) hv1 h0 (hθ₀.of_le (by norm_num))
  have h := hasDerivAt_comp_flowOn_label_time hv1 h0
    (contDiffOn_forcedAmplitude (G := labelForcing v Dv a b θ₀ e) hΩ₀ hGc
      (fun r hr y ↦ hasFDerivAt_labelForcing hv h0 hθ₀ hr y)
      (continuousOn_labelForcingDeriv hv h0 hθ₀) h0)
    (fun y t ht ↦ hasDerivAt_forcedAmplitude (G := labelForcing v Dv a b θ₀ e) hGc h0 ht y) ht x
  rwa [labelForcing_eq hv1 h0 (hθ₀.differentiable two_ne_zero) (Ioo_subset_Icc_self ht)] at h

end LabelForcing

end PDE.Hyperbolic.Transport
