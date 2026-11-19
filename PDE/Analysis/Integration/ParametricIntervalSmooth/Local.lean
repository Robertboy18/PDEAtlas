/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import PDE.Analysis.Integration.ParametricIntervalSmooth
import PDE.Analysis.Integration.ParametricInterval
import PDE.Analysis.Topology.CompactFamilyBound
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smooth parameter integrals on a closed time interval

Only values on the interval being integrated matter. Joint smoothness on an open
parameter domain times that closed interval suffices; the integrand need not be
smooth outside it. Within-derivatives keep the endpoint hypotheses explicit,
while the parameter derivative is an ordinary Fréchet derivative. The global
regularity theorems specialize these results to the full parameter space. The
final lemma also allows the upper endpoint to vary inside the time interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Analysis

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {U : Set X} {a b : ℝ}

/-- If the integrand and its parameter derivative are jointly continuous on `U ×ˢ uIcc a b`
with `U` open, the interval integral has the integrated derivative as its parameter
derivative at every point of `U`. -/
theorem hasFDerivAt_intervalIntegral_of_continuousOn
    (hU : IsOpen U) {F : X → ℝ → Y} {D : X → ℝ → X →L[ℝ] Y}
    (hF : ContinuousOn F.uncurry (U ×ˢ uIcc a b))
    (hD : ContinuousOn D.uncurry (U ×ˢ uIcc a b))
    (hd : ∀ y ∈ U, ∀ t ∈ uIcc a b, HasFDerivAt (fun z ↦ F z t) (D y t) y)
    {x : X} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, F y t) (∫ t in a..b, D x t) x := by
  have hslice (y : X) (hy : y ∈ U) : ContinuousOn (F y) (uIcc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht ↦ ⟨hy, ht⟩)
  have hsliceD : ContinuousOn (D x) (uIcc a b) :=
    hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht ↦ ⟨hx, ht⟩)
  obtain ⟨V, hV, C, hVU, hC⟩ :=
    hD.exists_bound_nhds_of_isCompact hU isCompact_uIcc hx
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := V) (bound := fun _ ↦ C) hV
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hslice y hy).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  · exact (hslice x hx).intervalIntegrable
  · exact hsliceD.intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  · exact .of_forall fun t ht y hy ↦ hC y hy t (uIoc_subset_uIcc ht)
  · exact intervalIntegrable_const
  · exact .of_forall fun t ht y hy ↦ hd y (hVU hy) t (uIoc_subset_uIcc ht)

/-- The parameter derivative of an integrand smooth only on the closed strip
still differentiates its integral. Equal endpoints give the zero map. -/
theorem hasFDerivAt_intervalIntegral_of_contDiffOn
    (hU : IsOpen U) {H : X × ℝ → Y}
    (hH : ContDiffOn ℝ 1 H (U ×ˢ uIcc a b)) {x : X} (hx : x ∈ U) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, H (y, t))
      (∫ t in a..b,
        (fderivWithin ℝ H (U ×ˢ uIcc a b) (x, t)).comp
          (ContinuousLinearMap.inl ℝ X ℝ)) x := by
  by_cases hab : a = b
  · subst b
    simpa only [intervalIntegral.integral_same] using
      (hasFDerivAt_const (𝕜 := ℝ) (0 : Y) x)
  have hS : UniqueDiffOn ℝ (U ×ˢ uIcc a b) :=
    hU.uniqueDiffOn.prod (uniqueDiffOn_uIcc hab)
  apply hasFDerivAt_intervalIntegral_of_continuousOn
    (F := fun y t ↦ H (y, t))
    (D := fun y t ↦ (fderivWithin ℝ H (U ×ˢ uIcc a b) (y, t)).comp
      (ContinuousLinearMap.inl ℝ X ℝ)) hU hH.continuousOn
    ((hH.continuousOn_fderivWithin hS le_rfl).clm_comp continuousOn_const) ?_ hx
  intro y hy t ht
  have hd := (hH.differentiableOn one_ne_zero (y, t) ⟨hy, ht⟩).hasFDerivWithinAt
  exact hd.comp_hasFDerivAt y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)
    (by filter_upwards [hU.mem_nhds hy] with z hz using ⟨hz, ht⟩)

/-- Differentiating successive parameter derivatives preserves each finite order
of smoothness. The only derivative of the time variable is a within-derivative. -/
private theorem contDiffOn_intervalIntegral_nat
    {Y : Type (max u v)} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hU : IsOpen U) (hab : a ≠ b) {k : ℕ} {H : X × ℝ → Y}
    (hH : ContDiffOn ℝ k H (U ×ˢ uIcc a b)) :
    ContDiffOn ℝ k (fun y ↦ ∫ t in a..b, H (y, t)) U := by
  induction k generalizing Y with
  | zero => exact contDiffOn_zero.mpr (continuousOn_intervalIntegral hH.continuousOn)
  | succ k ih =>
    let D : X × ℝ → X →L[ℝ] Y := fun p ↦
      (fderivWithin ℝ H (U ×ˢ uIcc a b) p).comp (ContinuousLinearMap.inl ℝ X ℝ)
    have hS : UniqueDiffOn ℝ (U ×ˢ uIcc a b) :=
      hU.uniqueDiffOn.prod (uniqueDiffOn_uIcc hab)
    have hD : ContDiffOn ℝ k D (U ×ˢ uIcc a b) :=
      (hH.fderivWithin hS (by simp)).clm_comp contDiffOn_const
    have hi (x : X) (hx : x ∈ U) :=
      hasFDerivAt_intervalIntegral_of_contDiffOn hU (hH.of_le (by simp)) hx
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx ↦ (hi x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact (ih hD).congr fun x hx ↦ (hi x hx).fderiv

/-- Integration preserves finite or infinite joint smoothness on an open
parameter domain times the closed integration interval. Equal endpoints are allowed. -/
theorem contDiffOn_intervalIntegral
    [CompleteSpace Y] (hU : IsOpen U) {n : ℕ∞} {H : X × ℝ → Y}
    (hH : ContDiffOn ℝ n H (U ×ˢ uIcc a b)) :
    ContDiffOn ℝ n (fun y ↦ ∫ t in a..b, H (y, t)) U := by
  by_cases hab : a = b
  · subst b
    simpa only [intervalIntegral.integral_same] using
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : X ↦ (0 : Y)) U)
  let e : ULift.{u} Y ≃ₗᵢ[ℝ] Y := LinearIsometryEquiv.ulift ℝ Y
  have hlift : ContDiffOn ℝ n (fun y ↦ ∫ t in a..b, e.symm (H (y, t))) U := by
    have hH := e.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hH
    induction n using ENat.recTopCoe with
    | top =>
      rw [contDiffOn_infty] at hH ⊢
      exact fun k ↦ contDiffOn_intervalIntegral_nat hU hab (hH k)
    | coe k =>
      exact contDiffOn_intervalIntegral_nat hU hab hH
  have h := e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hlift
  apply h.congr
  intro x _
  simpa only [Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, e.apply_symm_apply] using
    e.toLinearIsometry.intervalIntegral_comp_comm
      (fun t ↦ e.symm (H (x, t))) (a := a) (b := b) (μ := volume)

/-- For a jointly `C¹` integrand, the parameter derivative of its interval integral
is the integral of the partial derivative. Compactness supplies local domination. -/
theorem hasFDerivAt_intervalIntegral_of_contDiff
    {H : X × ℝ → Y} (hH : ContDiff ℝ 1 H) (a b : ℝ) (x : X) :
    HasFDerivAt (fun y ↦ ∫ t in a..b, H (y, t))
      (∫ t in a..b,
        (fderiv ℝ H (x, t)).comp (ContinuousLinearMap.inl ℝ X ℝ)) x := by
  apply hasFDerivAt_intervalIntegral_of_continuousOn
    (U := Set.univ) (a := a) (b := b)
    (F := fun y t ↦ H (y, t))
    (D := fun y t ↦ (fderiv ℝ H (y, t)).comp
      (ContinuousLinearMap.inl ℝ X ℝ))
    isOpen_univ hH.continuous.continuousOn
    ((hH.continuous_fderiv one_ne_zero).clm_comp continuous_const).continuousOn
    ?_ (Set.mem_univ x)
  intro y _ t _
  exact ((hH.differentiable one_ne_zero) (y, t)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t)

/-- Integrating over a fixed compact interval preserves joint `C^n` regularity,
for finite `n` or `n = ∞`. -/
theorem contDiff_intervalIntegral
    [CompleteSpace Y]
    {n : ℕ∞} {H : X × ℝ → Y} (hH : ContDiff ℝ n H) (a b : ℝ) :
    ContDiff ℝ n (fun x ↦ ∫ t in a..b, H (x, t)) := by
  exact contDiffOn_univ.mp
    (contDiffOn_intervalIntegral (U := Set.univ) (a := a) (b := b)
      isOpen_univ hH.contDiffOn)

/-- Differentiate a moving-right-endpoint integral using actual continuous
parameter derivatives on one closed time strip. Either orientation of the
integral is allowed; the parameter derivative is ordinary. -/
theorem hasDerivAt_intervalIntegral_moving_right_of_continuousOn
    {U : Set ℝ} {F D : ℝ → ℝ → ℝ} {L : ℝ → ℝ} {a lo hi p ℓ : ℝ}
    (hU : IsOpen U) (hp : p ∈ U) (ha : a ∈ Icc lo hi)
    (hT : L p ∈ Ioo lo hi)
    (hF : ContinuousOn F.uncurry (U ×ˢ Icc lo hi))
    (hD : ContinuousOn D.uncurry (U ×ˢ Icc lo hi))
    (hd : ∀ q ∈ U, ∀ s ∈ Icc lo hi, HasDerivAt (fun v ↦ F v s) (D q s) q)
    (hL : HasDerivAt L ℓ p) :
    HasDerivAt (fun q ↦ ∫ s in a..L q, F q s)
      (ℓ * F p (L p) + ∫ s in a..L p, D p s) p := by
  have hTc : L p ∈ Icc lo hi := ⟨hT.1.le, hT.2.le⟩
  have hseg : uIcc a (L p) ⊆ Icc lo hi := uIcc_subset_Icc ha hTc
  have hslice (q : ℝ) (hq : q ∈ U) : ContinuousOn (F q) (Icc lo hi) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hs ↦ ⟨hq, hs⟩)
  let J : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun q s ↦ ContinuousLinearMap.toSpanSingleton ℝ (D q s)
  have hJ : ContinuousOn J.uncurry (U ×ˢ Icc lo hi) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn hD
  have hfixed : HasFDerivAt (fun q ↦ ∫ s in a..L p, F q s)
      (∫ s in a..L p, J p s) p :=
    PDE.Analysis.hasFDerivAt_intervalIntegral_of_continuousOn
      (F := F) (D := J) hU
      (hF.mono (fun _ hs ↦ ⟨hs.1, hseg hs.2⟩))
      (hJ.mono (fun _ hs ↦ ⟨hs.1, hseg hs.2⟩))
      (fun q hq s hs ↦ (hd q hq s (hseg hs)).hasFDerivAt) hp
  have hcorner : ContinuousAt F.uncurry (p, L p) :=
    hF.continuousAt (mem_of_superset
      ((hU.prod isOpen_Ioo).mem_nhds ⟨hp, hT⟩)
      (fun _ hs ↦ ⟨hs.1, hs.2.1.le, hs.2.2.le⟩))
  have hmeas : StronglyMeasurableAtFilter (F p) (𝓝 (L p)) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
      ((hslice p hp).mono Ioo_subset_Icc_self) (L p) hT
  have hint : ∀ᶠ q in 𝓝 p,
      IntervalIntegrable (F q) volume a (L p) ∧
        IntervalIntegrable (F q) volume (L p) (L q) ∧
        IntervalIntegrable (F p) volume (L p) (L q) := by
    filter_upwards [hU.mem_nhds hp,
      hL.continuousAt (Icc_mem_nhds hT.1 hT.2)] with q hq hqt
    exact ⟨((hslice q hq).mono hseg).intervalIntegrable,
      ((hslice q hq).mono (uIcc_subset_Icc hTc hqt)).intervalIntegrable,
      ((hslice p hp).mono (uIcc_subset_Icc hTc hqt)).intervalIntegrable⟩
  have hv := PDE.Analysis.hasFDerivAt_intervalIntegral_moving_right
    F a L p hL.hasFDerivAt hfixed hcorner hmeas hint
  have hJint : IntervalIntegrable (J p) volume a (L p) :=
    (hJ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hs ↦ ⟨hp, hseg hs⟩)).intervalIntegrable
  apply hv.hasDerivAt.congr_deriv
  simp only [add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply_one, smul_eq_mul]
  rw [ContinuousLinearMap.intervalIntegral_apply hJint]
  simp only [J, ContinuousLinearMap.toSpanSingleton_apply_one]

end PDE.Analysis
