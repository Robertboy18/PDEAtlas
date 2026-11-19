/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.Calculus.ParametricIntegral.CompactSupport
public import PDE.DistributionTheory.TestFunction.IntegrationByParts
public import PDE.FDeriv.Laplacian.Continuity
public import PDE.FDeriv.Laplacian.Congruence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Green pairing for finite forward wave intervals

For fields `u` and `v` with time derivatives `U`, `V` and second time derivatives
`U₂`, `V₂`, the Green pairing `∫ (U v - u V) dx` has time derivative
`∫ ((U₂ - Δu) v - u (V₂ - Δv)) dx`. Only `v` needs a common compact spatial support;
`u` may grow arbitrarily in space. When `v` solves the free wave equation the second
residual vanishes. On a closed interval the first time derivatives are continuous up
to the endpoints, and second derivatives are needed only in the open interval.
-/

@[expose] public section

open MeasureTheory Filter Set PDE
open scoped Topology

namespace WaveEquation

/-- The time derivative of the Green pairing is the pairing of the two wave residuals.
Only the second field has a common compact spatial support. -/
theorem hasDerivAt_integral_wavePairing_residuals {n : ℕ} {I : Set ℝ} {K : Set (ℝ^n)}
    {u v U V U₂ V₂ : ℝ → ℝ^n → ℝ} (hI : IsOpen I) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (I ×ˢ univ)) (hv : ContinuousOn v.uncurry (I ×ˢ univ))
    (hU : ContinuousOn U.uncurry (I ×ˢ univ)) (hV : ContinuousOn V.uncurry (I ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (I ×ˢ univ)) (hV₂ : ContinuousOn V₂.uncurry (I ×ˢ univ))
    (hdu : ∀ s ∈ I, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdv : ∀ s ∈ I, ∀ x, HasDerivAt (fun r ↦ v r x) (V s x) s)
    (hdU : ∀ s ∈ I, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hdV : ∀ s ∈ I, ∀ x, HasDerivAt (fun r ↦ V r x) (V₂ s x) s)
    (hsupp : ∀ s ∈ I, ∀ x ∉ K, v s x = 0) {t : ℝ} (ht : t ∈ I) (hu₂ : ContDiff ℝ 2 (u t))
    (hv₂ : ContDiff ℝ 2 (v t)) :
    HasDerivAt (fun s ↦ ∫ x, U s x * v s x - u s x * V s x)
      (∫ x, (U₂ t x - laplacian (u t) x) * v t x - u t x * (V₂ t x - laplacian (v t) x)) t := by
  have hVzero (s : ℝ) (hs : s ∈ I) (x : ℝ^n) (hx : x ∉ K) : V s x = 0 := by
    have he : (fun r ↦ v r x) =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hI.mem_nhds hs] with r hr using hsupp r hr x hx
    exact (hdv s hs x).unique ((hasDerivAt_const s 0).congr_of_eventuallyEq he)
  have hd : HasDerivAt (fun s ↦ ∫ x, U s x * v s x - u s x * V s x)
      (∫ x, U₂ t x * v t x - u t x * V₂ t x) t := by
    apply hasDerivAt_integral_of_locally_uniform_compact_support
      (f := fun s x ↦ U s x * v s x - u s x * V s x)
      (D := fun s x ↦ U₂ s x * v s x - u s x * V₂ s x) hI hK
      ((hU.mul hv).sub (hu.mul hV)) ((hU₂.mul hv).sub (hu.mul hV₂)) ?_ ?_ ht
    · intro s hs x
      apply (((hdU s hs x).mul (hdv s hs x)).sub ((hdu s hs x).mul (hdV s hs x))).congr_deriv
      abel
    · intro s hs x hx
      simp only [hsupp s hs x hx, hVzero s hs x hx, mul_zero, sub_self]
  have hV₂zero (s : ℝ) (hs : s ∈ I) (x : ℝ^n) (hx : x ∉ K) : V₂ s x = 0 := by
    have he : (fun r ↦ V r x) =ᶠ[𝓝 s] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hI.mem_nhds hs] with r hr using hVzero r hr x hx
    exact (hdV s hs x).unique ((hasDerivAt_const s 0).congr_of_eventuallyEq he)
  have hcompact : HasCompactSupport (v t) := HasCompactSupport.intro hK (hsupp t ht)
  have hcU₂ : Continuous (U₂ t) :=
    continuousOn_univ.mp (hU₂.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ ↦ ⟨ht, mem_univ x⟩))
  have hA : Integrable (fun x ↦ U₂ t x * v t x) :=
    (hcU₂.mul hv₂.continuous).integrable_of_hasCompactSupport hcompact.mul_left
  have hcV₂ : Continuous (V₂ t) :=
    continuousOn_univ.mp (hV₂.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ ↦ ⟨ht, mem_univ x⟩))
  have hB : Integrable (fun x ↦ u t x * V₂ t x) :=
    (hu₂.continuous.mul hcV₂).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK (hV₂zero t ht)).mul_left
  have hC : Integrable (fun x ↦ laplacian (u t) x * v t x) :=
    Continuous.integrable_of_hasCompactSupport
      (hu₂.continuous_coordinate_laplacian.mul hv₂.continuous) hcompact.mul_left
  have hD : Integrable (fun x ↦ u t x * laplacian (v t) x) :=
    Continuous.integrable_of_hasCompactSupport
      (hu₂.continuous.mul hv₂.continuous_coordinate_laplacian)
      hcompact.coordinate_laplacian.mul_left
  have he : (∫ x, laplacian (u t) x * v t x) =
      ∫ x, u t x * laplacian (v t) x := by
    simpa only [mul_comm] using
      PDE.DistributionTheory.integral_mul_laplacian_eq (u t) hv₂ hu₂ hcompact
  apply hd.congr_deriv
  simp_rw [sub_mul, mul_sub]
  rw [integral_sub hA hB, integral_sub (f := fun x ↦ U₂ t x * v t x - laplacian (u t) x * v t x)
      (g := fun x ↦ u t x * V₂ t x - u t x * laplacian (v t) x) (hA.sub hC) (hB.sub hD),
    integral_sub hA hC, integral_sub hB hD, he]
  abel

/-- The two-field Green identity on `[a, b]`: the time integral of the residual pairing
is the change of the Green pairing. -/
theorem integral_wavePairing_residuals_eq_sub {n : ℕ} {a b : ℝ} {K : Set (ℝ^n)}
    {u v U V U₂ V₂ : ℝ → ℝ^n → ℝ} (hab : a < b) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (Icc a b ×ˢ univ)) (hv : ContinuousOn v.uncurry (Icc a b ×ˢ univ))
    (hU : ContinuousOn U.uncurry (Icc a b ×ˢ univ)) (hV : ContinuousOn V.uncurry (Icc a b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo a b ×ˢ univ))
    (hV₂ : ContinuousOn V₂.uncurry (Ioo a b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdv : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ v r x) (V s x) s)
    (hdU : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hdV : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ V r x) (V₂ s x) s)
    (hsupp : ∀ s ∈ Icc a b, ∀ x ∉ K, v s x = 0) (hu₂ : ∀ s ∈ Ioo a b, ContDiff ℝ 2 (u s))
    (hv₂ : ∀ s ∈ Ioo a b, ContDiff ℝ 2 (v s))
    (hint : IntervalIntegrable (fun s ↦ ∫ x, (U₂ s x - laplacian (u s) x) * v s x - u s x *
      (V₂ s x - laplacian (v s) x)) volume a b) :
    (∫ s in a..b, ∫ x, (U₂ s x - laplacian (u s) x) * v s x - u s x *
      (V₂ s x - laplacian (v s) x)) = (∫ x, U b x * v b x - u b x * V b x) - ∫ x,
      U a x * v a x - u a x * V a x := by
  have hVzero (s : ℝ) (hs : s ∈ Icc a b) (x : ℝ^n) (hx : x ∉ K) :
      V s x = 0 := by
    have hm : MapsTo (fun r ↦ V r x) (Ioo a b) ({0} : Set ℝ) := by
      intro r hr
      have he : (fun t ↦ v t x) =ᶠ[𝓝 r] fun _ ↦ (0 : ℝ) := by
        filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
        exact hsupp t (Ioo_subset_Icc_self ht) x hx
      exact (hdv r hr x).unique ((hasDerivAt_const r 0).congr_of_eventuallyEq he)
    have hc : ContinuousOn (fun r ↦ V r x) (closure (Ioo a b)) := by
      rw [closure_Ioo hab.ne]
      exact hV.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr ↦ ⟨hr, mem_univ x⟩)
    have hs' : s ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    simpa only [isClosed_singleton.closure_eq, mem_singleton_iff] using
      hm.closure_of_continuousOn hc hs'
  have hc : ContinuousOn (fun s ↦ ∫ x, U s x * v s x - u s x * V s x)
      (Icc a b) := by
    apply continuousOn_integral_of_compact_support hK ((hU.mul hv).sub (hu.mul hV))
    intro s x hs hx
    simp only [hsupp s hs x hx, hVzero s hs x hx, mul_zero, sub_self]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hc ?_ hint
  intro s hs
  exact hasDerivAt_integral_wavePairing_residuals isOpen_Ioo hK
    (hu.mono (prod_mono_left Ioo_subset_Icc_self)) (hv.mono (prod_mono_left Ioo_subset_Icc_self))
    (hU.mono (prod_mono_left Ioo_subset_Icc_self))
    (hV.mono (prod_mono_left Ioo_subset_Icc_self)) hU₂ hV₂ hdu hdv hdU hdV
    (fun r hr ↦ hsupp r (Ioo_subset_Icc_self hr)) hs (hu₂ s hs) (hv₂ s hs)

/-- The Green identity on `[a, b]` when `v` has compact spatial support and solves the
free wave equation. -/
theorem integral_wavePairing_derivative_eq_sub {n : ℕ} {a b : ℝ} {K : Set (ℝ^n)}
    {u v U V U₂ V₂ : ℝ → ℝ^n → ℝ} (hab : a < b) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (Icc a b ×ˢ univ)) (hv : ContinuousOn v.uncurry (Icc a b ×ˢ univ))
    (hU : ContinuousOn U.uncurry (Icc a b ×ˢ univ)) (hV : ContinuousOn V.uncurry (Icc a b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo a b ×ˢ univ))
    (hV₂ : ContinuousOn V₂.uncurry (Ioo a b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdv : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ v r x) (V s x) s)
    (hdU : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hdV : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r ↦ V r x) (V₂ s x) s)
    (hsupp : ∀ s ∈ Icc a b, ∀ x ∉ K, v s x = 0) (hu₂ : ∀ s ∈ Ioo a b, ContDiff ℝ 2 (u s))
    (hv₂ : ∀ s ∈ Ioo a b, ContDiff ℝ 2 (v s)) (hw : ∀ s ∈ Ioo a b, ∀ x, V₂ s x = laplacian (v s) x)
    (hint : IntervalIntegrable (fun s ↦ ∫ x, (U₂ s x - laplacian (u s) x) * v s x) volume a b) :
    (∫ s in a..b, ∫ x, (U₂ s x - laplacian (u s) x) * v s x) =
      (∫ x, U b x * v b x - u b x * V b x) - ∫ x, U a x * v a x - u a x * V a x := by
  have he : EqOn (fun s ↦ ∫ x, (U₂ s x - laplacian (u s) x) * v s x -
      u s x * (V₂ s x - laplacian (v s) x))
      (fun s ↦ ∫ x, (U₂ s x - laplacian (u s) x) * v s x) (Ioo a b) := by
    intro s hs
    simp only [hw s hs, sub_self, mul_zero, sub_zero]
  have hi := hint.congr_uIoo (show EqOn _ _ (uIoo a b) from (uIoo_of_le hab.le).symm ▸ he.symm)
  rw [← intervalIntegral.integral_congr_Ioo_of_le hab.le he]
  exact integral_wavePairing_residuals_eq_sub hab hK hu hv hU hV hU₂ hV₂
    hdu hdv hdU hdV hsupp hu₂ hv₂ hi

end WaveEquation
