/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Causality
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Testing
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.BackwardTest
import PDE.FDeriv.Calculus

/-!
# Identification of classical waves with physical Duhamel evolution

A compact backward Fourier wave tests the classical residual. Its
support is supplied by finite propagation, while L1L2 forcing supplies the
integrability in the Green identity. Uniqueness against compact smooth tests
identifies the classical wave with the real part of the physical L2 forcing
integral plus its real homogeneous Fourier solution.

The field and its first time derivative have continuous closed forward traces.
Second derivatives and the wave equation are needed only in the time interior.
The compared wave has no spatial support or growth assumption. Restricting the
forcing class gives identification at every time of the closed interval,
including time zero.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Fourier

/-- A zero-data classical field whose residual is L1L2 equals the
real part of the physical Duhamel class at the terminal time. Test-wave
integrability is derived, without support or spatial growth of the field. -/
theorem ae_eq_duhamelL2_of_zero_initialData {n : ℕ} [Fact (0 < n)] {b : ℝ} (hb : 0 < b)
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc 0 b))) {u U U₂ : ℝ → ℝ^n → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hzero : ∀ x, u 0 x = 0) (hzero' : ∀ x, U 0 x = 0)
    (hr : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ)) :
    u b =ᵐ[volume] fun x ↦ (duhamelL2 0 b b f x).re := by
  have hub : Continuous (u b) := hu.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨⟨hb.le, le_rfl⟩, mem_univ _⟩)
  have hD : LocallyIntegrable (fun x ↦ (duhamelL2 0 b b f x).re) volume :=
    ((Lp.memLp (duhamelL2 0 b b f)).re).locallyIntegrable (by norm_num)
  apply ae_eq_of_integral_contDiff_smul_eq (hub.locallyIntegrable (μ := volume)) hD
  intro ψ hψ hψc
  let φ : 𝓢(ℝ^n, ℝ) := hψc.toSchwartzMap hψ
  have hφ : HasCompactSupport (φ : ℝ^n → ℝ) := hψc
  have hi := integrable_mul_backwardRealSolution 0 b f φ hr
  have hint := (intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mpr hi
  have hgreen := integral_mul_eq_integral_backwardWave_residual hb φ hφ
    hu hU hU₂ hdu hdU hu₂ hzero hzero' hint
  have htest := re_inner_duhamelL2_realSchwartz_eq_integral 0 b f φ hr
  rw [re_inner_realSchwartz_eq_integral φ _ (Filter.EventuallyEq.rfl)] at htest
  rw [intervalIntegral.integral_of_le hb.le, ← integral_Icc_eq_integral_Ioc] at hgreen
  have hφeq : (φ : ℝ^n → ℝ) = ψ := rfl
  change (∫ x, u b x * (φ : ℝ^n → ℝ) x) = _ at hgreen
  change (∫ x, (φ : ℝ^n → ℝ) x * (duhamelL2 0 b b f x).re) = _ at htest
  rw [hφeq] at hgreen htest
  simpa only [smul_eq_mul, mul_comm] using hgreen.trans htest.symm

/-- A classical forced wave with Schwartz initial data equals the homogeneous
Fourier wave plus the real part of physical Duhamel at the terminal time. -/
theorem ae_eq_realSolution_add_duhamelL2 {n : ℕ} [Fact (0 < n)] {b : ℝ} (hb : 0 < b)
    (g h : 𝓢(ℝ^n, ℝ)) (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc 0 b)))
    {u U U₂ : ℝ → ℝ^n → ℝ} (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ))
    (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hr : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ)) :
    u b =ᵐ[volume] fun x ↦ realSolution g h (timeSpaceCons b x) + (duhamelL2 0 b b f x).re := by
  let Φ := realSolution g h
  let v := fun s x ↦ Φ (timeSpaceCons s x)
  let V := fun s x ↦ (∂[0] Φ) (timeSpaceCons s x)
  let V₂ := fun s x ↦ (∂[0] (∂[0] Φ)) (timeSpaceCons s x)
  have hΦ : ContDiff ℝ 2 Φ := contDiff_two_realSolution g h
  have hΦ' : ContDiff ℝ 1 (∂[0] Φ) := contDiff_partialDeriv_of_succ hΦ
  have hΦ'' : Continuous (∂[0] (∂[0] Φ)) := (contDiff_partialDeriv_of_succ (m := 0) hΦ').continuous
  have ha : Continuous (fun p : ℝ × ℝ^n ↦ timeSpaceCons p.1 p.2) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous
  have hv : Continuous v.uncurry := hΦ.continuous.comp ha
  have hV : Continuous V.uncurry := hΦ'.continuous.comp ha
  have hV₂ : Continuous V₂.uncurry := hΦ''.comp ha
  have hdv (s : ℝ) (x : ℝ^n) : HasDerivAt (fun r ↦ v r x) (V s x) s :=
    hasDerivAt_timeSpaceCons Φ s x (hΦ.differentiable (by norm_num) _)
  have hdV (s : ℝ) (x : ℝ^n) : HasDerivAt (fun r ↦ V r x) (V₂ s x) s :=
    hasDerivAt_timeSpaceCons (∂[0] Φ) s x (hΦ'.differentiable one_ne_zero _)
  have hv₂ (s : ℝ) : ContDiff ℝ 2 (v s) := hΦ.comp (contDiff_timeSpaceCons_spatial n s)
  have hw (s : ℝ) (x : ℝ^n) : V₂ s x = laplacian (v s) x := by
    have he := waveOperator_realSolution g h (timeSpaceCons s x)
    change (∂[0] (∂[0] Φ)) (timeSpaceCons s x) -
      (∑ i : Fin n, (∂[i.succ] (∂[i.succ] Φ)) (timeSpaceCons s x)) = 0 at he
    rw [← laplacian_timeSlice Φ s x hΦ] at he
    exact sub_eq_zero.mp he
  have hres : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦
        ((U₂ s x - V₂ s x - laplacian (fun y ↦ u s y - v s y) x : ℝ) : ℂ) := by
    have hs : ∀ᵐ s ∂volume.restrict (Icc 0 b), s ∈ Ioo 0 b := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hr, hs] with s hsr hs
    filter_upwards [hsr] with x hx
    rw [hx, laplacian_sub (u s) (v s) x (hu₂ s hs).contDiffAt (hv₂ s).contDiffAt, hw]
    congr 1
    abel
  have he := ae_eq_duhamelL2_of_zero_initialData hb f
    (u := fun s x ↦ u s x - v s x) (U := fun s x ↦ U s x - V s x) (U₂ := fun s x ↦ U₂ s x - V₂ s x)
    (hu.sub hv.continuousOn) (hU.sub hV.continuousOn) (hU₂.sub hV₂.continuousOn)
    (fun s hs x ↦ (hdu s hs x).sub (hdv s x)) (fun s hs x ↦ (hdU s hs x).sub (hdV s x))
    (fun s hs ↦ (hu₂ s hs).sub (hv₂ s))
    (fun x ↦ by simp only [v, Φ, hpos, realSolution_initial_position, sub_self])
    (fun x ↦ by simp only [V, Φ, hvel, partialDeriv_realSolution_initial_velocity, sub_self]) hres
  filter_upwards [he] with x hx using (sub_eq_iff_eq_add.mp hx).trans (add_comm _ _)

/-- The same physical forcing class identifies a classical wave at every time
of the closed forward interval, including its initial endpoint. -/
theorem ae_eq_realSolution_add_duhamelL2_on_Icc {n : ℕ} [Fact (0 < n)] {b : ℝ} (g h : 𝓢(ℝ^n, ℝ))
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^n))) 1 (volume.restrict (Icc 0 b))) {u U U₂ : ℝ → ℝ^n → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hr : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ)) :
    ∀ t ∈ Icc 0 b, u t =ᵐ[volume] fun x ↦ realSolution g h (timeSpaceCons t x) +
      (duhamelL2 0 b t f x).re := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    have hD := duhamelL2_eq_zero_of_le (a := 0) (b := b) (t := 0) le_rfl f
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure (ℝ^n)))] with x hx
    simp only [hD, hx, Pi.zero_apply, Complex.zero_re, add_zero, hpos,
      realSolution_initial_position]
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
    have hsub' : Ioo (0 : ℝ) t ⊆ Ioo 0 b := Ioo_subset_Ioo le_rfl ht.2
    have hμ : volume.restrict (Icc (0 : ℝ) t) ≤ volume.restrict (Icc 0 b) :=
      Measure.restrict_mono hsub le_rfl
    let f' := Lp.restrictionCLMOfLE hμ f
    have hforce : ∀ᵐ s ∂volume.restrict (Icc 0 t), (f' s : ℝ^n → ℂ) =ᵐ[volume] fun x ↦
          ((U₂ s x - laplacian (u s) x : ℝ) : ℂ) := by
      filter_upwards [Lp.restrictionCLMOfLE_apply_ae hμ f, ae_mono hμ hr] with s hs hsr
      exact hs ▸ hsr
    have he := ae_eq_realSolution_add_duhamelL2 htp g h f' (hu.mono (Set.prod_mono hsub Subset.rfl))
      (hU.mono (Set.prod_mono hsub Subset.rfl)) (hU₂.mono (Set.prod_mono hsub' Subset.rfl))
      (fun s hs ↦ hdu s (hsub' hs)) (fun s hs ↦ hdU s (hsub' hs))
      (fun s hs ↦ hu₂ s (hsub' hs)) hpos hvel hforce
    have hD : duhamelL2 0 t t f' = duhamelL2 0 b t f :=
      duhamelL2_restrict_right 0 b t t ht.2 le_rfl f
    rwa [hD] at he

end WaveEquation.Fourier
