/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives

/-!
# Zero weak gradient on a connected domain

An integrable function whose weak coordinate derivatives vanish on a connected open set
is constant almost everywhere there. The proof uses interior mollification along a compact
path joining two points. For sufficiently small kernels, the mollification has zero classical
gradient on a connected neighborhood of that path. Almost-everywhere convergence of normalized
bump convolutions then identifies the original function with a constant.

This is the step "`v` is constant, since `U` is connected" in the proof by contradiction of
Poincaré's inequality, Evans §5.8.1, Theorem 1, which Evans leaves to Problem 11.
No continuity of the original function or boundary regularity is required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.1, proof of Theorem 1, p. 290.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Convolution Topology

namespace SobolevSpace

open Approximation

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

private theorem eventually_convolution_eq_of_weak_gradient_zero
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IntegrableOn f Ω)
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] f 0)
    {φ : ℕ → ContDiffBump (0 : ℝ^n)}
    (hφ : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0))
    {x y : ℝ^n} (hx : x ∈ Ω) (hy : y ∈ Ω) :
    ∀ᶠ k in atTop,
      ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Ω.indicator f) x =
      ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Ω.indicator f) y := by
  have hpath := (hΩ.isConnected_iff_isPathConnected.mp hconn).joinedIn x hx y hy
  let K := Set.range hpath.somePath
  have hK : IsCompact K := isCompact_range hpath.somePath.continuous
  have hKconn : IsPreconnected K :=
    (isConnected_range hpath.somePath.continuous).isPreconnected
  have hxK : x ∈ K := ⟨0, hpath.somePath.source⟩
  have hyK : y ∈ K := ⟨1, hpath.somePath.target⟩
  have hKΩ : K ⊆ Ω := by
    rintro _ ⟨t, rfl⟩
    exact hpath.somePath_mem t
  obtain ⟨V, hV, hKV, hclVΩ, hclV⟩ :=
    exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨δ, hδ, hδΩ⟩ := hclV.exists_cthickening_subset_open hΩ hclVΩ
  have hKC : K ⊆ connectedComponentIn V x :=
    hKconn.subset_connectedComponentIn hxK hKV
  have hF : LocallyIntegrable (Ω.indicator f) volume :=
    (hf.integrable_indicator hΩ.measurableSet).locallyIntegrable
  filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with k hk
  let μ : Approximation.Mollifier n :=
    { ρ := (φ k).normed volume
      smooth := (φ k).contDiff_normed
      compactSupport := (φ k).hasCompactSupport_normed
      nonneg := (φ k).nonneg_normed
      integral_one := (φ k).integral_normed }
  have hmoll :
      Approximation.mollify μ 1 (Ω.indicator f) =
        ((φ k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          Ω.indicator f) := by
    have hscaled : Approximation.scaled μ 1 = (φ k).normed volume := by
      rw [Approximation.scaled_of_pos μ zero_lt_one]
      simp [μ]
    simp only [Approximation.mollify, hscaled]
  have hsmooth := Approximation.mollify_contDiff_of_pos μ zero_lt_one
    (Ω.indicator f) hF
  have hderiv : V.EqOn (fderiv ℝ (Approximation.mollify μ 1 (Ω.indicator f))) 0 := by
    intro z hz
    have hball : Metric.closedBall z (1 * (φ k).rOut) ⊆ Ω := by
      refine (Metric.closedBall_subset_closedBall (by simpa using hk.le)).trans ?_
      exact (Metric.closedBall_subset_cthickening (subset_closure hz) δ).trans hδΩ
    have hpartial (i : Fin n) :
        (∂[i] (Approximation.mollify μ 1 (Ω.indicator f))) z = 0 := by
      have h :=
        iteratedPartialDeriv_mollify_indicator_eq_mollify_indicator_of_hasWeakDerivativeOn
          μ zero_lt_one
          (show tsupport μ.ρ ⊆ Metric.closedBall 0 (φ k).rOut by
            simpa [μ] using (φ k).tsupport_normed_eq (μ := volume) |>.subset)
          (by simp : [i] ≠ []) hF (hweak i) z hball
      change (∂[i] (Approximation.mollify μ 1 (Ω.indicator f))) z =
        Approximation.mollify μ 1 (Ω.indicator 0) z at h
      have hzero : Approximation.mollify μ 1 (Ω.indicator 0) z = 0 := by
        simp [Approximation.mollify, convolution_def]
      exact h.trans hzero
    ext v
    rw [PDE.fderiv_apply_eq_sum_smul_partialDeriv]
    simp [hpartial]
  rw [← hmoll]
  exact hV.connectedComponentIn.is_const_of_fderiv_eq_zero
    isPreconnected_connectedComponentIn
    (hsmooth.differentiable (by simp)).differentiableOn
    (hderiv.mono (connectedComponentIn_subset V x)) (hKC hxK) (hKC hyK)

/-- If `Ω` is open and connected, `f` is integrable on `Ω` and every weak first derivative of `f`
on `Ω` is zero, then `f` is almost everywhere equal on `Ω` to a constant. The conclusion concerns
`f` itself, not a chosen representative. -/
theorem exists_ae_eq_const_of_weak_gradient_zero
    (hΩ : IsOpen Ω) (hconn : IsConnected Ω)
    (hf : IntegrableOn f Ω)
    (hweak : ∀ i, HasWeakDerivativeOn Ω [i] f 0) :
    ∃ c : ℝ, f =ᵐ[volume.restrict Ω] fun _ ↦ c := by
  let r : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hr (k : ℕ) : 0 < r k := by
    dsimp only [r]
    positivity
  let φ : ℕ → ContDiffBump (0 : ℝ^n) := fun k ↦
    { rIn := r k
      rOut := 2 * r k
      rIn_pos := hr k
      rIn_lt_rOut := by linarith [hr k] }
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hout : Tendsto (fun k ↦ (φ k).rOut) atTop (𝓝 0) := by
    simpa only [φ, mul_zero] using tendsto_const_nhds.mul hr0
  have hF : LocallyIntegrable (Ω.indicator f) volume :=
    (hf.integrable_indicator hΩ.measurableSet).locallyIntegrable
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    hout (Eventually.of_forall fun _ ↦ le_rfl) hF
  obtain ⟨x, hx, hfx⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (hΩ.measure_pos volume hconn.nonempty).ne' (ae_restrict_of_ae hae)
  refine ⟨f x, ?_⟩
  filter_upwards [ae_restrict_of_ae hae, self_mem_ae_restrict hΩ.measurableSet] with y hfy hy
  have heq := eventually_convolution_eq_of_weak_gradient_zero hΩ hconn hf hweak hout hy hx
  have hy' := hfy.congr' heq
  simpa only [Set.indicator_of_mem hx, Set.indicator_of_mem hy] using
    tendsto_nhds_unique hy' hfx

end SobolevSpace
