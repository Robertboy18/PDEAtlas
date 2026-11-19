/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Inequalities.Morrey.BallAverage
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import CAS.ExactTactic

/-!
# Differentiability at Lebesgue points of a supercritical weak gradient

Subtract the affine function with slope equal to the weak gradient at the center.
The local Morrey estimate bounds the resulting first-order remainder by its radius
times the scaled `Lᵖ` oscillation of the weak gradient. Lebesgue differentiation makes
that factor vanish. This proves Evans, §5.8.3, Theorem 5 for finite exponents, with
the derivative identified as the weak gradient.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.3, Theorem 5, pp. 295-296: for `n < p ≤ ∞`, every
  `u ∈ W^{1,p}_loc(U)` is differentiable almost everywhere and its gradient equals its weak gradient
  almost everywhere; the proof uses Morrey's estimate (14) and Lebesgue's differentiation theorem.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology Sobolev

namespace SobolevSpace

open GraphSpace

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ} {g : ℝ^n → ℝ^n}

/-- A continuous Sobolev representative is differentiable at every `Lᵖ` Lebesgue point
of its weak gradient when `p > n`. Its derivative is the linear functional given by
that gradient. The oscillation limit is obtained almost everywhere in the next theorem. -/
theorem hasFDerivAt_of_tendsto_weakGradient_oscillation
    (hp : (n : ℝ≥0∞) < p) (hΩ : IsOpen Ω)
    (hfc : ContinuousOn f Ω) (hf : MemLp f p (domainMeasure n Ω))
    (hg : MemLp g p (domainMeasure n Ω))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun y ↦ g y i))
    {x : ℝ^n} (hx : x ∈ Ω)
    (hlim : Tendsto
      (fun r : ℝ ↦ MeanScaling.normFactor n r p *
        (eLpNorm (fun y ↦ g y - g x) p (volume.restrict (ball x r))).toReal)
      (𝓝[>] 0) (𝓝 0)) :
    HasFDerivAt f (innerSL ℝ (g x)) x := by
  let L : (ℝ^n) →L[ℝ] ℝ := innerSL ℝ (g x)
  obtain ⟨C, hC, hosc⟩ := exists_oscillation_bound_ball hp
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsmall := (tendsto_order.mp hlim).2 (ε / (2 * (C + 1)))
    (div_pos hε (by positivity))
  obtain ⟨δ, hδ, hδsmall⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hsmall
  change 0 < δ at hδ
  have hrad : 0 < min ρ δ / 4 := by positivity
  filter_upwards [ball_mem_nhds x hrad] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let r := 2 * ‖y - x‖
  have hr : 0 < r := by positivity
  have hry : r < min ρ δ := by
    have hdist : ‖y - x‖ < min ρ δ / 4 := by simpa only [mem_ball, dist_eq_norm] using hy
    dsimp [r]
    linarith
  have hrρ : r < ρ := hry.trans_le (min_le_left _ _)
  have hrδ : r ≤ δ := hry.le.trans (min_le_right _ _)
  have hsub : ball x r ⊆ Ω := (ball_subset_ball hrρ.le).trans hball
  have hfr : MemLp f p (domainMeasure n (ball x r)) :=
    hf.mono_measure (domainMeasure_le hsub)
  have hgr : MemLp g p (domainMeasure n (ball x r)) :=
    hg.mono_measure (domainMeasure_le hsub)
  have : IsFiniteMeasure (domainMeasure n (ball x r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hLmem : MemLp L p (domainMeasure n (ball x r)) :=
    L.continuous.continuousOn.memLp_of_subset_isCompact (isCompact_closedBall x r)
      measurableSet_ball ball_subset_closedBall
  have hLweak (i : Fin n) :
      HasWeakDerivativeOn (ball x r) [i] L (fun _ ↦ g x i) := by
    have h := hasWeakDerivativeOn_iteratedPartialDeriv_finite (Ω := ball x r) [i]
      L.contDiff
    change HasWeakDerivativeOn (ball x r) [i] L
      (fun z ↦ fderiv ℝ L z (EuclideanSpace.single i 1)) at h
    simp only [L.hasFDerivAt.fderiv] at h
    simpa only [L, innerSL_apply_apply, EuclideanSpace.inner_single_right,
      one_mul, starRingEnd_apply, star_trivial] using h
  obtain ⟨V, hVbase, hVgrad⟩ := exists_of_weakGradient (hfr.sub hLmem)
    (hgr.sub (memLp_const (g x))) (fun i ↦
      hasWeakDerivativeOn_sub [i]
        (HasWeakDerivativeOn.mono measurableSet_ball hsub (hweak i)) (hLweak i))
  have hbound := hosc x r hr V (fun z ↦ f z - L z)
    ((hfc.mono hsub).sub L.continuous.continuousOn) hVbase.symm y
    (show y ∈ ball x r from by simp only [mem_ball, dist_eq_norm]; dsimp [r]; linarith)
    x (mem_ball_self hr)
  have hnorm : ‖∇ V‖ =
      (eLpNorm (fun z ↦ g z - g x) p (volume.restrict (ball x r))).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hVgrad]
    rfl
  rw [hnorm] at hbound
  have hsmallr : MeanScaling.normFactor n r p *
      (eLpNorm (fun z ↦ g z - g x) p (volume.restrict (ball x r))).toReal <
        ε / (2 * (C + 1)) := hδsmall ⟨hr, hrδ⟩
  have hrem : f y - f x - L (y - x) = (f y - L y) - (f x - L x) := by
    rw [map_sub]
    abel
  change ‖f y - f x - L (y - x)‖ ≤ ε * ‖y - x‖
  rw [hrem]
  apply hbound.trans
  have hCsmall : C * (ε / (2 * (C + 1))) ≤ ε / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hratio : C / (C + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      C * (ε / (2 * (C + 1))) * 2 = ε * (C / (C + 1)) := by cas
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hratio hε.le
      _ = ε := mul_one ε
  calc
    C * MeanScaling.normFactor n r p *
        (r * (eLpNorm (fun z ↦ g z - g x) p (volume.restrict (ball x r))).toReal) =
      (C * (MeanScaling.normFactor n r p *
        (eLpNorm (fun z ↦ g z - g x) p (volume.restrict (ball x r))).toReal)) * r := by
          ring
    _ ≤ (C * (ε / (2 * (C + 1)))) * r := by gcongr
    _ ≤ (ε / 2) * r := mul_le_mul_of_nonneg_right hCsmall hr.le
    _ = ε * ‖y - x‖ := by dsimp [r]; cas

/-- A continuous `W¹ᵖ` representative on an arbitrary open domain is differentiable
almost everywhere for `n < p < ∞`, with classical derivative equal to its weak gradient. -/
theorem ae_hasFDerivAt_of_continuousOn_weakGradient
    (hp : (n : ℝ≥0∞) < p) (hp_top : p ≠ ∞) (hΩ : IsOpen Ω)
    (hfc : ContinuousOn f Ω) (hf : MemLp f p (domainMeasure n Ω))
    (hg : MemLp g p (domainMeasure n Ω))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun y ↦ g y i)) :
    ∀ᵐ x ∂domainMeasure n Ω, HasFDerivAt f (innerSL ℝ (g x)) x := by
  have hp₀ : p ≠ 0 := ne_of_gt ((show (0 : ℝ≥0∞) ≤ n from bot_le).trans_lt hp)
  filter_upwards [MeanScaling.ae_tendsto_normFactor_mul_eLpNorm_sub_on hp₀ hp_top hΩ hg,
    ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  exact hasFDerivAt_of_tendsto_weakGradient_oscillation hp hΩ hfc hf hg hweak hxΩ hx

end SobolevSpace
