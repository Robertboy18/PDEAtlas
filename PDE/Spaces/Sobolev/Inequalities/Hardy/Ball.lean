/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Hardy.BallSmooth
public import PDE.Spaces.Sobolev.Inequalities.Hardy.BallBoundary
public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Hardy's inequality for arbitrary H¹ functions on a ball

In dimension at least three, division by the distance to the center maps `H¹(B(0, r))` into
`L²`, with an energy bound whose lower-order term scales as `r⁻²` (Evans, §5.8.4, Theorem 7).
No trace condition is imposed.

## Main results

* `memLp_div_norm_h1_ball`: for `n ≥ 3` and `U ∈ H¹(B(0, r))`, `U/‖x‖ ∈ L²(B(0, r))`.
* `integral_hardy_ball`: for `n ≥ 3`,
  `∫_{B(0, r)} U²/‖x‖² ≤ 2n ∫_{B(0, r)} (‖∇U‖² + U²/r²)`.
* `hardy_ball`: Evans's form of the theorem, with a constant `C > 0` that does not depend on `r`.

## How it works

Evans proves the estimate for smooth `u` by integrating by parts against `x/|x|²` and bounding
the boundary integral by a trace inequality. For smooth data we use instead the regularized
multiplier of `Hardy.BallRegularization`, which vanishes on the sphere, and remove the
regularization in `integrable_hardy_ball_and_bound_of_contDiff`. Smooth approximation up to the
boundary, an a.e. convergent subsequence of the base `L²` representatives, and Fatou's lemma then
extend the estimate to all of `H¹(B(0, r))` (`integrable_hardy_ball_and_bound`). The function and
gradient energies converge separately, so the constant depends only on the dimension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.4, Theorem 7, pp. 296-297.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Metric Filter
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- The gradient energy of the smooth Sobolev constructor is the integral of the
squared operator norm of the classical derivative, on any domain. -/
theorem norm_wkpGradientCLM_mkWkpSpaceOnOfContDiff_sq
    {n : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ‖∇ (mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) f hf hc)‖ ^ 2 =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂domainMeasure n Ω := by
  let U := mkWkpSpaceOnOfContDiff (k := 1) (p := 2) (Ω := Ω) f hf hc
  have hrows : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      (U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) x = (∂[i] f) x := by
    apply ae_all_iff.mpr
    intro i
    simpa only [singleDerivIndex_toList, iteratedPartialDeriv, U] using!
      mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := 2) (Ω := Ω)
        f hf hc (singleDerivIndex n i)
  rw [Lp.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [wkpGradientCLM_apply_ae U, hrows] with x hx hy
  rw [PDE.norm_fderiv_sq_eq_sum_partialDeriv_sq (hf.differentiable (by simp) x),
    EuclideanSpace.real_norm_sq_eq]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun t : ℝ ↦ t ^ 2) ((hx i).trans (hy i))

end SobolevSpace.GraphSpace

namespace SobolevSpace.Hardy

open GraphSpace

variable {n : ℕ}

/-- Full H¹ approximation preserves the singular Hardy estimate and proves
integrability of the limiting inverse-square energy. -/
theorem integrable_hardy_ball_and_bound (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r)
    (U : H¹(ball (0 : ℝ^n) r)) :
    IntegrableOn (fun x ↦ baseRepresentative U x ^ 2 / ‖x‖ ^ 2) (ball (0 : ℝ^n) r) ∧
      (∫ x in ball (0 : ℝ^n) r, baseRepresentative U x ^ 2 / ‖x‖ ^ 2) ≤
        4 * ‖∇ U‖ ^ 2 + 2 * (n : ℝ) / r ^ 2 * ‖wkpBaseCoordinateCLM U‖ ^ 2 := by
  obtain ⟨f, hf, hc, happ⟩ := Approximation.UpToBoundary.smooth_approximation
    isOpen_ball isBounded_ball
    (Boundary.hasC1Boundary_ball 0 hr) (by simp) U
  let V (k : ℕ) : H¹(ball (0 : ℝ^n) r) :=
    mkWkpSpaceOnOfContDiff (f k) (hf k) (hc k)
  have hV : Tendsto V atTop (𝓝 U) := tendsto_iff_norm_sub_tendsto_zero.mpr happ
  have hbase : Tendsto (fun k ↦ wkpBaseCoordinateCLM (V k)) atTop
      (𝓝 (wkpBaseCoordinateCLM U)) :=
    wkpBaseCoordinateCLM.continuous.continuousAt.tendsto.comp hV
  have hgrad : Tendsto (fun k ↦ ∇ (V k)) atTop (𝓝 (∇ U)) :=
    wkpGradientCLM.continuous.continuousAt.tendsto.comp hV
  have hrep (k : ℕ) : (wkpBaseCoordinateCLM (V k) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball 0 r)] f k :=
    wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (hf k) (hc k)
  have hfunEnergy (k : ℕ) :
      (∫ x in ball (0 : ℝ^n) r, f k x ^ 2) = ‖wkpBaseCoordinateCLM (V k)‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    exact integral_congr_ae ((hrep k).fun_comp (fun t : ℝ ↦ t ^ 2)).symm
  have hgradEnergy (k : ℕ) :
      (∫ x in ball (0 : ℝ^n) r, ‖fderiv ℝ (f k) x‖ ^ 2) = ‖∇ (V k)‖ ^ 2 :=
    (norm_wkpGradientCLM_mkWkpSpaceOnOfContDiff_sq (hf k) (hc k)).symm
  obtain ⟨s, hs, hsub⟩ := (tendstoInMeasure_of_tendsto_Lp hbase).exists_seq_tendsto_ae
  apply integrable_and_integral_le_of_ae_limit_nonneg_of_tendsto_bound
    (u := fun k x ↦ f (s k) x ^ 2 / ‖x‖ ^ 2)
    (b := fun k ↦ 4 * ‖∇ (V (s k))‖ ^ 2 +
      2 * (n : ℝ) / r ^ 2 * ‖wkpBaseCoordinateCLM (V (s k))‖ ^ 2)
  · intro k
    exact (integrable_hardy_ball_and_bound_of_contDiff hn ((hf (s k)).of_le (by simp)) hr).1
  · intro k
    exact Eventually.of_forall fun x ↦ div_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro k
    simpa only [hfunEnergy, hgradEnergy] using
      (integrable_hardy_ball_and_bound_of_contDiff hn ((hf (s k)).of_le (by simp)) hr).2
  · exact (((hgrad.comp hs.tendsto_atTop).norm.pow 2).const_mul 4).add
      (((hbase.comp hs.tendsto_atTop).norm.pow 2).const_mul (2 * (n : ℝ) / r ^ 2))
  · have hall := ae_all_iff.mpr hrep
    filter_upwards [hsub, hall] with x hx hy
    have hfx : Tendsto (fun k ↦ f (s k) x) atTop (𝓝 (baseRepresentative U x)) := by
      simp only [hy] at hx
      simpa only [baseRepresentative, wkpBaseCoordinateCLM_apply] using! hx
    exact (hfx.pow 2).div_const (‖x‖ ^ 2)

/-- The integrability part of Evans §5.8.4, Theorem 7: for `n ≥ 3`, `0 < r` and
`U ∈ H¹(B(0, r))`, the quotient `U/‖x‖` is in `L²(B(0, r))`. -/
theorem memLp_div_norm_h1_ball (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r)
    (U : H¹(ball (0 : ℝ^n) r)) :
    MemLp (fun x ↦ baseRepresentative U x / ‖x‖) 2 (domainMeasure n (ball 0 r)) := by
  have hm : AEStronglyMeasurable (fun x ↦ baseRepresentative U x / ‖x‖)
      (domainMeasure n (ball 0 r)) :=
    ((Lp.aestronglyMeasurable (wkpBaseCoordinateCLM U)).aemeasurable.div
      continuous_norm.measurable.aemeasurable).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [div_pow] using! (integrable_hardy_ball_and_bound hn hr U).1

/-- Hardy's inequality on a ball with the radius-independent constant `2 * n`: for `n ≥ 3`,
`0 < r` and `U ∈ H¹(B(0, r))`, `∫_{B(0, r)} U²/‖x‖² ≤ 2n ∫_{B(0, r)} (‖∇U‖² + U²/r²)`. -/
theorem integral_hardy_ball (hn : 3 ≤ n) {r : ℝ} (hr : 0 < r)
    (U : H¹(ball (0 : ℝ^n) r)) :
    (∫ x in ball (0 : ℝ^n) r, baseRepresentative U x ^ 2 / ‖x‖ ^ 2) ≤
      2 * (n : ℝ) * ∫ x in ball (0 : ℝ^n) r,
        (‖∇ U x‖ ^ 2 + baseRepresentative U x ^ 2 / r ^ 2) := by
  have hU : Integrable (fun x ↦ wkpBaseCoordinateCLM U x ^ 2)
      (domainMeasure n (ball 0 r)) := (Lp.memLp (wkpBaseCoordinateCLM U)).integrable_sq
  have hG : Integrable (fun x ↦ ‖∇ U x‖ ^ 2) (domainMeasure n (ball 0 r)) :=
    (Lp.memLp (∇ U)).norm.integrable_sq
  have heq : (∫ x in ball (0 : ℝ^n) r,
      (‖∇ U x‖ ^ 2 + baseRepresentative U x ^ 2 / r ^ 2)) =
        ‖∇ U‖ ^ 2 + ‖wkpBaseCoordinateCLM U‖ ^ 2 / r ^ 2 := by
    change (∫ x, (‖∇ U x‖ ^ 2 + (wkpBaseCoordinateCLM U x) ^ 2 / r ^ 2)
      ∂domainMeasure n (ball 0 r)) = _
    rw [integral_add hG (hU.div_const _), integral_div,
      ← Lp.norm_sq_eq_integral_norm_sq, ← Lp.norm_sq_eq_integral_sq]
  rw [heq]
  have h := (integrable_hardy_ball_and_bound hn hr U).2
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnonneg := mul_nonneg (show 0 ≤ 2 * (n : ℝ) - 4 by linarith) (sq_nonneg ‖∇ U‖)
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith

/-- Evans §5.8.4, Theorem 7: for `n ≥ 3` there is `C > 0` such that for every `r > 0` and
`U ∈ H¹(B(0, r))`, `U/‖x‖ ∈ L²(B(0, r))` and
`∫_{B(0, r)} U²/‖x‖² ≤ C ∫_{B(0, r)} (‖∇U‖² + U²/r²)`. -/
theorem hardy_ball (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ U : H¹(ball (0 : ℝ^n) r),
      MemLp (fun x ↦ baseRepresentative U x / ‖x‖) 2 (domainMeasure n (ball 0 r)) ∧
        (∫ x in ball (0 : ℝ^n) r, baseRepresentative U x ^ 2 / ‖x‖ ^ 2) ≤
          C * ∫ x in ball (0 : ℝ^n) r,
            (‖∇ U x‖ ^ 2 + baseRepresentative U x ^ 2 / r ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  refine ⟨2 * (n : ℝ), by positivity, fun r hr U ↦ ?_⟩
  exact ⟨memLp_div_norm_h1_ball hn hr U, integral_hardy_ball hn hr U⟩

end SobolevSpace.Hardy
