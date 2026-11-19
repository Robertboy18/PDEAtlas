/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Weak.Divergence
public import PDE.Hyperbolic.HamiltonJacobi.Weak.GradientConvergence

/-!
# Convergence and bounds for the Hamilton–Jacobi drift

The regularized drift converges almost everywhere to the average of
`DH` between the two spatial gradients. Its norm is uniformly bounded by
a constant obtained from compactness of the gradient ball. These conclusions
require only a `C¹` Hamiltonian and forward Lipschitz inputs. In the proof of Theorem 7 in
Evans, §3.3.3(b), they are the convergence `b_ε → b` used in step 6 and the cone speed (47).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, steps 4 and 6, equations
  (44) and (47).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Filter Metric Set
open scoped Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- The vector drift in the difference equation of two weak solutions. -/
def drift (H : E → ℝ) (u v : E × ℝ → ℝ) (z : E × ℝ) : E :=
  ∫ r in (0 : ℝ)..1, ∇ H
    (r • ∇ (fun x ↦ u (x, z.2)) z.1 +
      (1 - r) • ∇ (fun x ↦ v (x, z.2)) z.1)

/-- Averaging `DH` along a segment depends continuously on both endpoints. -/
theorem continuous_integral_gradient_segment {H : E → ℝ} (hH : ContDiff ℝ 1 H) :
    Continuous (fun p : E × E ↦ ∫ r in (0 : ℝ)..1, ∇ H (r • p.1 + (1 - r) • p.2)) := by
  have hg : Continuous (∇ H) := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hH.continuous_fderiv one_ne_zero)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hg.comp ((continuous_snd.smul continuous_fst.fst).add
    ((continuous_const.sub continuous_snd).smul continuous_fst.snd))

/-- Convergence of both endpoints implies convergence of their averaged
Hamiltonian gradient. -/
theorem tendsto_integral_gradient_segment {H : E → ℝ} (hH : ContDiff ℝ 1 H) {ι : Type*}
    {l : Filter ι} {p q : ι → E} {p₀ q₀ : E} (hp : Tendsto p l (𝓝 p₀)) (hq : Tendsto q l (𝓝 q₀)) :
    Tendsto (fun i ↦ ∫ r in (0 : ℝ)..1, ∇ H (r • p i + (1 - r) • q i))
      l (𝓝 (∫ r in (0 : ℝ)..1, ∇ H (r • p₀ + (1 - r) • q₀))) := by
  have hcont := (continuous_integral_gradient_segment hH).tendsto (p₀, q₀)
  have hpair := hp.prodMk_nhds hq
  have h := hcont.comp hpair
  exact h

/-- Compactness supplies the speed bound on every ball of gradients; it is
not a global bound on the Hamiltonian derivative. -/
theorem exists_norm_gradient_bound_closedBall {H : E → ℝ} (hH : ContDiff ℝ 1 H) (K : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p, ‖p‖ ≤ K → ‖∇ H p‖ ≤ R := by
  have hg : Continuous (∇ H) := (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hH.continuous_fderiv one_ne_zero)
  obtain ⟨R, hR⟩ := (isCompact_closedBall (0 : E) K).exists_bound_of_continuousOn hg.continuousOn
  exact ⟨max 0 R, le_max_left _ _, fun p hp ↦
    (hR p (by simpa using hp)).trans (le_max_right _ _)⟩

/-- An average of `DH` over a segment in the gradient ball obeys the same
speed bound as `DH` on that ball. -/
theorem norm_integral_gradient_segment_le {H : E → ℝ} {K R : ℝ} (hH : ∀ p, ‖p‖ ≤ K → ‖∇ H p‖ ≤ R)
    {p q : E} (hp : ‖p‖ ≤ K) (hq : ‖q‖ ≤ K) :
    ‖∫ r in (0 : ℝ)..1, ∇ H (r • p + (1 - r) • q)‖ ≤ R := by
  have hbound (r : ℝ) (hr : r ∈ Set.uIoc (0 : ℝ) 1) :
      ‖∇ H (r • p + (1 - r) • q)‖ ≤ R := by
    have hr' : r ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le zero_le_one] using uIoc_subset_uIcc hr
    apply hH
    have hmem := convex_closedBall (0 : E) K
      (by simpa using hp : p ∈ closedBall 0 K)
      (by simpa using hq : q ∈ closedBall 0 K) hr'.1 (sub_nonneg.mpr hr'.2) (add_sub_cancel _ _)
    simpa using hmem
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- The totalized spatial gradient is bounded by the forward Lipschitz
constant, including points where the slice is not differentiable. -/
theorem norm_gradient_spatial_le_of_lipschitzOn_forward {u : E × ℝ → ℝ} {K : NNReal}
    (hu : LipschitzOnWith K u {z | 0 ≤ z.2}) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    ‖∇ (fun y ↦ u (y, t)) x‖ ≤ K := by
  have hslice : LipschitzWith K (fun y ↦ u (y, t)) := by
    refine LipschitzWith.of_dist_le_mul fun y z ↦ ?_
    simpa using hu.dist_le_mul (y, t) ht (z, t) ht
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hslice

variable [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- The regularized drifts converge almost everywhere at positive
times. Continuity of the segment integral upgrades convergence of its two
gradient endpoints to convergence of the vector drift. -/
theorem ae_tendsto_mollifiedDrift {H : E → ℝ} (hH : ContDiff ℝ 1 H) {u v : E × ℝ → ℝ}
    {Ku Kv : NNReal} (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2})
    (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) {ι : Type*} {φ : ι → ContDiffBump (0 : E × ℝ)}
    {l : Filter ι} {A : ℝ} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn) :
    ∀ᵐ z ∂μ.restrict {z : E × ℝ | 0 < z.2},
      Tendsto (fun i ↦ mollifiedDrift (μ := μ) H (φ i) u v z) l (𝓝 (drift H u v z)) := by
  filter_upwards [ae_tendsto_gradient_convolution_forwardExtension hu hφ hφ_ratio
    (μ := μ), ae_tendsto_gradient_convolution_forwardExtension hv hφ hφ_ratio (μ := μ)]
    with z hzu hzv
  exact tendsto_integral_gradient_segment hH hzu hzv

/-- A single speed bound controls both the drift and every mollified
drift beyond its kernel radius. The constant is derived from `H` on the ball
of radius `max (Lip u) (Lip v)`, as for the cone speed (47) in the proof of Evans, §3.3.3(b),
Theorem 7. -/
theorem exists_norm_drift_le {H : E → ℝ} (hH : ContDiff ℝ 1 H) {u v : E × ℝ → ℝ} {Ku Kv : NNReal}
    (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2}) (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) :
    ∃ R : ℝ, 0 ≤ R ∧ (∀ x t, 0 ≤ t → ‖drift H u v (x, t)‖ ≤ R) ∧ ∀ (φ : ContDiffBump (0 : E × ℝ)) x
      t, φ.rOut < t → ‖mollifiedDrift (μ := μ) H φ u v (x, t)‖ ≤ R := by
  obtain ⟨R, hR, hHR⟩ := exists_norm_gradient_bound_closedBall hH (max (Ku : ℝ) (Kv : ℝ))
  refine ⟨R, hR, ?_, ?_⟩
  · exact fun x t ht ↦ norm_integral_gradient_segment_le hHR
      ((norm_gradient_spatial_le_of_lipschitzOn_forward hu x ht).trans (le_max_left _ _))
      ((norm_gradient_spatial_le_of_lipschitzOn_forward hv x ht).trans (le_max_right _ _))
  · intro φ x t ht
    have hu' := lipschitzWith_forwardExtension hu
    have hv' := lipschitzWith_forwardExtension hv
    exact norm_integral_gradient_segment_le hHR
      ((norm_gradient_convolution_spatial_le φ hu'.continuous hu'.lipschitzOnWith ht x
        (μ := μ)).trans (le_max_left _ _))
      ((norm_gradient_convolution_spatial_le φ hv'.continuous hv'.lipschitzOnWith ht x
        (μ := μ)).trans (le_max_right _ _))

end HamiltonJacobi.Weak
