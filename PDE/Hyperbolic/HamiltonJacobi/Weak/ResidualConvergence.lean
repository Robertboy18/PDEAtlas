/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Weak.DriftRegularity
public import PDE.Hyperbolic.HamiltonJacobi.Weak.Transport

/-!
# Vanishing transport residuals after mollification

Mollifying the transported density as well as the two solutions produces a
smooth density to which the classical moving-ball formula applies. Its
transport residual tends to zero almost everywhere. Lipschitz bounds provide
an integrable constant majorant on compact positive-time slabs, so the
integral of its absolute value also tends to zero.

The transport identity below is the equation for the density, not an assumed
energy estimate. For cutoffs of differences of weak Hamilton–Jacobi solutions,
it follows from the almost-everywhere subtraction and chain rules.
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Filter Set
open scoped Convolution Topology RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

/-- The transport residual of the mollified density and drift. -/
def mollifiedTransportResidual (H : E → ℝ) (φ : ContDiffBump (0 : E × ℝ))
    (u v w : E × ℝ → ℝ) (z : E × ℝ) : ℝ :=
  fderiv ℝ (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) z (0, 1) +
    ⟪mollifiedDrift (μ := μ) H φ u v z,
      ∇ (fun x ↦
        (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) (x, z.2)) z.1⟫

/-- The mollified transport residual is continuous, although the three inputs
are only forward Lipschitz. -/
theorem continuous_mollifiedTransportResidual {H : E → ℝ} (hH : ContDiff ℝ 2 H) {u v w : E × ℝ → ℝ}
    {Ku Kv Kw : NNReal} (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2})
    (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) (hw : LipschitzOnWith Kw w {z | 0 ≤ z.2})
    (φ : ContDiffBump (0 : E × ℝ)) :
    Continuous (mollifiedTransportResidual (μ := μ) H φ u v w) := by
  have hsmooth : ContDiff ℝ 2 (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) :=
    φ.hasCompactSupport_normed.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed
      (lipschitzWith_forwardExtension hw).continuous.locallyIntegrable
  exact ((hsmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
    ((contDiff_mollifiedDrift hH hu hv φ).continuous.inner
      (contDiff_gradient_spaceSlice (n := 1) hsmooth).continuous)

/-- Derivative and drift convergence make the residual of any forward
Lipschitz transported density vanish almost everywhere at positive times. -/
theorem ae_tendsto_mollifiedTransportResidual {H : E → ℝ} (hH : ContDiff ℝ 1 H) {u v w : E × ℝ → ℝ}
    {Ku Kv Kw : NNReal} (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2})
    (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) (hw : LipschitzOnWith Kw w {z | 0 ≤ z.2})
    (heq : ∀ᵐ z ∂μ.restrict {z : E × ℝ | 0 < z.2}, fderiv ℝ w z (0, 1) + ⟪drift H u v z,
      ∇ (fun x ↦ w (x, z.2)) z.1⟫ = 0)
    {ι : Type*} {φ : ι → ContDiffBump (0 : E × ℝ)} {l : Filter ι} {A : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn) :
    ∀ᵐ z ∂μ.restrict {z : E × ℝ | 0 < z.2},
      Tendsto (fun i ↦ mollifiedTransportResidual (μ := μ) H (φ i) u v w z) l (𝓝 0) := by
  filter_upwards [ae_tendsto_fderiv_convolution_forwardExtension_apply
    hw hφ hφ_ratio (0, 1) (μ := μ),
    ae_tendsto_gradient_convolution_forwardExtension hw hφ hφ_ratio (μ := μ),
    ae_tendsto_mollifiedDrift hH hu hv hφ hφ_ratio (μ := μ), heq] with z ht hg hb hz
  have h := ht.add (hb.inner hg)
  simpa only [mollifiedTransportResidual, hz] using h

/-- A single constant bounds all mollified transport residuals beyond their
kernel radii. The constant comes from the three Lipschitz constants and the
Hamiltonian gradient on a compact ball. -/
theorem exists_norm_mollifiedTransportResidual_le {H : E → ℝ} (hH : ContDiff ℝ 1 H)
    {u v w : E × ℝ → ℝ} {Ku Kv Kw : NNReal} (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2})
    (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) (hw : LipschitzOnWith Kw w {z | 0 ≤ z.2}) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : ContDiffBump (0 : E × ℝ)) (z : E × ℝ),
      φ.rOut < z.2 → ‖mollifiedTransportResidual (μ := μ) H φ u v w z‖ ≤ B := by
  obtain ⟨R, hR, _, hRb⟩ := exists_norm_drift_le (μ := μ) hH hu hv
  refine ⟨Kw + R * Kw, by positivity, fun φ z hz ↦ ?_⟩
  have hw' := lipschitzWith_forwardExtension hw
  have hLip := PDE.Analysis.lipschitzWith_normed_convolution (μ := μ) φ hw'
  have ht : ‖fderiv ℝ
      (φ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension w) z (0, 1)‖ ≤ Kw :=
    (ContinuousLinearMap.le_opNorm _ _).trans (by
      simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := z) hLip)
  have hg := norm_gradient_convolution_spatial_le (μ := μ) φ hw'.continuous
    hw'.lipschitzOnWith hz z.1
  unfold mollifiedTransportResidual
  exact (norm_add_le _ _).trans (add_le_add ht ((norm_inner_le_norm _ _).trans
      (mul_le_mul (hRb φ z.1 z.2 hz) hg (norm_nonneg _) hR)))

/-- On every compact slab bounded away from the initial time, the integral
of the absolute transport residual tends to zero. Both pointwise convergence
and the majorant are derived above. -/
theorem tendsto_setIntegral_norm_mollifiedTransportResidual {H : E → ℝ} (hH : ContDiff ℝ 2 H)
    {u v w : E × ℝ → ℝ} {Ku Kv Kw : NNReal} (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2})
    (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2}) (hw : LipschitzOnWith Kw w {z | 0 ≤ z.2})
    (heq : ∀ᵐ z ∂μ.restrict {z : E × ℝ | 0 < z.2}, fderiv ℝ w z (0, 1) + ⟪drift H u v z,
      ∇ (fun x ↦ w (x, z.2)) z.1⟫ = 0)
    {ι : Type*} {φ : ι → ContDiffBump (0 : E × ℝ)} {l : Filter ι} [l.IsCountablyGenerated] {A : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn)
    {S : Set (E × ℝ)} (hS : IsCompact S) {a : ℝ} (ha : 0 < a) (hSa : ∀ z ∈ S, a ≤ z.2) :
    Tendsto (fun i ↦ ∫ z in S,
      ‖mollifiedTransportResidual (μ := μ) H (φ i) u v w z‖ ∂μ) l (𝓝 0) := by
  have hH' : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  obtain ⟨B, _, hB⟩ := exists_norm_mollifiedTransportResidual_le (μ := μ) hH' hu hv hw
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hlim := ae_tendsto_mollifiedTransportResidual hH' hu hv hw heq hφ hφ_ratio
  have hlimS := hlim.filter_mono (ae_mono (Measure.restrict_mono_set (μ := μ)
    (show S ⊆ {z : E × ℝ | 0 < z.2} from fun z hz ↦ ha.trans_le (hSa z hz))))
  have hsmall : ∀ᶠ i in l, (φ i).rOut < a := hφ.eventually (Iio_mem_nhds ha)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ.restrict S) (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ B) (Eventually.of_forall fun i ↦
      (continuous_mollifiedTransportResidual hH hu hv hw (φ i)).norm.aestronglyMeasurable)
    (by
      filter_upwards [hsmall] with i hi
      filter_upwards [ae_restrict_mem hS.isClosed.measurableSet] with z hz
      simpa only [norm_norm] using hB (φ i) z (hi.trans_le (hSa z hz))) (integrable_const B)
    (by
      filter_upwards [hlimS] with z hz
      simpa only [norm_zero] using hz.norm)
  simpa only [integral_zero] using h

/-- For any differentiable Lipschitz cutoff of the difference of two arbitrary
AE Hamilton–Jacobi solutions, the mollified transport residual vanishes
in integral on compact positive-time slabs. The AE equations and the chain rule give the transport
identity. -/
theorem tendsto_setIntegral_norm_mollifiedTransportResidual_comp_sub {H : E → ℝ}
    (hH : ContDiff ℝ 2 H) {u v : E × ℝ → ℝ} {Ku Kv : NNReal}
    (hu : LipschitzOnWith Ku u {z | 0 ≤ z.2}) (hv : LipschitzOnWith Kv v {z | 0 ≤ z.2})
    (hu_eq : ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      fderiv ℝ u z (0, 1) + H (∇ (fun x ↦ u (x, z.2)) z.1) = 0)
    (hv_eq : ∀ᵐ z ∂μ.restrict positiveTimeDomain,
      fderiv ℝ v z (0, 1) + H (∇ (fun x ↦ v (x, z.2)) z.1) = 0)
    {χ : ℝ → ℝ} {Kχ : NNReal} (hχ : LipschitzWith Kχ χ) (hχ_diff : Differentiable ℝ χ) {ι : Type*}
    {φ : ι → ContDiffBump (0 : E × ℝ)} {l : Filter ι} [l.IsCountablyGenerated] {A : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn)
    {S : Set (E × ℝ)} (hS : IsCompact S) {a : ℝ} (ha : 0 < a) (hSa : ∀ z ∈ S, a ≤ z.2) :
    Tendsto (fun i ↦ ∫ z in S, ‖mollifiedTransportResidual (μ := μ) H (φ i) u v
      (fun y ↦ χ (u y - v y)) z‖ ∂μ) l (𝓝 0) := by
  have hH' : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  apply tendsto_setIntegral_norm_mollifiedTransportResidual hH hu hv
    (hχ.comp_lipschitzOnWith (hu.sub hv)) _ hφ hφ_ratio hS ha hSa
  filter_upwards [ae_transport_comp_sub_eq_zero hH' hu hv hu_eq hv_eq hχ_diff] with z hz
  simpa only [averagedFDeriv_eq_inner_integral_gradient hH', drift, Function.comp_def] using hz

end HamiltonJacobi.Weak
