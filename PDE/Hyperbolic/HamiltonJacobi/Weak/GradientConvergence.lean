/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.LipschitzDerivative
public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Basic
public import PDE.Hyperbolic.HamiltonJacobi.Weak.ForwardExtension

/-!
# Almost-everywhere convergence of mollified spatial gradients

These are the spacetime convolutions of step 3 of the proof of Theorem 7 in Evans,
§3.3.3(b), and the convergence is (42). Evans takes it from the properties of mollifiers
(§C.4); we derive it from Lipschitz integration by parts and Lebesgue differentiation
in spacetime, applied in an orthonormal basis of spatial directions. Holding the initial value
fixed at negative times gives a global Lipschitz extension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), proof of Theorem 7, step 3, equation (42).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi.Weak

open MeasureTheory Filter
open scoped Convolution Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure (E × ℝ)} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- At positive times the forward extension agrees locally with the original
input, so their joint derivatives agree as well. -/
theorem fderiv_forwardExtension {u : E × ℝ → ℝ} {z : E × ℝ} (hz : 0 < z.2) :
    fderiv ℝ (forwardExtension u) z = fderiv ℝ u z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [continuous_snd.continuousAt (Ioi_mem_nhds hz)] with w hw
  exact forwardExtension_eq (le_of_lt hw)

/-- Every fixed spacetime directional derivative of the mollification
converges almost everywhere, in particular the time derivative. -/
theorem ae_tendsto_fderiv_convolution_forwardExtension_apply {u : E × ℝ → ℝ} {K : NNReal}
    (hu : LipschitzOnWith K u {z | 0 ≤ z.2}) {ι : Type*} {φ : ι → ContDiffBump (0 : E × ℝ)}
    {l : Filter ι} {A : ℝ} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn) (v : E × ℝ) :
    ∀ᵐ z ∂μ.restrict {z : E × ℝ | 0 < z.2}, Tendsto
      (fun i ↦ fderiv ℝ ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
        forwardExtension u) z v) l (𝓝 (fderiv ℝ u z v)) := by
  have h := PDE.Analysis.ae_tendsto_fderiv_convolution_apply
    (μ := μ) (lipschitzWith_forwardExtension hu) hφ hφ_ratio v
  filter_upwards [ae_restrict_of_ae h,
    ae_restrict_mem (measurableSet_lt measurable_const measurable_snd)] with z hz ht
  simpa only [fderiv_forwardExtension ht] using hz

/-- Spacetime mollification of a globally Lipschitz function has spatial
gradients converging almost everywhere to its spatial gradient. -/
theorem ae_tendsto_gradient_convolution_spatial {u : E × ℝ → ℝ} {K : NNReal}
    (hu : LipschitzWith K u) {ι : Type*} {φ : ι → ContDiffBump (0 : E × ℝ)} {l : Filter ι} {A : ℝ}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn) :
    ∀ᵐ z ∂μ, Tendsto (fun i ↦ ∇ (fun x ↦ ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u)
      (x, z.2)) z.1) l (𝓝 (∇ (fun x ↦ u (x, z.2)) z.1)) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  have hdir (j : Fin (Module.finrank ℝ E)) :=
    PDE.Analysis.ae_tendsto_fderiv_convolution_apply (μ := μ) hu hφ hφ_ratio (b j, 0)
  filter_upwards [ae_all_iff.2 hdir, hu.ae_differentiableAt (μ := μ)] with z hz hzu
  have hsum (f : E × ℝ → ℝ) (hf : DifferentiableAt ℝ f z) : (∑ j, fderiv ℝ f z (b j, 0) • b j) =
        ∇ (fun x ↦ f (x, z.2)) z.1 := by
    convert b.sum_repr' (∇ (fun x ↦ f (x, z.2)) z.1) using 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply, fderiv_spaceSlice hf]
    rfl
  have hconv (i : ι) : DifferentiableAt ℝ
      ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u) z :=
    ((φ i).hasCompactSupport_normed.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (φ i).contDiff_normed
      hu.continuous.locallyIntegrable z).differentiableAt
  have h := tendsto_finsetSum Finset.univ (fun j _ ↦ (hz j).smul
    (show Tendsto (fun _ : ι ↦ b j) l (𝓝 (b j)) from tendsto_const_nhds))
  simpa only [hsum _ hzu, hsum _ (hconv _)] using h

/-- Evans's gradient convergence (42) for arbitrary forward Lipschitz inputs.
Only positive times occur in the conclusion, so the extension does not change
the limiting spatial gradient. -/
theorem ae_tendsto_gradient_convolution_forwardExtension {u : E × ℝ → ℝ} {K : NNReal}
    (hu : LipschitzOnWith K u {z | 0 ≤ z.2}) {ι : Type*} {φ : ι → ContDiffBump (0 : E × ℝ)}
    {l : Filter ι} {A : ℝ} (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0))
    (hφ_ratio : ∀ᶠ i in l, (φ i).rOut ≤ A * (φ i).rIn) :
    ∀ᵐ z ∂μ.restrict {z : E × ℝ | 0 < z.2}, Tendsto (fun i ↦
      ∇ (fun x ↦ ((φ i).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] forwardExtension u) (x, z.2))
      z.1) l (𝓝 (∇ (fun x ↦ u (x, z.2)) z.1)) := by
  have h := ae_tendsto_gradient_convolution_spatial
    (μ := μ) (lipschitzWith_forwardExtension hu) hφ hφ_ratio
  filter_upwards [ae_restrict_of_ae h,
    ae_restrict_mem (measurableSet_lt measurable_const measurable_snd)] with z hz ht
  have heq : (fun x ↦ forwardExtension u (x, z.2)) = (fun x ↦ u (x, z.2)) := by
    ext x
    exact forwardExtension_eq (le_of_lt ht)
  simpa only [heq] using hz

end HamiltonJacobi.Weak
