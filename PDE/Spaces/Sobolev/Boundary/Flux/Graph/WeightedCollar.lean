/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.WeightedSlab
public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Integral
import PDE.Analysis.MeasureTheory.AreaFormula.C1

/-!
# Weighted collar limits in general linear graph coordinates

A continuous graph shear and a linear change of variables reduce a physical
collar to a product slab. For a C¹ graph, the area formula identifies its limit
with Euclidean Hausdorff surface measure. The coordinate map may be nonorthogonal.
Only the graph's first derivative occurs; no boundary trace of a weak gradient
is assumed or constructed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Boundary.Flux.Graph

open Set Filter MeasureTheory Trace.HalfSpace
open scoped Topology

variable {m : ℕ}

/-- Integrating a weighted physical graph slab reduces to iterated flat-slab
integration. The determinant is retained for a general linear coordinate map. -/
theorem integral_linearGraphSlab_eq
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : Continuous g)
    {f : ℝ^(m + 1) → ℝ} (hf : Continuous f) (hcompact : HasCompactSupport f)
    {w : ℝ → ℝ} (hw : Continuous w) (h : ℝ) :
    ∫ x in {x | linearGraphHeight A g x ∈ Ioo 0 h},
        w (linearGraphHeight A g x / h) * f x =
      |A.symm.toLinearMap.det| *
        ∫ r in Ioo 0 h, w (r / h) *
          ∫ y, f (A.symm (joinTangentialNormal (y, r + g y))) := by
  let S := tangentialNormalContinuousLinearEquiv (n := m)
  let B : (ℝ^m × ℝ) ≃L[ℝ] ℝ^(m + 1) := S.symm.trans A.symm
  let H : Set (ℝ^(m + 1)) := {z | (S z).2 - g (S z).1 ∈ Ioo 0 h}
  let V : Set (ℝ^m × ℝ) := {z | z.2 - g z.1 ∈ Ioo 0 h}
  let F : ℝ^m × ℝ → ℝ := fun z ↦ f (B (Homeomorph.graphShear g hg z))
  have hF : Continuous F := hf.comp (B.continuous.comp (Homeomorph.graphShear g hg).continuous)
  have hFc : HasCompactSupport F :=
    (hcompact.comp_isClosedEmbedding B.toHomeomorph.isClosedEmbedding).comp_isClosedEmbedding
      (Homeomorph.graphShear g hg).isClosedEmbedding
  have hH : MeasurableSet H :=
    (S.continuous.snd.sub (hg.comp S.continuous.fst)).measurable measurableSet_Ioo
  have himage : A.symm '' H = {x | linearGraphHeight A g x ∈ Ioo 0 h} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [linearGraphHeight, H, S] using hz
    · intro hx
      refine ⟨A x, ?_, A.symm_apply_apply x⟩
      exact hx
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hH
    (fun z _ ↦ A.symm.hasFDerivAt.hasFDerivWithinAt) A.symm.injective.injOn
    (fun x ↦ w (linearGraphHeight A g x / h) * f x)
  rw [himage] at hchange
  have hsplit :
      ∫ z in H, w (linearGraphHeight A g (A.symm z) / h) * f (A.symm z) =
        ∫ z in V, w ((z.2 - g z.1) / h) * f (B z) ∂volume.prod volume := by
    have hmp := measurePreserving_tangentialNormalMeasurableEquiv (n := m)
    have heq := hmp.setIntegral_preimage_emb
      tangentialNormalMeasurableEquiv.measurableEmbedding
      (fun z : ℝ^m × ℝ ↦ w ((z.2 - g z.1) / h) * f (B z)) V
    simpa [H, V, B, S, linearGraphHeight, Measure.volume_eq_prod] using heq
  have hshear :
      ∫ z in V, w ((z.2 - g z.1) / h) * f (B z) ∂volume.prod volume =
        ∫ z in Set.univ ×ˢ Ioo 0 h, w (z.2 / h) * F z ∂volume.prod volume := by
    have heq :=
      (Homeomorph.measurePreserving_graphShear (μ := volume) g hg).setIntegral_preimage_emb
      (Homeomorph.graphShear g hg).measurableEmbedding
      (fun z : ℝ^m × ℝ ↦ w ((z.2 - g z.1) / h) * f (B z)) V
    have hpre : Homeomorph.graphShear g hg ⁻¹' V = Set.univ ×ˢ Ioo 0 h := by
      ext z
      simp [V]
    rw [hpre] at heq
    simpa [F] using heq.symm
  have hint : Integrable (fun z : ℝ^m × ℝ ↦ w (z.2 / h) * F z)
      (volume.prod volume) :=
    ((hw.comp (continuous_snd.div_const h)).mul hF).integrable_of_hasCompactSupport hFc.mul_left
  have hprod :
      ∫ z in Set.univ ×ˢ Ioo 0 h, w (z.2 / h) * F z ∂volume.prod volume =
        ∫ r in Ioo 0 h, w (r / h) * ∫ y, F (y, r) := by
    have hi : Integrable (fun z : ℝ^m × ℝ ↦ w (z.2 / h) * F z)
        (volume.prod (volume.restrict (Ioo 0 h))) := by
      simpa only [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] using
        hint.integrableOn (s := Set.univ ×ˢ Ioo 0 h)
    rw [← Measure.prod_restrict, Measure.restrict_univ, integral_prod_symm _ hi]
    simp_rw [integral_const_mul]
  rw [hchange]
  simp only [smul_eq_mul, integral_const_mul]
  rw [hsplit, hshear, hprod]
  rfl

/-- A weighted collar of a continuous graph converges to its parameter-space
boundary slice. No differentiability of the graph is needed at this stage. -/
theorem tendsto_normalized_linearGraphSlab_integral
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : Continuous g)
    {f : ℝ^(m + 1) → ℝ} (hf : Continuous f) (hcompact : HasCompactSupport f)
    {w : ℝ → ℝ} (hw : Continuous w) :
    Tendsto (fun h : ℝ ↦ h⁻¹ *
      ∫ x in {x | linearGraphHeight A g x ∈ Ioo 0 h},
        w (linearGraphHeight A g x / h) * f x)
      (𝓝[>] 0) (𝓝 (|A.symm.toLinearMap.det| *
        ((∫ s in (0 : ℝ)..1, w s) * ∫ y, f (linearGraphParametrization A g y)))) := by
  let S := tangentialNormalContinuousLinearEquiv (n := m)
  let B : (ℝ^m × ℝ) ≃L[ℝ] ℝ^(m + 1) := S.symm.trans A.symm
  let F : ℝ^m × ℝ → ℝ := fun z ↦ f (B (Homeomorph.graphShear g hg z))
  have hF : Continuous F := hf.comp (B.continuous.comp (Homeomorph.graphShear g hg).continuous)
  have hFc : HasCompactSupport F :=
    (hcompact.comp_isClosedEmbedding B.toHomeomorph.isClosedEmbedding).comp_isClosedEmbedding
      (Homeomorph.graphShear g hg).isClosedEmbedding
  have ht := tendsto_normalized_weighted_slab_integral_of_hasCompactSupport
    (μ := volume) hF hw hFc
  have hboundary (y : ℝ^m) : F (y, 0) = f (linearGraphParametrization A g y) := by
    simp [F, B, S, linearGraphParametrization]
  simp only [hboundary] at ht
  apply (ht.const_mul |A.symm.toLinearMap.det|).congr'
  filter_upwards [] with h
  rw [integral_linearGraphSlab_eq A hg hf hcompact hw]
  rw [mul_left_comm]
  rfl

/-- The C¹ graph area formula with one extra conormal length. The parameter
integral contains the square of that length and the linear volume determinant. -/
theorem integral_linearGraph_mul_conormal_eq
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    {f : ℝ^(m + 1) → ℝ} (hf : Continuous f) :
    ∫ x in frontier (linearEpigraph A g),
        f x * ‖linearGraphConormal A g (splitTangentialNormal (A x)).1‖
          ∂Measure.euclideanHausdorffMeasure m =
      |A.symm.toLinearMap.det| * ∫ y,
        f (linearGraphParametrization A g y) * ‖linearGraphConormal A g y‖ ^ 2 := by
  let H : ℝ^(m + 1) → ℝ := fun x ↦
    f x * ‖linearGraphConormal A g (splitTangentialNormal (A x)).1‖
  have hH : Continuous H := hf.mul
    (((continuous_linearGraphConormal A hg).comp
      (tangentialNormalContinuousLinearEquiv.continuous.fst.comp A.continuous)).norm)
  have harea := integral_image_eq_integral_normDet_smul_of_contDiffOn isOpen_univ
    (contDiff_linearGraphParametrization A hg).contDiffOn
    (linearGraphParametrization_injective A g).injOn
    (fun y _ ↦ by
      rw [(hasFDerivAt_linearGraphParametrization A hg y).fderiv]
      exact linearGraphTangent_injective A g y) H hH.aestronglyMeasurable
  simp only [image_univ, range_linearGraphParametrization A g hg.continuous,
    finrank_euclideanSpace_fin, setIntegral_univ] at harea
  change (∫ x in frontier (linearEpigraph A g), H x
    ∂Measure.euclideanHausdorffMeasure m) = _
  rw [harea, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [(hasFDerivAt_linearGraphParametrization A hg y).fderiv, normDet_linearGraphTangent]
  simp only [H, linearGraphParametrization, ContinuousLinearEquiv.apply_symm_apply,
    split_joinTangentialNormal, smul_eq_mul]
  ring

/-- A squared-conormal weighted physical collar converges to the corresponding
Hausdorff boundary integral with one conormal length. A squared continuous
cutoff derivative is allowed as the transverse weight. -/
theorem tendsto_normalized_linearGraphCollar_integral
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    {f : ℝ^(m + 1) → ℝ} (hf : Continuous f) (hcompact : HasCompactSupport f)
    {w : ℝ → ℝ} (hw : Continuous w) :
    Tendsto (fun h : ℝ ↦ h⁻¹ *
      ∫ x in {x | linearGraphHeight A g x ∈ Ioo 0 h},
        w (linearGraphHeight A g x / h) *
          (f x * ‖linearGraphConormal A g (splitTangentialNormal (A x)).1‖ ^ 2))
      (𝓝[>] 0) (𝓝 ((∫ s in (0 : ℝ)..1, w s) *
        ∫ x in frontier (linearEpigraph A g),
          f x * ‖linearGraphConormal A g (splitTangentialNormal (A x)).1‖
            ∂Measure.euclideanHausdorffMeasure m)) := by
  have hc : Continuous (fun x : ℝ^(m + 1) ↦
      f x * ‖linearGraphConormal A g (splitTangentialNormal (A x)).1‖ ^ 2) :=
    hf.mul ((((continuous_linearGraphConormal A hg).comp
      (tangentialNormalContinuousLinearEquiv.continuous.fst.comp A.continuous)).norm).pow 2)
  have ht := tendsto_normalized_linearGraphSlab_integral A hg.continuous hc hcompact.mul_right hw
  rw [integral_linearGraph_mul_conormal_eq A hg hf]
  have hparam (y : ℝ^m) :
      (splitTangentialNormal (A (linearGraphParametrization A g y))).1 = y := by
    simp [linearGraphParametrization]
  simp only [hparam] at ht
  convert ht using 1
  congr 1
  ring

/-- The conormal norm is the operator norm of the differential of the physical
height. This identifies the collar weight without a separate gradient notation. -/
theorem norm_fderiv_linearGraphHeight
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    (x : ℝ^(m + 1)) :
    ‖fderiv ℝ (linearGraphHeight A g) x‖ =
      ‖linearGraphConormal A g (splitTangentialNormal (A x)).1‖ := by
  rw [(hasFDerivAt_linearGraphHeight A hg x).fderiv, linearGraphConormal]
  exact ((InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.norm_map _).symm

/-- The collar formula for squared test functions and squared transverse
weights. Taking `ψ = deriv χ` gives the cutoff-derivative weight used in a weak
normal-trace estimate. No assumptions on a weak solution enter this limit. -/
theorem tendsto_normalized_linearGraphCollar_sq_integral
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    {V : ℝ^(m + 1) → ℝ} (hV : Continuous V) (hcompact : HasCompactSupport V)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) :
    Tendsto (fun h : ℝ ↦ h⁻¹ *
      ∫ x in {x | linearGraphHeight A g x ∈ Ioo 0 h},
        ψ (linearGraphHeight A g x / h) ^ 2 *
          (V x ^ 2 * ‖fderiv ℝ (linearGraphHeight A g) x‖ ^ 2))
      (𝓝[>] 0) (𝓝 ((∫ s in (0 : ℝ)..1, ψ s ^ 2) *
        ∫ x in frontier (linearEpigraph A g),
          V x ^ 2 * ‖fderiv ℝ (linearGraphHeight A g) x‖
            ∂Measure.euclideanHausdorffMeasure m)) := by
  have hVc : HasCompactSupport (fun x ↦ V x ^ 2) := by
    exact hcompact.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  simpa only [norm_fderiv_linearGraphHeight A hg, Pi.pow_apply] using
    tendsto_normalized_linearGraphCollar_integral A hg (hV.pow 2) hVc (hψ.pow 2)

end SobolevSpace.Boundary.Flux.Graph
