/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Shearing a half-space onto an epigraph

Translation of the vertical coordinate by a continuous height is a
homeomorphism preserving product measure. Thus integration over an epigraph
reduces to a fixed half-space without differentiating a Jacobian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]

/-- The shear adding a height depending on the first coordinate. -/
def graphShear (g : E → ℝ) (hg : Continuous g) : E × ℝ ≃ₜ E × ℝ where
  toFun z := (z.1, z.2 + g z.1)
  invFun z := (z.1, z.2 - g z.1)
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (hg.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hg.comp continuous_fst))

@[simp]
theorem graphShear_apply (g : E → ℝ) (hg : Continuous g) (z : E × ℝ) :
    graphShear g hg z = (z.1, z.2 + g z.1) := rfl

@[simp]
theorem graphShear_symm_apply (g : E → ℝ) (hg : Continuous g) (z : E × ℝ) :
    (graphShear g hg).symm z = (z.1, z.2 - g z.1) := rfl

/-- The upper half-space is the inverse image of the strict epigraph. -/
theorem graphShear_preimage_epigraph (g : E → ℝ) (hg : Continuous g) :
    graphShear g hg ⁻¹' {z | g z.1 < z.2} = _root_.Set.univ ×ˢ Set.Ioi 0 := by
  ext z
  simp

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [SFinite μ]

/-- A graph shear preserves the product of any base measure with Lebesgue
measure on the vertical line. -/
theorem measurePreserving_graphShear (g : E → ℝ) (hg : Continuous g) :
    MeasurePreserving (graphShear g hg) (μ.prod volume) (μ.prod volume) := by
  exact (MeasurePreserving.id μ).skew_product
    (continuous_snd.add (hg.comp continuous_fst)).measurable
    (ae_of_all _ fun y ↦ (measurePreserving_add_right (volume : Measure ℝ) (g y)).map_eq)

/-- Signed integrals over an epigraph can be computed on the fixed upper
half-space after shear. -/
theorem integral_epigraph_eq_integral_graphShear
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → ℝ) (hg : Continuous g) (f : E × ℝ → F) :
    ∫ z in {z | g z.1 < z.2}, f z ∂μ.prod volume =
      ∫ z in _root_.Set.univ ×ˢ Set.Ioi 0, f (graphShear g hg z) ∂μ.prod volume := by
  rw [← graphShear_preimage_epigraph g hg]
  exact ((measurePreserving_graphShear g hg).setIntegral_preimage_emb
    (graphShear g hg).measurableEmbedding _ _).symm

end Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A C¹ graph shear has the same regularity as its height. -/
theorem ContDiff.graphShear {k : WithTop ℕ∞} {g : E → ℝ} (hg : ContDiff ℝ k g) :
    ContDiff ℝ k (Homeomorph.graphShear g hg.continuous) :=
  contDiff_fst.prodMk (contDiff_snd.add (hg.comp contDiff_fst))

namespace PDE

/-- The derivative of a scalar or vector-valued pullback under a graph shear.
Only the first derivative of the height occurs. -/
theorem fderiv_comp_graphShear_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) {f : E × ℝ → F}
    (hf : ContDiff ℝ 1 f) (z w : E × ℝ) :
    fderiv ℝ (fun x ↦ f (Homeomorph.graphShear g hg.continuous x)) z w =
      fderiv ℝ f (Homeomorph.graphShear g hg.continuous z)
        (w.1, w.2 + fderiv ℝ g z.1 w.1) := by
  have hs := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
    ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add
      ((hg.differentiable one_ne_zero z.1).hasFDerivAt.comp z
        (hasFDerivAt_fst (𝕜 := ℝ) (p := z))))
  have h := ((hf.differentiable one_ne_zero
    (Homeomorph.graphShear g hg.continuous z)).hasFDerivAt.comp z hs).fderiv
  exact congrArg (fun A : E × ℝ →L[ℝ] F ↦ A w) h

end PDE
