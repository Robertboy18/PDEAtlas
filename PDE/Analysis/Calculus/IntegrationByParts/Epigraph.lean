/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Graph.Shear
public import PDE.Analysis.Calculus.IntegrationByParts.HalfSpace

/-!
# Integration by parts above a C¹ graph

For a compactly supported C¹ scalar function, integration of its derivative
in the direction `(v,r)` above the graph of `g` gives the graph integral
weighted by `Dg(v) - r`. This is the signed, unnormalized outward conormal.

The proof pulls back scalar functions under the graph shear. It differentiates
the height only once, so a C¹ boundary is sufficient.
-/

@[expose] public section

open MeasureTheory Measure Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

namespace PDE

/-- The signed directional integration-by-parts formula on a strict epigraph.
Both the graph and the scalar function require only C¹ regularity. -/
theorem integral_epigraph_fderiv {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    {f : E × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (v : E) (r : ℝ) :
    ∫ z in {z | g z.1 < z.2}, fderiv ℝ f z (v, r) ∂μ.prod volume =
      ∫ y, (fderiv ℝ g y v - r) * f (y, g y) ∂μ := by
  let H : E × ℝ → ℝ := fun z ↦ f (Homeomorph.graphShear g hg.continuous z)
  have hH : ContDiff ℝ 1 H := hf.comp hg.graphShear
  have hHcompact : HasCompactSupport H :=
    hcompact.comp_isClosedEmbedding (Homeomorph.graphShear g hg.continuous).isClosedEmbedding
  have ha : Continuous (fun y ↦ fderiv ℝ g y v - r) :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub continuous_const
  have ht := integral_halfSpace_fderiv_tangential (μ := μ) hH hHcompact v
  have hn := integral_halfSpace_mul_fderiv_normal (μ := μ) hH hHcompact ha
  have hidentity (z : E × ℝ) :
      fderiv ℝ f (Homeomorph.graphShear g hg.continuous z) (v, r) =
        fderiv ℝ H z (v, 0) -
          (fderiv ℝ g z.1 v - r) * fderiv ℝ H z (0, 1) := by
    dsimp only [H]
    rw [fderiv_comp_graphShear_apply hg hf, fderiv_comp_graphShear_apply hg hf]
    simp only [map_zero, add_zero, zero_add]
    have hvec : (v, fderiv ℝ g z.1 v) -
        (fderiv ℝ g z.1 v - r) • ((0, 1) : E × ℝ) = (v, r) := by
      ext <;> simp
    rw [← smul_eq_mul, ← map_smul, ← map_sub, hvec]
  have htc : Continuous (fun z : E × ℝ ↦ fderiv ℝ H z (v, 0)) :=
    (hH.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hti : IntegrableOn (fun z : E × ℝ ↦ fderiv ℝ H z (v, 0))
      (Set.univ ×ˢ Ioi 0) (μ.prod volume) :=
    (htc.integrable_of_hasCompactSupport (hHcompact.fderiv_apply ℝ (v, 0))).integrableOn
  have hnc : Continuous (fun z : E × ℝ ↦
      (fderiv ℝ g z.1 v - r) * fderiv ℝ H z (0, 1)) :=
    (ha.comp continuous_fst).mul
      ((hH.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hni : IntegrableOn (fun z : E × ℝ ↦
      (fderiv ℝ g z.1 v - r) * fderiv ℝ H z (0, 1))
      (Set.univ ×ˢ Ioi 0) (μ.prod volume) :=
    (hnc.integrable_of_hasCompactSupport
      (hHcompact.fderiv_apply ℝ (0, 1)).mul_left).integrableOn
  rw [Homeomorph.integral_epigraph_eq_integral_graphShear g hg.continuous]
  simp_rw [hidentity]
  rw [integral_sub hti hni, ht, hn]
  simp [H]

end PDE
