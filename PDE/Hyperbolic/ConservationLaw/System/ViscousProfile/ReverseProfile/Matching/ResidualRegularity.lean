/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

import PDE.Analysis.Calculus.Prod.SliceDerivative

/-!
# Local smoothness of the first-match residual

The terminal coordinates may depend on any normed real parameter space. On the open slice
`(μ,a) = (0,0)`, their quotient and its ordinary physical slice derivatives give
a smooth residual. Both terminal coordinates may depend on every parameter;
all regularity and denominator hypotheses are local to the supplied open set.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis

/-- The first-match residual is smooth on the open zero-physical-parameter slice.
Its speed and displacement derivatives are ordinary `deriv` of the terminal
maps. Their parameter regularity follows from joint smoothness on the open domain.
The real reflection slope `h` is fixed, while both terminal coordinates may vary. -/
theorem contDiffOn_matching_residual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x z : (E × (ℝ × ℝ)) → ℝ} {U : Set (E × (ℝ × ℝ))} (hU : IsOpen U) (hx : ContDiffOn ℝ ∞ x U)
    (hz : ContDiffOn ℝ ∞ z U) (hz_ne : ∀ u ∈ U, z u ≠ 0) (h : ℝ) :
    let S : Set E :=
      (fun σ ↦ (σ, ((0 : ℝ), (0 : ℝ)))) ⁻¹' U
    let ρ : (E × (ℝ × ℝ)) → ℝ := fun u ↦ x u / z u
    let G : E → Fin 3 → ℝ := fun σ ↦
      ![ρ (σ, (0, 0)) - 1,
        deriv (fun a : ℝ ↦ ρ (σ, (0, a))) 0,
        z (σ, (0, 0)) * deriv (fun μ : ℝ ↦ ρ (σ, (μ, 0))) 0 +
          2 * deriv (fun μ : ℝ ↦ z (σ, (μ, 0))) 0 +
          h * deriv (fun a : ℝ ↦ z (σ, (0, a))) 0]
    IsOpen S ∧ ContDiffOn ℝ ∞ G S := by
  intro S ρ G
  have hρ : ContDiffOn ℝ ∞ ρ U := hx.fun_div hz hz_ne
  have hbase : ContDiff ℝ ∞ (fun σ : E ↦ (σ, ((0 : ℝ), (0 : ℝ)))) :=
    contDiff_id.prodMk contDiff_const
  -- On an open axis pullback, the ordinary derivative equals the joint
  -- differential evaluated on the scalar-factor direction.
  have hslice {f : (E × ℝ) → ℝ} {W : Set (E × ℝ)} (hW : IsOpen W) (hf : ContDiffOn ℝ ∞ f W) :
      ContDiffOn ℝ ∞ (fun σ : E ↦ deriv (fun t : ℝ ↦ f (σ, t)) 0)
        ((fun σ : E ↦ (σ, (0 : ℝ))) ⁻¹' W) := by
    have ht : ContDiffOn ℝ ∞ (fun w : E × ℝ ↦ deriv (fun t : ℝ ↦ f (w.1, t)) w.2) W :=
      ((hf.fderiv_of_isOpen hW (by simp)).clm_apply contDiffOn_const).congr fun w hw ↦
        deriv_prod_timeSlice f w.1 w.2
          ((hf.contDiffAt (hW.mem_nhds hw)).differentiableAt (by simp))
    exact ht.comp (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hσ ↦ hσ
  have hμ {f : (E × (ℝ × ℝ)) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ContDiffOn ℝ ∞ (fun σ : E ↦ deriv (fun μ : ℝ ↦ f (σ, (μ, 0))) 0) S := by
    have he : ContDiff ℝ ∞ (fun w : E × ℝ ↦ (w.1, (w.2, (0 : ℝ)))) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
    exact hslice (hU.preimage he.continuous) (hf.comp he.contDiffOn fun _ hw ↦ hw)
  have ha {f : (E × (ℝ × ℝ)) → ℝ} (hf : ContDiffOn ℝ ∞ f U) :
      ContDiffOn ℝ ∞ (fun σ : E ↦ deriv (fun a : ℝ ↦ f (σ, (0, a))) 0) S := by
    have he : ContDiff ℝ ∞ (fun w : E × ℝ ↦ (w.1, ((0 : ℝ), w.2))) :=
      contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd)
    exact hslice (hU.preimage he.continuous) (hf.comp he.contDiffOn fun _ hw ↦ hw)
  refine ⟨hU.preimage hbase.continuous, contDiffOn_pi.mpr fun i ↦ ?_⟩
  fin_cases i
  · exact (hρ.comp hbase.contDiffOn fun _ hσ ↦ hσ).sub contDiffOn_const
  · exact ha hρ
  · exact (((hz.comp hbase.contDiffOn fun _ hσ ↦ hσ).mul (hμ hρ)).add
      (contDiffOn_const.mul (hμ hz))).add (contDiffOn_const.mul (ha hz))

end PDE.Analysis
