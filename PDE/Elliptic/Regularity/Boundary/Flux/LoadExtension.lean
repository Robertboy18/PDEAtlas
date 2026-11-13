/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Calculus.Pullback.Divergence.Load
public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension

/-!
# Extending the transformed load to the upper half-space

The restricted chart transforms the physical `L²` load on `Ω ∩ source`.
Zero extension from its target gives an `L²` field on the full half-space.
On the chart target this field is the determinant-weighted pullback.
This construction uses no regularity of the solution.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Boundary

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.WeakChangeOfVariables
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- An `L²` physical load has an `L²` extension of its transformed
load on the upper half-space. -/
theorem exists_chartLoad_extension
    (hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω) (a : Fin hΩ.N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : DerivLp n 2 Ω,
    ∃ F : DerivLp n 2 (HalfSpace.upper n), ‖F‖ ≤ C * ‖f‖ ∧
      ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), y ∈ (hΩ.chart a).target →
        F y = |(fderiv ℝ (fun z ↦ (hΩ.chart a).symm z) y).det| *
          f ((hΩ.chart a).symm y) := by
  let E := SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ (Ω := Ω) a
  have hE : ContDiff ℝ 1 (fun x ↦ E x) := hΩ.chart_contDiff a
  have hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y) := hΩ.chart_symm_contDiff a
  have hsource : E.source ⊆ Ω := fun _ hx ↦ hx.2
  have htarget : E.target ⊆ (hΩ.chart a).target := fun _ hy ↦ hy.1
  have hbounded := (hΩ.chart_target_bounded a).subset htarget
  let P := piolaLoadCLM (p := 2) hE hSymm hbounded
  refine ⟨‖P‖, P.opNorm_nonneg, fun f ↦ ?_⟩
  let f₀ := restrictDerivLp (p := 2) hsource f
  let g := P f₀
  let g₀ := Extension.Lp.zeroExtendLp E.open_target.measurableSet g
  let F := restrictDerivLp (p := 2) (subset_univ (HalfSpace.upper n)) g₀
  have hf₀ := (quasiMeasurePreserving_partialHomeomorph hSymm hE).ae_eq_comp
    (restrictDerivLp_apply_ae (p := 2) hsource f)
  have hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n E.target]
      fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y) := by
    filter_upwards [piolaLoadCLM_apply_ae hE hSymm hbounded f₀, hf₀] with y hy hf
    exact hy.trans (congrArg (_ * ·) hf)
  have hg₀ : (g₀ : ℝ^n → ℝ) =ᵐ[domainMeasure n E.target]
      fun y ↦ |(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y) :=
    (Extension.Lp.zeroExtendLp_agree_ae E.open_target.measurableSet g).trans hg
  have hg₀imp : ∀ᵐ y ∂volume, y ∈ E.target →
      g₀ y = |(fderiv ℝ (fun z ↦ E.symm z) y).det| * f (E.symm y) :=
    (ae_restrict_iff' E.open_target.measurableSet).mp hg₀
  refine ⟨F, ?_, ?_⟩
  · calc
      ‖F‖ ≤ ‖g₀‖ := norm_restrictDerivLp_le _ _
      _ = ‖g‖ := Extension.Lp.norm_zeroExtendLp E.open_target.measurableSet g
      _ ≤ ‖P‖ * ‖f₀‖ := P.le_opNorm f₀
      _ ≤ ‖P‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_left (norm_restrictDerivLp_le hsource f) P.opNorm_nonneg
  filter_upwards [restrictDerivLp_apply_ae (p := 2)
      (subset_univ (HalfSpace.upper n)) g₀,
    ae_restrict_of_ae hg₀imp,
    ae_restrict_mem (HalfSpace.isOpen_upper n).measurableSet] with y hF hg hy hyT
  have hyE : y ∈ E.target := by
    rw [SobolevSpace.Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
    exact ⟨hyT, hy⟩
  exact hF.trans (hg hyE)

end PDE.Elliptic.Regularity.Boundary
