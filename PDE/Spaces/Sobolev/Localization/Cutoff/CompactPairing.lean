/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Analysis.MeasureTheory.Lp.Localization.Pairing
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Localization.Cutoff.FixedPoints

/-!
# Local coefficient pairings with compactly supported Sobolev fields

The base support controls every first weak derivative: a cutoff equal to one
on that support fixes the entire Sobolev element by weak derivative
uniqueness. Thus locally L² coefficients pair integrably with every stored
coordinate, including first derivatives.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A locally L² coefficient has an integrable product with any stored
coordinate of an H¹ field compactly supported inside the open domain. -/
theorem integrable_mul_coordinate_of_compact_base_support (hΩ : IsOpen Ω)
    (g : ℝ^n → ℝ)
    (hg : ∀ K, IsCompact K → K ⊆ Ω → MemLp g 2 (volume.restrict K))
    (v : H¹(Ω)) {K : Set (ℝ^n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hv : ∀ᵐ x ∂domainMeasure n Ω, x ∉ K →
      ((v : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) x = 0)
    (a : DerivIndex n 1) :
    Integrable (fun x ↦ g x * ((v : WkpAmbientOn n 1 2 Ω) a) x)
      (domainMeasure n Ω) := by
  obtain ⟨κ, hκΩ, hκone, -, -⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ hK hKΩ
  have hfix : cutoffCLM (p := 2) κ v = v :=
    cutoffCLM_eq_self_of_base_support hΩ κ v hκone hv
  have hlocal : MemLp ((tsupport κ.toFun).indicator g) 2 (domainMeasure n Ω) := by
    apply (memLp_indicator_iff_restrict κ.hasCompactSupport.measurableSet.nullMeasurableSet).2
    have hs : tsupport κ.toFun ∩ Ω = tsupport κ.toFun := inter_eq_left.mpr hκΩ
    rw [domainMeasure, Measure.restrict_restrict κ.hasCompactSupport.measurableSet]
    change MemLp g 2 (volume.restrict (tsupport κ.toFun ∩ Ω))
    rw [hs]
    exact hg _ κ.hasCompactSupport hκΩ
  have hsupp :
      (tsupport κ.toFun).indicator
        (((v : WkpAmbientOn n 1 2 Ω) a) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        ((v : WkpAmbientOn n 1 2 Ω) a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [hfix] using cutoffCLM_base_tsupport_indicator_ae κ v
    · simpa only [hfix] using cutoffCLM_singleDeriv_tsupport_indicator_ae κ v i
  exact integrable_mul_of_memLp_indicator hlocal (Lp.memLp _) hsupp

end SobolevSpace.GraphSpace
