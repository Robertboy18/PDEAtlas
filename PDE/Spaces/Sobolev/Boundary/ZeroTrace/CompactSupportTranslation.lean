/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Compactness.Translation.H1
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport

/-!
# Translated compact support and zero trace

Global `H¹` translation combined with the compact-support criterion for membership in
`H¹₀`. The corollary is kept apart so that the compact-support theorem does not import
the Rellich compactness development.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A translated compactly supported global `H¹` field still restricts to
`H¹₀(Ω)` whenever the translated representative retains a positive collar
inside `Ω`. -/
theorem restrict_translateH1_mem_H10_of_compactSupport_collar
    (hΩopen : IsOpen Ω) (μ : Approximation.Mollifier n)
    (a : ℝ^n) (U : H¹(ℝ^n)) (f : ℝ^n → ℝ)
    (hUbase :
      ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
        DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] f)
    (hUcs : HasCompactSupport f)
    {R δ : ℝ} (hRnonneg : 0 ≤ R) (hδ : 0 < δ)
    (hR : tsupport μ.ρ ⊆ Metric.closedBall (0 : ℝ^n) R)
    (hcollar : Metric.cthickening δ (tsupport (fun x ↦ f (x + a))) ⊆ Ω) :
    restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet
        (subset_univ Ω) (translateH1 (n := n) a U) ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  let fa : ℝ^n → ℝ := fun x ↦ f (x + a)
  have hpres : MeasurePreserving (Rellich.translationContinuousMap a)
      (domainMeasure n Set.univ) (domainMeasure n Set.univ) :=
    Rellich.translationMeasurePreserving (n := n) a
  have hUbaseShift :
      (fun x ↦
        ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)) (x + a)) =ᵐ[MeasureTheory.volume] fa := by
    simpa [fa, domainMeasure, Function.comp_def, Rellich.translationContinuousMap] using
      hpres.quasiMeasurePreserving.ae_eq_comp
        (by simpa [domainMeasure] using hUbase)
  have htranslated := Rellich.translateLp_apply_ae (n := n) 2 a
    ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))
  have hbase :
      (((((translateH1 (n := n) a U : H¹(ℝ^n)) :
        WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
          DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume] fa := by
    have ht :
        (((((translateH1 (n := n) a U : H¹(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
            DerivLp n 2 Set.univ) : ℝ^n → ℝ)) =ᵐ[MeasureTheory.volume]
          fun x ↦
            ((((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) :
              DerivLp n 2 Set.univ) : ℝ^n → ℝ)) (x + a) := by
      simpa [translateH1_apply, domainMeasure] using htranslated
    exact ht.trans hUbaseShift
  have hfacs : HasCompactSupport fa := by
    simpa [fa, Function.comp_def] using
      hUcs.comp_homeomorph (Homeomorph.addRight a)
  exact restrict_mem_H10_of_compactSupport_collar hΩopen μ
    (translateH1 (n := n) a U) fa hbase hfacs hRnonneg hδ hR
    (by simpa [fa] using hcollar)

end SobolevSpace.GraphSpace
