/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.Slicing.NormalIntegral

/-!
# Nonnegative integration in tangential-normal coordinates

Tangential-normal coordinates preserve volume on the upper half-space. The nonnegative
integral form lets us change coordinates before proving that an energy is finite.
-/

@[expose] public section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

/-- Nonnegative integration in tangential-normal coordinates agrees with integration
over the upper half-space, even before finiteness or measurability is established. -/
theorem lintegral_joinTangentialNormal_eq_lintegral_upper
    (g : ℝ^(n + 1) → ℝ≥0∞) :
    (∫⁻ p, g (joinTangentialNormal p)
      ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) =
      ∫⁻ x in ℝ^(n + 1)₊, g x := by
  let e := tangentialNormalMeasurableEquiv (n := n)
  let S : Set (ℝ^n × ℝ) := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  have htransport :=
    (measurePreserving_tangentialNormalMeasurableEquiv
      (n := n)).setLIntegral_comp_preimage_emb
      e.measurableEmbedding
      (fun p : ℝ^n × ℝ ↦ g (joinTangentialNormal p)) S
  have hprod :
      (volume : Measure (ℝ^n)).prod positiveNormalMeasure =
        ((volume : Measure (ℝ^n)).prod (volume : Measure ℝ)).restrict S := by
    simpa [positiveNormalMeasure, S] using
      (Measure.prod_restrict
        (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure ℝ))
        Set.univ (Set.Ioi (0 : ℝ)))
  rw [hprod]
  change (∫⁻ p in S, g (joinTangentialNormal p)
      ∂((volume : Measure (ℝ^n)).prod (volume : Measure ℝ))) = _
  have htransport' :
      (∫⁻ x in e ⁻¹' S, g (joinTangentialNormal (e x))) =
        ∫⁻ p in S, g (joinTangentialNormal p)
          ∂((volume : Measure (ℝ^n)).prod (volume : Measure ℝ)) := by
    simpa only [Measure.volume_eq_prod] using htransport
  rw [← htransport']
  dsimp [e, S]
  rw [show (tangentialNormalMeasurableEquiv (n := n) :
      ℝ^(n + 1) → ℝ^n × ℝ) = splitTangentialNormal by
    funext x
    exact tangentialNormalMeasurableEquiv_apply x]
  simp only [join_splitTangentialNormal]
  rw [← upper_eq_preimage_split_snd_Ioi (n := n)]

end SobolevSpace.Trace.HalfSpace
