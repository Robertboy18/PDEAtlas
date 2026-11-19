/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integration in tangential-normal coordinates

We record the measure-theoretic change of variables from the upper
half-space to tangential coordinates and a positive normal coordinate.
The coordinate equivalence preserves Euclidean volume, so no Jacobian factor
appears.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.HalfSpace

open MeasureTheory Set

variable {n : ℕ}

/-- Lebesgue measure on the positive normal half-line. -/
abbrev positiveNormalMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))

/-- Integrability in positive tangential-normal coordinates is equivalent
to integrability on the upper half-space. -/
theorem integrable_comp_joinTangentialNormal_iff_integrableOn_upper
    (g : ℝ^(n + 1) → ℝ) :
    Integrable (fun p ↦ g (joinTangentialNormal p))
        ((volume : Measure (ℝ^n)).prod positiveNormalMeasure) ↔
      IntegrableOn g
        (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩) := by
  let e := tangentialNormalMeasurableEquiv (n := n)
  let S : Set (ℝ^n × ℝ) := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  have hprod :
      (volume : Measure (ℝ^n)).prod positiveNormalMeasure =
        ((volume : Measure (ℝ^n)).prod (volume : Measure ℝ)).restrict S := by
    calc
      _ = ((volume : Measure (ℝ^n)).restrict Set.univ).prod
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
            simp [positiveNormalMeasure]
      _ = _ := by
        simpa [S] using
          (Measure.prod_restrict
            (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure ℝ))
            Set.univ (Set.Ioi (0 : ℝ)))
  rw [hprod]
  change IntegrableOn (fun p ↦ g (joinTangentialNormal p)) S
      ((volume : Measure (ℝ^n)).prod (volume : Measure ℝ)) ↔ _
  rw [← Measure.volume_eq_prod (ℝ^n) ℝ]
  have htransport :=
    (measurePreserving_tangentialNormalMeasurableEquiv
      (n := n)).integrableOn_comp_preimage e.measurableEmbedding
      (f := fun p : ℝ^n × ℝ ↦ g (joinTangentialNormal p)) (s := S)
  have he :
      (e : ℝ^(n + 1) → ℝ^n × ℝ) = splitTangentialNormal := by
    funext x
    exact tangentialNormalMeasurableEquiv_apply x
  rw [he] at htransport
  simpa [S, Function.comp_def, upper_eq_preimage_split_snd_Ioi] using
    htransport.symm

/-- Integration over positive tangential-normal coordinates agrees with
integration over the upper half-space. -/
theorem integral_joinTangentialNormal_eq_integral_upper
    (g : ℝ^(n + 1) → ℝ) :
    (∫ p, g (joinTangentialNormal p)
      ∂((volume : Measure (ℝ^n)).prod positiveNormalMeasure)) =
      ∫ x in (@HalfSpace.upper (n + 1) ⟨Nat.zero_lt_succ n⟩), g x := by
  let e := tangentialNormalMeasurableEquiv (n := n)
  let S : Set (ℝ^n × ℝ) := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  have htransport :=
    (measurePreserving_tangentialNormalMeasurableEquiv
      (n := n)).setIntegral_preimage_emb
      e.measurableEmbedding
      (fun p : ℝ^n × ℝ ↦ g (joinTangentialNormal p)) S
  have hprod :
      (volume : Measure (ℝ^n)).prod positiveNormalMeasure =
        ((volume : Measure (ℝ^n)).prod (volume : Measure ℝ)).restrict S := by
    calc
      _ = ((volume : Measure (ℝ^n)).restrict Set.univ).prod
          ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))) := by
            simp [positiveNormalMeasure]
      _ = _ := by
        simpa [S] using
          (Measure.prod_restrict
            (μ := (volume : Measure (ℝ^n))) (ν := (volume : Measure ℝ))
            Set.univ (Set.Ioi (0 : ℝ)))
  rw [hprod]
  change (∫ p in S, g (joinTangentialNormal p)
      ∂((volume : Measure (ℝ^n)).prod (volume : Measure ℝ))) = _
  have htransport' :
      (∫ x in e ⁻¹' S, g (joinTangentialNormal (e x))) =
        ∫ p in S, g (joinTangentialNormal p)
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

end Trace.HalfSpace
end SobolevSpace
