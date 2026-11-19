/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.DomainLipschitz
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore
public import PDE.Spaces.Sobolev.Calculus.Composition.PositivePart.Continuity

/-!
# Positive parts on C¹ extension domains

The domain Lipschitz composition with `max · 0` equals restriction
of the whole-space positive part of the extension. This identifies
its indicator derivative and proves strong continuity for every finite exponent.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {Ω : Set ℝ^n} [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The positive-part composition is the restricted whole-space positive part. -/
theorem lipschitzCompositionOn_posPart_eq_restrict
    (U : W^{1,p}(Ω)) :
    lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U =
      restrictCLM hΩ.isOpen.measurableSet (subset_univ Ω)
        (positivePart (Extension.C1.extensionCLM U)) := by
  apply wkpBaseCoordinateCLM_injective hΩ.isOpen
  apply Lp.ext
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  filter_upwards [lipschitzCompositionOn_base_ae hΩ.isOpen Lp.lipschitzWith_pos_part U,
    restrictCLM_apply_ae hΩ.isOpen.measurableSet (subset_univ Ω)
      (positivePart (Extension.C1.extensionCLM U)) (baseIndex n 1),
    (positivePart_base_ae (Extension.C1.extensionCLM U)).filter_mono (ae_mono hmeasure),
    Extension.C1.extensionCLM_agree_ae U] with x hlocal hrestrict hglobal hext
  exact hlocal.trans ((congrArg (fun t : ℝ ↦ max t 0) hext.symm).trans
    (hglobal.symm.trans hrestrict.symm))

/-- The domain positive part is strongly continuous, including `p = 1`. -/
theorem continuous_lipschitzCompositionOn_posPart (hp : p ≠ ∞) :
    Continuous (lipschitzCompositionOn (n := n) (p := p) (Ω := Ω)
      hΩ.isOpen Lp.lipschitzWith_pos_part) := by
  change Continuous (fun U : W^{1,p}(Ω) ↦
    lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U)
  simp_rw [lipschitzCompositionOn_posPart_eq_restrict]
  exact (restrictCLM hΩ.isOpen.measurableSet (subset_univ Ω)).continuous.comp
    ((continuous_positivePart hp).comp Extension.C1.extensionCLM.continuous)

/-- Every derivative of the domain positive part is localized to the positive set. -/
theorem lipschitzCompositionOn_posPart_derivative_ae
    (U : W^{1,p}(Ω)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i)
      (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < (wkpCoordinateCLM (baseIndex n 1) U : ℝ^n → ℝ) x then
          (wkpCoordinateCLM (singleDerivIndex n i) U : ℝ^n → ℝ) x else 0 := by
  rw [lipschitzCompositionOn_posPart_eq_restrict]
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  filter_upwards [restrictCLM_apply_ae hΩ.isOpen.measurableSet (subset_univ Ω)
      (positivePart (Extension.C1.extensionCLM U)) (singleDerivIndex n i),
    (positivePart_derivative_indicator_ae (Extension.C1.extensionCLM U) i).filter_mono
      (ae_mono hmeasure),
    DomainComposition.extension_coordinate_ae hΩ.isOpen Extension.C1.operator U
      (baseIndex n 1),
    DomainComposition.extension_coordinate_ae hΩ.isOpen Extension.C1.operator U
      (singleDerivIndex n i)] with x hr hp hb hd
  simp only [Extension.C1.operator] at hb hd
  exact hr.trans (hp.trans (congrArg₂ (fun s t : ℝ ↦ if 0 < s then t else 0) hb hd))

/-- All coordinates of the positive part are restricted to its positive set. -/
theorem lipschitzCompositionOn_posPart_coordinate_ae
    (U : W^{1,p}(Ω)) (a : DerivIndex n 1) :
    (wkpCoordinateCLM a (lipschitzCompositionOn hΩ.isOpen Lp.lipschitzWith_pos_part U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦
        if 0 < wkpBaseCoordinateCLM U x then wkpCoordinateCLM a U x else 0 := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    filter_upwards [lipschitzCompositionOn_base_ae hΩ.isOpen Lp.lipschitzWith_pos_part U] with x hx
    change _ = max (wkpBaseCoordinateCLM U x) 0 at hx
    change _ = if 0 < wkpBaseCoordinateCLM U x then wkpBaseCoordinateCLM U x else 0
    apply hx.trans
    split_ifs with h
    · exact max_eq_left h.le
    · exact max_eq_right (le_of_not_gt h)
  · subst a
    exact lipschitzCompositionOn_posPart_derivative_ae U i

end SobolevSpace.GraphSpace
