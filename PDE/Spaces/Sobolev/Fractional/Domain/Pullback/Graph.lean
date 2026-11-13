/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Estimates
import PDE.Analysis.MeasureTheory.LpNorm.PowerIntegral

/-!
# Pullback of intrinsic fractional graph elements

Physical composition with a chart defines a map between the `GagliardoSpace`s of its
target and source, at all finite exponents at least one. The base p-energy is controlled by
`D`, and the difference p-energy by `D² (L^(n / p.toReal + s))^p.toReal`. No completeness of
the real normed codomain is needed. `Operator` packages the map as a bounded linear operator.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {L D : ℝ≥0}

section General

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable (hs : 0 ≤ (n : ℝ) / p.toReal + s) (hE : Measurable (fun x ↦ E x))
  (hL : LipschitzOnWith L E E.source)
  (hD : Measure.map E (volume.restrict E.source) ≤
    (D : ℝ≥0∞) • volume.restrict E.target)

/-- Physical composition with a chart, as an intrinsic Gagliardo element. -/
def pullback (u : W^{s,p}(E.target; F)) :
    W^{s,p}(E.source; F) :=
  ofFunction ((toLp n s E.target u : ℝ^n → F) ∘ E)
    (Pullback.memGagliardo_comp hs hE hL hD ⟨Lp.memLp _, toLp_mem_domain u⟩)

/-- The underlying Lp class is represented by composition with the chart. -/
theorem toLp_pullback_apply_ae (u : W^{s,p}(E.target; F)) :
    (toLp n s E.source (pullback hs hE hL hD u) : ℝ^n → F) =ᵐ[volume.restrict E.source]
      (toLp n s E.target u : ℝ^n → F) ∘ E :=
  toLp_ofFunction_apply_ae _ _

/-- The base p-energy grows by at most the inverse volume distortion. -/
theorem norm_toLp_pullback_rpow_le (hp : p ≠ ∞)
    (u : W^{s,p}(E.target; F)) :
    ‖toLp n s E.source (pullback hs hE hL hD u)‖ ^ p.toReal ≤
      (D : ℝ) * ‖toLp n s E.target u‖ ^ p.toReal := by
  have hmeas := (Lp.aestronglyMeasurable (toLp n s E.target u)).enorm
  have h := Pullback.lintegral_comp_le_of_map_le hE hD (hmeas.pow_const p.toReal)
  have hsource := Lp.lintegral_enorm_rpow_eq_of_ae hp _
    (toLp_pullback_apply_ae hs hE hL hD u)
  simp only [Function.comp_apply] at hsource
  rw [hsource, Lp.lintegral_enorm_rpow_eq_of_ae hp _ (ae_eq_refl _)] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.toReal_mul, ENNReal.coe_toReal] using hreal

/-- The difference p-energy is controlled by both product volume and distance distortion. -/
theorem norm_differenceQuotient_pullback_rpow_le (hp : p ≠ ∞)
    (u : W^{s,p}(E.target; F)) :
    ‖differenceQuotient n s E.source (pullback hs hE hL hD u)‖ ^ p.toReal ≤
      ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal * (D : ℝ) ^ 2 *
        ‖differenceQuotient n s E.target u‖ ^ p.toReal := by
  have h := Pullback.lintegral_diffQuot_comp_le hs hE hL hD
    (Lp.aestronglyMeasurable (toLp n s E.target u))
  have hsource := Lp.lintegral_enorm_rpow_eq_of_ae hp _
    ((differenceQuotient_apply_ae (pullback hs hE hL hD u)).trans
      (diffQuot_congr_ae (s := s) (p := p) (toLp_pullback_apply_ae hs hE hL hD u)))
  rw [hsource, Lp.lintegral_enorm_rpow_eq_of_ae hp _ (differenceQuotient_apply_ae u)] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _),
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (Real.rpow_nonneg L.coe_nonneg _)] using hreal

/-- Separate bounds for the two components of the fractional graph norm. -/
theorem norm_pullback_rpow_le (hp : p ≠ ∞)
    (u : W^{s,p}(E.target; F)) :
    ‖pullback hs hE hL hD u‖ ^ p.toReal ≤
      (D : ℝ) * ‖toLp n s E.target u‖ ^ p.toReal +
        ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal * (D : ℝ) ^ 2 *
          ‖differenceQuotient n s E.target u‖ ^ p.toReal := by
  rw [norm_rpow_eq hp]
  exact add_le_add (norm_toLp_pullback_rpow_le hs hE hL hD hp u)
    (norm_differenceQuotient_pullback_rpow_le hs hE hL hD hp u)

/-- A finite graph-norm bound at every finite exponent at least one. -/
theorem norm_pullback_le_of_ne_top (hp : p ≠ ∞)
    (u : W^{s,p}(E.target; F)) :
    ‖pullback hs hE hL hD u‖ ≤
      ((D : ℝ) + ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal * (D : ℝ) ^ 2) ^
        (1 / p.toReal) * ‖u‖ := by
  have hr : 0 < p.toReal := p.toReal_pos_iff_ne_top.mpr hp
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (by positivity) hr).mp
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), one_div,
    Real.rpow_inv_rpow (by positivity) hr.ne']
  have hu := norm_rpow_eq hp u
  calc
    _ ≤ _ := norm_pullback_rpow_le hs hE hL hD hp u
    _ ≤ ((D : ℝ) + ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal * (D : ℝ) ^ 2) *
        (‖toLp n s E.target u‖ ^ p.toReal +
          ‖differenceQuotient n s E.target u‖ ^ p.toReal) := by
      nlinarith [mul_nonneg D.coe_nonneg
        (Real.rpow_nonneg (norm_nonneg (differenceQuotient n s E.target u)) p.toReal),
        mul_nonneg (show 0 ≤ ((L : ℝ) ^ ((n : ℝ) / p.toReal + s)) ^ p.toReal *
          (D : ℝ) ^ 2 by positivity)
          (Real.rpow_nonneg (norm_nonneg (toLp n s E.target u)) p.toReal)]
    _ = _ := by rw [hu]

end General

end SobolevSpace.Fractional.GagliardoSpace
