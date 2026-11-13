/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Displacement
import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Energy

/-!
# Displacement energy of a Gagliardo-space element

The weighted displacement integral is exactly the power of the graph's
difference-quotient norm. This identifies the energy used by signed convolution
kernels with a component of the fractional norm, in every dimension.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s p : ℝ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fact (1 ≤ ENNReal.ofReal p)]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
/-- The exponent is positive, since `1 ≤ ENNReal.ofReal p`. -/
private theorem pos_of_one_le_ofReal : 0 < p := by
  by_contra h
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
  rw [ENNReal.ofReal_of_nonpos (not_lt.mp h)] at h1
  simp at h1

/-- Weighted displacement energy is the power of the graph difference norm. -/
theorem lintegral_weighted_displacement_eq
    (g : GagliardoSpace n s Set.univ (p := ENNReal.ofReal p) (F := F)) :
    (∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
      ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + s * p))) *
        ENNReal.ofReal (‖toLp n s Set.univ g (x - h) - toLp n s Set.univ g x‖ ^ p)) =
      ‖differenceQuotient n s Set.univ g‖ₑ ^ p := by
  have hp : 0 < p := pos_of_one_le_ofReal
  have hg : AEStronglyMeasurable (toLp n s Set.univ g) volume :=
    (Lp.stronglyMeasurable _).aestronglyMeasurable
  rw [← lintegral_enorm_sub_div_eq_weighted_displacement hg hp]
  rw [Lp.enorm_def]
  have hpow := eLpNorm_nnreal_pow_eq_lintegral
    (p := p.toNNReal) (Real.toNNReal_pos.mpr hp).ne'
    (Lp.aestronglyMeasurable (differenceQuotient n s Set.univ g))
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal p hp.le] at hpow
  rw [hpow]
  have hdiff := differenceQuotient_apply_ae g
  simp only [gagliardoProductMeasure, Measure.restrict_univ] at hdiff ⊢
  apply lintegral_congr_ae
  filter_upwards [hdiff] with z hz
  rw [hz]
  simpa only [ENNReal.toReal_ofReal hp.le] using
    (enorm_diffQuot_rpow (n := n) (s := s) (toLp n s Set.univ g) z
      (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).symm

/-- The fractional displacement energy is bounded by the full graph norm. -/
theorem lintegral_weighted_displacement_le
    (g : GagliardoSpace n s Set.univ (p := ENNReal.ofReal p) (F := F)) :
    (∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
      ENNReal.ofReal (‖h‖ ^ (-((n : ℝ) + s * p))) *
        ENNReal.ofReal (‖toLp n s Set.univ g (x - h) - toLp n s Set.univ g x‖ ^ p)) ≤
      ‖g‖ₑ ^ p := by
  rw [lintegral_weighted_displacement_eq]
  apply ENNReal.rpow_le_rpow _ pos_of_one_le_ofReal.le
  exact WithLp.enorm_snd_le _ g.val

end SobolevSpace.Fractional.GagliardoSpace
