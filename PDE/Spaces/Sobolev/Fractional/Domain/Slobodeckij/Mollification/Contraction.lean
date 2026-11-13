/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.DisplacementNorm
public import PDE.Spaces.Sobolev.Approximation.Mollification.Translation
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Mollification contracts the fractional seminorm

Convolution commutes with translation increments and contracts their `Lᵖ` norms.
Integrating this estimate over the displacement proves contraction of the fractional
seminorm. The argument works for every real order: membership itself supplies the
finite energy needed later for convergence.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Positive-scale mollification contracts the fractional difference seminorm
at every finite exponent `p ≥ 1`, including when that seminorm is infinite. -/
theorem eLpNorm_diffQuot_mollifyVector_le (μ : Mollifier n) {ε : ℝ}
    (hε : 0 < ε) (hp : p ≠ ∞) {u : ℝ^n → F} (hu : MemLp u p volume) :
    eLpNorm (diffQuot n s (mollifyVector μ ε u) (p := p)) p
        (gagliardoProductMeasure n Set.univ) ≤
      eLpNorm (diffQuot n s u (p := p)) p (gagliardoProductMeasure n Set.univ) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  have hp_pos := ENNReal.toReal_pos hp0 hp
  have hu_loc := hu.locallyIntegrable (Fact.out : 1 ≤ p)
  have hm : AEStronglyMeasurable (mollifyVector μ ε u) volume :=
    (mollifyVector_contDiff_of_pos μ hε u hu_loc).continuous.aestronglyMeasurable
  apply (ENNReal.rpow_le_rpow_iff hp_pos).mp
  rw [eLpNorm_diffQuot_rpow_eq_lintegral_displacement hm hp0 hp,
    eLpNorm_diffQuot_rpow_eq_lintegral_displacement hu.aestronglyMeasurable hp0 hp]
  apply lintegral_mono
  intro h
  apply mul_le_mul_right
  rw [← mollifyVector_sub_translate μ hu_loc h]
  have hshift : MemLp (fun x ↦ u (x - h)) p volume := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      hu.comp_measurePreserving (measurePreserving_add_right volume (-h))
  exact ENNReal.rpow_le_rpow
    (MollifyLp.eLpNorm_mollifyVector_le μ hε hp (hshift.sub hu)) hp_pos.le

/-- Mollification preserves whole-space Gagliardo membership for every finite
exponent `p ≥ 1`. No restriction on the real order or the dimension is needed. -/
theorem MemGagliardo.mollifyVector (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (hp : p ≠ ∞) {u : ℝ^n → F} (hu : MemGagliardo n s Set.univ u (p := p)) :
    MemGagliardo n s Set.univ (mollifyVector μ ε u) (p := p) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have huf : MemLp u p volume := by
    simpa only [Measure.restrict_univ] using hu.1
  have hbase : MemLp (Approximation.mollifyVector μ ε u) p volume :=
    (MollifyLp.eLpNorm_mollifyVector_le μ hε hp huf).trans_lt huf.eLpNorm_lt_top
  refine ⟨by simpa only [Measure.restrict_univ] using hbase, ?_⟩
  exact (eLpNorm_diffQuot_mollifyVector_le μ hε hp huf).trans_lt hu.2.eLpNorm_lt_top

end SobolevSpace.Fractional
