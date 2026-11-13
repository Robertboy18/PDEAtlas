/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Differentiating Sobolev translations in Lp

For a whole-space Sobolev function at finite exponent, translation in a coordinate direction
is differentiable as an Lp-valued curve. Its derivative is the translated weak derivative.
This allows the Banach-space mean value inequality to be applied after restriction to an
interior set.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set Rellich
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The strong difference-quotient limit, with the punctured neighbourhood filter. -/
theorem tendsto_differenceQuotientLp_base (hp : p ≠ ∞) (i : Fin n)
    (U : W^{1,p}(ℝ^n)) :
    Tendsto (fun h ↦ differenceQuotientLp p i h (wkpBaseCoordinateCLM U))
      (𝓝[≠] 0) (𝓝 (wkpCoordinateCLM (singleDerivIndex n i) U)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro h hh
  have he : ∀ᶠ m in atTop, h m ≠ 0 := by
    simpa using (tendsto_nhdsWithin_iff.mp hh).2
  let k (m : ℕ) := if h m = 0 then 1 else h m
  have hk : k =ᶠ[atTop] h := he.mono fun m hm ↦ by simp [k, hm]
  have hkzero : Tendsto k atTop (𝓝 0) :=
    (hh.mono_right nhdsWithin_le_nhds).congr' hk.symm
  have hkne (m : ℕ) : k m ≠ 0 := by
    simp only [k]
    split_ifs <;> simp_all
  exact (tendsto_differenceQuotientLp_base_of_ne_top p hp i U k hkzero hkne).congr'
    (hk.mono fun _ hm ↦ congrArg (fun a ↦
      differenceQuotientLp p i a (wkpBaseCoordinateCLM U)) hm)

/-- The derivative of the coordinate translation curve is the translated weak derivative. -/
theorem hasDerivAt_translateLp_base_of_ne_top (hp : p ≠ ∞) (i : Fin n)
    (U : W^{1,p}(ℝ^n)) (t : ℝ) :
    HasDerivAt (fun s ↦ translateLp p (coordinateStep i s) (wkpBaseCoordinateCLM U))
      (translateLp p (coordinateStep i t) (wkpCoordinateCLM (singleDerivIndex n i) U))
      t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have ht := ((translateLp p (coordinateStep i t)).continuous.tendsto
    (wkpCoordinateCLM (singleDerivIndex n i) U)).comp
      (tendsto_differenceQuotientLp_base hp i U)
  convert ht using 1
  ext h
  simp only [Function.comp_apply, differenceQuotientLp_apply, map_smul, map_sub,
    translateLp_add]
  rw [show coordinateStep i (t + h) = coordinateStep i t + coordinateStep i h by
    simp only [coordinateStep, add_smul]]

end SobolevSpace.GraphSpace.DifferenceQuotient
