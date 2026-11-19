/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Composition.Smooth
public import PDE.Spaces.Sobolev.Calculus.Composition.AbsoluteValue.Approximation

/-!
# Positive parts in the supported Sobolev closure

Taking the positive part preserves `W^{1,p}_0` for every finite `p ≥ 1`.
The argument uses strong approximation, so it includes `p = 1` and needs
neither a boundary atlas nor finite measure.

Smooth zero-preserving composition preserves the supported closure. Let the
smoothing scale in the absolute-value approximation tend to zero. Closedness
then gives the absolute value, and linearity gives the positive part.

For measurable sets the conclusion concerns the supported-core definition.
On open sets this is the usual zero-boundary Sobolev space.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter Function MeasureTheory Set
open scoped ENNReal Topology Sobolev
open ZeroTrace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restricting the absolute value of the zero extension gives another
element of the supported Sobolev closure for every finite exponent. -/
theorem restrict_absoluteValue_zeroExtendWkp0_mem
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (u : W₀^{1,p}(Ω)) :
    restrictCLM hΩ (subset_univ Ω) (absoluteValue (zeroExtendWkp0 hΩ u)) ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j :=
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one)
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := tendsto_smoothAbsComposition hp (zeroExtendWkp0 hΩ u) ε hε hε0
  apply (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := Ω)).isClosed'.mem_of_tendsto
    (((restrictCLM hΩ (subset_univ Ω)).continuous.tendsto _).comp hconv)
  exact Eventually.of_forall fun j ↦
    restrict_smoothComposition_zeroExtendWkp0_mem hΩ hp
      (PDE.Analysis.Calculus.contDiff_smoothAbs (hε j))
      (PDE.Analysis.Calculus.continuous_smoothAbsSlope (hε j))
      (PDE.Analysis.Calculus.hasDerivAt_smoothAbs (hε j))
      (PDE.Analysis.Calculus.smoothAbs_zero (ε j) (hε j).le)
      (PDE.Analysis.Calculus.lipschitzWith_smoothAbs (hε j))
      (PDE.Analysis.Calculus.abs_smoothAbsSlope_le_one (hε j)) u

/-- Absolute value in the supported `W^{1,p}` closure, constructed by
smooth approximation in the full Sobolev norm. -/
def absoluteValueWkp0 {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (u : W₀^{1,p}(Ω)) : W₀^{1,p}(Ω) :=
  ⟨restrictCLM hΩ (subset_univ Ω) (absoluteValue (zeroExtendWkp0 hΩ u)),
    restrict_absoluteValue_zeroExtendWkp0_mem hΩ hp u⟩

/-- The positive part in the supported `W^{1,p}` closure. -/
def positivePartWkp0 {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (u : W₀^{1,p}(Ω)) : W₀^{1,p}(Ω) :=
  (1 / 2 : ℝ) • (u + absoluteValueWkp0 hΩ hp u)

/-- The positive part in the supported closure is the restriction of the
positive part of the global zero extension. -/
private theorem positivePartWkp0_coe
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (u : W₀^{1,p}(Ω)) :
    (positivePartWkp0 hΩ hp u : W^{1,p}(Ω)) =
      restrictCLM hΩ (subset_univ Ω) (positivePart (zeroExtendWkp0 hΩ u)) := by
  have hrestrict :
      restrictCLM hΩ (subset_univ Ω) (zeroExtendWkp0 hΩ u) =
        (u : W^{1,p}(Ω)) := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    exact restrict_zeroExtendWkp0_coordinate hΩ u a
  simp only [positivePartWkp0, positivePart, map_smul, map_add, hrestrict]
  rfl

/-- The constructed positive part represents `max u 0` almost everywhere. -/
theorem positivePartWkp0_base_ae
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (u : W₀^{1,p}(Ω)) :
    (wkpCoordinateCLM (baseIndex n 1)
      (positivePartWkp0 hΩ hp u : W^{1,p}(Ω)) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ max ((wkpCoordinateCLM (baseIndex n 1)
        (u : W^{1,p}(Ω)) : ℝ^n → ℝ) x) 0 := by
  rw [positivePartWkp0_coe]
  have hglobal := ae_mono (domainMeasure_le (subset_univ Ω))
    (positivePart_base_ae (zeroExtendWkp0 hΩ u))
  filter_upwards
    [restrictCLM_apply_ae hΩ (subset_univ Ω) (positivePart (zeroExtendWkp0 hΩ u))
      (baseIndex n 1),
     hglobal, zeroExtendWkp0_coordinate_ae_on hΩ u (baseIndex n 1)] with x hx hy hz
  exact hx.trans (hy.trans (congrArg (fun t : ℝ ↦ max t 0) hz))

/-- The weak gradient of the positive part is the original gradient on
`{u > 0}` and zero elsewhere, including the zero level set. -/
theorem positivePartWkp0_derivative_ae
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hp : p ≠ ∞)
    (u : W₀^{1,p}(Ω)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i)
      (positivePartWkp0 hΩ hp u : W^{1,p}(Ω)) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ if 0 < (wkpCoordinateCLM (baseIndex n 1)
        (u : W^{1,p}(Ω)) : ℝ^n → ℝ) x then
          (wkpCoordinateCLM (singleDerivIndex n i)
            (u : W^{1,p}(Ω)) : ℝ^n → ℝ) x else 0 := by
  rw [positivePartWkp0_coe]
  have hglobal := ae_mono (domainMeasure_le (subset_univ Ω))
    (positivePart_derivative_indicator_ae (zeroExtendWkp0 hΩ u) i)
  filter_upwards
    [restrictCLM_apply_ae hΩ (subset_univ Ω) (positivePart (zeroExtendWkp0 hΩ u))
      (singleDerivIndex n i),
     hglobal, zeroExtendWkp0_coordinate_ae_on hΩ u (baseIndex n 1),
     zeroExtendWkp0_coordinate_ae_on hΩ u (singleDerivIndex n i)] with x hx hy hb hd
  exact hx.trans (hy.trans
    (congrArg₂ (fun s t : ℝ ↦ if 0 < s then t else 0) hb hd))

end SobolevSpace.GraphSpace
