/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Dominated convergence in the extended Lp norm

An integrable bound on the p-th powers of the norms turns pointwise convergence
to zero into convergence in `Lᵖ`. The exponent may be any finite positive real
number; neither a normed `Lᵖ` space nor completeness of the codomain is needed.
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι F : Type*} [MeasurableSpace α] [SeminormedAddCommGroup F]
  {μ : Measure α} {l : Filter ι} [l.IsCountablyGenerated]
  {p : ℝ≥0∞} {f : ι → α → F}

/-- An integrable majorant for the p-th powers controls convergence of the
extended `Lᵖ` norm, for every finite positive exponent. -/
theorem tendsto_eLpNorm_zero_of_dominated_convergence
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (bound : α → ℝ≥0∞)
    (hmeas : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ₑ ^ p.toReal ≤ bound x)
    (hfinite : (∫⁻ x, bound x ∂μ) ≠ ∞)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun i ↦ f i x) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (f i) p μ) l (𝓝 0) := by
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hint := tendsto_lintegral_filter_of_dominated_convergence'
    (f := fun _ : α ↦ (0 : ℝ≥0∞)) bound
    (hmeas.mono fun i hi ↦ hi.enorm.pow_const p.toReal) hbound hfinite
    (hzero.mono fun x hx ↦ by
      simpa only [enorm_eq_nnnorm, nnnorm_zero, ENNReal.coe_zero,
        ENNReal.zero_rpow_of_pos hr] using
        hx.enorm.ennrpow_const p.toReal)
  have hroot := hint.ennrpow_const p.toReal⁻¹
  simp only [lintegral_zero, ENNReal.zero_rpow_of_pos (inv_pos.mpr hr)] at hroot
  apply hroot.congr'
  filter_upwards [hmeas] with i hi
  simpa only [one_div] using (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hi).symm

end MeasureTheory
