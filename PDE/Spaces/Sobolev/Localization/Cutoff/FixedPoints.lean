/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Sobolev fields fixed by a cutoff

A cutoff that fixes the base representative also fixes every weak derivative,
by uniqueness on the open domain. In particular, a cutoff equal to one on the
support of the base fixes the entire Sobolev element.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Multiplication by a cutoff fixes a Sobolev element whenever it fixes the
base representative almost everywhere. -/
theorem cutoffCLM_eq_self_of_base_ae (hΩ : IsOpen Ω)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : W^{1,p}(Ω))
    (h : ∀ᵐ x ∂domainMeasure n Ω,
      κ.toFun x * ((u : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x =
        ((u : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x) :
    cutoffCLM κ u = u := by
  apply WkpSpaceOn.ext_of_base_ae hΩ
  filter_upwards [cutoffCLM_base_apply_ae κ u, h] with x hx hfix
  exact hx.trans hfix

/-- A cutoff equal to one on the base support fixes the Sobolev element.
The supporting set need not be compact or measurable. -/
theorem cutoffCLM_eq_self_of_base_support (hΩ : IsOpen Ω)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : W^{1,p}(Ω))
    {s : Set (ℝ^n)} (hκ : ∀ x ∈ s, κ.toFun x = 1)
    (hu : ∀ᵐ x ∂domainMeasure n Ω, x ∉ s →
      ((u : WkpAmbientOn n 1 p Ω) (baseIndex n 1)) x = 0) :
    cutoffCLM κ u = u := by
  apply cutoffCLM_eq_self_of_base_ae hΩ
  filter_upwards [hu] with x hx
  by_cases hxs : x ∈ s
  · rw [hκ x hxs, one_mul]
  · rw [hx hxs, mul_zero]

end SobolevSpace.GraphSpace
