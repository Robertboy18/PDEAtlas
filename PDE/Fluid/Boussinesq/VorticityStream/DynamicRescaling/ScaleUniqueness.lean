/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.VorticityStream.DynamicRescaling.Basic
public import PDE.Analysis.Evolution.ODE.Linear.OffCountable
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Dynamic rescalings with the same rates

If two dynamic rescalings `D`, `D'` satisfy the scale ODEs on `[0, q]` with the same rates and
start from the same scales and the same physical time, and the scales of `D'` do not vanish, then
their scales and clocks agree on `[0, q]`
(`DynamicRescalingData.eqOn_of_satisfiesDynamicScaleODEsAt`): each quotient of scales has
derivative zero, and then so has the difference of the clocks. This identifies a rescaling built
from rates in physical time with `DynamicRescalingData.ofRates` on the times where both are
defined.

## Main results

* `Boussinesq.DynamicRescalingData.eqOn_of_satisfiesDynamicScaleODEsAt`.
-/

@[expose] public section

noncomputable section

open Set

namespace Boussinesq.DynamicRescalingData

set_option linter.missingDocs true

/-- A positive solution of `f' = r f` and a nonvanishing solution of `g' = r g` on `[0, q]`
starting from the same value agree there. -/
private theorem eqOn_of_hasDerivAt_mul {f g r : ℝ → ℝ} {q : ℝ}
    (hf : ∀ σ ∈ Icc 0 q, HasDerivAt f (r σ * f σ) σ)
    (hg : ∀ σ ∈ Icc 0 q, HasDerivAt g (r σ * g σ) σ) (hg0 : ∀ σ ∈ Icc 0 q, g σ ≠ 0)
    (h0 : f 0 = g 0) : ∀ σ ∈ Icc 0 q, f σ = g σ := by
  have hd : ∀ σ ∈ Icc 0 q, HasDerivAt (fun s ↦ f s / g s) 0 σ := fun σ hσ ↦
    (HasDerivAt.div (hf σ hσ) (hg σ hσ) (hg0 σ hσ)).congr_deriv (by
      field_simp
      ring)
  have hc : ContinuousOn (fun s ↦ f s / g s) (Icc 0 q) := fun σ hσ ↦
    (hd σ hσ).continuousAt.continuousWithinAt
  have hconst := PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero hc
    fun σ hσ ↦ hd σ (Ioo_subset_Icc_self hσ)
  intro σ hσ
  have h := hconst σ hσ
  have hq : (0 : ℝ) ∈ Icc 0 q := ⟨le_rfl, hσ.1.trans hσ.2⟩
  rw [h0, div_self (hg0 0 hq)] at h
  rwa [div_eq_one_iff_eq (hg0 σ hσ)] at h

/-- **Rescalings with the same rates agree.** If `D` and `D'` satisfy the scale ODEs on `[0, q]`,
have the same rates there, the same initial scales and physical time, and the scales of `D'` do
not vanish on `[0, q]`, then their clocks and scales agree on `[0, q]`. -/
theorem eqOn_of_satisfiesDynamicScaleODEsAt {D D' : DynamicRescalingData} {q : ℝ}
    (hD : ∀ σ ∈ Icc 0 q, SatisfiesDynamicScaleODEsAt D σ)
    (hD' : ∀ σ ∈ Icc 0 q, SatisfiesDynamicScaleODEsAt D' σ)
    (hcω : ∀ σ ∈ Icc 0 q, D.vorticityRate σ = D'.vorticityRate σ)
    (hcl : ∀ σ ∈ Icc 0 q, D.spatialRate σ = D'.spatialRate σ)
    (hcθ : ∀ σ ∈ Icc 0 q, D.temperatureRate σ = D'.temperatureRate σ)
    (hω0 : D.vorticityScale 0 = D'.vorticityScale 0) (hl0 : D.spatialScale 0 = D'.spatialScale 0)
    (hθ0 : D.temperatureScale 0 = D'.temperatureScale 0)
    (ht0 : D.physicalTime 0 = D'.physicalTime 0)
    (hω : ∀ σ ∈ Icc 0 q, D'.vorticityScale σ ≠ 0) (hl : ∀ σ ∈ Icc 0 q, D'.spatialScale σ ≠ 0)
    (hθ : ∀ σ ∈ Icc 0 q, D'.temperatureScale σ ≠ 0) :
    ∀ σ ∈ Icc 0 q, D.physicalTime σ = D'.physicalTime σ ∧
      D.vorticityScale σ = D'.vorticityScale σ ∧ D.spatialScale σ = D'.spatialScale σ ∧
      D.temperatureScale σ = D'.temperatureScale σ := by
  have hCω := eqOn_of_hasDerivAt_mul (f := D.vorticityScale) (g := D'.vorticityScale)
    (r := D'.vorticityRate) (fun σ hσ ↦ (hD σ hσ).vorticityScale_hasDerivAt.congr_deriv
      (by rw [hcω σ hσ])) (fun σ hσ ↦ (hD' σ hσ).vorticityScale_hasDerivAt) hω hω0
  have hCl := eqOn_of_hasDerivAt_mul (f := D.spatialScale) (g := D'.spatialScale)
    (r := fun σ ↦ -D'.spatialRate σ) (fun σ hσ ↦ (hD σ hσ).spatialScale_hasDerivAt.congr_deriv
      (by rw [hcl σ hσ])) (fun σ hσ ↦ (hD' σ hσ).spatialScale_hasDerivAt) hl hl0
  have hCθ := eqOn_of_hasDerivAt_mul (f := D.temperatureScale) (g := D'.temperatureScale)
    (r := D'.temperatureRate) (fun σ hσ ↦ (hD σ hσ).temperatureScale_hasDerivAt.congr_deriv
      (by rw [hcθ σ hσ])) (fun σ hσ ↦ (hD' σ hσ).temperatureScale_hasDerivAt) hθ hθ0
  have hd : ∀ σ ∈ Icc 0 q, HasDerivAt (fun s ↦ D.physicalTime s - D'.physicalTime s) 0 σ :=
    fun σ hσ ↦ ((hD σ hσ).physicalTime_hasDerivAt.sub (hD' σ hσ).physicalTime_hasDerivAt
      ).congr_deriv (by rw [hCω σ hσ, sub_self])
  have hc : ContinuousOn (fun s ↦ D.physicalTime s - D'.physicalTime s) (Icc 0 q) :=
    fun σ hσ ↦ (hd σ hσ).continuousAt.continuousWithinAt
  have hconst := PDE.Analysis.Evolution.eqOn_const_of_hasDerivAt_zero hc
    fun σ hσ ↦ hd σ (Ioo_subset_Icc_self hσ)
  intro σ hσ
  refine ⟨?_, hCω σ hσ, hCl σ hσ, hCθ σ hσ⟩
  have h := hconst σ hσ
  rw [ht0, sub_self, sub_eq_zero] at h
  exact h

end Boussinesq.DynamicRescalingData
