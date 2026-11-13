/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence
public import PDE.Analysis.MeasureTheory.Lp.WeightedWeakLimit

/-!
# Weighted derivative energy of a weak `H¹` limit

Let `uᵢ` be uniformly bounded in `H¹(ℝ)` with real `L²` bases converging strongly to that
of `U`, so that the derivatives converge only weakly. Let `ψ ≥ 0` and `h` be continuous on an
open interval `(a, b)`; `ψ` may be singular at the endpoints. If eventually the densities
`(uᵢ' - h)² ψ` are integrable on `(a, b)` with integrals at most `Mᵢ`, and `Mᵢ → m`, then
`(U' - h)² ψ` is integrable on `(a, b)` with integral at most `m`: this is
`PDE.Analysis.integral_sq_sub_mul_le_of_pairing` for the weakly convergent derivatives.

## Main results

* `tendsto_integral_mul_realLineDerivative`: the derivatives converge weakly in `L²`.
* `integral_sq_realLineDerivative_sub_mul_le`: weak lower semicontinuity of a weighted
  derivative energy on an interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {ι : Type*} {l : Filter ι} {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {B : ℝ}

/-- Weak convergence of the derivative coordinate, tested against a fixed square
integrable function. -/
theorem tendsto_integral_mul_realLineDerivative
    (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    {w : ℝ → ℝ} (hw : MemLp w 2 volume) :
    Tendsto (fun i ↦ ∫ x, w x * realLineCoordinateCLM (singleDerivIndex 1 0) (u i) x) l
      (𝓝 (∫ x, w x * realLineCoordinateCLM (singleDerivIndex 1 0) U x)) := by
  have hweak := tendsto_weak_realLineCoordinate_of_h1_bound u U hbound hbase
    (singleDerivIndex 1 0)
  have h := PDE.Analysis.WeakCompactness.tendsto_evaluation hweak (innerSL ℝ (hw.toLp w))
  have hpair (V : W^{1,2}(ℝ^1)) :
      innerSL ℝ (hw.toLp w) ((toWeakSpace ℝ (Lp ℝ 2 (volume : Measure ℝ))).symm
        (toWeakSpace ℝ (Lp ℝ 2 (volume : Measure ℝ))
          (realLineCoordinateCLM (singleDerivIndex 1 0) V))) =
        ∫ x, w x * realLineCoordinateCLM (singleDerivIndex 1 0) V x := by
    rw [LinearEquiv.symm_apply_apply, innerSL_apply_apply, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw.coeFn_toLp] with x hx
    rw [hx, Real.inner_apply]
  simpa only [hpair] using h

/-- Weak lower semicontinuity of a weighted derivative energy on an interval: if the bases
of a bounded `H¹` family converge in `L²` to that of `U`, and eventually `(uᵢ' - h)² ψ` is
integrable on `(a, b)` with `∫ₐᵇ (uᵢ' - h)² ψ ≤ Mᵢ`, where `Mᵢ → m`, then `(U' - h)² ψ` is
integrable on `(a, b)` with integral at most `m`. The weight `ψ ≥ 0` and the shift `h` need
only be continuous on the open interval. -/
theorem integral_sq_realLineDerivative_sub_mul_le [l.NeBot]
    (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    {a b : ℝ} {h ψ : ℝ → ℝ}
    (hh : ContinuousOn h (Ioo a b)) (hψ : ContinuousOn ψ (Ioo a b))
    (hψnonneg : ∀ x ∈ Ioo a b, 0 ≤ ψ x) {M : ι → ℝ} {m : ℝ} (hM : Tendsto M l (𝓝 m))
    (henergy : ∀ᶠ i in l, IntegrableOn
      (fun x ↦ (realLineCoordinateCLM (singleDerivIndex 1 0) (u i) x - h x) ^ 2 * ψ x)
        (Ioo a b) ∧
      ∫ x in Ioo a b,
        (realLineCoordinateCLM (singleDerivIndex 1 0) (u i) x - h x) ^ 2 * ψ x ≤ M i) :
    IntegrableOn (fun x ↦ (realLineCoordinateCLM (singleDerivIndex 1 0) U x - h x) ^ 2 * ψ x)
        (Ioo a b) ∧
      ∫ x in Ioo a b,
        (realLineCoordinateCLM (singleDerivIndex 1 0) U x - h x) ^ 2 * ψ x ≤ m :=
  PDE.Analysis.integral_sq_sub_mul_le_of_pairing (fun _ ↦ Lp.memLp _) (Lp.memLp _)
    (fun _ hw ↦ tendsto_integral_mul_realLineDerivative hbound hbase hw)
    hh hψ hψnonneg hM henergy

end SobolevSpace.GraphSpace
