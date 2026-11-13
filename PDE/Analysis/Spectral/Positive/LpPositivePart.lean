/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.PositivePart
public import PDE.Analysis.MeasureTheory.Lp.PositiveOperator
public import PDE.Analysis.MeasureTheory.Lp.PositivePairing

/-!
# Positive parts at a positive weighted eigenvalue

For a positive operator with a strictly positive adjoint weight, taking the
positive part preserves the associated real eigen-equation. The order
inequality becomes equality because its nonnegative defect has zero pairing
with the weight.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace LinearMap

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Positive parts remain eigenvectors at the reciprocal eigenvalue detected
by a strictly positive adjoint weight. -/
theorem posPart_eq_smul_apply_of_pos_adjoint_weight
    (A : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ)
    (hA : ∀ v : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ v x) → ∀ᵐ x ∂μ, 0 ≤ A v x)
    (q : Lp ℝ 2 μ) (hq : ∀ᵐ x ∂μ, 0 < q x)
    {r : ℝ} (hr : 0 < r)
    (hweight : ∀ v : Lp ℝ 2 μ, r * ⟪q, A v⟫_ℝ = ⟪q, v⟫_ℝ)
    (u : Lp ℝ 2 μ) (hu : u = r • A u) :
    Lp.posPart u = r • A (Lp.posPart u) := by
  let w := Lp.posPart u
  have huw : ∀ᵐ x ∂μ, u x ≤ w x := by
    filter_upwards [Lp.coeFn_posPart u] with x hx
    exact (le_max_left _ _).trans_eq hx.symm
  have hAw := hA w (Lp.posPart_nonneg_ae u)
  have hmono := A.map_le_map_ae_of_nonneg hA huw
  have hueq : ∀ᵐ x ∂μ, u x = r * A u x := by
    filter_upwards [Lp.coeFn_smul r (A u)] with x hx
    have h := congrArg (fun v : Lp ℝ 2 μ ↦ v x) hu
    simpa only [hx, Pi.smul_apply, smul_eq_mul] using h
  have hgap : ∀ᵐ x ∂μ, 0 ≤ (r • A w - w) x := by
    filter_upwards [hAw, hmono, hueq, Lp.coeFn_posPart u,
      Lp.coeFn_smul r (A w), Lp.coeFn_sub (r • A w) w]
        with x hAwx hmonox hux hwx hs hd
    rw [hd, Pi.sub_apply, hs, Pi.smul_apply, smul_eq_mul]
    apply sub_nonneg.mpr
    rw [hwx]
    exact max_le (hux.trans_le (mul_le_mul_of_nonneg_left hmonox hr.le))
      (mul_nonneg hr.le hAwx)
  have hzero : r • A w - w = 0 := by
    apply Lp.eq_zero_of_nonneg_ae_of_inner_eq_zero q _ hq hgap
    rw [inner_sub_right, real_inner_smul_right, hweight, sub_self]
  exact (sub_eq_zero.mp hzero).symm

end LinearMap
