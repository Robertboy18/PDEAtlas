/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Tangent half-spaces from the intrinsic normal

Near a C¹ boundary point the domain lies in every prescribed enlargement of the inward
tangent half-space. The proof uses the differential of the chart height, converted to its
physical Riesz vector. It never treats a flattening chart as an orthogonal transformation.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set
open scoped Topology InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Close to a boundary point, the displacement of an interior point makes an arbitrarily
small negative angle with the inward intrinsic normal. The estimate also allows zero
displacement, avoiding a division by its norm. -/
theorem eventually_neg_normal_inner_ge (x : frontier Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (x : ℝ^n), y ∈ Ω →
      -ε * ‖y - x‖ ≤ inner ℝ (-outwardUnitNormal (Ω := Ω) x) (y - x) := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) x.property
  let f : ℝ^n → ℝ := fun y ↦ (hΩ.chart i y) (PDE.Common.lastIndex (n := n))
  let L : ℝ^n →L[ℝ] ℝ :=
    (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun y ↦ hΩ.chart i y) x)
  let c := chartConormal (Ω := Ω) i x
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr (chartConormal_ne_zero i hi)
  have hf : HasFDerivAt f L x := hasFDerivAt_chartLastCoordinate i x
  have hzero : f x = 0 := (chartLastCoordinate_eq_zero_iff i hi).mpr x.property
  have hdual : (InnerProductSpace.toDual ℝ (ℝ^n)) c = L :=
    (InnerProductSpace.toDual ℝ (ℝ^n)).apply_symm_apply L
  have hnormal : -outwardUnitNormal (Ω := Ω) x = ‖c‖⁻¹ • c := by
    rw [outwardUnitNormal_eq_chart x i hi, chartOutwardUnitNormal, neg_smul, neg_neg]
  filter_upwards [(hΩ.chart i).open_source.mem_nhds hi,
    hf.isLittleO.bound (mul_pos hε hc)] with y hy herr hyΩ
  have hpos : 0 ≤ f y := ((chartLastCoordinate_pos_iff i hy).mpr hyΩ).le
  have herror : |f y - L (y - x)| ≤ ε * ‖c‖ * ‖y - x‖ := by
    simpa only [hzero, sub_zero, Real.norm_eq_abs] using herr
  have hL : -(ε * ‖c‖ * ‖y - x‖) ≤ L (y - x) := by
    linarith [(abs_le.mp herror).2]
  rw [hnormal, real_inner_smul_left, ← InnerProductSpace.toDual_apply_apply, hdual]
  have hscaled := mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr hc.le)
  convert hscaled using 1
  field_simp

end SobolevSpace.Trace.C1
