/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Nonnegative bounded multipliers on real `L²`

A nonnegative bounded real coefficient defines a nonnegative quadratic form
by multiplication. The statement uses the almost-everywhere sign of the
coefficient and works for an arbitrary measure. The finite-matrix estimate also
allows a constant mass compensation, without a separate symmetry hypothesis.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory.Lp

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- A nonnegative real multiplier has a nonnegative quadratic pairing on `L²`. -/
theorem inner_lpSMul_self_nonneg
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (a : Lp ℝ ∞ μ)
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (u : Lp ℝ 2 μ) :
    0 ≤ ⟪a • u, u⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [ha, coeFn_lpSMul (r := (2 : ℝ≥0∞)) a u] with x hx hu
  rw [hu]
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial, Pi.mul_apply, Pi.zero_apply]
  nlinarith [mul_nonneg hx (sq_nonneg (u x))]

/-- A pointwise mass-compensated matrix inequality passes to the `L²` quadratic form. -/
theorem sum_inner_lpSMul_matrix_self_lower_bound {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [Fintype ι] (a : ι → ι → Lp ℝ ∞ μ) (η : ℝ)
    (ha : ∀ᵐ x ∂μ, ∀ v : ι → ℝ,
      -η * (∑ i, (v i) ^ 2) ≤ ∑ i, ∑ j, a i j x * v j * v i)
    (u : ι → Lp ℝ 2 μ) :
    -η * (∑ i, ‖u i‖ ^ 2) ≤ ∑ i, ∑ j, ⟪a i j • u j, u i⟫_ℝ := by
  classical
  have hint (i j : ι) :
      Integrable (fun x ↦ ⟪(a i j • u j : Lp ℝ 2 μ) x, u i x⟫_ℝ) μ :=
    L2.integrable_inner (a i j • u j) (u i)
  have hmul : ∀ᵐ x ∂μ, ∀ i j,
      (a i j • u j : Lp ℝ 2 μ) x = a i j x * u j x := by
    exact ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ by
      filter_upwards [coeFn_lpSMul (r := (2 : ℝ≥0∞)) (a i j) (u j)] with x hx
      simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using hx
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ ↦ L2.integrable_inner (u i) (u i)),
    ← integral_const_mul]
  simp_rw [← integral_finsetSum _ (fun j _ ↦ hint _ j)]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j)]
  apply integral_mono_ae
    ((integrable_finsetSum _ fun i _ ↦ L2.integrable_inner (u i) (u i)).const_mul (-η))
    (integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j)
  filter_upwards [ha, hmul] with x hx hm
  have hform :
      (∑ i, ∑ j, ⟪(a i j • u j : Lp ℝ 2 μ) x, u i x⟫_ℝ) =
        ∑ i, ∑ j, a i j x * u j x * u i x := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hm i j]
    simp only [Real.inner_apply]
  rw [hform]
  simpa only [Real.inner_apply, pow_two] using hx (fun i ↦ u i x)

end MeasureTheory.Lp
