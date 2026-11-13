/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integral pairings with bounded real coefficients

A bounded real multiplier can be moved across the conjugate Lp–Lq integral pairing,
including the endpoint pair L¹–L∞. In L², multiplication is symmetric in the inner product.
The same holds in complex L² for a complex coefficient that is real almost everywhere.
Its bilinear pairing is bounded by the coefficient norm and the two L² norms. Summing over
finitely many components gives a matrix estimate using the total squared L² norm.

The measure is arbitrary; no finiteness assumption is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace MeasureTheory.Lp

/-- A real bounded multiplier may be moved to either side of the conjugate integral
pairing. The measure is arbitrary. -/
theorem lpPairing_lpSMul_left
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (a : Lp ℝ ∞ μ) (u : Lp ℝ p μ) (v : Lp ℝ q μ) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q (a • u) v =
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ p q u (a • v) := by
  simp only [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  filter_upwards [coeFn_lpSMul (r := p) a u, coeFn_lpSMul (r := q) a v] with x hu hv
  simp only [smul_eq_mul, Pi.mul_apply] at hu hv
  rw [hu, hv]
  ac_rfl

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Multiplication by a bounded real coefficient is symmetric in the real L2 pairing. -/
theorem inner_lpSMul_left (a : Lp ℝ ∞ μ) (u v : Lp ℝ 2 μ) :
    ⟪a • u, v⟫_ℝ = ⟪u, a • v⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_lpSMul (r := (2 : ℝ≥0∞)) a u,
    coeFn_lpSMul (r := (2 : ℝ≥0∞)) a v] with x hu hv
  simp only [smul_eq_mul] at hu hv
  rw [hu, hv]
  simp [RCLike.inner_apply, mul_assoc, mul_comm, mul_left_comm]

/-- Multiplication by a bounded complex coefficient that is real almost everywhere is symmetric
in the complex L2 inner product. -/
theorem inner_lpSMul_left_of_real {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {m : Lp ℂ ∞ μ} (hm : ∀ᵐ x ∂μ, conj (m x) = m x) (u v : Lp F 2 μ) :
    ⟪(m • u : Lp F 2 μ), v⟫_ℂ = ⟪u, (m • v : Lp F 2 μ)⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hm, coeFn_lpSMul (r := 2) m u, coeFn_lpSMul (r := 2) m v] with x hx hu hv
  rw [hu, hv, Pi.smul_apply', Pi.smul_apply', inner_smul_left, inner_smul_right, hx]

/-- A bounded coefficient controls the absolute value of its scalar L2 pairing. -/
theorem abs_inner_lpSMul_le (a : Lp ℝ ∞ μ) (u v : Lp ℝ 2 μ) :
    |⟪a • u, v⟫_ℝ| ≤ ‖a‖ * ‖u‖ * ‖v‖ := by
  exact (abs_real_inner_le_norm (a • u) v).trans
    (mul_le_mul_of_nonneg_right (Lp.norm_smul_le a u) (norm_nonneg v))

/-- The sum of the coefficient norms bounds a finite matrix pairing on scalar L2 fields.

This estimate uses the total squared L2 norm of the components, with no derivative norm. -/
theorem abs_sum_inner_lpSMul_le {ι : Type*} [Fintype ι]
    (a : ι → ι → Lp ℝ ∞ μ) (u : ι → Lp ℝ 2 μ) :
    |∑ p, ∑ q, ⟪a p q • u q, u p⟫_ℝ| ≤
      (∑ p, ∑ q, ‖a p q‖) * (∑ p, ‖u p‖ ^ 2) := by
  classical
  have hproduct (p q : ι) : ‖u q‖ * ‖u p‖ ≤ ∑ r, ‖u r‖ ^ 2 := by
    have hp : ‖u p‖ ^ 2 ≤ ∑ r, ‖u r‖ ^ 2 :=
      Finset.single_le_sum (fun r _ ↦ sq_nonneg ‖u r‖) (Finset.mem_univ p)
    have hq : ‖u q‖ ^ 2 ≤ ∑ r, ‖u r‖ ^ 2 :=
      Finset.single_le_sum (fun r _ ↦ sq_nonneg ‖u r‖) (Finset.mem_univ q)
    nlinarith [sq_nonneg (‖u p‖ - ‖u q‖)]
  calc
    |∑ p, ∑ q, ⟪a p q • u q, u p⟫_ℝ| ≤
        ∑ p, |∑ q, ⟪a p q • u q, u p⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |⟪a p q • u q, u p⟫_ℝ| := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, ‖a p q‖ * (∑ r, ‖u r‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q _
      calc
        |⟪a p q • u q, u p⟫_ℝ| ≤ ‖a p q‖ * ‖u q‖ * ‖u p‖ :=
          abs_inner_lpSMul_le _ _ _
        _ = ‖a p q‖ * (‖u q‖ * ‖u p‖) := mul_assoc _ _ _
        _ ≤ ‖a p q‖ * (∑ r, ‖u r‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hproduct p q) (norm_nonneg _)
    _ = (∑ p, ∑ q, ‖a p q‖) * (∑ r, ‖u r‖ ^ 2) := by
      simp only [Finset.sum_mul]

end MeasureTheory.Lp

open Filter
open scoped Topology

namespace MeasureTheory

/-- Strong L² convergence in both factors passes a quadratic integral with
any fixed essentially bounded real coefficient to the limit. -/
theorem tendsto_integral_weighted_mul_of_tendsto_L2
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {f g : ι → Lp ℝ 2 μ} {F G : Lp ℝ 2 μ} {φ : α → ℝ}
    (hφ : MemLp φ ∞ μ)
    (hf : Tendsto f l (𝓝 F)) (hg : Tendsto g l (𝓝 G)) :
    Tendsto (fun i ↦ ∫ x, φ x * f i x * g i x ∂μ) l
      (𝓝 (∫ x, φ x * F x * G x ∂μ)) := by
  let A : Lp ℝ ∞ μ := hφ.toLp φ
  let M : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 2 2 A
  have hM (u : Lp ℝ 2 μ) : (M u : α → ℝ) =ᵐ[μ] fun x ↦ φ x * u x := by
    have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) A u
    filter_upwards [h, hφ.coeFn_toLp] with x hx hφx
    change M u x = A x * u x at hx
    change A x = φ x at hφx
    rw [hφx] at hx
    exact hx
  have hinner (u v : Lp ℝ 2 μ) :
      inner ℝ (M u) v = ∫ x, φ x * u x * v x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hM u] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx]
    ring
  have hlimit := (((M.continuous.tendsto F).comp hf).inner (𝕜 := ℝ) hg)
  simpa only [Function.comp_def, hinner] using hlimit

end MeasureTheory
