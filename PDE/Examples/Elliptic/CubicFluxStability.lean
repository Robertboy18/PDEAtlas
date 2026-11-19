/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.FiniteExponent.Stability
public import PDE.Elliptic.Monotone.FiniteExponent.Uniqueness

/-!
# The cubic gradient flux

The equation `-div (‖Du‖² Du) = ℓ` has exactly one zero-boundary weak solution
in `W^{1,4}` on every bounded domain of positive dimension. The solutions obey
`‖u - v‖³ ≤ K ‖ℓ₁ - ℓ₂‖`, giving dependence of order `1/3` on the load.
The cubic flux is not globally Lipschitz and has no positive quadratic modulus
at zero. Its fourth-power monotonicity bound is the input to the estimate.

The domain may be nonopen: in that case the boundary space is the closure of
smooth functions with support in the set.
-/

@[expose] public section

noncomputable section

namespace PDE.Examples.CubicFluxStability

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace NNReal Topology Sobolev

local instance : Fact (1 ≤ ((4 : NNReal) : ℝ≥0∞)) := ⟨by norm_num⟩

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- The difference of the cubic flux controls a quarter of the fourth power
of the difference. The bound uses only the real inner product and holds
also at zero and in the zero-dimensional space. -/
private theorem cubic_pairing_lower_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z w : E) :
    (1 / 4 : ℝ) * ‖z - w‖ ^ 4 ≤
      inner ℝ (‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w) (z - w) := by
  have hidentity :
      4 * inner ℝ (‖z‖ ^ 2 • z - ‖w‖ ^ 2 • w) (z - w) - ‖z - w‖ ^ 4 =
        ‖z + w‖ ^ 2 * ‖z - w‖ ^ 2 + 2 * (‖z‖ ^ 2 - ‖w‖ ^ 2) ^ 2 := by
    rw [show ‖z - w‖ ^ 4 = (‖z - w‖ ^ 2) ^ 2 by ring]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq, real_inner_comm w z, norm_add_sq_real, norm_sub_sq_real]
    ring
  have hproduct := mul_nonneg (sq_nonneg ‖z + w‖) (sq_nonneg ‖z - w‖)
  nlinarith [sq_nonneg (‖z‖ ^ 2 - ‖w‖ ^ 2)]

/-- The cubic flux has exactly cubic norm growth. -/
private theorem norm_cubic_flux (z : ℝ^n) :
    ‖‖z‖ ^ 2 • z‖ = ‖z‖ ^ 3 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  ring

/-- The Dirichlet problem for the cubic flux has a unique weak solution for every
continuous dual load. Growth, strict monotonicity, hemicontinuity and coercivity
are established for this particular flux before the existence theorem is used. -/
theorem existsUnique_cubic_flux (hn : 0 < n) (hΩ : Bornology.IsBounded Ω)
    (ℓ : StrongDual ℝ W₀^{1,(4 : NNReal)}(Ω)) :
    ∃! u : W₀^{1,(4 : NNReal)}(Ω), ∀ z : W₀^{1,(4 : NNReal)}(Ω),
      (∫ x, inner ℝ (‖∇ (u : W^{1,(4 : NNReal)}(Ω)) x‖ ^ 2 • ∇ (u : W^{1,(4 : NNReal)}(Ω)) x)
        (∇ (z : W^{1,(4 : NNReal)}(Ω)) x) ∂μ) = ℓ z := by
  let a (_x : ℝ^n) (z : ℝ^n) := ‖z‖ ^ 2 • z
  have hmeas : Measurable (Function.uncurry a) := by
    apply Continuous.measurable
    dsimp [a, Function.uncurry]
    fun_prop
  have hgrowth : ∀ᵐ x ∂μ, ∀ z : ℝ^n,
      ‖a x z‖ ≤ 0 + 1 * ‖z‖ ^ (((4 : NNReal) : ℝ) - 1) := by
    apply ae_of_all
    intro x z
    dsimp only [a]
    simpa only [NNReal.coe_ofNat, show (4 : ℝ) - 1 = 3 by norm_num,
      zero_add, one_mul, Real.rpow_ofNat] using (norm_cubic_flux z).le
  have hstrict : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, z ≠ w →
      0 < inner ℝ (a x z - a x w) (z - w) := by
    apply ae_of_all
    intro x z w hzw
    exact lt_of_lt_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 1 / 4)
        (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw)) 4))
      (cubic_pairing_lower_bound z w)
  have hhemi : ∀ᵐ x ∂μ, ∀ z w : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (z + t • w)) w) (Ici 0) 0 := by
    apply ae_of_all
    intro x z w
    apply Continuous.continuousWithinAt
    dsimp [a]
    fun_prop
  have hlower : ∀ᵐ x ∂μ, ∀ z : ℝ^n,
      1 * ‖z‖ ^ (((4 : NNReal) : ℝ)) - 0 ≤
        inner ℝ (a x z) z := by
    apply ae_of_all
    intro x z
    dsimp only [a]
    simp only [NNReal.coe_ofNat, sub_zero, one_mul, Real.rpow_ofNat]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact le_of_eq (by ring)
  exact existsUnique_weak_solution_of_strictMonotone_wkpGradientFlux
    (p := (4 : NNReal)) (by norm_num) a hmeas (MemLp.zero : MemLp (0 : ℝ^n → ℝ)
      (ENNReal.conjExponent ((4 : NNReal) : ℝ≥0∞)) μ)
    hgrowth hn hΩ hstrict hhemi (by norm_num : (0 : ℝ) < 1)
    (integrable_zero _ _ _ : Integrable (0 : ℝ^n → ℝ) μ) hlower ℓ

/-- Two cubic-flux solutions on a bounded domain satisfy a cubic error bound
in the full `W^{1,4}` norm. The constant is uniform over the two dual loads. -/
theorem cubic_flux_stability (hn : 0 < n) (hΩ : Bornology.IsBounded Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ℓ₁ ℓ₂ : StrongDual ℝ W₀^{1,(4 : NNReal)}(Ω)) (u v : W₀^{1,(4 : NNReal)}(Ω)),
      (∀ z : W₀^{1,(4 : NNReal)}(Ω),
        (∫ x, inner ℝ (‖∇ (u : W^{1,(4 : NNReal)}(Ω)) x‖ ^ 2 • ∇ (u : W^{1,(4 : NNReal)}(Ω)) x)
        (∇ (z : W^{1,(4 : NNReal)}(Ω)) x) ∂μ) = ℓ₁ z) →
      (∀ z : W₀^{1,(4 : NNReal)}(Ω),
        (∫ x, inner ℝ (‖∇ (v : W^{1,(4 : NNReal)}(Ω)) x‖ ^ 2 • ∇ (v : W^{1,(4 : NNReal)}(Ω)) x)
        (∇ (z : W^{1,(4 : NNReal)}(Ω)) x) ∂μ) = ℓ₂ z) →
      ‖u - v‖ ^ 3 ≤ K * ‖ℓ₁ - ℓ₂‖ := by
  let a (_x : ℝ^n) (z : ℝ^n) := ‖z‖ ^ 2 • z
  have hmeas : Measurable (Function.uncurry a) := by
    apply Continuous.measurable
    dsimp [a, Function.uncurry]
    fun_prop
  have hgrowth : ∀ᵐ x ∂μ, ∀ z : ℝ^n,
      ‖a x z‖ ≤ 0 + 1 * ‖z‖ ^ (((4 : NNReal) : ℝ) - 1) := by
    apply ae_of_all
    intro x z
    dsimp only [a]
    simpa only [NNReal.coe_ofNat, show (4 : ℝ) - 1 = 3 by norm_num,
      zero_add, one_mul, Real.rpow_ofNat] using (norm_cubic_flux z).le
  have hmono : ∀ᵐ x ∂μ, ∀ z w : ℝ^n,
      (1 / 4 : ℝ) * ‖z - w‖ ^ (((4 : NNReal) : ℝ)) ≤
        inner ℝ (a x z - a x w) (z - w) := by
    apply ae_of_all
    intro x z w
    simpa only [NNReal.coe_ofNat, Real.rpow_ofNat, a] using cubic_pairing_lower_bound z w
  obtain ⟨K, hK, hbound⟩ := exists_norm_sub_rpow_le_load_norm_of_wkpGradientFlux
    (p := (4 : NNReal)) (by norm_num) a hmeas (MemLp.zero : MemLp (0 : ℝ^n → ℝ)
      (ENNReal.conjExponent ((4 : NNReal) : ℝ≥0∞)) μ)
    hgrowth hn hΩ (by norm_num : (0 : ℝ) < 1 / 4) hmono
  refine ⟨K, hK, fun ℓ₁ ℓ₂ u v hu hv ↦ ?_⟩
  simpa only [NNReal.coe_ofNat, show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_ofNat] using
    hbound ℓ₁ ℓ₂ u v hu hv

end PDE.Examples.CubicFluxStability
