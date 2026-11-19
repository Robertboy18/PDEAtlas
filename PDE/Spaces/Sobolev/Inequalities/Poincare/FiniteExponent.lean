/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Closure
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
import PDE.Spaces.Sobolev.GraphSpace.Norms
import PDE.Analysis.FunctionalSpaces.Poincare
import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global

/-!
# Poincaré on the supported-core closure at finite exponents

A bounded domain gives a uniform estimate for compactly supported smooth functions.
Density passes that estimate to the completed Sobolev space. No boundary regularity
or extension operator is needed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Function Set
open scoped ENNReal Sobolev

/-- On a bounded domain of positive dimension, the `Lᵖ` norm of an element of
`W^{1,p}_0` is controlled by its first weak derivatives at the same exponent.
Every finite `p ≥ 1` is allowed, including the critical and supercritical cases. -/
theorem exists_poincare_Wkp0 {n : ℕ} (hn : 0 < n) {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) {p : NNReal} (hp : 1 ≤ p)
    [Fact (1 ≤ (p : ℝ≥0∞))] :
    ∃ C : NNReal, ∀ u : W₀^{1,p}(Ω),
      ‖(((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) (baseIndex n 1))‖ ≤
        (C : ℝ) * ∑ i : Fin n,
          ‖(((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
            (singleDerivIndex n i))‖ := by
  have hclassical : ∃ C : NNReal, ∀ f : ℝ^n → ℝ,
      ContDiff ℝ 1 f → support f ⊆ Ω →
        eLpNorm f p volume ≤ C * eLpNorm (fderiv ℝ f) p volume := by
    by_cases h1 : n = 1
    · subst n
      exact ⟨(volume (closure Ω)).toNNReal, fun f hf hs ↦
        MeasureTheory.eLpNorm_le_eLpNorm_fderiv_euclidean_one hf hs hp hΩ⟩
    · exact MeasureTheory.exists_eLpNorm_le_eLpNorm_fderiv_of_bounded_support
        (F := ℝ) (volume : Measure (ℝ^n)) (by simpa using (show 1 < n by omega)) hΩ hp
  obtain ⟨C, hC⟩ := hclassical
  refine ⟨C, fun u ↦ poincare_Wkp0_of_testFunctions C ?_ u⟩
  intro φ
  have hφ : ContDiff ℝ 1 φ.1.toFun := φ.1.contDiff.of_le (by simp)
  apply (hC φ.1.toFun hφ ((subset_tsupport _).trans φ.2)).trans
  gcongr
  exact Inequalities.eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv hφ

/-- On a bounded set of positive dimension, the vector-valued weak gradient
controls the full zero-boundary Sobolev norm at every finite `p ≥ 1`. -/
theorem exists_norm_le_wkpGradientCLM {n : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) {p : NNReal} (hp : 1 ≤ p)
    [Fact (1 ≤ (p : ℝ≥0∞))] :
    ∃ C : NNReal, ∀ u : W₀^{1,p}(Ω),
      ‖u‖ ≤ (C : ℝ) * ‖∇ (u : W^{1,p}(Ω))‖ := by
  obtain ⟨C, hC⟩ := exists_poincare_Wkp0 hn hΩ hp
  refine ⟨(C + 1) * n, fun u ↦ ?_⟩
  have hsum :
      (∑ i : Fin n, ‖((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω)
        (singleDerivIndex n i)‖) ≤ n * ‖∇ (u : W^{1,p}(Ω))‖ := by
    calc
      _ ≤ ∑ _i : Fin n, ‖∇ (u : W^{1,p}(Ω))‖ :=
        Finset.sum_le_sum fun i _ ↦ norm_derivCoordinate_le_wkpGradientCLM _ i
      _ = _ := by simp
  have hnorm := ambient_norm_le_base_add_sum_deriv
    (((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω))
  change ‖(((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω))‖ ≤ _
  calc
    _ ≤ (C : ℝ) * (∑ i : Fin n,
        ‖((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖) +
        ∑ i : Fin n,
          ‖((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖ :=
      hnorm.trans (add_le_add (hC u) le_rfl)
    _ = ((C : ℝ) + 1) * (∑ i : Fin n,
        ‖((u : W^{1,p}(Ω)) : WkpAmbientOn n 1 p Ω) (singleDerivIndex n i)‖) :=
      by ring
    _ ≤ ((C : ℝ) + 1) *
        (n * ‖∇ (u : W^{1,p}(Ω))‖) := by gcongr
    _ = _ := by push_cast; ring

/-- Equal gradients determine equal Sobolev elements in the same affine
zero-boundary class on a bounded domain of positive dimension. -/
theorem eq_of_sub_mem_Wkp0_of_wkpGradientCLM_eq {n : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) {p : NNReal} (hp : 1 ≤ p)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    {u v : W^{1,(p : ℝ≥0∞)}(Ω)}
    (hboundary : u - v ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞))
      (Ω := Ω))
    (hgradient : ∇ u = ∇ v) : u = v := by
  obtain ⟨C, hC⟩ := exists_norm_le_wkpGradientCLM hn hΩ hp
  have h := hC ⟨u - v, hboundary⟩
  change ‖u - v‖ ≤ (C : ℝ) * ‖∇ (u - v)‖ at h
  rw [map_sub, hgradient, sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- A positive multiple of the full zero-boundary Sobolev norm to the power `p`
is bounded by the same power of the weak-gradient norm. The constant is uniform
in the state; boundedness of the domain is the only geometric assumption. -/
theorem exists_pos_mul_norm_rpow_le_norm_wkpGradientCLM_rpow {n : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) {p : NNReal} (hp : 1 ≤ p)
    [Fact (1 ≤ (p : ℝ≥0∞))] :
    ∃ K : ℝ, 0 < K ∧ ∀ u : W₀^{1,p}(Ω),
      K * ‖u‖ ^ (p : ℝ) ≤
        ‖∇ (u : W^{1,p}(Ω))‖ ^ (p : ℝ) := by
  obtain ⟨C, hC⟩ := exists_norm_le_wkpGradientCLM hn hΩ hp
  have hs : 0 < (C : ℝ) + 1 := by positivity
  have hden : 0 < ((C : ℝ) + 1) ^ (p : ℝ) := Real.rpow_pos_of_pos hs _
  refine ⟨1 / ((C : ℝ) + 1) ^ (p : ℝ), div_pos zero_lt_one hden, fun u ↦ ?_⟩
  have hnorm : ‖u‖ ≤ ((C : ℝ) + 1) *
      ‖∇ (u : W^{1,p}(Ω))‖ :=
    (hC u).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
      (norm_nonneg _))
  have hpow := Real.rpow_le_rpow (norm_nonneg u) hnorm p.coe_nonneg
  rw [Real.mul_rpow hs.le (norm_nonneg _)] at hpow
  calc
    _ ≤ (1 / ((C : ℝ) + 1) ^ (p : ℝ)) *
        (((C : ℝ) + 1) ^ (p : ℝ) *
          ‖∇ (u : W^{1,p}(Ω))‖ ^ (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (div_nonneg zero_le_one hden.le)
    _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ hden.ne', one_mul]


end SobolevSpace.GraphSpace
