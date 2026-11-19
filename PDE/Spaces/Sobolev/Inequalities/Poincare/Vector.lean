/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder

/-!
# Poincaré for finite Sobolev systems

The full matrix gradient bounds the product Sobolev norm of a zero-trace
system. The proof uses the scalar Poincaré estimate in every component and
the Frobenius norm of the gradient, and also permits an empty target.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open scoped ENNReal NNReal Sobolev

/-- Matrix-gradient Poincaré on any bounded domain of positive dimension. -/
theorem exists_norm_le_vectorWkpGradientCLM {m n : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) {p : ℝ≥0}
    [Fact (1 ≤ (p : ℝ≥0∞))] (hp : 1 ≤ p) :
    ∃ C : ℝ≥0, ∀ u : Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω),
      ‖u‖ ≤ (C : ℝ) * ‖∇ (fun i ↦ (u i : W^{1,(p : ℝ≥0∞)}(Ω)))‖ := by
  obtain ⟨C, hC⟩ := exists_norm_le_wkpGradientCLM hn hΩ hp
  refine ⟨C * n, fun u ↦ ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (hC (u i)).trans
  calc
    _ ≤ (C : ℝ) * (n * ‖∇ (fun i ↦ (u i : W^{1,(p : ℝ≥0∞)}(Ω)))‖) :=
      mul_le_mul_of_nonneg_left
        (norm_wkpGradientCLM_le_vectorWkpGradientCLM _ i) C.coe_nonneg
    _ = _ := by push_cast; ring

/-- The full matrix gradient determines a finite Sobolev system in a fixed
affine zero-boundary class. This also holds for an empty target. -/
theorem eq_of_sub_mem_Wkp0_of_vectorWkpGradientCLM_eq {m n : ℕ} (hn : 0 < n)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) {p : ℝ≥0} (hp : 1 ≤ p)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    {u v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
    (hboundary : ∀ i, u i - v i ∈ wkp0SubmoduleOn
      (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω))
    (hgradient : ∇ u = ∇ v) : u = v := by
  obtain ⟨C, hC⟩ := exists_norm_le_vectorWkpGradientCLM hn hΩ hp
  let w : Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω) :=
    fun i ↦ ⟨u i - v i, hboundary i⟩
  have h := hC w
  have hg : ∇ (fun i ↦ (w i : W^{1,(p : ℝ≥0∞)}(Ω))) = 0 := by
    change ∇ (u - v) = 0
    rw [map_sub, hgradient, sub_self]
  rw [hg, norm_zero, mul_zero] at h
  have hw : w = 0 := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  funext i
  have hi := congrArg (fun z : Fin m → W₀^{1,(p : ℝ≥0∞)}(Ω) ↦
    (z i : W^{1,(p : ℝ≥0∞)}(Ω))) hw
  exact sub_eq_zero.mp hi

end SobolevSpace.GraphSpace
