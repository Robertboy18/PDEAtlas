/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Bootstrap.AutonomousStep

/-!
# Iterating the autonomous regularity step

Adjoining all first derivatives produces another finite system of the same
form. Its principal matrix has the same ellipticity bounds, and its forcing
remains smooth in the enlarged field. Induction therefore gives every finite
order of differentiability, and hence smoothness.
-/

@[expose] public noncomputable section

open Set SobolevSpace
open scoped ENNReal NNReal

namespace PDE.Elliptic.Regularity.Quasilinear.Bootstrap

variable {n : ℕ} [Fact (0 < n)] {I : Type*} [Fintype I] {Ω : Set ℝ^n}

/-- Every finite order follows by differentiating the autonomous
system and applying the same C¹ to C² gain to the enlarged field. -/
theorem contDiffOn_nat_of_autonomous_system (m : ℕ)
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω)
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    {f : I → Fin n → (I → ℝ) → ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hf : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (f l i))
    {v : ℝ^n → I → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    {θ Λ : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ)
    (hbound : ∀ x ∈ Ω, ∀ i j, ‖a i j (v x)‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j (v x) * ξ j * ξ i)
    (heq : ∀ l, HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, a i j (v x) * (∂[j] (fun y ↦ v y l)) x) - f l i (v x))) :
    ContDiffOn ℝ m v Ω := by
  induction m generalizing I with
  | zero => exact hv.of_le (by norm_num)
  | succ m ih =>
    have hv2 := contDiffOn_two_of_autonomous_system hq2 hq hΩ ha hf hv
      hθ hΛ hbound hell heq
    apply contDiffOn_succ_of_firstJet m hΩ hv
    exact ih (contDiff_prolongedCoefficient ha) (contDiff_prolongedForcing ha hf)
      (contDiffOn_one_firstJet hΩ hv2) hbound hell
      (hasZeroWeakDivergenceOn_firstJet hΩ ha hf hv2 heq)

/-- Smooth coefficients and forcing make every C¹ weak solution of the
autonomous diagonal system smooth on its open domain. -/
theorem contDiffOn_infty_of_autonomous_system
    {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω)
    {a : Fin n → Fin n → (I → ℝ) → ℝ}
    {f : I → Fin n → (I → ℝ) → ℝ}
    (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hf : ∀ l i, ContDiff ℝ (⊤ : ℕ∞) (f l i))
    {v : ℝ^n → I → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    {θ Λ : ℝ} (hθ : 0 < θ) (hΛ : 0 ≤ Λ)
    (hbound : ∀ x ∈ Ω, ∀ i j, ‖a i j (v x)‖ ≤ Λ)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, a i j (v x) * ξ j * ξ i)
    (heq : ∀ l, HasZeroWeakDivergenceOn Ω (fun i x ↦
      (∑ j, a i j (v x) * (∂[j] (fun y ↦ v y l)) x) - f l i (v x))) :
    ContDiffOn ℝ (⊤ : ℕ∞) v Ω :=
  contDiffOn_infty.mpr fun m ↦ contDiffOn_nat_of_autonomous_system m
    hq2 hq hΩ ha hf hv hθ hΛ hbound hell heq

end PDE.Elliptic.Regularity.Quasilinear.Bootstrap
