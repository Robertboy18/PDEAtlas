/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation
public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Smooth
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Bounded smooth approximation for derivative interpolation

The usual cutoff-and-mollifier approximation of a bounded Sobolev function
preserves its essential value bound. This additional uniform bound allows
the smooth Gagliardo–Nirenberg estimate to pass to weak derivatives.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SobolevSpace.GagliardoNirenberg

open Approximation

variable {n : ℕ}

/-- A bounded global Sobolev function admits smooth compact approximations with
the same value bound and convergence of every recorded weak derivative. -/
theorem exists_bounded_globalApproximation_Wkp (μ : Mollifier n)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (k : ℕ)
    (u : GlobalSobolevSpace n k p) {B : ℝ}
    (hB : ∀ᵐ x ∂volume, ‖u.toFun x‖ ≤ B) :
    ∃ v : ℕ → ℝ^n → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) ∧
      (∀ j, HasCompactSupport (v j)) ∧
      (∀ j x, ‖v j x‖ ≤ B) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ v j x - u.toFun x) p volume) atTop (𝓝 0) ∧
      ∀ α : List (Fin n), α.length ≤ k →
        ∃ g : ℝ^n → ℝ, MemLp g p volume ∧
          HasWeakDerivativeOn Set.univ α u.toFun g ∧
          Tendsto
            (fun j ↦ eLpNorm (fun x ↦ iteratedPartialDeriv α (v j) x - g x) p volume)
            atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hεpos (j : ℕ) : 0 < ε j := by dsimp only [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let R : ℕ → ℝ := fun j ↦ (j : ℝ) + 1
  have hRpos (j : ℕ) : 0 < R j := by dsimp only [R]; positivity
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  let w (j : ℕ) := mollify μ (ε j) u.toFun
  let v (j : ℕ) (x : ℝ^n) := cutoff (R j) x * w j x
  have hu : MemLp u.toFun p volume := by simpa only [domainMeasure, Measure.restrict_univ]
    using u.memLp
  have hw (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (w j) :=
    mollify_contDiff_of_pos μ (hεpos j) u.toFun (hu.locallyIntegrable Fact.out)
  have hv0 :
      Tendsto (fun j ↦ eLpNorm (fun x ↦ v j x - u.toFun x) p volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_cutoff_mul_sub hp hu (fun j ↦ (hw j).continuous.aestronglyMeasurable)
      (mollify_converges_Lp μ p hp ε hεpos hε hu) hRpos hR
  refine ⟨v, fun j ↦ (cutoff_contDiff (R j)).mul (hw j), ?_, ?_, hv0, ?_⟩
  · intro j
    exact (cutoff_hasCompactSupport (hRpos j).ne').mul_right
  · intro j x
    calc
      ‖v j x‖ = |cutoff (R j) x| * ‖w j x‖ := by
        simp only [v, norm_mul, Real.norm_eq_abs]
      _ ≤ ‖w j x‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (cutoff_abs_le_one (R j) x)
      _ ≤ B := norm_mollify_le_of_ae_bound μ (hεpos j) hB x
  · intro α hαk
    by_cases hα : α = []
    · subst α
      exact ⟨u.toFun, hu, hasWeakDerivativeOn_nil
        ((hu.locallyIntegrable Fact.out).locallyIntegrableOn univ), hv0⟩
    · obtain ⟨g, hg, hwg⟩ := u.weak_derivs_inLp α hαk
      have hg' : MemLp g p volume := by
        simpa only [domainMeasure, Measure.restrict_univ] using hg
      exact ⟨g, hg', hwg, tendsto_eLpNorm_iteratedPartialDeriv_cutoff_mollify_sub
        μ hp u α hα hαk hg' hwg hεpos hε hRpos hR⟩

end SobolevSpace.GagliardoNirenberg
