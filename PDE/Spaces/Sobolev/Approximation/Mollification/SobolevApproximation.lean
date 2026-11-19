/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.Truncation
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Global smooth approximation of Sobolev functions

We approximate Sobolev functions on `ℝ^n` by cutoff times mollifier, for `1 ≤ p < ∞` (the explicit
argument `hp : p ≠ ∞`); for `p = ∞` the statement is false, since `C_c^∞` is not dense in `W^{k,∞}`.
`globalApproximation_Wkp` gives compactly supported smooth functions `u_m = η_m · (ρ_{ε_m} ∗ u)`
converging in `L^p`, with every weak derivative of order at most `k` that the global space records
converging too. The Leibniz expansion `iteratedPartialDeriv_mul_eq_sum_split` separates the
principal term `η_m · D^α(ρ_{ε_m} ∗ u)`, which converges because mollification commutes with weak
derivatives, from a tail whose every term carries a cutoff derivative of order `|β| ≥ 1` and so
decays like `R_m^{-|β|}`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for the density of `C_c^∞(ℝ^N)` in `W^{1,p}(ℝ^N)`.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Convolution Pointwise Topology
open PDE.Analysis (standardBump)

namespace Approximation

variable {n : ℕ}

/-- Global approximation by smooth, compactly supported functions on `ℝ^n`, in the
project's representative-based `SobolevSpaceOn` encoding.

It is the `p ≠ ∞` density result for `C_c^∞` on `ℝ^n`, stated in terms of the stored weak
derivative representatives and `eLpNorm` convergence. It is the global input for the
extension-and-restriction proof of approximation up to the boundary in
`Approximation.Density.ExtensionDomain`. -/
theorem globalApproximation_Wkp (μ : Mollifier n) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (k : ℕ)
    (u : _root_.SobolevSpace.GlobalSobolevSpace n k p) :
      ∃ u_m : ℕ → (ℝ^n → ℝ),
        (∀ m, ContDiff ℝ (⊤ : ℕ∞) (u_m m)) ∧
        (∀ m, HasCompactSupport (u_m m)) ∧
        Filter.Tendsto
          (fun m ↦ eLpNorm (fun x ↦ u_m m x - u.toFun x) p volume)
          Filter.atTop (𝓝 0) ∧
        (∀ α : List (Fin n), α.length ≤ k →
          ∃ g : ℝ^n → ℝ,
            MemLp g p (volume : Measure (ℝ^n)) ∧
            HasWeakDerivativeOn (n := n) Set.univ α u.toFun g ∧
            Filter.Tendsto
              (fun m ↦
                eLpNorm (fun x ↦ iteratedPartialDeriv (n := n) α (u_m m) x - g x) p
                  (volume : Measure (ℝ^n)))
              Filter.atTop (𝓝 0)) := by
  classical
  -- Mollifier scales tend to zero while the cutoff radii tend to infinity.
  let ε : ℕ → ℝ := fun m ↦ (1 : ℝ) / ((m : ℝ) + 1)
  have hεpos (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hε : Filter.Tendsto ε Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let R : ℕ → ℝ := fun m ↦ (m : ℝ) + 1
  have hRpos (m : ℕ) : 0 < R m := by dsimp [R]; positivity
  have hR : Filter.Tendsto R Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  let v (m : ℕ) := mollify μ (ε m) u.toFun
  let u_m (m : ℕ) (x : ℝ^n) := cutoff (R m) x * v m x
  have hu : MemLp u.toFun p volume := by simpa [domainMeasure] using u.memLp
  have huLoc := hu.locallyIntegrable (Fact.out : 1 ≤ p)
  have hv (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (v m) :=
    mollify_contDiff_of_pos μ (hεpos m) u.toFun huLoc
  have hu0 : Filter.Tendsto (fun m ↦ eLpNorm (fun x ↦ u_m m x - u.toFun x) p volume)
      Filter.atTop (𝓝 0) :=
    tendsto_eLpNorm_cutoff_mul_sub hp hu (fun m ↦ (hv m).continuous.aestronglyMeasurable)
      (mollify_converges_Lp μ p hp ε hεpos hε hu) hRpos hR
  refine ⟨u_m, fun m ↦ (cutoff_contDiff (R m)).mul (hv m), ?_, hu0, ?_⟩
  · intro m
    exact (cutoff_hasCompactSupport (R := R m) (hRpos m).ne').mul_right
  · intro α hαk
    by_cases hα : α = []
    · subst α
      exact ⟨u.toFun, hu, hasWeakDerivativeOn_nil (huLoc.locallyIntegrableOn univ), hu0⟩
    · obtain ⟨g, hg, hw⟩ := u.weak_derivs_inLp α hαk
      have hg' : MemLp g p volume := by simpa [domainMeasure] using hg
      exact ⟨g, hg', hw, tendsto_eLpNorm_iteratedPartialDeriv_cutoff_mollify_sub
        μ hp u α hα hαk hg' hw hεpos hε hRpos hR⟩

end Approximation

end SobolevSpace
