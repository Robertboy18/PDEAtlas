/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.NewtonianDistribution
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarDistribution
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Calculus

/-!
# The Laplace pole identity at an arbitrary center

The logarithmic and Newtonian pole identities combine at the exact classical
test regularity `C²`. Translation gives the identity at every pole.
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory

open MeasureTheory Set TopologicalSpace
open scoped Distributions

/-- The fundamental solution has pole mass `-1` for the Laplacian,
tested against an arbitrary compactly supported `C²` function. -/
theorem integral_fundamentalSolution_mul_laplacian
    {n : ℕ} (hn : 2 ≤ n) {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u) :
    (∫ y, fundamentalSolution n y * laplacian u y) = -u 0 := by
  let φ : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ) := ⟨u, hu, hc, subset_univ _⟩
  by_cases h2 : n = 2
  · subst n
    exact Planar.integral_fundamentalSolution_mul_laplacian φ
  · have hn3 : 3 ≤ n := by omega
    have : Fact (0 < n) := ⟨by omega⟩
    exact Newtonian.integral_fundamentalSolution_mul_laplacian hn3 φ

/-- Translation preserves the exact pole mass, with no regularity beyond `C²`
on the compactly supported test function. -/
theorem integral_fundamentalSolution_sub_mul_laplacian
    {n : ℕ} (hn : 2 ≤ n) {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u) (x : ℝ^n) :
    (∫ y, fundamentalSolution n (y - x) * laplacian u y) = -u x := by
  have hs : ContDiff ℝ 2 (fun y ↦ u (x + y)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have hcs : HasCompactSupport (fun y ↦ u (x + y)) :=
    hc.comp_homeomorph (Homeomorph.addLeft x)
  have hpole := integral_fundamentalSolution_mul_laplacian hn hs hcs
  simp only [PDE.laplacian_comp_add_left u x _ hu.contDiffAt, add_zero] at hpole
  have htrans := integral_add_left_eq_self (μ := volume)
    (fun y ↦ fundamentalSolution n (y - x) * laplacian u y) x
  simp only [add_sub_cancel_left] at htrans
  exact htrans.symm.trans hpole

/-- The translated pole kernel times the Laplacian of a compact classical test
is integrable, despite the singularity at the pole. -/
theorem integrable_fundamentalSolution_sub_mul_laplacian
    {n : ℕ} {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u) (x : ℝ^n) :
    Integrable (fun y ↦ fundamentalSolution n (y - x) * laplacian u y) := by
  have hs : ContDiff ℝ 2 (fun y ↦ u (x + y)) :=
    hu.comp (contDiff_const.add contDiff_id)
  have hcs : HasCompactSupport (fun y ↦ u (x + y)) :=
    hc.comp_homeomorph (Homeomorph.addLeft x)
  let φ : 𝓓^{2}((⊤ : Opens (ℝ^n)), ℝ) := ⟨_, hs, hcs, subset_univ _⟩
  have hi : Integrable (fun y ↦ fundamentalSolution n y * laplacian φ y) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_fundamentalSolution n).integrable_smul_right_of_hasCompactSupport
        φ.continuous_laplacian_two φ.hasCompactSupport_laplacian
  have hlap (y : ℝ^n) : laplacian φ y = laplacian u (x + y) :=
    PDE.laplacian_comp_add_left u x y hu.contDiffAt
  apply (hi.comp_add_left (-x)).congr
  filter_upwards with y
  rw [hlap]
  congr 1
  · congr 1
    abel
  · congr 1
    abel

end PotentialTheory
