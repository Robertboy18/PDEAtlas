/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Similarity
import PDE.Elliptic.PotentialTheory.FundamentalSolution.Pole
import PDE.Analysis.Calculus.LocalExtension.Ball
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Congruence

/-!
# Testing a regularized fundamental pole

A classical regularization agrees with the fundamental solution outside an
interior ball. Its Laplacian therefore evaluates a function harmonic on that
ball. The proof extends the test compactly inside the domain, then uses ordinary
integration by parts and the distributional pole identity.

Only the compact test meets the singular kernel. No singular Green function is
treated as an H¹ test, and no boundary normal derivative is used.
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Metric Set
open scoped Topology

/-- The Laplacian of a regularized fundamental pole evaluates a locally harmonic
test with the negative sign of the convention `-ΔΦ = δ`. -/
theorem integral_mul_laplacian_regularization_eq_neg
    {n : ℕ} [Fact (0 < n)] (hn : 2 ≤ n)
    {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    {x : ℝ^n} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hball : closedBall x R ⊆ Ω)
    {A u : ℝ^n → ℝ} (hA : ContDiff ℝ 2 A) (hu : ContDiffOn ℝ 2 u Ω)
    (hreg : ∀ z ∈ Ω, r ≤ ‖z - x‖ →
      A =ᶠ[𝓝 z] fun y ↦ fundamentalSolution n (y - x))
    (hlap : ∀ z ∈ ball x r, laplacian u z = 0) :
    (∫ z in Ω, u z * laplacian A z) = -u x := by
  obtain ⟨a, ha, hac, has, heq⟩ :=
    hu.exists_contDiff_tsupport_subset_eqOn_closedBall hΩ hr hrR hball
  have hagerm {z : ℝ^n} (hz : z ∈ ball x r) : a =ᶠ[𝓝 z] u :=
    (heq.mono ball_subset_closedBall).eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)
  have halap {z : ℝ^n} (hz : z ∈ ball x r) : laplacian a z = 0 := by
    rw [EuclideanLaplacian.laplacian_congr_nhds (hagerm hz)]
    exact hlap z hz
  have haoff {z : ℝ^n} (hz : z ∉ Ω) : a =ᶠ[𝓝 z] fun _ ↦ 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hz (has h))
  have hlarge {z : ℝ^n} (hz : z ∈ Ω) (hrz : r ≤ ‖z - x‖) :
      A z = fundamentalSolution n (z - x) ∧ laplacian A z = 0 := by
    have hg := hreg z hz hrz
    refine ⟨hg.eq_of_nhds, ?_⟩
    rw [EuclideanLaplacian.laplacian_congr_nhds hg]
    have hzx : z ≠ x := by
      intro he
      simp only [he, sub_self, norm_zero] at hrz
      linarith
    simpa only [one_smul] using
      laplacian_fundamentalSolution_smul_sub_eq_zero n zero_lt_one x z hzx
  calc
    (∫ z in Ω, u z * laplacian A z) = ∫ z in Ω, a z * laplacian A z := by
      apply setIntegral_congr_fun hΩ.measurableSet
      intro z hz
      change u z * laplacian A z = a z * laplacian A z
      by_cases hzr : ‖z - x‖ < r
      · rw [(hagerm (by simpa only [mem_ball, dist_eq_norm] using hzr)).eq_of_nhds]
      · rw [(hlarge hz (not_lt.mp hzr)).2, mul_zero, mul_zero]
    _ = ∫ z, a z * laplacian A z :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz ↦ by rw [(haoff hz).eq_of_nhds, zero_mul])
    _ = ∫ z, laplacian a z * A z :=
      PDE.DistributionTheory.integral_mul_laplacian_eq A ha hA hac
    _ = ∫ z, fundamentalSolution n (z - x) * laplacian a z := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ Ω
      · by_cases hzr : ‖z - x‖ < r
        · rw [halap (by simpa only [mem_ball, dist_eq_norm] using hzr),
            zero_mul, mul_zero]
        · rw [(hlarge hz (not_lt.mp hzr)).1, mul_comm]
      · rw [EuclideanLaplacian.laplacian_congr_nhds (haoff hz), PDE.laplacian_const,
          zero_mul, mul_zero]
    _ = -a x := integral_fundamentalSolution_sub_mul_laplacian hn ha hac x
    _ = -u x := congrArg Neg.neg (heq (mem_closedBall_self hr.le))

end PotentialTheory.GreenFunction.Domain
