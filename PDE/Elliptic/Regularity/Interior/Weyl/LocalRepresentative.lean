/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Weyl.Mollification
import PDE.Elliptic.Regularity.Interior.Weyl.RadialStabilization
import PDE.Analysis.MeasureTheory.StabilizedLimit
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# A local harmonic representative of distributionally harmonic data

A cutoff equal to one on the ball of radius `3R` localizes the data. Mollifications at scales
less than `R/4` are harmonic in the ball of radius `2R` and agree in the ball of radius `R`.
Their `L¹` convergence identifies this fixed smooth function with the original data almost
everywhere. There is no continuity assumption on the data.
-/

@[expose] public section

open PDE (laplacian)

open MeasureTheory Set Filter TopologicalSpace
open scoped Convolution Distributions Topology ENNReal
open SobolevSpace.Approximation

namespace LaplacianEquation

/-- Every point of an open distributional harmonicity domain has a ball on which the `L¹_loc`
data agrees almost everywhere with a classical harmonic function. The construction uses an
explicit radial mollifier and applies in every positive dimension. -/
theorem exists_isHarmonicPDE_ae_eq_on_ball_of_integral_laplacian_eq_zero
    {n : ℕ} [Fact (0 < n)] {Ω : Opens (ℝ^n)} {u : ℝ^n → ℝ}
    (hu : LocallyIntegrableOn u Ω volume)
    (hweak : ∀ φ : 𝓓(Ω, ℝ), (∫ y, u y * laplacian (φ : ℝ^n → ℝ) y) = 0)
    {c : ℝ^n} (hc : c ∈ Ω) :
    ∃ R > 0, Metric.ball c R ⊆ Ω ∧ ∃ v : ℝ^n → ℝ,
      IsHarmonicPDE n v (Metric.ball c R) ∧
        u =ᵐ[volume.restrict (Metric.ball c R)] v := by
  obtain ⟨r, hr, hrdomain⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds hc)
  obtain ⟨R, hR, hclosed⟩ : ∃ R > 0, Metric.closedBall c (4 * R) ⊆ Ω :=
    ⟨r / 4, by positivity, by rwa [mul_div_cancel₀ r four_ne_zero]⟩
  let b : ContDiffBump c :=
    { rIn := 3 * R
      rOut := 4 * R
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let χ : 𝓓(Ω, ℝ) :=
    { toFun := b
      contDiff' := b.contDiff
      hasCompactSupport' := b.hasCompactSupport
      tsupport_subset' := by simpa only [b.tsupport_eq] using hclosed }
  have hflat : ∀ y ∈ Metric.closedBall c (3 * R), χ y = 1 := fun y hy ↦ b.one_of_mem_closedBall hy
  let f : ℝ^n → ℝ := fun y ↦ χ y * u y
  have hf : Integrable f := TestFunction.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu χ
  obtain ⟨μ, w, hw, hrad, hz⟩ := exists_radial_mollifier n
  have hharm {ε : ℝ} (hε : 0 < ε) (hεR : ε < R / 4) :
      IsHarmonicPDE n (mollify μ ε f) (Metric.ball c (2 * R)) := by
    have hcut : ∀ x ∈ Metric.ball c (2 * R), ∀ y,
        x - y ∈ tsupport (scaled μ ε) → χ y = 1 := by
      intro x hx y hy
      have hxy : dist y x ≤ 2 * ε := by
        have hs := tsupport_scaled_subset_of_radial hrad hz hε hy
        simpa only [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm,
          dist_comm x y] using hs
      apply hflat
      have htri := dist_triangle y x c
      change dist x c < 2 * R at hx
      change dist y c ≤ 3 * R
      linarith
    have hh := isHarmonicPDE_convolution_cutoff_of_integral_laplacian_eq_zero
      hu hweak χ (scaled_contDiff μ) (scaled_hasCompactSupport μ hε) hcut
    have hmoll : mollify μ ε f =
        f ⋆[ContinuousLinearMap.mul ℝ ℝ] scaled μ ε := by
      change (scaled μ ε) ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f =
        f ⋆[ContinuousLinearMap.mul ℝ ℝ] scaled μ ε
      rw [convolution_lsmul_eq_mul]
      exact convolution_symm (ContinuousLinearMap.mul ℝ ℝ)
        ContinuousLinearMap.flip_mul
    rw [hmoll]
    exact hh
  have hballs {ε : ℝ} (hεR : ε < R / 4) {x : ℝ^n} (hx : x ∈ Metric.ball c R) :
      Metric.closedBall x (2 * ε) ⊆ Metric.ball c (2 * R) :=
    Metric.closedBall_subset_ball' (by linarith [Metric.mem_ball.mp hx])
  obtain ⟨δ, hδ, hδR⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < R / 4 := ⟨R / 8, by positivity, by linarith⟩
  let v : ℝ^n → ℝ := mollify μ δ f
  have hv : IsHarmonicPDE n v (Metric.ball c (2 * R)) := hharm hδ hδR
  have hstable {ε : ℝ} (hε : 0 < ε) (hεR : ε < R / 4) :
      EqOn (mollify μ ε f) v (Metric.ball c R) := fun x hx ↦
    mollify_eq_mollify_of_isHarmonicPDE hw hrad hz hf.locallyIntegrable
      hε hδ (hharm hε hεR) hv (hballs hεR hx) (hballs hδR hx)
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hεpos : ∀ j, 0 < ε j := fun _ ↦ Nat.one_div_pos_of_nat
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεsmall : ∀ᶠ j in atTop, ε j < R / 4 :=
    hεlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < R / 4))
  have hvcont : Continuous v := (mollify_contDiff_of_pos μ hδ f hf.locallyIntegrable).continuous
  have hvf : v =ᵐ[volume.restrict (Metric.ball c R)] f := by
    apply PDE.Analysis.ae_eq_of_tendsto_eLpNorm_of_eventually_eqOn
      (p := 1) Metric.isOpen_ball.measurableSet (by norm_num)
     
      (mollify_converges_Lp μ 1 (by norm_num) ε hεpos hεlim
        (memLp_one_iff_integrable.mpr hf))
    filter_upwards [hεsmall] with j hj
    exact hstable (hεpos j) hj
  refine ⟨R, hR, ?_, v, hv.mono (Metric.ball_subset_ball (by linarith)), ?_⟩
  · exact (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))).trans hclosed
  · filter_upwards [hvf, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxball
    have hχ : χ x = 1 := hflat x
      (Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hxball))
    simpa only [f, hχ, one_mul] using hx.symm

end LaplacianEquation
