/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Regularization
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.RegularizedPole
public import PDE.Elliptic.Regularity.Interior.Weyl
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianH10
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Congruence

/-!
# Reciprocity from weak Dirichlet pairings

For distinct poles `x, y` in a bounded open domain with C¹ graph boundary,
`green_eq_swap_of_native_correctors` proves the symmetry `G(x, y) = G(y, x)`, Evans's §2.2.4(a),
Theorem 13, for correctors `φx`, `φy` that are harmonic, continuous on the closure with boundary
values `Φ(· - x)`, `Φ(· - y)`, and almost everywhere equal to weakly harmonic `H¹` functions. No
classical normal derivative or `C²` boundary regularity enters.

## How it works

Evans applies Green's identity to `G(x, ·)` and `G(y, ·)` on `U` minus two small balls, his (31). We
use the Dirichlet pairing instead. `exists_regularized_corrector` replaces each pole by a smooth
compactly supported function that agrees with the fundamental solution outside a small interior
ball, the two balls being disjoint, so that each corrector minus its regularized pole lies in `H¹₀`.
Testing the weak harmonicity of each corrector against the other `H¹₀` field
(`SobolevSpace.GraphSpace.sum_inner_gradient_sub_smooth_eq_integral_laplacian`) and evaluating the
regularized poles (`integral_mul_laplacian_regularization_eq_neg`) shows that the Dirichlet pairing
of the two fields equals `Φ(x - y) - φy(x)` and, read the other way, `Φ(y - x) - φx(y)`; its
symmetry gives the result.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), Theorem 13 (Symmetry of Green's function) and its
  proof, (31), pp. 35-36.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

open scoped Sobolev

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open scoped ENNReal InnerProductSpace Topology

private theorem laplacian_sub_regularization_eq_zero_near_other_pole
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    {p q : ℝ^n} {r : ℝ} (hr : 0 < r) (hp : ball p r ⊆ Ω)
    (hsep : 2 * r < dist p q)
    {φ A : ℝ^n → ℝ} (hφ : LaplacianEquation.IsHarmonicPDE n φ Ω)
    (hA : ContDiff ℝ 2 A)
    (hreg : ∀ z ∈ Ω, r ≤ ‖z - q‖ →
      A =ᶠ[𝓝 z] fun y ↦ fundamentalSolution n (y - q)) :
    ∀ z ∈ ball p r, laplacian (fun y ↦ φ y - A y) z = 0 := by
  intro z hz
  have hzΩ := hp hz
  have hdist : r ≤ dist z q := by
    linarith [dist_triangle p z q, (by simpa only [mem_ball, dist_comm] using hz : dist p z < r)]
  have hzq : z ≠ q := fun he ↦ by rw [he, dist_self] at hdist; linarith
  have hk : laplacian (fun y ↦ fundamentalSolution n (y - q)) z = 0 := by
    simpa only [one_smul] using laplacian_fundamentalSolution_smul_sub_eq_zero n zero_lt_one q z hzq
  rw [PDE.laplacian_sub _ _ _ (hφ.contDiffOn.contDiffAt (hΩ.mem_nhds hzΩ))
    hA.contDiffAt, hφ.laplacian_eq_zero hzΩ, EuclideanLaplacian.laplacian_congr_nhds
      (hreg z hzΩ (by simpa only [dist_eq_norm] using hdist)), hk, sub_zero]

/-- Continuous weak harmonic correctors on a C¹ graph domain give
the reciprocal Green kernel. This statement requires no classical boundary
derivatives; both testing fields are derived members of H¹₀. -/
theorem green_eq_swap_of_native_correctors
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    {x y : ℝ^(m + 1)} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y)
    (Ux Uy : H¹(Ω)) {φx φy : ℝ^(m + 1) → ℝ}
    (hUx : baseRepresentative Ux =ᵐ[domainMeasure (m + 1) Ω] φx)
    (hUy : baseRepresentative Uy =ᵐ[domainMeasure (m + 1) Ω] φy)
    (hφx : LaplacianEquation.IsHarmonicPDE (m + 1) φx Ω)
    (hφy : LaplacianEquation.IsHarmonicPDE (m + 1) φy Ω)
    (hcx : ContinuousOn φx (closure Ω)) (hcy : ContinuousOn φy (closure Ω))
    (hbx : EqOn φx (fun z ↦ fundamentalSolution (m + 1) (z - x)) (frontier Ω))
    (hby : EqOn φy (fun z ↦ fundamentalSolution (m + 1) (z - y)) (frontier Ω))
    (hwx : ∀ t : H¹₀(Ω),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex (m + 1) i) Ux, derivCoordCLM i t⟫_ℝ) = 0)
    (hwy : ∀ t : H¹₀(Ω),
      (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex (m + 1) i) Uy, derivCoordCLM i t⟫_ℝ) = 0) :
    fundamentalSolution (m + 1) (y - x) - φx y =
      fundamentalSolution (m + 1) (x - y) - φy x := by
  let := hgraph.c1ExtensionAtlas hΩ hbounded
  obtain ⟨P⟩ := exists_inwardPartition hΩ hbounded (hasC1Boundary_of_local_graph hgraph)
  obtain ⟨rx, hrx, hballx⟩ := Metric.isOpen_iff.mp hΩ x hx
  obtain ⟨ry, hry, hbally⟩ := Metric.isOpen_iff.mp hΩ y hy
  obtain ⟨r, hr, hrx', hry', hrxy⟩ : ∃ r : ℝ, 0 < r ∧ 8 * r ≤ rx ∧ 8 * r ≤ ry ∧
      8 * r ≤ dist x y := ⟨min rx (min ry (dist x y)) / 8,
    div_pos (lt_min hrx (lt_min hry (dist_pos.mpr hxy))) (by norm_num),
    by linarith [min_le_left rx (min ry (dist x y))],
    by linarith [(min_le_right rx (min ry (dist x y))).trans (min_le_left ry (dist x y))],
    by linarith [(min_le_right rx (min ry (dist x y))).trans (min_le_right ry (dist x y))]⟩
  have hBx : closedBall x (2 * r) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hballx
  have hBy : closedBall y (2 * r) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hbally
  have hsmallx : ball x r ⊆ Ω := (ball_subset_ball (by linarith)).trans hballx
  have hsmally : ball y r ⊆ Ω := (ball_subset_ball (by linarith)).trans hbally
  obtain ⟨Ax, hAx, hAxc, wx, hwx', hbasewx, hregx⟩ :=
    exists_regularized_corrector P hbounded hr hsmallx Ux hcx hUx hbx
  obtain ⟨Ay, hAy, hAyc, wy, hwy', hbasewy, hregy⟩ :=
    exists_regularized_corrector P hbounded hr hsmally Uy hcy hUy hby
  have heqx : (∫ z, baseCoordCLM wy z * laplacian Ax z ∂domainMeasure (m + 1) Ω) =
      -(φy x - Ay x) :=
    (integral_congr_ae (hbasewy.mono fun z hz ↦ congrArg (· * laplacian Ax z) hz)).trans <|
      integral_mul_laplacian_regularization_eq_neg hn hΩ hr (by linarith) hBx
        (hAx.of_le (by simp)) (hφy.contDiffOn.sub (hAy.of_le (by simp)).contDiffOn)
        (fun z hz ↦ hregx z (subset_closure hz))
        (laplacian_sub_regularization_eq_zero_near_other_pole hΩ hr hsmallx
          (by linarith) hφy (hAy.of_le (by simp)) (fun z hz ↦ hregy z (subset_closure hz)))
  have heqy : (∫ z, baseCoordCLM wx z * laplacian Ay z ∂domainMeasure (m + 1) Ω) =
      -(φx y - Ax y) :=
    (integral_congr_ae (hbasewx.mono fun z hz ↦ congrArg (· * laplacian Ay z) hz)).trans <|
      integral_mul_laplacian_regularization_eq_neg hn hΩ hr (by linarith) hBy
        (hAy.of_le (by simp)) (hφx.contDiffOn.sub (hAx.of_le (by simp)).contDiffOn)
        (fun z hz ↦ hregy z (subset_closure hz))
        (laplacian_sub_regularization_eq_zero_near_other_pole hΩ hr hsmally
          (by rw [dist_comm]; linarith) hφx (hAx.of_le (by simp))
          (fun z hz ↦ hregx z (subset_closure hz)))
  have hpairx := sum_inner_gradient_sub_smooth_eq_integral_laplacian Ux Ax hAx hAxc wx hwx' hwx wy
  have hpairy := sum_inner_gradient_sub_smooth_eq_integral_laplacian Uy Ay hAy hAyc wy hwy' hwy wx
  have hsym : (∑ i, ⟪derivCoordCLM i wx, derivCoordCLM i wy⟫_ℝ) =
      ∑ i, ⟪derivCoordCLM i wy, derivCoordCLM i wx⟫_ℝ :=
    Finset.sum_congr rfl (fun _ _ ↦ real_inner_comm _ _)
  have hAx_y := (hregx y (subset_closure hy) (by
    rw [← dist_eq_norm, dist_comm]
    linarith)).eq_of_nhds
  have hAy_x := (hregy x (subset_closure hx) (by
    rw [← dist_eq_norm]
    linarith)).eq_of_nhds
  rw [heqx] at hpairx
  rw [heqy] at hpairy
  linarith

end PotentialTheory.GreenFunction.Domain
