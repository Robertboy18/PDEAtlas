/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Graph.Regularity
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Graph.Tangency
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Graph.Differential
public import PDE.Analysis.Evolution.ODE.Linear.Diagonal.SpectralGap
public import PDE.Analysis.Calculus.LocalExtension.SmallDerivative

/-!
# Local invariant graphs from a smooth nonlinear remainder

A finite diagonal system with a nonlinear remainder vanishing to first order
has a local C² graph tangent to its center space. A compactly supported
extension makes the three weighted integral equations contractive. The graph
is constructed from their common solution. The differential invariance and
containment statements concern the original vector field on a ball where the
extension agrees with it.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff NNReal

namespace PDE.Analysis.Evolution

/-- A smooth finite diagonal system admits a local C² center graph.
The same graph contains every equilibrium and every complete orbit that stays
in the stated ball. The radius and graph are chosen before any orbit. -/
theorem exists_local_diagonalInvariantGraph
    {ι : Type*} [Fintype ι] (rate : ι → ℝ)
    {N : (ι → ℝ) → (ι → ℝ)} (hN : ContDiff ℝ ∞ N)
    (hN0 : N 0 = 0) (hDN0 : fderiv ℝ N 0 = 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ (ρ : ℝ) (φ : (ι → ℝ) → (ι → ℝ)), 0 < ρ ∧ ρ < r ∧
      ContDiff ℝ 2 φ ∧ φ 0 = 0 ∧
      HasFDerivAt φ (diagonalCenterProjection rate) 0 ∧
      (∀ ξ, diagonalCenterProjection rate (φ ξ) = diagonalCenterProjection rate ξ) ∧
      (∀ ξ, φ (diagonalCenterProjection rate ξ) = φ ξ) ∧
      (∀ ξ, (∀ i, rate i * ξ i = 0) → φ ξ ∈ ball 0 ρ →
        fderiv ℝ φ ξ (diagonalCenterProjection rate
          (fun i ↦ rate i * φ ξ i + N (φ ξ) i)) =
            fun i ↦ rate i * φ ξ i + N (φ ξ) i) ∧
      (∀ x ∈ ball 0 ρ, (∀ i, rate i * x i + N x i = 0) → x = φ x) ∧
      (∀ u : C(ℝ, ι → ℝ), (∀ t, u t ∈ ball 0 ρ) →
        (∀ t, HasDerivAt u (fun i ↦ rate i * u t i + N (u t) i) t) →
        ∀ t, u t = φ (u t)) := by
  obtain ⟨η, hη, hgap3⟩ := exists_pos_mul_lt_abs_rate rate 3
  have hgap1 (i : ι) (hi : rate i ≠ 0) : η < |rate i| := by
    have := hgap3 i hi
    linarith
  have hgap2 (i : ι) (hi : rate i ≠ 0) : 2 * η < |rate i| := by
    have := hgap3 i hi
    linarith
  let G := diagonalGreen hη rate hgap1
  let H := diagonalGreen (by linarith : 0 < 2 * η) rate hgap2
  let V := diagonalGreen (by linarith : 0 < 3 * η) rate hgap3
  let d : ℝ := 1 + ‖G‖ + ‖H‖ + ‖V‖
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨ρ, Ncut, hρ, hρr, hcut, _, _, hnear, hLip, hzero, hjet, M, K, hM, hK⟩ :=
    hN.exists_compactSupport_small_lipschitz hN0 hDN0 (inv_pos.mpr hd) hr
  have hsmall1 : ‖G‖ * (⟨d⁻¹, (inv_pos.mpr hd).le⟩ : ℝ≥0) < 1 := by
    change ‖G‖ * d⁻¹ < 1
    rw [← div_eq_mul_inv, div_lt_one hd]
    dsimp [d]
    linarith [norm_nonneg H, norm_nonneg V]
  have hsmall2 : ‖H‖ * (⟨d⁻¹, (inv_pos.mpr hd).le⟩ : ℝ≥0) < 1 := by
    change ‖H‖ * d⁻¹ < 1
    rw [← div_eq_mul_inv, div_lt_one hd]
    dsimp [d]
    linarith [norm_nonneg G, norm_nonneg V]
  have hsmall3 : ‖V‖ * (⟨d⁻¹, (inv_pos.mpr hd).le⟩ : ℝ≥0) < 1 := by
    change ‖V‖ * d⁻¹ < 1
    rw [← div_eq_mul_inv, div_lt_one hd]
    dsimp [d]
    linarith [norm_nonneg G, norm_nonneg H]
  let φ := diagonalInvariantGraph hη rate hgap1 hLip hzero hsmall1
  have hφ : ContDiff ℝ 2 φ :=
    contDiff_diagonalInvariantGraph hη rate hgap1 hgap2 hgap3 hLip hzero
      (hcut.of_le (by simp)) hM hK hsmall1 hsmall2 hsmall3
  refine ⟨ρ, φ, hρ, hρr, hφ,
    diagonalInvariantGraph_zero hη rate hgap1 hLip hzero hsmall1,
    hasFDerivAt_diagonalInvariantGraph_zero hη rate hgap1 hgap2 hLip hzero
      (hcut.of_le (by simp)) hM hjet hsmall1 hsmall2,
    diagonalCenterProjection_diagonalInvariantGraph hη rate hgap1 hLip hzero hsmall1,
    diagonalInvariantGraph_diagonalCenterProjection hη rate hgap1 hLip hzero hsmall1,
    ?_, ?_, ?_⟩
  · intro ξ hξ hmem
    have heq := fderiv_diagonalInvariantGraph_apply_center hη rate hgap1 hLip hzero
      hsmall1 ξ hξ (hφ.differentiable (by norm_num)).differentiableAt
    change fderiv ℝ φ ξ (diagonalCenterProjection rate
      (fun i ↦ rate i * φ ξ i + Ncut (φ ξ) i)) =
        fun i ↦ rate i * φ ξ i + Ncut (φ ξ) i at heq
    rwa [hnear (φ ξ) hmem] at heq
  · intro x hx heq
    apply equilibrium_eq_diagonalInvariantGraph hη rate hgap1 hLip hzero hsmall1 x
    simpa only [hnear x hx] using heq
  · intro u hbound hu t
    apply eq_diagonalInvariantGraph_of_bounded hη rate hgap1 hLip hzero hsmall1 u ρ
    · intro s
      exact (mem_ball_zero_iff.mp (hbound s)).le
    · intro s
      simpa only [hnear (u s) (hbound s)] using hu s

end PDE.Analysis.Evolution
