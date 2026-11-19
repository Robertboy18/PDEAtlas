/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.DirichletFlux
public import PDE.Elliptic.Homogenization.PeriodicCell.FluxProducts

/-!
# Oscillating-test identification of microscopic flux directions

The adjoint cell equation and the Dirichlet equation control the two
products in the oscillating-test identity. Consequently, strong convergence of
the solution values identifies every compactly tested microscopic flux direction
with the derived effective flux. No convergence of these products is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter TopologicalSpace SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.PeriodicAveraging SobolevSpace.Periodic
open scoped ENNReal Topology InnerProductSpace Sobolev Distributions

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
    {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)

/-- Pointwise adjointness identifies the two weighted oscillating-test pairings. -/
theorem inner_adjointCellFlux_weighted_gradient (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ξ : ℝ^n) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(Ω)) :
    ⟪rescaleLp hΩ ε hε hε1 (coefficientOperator (adjointCoefficient A)
      (correctedField (adjointCoefficient A) hα (adjointCoefficient_elliptic A hA) ξ)),
      testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM u⟫_ℝ =
    ⟪rescaledCoefficientOperator A hΩ ε hε hε1 (GraphSpace.gradientCLM u),
      testFunctionLpTop (Ω := Ω) κ • rescaleLp hΩ ε hε hε1
        (correctedField (adjointCoefficient A) hα
          (adjointCoefficient_elliptic A hA) ξ)⟫_ℝ := by
  let v := correctedField (adjointCoefficient A) hα (adjointCoefficient_elliptic A hA) ξ
  have ha := ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
    (inv_ne_zero hε.ne')).ae_eq_comp (adjointCoefficient_ae A)) (s := Ω)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rescale_coefficientOperator_ae (adjointCoefficient A) hΩ ε hε hε1 v,
    rescaledCoefficientOperator_ae A hΩ ε hε hε1 (GraphSpace.gradientCLM u),
    Lp.coeFn_lpSMul (r := 2) (testFunctionLpTop (Ω := Ω) κ) (GraphSpace.gradientCLM u),
    Lp.coeFn_lpSMul (r := 2) (testFunctionLpTop (Ω := Ω) κ) (rescaleLp hΩ ε hε hε1 v),
    rescaleLp_ae hΩ ε hε hε1 v, ha] with x hq hp hm hn hv ha
  change adjointCoefficient A (toTorus n (ε⁻¹ • x)) =
    (A (toTorus n (ε⁻¹ • x))).adjoint at ha
  rw [hq, hp, hm, hn, Pi.smul_apply', Pi.smul_apply', hv, ha,
    real_inner_smul_right, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm]

variable (hn : 0 < n) (hΩo : IsOpen Ω) (f : DerivLp n 2 Ω)


include hΩo in
/-- The Dirichlet equation makes the weighted microscopic flux pairing with
any rescaled cell correction tend to zero. -/
theorem tendsto_inner_dirichletFlux_corrector
    {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (w : h1Space n)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ Ω) :
    Tendsto (fun j ↦ ⟪rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j),
      testFunctionLpTop (Ω := Ω) κ • rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (SobolevSpace.Periodic.gradientCLM n w)⟫_ℝ) l (𝓝 0) := by
  obtain ⟨R, hR⟩ := exists_rescaledDirichletFlux_norm_bound A hΩ hα hA hn hΩo f
  exact tendsto_inner_rescale_gradient_of_weakDivergence hΩ hΩo
    (fun j ↦ rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j)) f
    (fun j ↦ weakDivergenceFunctional_rescaledDirichletFlux A hΩ hα hA hn hΩo f
      (ε j) (hε j) (hε1 j)) R (fun j ↦ hR (ε j) (hε j) (hε1 j)) ε hε hε1 ht w κ hκ

variable [IsFiniteMeasure (volume.restrict Ω)]

include hΩo in
/-- Along any strongly L²-convergent family of Dirichlet solutions,
compactly tested flux directions converge to the effective flux pairing. -/
theorem tendsto_inner_dirichletFlux_weighted_const
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ baseCoordCLM
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)) l
      (𝓝 (baseCoordCLM U)))
    (ξ : ℝ^n) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ Ω) :
    Tendsto (fun j ↦ ⟪rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j),
      testFunctionLpTop (Ω := Ω) κ • Lp.const 2 (volume.restrict Ω) ξ⟫_ℝ) l
      (𝓝 ⟪Lp.const 2 (volume.restrict Ω) ((effectiveOperator A hα hA).adjoint ξ),
        testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM U⟫_ℝ) := by
  let A' := adjointCoefficient A
  let hA' := adjointCoefficient_elliptic A hA
  let w := correctorPotential A' hα hA' ξ
  have hzero := tendsto_inner_dirichletFlux_corrector A hα hA hΩ hn hΩo f
    ε hε hε1 ht w.val κ hκ
  change Tendsto (fun j ↦ ⟪rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j),
    testFunctionLpTop (Ω := Ω) κ • rescaleLp hΩ (ε j) (hε j) (hε1 j)
      (meanZeroGradientCLM n (correctorPotential A' hα hA' ξ))⟫_ℝ) l (𝓝 0) at hzero
  rw [meanZeroGradientCLM_correctorPotential] at hzero
  have hcell := tendsto_inner_adjointCellFlux_weighted_gradient A hα hA hΩ hΩo
    ε hε hε1 ht (fun j ↦
      rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f) U hu ξ κ
  have he (j : ι) :
      ⟪rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j),
        testFunctionLpTop (Ω := Ω) κ • Lp.const 2 (volume.restrict Ω) ξ⟫_ℝ =
      ⟪rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (coefficientOperator A' (correctedField A' hα hA' ξ)),
        testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM
          (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)⟫_ℝ -
      ⟪rescaledDirichletFlux A hΩ hα hA hn f (ε j) (hε j) (hε1 j),
        testFunctionLpTop (Ω := Ω) κ • rescaleLp hΩ (ε j) (hε j) (hε1 j)
          (correctorGradient A' hα hA' ξ : Lp (ℝ^n) 2 (cellMeasure n))⟫_ℝ := by
    have h := inner_adjointCellFlux_weighted_gradient A hα hA hΩ
      (ε j) (hε j) (hε1 j) ξ κ
      (rescaledDirichletSolution A hα hA hn hΩ (ε j) (hε j).ne' f)
    have hc : rescaleLp hΩ (ε j) (hε j) (hε1 j) (correctedField A' hα hA' ξ) =
        Lp.const 2 (volume.restrict Ω) ξ +
          rescaleLp hΩ (ε j) (hε j) (hε1 j)
            (correctorGradient A' hα hA' ξ : Lp (ℝ^n) 2 (cellMeasure n)) := by
      change rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (Lp.const 2 (cellMeasure n) ξ +
          (correctorGradient A' hα hA' ξ : Lp (ℝ^n) 2 (cellMeasure n))) = _
      rw [map_add, rescaleLp_const]
    rw [hc, Lp.add_smul, inner_add_right] at h
    exact eq_sub_of_add_eq h.symm
  simp_rw [he]
  simpa only [sub_zero] using hcell.sub hzero

end PDE.Elliptic.Homogenization.PeriodicCell
