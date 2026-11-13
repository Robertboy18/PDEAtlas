/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.FluxLift
public import PDE.Spaces.Sobolev.Calculus.Divergence.Functional
public import PDE.FDeriv.Operators

/-!
# Canonical Sobolev tests for rescaled periodic fluxes

Smooth density extends the compact Euclidean divergence identity to the
zero-boundary Sobolev space. The resulting flux has zero residual in the canonical
weak divergence functional, with no extra regularity of the periodic field.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev Gradient

namespace SobolevSpace.Periodic

/-- The lifted divergence identity holds on every canonical zero-boundary Sobolev test. -/
theorem inner_rescale_gradient_eq_zero {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) (v : Lp (ℝ^n) 2 (cellMeasure n))
    (hv : ∀ u : h1Space n, ⟪v, gradientCLM n u⟫_ℝ = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (u : H¹₀(Ω)) :
    ⟪rescaleLp hΩ ε hε hε1 v, GraphSpace.gradientCLM u⟫_ℝ = 0 := by
  let q := rescaleLp hΩ ε hε hε1 v
  let L := (innerSL ℝ q).comp GraphSpace.gradientCLM
  change L u = 0
  refine DenseRange.induction_on GraphSpace.denseRange_testFunctionToH10Linear u ?_ ?_
  · exact isClosed_eq L.continuous continuous_const
  · intro φ
    change ⟪q, GraphSpace.gradientCLM (GraphSpace.testFunctionToH10 φ)⟫_ℝ = 0
    rw [L2.inner_def]
    have htest : (GraphSpace.gradientCLM (GraphSpace.testFunctionToH10 φ) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n Ω] ∇ φ.1.toFun := by
      have hd : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
          GraphSpace.derivCoordCLM i (GraphSpace.testFunctionToH10 φ) x =
            (∂[i] φ.1.toFun) x :=
        ae_all_iff.mpr fun i ↦ GraphSpace.derivCoordCLM_testFunction_apply_ae i φ
      filter_upwards [GraphSpace.gradientCLM_apply_ae (GraphSpace.testFunctionToH10 φ), hd]
        with x hx hy
      ext i
      exact (hx i).trans ((hy i).trans (PDE.gradient_apply_eq_partialDeriv _ _ _).symm)
    calc
      _ = ∫ x in Ω, ⟪v (toTorus n (ε⁻¹ • x)), ∇ φ.1.toFun x⟫_ℝ := by
        apply integral_congr_ae
        filter_upwards [rescaleLp_ae hΩ ε hε hε1 v, htest] with x hx hy
        rw [show q x = _ from hx, hy]
      _ = ∫ x, ⟪v (toTorus n (ε⁻¹ • x)), ∇ φ.1.toFun x⟫_ℝ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hz : ∇ φ.1.toFun x = 0 := by
          rw [gradient, fderiv_of_notMem_tsupport ℝ (fun h ↦ hx (φ.2 h)), map_zero]
        rw [hz, inner_zero_right]
      _ = 0 := integral_inner_gradient_toTorus_smul_eq_zero v hv ε⁻¹
        (inv_ne_zero hε.ne') (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport

/-- The canonical divergence residual of a rescaled periodic solenoidal field vanishes. -/
theorem weakDivergenceFunctional_rescale_eq_zero {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) (v : Lp (ℝ^n) 2 (cellMeasure n))
    (hv : ∀ u : h1Space n, ⟪v, gradientCLM n u⟫_ℝ = 0)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    GraphSpace.weakDivergenceFunctional
      (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp (rescaleLp hΩ ε hε hε1 v)) 0 = 0 := by
  ext u
  rw [GraphSpace.weakDivergenceFunctional_apply, inner_zero_left, sub_zero]
  let Q := fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp (rescaleLp hΩ ε hε hε1 v)
  change (∑ i, ⟪Q i, GraphSpace.derivCoordCLM i u⟫_ℝ) = 0
  rw [← Lp.inner_euclideanTuple]
  have hQ : Lp.euclideanTuple Q = rescaleLp hΩ ε hε hε1 v :=
    Lp.euclideanTuple_coordinates _
  rw [hQ]
  exact inner_rescale_gradient_eq_zero hΩ v hv ε hε hε1 u

end SobolevSpace.Periodic
