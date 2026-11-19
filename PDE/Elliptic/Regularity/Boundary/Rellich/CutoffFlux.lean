/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.CutoffTest
public import PDE.Elliptic.Regularity.Interior.PoissonWeakForm
public import PDE.Analysis.MeasureTheory.Integral.CollarCutoff
public import PDE.Analysis.MeasureTheory.Lp.Continuous
public import PDE.FDeriv.Calculus.ScalarComposition

/-!
# Weak Green pairings as collar flux limits

A complementary collar cutoff is a genuine H¹₀ test. Its weak Poisson identity
isolates a volume flux across the collar. The other two terms tend to zero by
dominated convergence. The state has only an L² weak gradient; no boundary
representative of this gradient occurs.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Sobolev Gradient Topology

namespace SobolevSpace.GraphSpace.Rellich

open Approximation.UpToBoundary

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}

/-- The gradient of the complementary cutoff, including its transversal term. -/
theorem gradient_collarComplement
    {φ d : ℝ^(m + 1) → ℝ} {χ : ℝ → ℝ} {x : ℝ^(m + 1)}
    (hφ : DifferentiableAt ℝ φ x) (hd : DifferentiableAt ℝ d x)
    (t : ℝ) (hχ : DifferentiableAt ℝ χ (d x / t)) :
    ∇ (fun y ↦ φ y * (1 - χ (d y / t))) x =
      (1 - χ (d x / t)) • ∇ φ x -
        (t⁻¹ * (φ x * deriv χ (d x / t))) • ∇ d x := by
  have hddiv : DifferentiableAt ℝ (fun y ↦ d y / t) x := by
    simpa only [div_eq_mul_inv] using hd.mul_const t⁻¹
  have hcomp : DifferentiableAt ℝ (fun y ↦ χ (d y / t)) x := hχ.comp x hddiv
  have hco : DifferentiableAt ℝ (fun y ↦ 1 - χ (d y / t)) x :=
    (differentiableAt_const (1 : ℝ)).fun_sub hcomp
  ext i
  simp only [WithLp.ofLp_sub, Pi.sub_apply, PiLp.smul_apply, smul_eq_mul,
    PDE.gradient_apply_eq_partialDeriv]
  rw [PDE.partialDeriv_mul hφ hco,
    PDE.partialDeriv_sub (differentiableAt_const (1 : ℝ)) hcomp,
    PDE.partialDeriv_const, PDE.partialDeriv_comp_real i hχ hddiv]
  have hs : (∂[i] (fun y ↦ d y / t)) x = t⁻¹ * (∂[i] d) x := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (PDE.partialDeriv_const_smul (n := m + 1) (i := i) (f := d) (x := x) t⁻¹)
  rw [hs]
  ring

/-- A weak Poisson state has zero Green pairing against any H¹₀ test,
expressed using specified almost-everywhere representatives. -/
theorem integral_greenPairing_eq_zero_of_H10
    (z : H¹(Ω)) (f : DerivLp (m + 1) 2 Ω)
    (hweak : ∀ φ : TestFunctionOn (m + 1) Ω,
      (∫ x, baseRepresentative z x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure (m + 1) Ω) =
      ∫ x, (f : ℝ^(m + 1) → ℝ) x * φ.1.toFun x ∂domainMeasure (m + 1) Ω)
    (v : H¹₀(Ω)) {v₀ : ℝ^(m + 1) → ℝ} {v₁ : ℝ^(m + 1) → ℝ^(m + 1)}
    (hv₀ : baseRepresentative (v : H¹(Ω)) =ᵐ[domainMeasure (m + 1) Ω] v₀)
    (hv₁ : (wkpGradientCLM (v : H¹(Ω)) : ℝ^(m + 1) → ℝ^(m + 1))
      =ᵐ[domainMeasure (m + 1) Ω] v₁) :
    (∫ x, (f : ℝ^(m + 1) → ℝ) x * v₀ x ∂domainMeasure (m + 1) Ω) +
      (∫ x, inner ℝ ((wkpGradientCLM z : ℝ^(m + 1) → ℝ^(m + 1)) x) (v₁ x)
        ∂domainMeasure (m + 1) Ω) = 0 := by
  have h := poisson_weakForm_of_integral_laplacian_eq z f hweak v
  have hg : inner ℝ (wkpGradientCLM z) (wkpGradientCLM (v : H¹(Ω))) =
      ∑ i, inner ℝ ((z : WkpAmbientOn (m + 1) 1 2 Ω) (singleDerivIndex (m + 1) i))
        (derivCoordCLM i v) := by
    simpa only [wkpGradientCLM, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_pi', wkpCoordinateCLM_apply, derivCoordCLM_apply] using
      Lp.inner_euclideanTuple
        (fun i ↦ wkpCoordinateCLM (singleDerivIndex (m + 1) i) z)
        (fun i ↦ wkpCoordinateCLM (singleDerivIndex (m + 1) i) (v : H¹(Ω)))
  have hb : inner ℝ f (baseCoordCLM v) =
      ∫ x, (f : ℝ^(m + 1) → ℝ) x * v₀ x ∂domainMeasure (m + 1) Ω := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv₀] with x hx
    change (baseRepresentative (v : H¹(Ω)) x) * (f : ℝ^(m + 1) → ℝ) x = _
    rw [hx, mul_comm]
  have hgi : inner ℝ (wkpGradientCLM z) (wkpGradientCLM (v : H¹(Ω))) =
      ∫ x, inner ℝ ((wkpGradientCLM z : ℝ^(m + 1) → ℝ^(m + 1)) x) (v₁ x)
        ∂domainMeasure (m + 1) Ω := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv₁] with x hx
    rw [hx]
  rw [← hg, inner_neg_left, hb, hgi] at h
  linarith

end SobolevSpace.GraphSpace.Rellich
