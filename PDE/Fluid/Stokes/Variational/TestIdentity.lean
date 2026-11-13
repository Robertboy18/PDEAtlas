/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Variational.Energy
public import PDE.Spaces.Sobolev.Calculus.Divergence.AntisymmetricTest

/-!
# Antisymmetric tests for the Stokes minimum

Testing stationarity with `eⱼ ∂ᵢφ - eᵢ ∂ⱼφ` gives the curl equation for
the Laplacian-plus-force residual. Every derivative of the state in this
identity is its native L² weak derivative. The second derivatives occur only
on the compactly supported smooth test.
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace IncompressibleFlow.Stokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem inner_load_single
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (j : Fin n) (φ : TestFunctionOn n Ω) :
    ⟪f, toLp (ofTestFunction (Pi.single j φ))⟫ =
      ∫ x, f x j * φ.1 x ∂domainMeasure n Ω := by
  classical
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toLp_ofTestFunction_apply_ae
    (Pi.single j φ)] with x hx
  have hval :
      toLp (ofTestFunction (Pi.single j φ)) x =
        EuclideanSpace.single j (φ.1 x) := by
    apply PiLp.ext
    intro i
    rw [hx i]
    by_cases hij : i = j
    · subst i
      simp
    · simp [hij]
  rw [hval, EuclideanSpace.inner_single_right]
  simp [mul_comm]

/-- The raw divergence-free energy minimum satisfies the antisymmetric
second-test identity. This is the distributional curl equation before any
interior regularity or pressure reconstruction. -/
theorem antisymmetric_test_identity_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w)
    (i j : Fin n) (φ : TestFunctionOn n Ω) :
    (∑ k : Fin n, ∫ x, derivCoordCLM k (u j) x *
      (∂[k] (∂[i] φ.1.toFun)) x ∂domainMeasure n Ω) -
      (∑ k : Fin n, ∫ x, derivCoordCLM k (u i) x *
        (∂[k] (∂[j] φ.1.toFun)) x ∂domainMeasure n Ω) =
      (∫ x, f x j * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) -
        ∫ x, f x i * (∂[j] φ.1.toFun) x ∂domainMeasure n Ω := by
  have h := stationary_of_minimizes_energy f u hu hmin (antisymmetricTest i j φ)
    (divergence_antisymmetricTest i j φ)
  simp only [antisymmetricTest, map_sub, inner_sub_right,
    inner_gradient_ofTestFunction_single,
    inner_deriv_testFunction_eq_integral, inner_load_single] at h
  exact h

end IncompressibleFlow.Stokes
