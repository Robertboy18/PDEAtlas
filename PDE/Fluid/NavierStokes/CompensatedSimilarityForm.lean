/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.SimilarityPrincipal
import PDE.Spaces.Sobolev.Calculus.Product.MatrixPairing

/-!
# The compensation term of the similarity form

The principal similarity form `similarityPrincipalForm hΩ hb b Q` depends on the compensation `Q`
only through the matrix pairing `∑ₖ ∑ⱼ ⟨Qₖⱼ uⱼ, vₖ⟩`, so it is the form without compensation plus
that pairing. When the entries of `Q` represent the matrix entries of a field of operators
`T(x)`, the pairing is the integral of `⟨T(x) u(x), v(x)⟩` over the domain. Together with
`similarityPrincipalForm_lower_bound` this turns a compensation inequality for `T` into a lower
bound of the uncompensated form minus `∫ ⟨T u, u⟩`, the form used in the finite-rank correction
(4.20) of Hou, Wang and Yang.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 4.1, (4.1)-(4.3), p. 24,
  and Section 4.3, (4.20), p. 28.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev RealInnerProductSpace

namespace NavierStokes

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The principal similarity form is the uncompensated form plus the compensation pairing. -/
theorem similarityPrincipalForm_apply_eq_add (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (b : Fin n → W^{1,∞}(Ω)) (Q : Fin n → Fin n → DerivLp n ∞ Ω) (U V : H¹₀(Ω; ℝ^n)) :
    similarityPrincipalForm hΩ hb b Q U V = similarityPrincipalForm hΩ hb b 0 U V +
      ∑ k, ∑ j, ⟪Q k j • baseCoordCLM (U j), baseCoordCLM (V k)⟫ := by
  rw [similarityPrincipalForm_apply, similarityPrincipalForm_apply]
  simp only [Pi.zero_apply, add_zero, Lp.smul_add, inner_add_left, Finset.sum_add_distrib]
  ring

/-- The compensation pairing of matrix entries representing a field of operators `T` is the
integral of `⟨T(x) U(x), V(x)⟩` over the domain. -/
theorem sum_inner_smul_baseCoordCLM_eq_integral (Q : Fin n → Fin n → DerivLp n ∞ Ω)
    (T : ℝ^n → ℝ^n →L[ℝ] ℝ^n)
    (hQ : ∀ k j, (Q k j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ T x (EuclideanSpace.single j 1) k)
    (U V : H¹₀(Ω; ℝ^n)) :
    ∑ k, ∑ j, ⟪Q k j • baseCoordCLM (U j), baseCoordCLM (V k)⟫ =
      ∫ x in Ω, ⟪T x (ZeroBoundaryVectorSpace.toLp U x), ZeroBoundaryVectorSpace.toLp V x⟫ := by
  let f : Fin n → Fin n → ℝ^n → ℝ := fun k j x ↦
    ⟪(Q k j • baseCoordCLM (U j) : DerivLp n 2 Ω) x, baseCoordCLM (V k) x⟫
  have hint (k j : Fin n) : Integrable (f k j) (domainMeasure n Ω) :=
    L2.integrable_inner (Q k j • baseCoordCLM (U j)) (baseCoordCLM (V k))
  have hmul (k j : Fin n) : (fun x ↦ (Q k j • baseCoordCLM (U j) : DerivLp n 2 Ω) x)
      =ᵐ[domainMeasure n Ω] fun x ↦ Q k j x * baseCoordCLM (U j) x := by
    filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (Q k j) (baseCoordCLM (U j))] with x hx
    exact hx
  have hpoint : (fun x ↦ ⟪T x (ZeroBoundaryVectorSpace.toLp U x),
      ZeroBoundaryVectorSpace.toLp V x⟫) =ᵐ[domainMeasure n Ω] fun x ↦ ∑ k, ∑ j, f k j x := by
    filter_upwards [ae_all_iff.mpr fun k ↦ ae_all_iff.mpr (hQ k),
      ZeroBoundaryVectorSpace.toLp_apply_ae U, ZeroBoundaryVectorSpace.toLp_apply_ae V,
      ae_all_iff.mpr fun k ↦ ae_all_iff.mpr (hmul k)] with x hQx hUx hVx hmx
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [continuousLinearMap_apply_coordinate]
    simp only [f, hmx, hQx, hUx, hVx, Real.inner_apply, Finset.sum_mul]
  rw [integral_congr_ae hpoint, integral_finsetSum Finset.univ fun k _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ hint k j]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum Finset.univ fun j _ ↦ hint k j]
  exact Finset.sum_congr rfl fun j _ ↦ L2.inner_def _ _

end NavierStokes
