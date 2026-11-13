/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Algebra
public import PDE.FDeriv.Operators
import CAS.ExactTactic

/-!
# The classical Poisson energy

We define the energy `classicalEnergy Ω f u = ∫_Ω ½|∇u|² - f u` for the convention `-Δu = f`,
and expand it along affine variations `u + t v`. For `u` and `v` that are `C¹` up to the boundary
of a bounded open set `Ω` (`ContDiffUpToBoundary 1`), `classicalEnergy_add_mul` writes the energy
of `u + t v` as an exact quadratic polynomial in `t` whose coefficients are finite integrals, and
`hasDerivAt_classicalEnergy_add_mul` reads off the first variation at `t = 0`; SymLean's `cas`
tactic differentiates the quadratic. No differentiable extension across the boundary is used.

The energy is Evans's energy functional `I[w]` of §2.2.5(b), and the expansion is his computation
of `i(τ) = I[u + τv]` in step 2 of the proof of Theorem 17 (Dirichlet's principle).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.5(b), the energy functional and the admissible set,
  p. 42, and step 2 of the proof of Theorem 17 (Dirichlet's principle), p. 43.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PoissonEquation

open MeasureTheory Set SobolevSpace
open scoped BigOperators Gradient

variable {n : ℕ} {Ω : Set (ℝ^n)} {f u v : ℝ^n → ℝ}

/-- The classical Dirichlet functional for the convention `-Δu = f`. -/
def classicalEnergy (Ω : Set (ℝ^n)) (f u : ℝ^n → ℝ) : ℝ :=
  ∫ x in Ω, (1 / 2 : ℝ) * (∑ i, ((∂[i] u) x) ^ 2) - f x * u x

/-- The coordinate definition is the usual integral of `½|∇u|² - fu`. -/
theorem classicalEnergy_eq_integral_norm :
    classicalEnergy Ω f u =
      ∫ x in Ω, (1 / 2 : ℝ) * ‖∇ u x‖ ^ 2 - f x * u x := by
  simp only [classicalEnergy, EuclideanSpace.real_norm_sq_eq,
    PDE.gradient_apply_eq_partialDeriv]

/-- Products of first derivatives are integrable for classical closure data. -/
private theorem integrable_partialDeriv_mul
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u Ω) (hv : ContDiffUpToBoundary 1 v Ω)
    (i : Fin n) :
    IntegrableOn (fun x ↦ (∂[i] u) x * (∂[i] v) x) Ω := by
  exact (hu.memLp_iteratedPartialDeriv hΩ hb 2 [i] (by simp)).integrable_mul
    (hv.memLp_iteratedPartialDeriv hΩ hb 2 [i] (by simp))

/-- The squared gradient of classical closure data is integrable. -/
private theorem integrable_sum_sq_partialDeriv
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u Ω) :
    IntegrableOn (fun x ↦ ∑ i, ((∂[i] u) x) ^ 2) Ω := by
  exact integrable_finsetSum _ fun i _ ↦
    (hu.memLp_iteratedPartialDeriv hΩ hb 2 [i] (by simp)).integrable_sq

/-- Integrability of the load term suffices for a finite classical energy. -/
theorem integrable_classicalEnergy
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u Ω) (hfu : IntegrableOn (fun x ↦ f x * u x) Ω) :
    IntegrableOn
      (fun x ↦ (1 / 2 : ℝ) * (∑ i, ((∂[i] u) x) ^ 2) - f x * u x) Ω :=
  ((integrable_sum_sq_partialDeriv hΩ hb hu).const_mul _).sub hfu

/-- For classical closure data, finiteness of the energy density is exactly
integrability of the load term. This excludes totalized nonintegrable integrals. -/
theorem integrable_classicalEnergy_iff
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u Ω) :
    IntegrableOn
      (fun x ↦ (1 / 2 : ℝ) * (∑ i, ((∂[i] u) x) ^ 2) - f x * u x) Ω ↔
      IntegrableOn (fun x ↦ f x * u x) Ω := by
  constructor
  · intro h
    exact (((integrable_sum_sq_partialDeriv hΩ hb hu).const_mul (1 / 2 : ℝ)).sub h).congr
      (Filter.Eventually.of_forall fun x ↦ by dsimp; ring)
  · exact integrable_classicalEnergy hΩ hb hu

/-- The exact affine expansion of the classical energy. The load only needs to
be integrable after multiplication by the two functions in this variation. -/
theorem classicalEnergy_add_mul
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u Ω) (hv : ContDiffUpToBoundary 1 v Ω)
    (hfu : IntegrableOn (fun x ↦ f x * u x) Ω)
    (hfv : IntegrableOn (fun x ↦ f x * v x) Ω) (t : ℝ) :
    classicalEnergy Ω f (fun x ↦ u x + t * v x) =
      classicalEnergy Ω f u +
        t * (∫ x in Ω, (∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x) +
        (t ^ 2 / 2) * (∫ x in Ω, ∑ i, ((∂[i] v) x) ^ 2) := by
  have hpair : IntegrableOn
      (fun x ↦ (∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x) Ω :=
    (integrable_finsetSum _ fun i _ ↦ integrable_partialDeriv_mul hΩ hb hu hv i).sub hfv
  have heq : classicalEnergy Ω f (fun x ↦ u x + t * v x) =
      ∫ x in Ω, ((1 / 2 : ℝ) * (∑ i, ((∂[i] u) x) ^ 2) - f x * u x) +
        t * ((∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x) +
        (t ^ 2 / 2) * (∑ i, ((∂[i] v) x) ^ 2) := by
    apply setIntegral_congr_fun hΩ.measurableSet
    intro x hx
    have hux := (hu.contDiffOn.contDiffAt (hΩ.mem_nhds hx)).differentiableAt
      (by norm_num)
    have hvx := (hv.contDiffOn.contDiffAt (hΩ.mem_nhds hx)).differentiableAt
      (by norm_num)
    have hdt (i : Fin n) :
        (∂[i] (fun y ↦ t * v y)) x = t * (∂[i] v) x :=
      PDE.partialDeriv_const_smul t
    simp only [PDE.partialDeriv_add hux (hvx.const_mul t), hdt]
    have hs : (∑ i : Fin n, ((∂[i] u) x + t * (∂[i] v) x) ^ 2) =
        (∑ i, ((∂[i] u) x) ^ 2) +
          2 * t * (∑ i, (∂[i] u) x * (∂[i] v) x) +
          t ^ 2 * (∑ i, ((∂[i] v) x) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hs]
    ring
  have hsum : IntegrableOn (fun x ↦
      ((1 / 2 : ℝ) * (∑ i, ((∂[i] u) x) ^ 2) - f x * u x) +
        t * ((∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x)) Ω :=
    (integrable_classicalEnergy hΩ hb hu hfu).add (hpair.const_mul t)
  rw [heq, integral_add hsum
    ((integrable_sum_sq_partialDeriv hΩ hb hv).const_mul (t ^ 2 / 2)),
    integral_add (integrable_classicalEnergy hΩ hb hu hfu) (hpair.const_mul t),
    integral_const_mul, integral_const_mul]
  rfl

/-- The first derivative of the integral energy along a classical
variation, computed from its exact quadratic expansion. -/
theorem hasDerivAt_classicalEnergy_add_mul
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffUpToBoundary 1 u Ω) (hv : ContDiffUpToBoundary 1 v Ω)
    (hfu : IntegrableOn (fun x ↦ f x * u x) Ω)
    (hfv : IntegrableOn (fun x ↦ f x * v x) Ω) :
    HasDerivAt (fun t ↦ classicalEnergy Ω f (fun x ↦ u x + t * v x))
      (∫ x in Ω, (∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x) 0 := by
  have heq : (fun t ↦ classicalEnergy Ω f (fun x ↦ u x + t * v x)) =
      (fun t ↦ classicalEnergy Ω f u +
        t * (∫ x in Ω, (∑ i, (∂[i] u) x * (∂[i] v) x) - f x * v x) +
        (t ^ 2 / 2) * (∫ x in Ω, ∑ i, ((∂[i] v) x) ^ 2)) :=
    funext (classicalEnergy_add_mul hΩ hb hu hv hfu hfv)
  rw [heq]
  cas

end PoissonEquation
