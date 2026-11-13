/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.SecondOrder.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.Core.EnergyIdentity
import PDE.Analysis.Evolution.Time.AbsoluteContinuity

/-!
# Energy identities for second-order systems

The energy of a second-order equation with a symmetric, time-dependent
stiffness operator. We prove the pointwise derivative,
integrated identity, initial-data form, and the elementary differential
inequality used before applying Grönwall's lemma.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 2, equations (20)-(25).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set

namespace Hyperbolic.Variational

/--
The finite-dimensional wave energy

`E(t) = 1/2 ‖p(t)‖² + 1/2 ⟪K(t)q(t),q(t)⟫`.

This is the wave energy when the mass metric is the displayed Hilbert
inner product and `K(t)` is symmetric for that metric. In a Gelfand Galerkin system,
`gelfandGalerkinOperator` has already been inverted by the pivot mass matrix
and need not be symmetric in the trial space's inherited `V` inner product.
For that system, the energy uses the pivot kinetic term
`1/2 ‖Jp‖_H²` plus the symmetric principal form `1/2 A(t)(q,q)`.

Positivity is not built into this generic definition; it is an assumption of
the subsequent estimate.
-/
def secondOrderEnergy
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : ℝ → F →L[ℝ] F) (q p : ℝ → F) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ‖p t‖ ^ 2 +
    (1 / 2 : ℝ) * inner ℝ (K t (q t)) (q t)

/--
Exact derivative of the energy for a symmetric, time-dependent stiffness.

The term `1/2 ⟪Kdot(t)q(t),q(t)⟫` is essential.  It is the abstract form of
the term with the time derivative of the coefficients in equation (22) of Evans, §7.2.2;
omitting it would silently specialize the theorem to autonomous coefficients.
-/
theorem hasDerivAt_secondOrderEnergy {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : ℝ → F →L[ℝ] F} {Kdot : F →L[ℝ] F} {q p f : ℝ → F} {t : ℝ} (hK : HasDerivAt K Kdot t)
    (hq : HasDerivAt q (p t) t) (hp : HasDerivAt p (-(K t) (q t) + f t) t)
    (hK_symmetric : ∀ x y : F, inner ℝ (K t x) y = inner ℝ x (K t y)) :
    HasDerivAt (secondOrderEnergy K q p)
      (inner ℝ (f t) (p t) + (1 / 2 : ℝ) * inner ℝ (Kdot (q t)) (q t)) t := by
  have hcoefficient : inner ℝ (-(K t) (q t) + f t) (p t) + (1 / 2 : ℝ) *
        (inner ℝ (K t (q t)) (p t) + inner ℝ (Kdot (q t) + K t (p t)) (q t)) =
      inner ℝ (f t) (p t) + (1 / 2 : ℝ) * inner ℝ (Kdot (q t)) (q t) := by
    simp only [inner_add_left, inner_neg_left]
    rw [hK_symmetric (p t) (q t), real_inner_comm (p t) (K t (q t))]
    ring
  simpa only [secondOrderEnergy, Pi.add_apply, hcoefficient] using!
    (PDE.Analysis.Evolution.hasDerivAt_half_norm_sq hp).add
      (((hK.clm_apply hq).inner ℝ hq).const_mul (1 / 2 : ℝ))

/--
Integrated nonautonomous energy identity for a second-order solution.

The stiffness curve is assumed absolutely continuous in operator norm and
`Kdot` is an explicitly supplied almost-everywhere derivative.  These are
the abstract counterparts of Evans's `C¹` coefficient hypothesis.  For
every `t ∈ [a,b]`,

`E(t)-E(a) = ∫ₐᵗ (⟪f,p⟫ + 1/2 ⟪Kdot q,q⟫)`.

The proof first establishes absolute continuity of the kinetic and
potential energies.  The latter uses the Banach-valued product rule twice:
once for `K(t)q(t)`, and once for its pairing with `q(t)`.  The exact
pointwise derivative theorem then holds almost everywhere, so the scalar
absolutely-continuous FTC yields the identity.
-/
theorem SecondOrderSolutionOn.integratedEnergyIdentity {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {K Kdot : ℝ → F →L[ℝ] F} {f : ℝ → F} {a b : ℝ} {q₀ p₀ : F}
    (U : SecondOrderSolutionOn K f a b q₀ p₀) (hab : a ≤ b)
    (hKAC : AbsolutelyContinuousOnInterval K a b)
    (hKderiv : ∀ᵐ s ∂volume.restrict (Set.Ioc a b), HasDerivAt K (Kdot s) s)
    (hK_symmetric : ∀ s ∈ Set.Icc a b, ∀ x y : F, inner ℝ (K s x) y = inner ℝ x (K s y)) :
    ∀ t ∈ Set.Icc a b,
      secondOrderEnergy K U.displacement U.velocity t -
          secondOrderEnergy K U.displacement U.velocity a =
        ∫ s in a..t, inner ℝ (f s) (U.velocity s) +
          (1 / 2 : ℝ) * inner ℝ (Kdot s (U.displacement s)) (U.displacement s) := by
  let qDual : ℝ → StrongDual ℝ F := fun s ↦ InnerProductSpace.toDualMap ℝ F (U.displacement s)
  have hqDualAC : AbsolutelyContinuousOnInterval qDual a b := by
    simpa only [qDual, Function.comp_def] using! (InnerProductSpace.toDualMap ℝ
      F).lipschitzWith.comp_absolutelyContinuousOnInterval U.displacementAbsolutelyContinuous
  have hEAC : AbsolutelyContinuousOnInterval (secondOrderEnergy K U.displacement U.velocity) a b :=
    (((PDE.Analysis.Evolution.absolutelyContinuousOnInterval_norm_sq
      U.velocityAbsolutelyContinuous).const_mul (1 / 2 : ℝ)).add
      (((PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply hqDualAC
        (PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply hKAC
          U.displacementAbsolutelyContinuous)).congr fun _ _ ↦
            real_inner_comm _ _).const_mul (1 / 2 : ℝ))).congr fun _ _ ↦ rfl
  have hderiv : ∀ᵐ s ∂volume.restrict (Set.Ioc a b),
      deriv (secondOrderEnergy K U.displacement U.velocity) s = inner ℝ (f s) (U.velocity s) +
        (1 / 2 : ℝ) * inner ℝ (Kdot s (U.displacement s)) (U.displacement s) := by
    filter_upwards [hKderiv, U.displacementEquationAE, U.velocityEquationAE,
      ae_restrict_mem measurableSet_Ioc] with s hKs hqs hps hs
    exact (hasDerivAt_secondOrderEnergy hKs hqs hps
      (hK_symmetric s (Set.Ioc_subset_Icc_self hs))).deriv
  intro t ht
  rw [← (hEAC.mono (uIcc_subset_uIcc_left (by rwa [uIcc_of_le hab]))).integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae_restrict ?_
  rw [uIoc_of_le ht.1]
  exact ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2) hderiv

/--
Initial-data form of `integratedEnergyIdentity`.

This is the display used in the Galerkin estimate: the initial energy is
written directly with the prescribed displacement `q₀` and velocity `p₀`,
rather than with the trajectory evaluated at `a`.
-/
theorem SecondOrderSolutionOn.energy_eq_initial_add_integral {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {K Kdot : ℝ → F →L[ℝ] F} {f : ℝ → F} {a b : ℝ} {q₀ p₀ : F}
    (U : SecondOrderSolutionOn K f a b q₀ p₀) (hab : a ≤ b)
    (hKAC : AbsolutelyContinuousOnInterval K a b)
    (hKderiv : ∀ᵐ s ∂volume.restrict (Set.Ioc a b), HasDerivAt K (Kdot s) s)
    (hK_symmetric : ∀ s ∈ Set.Icc a b, ∀ x y : F, inner ℝ (K s x) y = inner ℝ x (K s y)) :
    ∀ t ∈ Set.Icc a b,
      secondOrderEnergy K U.displacement U.velocity t =
        (1 / 2 : ℝ) * ‖p₀‖ ^ 2 + (1 / 2 : ℝ) * inner ℝ (K a q₀) q₀ +
          ∫ s in a..t, inner ℝ (f s) (U.velocity s) +
            (1 / 2 : ℝ) * inner ℝ (Kdot s (U.displacement s)) (U.displacement s) := by
  intro t ht
  have h := U.integratedEnergyIdentity hab hKAC hKderiv hK_symmetric t ht
  simp only [secondOrderEnergy, U.initialDisplacement, U.initialVelocity] at h ⊢
  linarith

/--
The elementary differential inequality behind the Galerkin energy estimate.

If the stiffness energy is nonnegative and its time derivative is bounded by
`C` times the stiffness energy, then Young's inequality gives

`E' ≤ (1+C)E + 1/2 ‖f‖²`.

With the exact derivative above, this is the pointwise form of inequality (25)
of Evans, §7.2.2, to which Grönwall's inequality is then applied. Its hypotheses expose
precisely where ellipticity and the coefficient-time regularity enter Evans's proof.
-/
theorem secondOrderEnergyDerivative_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K Kdot : F →L[ℝ] F) (q p f : F) (C : ℝ) (hC : 0 ≤ C) (hK_nonnegative : 0 ≤ inner ℝ (K q) q)
    (hKdot_bound : inner ℝ (Kdot q) q ≤ C * inner ℝ (K q) q) :
    inner ℝ f p + (1 / 2 : ℝ) * inner ℝ (Kdot q) q ≤ (1 + C) *
      ((1 / 2 : ℝ) * ‖p‖ ^ 2 + (1 / 2 : ℝ) * inner ℝ (K q) q) + (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  nlinarith [real_inner_le_norm f p, sq_nonneg (‖f‖ - ‖p‖), mul_nonneg hC hK_nonnegative,
    sq_nonneg ‖p‖]

end Hyperbolic.Variational
