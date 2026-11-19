/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
public import PDE.Analysis.Evolution.Core.WeakEvolution
import PDE.Analysis.Evolution.Integrated.TimeDistribution

/-!
# Classical trajectories in the integrated formulation

A pointwise differentiable weak evolution satisfies the Bochner `L²`
identity used by integrated weak solutions. The trajectory is
represented by an `Lp` class, while the initial value is retained through the
boundary term in the time-distribution identity.

## Main results

* `SatisfiesWeakEvolutionOn.integrated_initial_identity_L2`: for a test vector `v` and a time
  test `τ` vanishing at `b`,
  `-∫ ⟪u, v⟫ τ' + ∫ B(t)(u, v) τ = ∫ ℓ(t)(v) τ + ⟪u(a), v⟫ τ(a)`.
  With the test function `τ(t) v` this is the identity (33) that Evans, §7.1.2, deduces from
  (29) for the Galerkin approximations in step 3 of the proof of Theorem 3, where the boundary
  term identifies the initial value.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 3 (Existence of weak solution), step 3
  of its proof, (32)-(34), p. 379. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace SatisfiesWeakEvolutionOn

/--
A differentiable weak evolution satisfies the initial-value identity against
every endpoint time test after replacing the trajectory by an almost-everywhere
equal Bochner `L²` representative.
-/
theorem integrated_initial_identity_L2
    {a b : ℝ} (hab : a ≤ b)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u du : ℝ → V}
    (heq : SatisfiesWeakEvolutionOn B ell u du (Set.uIcc a b))
    (uLp : Lp V 2 (volume.restrict (Set.Ioc a b)))
    (huLp : (uLp : ℝ → V) =ᵐ[volume.restrict (Set.Ioc a b)] u)
    (hu : ∀ t ∈ Set.uIcc a b, HasDerivAt u (du t) t)
    (v : V) (τ : TimeTest a b)
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdτ : IntervalIntegrable τ.derivFun volume a b)
    (hBτ : IntervalIntegrable (fun t ↦ B t (u t) v * τ.toFun t) volume a b) :
    -(∫ t, inner ℝ (uLp t) v * τ.derivToLp t
        ∂(volume.restrict (Set.Ioc a b))) +
        ∫ t, B t (uLp t) v * τ.toLp t
          ∂(volume.restrict (Set.Ioc a b)) =
      (∫ t, ell t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) +
        inner ℝ (u a) v * τ.toFun a := by
  have hraw := heq.integrated_initial_identity v
    (fun t ht ↦ (hu t ht).hasDerivWithinAt)
    (fun t ht ↦ (τ.hasDerivAt t (by
      simpa only [Set.uIcc_of_le hab] using ht)).hasDerivWithinAt)
    hdu hdτ hBτ τ.final_zero
  have hτ : (τ.toLp : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioc a b)] τ.toFun :=
    τ.memLp.coeFn_toLp
  have hdτae : (τ.derivToLp : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioc a b)] τ.derivFun :=
    τ.derivMemLp.coeFn_toLp
  have htime :
      (∫ t, inner ℝ (uLp t) v * τ.derivToLp t
        ∂(volume.restrict (Set.Ioc a b))) =
      ∫ t in a..b, inner ℝ (u t) v * τ.derivFun t := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [huLp, hdτae] with t hut hdt
    rw [hut, hdt]
  have hform :
      (∫ t, B t (uLp t) v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) =
      ∫ t in a..b, B t (u t) v * τ.toFun t := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [huLp, hτ] with t hut hτt
    rw [hut, hτt]
  have hforcing :
      (∫ t, ell t v * τ.toLp t ∂(volume.restrict (Set.Ioc a b))) =
      ∫ t in a..b, ell t v * τ.toFun t := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [hτ] with t hτt
    rw [hτt]
  rw [htime, hform, hforcing]
  exact hraw

end SatisfiesWeakEvolutionOn

end PDE.Analysis.Evolution
