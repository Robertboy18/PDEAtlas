/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Regularity
public import PDE.Hyperbolic.HamiltonJacobi.Weak.InitialValue
import PDE.Analysis.MeasureTheory.SpaceTime
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Semiconcavity
import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# The Hamilton–Jacobi potential of an Oleinik weak solution

The potential is constructed from the weak initial conservation
identity. Its weak partials and Lipschitz regularity give the Hamilton–Jacobi
equation almost everywhere. Oleinik's slope bound gives spatial semiconcavity
at every positive time. The initial primitive supplies the initial
value required by the Hamilton–Jacobi uniqueness theorem.

In the notation of Evans, §3.4.2, the potential solves the Hamilton–Jacobi problem (26) with
the primitive `h` of (23) as initial value, and its spatial derivative is `u`. Evans obtains
this potential from the Hopf–Lax formula (24); we construct it from `u`. It is a weak solution
in the sense of §3.3.3(b), the class of the uniqueness Theorem 7 there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.3(b), definition of weak solution, conditions
  (a)-(c), and Theorem 7; §3.4.2, equations (23)-(26).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.ConservationLaw

/-- Every bounded weak initial solution with Oleinik's AE slope bound has a
semiconcave Hamilton–Jacobi potential. In particular, the equation,
initial values, and semiconcavity of the potential are conclusions. -/
theorem IsWeakInitialValueSolution.exists_hamiltonJacobiPotential {F g : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution F g u) (huBdd : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hF : Continuous F) {C : ℝ} (hC : 0 ≤ C)
    (hslope : ∀ᵐ t ∂volume, 0 < t → ∀ᵐ z ∂volume, 0 < z → ∀ᵐ x ∂volume,
      u !₂[t, x + z] - u !₂[t, x] ≤ C * (1 + t⁻¹) * z) :
    ∃ V : ℝ^2 → ℝ, HamiltonJacobi.Weak.IsInitialSolution (fun r : ℝ^1 ↦ F (r 0))
      (fun x : ℝ^1 ↦ ∫ y in 0..x 0, g y) (fun p : ℝ^1 × ℝ ↦ V (joinSpaceTime p)) ∧
      SobolevSpace.HasWeakDerivativeOn forwardHalfSpace [1] V u := by
  obtain ⟨V, L, _B, hV, ht, hx, hzero, _hmod⟩ := hu.exists_lipschitzConservativePotential huBdd hF
  have hU := forwardHalfSpace.isOpen.measurableSet
  have hxpos : SobolevSpace.HasWeakDerivativeOn forwardHalfSpace [1] V u :=
    (SobolevSpace.HasWeakDerivativeOn.mono hU (subset_univ _) hx).congr_ae (.refl _ _) <| by
      filter_upwards [ae_restrict_mem hU] with p hp using ite_eq_left hp
  have htpos : SobolevSpace.HasWeakDerivativeOn forwardHalfSpace [0] V (fun p ↦ -F (u p)) :=
    (SobolevSpace.HasWeakDerivativeOn.mono hU (subset_univ _) ht).congr_ae (.refl _ _) <| by
      filter_upwards [ae_restrict_mem hU] with p hp
      simp only [Set.indicator_of_mem hp, Function.comp_apply]
  have hpartial (i : Fin 2) (r : ℝ^2 → ℝ)
      (hr : SobolevSpace.HasWeakDerivativeOn forwardHalfSpace [i] V r) :
      ∀ᵐ p ∂volume.restrict forwardHalfSpace, (∂[i] V) p = r p := by
    have hc := SobolevSpace.HasWeakDerivativeOn.mono hU (subset_univ _)
      (SobolevSpace.GraphSpace.LipschitzWith.hasWeakDerivativeOn_lipschitzWeakCoord hV i)
    filter_upwards [hc.unique_ae forwardHalfSpace.isOpen hr,
      ae_restrict_of_ae (hV.ae_differentiableAt (μ := volume))] with p he hp
    simpa only [SobolevSpace.GraphSpace.lipschitzWeakCoord, hp.lineDeriv_eq_fderiv,
      partialDeriv] using he
  have hpoint : ∀ᵐ p ∂volume, 0 < p 0 →
      DifferentiableAt ℝ V p ∧ (∂[0] V) p = -F (u p) ∧ (∂[1] V) p = u p :=
    (ae_restrict_iff' hU).mp <| by
      filter_upwards [ae_restrict_of_ae (hV.ae_differentiableAt (μ := volume)),
        hpartial 0 _ htpos, hpartial 1 _ hxpos] with p hp hpt hpx using ⟨hp, hpt, hpx⟩
  have hswap : MeasurePreserving (Prod.swap : ℝ^1 × ℝ → ℝ × ℝ^1) volume volume := by
    rw [Measure.volume_eq_prod (ℝ^1) ℝ, Measure.volume_eq_prod ℝ (ℝ^1)]
    exact Measure.measurePreserving_swap
  have hjoin : MeasurePreserving (joinSpaceTime (n := 1)) volume volume :=
    (MeasurePreserving.symm (timeSpaceContinuousLinearEquiv 1).toHomeomorph.toMeasurableEquiv
      PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv).comp hswap
  have hpair : ∀ᵐ p : ℝ^1 × ℝ ∂volume, 0 < p.2 → DifferentiableAt ℝ V (joinSpaceTime p) ∧
      (∂[0] V) (joinSpaceTime p) = -F (u (joinSpaceTime p)) ∧
      (∂[1] V) (joinSpaceTime p) = u (joinSpaceTime p) := by
    simpa only [joinSpaceTime_apply_zero] using hjoin.quasiMeasurePreserving.ae hpoint
  have hcons (t : ℝ) (x : ℝ^1) : timeSpaceCons t x = (!₂[t, x 0] : ℝ^2) := by
    ext i
    fin_cases i
    exacts [timeSpaceCons_zero t x, timeSpaceCons_succ t x 0]
  refine ⟨V, ⟨?_, ?_, ?_, ?_⟩, hxpos⟩
  · exact ⟨_, (hV.comp
      (spaceTimeContinuousLinearEquiv 1).symm.toContinuousLinearMap.lipschitzWith).lipschitzOnWith⟩
  · intro x
    simpa only [joinSpaceTime, hcons] using hzero (x 0)
  · apply (ae_restrict_iff' HamiltonJacobi.isOpen_positiveTimeDomain.measurableSet).mpr
    filter_upwards [hpair] with p hp htpos
    obtain ⟨hd, hdt, hdx⟩ := hp htpos
    change fderiv ℝ (fun q : ℝ^1 × ℝ ↦ V (joinSpaceTime q)) p (0, 1) +
      F (∇ (fun x ↦ V (joinSpaceTime (x, p.2))) p.1 0) = 0
    rw [gradient_apply_eq_partialDeriv]
    change fderiv ℝ (fun q : ℝ^1 × ℝ ↦ V (joinSpaceTime q)) (p.1, p.2) (0, 1) +
      F ((∂[0] (fun x ↦ V (timeSpaceCons p.2 x))) p.1) = 0
    rw [fderiv_joinSpaceTime_time V p.1 p.2 hd, partialDeriv_timeSpaceCons_spatial 0 V p.2 p.1 hd]
    change (∂[0] V) (joinSpaceTime p) + F ((∂[1] V) (joinSpaceTime p)) = 0
    rw [hdt, hdx, neg_add_cancel]
  · refine ⟨C + 1, by positivity, fun x z t htpos ↦ ?_⟩
    have hz : ‖z‖ ^ 2 = (z 0) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_one]
    simp only [joinSpaceTime, hcons, PiLp.add_apply, PiLp.sub_apply]
    refine (secondDifference_le_of_lipschitz_weakDerivative_oleinik hV hxpos hslope
      (x 0) (z 0) t htpos).trans ?_
    rw [hz]
    gcongr
    linarith

end PDE.Hyperbolic.ConservationLaw
