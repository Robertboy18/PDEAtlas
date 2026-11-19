/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Integral
import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.Evolution.Core.Gronwall
import PDE.Hyperbolic.Variational.GelfandGalerkin.Basic

/-!
# Nonautonomous Galerkin wave energy with square-integrable forcing

For a Gelfand triple `V ↪ H ↪ V*`, split the spatial form as `A(t) + R(t)`.
The principal form is symmetric, uniformly coercive, and absolutely continuous in time.
The lower-order form is controlled in `V × H`; its sign is unrestricted.

Square-integrable pivot forcing supplies the energy budget directly. The resulting
exponential rate `2 + (L_R² + L_A) / c` is independent of the trial space. Absolute
continuity of the energy and the almost-everywhere Galerkin equations suffice; the
trajectory need not be twice continuously differentiable.

`gelfandWaveEnergy_le_exp_of_memLp` estimates a given trajectory. The theorem
`exists_with_energy_bound_of_memLp` constructs one for arbitrary initial values in the
finite trial space, then proves the same estimate. Constructing an infinite-dimensional
weak wave additionally requires uniformly controlled initial projections and weak limits.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 2 (the Galerkin energy estimate).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Square-integrable pivot forcing controls the nonautonomous Galerkin wave energy.
The dual force may use any almost-everywhere equal representative. The derivative
bound on the principal form is one-sided, and the lower-order estimate is in `V × H`. -/
theorem gelfandWaveEnergy_le_exp_of_memLp (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S] (A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (f : ℝ → H) {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun t ↦ gelfandGalerkinOperator T S (A t + R t))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hellPivot : ∀ᵐ t ∂volume.restrict (Ioc a b), ell t = T.pivotToDual (f t))
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Icc a b, ∀ x y : V, A t x y = A t y x) (c LR LA : ℝ) (hc : 0 < c) (hLA : 0 ≤ LA)
    (hcoercive : ∀ t ∈ Icc a b, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (hRbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x y : V, |R t x y| ≤ LR * ‖x‖ * ‖T.inclusion y‖)
    (hAdotBound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x : V, Adot t x x ≤ LA * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b, gelfandWaveEnergy T S A U.displacement U.velocity t ≤
      (gelfandWaveEnergy T S A U.displacement U.velocity a + (1 / 2 : ℝ) * ∫ s in a..b, ‖f s‖ ^ 2) *
      Real.exp ((2 + (LR ^ 2 + LA) / c) * (t - a)) := by
  let E : ℝ → ℝ := gelfandWaveEnergy T S A U.displacement U.velocity
  have hEAC : AbsolutelyContinuousOnInterval E a b :=
    absolutelyContinuousOnInterval_gelfandWaveEnergy T S A U hAAC
  have hforceInt : IntervalIntegrable (fun t ↦ (1 / 2 : ℝ) * ‖f t‖ ^ 2)
      volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
    exact ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).const_mul (1 / 2 : ℝ)
  have hprojected := projectedEquationAE T S (fun t ↦ A t + R t) ell U
  have hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv E t ≤ (2 + (LR ^ 2 + LA) / c) * E t + (1 / 2 : ℝ) * ‖f t‖ ^ 2 := by
    filter_upwards [hAderiv, U.displacementEquationAE, hprojected, hellPivot,
      hRbound, hAdotBound, ae_restrict_mem measurableSet_Ioc] with t hAt hqt hpt helt hRt hAdott ht
    have htIcc : t ∈ Icc a b := Ioc_subset_Icc_self ht
    have hEt : HasDerivAt E
        (ell t (U.velocity t : V) - R t (U.displacement t : V) (U.velocity t : V) +
          (1 / 2 : ℝ) * Adot t (U.displacement t : V) (U.displacement t : V)) t :=
      hasDerivAt_gelfandWaveEnergy T S A R ell hAt hqt hpt.1 hpt.2 (hAsymm t htIcc)
    rw [hEt.deriv, helt]
    exact gelfandWaveEnergyWork_le T (A t) (R t) (Adot t)
      (U.displacement t : V) (U.velocity t : V) (f t) c LR LA hc hLA
      (hcoercive t htIcc _) (hRt _ _) (hAdott _)
  have hbound := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le hab hEAC hforceInt
    (Filter.Eventually.of_forall fun t ↦
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg ‖f t‖))
    (show 0 ≤ 2 + (LR ^ 2 + LA) / c by positivity) hderiv
  simpa only [E, intervalIntegral.integral_const_mul] using hbound

/-- Bounded measurable nonautonomous forms and `L²` pivot forcing construct a finite
Galerkin trajectory satisfying the uniform energy estimate. Both initial values are arbitrary
elements of the selected trial space. The estimate depends on the initial energy and forcing, not on
the trial dimension. -/
theorem exists_with_energy_bound_of_memLp (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S] (A R Adot : ℝ → V →L[ℝ] StrongDual ℝ V) (f : ℝ → H)
    {a b : ℝ} (hab : a ≤ b) (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hBmeas : AEStronglyMeasurable (fun t ↦ A t + R t) (volume.restrict (Ioc a b))) (MB : NNReal)
    (hBbound : ∀ t ∈ Icc a b, ‖A t + R t‖ ≤ MB) (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Icc a b, ∀ x y : V, A t x y = A t y x) (c LR LA : ℝ) (hc : 0 < c) (hLA : 0 ≤ LA)
    (hcoercive : ∀ t ∈ Icc a b, ∀ x : V, c * ‖x‖ ^ 2 ≤ A t x x)
    (hRbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x y : V, |R t x y| ≤ LR * ‖x‖ * ‖T.inclusion y‖)
    (hAdotBound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ x : V, Adot t x x ≤ LA * ‖x‖ ^ 2) (q₀ p₀ : S) :
    ∃ U : SecondOrderSolutionOn
        (fun t ↦ gelfandGalerkinOperator T S (A t + R t))
        (gelfandGalerkinForcing T S (fun t ↦ T.pivotToDual (f t))) a b q₀ p₀,
      ∀ t ∈ Icc a b,
        gelfandWaveEnergy T S A U.displacement U.velocity t ≤
          ((1 / 2 : ℝ) * ‖T.inclusion (p₀ : V)‖ ^ 2 +
            (1 / 2 : ℝ) * A a (q₀ : V) (q₀ : V) +
            (1 / 2 : ℝ) * ∫ s in a..b, ‖f s‖ ^ 2) *
              Real.exp ((2 + (LR ^ 2 + LA) / c) * (t - a)) := by
  have hfIcc : MemLp f 2 (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hf
  have hell : IntegrableOn (fun t ↦ T.pivotToDual (f t)) (Icc a b) volume :=
    T.pivotToDual.integrable_comp (hfIcc.integrable (by norm_num))
  have hBmeasIcc : AEStronglyMeasurable (fun t ↦ A t + R t)
      (volume.restrict (Icc a b)) := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hBmeas
  obtain ⟨U⟩ := GelfandGalerkin.exists T S (fun t ↦ A t + R t)
    (fun t ↦ T.pivotToDual (f t)) hab hBmeasIcc hell MB hBbound q₀ p₀
  refine ⟨U, ?_⟩
  have hbound := gelfandWaveEnergy_le_exp_of_memLp T S A R Adot
    (fun t ↦ T.pivotToDual (f t)) f U hab hf (Filter.Eventually.of_forall fun _ ↦ rfl)
    hAAC hAderiv hAsymm c LR LA hc hLA hcoercive hRbound hAdotBound
  intro t ht
  have hinitial : gelfandWaveEnergy T S A U.displacement U.velocity a =
      (1 / 2 : ℝ) * ‖T.inclusion (p₀ : V)‖ ^ 2 +
        (1 / 2 : ℝ) * A a (q₀ : V) (q₀ : V) := by
    simp only [gelfandWaveEnergy, U.initialDisplacement, U.initialVelocity]
  simpa only [hinitial] using hbound t ht

end Hyperbolic.Variational.GelfandGalerkin
