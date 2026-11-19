/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.EnergyIdentity
public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
import PDE.Analysis.Evolution.Core.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Affine Hilbert-space evolution under a quadratic form bound

A one-sided bound `2 ⟪A(t)v, v⟫ ≤ C ‖v‖²` controls the energy of an affine
Carathéodory trajectory with L² forcing:
`‖u(t)‖² ≤ (‖u₀‖² + ∫ₐᵇ ‖f‖²) e^{(C+1)(t-a)}`. The bound does not depend on the
operator norm of `A(t)`.

Picard existence then produces a trajectory with this estimate from bounded measurable
operator coefficients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Energy estimate for an affine Carathéodory trajectory: if
`2 ⟪A(t) v, v⟫ ≤ C ‖v‖²` with `C ≥ 0` and `f ∈ L²`, then
`‖u(t)‖² ≤ (‖u₀‖² + ∫ₐᵇ ‖f‖²) e^{(C+1)(t-a)}`. -/
theorem AffineCaratheodorySolutionOn.norm_sq_le_mul_exp_of_quadratic_bound
    {a b : ℝ} (hab : a ≤ b) {A : ℝ → H →L[ℝ] H} {f : ℝ → H} {u₀ : H}
    (U : AffineCaratheodorySolutionOn A f a b u₀)
    (hf : MemLp f 2 (volume.restrict (Icc a b)))
    {C : ℝ} (hC : 0 ≤ C)
    (hform : ∀ t ∈ Icc a b, ∀ v : H, 2 * ⟪A t v, v⟫_ℝ ≤ C * ‖v‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖U.trajectory t‖ ^ 2 ≤
        (‖u₀‖ ^ 2 + ∫ s in a..b, ‖f s‖ ^ 2) * Real.exp ((C + 1) * (t - a)) := by
  let q : ℝ → ℝ := fun t ↦ ‖U.trajectory t‖ ^ 2
  have hqAC : AbsolutelyContinuousOnInterval q a b :=
    absolutelyContinuousOnInterval_norm_sq U.absolutely_continuous
  have hfsq : IntegrableOn (fun t ↦ ‖f t‖ ^ 2) (Icc a b) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hfsqInt : IntervalIntegrable (fun t ↦ ‖f t‖ ^ 2) volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hfsq
  have hderiv : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv q t ≤ (C + 1) * q t + ‖f t‖ ^ 2 := by
    have heq := U.equation_ae
    rw [restrict_Ioc_eq_restrict_Icc] at heq
    filter_upwards [heq, ae_restrict_mem measurableSet_Icc] with t ht htmem
    have hqt : deriv q t =
        2 * ⟪U.trajectory t, A t (U.trajectory t) + f t⟫_ℝ :=
      ht.norm_sq.deriv
    rw [hqt, inner_add_right]
    have hprincipal := hform t htmem (U.trajectory t)
    rw [real_inner_comm (U.trajectory t) (A t (U.trajectory t))] at hprincipal
    have hforcing := real_inner_le_norm (U.trajectory t) (f t)
    dsimp only [q]
    nlinarith [sq_nonneg (‖U.trajectory t‖ - ‖f t‖)]
  have hderivIoc : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv q t ≤ (C + 1) * q t + ‖f t‖ ^ 2 := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hderiv
  have hbound := le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le
    hab hqAC hfsqInt
    (Filter.Eventually.of_forall fun t ↦ sq_nonneg ‖f t‖)
    (by positivity : 0 ≤ C + 1) hderivIoc
  simpa only [q, U.initial_value] using hbound

/-- Bounded measurable affine coefficients and L² forcing construct a trajectory satisfying
the quadratic-form energy estimate. -/
theorem exists_affine_cauchy_with_quadratic_energy_bound [CompleteSpace H]
    {a b : ℝ} (hab : a ≤ b) (A : ℝ → H →L[ℝ] H) (f : ℝ → H)
    (hA : AEStronglyMeasurable A (volume.restrict (Icc a b)))
    (hf : MemLp f 2 (volume.restrict (Icc a b)))
    (MA : NNReal) (hAbound : ∀ t ∈ Icc a b, ‖A t‖ ≤ MA)
    {C : ℝ} (hC : 0 ≤ C)
    (hform : ∀ t ∈ Icc a b, ∀ v : H, 2 * ⟪A t v, v⟫_ℝ ≤ C * ‖v‖ ^ 2)
    (u₀ : H) :
    ∃ U : AffineCaratheodorySolutionOn A f a b u₀,
      ∀ t ∈ Icc a b,
        ‖U.trajectory t‖ ^ 2 ≤
          (‖u₀‖ ^ 2 + ∫ s in a..b, ‖f s‖ ^ 2) * Real.exp ((C + 1) * (t - a)) := by
  have hfInt : IntegrableOn f (Icc a b) volume := hf.integrable (by norm_num)
  obtain ⟨U⟩ := AffineCaratheodorySolutionOn.exists hab A f hA hfInt MA hAbound u₀
  exact ⟨U, U.norm_sq_le_mul_exp_of_quadratic_bound hab hf hC hform⟩

end PDE.Analysis.Evolution
