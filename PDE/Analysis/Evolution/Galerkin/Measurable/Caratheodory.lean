/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Analysis.Evolution.Galerkin.Measurable.Approximation
public import PDE.Analysis.Evolution.ODE.Caratheodory.Affine
import PDE.Analysis.Evolution.Galerkin.Measurable.Coefficients
import PDE.Analysis.Evolution.Galerkin.Measurable.Energy

/-!
# Carathéodory construction of measurable Galerkin approximations

The affine Carathéodory solver, applied to the finite-dimensional pivot-mass
Galerkin system, gives a measurable Galerkin trajectory with the
almost-everywhere projected equation and the uniform energy estimate. We also
construct families over trial-space sequences.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 1 (construction of approximate
  solutions) and its proof. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

section GalerkinCaratheodory

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace V] [CompleteSpace H] in
/--
Carathéodory existence for the pivot-mass Galerkin system (Evans §7.1.2, Theorem 1). If
`t ↦ B(t) v` (for each `v`) and `ℓ` are almost everywhere strongly measurable on `[a, b]`, with
`‖B(t)‖ ≤ MB` and `‖ℓ(t)‖ ≤ Mell` there, then `u' = -M_S⁻¹ A_S(t) u + M_S⁻¹ r_S(t)` has a
Carathéodory solution on `[a, b]` with `u(a) = u₀`.
-/
theorem exists_gelfandGalerkinCaratheodory
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (hell : AEStronglyMeasurable ell (volume.restrict (Set.Icc a b)))
    (MB Mell : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hell_bound : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S) :
    Nonempty
      (AffineCaratheodorySolutionOn
        (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
        (gelfandGalerkinForcing T S ell) a b u₀) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  let MA := gelfandGalerkinLipschitzBound T S MB
  let Mf := gelfandGalerkinLipschitzBound T S Mell
  obtain ⟨hAmeas, hfmeas⟩ :=
    aestronglyMeasurable_gelfandGalerkin_coefficients
      T S hB hell
  have hAbound : ∀ t ∈ Set.Icc a b,
      ‖-(gelfandGalerkinOperator T S (B t))‖ ≤ MA := by
    intro t ht
    exact norm_neg_gelfandGalerkinOperator_le
      T S (B t) MB (hB_bound t ht)
  have hfbound : ∀ t ∈ Set.Icc a b,
      ‖gelfandGalerkinForcing T S ell t‖ ≤ Mf := by
    intro t ht
    exact norm_gelfandGalerkinForcing_le
      T S (ell t) Mell (hell_bound t ht)
  have hfInt :
      IntegrableOn (gelfandGalerkinForcing T S ell)
        (Set.Icc a b) volume := by
    apply IntegrableOn.of_bound measure_Icc_lt_top hfmeas (Mf : ℝ)
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun t ht ↦ hfbound t ht
  exact AffineCaratheodorySolutionOn.exists hab
    (fun t ↦ -(gelfandGalerkinOperator T S (B t)))
    (gelfandGalerkinForcing T S ell)
    hAmeas hfInt MA hAbound u₀

omit [CompleteSpace V] [CompleteSpace H] in
/--
Existence of an almost-everywhere Galerkin approximation. Under the hypotheses of
`exists_gelfandGalerkinCaratheodory` and uniform coercivity `C ‖w‖² ≤ B(t)(w, w)` with
`C > 0`, the Carathéodory solution, with its `L²` derivative, the projected equation almost
everywhere and the integrated coercive estimate, is an `AEGelfandGalerkinApproximation` with
constants `C` and `Mell`.
-/
theorem exists_aeGelfandGalerkinApproximation
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (hell : AEStronglyMeasurable ell (volume.restrict (Set.Icc a b)))
    (MB Mell : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hell_bound : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (u₀ : S) :
    Nonempty
      (AEGelfandGalerkinApproximation
        T S B ell a b C (Mell : ℝ) u₀) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  obtain ⟨U⟩ :=
    exists_gelfandGalerkinCaratheodory
      T S B ell hab hB hell MB Mell hB_bound hell_bound u₀
  let du : ℝ → S := fun t ↦
    gelfandGalerkinVectorField T S B ell t (U.trajectory t)
  have hderiv :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
        HasDerivAt U.trajectory (du t) t := by
    filter_upwards [U.equation_ae] with t ht
    exact ht.congr_deriv
      (neg_gelfandGalerkinOperator_add_forcing
        T S B ell t (U.trajectory t))
  let MA := gelfandGalerkinLipschitzBound T S MB
  let Mf := gelfandGalerkinLipschitzBound T S Mell
  obtain ⟨hAmeas, hfmeas⟩ :=
    aestronglyMeasurable_gelfandGalerkin_coefficients T S hB hell
  have hAbound : ∀ t ∈ Set.Icc a b,
      ‖-(gelfandGalerkinOperator T S (B t))‖ ≤ MA := by
    intro t ht
    exact norm_neg_gelfandGalerkinOperator_le
      T S (B t) MB (hB_bound t ht)
  have hfbound : ∀ t ∈ Set.Icc a b,
      ‖gelfandGalerkinForcing T S ell t‖ ≤ Mf := by
    intro t ht
    exact norm_gelfandGalerkinForcing_le
      T S (ell t) Mell (hell_bound t ht)
  have hduMem :
      MemLp du 2 (volume.restrict (Set.Ioc a b)) := by
    have hrhs := U.rhsMemLp hab hAmeas hfmeas MA Mf hAbound hfbound
    apply (memLp_congr_ae ?_).1 hrhs
    filter_upwards with t
    exact neg_gelfandGalerkinOperator_add_forcing
      T S B ell t (U.trajectory t)
  have hequation :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          B t (U.trajectory t : V) (v : V) = ell t (v : V) := by
    filter_upwards with t
    exact gelfandGalerkinVectorField_equation
      T S B ell t (U.trajectory t)
  have henergy :=
    gelfandGalerkin_integrated_energy_bound_ae
      T S B ell U.trajectory du hab hC Mell.2
      U.absolutely_continuous hderiv hduMem hcoercive hell_bound hequation
  refine ⟨{
    trajectory := U.trajectory
    coefficientDerivative := du
    initial := U.initial_value
    trajectory_ac := U.absolutely_continuous
    derivative_ae := hderiv
    derivative_memLp := hduMem
    equation_ae := hequation
    integrated_energy_bound := ?_
  }⟩
  intro t ht
  simpa only [U.initial_value] using! henergy t ht

omit [CompleteSpace V] [CompleteSpace H] in
/-- Simultaneous measurable-time Galerkin construction over any sequence of
finite-dimensional trial spaces.  The coercivity and forcing constants are
shared across dimensions; finite-dimensional mass conditioning affects only
the internal ODE construction. -/
theorem AEGelfandGalerkinApproximation.exists_sequence
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 < C)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Set.Icc a b)))
    (hell : AEStronglyMeasurable ell (volume.restrict (Set.Icc a b)))
    (MB Mell : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hell_bound : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (u₀ : ∀ n, S n) :
    Nonempty (∀ n,
      AEGelfandGalerkinApproximation
        T (S n) B ell a b C (Mell : ℝ) (u₀ n)) := by
  classical
  have hex (n : ℕ) : Nonempty
      (AEGelfandGalerkinApproximation
        T (S n) B ell a b C (Mell : ℝ) (u₀ n)) := by
    let : FiniteDimensional ℝ (S n) := hfinite n
    exact exists_aeGelfandGalerkinApproximation
      T (S n) B ell hab hC hB hell MB Mell
      hB_bound hell_bound hcoercive (u₀ n)
  exact ⟨fun n ↦ (hex n).some⟩

end GalerkinCaratheodory

end PDE.Analysis.Evolution
