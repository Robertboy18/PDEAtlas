/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Analysis.Evolution.Compactness.Lp.TimeTesting
import PDE.Analysis.Evolution.Compactness.WeakLimitTesting
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.Completion
import PDE.Analysis.Evolution.LionsMagenes.EndpointRegularity.InitialTrace
import PDE.Analysis.Evolution.LionsMagenes.Regularity.OpenInterval

/-!
# From the almost-everywhere weak equation to integrated time tests

The continuous pivot representative and its integrated derivative yield
the endpoint integration-by-parts identity. An almost-everywhere equation then
implies the integrated formulation used by the Galerkin uniqueness theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1 (definition of a weak solution) and §5.9.2, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The AE equation and the continuous initial trace imply the integrated
weak formulation, without a stronger assumption on the time test class. -/
theorem IsGelfandIntegratedWeakSolution.of_ae_equation
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ} (hab : a < b)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))} {uInit : H}
    (E : ContinuousPivotEvolutionOn T (fun t ↦ u t) (fun t ↦ g t) a b)
    (htrace : E.representative a = uInit)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)))
    (MB : ℝ) (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), g t + B t (u t) = ell t) :
    IsGelfandIntegratedWeakSolution T B ell u uInit := by
  have hform := fun v τ ↦ integrable_timeDependentBilinearTimeTest B v τ hB MB hbound u
  refine ⟨hab, fun v τ ↦ hform v τ.toLp, fun v τ ↦ integrable_dualTimeTest v τ.toLp ell, ?_⟩
  intro v τ
  have hEae : E.representative =ᵐ[volume.restrict (Ioc a b)] fun t ↦ T.inclusion (u t) :=
    E.ae_eq_inclusion.filter_mono (ae_mono (volume.restrict_mono_set (by
      rw [uIcc_of_le hab.le]
      exact Ioc_subset_Icc_self)))
  have hτae : (τ.toLp : ℝ → ℝ) =ᵐ[volume.restrict (Ioc a b)] τ.toFun :=
    τ.memLp.coeFn_toLp
  have hdτae : (τ.derivToLp : ℝ → ℝ) =ᵐ[volume.restrict (Ioc a b)] τ.derivFun :=
    τ.derivMemLp.coeFn_toLp
  have hleft : (∫ t in Ioc a b, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivToLp t) =
      ∫ t in Ioc a b, inner ℝ (E.representative t) (T.inclusion v) * τ.derivFun t := by
    apply integral_congr_ae
    filter_upwards [hEae, hdτae] with t ht hdt
    rw [ht, hdt]
  have hright : (∫ t in Ioc a b, g t v * τ.toLp t) =
      ∫ t in Ioc a b, g t v * τ.toFun t := by
    apply integral_congr_ae
    filter_upwards [hτae] with t ht
    rw [ht]
  have hp := E.timeTest_boundary_identity hab.le v τ
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le,
    ← hleft, ← hright, htrace] at hp
  have heqint : (∫ t in Ioc a b, g t v * τ.toLp t) +
      (∫ t in Ioc a b, B t (u t) v * τ.toLp t) = ∫ t in Ioc a b, ell t v * τ.toLp t := by
    rw [← integral_add (integrable_dualTimeTest v τ.toLp g) (hform v τ.toLp)]
    apply integral_congr_ae
    filter_upwards [heq] with t ht
    have htv := congrArg (fun L : StrongDual ℝ V ↦ L v) ht
    simp only [add_apply] at htv
    change g t v * τ.toLp t + B t (u t) v * τ.toLp t = ell t v * τ.toLp t
    rw [← add_mul, htv]
  linarith

/-- A weak solution in the sense of Evans §7.1.1 (weak derivative, a.e. equation and
continuous initial trace) satisfies the integrated equation for all time tests. The energy
identity comes from the Lions–Magenes theorem. -/
theorem HasGelfandWeakTimeDerivativeOn.integrated_solution_of_ae_equation
    [CompleteSpace V] [CompleteSpace H]
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {T : GelfandTriple (V := V) (H := H)} {a b : ℝ} (hab : a < b)
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    {u : Lp V 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (hg : HasGelfandWeakTimeDerivativeOn T u g)
    {w : ℝ → H} (hw : ContinuousOn w (Icc a b))
    (hwae : w =ᵐ[volume.restrict (Ioc a b)] fun t ↦ T.inclusion (u t))
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)))
    (MB : ℝ) (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), g t + B t (u t) = ell t) :
    IsGelfandIntegratedWeakSolution T B ell u (w a) := by
  obtain ⟨Eopen⟩ := hg.hasWeakTimeDerivativeOn.nonempty_continuousPivotEvolutionOnOpen hab
  obtain ⟨E⟩ := Eopen.toContinuousPivotEvolutionOn T hab (Lp.memLp u) (Lp.memLp g)
  have hwae' : w =ᵐ[volume.restrict (Icc a b)] fun t ↦ T.inclusion (u t) := by
    rwa [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
  have hEae : E.representative =ᵐ[volume.restrict (Icc a b)] w := by
    have hE := E.ae_eq_inclusion
    rw [uIcc_of_le hab.le] at hE
    exact hE.trans hwae'.symm
  have hEq := Measure.eqOn_Icc_of_ae_eq volume hab.ne hEae
    (by simpa only [uIcc_of_le hab.le] using E.continuousOn) hw
  exact IsGelfandIntegratedWeakSolution.of_ae_equation hab E
    (hEq ⟨le_rfl, hab.le⟩) hB MB hbound heq

end PDE.Analysis.Evolution
