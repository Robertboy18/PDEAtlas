/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import PDE.Analysis.Evolution.Integrated.WeakEquation
public import PDE.Parabolic.Heat.Variational.MeasurableBounds

/-!
# Uniqueness in the original parabolic weak-solution class

A competitor is given only by its energy-space L² class, dual weak
derivative, almost-everywhere equation, and continuous L² representative with the
prescribed initial trace. Lions-Magenes supplies the integrated identity, so
competitors need no energy estimate or stronger time-test hypothesis.

The conclusion identifies the state and derivative classes, and every time slice
of the continuous representatives. This is Evans's §7.1.2, Theorem 4, for weak solutions
in the sense of his definition in §7.1.1: the competitor satisfies (i) for each test
function at almost every time, and (ii) through its continuous representative.

Evans proves uniqueness by testing the equation for the difference with itself, (36), and
applying Gronwall's inequality. We turn the competitor's equation into the integrated
equation (`HasGelfandWeakTimeDerivativeOn.integrated_solution_of_ae_equation`) and apply
the uniqueness of integrated solutions, which is part of `GardingWeakSolutionOn`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3 (More calculus), pp. 303-304; §7.1.1, the
  definition of weak solution and the remark after it, p. 374; §7.1.2, Theorem 4 (Uniqueness of weak
  solutions) and its proof, (35)-(36), p. 379.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace HeatEquation.Variational.BoundedMeasurableCoefficients

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- Every weak competitor satisfying the equation at almost every time for each spatial
test, and the initial condition, as in Evans's definition of weak solution in §7.1.1,
agrees with the constructed solution, including all continuous time slices. The
exceptional null set may depend on the spatial test. -/
theorem unique_of_ae_equation
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (hΩopen : IsOpen Ω) (hab : a < b) {alpha : ℝ}
    {f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))} {uInit : DerivLp n 2 Ω}
    (U : GardingWeakSolutionOn (h10L2GelfandTriple hΩopen) C.form
      (fun t ↦ (h10L2GelfandTriple hΩopen).pivotToDual (f t)) uInit a b
      (alpha / 2) (coerciveShift (n := n) alpha C.bound C.bound))
    {v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {g : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (hg : HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hΩopen) v g)
    {w : ℝ → DerivLp n 2 Ω} (hw : ContinuousOn w (Icc a b))
    (hwae : w =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ (h10L2GelfandTriple hΩopen).inclusion (v t))
    (htrace : w a = uInit)
    (heq : ∀ z : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t z + C.form t (v t) z = (h10L2GelfandTriple hΩopen).pivotToDual (f t) z) :
    v = U.state ∧ g = U.derivative ∧ EqOn w U.evolution.representative (Icc a b) := by
  let T := h10L2GelfandTriple hΩopen
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 Ω) := Lp.SecondCountableTopology
  have : SecondCountableTopology (H¹₀(Ω)) := inferInstance
  have hzero : (fun t ↦ (InnerProductSpace.toDual ℝ (H¹₀(Ω))).symm
      (g t + C.form t (v t) - T.pivotToDual (f t))) =ᵐ[volume.restrict (Ioc a b)] 0 := by
    apply ae_eq_zero_of_forall_inner (𝕜 := ℝ)
    intro z
    filter_upwards [heq z] with t ht
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simpa only [sub_apply, add_apply, Pi.zero_apply]
      using sub_eq_zero.mpr ht
  have heqDual : ∀ᵐ t ∂volume.restrict (Ioc a b),
      g t + C.form t (v t) = T.pivotToDual (f t) := by
    filter_upwards [hzero] with t ht
    apply sub_eq_zero.mp
    exact (LinearIsometryEquiv.map_eq_zero_iff _).mp ht
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
  have hell : (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.pivotToDual (f t) := T.pivotToDual.coeFn_compLpL f
  have heq' : ∀ᵐ t ∂volume.restrict (Ioc a b), g t + C.form t (v t) = ell t :=
    by
      filter_upwards [heqDual, hell] with t ht hlt
      exact ht.trans hlt.symm
  have hv := hg.integrated_solution_of_ae_equation hab hw hwae
    C.aestronglyMeasurable_form_apply C.formBound (Eventually.of_forall C.norm_form_le) heq'
  rw [htrace] at hv
  have hvEq : v = U.state := U.properties.unique v (hv.congr_forcing_ae hell)
  refine ⟨hvEq, ?_, ?_⟩
  · rw [hvEq] at hg
    exact hg.eq U.properties.weakDerivative
  · have hwae' : w =ᵐ[volume.restrict (Icc a b)]
        fun t ↦ T.inclusion (U.state t) := by
      rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
      simpa only [hvEq] using hwae
    have hEae := U.evolution.ae_eq_inclusion
    rw [uIcc_of_le hab.le] at hEae
    exact Measure.eqOn_Icc_of_ae_eq volume hab.ne (hwae'.trans hEae.symm) hw
      (by simpa only [uIcc_of_le hab.le] using U.evolution.continuousOn)

end HeatEquation.Variational.BoundedMeasurableCoefficients
