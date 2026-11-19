/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Variational.GelfandGalerkin.AutonomousDifferentiation
public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Basic
import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Integral

/-!
# Energy bounds for differentiated Gelfand Galerkin systems

We apply the nonautonomous Gelfand energy estimate to the
differentiated trajectory of an autonomous Galerkin equation.  The principal
coefficient derivative vanishes, leaving forcing and lower-order work.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, step 2, equations (54)-(55).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Evans's differentiated Galerkin energy estimate, in Grönwall-ready form.

Let `D` be the differentiated Galerkin solution constructed by
`GelfandGalerkin.timeDerivative`.  For an autonomous splitting
`B = A + R`, assume the integrated work of `D` satisfies

`∫ work_D ≤ G + Λ ∫ E_D`.

Then

`E_D(t) ≤ (E_D(a) + G) exp (Λ (t-a))`.

This is the abstract content of equations (54)-(55) and the subsequent
Grönwall step in Evans, §7.2.3.  The theorem keeps the work estimate explicit
because its concrete bound depends on the coercivity and lower-order
constants of the PDE; the differentiation and energy arguments themselves
are completely general.
-/
theorem GelfandGalerkin.timeDerivative_gelfandWaveEnergy_le_exp
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A R : V →L[ℝ] StrongDual ℝ V)
    {ell ellDot : ℝ → StrongDual ℝ V}
    {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn
      (fun _ ↦ gelfandGalerkinOperator T S (A + R))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hellAC : AbsolutelyContinuousOnInterval ell a b)
    (hellDeriv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt ell (ellDot t) t)
    (hA_symmetric : ∀ x y : V, A x y = A y x)
    (Λ G : ℝ) (hΛ : 0 ≤ Λ)
    (hwork : ∀ t ∈ Set.Icc a b,
      let D :=
        GelfandGalerkin.timeDerivative
          T S (A + R) U hellAC hellDeriv
      (∫ s in a..t,
          ellDot s (D.velocity s : V) -
            R (D.displacement s : V) (D.velocity s : V)) ≤
        G + Λ * ∫ s in a..t,
          gelfandWaveEnergy T S (fun _ ↦ A)
            D.displacement D.velocity s) :
    ∀ t ∈ Set.Icc a b,
      let D :=
        GelfandGalerkin.timeDerivative
          T S (A + R) U hellAC hellDeriv
      gelfandWaveEnergy T S (fun _ ↦ A)
          D.displacement D.velocity t ≤
        (gelfandWaveEnergy T S (fun _ ↦ A)
            D.displacement D.velocity a + G) *
          Real.exp (Λ * (t - a)) := by
  let D :=
    GelfandGalerkin.timeDerivative
      T S (A + R) U hellAC hellDeriv
  have hALipschitz :
      LipschitzWith (0 : NNReal) (fun _ : ℝ ↦ A) :=
    LipschitzWith.const' A
  have hAAC :
      AbsolutelyContinuousOnInterval
        (fun _ : ℝ ↦ A) a b :=
    hALipschitz.lipschitzOnWith.absolutelyContinuousOnInterval
  have hAderiv :
      ∀ᵐ s ∂volume.restrict (Set.Ioc a b),
        HasDerivAt (fun _ : ℝ ↦ A)
          (0 : V →L[ℝ] StrongDual ℝ V) s :=
    Filter.Eventually.of_forall fun s ↦ hasDerivAt_const s A
  have hworkD : ∀ t ∈ Set.Icc a b,
      (∫ s in a..t,
          ellDot s (D.velocity s : V) -
            R (D.displacement s : V) (D.velocity s : V) +
            (1 / 2 : ℝ) *
              (0 : V →L[ℝ] StrongDual ℝ V)
                (D.displacement s : V) (D.displacement s : V)) ≤
        G + Λ * ∫ s in a..t,
          gelfandWaveEnergy T S (fun _ ↦ A)
            D.displacement D.velocity s := by
    intro t ht
    simpa only [zero_apply, map_zero, mul_zero,
      add_zero] using hwork t ht
  intro t ht
  simpa only [D] using
    GelfandGalerkin.gelfandWaveEnergy_le_exp
      T S (fun _ ↦ A) (fun _ ↦ R) ellDot D
      (ht.1.trans ht.2) hAAC hAderiv
      (fun _ _ x y ↦ hA_symmetric x y)
      Λ G hΛ hworkD t ht

end Hyperbolic.Variational
