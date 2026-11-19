/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# From the weak divergence equation to the classical equation

Once a weak solution has a `C²` representative, integration by parts identifies its
classical flux equation. The coefficients need locally `C¹` representatives and the
forcing needs a continuous representative. Continuity then turns the almost-everywhere
identity into an equality at every interior point.

This step concerns the equation itself. It needs neither ellipticity nor a boundary
condition, and the coefficient matrix need not be symmetric.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A classical representative of an interior weak divergence-form solution satisfies
the pointwise flux equation when the coefficients are locally `C¹` and the forcing has
a continuous representative. There is no zero-trace, ellipticity, or symmetry assumption. -/
theorem IsInteriorWeakDivergenceSolution.neg_sum_partialDeriv_flux_eq_of_representatives
    {A : Fin n → Fin n → DerivLp n ∞ Ω} {F : DerivLp n 2 Ω}
    {u : H¹(Ω)} (hu : IsInteriorWeakDivergenceSolution A F u)
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (hA : ∀ i j, (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] a i j)
    (ha : ∀ i j x, x ∈ Ω → ContDiffAt ℝ 1 (a i j) x)
    {f g : ℝ^n → ℝ}
    (hrep : (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f)
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (hforce : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g)
    (hg : ContinuousOn g Ω) :
    ∀ x ∈ Ω, -(∑ i : Fin n, ∑ j : Fin n,
      (∂[i] (fun y ↦ a i j y * (∂[j] f) y)) x) = g x := by
  let du (j : Fin n) : DerivLp n 2 Ω :=
    wkpCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω)
      (singleDerivIndex n j) u
  let flux (i j : Fin n) (x : ℝ^n) := a i j x * (∂[j] f) x
  have hdu (j : Fin n) : (du j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] ∂[j] f := by
    have hw : HasWeakDerivativeOn (n := n) Ω [j]
        (wkpBaseCoordinateCLM u) (du j) := by
      simpa [du, wkpBaseCoordinateCLM, wkpCoordinateCLM, firstDerivIndex_one] using
        u.property.hasWeakDerivativeOn_first (by norm_num) j
    exact ((hasWeakDerivativeOn_congr_ae hrep Filter.EventuallyEq.rfl).mp hw).unique_ae
      hu.isOpen (hasWeakDerivativeOn_of_contDiffAt_one hu.isOpen
        (fun x hx ↦ (hreg x hx).of_le (by norm_num)) j)
  have hfluxreg (i j : Fin n) (x : ℝ^n) (hx : x ∈ Ω) :
      ContDiffAt ℝ 1 (flux i j) x :=
    (ha i j x hx).mul (PDE.contDiffAt_partialDeriv 1 (hreg x hx) j)
  have hfluxweak (i j : Fin n) : HasWeakDerivativeOn (n := n) Ω [i]
      (flux i j) (∂[i] (flux i j)) :=
    hasWeakDerivativeOn_of_contDiffAt_one hu.isOpen (hfluxreg i j) i
  have hcontinuous : ContinuousOn
      (fun x ↦ -(∑ i : Fin n, ∑ j : Fin n, (∂[i] (flux i j)) x)) Ω :=
    .neg (continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ x hx ↦
      (PDE.contDiffAt_partialDeriv 0 (hfluxreg i j x hx) i).continuousAt.continuousWithinAt)
  have hnil : HasWeakDerivativeOn (n := n) Ω [] g
      (fun x ↦ -(∑ i : Fin n, ∑ j : Fin n, (∂[i] (flux i j)) x)) := by
    refine ⟨hg.locallyIntegrableOn hu.isOpen.measurableSet,
      hcontinuous.locallyIntegrableOn hu.isOpen.measurableSet, ?_⟩
    intro φ hφ
    let test : TestFunctionOn n Ω := ⟨φ, hφ⟩
    have hterm (i j : Fin n) :
        ⟪multiplicationCoefficientOperator A i j (du j),
          derivCoordCLM (n := n) (Ω := Ω) i (testFunctionToH10 test)⟫_ℝ =
          -(∫ x, (∂[i] (flux i j)) x * φ.toFun x ∂domainMeasure n Ω) := by
      calc
        _ = ∫ x, flux i j x * (∂[i] φ.toFun) x ∂domainMeasure n Ω := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [multiplicationCoefficientOperator_apply_ae A i j (du j),
            derivCoordCLM_testFunction_apply_ae (n := n) (Ω := Ω) i test,
            hA i j, hdu j] with x hmul htest hAx hdux
          rw [hmul, htest, hAx, hdux]
          simp [RCLike.inner_apply, flux, test, mul_comm]
        _ = _ := by
          simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
            Nat.zero_add, pow_one, neg_one_mul] using hfluxweak i j φ hφ
    have hload : loadFunctional (n := n) (Ω := Ω) F (testFunctionToH10 test) =
        ∫ x, g x * φ.toFun x ∂domainMeasure n Ω := by
      rw [loadFunctional_apply, inner_base_testFunction_eq_integral]
      exact integral_congr_ae (hforce.mono fun x hx ↦ congrArg (· * φ.toFun x) hx)
    have hequation := hu.equation (testFunctionToH10 test)
    rw [interiorVariableCoeffForm_apply, hload] at hequation
    change (∑ i : Fin n, ∑ j : Fin n,
      ⟪multiplicationCoefficientOperator A i j (du j),
        derivCoordCLM (n := n) (Ω := Ω) i (testFunctionToH10 test)⟫_ℝ) = _ at hequation
    simp only [hterm] at hequation
    have hintegral :
        (∫ x, -(∑ i : Fin n, ∑ j : Fin n, (∂[i] (flux i j)) x) *
            φ.toFun x ∂domainMeasure n Ω) =
          ∑ i : Fin n, ∑ j : Fin n,
            -(∫ x, (∂[i] (flux i j)) x * φ.toFun x ∂domainMeasure n Ω) := by
      have hij (i j : Fin n) : Integrable
          (fun x ↦ (∂[i] (flux i j)) x * φ.toFun x) (domainMeasure n Ω) :=
        (hfluxweak i j).integrable_mul_testFunction φ hφ
      simp only [neg_mul, Finset.sum_mul, integral_neg, Finset.sum_neg_distrib]
      congr 1
      rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hij i j]
      exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hij i j
    simpa only [iteratedPartialDeriv, List.length_nil, pow_zero, one_mul] using
      hequation.symm.trans hintegral.symm
  have hsame := Measure.eqOn_open_of_ae_eq (μ := volume) (hnil.nil_ae_eq hu.isOpen)
    hu.isOpen hg hcontinuous
  exact fun x hx ↦ (hsame hx).symm

end SobolevSpace.GraphSpace
