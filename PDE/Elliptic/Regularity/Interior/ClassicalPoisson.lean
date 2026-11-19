/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DistributionalPoisson
public import PDE.FDeriv.Operators
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Classical equations for representatives of weak Poisson solutions

A `C²` representative of a weak Poisson solution satisfies the pointwise Poisson
equation wherever its forcing has a continuous representative. We identify
the equation; existence of the representatives is a separate regularity question.
-/

@[expose] public section

open PDE (laplacian iteratedPartialDeriv)

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A `C²` representative of a weak Poisson solution satisfies `−Δf = g`
pointwise whenever `g` is a continuous representative of the forcing. The existence
of these representatives is not part of this statement. -/
theorem IsWeakPoissonSolution.neg_laplacian_eq_of_representatives
    {F : DerivLp n 2 Ω} {u : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω) F u)
    {f g : ℝ^n → ℝ}
    (hrep : (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] f)
    (hreg : ∀ x ∈ Ω, ContDiffAt ℝ 2 f x)
    (hforce : (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g)
    (hg : ContinuousOn g Ω) :
    ∀ x ∈ Ω, -laplacian f x = g x := by
  have hfirst (i : Fin n) : HasWeakDerivativeOn (n := n) Ω [i]
      f (∂[i] f) :=
    hasWeakDerivativeOn_of_contDiffAt_one hu.1
      (fun x hx ↦ (hreg x hx).of_le (by norm_num)) i
  have hderiv (i : Fin n) : (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] ∂[i] f := by
    have hw : HasWeakDerivativeOn (n := n) Ω [i]
        (baseCoordCLM (n := n) (Ω := Ω) u) (derivCoordCLM (n := n) (Ω := Ω) i u) := by
      simpa only [firstDerivIndex_one, baseCoordCLM_apply, derivCoordCLM_apply] using
        (u : H¹(Ω)).property.hasWeakDerivativeOn_first (by norm_num) i
    exact (hw.congr_ae hrep .rfl).unique_ae hu.1 (hfirst i)
  have hsecond (i : Fin n) : HasWeakDerivativeOn (n := n) Ω [i]
      (∂[i] f) (∂[i] (∂[i] f)) :=
    hasWeakDerivativeOn_of_contDiffAt_one hu.1
      (fun x hx ↦ PDE.contDiffAt_partialDeriv 1 (hreg x hx) i) i
  have hlap : ContinuousOn (fun x ↦ -laplacian f x) Ω := by
    unfold laplacian
    exact (continuousOn_finsetSum _ fun i _ x hx ↦ (PDE.contDiffAt_partialDeriv 0
      (PDE.contDiffAt_partialDeriv 1 (hreg x hx) i) i).continuousAt.continuousWithinAt).neg
  have hnil : HasWeakDerivativeOn (n := n) Ω [] g (fun x ↦ -laplacian f x) := by
    refine ⟨hg.locallyIntegrableOn hu.1.measurableSet,
      hlap.locallyIntegrableOn hu.1.measurableSet, fun φ hφ ↦ ?_⟩
    have heq := hu.2 ⟨φ, hφ⟩
    have hleft : (∑ i : Fin n, ∫ x,
          (derivCoordCLM (n := n) (Ω := Ω) i u : ℝ^n → ℝ) x * (∂[i] φ.toFun) x
            ∂domainMeasure n Ω) =
        ∑ i : Fin n, -(∫ x, (∂[i] (∂[i] f)) x * φ.toFun x
          ∂domainMeasure n Ω) :=
      Finset.sum_congr rfl fun i _ ↦ (integral_congr_ae (g := fun x ↦ (∂[i] f) x *
        (∂[i] φ.toFun) x) ((hderiv i).mono fun x hx ↦ by simp only [hx])).trans
          (by simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
            Nat.zero_add, pow_one, neg_one_mul] using hsecond i φ hφ)
    have hright : (∫ x, (F : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω) =
        ∫ x, g x * φ.toFun x ∂domainMeasure n Ω :=
      integral_congr_ae (hforce.mono fun x hx ↦ by simp only [hx])
    have hlapint : (∫ x, -laplacian f x * φ.toFun x ∂domainMeasure n Ω) =
        ∑ i : Fin n, -(∫ x, (∂[i] (∂[i] f)) x * φ.toFun x
          ∂domainMeasure n Ω) := by
      simp only [laplacian, neg_mul, Finset.sum_mul, integral_neg, Finset.sum_neg_distrib]
      congr 1
      exact integral_finsetSum _ (fun i _ ↦ (hsecond i).integrable_mul_testFunction φ hφ)
    simpa only [iteratedPartialDeriv, List.length_nil, pow_zero, one_mul] using
      hright.symm.trans (heq.symm.trans (hleft.trans hlapint.symm))
  exact fun x hx ↦ (Measure.eqOn_open_of_ae_eq (μ := volume) (hnil.nil_ae_eq hu.1) hu.1 hg hlap
    hx).symm

end SobolevSpace.GraphSpace
