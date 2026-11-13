/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Recovering the pointwise equation from a regular flux

A C¹ representative of an L² flux satisfying the weak divergence equation
has classical divergence equal to minus the continuous forcing. Integration
by parts and uniqueness of weak derivatives give the equality almost
everywhere; continuity gives it at every interior point. The flux may be
nonlinear and no ellipticity assumption is used.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set SobolevSpace
open scoped ENNReal Sobolev InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n}

/-- A regular representative of a weak flux satisfies the
pointwise divergence equation, with the sign fixed by the weak pairing. -/
theorem neg_divergence_eq_of_flux_pairing
    (hΩ : IsOpen Ω) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i, ⟪q i, derivCoordCLM i v⟫_ℝ) = ⟪f, baseCoordCLM v⟫_ℝ)
    {Q : ℝ^n → ℝ^n} (hQ : ContDiffOn ℝ 1 Q Ω)
    (hq : ∀ i, (q i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦ Q x i)
    {g : ℝ^n → ℝ} (hg : ContinuousOn g Ω)
    (hf : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] g) :
    ∀ x ∈ Ω, -(PDE.divergence Q x) = g x := by
  have hQc (i : Fin n) (x : ℝ^n) (hx : x ∈ Ω) :
      ContDiffAt ℝ 1 (fun y ↦ Q y i) x :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.contDiffAt.comp x
      (hQ.contDiffAt (hΩ.mem_nhds hx))
  have hd (i : Fin n) : HasWeakDerivativeOn Ω [i] (fun x ↦ Q x i)
      (∂[i] (fun x ↦ Q x i)) :=
    hasWeakDerivativeOn_of_contDiffAt_one hΩ (hQc i) i
  have hc : ContinuousOn (fun x ↦ -(PDE.divergence Q x)) Ω := by
    apply ContinuousOn.neg
    apply continuousOn_finsetSum
    intro i _ x hx
    exact (PDE.contDiffAt_partialDeriv 0 (hQc i x hx) i).continuousAt.continuousWithinAt
  have hnil : HasWeakDerivativeOn Ω [] g (fun x ↦ -(PDE.divergence Q x)) := by
    refine ⟨hg.locallyIntegrableOn hΩ.measurableSet,
      hc.locallyIntegrableOn hΩ.measurableSet, ?_⟩
    intro φ hφ
    let test : TestFunctionOn n Ω := ⟨φ, hφ⟩
    have hterm (i : Fin n) :
        ⟪q i, derivCoordCLM i (testFunctionToH10 test)⟫_ℝ =
          -(∫ x, (∂[i] (fun y ↦ Q y i)) x * φ.toFun x ∂domainMeasure n Ω) := by
      calc
        _ = ∫ x, Q x i * (∂[i] φ.toFun) x ∂domainMeasure n Ω := by
          rw [inner_deriv_testFunction_data_eq_integral]
          apply integral_congr_ae
          filter_upwards [hq i] with x hx
          rw [hx]
        _ = _ := by
          simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
            Nat.zero_add, pow_one, neg_one_mul] using hd i φ hφ
    have hload : ⟪f, baseCoordCLM (testFunctionToH10 test)⟫_ℝ =
        ∫ x, g x * φ.toFun x ∂domainMeasure n Ω := by
      rw [inner_base_testFunction_eq_integral]
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [hx]
    have he := hweak (testFunctionToH10 test)
    simp only [hterm, hload] at he
    have hi :
        (∫ x, -(PDE.divergence Q x) * φ.toFun x ∂domainMeasure n Ω) =
          ∑ i, -(∫ x, (∂[i] (fun y ↦ Q y i)) x * φ.toFun x ∂domainMeasure n Ω) := by
      simp only [PDE.divergence, neg_mul, Finset.sum_mul, integral_neg,
        Finset.sum_neg_distrib]
      congr 1
      exact integral_finsetSum _ (fun i _ ↦ (hd i).integrable_mul_testFunction φ hφ)
    simpa only [iteratedPartialDeriv, List.length_nil, pow_zero, one_mul] using
      he.symm.trans hi.symm
  have he := Measure.eqOn_open_of_ae_eq (μ := volume) (hnil.nil_ae_eq hΩ) hΩ hg hc
  exact fun x hx ↦ (he hx).symm

end SobolevSpace.GraphSpace
