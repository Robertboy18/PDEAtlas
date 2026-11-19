/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.LaplacianTest
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# From the distributional Poisson equation to energy tests

An H¹ representative of `Δu = f` satisfies the variational equation against
every H¹₀ test. The sign of the load is `-f`. No boundary condition on the
state is imposed.

Integration by parts against a derivative of a smooth test gives the identity
on compact tests. Density then extends the two continuous L² pairings to H¹₀.
Local H¹ membership can therefore be obtained separately from distributional
regularity, without assuming the energy identity or an H¹ norm bound.
-/

@[expose] public noncomputable section

open PDE (laplacian iteratedPartialDeriv)

open scoped Sobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The distributional equation `Δu = f` for an H¹ state extends to all H¹₀
tests with load `-f`. Both pairings are between L² classes; the state
itself has no zero-trace requirement. -/
theorem poisson_weakForm_of_integral_laplacian_eq
    (u : H¹(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative u x * laplacian φ.1.toFun x ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω)
    (v : H¹₀(Ω)) :
    (∑ i : Fin n, ⟪(u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i),
      derivCoordCLM i v⟫_ℝ) = ⟪-f, baseCoordCLM v⟫_ℝ := by
  classical
  let du (i : Fin n) : DerivLp n 2 Ω :=
    (u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)
  let F : H¹₀(Ω) →L[ℝ] ℝ :=
    ∑ i : Fin n, (innerSL ℝ (du i)).comp (derivCoordCLM i)
  let G : H¹₀(Ω) →L[ℝ] ℝ :=
    (innerSL ℝ (-f)).comp baseCoordCLM
  have htest : (F : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear =
      (G : H¹₀(Ω) → ℝ) ∘ testFunctionToH10Linear := by
    funext φ
    change F (testFunctionToH10 φ) = G (testFunctionToH10 φ)
    simp only [F, G, du, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    simp only [sum_inner_deriv_test_eq_neg_integral_laplacian, hweak φ, inner_neg_left,
      inner_base_testFunction_eq_integral]
  have h := congrFun
    ((denseRange_testFunctionToH10Linear (n := n) (Ω := Ω)).equalizer
      F.continuous G.continuous htest) v
  simpa only [F, G, du, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] using h


/-- For a W²,² representative, the distributional equation identifies
its Laplacian with the forcing as an L² class. Openness supplies uniqueness of
the distribution represented by a locally integrable function. -/
theorem laplacian_rows_eq_of_integral_laplacian_eq
    (hΩ : IsOpen Ω) (u : W^{2,2}(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative u x * laplacian φ.1.toFun x ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω) :
    (∑ i : Fin n, (u : WkpAmbientOn n 2 2 Ω) (topPureDerivIndex n 2 i)) = f := by
  classical
  let d (i : Fin n) : DerivLp n 2 Ω :=
    (u : WkpAmbientOn n 2 2 Ω) (topPureDerivIndex n 2 i)
  let T : DerivLp n 2 Ω := ∑ i : Fin n, d i
  have hd (i : Fin n) :
      HasWeakDerivativeOn Ω [i, i] (baseRepresentative u) (d i) := by
    simpa only [baseRepresentative, d, topPureDerivIndex, pureDerivIndex, List.replicate_succ,
      List.replicate_zero] using u.property.hasWeakDerivativeOn_list [i, i] (by norm_num)
  have hT : HasWeakDerivativeOn Ω [] (T : ℝ^n → ℝ) (f : ℝ^n → ℝ) := by
    refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp T) (by norm_num),
      memLp_locallyIntegrableOn_domain (Lp.memLp f) (by norm_num), ?_⟩
    intro φ hφ
    simp only [iteratedPartialDeriv, List.length_nil, pow_zero, one_mul]
    calc
      _ = ∫ x, (∑ i : Fin n, (d i : ℝ^n → ℝ) x) * φ x ∂domainMeasure n Ω := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ d] with x hx
        rw [hx]
        simp only [TestFunction.toFun_eq_coe]
      _ = ∑ i : Fin n, ∫ x, (d i : ℝ^n → ℝ) x * φ x ∂domainMeasure n Ω := by
        simp only [Finset.sum_mul]
        exact integral_finsetSum _ (fun i _ ↦ (hd i).integrable_mul_testFunction φ hφ)
      _ = ∑ i : Fin n, ∫ x, baseRepresentative u x *
          (∂[i] (∂[i] φ.toFun)) x ∂domainMeasure n Ω := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [iteratedPartialDeriv] using (hd i φ hφ).symm
      _ = ∫ x, baseRepresentative u x * laplacian φ.toFun x ∂domainMeasure n Ω := by
        simp only [laplacian, Finset.mul_sum]
        symm
        apply integral_finsetSum
        intro i _
        simpa only [iteratedPartialDeriv] using
          (hd i).integrable_mul_iteratedPartialDeriv φ hφ
      _ = _ := hweak ⟨φ, hφ⟩
  exact Lp.ext (hT.nil_ae_eq hΩ)

end SobolevSpace.GraphSpace
