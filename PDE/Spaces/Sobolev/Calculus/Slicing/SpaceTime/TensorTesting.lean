/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.SpaceTime.TensorProduct
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.MeasureTheory.SpaceTime

/-!
# Tensor testing of raw spacetime weak derivatives

The canonical spacetime split preserves volume also after restricting the
time variable to an arbitrary set. Testing a raw weak derivative against a
time-space tensor and applying Fubini gives the iterated integral
identities needed to recover Sobolev spatial slices and weak time derivatives.
No regularity or integrability of slices is assumed.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Slices

open MeasureTheory Set TopologicalSpace PDE.Common
open scoped ENNReal Distributions

variable {n : ℕ} {I : Set ℝ}

/-- Splitting spacetime and restricting time commute at the level of
Lebesgue measures. Measurability of the time set is not needed. -/
theorem measurePreserving_timeSpaceCons_restrict (I : Set ℝ) :
    MeasurePreserving (timeSpaceContinuousLinearEquiv n).symm
      ((volume.restrict I).prod volume) (volume.restrict {p | p 0 ∈ I}) := by
  have h :=
    (PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv (n := n)).restrict_preimage_emb
    (timeSpaceContinuousLinearEquiv n).toHomeomorph.measurableEmbedding (I ×ˢ univ)
  have hpre : (timeSpaceContinuousLinearEquiv n) ⁻¹' (I ×ˢ univ) =
      {p : ℝ^(n + 1) | p 0 ∈ I} := by
    ext p
    simp
  rw [hpre, Measure.volume_eq_prod ℝ (ℝ^n), ← Measure.restrict_prod_eq_prod_univ] at h
  exact MeasurePreserving.symm (timeSpaceContinuousLinearEquiv n).toHomeomorph.toMeasurableEquiv h

private theorem integral_mul_tensor_factor (r h : ℝ^n → ℝ) (c : ℝ) :
    (∫ x, r x * (c * h x)) = c * ∫ x, r x * h x := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ ↦ mul_left_comm _ _ _

/-- Fubini separates a tensor test whose coordinate derivative also factors into
a time function and a spatial function. Integrability follows from the weak derivative. -/
private theorem integral_timeSpaceTensor_of_partialDeriv
    {f g : ℝ^(n + 1) → ℝ} {j : Fin (n + 1)}
    (h : HasWeakDerivativeOn {p | p 0 ∈ I} [j] f g)
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (hψ : tsupport ψ ⊆ I)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (a : ℝ → ℝ) (b : ℝ^n → ℝ)
    (hderiv : ∀ t x,
      (∂[j] (TestFunction.timeSpaceTensor ψ φ : ℝ^(n + 1) → ℝ))
        (timeSpaceCons t x) = a t * b x) :
    (∫ t in I, a t * ∫ x, f (timeSpaceCons t x) * b x) =
      -(∫ t in I, ψ t * ∫ x, g (timeSpaceCons t x) * φ.toFun x) := by
  let Φ := TestFunction.timeSpaceTensor ψ φ
  have hs : tsupport Φ.toFun ⊆ {p | p 0 ∈ I} := by
    simpa only [TestFunction.toFun_eq_coe] using
      TestFunction.tsupport_timeSpaceTensor_subset ψ φ hψ
  have hm := measurePreserving_timeSpaceCons_restrict (n := n) I
  have he := (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph.measurableEmbedding
  have hi := hm.integrable_comp_of_integrable (h.integrable_mul_iteratedPartialDeriv Φ hs)
  have hj := hm.integrable_comp_of_integrable (h.integrable_mul_testFunction Φ hs)
  have heq := h Φ hs
  rw [← hm.integral_comp he, ← hm.integral_comp he] at heq
  simp only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply,
    TestFunction.toFun_eq_coe, iteratedPartialDeriv, Φ,
    hderiv,
    TestFunction.timeSpaceTensor_timeSpaceCons] at hi hj heq
  rw [integral_prod _ hi, integral_prod _ hj] at heq
  simpa only [List.length_cons, List.length_nil, zero_add, pow_one, neg_one_mul,
    integral_mul_tensor_factor, TestFunction.toFun_eq_coe] using heq

/-- The spatial weak derivative identity after testing in time and splitting
the raw spacetime integral. -/
theorem _root_.SobolevSpace.HasWeakDerivativeOn.integral_timeSpaceTensor_spatial
    {f g : ℝ^(n + 1) → ℝ} (i : Fin n)
    (h : HasWeakDerivativeOn {p | p 0 ∈ I} [i.succ] f g)
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (hψ : tsupport ψ ⊆ I)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ t in I, ψ t * ∫ x, f (timeSpaceCons t x) * (∂[i] φ.toFun) x) =
      -(∫ t in I, ψ t * ∫ x, g (timeSpaceCons t x) * φ.toFun x) := by
  exact integral_timeSpaceTensor_of_partialDeriv h ψ hψ φ ψ (∂[i] φ.toFun)
    (TestFunction.partialDeriv_timeSpaceTensor_succ ψ φ i)

/-- The time weak derivative identity after testing in space and splitting
the raw spacetime integral. -/
theorem _root_.SobolevSpace.HasWeakDerivativeOn.integral_timeSpaceTensor_time
    {f g : ℝ^(n + 1) → ℝ} (h : HasWeakDerivativeOn {p | p 0 ∈ I} [0] f g)
    (ψ : 𝓓((⊤ : Opens ℝ), ℝ)) (hψ : tsupport ψ ⊆ I)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    (∫ t in I, deriv (ψ : ℝ → ℝ) t * ∫ x, f (timeSpaceCons t x) * φ.toFun x) =
      -(∫ t in I, ψ t * ∫ x, g (timeSpaceCons t x) * φ.toFun x) := by
  exact integral_timeSpaceTensor_of_partialDeriv h ψ hψ φ (deriv (ψ : ℝ → ℝ)) φ.toFun
    (TestFunction.partialDeriv_timeSpaceTensor_zero ψ φ)

end SobolevSpace.Slices
