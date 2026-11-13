/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakDifferentiation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Localizing transport coefficients on the support of a weak derivative

The rescaled drift grows linearly at infinity. A compact C¹ drift agreeing with
it near the vorticity support has exactly the same products with the second
weak derivative, including the divergence term in the energy identity.
The support of that weak derivative is proved from its continuous primitive.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open scoped Topology

namespace DeGregorio.Iteration

/-- A weak derivative vanishes almost everywhere outside the topological
support of its continuous primitive. -/
theorem ae_weakDerivative_eq_zero_outside
    {q r : ℝ → ℝ} {K : Set ℝ}
    (hqr : HasWeakTimeDerivativeOn univ q r) (hq : Continuous q)
    (hsupp : tsupport q ⊆ K) :
    ∀ᵐ x ∂volume, x ∉ K → r x = 0 := by
  filter_upwards [hqr.ae_hasDerivAt_of_continuous hq] with x hx
  intro hnot
  rw [← hx.deriv]
  exact deriv_of_notMem_tsupport (fun hs ↦ hnot (hsupp hs))

/-- A C¹ drift can be replaced by a compact C¹ drift agreeing with it and
its derivative on any prescribed compact set. Its global Lipschitz bound
comes from compact support. -/
theorem exists_compact_drift_eqOn
    {K : Set ℝ} (hK : IsCompact K) {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) :
    ∃ (A : ℝ → ℝ) (C : NNReal), ContDiff ℝ 1 A ∧ HasCompactSupport A ∧
      LipschitzWith C A ∧ EqOn A V K ∧ EqOn (deriv A) (deriv V) K := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt (0 : ℝ) (0 : ℝ)
  let χ : ContDiffBump (0 : ℝ) := ⟨r, r + 1, hr, lt_add_one r⟩
  let A := fun x ↦ χ x * V x
  have hA : ContDiff ℝ 1 A := χ.contDiff.mul hV
  have hc : HasCompactSupport A := χ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hA one_ne_zero
  have heq (x : ℝ) (hx : x ∈ K) : A =ᶠ[𝓝 x] V := by
    have hχ := χ.eventuallyEq_one_of_mem_ball (hKr hx)
    filter_upwards [hχ] with y hy
    change χ y * V y = V y
    rw [show χ y = 1 from hy, one_mul]
  exact ⟨A, C, hA, hc, hC, fun x hx ↦ (heq x hx).eq_of_nhds,
    fun x hx ↦ (heq x hx).deriv_eq⟩

/-- Compact localization preserves both the transport flux and its
coefficient-divergence product with a supported weak derivative. This is the
coefficient replacement needed for an L² transport commutator argument. -/
theorem exists_compact_drift_weak_products
    {K : Set ℝ} (hK : IsCompact K) {V q r : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V)
    (hqr : HasWeakTimeDerivativeOn univ q r) (hq : Continuous q)
    (hsupp : tsupport q ⊆ K) :
    ∃ (A : ℝ → ℝ) (C : NNReal), ContDiff ℝ 1 A ∧ HasCompactSupport A ∧
      LipschitzWith C A ∧
      (fun x ↦ A x * r x) =ᵐ[volume] (fun x ↦ V x * r x) ∧
      (fun x ↦ deriv A x * r x) =ᵐ[volume] (fun x ↦ deriv V x * r x) := by
  obtain ⟨A, C, hA, hc, hC, heq, hdeq⟩ := exists_compact_drift_eqOn hK hV
  refine ⟨A, C, hA, hc, hC, ?_, ?_⟩
  · filter_upwards [ae_weakDerivative_eq_zero_outside hqr hq hsupp] with x hx
    by_cases hmem : x ∈ K
    · rw [heq hmem]
    · rw [hx hmem, mul_zero, mul_zero]
  · filter_upwards [ae_weakDerivative_eq_zero_outside hqr hq hsupp] with x hx
    by_cases hmem : x ∈ K
    · rw [hdeq hmem]
    · rw [hx hmem, mul_zero, mul_zero]

end DeGregorio.Iteration
