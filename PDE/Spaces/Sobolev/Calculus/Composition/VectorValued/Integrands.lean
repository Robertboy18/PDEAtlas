/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Banach-valued composition integrands

The map `(z, v) ↦ DΦ(z)v` is continuous with linear growth when `Φ` is `C¹`
and its derivative is bounded. The general superposition theorem therefore
gives continuity on finite-exponent `Lp`, even when `DΦ` is not Lipschitz.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} {Φ : E → F} {C : ℝ≥0}

/-- A zero-preserving map with bounded derivative preserves every `Lp` class,
including exponent infinity and measures of infinite mass. -/
theorem memLp_comp_of_bounded_fderiv (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) {u : X → E} (hu : MemLp u p μ) :
    MemLp (Φ ∘ u) p μ :=
  (lipschitzWith_of_nnnorm_fderiv_le (hΦ.differentiable one_ne_zero) hbound).comp_memLp
    hzero hu

/-- Value superposition is continuous for finite normed exponents. -/
theorem continuous_valueSuperposition [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hΦ : ContDiff ℝ 1 Φ) (hzero : Φ 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) :
    Continuous (Lp.superposition (fun _ : X ↦ Φ)
      (fun u : Lp E p μ ↦ memLp_comp_of_bounded_fderiv hΦ hzero hbound (Lp.memLp u))) := by
  apply Lp.continuous_superposition hp _
    (Filter.Eventually.of_forall fun _ ↦ hΦ.continuous) (C := C) (a := 0) MemLp.zero
  apply Filter.Eventually.of_forall
  intro x z
  simpa only [Pi.zero_apply, zero_add, hzero, sub_zero] using
    (lipschitzWith_of_nnnorm_fderiv_le (hΦ.differentiable one_ne_zero) hbound).norm_sub_le z 0

/-- The derivative of the composing map applied to a value and tangent pair. -/
def chainIntegrand (Φ : E → F) (s : E × E) : F :=
  fderiv ℝ Φ s.1 s.2

/-- Continuity of the derivative suffices for continuity of the chain integrand. -/
theorem continuous_chainIntegrand (hΦ : ContDiff ℝ 1 Φ) :
    Continuous (chainIntegrand Φ) :=
  ((hΦ.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_snd

/-- A bounded derivative controls the chain integrand by the tangent component. -/
theorem norm_chainIntegrand_le (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (s : E × E) :
    ‖chainIntegrand Φ s‖ ≤ C * ‖s.2‖ :=
  ((fderiv ℝ Φ s.1).le_opNorm s.2).trans
    (mul_le_mul_of_nonneg_right (hbound s.1) (norm_nonneg s.2))

/-- The chain integrand has linear growth in the pair norm. -/
theorem norm_chainIntegrand_le_pair (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (s : E × E) :
    ‖chainIntegrand Φ s‖ ≤ C * ‖s‖ :=
  (norm_chainIntegrand_le hbound s).trans
    (mul_le_mul_of_nonneg_left (norm_snd_le s) C.coe_nonneg)

/-- The derivative expression belongs to `Lp` for arbitrary Banach-valued inputs. -/
theorem memLp_chainIntegrand (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) (u : Lp (E × E) p μ) :
    MemLp (fun x ↦ chainIntegrand Φ (u x)) p μ := by
  refine ((Lp.memLp u).norm.const_mul (C : ℝ)).mono' ?_ ?_
  · exact (continuous_chainIntegrand hΦ).comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ norm_chainIntegrand_le_pair hbound (u x)

/-- Only measurability of the base and `Lp` membership of the tangent are needed
for `Lp` membership of the derivative expression. -/
theorem memLp_fderiv_apply (hΦ : ContDiff ℝ 1 Φ)
    (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) {u v : X → E}
    (hu : AEStronglyMeasurable u μ) (hv : MemLp v p μ) :
    MemLp (fun x ↦ fderiv ℝ Φ (u x) (v x)) p μ := by
  refine (hv.norm.const_mul (C : ℝ)).mono' ?_ ?_
  · exact (continuous_chainIntegrand hΦ).comp_aestronglyMeasurable
      (hu.prodMk hv.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun x ↦ norm_chainIntegrand_le hbound (u x, v x)

/-- Derivative superposition is continuous for every finite normed exponent. -/
theorem continuous_chainSuperposition [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hΦ : ContDiff ℝ 1 Φ) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) :
    Continuous (Lp.superposition (fun _ : X ↦ chainIntegrand Φ)
      (memLp_chainIntegrand (p := p) (μ := μ) hΦ hbound)) := by
  apply Lp.continuous_superposition hp _
    (Filter.Eventually.of_forall fun _ ↦ continuous_chainIntegrand hΦ)
    (C := C) (a := 0) MemLp.zero
  exact Filter.Eventually.of_forall fun _ s ↦ by
    simpa only [Pi.zero_apply, zero_add] using norm_chainIntegrand_le_pair hbound s

/-- Pair two `Lp` functions by mapping them through the two linear inclusions. -/
def pairLpCLM [Fact (1 ≤ p)] :
    Lp E p μ × Lp E p μ →L[ℝ] Lp (E × E) p μ :=
  ((ContinuousLinearMap.inl ℝ E E).compLpL p μ).comp
      (ContinuousLinearMap.fst ℝ _ _) +
    ((ContinuousLinearMap.inr ℝ E E).compLpL p μ).comp
      (ContinuousLinearMap.snd ℝ _ _)

/-- The paired `Lp` representative agrees with the pointwise pair almost everywhere. -/
theorem pairLpCLM_apply_ae [Fact (1 ≤ p)] (u v : Lp E p μ) :
    (pairLpCLM (u, v) : X → E × E) =ᵐ[μ] fun x ↦ (u x, v x) := by
  filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.inl ℝ E E).compLpL p μ u)
      ((ContinuousLinearMap.inr ℝ E E).compLpL p μ v),
    (ContinuousLinearMap.inl ℝ E E).coeFn_compLpL u,
    (ContinuousLinearMap.inr ℝ E E).coeFn_compLpL v] with x hadd hu hv
  change ((ContinuousLinearMap.inl ℝ E E).compLpL p μ u +
    (ContinuousLinearMap.inr ℝ E E).compLpL p μ v : Lp (E × E) p μ) x = _
  simp only [hadd, Pi.add_apply, hu, hv, ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]

variable {n : ℕ} {Ω : Opens ℝ^n} [CompleteSpace E] [Fact (1 ≤ p)]

/-- A Sobolev value and one weak derivative as a continuous `Lp` pair. -/
def valueDerivativeCLM (i : Fin n) :
    W^{1,p}(Ω; E) →L[ℝ] Lp (E × E) p (domainMeasure n Ω) :=
  pairLpCLM.comp ((coordinateCLM (baseIndex n 1)).prod
    (coordinateCLM (singleDerivIndex n i)))

/-- The two components of the pair retain their Sobolev representatives. -/
theorem valueDerivativeCLM_apply_ae (U : W^{1,p}(Ω; E)) (i : Fin n) :
    (valueDerivativeCLM i U : ℝ^n → E × E) =ᵐ[domainMeasure n Ω]
      fun x ↦ (U.val (baseIndex n 1) x, U.val (singleDerivIndex n i) x) :=
  pairLpCLM_apply_ae _ _

end SobolevSpace.VectorValued
