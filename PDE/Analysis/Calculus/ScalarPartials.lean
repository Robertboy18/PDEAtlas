/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Scalar differentials from partial derivatives

A real value variable and an inner product space variable give the differential
`(r,w) ↦ A r + ⟨D,w⟩`. Continuous partial derivatives suffice to derive it.
For a differentiable function of finitely many blocks, the differentials of the
coordinate restrictions determine its full differential by summing over the blocks.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Continuous value and gradient partials determine the joint differential. -/
theorem hasFDerivAt_of_continuous_scalar_partials
    {f A : ℝ × E → ℝ} {D : ℝ × E → E}
    (hvalue : ∀ s z, HasDerivAt (fun t ↦ f (t, z)) (A (s, z)) s)
    (hgradient : ∀ s z,
      HasFDerivAt (fun y ↦ f (s, y)) (innerSL ℝ (D (s, z))) z)
    (hA : Continuous A) (hD : Continuous D) (z : ℝ × E) :
    HasFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℝ (A z)).coprod (innerSL ℝ (D z))) z := by
  have hAc := (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp hA
  have hDc := (innerSL ℝ (E := E)).continuous.comp hD
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun s y ↦ f (s, y))
    (f₁ := fun s y ↦ ContinuousLinearMap.toSpanSingleton ℝ (A (s, y)))
    (f₂ := fun s y ↦ innerSL ℝ (D (s, y)))
    (Eventually.of_forall fun w ↦ (hvalue w.1 w.2).hasFDerivAt)
    (Eventually.of_forall fun w ↦ hgradient w.1 w.2)
    hAc.continuousAt hDc.continuousAt).hasFDerivAt

/-- The norm of a value-gradient differential is bounded by its two coefficient norms. -/
theorem norm_toSpanSingleton_coprod_innerSL_le (a : ℝ) (d : E) :
    ‖(ContinuousLinearMap.toSpanSingleton ℝ a).coprod (innerSL ℝ d)‖ ≤ |a| + ‖d‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro w
  change ‖w.1 * a + inner ℝ d w.2‖ ≤ (|a| + ‖d‖) * ‖w‖
  calc
    _ ≤ ‖w.1 * a‖ + ‖inner ℝ d w.2‖ := norm_add_le _ _
    _ ≤ |a| * ‖w.1‖ + ‖d‖ * ‖w.2‖ := by
      simpa only [norm_mul, Real.norm_eq_abs, mul_comm] using
        add_le_add (le_refl ‖w.1 * a‖) (norm_inner_le_norm (𝕜 := ℝ) d w.2)
    _ ≤ |a| * ‖w‖ + ‖d‖ * ‖w‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le w) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_snd_le w) (norm_nonneg _))
    _ = _ := (add_mul _ _ _).symm

/-- Evaluation of a value-gradient differential preserves measurability. -/
theorem measurable_toSpanSingleton_coprod_innerSL_apply
    {X : Type*} [MeasurableSpace X] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    {A r : X → ℝ} {D w : X → E}
    (hA : Measurable A) (hD : Measurable D) (hr : Measurable r) (hw : Measurable w) :
    Measurable (fun x ↦
      (ContinuousLinearMap.toSpanSingleton ℝ (A x)).coprod (innerSL ℝ (D x)) (r x, w x)) :=
  (hr.mul hA).add (hD.inner hw)

/-- Actual coordinate differentials determine the differential of a differentiable
function on a finite product. The coefficients may depend on every input coordinate. -/
theorem hasFDerivAt_of_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℝ (V i)]
    {f : (∀ i, V i) → ℝ} {x : ∀ i, V i} {D : ∀ i, V i →L[ℝ] ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hD : ∀ i, HasFDerivAt (fun y ↦ f (Function.update x i y)) (D i) (x i)) :
    HasFDerivAt f (∑ i, (D i).comp (ContinuousLinearMap.proj i)) x := by
  have hcoord (i : ι) (w : V i) :
      fderiv ℝ f x (Pi.single i w) = D i w := by
    have houter : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
      simpa only [Function.update_eq_self] using hf.hasFDerivAt
    have h := houter.comp (x i) (hasFDerivAt_update (𝕜 := ℝ) x (x i))
    have heq := h.unique (hD i)
    have hsingle :
        (ContinuousLinearMap.pi (Pi.single i (ContinuousLinearMap.id ℝ (V i)))) w =
          Pi.single i w := by
      ext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]
    simpa only [ContinuousLinearMap.comp_apply, hsingle] using congrArg (fun L ↦ L w) heq
  convert hf.hasFDerivAt using 1
  ext w
  conv_rhs => rw [← LinearMap.sum_single_apply V w]
  simp only [map_sum, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, hcoord]

/-- On a finite family of value-gradient pairs, continuous component partials give the
sum formula for the differential. Differentiability is pointwise in the state variables. -/
theorem hasFDerivAt_of_continuous_component_partials
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ × E) → ℝ} {A : (ι → ℝ × E) → ι → ℝ}
    {D : (ι → ℝ × E) → ι → E}
    (hvalue : ∀ z i, HasDerivAt
      (fun t ↦ f (Function.update z i (t, (z i).2))) (A z i) (z i).1)
    (hgradient : ∀ z i, HasFDerivAt
      (fun y ↦ f (Function.update z i ((z i).1, y))) (innerSL ℝ (D z i)) (z i).2)
    (hA : ∀ i, Continuous (fun z ↦ A z i))
    (hD : ∀ i, Continuous (fun z ↦ D z i))
    (z : ι → ℝ × E) (hf : DifferentiableAt ℝ f z) :
    HasFDerivAt f
      (∑ i, ((ContinuousLinearMap.toSpanSingleton ℝ (A z i)).coprod
        (innerSL ℝ (D z i))).comp (ContinuousLinearMap.proj i)) z := by
  apply hasFDerivAt_of_update hf
  intro i
  have hupdate : Continuous (Function.update z i) := continuous_const.update i continuous_id
  have h := hasFDerivAt_of_continuous_scalar_partials
    (f := fun w ↦ f (Function.update z i w))
    (A := fun w ↦ A (Function.update z i w) i)
    (D := fun w ↦ D (Function.update z i w) i)
    (fun s y ↦ by simpa using hvalue (Function.update z i (s, y)) i)
    (fun s y ↦ by simpa using hgradient (Function.update z i (s, y)) i)
    ((hA i).comp hupdate) ((hD i).comp hupdate) (z i)
  simpa only [Function.update_eq_self] using h

end PDE.Analysis
