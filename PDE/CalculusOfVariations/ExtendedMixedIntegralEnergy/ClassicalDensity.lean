/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PartialGradient
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurable supporting fields of classical mixed densities

A density that is C1 only on the open spatial domain has jointly measurable
representatives, with continuous value slices and its canonical gradient
supporting field. Extension by zero outside the spatial domain imposes no
regularity there. Values lie in an arbitrary normed space; the gradient
variable lies in a Hilbert space.
-/

open scoped Gradient

@[expose] public noncomputable section

open Set MeasureTheory

namespace PDE.CalculusOfVariations

/-- A continuous density on a measurable spatial domain can be evaluated on
measurable value and gradient fields. No extension regularity is needed. -/
theorem aestronglyMeasurable_classicalDensity
    {X E H : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    [SecondCountableTopology E] [SecondCountableTopology H]
    {μ : Measure X} {Ω : Set X} (hΩ : MeasurableSet Ω)
    {L : (X × E) × H → ℝ} (hL : ContinuousOn L ((Ω ×ˢ univ) ×ˢ univ))
    {u : X → E} {v : X → H} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    (hmem : ∀ᵐ x ∂μ, x ∈ Ω) :
    AEStronglyMeasurable (fun x ↦ L ((x, u x), v x)) μ := by
  classical
  have hmeas : Measurable (((Ω ×ˢ univ) ×ˢ univ).piecewise L 0) :=
    hL.measurable_piecewise continuous_zero.continuousOn
      ((hΩ.prod MeasurableSet.univ).prod MeasurableSet.univ)
  apply (hmeas.comp_aemeasurable
    ((aemeasurable_id.prodMk hu).prodMk hv)).aestronglyMeasurable.congr
  filter_upwards [hmem] with x hx
  exact Set.piecewise_eq_of_mem _ _ _ ⟨⟨hx, mem_univ _⟩, mem_univ _⟩

/-- Prepare a classical density and its canonical partial gradient for the
mixed integral lower-semicontinuity theorem. No convexity, growth, or global
regularity outside the open spatial domain is needed for this preparation. -/
theorem exists_measurable_gradient_representatives_of_contDiffOn
    {X E H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {Ω : Set X} (hopen : IsOpen Ω) {L : (X × E) × H → ℝ}
    (hL : ContDiffOn ℝ 1 L ((Ω ×ˢ univ) ×ˢ univ)) :
    ∃ (F : X → E × H → ℝ) (D : X → E × H → H),
      Measurable (Function.uncurry F) ∧ Measurable (Function.uncurry D) ∧
      (∀ x ∈ Ω, ∀ s z, F x (s, z) = L ((x, s), z)) ∧
      (∀ x ∈ Ω, ∀ z, Continuous (fun s ↦ F x (s, z))) ∧
      (∀ x ∈ Ω, ∀ z, Continuous (fun s ↦ D x (s, z))) ∧
      (∀ x ∈ Ω, ∀ s z,
        HasFDerivAt (fun y ↦ F x (s, y)) (innerSL ℝ (D x (s, z))) z) := by
  classical
  let S : Set ((X × E) × H) := (Ω ×ˢ univ) ×ˢ univ
  let T : Set (X × (E × H)) := Ω ×ˢ univ
  let e : X × (E × H) → (X × E) × H :=
    fun t ↦ ((t.1, t.2.1), t.2.2)
  let F₀ := fun t ↦ L (e t)
  let D₀ := fun t : X × (E × H) ↦
    ∇ (fun z ↦ L ((t.1, t.2.1), z)) t.2.2
  have hS : IsOpen S := (hopen.prod isOpen_univ).prod isOpen_univ
  have hT : IsOpen T := hopen.prod isOpen_univ
  have he : MapsTo e T S := fun _ ht ↦ ⟨⟨ht.1, mem_univ _⟩, mem_univ _⟩
  have hF₀ : ContinuousOn F₀ T :=
    hL.continuousOn.comp (by fun_prop : Continuous e).continuousOn he
  have hD₀ : ContinuousOn D₀ T :=
    (PDE.Analysis.continuousOn_gradient_snd hL hS).comp
      (by fun_prop : Continuous e).continuousOn he
  let F := Function.curry (T.piecewise F₀ 0)
  let D := Function.curry (T.piecewise D₀ 0)
  have hFmeas : Measurable (Function.uncurry F) :=
    hF₀.measurable_piecewise continuous_zero.continuousOn hT.measurableSet
  have hDmeas : Measurable (Function.uncurry D) :=
    hD₀.measurable_piecewise continuous_zero.continuousOn hT.measurableSet
  have hFeq (x : X) (hx : x ∈ Ω) (s : E) (z : H) :
      F x (s, z) = L ((x, s), z) :=
    ite_eq_left (show (x, (s, z)) ∈ T from ⟨hx, mem_univ _⟩)
  have hDeq (x : X) (hx : x ∈ Ω) (s : E) (z : H) :
      D x (s, z) = ∇ (fun y ↦ L ((x, s), y)) z :=
    ite_eq_left (show (x, (s, z)) ∈ T from ⟨hx, mem_univ _⟩)
  refine ⟨F, D, hFmeas, hDmeas, hFeq, ?_, ?_, ?_⟩
  · intro x hx z
    simp_rw [hFeq x hx]
    exact hL.continuousOn.comp_continuous (by fun_prop)
      (fun _ ↦ ⟨⟨hx, mem_univ _⟩, mem_univ _⟩)
  · intro x hx z
    simp_rw [hDeq x hx]
    exact (PDE.Analysis.continuousOn_gradient_snd hL hS).comp_continuous
      (by fun_prop : Continuous (fun s : E ↦ ((x, s), z)))
      (fun _ ↦ ⟨⟨hx, mem_univ _⟩, mem_univ _⟩)
  · intro x hx s z
    simp_rw [hFeq x hx, hDeq x hx]
    have hd := ((hL.differentiableOn (by decide)) ((x, s), z)
      ⟨⟨hx, mem_univ _⟩, mem_univ _⟩).differentiableAt
        (hS.mem_nhds ⟨⟨hx, mem_univ _⟩, mem_univ _⟩)
    have hpart := hd.hasFDerivAt.comp z
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) (x, s) z)
    exact hpart.differentiableAt.hasGradientAt.hasFDerivAt

end PDE.CalculusOfVariations
