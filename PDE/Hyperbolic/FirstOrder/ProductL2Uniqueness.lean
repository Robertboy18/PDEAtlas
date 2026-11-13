/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeProductFormulation
public import PDE.Hyperbolic.FirstOrder.DistributionalUniqueness
import PDE.Analysis.MeasureTheory.Lp.SectionReconstruction

/-!
# Uniqueness of joint product-L² weak states

A joint square-integrable state determines its Bochner L² sections by reconstruction.
The product-integral formulation then gives the spatial-L² weak equation.
Bochner uniqueness identifies the reconstructed classes, and Fubini gives equality
of the original joint states for the product measure.

The state and forcing need only belong to product L². The coefficients are joint representatives of
the specified symmetric W¹,∞ fields and their weak derivatives. Their base rows are continuous on
the closed time interval, and their spatial derivatives obey the uniform bounds. The initial datum
enters through the weak equation's boundary term, so equality says nothing about arbitrary
representatives on the initial time slice.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology Distributions ContDiff

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

/-- For a.e. strongly measurable joint functions, equality on almost every spatial
section implies equality for the product measure. Measurable representatives allow
the reverse Fubini implication; arbitrary nonmeasurable functions would not suffice. -/
private theorem ae_eq_of_ae_eq_sections {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MetricSpace E] {μ : Measure α} {ν : Measure β} [SFinite ν] {U V : α × β → E}
    (hU : AEStronglyMeasurable U (μ.prod ν)) (hV : AEStronglyMeasurable V (μ.prod ν))
    (hsec : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] fun x ↦ V (t, x)) :
    U =ᵐ[μ.prod ν] V := by
  have hmk : hU.mk U =ᵐ[μ.prod ν] hV.mk V := by
    refine (Measure.ae_prod_iff_ae_ae (μ := μ) (ν := ν) (p := fun z ↦ hU.mk U z = hV.mk V z)
      (hU.stronglyMeasurable_mk.measurableSet_eq_fun hV.stronglyMeasurable_mk)).mpr ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hU.ae_eq_mk,
      Measure.ae_ae_of_ae_prod hV.ae_eq_mk, hsec] with t htU htV ht
    filter_upwards [htU, htV, ht] with x hxU hxV hx using hxU.symm.trans (hx.trans hxV)
  exact hU.ae_eq_mk.trans (hmk.trans hV.ae_eq_mk.symm)

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "ν" => volume.restrict (Ioc a b)
local notation "σ" => domainMeasure n univ

/-- Joint product-L² solutions of the symmetric transport system with the same forcing
and initial boundary datum agree almost everywhere on time-space. Spatial L² sections
and their Bochner measurability are constructed from `hU`, `hV`, and `hF`, using the
countably generated Euclidean Borel space and its s-finite spatial measure.

Coefficient representative agreement is an explicit hypothesis connecting the
product equation to the given Sobolev field. -/
theorem ae_eq_of_symmetric_product_spacetime_weak_equations
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C₀ L₀ : ℝ} (hC₀ : 0 ≤ C₀) (hL₀ : 0 ≤ L₀)
    (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C₀)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L₀) (U V F : Fin m → ℝ × ℝ^n → ℝ)
    (hU : ∀ p, MemLp (U p) 2 ((ν).prod σ)) (hV : ∀ p, MemLp (V p) 2 ((ν).prod σ))
    (hF : ∀ p, MemLp (F p) 2 ((ν).prod σ)) (C B : Fin n → Fin m → Fin m → ℝ × ℝ^n → ℝ)
    (hC : ∀ j p q, AEStronglyMeasurable (C j p q) ((ν).prod σ))
    (hB : ∀ j p q, AEStronglyMeasurable (B j p q) ((ν).prod σ))
    (hCsec : ∀ j p q, ∀ᵐ t ∂ν, (fun x ↦ C j p q (t, x)) =ᵐ[σ]
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ))
    (hBsec : ∀ j p q, ∀ᵐ t ∂ν, (fun x ↦ B j p q (t, x)) =ᵐ[σ]
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ))
    (x₀ : H) (hUweak : IsProductSpacetimeTransportWeakSolution C B U F x₀ a b)
    (hVweak : IsProductSpacetimeTransportWeakSolution C B V F x₀ a b) :
    ∀ p, U p =ᵐ[(ν).prod σ] V p := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨u, hUsec⟩ := exists_L2_sections_pi hU
  obtain ⟨v, hVsec⟩ := exists_L2_sections_pi hV
  obtain ⟨f, hFsec⟩ := exists_L2_sections_pi hF
  let L : ℝ≥0 := ⟨C₀, hC₀⟩
  have hentry (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (coefficientDerivativeBound_entry_le (A t) j p q).trans (hdiv t ht)
  have hu : IsSpacetimeTransportWeakSolution A u f x₀ a b :=
    (isProductSpacetimeTransportWeakSolution_iff A hA hab.le L hentry (Lp.memLp u) (Lp.memLp f) U F
      (fun p ↦ (hU p).aestronglyMeasurable) (fun p ↦ (hF p).aestronglyMeasurable)
      hUsec hFsec C B hC hB hCsec hBsec x₀).mp hUweak
  have hv : IsSpacetimeTransportWeakSolution A v f x₀ a b :=
    (isProductSpacetimeTransportWeakSolution_iff A hA hab.le L hentry (Lp.memLp v) (Lp.memLp f) V F
      (fun p ↦ (hV p).aestronglyMeasurable) (fun p ↦ (hF p).aestronglyMeasurable)
      hVsec hFsec C B hC hB hCsec hBsec x₀).mp hVweak
  have huv : u = v := eq_of_symmetric_spacetime_weak_equations A hA hab hsym hC₀ hL₀ hdiv hgrad
      u v f x₀ hu hv
  intro p
  apply ae_eq_of_ae_eq_sections (hU p).aestronglyMeasurable (hV p).aestronglyMeasurable
  filter_upwards [hUsec p, hVsec p] with t htU htV
  rw [huv] at htU
  exact htU.trans htV.symm

end PDE.Hyperbolic.FirstOrder
