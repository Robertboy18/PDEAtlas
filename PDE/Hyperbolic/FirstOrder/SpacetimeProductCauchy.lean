/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeProductFormulation
public import PDE.Hyperbolic.FirstOrder.DistributionalUniqueness
import PDE.Hyperbolic.FirstOrder.ProductL2Uniqueness
import PDE.Analysis.MeasureTheory.Lp.SectionReconstruction

/-!
# The symmetric L² Cauchy solution with prescribed spacetime forcing

A square-integrable forcing on time-space determines a Bochner L² class of spatial
sections. The symmetric Cauchy theorem constructs the continuous spatial-L²
solution for that class, with its prescribed initial value and energy estimate.
The squared forcing norm is exactly the sum of the coordinate product integrals.

Joint representatives of the state and Sobolev coefficients satisfy the product-measure
equation for the supplied forcing, including its initial boundary term. Every joint
product-L² state satisfying the same equation agrees with the constructed state almost
everywhere.

The initial value belongs to the continuous L² curve; arbitrary joint representatives
have no prescribed values on the initial time slice.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology Distributions ContDiff

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "ν" => volume.restrict (Ioc a b)
local notation "σ" => domainMeasure n univ

/-- Prescribed product-L² forcing gives a continuous L² Cauchy solution with its initial
value, an energy estimate, and joint state and coefficient representatives satisfying
the full product-measure spacetime equation. The forcing contribution to the energy
is the sum of the integrals of coordinate squares, with no component-count factor.
Bochner sections of the forcing are constructed from `hF`.

Every joint product-L² competitor satisfying the same equation with this forcing and
initial boundary datum agrees almost everywhere with the constructed state. Equality of a supplied
competing Bochner class is also retained.

Initial values belong to the continuous L² curve and enter the equation through its
boundary term. The supplied forcing is only required to belong to product L²; joint
strong measurability is asserted for the chosen state and coefficient representatives.
Arbitrary joint representatives need not take the initial datum's value on its time slice. -/
theorem exists_symmetric_product_spacetime_cauchy_l2_unique
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q,
      ContinuousOn (fun t ↦ (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q, (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
      (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    {C₀ L₀ : ℝ} (hC₀ : 0 ≤ C₀) (hL₀ : 0 ≤ L₀)
    (hdiv : ∀ t ∈ Icc a b, coefficientDerivativeBound (A t) ≤ C₀)
    (hgrad : ∀ t ∈ Icc a b, coefficientGradientBound (A t) ≤ L₀) (x₀ : H) (F : Fin m → ℝ × ℝ^n → ℝ)
    (hF : ∀ p, MemLp (F p) 2 ((ν).prod σ)) :
    ∃ (u : ℝ → H) (hu : MemLp u 2 ν)
      (U : Fin m → ℝ × ℝ^n → ℝ)
      (C B : Fin n → Fin m → Fin m → ℝ × ℝ^n → ℝ),
      ContinuousOn u (Icc a b) ∧ u a = x₀ ∧
      (∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
        (‖x₀‖ ^ 2 + ∑ p, ∫ z, (F p z) ^ 2 ∂(ν).prod σ) *
          Real.exp ((C₀ + 1) * (t - a))) ∧
      (∀ p, StronglyMeasurable (U p) ∧ MemLp (U p) 2 ((ν).prod σ) ∧
        ∀ᵐ t ∂ν, (fun x ↦ U p (t, x)) =ᵐ[σ] (u t p : ℝ^n → ℝ)) ∧
      (∀ j p q, StronglyMeasurable (C j p q) ∧ StronglyMeasurable (B j p q) ∧
        (∀ᵐ t ∂ν, (fun x ↦ C j p q (t, x)) =ᵐ[σ]
          ((A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) : ℝ^n → ℝ)) ∧
        (∀ᵐ t ∂ν, (fun x ↦ B j p q (t, x)) =ᵐ[σ]
          ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j) : ℝ^n → ℝ))) ∧
      IsProductSpacetimeTransportWeakSolution C B U F x₀ a b ∧
      (∀ (v : Lp H 2 ν) (W : Fin m → ℝ × ℝ^n → ℝ),
        (∀ p, AEStronglyMeasurable (W p) ((ν).prod σ)) →
        (∀ p, ∀ᵐ t ∂ν, (fun x ↦ W p (t, x)) =ᵐ[σ] (v t p : ℝ^n → ℝ)) →
        IsProductSpacetimeTransportWeakSolution C B W F x₀ a b → v = hu.toLp u) ∧
      ∀ W : Fin m → ℝ × ℝ^n → ℝ,
        (∀ p, MemLp (W p) 2 ((ν).prod σ)) →
        IsProductSpacetimeTransportWeakSolution C B W F x₀ a b →
        ∀ p, W p =ᵐ[(ν).prod σ] U p := by
  classical
  let : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨f, hFsec⟩ := exists_L2_sections_pi hF
  have hfnorm : ‖f‖ ^ 2 = ∑ p, ∫ z, (F p z) ^ 2 ∂(ν).prod σ := by
    rw [Lp.norm_sq_eq_integral_norm_sq,
      integral_congr_ae (ae_of_all _ fun t ↦ PiLp.norm_sq_eq_of_L2 _ (f t)),
      integral_finsetSum _ fun p _ ↦ ((Lp.memLp f).eval_piLp p).norm.integrable_sq]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [integral_prod_real (fun z ↦ (F p z) ^ 2) (hF p).integrable_sq]
    refine integral_congr_ae ?_
    filter_upwards [hFsec p] with t ht
    rw [Lp.norm_sq_eq_integral_sq]
    exact integral_congr_ae (ht.symm.fun_comp fun y : ℝ ↦ y ^ 2)
  obtain ⟨u, hu, hucont, hua, huenergy, _huseparated, hufull, huunique⟩ :=
    exists_symmetric_spacetime_cauchy_l2_unique A hA hab hsym hC₀ hL₀ hdiv hgrad x₀ f
  let L : ℝ≥0 := ⟨C₀, hC₀⟩
  have hentry (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (coefficientDerivativeBound_entry_le (A t) j p q).trans (hdiv t ht)
  obtain ⟨U, _G, C, B, hU, _hG, hcoeff, _hproductG⟩ :=
    exists_product_representatives_of_spacetime_weak_solution A hA hab.le L hentry
      hu (Lp.memLp f) x₀ hufull
  have hC j p q := (hcoeff j p q).1.aestronglyMeasurable (μ := (ν).prod σ)
  have hB j p q := (hcoeff j p q).2.1.aestronglyMeasurable (μ := (ν).prod σ)
  have hCsec j p q := (hcoeff j p q).2.2.1
  have hBsec j p q := (hcoeff j p q).2.2.2
  have hproduct : IsProductSpacetimeTransportWeakSolution C B U F x₀ a b :=
    (isProductSpacetimeTransportWeakSolution_iff A hA hab.le L hentry hu (Lp.memLp f) U F
      (fun p ↦ (hU p).1.aestronglyMeasurable) (fun p ↦ (hF p).aestronglyMeasurable)
      (fun p ↦ (hU p).2.2) hFsec C B hC hB hCsec hBsec x₀).mpr hufull
  refine ⟨u, hu, U, C, B, hucont, hua, fun t ht ↦ ?_, hU, hcoeff, hproduct,
    fun v W hW hWsec hv ↦ huunique v ?_, fun W hW hWweak ↦ ?_⟩
  · simpa only [hfnorm] using huenergy t ht
  · exact (isProductSpacetimeTransportWeakSolution_iff A hA hab.le L hentry (Lp.memLp v)
      (Lp.memLp f) W F hW (fun p ↦ (hF p).aestronglyMeasurable) hWsec hFsec C B hC hB hCsec
      hBsec x₀).mp hv
  · exact ae_eq_of_symmetric_product_spacetime_weak_equations A hA hab hsym hC₀ hL₀ hdiv hgrad
      W U F hW (fun p ↦ (hU p).2.1) hF C B hC hB hCsec hBsec x₀ hWweak hproduct

end PDE.Hyperbolic.FirstOrder
