/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Equation
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bochner
import PDE.Analysis.MeasureTheory.StronglyMeasurable.Product

/-!
# The matrix diffusion equation on a common product null set

Joint representatives turn the native Sobolev equation into the full
matrix PDE for the product measure. The converse is used for uniqueness
among competitors satisfying the pointwise PDE. Coefficients need only be
jointly almost-everywhere measurable here; the joint Sobolev representatives come
from `Transport.Solution.Representatives`.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {n m : ℕ} {Ω : Set ℝ^n} {ε : ℝ}

/-- The product-a.e. matrix PDE and the native H¹ equation are
equivalent for joint representatives of the weak coordinates.
The parameter measure and the open spatial domain are arbitrary. -/
theorem transport_diffusion_equation_iff_product
    (hΩ : IsOpen Ω)
    (A : α → Fin n → Fin m → Fin m → W^{1,∞}(Ω))
    (B : Fin n → α × ℝ^n → Fin m → Fin m → ℝ)
    (hBmeas : ∀ j p q, AEStronglyMeasurable (fun z ↦ B j z p q)
      (μ.prod (domainMeasure n Ω)))
    (hB : ∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (U : Fin m → α → W^{3,2}(Ω))
    (G F : Fin m → α → W^{1,2}(Ω))
    (r : Fin m → DerivIndex n 3 → α × ℝ^n → ℝ)
    (v f : Fin m → α × ℝ^n → ℝ)
    (hrmeas : ∀ p a, AEStronglyMeasurable (r p a) (μ.prod (domainMeasure n Ω)))
    (hvmeas : ∀ p, AEStronglyMeasurable (v p) (μ.prod (domainMeasure n Ω)))
    (hfmeas : ∀ p, AEStronglyMeasurable (f p) (μ.prod (domainMeasure n Ω)))
    (hr : ∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ p a,
      r p a (t, x) = wkpCoordinateCLM a (U p t) x)
    (hv : ∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ p,
      v p (t, x) = wkpBaseCoordinateCLM (G p t) x)
    (hf : ∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ p,
      f p (t, x) = wkpBaseCoordinateCLM (F p t) x) :
    (∀ᵐ t ∂μ, ∀ p, G p t =
      ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p t) + F p t +
        vectorTransportH1CLM hΩ (A t)
          (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U q t)) p) ↔
    ∀ᵐ z ∂μ.prod (domainMeasure n Ω), ∀ p,
      v p z -
        ε * (∑ j, r p ((pairDerivIndex n j j).castOrder (by decide : 2 ≤ 3)) z) +
        (∑ j, ∑ q, B j z p q *
          r q ((singleDerivIndex n j).castOrder (by decide : 1 ≤ 3)) z) = f p z := by
  let P (t : α) : Prop := ∀ p, G p t =
    ε • higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) (U p t) + F p t +
      vectorTransportH1CLM hΩ (A t)
        (fun q ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U q t)) p
  let R (p : Fin m) (z : α × ℝ^n) : ℝ :=
    v p z -
      ε * (∑ j, r p ((pairDerivIndex n j j).castOrder (by decide : 2 ≤ 3)) z) +
      ∑ j, ∑ q, B j z p q *
        r q ((singleDerivIndex n j).castOrder (by decide : 1 ≤ 3)) z
  have hR (p : Fin m) : AEStronglyMeasurable (R p) (μ.prod (domainMeasure n Ω)) := by
    apply AEStronglyMeasurable.add
    · apply (hvmeas p).sub
      apply aestronglyMeasurable_const.mul
      exact Finset.aestronglyMeasurable_fun_sum _ fun j _ ↦ hrmeas p _
    · apply Finset.aestronglyMeasurable_fun_sum
      intro j _
      exact Finset.aestronglyMeasurable_fun_sum _ fun q _ ↦ (hBmeas j p q).mul (hrmeas q _)
  have hsection : (∀ᵐ t ∂μ, P t) ↔
      ∀ᵐ t ∂μ, ∀ᵐ x ∂domainMeasure n Ω, ∀ p, R p (t, x) = f p (t, x) := by
    constructor
    · intro h
      filter_upwards [h, hB, hr, hv, hf] with t ht hBt hrt hvt hft
      have heq := (transport_diffusion_equation_iff_ae hΩ (A t)
        (fun p ↦ U p t) (fun p ↦ G p t) (fun p ↦ F p t)).mp ht
      filter_upwards [heq, hBt, hrt, hvt, hft] with x hx hBx hrx hvx hfx
      intro p
      dsimp only [R]
      simp only [hvx, hfx, hrx, ← hBx]
      simpa only [wkpCoordinateCLM_apply, lowerOrderCLM_apply] using hx p
    · intro h
      filter_upwards [h, hB, hr, hv, hf] with t ht hBt hrt hvt hft
      apply (transport_diffusion_equation_iff_ae hΩ (A t)
        (fun p ↦ U p t) (fun p ↦ G p t) (fun p ↦ F p t)).mpr
      filter_upwards [ht, hBt, hrt, hvt, hft] with x hx hBx hrx hvx hfx
      intro p
      have hp := hx p
      dsimp only [R] at hp
      simp only [hvx, hfx, hrx, ← hBx] at hp
      simpa only [wkpCoordinateCLM_apply, lowerOrderCLM_apply] using hp
  constructor
  · intro h
    apply ae_all_iff.mpr
    intro p
    apply ae_eq_prod_of_ae_eq_sections (hR p) (hfmeas p)
    filter_upwards [hsection.mp h] with t ht
    exact ht.mono fun _ hx ↦ hx p
  · intro h
    exact hsection.mpr (Measure.ae_ae_of_ae_prod h)

end PDE.Parabolic.Systems
