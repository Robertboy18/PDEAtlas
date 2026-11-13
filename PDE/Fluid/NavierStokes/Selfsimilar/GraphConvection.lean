/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphLinearization
public import PDE.Fluid.NavierStokes.Nonlinearity.BoundedTransport

/-!
# The weak convection form as a transport pairing

The weak convection form `convectionForm b` of the graph linearization moves the derivative of
the coefficient `b` onto both fields. When the components of `b` are the base functions of
fields `B i ∈ W^{1,∞}(ℝⁿ)`, the Leibniz rule moves it back:

`convectionForm b h w = Σᵢⱼ ∫ (bⱼ ∂ⱼhᵢ + (∂ⱼBᵢ) hⱼ) wᵢ`

for all `h, w ∈ H¹`. The right side is the `L²` pairing of `w` with the bounded transport
`(b·∇)h + (h·∇)B` of `BoundedTransport.transport`, whose stretching coefficients are
`cᵢⱼ = ∂ⱼBᵢ`. Against a smooth compactly supported test field `φ` both the convection form and
the gradient form become integrals against `φ`: the convection form is
`Σᵢⱼ ∫ bⱼ ∂ⱼhᵢ φᵢ + Σᵢⱼ ∫ (∂ⱼBᵢ) hⱼ φᵢ` and the gradient form is `-∫ h·Δφ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Selfsimilar

open Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- For a coefficient `b` whose components are the base functions of `B i ∈ W^{1,∞}`, the weak
convection form is the `L²` pairing with the bounded transport whose stretching coefficients
are `c j i = ∂ᵢBⱼ`: `convectionForm b h w = Σᵢ ⟪(B h)ᵢ, wᵢ⟫` for all `h, w ∈ H¹`. -/
theorem convectionForm_eq_sum_inner (B : Fin n → W^{1,∞}(ℝ^n)) {b : Fin n → DerivLp n ∞ univ}
    {c : Fin n → Fin n → DerivLp n ∞ univ} (hB : ∀ i, wkpBaseCoordinateCLM (B i) = b i)
    (hc : ∀ j i, c j i = wkpCoordinateCLM (singleDerivIndex n i) (B j)) (h w : H) :
    convectionForm b h w = ∑ i, inner ℝ (wkpBaseCoordinateCLM (BoundedTransport.transport b c h i))
      (wkpBaseCoordinateCLM (w i)) := by
  have hibp (i j : Fin n) :
      -inner ℝ (b i • wkpCoordinateCLM (singleDerivIndex n j) (h j)) (wkpBaseCoordinateCLM (w i)) -
        inner ℝ (b i • wkpBaseCoordinateCLM (h j)) (wkpCoordinateCLM (singleDerivIndex n j) (w i)) =
      inner ℝ (c i j • wkpBaseCoordinateCLM (h j)) (wkpBaseCoordinateCLM (w i)) := by
    have hl : inner ℝ (wkpBaseCoordinateCLM (B i) •
          wkpCoordinateCLM (singleDerivIndex n j) (h j)) (wkpBaseCoordinateCLM (w i)) +
        inner ℝ (wkpBaseCoordinateCLM (B i) • wkpCoordinateCLM (singleDerivIndex n j) (w i))
          (wkpBaseCoordinateCLM (h j)) =
        -inner ℝ (wkpCoordinateCLM (singleDerivIndex n j) (B i) • wkpBaseCoordinateCLM (h j))
          (wkpBaseCoordinateCLM (w i)) :=
      inner_mul_deriv_add_inner_mul_deriv_univ (B i) j (h j) (w i)
    have hs : inner ℝ (b i • wkpBaseCoordinateCLM (h j))
        (wkpCoordinateCLM (singleDerivIndex n j) (w i)) =
        inner ℝ (b i • wkpCoordinateCLM (singleDerivIndex n j) (w i))
          (wkpBaseCoordinateCLM (h j)) := by
      rw [inner_lpSMul_left_eq_right, real_inner_comm]
    rw [hs, hc, ← hB i]
    linarith
  rw [convectionForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [BoundedTransport.transport_base, BoundedTransport.scalarTransport_apply, sum_inner]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [mulLpLeft_apply]
  rw [inner_add_left, ← hibp i j]
  ring

/-- Against a smooth compactly supported test field the weak convection form is the integral
`Σᵢ ∫ (B h)ᵢ φᵢ` of the bounded transport, for coefficients `bᵢ` that are the base functions
of `B i ∈ W^{1,∞}` and stretching coefficients `c j i = ∂ᵢBⱼ`. -/
theorem convectionForm_testFieldH1 (B : Fin n → W^{1,∞}(ℝ^n)) {b : Fin n → DerivLp n ∞ univ}
    {c : Fin n → Fin n → DerivLp n ∞ univ} (hB : ∀ i, wkpBaseCoordinateCLM (B i) = b i)
    (hc : ∀ j i, c j i = wkpCoordinateCLM (singleDerivIndex n i) (B j)) (h : H)
    {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    convectionForm b h (testFieldH1 φ hφ hcφ) = ∑ i, ∫ x,
      (wkpBaseCoordinateCLM (BoundedTransport.transport b c h i) : ℝ^n → ℝ) x * φ x i := by
  rw [convectionForm_eq_sum_inner B hB hc]
  exact Finset.sum_congr rfl fun i _ ↦
    inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _) (testFieldH1_base_ae hφ hcφ i)

/-- Against a smooth compactly supported test field the weak convection form, for coefficients
`bᵢ` that are the base functions of `B i ∈ W^{1,∞}`, is
`Σᵢⱼ ∫ bⱼ ∂ⱼhᵢ φᵢ + Σᵢⱼ ∫ (∂ⱼBᵢ) hⱼ φᵢ`. -/
theorem convectionForm_testFieldH1_eq_sum_integral (B : Fin n → W^{1,∞}(ℝ^n))
    {b : Fin n → DerivLp n ∞ univ} (hB : ∀ i, wkpBaseCoordinateCLM (B i) = b i) (h : H)
    {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ) :
    convectionForm b h (testFieldH1 φ hφ hcφ) =
      (∑ i, ∑ j, ∫ x, (b j : ℝ^n → ℝ) x *
        (wkpCoordinateCLM (singleDerivIndex n j) (h i) : ℝ^n → ℝ) x * φ x i) +
      ∑ i, ∑ j, ∫ x, (wkpCoordinateCLM (singleDerivIndex n j) (B i) : ℝ^n → ℝ) x *
        (wkpBaseCoordinateCLM (h j) : ℝ^n → ℝ) x * φ x i := by
  rw [convectionForm_eq_sum_inner B (c := fun j i ↦ wkpCoordinateCLM (singleDerivIndex n i) (B j))
    hB (fun _ _ ↦ rfl), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [BoundedTransport.transport_base, BoundedTransport.scalarTransport_apply, sum_inner,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hbase := testFieldH1_base_ae hφ hcφ i
  have h1 := mulLpLeft_apply_ae (b j) (wkpCoordinateCLM (singleDerivIndex n j) (h i))
  have h2 := mulLpLeft_apply_ae (wkpCoordinateCLM (singleDerivIndex n j) (B i))
    (wkpBaseCoordinateCLM (h j))
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2
  rw [inner_add_left, inner_eq_integral_mul_of_ae h1 hbase,
    inner_eq_integral_mul_of_ae h2 hbase]

/-- Against a smooth compactly supported test field the gradient form is `-Σᵢ ∫ hᵢ Δφᵢ`. -/
theorem gradientForm_testFieldH1 (h : H) {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hcφ : HasCompactSupport φ) :
    gradientForm h (testFieldH1 φ hφ hcφ) = -∑ i, ∫ x,
      (wkpBaseCoordinateCLM (h i) : ℝ^n → ℝ) x * PDE.laplacian (fun y ↦ φ y i) x := by
  rw [gradientForm_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hf : ContDiff ℝ ∞ (fun y ↦ φ y i) := contDiff_component hφ i
  have hfc : HasCompactSupport (fun y ↦ φ y i) := hasCompactSupport_component hcφ i
  have hint : ∀ j : Fin n, Integrable (fun x ↦ (wkpBaseCoordinateCLM (h i) : ℝ^n → ℝ) x *
      PDE.partialDeriv j (fun z ↦ PDE.partialDeriv j (fun y ↦ φ y i) z) x) volume := fun j ↦
    integrable_base_mul (h i)
      ((PDE.contDiff_top_partialDeriv (i := j)
        (PDE.contDiff_top_partialDeriv (i := j) hf)).continuous)
      ((hfc.partialDeriv j).partialDeriv j)
  simp only [PDE.laplacian, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ ↦ hint j, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_base_mul_partialDeriv (h i) j (PDE.contDiff_top_partialDeriv (i := j) hf)
    (hfc.partialDeriv j), neg_neg]
  exact inner_eq_integral_mul_of_ae (Filter.EventuallyEq.refl _ _)
    (testFieldH1_partial_ae hφ hcφ i j)

end NavierStokes.Selfsimilar
