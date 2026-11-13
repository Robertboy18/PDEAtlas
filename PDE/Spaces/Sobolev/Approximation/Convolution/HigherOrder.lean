/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceL2
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Analysis.Integration.ConvolutionDerivative
import PDE.Spaces.Sobolev.Approximation.Density.ClassicalDerivatives
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Sobolev regularity gained by convolution

A smooth compactly supported kernel sends arbitrary L² data into every
Hilbert Sobolev graph. Each output coordinate is convolution with a
derivative of the kernel. In particular no derivative or decay assumption is
imposed on the input.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open MeasureTheory PDE.Analysis GraphSpace
open scoped Convolution ENNReal Sobolev

variable {n : ℕ} {κ : ℝ^n → ℝ}

/-- Every derivative kernel is integrable, by smoothness and compact support. -/
theorem integrable_iteratedPartialDeriv_of_contDiff_compact
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hcs : HasCompactSupport κ)
    (α : List (Fin n)) :
    Integrable (iteratedPartialDeriv α κ) volume :=
  (PDE.contDiff_top_iteratedPartialDeriv hκ α).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedPartialDeriv hcs α)

/-- Differentiation of a convolution can be placed entirely on its smooth
compactly supported left factor. -/
theorem iteratedPartialDeriv_convolution_left
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hcs : HasCompactSupport κ)
    {f : ℝ^n → ℝ} (hf : LocallyIntegrable f volume) (α : List (Fin n)) :
    iteratedPartialDeriv α (κ ⋆ f) = (iteratedPartialDeriv α κ) ⋆ f := by
  have hcomm (a b : ℝ^n → ℝ) :
      a ⋆ b = b ⋆[ContinuousLinearMap.mul ℝ ℝ] a := by
    exact convolution_symm (ContinuousLinearMap.mul ℝ ℝ)
      (by ext; rfl)
  rw [hcomm κ f, hcomm (iteratedPartialDeriv α κ) f]
  exact funext (convolution_iteratedPartialDeriv_right f κ hf hcs hκ α)

/-- The bounded ambient tuple of convolution by each derivative kernel. -/
def convolutionHkAmbientCLM (r : ℕ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hcs : HasCompactSupport κ) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ] WkpAmbientOn n r 2 Set.univ :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : DerivIndex n r ↦ DerivLp n 2 Set.univ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a ↦
        wholeSpaceL2Equiv.symm.toLinearIsometry.toContinuousLinearMap.comp
        (convolutionL2CLM (iteratedPartialDeriv a.toList κ)
          (integrable_iteratedPartialDeriv_of_contDiff_compact hκ hcs a.toList)))

/-- Each ambient row is the derivative-kernel convolution in L². -/
theorem convolutionHkAmbientCLM_coordinate (r : ℕ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hcs : HasCompactSupport κ) (u : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (a : DerivIndex n r) :
    convolutionHkAmbientCLM r hκ hcs u a =
      wholeSpaceL2Equiv.symm (convolutionL2CLM (iteratedPartialDeriv a.toList κ)
        (integrable_iteratedPartialDeriv_of_contDiff_compact hκ hcs a.toList) u) :=
  rfl

/-- Almost everywhere, each constructed row is a classical derivative of the
same smooth convolution. -/
theorem convolutionHkAmbientCLM_coordinate_ae (r : ℕ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hcs : HasCompactSupport κ)
    (u : Lp ℝ 2 (volume : Measure (ℝ^n))) (a : DerivIndex n r) :
    (convolutionHkAmbientCLM r hκ hcs u a : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
      iteratedPartialDeriv a.toList (κ ⋆ (u : ℝ^n → ℝ)) := by
  simp only [domainMeasure, Measure.restrict_univ]
  rw [iteratedPartialDeriv_convolution_left hκ hcs
      ((Lp.memLp u).locallyIntegrable (by norm_num)) a.toList]
  rw [convolutionHkAmbientCLM_coordinate]
  exact ((wholeSpaceL2Equiv_ae _).symm.trans
    (by
      simpa using convolutionL2CLM_ae_eq (iteratedPartialDeriv a.toList κ)
        (integrable_iteratedPartialDeriv_of_contDiff_compact hκ hcs a.toList) u))

/-- The constructed convolution rows satisfy the weak derivative graph. -/
theorem convolutionHkAmbientCLM_mem (r : ℕ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hcs : HasCompactSupport κ) (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    convolutionHkAmbientCLM r hκ hcs u ∈ wkpSubmoduleOn n r 2 Set.univ := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (κ ⋆ (u : ℝ^n → ℝ)) :=
    hcs.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hκ
      ((Lp.memLp u).locallyIntegrable (by norm_num))
  intro a
  apply (hasWeakDerivativeOn_congr_ae
    (by simpa only [baseIndex_toList, iteratedPartialDeriv] using
      convolutionHkAmbientCLM_coordinate_ae r hκ hcs u (baseIndex n r))
    (convolutionHkAmbientCLM_coordinate_ae r hκ hcs u a)).mpr
  exact hasWeakDerivativeOn_iteratedPartialDeriv hs a.toList

/-- Convolution by a smooth compactly supported kernel maps L² continuously
into every finite-order Hilbert Sobolev graph. -/
def convolutionHkCLM (r : ℕ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hcs : HasCompactSupport κ) :
    Lp ℝ 2 (volume : Measure (ℝ^n)) →L[ℝ] W^{r,2}(ℝ^n) :=
  (convolutionHkAmbientCLM r hκ hcs).codRestrict
    (wkpSubmoduleOn n r 2 Set.univ) (convolutionHkAmbientCLM_mem r hκ hcs)

/-- The base row of the regularity-gaining map is the original L² convolution. -/
theorem convolutionHkCLM_base (r : ℕ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hcs : HasCompactSupport κ) (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    wkpBaseCoordinateCLM (convolutionHkCLM r hκ hcs u) =
      wholeSpaceL2Equiv.symm
        (convolutionL2CLM κ (hκ.continuous.integrable_of_hasCompactSupport hcs) u) := by
  change convolutionHkAmbientCLM r hκ hcs u (baseIndex n r) = _
  simp only [convolutionHkAmbientCLM_coordinate, baseIndex_toList, iteratedPartialDeriv]

end SobolevSpace.Approximation
