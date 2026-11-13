/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.OneDimensionalConstructor
public import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous
import PDE.FDeriv.PartialDeriv.Support
import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Compact Lipschitz functions as global Sobolev elements

Compactly supported Lipschitz functions belong to `W¹ᵖ` in every finite
Euclidean dimension, for all `p ≥ 1`, including `p = ∞`. Rademacher's theorem
identifies the almost-everywhere classical partial derivatives. Their uniform
bounds and compact support put them in every `Lᵖ`, and coordinate integration
by parts supplies the weak identities across corners.

The one-dimensional real-line constructor also records the ordinary derivative
and its weak time-derivative identity through absolute continuity on intervals.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Sobolev

namespace PDE.Analysis.Calculus

/-- Coordinate derivatives of a compact Lipschitz function belong to every `Lᵖ`. -/
theorem memLp_partialDeriv_of_lipschitzWith_compactSupport
    {n : ℕ} {f : ℝ^n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f)
    (p : ℝ≥0∞) (i : Fin n) : MemLp (∂[i] f) p volume := by
  apply (hc.partialDeriv i).memLp_of_bound
    (measurable_fderiv_apply_const ℝ f (EuclideanSpace.single i 1)).aestronglyMeasurable K
  apply Eventually.of_forall
  intro x
  calc
    ‖(∂[i] f) x‖ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
      (fderiv ℝ f x).le_opNorm _
    _ ≤ K := by
      simpa using norm_fderiv_le_of_lipschitz ℝ hf


/-- The classical derivative of a compact Lipschitz real function lies in every `Lᵖ`. -/
theorem memLp_deriv_of_lipschitzWith_compactSupport {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (p : ℝ≥0∞) :
    MemLp (deriv f) p volume :=
  hc.deriv.memLp_of_bound (aestronglyMeasurable_deriv f volume) K
    (Filter.Eventually.of_forall fun _ ↦ norm_deriv_le_of_lipschitz hf)

/-- The almost-everywhere classical derivative is the global distributional derivative.
No differentiability is required at the exceptional points. -/
theorem hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    PDE.Analysis.Evolution.HasWeakTimeDerivativeOn univ f (deriv f) := by
  apply PDE.Analysis.Evolution.HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
  · exact hf.continuous.locallyIntegrable
  · exact (memLp_deriv_of_lipschitzWith_compactSupport hf hc 1).locallyIntegrable le_rfl
  · intro a b
    exact hf.lipschitzOnWith.absolutelyContinuousOnInterval
  · filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    exact hx.hasDerivAt

end PDE.Analysis.Calculus

namespace SobolevSpace.GraphSpace

/-- Classical partial derivatives are weak partial derivatives of Lipschitz functions. -/
theorem hasWeakDerivativeOn_partialDeriv_of_lipschitzWith
    {n : ℕ} {f : ℝ^n → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (i : Fin n) :
    HasWeakDerivativeOn univ [i] f (∂[i] f) := by
  apply (LipschitzWith.hasWeakDerivativeOn_lipschitzWeakCoord hf i).congr_ae
    EventuallyEq.rfl
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
  exact hx.lineDeriv_eq_fderiv

/-- The base and partial derivative rows of a compact Lipschitz function lie in every `Lᵖ`. -/
theorem firstOrderRows_memLp_of_lipschitzWith_compactSupport
    {n : ℕ} {f : ℝ^n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (p : ℝ≥0∞)
    (a : DerivIndex n 1) :
    MemLp (firstOrderRows f (fun i ↦ ∂[i] f) a) p (domainMeasure n univ) := by
  simp only [domainMeasure, Measure.restrict_univ]
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [firstOrderRows_baseIndex] using hf.continuous.memLp_of_hasCompactSupport hc
  · simpa only [firstOrderRows_singleDerivIndex] using
      PDE.Analysis.Calculus.memLp_partialDeriv_of_lipschitzWith_compactSupport hf hc p i

/-- The first-order rows satisfy the distributional identities even at corners. -/
theorem firstOrderRows_hasWeakDerivativeOn_of_lipschitzWith
    {n : ℕ} {f : ℝ^n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a : DerivIndex n 1) :
    HasWeakDerivativeOn univ a.toList f (firstOrderRows f (fun i ↦ ∂[i] f) a) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [firstOrderRows_baseIndex, baseIndex_toList] using
      hasWeakDerivativeOn_nil (hf.continuous.locallyIntegrable.locallyIntegrableOn univ)
  · simpa only [firstOrderRows_singleDerivIndex, singleDerivIndex_toList] using
      hasWeakDerivativeOn_partialDeriv_of_lipschitzWith hf i

/-- A compactly supported Lipschitz function determines a first-order Sobolev element
in every finite dimension, for every exponent `p`, including `p = ∞`. -/
noncomputable def mkW1pOfLipschitzCompactSupport
    {n : ℕ} {f : ℝ^n → ℝ} {K : ℝ≥0} (p : ℝ≥0∞)
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) : W^{1,p}(ℝ^n) :=
  mkWkpSpaceOnOfWeakDerivatives f (firstOrderRows f (fun i ↦ ∂[i] f))
    (firstOrderRows_baseIndex _ _)
    (firstOrderRows_memLp_of_lipschitzWith_compactSupport hf hc p)
    (firstOrderRows_hasWeakDerivativeOn_of_lipschitzWith hf)

/-- The stored coordinates are the supplied function and its classical partial
derivatives, up to Lebesgue null sets. -/
theorem mkW1pOfLipschitzCompactSupport_apply_ae
    {n : ℕ} {f : ℝ^n → ℝ} {K : ℝ≥0} (p : ℝ≥0∞)
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (a : DerivIndex n 1) :
    (((mkW1pOfLipschitzCompactSupport p hf hc : WkpAmbientOn n 1 p univ)
      a : DerivLp n p univ) : ℝ^n → ℝ) =ᵐ[volume]
      firstOrderRows f (fun i ↦ ∂[i] f) a := by
  simpa [mkW1pOfLipschitzCompactSupport, domainMeasure] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae f (firstOrderRows f (fun i ↦ ∂[i] f))
      (firstOrderRows_baseIndex _ _)
      (firstOrderRows_memLp_of_lipschitzWith_compactSupport hf hc p)
      (firstOrderRows_hasWeakDerivativeOn_of_lipschitzWith hf) a


/-- Transport `Lᵖ` membership to the one-dimensional Euclidean coordinate model. -/
theorem memLp_oneDimensionalPullback {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (volume : Measure ℝ)) :
    MemLp (oneDimensionalPullback f) p (volume : Measure (ℝ^1)) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hmp : MeasurePreserving e.symm
      (volume : Measure (ℝ^1)) (volume : Measure ℝ) :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  change MemLp (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))) p volume
  simpa [e] using hf.comp_measurePreserving hmp

/-- The two-row family works in any `Lᵖ`, not only `L¹`. -/
theorem w11Rows_memLp_of_memLp {f g : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p (volume : Measure ℝ)) (hg : MemLp g p (volume : Measure ℝ)) :
    ∀ a, MemLp (w11Rows f g a) p (domainMeasure 1 univ) := by
  intro a
  simp only [w11Rows, domainMeasure, Measure.restrict_univ]
  split_ifs
  · exact memLp_oneDimensionalPullback hf
  · exact memLp_oneDimensionalPullback hg

/-- The two graph rows of a compact Lipschitz function satisfy the weak identities. -/
theorem lipschitzCompactRows_weak {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    ∀ a, HasWeakDerivativeOn (n := 1) univ a.toList
      (oneDimensionalPullback f) (w11Rows f (deriv f) a) := by
  apply w11Rows_hasWeakDerivative f (deriv f)
  · exact hf.continuous.memLp_of_hasCompactSupport hc
  · exact PDE.Analysis.Calculus.memLp_deriv_of_lipschitzWith_compactSupport hf hc 1
  · intro a b
    exact hf.lipschitzOnWith.absolutelyContinuousOnInterval
  · filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
    exact hx.hasDerivAt

/-- A compact Lipschitz real function determines a global `H¹` element,
whose weak derivative is its almost-everywhere classical derivative. -/
def mkW12OfLipschitzCompactSupport {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) : W^{1,2}(ℝ^1) :=
  mkWkpSpaceOnOfWeakDerivatives
    (oneDimensionalPullback f) (w11Rows f (deriv f))
    (w11Rows_base f (deriv f))
    (w11Rows_memLp_of_memLp (hf.continuous.memLp_of_hasCompactSupport hc)
      (PDE.Analysis.Calculus.memLp_deriv_of_lipschitzWith_compactSupport hf hc 2))
    (lipschitzCompactRows_weak hf hc)

/-- The `H¹` element has exactly the supplied base row and its classical derivative row,
up to Lebesgue null sets in the one-dimensional Euclidean model. -/
theorem mkW12OfLipschitzCompactSupport_apply_ae {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) (a : DerivIndex 1 1) :
    (((mkW12OfLipschitzCompactSupport hf hc : WkpAmbientOn 1 1 2 univ)
      a : DerivLp 1 2 univ) : ℝ^1 → ℝ) =ᵐ[volume] w11Rows f (deriv f) a := by
  simpa [mkW12OfLipschitzCompactSupport, domainMeasure] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (oneDimensionalPullback f) (w11Rows f (deriv f))
      (w11Rows_base f (deriv f))
      (w11Rows_memLp_of_memLp (hf.continuous.memLp_of_hasCompactSupport hc)
        (PDE.Analysis.Calculus.memLp_deriv_of_lipschitzWith_compactSupport hf hc 2))
      (lipschitzCompactRows_weak hf hc) a

end SobolevSpace.GraphSpace
