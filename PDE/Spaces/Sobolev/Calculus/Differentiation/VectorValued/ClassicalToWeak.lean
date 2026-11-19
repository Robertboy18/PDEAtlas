/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.FDeriv.Calculus

/-!
# Classical and weak derivatives of Banach-valued functions

A `C¹` function on an open domain has its classical partial derivatives as
weak derivatives. Testing against continuous linear functionals reduces
integration by parts to the scalar result. Uniqueness then identifies the
derivative coordinates of any Sobolev element represented by that function.

The chain rule and product rule both use this identification. It requires
no finite-dimensional assumption on the codomain.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A Banach-valued map that is `C¹` on an open domain has its classical coordinate
derivatives as weak derivatives on that domain. -/
theorem hasWeakDerivativeOn_of_contDiffOn_one {f : ℝ^n → F}
    (hf : ContDiffOn ℝ 1 f Ω) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] f (∂[i] f) := by
  have hlocal (x : ℝ^n) (hx : x ∈ Ω) : ContDiffAt ℝ 1 f x :=
    hf.contDiffAt (Ω.isOpen.mem_nhds hx)
  have hdcont : ContinuousOn (∂[i] f) Ω :=
    fun x hx ↦ (PDE.contDiffAt_partialDeriv 0 (hlocal x hx) i).continuousAt.continuousWithinAt
  apply (hasWeakDerivativeOn_iff_forall_dual
    (hf.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    (hdcont.locallyIntegrableOn Ω.isOpen.measurableSet)).mpr
  intro L
  have hs := SobolevSpace.hasWeakDerivativeOn_of_contDiffAt_one Ω.isOpen
    (fun x hx ↦ L.contDiff.contDiffAt.comp x (hlocal x hx)) i
  apply hs.congr_ae Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  exact L.partialDeriv_comp i ((hlocal x hx).differentiableAt one_ne_zero)

/-- A smooth representative of a first-order Sobolev element has the indicated classical
partial derivative as its derivative coordinate almost everywhere. -/
theorem coordinate_ae_partialDeriv_of_contDiffOn {p : ℝ≥0∞}
    (U : W^{1,p}(Ω; F)) {f : ℝ^n → F} (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f)
    (i : Fin n) :
    (U.val (singleDerivIndex n i) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      ∂[i] f := by
  have hw : HasWeakDerivativeOn Ω [i] f (U.val (singleDerivIndex n i)) :=
    by simpa only [singleDerivIndex_toList] using
      ((U.property (singleDerivIndex n i)).congr_ae hbase Filter.EventuallyEq.rfl)
  exact hw.ae_eq (hasWeakDerivativeOn_of_contDiffOn_one hf i)

end SobolevSpace.VectorValued
