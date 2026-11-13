/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Domain
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Operator
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# First-order Sobolev regularity of a nonlinear H² flux

The first derivatives of an `H²` field form a finite family of
`H¹` fields. A continuously differentiable Lipschitz flux acts on
this family by the finite-product chain rule. This yields the
flux in `H¹`, including a nonzero constant flux on bounded domains.

The extension operator is constructed from the boundary atlas. It is
used only to prove the chain rule; every resulting field remains in the
original Sobolev space.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full `H¹` family of first derivatives of an `H²` field. -/
def h2FirstDerivativeFamily (W : W^{2,2}(Ω)) (i : Fin n) :
    H¹(Ω) :=
  ∂[i] W

/-- The family has precisely the derivative coordinates of the order-one
restriction; no second Sobolev representative is introduced. -/
theorem h2FirstDerivativeFamily_base (W : W^{2,2}(Ω)) (i : Fin n) :
    wkpBaseCoordinateCLM (h2FirstDerivativeFamily W i) =
      wkpCoordinateCLM (singleDerivIndex n i) (lowerOrderCLM (by omega : 1 ≤ 2) W) := by
  change (h2FirstDerivativeFamily W i).val (baseIndex n 1) =
    (lowerOrderCLM (by omega : 1 ≤ 2) W).val (singleDerivIndex n i)
  simp only [h2FirstDerivativeFamily, partialDerivCLM,
    derivativeWordCLM_apply, derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
    DerivIndex.castOrder_singleDerivIndex]

/-- On a bounded extension domain, applying a `C¹` Lipschitz flux to the
gradient of an `H²` field gives `H¹` flux components with their
weak derivative columns. -/
theorem exists_H1_flux_of_H2 [Fact (0 < n)]
    (hΩ : Boundary.C1ExtensionAtlas n Ω)
    {A : ℝ^n → ℝ^n} (hA : ContDiff ℝ 1 A) {C : ℝ≥0} (hLip : LipschitzWith C A)
    (W : W^{2,2}(Ω)) :
    ∃ Q : Fin n → H¹(Ω),
      (∀ᵐ x ∂domainMeasure n Ω, ∀ i,
      wkpBaseCoordinateCLM (Q i) x =
        A (WithLp.toLp 2 (fun j ↦
          wkpCoordinateCLM (singleDerivIndex n j)
            (lowerOrderCLM (by omega : 1 ≤ 2) W) x)) i) ∧
      ∀ᵐ x ∂domainMeasure n Ω, ∀ i j,
        wkpCoordinateCLM (singleDerivIndex n j) (Q i) x =
          fderiv ℝ A (FiniteProductComposition.values (h2FirstDerivativeFamily W) x)
            (FiniteProductComposition.derivatives (h2FirstDerivativeFamily W) j x) i := by
  let := hΩ
  have := isFiniteMeasure_domainMeasure_of_isBounded hΩ.bounded
  let E := Extension.C1.operator (n := n) (p := 2) (Ω := Ω)
  have hAi (i : Fin n) : ContDiff ℝ 1 (fun z ↦ A z i) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp hA
  have hLipi (i : Fin n) : LipschitzWith C (fun z ↦ A z i) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [dist_eq_norm, dist_eq_norm]
    exact (PiLp.norm_apply_le (A z - A w) i).trans (hLip.norm_sub_le z w)
  have hDi (i : Fin n) (z : ℝ^n) : ‖fderiv ℝ (fun z ↦ A z i) z‖ ≤ C :=
    norm_fderiv_le_of_lipschitz ℝ (hLipi i)
  let Q (i : Fin n) : H¹(Ω) :=
    FiniteProductComposition.compositionOnOfExtension hΩ.isOpen E
      (by norm_num) (hAi i) (hDi i) (h2FirstDerivativeFamily W)
  refine ⟨Q, ?_, ?_⟩
  · have hQ := ae_all_iff.mpr fun i ↦
      FiniteProductComposition.compositionOnOfExtension_base_ae hΩ.isOpen E
        (by norm_num) (hAi i) (hDi i) (h2FirstDerivativeFamily W)
    filter_upwards [hQ] with x hx
    intro i
    rw [hx i]
    apply congrArg (fun z : ℝ^n ↦ A z i)
    exact PiLp.ext fun j ↦
      congrArg (fun f : DerivLp n 2 Ω ↦ f x) (h2FirstDerivativeFamily_base W j)
  · have hQ := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      FiniteProductComposition.compositionOnOfExtension_derivative_ae hΩ.isOpen E
        (by norm_num) (hAi i) (hDi i) (h2FirstDerivativeFamily W) j
    filter_upwards [hQ] with x hx
    intro i j
    rw [hx i j]
    have hd := ((EuclideanSpace.proj i).hasFDerivAt.comp
      (FiniteProductComposition.values (h2FirstDerivativeFamily W) x)
      (hA.differentiable_one _).hasFDerivAt).fderiv
    exact congrArg
      (fun D : ℝ^n →L[ℝ] ℝ ↦
        D (FiniteProductComposition.derivatives (h2FirstDerivativeFamily W) j x)) hd

end SobolevSpace.GraphSpace
