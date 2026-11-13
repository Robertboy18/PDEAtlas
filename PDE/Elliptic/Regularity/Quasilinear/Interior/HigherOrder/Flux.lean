/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.Spaces.Sobolev.Calculus.Composition.Flux.FirstOrder
import PDE.Spaces.Sobolev.Calculus.Composition.VectorValued.Nemytskii
import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Components
import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition

/-!
# Differentiating a nonlinear flux on an interior domain

The Banach-valued weak chain rule applies to the Sobolev gradient of an `H²`
field on any bounded open set. Commutation of its second weak derivatives
identifies the derivative of the flux with the linearized flux of each first
derivative. No extension atlas or boundary condition is needed.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A `C¹` Lipschitz flux of an `H²` gradient has `H¹` components. Its coordinate
derivative is the Fréchet derivative of the flux applied to the gradient
of the corresponding first derivative of the solution. -/
theorem exists_H1_linearizedFlux (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {A : ℝ^n → ℝ^n} (hA : ContDiff ℝ 1 A) {C : ℝ≥0} (hLip : LipschitzWith C A)
    (W : W^{2,2}(Ω)) :
    ∃ Q : Fin n → H¹(Ω),
      (∀ᵐ x ∂domainMeasure n Ω, ∀ i,
        wkpBaseCoordinateCLM (Q i) x =
          A (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x) i) ∧
      ∀ᵐ x ∂domainMeasure n Ω, ∀ i k,
        wkpCoordinateCLM (singleDerivIndex n k) (Q i) x =
          fderiv ℝ A (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x)
            (∇ (∂[k] W) x) i := by
  let D : TopologicalSpace.Opens (ℝ^n) := ⟨Ω, hΩ⟩
  let P : W^{1,2}(D; ℝ^n) := VectorValued.ofComponentsCLM (h2FirstDerivativeFamily W)
  let u := lowerOrderCLM (by omega : 1 ≤ 2) W
  have hP : (P.val (baseIndex n 1) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u := by
    filter_upwards [VectorValued.ofComponentsCLM_coordinate_ae
      (Ω := D) (h2FirstDerivativeFamily W) (baseIndex n 1),
      wkpGradientCLM_apply_ae u] with x hx hu
    rw [hx]
    exact PiLp.ext fun j ↦
      (congrArg (fun q : DerivLp n 2 Ω ↦ q x) (h2FirstDerivativeFamily_base W j)).trans
        (hu j).symm
  have hPd (k : Fin n) :
      (P.val (singleDerivIndex n k) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω]
        ∇ (∂[k] W) := by
    filter_upwards [VectorValued.ofComponentsCLM_coordinate_ae
      (Ω := D) (h2FirstDerivativeFamily W) (singleDerivIndex n k),
      wkpGradientCLM_apply_ae (∂[k] W)] with x hx hk
    rw [hx]
    apply PiLp.ext
    intro j
    rw [hk j]
    change W.val (derivativeWordIndex [j] _ (singleDerivIndex n k)) x =
      W.val (derivativeWordIndex [k] _ (singleDerivIndex n j)) x
    rw [derivativeWordIndex_singleDerivIndex_comm (n := n) (m := 2) j k (by norm_num)]
  have hbound (z : ℝ^n) : ‖fderiv ℝ A z‖ ≤ C :=
    norm_fderiv_le_of_lipschitz ℝ hLip
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hbase : MemLp (fun x ↦ A (P.val (baseIndex n 1) x)) 2 (domainMeasure n D) :=
    hLip.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp _)
  let R := VectorValued.compositionOfMemLp hA hbound P hbase
  let Q (i : Fin n) : H¹(Ω) := VectorValued.componentCLM i R
  refine ⟨Q, ?_, ?_⟩
  · have hQ := ae_all_iff.mpr fun i ↦
      VectorValued.componentCLM_apply_ae i R (baseIndex n 1)
    filter_upwards [hQ, VectorValued.compositionOfMemLp_base_ae hA hbound P hbase, hP]
      with x hx hR hPx
    intro i
    exact (hx i).trans (congrArg (fun z : ℝ^n ↦ z i) (hR.trans (congrArg A hPx)))
  · have hQ := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun k ↦
      VectorValued.componentCLM_apply_ae i R (singleDerivIndex n k)
    have hR := ae_all_iff.mpr fun k ↦
      VectorValued.compositionOfMemLp_derivative_ae hA hbound P hbase k
    filter_upwards [hQ, hR, hP, ae_all_iff.mpr hPd] with x hx hRx hPx hPdx
    intro i k
    exact (hx i k).trans (congrArg (fun z : ℝ^n ↦ z i)
      ((hRx k).trans (by rw [hPx, hPdx k])))

end PDE.Elliptic.Regularity.Quasilinear
