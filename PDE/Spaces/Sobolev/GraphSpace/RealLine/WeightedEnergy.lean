/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.EvenSupport
public import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
import PDE.Analysis.Calculus.Parity
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# H¹ control from two weighted energies on a half interval

For an odd compact Lipschitz function, reflection recovers both global L²
norms from the positive half interval. Positive floors for the function and
derivative weights therefore control its H¹ norm. Only almost-everywhere
differentiability is needed, so the result applies across spline corners.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped NNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- The continuous real representative determines an H¹ graph element. -/
theorem realLineRepresentative_injective :
    Function.Injective realLineRepresentative := by
  intro U V h
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  apply oneDimensionalPushforwardL2.injective
  change realLineCoordinateCLM (baseIndex 1 1) U =
    realLineCoordinateCLM (baseIndex 1 1) V
  apply Lp.ext
  exact (realLineCoordinate_ae_representative U).trans
    (h ▸ (realLineCoordinate_ae_representative V).symm)

/-- The compact Lipschitz constructor recovers its original function
pointwise, including corners where its classical derivative may not exist. -/
theorem realLineRepresentative_mkW12OfLipschitzCompactSupport
    {f : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    realLineRepresentative (mkW12OfLipschitzCompactSupport hf hc) = f := by
  have hbase : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hc
  have hderiv := Calculus.memLp_deriv_of_lipschitzWith_compactSupport hf hc 2
  have hweak := Calculus.hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport hf hc
  have heq : mkW12OfLipschitzCompactSupport hf hc =
      mkW12OfWeakDerivative hbase hderiv hweak := by
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    apply Lp.ext
    have hleft := mkW12OfLipschitzCompactSupport_apply_ae hf hc (baseIndex 1 1)
    have hright := oneDimensionalPullbackL2_toLp_ae hbase
    simp only [domainMeasure, Measure.restrict_univ] at hright ⊢
    change _ =ᵐ[volume] (realLineH1Jet _ _ (baseIndex 1 1) : ℝ^1 → ℝ)
    rw [realLineH1Jet_base]
    rw [w11Rows_base] at hleft
    exact hleft.trans hright.symm
  rw [heq]
  exact realLineRepresentative_mkW12 hbase hderiv hweak hf.continuous

/-- Positive weight floors turn finite half-interval energy into a global
H¹ bound. The derivative is the almost-everywhere classical derivative of
the Lipschitz representative. -/
theorem norm_le_of_odd_lipschitz_weighted_energy
    (U : W^{1,2}(ℝ^1)) {φ σ : ℝ → ℝ} {L a b E : ℝ} {K : ℝ≥0}
    (ha : 0 < a) (hb : 0 < b) (hE : 0 ≤ E)
    (hU : LipschitzWith K (realLineRepresentative U))
    (hc : HasCompactSupport (realLineRepresentative U))
    (hodd : Function.Odd (realLineRepresentative U))
    (hsupport : ∀ x, L ≤ x → realLineRepresentative U x = 0)
    (hφ : ∀ x ∈ Ioo 0 L, a ≤ φ x) (hσ : ∀ x ∈ Ioo 0 L, b ≤ σ x)
    (hint : IntegrableOn
      (fun x ↦ realLineRepresentative U x ^ 2 * φ x) (Ioo 0 L))
    (hintX : IntegrableOn
      (fun x ↦ deriv (realLineRepresentative U) x ^ 2 * σ x) (Ioo 0 L))
    (henergy : (∫ x in Ioo 0 L, realLineRepresentative U x ^ 2 * φ x) +
      (∫ x in Ioo 0 L, deriv (realLineRepresentative U) x ^ 2 * σ x) ≤ E ^ 2) :
    ‖U‖ ≤ (√(2 / a) + √(2 / b)) * E := by
  let ω := realLineRepresentative U
  have hω := memLp_realLineRepresentative U
  have hη := Calculus.memLp_deriv_of_lipschitzWith_compactSupport hU hc 2
  have hweak := Calculus.hasWeakTimeDerivativeOn_of_lipschitzWith_compactSupport hU hc
  have hd : ∀ x, L ≤ x → deriv ω x = 0 := by
    intro x hx
    have hz : HasDerivWithinAt ω 0 (Ici x) x :=
      (hasDerivWithinAt_const x (Ici x) (0 : ℝ)).congr
        (fun y hy ↦ hsupport y (hx.trans hy)) (hsupport x hx)
    exact hz.deriv_eq_zero (uniqueDiffWithinAt_Ici x)
  have hnorms := eLpNorm_add_le_of_even_sq_weighted_energy ha hb hE
    (fun x ↦ by simp only [hodd x, neg_sq])
    (fun x ↦ congrArg (fun y : ℝ ↦ y ^ 2) (even_deriv_of_odd hodd x))
    hsupport hd hφ hσ hint hintX henergy
  have hgraph : U = mkW12OfWeakDerivative hω hη hweak :=
    realLineRepresentative_injective
      (realLineRepresentative_mkW12 hω hη hweak hU.continuous).symm
  rw [hgraph]
  change ‖realLineH1Jet (hω.toLp _) (hη.toLp _)‖ ≤ _
  apply (norm_realLineH1Jet_le _ _).trans
  rw [Lp.norm_toLp, Lp.norm_toLp]
  exact hnorms

end SobolevSpace.GraphSpace
