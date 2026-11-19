/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized

/-!
# Coordinates of localized difference-quotient tests

The forward field `η² Dₖʰ(E₀u)` of an `H¹₀(Ω)` function `u` extended by zero, and the signed
backward test `-Dₖ^{-h}(η² Dₖʰ(E₀u))`, the test function of the interior regularity proof in Evans
§6.3.1, have their Sobolev coordinates given by the product rule and translation. These identities
hold independently of any equation or coefficient field.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, pp. 328-331, for the test
  function `v = -D_k^{-h}(ζ² D_k^h u)` (11).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace Sobolev
open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Derivative coordinate of Evans' signed backward test. -/
theorem derivCoord_backwardLocalizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω)
    (i : Fin n) :
    derivCoordCLM (n := n) (Ω := Ω) i
        (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift) =
      -restrictDerivLp (n := n) (p := 2)
        (subset_univ Ω)
        (differenceQuotientLp 2 k (-h)
          (((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet
            (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹(ℝ^n)) :
              WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))) := by
  simpa only [derivCoordCLM_apply] using
    backwardLocalizedDifferenceH10_coordinate hΩopen η hηΩ k h u hδ hshift
      (singleDerivIndex n i)

/-- Base coordinate of Evans' signed backward test. -/
theorem baseCoord_backwardLocalizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω))
    {δ : ℝ} (hδ : 0 < δ)
    (hshift : Metric.cthickening δ
      (shiftedSupport (coordinateStep k (-h)) (tsupport η.toFun)) ⊆ Ω) :
    baseCoordCLM (n := n) (Ω := Ω)
        (backwardLocalizedDifferenceH10 hΩopen η hηΩ k h u hδ hshift) =
      -restrictDerivLp (n := n) (p := 2)
        (subset_univ Ω)
        (differenceQuotientLp 2 k (-h)
          (((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω) hΩopen.measurableSet
            (localizedDifferenceH10 hΩopen η hηΩ k h u) : H¹(ℝ^n)) :
              WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))) := by
  simpa only [baseCoordCLM_apply] using
    backwardLocalizedDifferenceH10_coordinate hΩopen η hηΩ k h u hδ hshift
      (baseIndex n 1)

/-- Exact Sobolev product-rule expansion of a derivative of Evans'
localized forward field `η² Dₖʰ(E₀u)`.  The first summand is the
cutoff-weighted principal field; the second is the derivative-of-cutoff
error. -/
theorem derivCoord_localizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω))
    (i : Fin n) :
    let U : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet u
    derivCoordCLM (n := n) (Ω := Ω) i
        (localizedDifferenceH10 hΩopen η hηΩ k h u) =
      testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) •
          restrictDerivLp (n := n) (p := 2)
            (subset_univ Ω)
            (differenceQuotientLp 2 k h
              ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))) +
        partialTestFunctionLpTop (n := n) (Ω := Ω)
            (squaredCutoff η) i •
          restrictDerivLp (n := n) (p := 2)
            (subset_univ Ω)
            (differenceQuotientLp 2 k h
              ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))) := by
  dsimp only
  change
    ((((localizedDifferenceH10 hΩopen η hηΩ k h u :
      H¹₀(Ω)) : H¹(Ω)) :
        WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)) = _
  rw [localizedDifferenceH10_coordinate]
  simp [cutoffLpAt, restrictAmbient_apply]
  simp only [MeasureTheory.Lp.smul_comm]

/-- Base coordinate of Evans' localized forward field. -/
theorem baseCoord_localizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω)) :
    let U : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet u
    baseCoordCLM (n := n) (Ω := Ω)
        (localizedDifferenceH10 hΩopen η hηΩ k h u) =
      testFunctionLpTop (n := n) (Ω := Ω) (squaredCutoff η) •
        restrictDerivLp (n := n) (p := 2)
          (subset_univ Ω)
          (differenceQuotientLp 2 k h
            ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))) := by
  dsimp only
  change
    ((((localizedDifferenceH10 hΩopen η hηΩ k h u :
      H¹₀(Ω)) : H¹(Ω)) :
        WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) = _
  rw [localizedDifferenceH10_coordinate]
  simp [cutoffLpAt, restrictAmbient_apply]
  simp only [MeasureTheory.Lp.smul_comm]

/-- Whole-space form of the localized derivative expansion.  Compact
support of the cutoff removes every apparent boundary contribution when the
two local product-rule terms are extended by zero. -/
theorem zeroExtendedDeriv_localizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω))
    (i : Fin n) :
    let U : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet u
    let w := localizedDifferenceH10 hΩopen η hηΩ k h u
    let Z : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet w
    ((Z : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)) =
      testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) •
          differenceQuotientLp 2 k h
            ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i)) +
        partialTestFunctionLpTop (n := n) (Ω := Set.univ)
            (squaredCutoff η) i •
          differenceQuotientLp 2 k h
            ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) := by
  dsimp only
  let E0 := Extension.Lp.zeroExtendLp
    (n := n) (p := 2) (Ω := Ω) hΩopen.measurableSet
  have hlocal := derivCoord_localizedDifferenceH10
    hΩopen η hηΩ k h u i
  dsimp only at hlocal
  have hz := congrArg E0 hlocal
  rw [map_add] at hz
  have hη2Ω : tsupport (squaredCutoff η).toFun ⊆ Ω :=
    (tsupport_squaredCutoff_subset η).trans hηΩ
  have hfirst := Extension.Lp.zeroExtendLp_testFunction_smul_restrict
    (n := n) (Ω := Ω) hΩopen.measurableSet
    (squaredCutoff η) hη2Ω
    (differenceQuotientLp 2 k h
      ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet u : H¹(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))))
  have hdηΩ :
      tsupport
        ((_root_.TestFunction.lineDerivCLM ℝ
            (EuclideanSpace.single i (1 : ℝ)) (squaredCutoff η) :
          𝓓((⊤ : Opens (ℝ^n)), ℝ)).toFun) ⊆ Ω := by
    have hfun :
        ((_root_.TestFunction.lineDerivCLM ℝ
            (EuclideanSpace.single i (1 : ℝ)) (squaredCutoff η) :
          𝓓((⊤ : Opens (ℝ^n)), ℝ)).toFun) =
          fun x ↦ (∂[i]
            (squaredCutoff η).toFun) x := by
      funext x
      change (_root_.TestFunction.lineDerivCLM ℝ
          (EuclideanSpace.single i (1 : ℝ)) (squaredCutoff η) :
        𝓓((⊤ : Opens (ℝ^n)), ℝ)) x =
        (∂[i] (squaredCutoff η).toFun) x
      rw [_root_.TestFunction.lineDerivCLM_apply_of_le (by simp)]
      rw [((squaredCutoff η).contDiff.differentiable
        (by simp)).differentiableAt.lineDeriv_eq_fderiv]
      rfl
    rw [hfun]
    simpa only [partialDeriv] using
      (tsupport_fderiv_apply_subset ℝ (f := (squaredCutoff η).toFun)
        (EuclideanSpace.single i (1 : ℝ))).trans hη2Ω
  have hsecond := Extension.Lp.zeroExtendLp_testFunction_smul_restrict
    (n := n) (Ω := Ω) hΩopen.measurableSet
    (_root_.TestFunction.lineDerivCLM ℝ
      (EuclideanSpace.single i (1 : ℝ)) (squaredCutoff η)) hdηΩ
    (differenceQuotientLp 2 k h
      ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet u : H¹(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))))
  change E0
      (derivCoordCLM (n := n) (Ω := Ω) i
        (localizedDifferenceH10 hΩopen η hηΩ k h u)) = _
  rw [hz, hfirst]
  simpa only [partialTestFunctionLpTop] using congrArg
    (fun q ↦ testFunctionLpTop (n := n) (Ω := Set.univ)
      (squaredCutoff η) •
        differenceQuotientLp 2 k h
          ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
            hΩopen.measurableSet u : H¹(ℝ^n)) :
              WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n i))) + q)
    hsecond

/-- Whole-space base coordinate of the localized field.  This complements
`zeroExtendedDeriv_localizedDifferenceH10` and makes its complete `H¹` norm
available without any loss at the domain boundary. -/
theorem zeroExtendedBase_localizedDifferenceH10
    (hΩopen : IsOpen Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hηΩ : tsupport η.toFun ⊆ Ω)
    (k : Fin n) (h : ℝ)
    (u : H¹₀(Ω)) :
    let U : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet u
    let w := localizedDifferenceH10 hΩopen η hηΩ k h u
    let Z : H¹(ℝ^n) := ZeroTrace.zeroExtendH10
      (n := n) (Ω := Ω) hΩopen.measurableSet w
    ((Z : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) =
      testFunctionLpTop (n := n) (Ω := Set.univ) (squaredCutoff η) •
        differenceQuotientLp 2 k h
          ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1)) := by
  dsimp only
  let E0 := Extension.Lp.zeroExtendLp
    (n := n) (p := 2) (Ω := Ω) hΩopen.measurableSet
  have hlocal := baseCoord_localizedDifferenceH10
    hΩopen η hηΩ k h u
  dsimp only at hlocal
  have hz := congrArg E0 hlocal
  have hη2Ω : tsupport (squaredCutoff η).toFun ⊆ Ω :=
    (tsupport_squaredCutoff_subset η).trans hηΩ
  have hproduct := Extension.Lp.zeroExtendLp_testFunction_smul_restrict
    (n := n) (Ω := Ω) hΩopen.measurableSet
    (squaredCutoff η) hη2Ω
    (differenceQuotientLp 2 k h
      ((((ZeroTrace.zeroExtendH10 (n := n) (Ω := Ω)
        hΩopen.measurableSet u : H¹(ℝ^n)) :
          WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1))))
  change E0
      (baseCoordCLM (n := n) (Ω := Ω)
        (localizedDifferenceH10 hΩopen η hηΩ k h u)) = _
  rw [hz]
  exact hproduct

end SobolevSpace.GraphSpace
