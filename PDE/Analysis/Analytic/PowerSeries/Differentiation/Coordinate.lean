/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Differentiation.Iterated
public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet

/-!
# Analytic expansions of native coordinate jets

The continuous linear equivalence between finite coordinate functions and
Euclidean space carries the coordinate directions to the native orthonormal
basis. The commutative expansion of a native mixed partial is consequently the
corresponding mixed formal derivative.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.MultiIndex

/-- A mixed coordinate derivative of an analytic function is analytic at the
same point. Analyticity supplies all the necessary neighboring derivatives. -/
theorem analyticAt_coordinateDeriv {n j : ℕ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : AnalyticAt ℝ u x) (α : Sym (Fin n) j) :
    AnalyticAt ℝ (coordinateDeriv α u) x := by
  have hi : AnalyticAt ℝ (iteratedFDeriv ℝ j u) x :=
    (show AnalyticOnNhd ℝ u {y | AnalyticAt ℝ u y} from fun _ hy ↦ hy).iteratedFDeriv j x hu
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ ℝ^n) ℝ
    (directions α)).analyticAt _).comp hi

end PDE.Analysis.MultiIndex

open PDE.Analysis.MultiIndex

/-- Native Euclidean coordinate derivatives have the mixed formal coefficients
of the coordinate pullback. This includes order zero and dimension zero. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_coordinateDeriv
    {n j : ℕ} {u : ℝ^n → ℝ}
    {p q : FormalMultilinearSeries ℝ (Fin n → ℝ) ℝ}
    (hp : HasFPowerSeriesAt (fun x ↦ u (WithLp.toLp 2 x)) p 0)
    (α : Sym (Fin n) j)
    (hq : HasFPowerSeriesAt
      (fun x ↦ coordinateDeriv α u (WithLp.toLp 2 x)) q 0) :
    q.toMvPowerSeries =
      MvPowerSeries.iteratedPDeriv (α : Multiset (Fin n)) p.toMvPowerSeries := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm
  have he (i : Fin n) :
      e (Pi.single i 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
    simp only [e, PiLp.continuousLinearEquiv_symm_apply,
      EuclideanSpace.basisFun_apply, PiLp.toLp_single]
  have hi (x : Fin n → ℝ) :
      iteratedFDeriv ℝ j (fun y ↦ u (WithLp.toLp 2 y)) x
          (fun i ↦ Pi.single (α.sortedTuple i) 1) =
        coordinateDeriv α u (WithLp.toLp 2 x) := by
    have h := e.iteratedFDerivWithin_comp_right u
      (s := Set.univ) (x := x) uniqueDiffOn_univ (Set.mem_univ _) j
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
    change iteratedFDeriv ℝ j (u ∘ e) x
      (fun i ↦ Pi.single (α.sortedTuple i) 1) = _
    rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ j u (e x)
      (fun i ↦ e (Pi.single (α.sortedTuple i) 1)) =
        iteratedFDeriv ℝ j u (e x) (directions α)
    exact congrArg (iteratedFDeriv ℝ j u (e x)) (funext fun i ↦ he (α.sortedTuple i))
  have hq' : HasFPowerSeriesAt
      (fun x ↦ iteratedFDeriv ℝ j (fun y ↦ u (WithLp.toLp 2 y)) x
        (fun i ↦ Pi.single (α.sortedTuple i) 1)) q 0 := by
    simpa only [hi] using hq
  rw [hp.toMvPowerSeries_iteratedFDeriv_apply α.sortedTuple hq', Sym.ofFn_sortedTuple]
