/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.PolynomialComposition
public import PDE.Analysis.Calculus.MvPolynomial

/-!
# Differentiation of commutative analytic expansions

Native differentiation of a convergent multilinear expansion agrees with
algebraic partial differentiation of its commutative coefficients. Finite
polynomial truncations identify each derivative coefficient.
-/

@[expose] public section

section Normed

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A term of the derivative series depends only on the next homogeneous term. -/
theorem FormalMultilinearSeries.derivSeries_congr
    {p q : FormalMultilinearSeries 𝕜 E F} {n : ℕ} (h : p (1 + n) = q (1 + n)) :
    p.derivSeries n = q.derivSeries n := by
  simp only [FormalMultilinearSeries.derivSeries,
    ContinuousLinearMap.compFormalMultilinearSeries_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  simp only [FormalMultilinearSeries.changeOriginSeriesTerm]
  exact congrArg _ h

/-- Evaluating the native derivative series at a fixed vector gives the analytic
expansion of the corresponding directional derivative. -/
theorem HasFPowerSeriesAt.fderiv_apply [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hp : HasFPowerSeriesAt f p x) (v : E) :
    HasFPowerSeriesAt (fun y ↦ fderiv 𝕜 f y v)
      ((ContinuousLinearMap.apply 𝕜 F v).compFormalMultilinearSeries p.derivSeries) x := by
  obtain ⟨r, hp⟩ := hp
  exact ⟨r, (ContinuousLinearMap.apply 𝕜 F v).comp_hasFPowerSeriesOnBall hp.fderiv⟩

end Normed

namespace MvPowerSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Truncation preserves every native homogeneous multilinear term below its cutoff. -/
theorem toFormalMultilinearSeries_truncTotal (f : MvPowerSeries ι ℝ) {N n : ℕ}
    (hn : n < N) :
    (f.truncTotal N).toMvPowerSeries.toFormalMultilinearSeries n =
      f.toFormalMultilinearSeries n := by
  classical
  change (∑ s : Sym ι n, ContinuousMultilinearMap.symMonomial s
    ((f.truncTotal N).coeff (s : Multiset ι).toFinsupp)) =
      ∑ s : Sym ι n, ContinuousMultilinearMap.symMonomial s
        (coeff (s : Multiset ι).toFinsupp f)
  apply Finset.sum_congr rfl
  intro s hs
  rw [coeff_truncTotal f (show (s : Multiset ι).toFinsupp.degree < N from ?_)]
  change (s : Multiset ι).toFinsupp.sum (fun _ ↦ id) < N
  simpa only [Multiset.toFinsupp_sum_eq, Sym.card_coe] using hn

end MvPowerSeries

open scoped Topology
open Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Analytic coordinate differentiation agrees with partial differentiation of the
commutative Taylor coefficients. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_fderiv_apply
    {f : (ι → ℝ) → ℝ} {p q : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) (i : ι)
    (hq : HasFPowerSeriesAt (fun x ↦ fderiv ℝ f x (Pi.single i 1)) q 0) :
    q.toMvPowerSeries = MvPowerSeries.pderiv i p.toMvPowerSeries := by
  classical
  let L := ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ) : ι → ℝ)
  let p' := p.toMvPowerSeries.toFormalMultilinearSeries
  have hp' : HasFPowerSeriesAt f p' 0 := hp.ofMultiindexCoefficients
  have hd := hp'.fderiv_apply (Pi.single i 1)
  ext a
  let n := a.degree
  let P := p.toMvPowerSeries.truncTotal (n + 2)
  let P' := P.toMvPowerSeries.toFormalMultilinearSeries
  have hP := P.hasFiniteFPowerSeriesOnBall_eval.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  have hPd : HasFPowerSeriesAt (fun x ↦ MvPolynomial.eval x (MvPolynomial.pderiv i P))
      (L.compFormalMultilinearSeries P'.derivSeries) 0 :=
    (hP.fderiv_apply (Pi.single i 1)).congr
      (Eventually.of_forall fun x ↦ MvPolynomial.fderiv_eval_single P x i)
  have hbase : p' (1 + n) = P' (1 + n) :=
    (MvPowerSeries.toFormalMultilinearSeries_truncTotal p.toMvPowerSeries
      (show 1 + n < n + 2 by omega)).symm
  have hterms : (L.compFormalMultilinearSeries p'.derivSeries) n =
      (L.compFormalMultilinearSeries P'.derivSeries) n := by
    simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      FormalMultilinearSeries.derivSeries_congr hbase]
  have hc :
      MvPowerSeries.coeff a (L.compFormalMultilinearSeries p'.derivSeries).toMvPowerSeries =
        MvPowerSeries.coeff a
          (L.compFormalMultilinearSeries P'.derivSeries).toMvPowerSeries := by
    change ((L.compFormalMultilinearSeries p'.derivSeries) n).symCoefficient _ =
      ((L.compFormalMultilinearSeries P'.derivSeries) n).symCoefficient _
    rw [hterms]
  have ha : (a + Finsupp.single i 1).degree < n + 2 := by
    simp only [map_add, Finsupp.degree_single]
    exact Nat.lt_succ_self (n + 1)
  calc
    MvPowerSeries.coeff a q.toMvPowerSeries =
        MvPowerSeries.coeff a
          (L.compFormalMultilinearSeries p'.derivSeries).toMvPowerSeries :=
      congrArg (MvPowerSeries.coeff a) (hq.toMvPowerSeries_eq hd EventuallyEq.rfl)
    _ = MvPowerSeries.coeff a
        (L.compFormalMultilinearSeries P'.derivSeries).toMvPowerSeries := hc
    _ = (MvPolynomial.pderiv i P).coeff a := by
      rw [HasFPowerSeriesAt.toMvPowerSeries_eval (MvPolynomial.pderiv i P) hPd,
        MvPolynomial.coeff_coe]
    _ = MvPowerSeries.coeff a (MvPowerSeries.pderiv i p.toMvPowerSeries) := by
      rw [MvPolynomial.coeff_pderiv, MvPowerSeries.coeff_pderiv,
        MvPowerSeries.coeff_truncTotal p.toMvPowerSeries ha]
