/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial
public import CAS.Polynomial.MathlibBridge
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Two-polynomial interfaces for matched spline jets

These corollaries state the adjacent-panel regularity theorems for two polynomials,
without building a mesh. Matching through order `n` gives continuous derivatives
through order `n`, including the junction.

Conversely, `Cⁿ` regularity at the junction forces those jets to match, equivalently
the branch difference is divisible by `(X - cut)^(n + 1)`. Once `n` reaches the
degree of both branches, they must be the same polynomial. In particular, distinct
polynomial branches cannot be infinitely smooth at their junction.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open scoped _root_.Polynomial

private def twoPanelMesh (cut : ℝ) : StrictKnotMesh 2 :=
  ⟨fun i ↦ cut + (i.val : ℝ) - 1, by
    intro i j hij
    have h : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith⟩

private def twoPanelData (left right : ℝ[X]) (cut : ℝ) :
    PolynomialSplineData (twoPanelMesh cut) (max left.natDegree right.natDegree) where
  piece i := if i.val = 0 then left else right
  degree_le i := by
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _

private theorem twoPanelData_matches
    (left right : ℝ[X]) (cut : ℝ) (order : ℕ)
    (hmatch : ∀ k ≤ order, polynomialJet k left cut = polynomialJet k right cut) :
    (twoPanelData left right cut).MatchesJetsThrough order := by
  intro panel hasRight k hk
  have hp : panel.val = 0 := by omega
  have hp' : panel = 0 := Fin.ext hp
  subst panel
  simpa [twoPanelData, twoPanelMesh, StrictKnotMesh.panelRight,
    StrictKnotMesh.knot, StrictKnotMesh.rightNeighbor] using hmatch k hk

/-- Polynomial jet matching identifies the iterated derivatives of the glued
function at every real point, including the cut. -/
theorem iteratedDeriv_if_polynomialJet_eq
    (left right : ℝ[X]) (cut : ℝ) (smoothness : ℕ)
    (hmatch : ∀ k ≤ smoothness,
      polynomialJet k left cut = polynomialJet k right cut)
    (order : ℕ) (horder : order ≤ smoothness) :
    iteratedDeriv order (fun x ↦ if x ≤ cut then left.eval x else right.eval x) =
      fun x ↦ if x ≤ cut then polynomialJet order left x else polynomialJet order right x := by
  have h := (twoPanelData left right cut).iteratedDeriv_adjacentEvaluator
    (twoPanelData_matches left right cut smoothness hmatch) (0 : Fin 2) (by decide)
    order horder
  unfold PolynomialSplineData.adjacentEvaluator
    PolynomialSplineData.adjacentJetEvaluator at h
  simpa [twoPanelData, twoPanelMesh, StrictKnotMesh.panelRight,
    StrictKnotMesh.knot, StrictKnotMesh.rightNeighbor,
    Polynomial.aeval_def, Algebra.algebraMap_self] using h

/-- The existing polynomial-spline regularity theorem applied to two branches.
No regularity premise is required beyond the exact algebraic jet equalities. -/
theorem contDiff_if_polynomialJet_eq
    (left right : ℝ[X]) (cut : ℝ) (smoothness : ℕ)
    (hmatch : ∀ k ≤ smoothness,
      polynomialJet k left cut = polynomialJet k right cut) :
    ContDiff ℝ smoothness (fun x ↦ if x ≤ cut then left.eval x else right.eval x) := by
  have h := (twoPanelData left right cut).contDiff_adjacentEvaluator
    (twoPanelData_matches left right cut smoothness hmatch) (0 : Fin 2) (by decide)
  unfold PolynomialSplineData.adjacentEvaluator at h
  simpa [twoPanelData, twoPanelMesh, StrictKnotMesh.panelRight,
    StrictKnotMesh.knot, StrictKnotMesh.rightNeighbor,
    Polynomial.aeval_def, Algebra.algebraMap_self] using h

open scoped Topology in
/-- Continuous derivatives at a polynomial junction force equality of the branch jets.
One-sided limits identify both polynomial jets with the same derivative. -/
theorem polynomialJet_eq_of_contDiffAt_if (left right : ℝ[X]) (cut : ℝ) (smoothness : ℕ)
    (hregular : ContDiffAt ℝ smoothness
      (fun x ↦ if x ≤ cut then left.eval x else right.eval x) cut)
    (order : ℕ) (horder : order ≤ smoothness) :
    polynomialJet order left cut = polynomialJet order right cut := by
  let f : ℝ → ℝ := fun x ↦ if x ≤ cut then left.eval x else right.eval x
  have hcontinuous : ContinuousAt (iteratedDeriv order f) cut := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin order) ℝ).symm.continuous.continuousAt.comp
      (hregular.continuousAt_iteratedFDeriv (by exact_mod_cast horder))
  have hpoly (p : ℝ[X]) : iteratedDeriv order p.eval = polynomialJet order p := by
    simpa using iteratedDeriv_if_polynomialJet_eq p p cut order (fun _ _ ↦ rfl) order le_rfl
  have hleft : iteratedDeriv order f =ᶠ[𝓝[<] cut] polynomialJet order left := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hlocal : f =ᶠ[𝓝 x] left.eval := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact ite_eq_left hy.le
    rw [← hpoly]
    exact hlocal.iteratedDeriv_eq order
  have hright : iteratedDeriv order f =ᶠ[𝓝[>] cut] polynomialJet order right := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hlocal : f =ᶠ[𝓝 x] right.eval := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact ite_eq_right (not_le_of_gt hy)
    rw [← hpoly]
    exact hlocal.iteratedDeriv_eq order
  have hl : iteratedDeriv order f cut = polynomialJet order left cut :=
    tendsto_nhds_unique ((hcontinuous.mono_left nhdsWithin_le_nhds).congr' hleft)
      ((PolynomialSplineData.continuous_polynomialJet order left).continuousAt.mono_left
        nhdsWithin_le_nhds)
  have hr : iteratedDeriv order f cut = polynomialJet order right cut :=
    tendsto_nhds_unique ((hcontinuous.mono_left nhdsWithin_le_nhds).congr' hright)
      ((PolynomialSplineData.continuous_polynomialJet order right).continuousAt.mono_left
        nhdsWithin_le_nhds)
  exact hl.symm.trans hr

/-- A polynomial junction is `Cⁿ` exactly when its branch difference vanishes
to order at least `n + 1` at the cut. -/
theorem contDiffAt_if_polynomial_iff_pow_dvd_sub (left right : ℝ[X]) (cut : ℝ)
    (smoothness : ℕ) :
    ContDiffAt ℝ smoothness (fun x ↦ if x ≤ cut then left.eval x else right.eval x) cut ↔
      (Polynomial.X - Polynomial.C cut) ^ (smoothness + 1) ∣ left - right := by
  constructor
  · intro hregular
    by_cases hzero : left - right = 0
    · rw [hzero]
      exact dvd_zero _
    · apply (Polynomial.le_rootMultiplicity_iff hzero).mp
      apply Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hzero
      intro order horder
      simpa only [polynomialJet, Polynomial.IsRoot, Polynomial.iterate_derivative_sub,
        Polynomial.eval_sub, sub_eq_zero] using
        polynomialJet_eq_of_contDiffAt_if left right cut smoothness hregular order horder
  · intro hfactor
    exact (contDiff_if_polynomialJet_eq left right cut smoothness
      (fun _ horder ↦ polynomialJet_eq_of_pow_dvd_sub hfactor horder)).contDiffAt

/-- Distinct branches of degree at most `p` cannot form a `Cᵖ` junction.
The vanishing order required of their difference would exceed its degree. -/
theorem contDiffAt_if_polynomial_iff_eq_of_degree_le (left right : ℝ[X]) (cut : ℝ)
    (degree : ℕ) (hleft : left.natDegree ≤ degree) (hright : right.natDegree ≤ degree) :
    ContDiffAt ℝ degree (fun x ↦ if x ≤ cut then left.eval x else right.eval x) cut ↔
      left = right := by
  rw [contDiffAt_if_polynomial_iff_pow_dvd_sub]
  constructor
  · intro hfactor
    by_contra hne
    have hlower := Polynomial.natDegree_le_of_dvd hfactor (sub_ne_zero.mpr hne)
    have hupper := (Polynomial.natDegree_sub_le left right).trans (max_le hleft hright)
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at hlower
    omega
  · rintro rfl
    simp

/-- Infinite smoothness across a polynomial junction is possible only when
both branches are the same polynomial. -/
theorem contDiffAt_infty_if_polynomial_iff (left right : ℝ[X]) (cut : ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x ↦ if x ≤ cut then left.eval x else right.eval x) cut ↔
      left = right := by
  constructor
  · intro hregular
    exact (contDiffAt_if_polynomial_iff_eq_of_degree_le left right cut
      (max left.natDegree right.natDegree) (le_max_left _ _) (le_max_right _ _)).mp
      (contDiffAt_infty.mp hregular _)
  · rintro rfl
    simpa only [ite_self, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using (left.contDiff_aeval (⊤ : ℕ∞)).contDiffAt (x := cut)

/-- Sparse CAS derivative certificates use precisely the polynomial jets required
by the analytic adjacent-panel theorem. -/
theorem polynomialJet_toRealPolynomial
    (polynomial : CAS.Polynomial.Sparse.Univariate) (order : ℕ) (x : ℝ) :
    polynomialJet order
        (CAS.Polynomial.Sparse.toRealPolynomial polynomial) x =
      CAS.Polynomial.Sparse.evalReal
        ((CAS.Polynomial.Sparse.derivative (0 : Fin 1))^[order] polynomial) x := by
  have h : ∀ n,
      Polynomial.derivative^[n]
          (CAS.Polynomial.Sparse.toRealPolynomial polynomial) =
        CAS.Polynomial.Sparse.toRealPolynomial
          ((CAS.Polynomial.Sparse.derivative (0 : Fin 1))^[n] polynomial) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        CAS.Polynomial.Sparse.toRealPolynomial_derivative]
  rw [polynomialJet, h, CAS.Polynomial.Sparse.eval_toRealPolynomial]

/-- Exact equality of sparse polynomial derivatives through `smoothness` makes
its two-branch evaluator `C^smoothness`. -/
theorem contDiff_if_sparse_iteratedDeriv_eq
    (left right : CAS.Polynomial.Sparse.Univariate) (cut : ℝ) (smoothness : ℕ)
    (hmatch : ∀ k ≤ smoothness,
      iteratedDeriv k (CAS.Polynomial.Sparse.evalReal left) cut =
        iteratedDeriv k (CAS.Polynomial.Sparse.evalReal right) cut) :
    ContDiff ℝ smoothness (fun x ↦ if x ≤ cut then
      CAS.Polynomial.Sparse.evalReal left x else
      CAS.Polynomial.Sparse.evalReal right x) := by
  have hpolynomial : ∀ k ≤ smoothness,
      polynomialJet k (CAS.Polynomial.Sparse.toRealPolynomial left) cut =
        polynomialJet k (CAS.Polynomial.Sparse.toRealPolynomial right) cut := by
    intro k hk
    simpa only [polynomialJet_toRealPolynomial,
      CAS.Polynomial.Sparse.iteratedDeriv_evalReal] using hmatch k hk
  simpa only [CAS.Polynomial.Sparse.eval_toRealPolynomial] using
    contDiff_if_polynomialJet_eq
      (CAS.Polynomial.Sparse.toRealPolynomial left)
      (CAS.Polynomial.Sparse.toRealPolynomial right) cut smoothness hpolynomial

end CAS.Splines
