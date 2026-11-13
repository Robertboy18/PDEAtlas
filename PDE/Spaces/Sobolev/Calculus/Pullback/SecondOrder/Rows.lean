/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability -- shake: keep

/-!
# Second-order pullback rows for Sobolev data

The chain-rule rows for pulling an `H²` function back through a `C²` chart `E` with `C¹`
inverse, on a compact patch `K` of the target. Classically, for smooth `u`,

`∂ᵢ(u ∘ E) = Σ_j (∂ⱼu ∘ E) ∂ᵢEⱼ`,

`∂ᵢ∂ₖ(u ∘ E) = Σ_{j,l} (∂ₗ∂ⱼu ∘ E) ∂ᵢEₗ ∂ₖEⱼ + Σ_j (∂ⱼu ∘ E) ∂ᵢ∂ₖEⱼ`.

We build the right-hand sides for `U ∈ W^{2,2}(E.target)` as elements of
`L²(E.symm '' K)`. The chart derivatives are continuous on the compact source patch, hence
`L^∞` coefficients (`firstChartCoefficient`, `gradientChartCoefficient`,
`hessianChartCoefficient`), and the derivative rows of `U` are pulled back by the bounded
operator `localizedPullbackCLM` of `Pullback.FirstOrder.LocalizedPullback` and multiplied by
those coefficients. Each row is therefore a bounded linear function of `U`, with an explicit
constant that separates the chart data from the operator norm of the localized pullback. That
these rows are the weak derivatives of `u ∘ E` is proved in
`Pullback.SecondOrder.WeakChainRule`.

These are the estimates needed when straightening the boundary in `H²` boundary regularity:
in step 10 of the proof of Evans §6.3.2, Theorem 4, the bound on `u' = u ∘ Ψ` in `H²(V')` is
turned into the bound (71) on `u` in `H²(Ψ(V'))`, with constants depending on the chart.

## Main results

* `compactCoefficientLp`: a continuous function on a compact set as an `L^∞` class.
* `firstSobolevPullbackRow`, `secondSobolevPullbackRow`: the gradient and Hessian rows of the
  pulled-back function as `L²` elements.
* `norm_firstSobolevPullbackRow_le_chartConstant`,
  `norm_secondSobolevPullbackRow_le_chartConstant`: row bounds of the form
  `(coefficient bound) · ‖localizedPullbackCLM‖ · ‖U‖`.
* `secondSobolevPullbackRowCLM`, `tendsto_secondSobolevPullbackRow`: the Hessian row as a
  continuous linear operator on `H²`, so that convergence of approximants is automatic.

## Implementation notes

Second derivative coordinates of `U` are addressed through `pairDerivIndex n l j`, so the
double sum over `(j, l)` runs over ordered pairs; no symmetry of the Hessian is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4, pp. 334-340; the proof straightens the
  boundary in steps 7-9, (58)-(70), pp. 338-339, and returns to the original coordinates in step 10,
  (71), p. 340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set Function ENNReal
open scoped Sobolev
open SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A continuous scalar coefficient, restricted to a compact set, as an
`L∞` equivalence class. -/
noncomputable def compactCoefficientLp
    {K : Set (ℝ^n)} (hK : IsCompact K) (a : ℝ^n → ℝ)
    (ha : Continuous a) : DerivLp n ∞ K :=
  (memLp_on_compact_of_continuous (n := n) (p := (∞ : ENNReal)) hK ha).toLp a

/-- The `L∞` coefficient has the expected representative almost everywhere on
the compact patch. -/
theorem compactCoefficientLp_apply_ae
    {K : Set (ℝ^n)} (hK : IsCompact K) (a : ℝ^n → ℝ)
    (ha : Continuous a) :
    ((compactCoefficientLp (n := n) hK a ha : DerivLp n ∞ K) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n K] a :=
  (memLp_on_compact_of_continuous (n := n) (p := (∞ : ENNReal)) hK ha).coeFn_toLp

namespace SecondOrderPullback

/-- Each coordinate function `x ↦ (E x)ⱼ` of a `C²` chart is `C²`. -/
theorem contDiff_chart_coordinate
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x)) (j : Fin n) :
    ContDiff ℝ 2 (fun x ↦ E x j) := by
  exact (PiLp.proj (2 : ENNReal) (fun _ : Fin n ↦ ℝ) j).contDiff.comp hE

/-- The first partial derivatives `∂ᵢEⱼ` of a `C²` chart are continuous. -/
theorem continuous_chart_first
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x)) (i j : Fin n) :
    Continuous (fun x ↦ (∂[i] (fun y ↦ E y j)) x) := by
  have hc := contDiff_chart_coordinate (n := n) hE j
  have hfd : ContDiff ℝ 1 (fderiv ℝ (fun y ↦ E y j)) :=
    hc.fderiv_right (by norm_num)
  have hp : ContDiff ℝ 1
      (fun x ↦ (∂[i] (fun y ↦ E y j)) x) := by
    simpa [partialDeriv, partialDeriv] using
      hfd.clm_apply (contDiff_const : ContDiff ℝ 1
        (fun _ : ℝ^n ↦ EuclideanSpace.single i (1 : ℝ)))
  exact hp.continuous

/-- The `j`-th component of `DE(x) eᵢ` is the partial derivative `∂ᵢEⱼ(x)`: applying the
Fréchet derivative to a basis vector reads off a Jacobian entry. -/
theorem fderiv_chart_single_apply
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (x : ℝ^n) (i j : Fin n) :
    ((fderiv ℝ (fun y ↦ E y) x) (EuclideanSpace.single i (1 : ℝ))) j =
      (∂[i] (fun y ↦ E y j)) x := by
  let P := PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin n ↦ ℝ) j
  have hfd : fderiv ℝ (fun y ↦ E y j) x =
      P.comp (fderiv ℝ (fun y ↦ E y) x) := by
    exact (P.hasFDerivAt.comp x
      (hE.differentiable (by norm_num) x).hasFDerivAt).fderiv
  have h := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ))) hfd
  simpa [partialDeriv, partialDeriv, P] using h.symm

/-- The second partial derivatives `∂ᵢ∂ₖEⱼ` of a `C²` chart are continuous. -/
theorem continuous_chart_second
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x)) (i k j : Fin n) :
    Continuous (fun x ↦
      (∂[i]
        (fun y ↦ (∂[k] (fun z ↦ E z j)) y)) x) := by
  have hc := contDiff_chart_coordinate (n := n) hE j
  have hfirst : ContDiff ℝ 1
      (fun y ↦ (∂[k] (fun z ↦ E z j)) y) := by
    have hfd : ContDiff ℝ 1 (fderiv ℝ (fun z ↦ E z j)) :=
      hc.fderiv_right (by norm_num)
    simpa [partialDeriv, partialDeriv] using
      hfd.clm_apply (contDiff_const : ContDiff ℝ 1
        (fun _ : ℝ^n ↦ EuclideanSpace.single k (1 : ℝ)))
  have hfd : ContDiff ℝ 0
      (fderiv ℝ (fun y ↦ (∂[k] (fun z ↦ E z j)) y)) :=
    hfirst.fderiv_right (by norm_num)
  have hsecond : ContDiff ℝ 0 (fun x ↦
      (∂[i]
        (fun y ↦ (∂[k] (fun z ↦ E z j)) y)) x) := by
    simpa [partialDeriv, partialDeriv] using
      hfd.clm_apply (contDiff_const : ContDiff ℝ 0
        (fun _ : ℝ^n ↦ EuclideanSpace.single i (1 : ℝ)))
  exact hsecond.continuous

end SecondOrderPullback

open SecondOrderPullback

/-- Product of the two first-chart-derivative factors in the Hessian term,
as a bounded coefficient on the compact source patch. -/
noncomputable def hessianChartCoefficient
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K)
    (i k j l : Fin n) :
    DerivLp n ∞ (compactPullbackSource (n := n) E K) := by
  let L := compactPullbackSource (n := n) E K
  have hL : IsCompact L :=
    isCompact_compactPullbackSource (n := n) hEsymm.continuous hK
  let a : ℝ^n → ℝ := fun x ↦
    (∂[i] (fun y ↦ E y l)) x *
      (∂[k] (fun y ↦ E y j)) x
  have ha : Continuous a :=
    (continuous_chart_first (n := n) hE i l).mul
      (continuous_chart_first (n := n) hE k j)
  exact compactCoefficientLp (n := n) hL a ha

/-- The second-chart-derivative coefficient in the gradient correction term,
as a bounded coefficient on the compact source patch. -/
noncomputable def gradientChartCoefficient
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K)
    (i k j : Fin n) :
    DerivLp n ∞ (compactPullbackSource (n := n) E K) := by
  let L := compactPullbackSource (n := n) E K
  have hL : IsCompact L :=
    isCompact_compactPullbackSource (n := n) hEsymm.continuous hK
  let a : ℝ^n → ℝ := fun x ↦
    (∂[i]
      (fun y ↦ (∂[k] (fun z ↦ E z j)) y)) x
  exact compactCoefficientLp (n := n) hL a
    (continuous_chart_second (n := n) hE i k j)

/-- A first chart derivative, as a bounded coefficient on the
compact source patch. -/
noncomputable def firstChartCoefficient
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i j : Fin n) :
    DerivLp n ∞ (compactPullbackSource (n := n) E K) := by
  let L := compactPullbackSource (n := n) E K
  have hL : IsCompact L :=
    isCompact_compactPullbackSource (n := n) hEsymm.continuous hK
  let a : ℝ^n → ℝ := fun x ↦
    (∂[i] (fun y ↦ E y j)) x
  exact compactCoefficientLp (n := n) hL a
    (continuous_chart_first (n := n) hE i j)

/-- The `i`-th weak gradient row of the compactly localized pullback of an
`H²` function. -/
noncomputable def firstSobolevPullbackRow
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i : Fin n) :
    DerivLp n 2 (compactPullbackSource (n := n) E K) :=
  ∑ j : Fin n,
    mulLpLeft (n := n) (p := (2 : ENNReal))
      (firstChartCoefficient (n := n) hE hEsymm hK i j)
      (localizedPullbackCLM (n := n) (p := (2 : ENNReal))
        (hE.of_le (by norm_num)) hEsymm hK hKsub
        ((U : WkpAmbientOn n 2 2 E.target)
          (firstDerivIndex n 2 (by norm_num) j)))

/-- Quantitative `L²` estimate for a first-order pullback row. -/
theorem norm_firstSobolevPullbackRow_le
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i : Fin n) :
    ‖firstSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i‖ ≤
      ∑ j : Fin n,
        ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖ *
          ‖localizedPullbackCLM (n := n) (p := (2 : ENNReal))
            (hE.of_le (by norm_num)) hEsymm hK hKsub
            ((U : WkpAmbientOn n 2 2 E.target)
              (firstDerivIndex n 2 (by norm_num) j))‖ := by
  classical
  unfold firstSobolevPullbackRow
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  exact norm_mulLpLeft_apply_le
    (n := n) (p := (2 : ENNReal))
    (firstChartCoefficient (n := n) hE hEsymm hK i j) _

/-- Sum of the bounded first-chart-derivative coefficients in one gradient
row. -/
noncomputable def firstPullbackCoefficientBound
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i : Fin n) : ℝ :=
  ∑ j : Fin n, ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖

/-- The first-order chart coefficient bound is a sum of norms, hence nonnegative. -/
theorem firstPullbackCoefficientBound_nonneg
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i : Fin n) :
    0 ≤ firstPullbackCoefficientBound (n := n) hE hEsymm hK i := by
  unfold firstPullbackCoefficientBound
  positivity

/-- Compact-chart estimate for one transformed gradient row. The constant separates into the
finite chart coefficient bound and the norm of the localized `L²` pullback operator, and is
independent of `U`. -/
theorem norm_firstSobolevPullbackRow_le_chartConstant
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i : Fin n) :
    ‖firstSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i‖ ≤
      (firstPullbackCoefficientBound (n := n) hE hEsymm hK i *
        ‖localizedPullbackCLM (n := n) (p := (2 : ENNReal))
          (hE.of_le (by norm_num)) hEsymm hK hKsub‖) * ‖U‖ := by
  classical
  let P := localizedPullbackCLM (n := n) (p := (2 : ENNReal))
    (hE.of_le (by norm_num)) hEsymm hK hKsub
  have hpull (j : Fin n) :
      ‖P ((U : WkpAmbientOn n 2 2 E.target)
          (firstDerivIndex n 2 (by norm_num) j))‖ ≤
        ‖P‖ * ‖U‖ := by
    calc
      ‖P ((U : WkpAmbientOn n 2 2 E.target)
          (firstDerivIndex n 2 (by norm_num) j))‖ ≤
          ‖P‖ * ‖(U : WkpAmbientOn n 2 2 E.target)
            (firstDerivIndex n 2 (by norm_num) j)‖ :=
        ContinuousLinearMap.le_opNorm P _
      _ ≤ ‖P‖ * ‖(U : WkpAmbientOn n 2 2 E.target)‖ :=
        mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) (norm_nonneg P)
      _ = ‖P‖ * ‖U‖ := rfl
  refine (norm_firstSobolevPullbackRow_le
    (n := n) hE hEsymm hK hKsub U i).trans ?_
  calc
    (∑ j : Fin n,
        ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖ *
          ‖P ((U : WkpAmbientOn n 2 2 E.target)
            (firstDerivIndex n 2 (by norm_num) j))‖) ≤
      ∑ j : Fin n,
        ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖ *
          (‖P‖ * ‖U‖) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hpull j) (norm_nonneg _)
    _ = (firstPullbackCoefficientBound (n := n) hE hEsymm hK i * ‖P‖) * ‖U‖ := by
      unfold firstPullbackCoefficientBound
      calc
        (∑ j : Fin n,
            ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖ *
              (‖P‖ * ‖U‖)) =
            ∑ j : Fin n,
              (‖firstChartCoefficient (n := n) hE hEsymm hK i j‖ * ‖P‖) * ‖U‖ := by
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = (∑ j : Fin n,
              ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖ * ‖P‖) * ‖U‖ :=
            by rw [Finset.sum_mul]
        _ = ((∑ j : Fin n,
              ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖) * ‖P‖) * ‖U‖ := by
            congr 1
            exact (Finset.sum_mul (s := Finset.univ)
              (f := fun j : Fin n ↦
                ‖firstChartCoefficient (n := n) hE hEsymm hK i j‖)
              (a := ‖P‖)).symm

/-- The `(i,k)` Hessian row of the compactly localized pullback of an `H²`
function.  This is the exact Sobolev counterpart of `secondPullbackRow`:
target Hessian rows are pulled back and multiplied by first chart derivatives,
while target gradient rows are multiplied by second chart derivatives. -/
noncomputable def secondSobolevPullbackRow
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    DerivLp n 2 (compactPullbackSource (n := n) E K) :=
  (∑ j : Fin n, ∑ l : Fin n,
    mulLpLeft (n := n) (p := (2 : ENNReal))
      (hessianChartCoefficient (n := n) hE hEsymm hK i k j l)
      (localizedPullbackCLM (n := n) (p := (2 : ENNReal))
        (hE.of_le (by norm_num)) hEsymm hK hKsub
        ((U : WkpAmbientOn n 2 2 E.target)
          (pairDerivIndex n l j)))) +
  ∑ j : Fin n,
    mulLpLeft (n := n) (p := (2 : ENNReal))
      (gradientChartCoefficient (n := n) hE hEsymm hK i k j)
      (localizedPullbackCLM (n := n) (p := (2 : ENNReal))
        (hE.of_le (by norm_num)) hEsymm hK hKsub
        ((U : WkpAmbientOn n 2 2 E.target)
          (firstDerivIndex n 2 (by norm_num) j)))

/-- Quantitative `L²` estimate for a second-order pullback row.  Each term is
controlled by the `L∞` norm of its chart coefficient and the `L²` norm of the
corresponding localized target derivative row.  This is the precise finite-sum
estimate needed to pass from smooth approximants to arbitrary `H²` data. -/
theorem norm_secondSobolevPullbackRow_le
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    ‖secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k‖ ≤
      (∑ j : Fin n, ∑ l : Fin n,
        ‖hessianChartCoefficient (n := n) hE hEsymm hK i k j l‖ *
          ‖localizedPullbackCLM (n := n) (p := (2 : ENNReal))
            (hE.of_le (by norm_num)) hEsymm hK hKsub
            ((U : WkpAmbientOn n 2 2 E.target)
              (pairDerivIndex n l j))‖) +
      ∑ j : Fin n,
        ‖gradientChartCoefficient (n := n) hE hEsymm hK i k j‖ *
          ‖localizedPullbackCLM (n := n) (p := (2 : ENNReal))
            (hE.of_le (by norm_num)) hEsymm hK hKsub
            ((U : WkpAmbientOn n 2 2 E.target)
              (firstDerivIndex n 2 (by norm_num) j))‖ := by
  classical
  unfold secondSobolevPullbackRow
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro l _
    exact norm_mulLpLeft_apply_le
      (n := n) (p := (2 : ENNReal))
      (hessianChartCoefficient (n := n) hE hEsymm hK i k j l) _
  · refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro j _
    exact norm_mulLpLeft_apply_le
      (n := n) (p := (2 : ENNReal))
      (gradientChartCoefficient (n := n) hE hEsymm hK i k j) _

/-- Continuous projection onto one derivative row of the target `H²` bundle. -/
noncomputable def h2RowProj
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) (a : DerivIndex n 2) :
    W^{2,2}(E.target) →L[ℝ] DerivLp n 2 E.target :=
  (PiLp.proj (𝕜 := ℝ) (p := (2 : ENNReal))
    (β := fun _ : DerivIndex n 2 ↦ DerivLp n 2 E.target) a).comp
    (Submodule.subtypeL (wkpSubmoduleOn n 2 2 E.target))

/-- The second-order compact pullback row as a continuous linear operator on
`H²`.  Packaging the row this way makes convergence of smooth approximants an
immediate consequence of continuity rather than a new coordinatewise
estimate for each approximation sequence. -/
noncomputable def secondSobolevPullbackRowCLM
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (i k : Fin n) :
    W^{2,2}(E.target) →L[ℝ]
      DerivLp n 2 (compactPullbackSource (n := n) E K) :=
  (∑ j : Fin n, ∑ l : Fin n,
    (mulLpLeft (n := n) (p := (2 : ENNReal))
      (hessianChartCoefficient (n := n) hE hEsymm hK i k j l)).comp
      ((localizedPullbackCLM (n := n) (p := (2 : ENNReal))
        (hE.of_le (by norm_num)) hEsymm hK hKsub).comp
        (h2RowProj (n := n) E
          (pairDerivIndex n l j)))) +
  ∑ j : Fin n,
    (mulLpLeft (n := n) (p := (2 : ENNReal))
      (gradientChartCoefficient (n := n) hE hEsymm hK i k j)).comp
      ((localizedPullbackCLM (n := n) (p := (2 : ENNReal))
        (hE.of_le (by norm_num)) hEsymm hK hKsub).comp
        (h2RowProj (n := n) E
          (firstDerivIndex n 2 (by norm_num) j)))

/-- The operator form of the Hessian row evaluates to `secondSobolevPullbackRow`. -/
@[simp] theorem secondSobolevPullbackRowCLM_apply
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    secondSobolevPullbackRowCLM (n := n) hE hEsymm hK hKsub i k U =
      secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k := by
  simp [secondSobolevPullbackRowCLM, secondSobolevPullbackRow, h2RowProj]

/-- Operator-norm control of every Hessian row of the compact pullback. -/
theorem norm_secondSobolevPullbackRow_le_opNorm
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    ‖secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k‖ ≤
      ‖secondSobolevPullbackRowCLM (n := n) hE hEsymm hK hKsub i k‖ * ‖U‖ := by
  rw [← secondSobolevPullbackRowCLM_apply]
  exact ContinuousLinearMap.le_opNorm _ _

/-- Smooth `H²` approximants converge in every second-order compact
pullback row. -/
theorem tendsto_secondSobolevPullbackRow
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    {U_m : ℕ → W^{2,2}(E.target)} {U : W^{2,2}(E.target)}
    (hU : Filter.Tendsto U_m Filter.atTop (nhds U)) (i k : Fin n) :
    Filter.Tendsto
      (fun m ↦ secondSobolevPullbackRow (n := n)
        hE hEsymm hK hKsub (U_m m) i k)
      Filter.atTop
      (nhds (secondSobolevPullbackRow (n := n)
        hE hEsymm hK hKsub U i k)) := by
  simp only [← secondSobolevPullbackRowCLM_apply]
  change Filter.Tendsto
    ((secondSobolevPullbackRowCLM (n := n) hE hEsymm hK hKsub i k) ∘ U_m)
    Filter.atTop
    (nhds ((secondSobolevPullbackRowCLM (n := n) hE hEsymm hK hKsub i k) U))
  exact
    ((secondSobolevPullbackRowCLM (n := n) hE hEsymm hK hKsub i k).continuous.tendsto U).comp hU

/-- Sum of the `L∞` chart-coefficient norms occurring in one transformed
Hessian row.  It is finite because both coordinate index sets are finite and
the chart is `C²` on the compact source patch. -/
noncomputable def secondPullbackCoefficientBound
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i k : Fin n) : ℝ :=
  (∑ j : Fin n, ∑ l : Fin n,
    ‖hessianChartCoefficient (n := n) hE hEsymm hK i k j l‖) +
  ∑ j : Fin n,
    ‖gradientChartCoefficient (n := n) hE hEsymm hK i k j‖

/-- The second-order chart coefficient bound is a sum of norms, hence nonnegative. -/
theorem secondPullbackCoefficientBound_nonneg
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (i k : Fin n) :
    0 ≤ secondPullbackCoefficientBound (n := n) hE hEsymm hK i k := by
  unfold secondPullbackCoefficientBound
  positivity

/-- Compact-chart estimate for one transformed Hessian row.  The constant
separates into the finite `C²` chart coefficient bound and the norm of the
localized `L²` pullback operator; it is independent of `U`. -/
theorem norm_secondSobolevPullbackRow_le_chartConstant
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (i k : Fin n) :
    ‖secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k‖ ≤
      (secondPullbackCoefficientBound (n := n) hE hEsymm hK i k *
        ‖localizedPullbackCLM (n := n) (p := (2 : ENNReal))
          (hE.of_le (by norm_num)) hEsymm hK hKsub‖) * ‖U‖ := by
  classical
  let P := localizedPullbackCLM (n := n) (p := (2 : ENNReal))
    (hE.of_le (by norm_num)) hEsymm hK hKsub
  have hpull (a : DerivIndex n 2) :
      ‖P ((U : WkpAmbientOn n 2 2 E.target) a)‖ ≤ ‖P‖ * ‖U‖ := by
    calc
      ‖P ((U : WkpAmbientOn n 2 2 E.target) a)‖ ≤
          ‖P‖ * ‖(U : WkpAmbientOn n 2 2 E.target) a‖ :=
        ContinuousLinearMap.le_opNorm P _
      _ ≤ ‖P‖ * ‖(U : WkpAmbientOn n 2 2 E.target)‖ :=
        mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ a) (norm_nonneg P)
      _ = ‖P‖ * ‖U‖ := rfl
  refine (norm_secondSobolevPullbackRow_le
    (n := n) hE hEsymm hK hKsub U i k).trans ?_
  have hfirst :
      (∑ j : Fin n, ∑ l : Fin n,
        ‖hessianChartCoefficient (n := n) hE hEsymm hK i k j l‖ *
          ‖P ((U : WkpAmbientOn n 2 2 E.target)
            (pairDerivIndex n l j))‖) ≤
      (∑ j : Fin n, ∑ l : Fin n,
        ‖hessianChartCoefficient (n := n) hE hEsymm hK i k j l‖) *
        (‖P‖ * ‖U‖) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l _
    exact mul_le_mul_of_nonneg_left
      (hpull (pairDerivIndex n l j))
      (norm_nonneg _)
  have hsecond :
      (∑ j : Fin n,
        ‖gradientChartCoefficient (n := n) hE hEsymm hK i k j‖ *
          ‖P ((U : WkpAmbientOn n 2 2 E.target)
            (firstDerivIndex n 2 (by norm_num) j))‖) ≤
      (∑ j : Fin n,
        ‖gradientChartCoefficient (n := n) hE hEsymm hK i k j‖) *
        (‖P‖ * ‖U‖) := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left
      (hpull (firstDerivIndex n 2 (by norm_num) j))
      (norm_nonneg _)
  calc
    (∑ j : Fin n, ∑ l : Fin n,
        ‖hessianChartCoefficient (n := n) hE hEsymm hK i k j l‖ *
          ‖P ((U : WkpAmbientOn n 2 2 E.target)
            (pairDerivIndex n l j))‖) +
      ∑ j : Fin n,
        ‖gradientChartCoefficient (n := n) hE hEsymm hK i k j‖ *
          ‖P ((U : WkpAmbientOn n 2 2 E.target)
            (firstDerivIndex n 2 (by norm_num) j))‖
        ≤
      (∑ j : Fin n, ∑ l : Fin n,
        ‖hessianChartCoefficient (n := n) hE hEsymm hK i k j l‖) *
          (‖P‖ * ‖U‖) +
      (∑ j : Fin n,
        ‖gradientChartCoefficient (n := n) hE hEsymm hK i k j‖) *
          (‖P‖ * ‖U‖) := add_le_add hfirst hsecond
    _ = (secondPullbackCoefficientBound (n := n) hE hEsymm hK i k * ‖P‖) * ‖U‖ := by
      unfold secondPullbackCoefficientBound
      ring


end SobolevSpace.WeakChangeOfVariables
