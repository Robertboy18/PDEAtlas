/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.Analysis.Calculus.Potential.Convex

/-!
# Parametric pressure reconstruction

Given a time-dependent spatial field `g : ℝ → ℝ^n → ℝ^n`, we reconstruct a pressure without
making an arbitrary additive choice on each time slice. Fixing a base point `a`,
`normalizedPressure a g t x` is the line integral of `g t` along the segment from `a` to `x`. Its
value at `a` is zero at every time, so the additive pressure gauge is fixed coherently in time.

The spatial statement is the Poincaré lemma for closed one-forms on a convex domain: if `g t` is
differentiable with symmetric derivative on an open convex set containing `a`, the normalized
pressure has spatial gradient `g t` throughout that set. The parametric statement is that joint
regularity of `g` in `(t, x)` passes to the pressure: joint continuity gives joint continuity, and
joint `C^m` regularity gives joint `C^m` regularity for every finite `m`, hence also for `C^∞`.

## Main results

* `normalizedPressure`: the segment integral defining the gauge-fixed pressure.
* `hasGradientAt_normalizedPressure`: on an open convex domain the spatial gradient is `g t`
  whenever the derivative of `g t` is symmetric there.
* `continuous_normalizedPressure`, `contDiff_normalizedPressure`,
  `contDiff_infty_normalizedPressure`: joint regularity of the pressure from joint regularity of
  the field.
* `exists_jointly_contDiff_normalized_pressure_of_partialDeriv_comm` and its continuous and
  smooth variants: existence statements phrased with commuting spatial coordinate derivatives
  in place of the symmetric-derivative condition.

## Implementation notes

The integral is taken over the compact parameter set `Icc 0 1` rather than as an interval
integral, so that Mathlib's dominated-differentiation theorem
`hasFDerivAt_integral_of_dominated_of_fderiv_le` applies directly. Compactness of a closed ball
times `Icc 0 1` supplies the locally uniform derivative bound needed at each order. The gradient
identity is obtained from Mathlib's curve-integral form of the Poincaré lemma through
`normalizedPressure_eq_curveIntegral`.

## References

* M. Spivak, *Calculus on Manifolds: A Modern Approach to Classical Theorems of Advanced Calculus*,
  CRC Press, 2018.
  <https://doi.org/10.1201/9780429501906>
-/

@[expose] public section

noncomputable section

open Filter

open scoped Gradient Interval

namespace IncompressibleFlow

set_option linter.missingDocs true

variable {n : ℕ}

private theorem contDiff_setIntegral_Icc_of_contDiff
    {H E : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] (m : ℕ) {F : H → ℝ → E}
    (hF : ContDiff ℝ m F.uncurry) :
    ContDiff ℝ m (fun x ↦ ∫ r in Set.Icc (0 : ℝ) 1, F x r) := by
  induction m generalizing E with
  | zero =>
      exact contDiff_zero.mpr <|
        continuous_parametric_integral_of_continuous hF.continuous isCompact_Icc
  | succ m ih =>
      let D : H → ℝ → H →L[ℝ] E := fun x r ↦
        (fderiv ℝ F.uncurry (x, r)).comp
          ((ContinuousLinearMap.id ℝ H).prod (0 : H →L[ℝ] ℝ))
      have hD : ContDiff ℝ m D.uncurry := by
        exact (hF.fderiv_right (by simp)).clm_comp contDiff_const
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      refine ⟨fun x ↦ ∫ r in Set.Icc (0 : ℝ) 1, D x r, ih hD, ?_⟩
      intro x
      have hFMeasurable : ∀ᶠ y in nhds x,
          MeasureTheory.AEStronglyMeasurable (F y)
            (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
        filter_upwards with y
        exact (hF.continuous.comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      have hFIntegrable : MeasureTheory.Integrable (F x)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (hF.continuous.comp
          (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
            isCompact_Icc
      have hDMeasurable : MeasureTheory.AEStronglyMeasurable (D x)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        (hD.continuous.comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      obtain ⟨M, hM⟩ :=
        ((isCompact_closedBall x 1).prod
          (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).bddAbove_image
            hD.continuous.norm.continuousOn
      have hBound : ∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1),
          ∀ y ∈ Metric.ball x 1, ‖D y r‖ ≤ M := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with r hr y hy
        apply hM
        exact ⟨(y, r), ⟨Metric.ball_subset_closedBall hy, hr⟩, rfl⟩
      have hMIntegrable : MeasureTheory.Integrable (fun _ : ℝ ↦ M)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) :=
        MeasureTheory.integrableOn_const isCompact_Icc.measure_ne_top (by simp)
      have hDerivative : ∀ᵐ r ∂MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1),
          ∀ y ∈ Metric.ball x 1, HasFDerivAt (fun z ↦ F z r) (D y r) y := by
        refine Filter.Eventually.of_forall fun r y _hy ↦ ?_
        have hline : HasFDerivAt (fun z : H ↦ (z, r))
            ((ContinuousLinearMap.id ℝ H).prod (0 : H →L[ℝ] ℝ)) y :=
          (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const r y)
        simpa [D, Function.comp_def] using
          (hF.differentiable (by simp) (y, r)).hasFDerivAt.comp y hline
      exact hasFDerivAt_integral_of_dominated_of_fderiv_le
        (Metric.ball_mem_nhds x zero_lt_one) hFMeasurable hFIntegrable hDMeasurable
        hBound hMIntegrable hDerivative

/-- The pressure normalized at `a`, obtained by integrating the spatial field `g t` along the
segment from `a` to `x`. -/
def normalizedPressure (a : ℝ^n) (g : ℝ → ℝ^n → ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  ∫ r in Set.Icc (0 : ℝ) 1,
    inner ℝ (g t (AffineMap.lineMap a x r)) (x - a)

/-- The gauge-fixed pressure vanishes at its base point at every time: the segment from `a` to
itself has zero displacement, so the line integral is zero. -/
@[simp]
theorem normalizedPressure_apply_base (a : ℝ^n) (g : ℝ → ℝ^n → ℝ^n) (t : ℝ) :
    normalizedPressure a g t a = 0 := by
  simp [normalizedPressure]

/-- The normalized pressure is the curve integral of the one-form associated to `g t` along the
segment from the base point. -/
theorem normalizedPressure_eq_curveIntegral (a : ℝ^n) (g : ℝ → ℝ^n → ℝ^n)
    (t : ℝ) (x : ℝ^n) :
    normalizedPressure a g t x =
      ∫ᶜ y in Path.segment a x, innerSL ℝ (g t y) := by
  rw [normalizedPressure, curveIntegral_segment,
    intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

/-- Joint continuity of the gradient field gives joint continuity of its gauge-fixed pressure.

Compactness of the unit segment parameter makes the integral depend continuously on both the time
and spatial endpoint. -/
theorem continuous_normalizedPressure (a : ℝ^n) {g : ℝ → ℝ^n → ℝ^n}
    (hg : Continuous g.uncurry) :
    Continuous (normalizedPressure a g).uncurry := by
  apply continuous_parametric_integral_of_continuous
  · have harg : Continuous (fun z : (ℝ × ℝ^n) × ℝ ↦
        (z.1.1, AffineMap.lineMap a z.1.2 z.2)) := by
      fun_prop
    have hdisplacement : Continuous (fun z : (ℝ × ℝ^n) × ℝ ↦ z.1.2 - a) := by
      fun_prop
    exact (hg.comp harg).inner hdisplacement
  · exact isCompact_Icc

/-- Joint finite-order smoothness of the gradient field passes to its gauge-fixed pressure. -/
theorem contDiff_normalizedPressure (m : ℕ) (a : ℝ^n) {g : ℝ → ℝ^n → ℝ^n}
    (hg : ContDiff ℝ m g.uncurry) :
    ContDiff ℝ m (normalizedPressure a g).uncurry := by
  let F : (ℝ × ℝ^n) → ℝ → ℝ := fun tx r ↦
    inner ℝ (g tx.1 (AffineMap.lineMap a tx.2 r)) (tx.2 - a)
  have harg : ContDiff ℝ m (fun z : (ℝ × ℝ^n) × ℝ ↦
      (z.1.1, AffineMap.lineMap a z.1.2 z.2)) := by
    fun_prop
  have hdisplacement : ContDiff ℝ m (fun z : (ℝ × ℝ^n) × ℝ ↦ z.1.2 - a) := by
    fun_prop
  have hF : ContDiff ℝ m F.uncurry := (hg.comp harg).inner ℝ hdisplacement
  exact contDiff_setIntegral_Icc_of_contDiff m hF

/-- Joint smoothness of the gradient field passes to its gauge-fixed pressure. -/
theorem contDiff_infty_normalizedPressure (a : ℝ^n) {g : ℝ → ℝ^n → ℝ^n}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g.uncurry) :
    ContDiff ℝ (⊤ : ℕ∞) (normalizedPressure a g).uncurry := by
  rw [contDiff_infty]
  intro m
  exact contDiff_normalizedPressure m a ((contDiff_infty.mp hg) m)

/-- On an open convex domain, the normalized pressure has spatial gradient `g t` whenever the
spatial derivative of `g t` is symmetric. -/
theorem hasGradientAt_normalizedPressure
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s) {a : ℝ^n} (ha : a ∈ s)
    {g : ℝ → ℝ^n → ℝ^n} (t : ℝ) (hg : DifferentiableOn ℝ (g t) s)
    (hsymm : ∀ x ∈ s, ∀ u v : ℝ^n,
      inner ℝ ((fderiv ℝ (g t) x) u) v = inner ℝ ((fderiv ℝ (g t) x) v) u)
    {x : ℝ^n} (hx : x ∈ s) :
    HasGradientAt (normalizedPressure a g t) (g t x) x := by
  let omega : ℝ^n → ℝ^n →L[ℝ] ℝ := fun y ↦ innerSL ℝ (g t y)
  let domega : ℝ^n → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ :=
    fun y ↦ (innerSL ℝ).comp (fderiv ℝ (g t) y)
  have hgAt (y : ℝ^n) (hy : y ∈ s) : DifferentiableAt ℝ (g t) y :=
    (hg y hy).differentiableAt (hso.mem_nhds hy)
  have homega (y : ℝ^n) (hy : y ∈ s) : HasFDerivWithinAt omega (domega y) s y := by
    exact ((innerSL ℝ).hasFDerivAt.comp y (hgAt y hy).hasFDerivAt).hasFDerivWithinAt
  have homegaSymm (y : ℝ^n) (hy : y ∈ s) (u v : ℝ^n) :
      domega y u v = domega y v u := by
    simpa [domega] using hsymm y hy u v
  have hpWithin : HasFDerivWithinAt
      (fun y ↦ ∫ᶜ z in Path.segment a y, omega z) (omega x) s x :=
    hs.hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
      homega (fun y hy u _hu v _hv ↦ homegaSymm y hy u v) ha hx
  have hp : HasFDerivAt (normalizedPressure a g t) (innerSL ℝ (g t x)) x := by
    rw [funext fun y ↦ normalizedPressure_eq_curveIntegral a g t y]
    exact hpWithin.hasFDerivAt (hso.mem_nhds hx)
  have hRiesz :
      (InnerProductSpace.toDual ℝ (ℝ^n)).symm (innerSL ℝ (g t x)) = g t x := by
    apply (InnerProductSpace.toDual ℝ (ℝ^n)).injective
    simp only [LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [← hRiesz]
  exact hp.hasGradientAt

/-- A jointly continuous, spatially closed field on an open convex domain has a jointly continuous
pressure whose gauge is fixed at `a` and whose spatial gradient is the given field. -/
theorem exists_jointly_continuous_normalized_pressure
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s) {a : ℝ^n} (ha : a ∈ s)
    {g : ℝ → ℝ^n → ℝ^n} (hgContinuous : Continuous g.uncurry)
    (hgDifferentiable : ∀ t : ℝ, DifferentiableOn ℝ (g t) s)
    (hsymm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ u v : ℝ^n,
      inner ℝ ((fderiv ℝ (g t) x) u) v = inner ℝ ((fderiv ℝ (g t) x) v) u) :
    ∃ p : ℝ → ℝ^n → ℝ,
      Continuous p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s → HasGradientAt (p t) (g t x) x := by
  refine ⟨normalizedPressure a g, continuous_normalizedPressure a hgContinuous, ?_, ?_⟩
  · exact normalizedPressure_apply_base a g
  · intro t x hx
    exact hasGradientAt_normalizedPressure hs hso ha t (hgDifferentiable t) (hsymm t) hx

/-- A jointly continuous field with commuting spatial coordinate derivatives
has a jointly continuous pressure normalized at `a`. The point `a` need not lie in `s`: a
pressure normalized at a point of `s` is shifted by its value at `a`. -/
theorem exists_jointly_continuous_normalized_pressure_of_partialDeriv_comm
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} {g : ℝ → ℝ^n → ℝ^n}
    (hgContinuous : Continuous g.uncurry)
    (hgDifferentiable : ∀ t : ℝ, DifferentiableOn ℝ (g t) s)
    (hcomm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ i j : Fin n,
      (∂[i] (fun y ↦ g t y j)) x =
        (∂[j] (fun y ↦ g t y i)) x) :
    ∃ p : ℝ → ℝ^n → ℝ,
      Continuous p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s → HasGradientAt (p t) (g t x) x := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨b, hb⟩
  · exact ⟨fun _ _ ↦ 0, continuous_const, fun _ ↦ rfl, fun _ _ hx ↦ absurd hx (Set.notMem_empty _)⟩
  obtain ⟨q, hq, -, hgrad⟩ : ∃ q : ℝ → ℝ^n → ℝ, Continuous q.uncurry ∧ (∀ t : ℝ, q t b = 0) ∧
      ∀ (t : ℝ) (x : ℝ^n), x ∈ s → HasGradientAt (q t) (g t x) x := by
    apply exists_jointly_continuous_normalized_pressure hs hso hb
      hgContinuous hgDifferentiable
    intro t x hx u v
    exact EuclideanSpace.inner_fderiv_apply_comm_of_partialDeriv_comm (g t) x
      ((hgDifferentiable t x hx).differentiableAt (hso.mem_nhds hx))
      (hcomm t x hx) u v
  refine ⟨fun t x ↦ q t x - q t a, hq.sub (hq.comp (continuous_fst.prodMk continuous_const)),
    fun t ↦ sub_self _, fun t x hx ↦ ?_⟩
  exact hasGradientAt_iff_hasFDerivAt.mpr
    ((hasGradientAt_iff_hasFDerivAt.mp (hgrad t x hx)).sub_const (q t a))

/-- A jointly `C^m` field with commuting spatial coordinate derivatives has a jointly `C^m`
pressure normalized at `a`, for every finite order `m`. -/
theorem exists_jointly_contDiff_normalized_pressure_of_partialDeriv_comm
    (m : ℕ) {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) {g : ℝ → ℝ^n → ℝ^n}
    (hgSmooth : ContDiff ℝ m g.uncurry)
    (hgDifferentiable : ∀ t : ℝ, DifferentiableOn ℝ (g t) s)
    (hcomm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ i j : Fin n,
      (∂[i] (fun y ↦ g t y j)) x =
        (∂[j] (fun y ↦ g t y i)) x) :
    ∃ p : ℝ → ℝ^n → ℝ,
      ContDiff ℝ m p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s → HasGradientAt (p t) (g t x) x := by
  refine ⟨normalizedPressure a g, contDiff_normalizedPressure m a hgSmooth, ?_, ?_⟩
  · exact normalizedPressure_apply_base a g
  · intro t x hx
    exact hasGradientAt_normalizedPressure hs hso ha t (hgDifferentiable t)
      (fun y hy u v ↦ EuclideanSpace.inner_fderiv_apply_comm_of_partialDeriv_comm (g t) y
        ((hgDifferentiable t y hy).differentiableAt (hso.mem_nhds hy))
        (hcomm t y hy) u v) hx

/-- A jointly smooth field with commuting spatial coordinate derivatives has a jointly smooth
pressure with a fixed spatial gauge. -/
theorem exists_jointly_smooth_normalized_pressure_of_partialDeriv_comm
    {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) {g : ℝ → ℝ^n → ℝ^n}
    (hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g.uncurry)
    (hgDifferentiable : ∀ t : ℝ, DifferentiableOn ℝ (g t) s)
    (hcomm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ i j : Fin n,
      (∂[i] (fun y ↦ g t y j)) x =
        (∂[j] (fun y ↦ g t y i)) x) :
    ∃ p : ℝ → ℝ^n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s → HasGradientAt (p t) (g t x) x := by
  refine ⟨normalizedPressure a g, contDiff_infty_normalizedPressure a hgSmooth, ?_, ?_⟩
  · exact normalizedPressure_apply_base a g
  · intro t x hx
    exact hasGradientAt_normalizedPressure hs hso ha t (hgDifferentiable t)
      (fun y hy u v ↦ EuclideanSpace.inner_fderiv_apply_comm_of_partialDeriv_comm (g t) y
        ((hgDifferentiable t y hy).differentiableAt (hso.mem_nhds hy))
        (hcomm t y hy) u v) hx

end IncompressibleFlow
