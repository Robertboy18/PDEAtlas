/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import PDE.Analysis.Calculus.CompactParametricIntegral

/-!
# Classical curves and the Euler–Lagrange equation

A `C²` curve that minimizes the action `∫ L(Ẋ, X)` among `C²` curves with the same endpoints
solves the Euler–Lagrange equation `(∇_q L(Ẋ, X))' = ∇_x L(Ẋ, X)` on the whole closed
interval, with one-sided derivatives at the endpoints. This is the theorem of Evans, §3.3.1,
Theorem 1, for a Lagrangian on a real Hilbert space instead of `ℝⁿ × ℝⁿ`. The action uses the
derivative within the closed time interval, and a minimizer is compared only with `C²` curves
having the same endpoints.

## Main results

* `integral_firstVariation_eq_zero`: the first variation of a fixed-endpoint minimizer vanishes
  in every `C²` direction vanishing at the endpoints.
* `eulerLagrange_of_curveAction_min`: the Euler–Lagrange equation for such a minimizer.

## Implementation notes

We differentiate the action under the integral sign with `hasFDerivAt_integral_of_compact`: the
perturbed jets form a compact family, so no growth condition on the Lagrangian is needed. The
equation then follows by integrating by parts against scalar test functions times a fixed
vector, applying the fundamental lemma of the calculus of variations on the open interval, and
extending by continuity to the endpoints.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff RealInnerProductSpace Gradient

namespace PDE.CalculusOfVariations

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {L : E × E → ℝ} {X V : ℝ → E}

/-- The autonomous action of a curve on a closed time interval. -/
def curveAction (L : E × E → ℝ) (a b : ℝ) (X : ℝ → E) : ℝ :=
  ∫ s in a..b, L (derivWithin X (Icc a b) s, X s)

/-- The first variation of a continuous family of jets. The uniform bound
needed to differentiate the integral follows from compactness. -/
theorem hasDerivAt_integral_lagrangian_variation (hab : a < b)
    (hL : ContDiff ℝ 1 L) {q x v w : ℝ → E}
    (hq : ContinuousOn q (Icc a b)) (hx : ContinuousOn x (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hw : ContinuousOn w (Icc a b)) :
    HasDerivAt
      (fun τ : ℝ ↦ ∫ s in a..b, L (q s + τ • v s, x s + τ • w s))
      (∫ s in a..b, fderiv ℝ L (q s, x s) (v s, w s)) 0 := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let := Measure.Subtype.measureSpace (p := fun s ↦ s ∈ Icc a b)
  have : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  let F (τ : ℝ) (s : Icc a b) := L (q s + τ • v s, x s + τ • w s)
  let D (τ : ℝ) (s : Icc a b) :=
    (fderiv ℝ L (q s + τ • v s, x s + τ • w s)).comp
      (ContinuousLinearMap.toSpanSingleton ℝ (v s, w s))
  have hq' : Continuous (fun s : Icc a b ↦ q s) := hq.domRestrict
  have hx' : Continuous (fun s : Icc a b ↦ x s) := hx.domRestrict
  have hv' : Continuous (fun s : Icc a b ↦ v s) := hv.domRestrict
  have hw' : Continuous (fun s : Icc a b ↦ w s) := hw.domRestrict
  have hjet : Continuous (fun z : ℝ × Icc a b ↦
      (q z.2 + z.1 • v z.2, x z.2 + z.1 • w z.2)) :=
    ((hq'.comp continuous_snd).add
      (continuous_fst.smul (hv'.comp continuous_snd))).prodMk
        ((hx'.comp continuous_snd).add
          (continuous_fst.smul (hw'.comp continuous_snd)))
  have hF : Continuous F.uncurry := hL.continuous.comp hjet
  have hD : Continuous D.uncurry := by
    exact ((hL.continuous_fderiv one_ne_zero).comp hjet).clm_comp
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ (E × E)).continuous.comp
        ((hv'.comp continuous_snd).prodMk (hw'.comp continuous_snd)))
  have hd : ∀ τ s, HasFDerivAt (fun r ↦ F r s) (D τ s) τ := by
    intro τ s
    simpa [F, D, Function.comp_def] using (hL.differentiable one_ne_zero _).hasFDerivAt.comp τ
      (((hasDerivAt_id τ).smul_const (v s) |>.const_add (q s)).prodMk
        ((hasDerivAt_id τ).smul_const (w s) |>.const_add (x s))).hasFDerivAt
  have hi := (hasFDerivAt_integral_of_compact (μ := volume) hF hD hd 0).hasDerivAt
  have hDi : Integrable (D 0) := by
    exact (hD.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  simp only [ContinuousLinearMap.integral_apply hDi] at hi
  simp only [F, D, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, zero_smul, add_zero] at hi
  have hval (τ : ℝ) := integral_subtype_comap (μ := volume) (s := Icc a b) measurableSet_Icc
    (fun s ↦ L (q s + τ • v s, x s + τ • w s))
  have hdiff := integral_subtype_comap (μ := volume) (s := Icc a b) measurableSet_Icc
    (fun s ↦ fderiv ℝ L (q s, x s) (v s, w s))
  simp only [Measure.Subtype.volume_def] at hi
  simp_rw [hval, hdiff] at hi
  simpa only [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab.le] using hi

/-- A fixed-endpoint `C²` minimizer has zero first variation for every `C²`
fixed-endpoint variation. -/
theorem integral_firstVariation_eq_zero (hab : a < b)
    (hL : ContDiff ℝ 1 L) (hX : ContDiffOn ℝ 2 X (Icc a b))
    (hmin : ∀ Y : ℝ → E, ContDiffOn ℝ 2 Y (Icc a b) →
      Y a = X a → Y b = X b → curveAction L a b X ≤ curveAction L a b Y)
    (hV : ContDiffOn ℝ 2 V (Icc a b)) (hVa : V a = 0) (hVb : V b = 0) :
    (∫ s in a..b, fderiv ℝ L (derivWithin X (Icc a b) s, X s)
      (derivWithin V (Icc a b) s, V s)) = 0 := by
  have hU := uniqueDiffOn_Icc hab
  have hd := hasDerivAt_integral_lagrangian_variation hab hL
    (hX.continuousOn_derivWithin hU (by norm_num)) hX.continuousOn
    (hV.continuousOn_derivWithin hU (by norm_num)) hV.continuousOn
  apply IsLocalMin.hasDerivAt_eq_zero _ hd
  apply Filter.Eventually.of_forall
  intro τ
  have hm := hmin (fun s ↦ X s + τ • V s) (hX.add (hV.const_smul τ))
    (by simp [hVa]) (by simp [hVb])
  simpa only [curveAction, zero_smul, add_zero] using hm.trans_eq (by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hab.le] at hs
    have he := ((hX.differentiableOn (by norm_num) s hs).hasDerivWithinAt.add
      ((hV.differentiableOn (by norm_num) s hs).hasDerivWithinAt.const_smul τ)).derivWithin
        (hU s hs)
    exact congrArg (fun q ↦ L (q, X s + τ • V s)) he)

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} {L : E × E → ℝ} {X : ℝ → E}

/-- The momentum and position gradients of a `C²` Lagrangian are jointly `C¹`. -/
theorem contDiff_lagrangian_gradients (hL : ContDiff ℝ 2 L) :
    ContDiff ℝ 1 (fun z : E × E ↦ ∇ (fun q ↦ L (q, z.2)) z.1) ∧
      ContDiff ℝ 1 (fun z : E × E ↦ ∇ (fun x ↦ L (z.1, x)) z.2) := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  constructor
  · exact R.contDiff.comp
      ((hL.comp (contDiff_snd.prodMk (contDiff_fst.snd))).fderiv
        contDiff_fst (by norm_num))
  · exact R.contDiff.comp
      ((hL.comp ((contDiff_fst.fst).prodMk contDiff_snd)).fderiv
        contDiff_snd (by norm_num))

/-- The differential of the Lagrangian splits into its momentum and position
gradients paired with the corresponding variations. -/
theorem fderiv_lagrangian_apply {q x : E} (hL : DifferentiableAt ℝ L (q, x)) (v w : E) :
    fderiv ℝ L (q, x) (v, w) =
      ⟪∇ (fun r ↦ L (r, x)) q, v⟫ + ⟪∇ (fun y ↦ L (q, y)) x, w⟫ := by
  have hq := hL.hasFDerivAt.comp q (hasFDerivAt_prodMk_left (𝕜 := ℝ) q x)
  have hx := hL.hasFDerivAt.comp x (hasFDerivAt_prodMk_right (𝕜 := ℝ) q x)
  dsimp only [Function.comp_def] at hq hx
  rw [inner_gradient_left, inner_gradient_left, hq.fderiv, hx.fderiv]
  change _ = fderiv ℝ L (q, x) (v, 0) + fderiv ℝ L (q, x) (0, w)
  rw [← map_add]
  simp

/-- A `C²` minimizer among `C²` curves with the same endpoints satisfies the
Euler–Lagrange equation, including the one-sided derivatives at the endpoints. -/
theorem eulerLagrange_of_curveAction_min (hab : a < b) (hL : ContDiff ℝ 2 L)
    (hX : ContDiffOn ℝ 2 X (Icc a b))
    (hmin : ∀ Y : ℝ → E, ContDiffOn ℝ 2 Y (Icc a b) →
      Y a = X a → Y b = X b → curveAction L a b X ≤ curveAction L a b Y)
    {t : ℝ} (ht : t ∈ Icc a b) :
    derivWithin
        (fun s ↦ ∇ (fun q ↦ L (q, X s)) (derivWithin X (Icc a b) s))
        (Icc a b) t =
      ∇ (fun x ↦ L (derivWithin X (Icc a b) t, x)) (X t) := by
  let p (s : ℝ) := ∇ (fun q ↦ L (q, X s)) (derivWithin X (Icc a b) s)
  let F (s : ℝ) := ∇ (fun x ↦ L (derivWithin X (Icc a b) s, x)) (X s)
  have hU := uniqueDiffOn_Icc hab
  have hjet : ContDiffOn ℝ 1
      (fun s ↦ (derivWithin X (Icc a b) s, X s)) (Icc a b) :=
    (hX.derivWithin hU (by norm_num)).prodMk (hX.of_le (by norm_num))
  have hp : ContDiffOn ℝ 1 p (Icc a b) :=
    (contDiff_lagrangian_gradients hL).1.comp_contDiffOn hjet
  have hF : ContinuousOn F (Icc a b) :=
    ((contDiff_lagrangian_gradients hL).2.comp_contDiffOn hjet).continuousOn
  have hp' := hp.continuousOn_derivWithin hU le_rfl
  apply ext_inner_right ℝ
  intro v
  let r (s : ℝ) := ⟪derivWithin p (Icc a b) s - F s, v⟫
  have hr : ContinuousOn r (Icc a b) := (hp'.sub hF).inner continuousOn_const
  have hae : ∀ᵐ s : ℝ, s ∈ Ioo a b → r s = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hr.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo)
    intro g hg hgK hgs
    have hga : g a = 0 := image_eq_zero_of_notMem_tsupport
      (fun ha ↦ (hgs ha).1.false)
    have hgb : g b = 0 := image_eq_zero_of_notMem_tsupport
      (fun hb ↦ (hgs hb).2.false)
    have hgd : ContDiff ℝ 1 (deriv g) := (hg.of_le (show 2 ≤ (∞ : ℕ∞ω) by simp)).deriv'
    have hfirst := integral_firstVariation_eq_zero (V := fun s ↦ g s • v)
      hab (hL.of_le (by norm_num)) hX hmin
      ((hg.of_le (by simp)).smul contDiff_const).contDiffOn
      (by simp [hga]) (by simp [hgb])
    have hvderiv (s : ℝ) (hs : s ∈ Icc a b) :
        derivWithin (fun s ↦ g s • v) (Icc a b) s = deriv g s • v :=
      (((hg.differentiable (by simp) s).hasDerivAt.smul_const v).hasDerivWithinAt).derivWithin
        (hU s hs)
    have hfirst' :
        (∫ s in a..b, deriv g s * ⟪p s, v⟫ + g s * ⟪F s, v⟫) = 0 := by
      convert hfirst using 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hab.le] at hs
      dsimp only
      rw [hvderiv s hs, fderiv_lagrangian_apply (hL.differentiable (by norm_num) _)]
      simp [p, F, inner_smul_right]
    have hd (s : ℝ) (hs : s ∈ Icc a b) :
        HasDerivWithinAt (fun s ↦ ⟪p s, v⟫) ⟪derivWithin p (Icc a b) s, v⟫
          (Icc a b) s := by
      simpa using ((hp.differentiableOn one_ne_zero s hs).hasDerivWithinAt.inner ℝ
        (hasDerivWithinAt_const s (Icc a b) v))
    have hparts :
        (∫ s in a..b, deriv g s * ⟪p s, v⟫ +
          g s * ⟪derivWithin p (Icc a b) s, v⟫) = 0 := by
      have hi := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt
        (u := g) (u' := deriv g)
        (v := fun s ↦ ⟪p s, v⟫) (v' := fun s ↦ ⟪derivWithin p (Icc a b) s, v⟫)
        (fun s _ ↦ (hg.differentiable (by simp) s).hasDerivAt.hasDerivWithinAt)
        (fun s hs ↦ by
          rw [uIcc_of_le hab.le] at hs ⊢
          exact hd s hs)
        (hgd.continuous.intervalIntegrable a b)
        ((hp'.inner continuousOn_const).intervalIntegrable_of_Icc hab.le)
      simpa [hga, hgb] using hi
    have hi₁ : IntervalIntegrable
        (fun s ↦ deriv g s * ⟪p s, v⟫ + g s * ⟪derivWithin p (Icc a b) s, v⟫)
        volume a b :=
      ((hgd.continuous.continuousOn.mul (hp.continuousOn.inner continuousOn_const)).add
        (hg.continuous.continuousOn.mul (hp'.inner continuousOn_const))).intervalIntegrable_of_Icc
          hab.le
    have hi₂ : IntervalIntegrable
        (fun s ↦ deriv g s * ⟪p s, v⟫ + g s * ⟪F s, v⟫) volume a b :=
      ((hgd.continuous.continuousOn.mul (hp.continuousOn.inner continuousOn_const)).add
        (hg.continuous.continuousOn.mul (hF.inner continuousOn_const))).intervalIntegrable_of_Icc
          hab.le
    have hz : (∫ s in a..b, g s • r s) = 0 := by
      have he := congrArg₂ (fun x y : ℝ ↦ x - y) hparts hfirst'
      rw [← intervalIntegral.integral_sub hi₁ hi₂] at he
      simpa only [r, smul_eq_mul, inner_sub_left, sub_add_eq_sub_sub,
        add_sub_cancel_left, ← mul_sub, sub_self] using he
    apply (intervalIntegral.integral_eq_integral_of_support_subset ?_).symm.trans hz
    intro s hs
    exact Ioo_subset_Ioc_self (hgs (subset_tsupport g
      (Function.support_smul_subset_left g r hs)))
  have he := Measure.eqOn_Ioo_of_ae_eq volume
    ((ae_restrict_iff' measurableSet_Ioo).mpr hae)
    (hr.mono Ioo_subset_Icc_self) continuousOn_const
  have hc := he.of_subset_closure hr continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])
  exact sub_eq_zero.mp (by simpa only [r, inner_sub_left] using hc ht)

end InnerProduct

end PDE.CalculusOfVariations
