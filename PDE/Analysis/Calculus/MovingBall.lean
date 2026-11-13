/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.Analysis.Calculus.EuclideanBall
import CAS.ExactTactic

/-!
# Reynolds transport on Euclidean balls

We differentiate integrals `∫_{B(c, r(t))} f(t, x) dx` whose density
and radius both depend on time.  For a `C¹` density and the shrinking ball
`B(c, T - t)`, the Reynolds transport theorem reads

`d/dt ∫_{B(c, T - t)} f(t, x) dx
  = ∫_{B(c, T - t)} ∂_t f(t, x) dx - ∫_{∂B(c, T - t)} f(t, x) dσ`:

the time derivative of the density inside, minus the density swept out by the
boundary moving inward at unit speed.  This is the form used for local energy
estimates on backward light cones, where the domain of influence shrinks
towards the blowup point.

The shrinking-ball formula is the case `v · ν = -1` of Evans's differentiation formula for
moving regions (App. C.4, Theorem 6), stated there for smooth `f` and smooth regions. It is
the computation (4) in his proof of the flux identity for the wave equation in §12.1.2.

## Main results

* `hasDerivAt_ballIntegral_moving`: Reynolds transport for an arbitrary
  differentiable positive radius.
* `hasDerivAt_ballIntegral_shrinking`: the backward-cone specialization.

## Implementation notes

The proof combines two partial derivatives of `(s, r) ↦ ∫_{B(c, r)} f(s, x) dx`:
in `s`, by dominated differentiation under the integral, and in `r`, by
`hasDerivAt_ballIntegral_radius`.  Joint continuity of both partial derivatives
(the latter through the polar coarea formula) upgrades them to a strict
Fréchet derivative, which is then composed with the path `s ↦ (s, T - s)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.4, Theorem 6, p. 713, and §12.1.2, step 1 of the
  proof of Theorem 2, (4), p. 661. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped Topology

variable {n : ℕ}

private theorem continuous_sphereIntegral_parameter
    (f : ℝ → ℝ^n → ℝ) (hf : Continuous (Function.uncurry f)) (c : ℝ^n) :
    Continuous (fun p : ℝ × ℝ ↦ sphereIntegral n (f p.1) c p.2) := by
  unfold sphereIntegral
  refine (continuous_snd.abs.pow (n - 1)).mul ?_
  have hmap : Continuous fun q : (ℝ × ℝ) × Metric.sphere (0 : ℝ^n) 1 ↦
      (q.1.1, c + q.1.2 • (q.2 : ℝ^n)) := by fun_prop
  simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
    (μ := (volume : Measure (ℝ^n)).toSphere) (f := fun (p : ℝ × ℝ) (ω : Metric.sphere (0 : ℝ^n) 1) ↦
      f p.1 (c + p.2 • (ω : ℝ^n)))
    (hf.comp hmap) isCompact_univ

private theorem hasDerivAt_ballIntegral_time
    (f : ℝ → ℝ^n → ℝ) (hf : ContDiff ℝ 1 (Function.uncurry f)) (c : ℝ^n) {t r : ℝ} :
    HasDerivAt (fun s ↦ ballIntegral n (f s) c r)
      (ballIntegral n (fun x ↦ fderiv ℝ (Function.uncurry f) (t, x) ((1 : ℝ), (0 : ℝ^n))) c r)
      t := by
  let F' : ℝ → (ℝ^n) → ℝ := fun s x ↦
    fderiv ℝ (Function.uncurry f) (s, x) ((1 : ℝ), (0 : (ℝ^n)))
  have hF'cont : Continuous (Function.uncurry F') :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hslice (s : ℝ) : Continuous (f s) :=
    hf.continuous.comp (continuous_const.prodMk continuous_id)
  -- `∂ₜ f` is bounded on the compact set `[t - 1, t + 1] × B̄(c, r)`
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall c r)).bddAbove_image
    (hF'cont.norm.continuousOn (s := Icc (t - 1) (t + 1) ×ˢ Metric.closedBall c r))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (ℝ^n)).restrict (Metric.ball c r)) (F := fun s x ↦ f s x)
    (F' := F') (bound := fun _ ↦ M)
    (Ioo_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))
    (.of_forall fun s ↦ (hslice s).aestronglyMeasurable)
    (((hslice t).continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      Metric.ball_subset_closedBall)
    (hF'cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx s hs
      exact hM ⟨(s, x), ⟨⟨hs.1.le, hs.2.le⟩, Metric.ball_subset_closedBall hx⟩, rfl⟩)
    integrableOn_const
    (.of_forall fun x s _ ↦ (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt s (show HasDerivAt (fun a : ℝ ↦ (a, x)) ((1 : ℝ), (0 : ℝ^n)) s from
        (hasDerivAt_id s).prodMk (hasDerivAt_const s x)))
  simpa [ballIntegral, F'] using hmain.2

private theorem continuousAt_ballIntegral_parameter
    [Fact (0 < n)] (f : ℝ → ℝ^n → ℝ) (hf : Continuous (Function.uncurry f))
    (c : ℝ^n) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ ↦ ballIntegral n (f q.1) c q.2) p := by
  have hmap : Continuous fun q : (ℝ × ℝ) × ℝ ↦ (q.1.1, q.2 * q.1.2) := by fun_prop
  have hinner : Continuous (fun q : ℝ × ℝ ↦
      ∫ z in Set.Icc (0 : ℝ) 1, sphereIntegral n (f q.1) c (z * q.2)) :=
    continuous_parametric_integral_of_continuous
      (f := fun (q : ℝ × ℝ) (z : ℝ) ↦ sphereIntegral n (f q.1) c (z * q.2))
      ((continuous_sphereIntegral_parameter f hf c).comp hmap) isCompact_Icc
  -- polar coordinates: `∫_{B(c, r)} f = r ∫₀¹ ∫_{∂B(c, z r)} f dz` for `r > 0`
  refine (continuous_snd.mul hinner).continuousAt.congr_of_eventuallyEq ?_
  filter_upwards [continuous_snd.continuousAt (Ioi_mem_nhds hp)] with q (hq : 0 < q.2)
  rw [coarea_formula_ball (f q.1) c q.2 ((((hf.comp (continuous_const.prodMk
    continuous_id)).continuousOn.integrableOn_compact (isCompact_closedBall c q.2)).mono_set
      Metric.ball_subset_closedBall)), ← setIntegral_congr_set Ioc_ae_eq_Icc,
    ← intervalIntegral.integral_of_le hq.le]
  have hsubst := intervalIntegral.smul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1)
    (fun ρ ↦ sphereIntegral n (f q.1) c ρ) q.2
  rw [intervalIntegral.integral_of_le zero_le_one, setIntegral_congr_set Ioc_ae_eq_Icc] at hsubst
  simpa [smul_eq_mul] using hsubst.symm

/-- Reynolds transport for a `C¹` scalar density on a differentiably moving
Euclidean ball.

The derivative is the integral of the time derivative plus the normal boundary
flux generated by the radius velocity `ρ'`. -/
theorem hasDerivAt_ballIntegral_moving
    [Fact (0 < n)]
    (f : ℝ → ℝ^n → ℝ)
    (hf : ContDiff ℝ 1 (Function.uncurry f))
    (c : ℝ^n) (ρ : ℝ → ℝ) {t ρ' : ℝ}
    (hρ : HasDerivAt ρ ρ' t) (hr : 0 < ρ t) :
    HasDerivAt
      (fun s ↦ ballIntegral n (f s) c (ρ s))
      (ballIntegral n
          (fun x ↦
            fderiv ℝ (Function.uncurry f) (t, x)
              ((1 : ℝ), (0 : ℝ^n)))
          c (ρ t) +
        ρ' * sphereIntegral n (f t) c (ρ t))
      t := by
  let ft : ℝ → (ℝ^n) → ℝ := fun s x ↦
    fderiv ℝ (Function.uncurry f) (s, x) ((1 : ℝ), (0 : (ℝ^n)))
  let Φ : ℝ → ℝ → ℝ := fun s r ↦ ballIntegral n (f s) c r
  let Ltime : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun s r ↦
    ContinuousLinearMap.toSpanSingleton ℝ (ballIntegral n (ft s) c r)
  let Lradius : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun s r ↦
    ContinuousLinearMap.toSpanSingleton ℝ (sphereIntegral n (f s) c r)
  have hspan : Continuous (fun a : ℝ ↦ ContinuousLinearMap.toSpanSingleton ℝ a) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous
  -- the two partial derivatives of `Φ` near `(t, ρ t)` and their continuity
  have htimeDeriv : ∀ᶠ q in 𝓝 (t, ρ t),
      HasFDerivAt (Φ · q.2) (Function.uncurry Ltime q) q.1 :=
    .of_forall fun q ↦ (hasDerivAt_ballIntegral_time f hf c).hasFDerivAt
  have hradiusDeriv : ∀ᶠ q in 𝓝 (t, ρ t),
      HasFDerivAt (Φ q.1 ·) (Function.uncurry Lradius q) q.2 := by
    filter_upwards [continuous_snd.continuousAt (Ioi_mem_nhds hr)] with q (hq : 0 < q.2)
    exact (hasDerivAt_ballIntegral_radius (f q.1)
      (hf.continuous.comp (continuous_const.prodMk continuous_id)) c hq).hasFDerivAt
  have htimeContinuous : ContinuousAt (Function.uncurry Ltime) (t, ρ t) :=
    hspan.continuousAt.comp (continuousAt_ballIntegral_parameter ft
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const) c hr)
  have hradiusContinuous : ContinuousAt (Function.uncurry Lradius) (t, ρ t) :=
    (hspan.comp (continuous_sphereIntegral_parameter f hf.continuous c)).continuousAt
  have hcomposed := (hasStrictFDerivAt_uncurry_coprod (u := (t, ρ t)) (f := Φ) (f₁ := Ltime)
    (f₂ := Lradius) htimeDeriv hradiusDeriv htimeContinuous hradiusContinuous).hasFDerivAt
      |>.comp_hasDerivAt t (show HasDerivAt (fun s : ℝ ↦ (s, ρ s)) ((1 : ℝ), ρ') t from
        (hasDerivAt_id t).prodMk hρ)
  simp only [ContinuousLinearMap.coprod_apply] at hcomposed
  refine hcomposed.congr_deriv
    (show Function.uncurry Ltime (t, ρ t) 1 + Function.uncurry Lradius (t, ρ t) ρ' = _ from ?_)
  simp [Ltime, Lradius, ft, ContinuousLinearMap.toSpanSingleton_apply]

/-- Reynolds transport for a `C¹` scalar density on a shrinking Euclidean ball.

The derivative is the integral of the time derivative minus the density swept
out by the inward-moving boundary. -/
theorem hasDerivAt_ballIntegral_shrinking
    [Fact (0 < n)]
    (f : ℝ → ℝ^n → ℝ)
    (hf : ContDiff ℝ 1 (Function.uncurry f))
    (c : ℝ^n) (T : ℝ) {t : ℝ}
    (hr : 0 < T - t) :
    HasDerivAt
      (fun s ↦ ballIntegral n (f s) c (T - s))
      (ballIntegral n
          (fun x ↦
            fderiv ℝ (Function.uncurry f) (t, x)
              ((1 : ℝ), (0 : ℝ^n)))
          c (T - t) -
        sphereIntegral n (f t) c (T - t))
      t := by
  have hρ :
      HasDerivAt (fun s : ℝ ↦ T - s) (-1) t := by
    cas
  simpa [sub_eq_add_neg] using
    hasDerivAt_ballIntegral_moving (n := n) f hf c
      (fun s ↦ T - s) hρ hr

end PDE.Analysis
