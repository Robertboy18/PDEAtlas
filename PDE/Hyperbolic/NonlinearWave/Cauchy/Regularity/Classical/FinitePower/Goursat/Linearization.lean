/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.DSlope
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Equation
import CAS.ExactTactic

/-!
# Zero-amplitude Goursat linearization

Fixed-point uniqueness identifies the exact zero-amplitude field. Parameter differentiation of
the characteristic equation determines its first amplitude variation.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE.Analysis
open scoped Topology Interval ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

private theorem hasDerivAt_intervalIntegral_zero_parameter {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (a b x : ℝ) (hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun ε : ℝ ↦ F (ε, t)) 0 x) :
    HasDerivAt (fun ε : ℝ ↦ ∫ t in a..b, F (ε, t)) 0 x := by
  have hi := hasFDerivAt_intervalIntegral_of_contDiff hF a b x
  have hz : (∫ t in a..b, (fderiv ℝ F (x, t)).comp
      (ContinuousLinearMap.inl ℝ ℝ ℝ)) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ →L[ℝ] ℝ) := intervalIntegral.integral_congr (by
        intro t ht
        have hd := ((hF.differentiable one_ne_zero) (x, t)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
        have hd0 : HasFDerivAt (fun ε : ℝ ↦ F (ε, t)) (0 : ℝ →L[ℝ] ℝ) x := by
          simpa using (hderiv t ht).hasFDerivAt
        exact hd.unique hd0)
      _ = 0 := by simp
  rw [hz] at hi
  simpa using hi.hasDerivAt

/-- The amplitude derivative is exactly the prescribed linear characteristic
profile throughout every rectangle on which the zero-amplitude slice vanishes. -/
theorem hasDerivAt_polynomial_goursat_amplitude_zero {c : ℝ → ℝ} (hc : ContDiff ℝ 1 c)
    {W : Parameter → ℝ} (hW : ContDiff ℝ 1 W) {δ η a b : ℝ} (hδ : 0 < δ) (hηδ : η ≤ δ)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2)
    (hzero : ∀ s t : ℝ, |s| < η → |t| < η → W (s, t, 0) = 0) (ha : |a| < η) (hb : |b| < η) :
    HasDerivAt (fun ε : ℝ ↦ W (a, b, ε)) a 0 := by
  have hsη {s : ℝ} (hs : s ∈ uIcc 0 a) : |s| < η :=
    (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hs : |s| ≤ |a|).trans_lt ha
  have htη {t : ℝ} (ht : t ∈ uIcc 0 b) : |t| < η :=
    (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht : |t| ≤ |b|).trans_lt hb
  have hf : ContDiff ℝ 1 (fun z : (ℝ × ℝ) × ℝ ↦ c (z.1.2 - z.2) * W (z.1.2, z.2, z.1.1) ^ 2) :=
    (hc.comp (contDiff_fst.snd.sub contDiff_snd)).mul ((hW.comp (contDiff_fst.snd.prodMk
        (contDiff_snd.prodMk contDiff_fst.fst))).pow 2)
  have hinner (s : ℝ) (hs : s ∈ uIcc 0 a) : HasDerivAt (fun ε : ℝ ↦ ∫ t in (0 : ℝ)..b,
        c (s - t) * W (s, t, ε) ^ 2) 0 0 := by
    have hfs : ContDiff ℝ 1 (fun z : ℝ × ℝ ↦ c (s - z.2) * W (s, z.2, z.1) ^ 2) :=
      hf.comp ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd)
    apply hasDerivAt_intervalIntegral_zero_parameter hfs 0 b 0
    intro t ht
    have hd := ((hW.differentiable one_ne_zero) (s, t, 0)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (0 : ℝ) s).prodMk
        ((hasDerivAt_const (0 : ℝ) t).prodMk (hasDerivAt_id (0 : ℝ))))
    simpa [Function.comp_def, hzero s t (hsη hs) (htη ht)] using (hd.pow 2).const_mul (c (s - t))
  have houter := hasDerivAt_intervalIntegral_zero_parameter
    (contDiff_intervalIntegral hf 0 b) 0 a 0 hinner
  have hd := ((hasDerivAt_id (0 : ℝ)).mul_const a).add houter
  simp only [one_mul, add_zero] at hd
  apply hd.congr_of_eventuallyEq
  have hp : (a, b, (0 : ℝ)) ∈ Metric.ball 0 δ := by
    simp only [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff,
      Real.norm_eq_abs, abs_zero]
    exact ⟨ha.trans_le hηδ, hb.trans_le hηδ, hδ⟩
  have hpath : Continuous (fun ε : ℝ ↦ (a, b, ε)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  filter_upwards [hpath.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hp)] with ε hε
  exact heq (a, b, ε) hε

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

private def goursatRectangle (W : C(Parameter, ℝ)) (p : Parameter) : Rectangle →ᵇ ℝ :=
  mkOfCompact ⟨fun q ↦ W (restrictParameter p q), W.continuous.comp
    ((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).prodMk
      ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).prodMk
        continuous_const))⟩

private theorem goursatRectangle_fixedPoint {c W δ p}
    (heq : ∀ p ∈ Metric.ball 0 δ, (W : C(Parameter, ℝ)) p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1,
      ∫ t in (0 : ℝ)..p.2.1, (c : C(ℝ, ℝ)) (s - t) * W (s, t, p.2.2) ^ 2)
    (hp : p ∈ Metric.ball 0 δ) :
    goursatRectangle W p = polynomialFixedPoint c p (goursatRectangle W p) := by
  ext q
  have hmem : restrictParameter p q ∈ Metric.ball 0 δ := by
    rw [Metric.mem_ball, dist_zero_right] at hp ⊢
    exact (norm_restrictParameter_le p q).trans_lt hp
  have h := heq _ hmem
  rw [← integral_rectangle_eq_normalized] at h
  change W (restrictParameter p q) = (p.2.2 * p.1) * (q.1 : ℝ) + (p.1 * p.2.1) * rectangularOperator
      (rectangularCoefficient c p * goursatRectangle W p ^ 2) q
  rw [h, rectangularOperator_apply]
  simp only [restrictParameter] at *
  have hi : (∫ s : I, ∫ t : I, c (p.1 * (q.1 : ℝ) * (s : ℝ) - p.2.1 * (q.2 : ℝ) * (t : ℝ)) *
        W (p.1 * (q.1 : ℝ) * (s : ℝ), p.2.1 * (q.2 : ℝ) * (t : ℝ), p.2.2) ^ 2) = ∫ s : I, ∫ t : I,
        (rectangularCoefficient c p * goursatRectangle W p ^ 2) (descend q (s, t)) := by
    apply integral_congr_ae
    filter_upwards [] with s
    apply integral_congr_ae
    filter_upwards [] with t
    change _ = c (p.1 * ((q.1 : ℝ) * (s : ℝ)) - p.2.1 * ((q.2 : ℝ) * (t : ℝ))) *
      W (p.1 * ((q.1 : ℝ) * (s : ℝ)), p.2.1 * ((q.2 : ℝ) * (t : ℝ)), p.2.2) ^ 2
    simp only [mul_assoc]
  rw [hi]
  generalize (∫ s : I, ∫ t : I,
    (rectangularCoefficient c p * goursatRectangle W p ^ 2) (descend q (s, t))) = J
  generalize p.1 = a, p.2.1 = b, p.2.2 = ε, (q.1 : ℝ) = s, (q.2 : ℝ) = t
  cas

/-- The zero-amplitude slice of any continuous local polynomial Goursat
solution vanishes on a smaller uniform characteristic neighborhood. -/
theorem exists_pos_polynomial_goursat_zero_amplitude {k : ℕ} {c : ℝ → ℝ} (hc : ContDiff ℝ (k + 1) c)
    {W : Parameter → ℝ} (hW : Continuous W) {δ : ℝ} (hδ : 0 < δ)
    (heq : ∀ p ∈ Metric.ball 0 δ, W p = p.2.2 * p.1 + ∫ s in (0 : ℝ)..p.1, ∫ t in (0 : ℝ)..p.2.1,
      c (s - t) * W (s, t, p.2.2) ^ 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ ∀ a b : ℝ, |a| < η → |b| < η → W (a, b, 0) = 0 := by
  obtain ⟨d, r, hd, hr, ψ, _, _, _, hunique⟩ := exists_polynomial_fixed_point hc
  have hW0 : W (0 : Parameter) = 0 := by
    simpa using heq 0 (Metric.mem_ball_self hδ)
  have hsmall : ∀ᶠ p in 𝓝 (0 : Parameter), ‖W p‖ < r :=
    hW.norm.continuousAt.eventually (gt_mem_nhds (by simpa [hW0] using hr))
  obtain ⟨θ, hθ, hθsmall⟩ := Metric.mem_nhds_iff.mp hsmall
  let η := min δ (min d θ)
  have hη : 0 < η := lt_min hδ (lt_min hd hθ)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηd : η ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hηθ : η ≤ θ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, hηδ, ?_⟩
  intro a b ha hb
  let p : Parameter := (a, b, 0)
  have hp : p ∈ Metric.ball 0 η := by
    simp only [p, Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs,
      max_lt_iff, norm_zero]
    exact ⟨ha, hb, hη⟩
  have hpδ := Metric.ball_subset_ball hηδ hp
  have hpd := Metric.ball_subset_ball hηd hp
  let w := goursatRectangle ⟨W, hW⟩ p
  have hwr : ‖w‖ < r := (norm_lt_iff_of_compact hr).mpr fun q ↦ by
    apply hθsmall
    rw [Metric.mem_ball, dist_zero_right] at hp ⊢
    exact (norm_restrictParameter_le p q).trans_lt (hp.trans_le hηθ)
  have hw := hunique p hpd w hwr (goursatRectangle_fixedPoint heq hpδ)
  have hz : ψ p = 0 := hunique p hpd 0 (by simpa using hr) (by
    simp [polynomialFixedPoint, p])
  have he := congrArg (fun v : Rectangle →ᵇ ℝ ↦ v (1, 1)) (hw.symm.trans hz)
  change W (a * 1, b * 1, 0) = 0 at he
  simpa only [mul_one] using he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
