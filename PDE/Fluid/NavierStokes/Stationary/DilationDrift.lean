/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.SolenoidalDensity
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceL2Pairing
public import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.FDeriv.PartialDeriv.Dilation

/-!
# The dilation drift on `H¹` fields

Fix a property `P` of test fields that is preserved by the dilations `φ ↦ φ(s ·)`, `s > 0`, for
example vanishing divergence. Suppose that for a vector `H¹` field `d` the drift pairing
`φ ↦ ⟨d, x·∇φ⟩` agrees on the test fields with property `P` with a continuous linear functional `Ψ`
on vector `H¹`, and that `d` lies in the closed span of these test fields. Then `Ψ(d) = -(n/2) ‖d‖²`
(`drift_eq_neg_half_mul_massPairing`): the formal identity `⟨d, x·∇d⟩ = -(n/2) ‖d‖²` holds without
any weight on `d`. For the divergence-free property the closed span contains every divergence-free
`H¹` field (`solenoidalTestFields_eq_testFieldsOf` and
`mem_topologicalClosure_span_solenoidalTestFields`).

## How it works

For smooth decaying `d` the identity is one integration by parts, but for `d` in `H¹` the field
`x·∇d` need not be in `L²`, so we pass through dilations. For a smooth compactly supported field `φ`
the pairing `⟨d, x·∇φ⟩` is the derivative of `s ↦ ⟨d, φ(s ·)⟩` at `s = 1`, up to the factor `1/s`
(`hasDerivAt_integral_mul_comp_smul`). Integrating in the dilation factor gives

`⟨d, v(t ·)⟩ - ⟨d, v⟩ = -∫ₜ¹ s⁻¹ Ψ(v(s ·)) ds`

first for the test fields with property `P` (`massPairing_dilation_testFieldH1_sub`), then by
linearity and continuity on their closed span (`massPairing_dilation_sub_of_mem_closure`). We take
`v = d` and use `‖d(t ·) - d‖² ≥ 0` (`massPairing_sub_sub_nonneg`) and `‖d(t ·)‖² = t⁻ⁿ ‖d‖²`
(`massPairing_dilationH1`). After division by `1 - t`, the limits `t → 1⁻` and `t → 1⁺` give
opposite inequalities between `Ψ(d)` and `-(n/2) ‖d‖²`. The dilation factor is frozen below `1/2`
(`dilationH1Half`, `driftIntegral`), so that the integrand is continuous in `s` on all of `ℝ`.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv iteratedPartialDeriv_comp_const_smul)
open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal NNReal Sobolev ContDiff SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

variable {n : ℕ}



/-- Componentwise spatial dilation `v ↦ v(s ·)` on vector `H¹` fields. -/
def dilationH1 (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) :=
  ContinuousLinearMap.piLpMap 2 fun _ ↦ dilationWkpCLM (by norm_num) s hs

theorem dilationH1_apply (s : ℝ) (hs : s ≠ 0) (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (i : Fin n) : dilationH1 n s hs v i = dilationWkpCLM (by norm_num) s hs (v i) := rfl

theorem contDiff_comp_smul {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (s : ℝ) :
    ContDiff ℝ ∞ (fun x ↦ φ (s • x)) :=
  hφ.comp (contDiff_const_smul s)

theorem hasCompactSupport_comp_smul {φ : ℝ^n → ℝ^n} (hc : HasCompactSupport φ) {s : ℝ}
    (hs : s ≠ 0) : HasCompactSupport (fun x ↦ φ (s • x)) :=
  hc.comp_homeomorph (Homeomorph.smulOfNeZero s hs)

theorem hasCompactSupport_comp_smul' {ψ : ℝ^n → ℝ} (hc : HasCompactSupport ψ) {s : ℝ}
    (hs : s ≠ 0) : HasCompactSupport (fun x ↦ ψ (s • x)) :=
  hc.comp_homeomorph (Homeomorph.smulOfNeZero s hs)

theorem divergence_comp_smul {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ)
    (hdiv : ∀ x, PDE.divergence φ x = 0) (s : ℝ) (x : ℝ^n) :
    PDE.divergence (fun y ↦ φ (s • y)) x = 0 := by
  have h : ∀ i : Fin n, PDE.partialDeriv i (fun y ↦ φ (s • y) i) x =
      s * PDE.partialDeriv i (fun y ↦ φ y i) (s • x) := by
    intro i
    have := iteratedPartialDeriv_comp_const_smul [i] (contDiff_component hφ i) s x
    simpa [iteratedPartialDeriv] using this
  simp only [PDE.divergence, h, ← Finset.mul_sum]
  rw [show ∑ i : Fin n, PDE.partialDeriv i (fun y ↦ φ y i) (s • x) = PDE.divergence φ (s • x)
    from rfl, hdiv, mul_zero]

/-- The `H¹` embedding commutes with spatial dilation. -/
theorem testFieldH1_comp_smul {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {s : ℝ} (hs : s ≠ 0) :
    testFieldH1 (fun x ↦ φ (s • x)) (contDiff_comp_smul hφ s) (hasCompactSupport_comp_smul hc hs) =
      dilationH1 n s hs (testFieldH1 φ hφ hc) := by
  ext i : 1
  apply Subtype.ext
  apply PiLp.ext
  intro α
  rw [dilationH1_apply]
  change wkpCoordinateCLM α (testFieldH1 (fun x ↦ φ (s • x)) (contDiff_comp_smul hφ s)
      (hasCompactSupport_comp_smul hc hs) i) =
    wkpCoordinateCLM α (dilationWkpCLM (by norm_num) s hs (testFieldH1 φ hφ hc i))
  rw [dilationWkpCLM_coordinate]
  apply Lp.ext
  have hL := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ)
    (fun x ↦ φ (s • x) i) (contDiff_component (contDiff_comp_smul hφ s) i)
    (hasCompactSupport_component (hasCompactSupport_comp_smul hc hs) i) α
  have hR := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ)
    (fun x ↦ φ x i) (contDiff_component hφ i) (hasCompactSupport_component hc i) α
  have hcomp := (Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^n)) hs).ae_eq_comp
    (show ((testFieldH1 φ hφ hc i : WkpAmbientOn n 1 2 univ) α : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ iteratedPartialDeriv α.toList (fun x ↦ φ x i) x by
        simpa [domainMeasure, testFieldH1] using hR)
  have hsmul := Lp.coeFn_smul (s ^ α.toList.length)
    (Lp.compSMul (domainMeasure n univ) 2 s hs (wkpCoordinateCLM α (testFieldH1 φ hφ hc i)))
  have hcs := Lp.coeFn_compSMul (domainMeasure n univ) 2 s hs
    (wkpCoordinateCLM α (testFieldH1 φ hφ hc i))
  simp only [domainMeasure, Measure.restrict_univ] at hL hsmul hcs ⊢
  filter_upwards [hL, hsmul, hcs, hcomp] with x h1 h2 h3 h4
  rw [show ((wkpCoordinateCLM α (testFieldH1 (fun x ↦ φ (s • x)) (contDiff_comp_smul hφ s)
      (hasCompactSupport_comp_smul hc hs) i) : DerivLp n 2 univ) : ℝ^n → ℝ) x = _ from h1, h2,
    Pi.smul_apply, h3, smul_eq_mul]
  simp only [Function.comp_apply] at h4
  rw [show ((wkpCoordinateCLM α (testFieldH1 φ hφ hc i) : DerivLp n 2 univ) : ℝ^n → ℝ)
      (s • x) = _ from h4]
  exact iteratedPartialDeriv_comp_const_smul α.toList (contDiff_component hφ i) s x

/-- Pairings with a dilated smooth compactly supported function are differentiable in the
dilation factor. -/
theorem hasDerivAt_integral_mul_comp_smul {f : ℝ^n → ℝ} (hf : MemLp f 2 volume)
    {ψ : ℝ^n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) {s₀ : ℝ} (hs₀ : 0 < s₀) :
    HasDerivAt (fun s ↦ ∫ x, f x * ψ (s • x)) (∫ x, f x * fderiv ℝ ψ (s₀ • x) x) s₀ := by
  obtain ⟨R, hR0, hR⟩ : ∃ R, 0 < R ∧ tsupport ψ ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  have hdψ : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hdψc : HasCompactSupport (fderiv ℝ ψ) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨M, hM⟩ := hdψ.bounded_above_of_compact_support hdψc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set ρ : ℝ := 2 * R / s₀
  have hzero : ∀ s ∈ Metric.ball s₀ (s₀ / 2), ∀ x : ℝ^n, ρ < ‖x‖ → fderiv ℝ ψ (s • x) = 0 := by
    intro s hs x hx
    have hs' : s₀ / 2 < s := by
      have := (Metric.mem_ball.mp hs)
      rw [Real.dist_eq] at this
      linarith [abs_lt.mp this]
    have hsx : R < ‖s • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have : ρ * (s₀ / 2) = R := by simp only [ρ]; field_simp
      nlinarith [norm_nonneg x]
    apply fderiv_of_notMem_tsupport
    intro hmem
    have := Metric.mem_closedBall.mp (hR hmem)
    rw [dist_zero_right] at this
    linarith
  set bound : ℝ^n → ℝ := fun x ↦
    ‖f x‖ * (M * ρ) * (Metric.closedBall (0 : ℝ^n) ρ).indicator (fun _ ↦ (1 : ℝ)) x
  have hfm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hbound_int : Integrable bound volume := by
    have hind : MemLp ((Metric.closedBall (0 : ℝ^n) ρ).indicator (fun _ ↦ (1 : ℝ))) 2 volume :=
      memLp_indicator_const 2 (measurableSet_closedBall : MeasurableSet
        (Metric.closedBall (0 : ℝ^n) ρ)).nullMeasurableSet (1 : ℝ)
        (Or.inr (measure_closedBall_lt_top (μ := (volume : Measure (ℝ^n))) (x := 0)
          (r := ρ)).ne)
    have h := (hf.norm.const_mul (M * ρ)).integrable_mul (q := 2) hind
    refine h.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [bound, Pi.mul_apply]
    ring
  have hcomp : ∀ s : ℝ, Continuous fun x : ℝ^n ↦ ψ (s • x) := fun s ↦
    hψ.continuous.comp (continuous_id.const_smul s)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x ↦ f x * ψ (s • x)) (F' := fun s x ↦ f x * fderiv ℝ ψ (s • x) x)
    (Metric.ball_mem_nhds s₀ (half_pos hs₀))
    (Filter.Eventually.of_forall fun s ↦
      (hfm.mul (hcomp s).aestronglyMeasurable :
        AEStronglyMeasurable (fun x ↦ f x * ψ (s • x)) volume)) ?_ ?_ ?_
    hbound_int ?_).2
  · exact hf.integrable_mul (q := 2)
      ((hcomp s₀).memLp_of_hasCompactSupport (hasCompactSupport_comp_smul' hc hs₀.ne'))
  · exact (hfm.mul (((hdψ.comp (continuous_id.const_smul s₀)).clm_apply
      continuous_id).aestronglyMeasurable) :
        AEStronglyMeasurable (fun x ↦ f x * fderiv ℝ ψ (s₀ • x) x) volume)
  · refine Filter.Eventually.of_forall fun x s hs ↦ ?_
    simp only [bound, norm_mul, Real.norm_eq_abs]
    by_cases hx : ‖x‖ ≤ ρ
    · rw [Set.indicator_of_mem (by simpa using hx), mul_one]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc |fderiv ℝ ψ (s • x) x| ≤ ‖fderiv ℝ ψ (s • x)‖ * ‖x‖ := by
            rw [← Real.norm_eq_abs]; exact (fderiv ℝ ψ (s • x)).le_opNorm x
        _ ≤ M * ρ := mul_le_mul (hM _) hx (norm_nonneg _) hM0
    · push Not at hx
      rw [hzero s hs x hx]
      have hρ : 0 ≤ ρ := by simp only [ρ]; positivity
      have hind : 0 ≤ (Metric.closedBall (0 : ℝ^n) ρ).indicator (fun _ ↦ (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ ↦ zero_le_one) x
      simp only [zero_apply, abs_zero, mul_zero]
      positivity
  · refine Filter.Eventually.of_forall fun x s _ ↦ ?_
    have h1 : HasDerivAt (fun s : ℝ ↦ s • x) x s := by
      simpa using (hasDerivAt_id s).smul_const x
    have h2 := ((hψ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt s h1
    exact h2.const_mul (f x)

/-- Smooth compactly supported fields with the property `P`, embedded in `H¹`. -/
def testFieldsOf (P : (ℝ^n → ℝ^n) → Prop) : Set (PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :=
  {v | ∃ (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
    P φ ∧ testFieldH1 φ hφ hc = v}

theorem solenoidalTestFields_eq_testFieldsOf :
    solenoidalTestFields n = testFieldsOf fun φ ↦ ∀ x, PDE.divergence φ x = 0 :=
  rfl

/-- The `L²` pairing of the base rows of two vector `H¹` fields. -/
def massPairing (u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) : ℝ :=
  ∑ i, inner ℝ (wkpBaseCoordinateCLM (u i)) (wkpBaseCoordinateCLM (v i))

theorem massPairing_eq_integral (u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    massPairing u v = ∑ i, ∫ x, (wkpBaseCoordinateCLM (u i) : ℝ^n → ℝ) x *
      (wkpBaseCoordinateCLM (v i) : ℝ^n → ℝ) x := by
  simp only [massPairing, L2.inner_def, domainMeasure, Measure.restrict_univ]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards with x
  rw [real_inner_eq_re_inner, RCLike.re_to_real]
  simp [mul_comm]

theorem max_half_ne_zero (s : ℝ) : max s (1 / 2) ≠ 0 :=
  (lt_of_lt_of_le (by norm_num) (le_max_right s (1 / 2))).ne'

/-- Dilation by `max s (1/2)`, a total and continuous family in the parameter. -/
def dilationH1Half (n : ℕ) (s : ℝ) :
    PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) :=
  dilationH1 n (max s (1 / 2)) (max_half_ne_zero s)

theorem continuous_dilationH1Half_apply (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    Continuous (fun s : ℝ ↦ dilationH1Half n s v) := by
  have hmax : Continuous (fun s : ℝ ↦
      (⟨max s (1 / 2), Set.mem_Ici.mpr (le_max_right _ _)⟩ : Ici (1 / 2 : ℝ))) :=
    (continuous_id.max continuous_const).subtype_mk _
  have hcomp (i : Fin n) : Continuous (fun s : ℝ ↦ dilationWkpCLM (by norm_num)
      (max s (1 / 2)) (max_half_ne_zero s) (v i)) := by
    have h := continuous_dilationWkpCLM_Ici (n := n) (k := 1) (by norm_num : (0 : ℝ) < 1 / 2)
    have hpair : Continuous (fun s : ℝ ↦ ((v i : W^{1,2}(ℝ^n)),
        (⟨max s (1 / 2), Set.mem_Ici.mpr (le_max_right _ _)⟩ : Ici (1 / 2 : ℝ)))) :=
      continuous_const.prodMk hmax
    exact (h.comp hpair).congr fun s ↦ rfl
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hcomp)

theorem dilationH1Half_eq {s : ℝ} (hs : 1 / 2 ≤ s) :
    dilationH1Half n s = dilationH1 n s (lt_of_lt_of_le (by norm_num) hs).ne' := by
  simp only [dilationH1Half]
  congr 1
  exact max_eq_left hs

/-- The mass pairing with a test field is the literal integral against its components. -/
theorem massPairing_testFieldH1 (d : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) {φ : ℝ^n → ℝ^n}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    massPairing d (testFieldH1 φ hφ hc) =
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x * φ x i := by
  rw [massPairing_eq_integral]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  have h := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := univ)
    (fun x ↦ φ x i) (contDiff_component hφ i) (hasCompactSupport_component hc i) (baseIndex n 1)
  have h' : (wkpBaseCoordinateCLM (testFieldH1 φ hφ hc i) : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ φ x i := by
    simpa [domainMeasure, testFieldH1, iteratedPartialDeriv, wkpBaseCoordinateCLM_apply] using h
  filter_upwards [h'] with x hx
  rw [hx]

/-- The derivative of the component field along the dilation direction. -/
theorem fderiv_comp_smul_apply {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (s : ℝ) (x : ℝ^n) :
    fderiv ℝ (fun y ↦ φ (s • y)) x x = s • fderiv ℝ φ (s • x) x := by
  have h1 : HasFDerivAt (fun y : ℝ^n ↦ s • y) (s • ContinuousLinearMap.id ℝ (ℝ^n)) x :=
    (hasFDerivAt_id x).const_smul s
  have h2 : HasFDerivAt (fun y ↦ φ (s • y))
      ((fderiv ℝ φ (s • x)).comp (s • ContinuousLinearMap.id ℝ (ℝ^n))) x :=
    ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x h1
  rw [h2.fderiv]
  simp

private theorem half_le_of_mem_uIcc {t s : ℝ} (ht : 1 / 2 ≤ t) (hs : s ∈ uIcc t 1) : 1 / 2 ≤ s :=
  (le_inf ht (by norm_num)).trans hs.1

/-- For a test field, the mass pairing along dilations is the integral of the drift functional. -/
theorem massPairing_dilation_testFieldH1_sub (P : (ℝ^n → ℝ^n) → Prop)
    (hP : ∀ φ : ℝ^n → ℝ^n, ContDiff ℝ ∞ φ → P φ → ∀ s : ℝ, 0 < s → P (fun x ↦ φ (s • x)))
    (d : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ)
    (hΛ : ∀ (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ), P φ →
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x * fderiv ℝ φ x x i =
        Ψ (testFieldH1 φ hφ hc))
    {φ : ℝ^n → ℝ^n} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hPφ : P φ) {t : ℝ} (ht : 1 / 2 ≤ t) :
    massPairing d (dilationH1Half n t (testFieldH1 φ hφ hc)) -
        massPairing d (testFieldH1 φ hφ hc) =
      -∫ s in t..1, s⁻¹ * Ψ (dilationH1Half n s (testFieldH1 φ hφ hc)) := by
  set g : ℝ → ℝ := fun s ↦ ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x * φ (s • x) i
  have hdm : ∀ i, MemLp (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) 2 volume := fun i ↦ by
    simpa [domainMeasure] using Lp.memLp (wkpBaseCoordinateCLM (d i))
  -- the pairing along dilations is `g`
  have hpair : ∀ s, 1 / 2 ≤ s →
      massPairing d (dilationH1Half n s (testFieldH1 φ hφ hc)) = g s := by
    intro s hs
    have hs0 : s ≠ 0 := (lt_of_lt_of_le (by norm_num) hs).ne'
    rw [dilationH1Half_eq hs, ← testFieldH1_comp_smul hφ hc hs0, massPairing_testFieldH1]
  -- the derivative of `g`
  have hderiv : ∀ s, 1 / 2 ≤ s →
      HasDerivAt g (s⁻¹ * Ψ (dilationH1Half n s (testFieldH1 φ hφ hc))) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hcomp : ∀ i, HasDerivAt (fun s ↦ ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x *
        φ (s • x) i) (∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x *
          fderiv ℝ (fun y ↦ φ y i) (s • x) x) s := fun i ↦
      hasDerivAt_integral_mul_comp_smul (hdm i) (contDiff_component hφ i)
        (hasCompactSupport_component hc i) hs0
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hcomp i
    refine hsum.congr_deriv ?_
    have hfd : ∀ i x, fderiv ℝ (fun y ↦ φ y i) (s • x) x = fderiv ℝ φ (s • x) x i := by
      intro i x
      have := ((EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).hasFDerivAt.comp (s • x)
        ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt)).fderiv
      rw [show (fun y ↦ φ y i) = (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ) ∘ φ from rfl, this]
      rfl
    have hΛs := hΛ (fun y ↦ φ (s • y)) (contDiff_comp_smul hφ s)
      (hasCompactSupport_comp_smul hc hs0.ne') (hP φ hφ hPφ s hs0)
    rw [testFieldH1_comp_smul hφ hc hs0.ne', ← dilationH1Half_eq hs] at hΛs
    rw [← hΛs, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [hfd, fderiv_comp_smul_apply hφ s x, PiLp.smul_apply, smul_eq_mul]
    field_simp
  -- the fundamental theorem of calculus on `[t, 1]`
  have hcont : ContinuousOn (fun s ↦ s⁻¹ * Ψ (dilationH1Half n s (testFieldH1 φ hφ hc)))
      (uIcc t 1) := by
    apply ContinuousOn.mul
    · apply continuousOn_inv₀.mono
      intro s hs
      exact (lt_of_lt_of_le (by norm_num) (half_le_of_mem_uIcc ht hs)).ne'
    · exact (Ψ.continuous.comp (continuous_dilationH1Half_apply _)).continuousOn
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs ↦ hderiv s (half_le_of_mem_uIcc ht hs))
    (hcont.intervalIntegrable)
  rw [hftc, hpair t ht, show massPairing d (testFieldH1 φ hφ hc) = g 1 by
    rw [← hpair 1 (by norm_num), dilationH1Half_eq (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    congr 1
    ext i : 1
    exact (dilationWkpCLM_one (by norm_num) _).symm]
  ring

theorem continuous_dilationH1Half_uncurry :
    Continuous (fun p : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) × ℝ ↦ dilationH1Half n p.2 p.1) := by
  have hmax : Continuous (fun p : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) × ℝ ↦
      (⟨max p.2 (1 / 2), Set.mem_Ici.mpr (le_max_right _ _)⟩ : Ici (1 / 2 : ℝ))) :=
    ((continuous_snd.max continuous_const).subtype_mk _)
  have hcomp (i : Fin n) : Continuous (fun p : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) × ℝ ↦
      dilationWkpCLM (by norm_num) (max p.2 (1 / 2)) (max_half_ne_zero p.2) (p.1 i)) := by
    have h := continuous_dilationWkpCLM_Ici (n := n) (k := 1) (by norm_num : (0 : ℝ) < 1 / 2)
    have hpair : Continuous (fun p : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) × ℝ ↦
        ((p.1 i : W^{1,2}(ℝ^n)),
          (⟨max p.2 (1 / 2), Set.mem_Ici.mpr (le_max_right _ _)⟩ : Ici (1 / 2 : ℝ)))) :=
      ((PiLp.continuous_apply 2 _ i).comp continuous_fst).prodMk hmax
    exact (h.comp hpair).congr fun p ↦ rfl
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hcomp)

/-- The drift integral `v ↦ ∫ₜ¹ s⁻¹ Ψ(v(s ·)) ds`, with the factor frozen below one half. -/
def driftIntegral (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ) (t : ℝ)
    (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) : ℝ :=
  ∫ s in t..1, (max s (1 / 2))⁻¹ * Ψ (dilationH1Half n s v)

theorem continuous_driftIntegral (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ) (t : ℝ) :
    Continuous (driftIntegral Ψ t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have h1 : Continuous fun p : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) × ℝ ↦ (max p.2 (1 / 2))⁻¹ :=
    (continuous_snd.max continuous_const).inv₀ fun p ↦ max_half_ne_zero p.2
  exact h1.mul (Ψ.continuous.comp continuous_dilationH1Half_uncurry)

theorem intervalIntegrable_drift (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ)
    (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) (a b : ℝ) :
    IntervalIntegrable (fun s ↦ (max s (1 / 2))⁻¹ * Ψ (dilationH1Half n s v)) volume a b := by
  apply Continuous.intervalIntegrable
  exact ((continuous_id.max continuous_const).inv₀ fun s ↦ max_half_ne_zero s).mul
    (Ψ.continuous.comp (continuous_dilationH1Half_apply v))

theorem driftIntegral_add (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ) (t : ℝ)
    (u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    driftIntegral Ψ t (u + v) = driftIntegral Ψ t u + driftIntegral Ψ t v := by
  simp only [driftIntegral, map_add, mul_add]
  exact intervalIntegral.integral_add (intervalIntegrable_drift Ψ u t 1)
    (intervalIntegrable_drift Ψ v t 1)

theorem driftIntegral_smul (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ) (t c : ℝ)
    (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    driftIntegral Ψ t (c • v) = c * driftIntegral Ψ t v := by
  simp only [driftIntegral, map_smul, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext s
  ring

theorem massPairing_add_right (d u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    massPairing d (u + v) = massPairing d u + massPairing d v := by
  simp only [massPairing, PiLp.add_apply, map_add, inner_add_right, Finset.sum_add_distrib]

theorem massPairing_smul_right (d v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) (c : ℝ) :
    massPairing d (c • v) = c * massPairing d v := by
  simp only [massPairing, PiLp.smul_apply, map_smul, real_inner_smul_right, Finset.mul_sum]

theorem continuous_massPairing_right (d : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    Continuous (massPairing d) := by
  unfold massPairing
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact continuous_const.inner (wkpBaseCoordinateCLM.continuous.comp (PiLp.continuous_apply 2 _ i))

/-- The integrated dilation identity on the closed span of the test fields with a
dilation-invariant property `P`. -/
theorem massPairing_dilation_sub_of_mem_closure (P : (ℝ^n → ℝ^n) → Prop)
    (hP : ∀ φ : ℝ^n → ℝ^n, ContDiff ℝ ∞ φ → P φ → ∀ s : ℝ, 0 < s → P (fun x ↦ φ (s • x)))
    (d : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ)
    (hΛ : ∀ (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ), P φ →
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x * fderiv ℝ φ x x i =
        Ψ (testFieldH1 φ hφ hc))
    {t : ℝ} (ht : 1 / 2 ≤ t) {v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))}
    (hv : v ∈ (Submodule.span ℝ (testFieldsOf P)).topologicalClosure) :
    massPairing d (dilationH1Half n t v) - massPairing d v = -driftIntegral Ψ t v := by
  set Z : Submodule ℝ (PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :=
    { carrier := {v | massPairing d (dilationH1Half n t v) - massPairing d v =
        -driftIntegral Ψ t v}
      add_mem' := by
        intro u w hu hw
        simp only [Set.mem_ofPred_eq] at hu hw ⊢
        rw [map_add, massPairing_add_right, massPairing_add_right, driftIntegral_add]
        linarith
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, map_zero]
        have h0 := driftIntegral_smul Ψ t 0 0
        rw [zero_smul, zero_mul] at h0
        rw [h0, show massPairing d 0 = 0 by simp [massPairing]]
        ring
      smul_mem' := by
        intro c u hu
        simp only [Set.mem_ofPred_eq] at hu ⊢
        rw [map_smul, massPairing_smul_right, massPairing_smul_right, driftIntegral_smul]
        rw [← mul_sub, hu]
        ring }
  have hS : testFieldsOf P ⊆ Z := by
    rintro _ ⟨φ, hφ, hc, hPφ, rfl⟩
    change _ = _
    rw [massPairing_dilation_testFieldH1_sub P hP d Ψ hΛ hφ hc hPφ ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [max_eq_left (half_le_of_mem_uIcc ht hs)]
  have hclosed : IsClosed (Z : Set (PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))) := by
    apply isClosed_eq
    · exact ((continuous_massPairing_right d).comp (dilationH1Half n t).continuous).sub
        (continuous_massPairing_right d)
    · exact (continuous_driftIntegral Ψ t).neg
  have hle : (Submodule.span ℝ (testFieldsOf P)).topologicalClosure ≤ Z :=
    Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hS) hclosed
  exact hle hv

theorem massPairing_comm (u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    massPairing u v = massPairing v u :=
  Finset.sum_congr rfl fun _ _ ↦ real_inner_comm _ _

theorem massPairing_sub_sub_nonneg (u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    0 ≤ massPairing (u - v) (u - v) := by
  simp only [massPairing]
  exact Finset.sum_nonneg fun i _ ↦ real_inner_self_nonneg

theorem massPairing_sub_sub (u v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    massPairing (u - v) (u - v) = massPairing u u - 2 * massPairing u v + massPairing v v := by
  have hpt : ∀ i : Fin n, inner ℝ (wkpBaseCoordinateCLM ((u - v) i))
      (wkpBaseCoordinateCLM ((u - v) i)) =
      inner ℝ (wkpBaseCoordinateCLM (u i)) (wkpBaseCoordinateCLM (u i)) -
        2 * inner ℝ (wkpBaseCoordinateCLM (u i)) (wkpBaseCoordinateCLM (v i)) +
        inner ℝ (wkpBaseCoordinateCLM (v i)) (wkpBaseCoordinateCLM (v i)) := by
    intro i
    rw [PiLp.sub_apply, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_comm (wkpBaseCoordinateCLM (v i)) (wkpBaseCoordinateCLM (u i))]
    ring
  simp only [massPairing, hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Dilation scales the mass by `t⁻ⁿ`. -/
theorem massPairing_dilationH1 (u : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) {t : ℝ} (ht : 0 < t) :
    massPairing (dilationH1 n t ht.ne' u) (dilationH1 n t ht.ne' u) =
      (t ^ n)⁻¹ * massPairing u u := by
  simp only [massPairing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [dilationH1_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have h := norm_dilationWkpCLM_coordinate (n := n) (k := 1) (p := 2) (by norm_num) t ht.ne'
    (u i) (baseIndex n 1)
  simp only [baseIndex_toList, List.length_nil, pow_zero, one_mul] at h
  change ‖wkpCoordinateCLM (baseIndex n 1) _‖ ^ 2 = _ * ‖wkpCoordinateCLM (baseIndex n 1) _‖ ^ 2
  have hx : 0 ≤ (t ^ n)⁻¹ := by positivity
  rw [h, mul_pow, abs_of_nonneg hx, show ((1 / 2 : ℝ≥0∞).toReal) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt hx]

/-- Dilation identity: if the drift pairing `φ ↦ ⟨d, x·∇φ⟩` agrees with a continuous
linear functional `Ψ` on the test fields with a dilation-invariant property `P`, and `d` lies in
the closed span of these test fields, then `Ψ(d) = -(n/2) ‖d‖²`. -/
theorem drift_eq_neg_half_mul_massPairing (P : (ℝ^n → ℝ^n) → Prop)
    (hP : ∀ φ : ℝ^n → ℝ^n, ContDiff ℝ ∞ φ → P φ → ∀ s : ℝ, 0 < s → P (fun x ↦ φ (s • x)))
    (d : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)))
    (Ψ : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n)) →L[ℝ] ℝ)
    (hΛ : ∀ (φ : ℝ^n → ℝ^n) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ), P φ →
      ∑ i, ∫ x, (wkpBaseCoordinateCLM (d i) : ℝ^n → ℝ) x * fderiv ℝ φ x x i =
        Ψ (testFieldH1 φ hφ hc))
    (hd : d ∈ (Submodule.span ℝ (testFieldsOf P)).topologicalClosure) :
    Ψ d = -((n : ℝ) / 2) * massPairing d d := by
  set m := massPairing d d
  set h : ℝ → ℝ := fun s ↦ (max s (1 / 2))⁻¹ * Ψ (dilationH1Half n s d)
  have hcont : Continuous h :=
    ((continuous_id.max continuous_const).inv₀ fun s ↦ max_half_ne_zero s).mul
      (Ψ.continuous.comp (continuous_dilationH1Half_apply d))
  have h1 : h 1 = Ψ d := by
    simp only [h, dilationH1Half_eq (by norm_num : (1 / 2 : ℝ) ≤ 1)]
    have : dilationH1 n 1 one_ne_zero d = d := by
      ext i : 1
      exact dilationWkpCLM_one (by norm_num) _
    rw [show max (1 : ℝ) (1 / 2) = 1 by norm_num, inv_one, one_mul]
    congr 1
  -- the averaged drift converges to `Ψ d` from both sides
  have hG : HasDerivAt (fun t ↦ driftIntegral Ψ t d) (-h 1) 1 :=
    intervalIntegral.integral_hasDerivAt_left (hcont.intervalIntegrable _ _)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hG1 : driftIntegral Ψ 1 d = 0 := by simp [driftIntegral]
  have hlimG : Tendsto (fun t ↦ driftIntegral Ψ t d / (1 - t)) (𝓝[≠] 1) (𝓝 (Ψ d)) := by
    rw [← h1]
    refine (hG.tendsto_slope.neg.congr' ?_).trans (by simp)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t - 1 ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp ht)
    have ht'' : 1 - t ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp ht).symm
    simp only [slope_def_field, hG1, sub_zero]
    field_simp
    ring
  -- the Jacobian quotient converges to `n`
  have hJ : HasDerivAt (fun t : ℝ ↦ t ^ (-(n : ℤ))) (-(n : ℝ)) 1 := by
    have := hasDerivAt_zpow (-(n : ℤ)) (1 : ℝ) (Or.inl one_ne_zero)
    simpa using this
  have hlimJ : Tendsto (fun t : ℝ ↦ -(1 / 2) * ((t ^ (-(n : ℤ)) - 1) / (1 - t)) * m) (𝓝[≠] 1)
      (𝓝 (-((n : ℝ) / 2) * m)) := by
    have hq : Tendsto (fun t : ℝ ↦ (t ^ (-(n : ℤ)) - 1) / (1 - t)) (𝓝[≠] 1) (𝓝 (n : ℝ)) := by
      refine (hJ.tendsto_slope.neg.congr' ?_).trans (by simp)
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t - 1 ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp ht)
      simp only [slope_def_field, one_zpow]
      rw [show (1 : ℝ) - t = -(t - 1) by ring, div_neg]
    convert ((hq.const_mul (-(1 / 2))).mul_const m) using 2
    ring
  -- the inequality `‖d(t ·) - d‖² ≥ 0` in terms of the drift integral
  have hkey : ∀ t : ℝ, 1 / 2 < t → -(1 / 2) * ((t ^ n)⁻¹ - 1) * m ≤ driftIntegral Ψ t d := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hid := massPairing_dilation_sub_of_mem_closure P hP d Ψ hΛ ht.le hd
    rw [dilationH1Half_eq ht.le] at hid
    have hsq := massPairing_sub_sub_nonneg (dilationH1 n t ht0.ne' d) d
    rw [massPairing_sub_sub, massPairing_dilationH1 d ht0,
      massPairing_comm (dilationH1 n t ht0.ne' d) d] at hsq
    simp only [m]
    nlinarith
  have hzpow : ∀ t : ℝ, t ^ (-(n : ℤ)) = (t ^ n)⁻¹ := fun t ↦ by simp [zpow_neg]
  have hlt : 𝓝[<] (1 : ℝ) ≤ 𝓝[≠] 1 := nhdsWithin_mono _ fun t ht ↦ ne_of_lt ht
  have hgt : 𝓝[>] (1 : ℝ) ≤ 𝓝[≠] 1 := nhdsWithin_mono _ fun t ht ↦ (Set.mem_Ioi.mp ht).ne'
  have hlow : -((n : ℝ) / 2) * m ≤ Ψ d := by
    refine le_of_tendsto_of_tendsto (hlimJ.mono_left hlt) (hlimG.mono_left hlt) ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)] with t ht
    have hpos : 0 < 1 - t := by linarith [ht.2]
    rw [hzpow]
    calc -(1 / 2) * (((t ^ n)⁻¹ - 1) / (1 - t)) * m =
          (-(1 / 2) * ((t ^ n)⁻¹ - 1) * m) / (1 - t) := by ring
      _ ≤ driftIntegral Ψ t d / (1 - t) :=
          (div_le_div_iff_of_pos_right hpos).mpr (hkey t ht.1)
  have hup : Ψ d ≤ -((n : ℝ) / 2) * m := by
    refine le_of_tendsto_of_tendsto (hlimG.mono_left hgt) (hlimJ.mono_left hgt) ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)] with t ht
    have hneg : 1 - t < 0 := by linarith [ht.1]
    rw [hzpow]
    calc driftIntegral Ψ t d / (1 - t) ≤ (-(1 / 2) * ((t ^ n)⁻¹ - 1) * m) / (1 - t) :=
          div_le_div_of_nonpos_of_le hneg.le (hkey t (by linarith [ht.1]))
      _ = -(1 / 2) * (((t ^ n)⁻¹ - 1) / (1 - t)) * m := by ring
  exact le_antisymm hup hlow

end NavierStokes.Stationary
