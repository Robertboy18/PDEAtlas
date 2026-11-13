/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.RegularLevel
public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.Parameter
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.LowerReturn

import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Physical speed and initial displacement for one prescribed clock

The thresholds `A,B` are fixed at the reference fast states. The parameter
is `(μ,a)`, and the initial state is `(a,1)`. The equations are
`X' = prescribedClockField A B Z X - μ * X` and `Z' = (2-μ) * Z`.

The reference trajectory and its upward 205 passage are hypotheses.
One application of the finite-interval theorem constructs the family.
Two applications of RegularLevel to that same family continue the upward passage
and the late zero. Both parameterized event maps are constructed from those passages.

The upward speed is `g 205 + 1 - 205*μ`, hence `g 205 + 1` on the zero-speed slice.
The late-zero speed stays `-8`.
-/

@[expose] public noncomputable section

open Filter Set
open PDE.Analysis PDE.Analysis.NormalizedPulse
open scoped Topology ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- The prescribed field at log-cosh parameter zero and physical speed `μ`.
The input is `(μ,(x,z))`; both thresholds remain fixed. -/
def prescribedSpeedField (A B : ℝ) (p : ℝ × (ℝ × ℝ)) : ℝ × ℝ :=
  (prescribedClockField A B p.2.2 p.2.1 - p.1 * p.2.1, (2 - p.1) * p.2.2)

/-- Fixed thresholds make the physical speed field globally smooth in speed and state. -/
theorem contDiff_prescribedSpeedField (A B : ℝ) :
    ContDiff ℝ ∞ (prescribedSpeedField A B) :=
  (((contDiff_prescribedClockField A B).comp (contDiff_snd.snd.prodMk contDiff_snd.fst)).sub
    (contDiff_fst.mul contDiff_snd.fst)).prodMk
      ((contDiff_const.sub contDiff_fst).mul contDiff_snd.snd)

/-- One speed/displacement family through the prescribed reference
has a smooth upward 205 passage `Bhit` and a smooth late zero `L`. Both event maps
use one common neighborhood, and their time derivatives are derived from
strict switching margins. Uniqueness is stated as a germ at each reference event. -/
theorem exists_prescribed_speed_family_events (A B : ℝ) {X Z : ℝ → ℝ} {T d τ0 b₀ : ℝ} (hA : A = Z T)
    (hB : B = Z (T + 1 / 2)) (hXzero : X 0 = 0) (hZzero : Z 0 = 1)
    (hZ : ∀ t, HasDerivAt Z (2 * Z t) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) (hd : T + 1 / 2 < d)
    (hτ0 : d < τ0) (hb₀ : b₀ ∈ Ioo (1 : ℝ) T)
    (hX : ∀ t, HasDerivAt X (prescribedClockField A B (Z t) (X t)) t) (hhit : X b₀ = 205)
    (hzero : X τ0 = 0) :
    ∃ (F : ℝ × (ℝ × ℝ) → ℝ × ℝ) (N : Set (ℝ × ℝ))
      (L Bhit : ℝ × ℝ → ℝ),
      IsOpen N ∧ (0, 0) ∈ N ∧ (∀ p ∈ N, |p.1| < 1 / 410) ∧
      ContDiff ℝ ∞ F ∧ (∀ p, F (0, p) = (p.2, 1)) ∧
      EqOn (fun t ↦ F (t, (0, 0))) (fun t ↦ (X t, Z t))
        (Icc (-1 : ℝ) (τ0 + 1)) ∧
      (∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
        HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t) ∧
      ContDiffOn ℝ ∞ L N ∧ ContDiffOn ℝ ∞ Bhit N ∧
      L (0, 0) = τ0 ∧ Bhit (0, 0) = b₀ ∧
      (∀ p ∈ N, L p ∈ Ioo d (τ0 + 1) ∧ (F (L p, p)).1 = 0 ∧
        B ^ 2 < (F (L p, p)).2 ^ 2 ∧
        HasDerivAt (fun t ↦ (F (t, p)).1) (-8) (L p)) ∧
      (∀ p ∈ N, Bhit p ∈ Ioo (1 : ℝ) T ∧ (F (Bhit p, p)).1 = 205 ∧
        2 < (F (Bhit p, p)).2 ∧ (F (Bhit p, p)).2 ^ 2 < A ^ 2 ∧
        HasDerivAt (fun t ↦ (F (t, p)).1) (g 205 + 1 - 205 * p.1) (Bhit p) ∧
        0 < g 205 + 1 - 205 * p.1) ∧
      (∀ᶠ p in 𝓝 ((0, 0), τ0), (F (p.2, p.1)).1 = 0 ↔ L p.1 = p.2) ∧
      (∀ᶠ p in 𝓝 ((0, 0), b₀), (F (p.2, p.1)).1 = 205 ↔ Bhit p.1 = p.2) := by
  have hT : 1 ≤ T := (hb₀.1.trans hb₀.2).le
  have hT0 : 0 ≤ T := by linarith only [hT]
  have hS0 : 0 ≤ T + 1 / 2 := by linarith only [hT]
  have hdpos : 0 < d := by linarith only [hT, hd]
  have hτpos : 0 < τ0 := hdpos.trans hτ0
  have hZfast (t : ℝ) : HasDerivAt Z (fastLogCosh 0 (Z t)) t := by
    simpa only [fastLogCosh, zero_mul, add_zero] using hZ t
  have hZsq := ClockSwitch.strictMonoOn_fast_clock_sq (δ := 0)
    (by norm_num) hZfast hZlower
  have hab : A ^ 2 < B ^ 2 := by rw [hA, hB]; exact hZsq hT0 hS0 (by linarith)
  have hlateMargin : B ^ 2 < Z τ0 ^ 2 := by rw [hB]; exact hZsq hS0 hτpos.le (hd.trans hτ0)
  have hb0 : 0 ≤ b₀ := by linarith only [hb₀.1]
  have hinnerMargin : 2 < Z b₀ := by linarith only [hZlower b₀ hb0, hb₀.1]
  have houterMargin : Z b₀ ^ 2 < A ^ 2 := by rw [hA]; exact hZsq hb0 hT0 hb₀.2
  have hupfield (z y : ℝ) (hz : 2 < z) (hza : z ^ 2 < A ^ 2) :
      prescribedClockField A B z y = g y + 1 := by
    have hi : transition (z ^ 2 - 1) = 1 := by
      apply transition_of_one_le
      nlinarith only [hz, sq_nonneg (z - 2)]
    simp only [prescribedClockField, clockFeedback_of_sq_le hab hza.le,
      outerTransition_of_sq_le hab hza.le, hi, mul_zero, sub_zero]
  have hXlate : prescribedClockField A B (Z τ0) 0 = -8 := by
    rw [prescribedClockField_eq_lower hab hlateMargin.le, lowerClockField_zero]
  have hXup : prescribedClockField A B (Z b₀) 205 = g 205 + 1 :=
    hupfield _ _ hinnerMargin houterMargin
  have hXd : Differentiable ℝ X := fun t ↦ (hX t).differentiableAt
  have hZd : Differentiable ℝ Z := fun t ↦ (hZ t).differentiableAt
  obtain ⟨Φ, U, hU, hbaseU, hΦ, hΦzero, hsame, hΦode⟩ :=
    PDE.Analysis.ODE.exists_contDiff_infty_parameterized_family_near_solution_Icc
      (prescribedSpeedField A B) (contDiff_prescribedSpeedField A B)
      (a := -1) (b := τ0 + 1) (by norm_num) (by linarith only [hτpos])
      0 (fun t ↦ (X t, Z t)) (hXd.continuous.prodMk hZd.continuous).continuousOn
      (fun t _ ↦ by
        simpa only [prescribedSpeedField, zero_mul, sub_zero] using (hX t).prodMk (hZ t))
      (0, 1) (Prod.ext hXzero hZzero)
  let F : ℝ × (ℝ × ℝ) → ℝ × ℝ := fun p ↦ Φ (p.1, (p.2.1, (p.2.2, 1)))
  let V₀ : Set (ℝ × ℝ) := {p | (p.1, (p.2, 1)) ∈ U} ∩ {p | |p.1| < 1 / 410}
  have hF : ContDiff ℝ ∞ F :=
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk contDiff_const)))
  have hV₀ : IsOpen V₀ :=
    (hU.preimage (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))).inter
      (isOpen_lt continuous_fst.abs continuous_const)
  have hbaseV₀ : (0, 0) ∈ V₀ := ⟨hbaseU, by norm_num⟩
  have hFode (p : ℝ × ℝ) (hp : p ∈ V₀) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) (τ0 + 1)) :
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t :=
    hΦode (p.1, (p.2, 1)) hp.1 t ht
  have hFsame {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) (τ0 + 1)) : F (t, (0, 0)) = (X t, Z t) := hsame ht
  have hlateTime : τ0 ∈ Icc (-1 : ℝ) (τ0 + 1) := by
    constructor <;> linarith only [hτpos]
  have hupTime : b₀ ∈ Icc (-1 : ℝ) (τ0 + 1) := by
    constructor <;> linarith only [hb₀.1, hb₀.2, hd, hτ0]
  have hfirst (p : ℝ × ℝ) (hp : p ∈ V₀) (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) (τ0 + 1)) :
      HasDerivAt (fun s ↦ (F (s, p)).1) (prescribedSpeedField A B (p.1, F (t, p))).1 t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hFode p hp t ht)
  -- Both regular-level applications use the same constructed scalar function.
  let R : (ℝ × ℝ) × ℝ → ℝ := fun p ↦ (F (p.2, p.1)).1
  have hR : ContDiff ℝ ∞ R := (hF.comp (contDiff_snd.prodMk contDiff_fst)).fst
  have hpartial (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) (τ0 + 1)) : fderiv ℝ R ((0, 0), t) (0, 1) =
        (prescribedSpeedField A B (0, F (t, (0, 0)))).1 := by
    have hc : HasDerivAt (fun s ↦ R ((0, 0), s))
        (fderiv ℝ R ((0, 0), t) (0, 1)) t := by
      simpa only [Function.comp_def] using
        ((hR.differentiable (by simp)) ((0, 0), t)).hasFDerivAt.comp_hasDerivAt t
          ((hasDerivAt_const t ((0, 0) : ℝ × ℝ)).prodMk (hasDerivAt_id t))
    exact hc.unique (hfirst (0, 0) hbaseV₀ t ht)
  have hpartialLate : fderiv ℝ R ((0, 0), τ0) (0, 1) ≠ 0 := by
    rw [hpartial τ0 hlateTime, hFsame hlateTime]
    simp only [prescribedSpeedField, hzero, hXlate, zero_mul, sub_zero]
    norm_num
  have hpartialUp : fderiv ℝ R ((0, 0), b₀) (0, 1) ≠ 0 := by
    rw [hpartial b₀ hupTime, hFsame hupTime]
    simp only [prescribedSpeedField, hhit, hXup, zero_mul, sub_zero]
    linarith only [g_nonneg (205 : ℝ)]
  have hRlate : R ((0, 0), τ0) = 0 := (congrArg Prod.fst (hFsame hlateTime)).trans hzero
  have hRup : R ((0, 0), b₀) = 205 := (congrArg Prod.fst (hFsame hupTime)).trans hhit
  have hz : Continuous (fun p : (ℝ × ℝ) × ℝ ↦ (F (p.2, p.1)).2) :=
    (hF.continuous.comp (continuous_snd.prodMk continuous_fst)).snd
  let Dlate : Set ((ℝ × ℝ) × ℝ) := (V₀ ×ˢ Ioo d (τ0 + 1)) ∩ {p | B ^ 2 < (F (p.2, p.1)).2 ^ 2}
  let Dup : Set ((ℝ × ℝ) × ℝ) := (V₀ ×ˢ Ioo (1 : ℝ) T) ∩
      {p | 2 < (F (p.2, p.1)).2 ∧ (F (p.2, p.1)).2 ^ 2 < A ^ 2}
  have hDlate : IsOpen Dlate := (hV₀.prod isOpen_Ioo).inter (isOpen_lt continuous_const (hz.pow 2))
  have hDup : IsOpen Dup := (hV₀.prod isOpen_Ioo).inter
    ((isOpen_lt continuous_const hz).inter (isOpen_lt (hz.pow 2) continuous_const))
  have hbaseLate : ((0, 0), τ0) ∈ Dlate := ⟨⟨hbaseV₀, hτ0, by linarith⟩,
    show B ^ 2 < (F (τ0, (0, 0))).2 ^ 2 by simpa only [hFsame hlateTime] using hlateMargin⟩
  have hbaseUp : ((0, 0), b₀) ∈ Dup := ⟨⟨hbaseV₀, hb₀⟩,
    show 2 < (F (b₀, (0, 0))).2 ∧ (F (b₀, (0, 0))).2 ^ 2 < A ^ 2 by
      simpa only [hFsame hupTime] using And.intro hinnerMargin houterMargin⟩
  obtain ⟨L, VL, hVL, hbaseVL, hL, hLbase, hLgraph, hLunique⟩ :=
    (hR.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) R Dlate).exists_implicitFunction_of_fderiv_snd_ne_zero
      hDlate (by simp) hbaseLate hpartialLate
  obtain ⟨Bhit, VB, hVB, hbaseVB, hBhit, hBbase, hBgraph, hBunique⟩ :=
    (hR.contDiffOn : ContDiffOn ℝ (⊤ : ℕ∞) R Dup).exists_implicitFunction_of_fderiv_snd_ne_zero
      hDup (by simp) hbaseUp hpartialUp
  let N : Set (ℝ × ℝ) := VL ∩ VB
  have hNsub : N ⊆ V₀ := fun p hp ↦ (hLgraph p hp.1).1.1.1
  refine ⟨F, N, L, Bhit, hVL.inter hVB, ⟨hbaseVL, hbaseVB⟩,
    fun p hp ↦ (hNsub hp).2, hF, fun p ↦ hΦzero (p.1, (p.2, 1)), fun t ht ↦ hFsame ht,
    fun p hp t ht ↦ hFode p (hNsub hp) t ht, hL.mono inter_subset_left,
    hBhit.mono inter_subset_right, hLbase, hBbase, fun p hp ↦ ?_, fun p hp ↦ ?_,
    hLunique.mono fun p hp ↦ by simpa only [hRlate, R] using hp,
    hBunique.mono fun p hp ↦ by simpa only [hRup, R] using hp⟩
  · obtain ⟨⟨⟨-, htime⟩, hmargin⟩, hlevel⟩ := hLgraph p hp.1
    have hvalue : (F (L p, p)).1 = 0 := hlevel.trans hRlate
    refine ⟨htime, hvalue, hmargin, ?_⟩
    simpa only [prescribedSpeedField, hvalue, prescribedClockField_eq_lower hab hmargin.le,
      lowerClockField_zero, mul_zero, sub_zero] using
      hfirst p (hNsub hp) (L p) ⟨by linarith only [hdpos, htime.1], htime.2.le⟩
  · obtain ⟨⟨⟨-, htime⟩, hmargin⟩, hlevel⟩ := hBgraph p hp.2
    have hvalue : (F (Bhit p, p)).1 = 205 := hlevel.trans hRup
    refine ⟨htime, hvalue, hmargin.1, hmargin.2, ?_, ?_⟩
    · simpa only [prescribedSpeedField, hvalue, hupfield _ 205 hmargin.1 hmargin.2, mul_comm]
        using hfirst p (hNsub hp) (Bhit p) ⟨by linarith only [htime.1, htime.2, hd, hτ0],
          by linarith only [htime.1, htime.2, hd, hτ0]⟩
    · linarith only [(le_abs_self p.1).trans_lt (hNsub hp).2, g_nonneg (205 : ℝ)]

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
