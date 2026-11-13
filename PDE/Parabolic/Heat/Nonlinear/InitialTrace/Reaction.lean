/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.SignedWeight
public import PDE.Parabolic.Heat.Nonlinear.CompactInitialTrace
public import PDE.Parabolic.Heat.Nonlinear.InitialMomentTrace
import Mathlib.MeasureTheory.Integral.Prod
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity
import CAS.ExactTactic

/-!
# Reaction integrability from compact testing

Compact tests bound the quadratic reaction on translated positive-time strips.
A uniform negative weighted moment makes these bounds independent of the initial
time shift. Fatou then gives reaction integrability down to the initial time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology ENNReal

namespace HeatEquation.Nonlinear

/-- Endpoint moment bounds and a lower bound on the Laplacian pairing control
the time integral of the compactly tested quadratic reaction. -/
theorem compact_square_integral_le_of_pairing_lower
    {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ} {T M K L : ℝ}
    (hΩ : IsOpen Ω) (hT : 0 ≤ T)
    (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω))
    (heq : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hk : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω)
    (hzero : -K ≤ ∫ x, φ x * u 0 x)
    (hend : (∫ x, φ x * u T x) ≤ M)
    (hlow : ∀ t ∈ Ioo 0 T, -L ≤ ∫ x, laplacian φ x * u t x) :
    (∫ t in 0..T, ∫ x, φ x * u t x ^ 2) ≤ M + K + L * T := by
  have hi := compact_moment_eq_initial_add_integral hΩ hc hs heq
    (g := u 0) (fun _ _ ↦ rfl) hφ hk hφΩ ⟨hT, le_rfl⟩
  have hR := intervalIntegrable_compact_square_of_initial_continuity hc
    hφ.continuous hk hφΩ ⟨hT, le_rfl⟩
  have hsupp : tsupport (laplacian φ) ⊆ tsupport φ :=
    closure_minimal (fun x hx ↦ Classical.byContradiction fun hxφ ↦
      hx (EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hxφ)) (isClosed_tsupport φ)
  have hLc := continuousOn_compact_moment_of_initial_continuity hc
    hφ.continuous_coordinate_laplacian hk.coordinate_laplacian (hsupp.trans hφΩ)
  have hL : IntervalIntegrable (fun r ↦ ∫ x, laplacian φ x * u r x) volume 0 T :=
    hLc.intervalIntegrable_of_Icc hT
  have h := intervalIntegral.integral_mono_on_of_le_Ioo hT
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ -L) volume 0 T) hL hlow
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  rw [intervalIntegral.integral_add hL hR] at hi
  nlinarith only [hi, h, hzero, hend]

/-- A uniform bound on the weighted negative moment controls the quadratic
reaction on every positive-time strip, with a constant independent of its
initial time. Compact tests may approach the full eigenfunction as closely as
needed; their admissible threshold depends on the strip. -/
theorem exists_dirichletTest_reaction_bound_of_negative_moment
    {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ} {w : ℝ^n → ℝ}
    {lambda K a T : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda)
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    (hnegative : ∀ t > 0, (∫ x in Ω, w x * max (-u t x) 0) ≤ K)
    (ha : 0 < a) (hT : 0 ≤ T) :
    ∃ e > 0, ∀ ε > 0, ε ≤ e →
      (∫ t in 0..T, ∫ x, dirichletTest Ω w ε x * u (a + t) x ^ 2) ≤
        lambda + 2 * K + (lambda * (lambda + K) + lambda + 1) * T := by
  have hcont : ContinuousOn (fun q : ℝ × ℝ^n ↦ u (a + q.1) q.2)
      (Icc 0 T ×ˢ closure Ω) :=
    hc.comp ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq ↦ ⟨by change 0 < a + q.1; linarith [hq.1.1], hq.2⟩)
  have huc (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContinuousOn (u (a + t)) (closure Ω) :=
    hcont.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hx ↦ ⟨ht, hx⟩)
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_Icc.prod hb.isCompact_closure).exists_bound_of_continuousOn hcont
  let B := max B₀ 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hBu (t : ℝ) (ht : t ∈ Icc 0 T) (x : ℝ^n) (hx : x ∈ Ω) : |u (a + t) x| ≤ B :=
    (Real.norm_eq_abs _ ▸ hB₀ (t, x) ⟨ht, subset_closure hx⟩).trans
      (le_add_of_le_of_nonneg (le_max_left B₀ 0) zero_le_one)
  have hwstrip : ContinuousOn (fun q : ℝ × ℝ^n ↦ w q.2)
      (Icc 0 T ×ˢ closure Ω) :=
    hwc.comp continuous_snd.continuousOn (fun _ hq ↦ hq.2)
  obtain ⟨e₀, he₀, helayer⟩ := exists_pos_weight_layer
    (isCompact_Icc.prod hb.isCompact_closure) hwstrip hcont (fun q hq ↦ by
      by_cases hx : q.2 ∈ Ω
      · exact (hwpos q.2 hx).le
      · rw [hwzero q.2 ⟨hq.2, fun h ↦ hx (interior_subset h)⟩])
    (fun q hq hz ↦ by
      have hx : q.2 ∈ frontier Ω := ⟨hq.2, fun h ↦
        (hwpos q.2 (interior_subset h)).ne' hz⟩
      exact hboundary q.2 hx (a + q.1) (by linarith [hq.1.1])) (η := 1) zero_lt_one
  obtain ⟨e₁, he₁, herr₁⟩ := exists_pos_mul_lt zero_lt_one
    (2 * lambda * (1 + B) * volume.real Ω)
  refine ⟨min e₀ e₁, lt_min he₀ he₁, ?_⟩
  intro ε hε hεe
  have hε₀ : ε ≤ e₀ := hεe.trans (min_le_left _ _)
  have hε₁ : ε ≤ e₁ := hεe.trans (min_le_right _ _)
  have herr : (2 * lambda * ε) * (1 + B) * volume.real Ω ≤ 1 := by
    have h := (mul_le_mul_of_nonneg_left hε₁
      (by positivity : 0 ≤ 2 * lambda * (1 + B) * volume.real Ω)).trans_lt herr₁
    nlinarith only [h]
  let φ := dirichletTest Ω w ε
  have hφ : ContDiff ℝ 2 φ := contDiff_dirichletTest hΩ hε hw hwc hwzero
  have hk : HasCompactSupport φ := hasCompactSupport_dirichletTest hb hε hwc hwzero
  have hφΩ : tsupport φ ⊆ Ω := tsupport_dirichletTest_subset hε hwc hwzero
  have hwn : ∀ x ∈ Ω, 0 ≤ w x := fun x hx ↦ (hwpos x hx).le
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have hmom (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ x, φ x * u (a + t) x) ∈ Icc (-K) (lambda + K) := by
    have htest := integral_mul_mem_Icc_of_le_weight
      (hint (hφ.continuous.continuousOn.mul (huc t ht)))
      (hint (hwc.mul (huc t ht)))
      (hint (hwc.mul ((huc t ht).neg.sup continuousOn_const))) (by
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        exact ⟨(dirichletTest_bounds hwn x).1,
          by simpa only [indicator_of_mem hx] using (dirichletTest_bounds hwn x).2⟩)
    have hφeq : (∫ x in Ω, φ x * u (a + t) x) = ∫ x, φ x * u (a + t) x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφΩ h)), zero_mul]
    have htpos : 0 < a + t := by linarith [ht.1]
    have hM := moment_le_eigenvalue_of_global_dirichlet_square_solution
      hΩ hb hw hwc hwzero hwpos hunit heigen hlambda hc hs heq hboundary htpos
    have hN := hnegative (a + t) htpos
    rw [hφeq] at htest
    exact ⟨by linarith [htest.1], by linarith [htest.2]⟩
  have hlow (t : ℝ) (ht : t ∈ Ioo 0 T) :
      -(lambda * (lambda + K) + lambda + 1) ≤
        ∫ x, laplacian φ x * u (a + t) x := by
    have ht' : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
    have h := dirichletTest_laplacian_pairing_lower hΩ hb hε hlambda.le
      (by norm_num : (0 : ℝ) ≤ 1) hB.le hw hwc hwzero hwn hunit.le heigen
      (huc t ht') (hBu t ht') (fun x hx hxw ↦
        (helayer (t, x) ⟨ht', subset_closure hx⟩
          (hxw.trans (mul_le_mul_of_nonneg_left hε₀ (by norm_num)))).le)
    have hmul := mul_le_mul_of_nonneg_left (hmom t ht').2 hlambda.le
    dsimp only [φ] at hmul ⊢
    nlinarith only [h, hmul, herr]
  have hsi : ContDiffOn ℝ 2 (fun q : ℝ × ℝ^n ↦ u (a + q.1) q.2)
      (Ioo 0 T ×ˢ Ω) :=
    hs.comp ((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq ↦ ⟨by change 0 < a + q.1; linarith [hq.1.1], hq.2⟩)
  have heqi (t : ℝ) (ht : t ∈ Ioo 0 T) (x : ℝ^n) (hx : x ∈ Ω) :
      deriv (fun r ↦ u (a + r) x) t - laplacian (u (a + t)) x =
        u (a + t) x ^ 2 := by
    rw [deriv_comp_const_add (fun r ↦ u r x) a t]
    exact heq (a + t) (by linarith [ht.1]) x hx
  have h := compact_square_integral_le_of_pairing_lower
    (u := fun t x ↦ u (a + t) x) hΩ hT
    (hcont.mono (prod_mono Subset.rfl subset_closure)) hsi heqi hφ hk hφΩ
    (hmom 0 ⟨le_rfl, hT⟩).1 (hmom T ⟨hT, le_rfl⟩).2 hlow
  exact h.trans_eq (by cas)

/-- Compact Dirichlet tests converge pointwise to the positive weight as the
cutoff parameter tends to zero. -/
theorem tendsto_dirichletTest_of_tendsto_zero
    {n : ℕ} {Ω : Set (ℝ^n)} {w : ℝ^n → ℝ} {ε : ℕ → ℝ}
    (hwpos : ∀ x ∈ Ω, 0 ≤ w x) (hε : ∀ k, 0 < ε k)
    (hlim : Tendsto ε atTop (𝓝 0)) {x : ℝ^n} (hx : x ∈ Ω) :
    Tendsto (fun k ↦ dirichletTest Ω w (ε k) x) atTop (𝓝 (w x)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun k ↦ w x - 2 * ε k) atTop (𝓝 (w x)) by
      simpa using tendsto_const_nhds.sub (hlim.const_mul 2)) tendsto_const_nhds
  · exact fun k ↦ sub_two_mul_le_dirichletTest (hε k) hwpos hx
  · intro k
    simpa only [indicator_of_mem hx] using (dirichletTest_bounds (ε := ε k) hwpos x).2

/-- A uniform negative eigenfunction moment gives integrability of the
quadratic reaction down to time zero. The reaction integrability is proved by
Fatou on spacetime, using compact tests on translated positive-time strips. -/
theorem integrableOn_weighted_square_of_negative_moment
    {n : ℕ} {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ} {w : ℝ^n → ℝ}
    {lambda K T : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda)
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    (hnegative : ∀ t > 0, (∫ x in Ω, w x * max (-u t x) 0) ≤ K)
    (hT : 0 < T) :
    IntegrableOn (fun t ↦ ∫ x in Ω, w x * u t x ^ 2) (Ioc 0 T) := by
  classical
  let a : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hext (k : ℕ) := exists_dirichletTest_reaction_bound_of_negative_moment
    hΩ hb hw hwc hwzero hwpos hunit heigen hlambda hc hs heq hboundary hnegative
    (ha k) hT.le
  choose e he hbound using hext
  let ε : ℕ → ℝ := fun k ↦ min (e k) (a k)
  have hε (k : ℕ) : 0 < ε k := lt_min (he k) (ha k)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (hε k).le) (fun k ↦ min_le_right (e k) (a k)) halim
  let μ : Measure (ℝ × ℝ^n) :=
    (volume.restrict (Ioc 0 T)).prod (volume.restrict Ω)
  let F : ℕ → ℝ × ℝ^n → ℝ := fun k q ↦
    dirichletTest Ω w (ε k) q.2 * u (a k + q.1) q.2 ^ 2
  have hφ (k : ℕ) : ContDiff ℝ 2 (dirichletTest Ω w (ε k)) :=
    contDiff_dirichletTest hΩ (hε k) hw hwc hwzero
  have hφΩ (k : ℕ) : tsupport (dirichletTest Ω w (ε k)) ⊆ Ω :=
    tsupport_dirichletTest_subset (hε k) hwc hwzero
  have hFi (k : ℕ) : Integrable (F k) μ := by
    have hcont : ContinuousOn (fun q : ℝ × ℝ^n ↦ u (a k + q.1) q.2)
        (Icc 0 T ×ˢ closure Ω) :=
      hc.comp ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
        (fun q hq ↦ ⟨by change 0 < a k + q.1; linarith [ha k, hq.1.1], hq.2⟩)
    have hFc : ContinuousOn (F k) (Icc 0 T ×ˢ closure Ω) :=
      ((hφ k).continuous.comp continuous_snd).continuousOn.mul (hcont.pow 2)
    have hsub : Ioc 0 T ×ˢ Ω ⊆ Icc 0 T ×ˢ closure Ω :=
      prod_mono Ioc_subset_Icc_self subset_closure
    have hK : IsCompact (Icc (0 : ℝ) T ×ˢ closure Ω) := isCompact_Icc.prod hb.isCompact_closure
    dsimp only [μ]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hFc.integrableOn_of_subset_isCompact hK (measurableSet_Ioc.prod hΩ.measurableSet) hsub
      ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
  have hI (k : ℕ) : (∫ q, F k q ∂μ) =
      ∫ t in 0..T, ∫ x, dirichletTest Ω w (ε k) x * u (a k + t) x ^ 2 := by
    rw [intervalIntegral.integral_of_le hT.le, integral_prod (F k) (hFi k)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
    dsimp only [F]
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφΩ k h)), zero_mul]
  have hmem : ∀ᵐ q ∂μ, q ∈ Ioc 0 T ×ˢ Ω := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioc.prod hΩ.measurableSet)
  have hlim : ∀ᵐ q ∂μ, Tendsto (fun k ↦ F k q) atTop
      (𝓝 (w q.2 * u q.1 q.2 ^ 2)) := by
    filter_upwards [hmem] with q hq
    have huAt : ContinuousAt u.uncurry q :=
      hs.continuousOn.continuousAt ((isOpen_Ioi.prod hΩ).mem_nhds ⟨hq.1.1, hq.2⟩)
    have hqLim : Tendsto (fun k ↦ (a k + q.1, q.2)) atTop (𝓝 q) := by
      simpa only [zero_add, Prod.mk.eta] using
        (halim.add_const q.1).prodMk_nhds (tendsto_const_nhds (x := q.2))
    exact (tendsto_dirichletTest_of_tendsto_zero (fun x hx ↦ (hwpos x hx).le)
      hε hεlim hq.2).mul ((huAt.tendsto.comp hqLim).pow 2)
  have hG := integrable_and_integral_le_of_nonnegative_limit hFi
    (fun k ↦ Eventually.of_forall fun q ↦ mul_nonneg
      (dirichletTest_bounds (ε := ε k) (fun x hx ↦ (hwpos x hx).le) q.2).1
      (sq_nonneg (u (a k + q.1) q.2))) (Eventually.of_forall fun k ↦ by
        rw [hI k]
        exact hbound k (ε k) (hε k) (min_le_left (e k) (a k))) hlim
  exact hG.1.integral_prod_left

end HeatEquation.Nonlinear
