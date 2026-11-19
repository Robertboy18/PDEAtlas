/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.ClassicalPDE
public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy
public import PDE.Analysis.Calculus.Prod.ParameterDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Uniqueness for the heat and wave equations on an interval

For `w` of class `C²` on `ℝ × ℝ` with zero boundary values on `[0, L]` and zero initial data:

* heat, `w_t = κ w_xx` (`κ ≥ 0`): the energy `∫₀ᴸ w ^ 2` has derivative
  `-2 κ ∫₀ᴸ w_x ^ 2 ≤ 0`, so it stays `0` and `w = 0` (`heat_eq_zero`);
* wave, `w_tt = c ^ 2 w_xx`: the energy `∫₀ᴸ w_t ^ 2 + c ^ 2 ∫₀ᴸ w_x ^ 2` is constant, since
  `∂ₜ w_x = ∂ₓ w_t` and the boundary term `w_t w_x` vanishes, so `w_t = 0` and `w = 0`
  (`wave_eq_zero`).

The equations are required for `t > 0` and `0 < x < L`, the boundary values for `t ≥ 0` and the
initial data on `[0, L]`; the conclusions hold on `[0, ∞) × [0, L]`. Two solutions with the same
data agree there (`heat_unique`, `wave_unique`), so the separated sums of `heatSum_solves` and
`waveSum_solves` are the only `C²` solutions (`heatSum_unique`, `waveSum_unique`).
-/

@[expose] public section

namespace CAS.ClassicalPDE

open Filter MeasureTheory Set Topology
open scoped ContDiff

/-! ## Partial derivatives of a `C²` function of `(t, x)` -/

theorem contDiff_partial_t {w : ℝ → ℝ → ℝ} {n : ℕ}
    (hw : ContDiff ℝ (n + 1) (fun p : ℝ × ℝ ↦ w p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ ↦ deriv (fun s ↦ w s p.2) p.1) := by
  have hD : ContDiff ℝ n (fun p : ℝ × ℝ ↦ fderiv ℝ (fun q : ℝ × ℝ ↦ w q.1 q.2) p (1, 0)) :=
    (hw.fderiv_right (m := n) le_rfl).clm_apply contDiff_const
  convert hD using 1
  funext p
  exact PDE.Analysis.deriv_parameter_eq ((hw.differentiable (by simp)) p)

theorem contDiff_partial_x {w : ℝ → ℝ → ℝ} {n : ℕ}
    (hw : ContDiff ℝ (n + 1) (fun p : ℝ × ℝ ↦ w p.1 p.2)) :
    ContDiff ℝ n (fun p : ℝ × ℝ ↦ deriv (fun y ↦ w p.1 y) p.2) := by
  have hD : ContDiff ℝ n (fun p : ℝ × ℝ ↦ fderiv ℝ (fun q : ℝ × ℝ ↦ w q.1 q.2) p (0, 1)) :=
    (hw.fderiv_right (m := n) le_rfl).clm_apply contDiff_const
  convert hD using 1
  funext p
  exact PDE.Analysis.fderiv_space_apply (U := w) ((hw.differentiable (by simp)) p) 1

theorem hasDerivAt_slice_t {w : ℝ → ℝ → ℝ} (hw : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ w p.1 p.2))
    (t x : ℝ) : HasDerivAt (fun s ↦ w s x) (deriv (fun s ↦ w s x) t) t := by
  have h : ContDiff ℝ 1 (fun s ↦ w s x) := hw.comp (contDiff_id.prodMk contDiff_const)
  exact (h.differentiable (by simp) t).hasDerivAt

theorem hasDerivAt_slice_x {w : ℝ → ℝ → ℝ} (hw : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ w p.1 p.2))
    (t x : ℝ) : HasDerivAt (fun y ↦ w t y) (deriv (fun y ↦ w t y) x) x := by
  have h : ContDiff ℝ 1 (fun y ↦ w t y) := hw.comp (contDiff_const.prodMk contDiff_id)
  exact (h.differentiable (by simp) x).hasDerivAt

/-! ## Energies on `[a, b]` -/

theorem hasDerivAt_energy {G : ℝ → ℝ → ℝ} (hG : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ G p.1 p.2))
    (a b t : ℝ) :
    HasDerivAt (fun s ↦ ∫ x in Icc a b, G s x ^ 2)
      (2 * ∫ x in Icc a b, G t x * deriv (fun s ↦ G s x) t) t := by
  have htime : Continuous (fun p : ℝ × ℝ ↦ deriv (fun s ↦ G s p.2) p.1) :=
    (contDiff_partial_t (n := 0) (hG.of_le (by norm_num))).continuous
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (t - 1) (t + 1) ×ˢ Icc a b) hG.continuous.continuousOn
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (t - 1) (t + 1) ×ˢ Icc a b) htime.continuousOn
  apply hasDerivAt_integral_sq_of_memLp_bounds
    (s := Ioo (t - 1) (t + 1)) (A := fun _ ↦ A) (B := fun _ ↦ B)
  · exact Ioo_mem_nhds (sub_lt_self t zero_lt_one) (lt_add_one t)
  · exact Eventually.of_forall fun s ↦
      (hG.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (htime.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact memLp_const A
  · exact memLp_const B
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro s hs
    have h1 := hA (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩
    have h2 := hB (s, x) ⟨⟨hs.1.le, hs.2.le⟩, hx⟩
    simp only [Real.norm_eq_abs] at h1 h2
    exact ⟨h1, h2⟩
  · filter_upwards with x
    intro s _
    exact hasDerivAt_slice_t hG s x

theorem integral_Icc_mul_deriv {f f' g g' : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hg : ∀ x, HasDerivAt g (g' x) x)
    (hf' : Continuous f') (hg' : Continuous g') :
    ∫ x in Icc 0 L, f x * g' x = f L * g L - f 0 * g 0 - ∫ x in Icc 0 L, f' x * g x := by
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL, ← intervalIntegral.integral_of_le hL]
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun x _ ↦ hf x) (fun x _ ↦ hg x)
    (hf'.intervalIntegrable _ _) (hg'.intervalIntegrable _ _)

theorem eqOn_zero_of_integral_eq_zero {h : ℝ → ℝ} (hc : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    {L : ℝ} (hint : ∫ x in Icc 0 L, h x = 0) : ∀ x ∈ Ioo 0 L, h x = 0 := by
  have hae : h =ᵐ[volume.restrict (Icc 0 L)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hnn)
      hc.integrableOn_Icc).mp hint
  have hae' : h =ᵐ[volume.restrict (Ioo 0 L)] 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hae
  exact fun x hx ↦ (Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo hc.continuousOn
    continuousOn_const) hx

theorem integral_Icc_congr_Ioo {f g : ℝ → ℝ} {L : ℝ} (h : ∀ x ∈ Ioo 0 L, f x = g x) :
    ∫ x in Icc 0 L, f x = ∫ x in Icc 0 L, g x := by
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- A function constant in time on `[0, ∞)` from a vanishing derivative for `t > 0`. -/
theorem eq_of_deriv_eq_zero_Ioi {φ : ℝ → ℝ} (hc : Continuous φ)
    (hd : ∀ t > 0, HasDerivAt φ 0 t) : ∀ t ≥ 0, φ t = φ 0 := by
  intro t ht
  have hdiff : DifferentiableOn ℝ φ (interior (Ici 0)) := by
    rw [interior_Ici]
    exact fun s hs ↦ (hd s hs).differentiableAt.differentiableWithinAt
  have hz : ∀ s ∈ interior (Ici (0 : ℝ)), deriv φ s = 0 := by
    rw [interior_Ici]
    exact fun s hs ↦ (hd s hs).deriv
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici 0) hc.continuousOn hdiff
    (fun s hs ↦ (hz s hs).le)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Ici 0) hc.continuousOn hdiff
    (fun s hs ↦ (hz s hs).ge)
  exact le_antisymm (hanti (self_mem_Ici) ht ht) (hmono (self_mem_Ici) ht ht)

/-! ## Heat equation -/

/-- A `C²` solution of `w_t = κ w_xx` with zero boundary values and zero initial data vanishes
on `[0, ∞) × [0, L]`. -/
theorem heat_eq_zero {κ L : ℝ} (hκ : 0 ≤ κ) (hL : 0 < L) {w : ℝ → ℝ → ℝ}
    (hw : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ w p.1 p.2))
    (hpde : ∀ t > 0, ∀ x ∈ Ioo 0 L,
      deriv (fun s ↦ w s x) t = κ * deriv (fun y ↦ deriv (fun z ↦ w t z) y) x)
    (h0 : ∀ t ≥ 0, w t 0 = 0) (hL0 : ∀ t ≥ 0, w t L = 0)
    (hinit : ∀ x ∈ Icc 0 L, w 0 x = 0) : ∀ t ≥ 0, ∀ x ∈ Icc 0 L, w t x = 0 := by
  have hw1 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ w p.1 p.2) := hw.of_le (by norm_num)
  have hx1 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ deriv (fun y ↦ w p.1 y) p.2) :=
    contDiff_partial_x (n := 1) (hw.of_le (by norm_num))
  have hxx : Continuous (fun p : ℝ × ℝ ↦ deriv (fun y ↦ deriv (fun z ↦ w p.1 z) y) p.2) :=
    (contDiff_partial_x (w := fun t x ↦ deriv (fun y ↦ w t y) x) (n := 0)
      (hx1.of_le (by norm_num))).continuous
  set E : ℝ → ℝ := fun t ↦ ∫ x in Icc 0 L, w t x ^ 2 with hEdef
  have hE : ∀ t, HasDerivAt E (2 * ∫ x in Icc 0 L, w t x * deriv (fun s ↦ w s x) t) t :=
    fun t ↦ hasDerivAt_energy hw1 0 L t
  have hrate : ∀ t > 0, 2 * ∫ x in Icc 0 L, w t x * deriv (fun s ↦ w s x) t ≤ 0 := by
    intro t ht
    rw [integral_Icc_congr_Ioo (g := fun x ↦ κ * (w t x *
        deriv (fun y ↦ deriv (fun z ↦ w t z) y) x)) (fun x hx ↦ by rw [hpde t ht x hx]; ring),
      integral_const_mul,
      integral_Icc_mul_deriv hL.le (f := fun x ↦ w t x)
        (f' := fun x ↦ deriv (fun y ↦ w t y) x) (g := fun x ↦ deriv (fun y ↦ w t y) x)
        (g' := fun x ↦ deriv (fun y ↦ deriv (fun z ↦ w t z) y) x)
        (hasDerivAt_slice_x hw1 t)
        (hasDerivAt_slice_x (w := fun t x ↦ deriv (fun y ↦ w t y) x) hx1 t)
        (hx1.continuous.comp (continuous_const.prodMk continuous_id))
        (hxx.comp (continuous_const.prodMk continuous_id)),
      h0 t ht.le, hL0 t ht.le]
    have hnn : 0 ≤ ∫ x in Icc 0 L, deriv (fun y ↦ w t y) x * deriv (fun y ↦ w t y) x :=
      setIntegral_nonneg measurableSet_Icc fun x _ ↦ mul_self_nonneg _
    nlinarith
  have hcont : Continuous E := continuous_iff_continuousAt.mpr fun t ↦ (hE t).continuousAt
  have hdiff : DifferentiableOn ℝ E (interior (Ici 0)) :=
    fun t _ ↦ (hE t).differentiableAt.differentiableWithinAt
  have hanti := antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont.continuousOn hdiff
    (fun t ht ↦ by rw [interior_Ici] at ht; rw [(hE t).deriv]; exact hrate t ht)
  have hE0 : E 0 = 0 := by
    simp only [hEdef]
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ ↦ (0 : ℝ))
      (fun x hx ↦ by simp [hinit x hx])]
    simp
  intro t ht x hx
  have hEt : E t = 0 := le_antisymm (hE0 ▸ hanti self_mem_Ici ht ht)
    (setIntegral_nonneg measurableSet_Icc fun x _ ↦ sq_nonneg _)
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; exact h0 t ht
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h']; exact hL0 t ht
  have := eqOn_zero_of_integral_eq_zero (h := fun x ↦ w t x ^ 2)
    ((hw1.continuous.comp (continuous_const.prodMk continuous_id)).pow 2)
    (fun x ↦ sq_nonneg _) hEt x ⟨h, h'⟩
  exact pow_eq_zero_iff (two_ne_zero) |>.mp this

/-! ## Wave equation -/

theorem deriv_eq_zero_of_eq_zero_Ici {φ : ℝ → ℝ} (h : ∀ t ≥ 0, φ t = 0) {t : ℝ} (ht : 0 < t) :
    deriv φ t = 0 := by
  have : φ =ᶠ[𝓝 t] fun _ ↦ 0 := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact h s (le_of_lt hs)
  rw [this.deriv_eq, deriv_const]

/-- A `C²` solution of `w_tt = c ^ 2 w_xx` with zero boundary values and zero initial data
vanishes on `[0, ∞) × [0, L]`. -/
theorem wave_eq_zero {c L : ℝ} (hL : 0 < L) {w : ℝ → ℝ → ℝ}
    (hw : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ w p.1 p.2))
    (hpde : ∀ t > 0, ∀ x ∈ Ioo 0 L, deriv (fun s ↦ deriv (fun r ↦ w r x) s) t =
      c ^ 2 * deriv (fun y ↦ deriv (fun z ↦ w t z) y) x)
    (h0 : ∀ t ≥ 0, w t 0 = 0) (hL0 : ∀ t ≥ 0, w t L = 0)
    (hinit : ∀ x ∈ Icc 0 L, w 0 x = 0) (hvel : ∀ x ∈ Icc 0 L, deriv (fun s ↦ w s x) 0 = 0) :
    ∀ t ≥ 0, ∀ x ∈ Icc 0 L, w t x = 0 := by
  have hw1 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ w p.1 p.2) := hw.of_le (by norm_num)
  have ht1 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ deriv (fun s ↦ w s p.2) p.1) :=
    contDiff_partial_t (n := 1) (hw.of_le (by norm_num))
  have hx1 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ deriv (fun y ↦ w p.1 y) p.2) :=
    contDiff_partial_x (n := 1) (hw.of_le (by norm_num))
  have hxt : Continuous (fun p : ℝ × ℝ ↦ deriv (fun y ↦ deriv (fun s ↦ w s y) p.1) p.2) :=
    (contDiff_partial_x (w := fun t x ↦ deriv (fun s ↦ w s x) t) (n := 0)
      (ht1.of_le (by norm_num))).continuous
  have hxx : Continuous (fun p : ℝ × ℝ ↦ deriv (fun y ↦ deriv (fun z ↦ w p.1 z) y) p.2) :=
    (contDiff_partial_x (w := fun t x ↦ deriv (fun y ↦ w t y) x) (n := 0)
      (hx1.of_le (by norm_num))).continuous
  -- `∂ₜ w_x = ∂ₓ w_t`.
  have hswap : ∀ t x, deriv (fun s ↦ deriv (fun y ↦ w s y) x) t =
      deriv (fun y ↦ deriv (fun s ↦ w s y) t) x := fun t x ↦
    (PDE.Analysis.hasDerivAt_fderiv_space (U := w) (hw.contDiffAt) 1).deriv
  set E : ℝ → ℝ := fun t ↦ (∫ x in Icc 0 L, deriv (fun s ↦ w s x) t ^ 2) +
    c ^ 2 * ∫ x in Icc 0 L, deriv (fun y ↦ w t y) x ^ 2 with hEdef
  have hE : ∀ t, HasDerivAt E
      (2 * (∫ x in Icc 0 L, deriv (fun s ↦ w s x) t *
          deriv (fun s ↦ deriv (fun r ↦ w r x) s) t) +
        c ^ 2 * (2 * ∫ x in Icc 0 L, deriv (fun y ↦ w t y) x *
          deriv (fun s ↦ deriv (fun y ↦ w s y) x) t)) t := fun t ↦
    (hasDerivAt_energy (G := fun t x ↦ deriv (fun s ↦ w s x) t) ht1 0 L t).add
      ((hasDerivAt_energy (G := fun t x ↦ deriv (fun y ↦ w t y) x) hx1 0 L t).const_mul
        (c ^ 2))
  have hrate : ∀ t > 0, HasDerivAt E 0 t := by
    intro t ht
    convert hE t using 1
    simp only [hswap t]
    rw [integral_Icc_congr_Ioo (g := fun x ↦ c ^ 2 * (deriv (fun s ↦ w s x) t *
        deriv (fun y ↦ deriv (fun z ↦ w t z) y) x)) (fun x hx ↦ by rw [hpde t ht x hx]; ring),
      integral_const_mul,
      integral_Icc_mul_deriv hL.le (f := fun x ↦ deriv (fun s ↦ w s x) t)
        (f' := fun x ↦ deriv (fun y ↦ deriv (fun s ↦ w s y) t) x)
        (g := fun x ↦ deriv (fun y ↦ w t y) x)
        (g' := fun x ↦ deriv (fun y ↦ deriv (fun z ↦ w t z) y) x)
        (hasDerivAt_slice_x (w := fun t x ↦ deriv (fun s ↦ w s x) t) ht1 t)
        (hasDerivAt_slice_x (w := fun t x ↦ deriv (fun y ↦ w t y) x) hx1 t)
        (hxt.comp (continuous_const.prodMk continuous_id))
        (hxx.comp (continuous_const.prodMk continuous_id))]
    have hb0 : deriv (fun s ↦ w s 0) t = 0 := deriv_eq_zero_of_eq_zero_Ici h0 ht
    have hbL : deriv (fun s ↦ w s L) t = 0 := deriv_eq_zero_of_eq_zero_Ici hL0 ht
    rw [hb0, hbL]
    have hcomm : ∫ x in Icc 0 L, deriv (fun y ↦ w t y) x *
        deriv (fun y ↦ deriv (fun s ↦ w s y) t) x =
        ∫ x in Icc 0 L, deriv (fun y ↦ deriv (fun s ↦ w s y) t) x * deriv (fun y ↦ w t y) x :=
      setIntegral_congr_fun measurableSet_Icc fun x _ ↦ mul_comm _ _
    rw [hcomm]
    ring
  have hcont : Continuous E := continuous_iff_continuousAt.mpr fun t ↦ (hE t).continuousAt
  have hconst := eq_of_deriv_eq_zero_Ioi hcont hrate
  have hE0 : E 0 = 0 := by
    simp only [hEdef]
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ ↦ (0 : ℝ))
        (fun x hx ↦ by simp [hvel x hx]),
      integral_Icc_congr_Ioo (f := fun x ↦ deriv (fun y ↦ w 0 y) x ^ 2) (g := fun _ ↦ (0 : ℝ))
        (fun x hx ↦ by
        have : (fun y ↦ w 0 y) =ᶠ[𝓝 x] fun _ ↦ 0 := by
          filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
          exact hinit y (Ioo_subset_Icc_self hy)
        simp [this.deriv_eq])]
    simp
  -- `w_t = 0`.
  have hwt : ∀ t ≥ 0, ∀ x ∈ Ioo 0 L, deriv (fun s ↦ w s x) t = 0 := by
    intro t ht x hx
    have hEt : E t = 0 := by rw [hconst t ht, hE0]
    have h1 : 0 ≤ ∫ x in Icc 0 L, deriv (fun s ↦ w s x) t ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun x _ ↦ sq_nonneg _
    have h2 : 0 ≤ c ^ 2 * ∫ x in Icc 0 L, deriv (fun y ↦ w t y) x ^ 2 :=
      mul_nonneg (sq_nonneg c) (setIntegral_nonneg measurableSet_Icc fun x _ ↦ sq_nonneg _)
    have h3 : ∫ x in Icc 0 L, deriv (fun s ↦ w s x) t ^ 2 = 0 := by
      simp only [hEdef] at hEt
      linarith
    have := eqOn_zero_of_integral_eq_zero (h := fun x ↦ deriv (fun s ↦ w s x) t ^ 2)
      ((ht1.continuous.comp (continuous_const.prodMk continuous_id)).pow 2)
      (fun x ↦ sq_nonneg _) h3 x hx
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  intro t ht x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]; exact h0 t ht
  rcases eq_or_lt_of_le hx.2 with h' | h'
  · rw [h']; exact hL0 t ht
  have hφ := eq_of_deriv_eq_zero_Ioi (φ := fun s ↦ w s x)
    (hw1.continuous.comp (continuous_id.prodMk continuous_const))
    (fun s hs ↦ by
      have := hasDerivAt_slice_t hw1 s x
      rwa [hwt s hs.le x ⟨h, h'⟩] at this) t ht
  simpa [hinit x hx] using hφ

/-! ## Two solutions with the same data -/

section Difference

variable {u v : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ u p.1 p.2))
  (hv : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ v p.1 p.2))
include hu hv

theorem deriv_t_sub (t x : ℝ) : deriv (fun s ↦ u s x - v s x) t =
    deriv (fun s ↦ u s x) t - deriv (fun s ↦ v s x) t :=
  deriv_sub (hasDerivAt_slice_t (hu.of_le (by norm_num)) t x).differentiableAt
    (hasDerivAt_slice_t (hv.of_le (by norm_num)) t x).differentiableAt

theorem deriv_x_sub (t x : ℝ) : deriv (fun y ↦ u t y - v t y) x =
    deriv (fun y ↦ u t y) x - deriv (fun y ↦ v t y) x :=
  deriv_sub (hasDerivAt_slice_x (hu.of_le (by norm_num)) t x).differentiableAt
    (hasDerivAt_slice_x (hv.of_le (by norm_num)) t x).differentiableAt

theorem deriv_xx_sub (t x : ℝ) :
    deriv (fun y ↦ deriv (fun z ↦ u t z - v t z) y) x =
      deriv (fun y ↦ deriv (fun z ↦ u t z) y) x - deriv (fun y ↦ deriv (fun z ↦ v t z) y) x := by
  have e : (fun y ↦ deriv (fun z ↦ u t z - v t z) y) =
      fun y ↦ deriv (fun z ↦ u t z) y - deriv (fun z ↦ v t z) y :=
    funext fun y ↦ deriv_x_sub hu hv t y
  rw [e]
  exact deriv_sub (hasDerivAt_slice_x (w := fun t x ↦ deriv (fun y ↦ u t y) x)
      (contDiff_partial_x (n := 1) (hu.of_le (by norm_num))) t x).differentiableAt
    (hasDerivAt_slice_x (w := fun t x ↦ deriv (fun y ↦ v t y) x)
      (contDiff_partial_x (n := 1) (hv.of_le (by norm_num))) t x).differentiableAt

theorem deriv_tt_sub (t x : ℝ) :
    deriv (fun s ↦ deriv (fun r ↦ u r x - v r x) s) t =
      deriv (fun s ↦ deriv (fun r ↦ u r x) s) t - deriv (fun s ↦ deriv (fun r ↦ v r x) s) t := by
  have e : (fun s ↦ deriv (fun r ↦ u r x - v r x) s) =
      fun s ↦ deriv (fun r ↦ u r x) s - deriv (fun r ↦ v r x) s :=
    funext fun s ↦ deriv_t_sub hu hv s x
  rw [e]
  exact deriv_sub (hasDerivAt_slice_t (w := fun t x ↦ deriv (fun s ↦ u s x) t)
      (contDiff_partial_t (n := 1) (hu.of_le (by norm_num))) t x).differentiableAt
    (hasDerivAt_slice_t (w := fun t x ↦ deriv (fun s ↦ v s x) t)
      (contDiff_partial_t (n := 1) (hv.of_le (by norm_num))) t x).differentiableAt

end Difference

/-- Two `C²` solutions of the heat equation on `[0, L]` with the same boundary values and initial
data agree on `[0, ∞) × [0, L]`. -/
theorem heat_unique {κ L : ℝ} (hκ : 0 ≤ κ) (hL : 0 < L) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ u p.1 p.2)) (hv : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ v p.1 p.2))
    (hpu : ∀ t > 0, ∀ x ∈ Ioo 0 L,
      deriv (fun s ↦ u s x) t = κ * deriv (fun y ↦ deriv (fun z ↦ u t z) y) x)
    (hpv : ∀ t > 0, ∀ x ∈ Ioo 0 L,
      deriv (fun s ↦ v s x) t = κ * deriv (fun y ↦ deriv (fun z ↦ v t z) y) x)
    (h0 : ∀ t ≥ 0, u t 0 = v t 0) (hL0 : ∀ t ≥ 0, u t L = v t L)
    (hinit : ∀ x ∈ Icc 0 L, u 0 x = v 0 x) : ∀ t ≥ 0, ∀ x ∈ Icc 0 L, u t x = v t x := by
  have h := heat_eq_zero hκ hL (w := fun t x ↦ u t x - v t x) (hu.sub hv)
    (fun t ht x hx ↦ by
      rw [deriv_t_sub hu hv, deriv_xx_sub hu hv, hpu t ht x hx, hpv t ht x hx]
      ring)
    (fun t ht ↦ by simp [h0 t ht]) (fun t ht ↦ by simp [hL0 t ht])
    (fun x hx ↦ by simp [hinit x hx])
  exact fun t ht x hx ↦ sub_eq_zero.mp (h t ht x hx)

/-- Two `C²` solutions of the wave equation on `[0, L]` with the same boundary values, initial
displacement and initial velocity agree on `[0, ∞) × [0, L]`. -/
theorem wave_unique {c L : ℝ} (hL : 0 < L) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ u p.1 p.2)) (hv : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ v p.1 p.2))
    (hpu : ∀ t > 0, ∀ x ∈ Ioo 0 L, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t =
      c ^ 2 * deriv (fun y ↦ deriv (fun z ↦ u t z) y) x)
    (hpv : ∀ t > 0, ∀ x ∈ Ioo 0 L, deriv (fun s ↦ deriv (fun r ↦ v r x) s) t =
      c ^ 2 * deriv (fun y ↦ deriv (fun z ↦ v t z) y) x)
    (h0 : ∀ t ≥ 0, u t 0 = v t 0) (hL0 : ∀ t ≥ 0, u t L = v t L)
    (hinit : ∀ x ∈ Icc 0 L, u 0 x = v 0 x)
    (hvel : ∀ x ∈ Icc 0 L, deriv (fun s ↦ u s x) 0 = deriv (fun s ↦ v s x) 0) :
    ∀ t ≥ 0, ∀ x ∈ Icc 0 L, u t x = v t x := by
  have h := wave_eq_zero hL (c := c) (w := fun t x ↦ u t x - v t x) (hu.sub hv)
    (fun t ht x hx ↦ by
      rw [deriv_tt_sub hu hv, deriv_xx_sub hu hv, hpu t ht x hx, hpv t ht x hx]
      ring)
    (fun t ht ↦ by simp [h0 t ht]) (fun t ht ↦ by simp [hL0 t ht])
    (fun x hx ↦ by simp [hinit x hx])
    (fun x hx ↦ by rw [deriv_t_sub hu hv, hvel x hx, sub_self])
  exact fun t ht x hx ↦ sub_eq_zero.mp (h t ht x hx)

/-! ## The separated sums are the only solutions -/

theorem contDiff_heatSum (κ : ℝ) : ∀ terms : List (ℝ × ℝ),
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ heatSum κ terms p.1 p.2)
  | [] => by simp only [heatSum, List.map_nil, List.sum_nil]; exact contDiff_const
  | e :: rest => by
    have h : (fun p : ℝ × ℝ ↦ heatSum κ (e :: rest) p.1 p.2) =
        fun p ↦ heatTerm κ e.1 e.2 p.1 p.2 + heatSum κ rest p.1 p.2 := by
      funext p
      simp [heatSum]
    rw [h]
    exact (by unfold heatTerm; fun_prop : ContDiff ℝ ⊤ fun p : ℝ × ℝ ↦
      heatTerm κ e.1 e.2 p.1 p.2).add (contDiff_heatSum κ rest)

theorem contDiff_waveSum (c : ℝ) : ∀ terms : List (ℝ × ℝ × ℝ),
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ ↦ waveSum c terms p.1 p.2)
  | [] => by simp only [waveSum, List.map_nil, List.sum_nil]; exact contDiff_const
  | e :: rest => by
    have h : (fun p : ℝ × ℝ ↦ waveSum c (e :: rest) p.1 p.2) =
        fun p ↦ waveTerm c e.1 e.2.1 e.2.2 p.1 p.2 + waveSum c rest p.1 p.2 := by
      funext p
      simp [waveSum]
    rw [h]
    exact (by unfold waveTerm; fun_prop : ContDiff ℝ ⊤ fun p : ℝ × ℝ ↦
      waveTerm c e.1 e.2.1 e.2.2 p.1 p.2).add (contDiff_waveSum c rest)

/-- Every `C²` solution of the heat problem with initial value `∑ b sin (ω x)` is the separated
sum on `[0, ∞) × [0, L]`. -/
theorem heatSum_unique {κ L : ℝ} (hκ : 0 ≤ κ) (hL : 0 < L) (terms : List (ℝ × ℝ))
    (hsin : ∀ e ∈ terms, Real.sin (e.2 * L) = 0) {u : ℝ → ℝ → ℝ}
    (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ u p.1 p.2))
    (hpde : ∀ t > 0, ∀ x ∈ Ioo 0 L,
      deriv (fun s ↦ u s x) t = κ * deriv (fun y ↦ deriv (fun z ↦ u t z) y) x)
    (h0 : ∀ t ≥ 0, u t 0 = 0) (hL0 : ∀ t ≥ 0, u t L = 0)
    (hinit : ∀ x ∈ Icc 0 L, u 0 x = (terms.map fun e ↦ e.1 * Real.sin (e.2 * x)).sum) :
    ∀ t ≥ 0, ∀ x ∈ Icc 0 L, u t x = heatSum κ terms t x := by
  obtain ⟨hp, hb0, hbL, hb⟩ := heatSum_solves κ L terms hsin
  exact heat_unique hκ hL hu ((contDiff_heatSum κ terms).of_le le_top) hpde
    (fun t _ x _ ↦ hp t x) (fun t ht ↦ by rw [h0 t ht, hb0]) (fun t ht ↦ by rw [hL0 t ht, hbL])
    (fun x hx ↦ by rw [hinit x hx, hb])

/-- Every `C²` solution of the wave problem with initial values `∑ a sin (ω x)`,
`∑ b sin (ω x)` is the separated sum on `[0, ∞) × [0, L]`. -/
theorem waveSum_unique {c L : ℝ} (hL : 0 < L) (terms : List (ℝ × ℝ × ℝ))
    (hω : ∀ e ∈ terms, c * e.2.2 ≠ 0) (hsin : ∀ e ∈ terms, Real.sin (e.2.2 * L) = 0)
    {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ u p.1 p.2))
    (hpde : ∀ t > 0, ∀ x ∈ Ioo 0 L, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t =
      c ^ 2 * deriv (fun y ↦ deriv (fun z ↦ u t z) y) x)
    (h0 : ∀ t ≥ 0, u t 0 = 0) (hL0 : ∀ t ≥ 0, u t L = 0)
    (hinit : ∀ x ∈ Icc 0 L, u 0 x = (terms.map fun e ↦ e.1 * Real.sin (e.2.2 * x)).sum)
    (hvel : ∀ x ∈ Icc 0 L,
      deriv (fun s ↦ u s x) 0 = (terms.map fun e ↦ e.2.1 * Real.sin (e.2.2 * x)).sum) :
    ∀ t ≥ 0, ∀ x ∈ Icc 0 L, u t x = waveSum c terms t x := by
  obtain ⟨hp, hb0, hbL, hb, hbv⟩ := waveSum_solves c L terms hω hsin
  exact wave_unique hL hu ((contDiff_waveSum c terms).of_le le_top) hpde
    (fun t _ x _ ↦ hp t x) (fun t ht ↦ by rw [h0 t ht, hb0]) (fun t ht ↦ by rw [hL0 t ht, hbL])
    (fun x hx ↦ by rw [hinit x hx, hb]) (fun x hx ↦ by rw [hvel x hx, hbv])

end CAS.ClassicalPDE
