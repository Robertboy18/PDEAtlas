/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearPrincipalValue
import PDE.Analysis.Fourier.HilbertTransform.EndpointMoments

/-!
# The horizontal Hölder estimate of the localized `u_y`

Chen and Hou, Part I, Lemma 3.4 for `u_y`: for two points `x, z` at the same height `x₂ > 0` and
the square boxes `Q(x) = Q_{a,a,a}(x)` with `a ≥ 2|x - z|`, the localized `u_y` of (3.4) satisfies

`|u_y(x) - u_y(z)| / |x - z|^{1/2} ≤
  (C_x S̃_{1D}(B, A) + C_y (S_up(B, A) + S_out(B, h))) / (π √2)`,

`B = 2a/|x - z|`, `h = 2x₂/|x - z|`, `A = min(h, B)`, where `C_x` bounds the horizontal
`1/2`-Hölder seminorm of the odd extension `W` on `Q(x) ∪ Q(z)` and `C_y` the vertical one on its
upper part.

Removing vertical strips around the two points instead of discs absorbs the local terms of `u_y`
(`tendsto_setIntegral_box_inter_strip`). Rescaling `y = (m + c p, x₂ - c τ)`, `c = |x - z|/2`,
the difference of the two strip-truncated integrals becomes an integral over columns `p` of
`∫ Δ_B(p, τ) W(m + c p, x₂ - c τ) dτ`, and the columns `p` and `-p` together are bounded by the
column estimate `abs_integral_localShearDifference_add_le`.

## Main results

* `boxKernelDifference_shear_mk`: the localized kernel difference at a rescaled point.
* `integral_eq_mul_integral_integral`: Fubini in rescaled coordinates.
* `abs_sub_le_of_directionalSeminorm`: directional seminorms give a Hölder bound at a point.
* `abs_sub_div_le_shear`: Part I, Lemma 3.4, the estimate of `u_y`.
* `abs_sub_div_le_shear_residual`: Part I, Lemma 3.4, the estimate of `v_x`.
* `shearConstant`, `shearResidualConstant`, `div_le_div_mul_max`: the constants `C₂(τ)`, `C₁(τ)`
  and the anisotropic form.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, (3.4), p. 27, Lemma 3.4, pp. 28-29,
  and Appendix B.1, (B.1), (B.39) and (B.40), pp. 129-136.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric PDE.Common
open PDE.Analysis (planeEquiv planeEquiv_symm_apply measurePreserving_planeEquiv)
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

variable {K : ℝ^2 → ℝ} {a : ℝ}

/-- `K₂` is homogeneous of degree `-2`. -/
theorem shearDensity_mul {c : ℝ} (hc : c ≠ 0) (s t : ℝ) :
    shearDensity (c * s) (c * t) = shearDensity s t / c ^ 2 := by
  simp only [shearDensity_eq]
  rcases eq_or_ne (s ^ 2 + t ^ 2) 0 with h | h
  · have hs : s = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    have ht : t = 0 := by nlinarith [sq_nonneg s, sq_nonneg t]
    simp [hs, ht]
  · field_simp

/-- At the rescaled point `y = (m + c p, x₂ - c τ)` of two points `z = (m - c, x₂)`,
`x = (m + c, x₂)`, `c > 0`:
`1_{Q(z)} K₂(z - y) - 1_{Q(x)} K₂(x - y) = 1{|τ| ≤ a/c} Δ_{a/c}(p, τ) / c²`. -/
theorem boxKernelDifference_shear_mk (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {x z : ℝ^2} (hxz : x 1 = z 1) (hd : z 0 < x 0) (p τ : ℝ) :
    boxKernelDifference K a a a z x
        !₂[(x 0 + z 0) / 2 + (x 0 - z 0) / 2 * p, x 1 - (x 0 - z 0) / 2 * τ] =
      (if |τ| ≤ a / ((x 0 - z 0) / 2) then
        localShearDifference (a / ((x 0 - z 0) / 2)) p τ else 0) / ((x 0 - z 0) / 2) ^ 2 := by
  set c := (x 0 - z 0) / 2 with hc_def
  have hc : 0 < c := by simp only [hc_def]; linarith
  set m := (x 0 + z 0) / 2
  have hx0 : x 0 = m + c := by simp only [m, c]; ring
  have hz0 : z 0 = m - c := by simp only [m, c]; ring
  have hKx : K (x - !₂[m + c * p, x 1 - c * τ]) = shearDensity (p - 1) τ / c ^ 2 := by
    rw [shearKernel_apply hK]
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show x 0 - (m + c * p) = c * (-(p - 1)) by rw [hx0]; ring,
      show x 1 - (x 1 - c * τ) = c * τ by ring, shearDensity_mul hc.ne', shearDensity_neg_left]
  have hKz : K (z - !₂[m + c * p, x 1 - c * τ]) = shearDensity (p + 1) τ / c ^ 2 := by
    rw [shearKernel_apply hK]
    simp only [PiLp.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show z 0 - (m + c * p) = c * (-(p + 1)) by rw [hz0]; ring, ← hxz,
      show x 1 - (x 1 - c * τ) = c * τ by ring, shearDensity_mul hc.ne', shearDensity_neg_left]
  have key {u v : ℝ} (huv : u = c * v) : |u| ≤ a ↔ |v| ≤ a / c := by
    rw [huv, abs_mul, abs_of_pos hc, le_div_iff₀ hc, mul_comm]
  have kt : |x 1 - c * τ - x 1| ≤ a ↔ |τ| ≤ a / c := by rw [key (v := -τ) (by ring), abs_neg]
  have kx : |m + c * p - x 0| ≤ a ↔ |p - 1| ≤ a / c := key (by rw [hx0]; ring)
  have kz : |m + c * p - z 0| ≤ a ↔ |p + 1| ≤ a / c := key (by rw [hz0]; ring)
  have hcx : !₂[m + c * p, x 1 - c * τ] ∈ box a a a x ↔ |p - 1| ≤ a / c ∧ |τ| ≤ a / c := by
    rw [mk_mem_box, mem_Icc_iff_abs_sub_le, mem_Icc_iff_abs_sub_le, kt, kx]
  have hcz : !₂[m + c * p, x 1 - c * τ] ∈ box a a a z ↔ |p + 1| ≤ a / c ∧ |τ| ≤ a / c := by
    rw [mk_mem_box, mem_Icc_iff_abs_sub_le, mem_Icc_iff_abs_sub_le, ← hxz, kt, kz]
  simp only [boxKernelDifference, indicator, localShearDifference]
  by_cases h₀ : |τ| ≤ a / c <;> by_cases h₁ : |p + 1| ≤ a / c <;>
    by_cases h₂ : |p - 1| ≤ a / c <;>
    simp only [h₀, h₁, h₂, hcx, hcz, and_self, and_false, false_and, ite_true, ite_false, hKx,
      hKz] <;> ring

/-- **Rescaled Fubini.** For an integrable `F` on the plane and `c > 0`,
`∫ F = c² ∫_p ∫_τ F(m + c p, e - c τ) dτ dp`, and the inner integral is integrable in `p`. -/
theorem integral_eq_mul_integral_integral {F : ℝ^2 → ℝ} (hF : Integrable F) {c : ℝ} (hc : 0 < c)
    (m e : ℝ) :
    Integrable (fun p ↦ ∫ τ, F !₂[m + c * p, e - c * τ]) ∧
      ∫ y, F y = c ^ 2 * ∫ p, ∫ τ, F !₂[m + c * p, e - c * τ] := by
  have hmp := measurePreserving_planeEquiv.symm
  have hG₀ := (hmp.integrable_comp_emb planeEquiv.symm.measurableEmbedding).2 hF
  have hG : Integrable (fun q : ℝ × ℝ ↦ F !₂[q.1, q.2]) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    simpa only [Function.comp_def, planeEquiv_symm_apply] using hG₀
  set Φ : ℝ → ℝ := fun s ↦ ∫ t, F !₂[s, t] with hΦ
  have hΦi : Integrable Φ := hG.integral_prod_left
  have hint : (fun p ↦ ∫ τ, F !₂[m + c * p, e - c * τ]) = fun p ↦ c⁻¹ * Φ (m + c * p) := by
    ext p
    have h1 := Measure.integral_comp_mul_left (fun τ ↦ F !₂[m + c * p, e - τ]) c
    rwa [integral_sub_left_eq_self (fun t ↦ F !₂[m + c * p, t]) volume e, abs_inv,
      abs_of_pos hc, smul_eq_mul] at h1
  refine ⟨hint ▸ ((hΦi.comp_add_left m).comp_mul_left' hc.ne').const_mul _, ?_⟩
  have h3 := Measure.integral_comp_mul_left (fun p ↦ Φ (m + p)) c
  rw [abs_inv, abs_of_pos hc, smul_eq_mul,
    integral_add_left_eq_self m (μ := volume) (f := Φ)] at h3
  have h4 : ∫ y, F y = ∫ s, Φ s := by
    rw [← hmp.integral_comp' F, Measure.volume_eq_prod,
      integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hG₀)]
    simp only [planeEquiv_symm_apply, Φ]
  rw [hint, integral_const_mul, h3, h4]
  field_simp

/-- The center of a box with nonnegative sides lies in it. -/
theorem self_mem_box {a b₁ b₂ : ℝ} (ha : 0 ≤ a) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (x : ℝ^2) :
    x ∈ box a b₁ b₂ x := by
  simp only [box, mem_ofPred_eq]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Directional `1/2`-Hölder bounds of `W` on `S ⊇ Q(x)` (horizontal on `S`, vertical on the upper
part) and a bound `|W| ≤ M₀` give the Hölder bound
`|W(y) - W(x)| ≤ (C_x + C_y + 2 |M₀| x₂^{-1/2}) |y - x|^{1/2}` on `Q(x)` for `x₂ > 0`. -/
theorem abs_sub_le_of_directionalSeminorm {W : ℝ^2 → ℝ} {x : ℝ^2} (hx : 0 < x 1)
    {S : Set (ℝ^2)} (hS : box a a a x ⊆ S) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) S W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2) (S ∩ {y | 0 ≤ y 1}) W ≤ Cy) {M₀ : ℝ}
    (hWb : ∀ y ∈ S, |W y| ≤ M₀) :
    ∀ y ∈ box a a a x, |W y - W x| ≤
      (Cx + Cy + 2 * |M₀| / x 1 ^ (1 / 2 : ℝ)) * ‖y - x‖ ^ (1 / 2 : ℝ) := by
  intro y hy
  have hn : ∀ i : Fin 2, |y i - x i| ^ (1 / 2 : ℝ) ≤ ‖y - x‖ ^ (1 / 2 : ℝ) := fun i ↦
    Real.rpow_le_rpow (abs_nonneg _) (abs_sub_apply_le_norm x y i) (by norm_num)
  have hx' : 0 < x 1 ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hM : 0 ≤ 2 * |M₀| / x 1 ^ (1 / 2 : ℝ) := by positivity
  have hyx : y = !₂[y 0, y 1] := by ext i; fin_cases i <;> simp
  have hxx : x = !₂[x 0, x 1] := by ext i; fin_cases i <;> simp
  have hya := hy
  simp only [box, mem_ofPred_eq] at hya
  have ha : 0 ≤ a := by linarith [hya.1, hya.2.1]
  have hxQ : x ∈ box a a a x := self_mem_box ha ha ha x
  rcases le_or_gt 0 (y 1) with h₁ | h₁
  · -- the upper part: a horizontal and a vertical step through `(x₁, y₂)`
    have hmid : !₂[x 0, y 1] ∈ box a a a x := by
      rw [mk_mem_box]
      exact ⟨⟨by linarith, by linarith⟩, ⟨hya.2.2.1, hya.2.2.2⟩⟩
    have hd₀ := (HolderSpace.holderOnWith_slice_zero hCx (y 1)).dist_le
      (show y 0 ∈ {t | !₂[t, y 1] ∈ S} from by rw [mem_ofPred_eq, ← hyx]; exact hS hy)
      (show x 0 ∈ {t | !₂[t, y 1] ∈ S} from hS hmid)
    have hd₁ := (HolderSpace.holderOnWith_slice_one hCy (x 0)).dist_le
      (show y 1 ∈ {t | !₂[x 0, t] ∈ S ∩ {y | 0 ≤ y 1}} from ⟨hS hmid, by simpa using h₁⟩)
      (show x 1 ∈ {t | !₂[x 0, t] ∈ S ∩ {y | 0 ≤ y 1}} from
        ⟨by rw [← hxx]; exact hS hxQ, by simpa using hx.le⟩)
    rw [← hyx, Real.dist_eq, Real.dist_eq] at hd₀
    rw [← hxx, Real.dist_eq, Real.dist_eq] at hd₁
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hd₀ hd₁
    calc |W y - W x| = |(W y - W !₂[x 0, y 1]) + (W !₂[x 0, y 1] - W x)| := by ring_nf
      _ ≤ |W y - W !₂[x 0, y 1]| + |W !₂[x 0, y 1] - W x| := abs_add_le _ _
      _ ≤ Cx * ‖y - x‖ ^ (1 / 2 : ℝ) + Cy * ‖y - x‖ ^ (1 / 2 : ℝ) := by
          gcongr
          · exact hd₀.trans (mul_le_mul_of_nonneg_left (hn 0) (NNReal.coe_nonneg _))
          · exact hd₁.trans (mul_le_mul_of_nonneg_left (hn 1) (NNReal.coe_nonneg _))
      _ ≤ _ := by linarith [mul_nonneg hM (Real.rpow_nonneg (norm_nonneg (y - x)) (1 / 2 : ℝ))]
  · -- the lower part: far from `x`
    have hfar : x 1 ≤ ‖y - x‖ := by linarith [neg_le_abs (y 1 - x 1), abs_sub_apply_le_norm x y 1]
    have hfar' : x 1 ^ (1 / 2 : ℝ) ≤ ‖y - x‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hx.le hfar (by norm_num)
    have hb : |W y - W x| ≤ 2 * |M₀| := by
      linarith [hWb y (hS hy), hWb x (hS hxQ), le_abs_self M₀, abs_sub (W y) (W x)]
    calc |W y - W x| ≤ 2 * |M₀| / x 1 ^ (1 / 2 : ℝ) * x 1 ^ (1 / 2 : ℝ) := by
          rwa [div_mul_cancel₀ _ hx'.ne']
      _ ≤ 2 * |M₀| / x 1 ^ (1 / 2 : ℝ) * ‖y - x‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hfar' hM
      _ ≤ _ := by
          have hs := Real.rpow_nonneg (norm_nonneg (y - x)) (1 / 2 : ℝ)
          linarith [mul_nonneg Cx.coe_nonneg hs, mul_nonneg Cy.coe_nonneg hs]

/-- Integrals over a thinning vertical strip `|y₁ - c| < ε` tend to zero. -/
theorem tendsto_setIntegral_inter_abs_lt {U : Set (ℝ^2)} {g : ℝ^2 → ℝ} (hg : IntegrableOn g U)
    (c : ℝ) : Tendsto (fun ε ↦ ∫ y in U ∩ {y | |y 0 - c| < ε}, g y) (𝓝[>] 0) (𝓝 0) := by
  have h₀ : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have hm : ∀ ε : ℝ, MeasurableSet {y : ℝ^2 | |y 0 - c| < ε} := fun ε ↦
    measurableSet_lt (continuous_abs.measurable.comp (h₀.sub measurable_const)) measurable_const
  have h : ∀ ε, ∫ y in U ∩ {y | |y 0 - c| < ε}, g y =
      ∫ y in U, {y : ℝ^2 | |y 0 - c| < ε}.indicator g y := fun ε ↦ by
    rw [setIntegral_indicator (hm ε)]
  simp_rw [h]
  have hdom := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
    (μ := volume.restrict U) (f := fun _ ↦ (0 : ℝ))
    (F := fun ε ↦ {y : ℝ^2 | |y 0 - c| < ε}.indicator g) (fun y ↦ ‖g y‖)
    (Eventually.of_forall fun ε ↦ hg.aestronglyMeasurable.indicator (hm ε))
    (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ norm_indicator_le_norm_self _ y)
    hg.norm ?_
  · rwa [integral_zero] at hdom
  have hae : ∀ᵐ y : ℝ^2, y 0 ≠ c := measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq c)
  filter_upwards [ae_restrict_of_ae hae] with y hy
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hy)))] with ε hε
  rw [indicator_of_notMem (show y ∉ {y : ℝ^2 | |y 0 - c| < ε} from fun h ↦ (not_lt.2 hε.le) h)]

/-- `K₂(q - y) W(y)` is integrable on a measurable part `T` of a bounded set on which `W` is
bounded, if `T` stays at horizontal distance at least `ε > 0` from `q`. -/
theorem integrableOn_shearKernel_mul (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {S T : Set (ℝ^2)} (hS : Bornology.IsBounded S)
    {M₀ : ℝ} (hWb : ∀ y ∈ S, |W y| ≤ M₀) (q : ℝ^2) {ε : ℝ} (hε : 0 < ε) (hTS : T ⊆ S)
    (hTm : MeasurableSet T) (hTε : ∀ y ∈ T, ε ≤ |y 0 - q 0|) :
    IntegrableOn (fun y ↦ K (q - y) * W y) T := by
  refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2) * M₀)
    ((measure_mono hTS).trans_lt hS.measure_lt_top).ne
    (((measurable_shearKernel hK).comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hWm) ?_
  filter_upwards [ae_restrict_mem hTm] with y hy
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul ((abs_shearKernel_le hK _).trans ?_) (hWb y (hTS hy)) (abs_nonneg _)
    (by positivity)
  have h1 := (hTε y hy).trans (abs_sub_apply_le_norm q y 0)
  rw [norm_sub_rev] at h1
  gcongr

/-- The integrals of `K₂(x - y) W(y)` over `Q(x)` and a thinning vertical strip around another
abscissa `q ≠ x₁` tend to zero. -/
theorem tendsto_setIntegral_box_inter_abs_lt
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {W : ℝ^2 → ℝ}
    (hWm : AEStronglyMeasurable W) {x : ℝ^2} {M₀ : ℝ} (hWb : ∀ y ∈ box a a a x, |W y| ≤ M₀)
    {q : ℝ} (hq : q ≠ x 0) :
    Tendsto (fun ε ↦ ∫ y in box a a a x ∩ {y | |y 0 - q| < ε}, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 0) := by
  set δ := |x 0 - q| / 2 with hδ
  have hδ0 : 0 < δ := by have := abs_pos.2 (sub_ne_zero.2 hq.symm); positivity
  have h₀ : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have hU : IntegrableOn (fun y ↦ K (x - y) * W y) (box a a a x ∩ {y | δ ≤ |y 0 - x 0|}) :=
    integrableOn_shearKernel_mul hK hWm (isBounded_box x) hWb x hδ0 inter_subset_left
      ((measurableSet_box x).inter (measurableSet_le measurable_const
        (continuous_abs.measurable.comp (h₀.sub measurable_const)))) fun y hy ↦ hy.2
  refine (tendsto_setIntegral_inter_abs_lt hU q).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hδ0)] with ε hε
  have hset : (box a a a x ∩ {y | δ ≤ |y 0 - x 0|}) ∩ {y | |y 0 - q| < ε} =
      box a a a x ∩ {y | |y 0 - q| < ε} := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, ?_⟩, h.2⟩⟩
    have h1 := abs_sub_abs_le_abs_sub (x 0 - q) (y 0 - q)
    rw [show x 0 - q - (y 0 - q) = -(y 0 - x 0) by ring, abs_neg] at h1
    have h2 : |x 0 - q| = 2 * δ := by rw [hδ]; ring
    linarith [h.2]
  rw [hset]

/-- **The rescaled column representation** of the difference of the strip truncations at two
points `x = (m + c, x₂)`, `z = (m - c, x₂)`, `c > 0`: with `B = a/c` and `0 < ε ≤ c`, the
difference of the integrals over `Q(z) ∩ {|y₁ - z₁| ≥ ε}` and `Q(x) ∩ {|y₁ - x₁| ≥ ε}` is the
integral over the columns `p` with `|p ∓ 1| ≥ ε/c` of
`∫_{-B}^{B} Δ_B(p, τ) W(m + c p, x₂ - c τ) dτ`, up to the integrals over `Q(z)` and `Q(x)` near the
other point. -/
theorem integral_inter_strip_sub_eq (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {x z : ℝ^2} {m c : ℝ}
    (hx0 : x 0 = m + c) (hz0 : z 0 = m - c) (hxz : x 1 = z 1) {M₀ : ℝ}
    (hWb : ∀ y ∈ box a a a x ∪ box a a a z, |W y| ≤ M₀) {ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    Integrable ({p : ℝ | ε / c ≤ |p - 1| ∧ ε / c ≤ |p + 1|}.indicator fun p ↦
        ∫ τ in Icc (-(a / c)) (a / c),
          localShearDifference (a / c) p τ * W !₂[m + c * p, x 1 - c * τ]) ∧
      (∫ y in box a a a z ∩ {y | ε ≤ |y 0 - z 0|}, K (z - y) * W y) -
          ∫ y in box a a a x ∩ {y | ε ≤ |y 0 - x 0|}, K (x - y) * W y =
        (∫ p, {p : ℝ | ε / c ≤ |p - 1| ∧ ε / c ≤ |p + 1|}.indicator (fun p ↦
            ∫ τ in Icc (-(a / c)) (a / c),
              localShearDifference (a / c) p τ * W !₂[m + c * p, x 1 - c * τ]) p) +
          (∫ y in box a a a z ∩ {y | |y 0 - x 0| < ε}, K (z - y) * W y) -
          ∫ y in box a a a x ∩ {y | |y 0 - z 0| < ε}, K (x - y) * W y := by
  have hc : 0 < c := by linarith
  set B := a / c with hB
  set Qx := box a a a x with hQx
  set Qz := box a a a z with hQz
  have hQxm : MeasurableSet Qx := measurableSet_box x
  have hQzm : MeasurableSet Qz := measurableSet_box z
  have hSb : Bornology.IsBounded (Qx ∪ Qz) := (isBounded_box x).union (isBounded_box z)
  have h₀ : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have hstrip (q ε : ℝ) : MeasurableSet {y : ℝ^2 | ε ≤ |y 0 - q|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (h₀.sub measurable_const))
  have hstrip' (q ε : ℝ) : MeasurableSet {y : ℝ^2 | |y 0 - q| < ε} :=
    measurableSet_lt (continuous_abs.measurable.comp (h₀.sub measurable_const)) measurable_const
  have hbdd (q : ℝ^2) {T : Set (ℝ^2)} (hTS : T ⊆ Qx ∪ Qz) (hTm : MeasurableSet T)
      (hTε : ∀ y ∈ T, ε ≤ |y 0 - q 0|) : IntegrableOn (fun y ↦ K (q - y) * W y) T :=
    integrableOn_shearKernel_mul hK hWm hSb hWb q hε hTS hTm hTε
  have hfarx (y : ℝ^2) (hy : |y 0 - z 0| < ε) : ε ≤ |y 0 - x 0| :=
    le_abs.2 (Or.inr (by linarith [(abs_lt.1 hy).2]))
  have hfarz (y : ℝ^2) (hy : |y 0 - x 0| < ε) : ε ≤ |y 0 - z 0| :=
    le_abs.2 (Or.inl (by linarith [(abs_lt.1 hy).1]))
  set T : Set (ℝ^2) := {y | ε ≤ |y 0 - x 0| ∧ ε ≤ |y 0 - z 0|} with hT
  have hTm : MeasurableSet T := (hstrip (x 0) ε).inter (hstrip (z 0) ε)
  -- the decomposition
  have hux : Qx ∩ {y | ε ≤ |y 0 - x 0|} = (Qx ∩ T) ∪ (Qx ∩ {y | |y 0 - z 0| < ε}) := by
    ext y
    simp only [hT, mem_inter_iff, mem_union, mem_ofPred_eq]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ (le_or_gt ε |y 0 - z 0|).imp (⟨h₁, h₂, ·⟩) (⟨h₁, ·⟩), ?_⟩
    rintro (⟨h₁, h₂, -⟩ | ⟨h₁, h₂⟩)
    exacts [⟨h₁, h₂⟩, ⟨h₁, hfarx y h₂⟩]
  have huz : Qz ∩ {y | ε ≤ |y 0 - z 0|} = (Qz ∩ T) ∪ (Qz ∩ {y | |y 0 - x 0| < ε}) := by
    ext y
    simp only [hT, mem_inter_iff, mem_union, mem_ofPred_eq]
    refine ⟨fun ⟨h₁, h₂⟩ ↦ (le_or_gt ε |y 0 - x 0|).imp (⟨h₁, ·, h₂⟩) (⟨h₁, ·⟩), ?_⟩
    rintro (⟨h₁, -, h₂⟩ | ⟨h₁, h₂⟩)
    exacts [⟨h₁, h₂⟩, ⟨h₁, hfarz y h₂⟩]
  have hiz := hbdd z (inter_subset_left.trans subset_union_right) (hQzm.inter hTm)
    fun y hy ↦ hy.2.2
  have hix := hbdd x (inter_subset_left.trans subset_union_left) (hQxm.inter hTm)
    fun y hy ↦ hy.2.1
  have hdec : (∫ y in Qz ∩ {y | ε ≤ |y 0 - z 0|}, K (z - y) * W y) -
      ∫ y in Qx ∩ {y | ε ≤ |y 0 - x 0|}, K (x - y) * W y =
      ((∫ y in Qz ∩ T, K (z - y) * W y) - ∫ y in Qx ∩ T, K (x - y) * W y) +
        (∫ y in Qz ∩ {y | |y 0 - x 0| < ε}, K (z - y) * W y) -
        ∫ y in Qx ∩ {y | |y 0 - z 0| < ε}, K (x - y) * W y := by
    rw [hux, huz, setIntegral_union (disjoint_left.2 fun y h₁ h₂ ↦ (not_lt.2 h₁.2.2) h₂.2)
      (hQxm.inter (hstrip' _ _)) hix (hbdd x (inter_subset_left.trans subset_union_left)
        (hQxm.inter (hstrip' _ _)) fun y hy ↦ hfarx y hy.2),
      setIntegral_union (disjoint_left.2 fun y h₁ h₂ ↦ (not_lt.2 h₁.2.1) h₂.2)
      (hQzm.inter (hstrip' _ _)) hiz (hbdd z (inter_subset_left.trans subset_union_right)
        (hQzm.inter (hstrip' _ _)) fun y hy ↦ hfarz y hy.2)]
    ring
  -- the rescaling
  set f : ℝ → ℝ := fun p ↦ ∫ τ in Icc (-B) B,
    localShearDifference B p τ * W !₂[m + c * p, x 1 - c * τ] with hf
  set Jc : Set ℝ := {p | ε / c ≤ |p - 1| ∧ ε / c ≤ |p + 1|} with hJc
  set F : ℝ^2 → ℝ := T.indicator fun y ↦ boxKernelDifference K a a a z x y * W y with hF
  have hFeq : F = (Qz ∩ T).indicator (fun y ↦ K (z - y) * W y) -
      (Qx ∩ T).indicator (fun y ↦ K (x - y) * W y) := by
    ext y
    simp only [hF, boxKernelDifference, Pi.sub_apply, hQx, hQz, indicator_apply]
    by_cases h₁ : y ∈ T <;> by_cases h₂ : y ∈ box a a a z <;> by_cases h₃ : y ∈ box a a a x <;>
      simp [h₁, h₂, h₃, sub_mul]
  have hzT := hiz.integrable_indicator (hQzm.inter hTm)
  have hxT := hix.integrable_indicator (hQxm.inter hTm)
  have hFi : Integrable F := hFeq ▸ hzT.sub hxT
  obtain ⟨hint, hval⟩ := integral_eq_mul_integral_integral hFi hc m (x 1)
  have hD (p τ : ℝ) : boxKernelDifference K a a a z x !₂[m + c * p, x 1 - c * τ] =
      (if |τ| ≤ B then localShearDifference B p τ else 0) / c ^ 2 := by
    have := boxKernelDifference_shear_mk (a := a) hK hxz (by linarith) p τ
    rwa [show (x 0 + z 0) / 2 = m by rw [hx0, hz0]; ring,
      show (x 0 - z 0) / 2 = c by rw [hx0, hz0]; ring] at this
  have hTp (p τ : ℝ) : !₂[m + c * p, x 1 - c * τ] ∈ T ↔ p ∈ Jc := by
    simp only [hT, hJc, mem_ofPred_eq, Matrix.cons_val_zero]
    rw [show m + c * p - x 0 = c * (p - 1) by rw [hx0]; ring,
      show m + c * p - z 0 = c * (p + 1) by rw [hz0]; ring, abs_mul, abs_mul, abs_of_pos hc,
      div_le_iff₀ hc, div_le_iff₀ hc, mul_comm (|p - 1|), mul_comm (|p + 1|)]
  have hpt (p : ℝ) : ∫ τ, F !₂[m + c * p, x 1 - c * τ] = Jc.indicator f p / c ^ 2 := by
    by_cases hp : p ∈ Jc
    · simp only [indicator_of_mem hp, hf, ← integral_indicator measurableSet_Icc, ← integral_div]
      congr 1 with τ
      rw [hF, indicator_of_mem ((hTp p τ).2 hp), hD]
      simp only [indicator_apply, mem_Icc, ← abs_le]
      split_ifs <;> ring
    · rw [indicator_of_notMem hp, zero_div]
      exact integral_eq_zero_of_ae (ae_of_all _ fun τ ↦ indicator_of_notMem (mt (hTp p τ).1 hp) _)
  refine ⟨(hint.const_mul (c ^ 2)).congr (ae_of_all _ fun p ↦ ?_), ?_⟩
  · simp only [hpt]
    field_simp
  · rw [hdec, ← integral_indicator (hQzm.inter hTm), ← integral_indicator (hQxm.inter hTm),
      ← integral_sub' hzT hxT, ← hFeq, hval]
    simp only [hpt, integral_div]
    field_simp

/-- A rescaled `1/2`-Hölder function: if `f` is `1/2`-Hölder with constant `C` on `S` and
`e - c τ ∈ S` for `τ ∈ T` (`c > 0`), then `τ ↦ f(e - c τ)` is `1/2`-Hölder on `T` with constant
`C c^{1/2}`. -/
theorem holderOnWith_comp_sub_mul {f : ℝ → ℝ} {C : ℝ≥0} {S : Set ℝ}
    (hf : HolderOnWith C (1 / 2) f S) {c : ℝ} (hc : 0 < c) (e : ℝ) {T : Set ℝ}
    (hT : ∀ τ ∈ T, e - c * τ ∈ S) :
    HolderOnWith (C * (c ^ (1 / 2 : ℝ)).toNNReal) (1 / 2) (fun τ ↦ f (e - c * τ)) T := by
  intro τ hτ τ' hτ'
  refine (hf _ (hT τ hτ) _ (hT τ' hτ')).trans ?_
  rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
    show e - c * τ - (e - c * τ') = c * (τ' - τ) by ring, abs_mul, abs_of_pos hc, abs_sub_comm,
    ENNReal.coe_mul, mul_assoc]
  gcongr
  rw [ENNReal.ofReal_mul hc.le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hc.le (by norm_num), ENNReal.ofReal]
  norm_num

/-- The rescaled point `(m + c q, x₂ - c τ)` of two points `x = (m + c, x₂)`, `z = (m - c, x₂)`
lies in `Q(x) ∪ Q(z)` when `|τ| ≤ a/c` and `|q - 1| ≤ a/c` or `|q + 1| ≤ a/c`. -/
theorem mk_mem_box_union {x z : ℝ^2} {m c : ℝ} (hc : 0 < c) (hx0 : x 0 = m + c)
    (hz0 : z 0 = m - c) (hxz : x 1 = z 1) {q τ : ℝ}
    (hq : |q - 1| ≤ a / c ∨ |q + 1| ≤ a / c) (hτ : |τ| ≤ a / c) :
    !₂[m + c * q, x 1 - c * τ] ∈ box a a a x ∪ box a a a z := by
  have hτc : |x 1 - c * τ - x 1| ≤ a := by
    rw [show x 1 - c * τ - x 1 = c * -τ by ring, abs_mul, abs_of_pos hc, abs_neg]
    rwa [le_div_iff₀ hc, mul_comm] at hτ
  rcases hq with hq | hq
  · left
    rw [mk_mem_box, mem_Icc_iff_abs_sub_le, mem_Icc_iff_abs_sub_le]
    refine ⟨?_, hτc⟩
    rw [show m + c * q - x 0 = c * (q - 1) by rw [hx0]; ring, abs_mul, abs_of_pos hc]
    rwa [le_div_iff₀ hc, mul_comm] at hq
  · right
    rw [mk_mem_box, mem_Icc_iff_abs_sub_le, mem_Icc_iff_abs_sub_le, ← hxz]
    refine ⟨?_, hτc⟩
    rw [show m + c * q - z 0 = c * (q + 1) by rw [hz0]; ring, abs_mul, abs_of_pos hc]
    rwa [le_div_iff₀ hc, mul_comm] at hq

/-- A rescaled column `τ ↦ W(m + c q, x₂ - c τ)` inside the boxes is `1/2`-Hölder with constant
`C_y c^{1/2}` on `[-a/c, min(x₂/c, a/c)]`, where it reads the upper half-plane. -/
theorem holderOnWith_column {W : ℝ^2 → ℝ} {x z : ℝ^2} {m c : ℝ} (hc : 0 < c)
    (hx0 : x 0 = m + c) (hz0 : z 0 = m - c) (hxz : x 1 = z 1) {Cy : ℝ≥0}
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a a a x ∪ box a a a z) ∩ {y | 0 ≤ y 1}) W ≤ Cy) {q : ℝ}
    (hq : |q - 1| ≤ a / c ∨ |q + 1| ≤ a / c) :
    HolderOnWith (Cy * (c ^ (1 / 2 : ℝ)).toNNReal) (1 / 2)
      (fun τ ↦ W !₂[m + c * q, x 1 - c * τ]) (Icc (-(a / c)) (min (x 1 / c) (a / c))) := by
  have hs := HolderSpace.holderOnWith_slice_one hCy (m + c * q)
  refine holderOnWith_comp_sub_mul hs hc (x 1) fun τ hτ ↦ ?_
  have hτB : |τ| ≤ a / c := abs_le.2 ⟨hτ.1, hτ.2.trans (min_le_right _ _)⟩
  refine ⟨mk_mem_box_union hc hx0 hz0 hxz hq hτB, ?_⟩
  have : c * τ ≤ x 1 := by
    have h := mul_le_mul_of_nonneg_left (hτ.2.trans (min_le_left _ _)) hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at h
  simp only [mem_ofPred_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  linarith

/-- On a rescaled column the odd extension pairs `τ > x₂/c` with `2 x₂/c - τ`. -/
theorem column_odd {W : ℝ^2 → ℝ} (hodd : ∀ y : ℝ^2, y 1 < 0 → W y = -W !₂[y 0, -y 1])
    {c e : ℝ} (hc : 0 < c) (s : ℝ) {τ : ℝ} (hτ : e / c < τ) :
    W !₂[s, e - c * τ] = -W !₂[s, e - c * (2 * (e / c) - τ)] := by
  have hlt : (!₂[s, e - c * τ] : ℝ^2) 1 < 0 := by
    have : e < c * τ := by
      have h := mul_lt_mul_of_pos_left hτ hc
      rwa [mul_div_cancel₀ _ hc.ne'] at h
    simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linarith
  rw [hodd _ hlt]
  congr 2
  ext i
  fin_cases i
  · simp
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    ring

/-- Two rescaled columns at the same height inside the boxes differ by at most
`C_x c^{1/2} |p - q|^{1/2}`. -/
theorem abs_column_sub_le {W : ℝ^2 → ℝ} {x z : ℝ^2} {m c : ℝ} (hc : 0 < c)
    (hx0 : x 0 = m + c) (hz0 : z 0 = m - c) (hxz : x 1 = z 1) {Cx : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a a a x ∪ box a a a z) W ≤ Cx)
    {p q τ : ℝ} (hp : |p - 1| ≤ a / c ∨ |p + 1| ≤ a / c) (hq : |q - 1| ≤ a / c ∨ |q + 1| ≤ a / c)
    (hτ : |τ| ≤ a / c) :
    |W !₂[m + c * p, x 1 - c * τ] - W !₂[m + c * q, x 1 - c * τ]| ≤
      (Cx * (c ^ (1 / 2 : ℝ)).toNNReal : ℝ≥0) * |p - q| ^ (1 / 2 : ℝ) := by
  have hs := (HolderSpace.holderOnWith_slice_zero hCx (x 1 - c * τ)).dist_le
    (show m + c * p ∈ {s | !₂[s, x 1 - c * τ] ∈ box a a a x ∪ box a a a z} from
      mk_mem_box_union hc hx0 hz0 hxz hp hτ)
    (show m + c * q ∈ {s | !₂[s, x 1 - c * τ] ∈ box a a a x ∪ box a a a z} from
      mk_mem_box_union hc hx0 hz0 hxz hq hτ)
  rw [Real.dist_eq, Real.dist_eq, show m + c * p - (m + c * q) = c * (p - q) by ring, abs_mul,
    abs_of_pos hc, show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num,
    Real.mul_rpow hc.le (abs_nonneg _)] at hs
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
  calc _ ≤ Cx * (c ^ (1 / 2 : ℝ) * |p - q| ^ (1 / 2 : ℝ)) := hs
    _ = _ := by ring
/-- The column integrals over `|p ∓ 1| ≥ ε/c` of the rescaled kernel difference tend to
`(v_z + (π/2) W(z)) - (v_x + (π/2) W(x))`: the strip principal values
(`tendsto_setIntegral_box_inter_strip`) in the column representation
(`integral_inter_strip_sub_eq`), whose integrals near the other point vanish in the limit. -/
private theorem tendsto_integral_columns (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} {x z : ℝ^2} {m c : ℝ} (hc : 0 < c) (hx0 : x 0 = m + c) (hz0 : z 0 = m - c)
    (hxz : x 1 = z 1) (hx : 0 < x 1) (ha : 0 < a) (hWm : AEStronglyMeasurable W) {M₀ : ℝ}
    (hWb : ∀ y ∈ box a a a x ∪ box a a a z, |W y| ≤ M₀) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a a a x ∪ box a a a z) W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a a a x ∪ box a a a z) ∩ {y | 0 ≤ y 1}) W ≤ Cy) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in box a a a x \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in box a a a z \ ball z ε, K (z - y) * W y) (𝓝[>] 0)
      (𝓝 vz)) :
    Tendsto (fun ε ↦ ∫ p, {p : ℝ | ε / c ≤ |p - 1| ∧ ε / c ≤ |p + 1|}.indicator (fun p ↦
        ∫ τ in Icc (-(a / c)) (a / c),
          localShearDifference (a / c) p τ * W !₂[m + c * p, x 1 - c * τ]) p) (𝓝[>] 0)
      (𝓝 ((vz + Real.pi / 2 * W z) - (vx + Real.pi / 2 * W x))) := by
  have hlt : z 0 < x 0 := by linarith
  have hz : 0 < z 1 := hxz ▸ hx
  have hsx := tendsto_setIntegral_box_inter_strip hK ha ha ha hWm (by norm_num : (0 : ℝ) < 1 / 2)
    (abs_sub_le_of_directionalSeminorm hx subset_union_left hCx hCy hWb) hvx
  have hsz := tendsto_setIntegral_box_inter_strip hK ha ha ha hWm (by norm_num : (0 : ℝ) < 1 / 2)
    (abs_sub_le_of_directionalSeminorm hz subset_union_right hCx hCy hWb) hvz
  have hrx := tendsto_setIntegral_box_inter_abs_lt hK hWm (fun y hy ↦ hWb y (Or.inl hy)) hlt.ne
  have hrz := tendsto_setIntegral_box_inter_abs_lt hK hWm (fun y hy ↦ hWb y (Or.inr hy)) hlt.ne'
  have h := (hsz.sub hsx).sub (hrz.sub hrx)
  rw [sub_zero, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_le_nhds hc)] with ε (hε : 0 < ε) hεc
  rw [(integral_inter_strip_sub_eq hK hWm hx0 hz0 hxz hWb hε hεc).2]
  ring

/-- A bound `|L| ≤ c^{1/2} X` gives `|L| / (π (2c)^{1/2}) ≤ X / (π √2)`. -/
private theorem ofReal_shear_quotient_le {c L : ℝ} (hc : 0 < c) {X : ℝ≥0∞}
    (h : ENNReal.ofReal |L| ≤ ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * X) :
    ENNReal.ofReal (|L| / (Real.pi * (2 * c) ^ (1 / 2 : ℝ))) ≤
      X / ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
  have hsc : 0 < c ^ (1 / 2 : ℝ) := by positivity
  have hq : 0 < Real.pi * (2 * c) ^ (1 / 2 : ℝ) := by positivity
  have e : Real.pi * (2 * c) ^ (1 / 2 : ℝ) = c ^ (1 / 2 : ℝ) * (Real.pi * Real.sqrt 2) := by
    rw [Real.mul_rpow (by norm_num) hc.le, ← Real.sqrt_eq_rpow]
    ring
  rw [ENNReal.ofReal_div_of_pos hq, e, ENNReal.ofReal_mul hsc.le,
    ← ENNReal.mul_div_mul_left X _ (ENNReal.ofReal_pos.2 hsc).ne' ENNReal.ofReal_ne_top]
  gcongr

/-- **Chen and Hou, Part I, Lemma 3.4, the estimate of `u_y`**, for the strip principal values.
Let `x, z` lie at the same height `x₂ > 0` with `x₁ ≠ z₁`, `a ≥ 2 |x - z|`, and let `W` be
measurable, bounded by `M₀` on `Q(x) ∪ Q(z)` (`Q = Q_{a,a,a}`), odd in the second coordinate,
with horizontal `1/2`-Hölder seminorm at most `C_x` on `Q(x) ∪ Q(z)` and vertical seminorm at most
`C_y` on its upper part. If the disc truncations of `∫_{Q(x)} K₂(x - y) W(y) dy` and
`∫_{Q(z)} K₂(z - y) W(y) dy` converge to `v_x`, `v_z`, then, with `B = 2a/|x - z|`,
`h = 2x₂/|x - z|` and `A = min(h, B)`,

`|(v_x + (π/2) W(x)) - (v_z + (π/2) W(z))| / (π |x - z|^{1/2}) ≤
  (C_x S̃_{1D}(B, A) + C_y (S_up(B, A) + S_out(B, h))) / (π √2)`.

For the localized velocity, `u_y = π⁻¹ v + W(x)/2` (Part I, (3.4)), so the left side is the
Hölder quotient of `u_y` (Part I, Appendix B.1.5, (B.40)). -/
theorem abs_sub_div_le_shear (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} {x z : ℝ^2} (hxz : x 1 = z 1) (hne : x 0 ≠ z 0) (hx : 0 < x 1)
    (ha : 2 * |x 0 - z 0| ≤ a) (hWm : AEStronglyMeasurable W) {M₀ : ℝ}
    (hWb : ∀ y ∈ box a a a x ∪ box a a a z, |W y| ≤ M₀)
    (hodd : ∀ y : ℝ^2, y 1 < 0 → W y = -W !₂[y 0, -y 1]) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a a a x ∪ box a a a z) W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a a a x ∪ box a a a z) ∩ {y | 0 ≤ y 1}) W ≤ Cy) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in box a a a x \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in box a a a z \ ball z ε, K (z - y) * W y) (𝓝[>] 0)
      (𝓝 vz)) :
    ENNReal.ofReal (|(vx + Real.pi / 2 * W x) - (vz + Real.pi / 2 * W z)| /
        (Real.pi * |x 0 - z 0| ^ (1 / 2 : ℝ))) ≤
      (Cx * shearMassCost (2 * a / |x 0 - z 0|)
          (min (2 * x 1 / |x 0 - z 0|) (2 * a / |x 0 - z 0|)) +
        Cy * (shearUpperCost (2 * a / |x 0 - z 0|)
            (min (2 * x 1 / |x 0 - z 0|) (2 * a / |x 0 - z 0|)) +
          shearOuterCost (2 * a / |x 0 - z 0|) (2 * x 1 / |x 0 - z 0|))) /
        ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
  wlog hlt : z 0 < x 0 generalizing x z vx vz
  · have := this hxz.symm hne.symm (hxz ▸ hx) (by rwa [abs_sub_comm]) (by rwa [union_comm])
      (by rwa [union_comm]) (by rwa [union_comm]) hvz hvx (lt_of_le_of_ne (not_lt.1 hlt) hne)
    rwa [abs_sub_comm (vz + _), abs_sub_comm (z 0), ← hxz] at this
  obtain ⟨c, m, hc, hx0, hz0⟩ : ∃ c m : ℝ, 0 < c ∧ x 0 = m + c ∧ z 0 = m - c :=
    ⟨(x 0 - z 0) / 2, (x 0 + z 0) / 2, by linarith, by ring, by ring⟩
  have hd : |x 0 - z 0| = 2 * c := by rw [hx0, hz0, abs_of_pos (by linarith)]; ring
  rw [hd] at ha
  rw [hd, mul_div_mul_left a c two_ne_zero, mul_div_mul_left (x 1) c two_ne_zero]
  set B := a / c
  set h := x 1 / c
  have hB4 : 4 ≤ B := (le_div_iff₀ hc).2 (by linarith)
  have hh0 : 0 < h := by positivity
  -- the column representation and its limit
  set w : ℝ → ℝ → ℝ := fun p τ ↦ W !₂[m + c * p, x 1 - c * τ]
  set f : ℝ → ℝ := fun p ↦ ∫ τ in Icc (-B) B, localShearDifference B p τ * w p τ with hf
  set Jc : ℝ → Set ℝ := fun ε ↦ {p | ε / c ≤ |p - 1| ∧ ε / c ≤ |p + 1|} with hJc
  set E : ℝ → ℝ := fun ε ↦ ∫ p, (Jc ε).indicator f p
  have hrep (ε : ℝ) (hε : 0 < ε) (hεc : ε ≤ c) : Integrable ((Jc ε).indicator f) :=
    (integral_inter_strip_sub_eq hK hWm hx0 hz0 hxz hWb hε hεc).1
  have hlim : Tendsto E (𝓝[>] 0) (𝓝 ((vz + Real.pi / 2 * W z) - (vx + Real.pi / 2 * W x))) :=
    tendsto_integral_columns hK hc hx0 hz0 hxz hx (by linarith) hWm hWb hCx hCy hvx hvz
  -- the column bound
  set Cx' : ℝ≥0 := Cx * (c ^ (1 / 2 : ℝ)).toNNReal with hCx'
  set Cy' : ℝ≥0 := Cy * (c ^ (1 / 2 : ℝ)).toNNReal with hCy'
  set A := min h B
  set bnd : ℝ → ℝ≥0∞ := fun p ↦ 4 * Cy' * shearCost B A p +
    Cx' * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|) +
    2 * Cy' * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
      ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ with hbnd
  have hcol (p : ℝ) (hp : 0 < p) (hp1 : p ≠ 1) (hpB : p ≤ B + 1) :
      ENNReal.ofReal |f p + f (-p)| ≤ bnd p := by
    have hpx : |p - 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
    have hpz : |-p + 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
    refine abs_integral_localShearDifference_add_le (by linarith : (2 : ℝ) ≤ B) hh0 hp hp1
      (holderOnWith_column hc hx0 hz0 hxz hCy (Or.inl hpx))
      (holderOnWith_column hc hx0 hz0 hxz hCy (Or.inr hpz))
      (fun τ hτ ↦ column_odd hodd hc _ hτ.1) (fun τ hτ ↦ column_odd hodd hc _ hτ.1) fun τ hτ ↦ ?_
    have := abs_column_sub_le hc hx0 hz0 hxz hCx (τ := τ) (Or.inl hpx) (Or.inr hpz)
      (abs_le.2 ⟨by linarith [hτ.1, min_le_right h B], hτ.2.trans (min_le_right _ _)⟩)
    rwa [show p - -p = 2 * p by ring, abs_of_pos (by linarith : (0 : ℝ) < 2 * p)] at this
  -- the bound almost everywhere on `p > 0`
  have hae_bnd (ε : ℝ) : ∀ᵐ p ∂(volume.restrict (Ioi 0)),
      ‖(Jc ε).indicator f p + (Jc ε).indicator f (-p)‖ₑ ≤ bnd p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (Measure.ae_ne volume 1)] with p (hp : 0 < p) hp1
    have hJneg : -p ∈ Jc ε ↔ p ∈ Jc ε := by
      simp only [hJc, mem_ofPred_eq, show -p - 1 = -(p + 1) by ring, neg_add_eq_sub, abs_neg,
        abs_sub_comm 1 p, and_comm]
    by_cases hJ : p ∈ Jc ε
    · rw [indicator_of_mem hJ, indicator_of_mem (hJneg.2 hJ), Real.enorm_eq_ofReal_abs]
      by_cases hpB : p ≤ B + 1
      · exact hcol p hp hp1 hpB
      · simp only [hf, localShearDifference_neg_left, localShearDifference_of_gt (not_le.1 hpB),
          neg_zero, zero_mul, integral_zero, add_zero, abs_zero, ENNReal.ofReal_zero, zero_le]
    · simp only [indicator_of_notMem hJ, indicator_of_notMem (mt hJneg.1 hJ), add_zero, enorm_zero,
        zero_le]
  -- integrating the bound
  have hlint : ∫⁻ p in Ioi 0, bnd p =
      Cx' * shearMassCost B A + Cy' * (shearUpperCost B A + shearOuterCost B h) := by
    have hm₁ : Measurable fun p : ℝ ↦ ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|) :=
      (((measurable_id.const_mul 2).pow_const _).mul
        (continuous_abs.measurable.comp (measurable_shearMass B A))).ennreal_ofReal
    simp only [hbnd]
    rw [lintegral_add_right _ ((measurable_lintegral_localShearDifference B h).const_mul _),
      lintegral_add_right _ (hm₁.const_mul _), lintegral_const_mul' _ _ (by finiteness),
      lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by finiteness)]
    simp only [shearMassCost, shearUpperCost, shearOuterCost]
    ring
  set Bd := Cx' * shearMassCost B A + Cy' * (shearUpperCost B A + shearOuterCost B h) with hBd
  -- the limit
  have hLbd : ENNReal.ofReal |(vz + Real.pi / 2 * W z) - (vx + Real.pi / 2 * W x)| ≤ Bd := by
    refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_abs.tendsto _).comp hlim)) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds hc)] with ε (hε : 0 < ε) hεc
    change ENNReal.ofReal |∫ p, (Jc ε).indicator f p| ≤ Bd
    rw [PDE.Analysis.integral_eq_integral_Ioi_add_reflection (hrep ε hε hεc),
      ← Real.enorm_eq_ofReal_abs, ← hlint]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae (hae_bnd ε))
  -- dividing by `π |x - z|^{1/2}`
  rw [abs_sub_comm]
  refine ofReal_shear_quotient_le hc (hLbd.trans_eq ?_)
  rw [hBd, hCx', hCy', ENNReal.coe_mul, ENNReal.coe_mul, ← ENNReal.ofReal]
  ring

/-- **Chen and Hou, Part I, Lemma 3.4, the estimate of `v_x`**, for the strip principal values,
under the hypotheses of `abs_sub_div_le_shear`: with `B = 2a/|x - z|`, `h = 2x₂/|x - z|` and
`A = min(h, B)`,

`|(v_x - (π/2) W(x)) - (v_z - (π/2) W(z))| / (π |x - z|^{1/2}) ≤
  (C_x (S_{in,x}(B, A) + S_{1D}(B, A)) + C_y (S_up(B, A) + S_low(B, A) + S_out(B, h))) / (π √2)`.

For the localized velocity, `v_x = π⁻¹ v - W(x)/2` (Part I, (3.4)), so the left side is the Hölder
quotient of `v_x` (Part I, Appendix B.1, (B.1) and (B.39)):
on the columns `0 < p ≤ 9` the column masses are moved vertically to the height of the two
points, and from there horizontally to the two points (`abs_integral_shearMass_mul_add_le`),
where they cancel the local term `-W`. -/
theorem abs_sub_div_le_shear_residual (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} {x z : ℝ^2} (hxz : x 1 = z 1) (hne : x 0 ≠ z 0) (hx : 0 < x 1)
    (ha : 2 * |x 0 - z 0| ≤ a) (hWm : AEStronglyMeasurable W) {M₀ : ℝ}
    (hWb : ∀ y ∈ box a a a x ∪ box a a a z, |W y| ≤ M₀)
    (hodd : ∀ y : ℝ^2, y 1 < 0 → W y = -W !₂[y 0, -y 1]) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a a a x ∪ box a a a z) W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a a a x ∪ box a a a z) ∩ {y | 0 ≤ y 1}) W ≤ Cy) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in box a a a x \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in box a a a z \ ball z ε, K (z - y) * W y) (𝓝[>] 0)
      (𝓝 vz)) :
    ENNReal.ofReal (|(vx - Real.pi / 2 * W x) - (vz - Real.pi / 2 * W z)| /
        (Real.pi * |x 0 - z 0| ^ (1 / 2 : ℝ))) ≤
      (Cx * (shearInnerMassCost (2 * a / |x 0 - z 0|)
            (min (2 * x 1 / |x 0 - z 0|) (2 * a / |x 0 - z 0|)) +
          shearLineCost (2 * a / |x 0 - z 0|)
            (min (2 * x 1 / |x 0 - z 0|) (2 * a / |x 0 - z 0|))) +
        Cy * (shearUpperCost (2 * a / |x 0 - z 0|)
            (min (2 * x 1 / |x 0 - z 0|) (2 * a / |x 0 - z 0|)) +
          shearLowerCost (2 * a / |x 0 - z 0|)
            (min (2 * x 1 / |x 0 - z 0|) (2 * a / |x 0 - z 0|)) +
          shearOuterCost (2 * a / |x 0 - z 0|) (2 * x 1 / |x 0 - z 0|))) /
        ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
  wlog hlt : z 0 < x 0 generalizing x z vx vz
  · have := this hxz.symm hne.symm (hxz ▸ hx) (by rwa [abs_sub_comm]) (by rwa [union_comm])
      (by rwa [union_comm]) (by rwa [union_comm]) hvz hvx (lt_of_le_of_ne (not_lt.1 hlt) hne)
    rwa [abs_sub_comm (vz - _), abs_sub_comm (z 0), ← hxz] at this
  obtain ⟨c, m, hc, hx0, hz0⟩ : ∃ c m : ℝ, 0 < c ∧ x 0 = m + c ∧ z 0 = m - c :=
    ⟨(x 0 - z 0) / 2, (x 0 + z 0) / 2, by linarith, by ring, by ring⟩
  have hd : |x 0 - z 0| = 2 * c := by rw [hx0, hz0, abs_of_pos (by linarith)]; ring
  rw [hd] at ha
  rw [hd, mul_div_mul_left a c two_ne_zero, mul_div_mul_left (x 1) c two_ne_zero]
  set B := a / c
  set h := x 1 / c
  have hB4 : 4 ≤ B := (le_div_iff₀ hc).2 (by linarith)
  have hh0 : 0 < h := by positivity
  -- the column representation and its limit
  set w : ℝ → ℝ → ℝ := fun p τ ↦ W !₂[m + c * p, x 1 - c * τ] with hw
  set f : ℝ → ℝ := fun p ↦ ∫ τ in Icc (-B) B, localShearDifference B p τ * w p τ with hf
  set Jc : ℝ → Set ℝ := fun ε ↦ {p | ε / c ≤ |p - 1| ∧ ε / c ≤ |p + 1|} with hJc
  set E : ℝ → ℝ := fun ε ↦ ∫ p, (Jc ε).indicator f p
  have hrep (ε : ℝ) (hε : 0 < ε) (hεc : ε ≤ c) : Integrable ((Jc ε).indicator f) :=
    (integral_inter_strip_sub_eq hK hWm hx0 hz0 hxz hWb hε hεc).1
  set L := (vz + Real.pi / 2 * W z) - (vx + Real.pi / 2 * W x) with hL
  have hlim : Tendsto E (𝓝[>] 0) (𝓝 L) :=
    tendsto_integral_columns hK hc hx0 hz0 hxz hx (by linarith) hWm hWb hCx hCy hvx hvz
  -- the columns
  set Cx' : ℝ≥0 := Cx * (c ^ (1 / 2 : ℝ)).toNNReal with hCx'
  set Cy' : ℝ≥0 := Cy * (c ^ (1 / 2 : ℝ)).toNNReal with hCy'
  set A := min h B
  set M : ℝ → ℝ := shearMass B A with hM
  set u : ℝ → ℝ := fun p ↦ w p 0 with hu
  set G : ℝ → ℝ := fun p ↦ M p * (u p - u (-p)) with hG
  have hvert (q : ℝ) (hq : |q - 1| ≤ B ∨ |q + 1| ≤ B) :
      HolderOnWith Cy' (1 / 2) (w q) (Icc (-B) (min h B)) :=
    holderOnWith_column hc hx0 hz0 hxz hCy hq
  have hoddc (q τ : ℝ) (hτ : τ ∈ Ioc h B) : w q τ = -w q (2 * h - τ) := column_odd hodd hc _ hτ.1
  have hcolout (p : ℝ) (hp : 0 < p) (hp1 : p ≠ 1) (hpB : p ≤ B + 1) :
      ENNReal.ofReal |f p + f (-p)| ≤ 4 * Cy' * shearCost B A p +
        Cx' * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |M p|) +
        2 * Cy' * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
          ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ := by
    have hpx : |p - 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
    have hpz : |-p + 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
    refine abs_integral_localShearDifference_add_le (by linarith : (2 : ℝ) ≤ B) hh0 hp hp1
      (hvert p (Or.inl hpx)) (hvert (-p) (Or.inr hpz)) (hoddc p) (hoddc (-p)) fun τ hτ ↦ ?_
    have := abs_column_sub_le hc hx0 hz0 hxz hCx (τ := τ) (Or.inl hpx) (Or.inr hpz)
      (abs_le.2 ⟨by linarith [hτ.1, min_le_right h B], hτ.2.trans (min_le_right _ _)⟩)
    rwa [show p - -p = 2 * p by ring, abs_of_pos (by linarith : (0 : ℝ) < 2 * p)] at this
  have hcolin (p : ℝ) (hp : 0 < p) (hp1 : p ≠ 1) (hpB : p ≤ B + 1) :
      ENNReal.ofReal |f p + f (-p) - G p| ≤ 4 * Cy' * shearCost B A p +
        4 * Cy' * shearLowCost B A p + 2 * Cy' * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
          ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ := by
    have hpx : |p - 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
    have hpz : |-p + 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
    have h₁ := abs_integral_localShearDifference_sub_mul_le (by linarith : (2 : ℝ) ≤ B) hh0 hp
      hp1 (hvert p (Or.inl hpx)) (hoddc p)
    have h₂ := abs_integral_localShearDifference_sub_mul_le (by linarith : (2 : ℝ) ≤ B) hh0 hp
      hp1 (hvert (-p) (Or.inr hpz)) (hoddc (-p))
    have hneg : f (-p) = -∫ τ in Icc (-B) B, localShearDifference B p τ * w (-p) τ := by
      simp only [hf, localShearDifference_neg_left, neg_mul, integral_neg]
    have e : f p + f (-p) - G p =
        ((∫ τ in Icc (-B) B, localShearDifference B p τ * w p τ) - M p * w p 0) -
          ((∫ τ in Icc (-B) B, localShearDifference B p τ * w (-p) τ) - M p * w (-p) 0) := by
      rw [hneg, hG, hu]
      ring
    rw [e]
    refine (ENNReal.ofReal_le_ofReal (abs_sub _ _)).trans ?_
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact (add_le_add h₁ h₂).trans_eq (by ring)
  -- the bound almost everywhere on `p > 0`
  set bnd : ℝ → ℝ≥0∞ := fun p ↦ 4 * Cy' * shearCost B A p +
    4 * Cy' * (Ioc 0 9).indicator (shearLowCost B A) p +
    Cx' * (Ioi 9).indicator (fun p ↦ ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |M p|)) p +
    2 * Cy' * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
      ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ with hbnd
  have hae_bnd (ε : ℝ) : ∀ᵐ p ∂(volume.restrict (Ioi 0)),
      ‖(Jc ε).indicator f p + (Jc ε).indicator f (-p) -
        (Ioc 0 9).indicator ((Jc ε).indicator G) p‖ₑ ≤ bnd p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (Measure.ae_ne volume 1)] with p (hp : 0 < p) hp1
    have hJneg : -p ∈ Jc ε ↔ p ∈ Jc ε := by
      simp only [hJc, mem_ofPred_eq, show -p - 1 = -(p + 1) by ring, neg_add_eq_sub, abs_neg,
        abs_sub_comm 1 p, and_comm]
    by_cases hJ : p ∈ Jc ε
    · rw [indicator_of_mem hJ, indicator_of_mem (hJneg.2 hJ), Real.enorm_eq_ofReal_abs]
      by_cases hpB : p ≤ B + 1
      · by_cases hp9 : p ≤ 9
        · rw [indicator_of_mem (show p ∈ Ioc 0 9 from ⟨hp, hp9⟩), indicator_of_mem hJ]
          refine (hcolin p hp hp1 hpB).trans ?_
          simp only [hbnd, indicator_of_mem (show p ∈ Ioc 0 9 from ⟨hp, hp9⟩),
            indicator_of_notMem (show p ∉ Ioi 9 from not_lt.2 hp9), mul_zero, add_zero, le_refl]
        · rw [indicator_of_notMem (show p ∉ Ioc 0 9 from fun h ↦ hp9 h.2), sub_zero]
          refine (hcolout p hp hp1 hpB).trans ?_
          simp only [hbnd, indicator_of_notMem (show p ∉ Ioc 0 9 from fun h ↦ hp9 h.2),
            indicator_of_mem (show p ∈ Ioi 9 from lt_of_not_ge hp9), mul_zero, add_zero, le_refl]
      · have hpB' : B + 1 < p := not_le.1 hpB
        have hG0 : (Ioc 0 9).indicator ((Jc ε).indicator G) p = 0 :=
          indicator_apply_eq_zero.2 fun _ ↦ indicator_apply_eq_zero.2 fun _ ↦ by
            simp only [hG, hM, shearMass_of_lt (show B + 1 < |p| by rwa [abs_of_pos hp]), zero_mul]
        simp only [hf, hG0, localShearDifference_neg_left, localShearDifference_of_gt hpB',
          neg_zero, zero_mul, integral_zero, add_zero, sub_zero, abs_zero, ENNReal.ofReal_zero,
          zero_le]
    · have hG0 : (Ioc 0 9).indicator ((Jc ε).indicator G) p = 0 :=
        indicator_apply_eq_zero.2 fun _ ↦ indicator_of_notMem hJ _
      simp only [indicator_of_notMem hJ, indicator_of_notMem (mt hJneg.1 hJ), hG0, add_zero,
        sub_zero, enorm_zero, zero_le]
  -- integrating the bound
  have hlint : ∫⁻ p in Ioi 0, bnd p = Cx' * shearInnerMassCost B A +
      Cy' * (shearUpperCost B A + shearLowerCost B A + shearOuterCost B h) := by
    have hm₁ : Measurable fun p : ℝ ↦ ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |M p|) :=
      (((measurable_id.const_mul 2).pow_const _).mul
        (continuous_abs.measurable.comp (measurable_shearMass B A))).ennreal_ofReal
    simp only [hbnd]
    rw [lintegral_add_right _ ((measurable_lintegral_localShearDifference B h).const_mul _),
      lintegral_add_right _ ((hm₁.indicator measurableSet_Ioi).const_mul _),
      lintegral_add_right _
        (((measurable_shearLowCost B A).indicator measurableSet_Ioc).const_mul _),
      lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by finiteness),
      lintegral_const_mul' _ _ (by finiteness), lintegral_const_mul' _ _ (by finiteness),
      setLIntegral_indicator measurableSet_Ioi, setLIntegral_indicator measurableSet_Ioc,
      show Ioi (9 : ℝ) ∩ Ioi 0 = Ioi 9 from Ioi_inter_Ioi.trans (by norm_num),
      show Ioc (0 : ℝ) 9 ∩ Ioi 0 = Ioc 0 9 from inter_eq_left.2 Ioc_subset_Ioi_self]
    simp only [shearInnerMassCost, shearUpperCost, shearLowerCost, shearOuterCost, hM]
    ring
  set Bd := Cx' * shearInnerMassCost B A +
    Cy' * (shearUpperCost B A + shearLowerCost B A + shearOuterCost B h) with hBd
  -- the line integral and its integrability
  have hline : ∀ p ∈ Icc (-(B + 1)) (B + 1), ∀ q ∈ Icc (-(B + 1)) (B + 1),
      |u p - u q| ≤ Cx' * |p - q| ^ (1 / 2 : ℝ) := by
    have hside (r : ℝ) (hr : r ∈ Icc (-(B + 1)) (B + 1)) : |r - 1| ≤ B ∨ |r + 1| ≤ B :=
      (le_or_gt 0 r).imp (fun _ ↦ abs_le.2 ⟨by linarith, by linarith [hr.2]⟩)
        fun _ ↦ abs_le.2 ⟨by linarith [hr.1], by linarith⟩
    exact fun p hp q hq ↦ abs_column_sub_le hc hx0 hz0 hxz hCx (τ := 0) (hside p hp) (hside q hq)
      (abs_zero.trans_le (by linarith : (0 : ℝ) ≤ B))
  have hGi : IntegrableOn G (Ioc 0 9) := by
    have huc : ContinuousOn u (Icc (-(B + 1)) (B + 1)) := by
      refine HolderOnWith.continuousOn (C := Cx') (r := 1 / 2) (fun p hp q hq ↦ ?_) (by norm_num)
      rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num),
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul Cx'.coe_nonneg]
      exact ENNReal.ofReal_le_ofReal (by simpa [Real.dist_eq] using hline p hp q hq)
    exact integrableOn_shearMass_mul (lt_min hh0 (by linarith))
      (huc.sub (huc.comp continuous_neg.continuousOn fun p hp ↦
        ⟨by linarith [hp.2], by linarith [hp.1]⟩)) (by simp)
  have hJm (ε : ℝ) : MeasurableSet (Jc ε) :=
    (measurableSet_le measurable_const (continuous_abs.measurable.comp
      (measurable_id.sub_const 1))).inter (measurableSet_le measurable_const
        (continuous_abs.measurable.comp (measurable_id.add_const 1)))
  set R : ℝ → ℝ := fun ε ↦ ∫ p in Ioc 0 9, (Jc ε).indicator G p with hR
  have hRlim : Tendsto R (𝓝[>] 0) (𝓝 (∫ p in Ioc 0 9, G p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p ↦ ‖G p‖)
      (Eventually.of_forall fun ε ↦ hGi.aestronglyMeasurable.indicator (hJm ε))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun p ↦ norm_indicator_le_norm_self _ p)
      hGi.norm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume 1)] with p hp hp1
    have hlim : Tendsto (fun ε : ℝ ↦ ε / c) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_id.div_const c).tendsto 0).mono_left nhdsWithin_le_nhds
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hlim.eventually (eventually_lt_nhds (lt_min (abs_pos.2 (sub_ne_zero.2 hp1))
      (abs_pos.2 (by linarith [hp.1] : (0 : ℝ) < p + 1).ne')))] with ε hε
    rw [indicator_of_mem (show p ∈ Jc ε from ⟨(hε.trans_le (min_le_left _ _)).le,
      (hε.trans_le (min_le_right _ _)).le⟩)]
  -- the limit
  have hLbd : ENNReal.ofReal |L - ∫ p in Ioc 0 9, G p| ≤ Bd := by
    refine le_of_tendsto ((ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_abs.tendsto _).comp (hlim.sub hRlim))) ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds hc)] with ε (hε : 0 < ε) hεc
    have hΦi := hrep ε hε hεc
    have e₁ : E ε = ∫ p in Ioi 0, ((Jc ε).indicator f p + (Jc ε).indicator f (-p)) :=
      PDE.Analysis.integral_eq_integral_Ioi_add_reflection hΦi
    have e₂ : R ε = ∫ p in Ioi 0, (Ioc 0 9).indicator ((Jc ε).indicator G) p := by
      rw [setIntegral_indicator measurableSet_Ioc,
        show Ioi (0 : ℝ) ∩ Ioc 0 9 = Ioc 0 9 from inter_eq_right.2 Ioc_subset_Ioi_self]
    have h₁ : IntegrableOn (fun p ↦ (Jc ε).indicator f p + (Jc ε).indicator f (-p)) (Ioi 0) :=
      (hΦi.add hΦi.comp_neg).integrableOn
    change ENNReal.ofReal |E ε - R ε| ≤ Bd
    rw [e₁, e₂, ← integral_sub h₁
      ((integrable_indicator_iff measurableSet_Ioc).2 (hGi.indicator (hJm ε))).integrableOn,
      ← Real.enorm_eq_ofReal_abs, ← hlint]
    exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae (hae_bnd ε))
  -- the line term
  have hI0 : ENNReal.ofReal |(∫ p in Ioc 0 9, G p) + Real.pi * (u 1 - u (-1))| ≤
      Cx' * shearLineCost B A := by
    simpa only [hG, hM] using abs_integral_shearMass_mul_add_le hB4 (lt_min hh0 (by linarith)) hline
  have hux : u 1 = W x := by
    simp only [hu, hw, mul_one, mul_zero, sub_zero, ← hx0]
    congr 1
    ext i
    fin_cases i <;> simp
  have huz : u (-1) = W z := by
    simp only [hu, hw, mul_neg, mul_one, mul_zero, sub_zero, ← sub_eq_add_neg, ← hz0, hxz]
    congr 1
    ext i
    fin_cases i <;> simp
  have hsplit : (vz - Real.pi / 2 * W z) - (vx - Real.pi / 2 * W x) =
      (L - ∫ p in Ioc 0 9, G p) + ((∫ p in Ioc 0 9, G p) + Real.pi * (u 1 - u (-1))) := by
    rw [hux, huz, hL]
    ring
  -- dividing by `π |x - z|^{1/2}`
  rw [abs_sub_comm, hsplit]
  refine ofReal_shear_quotient_le hc
    (((ofReal_abs_add_le _ _).trans (add_le_add hLbd hI0)).trans_eq ?_)
  rw [hBd, hCx', hCy', ENNReal.coe_mul, ENNReal.coe_mul, ← ENNReal.ofReal]
  ring

/-- The constant `C₂(τ)` of Chen and Hou, Part I, Lemma 3.4 (the estimate of `u_y`):
`sup_{h > 0, B ≥ 4} (S̃_{1D}(B, A) + τ (S_up(B, A) + S_out(B, h))) / √2`, `A = min(h, B)`. -/
def shearConstant (τ : ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : 0 < h) (B : ℝ) (_ : 4 ≤ B),
    (shearMassCost B (min h B) + ENNReal.ofReal τ *
      (shearUpperCost B (min h B) + shearOuterCost B h)) / ENNReal.ofReal (Real.sqrt 2)

/-- The constant `C₁(τ)` of Chen and Hou, Part I, Lemma 3.4 (the estimate of `v_x`):
`sup_{h > 0, B ≥ 4} (S_{in,x}(B, A) + S_{1D}(B, A) + τ (S_up(B, A) + S_low(B, A) +
S_out(B, h))) / √2`, `A = min(h, B)`. -/
def shearResidualConstant (τ : ℝ) : ℝ≥0∞ :=
  ⨆ (h : ℝ) (_ : 0 < h) (B : ℝ) (_ : 4 ≤ B),
    (shearInnerMassCost B (min h B) + shearLineCost B (min h B) + ENNReal.ofReal τ *
      (shearUpperCost B (min h B) + shearLowerCost B (min h B) + shearOuterCost B h)) /
      ENNReal.ofReal (Real.sqrt 2)

/-- The anisotropic form of the bounds of `abs_sub_div_le_shear` and
`abs_sub_div_le_shear_residual`: for `τ > 0`, if `(X + τ Y)/√2 ≤ K`, then
`(C_x X + C_y Y) / (π √2) ≤ (K/π) max(C_x, τ⁻¹ C_y)`. -/
theorem div_le_div_mul_max {τ : ℝ} (hτ : 0 < τ) {Cx Cy X Y K : ℝ≥0∞}
    (hK : (X + ENNReal.ofReal τ * Y) / ENNReal.ofReal (Real.sqrt 2) ≤ K) :
    (Cx * X + Cy * Y) / ENNReal.ofReal (Real.pi * Real.sqrt 2) ≤
      K / ENNReal.ofReal Real.pi * max Cx (ENNReal.ofReal (1 / τ) * Cy) := by
  set M := max Cx (ENNReal.ofReal (1 / τ) * Cy)
  have hCy : Cy ≤ ENNReal.ofReal τ * M := by
    calc Cy = ENNReal.ofReal τ * (ENNReal.ofReal (1 / τ) * Cy) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hτ.le, mul_one_div_cancel hτ.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal τ * M := by gcongr; exact le_max_right _ _
  have hπ : ENNReal.ofReal (Real.pi * Real.sqrt 2) =
      ENNReal.ofReal Real.pi * ENNReal.ofReal (Real.sqrt 2) :=
    ENNReal.ofReal_mul Real.pi_pos.le
  calc (Cx * X + Cy * Y) / ENNReal.ofReal (Real.pi * Real.sqrt 2)
      ≤ M * (X + ENNReal.ofReal τ * Y) / ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
        gcongr
        calc Cx * X + Cy * Y ≤ M * X + ENNReal.ofReal τ * M * Y := by
              gcongr
              exact le_max_left _ _
          _ = M * (X + ENNReal.ofReal τ * Y) := by ring
    _ = (X + ENNReal.ofReal τ * Y) / ENNReal.ofReal (Real.sqrt 2) / ENNReal.ofReal Real.pi *
          M := by
        rw [hπ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 Real.pi_pos).ne')
            (Or.inl ENNReal.ofReal_ne_top)]
        ring
    _ ≤ K / ENNReal.ofReal Real.pi * M := by gcongr

/-- The integrals of `abs_sub_div_le_shear` are bounded by `C₂(τ)`. -/
theorem le_shearConstant {τ h B : ℝ} (hh : 0 < h) (hB : 4 ≤ B) :
    (shearMassCost B (min h B) + ENNReal.ofReal τ *
      (shearUpperCost B (min h B) + shearOuterCost B h)) / ENNReal.ofReal (Real.sqrt 2) ≤
      shearConstant τ :=
  le_iSup₂_of_le h hh (le_iSup₂_of_le B hB le_rfl)

/-- The integrals of `abs_sub_div_le_shear_residual` are bounded by `C₁(τ)`. -/
theorem le_shearResidualConstant {τ h B : ℝ} (hh : 0 < h) (hB : 4 ≤ B) :
    (shearInnerMassCost B (min h B) + shearLineCost B (min h B) + ENNReal.ofReal τ *
      (shearUpperCost B (min h B) + shearLowerCost B (min h B) + shearOuterCost B h)) /
      ENNReal.ofReal (Real.sqrt 2) ≤ shearResidualConstant τ :=
  le_iSup₂_of_le h hh (le_iSup₂_of_le B hB le_rfl)

end IncompressibleFlow.SharpHolder
