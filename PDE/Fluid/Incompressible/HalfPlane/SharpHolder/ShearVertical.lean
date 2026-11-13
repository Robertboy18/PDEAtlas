/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearHolder
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowTransport
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearColumnTransport
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMixedPrincipalValue

/-!
# The vertical Hölder estimate of the unlocalized `u_y` and `v_x`

Chen and Hou, Part I, Lemma 3.5: for two points `x = (x₁, x₂)`, `z = (x₁, z₂)` of the open upper
half-plane on a vertical line and the odd extension `W` of a vorticity decaying at infinity, the
unlocalized `u_y` and `v_x` satisfy, for every `τ > 0`,

`|f(x) - f(z)| / |x - z|^{1/2} ≤ (C₃(τ)/π) max([ω]_{C_x^{1/2}}, τ⁻¹ [ω]_{C_y^{1/2}})`,

`C₃(τ) = (C_{mid,2} + τ (C_in + (π/2) √2)) / √2` with the integrals of Part I, Appendix B.2,
taken with `δ = 0`:

* `C_in = 4 ∫_0^{y_c} ∫_0^{h_c^-(q)} |Δ| |p - T_y(p, q)|^{1/2} + 2 ∫_{R_in^{++}} |Δ| (2p)^{1/2}`
  (`shearVerticalInnerCost`, the horizontal transport of the rows `|p| ≤ 1`, (B.50));
* `C_{mid,2} = 4 ∫_1^∞ ∫_{s_c(p)}^∞ |Δ| |q - T(p, q)|^{1/2}` (`shearVerticalOuterCost 1`, the
  vertical transport of the columns `|p| > 1`, (B.56)).

After rotating and rescaling, `y = (x₁ + c q, M - c p)`, `c = |x₂ - z₂|/2`, `M = (x₂ + z₂)/2`, the
two points are `(± 1, 0)` and the kernel difference is `Δ(p, q) = K₂(p + 1, q) - K₂(p - 1, q)`.
The disc principal values at the two points are the limits of the mixed truncations
(`tendsto_setIntegral_pairTruncation`): vertical strips on the rows `|p| ≤ 1` and horizontal strips
on the columns `|p| ≥ 1`, with no local term. The rows are estimated by horizontal transport
(`abs_integral_shearDifference_mul_le_row`, Hölder constant `[ω]_{C_y}`), the columns by vertical
transport (`abs_integral_shearDifference_mul_le_column`, `[ω]_{C_x}`); the local terms `± ω/2` of
`u_y`, `v_x` contribute `(π/2) √2 [ω]_{C_y}`.

The mixed-truncation estimate gives the constant `C₃(τ)/π` for both components. The estimate of
`u_y` with the vertical strips removed everywhere, so that the rows reach the boundary (Part I,
Appendix B.2), uses `m = (x₂ + z₂)/|x₂ - z₂|`: the rows `|p| ≤ m` give `C_in + C_{mid,1}(m)` and
the columns `|p| > m` give `C_out(m)` (`abs_sub_div_le_shear_vertical_mid`), and
`C₄(τ) = sup_{m > 1} (C_out(m) + τ (C_in + C_{mid,1}(m))) / √2` (`shearVerticalConstant`).

## Main results

* `abs_sub_le_shearVertical`: the difference of the disc principal values.
* `abs_sub_div_le_shear_vertical`: Part I, Lemma 3.5, for `u_y` (`s = 1`) and `v_x` (`s = -1`)
  with `C₃(τ)` (`shearVerticalResidualConstant`).
* `abs_sub_div_le_shear_vertical_mid`: Part I, Lemma 3.5, for `u_y` with the middle region, and
  the constant `C₄(τ)` (`shearVerticalConstant`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.5, p. 29, and Appendix B.2,
  pp. 136-141.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric PDE.Common
open scoped ENNReal NNReal Topology
open PDE.Analysis (planeEquivSwap planeEquivSwap_apply measurePreserving_planeEquivSwap)

namespace IncompressibleFlow.SharpHolder

variable {K : ℝ^2 → ℝ}

/-- **Rescaled Fubini over horizontal lines.** For an integrable `F` on the plane and `c > 0`,
`∫ F = c² ∫_p ∫_q F(m + c q, e - c p) dq dp`, and the inner integral is integrable in `p`. -/
theorem integral_eq_mul_integral_integral_height {F : ℝ^2 → ℝ} (hF : Integrable F) {c : ℝ}
    (hc : 0 < c) (m e : ℝ) :
    Integrable (fun p ↦ ∫ q, F !₂[m + c * q, e - c * p]) ∧
      ∫ y, F y = c ^ 2 * ∫ p, ∫ q, F !₂[m + c * q, e - c * p] := by
  have hmp := measurePreserving_planeEquivSwap
  have hG : Integrable (fun v : ℝ × ℝ ↦ F !₂[v.2, v.1]) (volume.prod volume) := by
    have := (hmp.integrable_comp_emb planeEquivSwap.measurableEmbedding).2 hF
    rw [← Measure.volume_eq_prod]
    simpa only [Function.comp_def, planeEquivSwap_apply] using this
  set Φ : ℝ → ℝ := fun t ↦ ∫ s, F !₂[s, t] with hΦ
  have hΦi : Integrable Φ := hG.integral_prod_left
  have hinner : ∀ t, ∫ q, F !₂[m + c * q, t] = c⁻¹ * Φ t := fun t ↦ by
    have h1 := Measure.integral_comp_mul_left (fun q ↦ F !₂[m + q, t]) c
    have h2 : ∫ q, F !₂[m + q, t] = Φ t := integral_add_left_eq_self (fun s ↦ F !₂[s, t]) m
    rw [h2, abs_inv, abs_of_pos hc, smul_eq_mul] at h1
    exact h1
  have hint : (fun p ↦ ∫ q, F !₂[m + c * q, e - c * p]) = fun p ↦ c⁻¹ * Φ (e - c * p) := by
    ext p
    exact hinner _
  refine ⟨?_, ?_⟩
  · rw [hint]
    exact ((hΦi.comp_sub_left e).comp_mul_left' hc.ne').const_mul _
  · rw [hint, integral_const_mul]
    have h3 := Measure.integral_comp_mul_left (fun p ↦ Φ (e - p)) c
    rw [abs_inv, abs_of_pos hc, smul_eq_mul,
      integral_sub_left_eq_self Φ (μ := volume) e] at h3
    rw [h3]
    have h4 : ∫ y, F y = ∫ t, Φ t := by
      rw [← hmp.integral_comp' F, Measure.volume_eq_prod,
        integral_prod _ (by
          rw [← Measure.volume_eq_prod]
          simpa only [Function.comp_def, planeEquivSwap_apply] using
            (hmp.integrable_comp_emb planeEquivSwap.measurableEmbedding).2 hF)]
      simp only [planeEquivSwap_apply, Φ]
    rw [h4]
    field_simp

/-- The kernel difference at the rescaled point `(x₁ + c q, M - c p)` of two points `x`, `z` on a
vertical line, `x₂ = M - c`, `z₂ = M + c`: `K₂(x - y) - K₂(z - y) = Δ(p, q) / c²`. -/
theorem shearKernel_sub_sub_mk (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {x z : ℝ^2} {M c : ℝ} (hc : c ≠ 0) (hxz : x 0 = z 0) (hx : x 1 = M - c) (hz : z 1 = M + c)
    (p q : ℝ) :
    K (x - !₂[x 0 + c * q, M - c * p]) - K (z - !₂[x 0 + c * q, M - c * p]) =
      shearDifference p q / c ^ 2 := by
  have e : ∀ (w : ℝ^2) (s : ℝ), w 0 = x 0 → w 1 = M + c * s →
      K (w - !₂[x 0 + c * q, M - c * p]) = -(shearDensity (p + s) q / c ^ 2) := by
    intro w s h0 h1
    rw [shearKernel_apply hK]
    have a0 : (w - !₂[x 0 + c * q, M - c * p]) 0 = c * -q := by simp [h0]
    have a1 : (w - !₂[x 0 + c * q, M - c * p]) 1 = c * (p + s) := by simp [h1]; ring
    rw [a0, a1, shearDensity_mul hc, shearDensity_neg_left, shearDensity_comm]
    ring
  rw [e x (-1) rfl (by rw [hx]; ring), e z 1 hxz.symm (by rw [hz]; ring), shearDifference,
    show p + -1 = p - 1 by ring]
  ring

/-- A `1/2`-Hölder function composed with `q ↦ m + c q`, `c > 0`, is `1/2`-Hölder with constant
`C c^{1/2}`. -/
theorem holderOnWith_comp_add_mul {f : ℝ → ℝ} {C : ℝ≥0} {S : Set ℝ}
    (hf : HolderOnWith C (1 / 2) f S) {c : ℝ} (hc : 0 < c) (m : ℝ) {T : Set ℝ}
    (hT : ∀ q ∈ T, m + c * q ∈ S) :
    HolderOnWith (C * (c ^ (1 / 2 : ℝ)).toNNReal) (1 / 2) (fun q ↦ f (m + c * q)) T := by
  have h := holderOnWith_comp_sub_mul hf hc m (T := Neg.neg ⁻¹' T) (fun τ hτ ↦ by
    simpa [sub_eq_add_neg, mul_neg] using hT (-τ) hτ)
  intro q hq q' hq'
  have := h (-q) (by simpa using hq) (-q') (by simpa using hq')
  simpa [mul_neg, sub_neg_eq_add, edist_neg_neg] using this

/-- In the middle region of width zero (`m = 1`) nothing is transported and nothing is left. -/
theorem shearMidRowCost_one {q : ℝ} (hq : 0 ≤ q) : shearMidRowCost 1 q = 0 := by
  have h1 := one_le_upperShearThreshold hq
  have hedge : shearMidEdge 1 q = 1 := by
    simp only [shearMidEdge, ite_eq_right_iff]
    exact fun h ↦ absurd h (not_lt.2 h1)
  simp [shearMidRowCost, hedge, Ioo_eq_empty (not_lt.2 h1)]

/-! ### Measurability of the costs -/

/-- `Δ` is jointly measurable. -/
theorem measurable_shearDifference : Measurable fun x : ℝ × ℝ ↦ shearDifference x.1 x.2 := by
  have e : (fun x : ℝ × ℝ ↦ shearDifference x.1 x.2) = fun x ↦
      ((x.1 + 1) ^ 2 - x.2 ^ 2) / (2 * ((x.1 + 1) ^ 2 + x.2 ^ 2) ^ 2) -
        ((x.1 - 1) ^ 2 - x.2 ^ 2) / (2 * ((x.1 - 1) ^ 2 + x.2 ^ 2) ^ 2) := by
    ext x
    simp only [shearDifference, shearDensity_eq]
  rw [e]
  fun_prop

/-- A lintegral over an interval with measurable ends depends measurably on the parameter. -/
theorem measurable_setLIntegral_Ioo {a b : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    {F : ℝ → ℝ → ℝ≥0∞} (hF : Measurable fun x : ℝ × ℝ ↦ F x.1 x.2) :
    Measurable fun q ↦ ∫⁻ p in Ioo (a q) (b q), F p q := by
  have e : (fun q ↦ ∫⁻ p in Ioo (a q) (b q), F p q) = fun q ↦ ∫⁻ p,
      {x : ℝ × ℝ | a x.1 < x.2 ∧ x.2 < b x.1}.indicator (fun x ↦ F x.2 x.1) (q, p) := by
    ext q
    rw [← lintegral_indicator measurableSet_Ioo]
    rfl
  rw [e]
  refine Measurable.lintegral_prod_right' (Measurable.indicator ?_ ?_)
  · exact hF.comp (measurable_snd.prodMk measurable_fst)
  · exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hb.comp measurable_fst))

/-- The row map is jointly measurable. -/
theorem measurable_horizontalShearMap :
    Measurable fun x : ℝ × ℝ ↦ horizontalShearMap x.1 x.2 := by
  have hn : Measurable fun x : ℝ × ℝ ↦
      x.1 ^ 2 + 2 * x.2 ^ 2 + x.1 ^ 2 * x.2 ^ 2 + 3 * x.2 ^ 4 - 1 := by fun_prop
  have hd : Measurable fun x : ℝ × ℝ ↦ x.1 ^ 2 - x.2 ^ 2 - 1 := by fun_prop
  exact (hn.div hd).sqrt

/-- The inner row cost is measurable in the row. -/
theorem measurable_shearInnerRowCost : Measurable shearInnerRowCost := by
  have hF : Measurable fun x : ℝ × ℝ ↦ ‖shearDifference x.1 x.2‖ₑ *
      ENNReal.ofReal (|x.1 - horizontalShearMap x.1 x.2| ^ (1 / 2 : ℝ)) :=
    measurable_shearDifference.enorm.mul
      ((continuous_abs.measurable.comp (measurable_fst.sub measurable_horizontalShearMap)).pow_const
        _).ennreal_ofReal
  have hG : Measurable fun x : ℝ × ℝ ↦ ‖shearDifference x.1 x.2‖ₑ *
      ENNReal.ofReal ((2 * x.1) ^ (1 / 2 : ℝ)) :=
    measurable_shearDifference.enorm.mul
      ((measurable_fst.const_mul 2).pow_const _).ennreal_ofReal
  have hl : Measurable lowerShearThreshold := by
    have : Measurable fun q : ℝ ↦ q ^ 2 + 1 - 2 * q * Real.sqrt (q ^ 2 + 1) := by fun_prop
    exact this.sqrt
  have hT : Measurable fun q ↦ horizontalShearMap 0 q := by
    simp only [horizontalShearMap_zero_left]
    exact (by fun_prop : Measurable fun q : ℝ ↦ 1 - 3 * q ^ 2).sqrt
  unfold shearInnerRowCost
  exact ((measurable_setLIntegral_Ioo measurable_const hl hF).const_mul 2).add
    (measurable_setLIntegral_Ioo hT measurable_const hG)

/-- The constant `C_in` of Chen and Hou, Part I, (B.50): `C_in = 2 ∫_0^∞ shearInnerRowCost q dq`,
that is
`4 ∫_0^{y_c} ∫_0^{h_c^-(q)} |Δ| |p - T_y(p, q)|^{1/2} dp dq + 2 ∫_{R_in^{++}} |Δ| (2p)^{1/2}`. -/
def shearVerticalInnerCost : ℝ≥0∞ :=
  2 * ∫⁻ q in Ioi 0, shearInnerRowCost q

/-- The constant `C_out(m)` of Chen and Hou, Part I, (B.59), with `δ = 0`:
`4 ∫_m^∞ ∫_{s_c(p)}^∞ |Δ(p, q)| |q - T(p, q)|^{1/2} dq dp`; `C_{mid,2}` of (B.56) is
`shearVerticalOuterCost 1`. -/
def shearVerticalOuterCost (m : ℝ) : ℝ≥0∞ :=
  4 * ∫⁻ p in Ioi m, shearColumnCost p

/-- The constant `C₃(τ)` of Chen and Hou, Part I, Lemma 3.5:
`(C_{mid,2} + τ (C_in + (π/2) √2)) / √2`. The factor `τ` enters as `ENNReal.ofReal τ`, so the
formula is the real one for `τ ≥ 0`. -/
def shearVerticalResidualConstant (τ : ℝ) : ℝ≥0∞ :=
  (shearVerticalOuterCost 1 + ENNReal.ofReal τ *
    (shearVerticalInnerCost + ENNReal.ofReal (Real.pi / 2 * Real.sqrt 2))) /
    ENNReal.ofReal (Real.sqrt 2)

/-- The constant `C_{mid,1}(m)` of Chen and Hou, Part I, (B.53):
`C_{mid,1}(m) = 2 ∫_0^∞ shearMidRowCost m q dq`, that is
`4 ∫_0^{s_c(m)} ∫_{h_c^+(q)}^{m} |Δ| |p - T_y(p, q)|^{1/2} dp dq +
2 ∫_{R_mid^{++}} |Δ| (2p)^{1/2}`. -/
def shearVerticalMidCost (m : ℝ) : ℝ≥0∞ :=
  2 * ∫⁻ q in Ioi 0, shearMidRowCost m q

/-- The constant `C₄(τ)` of Chen and Hou, Part I, Lemma 3.5 (the estimate of `u_y`):
`sup_{m > 1} (C_out(m) + τ (C_in + C_{mid,1}(m))) / √2`. The factor `τ` enters as
`ENNReal.ofReal τ`, so the formula is the real one for `τ ≥ 0`. -/
def shearVerticalConstant (τ : ℝ) : ℝ≥0∞ :=
  ⨆ (m : ℝ) (_ : 1 < m), (shearVerticalOuterCost m + ENNReal.ofReal τ *
    (shearVerticalInnerCost + shearVerticalMidCost m)) / ENNReal.ofReal (Real.sqrt 2)

/-- The middle region of width zero contributes nothing: `C_{mid,1}(1) = 0`. -/
theorem shearVerticalMidCost_one : shearVerticalMidCost 1 = 0 := by
  rw [shearVerticalMidCost, setLIntegral_congr_fun measurableSet_Ioi
    (fun q (hq : 0 < q) ↦ shearMidRowCost_one hq.le)]
  simp

/-- A lintegral over the line is the lintegral over `(0, ∞)` of the even fold. -/
theorem lintegral_eq_setLIntegral_Ioi_add_neg (f : ℝ → ℝ≥0∞) :
    ∫⁻ x, f x = (∫⁻ x in Ioi 0, f x) + ∫⁻ x in Ioi 0, f (-x) := by
  rw [← lintegral_add_compl f measurableSet_Ioi, compl_Ioi]
  congr 1
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  rw [← hmp.setLIntegral_comp_preimage_emb (Homeomorph.neg ℝ).measurableEmbedding,
    Set.neg_preimage, neg_Iic, neg_zero]
  exact setLIntegral_congr (Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm

/-- **The rows.** For `m ≥ 1`, if every row `p ↦ w(p, q)` is `1/2`-Hölder with constant `C` on
`[-m, m]`, the integral over any set of rows of `∫_{-m}^{m} Δ(p, q) w(p, q) dp` is at most
`C (C_in + C_{mid,1}(m))`. -/
theorem ofReal_abs_integral_rows_le {m : ℝ} (hm : 1 ≤ m) {w : ℝ → ℝ → ℝ} {C : ℝ≥0}
    (hw : ∀ q, HolderOnWith C (1 / 2) (fun p ↦ w p q) (Icc (-m) m)) (S : Set ℝ) :
    ENNReal.ofReal |∫ q, S.indicator (fun q ↦ ∫ p in Icc (-m) m,
      shearDifference p q * w p q) q| ≤
      C * (shearVerticalInnerCost + shearVerticalMidCost m) := by
  set r : ℝ → ℝ := fun q ↦ ∫ p in Icc (-m) m, shearDifference p q * w p q with hr
  set g : ℝ → ℝ≥0∞ := fun q ↦ C * (shearInnerRowCost q + shearMidRowCost m q) with hg
  have hrow : ∀ q, 0 < q → ‖S.indicator r q‖ₑ ≤ g q := fun q hq ↦ by
    refine (enorm_indicator_le_enorm_self _ _).trans ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact abs_integral_shearDifference_mul_le_row hm hq (hw q)
  have hrow' : ∀ q, 0 < q → ‖S.indicator r (-q)‖ₑ ≤ g q := fun q hq ↦ by
    refine (enorm_indicator_le_enorm_self _ _).trans ?_
    rw [Real.enorm_eq_ofReal_abs]
    have := abs_integral_shearDifference_mul_le_row hm hq (hw (-q))
    simpa only [hr, shearDifference_neg_right] using this
  have hmeas : Measurable fun q ↦ shearInnerRowCost q := measurable_shearInnerRowCost
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [lintegral_eq_setLIntegral_Ioi_add_neg]
  calc (∫⁻ q in Ioi 0, ‖S.indicator r q‖ₑ) + ∫⁻ q in Ioi 0, ‖S.indicator r (-q)‖ₑ
      ≤ (∫⁻ q in Ioi 0, g q) + ∫⁻ q in Ioi 0, g q :=
        add_le_add (setLIntegral_mono' measurableSet_Ioi hrow)
          (setLIntegral_mono' measurableSet_Ioi hrow')
    _ = C * (shearVerticalInnerCost + shearVerticalMidCost m) := by
        rw [hg, lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_add_left' hmeas.aemeasurable,
          shearVerticalInnerCost, shearVerticalMidCost]
        ring

/-- **The columns.** For `m ≥ 1`, if every column `q ↦ w(p, q)` is `1/2`-Hölder with constant `C`
on the line, the integral over any set of columns `|p| > m` of `∫ Δ(p, q) w(p, q) dq` is at most
`C C_out(m)`. -/
theorem ofReal_abs_integral_columns_le {m : ℝ} (hm : 1 ≤ m) {w : ℝ → ℝ → ℝ} {C : ℝ≥0}
    (hw : ∀ p, HolderOnWith C (1 / 2) (w p) univ) {S : Set ℝ} (hS : ∀ p ∈ S, m < |p|) :
    ENNReal.ofReal |∫ p, S.indicator (fun p ↦ ∫ q, shearDifference p q * w p q) p| ≤
      C * shearVerticalOuterCost m := by
  set k : ℝ → ℝ := fun p ↦ ∫ q, shearDifference p q * w p q with hk
  set g : ℝ → ℝ≥0∞ := (Ioi m).indicator fun p ↦ 2 * C * shearColumnCost p with hg
  have hcol : ∀ p, 0 < p → ‖S.indicator k p‖ₑ ≤ g p := fun p hp ↦ by
    by_cases hpS : p ∈ S
    · have h1 : m < p := by simpa [abs_of_pos hp] using hS p hpS
      rw [indicator_of_mem hpS, hg, indicator_of_mem (show p ∈ Ioi m from h1),
        Real.enorm_eq_ofReal_abs]
      exact abs_integral_shearDifference_mul_le_column (hm.trans_lt h1) (hw p)
    · rw [indicator_of_notMem hpS, enorm_zero]
      exact zero_le
  have hcol' : ∀ p, 0 < p → ‖S.indicator k (-p)‖ₑ ≤ g p := fun p hp ↦ by
    by_cases hpS : -p ∈ S
    · have h1 : m < p := by simpa [abs_of_pos hp] using hS (-p) hpS
      rw [indicator_of_mem hpS, hg, indicator_of_mem (show p ∈ Ioi m from h1),
        Real.enorm_eq_ofReal_abs]
      have := abs_integral_shearDifference_mul_le_column (hm.trans_lt h1) (hw (-p))
      have e : k (-p) = -∫ q, shearDifference p q * w (-p) q := by
        rw [hk, ← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun q ↦ ?_)
        simp only [shearDifference_neg_left]
        ring
      rwa [e, abs_neg]
    · rw [indicator_of_notMem hpS, enorm_zero]
      exact zero_le
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [lintegral_eq_setLIntegral_Ioi_add_neg]
  have hgI : ∫⁻ p in Ioi 0, g p = 2 * C * ∫⁻ p in Ioi m, shearColumnCost p := by
    rw [hg, setLIntegral_indicator measurableSet_Ioi,
      show Ioi m ∩ Ioi 0 = Ioi m from inter_eq_left.2 (Ioi_subset_Ioi (by linarith)),
      lintegral_const_mul' _ _ (by finiteness)]
  calc (∫⁻ p in Ioi 0, ‖S.indicator k p‖ₑ) + ∫⁻ p in Ioi 0, ‖S.indicator k (-p)‖ₑ
      ≤ (∫⁻ p in Ioi 0, g p) + ∫⁻ p in Ioi 0, g p :=
        add_le_add (setLIntegral_mono' measurableSet_Ioi hcol)
          (setLIntegral_mono' measurableSet_Ioi hcol')
    _ = C * shearVerticalOuterCost m := by
        rw [hgI, shearVerticalOuterCost]
        ring

/-- **Rows in rescaled coordinates.** For `c > 0` and `F` integrable on the strip
`R = {M - c a ≤ y₂ ≤ M + c a, |y₁ - x₁| ≥ ε}`,
`∫_R F = c² ∫_{c |q| ≥ ε} ∫_{-a}^{a} F(x₁ + c q, M - c p) dp dq`. -/
theorem setIntegral_rows_eq {F : ℝ^2 → ℝ} {x₀ M c a ε : ℝ} (hc : 0 < c)
    (hF : IntegrableOn F {y | M - c * a ≤ y 1 ∧ y 1 ≤ M + c * a ∧ ε ≤ |y 0 - x₀|}) :
    ∫ y in {y | M - c * a ≤ y 1 ∧ y 1 ≤ M + c * a ∧ ε ≤ |y 0 - x₀|}, F y =
      c ^ 2 * ∫ q, {q | ε ≤ c * |q|}.indicator
        (fun q ↦ ∫ p in Icc (-a) a, F !₂[x₀ + c * q, M - c * p]) q := by
  set A := {y : ℝ^2 | M - c * a ≤ y 1 ∧ y 1 ≤ M + c * a ∧ ε ≤ |y 0 - x₀|} with hA
  have h₀ : Measurable fun u : ℝ^2 ↦ u 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have h₁ : Measurable fun u : ℝ^2 ↦ u 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const h₁).inter ((measurableSet_le h₁ measurable_const).inter
      (measurableSet_le measurable_const (continuous_abs.measurable.comp (h₀.sub_const _))))
  have hI : Integrable (A.indicator F) := (integrable_indicator_iff hAm).2 hF
  rw [← integral_indicator hAm, (integral_eq_mul_integral_integral hI hc x₀ M).2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun q ↦ ?_)
  beta_reduce
  have hmem : ∀ p, !₂[x₀ + c * q, M - c * p] ∈ A ↔ p ∈ Icc (-a) a ∧ ε ≤ c * |q| := fun p ↦ by
    simp only [hA, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, add_sub_cancel_left, abs_mul, abs_of_pos hc, mem_Icc]
    constructor
    · rintro ⟨h1, h2, d⟩
      exact ⟨⟨by nlinarith, by nlinarith⟩, d⟩
    · rintro ⟨⟨h1, h2⟩, d⟩
      exact ⟨by nlinarith, by nlinarith, d⟩
  by_cases hq : ε ≤ c * |q|
  · rw [indicator_of_mem (show q ∈ {q | ε ≤ c * |q|} from hq), ← integral_indicator
      measurableSet_Icc]
    refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
    beta_reduce
    by_cases hp : p ∈ Icc (-a) a
    · rw [indicator_of_mem ((hmem p).2 ⟨hp, hq⟩), indicator_of_mem hp]
    · rw [indicator_of_notMem (fun h ↦ hp ((hmem p).1 h).1), indicator_of_notMem hp]
  · rw [indicator_of_notMem (show q ∉ {q | ε ≤ c * |q|} from hq)]
    have : ∀ p, A.indicator F !₂[x₀ + c * q, M - c * p] = 0 := fun p ↦
      indicator_of_notMem (fun h ↦ hq ((hmem p).1 h).2) _
    simp only [this, integral_zero]

/-- **Columns in rescaled coordinates.** For `c > 0`, a measurable set `P` of columns and `F`
integrable on the horizontal strips `R = {(M - y₂)/c ∈ P}`,
`∫_R F = c² ∫_P ∫ F(x₁ + c q, M - c p) dq dp`. -/
theorem setIntegral_columns_eq {F : ℝ^2 → ℝ} {x₀ M c : ℝ} (hc : 0 < c) {P : Set ℝ}
    (hP : MeasurableSet P) (hF : IntegrableOn F {y | (M - y 1) / c ∈ P}) :
    ∫ y in {y | (M - y 1) / c ∈ P}, F y =
      c ^ 2 * ∫ p, P.indicator (fun p ↦ ∫ q, F !₂[x₀ + c * q, M - c * p]) p := by
  set A := {y : ℝ^2 | (M - y 1) / c ∈ P} with hA
  have h₁ : Measurable fun u : ℝ^2 ↦ u 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  have hAm : MeasurableSet A := ((measurable_const.sub h₁).div_const c) hP
  have hI : Integrable (A.indicator F) := (integrable_indicator_iff hAm).2 hF
  rw [← integral_indicator hAm, (integral_eq_mul_integral_integral_height hI hc x₀ M).2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
  beta_reduce
  have hmem : ∀ q, !₂[x₀ + c * q, M - c * p] ∈ A ↔ p ∈ P := fun q ↦ by
    simp only [hA, mem_ofPred_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_sub_cancel]
    rw [mul_div_cancel_left₀ _ hc.ne']
  by_cases hp : p ∈ P
  · rw [indicator_of_mem hp]
    refine integral_congr_ae (Eventually.of_forall fun q ↦ ?_)
    beta_reduce
    rw [indicator_of_mem ((hmem q).2 hp)]
  · rw [indicator_of_notMem hp]
    have : ∀ q, A.indicator F !₂[x₀ + c * q, M - c * p] = 0 := fun q ↦
      indicator_of_notMem (fun h ↦ hp ((hmem q).1 h)) _
    simp only [this, integral_zero]

/-- A decay bound `|W(y)| ≤ C (1 + |y|)^{-ε₀}` with `ε₀ > 0` bounds `W` by `C`. -/
private theorem abs_le_of_decay {W : ℝ^2 → ℝ} {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) (y : ℝ^2) : |W y| ≤ C :=
  (hdec y).trans (mul_le_of_le_one_right
    (nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hdec 0)) (by positivity))
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)))

/-- Clearing the rescaling factor: `c² ∫ 1_T (g / c²) = ∫ 1_T g` for `c ≠ 0`. -/
private theorem mul_integral_indicator_div {c : ℝ} (hc : c ≠ 0) (T : Set ℝ) (g : ℝ → ℝ) :
    c ^ 2 * ∫ t, T.indicator (fun t ↦ g t / c ^ 2) t = ∫ t, T.indicator g t := by
  simp only [div_eq_mul_inv, indicator_mul_left, integral_mul_const]
  field_simp

/-- **The difference of the disc principal values** at two points `x`, `z` of a vertical line in
the open upper half-plane, `x₂ < z₂`, for `W` measurable with `|W(y)| ≤ C (1 + |y|)^{-ε₀}`
(`ε₀ > 0`), horizontal `1/2`-Hölder seminorm at most `C_x` on the plane and vertical seminorm at
most `C_y` on the closed upper half-plane: with `c = (z₂ - x₂)/2`,

`|v_x - v_z| ≤ c^{1/2} (C_y C_in + C_x C_{mid,2})`.

The mixed truncations (`tendsto_setIntegral_pairTruncation`) split in rescaled coordinates into
rows `|p| ≤ 1`, `|q| ≥ ε/c`, and columns `|p| ≥ 1 + ε/c`. -/
theorem abs_sub_le_shearVertical (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) univ W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2) {y | 0 ≤ y 1} W ≤ Cy) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hlt : x 1 < z 1) (hx : 0 < x 1) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in univ \ ball z ε, K (z - y) * W y) (𝓝[>] 0) (𝓝 vz)) :
    ENNReal.ofReal |vx - vz| ≤ ENNReal.ofReal (((z 1 - x 1) / 2) ^ (1 / 2 : ℝ)) *
      (Cy * shearVerticalInnerCost + Cx * shearVerticalOuterCost 1) := by
  set c := (z 1 - x 1) / 2 with hc_def
  set M := (x 1 + z 1) / 2 with hM_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hxM : x 1 = M - c := by rw [hM_def, hc_def]; ring
  have hzM : z 1 = M + c := by rw [hM_def, hc_def]; ring
  have hz : 0 < z 1 := hx.trans hlt
  -- Hölder at the two points
  have hWb : ∀ y ∈ (univ : Set (ℝ^2)), |W y| ≤ C := fun y _ ↦ abs_le_of_decay hε₀ hdec y
  have hCy' : HolderSpace.directionalSeminorm 1 (1 / 2) (univ ∩ {y | 0 ≤ y 1}) W ≤ Cy := by
    rwa [univ_inter]
  have hholx := abs_sub_le_of_directionalSeminorm (a := 1) hx (subset_univ _) hCx hCy' hWb
  have hholz : ∀ y ∈ box 1 1 1 z, |W y - W z| ≤
      (Cx + Cy + 2 * |C| / x 1 ^ (1 / 2 : ℝ)) * ‖y - z‖ ^ (1 / 2 : ℝ) := fun y hy ↦ by
    refine (abs_sub_le_of_directionalSeminorm (a := 1) hz (subset_univ _) hCx hCy' hWb y
      hy).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have : x 1 ^ (1 / 2 : ℝ) ≤ z 1 ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hx.le hlt.le (by norm_num)
    gcongr
  have hG := tendsto_setIntegral_pairTruncation hK hWm hε₀ hdec hxz hlt one_pos
    (by norm_num : (0 : ℝ) < 1 / 2) hholx hholz hvx hvz
  -- the rescaled field and its slices
  set w : ℝ → ℝ → ℝ := fun p q ↦ W !₂[x 0 + c * q, M - c * p] with hw
  set Cx' : ℝ≥0 := Cx * (c ^ (1 / 2 : ℝ)).toNNReal with hCx'
  set Cy' : ℝ≥0 := Cy * (c ^ (1 / 2 : ℝ)).toNNReal with hCy'
  have hrows : ∀ q, HolderOnWith Cy' (1 / 2) (fun p ↦ w p q) (Icc (-1) 1) := fun q ↦ by
    have hs := HolderSpace.holderOnWith_slice_one hCy (x 0 + c * q)
    refine holderOnWith_comp_sub_mul hs hc M fun p hp ↦ ?_
    simp only [mem_ofPred_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [hp.2]
  have hcols : ∀ p, HolderOnWith Cx' (1 / 2) (w p) univ := fun p ↦ by
    have hs := HolderSpace.holderOnWith_slice_zero hCx (M - c * p)
    exact holderOnWith_comp_add_mul hs hc (x 0) fun q _ ↦ mem_univ _
  -- the bound at each truncation
  have hbd : ∀ ε, 0 < ε →
      ENNReal.ofReal |∫ y in pairTruncation x z ε, (K (x - y) - K (z - y)) * W y| ≤
        Cy' * shearVerticalInnerCost + Cx' * shearVerticalOuterCost 1 := by
    intro ε hε
    set F : ℝ^2 → ℝ := fun y ↦ (K (x - y) - K (z - y)) * W y with hF
    set A₁ : Set (ℝ^2) := {y | x 1 ≤ y 1 ∧ y 1 ≤ z 1 ∧ ε ≤ |y 0 - x 0|} with hA₁
    set A₂ : Set (ℝ^2) := {y | y 1 ≤ x 1 - ε} ∪ {y | z 1 + ε ≤ y 1} with hA₂
    have hA₂m : MeasurableSet A₂ :=
      (measurableSet_le (by fun_prop) measurable_const).union (measurableSet_le measurable_const
        (by fun_prop))
    have hA : pairTruncation x z ε = A₁ ∪ A₂ := union_assoc _ _ _
    have hdisj : Disjoint A₁ A₂ := disjoint_left.2 fun y ⟨a, b, _⟩ h₂ ↦ by
      rcases h₂ with (h : y 1 ≤ x 1 - ε) | (h : z 1 + ε ≤ y 1) <;> linarith
    have hFi : IntegrableOn F (pairTruncation x z ε) := by
      have h1 := (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hε).mono_set
        (pairTruncation_subset_left hlt.le ε)
      have h2 := (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec z hε).mono_set
        (pairTruncation_subset_right hxz hlt.le ε)
      refine (h1.sub h2).congr_fun (fun y _ ↦ ?_) (measurableSet_pairTruncation x z ε)
      simp only [hF, Pi.sub_apply]
      ring
    have hF₁ : IntegrableOn F A₁ := hFi.mono_set (hA ▸ subset_union_left)
    have hF₂ : IntegrableOn F A₂ := hFi.mono_set (hA ▸ subset_union_right)
    have hker : ∀ p q, F !₂[x 0 + c * q, M - c * p] = shearDifference p q * w p q / c ^ 2 :=
      fun p q ↦ by
        simp only [hF]
        rw [shearKernel_sub_sub_mk hK hc.ne' hxz hxM hzM]
        simp only [hw]
        ring
    -- the rows
    have hrep₁ : ∫ y in A₁, F y = ∫ q, {q | ε ≤ c * |q|}.indicator
        (fun q ↦ ∫ p in Icc (-1) 1, shearDifference p q * w p q) q := by
      have eA : A₁ = {y | M - c * 1 ≤ y 1 ∧ y 1 ≤ M + c * 1 ∧ ε ≤ |y 0 - x 0|} := by
        rw [hA₁, mul_one, ← hxM, ← hzM]
      rw [eA] at hF₁ ⊢
      rw [setIntegral_rows_eq hc hF₁]
      simp only [hker, integral_div]
      exact mul_integral_indicator_div hc.ne' _ _
    -- the columns
    have hrep₂ : ∫ y in A₂, F y = ∫ p, {p | ε ≤ c * (|p| - 1)}.indicator
        (fun p ↦ ∫ q, shearDifference p q * w p q) p := by
      have eA : A₂ = {y | (M - y 1) / c ∈ {p : ℝ | ε ≤ c * (|p| - 1)}} := by
        ext y
        simp only [hA₂, mem_union, mem_ofPred_eq, hxM, hzM]
        rw [show c * (|(M - y 1) / c| - 1) = |M - y 1| - c by
          rw [abs_div, abs_of_pos hc, mul_sub, mul_div_cancel₀ _ hc.ne', mul_one],
          le_sub_iff_add_le (a := ε), le_abs']
        constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
      have hPm : MeasurableSet {p : ℝ | ε ≤ c * (|p| - 1)} :=
        measurableSet_le measurable_const (by fun_prop)
      rw [eA] at hF₂ ⊢
      rw [setIntegral_columns_eq (x₀ := x 0) hc hPm hF₂]
      simp only [hker, integral_div]
      exact mul_integral_indicator_div hc.ne' _ _
    have hS₂ : ∀ p ∈ {p : ℝ | ε ≤ c * (|p| - 1)}, 1 < |p| := fun p hp ↦ by
      have : ε ≤ c * (|p| - 1) := hp
      nlinarith
    rw [hA, setIntegral_union hdisj hA₂m hF₁ hF₂, hrep₁, hrep₂]
    have h1 := ofReal_abs_integral_rows_le le_rfl hrows {q | ε ≤ c * |q|}
    have h2 := ofReal_abs_integral_columns_le le_rfl hcols hS₂
    rw [shearVerticalMidCost_one, add_zero] at h1
    exact (ofReal_abs_add_le _ _).trans (add_le_add h1 h2)
  have hlim : Tendsto (fun ε ↦ ENNReal.ofReal
      |∫ y in pairTruncation x z ε, (K (x - y) - K (z - y)) * W y|) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal |vx - vz|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp hG)
  refine (le_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using hbd ε hε)).trans_eq ?_
  rw [hCx', hCy', ENNReal.coe_mul, ENNReal.coe_mul, ← ENNReal.ofReal]
  ring

/-- **The difference of the strip principal values with the middle region**, the estimate of `u_y`
of Chen and Hou, Part I, Appendix B.2, (B.50), (B.53), (B.59): under the hypotheses of
`abs_sub_le_shearVertical`, with `c = (z₂ - x₂)/2` and `m = (x₂ + z₂)/(z₂ - x₂) > 1`,

`|(v_x + (π/2) W(x)) - (v_z + (π/2) W(z))| ≤
  c^{1/2} (C_y (C_in + C_{mid,1}(m)) + C_x C_out(m))`.

Removing the vertical strip `|y₁ - x₁| < ε` at both points gives the left side
(`tendsto_setIntegral_strip_of_decay`); the rows `|p| ≤ m` reach the boundary from above and are
transported horizontally, the rest are whole columns `|p| > m`. -/
theorem abs_sub_le_shearVertical_mid (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) univ W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2) {y | 0 ≤ y 1} W ≤ Cy) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hlt : x 1 < z 1) (hx : 0 < x 1) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in univ \ ball z ε, K (z - y) * W y) (𝓝[>] 0) (𝓝 vz)) :
    ENNReal.ofReal |(vx + Real.pi / 2 * W x) - (vz + Real.pi / 2 * W z)| ≤
      ENNReal.ofReal (((z 1 - x 1) / 2) ^ (1 / 2 : ℝ)) *
        (Cy * (shearVerticalInnerCost + shearVerticalMidCost ((x 1 + z 1) / (z 1 - x 1))) +
          Cx * shearVerticalOuterCost ((x 1 + z 1) / (z 1 - x 1))) := by
  set c := (z 1 - x 1) / 2 with hc_def
  set M := (x 1 + z 1) / 2 with hM_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hxM : x 1 = M - c := by rw [hM_def, hc_def]; ring
  have hzM : z 1 = M + c := by rw [hM_def, hc_def]; ring
  have hz : 0 < z 1 := hx.trans hlt
  set m := (x 1 + z 1) / (z 1 - x 1) with hm_def
  have hmc : c * m = M := by
    rw [hm_def, hc_def, hM_def]
    field_simp
  have hm1 : 1 < m := by
    rw [hm_def, one_lt_div (by linarith)]
    linarith
  -- Hölder at the two points
  have hWb : ∀ y ∈ (univ : Set (ℝ^2)), |W y| ≤ C := fun y _ ↦ abs_le_of_decay hε₀ hdec y
  have hCy' : HolderSpace.directionalSeminorm 1 (1 / 2) (univ ∩ {y | 0 ≤ y 1}) W ≤ Cy := by
    rwa [univ_inter]
  have hholx := abs_sub_le_of_directionalSeminorm (a := 1) hx (subset_univ _) hCx hCy' hWb
  have hholz := abs_sub_le_of_directionalSeminorm (a := 1) hz (subset_univ _) hCx hCy' hWb
  -- the strip truncations
  set F : ℝ^2 → ℝ := fun y ↦ (K (x - y) - K (z - y)) * W y with hF
  set S : ℝ → Set (ℝ^2) := fun ε ↦ {y | ε ≤ |y 0 - x 0|} with hS
  have hSm : ∀ ε, MeasurableSet (S ε) := fun ε ↦ measurableSet_le measurable_const (by fun_prop)
  have hSx : ∀ ε, S ε ⊆ {y | ε ≤ ‖y - x‖} := fun ε y hy ↦
    (show ε ≤ |y 0 - x 0| from hy).trans (abs_sub_apply_le_norm x y 0)
  have hSz : ∀ ε, S ε ⊆ {y | ε ≤ ‖y - z‖} := fun ε y hy ↦ by
    have : ε ≤ |y 0 - z 0| := by rw [← hxz]; exact hy
    exact this.trans (abs_sub_apply_le_norm z y 0)
  have hFS : ∀ ε, 0 < ε → IntegrableOn F (S ε) := fun ε hε ↦ by
    have h1 := (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hε).mono_set (hSx ε)
    have h2 := (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec z hε).mono_set (hSz ε)
    refine (h1.sub h2).congr_fun (fun y _ ↦ ?_) (hSm ε)
    simp only [hF, Pi.sub_apply]
    ring
  have hGx := tendsto_setIntegral_strip_of_decay hK hWm hε₀ hdec one_pos
    (by norm_num : (0 : ℝ) < 1 / 2) hholx hvx
  have hGz := tendsto_setIntegral_strip_of_decay hK hWm hε₀ hdec one_pos
    (by norm_num : (0 : ℝ) < 1 / 2) hholz hvz
  rw [← hxz] at hGz
  have hG : Tendsto (fun ε ↦ ∫ y in S ε, F y) (𝓝[>] 0)
      (𝓝 ((vx + Real.pi / 2 * W x) - (vz + Real.pi / 2 * W z))) := by
    refine (hGx.sub hGz).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← integral_sub ((integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hε).mono_set
      (hSx ε)) ((integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec z hε).mono_set (hSz ε))]
    congr 1
    ext y
    simp only [hF]
    ring
  -- the columns `|p| > m`
  set P : Set ℝ := {p | m < |p|} with hP
  have hPm : MeasurableSet P := measurableSet_lt measurable_const continuous_abs.measurable
  set B : Set (ℝ^2) := {y | (M - y 1) / c ∈ P} with hB
  have hBm : MeasurableSet B := (by fun_prop : Measurable fun y : ℝ^2 ↦ (M - y 1) / c) hPm
  have hBmem : ∀ y : ℝ^2, y ∈ B ↔ y 1 < 0 ∨ 2 * M < y 1 := fun y ↦ by
    simp only [hB, hP, mem_ofPred_eq, abs_div, abs_of_pos hc, lt_div_iff₀ hc, mul_comm _ c, hmc]
    rw [lt_abs]
    constructor <;> rintro (h | h) <;> first | (left; linarith) | (right; linarith)
  have hFB : IntegrableOn F B := by
    have hBx : B ⊆ {y | x 1 ≤ ‖y - x‖} := fun y hy ↦ show x 1 ≤ ‖y - x‖ by
      have := abs_sub_apply_le_norm x y 1
      rcases (hBmem y).1 hy with h | h <;>
        linarith [neg_le_abs (y 1 - x 1), le_abs_self (y 1 - x 1)]
    have hBz : B ⊆ {y | x 1 ≤ ‖y - z‖} := fun y hy ↦ show x 1 ≤ ‖y - z‖ by
      have := abs_sub_apply_le_norm z y 1
      rcases (hBmem y).1 hy with h | h <;>
        linarith [neg_le_abs (y 1 - z 1), le_abs_self (y 1 - z 1)]
    have h1 := (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hx).mono_set hBx
    have h2 := (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec z hx).mono_set hBz
    refine (h1.sub h2).congr_fun (fun y _ ↦ ?_) hBm
    simp only [hF, Pi.sub_apply]
    ring
  have hnull : ∀ᵐ y : ℝ^2, y 0 ≠ x 0 := measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq (x 0))
  have hcolsS : Tendsto (fun ε ↦ ∫ y in B ∩ S ε, F y) (𝓝[>] 0) (𝓝 (∫ y in B, F y)) := by
    have h : ∀ ε, ∫ y in B ∩ S ε, F y = ∫ y in B, (S ε).indicator F y := fun ε ↦ by
      rw [setIntegral_indicator (hSm ε)]
    simp_rw [h]
    refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖F y‖)
      (Eventually.of_forall fun ε ↦ hFB.aestronglyMeasurable.indicator (hSm ε))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ norm_indicator_le_norm_self _ y)
      hFB.norm ?_
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (abs_pos.2 (sub_ne_zero.2 hy)))] with ε hε
    rw [indicator_of_mem (show y ∈ S ε from hε)]
  -- the rescaled field
  set w : ℝ → ℝ → ℝ := fun p q ↦ W !₂[x 0 + c * q, M - c * p] with hw
  set Cx' : ℝ≥0 := Cx * (c ^ (1 / 2 : ℝ)).toNNReal with hCx'
  set Cy' : ℝ≥0 := Cy * (c ^ (1 / 2 : ℝ)).toNNReal with hCy'
  have hrows : ∀ q, HolderOnWith Cy' (1 / 2) (fun p ↦ w p q) (Icc (-m) m) := fun q ↦ by
    have hs := HolderSpace.holderOnWith_slice_one hCy (x 0 + c * q)
    refine holderOnWith_comp_sub_mul hs hc M fun p hp ↦ ?_
    simp only [mem_ofPred_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    nlinarith [hp.2]
  have hcols : ∀ p, HolderOnWith Cx' (1 / 2) (w p) univ := fun p ↦ by
    have hs := HolderSpace.holderOnWith_slice_zero hCx (M - c * p)
    exact holderOnWith_comp_add_mul hs hc (x 0) fun q _ ↦ mem_univ _
  have hker : ∀ p q, F !₂[x 0 + c * q, M - c * p] = shearDifference p q * w p q / c ^ 2 :=
    fun p q ↦ by
      simp only [hF]
      rw [shearKernel_sub_sub_mk hK hc.ne' hxz hxM hzM]
      simp only [hw]
      ring
  have hcolB : ENNReal.ofReal |∫ y in B, F y| ≤ Cx' * shearVerticalOuterCost m := by
    rw [hB, setIntegral_columns_eq (x₀ := x 0) hc hPm hFB]
    simp only [hker, integral_div]
    rw [mul_integral_indicator_div hc.ne']
    exact ofReal_abs_integral_columns_le hm1.le hcols fun p hp ↦ hp
  -- the rows `|p| ≤ m`
  have hrow : ∀ ε, 0 < ε → ENNReal.ofReal |(∫ y in S ε, F y) - ∫ y in B ∩ S ε, F y| ≤
      Cy' * (shearVerticalInnerCost + shearVerticalMidCost m) := by
    intro ε hε
    set R : Set (ℝ^2) := {y | M - c * m ≤ y 1 ∧ y 1 ≤ M + c * m ∧ ε ≤ |y 0 - x 0|} with hR
    have hRS : S ε = R ∪ (B ∩ S ε) := by
      ext y
      simp only [hS, hR, mem_union, mem_inter_iff, mem_ofPred_eq, hBmem, hmc]
      refine ⟨fun h ↦ ?_, by rintro (⟨-, -, h⟩ | ⟨-, h⟩) <;> exact h⟩
      rcases lt_or_ge (y 1) 0 with h' | h'
      · exact Or.inr ⟨Or.inl h', h⟩
      rcases lt_or_ge (2 * M) (y 1) with h'' | h''
      exacts [Or.inr ⟨Or.inr h'', h⟩, Or.inl ⟨by linarith, by linarith, h⟩]
    have hdisj : Disjoint R (B ∩ S ε) := by
      refine disjoint_left.2 fun y hyR hyB ↦ ?_
      obtain ⟨a, b, -⟩ := hyR
      rcases (hBmem y).1 hyB.1 with h | h <;> nlinarith
    have hFR : IntegrableOn F R := (hFS ε hε).mono_set (hRS ▸ subset_union_left)
    have hFBS : IntegrableOn F (B ∩ S ε) := hFB.mono_set inter_subset_left
    have hsplit : ∫ y in S ε, F y = (∫ y in R, F y) + ∫ y in B ∩ S ε, F y := by
      conv_lhs => rw [hRS]
      exact setIntegral_union hdisj (hBm.inter (hSm ε)) hFR hFBS
    rw [hsplit, add_sub_cancel_right, hR, setIntegral_rows_eq hc hFR]
    simp only [hker, integral_div]
    rw [mul_integral_indicator_div hc.ne']
    exact ofReal_abs_integral_rows_le hm1.le hrows _
  -- the limit
  set Q := (vx + Real.pi / 2 * W x) - (vz + Real.pi / 2 * W z) with hQ
  have hlim : Tendsto (fun ε ↦ ENNReal.ofReal |(∫ y in S ε, F y) - ∫ y in B ∩ S ε, F y|)
      (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal |Q - ∫ y in B, F y|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp (hG.sub hcolsS))
  have hQB := le_of_tendsto hlim (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using hrow ε hε)
  calc ENNReal.ofReal |Q| = ENNReal.ofReal |(Q - ∫ y in B, F y) + ∫ y in B, F y| := by ring_nf
    _ ≤ ENNReal.ofReal |Q - ∫ y in B, F y| + ENNReal.ofReal |∫ y in B, F y| :=
        ofReal_abs_add_le _ _
    _ ≤ Cy' * (shearVerticalInnerCost + shearVerticalMidCost m) +
          Cx' * shearVerticalOuterCost m := add_le_add hQB hcolB
    _ = _ := by
        rw [hCx', hCy', ENNReal.coe_mul, ENNReal.coe_mul, ← ENNReal.ofReal]
        ring

/-- **Chen and Hou, Part I, Lemma 3.5** for the disc principal values. Let `x, z` lie on a
vertical line in the open upper half-plane, `x₂ ≠ z₂`, let `W` be measurable with
`|W(y)| ≤ C (1 + |y|)^{-ε₀}` (`ε₀ > 0`), with horizontal `1/2`-Hölder seminorm at most `C_x` on the
plane and vertical seminorm at most `C_y` on the closed upper half-plane, and let the disc
truncations of `∫ K₂(x - y) W(y) dy` and `∫ K₂(z - y) W(y) dy` over the plane converge to `v_x`,
`v_z`. For `s = ± 1`,

`|(v_x + s (π/2) W(x)) - (v_z + s (π/2) W(z))| / (π |x - z|^{1/2}) ≤
  (C_y (C_in + (π/2) √2) + C_x C_{mid,2}) / (π √2)`.

For the unlocalized velocity, `u_y = π⁻¹ v + W/2` (`s = 1`) and `v_x = π⁻¹ v - W/2` (`s = -1`)
(Part I, (3.4)), so the left side is the Hölder quotient of `u_y` or `v_x` (Part I,
Appendix B.2). -/
theorem abs_sub_div_le_shear_vertical (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) univ W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2) {y | 0 ≤ y 1} W ≤ Cy) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hne : x 1 ≠ z 1) (hx : 0 < x 1) (hz : 0 < z 1) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in univ \ ball z ε, K (z - y) * W y) (𝓝[>] 0) (𝓝 vz))
    {s : ℝ} (hs : |s| = 1) :
    ENNReal.ofReal (|(vx + s * (Real.pi / 2) * W x) - (vz + s * (Real.pi / 2) * W z)| /
        (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ))) ≤
      (Cy * (shearVerticalInnerCost + ENNReal.ofReal (Real.pi / 2 * Real.sqrt 2)) +
        Cx * shearVerticalOuterCost 1) / ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
  wlog hlt : x 1 < z 1 generalizing x z vx vz
  · have hlt' : z 1 < x 1 := lt_of_le_of_ne (not_lt.1 hlt) hne.symm
    have := this hxz.symm hne.symm hz hx hvz hvx hlt'
    rwa [abs_sub_comm (vz + _), abs_sub_comm (z 1)] at this
  set c := (z 1 - x 1) / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hd : |x 1 - z 1| = 2 * c := by
    rw [abs_sub_comm, abs_of_pos (by linarith), hc_def]
    ring
  have hcore := abs_sub_le_shearVertical hK hWm hε₀ hdec hCx hCy hxz hlt hx hvx hvz
  -- the local terms
  have hW : |W x - W z| ≤ Cy * (2 * c) ^ (1 / 2 : ℝ) := by
    have hxx : x = !₂[x 0, x 1] := by ext i; fin_cases i <;> simp
    have hzz : z = !₂[x 0, z 1] := by ext i; fin_cases i <;> simp [hxz]
    have h := (HolderSpace.holderOnWith_slice_one hCy (x 0)).dist_le
      (show x 1 ∈ {t | !₂[x 0, t] ∈ {y : ℝ^2 | 0 ≤ y 1}} by simpa using hx.le)
      (show z 1 ∈ {t | !₂[x 0, t] ∈ {y : ℝ^2 | 0 ≤ y 1}} by simpa using hz.le)
    rw [← hxx, ← hzz, Real.dist_eq, Real.dist_eq, hd] at h
    simpa using h
  have hsc : 0 < c ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc _
  have h2c : (2 * c) ^ (1 / 2 : ℝ) = Real.sqrt 2 * c ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hc.le, ← Real.sqrt_eq_rpow]
  have hnum : ENNReal.ofReal |(vx + s * (Real.pi / 2) * W x) - (vz + s * (Real.pi / 2) * W z)| ≤
      ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * (Cy * (shearVerticalInnerCost +
        ENNReal.ofReal (Real.pi / 2 * Real.sqrt 2)) + Cx * shearVerticalOuterCost 1) := by
    have e : (vx + s * (Real.pi / 2) * W x) - (vz + s * (Real.pi / 2) * W z) =
        (vx - vz) + s * (Real.pi / 2) * (W x - W z) := by ring
    have hloc : ENNReal.ofReal |s * (Real.pi / 2) * (W x - W z)| ≤
        ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * (Cy * ENNReal.ofReal (Real.pi / 2 * Real.sqrt 2)) := by
      rw [abs_mul, abs_mul, hs, one_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / 2),
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
        ← ENNReal.ofReal_mul hsc.le]
      exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hW (by positivity)).trans_eq
        (by rw [h2c]; ring))
    rw [e]
    exact (ofReal_abs_add_le _ _).trans ((add_le_add hcore hloc).trans_eq (by ring))
  have hq : 0 < Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ) := by rw [hd]; positivity
  rw [ENNReal.ofReal_div_of_pos hq]
  have e₁ : ENNReal.ofReal (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
    rw [← ENNReal.ofReal_mul hsc.le, hd, h2c]
    congr 1
    ring
  calc _ ≤ ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * (Cy * (shearVerticalInnerCost +
          ENNReal.ofReal (Real.pi / 2 * Real.sqrt 2)) + Cx * shearVerticalOuterCost 1) /
          ENNReal.ofReal (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by
      rw [e₁, ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hsc).ne' ENNReal.ofReal_ne_top]

/-- The integrals of `abs_sub_div_le_shear_vertical` in the anisotropic form: for `τ > 0`,
`(C_y (C_in + (π/2) √2) + C_x C_{mid,2}) / (π √2) ≤ (C₃(τ)/π) max(C_x, τ⁻¹ C_y)`. -/
theorem div_le_shearVerticalResidualConstant_mul {τ : ℝ} (hτ : 0 < τ) (Cx Cy : ℝ≥0∞) :
    (Cy * (shearVerticalInnerCost + ENNReal.ofReal (Real.pi / 2 * Real.sqrt 2)) +
        Cx * shearVerticalOuterCost 1) / ENNReal.ofReal (Real.pi * Real.sqrt 2) ≤
      shearVerticalResidualConstant τ / ENNReal.ofReal Real.pi *
        max Cx (ENNReal.ofReal (1 / τ) * Cy) := by
  rw [add_comm]
  exact div_le_div_mul_max hτ le_rfl

/-- **Chen and Hou, Part I, Lemma 3.5 for `u_y`** with the middle region, for the disc principal
values: under the hypotheses of `abs_sub_div_le_shear_vertical`, with
`m = (x₂ + z₂)/|x₂ - z₂|`,

`|(v_x + (π/2) W(x)) - (v_z + (π/2) W(z))| / (π |x - z|^{1/2}) ≤
  (C_y (C_in + C_{mid,1}(m)) + C_x C_out(m)) / (π √2)`

(Part I, Appendix B.2, the estimate of `u_y` with the first estimate in `Ω_mid`). -/
theorem abs_sub_div_le_shear_vertical_mid
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) univ W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2) {y | 0 ≤ y 1} W ≤ Cy) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hne : x 1 ≠ z 1) (hx : 0 < x 1) (hz : 0 < z 1) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in univ \ ball z ε, K (z - y) * W y) (𝓝[>] 0) (𝓝 vz)) :
    ENNReal.ofReal (|(vx + Real.pi / 2 * W x) - (vz + Real.pi / 2 * W z)| /
        (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ))) ≤
      (Cy * (shearVerticalInnerCost + shearVerticalMidCost ((x 1 + z 1) / |x 1 - z 1|)) +
        Cx * shearVerticalOuterCost ((x 1 + z 1) / |x 1 - z 1|)) /
        ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
  wlog hlt : x 1 < z 1 generalizing x z vx vz
  · have hlt' : z 1 < x 1 := lt_of_le_of_ne (not_lt.1 hlt) hne.symm
    have := this hxz.symm hne.symm hz hx hvz hvx hlt'
    rwa [abs_sub_comm (vz + _), abs_sub_comm (z 1), add_comm (z 1)] at this
  set c := (z 1 - x 1) / 2 with hc_def
  have hc : 0 < c := by rw [hc_def]; linarith
  have hd : |x 1 - z 1| = 2 * c := by
    rw [abs_sub_comm, abs_of_pos (by linarith), hc_def]
    ring
  have hm : (x 1 + z 1) / |x 1 - z 1| = (x 1 + z 1) / (z 1 - x 1) := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
  have hcore := abs_sub_le_shearVertical_mid hK hWm hε₀ hdec hCx hCy hxz hlt hx hvx hvz
  rw [hm]
  have hsc : 0 < c ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hc _
  have hq : 0 < Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ) := by rw [hd]; positivity
  rw [ENNReal.ofReal_div_of_pos hq]
  have e₁ : ENNReal.ofReal (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (c ^ (1 / 2 : ℝ)) * ENNReal.ofReal (Real.pi * Real.sqrt 2) := by
    rw [← ENNReal.ofReal_mul hsc.le, hd, Real.mul_rpow (by norm_num) hc.le,
      ← Real.sqrt_eq_rpow]
    congr 1
    ring
  calc _ ≤ ENNReal.ofReal (c ^ (1 / 2 : ℝ)) *
          (Cy * (shearVerticalInnerCost + shearVerticalMidCost ((x 1 + z 1) / (z 1 - x 1))) +
            Cx * shearVerticalOuterCost ((x 1 + z 1) / (z 1 - x 1))) /
          ENNReal.ofReal (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by
      rw [e₁, ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 hsc).ne' ENNReal.ofReal_ne_top]

/-- The integrals of `abs_sub_div_le_shear_vertical_mid` are bounded by `C₄(τ)`: for `m > 1` and
`τ > 0`, `(C_y (C_in + C_{mid,1}(m)) + C_x C_out(m)) / (π √2) ≤ (C₄(τ)/π) max(C_x, τ⁻¹ C_y)`. -/
theorem div_le_shearVerticalConstant_mul {τ m : ℝ} (hτ : 0 < τ) (hm : 1 < m) (Cx Cy : ℝ≥0∞) :
    (Cy * (shearVerticalInnerCost + shearVerticalMidCost m) + Cx * shearVerticalOuterCost m) /
        ENNReal.ofReal (Real.pi * Real.sqrt 2) ≤
      shearVerticalConstant τ / ENNReal.ofReal Real.pi *
        max Cx (ENNReal.ofReal (1 / τ) * Cy) := by
  rw [add_comm]
  exact div_le_div_mul_max hτ (le_iSup₂_of_le m hm le_rfl)

end IncompressibleFlow.SharpHolder
