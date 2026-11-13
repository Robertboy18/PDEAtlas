/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainHolder

/-!
# The vertical Hölder estimate of the localized strain

Chen and Hou, Part I, Lemma 3.3: for two points `x, z` on a vertical line, the localized strains
over the boxes `Q_{a,b,b}` satisfy

`|u_x(x, a, b) - u_x(z, a, b)| / |x - z|^{1/2} ≤ (1/2) C₁(a/|x - z|) [W]_{C_y^{1/2}} +
C₂(a/|x - z|) [W]_{C_x^{1/2}}`,

where the vertical seminorm is needed only above the midpoint height `m` of the two points (the
odd extension jumps across the boundary below), and

`C₂(a) = (√2/π) ∫_0^a ∫_0^∞ p^{1/2} |K₁(p, q + 1/2) - K₁(p, q - 1/2)| dq dp`

(`strainCrossConstant`). Above `m` the difference of the two kernels is the localized kernel
`k_B` of the horizontal estimate in rotated coordinates, and the half-line transport estimate gives
the first term; one half-line only, hence the factor `1/2`. Below `m` the horizontal reflection
about the common abscissa pairs `W(y)` with `W(R y)`, at horizontal distance `2 |y₁ - x₁|`, and the
truncation comparison of Part I, Lemma 3.10 removes the localization in the vertical direction.

## Main results

* `strainCrossConstant`, `lintegral_abs_strainDifference_eq`: `C₂` and the closed form
  `∫_0^∞ |Δ(q, p)| dq = 2 Φ_p(f(p))` of its inner integral.
* `lintegral_localStrainDifference_le`: `∫_0^∞ |k_B(q, p)| dq ≤ ∫_0^∞ |Δ(q, p)| dq`.
* `abs_sub_div_le_vertical`: Part I, Lemma 3.3, for the reflected integrals.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.3, p. 28, and Section 3.4,
  (3.31), (3.32) and Lemma 3.10, pp. 36-37.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric PDE.Common PDE.Analysis.Rearrangement
open PDE.Analysis (planeEquiv planeEquiv_symm_apply measurePreserving_planeEquiv)
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- The constant `C₂(a) = (√2/π) ∫_0^a p^{1/2} ∫_0^∞ |K₁(p, q + 1/2) - K₁(p, q - 1/2)| dq dp` of
Chen and Hou, Part I, Lemma 3.3, as an extended real. The inner kernel is `Δ(q, p)`. -/
def strainCrossConstant (a : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt 2 / Real.pi) *
    ∫⁻ p in Ioo 0 a, ENNReal.ofReal (p ^ (1 / 2 : ℝ)) *
      ∫⁻ q in Ioi 0, ENNReal.ofReal |strainDifference q p|

/-- `C₂` is nondecreasing. -/
theorem monotone_strainCrossConstant : Monotone strainCrossConstant := fun _ _ h ↦
  mul_le_mul_right (lintegral_mono_set (Ioo_subset_Ioo_right h)) _

/-- The inner integral of `C₂` in closed form: `∫_0^∞ |Δ(q, p)| dq = 2 Φ_p(f(p))` for `p > 0`,
since `Δ(·, p)` is positive on `(0, f(p))`, negative beyond, and `Φ_p(0) = Φ_p(∞) = 0`. -/
theorem lintegral_abs_strainDifference_eq {p : ℝ} (hp : 0 < p) :
    ∫⁻ q in Ioi 0, ENNReal.ofReal |strainDifference q p| =
      ENNReal.ofReal (2 * strainPotential p (strainThreshold p)) := by
  have hf := strainThreshold_pos p
  have hi : Integrable fun q ↦ strainDifference q p := integrable_strainDifference_left hp.ne'
  have hin : Integrable fun q ↦ -strainDifference q p := hi.neg
  have hpos : ∀ q ∈ Ioc 0 (strainThreshold p), 0 ≤ strainDifference q p := fun q hq ↦ by
    rcases eq_or_lt_of_le hq.2 with h | h
    · rw [h, strainDifference_eq hp.ne', strainQuartic_strainThreshold, mul_zero, zero_div]
    · exact ((strainDifference_pos_iff hq.1.le hp).2 h).le
  have hneg : ∀ q ∈ Ioi (strainThreshold p), strainDifference q p ≤ 0 := fun q hq ↦
    ((strainDifference_neg_iff (hf.trans hq).le hp).2 hq).le
  have hΦ : 0 ≤ strainPotential p (strainThreshold p) := by
    have := (strictMonoOn_strainPotential hp).monotoneOn ⟨le_rfl, hf.le⟩ ⟨hf.le, le_rfl⟩ hf.le
    rwa [strainPotential_zero] at this
  have h₁ : ∫⁻ q in Ioc 0 (strainThreshold p), ENNReal.ofReal |strainDifference q p| =
      ENNReal.ofReal (strainPotential p (strainThreshold p)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (g := fun q ↦ ENNReal.ofReal (strainDifference q p)) fun q hq ↦ by
        rw [abs_of_nonneg (hpos q hq)],
      ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hpos)),
      ← intervalIntegral.integral_of_le hf.le, integral_strainDifference hp.ne',
      strainPotential_zero, sub_zero]
  have h₂ : ∫⁻ q in Ioi (strainThreshold p), ENNReal.ofReal |strainDifference q p| =
      ENNReal.ofReal (strainPotential p (strainThreshold p)) := by
    have hI := integral_Ioi_of_hasDerivAt_of_tendsto (a := strainThreshold p)
      (continuous_strainPotential hp.ne').continuousWithinAt
      (fun t _ ↦ hasDerivAt_strainPotential hp.ne' t) hi.integrableOn
      (tendsto_strainPotential_atTop p)
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (g := fun q ↦ ENNReal.ofReal (-strainDifference q p)) fun q hq ↦ by
        rw [abs_of_nonpos (hneg q hq)],
      ← ofReal_integral_eq_lintegral_ofReal hin.integrableOn
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun q hq ↦
          neg_nonneg.2 (hneg q hq))), integral_neg, hI, zero_sub, neg_neg]
  rw [← Ioc_union_Ioi_eq_Ioi hf.le, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
    h₁, h₂, ← ENNReal.ofReal_add hΦ hΦ, two_mul]

/-- `C₂(a) = 0` for `a ≤ 0`. -/
theorem strainCrossConstant_of_nonpos {a : ℝ} (ha : a ≤ 0) : strainCrossConstant a = 0 := by
  rw [strainCrossConstant, Ioo_eq_empty (not_lt.2 ha), Measure.restrict_empty,
    lintegral_zero_measure, mul_zero]

/-- `C₂` as a one-dimensional integral:
`C₂(a) = (√2/π) ∫_0^a p^{1/2} 2 Φ_p(f(p)) dp`, from `∫_0^∞ |Δ(q, p)| dq = 2 Φ_p(f(p))`. -/
theorem strainCrossConstant_eq (a : ℝ) :
    strainCrossConstant a = ENNReal.ofReal (Real.sqrt 2 / Real.pi) *
      ∫⁻ p in Ioo 0 a, ENNReal.ofReal (p ^ (1 / 2 : ℝ)) *
        ENNReal.ofReal (2 * strainPotential p (strainThreshold p)) := by
  rw [strainCrossConstant]
  congr 1
  exact setLIntegral_congr_fun measurableSet_Ioo fun p hp ↦ by
    rw [lintegral_abs_strainDifference_eq hp.1]

/-- **The truncation comparison** of Chen and Hou, Part I, Section 3.4 (from Lemma 3.10 with
shift `1/2`, `c = ∞` and weight `1`): for `B ≥ 1/2` and `p ≠ 0`, the localized kernel on the
half-line has no more mass than the full one, `∫_0^∞ |k_B(q, p)| dq ≤ ∫_0^∞ |Δ(q, p)| dq`. -/
theorem lintegral_localStrainDifference_le {B p : ℝ} (hB : 1 / 2 ≤ B) (hp : p ≠ 0) :
    ∫⁻ q in Ioi 0, ‖localStrainDifference B q p‖ₑ ≤ ∫⁻ q in Ioi 0, ‖strainDifference q p‖ₑ := by
  have hB0 : (0 : ℝ) ≤ B - 1 / 2 := by linarith
  have hint := integrable_strainDensity_left hp
  rw [← Ioc_union_Ioi_eq_Ioi hB0, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
    lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  have e₁ : ∫⁻ q in Ioc 0 (B - 1 / 2), ‖localStrainDifference B q p‖ₑ =
      ∫⁻ q in Ioc 0 (B - 1 / 2), ‖strainDifference q p‖ₑ :=
    setLIntegral_congr_fun measurableSet_Ioc fun q hq ↦ by
      rw [localStrainDifference_of_le hq.1.le hq.2]
  have e₂ : ∫⁻ q in Ioi (B - 1 / 2), ‖localStrainDifference B q p‖ₑ =
      ∫⁻ q in Ioc (B - 1 / 2) (B + 1 / 2), ‖strainDensity (q - 1 / 2) p‖ₑ * 1 := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : B - 1 / 2 ≤ B + 1 / 2),
      lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl),
      setLIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ (0 : ℝ≥0∞)) fun q hq ↦ by
        rw [localStrainDifference_eq_zero (by
          rw [abs_of_pos (by linarith [mem_Ioi.1 hq])]; exact hq), enorm_zero],
      lintegral_zero, add_zero]
    refine setLIntegral_congr_fun measurableSet_Ioc fun q hq ↦ ?_
    rw [localStrainDifference_of_lt hB hq.1 hq.2, enorm_neg, mul_one]
  have hshift := lintegral_shift_le_of_tail (f := fun u ↦ strainDensity u p)
    (g := fun _ ↦ (1 : ℝ≥0∞)) (b := B) (h := 1 / 2) hint.aemeasurable monotoneOn_const
    (by norm_num) (by
      simp only [mul_one]
      exact ((hint.comp_sub_right (1 / 2)).integrableOn (s := Ioi (B + 1 / 2))).2.ne)
  rw [e₁, e₂]
  refine add_le_add le_rfl (hshift.trans_eq (setLIntegral_congr_fun measurableSet_Ioi
    fun q _ ↦ ?_))
  rw [mul_one, strainDifference, ← enorm_neg, neg_sub]

/-! ### The kernel difference on a vertical line -/

variable {K : ℝ^2 → ℝ} {a b : ℝ}

/-- The difference `1_{Q(x)} K(x - y) - 1_{Q(z)} K(z - y)` of the two localized kernels. -/
def boxKernelDifference (K : ℝ^2 → ℝ) (a b₁ b₂ : ℝ) (x z y : ℝ^2) : ℝ :=
  (box a b₁ b₂ x).indicator (fun y ↦ K (x - y)) y -
    (box a b₁ b₂ z).indicator (fun y ↦ K (z - y)) y

/-- On a vertical line the kernel difference is the localized kernel `k_B` in rotated
coordinates: for `x = (c, m - d/2)`, `z = (c, m + d/2)` and `y = (s, m + d q)`,
`1_{Q(x)} K(x - y) - 1_{Q(z)} K(z - y) = -1{|c - s| ≤ a} k_{b/d}(q, (c - s)/d) / d²`. -/
theorem boxKernelDifference_mk (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hd : x 1 < z 1) (s q : ℝ) :
    boxKernelDifference K a b b x z !₂[s, (x 1 + z 1) / 2 + (z 1 - x 1) * q] =
      -((if |x 0 - s| ≤ a then 1 else 0) *
        localStrainDifference (b / (z 1 - x 1)) q ((x 0 - s) / (z 1 - x 1)) / (z 1 - x 1) ^ 2) := by
  set d := z 1 - x 1
  have hd0 : 0 < d := sub_pos.2 hd
  set m := (x 1 + z 1) / 2
  set p := (x 0 - s) / d
  have hp : x 0 - s = d * p := by simp only [p]; field_simp
  have hx1 : x 1 = m + d * (-(1 / 2)) := by simp only [m, d]; ring
  have hz1 : z 1 = m + d * (1 / 2) := by simp only [m, d]; ring
  have hKx : K (x - !₂[s, m + d * q]) = -strainDensity (q + 1 / 2) p / d ^ 2 := by
    rw [kernel_sub_mk hK, hp, show x 1 - (m + d * q) = d * (-(q + 1 / 2)) by rw [hx1]; ring,
      strainDensity_mul hd0.ne', strainDensity_neg_right, strainDensity_comm, neg_div]
  have hKz : K (z - !₂[s, m + d * q]) = -strainDensity (q - 1 / 2) p / d ^ 2 := by
    rw [kernel_sub_mk hK, ← hxz, hp,
      show z 1 - (m + d * q) = d * (-(q - 1 / 2)) by rw [hz1]; ring,
      strainDensity_mul hd0.ne', strainDensity_neg_right, strainDensity_comm, neg_div]
  have kx : |q + 1 / 2| * d = |m + d * q - x 1| := by
    rw [hx1, show m + d * q - (m + d * -(1 / 2)) = d * (q + 1 / 2) by ring, abs_mul,
      abs_of_pos hd0, mul_comm]
  have kz : |q - 1 / 2| * d = |m + d * q - z 1| := by
    rw [hz1, show m + d * q - (m + d * (1 / 2)) = d * (q - 1 / 2) by ring, abs_mul,
      abs_of_pos hd0, mul_comm]
  have hcx : !₂[s, m + d * q] ∈ box a b b x ↔ |x 0 - s| ≤ a ∧ |q + 1 / 2| ≤ b / d := by
    rw [mk_mem_box, mem_Icc, mem_Icc, le_div_iff₀ hd0, kx, abs_sub_le_iff, abs_sub_le_iff]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;> exact ⟨⟨by linarith, by linarith⟩, by linarith,
      by linarith⟩
  have hcz : !₂[s, m + d * q] ∈ box a b b z ↔ |x 0 - s| ≤ a ∧ |q - 1 / 2| ≤ b / d := by
    rw [mk_mem_box, mem_Icc, mem_Icc, le_div_iff₀ hd0, kz, abs_sub_le_iff, abs_sub_le_iff, ← hxz]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;> exact ⟨⟨by linarith, by linarith⟩, by linarith,
      by linarith⟩
  simp only [boxKernelDifference, indicator, localStrainDifference]
  by_cases h₀ : |x 0 - s| ≤ a <;> by_cases h₁ : |q + 1 / 2| ≤ b / d <;>
    by_cases h₂ : |q - 1 / 2| ≤ b / d <;>
    simp only [h₀, h₁, h₂, hcx, hcz, and_self, and_false, false_and, ite_true, ite_false, hKx,
      hKz] <;> ring

/-- The kernel difference vanishes off the two boxes. -/
theorem boxKernelDifference_eq_zero {x z y : ℝ^2} {b₁ b₂ : ℝ}
    (hy : y ∉ box a b₁ b₂ x ∪ box a b₁ b₂ z) : boxKernelDifference K a b₁ b₂ x z y = 0 := by
  simp only [boxKernelDifference, indicator_of_notMem (fun h ↦ hy (Or.inl h)),
    indicator_of_notMem (fun h ↦ hy (Or.inr h)), sub_zero]

/-- The kernel difference is measurable. -/
theorem measurable_boxKernelDifference (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) (b₁ b₂ : ℝ)
    (x z : ℝ^2) : Measurable (boxKernelDifference K a b₁ b₂ x z) :=
  (((measurable_kernel hK).comp (measurable_const.sub measurable_id)).indicator
    (measurableSet_box x)).sub
    (((measurable_kernel hK).comp (measurable_const.sub measurable_id)).indicator
      (measurableSet_box z))

/-- The rescaled vertical slice of the reflected difference above the midpoint is
`1/2`-Hölder with constant `2 C d^{1/2}`. -/
private theorem holderOnWith_vertical_slice {x z : ℝ^2} (hxz : x 0 = z 0) (hd : x 1 < z 1)
    (hb : (z 1 - x 1) / 2 ≤ b) {W : ℝ^2 → ℝ} {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a b b x ∪ box a b b z) ∩ {y | (x 1 + z 1) / 2 ≤ y 1}) W ≤ C)
    {s : ℝ} (hs : |x 0 - s| ≤ a) :
    HolderOnWith (2 * C * ((z 1 - x 1) ^ (1 / 2 : ℝ)).toNNReal) (1 / 2)
      (fun q ↦ W !₂[s, (x 1 + z 1) / 2 + (z 1 - x 1) * q] -
        W !₂[2 * x 0 - s, (x 1 + z 1) / 2 + (z 1 - x 1) * q])
      (Icc 0 (b / (z 1 - x 1) + 1 / 2)) := by
  set d := z 1 - x 1
  have hd0 : 0 < d := sub_pos.2 hd
  set m := (x 1 + z 1) / 2
  set D := (box a b b x ∪ box a b b z) ∩ {y : ℝ^2 | m ≤ y 1}
  have hmem : ∀ s' : ℝ, |x 0 - s'| ≤ a → ∀ q ∈ Icc 0 (b / d + 1 / 2), !₂[s', m + d * q] ∈ D := by
    intro s' hs' q hq
    have h₁ : d * q ≤ b + d / 2 :=
      (mul_le_mul_of_nonneg_left hq.2 hd0.le).trans_eq (by field_simp)
    have h₂ : 0 ≤ d * q := mul_nonneg hd0.le hq.1
    refine ⟨Or.inr (mk_mem_box.2 ⟨?_, ?_⟩), ?_⟩
    · rw [← hxz, mem_Icc]
      constructor <;> linarith [(abs_le.1 hs').1, (abs_le.1 hs').2]
    · simp only [m, d] at h₁ h₂ ⊢
      constructor <;> linarith
    · change m ≤ m + d * q
      linarith
  have hs' : |x 0 - (2 * x 0 - s)| ≤ a := by
    rwa [show x 0 - (2 * x 0 - s) = -(x 0 - s) by ring, abs_neg]
  have hslice := fun s' (hs'' : |x 0 - s'| ≤ a) ↦ HolderSpace.holderOnWith_slice_one hC s'
  intro q hq q' hq'
  have e₁ := hslice s hs _ (hmem s hs q hq) _ (hmem s hs q' hq')
  have e₂ := hslice (2 * x 0 - s) hs' _ (hmem _ hs' q hq) _ (hmem _ hs' q' hq')
  have hdist : edist (m + d * q) (m + d * q') ^ ((1 / 2 : ℝ≥0) : ℝ) =
      ENNReal.ofReal (d ^ (1 / 2 : ℝ)) * edist q q' ^ ((1 / 2 : ℝ≥0) : ℝ) := by
    rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq,
      show m + d * q - (m + d * q') = d * (q - q') by ring, abs_mul, abs_of_pos hd0,
      ENNReal.ofReal_mul hd0.le, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
      ENNReal.ofReal_rpow_of_nonneg hd0.le (by norm_num)]
    norm_num
  calc edist (W !₂[s, m + d * q] - W !₂[2 * x 0 - s, m + d * q])
        (W !₂[s, m + d * q'] - W !₂[2 * x 0 - s, m + d * q'])
      ≤ edist (W !₂[s, m + d * q]) (W !₂[s, m + d * q']) +
          edist (W !₂[2 * x 0 - s, m + d * q]) (W !₂[2 * x 0 - s, m + d * q']) := by
        rw [edist_dist, edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg]
        exact ENNReal.ofReal_le_ofReal (dist_sub_sub_le _ _ _ _)
    _ ≤ C * edist (m + d * q) (m + d * q') ^ ((1 / 2 : ℝ≥0) : ℝ) +
          C * edist (m + d * q) (m + d * q') ^ ((1 / 2 : ℝ≥0) : ℝ) := add_le_add e₁ e₂
    _ = ↑(2 * C * (d ^ (1 / 2 : ℝ)).toNNReal) * edist q q' ^ ((1 / 2 : ℝ≥0) : ℝ) := by
        rw [hdist, ENNReal.coe_mul, ENNReal.coe_mul,
          show ((d ^ (1 / 2 : ℝ)).toNNReal : ℝ≥0∞) = ENNReal.ofReal (d ^ (1 / 2 : ℝ)) from rfl]
        push_cast
        ring

/-- Off the horizontal range of the boxes the kernel difference vanishes on the whole line. -/
private theorem boxKernelDifference_mk_eq_zero {x z : ℝ^2} (hxz : x 0 = z 0) {s t : ℝ}
    (hs : ¬|x 0 - s| ≤ a) : boxKernelDifference K a b b x z !₂[s, t] = 0 := by
  refine boxKernelDifference_eq_zero fun h ↦ hs ?_
  rcases h with h | h <;> rw [mk_mem_box] at h <;>
    exact abs_le.2 ⟨by linarith [h.1.2], by linarith [h.1.1]⟩

/-- **The upper half-line**: the vertical slice above the midpoint of the reflected difference is
bounded by the half-line transport estimate,
`|∫_{t ≥ m} (1_{Q(x)} K(x - ·) - 1_{Q(z)} K(z - ·))(s, t) (W(s, t) - W(2x₁ - s, t)) dt| ≤
2 C d^{-1/2} M((x₁ - s)/d)` for `x₁ - a ≤ s < x₁`. -/
theorem abs_integral_upper_le (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hd : x 1 < z 1) (hb : (z 1 - x 1) / 2 ≤ b) {W : ℝ^2 → ℝ} {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a b b x ∪ box a b b z) ∩ {y | (x 1 + z 1) / 2 ≤ y 1}) W ≤ C)
    {s : ℝ} (hs : s < x 0) :
    ENNReal.ofReal |∫ t in Ici ((x 1 + z 1) / 2), boxKernelDifference K a b b x z !₂[s, t] *
        (W !₂[s, t] - W !₂[2 * x 0 - s, t])| ≤
      (Icc (x 0 - a) (x 0 + a)).indicator (fun s ↦ 2 * C *
        ENNReal.ofReal ((z 1 - x 1) ^ (-(1 / 2 : ℝ))) *
          strainCost ((x 0 - s) / (z 1 - x 1))) s := by
  set d := z 1 - x 1
  have hd0 : 0 < d := sub_pos.2 hd
  set m := (x 1 + z 1) / 2
  by_cases hsa : |x 0 - s| ≤ a
  swap
  · simp only [boxKernelDifference_mk_eq_zero hxz hsa, zero_mul, integral_zero, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le
  rw [indicator_of_mem (show s ∈ Icc (x 0 - a) (x 0 + a) from
    ⟨by linarith [(abs_le.1 hsa).2], by linarith [(abs_le.1 hsa).1]⟩)]
  set p := (x 0 - s) / d
  have hp : 0 < p := div_pos (sub_pos.2 hs) hd0
  have hB : 1 / 2 ≤ b / d := by rw [le_div_iff₀ hd0]; linarith
  set g : ℝ → ℝ := fun q ↦ W !₂[s, m + d * q] - W !₂[2 * x 0 - s, m + d * q]
  set F : ℝ → ℝ := fun t ↦ boxKernelDifference K a b b x z !₂[s, t] *
    (W !₂[s, t] - W !₂[2 * x 0 - s, t])
  -- substitution `t = m + d q`
  have hsub : ∫ t in Ici m, F t =
      -(1 / d) * ∫ q in Ioi 0, localStrainDifference (b / d) q p * g q := by
    rw [← integral_indicator measurableSet_Ici]
    have h := Measure.integral_comp_mul_left (fun v ↦ (Ici m).indicator F (m + v)) d
    rw [integral_add_left_eq_self m (μ := volume) (f := (Ici m).indicator F), abs_inv,
      abs_of_pos hd0, smul_eq_mul] at h
    have hF : ∀ q, (Ici m).indicator F (m + d * q) = (Ici (0 : ℝ)).indicator
        (fun q ↦ -(localStrainDifference (b / d) q p * g q / d ^ 2)) q := fun q ↦ by
      by_cases hq : 0 ≤ q
      · rw [indicator_of_mem (show m + d * q ∈ Ici m from by
            simp only [mem_Ici]; nlinarith), indicator_of_mem (show q ∈ Ici 0 from hq)]
        simp only [F, g]
        rw [boxKernelDifference_mk hK hxz hd, ite_eq_left hsa]
        ring
      · rw [indicator_of_notMem (show m + d * q ∉ Ici m from by
            simp only [mem_Ici, not_le]; nlinarith), indicator_of_notMem (show q ∉ Ici 0 from hq)]
    simp only [hF] at h
    rw [show ∫ t, (Ici m).indicator F t = d * ∫ q, (Ici (0 : ℝ)).indicator
        (fun q ↦ -(localStrainDifference (b / d) q p * g q / d ^ 2)) q by
      rw [h]; field_simp, integral_indicator measurableSet_Ici,
      setIntegral_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := (0 : ℝ))).symm, integral_neg]
    simp only [div_eq_mul_inv, integral_mul_const]
    field_simp
  have hg := holderOnWith_vertical_slice hxz hd hb hC hsa
  have hline := abs_setIntegral_localStrainDifference_mul_le hB hp hg
  rw [hsub, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / d),
    ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (1 / d) *
        ENNReal.ofReal |∫ q in Ioi 0, localStrainDifference (b / d) q p * g q|
      ≤ ENNReal.ofReal (1 / d) * (↑(2 * C * (d ^ (1 / 2 : ℝ)).toNNReal) * strainCost p) := by
        gcongr
    _ = 2 * C * ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) * strainCost p := by
        rw [ENNReal.coe_mul, ENNReal.coe_mul,
          show ((d ^ (1 / 2 : ℝ)).toNNReal : ℝ≥0∞) = ENNReal.ofReal (d ^ (1 / 2 : ℝ)) from rfl]
        have : ENNReal.ofReal (1 / d) * ENNReal.ofReal (d ^ (1 / 2 : ℝ)) =
            ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) := by
          rw [← ENNReal.ofReal_mul (by positivity), one_div, ← Real.rpow_neg_one,
            ← Real.rpow_add hd0]
          norm_num
        rw [← this]
        push_cast
        ring

/-- **The lower half-line**: the mass of the kernel difference on a vertical line below the
midpoint is at most `d⁻¹ ∫_0^∞ |Δ(q, p)| dq` with `p = (x₁ - s)/d`, by the truncation
comparison. -/
theorem lintegral_lower_le (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {x z : ℝ^2}
    (hxz : x 0 = z 0) (hd : x 1 < z 1) (hb : (z 1 - x 1) / 2 ≤ b) {s : ℝ} (hs : s < x 0) :
    ∫⁻ t in Iio ((x 1 + z 1) / 2), ENNReal.ofReal |boxKernelDifference K a b b x z !₂[s, t]| ≤
      (Icc (x 0 - a) (x 0 + a)).indicator (fun s ↦ ENNReal.ofReal (1 / (z 1 - x 1)) *
        ∫⁻ q in Ioi 0, ENNReal.ofReal |strainDifference q ((x 0 - s) / (z 1 - x 1))|) s := by
  set d := z 1 - x 1
  have hd0 : 0 < d := sub_pos.2 hd
  set m := (x 1 + z 1) / 2
  by_cases hsa : |x 0 - s| ≤ a
  swap
  · simp only [boxKernelDifference_mk_eq_zero hxz hsa, abs_zero, ENNReal.ofReal_zero,
      lintegral_zero]
    exact zero_le
  rw [indicator_of_mem (show s ∈ Icc (x 0 - a) (x 0 + a) from
    ⟨by linarith [(abs_le.1 hsa).2], by linarith [(abs_le.1 hsa).1]⟩)]
  set p := (x 0 - s) / d
  have hp : 0 < p := div_pos (sub_pos.2 hs) hd0
  have hB : 1 / 2 ≤ b / d := by rw [le_div_iff₀ hd0]; linarith
  -- substitution `t = m + d q`
  have hpre : (fun t ↦ (t - m) / d) ⁻¹' Iio 0 = Iio m := by
    ext t
    simp only [mem_preimage, mem_Iio]
    rw [div_lt_iff₀ hd0, zero_mul, sub_neg]
  have h := setLIntegral_comp_div_sub hd0.ne' m
    (fun q ↦ ENNReal.ofReal |boxKernelDifference K a b b x z !₂[s, m + d * q]|) (Iio 0)
  rw [hpre, abs_of_pos hd0] at h
  simp only [show ∀ t, m + d * ((t - m) / d) = t from fun t ↦ by
    rw [mul_div_cancel₀ _ hd0.ne']; ring] at h
  rw [h]
  have hk : ∀ q, ENNReal.ofReal |boxKernelDifference K a b b x z !₂[s, m + d * q]| =
      ENNReal.ofReal (1 / d ^ 2) * ‖localStrainDifference (b / d) q p‖ₑ := fun q ↦ by
    rw [boxKernelDifference_mk hK hxz hd, ite_eq_left hsa, one_mul, abs_neg, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < d ^ 2), Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_mul (by positivity), one_div_mul_eq_div]
  simp only [hk]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- reflect the lower half-line onto the upper one
  have hrefl : ∫⁻ q in Iio 0, ‖localStrainDifference (b / d) q p‖ₑ =
      ∫⁻ q in Ioi 0, ‖localStrainDifference (b / d) q p‖ₑ := by
    have hmp : MeasurePreserving (fun q : ℝ ↦ -q) volume volume := Measure.measurePreserving_neg _
    have hemb : MeasurableEmbedding fun q : ℝ ↦ -q := (Homeomorph.neg ℝ).measurableEmbedding
    have h := hmp.setLIntegral_comp_preimage_emb hemb
      (fun q ↦ ‖localStrainDifference (b / d) q p‖ₑ) (Iio 0)
    simp only [localStrainDifference_neg_left] at h
    rw [← h]
    congr 1
    ext q
    simp
  rw [hrefl]
  calc ENNReal.ofReal d * (ENNReal.ofReal (1 / d ^ 2) *
        ∫⁻ q in Ioi 0, ‖localStrainDifference (b / d) q p‖ₑ)
      ≤ ENNReal.ofReal d * (ENNReal.ofReal (1 / d ^ 2) *
          ∫⁻ q in Ioi 0, ‖strainDifference q p‖ₑ) := by
        exact mul_le_mul_right (mul_le_mul_right (lintegral_localStrainDifference_le hB hp.ne') _) _
    _ = ENNReal.ofReal (1 / d) * ∫⁻ q in Ioi 0, ENNReal.ofReal |strainDifference q p| := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hd0.le]
        simp only [Real.enorm_eq_ofReal_abs]
        congr 2
        field_simp

/-- The substitution `s = c - d p` on the left half-line:
`∫_{s < c} F(s) ds = d ∫_{p > 0} F(c - d p)` for `d > 0`. -/
theorem setLIntegral_Iio_eq {d : ℝ} (hd : 0 < d) (c : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Iio c, F s = ENNReal.ofReal d * ∫⁻ p in Ioi 0, F (c - d * p) := by
  have h := setLIntegral_comp_div_sub (neg_ne_zero.2 hd.ne') c (fun p ↦ F (c - d * p)) (Ioi 0)
  have hpre : (fun s ↦ (s - c) / -d) ⁻¹' Ioi 0 = Iio c := by
    ext s
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    rw [div_neg, neg_pos, div_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h (not_lt.2 hd.le)
      · linarith
    · intro h
      exact Or.inr ⟨by linarith, hd⟩
  rw [hpre, abs_neg, abs_of_pos hd] at h
  rw [← h]
  refine setLIntegral_congr_fun measurableSet_Iio fun s _ ↦ ?_
  congr 1
  field_simp
  ring

/-- The substitution `s = c - d p` for an integrand of `(c - s)/d` supported on `|c - s| ≤ a`:
`∫_{s < c} 1_{[c - a, c + a]}(s) F((c - s)/d) ds = d ∫_0^{a/d} F` for `d > 0`. -/
private theorem setLIntegral_Iio_indicator_eq {d : ℝ} (hd : 0 < d) (c a : ℝ) (F : ℝ → ℝ≥0∞) :
    ∫⁻ s in Iio c, (Icc (c - a) (c + a)).indicator (fun s ↦ F ((c - s) / d)) s =
      ENNReal.ofReal d * ∫⁻ p in Ioo 0 (a / d), F p := by
  rw [setLIntegral_Iio_eq hd, setLIntegral_congr (Ioo_ae_eq_Ioc (μ := volume) (a := 0)),
    ← Iic_inter_Ioi, ← setLIntegral_indicator measurableSet_Iic]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun p (hp : 0 < p) ↦ ?_
  have hpa : p ≤ a / d ↔ d * p ≤ a := by rw [le_div_iff₀ hd, mul_comm]
  by_cases h : p ≤ a / d
  · rw [indicator_of_mem (show c - d * p ∈ Icc (c - a) (c + a) from
      ⟨by linarith [hpa.1 h], by linarith [hpa.1 h, mul_pos hd hp]⟩),
      indicator_of_mem (show p ∈ Iic (a / d) from h), sub_sub_cancel, mul_div_cancel_left₀ _ hd.ne']
  · rw [indicator_of_notMem fun h' ↦ h (hpa.2 (by linarith [h'.1])),
      indicator_of_notMem (show p ∉ Iic (a / d) from h)]

/-- The horizontal reflection costs `C |2 (c - y₁)|^{1/2}` for a horizontal seminorm `C`. -/
theorem abs_sub_verticalReflection_le {S : Set (ℝ^2)} {W : ℝ^2 → ℝ} {C : ℝ≥0}
    (hC : HolderSpace.directionalSeminorm 0 (1 / 2) S W ≤ C) {c : ℝ} {y : ℝ^2} (hy : y ∈ S)
    (hRy : verticalReflection c y ∈ S) :
    |W y - W (verticalReflection c y)| ≤ C * |2 * (c - y 0)| ^ (1 / 2 : ℝ) := by
  have hfin : HolderSpace.directionalSeminorm 0 (1 / 2) S W ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hC
  have h := HolderSpace.dist_le_directionalSeminorm_mul (i := 0) (α := 1 / 2) hfin hy hRy
    (fun j hj ↦ by
      fin_cases j
      · exact absurd rfl hj
      · exact (verticalReflection_one _ _).symm)
  rw [Real.dist_eq, verticalReflection_zero] at h
  calc |W y - W (verticalReflection c y)|
      ≤ (HolderSpace.directionalSeminorm 0 (1 / 2) S W).toReal *
          |y 0 - (2 * c - y 0)| ^ ((1 / 2 : ℝ≥0) : ℝ) := h
    _ ≤ C * |y 0 - (2 * c - y 0)| ^ ((1 / 2 : ℝ≥0) : ℝ) :=
        mul_le_mul_of_nonneg_right (ENNReal.toReal_le_coe_of_le_coe hC) (by positivity)
    _ = C * |2 * (c - y 0)| ^ (1 / 2 : ℝ) := by
        rw [show y 0 - (2 * c - y 0) = -(2 * (c - y 0)) by ring, abs_neg]
        norm_num

/-- **Chen and Hou, Part I, Lemma 3.3**, for the reflected integrals. Let `x, z` lie on a
vertical line with `x₂ ≠ z₂`, let `b ≥ |x₂ - z₂| / 2`, and let `W` be measurable with horizontal
`1/2`-Hölder seminorm at most `C_x` on `Q(x) ∪ Q(z)` and vertical `1/2`-Hölder seminorm at most
`C_y` on the part of `Q(x) ∪ Q(z)` above the midpoint height. With `P(x)` the reflected
integral of `K(x - ·) W` over `Q_{a,b,b}(x)` (the principal value when `W` is also integrable on
the boxes, `abs_sub_div_le_vertical_of_tendsto`),
`|P(x) - P(z)| / (π |x - z|^{1/2}) ≤ (1/2) C₁(a/|x - z|) C_y + C₂(a/|x - z|) C_x`. -/
theorem abs_sub_div_le_vertical (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4) {W : ℝ^2 → ℝ}
    {x z : ℝ^2} (hxz : x 0 = z 0) (hne : x 1 ≠ z 1) (hb : |x 1 - z 1| / 2 ≤ b)
    (hWm : AEStronglyMeasurable W) {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b b x ∪ box a b b z) W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a b b x ∪ box a b b z) ∩ {y | (x 1 + z 1) / 2 ≤ y 1}) W ≤ Cy) :
    ENNReal.ofReal (|reflectedIntegral K W (box a b b x) x -
        reflectedIntegral K W (box a b b z) z| / (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ))) ≤
      strainConstant (a / |x 1 - z 1|) / 2 * Cy + strainCrossConstant (a / |x 1 - z 1|) * Cx := by
  wlog hlt : x 1 < z 1 generalizing x z
  · have hlt' : z 1 < x 1 := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
    have := this hxz.symm hne.symm (by rwa [abs_sub_comm]) (by rwa [union_comm])
      (by rwa [union_comm, add_comm]) hlt'
    rwa [abs_sub_comm (reflectedIntegral K W (box a b b z) z), abs_sub_comm (z 1)] at this
  set d := z 1 - x 1 with hd_def
  have hd0 : 0 < d := sub_pos.2 hlt
  have habs : |x 1 - z 1| = d := by rw [abs_sub_comm]; exact abs_of_pos hd0
  rw [habs] at hb ⊢
  set m := (x 1 + z 1) / 2 with hm
  set A := a / d with hA
  set H : Set (ℝ^2) := {y | y 0 < (x 0)} with hH
  set L : Set (ℝ^2) := {y | y 1 < m} with hL
  have hHm : MeasurableSet H := measurableSet_lt_coord (x 0)
  have hLm : MeasurableSet L := measurableSet_lt (by fun_prop) measurable_const
  set D : ℝ^2 → ℝ := fun y ↦
    boxKernelDifference K a b b x z y * (W y - W (verticalReflection (x 0) y)) with hD
  -- the reflected integrands
  have hCx₁ := (HolderSpace.directionalSeminorm_mono (subset_union_left (s := box a b b x)
    (t := box a b b z))).trans hCx
  have hCx₂ := (HolderSpace.directionalSeminorm_mono (subset_union_right (s := box a b b x)
    (t := box a b b z))).trans hCx
  have hGx := integrableOn_kernel_mul_sub hK (measurableSet_box x)
    (fun _ hy ↦ verticalReflection_mem_box hy) (isBounded_box x) hWm hCx₁
  have hGz := integrableOn_kernel_mul_sub hK (measurableSet_box z)
    (fun _ hy ↦ verticalReflection_mem_box hy) (isBounded_box z) hWm hCx₂
  rw [← hxz] at hGz
  have hDeq : (box a b b x ∩ H).indicator
        (fun y ↦ K (x - y) * (W y - W (verticalReflection (x 0) y))) -
      (box a b b z ∩ H).indicator
        (fun y ↦ K (z - y) * (W y - W (verticalReflection (x 0) y))) =
      H.indicator D := by
    ext y
    by_cases hy : y ∈ H
    · by_cases hx : y ∈ box a b b x <;> by_cases hz : y ∈ box a b b z <;>
        simp only [Pi.sub_apply, indicator, mem_inter_iff, hy, hx, hz, and_true,
          ite_true, ite_false, D, boxKernelDifference] <;> ring
    · simp [indicator, hy]
  have hDi : IntegrableOn D H := (integrable_indicator_iff hHm).1 (hDeq ▸
    (hGx.integrable_indicator ((measurableSet_box x).inter hHm)).sub
      (hGz.integrable_indicator ((measurableSet_box z).inter hHm)))
  have hdiff : reflectedIntegral K W (box a b b x) x - reflectedIntegral K W (box a b b z) z =
      ∫ y in H, D y := by
    rw [reflectedIntegral, reflectedIntegral, ← hxz,
      ← integral_indicator ((measurableSet_box x).inter hHm),
      ← integral_indicator ((measurableSet_box z).inter hHm),
      ← integral_sub (hGx.integrable_indicator ((measurableSet_box x).inter hHm))
        (hGz.integrable_indicator ((measurableSet_box z).inter hHm)),
      ← integral_indicator hHm]
    exact congrArg (fun f : ℝ^2 → ℝ ↦ ∫ y, f y) hDeq
  rw [hdiff, ← integral_inter_add_sdiff hLm hDi]
  -- coordinates
  have hmp := measurePreserving_planeEquiv.symm
  have hemb := planeEquiv.symm.measurableEmbedding
  have hpreL : planeEquiv.symm ⁻¹' (H ∩ L) = Iio (x 0) ×ˢ Iio m := by
    ext q
    simp [planeEquiv_symm_apply, H, L]
  have hpreU : planeEquiv.symm ⁻¹' (H \ L) = Iio (x 0) ×ˢ Ici m := by
    ext q
    simp [planeEquiv_symm_apply, H, L]
  -- the lower part
  set N : ℝ → ℝ≥0∞ := fun p ↦ ∫⁻ q in Ioi 0, ENNReal.ofReal |strainDifference q p|
  have hlow : ENNReal.ofReal |∫ y in H ∩ L, D y| ≤ ENNReal.ofReal (Real.sqrt 2 * d ^ (1 / 2 : ℝ)) *
      (∫⁻ p in Ioo 0 A, ENNReal.ofReal (p ^ (1 / 2 : ℝ)) * N p) * Cx := by
    set F : ℝ^2 → ℝ≥0∞ := fun y ↦ ENNReal.ofReal |boxKernelDifference K a b b x z y| *
      (Cx * ENNReal.ofReal ((2 * (x 0 - y 0)) ^ (1 / 2 : ℝ))) with hF
    have hFm : Measurable F := by
      have := measurable_boxKernelDifference (a := a) hK b b x z
      fun_prop
    have hpt : ∀ y ∈ H ∩ L, ‖D y‖ₑ ≤ F y := fun y hy ↦ by
      have hy0 : y 0 < x 0 := hy.1
      simp only [D, F, enorm_mul, Real.enorm_eq_ofReal_abs]
      by_cases hyS : y ∈ box a b b x ∪ box a b b z
      · gcongr
        have hRy : verticalReflection (x 0) y ∈ box a b b x ∪ box a b b z :=
          hyS.imp verticalReflection_mem_box fun h ↦ hxz ▸ verticalReflection_mem_box h
        have h := abs_sub_verticalReflection_le hCx hyS hRy
        rw [abs_of_pos (by linarith : 0 < 2 * (x 0 - y 0))] at h
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        exact ENNReal.ofReal_le_ofReal h
      · rw [boxKernelDifference_eq_zero hyS, abs_zero, ENNReal.ofReal_zero, zero_mul, zero_mul]
    have hprod : ∫⁻ y in H ∩ L, F y = ∫⁻ s in Iio (x 0), ∫⁻ t in Iio m, F !₂[s, t] := by
      rw [← hmp.setLIntegral_comp_preimage_emb hemb, hpreL, Measure.volume_eq_prod,
        setLIntegral_prod (fun q ↦ F (planeEquiv.symm q))
          (hFm.comp planeEquiv.symm.measurable).aemeasurable]
      simp only [planeEquiv_symm_apply]
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ y in H ∩ L, ‖D y‖ₑ
        ≤ ∫⁻ y in H ∩ L, F y := setLIntegral_mono' (hHm.inter hLm) hpt
      _ = ∫⁻ s in Iio (x 0), ∫⁻ t in Iio m, F !₂[s, t] := hprod
      _ ≤ ∫⁻ s in Iio (x 0), (Icc (x 0 - a) (x 0 + a)).indicator (fun s ↦
            ENNReal.ofReal (1 / d) * N ((x 0 - s) / d) *
              (Cx * ENNReal.ofReal ((2 * (d * ((x 0 - s) / d))) ^ (1 / 2 : ℝ)))) s := by
          refine setLIntegral_mono' measurableSet_Iio fun s hs ↦ ?_
          simp only [F, Matrix.cons_val_zero]
          rw [lintegral_mul_const' _ _ (by simp [ENNReal.mul_eq_top]), indicator_mul_left,
            mul_div_cancel₀ _ hd0.ne']
          gcongr
          exact lintegral_lower_le hK hxz hlt hb (mem_Iio.1 hs)
      _ = ENNReal.ofReal d * ∫⁻ p in Ioo 0 A, ENNReal.ofReal (1 / d) * N p *
            (Cx * ENNReal.ofReal ((2 * (d * p)) ^ (1 / 2 : ℝ))) :=
          setLIntegral_Iio_indicator_eq hd0 _ _ fun p ↦ ENNReal.ofReal (1 / d) * N p *
            (Cx * ENNReal.ofReal ((2 * (d * p)) ^ (1 / 2 : ℝ)))
      _ = ENNReal.ofReal (Real.sqrt 2 * d ^ (1 / 2 : ℝ)) *
            (∫⁻ p in Ioo 0 A, ENNReal.ofReal (p ^ (1 / 2 : ℝ)) * N p) * Cx := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            ← lintegral_mul_const' _ _ ENNReal.coe_ne_top]
          refine setLIntegral_congr_fun measurableSet_Ioo fun p hp ↦ ?_
          have e : ENNReal.ofReal d * (ENNReal.ofReal (1 / d) *
              ENNReal.ofReal ((2 * (d * p)) ^ (1 / 2 : ℝ))) =
              ENNReal.ofReal (Real.sqrt 2 * d ^ (1 / 2 : ℝ)) *
                ENNReal.ofReal (p ^ (1 / 2 : ℝ)) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd0.le,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [Real.mul_rpow (by norm_num) (mul_pos hd0 hp.1).le, Real.mul_rpow hd0.le hp.1.le,
              ← Real.sqrt_eq_rpow]
            field_simp
          calc ENNReal.ofReal d * (ENNReal.ofReal (1 / d) * N p *
                (Cx * ENNReal.ofReal ((2 * (d * p)) ^ (1 / 2 : ℝ))))
              = (ENNReal.ofReal d * (ENNReal.ofReal (1 / d) *
                  ENNReal.ofReal ((2 * (d * p)) ^ (1 / 2 : ℝ)))) * N p * Cx := by ring
            _ = _ := by rw [e]; ring
  -- the upper part
  have hup : ENNReal.ofReal |∫ y in H \ L, D y| ≤
      2 * ENNReal.ofReal (d ^ (1 / 2 : ℝ)) * (∫⁻ p in Ioo 0 A, strainCost p) * Cy := by
    have hDU : IntegrableOn (fun q : ℝ × ℝ ↦ D !₂[q.1, q.2]) (Iio (x 0) ×ˢ Ici m) := by
      have h := (hmp.integrableOn_comp_preimage hemb (f := D) (s := H \ L)).2
        (hDi.mono_set sdiff_subset)
      rw [hpreU] at h
      simpa only [Function.comp_def, planeEquiv_symm_apply] using h
    have hrepr : ∫ y in H \ L, D y = ∫ s in Iio (x 0), ∫ t in Ici m, D !₂[s, t] := by
      rw [← hmp.setIntegral_preimage_emb hemb, hpreU, Measure.volume_eq_prod,
        setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
      simp only [planeEquiv_symm_apply]
    rw [hrepr, ← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hslice : ∀ s ∈ Iio (x 0), ‖∫ t in Ici m, D !₂[s, t]‖ₑ ≤
        (Icc (x 0 - a) (x 0 + a)).indicator (fun s ↦ 2 * Cy *
          ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) * strainCost ((x 0 - s) / d)) s := fun s hs ↦ by
      rw [Real.enorm_eq_ofReal_abs]
      have h := abs_integral_upper_le hK hxz hlt hb hCy (mem_Iio.1 hs) (W := W)
      simp only [D, verticalReflection_mk]
      exact h
    calc ∫⁻ s in Iio (x 0), ‖∫ t in Ici m, D !₂[s, t]‖ₑ
        ≤ ∫⁻ s in Iio (x 0), (Icc (x 0 - a) (x 0 + a)).indicator (fun s ↦ 2 * Cy *
            ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) * strainCost ((x 0 - s) / d)) s :=
          setLIntegral_mono' measurableSet_Iio hslice
      _ = ENNReal.ofReal d * ∫⁻ p in Ioo 0 A,
            2 * Cy * ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) * strainCost p :=
          setLIntegral_Iio_indicator_eq hd0 _ _ fun p ↦
            2 * Cy * ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) * strainCost p
      _ = 2 * ENNReal.ofReal (d ^ (1 / 2 : ℝ)) * (∫⁻ p in Ioo 0 A, strainCost p) * Cy := by
          have : ENNReal.ofReal d * ENNReal.ofReal (d ^ (-(1 / 2 : ℝ))) =
              ENNReal.ofReal (d ^ (1 / 2 : ℝ)) := by
            rw [← ENNReal.ofReal_mul hd0.le, ← Real.rpow_one_add' hd0.le (by norm_num)]
            norm_num
          rw [lintegral_const_mul' _ _ (by simp [ENNReal.mul_eq_top]), ← this]
          ring
  -- assemble
  have hq : 0 < Real.pi * d ^ (1 / 2 : ℝ) := by positivity
  rw [ENNReal.ofReal_div_of_pos hq]
  have hsum : ENNReal.ofReal |(∫ y in H ∩ L, D y) + ∫ y in H \ L, D y| ≤
      ENNReal.ofReal |∫ y in H ∩ L, D y| + ENNReal.ofReal |∫ y in H \ L, D y| :=
    (ENNReal.ofReal_le_ofReal (abs_add_le _ _)).trans_eq (ENNReal.ofReal_add (abs_nonneg _)
      (abs_nonneg _))
  have hπ : ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.2 hq).ne'
  have e₁ : ENNReal.ofReal (Real.sqrt 2 * d ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) * ENNReal.ofReal (Real.sqrt 2 / Real.pi) := by
    rw [← ENNReal.ofReal_mul hq.le]
    congr 1
    field_simp
  have e₂ : 2 * ENNReal.ofReal (d ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) * (ENNReal.ofReal (4 / Real.pi) / 2) := by
    have h2 : ENNReal.ofReal (4 / Real.pi) / 2 = ENNReal.ofReal (2 / Real.pi) := by
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      congr 1
      ring
    rw [h2, ← ENNReal.ofReal_mul hq.le, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    field_simp
  calc ENNReal.ofReal |(∫ y in H ∩ L, D y) + ∫ y in H \ L, D y| /
        ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ))
      ≤ (ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) *
            (strainConstant A / 2 * Cy + strainCrossConstant A * Cx)) /
          ENNReal.ofReal (Real.pi * d ^ (1 / 2 : ℝ)) := by
        gcongr
        refine hsum.trans ((add_le_add hlow hup).trans_eq ?_)
        rw [e₁, e₂, strainConstant, strainCrossConstant]
        simp only [div_eq_mul_inv]
        ring
    _ = strainConstant A / 2 * Cy + strainCrossConstant A * Cx := by
        rw [mul_comm]
        exact ENNReal.mul_div_cancel_right hπ ENNReal.ofReal_ne_top

/-- **Chen and Hou, Part I, Lemma 3.3**, for the principal values: under the hypotheses of
`abs_sub_div_le_vertical`, with `W` also integrable on the two boxes, the ball truncations
converge and their limits `P(x)`, `P(z)` satisfy
`|P(x) - P(z)| / (π |x - z|^{1/2}) ≤ (1/2) C₁(a/|x - z|) C_y + C₂(a/|x - z|) C_x`. -/
theorem abs_sub_div_le_vertical_of_tendsto (hK : ∀ y, K y = y 0 * y 1 / ‖y‖ ^ 4)
    {W : ℝ^2 → ℝ} {x z : ℝ^2} (hxz : x 0 = z 0) (hne : x 1 ≠ z 1) (hb : |x 1 - z 1| / 2 ≤ b)
    (hWm : AEStronglyMeasurable W) (hWi : IntegrableOn W (box a b b x ∪ box a b b z))
    {Cx Cy : ℝ≥0}
    (hCx : HolderSpace.directionalSeminorm 0 (1 / 2) (box a b b x ∪ box a b b z) W ≤ Cx)
    (hCy : HolderSpace.directionalSeminorm 1 (1 / 2)
      ((box a b b x ∪ box a b b z) ∩ {y | (x 1 + z 1) / 2 ≤ y 1}) W ≤ Cy)
    {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in box a b b x \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in box a b b z \ ball z ε, K (z - y) * W y) (𝓝[>] 0)
      (𝓝 vz)) :
    ENNReal.ofReal (|vx - vz| / (Real.pi * |x 1 - z 1| ^ (1 / 2 : ℝ))) ≤
      strainConstant (a / |x 1 - z 1|) / 2 * Cy + strainCrossConstant (a / |x 1 - z 1|) * Cx := by
  have hx := tendsto_setIntegral_diff_ball hK (measurableSet_box x)
    (fun _ hy ↦ verticalReflection_mem_box hy) (isBounded_box x) hWm
    (hWi.mono_set subset_union_left)
    ((HolderSpace.directionalSeminorm_mono subset_union_left).trans hCx)
  have hz := tendsto_setIntegral_diff_ball hK (measurableSet_box z)
    (fun _ hy ↦ verticalReflection_mem_box hy) (isBounded_box z) hWm
    (hWi.mono_set subset_union_right)
    ((HolderSpace.directionalSeminorm_mono subset_union_right).trans hCx)
  rw [tendsto_nhds_unique hvx hx, tendsto_nhds_unique hvz hz]
  exact abs_sub_div_le_vertical hK hxz hne hb hWm hCx hCy

end IncompressibleFlow.SharpHolder
