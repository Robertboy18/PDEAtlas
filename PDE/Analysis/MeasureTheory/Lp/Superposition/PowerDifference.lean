/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ENNReal.Holder
public import PDE.Analysis.MeasureTheory.Lp.PowerSuperposition
public import PDE.Analysis.MeasureTheory.Lp.Superposition.WeightedDifference
import Mathlib.Tactic.Positivity.Finset

/-!
# Difference estimates for power-growth superposition operators

Hölder products turn pointwise difference bounds into norm estimates between
Lebesgue spaces. In particular, the resulting nonlinear maps are Lipschitz on
bounded balls.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A two-point power bound becomes an `Lp → L(p/r)` difference estimate
at every finite input exponent at least one. The nonlinear map may have an
offset; only output integrability and the difference bound enter the estimate.
The target exponent is given through an equality `p / r = q`. -/
theorem norm_superposition_sub_le_of_twoPointGrowth
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] {r C : ℝ}
    (hp : p ≠ ∞) (hr : 1 < r) (hq : p / ENNReal.ofReal r = q)
    (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hmem : ∀ u : Lp ℝ p μ, MemLp (fun x ↦ g (u x)) q μ)
    (hg : ∀ x y, ‖g x - g y‖ ≤
      C * (‖x‖ + ‖y‖) ^ (r - 1) * ‖x - y‖)
    (u v : Lp ℝ p μ) :
    ‖superposition (fun _ ↦ g) hmem u - superposition (fun _ ↦ g) hmem v‖ ≤
      C * (‖u‖ + ‖v‖) ^ (r - 1) * ‖u - v‖ := by
  have hs : 0 < r - 1 := sub_pos.mpr hr
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have : ENNReal.HolderTriple (p / ENNReal.ofReal (r - 1)) p q := by
    rw [← hq]
    exact ENNReal.holderTriple_div_ofReal hp0 hp hr
  let A : Lp ℝ p μ :=
    lipschitzWith_one_norm.compLp (_root_.norm_zero) u +
      lipschitzWith_one_norm.compLp (_root_.norm_zero) v
  let D : Lp ℝ p μ := lipschitzWith_one_norm.compLp (_root_.norm_zero) (u - v)
  let W : Lp ℝ q μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holder q (normRpow hs.le A) D
  have hA : A =ᵐ[μ] fun x ↦ ‖u x‖ + ‖v x‖ := by
    filter_upwards [Lp.coeFn_add
      (lipschitzWith_one_norm.compLp (_root_.norm_zero) u)
      (lipschitzWith_one_norm.compLp (_root_.norm_zero) v),
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) u,
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) v] with x hx hu hv
    simp only [A, hx, Pi.add_apply, hu, hv, Function.comp_apply]
  have hW : W =ᵐ[μ] fun x ↦ (‖u x‖ + ‖v x‖) ^ (r - 1) * ‖u x - v x‖ := by
    filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := q)
        (normRpow hs.le A) D,
      coeFn_normRpow hs.le A, hA,
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) (u - v),
      Lp.coeFn_sub u v] with x hw ha hax hd hsub
    simp only [W, hw, ContinuousLinearMap.mul_apply', ha, hax,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg (u x)) (norm_nonneg (v x))), D, hd,
      Function.comp_apply, hsub, Pi.sub_apply]
  have hN :
      ‖superposition (fun _ ↦ g) hmem u - superposition (fun _ ↦ g) hmem v‖ ≤
        C * ‖W‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [Lp.coeFn_sub (superposition (fun _ ↦ g) hmem u)
        (superposition (fun _ ↦ g) hmem v),
      coeFn_superposition (fun _ ↦ g) hmem u,
      coeFn_superposition (fun _ ↦ g) hmem v, hW] with x hsub hu hv hw
    rw [hsub, Pi.sub_apply, hu, hv, hw, norm_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg
        (add_nonneg (norm_nonneg _) (norm_nonneg _)) _), norm_norm, ← mul_assoc]
    exact hg (u x) (v x)
  have hA_norm : ‖A‖ ≤ ‖u‖ + ‖v‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      (by simpa using lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero) u)
      (by simpa using lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero) v))
  have hD_norm : ‖D‖ ≤ ‖u - v‖ := by
    simpa [D] using lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero) (u - v)
  have hW_norm : ‖W‖ ≤ (‖u‖ + ‖v‖) ^ (r - 1) * ‖u - v‖ := by
    calc
      ‖W‖ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖normRpow hs.le A‖ * ‖D‖ :=
        (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le _ _
      _ ≤ 1 * ‖normRpow hs.le A‖ * ‖D‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)
            (show 0 ≤ ‖normRpow hs.le A‖ from ENNReal.toReal_nonneg)) (norm_nonneg D)
      _ = ‖A‖ ^ (r - 1) * ‖D‖ := by rw [one_mul, norm_normRpow hs]
      _ ≤ (‖u‖ + ‖v‖) ^ (r - 1) * ‖u - v‖ :=
        mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) hA_norm hs.le) hD_norm
          (norm_nonneg _) (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)
  exact hN.trans ((mul_le_mul_of_nonneg_left hW_norm hC).trans_eq (by ring))

/-- On a finite measure space, an additive constant in a power difference bound
contributes its full finite-measure norm. In particular, this estimate retains
the constant part of a derivative-growth bound. -/
theorem norm_superposition_sub_le_of_twoPointGrowth_add_const
    [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] {r C K : ℝ}
    [Fact (1 ≤ p / ENNReal.ofReal (r - 1))]
    (hp : p ≠ ∞) (hr : 1 < r) (hq : p / ENNReal.ofReal r = q)
    (hC : 0 ≤ C) (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hmem : ∀ u : Lp ℝ p μ, MemLp (fun x ↦ g (u x)) q μ)
    (hg : ∀ x y, ‖g x - g y‖ ≤
      (K + C * (‖x‖ + ‖y‖) ^ (r - 1)) * ‖x - y‖)
    (u v : Lp ℝ p μ) :
    ‖superposition (fun _ ↦ g) hmem u - superposition (fun _ ↦ g) hmem v‖ ≤
      (K * (μ Set.univ).toReal ^ ((r - 1) / p.toReal) +
        C * (‖u‖ + ‖v‖) ^ (r - 1)) * ‖u - v‖ := by
  have hs : 0 < r - 1 := sub_pos.mpr hr
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have : ENNReal.HolderTriple (p / ENNReal.ofReal (r - 1)) p q := by
    rw [← hq]
    exact ENNReal.holderTriple_div_ofReal hp0 hp hr
  let A : Lp ℝ p μ :=
    lipschitzWith_one_norm.compLp (_root_.norm_zero) u +
      lipschitzWith_one_norm.compLp (_root_.norm_zero) v
  let b : Lp ℝ (p / ENNReal.ofReal (r - 1)) μ := (memLp_const K).toLp _
  let a := b + C • normRpow hs.le A
  have hA : A =ᵐ[μ] fun x ↦ ‖u x‖ + ‖v x‖ := by
    filter_upwards [Lp.coeFn_add
      (lipschitzWith_one_norm.compLp (_root_.norm_zero) u)
      (lipschitzWith_one_norm.compLp (_root_.norm_zero) v),
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) u,
      lipschitzWith_one_norm.coeFn_compLp (_root_.norm_zero) v] with x hx hu hv
    simp only [A, hx, Pi.add_apply, hu, hv, Function.comp_apply]
  have ha : a =ᵐ[μ] fun x ↦ K + C * (‖u x‖ + ‖v x‖) ^ (r - 1) := by
    filter_upwards [Lp.coeFn_add b (C • normRpow hs.le A),
      (memLp_const (μ := μ) (p := p / ENNReal.ofReal (r - 1)) K).coeFn_toLp,
      Lp.coeFn_smul C (normRpow hs.le A), coeFn_normRpow hs.le A, hA]
      with x hx hb hc hrpow hax
    simp only [a, hx, Pi.add_apply, b, hb, hc, Pi.smul_apply, smul_eq_mul, hrpow, hax,
      Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hb : ‖b‖ = K * (μ Set.univ).toReal ^ ((r - 1) / p.toReal) := by
    have ht0 : p / ENNReal.ofReal (r - 1) ≠ 0 :=
      ENNReal.div_ne_zero.mpr ⟨hp0, ENNReal.ofReal_ne_top⟩
    have httop : p / ENNReal.ofReal (r - 1) ≠ ∞ :=
      ENNReal.div_ne_top hp (by positivity)
    rw [norm_toLp, eLpNorm_const' _ ht0 httop, ENNReal.toReal_mul,
      ENNReal.toReal_rpow, toReal_enorm, Real.norm_of_nonneg hK,
      ENNReal.toReal_div, ENNReal.toReal_ofReal hs.le, one_div_div]
  have hA_norm : ‖A‖ ≤ ‖u‖ + ‖v‖ :=
    (norm_add_le _ _).trans (add_le_add
      (by simpa using lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero) u)
      (by simpa using lipschitzWith_one_norm.norm_compLp_le (_root_.norm_zero) v))
  have ha_norm : ‖a‖ ≤ K * (μ Set.univ).toReal ^ ((r - 1) / p.toReal) +
      C * (‖u‖ + ‖v‖) ^ (r - 1) := by
    calc
      ‖a‖ ≤ ‖b‖ + ‖C • normRpow hs.le A‖ := norm_add_le _ _
      _ = K * (μ Set.univ).toReal ^ ((r - 1) / p.toReal) +
          C * ‖A‖ ^ (r - 1) := by
        rw [hb, norm_smul, Real.norm_of_nonneg hC, norm_normRpow hs]
      _ ≤ _ := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hA_norm hs.le) hC)
  apply (norm_superposition_sub_le_of_weighted_bound (fun _ ↦ g) hmem u v a ?_).trans
    (mul_le_mul_of_nonneg_right ha_norm (norm_nonneg _))
  filter_upwards [ha] with x hx
  rw [hx, Real.norm_of_nonneg (add_nonneg hK
    (mul_nonneg hC (Real.rpow_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) _)))]
  exact hg (u x) (v x)

/-- Additive power difference bounds give Lipschitz constants on every bounded
ball in the input space. The measure term remains present even at small radii. -/
theorem lipschitzOnWith_superposition_of_twoPointGrowth_add_const
    [IsFiniteMeasure μ] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r C K : ℝ}
    [Fact (1 ≤ p / ENNReal.ofReal (r - 1))]
    (hp : p ≠ ∞) (hr : 1 < r) (hq : p / ENNReal.ofReal r = q)
    (hC : 0 ≤ C) (hK : 0 ≤ K) {g : ℝ → ℝ}
    (hmem : ∀ u : Lp ℝ p μ, MemLp (fun x ↦ g (u x)) q μ)
    (hg : ∀ x y, ‖g x - g y‖ ≤
      (K + C * (‖x‖ + ‖y‖) ^ (r - 1)) * ‖x - y‖)
    {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith
      ⟨K * (μ Set.univ).toReal ^ ((r - 1) / p.toReal) + C * (2 * R) ^ (r - 1),
        by positivity⟩
      (superposition (fun _ ↦ g) hmem) (Metric.closedBall 0 R) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
  simp only [Metric.mem_closedBall, dist_zero_right] at hu hv
  simp only [_root_.dist_eq_norm]
  apply (norm_superposition_sub_le_of_twoPointGrowth_add_const
    hp hr hq hC hK hmem hg u v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (add_nonneg (norm_nonneg _) (norm_nonneg _))
      (by linarith : ‖u‖ + ‖v‖ ≤ 2 * R) (sub_nonneg.mpr hr.le)) hC)

/-- A continuous scalar map vanishing at zero and satisfying a power
two-point bound maps `L^(2r)` into `L²`, on an arbitrary measure space. -/
theorem memLp_comp_of_twoPointGrowth
    {r C : ℝ} (hr : 1 < r) {g : ℝ → ℝ}
    (hcont : Continuous g) (hzero : g 0 = 0)
    (hg : ∀ x y, ‖g x - g y‖ ≤
      C * (‖x‖ + ‖y‖) ^ (r - 1) * ‖x - y‖)
    (u : Lp ℝ (ENNReal.ofReal (2 * r)) μ) :
    MemLp (fun x ↦ g (u x)) 2 μ := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hpow : MemLp (fun x ↦ ‖u x‖ ^ r) 2 μ := by
    have he : ENNReal.ofReal (2 * r) / ENNReal.ofReal r = 2 := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
        ENNReal.mul_div_cancel_right (by positivity) ENNReal.ofReal_ne_top]
    simpa only [ENNReal.toReal_ofReal hr0.le, he] using
      (Lp.memLp u).norm_rpow_div (ENNReal.ofReal r)
  refine (hpow.const_mul C).mono'
    (hcont.comp_aestronglyMeasurable (Lp.memLp u).aestronglyMeasurable) ?_
  filter_upwards with x
  have hx := hg (u x) (0 : ℝ)
  have hz : ‖(0 : ℝ)‖ = 0 := _root_.norm_zero
  simp only [hzero, sub_zero, hz, add_zero] at hx
  by_cases hu : u x = 0
  · simp [hu, hzero, Real.zero_rpow hr0.ne']
  · have hn : 0 < ‖u x‖ := norm_pos_iff.mpr hu
    have he : ‖u x‖ ^ (r - 1) * ‖u x‖ = ‖u x‖ ^ r := by
      rw [Real.rpow_sub_one hn.ne']
      field_simp
    simpa only [mul_assoc, he] using hx

/-- The preceding norm estimate gives Lipschitz bounds on every input
ball, with an explicit constant. -/
theorem lipschitzOnWith_superposition_of_twoPointGrowth
    {r C : ℝ} [Fact (1 ≤ ENNReal.ofReal (2 * r))]
    (hr : 1 < r) (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hmem : ∀ u : Lp ℝ (ENNReal.ofReal (2 * r)) μ,
      MemLp (fun x ↦ g (u x)) 2 μ)
    (hg : ∀ x y, ‖g x - g y‖ ≤
      C * (‖x‖ + ‖y‖) ^ (r - 1) * ‖x - y‖)
    {R : ℝ} (hR : 0 ≤ R) :
    LipschitzOnWith
      ⟨C * (2 * R) ^ (r - 1), mul_nonneg hC (Real.rpow_nonneg (by positivity) _)⟩
      (superposition (fun _ ↦ g) hmem)
      (Metric.closedBall (0 : Lp ℝ (ENNReal.ofReal (2 * r)) μ) R) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ ?_
  simp only [Metric.mem_closedBall, dist_zero_right] at hu hv
  simp only [_root_.dist_eq_norm]
  have hsum : ‖u‖ + ‖v‖ ≤ 2 * R := by linarith
  have hq : ENNReal.ofReal (2 * r) / ENNReal.ofReal r = 2 := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.mul_div_cancel_right (by positivity) ENNReal.ofReal_ne_top]
  exact (norm_superposition_sub_le_of_twoPointGrowth
    ENNReal.ofReal_ne_top hr hq hC hmem hg u v).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (add_nonneg (norm_nonneg _) (norm_nonneg _))
          hsum (sub_nonneg.mpr hr.le)) hC) (norm_nonneg _))

end MeasureTheory.Lp
