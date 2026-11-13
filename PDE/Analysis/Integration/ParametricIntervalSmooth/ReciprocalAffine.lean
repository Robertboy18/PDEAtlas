/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Primitive.MovingEndpoint
import CAS.ExactTactic

/-!
# Reciprocal interval integrals with a parameter

Compact nonvanishing gives one parameter window and a positive denominator
margin on the whole integration segment. `hasFDerivAt_intervalIntegral_of_continuousOn`
and `contDiffOn_intervalIntegral_moving_upper` then give the parameter derivative and
joint regularity with a moving endpoint.
An inner endpoint interval gives ordinary smoothness at its boundaries.
The integrals retain their orientation, and all coefficient assumptions are local.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Analysis

/-- Nonvanishing on a compact index set persists with a uniform positive
margin on a closed parameter window. No sign of either coefficient is assumed. -/
private theorem exists_pos_le_abs_reciprocal_affine_denominator
    {T : Type*} [TopologicalSpace T] {K : Set T} {d c : T → ℝ}
    (hK : IsCompact K) (hd : ContinuousOn d K) (hc : ContinuousOn c K)
    (hne : ∀ v ∈ K, d v ≠ 0) :
    ∃ ε > 0, ∃ η > 0, ∀ μ ∈ Icc (-ε) ε, ∀ v ∈ K,
      η ≤ |d v + μ * c v| := by
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_forall_le' hd.abs
    (fun v hv ↦ abs_pos.mpr (hne v hv))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  let B : ℝ := max C 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  have hcB (v : T) (hv : v ∈ K) : |c v| ≤ B := by
    have hvC : |c v| ≤ C := by simpa only [Real.norm_eq_abs] using hC v hv
    exact hvC.trans (le_max_left C 1)
  have hε : 0 < δ / (2 * B) := div_pos hδ (mul_pos zero_lt_two hB)
  refine ⟨δ / (2 * B), hε, δ / 2, half_pos hδ, ?_⟩
  intro μ hμ v hv
  have hμabs : |μ| ≤ δ / (2 * B) := abs_le.mpr hμ
  have hperturb : |μ * c v| ≤ δ / 2 := by
    calc
      |μ * c v| = |μ| * |c v| := abs_mul μ (c v)
      _ ≤ (δ / (2 * B)) * B :=
        mul_le_mul hμabs (hcB v hv) (abs_nonneg (c v)) hε.le
      _ = δ / 2 := by rw [← div_div, div_mul_cancel₀ _ hB.ne']
  have htriangle : |d v| ≤ |d v + μ * c v| + |μ * c v| := by
    simpa only [Real.norm_eq_abs, add_sub_cancel_right] using
      norm_sub_le (d v + μ * c v) (μ * c v)
  linarith only [hδK v hv, hperturb, htriangle]

private theorem hasDerivAt_reciprocal_affine_scalar {d c μ : ℝ}
    (hne : d + μ * c ≠ 0) :
    HasDerivAt (fun ν : ℝ ↦ 1 / (d + ν * c)) (-c / (d + μ * c) ^ 2) μ := by
  cas using hne

/-- Differentiate a reciprocal affine denominator over a signed compact segment.
Continuity is required only on `uIcc a b`, and nonvanishing only at the base
parameter `μ₀` on that segment. No ordering of the endpoints is required. -/
theorem hasDerivAt_intervalIntegral_reciprocal_affine
    {d c : ℝ → ℝ} {a b μ₀ : ℝ}
    (hd : ContinuousOn d (uIcc a b)) (hc : ContinuousOn c (uIcc a b))
    (hne : ∀ v ∈ uIcc a b, d v + μ₀ * c v ≠ 0) :
    HasDerivAt (fun μ : ℝ ↦ ∫ v in a..b, 1 / (d v + μ * c v))
      (∫ v in a..b, -c v / (d v + μ₀ * c v) ^ 2) μ₀ := by
  obtain ⟨ε, hε, η, hη, hsep⟩ :=
    exists_pos_le_abs_reciprocal_affine_denominator
      (d := fun v ↦ d v + μ₀ * c v) isCompact_uIcc
      (hd.add (continuousOn_const.mul hc)) hc hne
  let U : Set ℝ := Ioo (μ₀ - ε) (μ₀ + ε)
  have hU : IsOpen U := isOpen_Ioo
  have hμ₀ : μ₀ ∈ U := ⟨by linarith only [hε], by linarith only [hε]⟩
  have hnonzero : ∀ μ ∈ U, ∀ v ∈ uIcc a b, d v + μ * c v ≠ 0 := by
    intro μ hμ v hv
    have hshift : μ - μ₀ ∈ Icc (-ε) ε :=
      ⟨by linarith only [hμ.1], by linarith only [hμ.2]⟩
    have hbound := hsep (μ - μ₀) hshift v hv
    have heq : d v + μ₀ * c v + (μ - μ₀) * c v = d v + μ * c v := by
      generalize d v = a
      generalize c v = b
      cas
    rw [heq] at hbound
    exact abs_pos.mp (hη.trans_le hbound)
  have hdprod : ContinuousOn (fun p : ℝ × ℝ ↦ d p.2) (U ×ˢ uIcc a b) :=
    hd.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hcprod : ContinuousOn (fun p : ℝ × ℝ ↦ c p.2) (U ×ˢ uIcc a b) :=
    hc.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hden : ContinuousOn (fun p : ℝ × ℝ ↦ d p.2 + p.1 * c p.2)
      (U ×ˢ uIcc a b) :=
    hdprod.add (continuous_fst.continuousOn.mul hcprod)
  have hF : ContinuousOn (fun p : ℝ × ℝ ↦ 1 / (d p.2 + p.1 * c p.2))
      (U ×ˢ uIcc a b) :=
    continuousOn_const.div hden (fun p hp ↦ hnonzero p.1 hp.1 p.2 hp.2)
  have hjet : ContinuousOn
      (fun p : ℝ × ℝ ↦ -c p.2 / (d p.2 + p.1 * c p.2) ^ 2)
      (U ×ˢ uIcc a b) :=
    hcprod.neg.div (hden.pow 2)
      (fun p hp ↦ pow_ne_zero 2 (hnonzero p.1 hp.1 p.2 hp.2))
  let J : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun μ v ↦
    ContinuousLinearMap.toSpanSingleton ℝ (-c v / (d v + μ * c v) ^ 2)
  have hJ : ContinuousOn J.uncurry (U ×ˢ uIcc a b) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn hjet
  -- The PDE theorem bounds this continuous derivative family on a smaller
  -- parameter neighborhood, then applies Mathlib's dominated integral rule.
  have hi : HasFDerivAt (fun μ : ℝ ↦ ∫ v in a..b, 1 / (d v + μ * c v))
      (∫ v in a..b, J μ₀ v) μ₀ :=
    hasFDerivAt_intervalIntegral_of_continuousOn
      (F := fun μ v ↦ 1 / (d v + μ * c v)) (D := J) hU hF hJ
      (fun μ hμ v hv ↦
        (hasDerivAt_reciprocal_affine_scalar (hnonzero μ hμ v hv)).hasFDerivAt) hμ₀
  have hJint : IntervalIntegrable (J μ₀) volume a b :=
    (hJ.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hv ↦ ⟨hμ₀, hv⟩)).intervalIntegrable
  apply hi.hasDerivAt.congr_deriv
  rw [ContinuousLinearMap.intervalIntegral_apply hJint]
  simp only [J, ContinuousLinearMap.toSpanSingleton_apply_one]

/-- On an open parameter domain with nonzero denominators, local coefficient
regularity gives joint regularity of the primitive on the entire closed strip.
The anchor and endpoint need not be ordered. -/
private theorem contDiffOn_intervalIntegral_reciprocal_affine
    {n : ℕ∞} {d c : ℝ → ℝ} {a b base : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hd : ContDiffOn ℝ n d (uIcc a b))
    (hc : ContDiffOn ℝ n c (uIcc a b)) (hbase : base ∈ uIcc a b)
    (hne : ∀ μ ∈ U, ∀ v ∈ uIcc a b, d v + μ * c v ≠ 0) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ v in base..p.2, 1 / (d v + p.1 * c v))
      (U ×ˢ uIcc a b) := by
  have hdprod : ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ d p.2) (U ×ˢ uIcc a b) :=
    hd.comp contDiffOn_snd (fun _ hp ↦ hp.2)
  have hcprod : ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ c p.2) (U ×ˢ uIcc a b) :=
    hc.comp contDiffOn_snd (fun _ hp ↦ hp.2)
  have hden : ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ d p.2 + p.1 * c p.2)
      (U ×ˢ uIcc a b) :=
    hdprod.add (contDiffOn_fst.mul hcprod)
  have hrecip : ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ 1 / (d p.2 + p.1 * c p.2))
      (U ×ˢ uIcc a b) :=
    contDiffOn_const.div hden (fun p hp ↦ hne p.1 hp.1 p.2 hp.2)
  exact contDiffOn_intervalIntegral_moving_upper (n := n) hU hrecip hbase

/-- Construct a common parameter neighborhood, its denominator margin, and
joint regularity from coefficient regularity and nonvanishing at parameter zero.
In particular, take `n = ⊤` for infinite smoothness. -/
theorem exists_contDiffOn_intervalIntegral_reciprocal_affine
    {n : ℕ∞} {d c : ℝ → ℝ} {a b base : ℝ}
    (hd : ContDiffOn ℝ n d (uIcc a b)) (hc : ContDiffOn ℝ n c (uIcc a b))
    (hbase : base ∈ uIcc a b) (hne : ∀ v ∈ uIcc a b, d v ≠ 0) :
    ∃ ε > 0, ∃ η > 0,
      (∀ μ ∈ Icc (-ε) ε, ∀ v ∈ uIcc a b, η ≤ |d v + μ * c v|) ∧
      ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ v in base..p.2, 1 / (d v + p.1 * c v))
        (Ioo (-ε) ε ×ˢ uIcc a b) := by
  obtain ⟨ε, hε, η, hη, hsep⟩ :=
    exists_pos_le_abs_reciprocal_affine_denominator isCompact_uIcc
      hd.continuousOn hc.continuousOn hne
  have hnonzero : ∀ μ ∈ Ioo (-ε) ε, ∀ v ∈ uIcc a b,
      d v + μ * c v ≠ 0 := by
    intro μ hμ v hv
    exact abs_pos.mp (hη.trans_le (hsep μ (Ioo_subset_Icc_self hμ) v hv))
  exact ⟨ε, hε, η, hη, hsep,
    contDiffOn_intervalIntegral_reciprocal_affine isOpen_Ioo hd hc hbase hnonzero⟩

/-- Slack around both desired endpoints upgrades relative smoothness to
ordinary joint regularity, uniformly for the whole desired interval.
The endpoint interval `uIcc y₀ y₁` includes its boundary and either orientation.
No coefficient regularity or nonvanishing outside `Icc a b` is required. -/
theorem exists_contDiffAt_intervalIntegral_reciprocal_affine_of_slack
    {n : ℕ∞} {d c : ℝ → ℝ} {a b base y₀ y₁ : ℝ}
    (hd : ContDiffOn ℝ n d (Icc a b)) (hc : ContDiffOn ℝ n c (Icc a b))
    (hbase : base ∈ Icc a b) (hy₀ : y₀ ∈ Ioo a b) (hy₁ : y₁ ∈ Ioo a b)
    (hne : ∀ v ∈ Icc a b, d v ≠ 0) :
    ∃ ε > 0, ∃ η > 0,
      (∀ μ ∈ Icc (-ε) ε, ∀ v ∈ Icc a b, η ≤ |d v + μ * c v|) ∧
      ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ v in base..p.2, 1 / (d v + p.1 * c v))
        (Ioo (-ε) ε ×ˢ Icc a b) ∧
      ∀ μ ∈ Ioo (-ε) ε, ∀ y ∈ uIcc y₀ y₁,
        ContDiffAt ℝ n (fun p : ℝ × ℝ ↦ ∫ v in base..p.2, 1 / (d v + p.1 * c v)) (μ, y) := by
  have hab : a ≤ b := (hy₀.1.trans hy₀.2).le
  have hd' : ContDiffOn ℝ n d (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hd
  have hc' : ContDiffOn ℝ n c (uIcc a b) := by
    simpa only [uIcc_of_le hab] using hc
  have hbase' : base ∈ uIcc a b := mem_uIcc_of_le hbase.1 hbase.2
  have hne' : ∀ v ∈ uIcc a b, d v ≠ 0 := by
    simpa only [uIcc_of_le hab] using hne
  obtain ⟨ε, hε, η, hη, hsep, hsmooth⟩ :=
    exists_contDiffOn_intervalIntegral_reciprocal_affine (n := n) hd' hc' hbase' hne'
  have hclosed : ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ v in base..p.2, 1 / (d v + p.1 * c v))
      (Ioo (-ε) ε ×ˢ Icc a b) := by
    simpa only [uIcc_of_le hab] using hsmooth
  have hopen : ContDiffOn ℝ n (fun p : ℝ × ℝ ↦ ∫ v in base..p.2, 1 / (d v + p.1 * c v))
      (Ioo (-ε) ε ×ˢ Ioo a b) :=
    hclosed.mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  refine ⟨ε, hε, η, hη, ?_, hclosed, ?_⟩
  · simpa only [uIcc_of_le hab] using hsep
  · intro μ hμ y hy
    have hyinner : y ∈ Ioo a b := by
      rcases mem_uIcc.mp hy with h | h
      · exact ⟨hy₀.1.trans_le h.1, h.2.trans_lt hy₁.2⟩
      · exact ⟨hy₁.1.trans_le h.1, h.2.trans_lt hy₀.2⟩
    exact hopen.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hμ, hyinner⟩)

end PDE.Analysis
