/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import PDE.Analysis.MeasureTheory.Lp.DualMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integral representation of the real `Lp` dual over a finite measure

The indicator representation from `Lp.DualMeasure` extends first to simple functions and
then to bounded measurable tests by dominated convergence. Truncated signed powers give the
conjugate `Lq` estimate without assuming that power is integrable in advance.

Density of simple functions, `Lp.simpleFunc.denseRange`, and the continuity of Mathlib's
integral pairing `ContinuousLinearMap.lpPairing` then identify every bounded functional on
real `Lp` with an `Lq` density whose norm is at most its operator norm. The final
representation and pairing-surjectivity statements assume that the measure and both conjugate
exponents are finite. The test-function lemmas need fewer assumptions.

`exists_dualDensity` is the representation of the dual of `L^p(U)` in the Important Example
of Evans, App. D.4: each bounded linear functional on `L^p(U)` is `f ↦ ∫_U g f dx` for some
`g ∈ L^q(U)`. Ours is for a finite measure on any measurable space and for `1 < p < ∞`, and it
adds the bound `‖g‖ ≤ ‖Λ‖`; his case `p = 1`, `q = ∞` and open sets `U` of infinite measure
are not covered.

## Main results

* `eq_integral_simpleFunc_of_indicator_eq`, `eq_integral_of_indicator_eq_of_bounded`: an
  integrable density that represents `Λ` on indicators also represents it on simple functions
  and, for `p ≠ ∞`, on bounded measurable functions in `Lp`.
* `eLpNorm_le_opNorm_of_indicator_eq`: for finite `p` and `q`, a measurable such density has
  `Lq` seminorm at most `‖Λ‖`.
* `eq_lpPairing_of_indicator_eq`: if the density lies in `Lq`, `Λ` is its integral pairing.
* `exists_dualDensity`: every `Λ` is `f ↦ ∫ f g` for some `g` in `Lq` with `‖g‖ ≤ ‖Λ‖`.
* `surjective_lpPairing`: the integral pairing maps `Lq` onto the dual of `Lp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. D.4, the Important Example, pp. 723-724.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set Filter Function
open scoped ENNReal NNReal Topology symmDiff

namespace MeasureTheory
namespace Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An indicator representation of a bounded functional extends to simple functions. -/
theorem eq_integral_simpleFunc_of_indicator_eq
    (Λ : Lp ℝ p μ →L[ℝ] ℝ) {g : α → ℝ} (hg : Integrable g μ)
    (hset : ∀ (s : Set α) (hs : MeasurableSet s),
      Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, g x ∂μ)
    (f : SimpleFunc α ℝ) (hf : MemLp f p μ) :
    Λ (hf.toLp f) = ∫ x, f x * g x ∂μ := by
  classical
  revert hf
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    intro hf
    change MemLp (s.indicator fun _ ↦ c) p μ at hf
    change Λ (hf.toLp (s.indicator fun _ ↦ c)) =
      ∫ x, (s.indicator fun _ ↦ c) x * g x ∂μ
    have hLp : hf.toLp (s.indicator fun _ ↦ c) =
        c • indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ) := by
      apply Lp.ext
      filter_upwards [hf.coeFn_toLp,
        Lp.coeFn_smul c (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)),
        indicatorConstLp_coeFn (p := p) (hs := hs)
          (hμs := measure_ne_top μ s) (c := (1 : ℝ))] with x hx hsmul hone
      rw [hx, hsmul]
      simp only [Pi.smul_apply, smul_eq_mul, hone]
      by_cases hxs : x ∈ s <;> simp [hxs]
    rw [hLp, map_smul, hset s hs, smul_eq_mul, ← integral_const_mul, ← integral_indicator hs]
    exact integral_congr_ae (.of_forall fun x ↦ indicator_mul_left s (fun _ ↦ c) g)
  | @add f k _ ihf ihk =>
    intro hf
    have hf' := f.memLp_of_isFiniteMeasure p μ
    have hk' := k.memLp_of_isFiniteMeasure p μ
    have hint (v : SimpleFunc α ℝ) : Integrable (fun x ↦ v x * g x) μ := by
      obtain ⟨C, hC⟩ := v.exists_forall_norm_le
      exact hg.bdd_mul v.aestronglyMeasurable (Eventually.of_forall hC)
    have hLp : hf.toLp (f + k) = hf'.toLp f + hk'.toLp k := MemLp.toLp_add hf' hk'
    rw [hLp, map_add, ihf hf', ihk hk']
    simpa only [SimpleFunc.coe_add, Pi.add_apply, add_mul] using
      (integral_add (hint f) (hint k)).symm

/-- An integrable density representing a bounded functional on indicators represents it on
bounded measurable functions. The proof uses simple-function approximation and dominated
convergence against the density. -/
theorem eq_integral_of_indicator_eq_of_bounded (hp : p ≠ ∞)
    (Λ : Lp ℝ p μ →L[ℝ] ℝ) {g : α → ℝ} (hg : Integrable g μ)
    (hset : ∀ (s : Set α) (hs : MeasurableSet s),
      Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, g x ∂μ)
    {f : α → ℝ} (hf : Measurable f) (hfLp : MemLp f p μ)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Λ (hfLp.toLp f) = ∫ x, f x * g x ∂μ := by
  let S : ℕ → SimpleFunc α ℝ :=
    SimpleFunc.approxOn f hf (range f ∪ {0}) 0 (by simp)
  have hS (n : ℕ) : MemLp (S n) p μ := SimpleFunc.memLp_approxOn_range hf hfLp n
  have hleft : Tendsto (fun n ↦ Λ ((hS n).toLp (S n))) atTop
      (𝓝 (Λ (hfLp.toLp f))) :=
    (Λ.continuous.tendsto _).comp (SimpleFunc.tendsto_approxOn_range_Lp hp hf hfLp)
  have hright : Tendsto (fun n ↦ ∫ x, S n x * g x ∂μ) atTop
      (𝓝 (∫ x, f x * g x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (C + C) * ‖g x‖)
      (fun n ↦ (S n).aestronglyMeasurable.mul hg.aestronglyMeasurable)
      (hg.norm.const_mul (C + C)) (fun n ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((SimpleFunc.norm_approxOn_zero_le hf
        (s := range f ∪ {0}) (by simp) x n).trans (add_le_add (hC x) (hC x))) (norm_nonneg _)
    · exact (SimpleFunc.tendsto_approxOn hf (s := range f ∪ {0}) (by simp) (x := x)
        (subset_closure (by simp))).mul tendsto_const_nhds
  exact tendsto_nhds_unique (hleft.congr' (.of_forall fun n ↦
    eq_integral_simpleFunc_of_indicator_eq Λ hg hset (S n) (hS n))) hright

/-- If an integrable density represents a bounded functional on indicators, its conjugate
`Lq` seminorm is at most the operator norm. The signed-power tests are truncated before use,
so no conjugate integrability is assumed. -/
theorem eLpNorm_le_opNorm_of_indicator_eq [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (hq : q ≠ ∞)
    (Λ : Lp ℝ p μ →L[ℝ] ℝ) {g : α → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    (hset : ∀ (s : Set α) (hs : MeasurableSet s),
      Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, g x ∂μ) :
    eLpNorm g q μ ≤ ENNReal.ofReal ‖Λ‖ := by
  classical
  have hpq : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  let A : ℕ → Set α := fun n ↦ {x | ‖g x‖ ≤ (n : ℝ)}
  let v : ℕ → α → ℝ := fun n ↦ (A n).indicator (fun x ↦ ‖g x‖ ^ q.toReal)
  let φ : ℕ → α → ℝ := fun n ↦ (A n).indicator (fun x ↦
    if 0 ≤ g x then ‖g x‖ ^ (q.toReal - 1) else -(‖g x‖ ^ (q.toReal - 1)))
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le hgm.norm measurable_const
  have hvm (n : ℕ) : Measurable (v n) := (hgm.norm.pow_const _).indicator (hA n)
  have hφm (n : ℕ) : Measurable (φ n) :=
    (Measurable.ite (measurableSet_le measurable_const hgm)
      (hgm.norm.pow_const (q.toReal - 1))
      (hgm.norm.pow_const (q.toReal - 1)).neg).indicator (hA n)
  have hvnonneg (n : ℕ) (x : α) : 0 ≤ v n x :=
    indicator_nonneg (fun y _ ↦ Real.rpow_nonneg (norm_nonneg (g y)) _) x
  have hφnorm (n : ℕ) (x : α) :
      ‖φ n x‖ = (A n).indicator (fun x ↦ ‖g x‖ ^ (q.toReal - 1)) x := by
    simp only [φ, norm_indicator_eq_indicator_norm, apply_ite, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ite_self]
  have hφbound (n : ℕ) (x : α) : ‖φ n x‖ ≤ (n : ℝ) ^ (q.toReal - 1) :=
    hφnorm n x ▸ indicator_apply_le' (fun hx ↦ Real.rpow_le_rpow (norm_nonneg _) hx
      hpq.symm.sub_one_pos.le) fun _ ↦ Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hvbound (n : ℕ) (x : α) : ‖v n x‖ ≤ (n : ℝ) ^ q.toReal :=
    (Real.norm_of_nonneg (hvnonneg n x)).symm ▸ indicator_apply_le' (fun hx ↦
      Real.rpow_le_rpow (norm_nonneg _) hx hpq.symm.pos.le) fun _ ↦
      Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hφLp (n : ℕ) : MemLp (φ n) p μ :=
    MemLp.of_bound (hφm n).aestronglyMeasurable _ (Eventually.of_forall (hφbound n))
  have hvint (n : ℕ) : Integrable (v n) μ :=
    memLp_one_iff_integrable.mp
      (MemLp.of_bound (hvm n).aestronglyMeasurable _ (Eventually.of_forall (hvbound n)))
  have hφpow (n : ℕ) (x : α) : ‖φ n x‖ ^ p.toReal = v n x := by
    rw [hφnorm]
    by_cases hx : x ∈ A n
    · simp only [v, Set.indicator_of_mem hx]
      rw [← Real.rpow_mul (norm_nonneg _), hpq.symm.sub_one_mul_conj]
    · simp only [v, Set.indicator_of_notMem hx, Real.zero_rpow hpq.ne_zero]
  have hφprod (n : ℕ) (x : α) : φ n x * g x = v n x := by
    have hpower : ‖g x‖ ^ (q.toReal - 1) * ‖g x‖ = ‖g x‖ ^ q.toReal := by
      simpa only [sub_add_cancel, Real.rpow_one] using (Real.rpow_add_of_nonneg
        (norm_nonneg (g x)) hpq.symm.sub_one_pos.le zero_le_one).symm
    by_cases hx : x ∈ A n
    · simp only [φ, v, Set.indicator_of_mem hx]
      split_ifs with hsign
      · simpa only [Real.norm_eq_abs, abs_of_nonneg hsign] using hpower
      · simpa only [Real.norm_eq_abs, abs_of_nonpos (le_of_lt (lt_of_not_ge hsign)),
          neg_mul, mul_neg] using hpower
    · simp only [φ, v, Set.indicator_of_notMem hx, zero_mul]
  have hYnonneg (n : ℕ) : 0 ≤ ∫ x, v n x ∂μ := integral_nonneg (hvnonneg n)
  have hnorm (n : ℕ) :
      ‖(hφLp n).toLp (φ n)‖ = (∫ x, v n x ∂μ) ^ p.toReal⁻¹ := by
    rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm
      (ENNReal.HolderConjugate.ne_zero p q) hp (hφLp n),
      integral_congr_ae (Eventually.of_forall (hφpow n)),
      ENNReal.toReal_ofReal (Real.rpow_nonneg (hYnonneg n) _)]
  have hYbound (n : ℕ) : ∫ x, v n x ∂μ ≤ ‖Λ‖ ^ q.toReal := by
    have hEq : Λ ((hφLp n).toLp (φ n)) = ∫ x, v n x ∂μ := by
      rw [eq_integral_of_indicator_eq_of_bounded hp Λ hg hset (hφm n) (hφLp n)
        ((n : ℝ) ^ (q.toReal - 1)) (hφbound n)]
      exact integral_congr_ae (Eventually.of_forall (hφprod n))
    have hY : ∫ x, v n x ∂μ ≤ ‖Λ‖ * (∫ x, v n x ∂μ) ^ p.toReal⁻¹ := by
      simpa only [hEq, Real.norm_eq_abs, abs_of_nonneg (hYnonneg n), hnorm] using
        Λ.le_opNorm ((hφLp n).toLp (φ n))
    have hroot : (∫ x, v n x ∂μ) ^ q.toReal⁻¹ ≤ ‖Λ‖ := by
      rcases (hYnonneg n).eq_or_lt with hz | hpos
      · rw [← hz, Real.zero_rpow (inv_ne_zero hpq.symm.ne_zero)]
        exact norm_nonneg _
      · refine (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hpos p.toReal⁻¹)).mp ?_
        simpa only [← Real.rpow_add hpos, hpq.symm.inv_add_inv_eq_one, Real.rpow_one] using hY
    calc
      ∫ x, v n x ∂μ = ((∫ x, v n x ∂μ) ^ q.toReal⁻¹) ^ q.toReal :=
        (Real.rpow_inv_rpow (hYnonneg n) hpq.symm.ne_zero).symm
      _ ≤ ‖Λ‖ ^ q.toReal :=
        Real.rpow_le_rpow (Real.rpow_nonneg (hYnonneg n) _) hroot hpq.symm.pos.le
  -- monotone convergence of the truncations
  have hvmono (x : α) : Monotone (fun n ↦ ENNReal.ofReal (v n x)) := fun n m hnm ↦
    ENNReal.ofReal_le_ofReal (indicator_le_indicator_apply_of_subset
      (fun y (hy : ‖g y‖ ≤ n) ↦ hy.trans (Nat.cast_le.mpr hnm))
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hvlim (x : α) :
      Tendsto (fun n ↦ ENNReal.ofReal (v n x)) atTop
        (𝓝 (ENNReal.ofReal (‖g x‖ ^ q.toReal))) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖g x‖
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop N).mono fun n hn ↦ ?_)
    simp only [v, Set.indicator_of_mem (show x ∈ A n from hN.trans (Nat.cast_le.mpr hn))]
  have hpowerint :
      ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.toReal) ∂μ ≤ ENNReal.ofReal (‖Λ‖ ^ q.toReal) :=
    le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone
      (fun n ↦ (hvm n).ennreal_ofReal.aemeasurable)
      (Eventually.of_forall hvmono) (Eventually.of_forall hvlim)) fun n ↦ by
      rw [← ofReal_integral_eq_lintegral_ofReal (hvint n) (Eventually.of_forall (hvnonneg n))]
      exact ENNReal.ofReal_le_ofReal (hYbound n)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.HolderConjugate.ne_zero q p) hq hg.aestronglyMeasurable]
  have hnormpower :
      (∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂μ) = ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.toReal) ∂μ := by
    simp only [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg,
      ofReal_norm]
  rw [hnormpower]
  calc
    (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.toReal) ∂μ) ^ (1 / q.toReal) ≤
        ENNReal.ofReal (‖Λ‖ ^ q.toReal) ^ (1 / q.toReal) :=
      ENNReal.rpow_le_rpow hpowerint (one_div_nonneg.mpr ENNReal.toReal_nonneg)
    _ = ENNReal.ofReal ‖Λ‖ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (one_div_nonneg.mpr ENNReal.toReal_nonneg),
        one_div, Real.rpow_rpow_inv (norm_nonneg _) hpq.symm.ne_zero]

/-- Agreement on indicators determines a real `Lp` functional represented by a conjugate
density. The extension to all of `Lp` follows from density of simple functions and the
continuity of Mathlib's integral pairing. -/
theorem eq_lpPairing_of_indicator_eq [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (Λ : Lp ℝ p μ →L[ℝ] ℝ) {g : α → ℝ}
    (hg : Integrable g μ) (hgq : MemLp g q μ)
    (hset : ∀ (s : Set α) (hs : MeasurableSet s),
      Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, g x ∂μ) :
    Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hgq.toLp g) := by
  let T : Lp ℝ p μ →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p (hgq.toLp g)
  have hT {f : α → ℝ} (hf : MemLp f p μ) :
      T (hf.toLp f) = ∫ x, f x * g x ∂μ := by
    dsimp only [T]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hgq.coeFn_toLp, hf.coeFn_toLp] with x hxg hxf
    simp only [ContinuousLinearMap.mul_apply', hxg, hxf, mul_comm]
  change Λ = T
  ext f
  refine (Lp.simpleFunc.denseRange (E := ℝ) (μ := μ) hp).induction_on
    (p := fun u : Lp ℝ p μ ↦ Λ u = T u) f
    (isClosed_eq Λ.continuous T.continuous) ?_
  intro s
  have hs : (simpleFunc.memLp s).toLp (simpleFunc.toSimpleFunc s) = (s : Lp ℝ p μ) :=
    congrArg (fun v : Lp.simpleFunc ℝ p μ ↦ (v : Lp ℝ p μ))
      (simpleFunc.toLp_toSimpleFunc s)
  rw [← hs, hT]
  exact eq_integral_simpleFunc_of_indicator_eq Λ hg hset
    (simpleFunc.toSimpleFunc s) (simpleFunc.memLp s)

/-- Every bounded functional on real `Lp` over a finite measure, with finite conjugate
exponents `p` and `q`, is integration against an `Lq` function whose norm is at most the
operator norm. The density is constructed from the induced signed measure and its
`Lq` bound is proved by truncated signed-power tests. -/
theorem exists_dualDensity [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (hq : q ≠ ∞) (Λ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : Lp ℝ q μ, ‖g‖ ≤ ‖Λ‖ ∧ ∀ f : Lp ℝ p μ, Λ f = ∫ x, f x * g x ∂μ := by
  obtain ⟨g, hgm, hg, hset⟩ := exists_integrable_dualDensity hp Λ
  have hbound := eLpNorm_le_opNorm_of_indicator_eq (q := q) hp hq Λ hgm hg hset
  have hgq : MemLp g q μ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hgq.toLp g, ?_, ?_⟩
  · rw [Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
      (ENNReal.toReal_ofReal (norm_nonneg Λ))
  · intro f
    rw [eq_lpPairing_of_indicator_eq hp Λ hg hgq hset,
      ContinuousLinearMap.lpPairing_eq_integral]
    simp only [ContinuousLinearMap.mul_apply', mul_comm]

/-- Over a finite measure, the real integral pairing maps `Lq` onto the continuous dual of
`Lp` for finite conjugate exponents. -/
theorem surjective_lpPairing [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Function.Surjective ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p) := by
  intro Λ
  obtain ⟨g, _, hg⟩ := exists_dualDensity hp hq Λ
  refine ⟨g, ?_⟩
  ext f
  rw [ContinuousLinearMap.lpPairing_eq_integral, hg f]
  simp only [ContinuousLinearMap.mul_apply', mul_comm]

end Lp
end MeasureTheory
