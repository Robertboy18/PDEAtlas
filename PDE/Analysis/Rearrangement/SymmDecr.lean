/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import PDE.Analysis.Rearrangement.PolyaSzego
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Module.Normalize
import PDE.Analysis.MeasureTheory.Integral.Equimeasurable

/-!
# The symmetric decreasing rearrangement

The symmetric decreasing rearrangement `f*` of a function `f ≥ 0` on a finite-dimensional real
normed space is the radial function, nonincreasing in `|x|`, with the distribution of `f`. Its
`L^p` norms are those of `f`, and by the Pólya–Szegő inequality its gradient energies are at
most those of `f`. Talenti's proof of the sharp Sobolev inequality replaces `u` by `|u|*`. The
rearrangement inequalities of Hardy–Littlewood and Riesz, and the Pólya–Szegő inequality for
Sobolev functions that are not Lipschitz with compact support, are not proved here. The
statements about the distribution hold in dimension zero too, where `f* = f`, but they are
proved for nontrivial spaces.

## Main results

* `symmDecr μ f`: the rearrangement, for every measure on a normed group and every `f` with
  values in `[0, ∞]`; `symmDecr_le_of_norm_le`, `lt_symmDecr_iff`.
* `measure_lt_symmDecr`: for a Haar measure on a nontrivial finite-dimensional real normed space
  and every `f`, measurable or not, `μ {f* > t} = μ {f > t}` at every level.
* `lintegral_symmDecr_rpow`, `eLpNorm_symmDecr`: for almost everywhere measurable `f`, the
  integrals of the powers `p > 0` and the `L^p` norms, `p < ∞`, are preserved.
* `eq_symmDecr_of_radial_antitone`: a continuous radial nonincreasing `F` with the distribution
  of `f` is `f*`.
* `lintegral_enorm_fderiv_symmDecr_le`, `eLpNorm_fderiv_symmDecr_le`: the Pólya–Szegő inequality
  `∫ ‖∇u*‖^p ≤ ∫ ‖∇u‖^p`, that is `‖∇u*‖_p ≤ ‖∇u‖_p`, for `u` in `lipClass L R M` on a
  nontrivial finite-dimensional real inner product space and `1 ≤ p < ∞`;
  `toReal_symmDecr_mem_lipClass`: `u*` is in the class of `u`.

## How it works

For a measure `μ` put `f*(x) = sup {t : μ(B(0, |x|)) < μ {f > t}}`. This depends on `|x|` only
and decreases as `|x|` grows. The set `{f* > t}` is `{x : μ(B(0, |x|)) < μ {f > t}}`, by
continuity of the measure along the increasing sets `{f > s}`, `s ↓ t`. For a Haar measure on a
finite-dimensional space `μ(B(0, r)) = c rⁿ`, so this set is the open ball centred at `0` whose
measure is `μ {f > t}`, or the whole space: `f*` and `f` have the same distribution, and equal
integrals follow from `MeasureTheory.lintegral_rpow_eq_of_measure_lt_eq`. A continuous radial
nonincreasing function with the distribution of `f` has the same balls as its sets `{> t}`, so it
is `f*`. The radial limit of polarizations of `exists_radial_lintegral_fderiv_le` has the
integrals of the continuous functions of the values of `u`; by
`MeasureTheory.measure_lt_eq_of_lintegral_comp_eq` it has the distribution of `u`, so it is `u*`
(`ofReal_eq_symmDecr`), and its bound on the gradient energies is the Pólya–Szegő inequality.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, American
  Mathematical Society, 2001, Chapter 3 (rearrangements of sets and functions) and Chapter 7
  (the rearrangement does not increase the gradient energy).
  <https://doi.org/10.1090/gsm/014>
* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372:
  the reduction of the Sobolev inequality to the rearrangement.
  <https://doi.org/10.1007/BF02418013>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric Module
open scoped ENNReal NNReal Topology

namespace PDE.Analysis.Rearrangement

/-! ## The rearrangement -/

section SymmDecr

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure E} {f : E → ℝ≥0∞}

/-- The symmetric decreasing rearrangement of `f` with respect to `μ`:
`f*(x) = sup {t : μ(B(0, |x|)) < μ {f > t}}`. -/
def symmDecr (μ : Measure E) (f : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  sSup {t | μ (ball 0 ‖x‖) < μ {y | t < f y}}

/-- The rearrangement does not increase when `|x|` grows. -/
theorem symmDecr_le_of_norm_le {x y : E} (h : ‖x‖ ≤ ‖y‖) : symmDecr μ f y ≤ symmDecr μ f x :=
  sSup_le_sSup fun _ ht ↦ lt_of_le_of_lt (measure_mono (ball_subset_ball h)) ht

/-- The rearrangement is radial. -/
theorem symmDecr_eq_of_norm_eq {x y : E} (h : ‖x‖ = ‖y‖) : symmDecr μ f x = symmDecr μ f y :=
  le_antisymm (symmDecr_le_of_norm_le h.ge) (symmDecr_le_of_norm_le h.le)

/-- **The sets `{f* > t}`.** A point `x` lies in `{f* > t}` exactly when the ball of radius
`|x|` has less measure than `{f > t}`. -/
theorem lt_symmDecr_iff {t : ℝ≥0∞} {x : E} :
    t < symmDecr μ f x ↔ μ (ball 0 ‖x‖) < μ {y | t < f y} := by
  rw [symmDecr, lt_sSup_iff]
  constructor
  · rintro ⟨s, hs, hts⟩
    exact lt_of_lt_of_le hs (measure_mono fun y hy ↦ hts.trans hy)
  · intro h
    have ht : t ≠ ∞ := by
      rintro rfl
      simp at h
    -- `{f > t}` is the increasing union of the sets `{f > t + 1 / (k + 1)}`
    have hmono : Monotone fun k : ℕ ↦ {y | t + ((k : ℝ≥0∞) + 1)⁻¹ < f y} := by
      intro k l hkl y hy
      refine lt_of_le_of_lt (add_le_add_right (ENNReal.inv_le_inv.mpr ?_) t) hy
      exact add_le_add_left (Nat.cast_le.mpr hkl) 1
    have hU : {y | t < f y} = ⋃ k : ℕ, {y | t + ((k : ℝ≥0∞) + 1)⁻¹ < f y} := by
      ext y
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt (tsub_pos_of_lt hy).ne'
        refine ⟨k, ?_⟩
        calc t + ((k : ℝ≥0∞) + 1)⁻¹ ≤ t + (k : ℝ≥0∞)⁻¹ :=
              add_le_add_right (ENNReal.inv_le_inv.mpr le_self_add) t
          _ < t + (f y - t) := ENNReal.add_lt_add_left ht hk
          _ = f y := add_tsub_cancel_of_le hy.le
      · rintro ⟨k, hk⟩
        exact lt_of_le_of_lt le_self_add hk
    rw [hU, hmono.measure_iUnion, lt_iSup_iff] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨t + ((k : ℝ≥0∞) + 1)⁻¹, hk, ENNReal.lt_add_right ht (by simp)⟩

/-- The set `{f* > t}` consists of the points `x` whose ball of radius `|x|` has less measure
than `{f > t}`. -/
theorem setOf_lt_symmDecr (μ : Measure E) (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    {x | t < symmDecr μ f x} = {x | μ (ball 0 ‖x‖) < μ {y | t < f y}} :=
  Set.ext fun _ ↦ lt_symmDecr_iff

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **The rearrangement has the distribution of `f`**: `μ {f* > t} = μ {f > t}` for every
level `t`, for a Haar measure on a nontrivial finite-dimensional real normed space. No
measurability of `f` is needed. -/
theorem measure_lt_symmDecr (f : E → ℝ≥0∞) (t : ℝ≥0∞) :
    μ {x | t < symmDecr μ f x} = μ {y | t < f y} := by
  rw [setOf_lt_symmDecr]
  set m : ℝ≥0∞ := μ {y | t < f y} with hm
  have hc0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (ball (0 : E) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hn : finrank ℝ E ≠ 0 := finrank_pos.ne'
  rcases eq_or_ne m ∞ with hmt | hmt
  · -- the whole space
    have huniv : {x : E | μ (ball 0 ‖x‖) < m} = univ := by
      ext x
      simp only [mem_ofPred_eq, mem_univ, iff_true, hmt]
      exact measure_ball_lt_top
    rw [huniv, hmt]
    exact measure_univ_of_isAddLeftInvariant μ
  · -- the open ball of measure `m`
    have hc' : 0 < (μ (ball (0 : E) 1)).toReal := ENNReal.toReal_pos hc0 hctop
    have hq : 0 ≤ m.toReal / (μ (ball (0 : E) 1)).toReal := by positivity
    set ρ : ℝ := (m.toReal / (μ (ball (0 : E) 1)).toReal) ^ ((finrank ℝ E : ℝ)⁻¹) with hρ
    have hρ0 : 0 ≤ ρ := Real.rpow_nonneg hq _
    have hρn : ρ ^ finrank ℝ E = m.toReal / (μ (ball (0 : E) 1)).toReal := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul hq,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), Real.rpow_one]
    have hball : {x : E | μ (ball 0 ‖x‖) < m} = ball (0 : E) ρ := by
      ext x
      rw [mem_ofPred_eq, mem_ball_zero_iff, ← ENNReal.toReal_lt_toReal measure_ball_lt_top.ne hmt,
        Measure.addHaar_ball μ 0 (norm_nonneg x), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg (norm_nonneg x) _), ← lt_div_iff₀ hc', ← hρn]
      exact pow_lt_pow_iff_left₀ (norm_nonneg x) hρ0 hn
    rw [hball, Measure.addHaar_ball μ 0 hρ0, hρn, ENNReal.ofReal_div_of_pos hc',
      ENNReal.ofReal_toReal hmt, ENNReal.ofReal_toReal hctop, ENNReal.div_mul_cancel hc0 hctop]

/-- The rearrangement is measurable: its sets `{f* > t}` are open balls or the whole space. -/
theorem measurable_symmDecr (f : E → ℝ≥0∞) : Measurable (symmDecr μ f) := by
  refine measurable_of_Ioi fun t ↦ ?_
  have hset : symmDecr μ f ⁻¹' Ioi t = {x | μ (ball 0 ‖x‖) < μ {y | t < f y}} :=
    setOf_lt_symmDecr μ f t
  have hmeas : Measurable fun x : E ↦ μ (ball 0 ‖x‖) := by
    have e : (fun x : E ↦ μ (ball 0 ‖x‖)) =
        fun x ↦ ENNReal.ofReal (‖x‖ ^ finrank ℝ E) * μ (ball 0 1) :=
      funext fun x ↦ Measure.addHaar_ball μ 0 (norm_nonneg x)
    rw [e]
    exact (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)).mul_const _
  rw [hset]
  exact measurableSet_lt hmeas measurable_const

/-- **The rearrangement preserves the integral of the `p`-th power**, `p > 0`. -/
theorem lintegral_symmDecr_rpow {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, symmDecr μ f x ^ p ∂μ = ∫⁻ x, f x ^ p ∂μ :=
  lintegral_rpow_eq_of_measure_lt_eq (measurable_symmDecr μ f).aemeasurable hf
    (measure_lt_symmDecr μ f) hp

/-- **The rearrangement preserves the `L^p` norm**, `p < ∞`. -/
theorem eLpNorm_symmDecr {f : E → ℝ≥0∞} (hf : AEMeasurable f μ) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    eLpNorm (symmDecr μ f) p μ = eLpNorm f p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero (measurable_symmDecr μ f).aestronglyMeasurable,
      eLpNorm_exponent_zero hf.aestronglyMeasurable]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
      (measurable_symmDecr μ f).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf.aestronglyMeasurable]
  simp only [eNorm_eq_self]
  rw [lintegral_symmDecr_rpow μ hf (ENNReal.toReal_pos hp0 hp)]

/-- **Uniqueness of the rearrangement.** A continuous function `F` that does not increase when
`|x|` grows and has the distribution of `f` is the symmetric decreasing rearrangement of `f`:
its sets `{F > t}` are balls centred at `0`, of the measure of `{f > t}`. -/
theorem eq_symmDecr_of_radial_antitone {F f : E → ℝ≥0∞} (hFc : Continuous F)
    (hrad : ∀ x y : E, ‖x‖ ≤ ‖y‖ → F y ≤ F x)
    (heq : ∀ t, μ {x | t < F x} = μ {y | t < f y}) : F = symmDecr μ f := by
  funext x
  refine eq_of_forall_lt_iff fun T ↦ ?_
  rw [lt_symmDecr_iff, ← heq T]
  constructor
  · intro hT
    -- `{F > T}` contains a ball centred at `0` of radius larger than `|x|`
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hFc) x hT
    obtain ⟨e, he, hxe⟩ : ∃ e : E, ‖e‖ = 1 ∧ x = ‖x‖ • e := by
      rcases eq_or_ne x 0 with rfl | hx
      · obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
        exact ⟨e, he, by simp⟩
      · exact ⟨NormedSpace.normalize x, NormedSpace.norm_normalize hx,
          (NormedSpace.norm_smul_normalize x).symm⟩
    have hyn : ‖(‖x‖ + δ / 2) • e‖ = ‖x‖ + δ / 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hyx : (‖x‖ + δ / 2) • e ∈ ball x δ := by
      have e1 : (‖x‖ + δ / 2) • e - x = (δ / 2) • e := by
        nth_rewrite 2 [hxe]
        rw [← sub_smul, add_sub_cancel_left]
      rw [mem_ball, dist_eq_norm, e1, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have hTy : T < F ((‖x‖ + δ / 2) • e) := hsub hyx
    have hball : ball (0 : E) (‖x‖ + δ / 2) ⊆ {z | T < F z} := fun z hz ↦
      lt_of_lt_of_le hTy (hrad z _ (by rw [hyn]; exact (mem_ball_zero_iff.mp hz).le))
    have hlt : μ (ball 0 ‖x‖) < μ (ball (0 : E) (‖x‖ + δ / 2)) := by
      rw [Measure.addHaar_ball μ 0 (norm_nonneg x),
        Measure.addHaar_ball μ 0 (show (0 : ℝ) ≤ ‖x‖ + δ / 2 by positivity)]
      refine (ENNReal.mul_lt_mul_iff_left (measure_ball_pos μ 0 one_pos).ne'
        measure_ball_lt_top.ne).mpr ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
      exact pow_lt_pow_left₀ (by linarith) (norm_nonneg x) finrank_pos.ne'
    exact lt_of_lt_of_le hlt (measure_mono hball)
  · intro h
    by_contra hT
    have hsub : {z | T < F z} ⊆ ball (0 : E) ‖x‖ := fun z hz ↦ by
      rw [mem_ball_zero_iff]
      by_contra hzx
      exact hT (lt_of_lt_of_le hz (hrad x z (not_lt.mp hzx)))
    exact absurd h (not_lt.mpr (measure_mono hsub))

end SymmDecr

/-! ## The Pólya–Szegő inequality for the rearrangement -/

section PolyaSzego

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

variable [Nontrivial E] {L : ℝ≥0} {R M : ℝ} {u : E → ℝ}

/-- **A radial nonincreasing function with the distribution of `u` is the rearrangement.**
Let `u` be measurable and let `v` be continuous, not increasing when `|x|` grows, with the
integrals of the continuous functions of the values of `u`. Then the positive part of `v` is
the symmetric decreasing rearrangement of the positive part of `u`. The radial limit of
polarizations of `exists_radial_lintegral_fderiv_le` is such a `v`, and it is nonnegative. -/
theorem ofReal_eq_symmDecr {v : E → ℝ} (hu : Measurable u) (hv : Continuous v)
    (hrad : ∀ x y : E, ‖x‖ ≤ ‖y‖ → v y ≤ v x)
    (hdist : ∀ g : ℝ → ℝ, Continuous g → g 0 = 0 →
      ∫⁻ x, ENNReal.ofReal (g (v x)) = ∫⁻ x, ENNReal.ofReal (g (u x))) (x : E) :
    ENNReal.ofReal (v x) = symmDecr volume (fun y ↦ ENNReal.ofReal (u y)) x := by
  refine congrFun (eq_symmDecr_of_radial_antitone volume (F := fun x ↦ ENNReal.ofReal (v x))
    (ENNReal.continuous_ofReal.comp hv)
    (fun x y hxy ↦ ENNReal.ofReal_le_ofReal (hrad x y hxy)) fun T ↦ ?_) x
  rcases eq_or_ne T ∞ with rfl | hT
  · simp
  · have e (w : E → ℝ) : {x | T < ENNReal.ofReal (w x)} = {x | T.toReal < w x} := by
      ext x
      exact ENNReal.lt_ofReal_iff_toReal_lt hT
    rw [e v, e u]
    exact measure_lt_eq_of_lintegral_comp_eq hu hv.measurable hdist ENNReal.toReal_nonneg

/-- The real-valued symmetric decreasing rearrangement of a function `u` of the class
`lipClass L R M` is the radial limit of polarizations of `exists_radial_lintegral_fderiv_le`: it
is in the class and its gradient energies are at most those of `u`. -/
private theorem toReal_symmDecr_mem_lipClass_and_lintegral_le (hu : u ∈ lipClass L R M) :
    (fun x ↦ (symmDecr volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal) ∈ lipClass L R M ∧
      ∀ p : ℝ, 1 ≤ p → ∫⁻ x, ‖fderiv ℝ (fun y ↦
        (symmDecr volume (fun z ↦ ENNReal.ofReal (u z)) y).toReal) x‖ₑ ^ p ≤
          ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ p := by
  obtain ⟨v, hvK, hrad, hdist, hgrad⟩ := exists_radial_lintegral_fderiv_le hu
  have hveq : (fun x ↦ (symmDecr volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal) = v := by
    funext x
    rw [← ofReal_eq_symmDecr hu.1.continuous.measurable hvK.1.continuous hrad hdist x,
      ENNReal.toReal_ofReal (hvK.2.1 x).1]
  rw [hveq]
  exact ⟨hvK, hgrad⟩

/-- The real-valued symmetric decreasing rearrangement of a function of the class
`lipClass L R M` is in the class: it is `L`-Lipschitz, takes values in `[0, M]` and vanishes
outside the closed ball of radius `R`. -/
theorem toReal_symmDecr_mem_lipClass (hu : u ∈ lipClass L R M) :
    (fun x ↦ (symmDecr volume (fun y ↦ ENNReal.ofReal (u y)) x).toReal) ∈ lipClass L R M :=
  (toReal_symmDecr_mem_lipClass_and_lintegral_le hu).1

/-- **The Pólya–Szegő inequality for the symmetric decreasing rearrangement.** Let `u` be
`L`-Lipschitz on a nontrivial finite-dimensional real inner product space, with values in
`[0, M]`, and zero outside a ball, and let `u*` be its symmetric decreasing rearrangement with
respect to the volume. Then `∫ ‖∇u*‖^p ≤ ∫ ‖∇u‖^p` for every `p ≥ 1`. -/
theorem lintegral_enorm_fderiv_symmDecr_le (hu : u ∈ lipClass L R M) {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ x, ‖fderiv ℝ (fun y ↦ (symmDecr volume (fun z ↦ ENNReal.ofReal (u z)) y).toReal) x‖ₑ ^ p ≤
      ∫⁻ x, ‖fderiv ℝ u x‖ₑ ^ p :=
  (toReal_symmDecr_mem_lipClass_and_lintegral_le hu).2 p hp

/-- **The Pólya–Szegő inequality in norm form**: `‖∇u*‖_p ≤ ‖∇u‖_p` for `1 ≤ p < ∞`, for a
function `u` of the class `lipClass L R M` and its symmetric decreasing rearrangement `u*`. -/
theorem eLpNorm_fderiv_symmDecr_le (hu : u ∈ lipClass L R M) {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) :
    eLpNorm (fderiv ℝ fun y ↦ (symmDecr volume (fun z ↦ ENNReal.ofReal (u z)) y).toReal) p volume ≤
      eLpNorm (fderiv ℝ u) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hp1' : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  have hm (w : E → ℝ) : AEStronglyMeasurable (fderiv ℝ w) (volume : Measure E) := by
    borelize (E →L[ℝ] ℝ)
    exact (measurable_fderiv ℝ w).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hm _),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hm _)]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_fderiv_symmDecr_le hu hp1') (by positivity)

end PolyaSzego

end PDE.Analysis.Rearrangement
