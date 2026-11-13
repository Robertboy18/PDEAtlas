/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Topology.MetricSpace.Holder

/-!
# One-dimensional transport of a sign-changing kernel

Let `k` change sign at `c`: `k ≤ 0` on `(-∞, c)` and `k ≥ 0` on `(c, ∞)`, with
`∫ |k(x)| |x - c|^α dx < ∞` and equal masses `∫_{x < c} |k| = ∫_{x > c} |k|` in `[0, ∞]`. A map
`T` from `(c, ∞)` to `(-∞, c)` that matches outer masses,

`∫_{x ≤ T(y)} |k| = ∫_{x ≥ y} |k|`,

pushes the measure `|k| dx` on `(c, ∞)` forward to `|k| dx` on `(-∞, c)`. Pairing `y` with `T y`
then gives the transport lemma of Chen and Hou (Part I, Lemma 3.6): for `g` Hölder of order
`α > 0` with constant `C`,

`|∫ k (g - g(c))| ≤ C ∫_{y > c} |k(y)| |y - T(y)|^α dy`.

Chen and Hou state the lemma for `α ∈ (0, 1)` and a kernel continuous off `c` on an interval;
ours holds for every `α > 0`.

The statement is measure-theoretic and covers kernels localized by indicator functions and
supported on half-lines: `k` is any measurable function on `ℝ` (bounded intervals and
half-lines are the case of a kernel supported there), integrability at infinity is a hypothesis,
the signs are non-strict, and `T` is any measurable map matching outer masses on the set where
`k ≠ 0`; it need not be unique, continuous or an involution. The proof is a monotone rearrangement
argument through the distribution of the tail masses (`measure_eq_of_tail_bounds`), with no
derivative of `T`.

The absolute form needs no principal value: `k (g - g(c))` is integrable. When
`∫_{|x - c| > ε} k → 0`, the truncated integrals of `k g` converge to `∫ k (g - g(c))`, which is
the principal value `PV ∫ k g` (`tendsto_integral_mul_of_tendsto`), and zero principal-value
mass forces equal masses on the two sides (`isBalancedKernel_of_tendsto`).

The file also proves Lemma 3.10 of Chen and Hou, an elementary comparison of shifted integrals
against a nondecreasing weight, in `[0, ∞]`-valued form on bounded intervals and on half-lines.

## Main declarations

* `IsBalancedKernel k c α`, `IsMassMatching k c T`: the hypotheses on the kernel and the map.
* `measure_eq_of_tail_bounds`: the distribution of tail masses of an atomless measure.
* `map_withDensity_eq`: `T` pushes `|k| dx` on `(c, ∞)` to `|k| dx` on `(-∞, c)`.
* `IsBalancedKernel.integral_comp_eq`, `IsBalancedKernel.lintegral_comp_eq`: the change of
  variables `∫_{x < c} |k| φ = ∫_{y > c} |k(y)| φ(T y)`.
* `IsBalancedKernel.abs_integral_mul_sub_le`: Lemma 3.6 in absolute form;
  `IsBalancedKernel.abs_setIntegral_mul_sub_le`: on a measurable set such as a bounded interval
  or a half-line; `IsBalancedKernel.abs_integral_mul_sub_le_left`: the cost on the left side;
  `IsBalancedKernel.integral_transportCost_eq`: the two costs agree for inverse maps.
* `IsBalancedKernel.abs_le_of_tendsto`, `isBalancedKernel_of_tendsto`: the principal-value form.
* `abs_integral_mul_le_of_integral_eq_zero`: the form for integrable kernels with `∫ k = 0` and
  `∫_{T y}^{y} k = 0`.
* `transportMap`, `IsBalancedKernel.isMassMatching_transportMap`: a canonical measurable
  mass-matching map.
* `lintegral_shift_le`, `lintegral_shift_le_of_tail`: Lemma 3.10 on `[b - h, c + h]` and on a
  half-line.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 3.2, Lemma 3.6, and
  Section 3.4, Lemma 3.10. <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PDE.Analysis.Rearrangement

section Tail

/-- Continuity from below: a bound on the tails `ρ [y, ∞)` for all `y > e` bounds `ρ (e, ∞)`. -/
private theorem measure_Ioi_le_of_forall {ρ : Measure ℝ} {e : ℝ} {s : ℝ≥0∞}
    (h : ∀ y, e < y → ρ (Ici y) ≤ s) : ρ (Ioi e) ≤ s := by
  obtain ⟨u, hu, hlt, hlim⟩ := exists_seq_strictAnti_tendsto e
  rw [← iUnion_Ici_eq_Ioi_of_lt_of_tendsto hlt hlim,
    Monotone.measure_iUnion fun _ _ hmn ↦ Ici_subset_Ici.2 (hu.antitone hmn)]
  exact iSup_le fun n ↦ h _ (hlt n)

/-- Continuity from below: a bound on `ρ (-∞, y]` for all `y < a` bounds `ρ (-∞, a)`. -/
private theorem measure_Iio_le_of_forall {ρ : Measure ℝ} {a : ℝ} {s : ℝ≥0∞}
    (h : ∀ y, y < a → ρ (Iic y) ≤ s) : ρ (Iio a) ≤ s := by
  obtain ⟨u, hu, hlt, hlim⟩ := exists_seq_strictMono_tendsto a
  rw [← iUnion_Iic_eq_Iio_of_lt_of_tendsto hlt hlim,
    Monotone.measure_iUnion fun _ _ hmn ↦ Iic_subset_Iic.2 (hu.monotone hmn)]
  exact iSup_le fun n ↦ h _ (hlt n)

/-- Continuity from above: a lower bound for the finite tails `ρ [y, ∞)` at the points `y` of
`(a, e)` is a lower bound at `e`. -/
private theorem le_measure_Ici_of_forall {ρ : Measure ℝ} {a e : ℝ} {s : ℝ≥0∞} (hae : a < e)
    (hfin : ∀ y ∈ Ioo a e, ρ (Ici y) ≠ ∞) (h : ∀ y ∈ Ioo a e, s ≤ ρ (Ici y)) :
    s ≤ ρ (Ici e) := by
  obtain ⟨u, hu, hmem, hlim⟩ := exists_seq_strictMono_tendsto' hae
  have hI : ⋂ n, Ici (u n) = Ici e := Subset.antisymm
    (fun y hy ↦ le_of_tendsto' hlim fun n ↦ mem_iInter.1 hy n)
    (subset_iInter fun n ↦ Ici_subset_Ici.2 (hmem n).2.le)
  rw [← hI, Antitone.measure_iInter (fun _ _ hmn ↦ Ici_subset_Ici.2 (hu.monotone hmn))
    (fun _ ↦ measurableSet_Ici.nullMeasurableSet) ⟨0, hfin _ (hmem 0)⟩]
  exact le_iInf fun n ↦ h _ (hmem n)

/-- Continuity from above: a lower bound for the finite masses `ρ (-∞, y]` at the points `y` of
`(a, b)` is a lower bound at `a`. -/
private theorem le_measure_Iic_of_forall {ρ : Measure ℝ} {a b : ℝ} {s : ℝ≥0∞} (hab : a < b)
    (hfin : ∀ y ∈ Ioo a b, ρ (Iic y) ≠ ∞) (h : ∀ y ∈ Ioo a b, s ≤ ρ (Iic y)) :
    s ≤ ρ (Iic a) := by
  obtain ⟨u, hu, hmem, hlim⟩ := exists_seq_strictAnti_tendsto' hab
  have hI : ⋂ n, Iic (u n) = Iic a := Subset.antisymm
    (fun y hy ↦ ge_of_tendsto' hlim fun n ↦ mem_iInter.1 hy n)
    (subset_iInter fun n ↦ Iic_subset_Iic.2 (hmem n).1.le)
  rw [← hI, Antitone.measure_iInter (fun _ _ hmn ↦ Iic_subset_Iic.2 (hu.antitone hmn))
    (fun _ ↦ measurableSet_Iic.nullMeasurableSet) ⟨0, hfin _ (hmem 0)⟩]
  exact le_iInf fun n ↦ h _ (hmem n)

/-- The distribution of tail masses. Let `ρ` be an atomless measure on `ℝ` carried by `(c, ∞)`,
with finite tails `ρ [y, ∞)` for `y > c`, and let `s ≤ ρ ℝ`. An upward closed subset `E` of
`(c, ∞)` on which the tail mass is at most `s`, and off which it is at least `s`, has measure
`s`. Applied to `E = {ρ [y, ∞) < s}` and `E = {ρ [y, ∞) ≤ s}` this says that the tail mass of a
`ρ`-random point is uniformly distributed on `[0, ρ ℝ]`. -/
theorem measure_eq_of_tail_bounds {ρ : Measure ℝ} {c : ℝ} {s : ℝ≥0∞} {E : Set ℝ}
    (hρc : ρ (Iic c) = 0) (hfin : ∀ y, c < y → ρ (Ici y) ≠ ∞) (hatom : ∀ y, ρ {y} = 0)
    (hs : s ≤ ρ univ) (hEc : E ⊆ Ioi c) (hup : ∀ y ∈ E, ∀ y', y ≤ y' → y' ∈ E)
    (hle : ∀ y ∈ E, ρ (Ici y) ≤ s) (hge : ∀ y, c < y → y ∉ E → s ≤ ρ (Ici y)) :
    ρ E = s := by
  rcases E.eq_empty_or_nonempty with rfl | hne
  · -- every tail mass is at least `s`, and the tails tend to zero
    have hanti : Antitone fun n : ℕ ↦ Ici (c + 1 + n) := fun _ _ hmn ↦ Ici_subset_Ici.2 (by gcongr)
    have htend := tendsto_measure_iInter_atTop (μ := ρ)
      (fun n ↦ measurableSet_Ici.nullMeasurableSet) hanti ⟨0, hfin _ (by simp)⟩
    have hempty : (⋂ n : ℕ, Ici (c + 1 + n)) = ∅ := eq_empty_of_forall_notMem fun y hy ↦ by
      obtain ⟨n, hn⟩ := exists_nat_gt (y - c)
      linarith [mem_Ici.1 (mem_iInter.1 hy n)]
    rw [hempty, measure_empty] at htend
    have hs0 : s ≤ 0 := ge_of_tendsto' htend fun n ↦
      hge _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (notMem_empty _)
    rw [measure_empty, le_antisymm hs0 bot_le]
  · have hbdd : BddBelow E := ⟨c, fun y hy ↦ (hEc hy).le⟩
    set e := sInf E
    have hce : c ≤ e := le_csInf hne fun y hy ↦ (hEc hy).le
    have hsup : Ioi e ⊆ E := fun y hy ↦ by
      obtain ⟨y', hy', hlt⟩ := exists_lt_of_csInf_lt hne hy
      exact hup y' hy' y hlt.le
    have hIci : ρ (Ici e) = ρ (Ioi e) := (measure_congr (Ioi_ae_eq_Ici' (hatom e))).symm
    rw [le_antisymm ((measure_mono fun y hy ↦ csInf_le hbdd hy).trans hIci.le)
      (measure_mono hsup)]
    refine le_antisymm (measure_Ioi_le_of_forall fun y hy ↦ hle _ (hsup hy)) ?_
    rcases eq_or_lt_of_le hce with hce | hce
    · -- `e = c`: the whole mass lies to the right of `e`
      rw [← hce]
      rw [← Iic_union_Ioi (a := c)] at hs
      exact hs.trans ((measure_union_le _ _).trans_eq (by rw [hρc, zero_add]))
    · -- `c < e`: continuity from above at `e`, through points of `(c, e)` outside `E`
      rw [← hIci]
      exact le_measure_Ici_of_forall hce (fun y hy ↦ hfin y hy.1)
        fun y hy ↦ hge y hy.1 fun hmem ↦ (csInf_le hbdd hmem).not_gt hy.2

end Tail

section Pushforward

variable {k T : ℝ → ℝ} {c : ℝ}

/-- `T` matches outer masses of `k` across `c`: on the set where `k ≠ 0` to the right of `c`, the
point `T y` lies to the left of `c` and the mass of `|k|` on `(-∞, T y]` equals the mass on
`[y, ∞)`. For a kernel with the signs of Chen and Hou, Lemma 3.6, and zero principal-value mass,
this is their defining equation `PV ∫_{T y}^{y} k = 0` of the transport map; for an integrable
kernel with `∫ k = 0` it is `∫_{T y}^{y} k = 0` (`isMassMatching_of_integral_eq_zero`). With
infinite masses on both sides, matching outer masses does not force `PV ∫_{T y}^{y} k = 0`, and
it is the outer-mass condition that the transport lemma uses. -/
structure IsMassMatching (k : ℝ → ℝ) (c : ℝ) (T : ℝ → ℝ) : Prop where
  aemeasurable : AEMeasurable T (volume.restrict (Ioi c))
  lt : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 → T y < c
  mass_eq : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 →
    ∫⁻ x in Iic (T y), ‖k x‖ₑ = ∫⁻ x in Ici y, ‖k x‖ₑ

/-- The measure `|k| dx` on `(c, ∞)`. -/
private abbrev rightMeasure (k : ℝ → ℝ) (c : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi c)).withDensity fun x ↦ ‖k x‖ₑ

/-- The measure `|k| dx` on `(-∞, c)`. -/
private abbrev leftMeasure (k : ℝ → ℝ) (c : ℝ) : Measure ℝ :=
  (volume.restrict (Iio c)).withDensity fun x ↦ ‖k x‖ₑ

/-- For `y > c`, the measure `|k| dx` on `(c, ∞)` gives `[y, ∞)` the mass `∫_{[y, ∞)} |k|`. -/
private theorem rightMeasure_Ici {y : ℝ} (hy : c < y) :
    rightMeasure k c (Ici y) = ∫⁻ x in Ici y, ‖k x‖ₑ := by
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    inter_eq_left.2 (Ici_subset_Ioi.2 hy)]

/-- The measure `|k| dx` on `(c, ∞)` gives no mass to `(-∞, c]`. -/
private theorem rightMeasure_Iic : rightMeasure k c (Iic c) = 0 := by
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    Iic_inter_Ioi, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]

/-- For `x < c`, the measure `|k| dx` on `(-∞, c)` gives `(-∞, x]` the mass `∫_{(-∞, x]} |k|`. -/
private theorem leftMeasure_Iic {x : ℝ} (hx : x < c) :
    leftMeasure k c (Iic x) = ∫⁻ t in Iic x, ‖k t‖ₑ := by
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    inter_eq_left.2 (Iic_subset_Iio.2 hx)]

/-- The measure `|k| dx` on `(-∞, c)` gives no mass to `[c, ∞)`. -/
private theorem leftMeasure_Ici : leftMeasure k c (Ici c) = 0 := by
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Ici_inter_Iio, Ico_self, Measure.restrict_empty, lintegral_zero_measure]

/-- Points are null for the measure `|k| dx` on `(c, ∞)`. -/
private theorem rightMeasure_singleton (y : ℝ) : rightMeasure k c {y} = 0 := by
  have : volume.restrict (Ioi c) {y} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton y)]
    exact measure_mono_null inter_subset_left Real.volume_singleton
  exact withDensity_absolutelyContinuous _ _ this

/-- The matching conditions hold almost everywhere for `|k| dx` on `(c, ∞)`. -/
private theorem IsMassMatching.ae_rightMeasure (hT : IsMassMatching k c T) (hk : AEMeasurable k) :
    ∀ᵐ y ∂rightMeasure k c, c < y ∧ T y < c ∧
      ∫⁻ x in Iic (T y), ‖k x‖ₑ = ∫⁻ x in Ici y, ‖k x‖ₑ := by
  rw [ae_withDensity_iff' hk.enorm.restrict]
  filter_upwards [hT.lt, hT.mass_eq, ae_restrict_mem measurableSet_Ioi] with y hlt hmass hyc hw
  have hky : k y ≠ 0 := fun h ↦ hw (by simp [h])
  exact ⟨hyc, hlt hky, hmass hky⟩

/-- The pushforward of `|k| dx` on `(c, ∞)` under a mass-matching map `T` is `|k| dx` on
`(-∞, c)`. The hypotheses are finiteness of the outer tails and equality of the total masses
(both possibly infinite). -/
theorem map_withDensity_eq (hk : AEMeasurable k)
    (hR : ∀ y, c < y → ∫⁻ x in Ici y, ‖k x‖ₑ ≠ ∞) (hL : ∀ x, x < c → ∫⁻ t in Iic x, ‖k t‖ₑ ≠ ∞)
    (hM : ∫⁻ x in Iio c, ‖k x‖ₑ = ∫⁻ x in Ioi c, ‖k x‖ₑ) (hT : IsMassMatching k c T) :
    ((volume.restrict (Ioi c)).withDensity fun x ↦ ‖k x‖ₑ).map T =
      (volume.restrict (Iio c)).withDensity fun x ↦ ‖k x‖ₑ := by
  change (rightMeasure k c).map T = leftMeasure k c
  have hTm : AEMeasurable T (rightMeasure k c) :=
    hT.aemeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
  have hT' := hT.ae_rightMeasure hk
  have huniv : rightMeasure k c univ = ∫⁻ x in Ioi c, ‖k x‖ₑ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  -- the cumulative distribution of the pushforward
  have key : ∀ x, x < c → rightMeasure k c (T ⁻¹' Iic x) = leftMeasure k c (Iic x) := by
    intro x hx
    rw [leftMeasure_Iic hx]
    set s := ∫⁻ t in Iic x, ‖k t‖ₑ
    have hs : s ≤ rightMeasure k c univ := by
      rw [huniv, ← hM]
      exact lintegral_mono_set (Iic_subset_Iio.2 hx)
    have hanti : ∀ y y' : ℝ, y ≤ y' → rightMeasure k c (Ici y') ≤ rightMeasure k c (Ici y) :=
      fun y y' h ↦ measure_mono (Ici_subset_Ici.2 h)
    have rank := fun E ↦ measure_eq_of_tail_bounds (ρ := rightMeasure k c) (s := s) (E := E)
      rightMeasure_Iic (fun y hy ↦ by rw [rightMeasure_Ici hy]; exact hR y hy)
      rightMeasure_singleton hs
    have h₁ : rightMeasure k c {y | c < y ∧ rightMeasure k c (Ici y) < s} = s :=
      rank _ (fun y hy ↦ hy.1)
        (fun y hy y' hyy' ↦ ⟨hy.1.trans_le hyy', (hanti _ _ hyy').trans_lt hy.2⟩)
        (fun y hy ↦ hy.2.le) (fun y hy hyE ↦ not_lt.1 fun h ↦ hyE ⟨hy, h⟩)
    have h₂ : rightMeasure k c {y | c < y ∧ rightMeasure k c (Ici y) ≤ s} = s :=
      rank _ (fun y hy ↦ hy.1)
        (fun y hy y' hyy' ↦ ⟨hy.1.trans_le hyy', (hanti _ _ hyy').trans hy.2⟩)
        (fun y hy ↦ hy.2) (fun y hy hyE ↦ (not_le.1 fun h ↦ hyE ⟨hy, h⟩).le)
    have hlo : {y | c < y ∧ rightMeasure k c (Ici y) < s} ≤ᵐ[rightMeasure k c] T ⁻¹' Iic x := by
      filter_upwards [hT'] with y ⟨hyc, _, hmass⟩ ⟨_, h⟩
      rw [rightMeasure_Ici hyc, ← hmass] at h
      exact not_lt.1 fun hcon ↦ h.not_ge (lintegral_mono_set (Iic_subset_Iic.2 hcon.le))
    have hhi : T ⁻¹' Iic x ≤ᵐ[rightMeasure k c] {y | c < y ∧ rightMeasure k c (Ici y) ≤ s} := by
      filter_upwards [hT'] with y ⟨hyc, _, hmass⟩ hmem
      exact ⟨hyc, (rightMeasure_Ici hyc).trans_le
        (hmass ▸ lintegral_mono_set (Iic_subset_Iic.2 hmem))⟩
    exact le_antisymm (h₂ ▸ measure_mono_ae hhi) (h₁ ▸ measure_mono_ae hlo)
  -- equality on `(-∞, x]` for every `x < c`
  have hres : ∀ x, x < c →
      ((rightMeasure k c).map T).restrict (Iic x) = (leftMeasure k c).restrict (Iic x) := by
    intro x hx
    have : IsFiniteMeasure ((leftMeasure k c).restrict (Iic x)) :=
      isFiniteMeasure_restrict.2 (by rw [leftMeasure_Iic hx]; exact hL x hx)
    refine (Measure.ext_of_Iic _ _ fun a ↦ ?_).symm
    rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
      Iic_inter_Iic, Measure.map_apply_of_aemeasurable hTm measurableSet_Iic,
      key _ (lt_of_le_of_lt inf_le_right hx)]
  have hleft :
      ((rightMeasure k c).map T).restrict (Iio c) = (leftMeasure k c).restrict (Iio c) := by
    obtain ⟨u, -, hlt, hlim⟩ := exists_seq_strictMono_tendsto c
    rw [← iUnion_Iic_eq_Iio_of_lt_of_tendsto hlt hlim]
    exact Measure.restrict_iUnion_congr.2 fun n ↦ hres _ (hlt n)
  have hright :
      ((rightMeasure k c).map T).restrict (Ici c) = (leftMeasure k c).restrict (Ici c) := by
    rw [Measure.restrict_eq_zero.2 leftMeasure_Ici, Measure.restrict_eq_zero,
      Measure.map_apply_of_aemeasurable hTm measurableSet_Ici]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hT'] with y hy
    exact fun h ↦ (not_le.2 hy.2.1) h
  rw [← Measure.restrict_add_restrict_compl (μ := (rightMeasure k c).map T) measurableSet_Iio,
    ← Measure.restrict_add_restrict_compl (μ := leftMeasure k c) measurableSet_Iio, compl_Iio,
    hleft, hright]

end Pushforward

section Kernel

/-- A kernel `k` balanced at `c` with weight exponent `α`: `k ≤ 0` to the left of `c`, `k ≥ 0` to
the right, `k (x) |x - c|^α` integrable on `ℝ`, and equal masses of `|k|` on the two sides, as
elements of `[0, ∞]`. With finite masses the last condition is `∫ k = 0`. -/
structure IsBalancedKernel (k : ℝ → ℝ) (c : ℝ) (α : ℝ≥0) : Prop where
  nonpos : ∀ᵐ x, x < c → k x ≤ 0
  nonneg : ∀ᵐ x, c < x → 0 ≤ k x
  integrable : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)
  mass_eq : ∫⁻ x in Iio c, ‖k x‖ₑ = ∫⁻ x in Ioi c, ‖k x‖ₑ

variable {k T g : ℝ → ℝ} {c : ℝ} {α C : ℝ≥0} {S : Set ℝ}

/-- The weight `|x - c|^α` is continuous. -/
private theorem continuous_rpow_abs_sub (c : ℝ) (α : ℝ≥0) :
    Continuous fun x : ℝ ↦ |x - c| ^ (α : ℝ) :=
  (continuous_abs.comp (continuous_id.sub continuous_const)).rpow_const fun _ ↦ Or.inr α.2

/-- A kernel with `k (x) |x - c|^α` integrable is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_of_integrable_mul_rpow
    (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)) : AEStronglyMeasurable k := by
  have hm : Measurable fun x : ℝ ↦ (|x - c| ^ (α : ℝ))⁻¹ :=
    (continuous_rpow_abs_sub c α).measurable.inv
  refine (hint.aestronglyMeasurable.mul hm.aestronglyMeasurable).congr ?_
  have hc : ∀ᵐ x : ℝ, x ∉ ({c} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 Real.volume_singleton
  filter_upwards [hc] with x hx
  replace hx : x ≠ c := hx
  have : |x - c| ^ (α : ℝ) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.2 (sub_ne_zero.2 hx)) _).ne'
  simp [this]

/-- A balanced kernel is almost everywhere strongly measurable. -/
theorem IsBalancedKernel.aestronglyMeasurable (hk : IsBalancedKernel k c α) :
    AEStronglyMeasurable k :=
  aestronglyMeasurable_of_integrable_mul_rpow hk.integrable

/-- Centering at `c` makes `k (g - g(c))` integrable: `|k (g - g(c))| ≤ C |k| |x - c|^α` on the
support of `k`. -/
theorem integrable_mul_sub_of_holderOnWith {g : ℝ → ℝ} {C : ℝ≥0} {S : Set ℝ}
    (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)) (hα₀ : 0 < α) (hS : MeasurableSet S)
    (hkS : ∀ᵐ x, k x ≠ 0 → x ∈ S) (hcS : c ∈ S) (hg : HolderOnWith C α g S) :
    Integrable fun x ↦ k x * (g x - g c) := by
  have hGb : ∀ x ∈ S, |g x - g c| ≤ C * |x - c| ^ (α : ℝ) := fun x hx ↦ by
    simpa [Real.dist_eq] using hg.dist_le hx hcS
  have hGm : AEStronglyMeasurable (S.indicator fun x ↦ g x - g c) :=
    (aestronglyMeasurable_indicator_iff hS).2
      (((hg.continuousOn hα₀).sub continuousOn_const).aestronglyMeasurable hS)
  refine (hint.norm.const_mul C).mono'
    (((aestronglyMeasurable_of_integrable_mul_rpow hint).mul hGm).congr ?_) ?_
  · filter_upwards [hkS] with x hx
    by_cases h : k x = 0
    · simp [h]
    · simp only [Pi.mul_apply]
      rw [indicator_of_mem (hx h)]
  · filter_upwards [hkS] with x hx
    by_cases h : k x = 0
    · simp [h]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), mul_left_comm]
      exact mul_le_mul_of_nonneg_left (hGb x (hx h)) (abs_nonneg _)

/-- A balanced kernel is almost everywhere measurable. -/
private theorem IsBalancedKernel.aemeasurable (hk : IsBalancedKernel k c α) : AEMeasurable k :=
  hk.aestronglyMeasurable.aemeasurable

/-- The pointwise bound `|k x| ≤ |k x| |x - c|^α / d^α` when `|x - c| ≥ d > 0`. -/
private theorem enorm_le_enorm_mul_rpow {x d : ℝ} (hd : 0 < d) (hx : d ≤ |x - c|) :
    ‖k x‖ₑ ≤ ‖k x * |x - c| ^ (α : ℝ)‖ₑ * ENNReal.ofReal (d ^ (-(α : ℝ))) := by
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), mul_assoc]
  have h1 : 1 ≤ |x - c| ^ (α : ℝ) * d ^ (-(α : ℝ)) := by
    rw [Real.rpow_neg hd.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hd _)]
    exact Real.rpow_le_rpow hd.le hx α.2
  nlinarith [abs_nonneg (k x)]

/-- The mass of `|k|` on a measurable set at distance at least `d > 0` from `c` is finite when
`k (x) |x - c|^α` is integrable. -/
private theorem setLIntegral_ne_top_of_le_abs (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ))
    {s : Set ℝ} (hs : MeasurableSet s) {d : ℝ} (hd : 0 < d) (hsd : ∀ x ∈ s, d ≤ |x - c|) :
    ∫⁻ x in s, ‖k x‖ₑ ≠ ∞ := by
  refine (lt_of_le_of_lt ?_ (ENNReal.mul_lt_top hint.hasFiniteIntegral
    (ENNReal.ofReal_lt_top (r := d ^ (-(α : ℝ)))))).ne
  calc ∫⁻ x in s, ‖k x‖ₑ
      ≤ ∫⁻ x in s, ‖k x * |x - c| ^ (α : ℝ)‖ₑ * ENNReal.ofReal (d ^ (-(α : ℝ))) :=
        setLIntegral_mono' hs fun x hx ↦ enorm_le_enorm_mul_rpow hd (hsd x hx)
    _ = (∫⁻ x in s, ‖k x * |x - c| ^ (α : ℝ)‖ₑ) * ENNReal.ofReal (d ^ (-(α : ℝ))) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ ≤ (∫⁻ x, ‖k x * |x - c| ^ (α : ℝ)‖ₑ) * ENNReal.ofReal (d ^ (-(α : ℝ))) :=
        mul_le_mul' (setLIntegral_le_lintegral _ _) le_rfl

/-- The right tails `∫_{x ≥ y} |k|`, `y > c`, are finite when `k (x) |x - c|^α` is integrable. -/
theorem lintegral_Ici_ne_top (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)) {y : ℝ}
    (hy : c < y) : ∫⁻ x in Ici y, ‖k x‖ₑ ≠ ∞ :=
  setLIntegral_ne_top_of_le_abs hint measurableSet_Ici (sub_pos.2 hy) fun _ hx ↦
    (sub_le_sub_right hx c).trans (le_abs_self _)

/-- The left tails `∫_{t ≤ x} |k|`, `x < c`, are finite when `k (x) |x - c|^α` is integrable. -/
theorem lintegral_Iic_ne_top (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)) {x : ℝ}
    (hx : x < c) : ∫⁻ t in Iic x, ‖k t‖ₑ ≠ ∞ :=
  setLIntegral_ne_top_of_le_abs hint measurableSet_Iic (sub_pos.2 hx) fun t ht ↦
    (sub_le_sub_left ht c).trans ((le_abs_self _).trans_eq (abs_sub_comm c t))

/-- The pushforward of `|k| dx` on `(c, ∞)` under a mass-matching map is `|k| dx` on
`(-∞, c)`, for a balanced kernel. -/
theorem IsBalancedKernel.map_withDensity_eq (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) :
    ((volume.restrict (Ioi c)).withDensity fun x ↦ ‖k x‖ₑ).map T =
      (volume.restrict (Iio c)).withDensity fun x ↦ ‖k x‖ₑ :=
  Rearrangement.map_withDensity_eq hk.aemeasurable
    (fun _ hy ↦ lintegral_Ici_ne_top hk.integrable hy)
    (fun _ hx ↦ lintegral_Iic_ne_top hk.integrable hx) hk.mass_eq hT

/-- A property that holds almost everywhere on `{k ≠ 0}` holds almost everywhere for the measure
`|k| dx` on `(c, ∞)`. -/
private theorem ae_rightMeasure {P : ℝ → Prop} (hk : AEMeasurable k)
    (h : ∀ᵐ x, k x ≠ 0 → P x) : ∀ᵐ x ∂rightMeasure k c, P x := by
  rw [ae_withDensity_iff' hk.enorm.restrict]
  filter_upwards [ae_restrict_of_ae h] with x hx hw
  exact hx fun h0 ↦ hw (by simp [h0])

/-- A property that holds almost everywhere on `{k ≠ 0}` holds almost everywhere for the measure
`|k| dx` on `(-∞, c)`. -/
private theorem ae_leftMeasure {P : ℝ → Prop} (hk : AEMeasurable k)
    (h : ∀ᵐ x, k x ≠ 0 → P x) : ∀ᵐ x ∂leftMeasure k c, P x := by
  rw [ae_withDensity_iff' hk.enorm.restrict]
  filter_upwards [ae_restrict_of_ae h] with x hx hw
  exact hx fun h0 ↦ hw (by simp [h0])

/-- The integral of `φ` for the measure `|k| dx` on `(c, ∞)` is `∫_{y > c} |k(y)| φ(y) dy`. -/
private theorem integral_rightMeasure (hk : AEMeasurable k) (φ : ℝ → ℝ) :
    ∫ y, φ y ∂rightMeasure k c = ∫ y in Ioi c, |k y| * φ y := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hk.enorm.restrict
    (Eventually.of_forall fun _ ↦ enorm_lt_top)]
  simp only [toReal_enorm, Real.norm_eq_abs, smul_eq_mul]

/-- The integral of `φ` for the measure `|k| dx` on `(-∞, c)` is `∫_{x < c} |k(x)| φ(x) dx`. -/
private theorem integral_leftMeasure (hk : AEMeasurable k) (φ : ℝ → ℝ) :
    ∫ x, φ x ∂leftMeasure k c = ∫ x in Iio c, |k x| * φ x := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hk.enorm.restrict
    (Eventually.of_forall fun _ ↦ enorm_lt_top)]
  simp only [toReal_enorm, Real.norm_eq_abs, smul_eq_mul]

/-- For a balanced kernel the weight `|y - c|^α` is integrable for the measure `|k| dx` on `(c, ∞)`.
-/
private theorem integrable_rightMeasure_rpow (hk : IsBalancedKernel k c α) :
    Integrable (fun y ↦ |y - c| ^ (α : ℝ)) (rightMeasure k c) := by
  refine ⟨(continuous_rpow_abs_sub c α).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_withDensity_eq_lintegral_mul₀ hk.aemeasurable.enorm.restrict
    (continuous_rpow_abs_sub c α).enorm.aemeasurable]
  refine lt_of_le_of_lt ?_ hk.integrable.hasFiniteIntegral
  simp only [Pi.mul_apply, ← enorm_mul]
  exact setLIntegral_le_lintegral _ _

/-- For a balanced kernel the weight `|x - c|^α` is integrable for the measure `|k| dx` on
`(-∞, c)`. -/
private theorem integrable_leftMeasure_rpow (hk : IsBalancedKernel k c α) :
    Integrable (fun x ↦ |x - c| ^ (α : ℝ)) (leftMeasure k c) := by
  refine ⟨(continuous_rpow_abs_sub c α).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_withDensity_eq_lintegral_mul₀ hk.aemeasurable.enorm.restrict
    (continuous_rpow_abs_sub c α).enorm.aemeasurable]
  refine lt_of_le_of_lt ?_ hk.integrable.hasFiniteIntegral
  simp only [Pi.mul_apply, ← enorm_mul]
  exact setLIntegral_le_lintegral _ _

end Kernel

section Transport

variable {k T g : ℝ → ℝ} {c : ℝ} {α C : ℝ≥0} {S : Set ℝ}

/-- For a balanced kernel, a mass-matching map `T` pushes `|k| dx` on `(c, ∞)` forward to `|k| dx`
on `(-∞, c)`. -/
private theorem map_rightMeasure (hk : IsBalancedKernel k c α) (hT : IsMassMatching k c T) :
    (rightMeasure k c).map T = leftMeasure k c :=
  hk.map_withDensity_eq hT

/-- `φ` is integrable for the measure `|k| dx` on `(c, ∞)` if and only if `|k| φ` is integrable on
`(c, ∞)`. -/
private theorem integrable_rightMeasure_iff (hk : AEMeasurable k) {φ : ℝ → ℝ} :
    Integrable φ (rightMeasure k c) ↔ IntegrableOn (fun y ↦ |k y| * φ y) (Ioi c) := by
  rw [integrable_withDensity_iff_integrable_smul₀' hk.enorm.restrict
    (Eventually.of_forall fun _ ↦ enorm_lt_top)]
  simp only [toReal_enorm, Real.norm_eq_abs, smul_eq_mul, IntegrableOn]

/-- A mass-matching map `T` is almost everywhere measurable for the measure `|k| dx` on `(c, ∞)`. -/
private theorem aemeasurable_rightMeasure (hT : IsMassMatching k c T) :
    AEMeasurable T (rightMeasure k c) :=
  hT.aemeasurable.mono_ac (withDensity_absolutelyContinuous _ _)

/-- The change of variables of the transport lemma:
`∫_{x < c} |k(x)| φ(x) dx = ∫_{y > c} |k(y)| φ(T y) dy`, the substitution `x = T(y)` given by
the pushforward of `|k| dx` on `(c, ∞)` under `T`; no smoothness of `k` or `T` is used. -/
theorem IsBalancedKernel.integral_comp_eq (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) {φ : ℝ → ℝ}
    (hφ : AEStronglyMeasurable φ ((volume.restrict (Iio c)).withDensity fun x ↦ ‖k x‖ₑ)) :
    ∫ x in Iio c, |k x| * φ x = ∫ y in Ioi c, |k y| * φ (T y) := by
  rw [← integral_leftMeasure hk.aemeasurable, ← integral_rightMeasure hk.aemeasurable,
    ← map_rightMeasure hk hT]
  exact integral_map (aemeasurable_rightMeasure hT) (by rwa [map_rightMeasure hk hT])

/-- The change of variables of the transport lemma for `[0, ∞]`-valued integrands:
`∫⁻_{x < c} |k(x)| φ(x) dx = ∫⁻_{y > c} |k(y)| φ(T y) dy`, both sides possibly infinite
(the real form `IsBalancedKernel.integral_comp_eq` totalizes nonintegrable sides to `0`). -/
theorem IsBalancedKernel.lintegral_comp_eq (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) {φ : ℝ → ℝ≥0∞}
    (hφ : AEMeasurable φ ((volume.restrict (Iio c)).withDensity fun x ↦ ‖k x‖ₑ)) :
    ∫⁻ x in Iio c, ‖k x‖ₑ * φ x = ∫⁻ y in Ioi c, ‖k y‖ₑ * φ (T y) := by
  have hmap := map_rightMeasure hk hT
  have hTm := aemeasurable_rightMeasure hT
  have hφR : AEMeasurable (φ ∘ T) (rightMeasure k c) := by
    have h : AEMeasurable φ ((rightMeasure k c).map T) := by rwa [hmap]
    exact h.comp_aemeasurable hTm
  have e₁ := lintegral_withDensity_eq_lintegral_mul₀' hk.aemeasurable.enorm.restrict hφ
  have e₂ := lintegral_withDensity_eq_lintegral_mul₀' (μ := volume.restrict (Ioi c))
    hk.aemeasurable.enorm.restrict hφR
  simp only [Pi.mul_apply, Function.comp_apply] at e₁ e₂
  rw [← e₁, ← e₂]
  change ∫⁻ x, φ x ∂leftMeasure k c = ∫⁻ y, φ (T y) ∂rightMeasure k c
  rw [← hmap]
  exact lintegral_map' (by rwa [hmap]) hTm

/-- The two transport costs of Chen and Hou, Lemma 3.6, agree: if `L` maps the left side to the
right side and inverts `T` almost everywhere on the support of `k` to the right of `c`, then
`∫_{x < c} |k(x)| |L(x) - x|^α dx = ∫_{y > c} |k(y)| |y - T(y)|^α dy`. Values of `L` on the
gaps of the density do not matter. -/
theorem IsBalancedKernel.integral_transportCost_eq (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) {L : ℝ → ℝ} (hL : AEMeasurable L (volume.restrict (Iio c)))
    (hLT : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 → L (T y) = y) :
    ∫ x in Iio c, |k x| * |L x - x| ^ (α : ℝ) = ∫ y in Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
  have hL' : AEMeasurable L ((volume.restrict (Iio c)).withDensity fun x ↦ ‖k x‖ₑ) :=
    hL.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [hk.integral_comp_eq hT (φ := fun x ↦ |L x - x| ^ (α : ℝ))
    ((continuous_abs.measurable.comp_aemeasurable (hL'.sub aemeasurable_id)).pow_const
      _).aestronglyMeasurable]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [ae_restrict_iff' measurableSet_Ioi |>.1 hLT] with y hy hyc
  by_cases hky : k y = 0
  · simp [hky]
  · rw [hy hyc hky]

/-- The transport cost `y ↦ |y - T y|^α` is integrable for `|k| dx` on `(c, ∞)`:
`|y - T y|^α ≤ 2^α (|y - c|^α + |T y - c|^α)`, and the second term is the image of
`|x - c|^α` under the pushforward. -/
theorem IsBalancedKernel.integrableOn_transportCost (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) :
    IntegrableOn (fun y ↦ |k y| * |y - T y| ^ (α : ℝ)) (Ioi c) := by
  have hTm := aemeasurable_rightMeasure hT
  have hT' := hT.ae_rightMeasure hk.aemeasurable
  have hTc : Integrable (fun y ↦ |T y - c| ^ (α : ℝ)) (rightMeasure k c) := by
    have h := integrable_leftMeasure_rpow hk
    rw [← map_rightMeasure hk hT] at h
    exact h.comp_aemeasurable hTm
  have hcost : Integrable (fun y ↦ |y - T y| ^ (α : ℝ)) (rightMeasure k c) := by
    refine (((integrable_rightMeasure_rpow hk).add hTc).const_mul (2 ^ (α : ℝ))).mono'
      ((continuous_abs.measurable.comp_aemeasurable (aemeasurable_id.sub hTm)).pow_const
        _).aestronglyMeasurable ?_
    filter_upwards [hT'] with y hy
    obtain ⟨hyc, hTy, -⟩ := hy
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_pos (sub_pos.2 (hTy.trans hyc)), abs_of_pos (sub_pos.2 hyc),
      abs_of_neg (sub_neg.2 hTy), neg_sub, show y - T y = (y - c) + (c - T y) by ring]
    have ha := (sub_pos.2 hyc).le
    have hb := (sub_pos.2 hTy).le
    calc ((y - c) + (c - T y)) ^ (α : ℝ)
        ≤ (2 * max (y - c) (c - T y)) ^ (α : ℝ) :=
          Real.rpow_le_rpow (add_nonneg ha hb)
            (by linarith [le_max_left (y - c) (c - T y), le_max_right (y - c) (c - T y)]) α.2
      _ = 2 ^ (α : ℝ) * max (y - c) (c - T y) ^ (α : ℝ) :=
          Real.mul_rpow zero_le_two (ha.trans (le_max_left _ _))
      _ ≤ 2 ^ (α : ℝ) * ((y - c) ^ (α : ℝ) + (c - T y) ^ (α : ℝ)) := by
          gcongr
          rcases le_total (y - c) (c - T y) with h | h
          · rw [max_eq_right h]; linarith [Real.rpow_nonneg ha (α : ℝ)]
          · rw [max_eq_left h]; linarith [Real.rpow_nonneg hb (α : ℝ)]
  exact (integrable_rightMeasure_iff hk.aemeasurable).1 hcost

/-- The transport lemma of Chen and Hou (Part I, Lemma 3.6) in absolute form. Let `k` be balanced
at `c` with exponent `α > 0`, let `T` match outer masses, and let `g` be `α`-Hölder with
constant `C` on a measurable set `S` containing `c` and, up to a null set, the support of `k`.
Then `|∫ k (g - g(c))| ≤ C ∫_{y > c} |k(y)| |y - T(y)|^α dy`. -/
theorem IsBalancedKernel.abs_integral_mul_sub_le (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) (hα₀ : 0 < α) (hS : MeasurableSet S)
    (hkS : ∀ᵐ x, k x ≠ 0 → x ∈ S) (hcS : c ∈ S) (hg : HolderOnWith C α g S) :
    |∫ x, k x * (g x - g c)| ≤ C * ∫ y in Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
  set G : ℝ → ℝ := fun x ↦ g x - g c with hG
  have hkm := hk.aemeasurable
  have hmap := map_rightMeasure hk hT
  have hTm := aemeasurable_rightMeasure hT
  have hT' := hT.ae_rightMeasure hkm
  have hGb : ∀ x ∈ S, |G x| ≤ C * |x - c| ^ (α : ℝ) := fun x hx ↦ by
    simpa [G, Real.dist_eq] using hg.dist_le hx hcS
  have hGm : AEStronglyMeasurable (S.indicator G) :=
    (aestronglyMeasurable_indicator_iff hS).2
      (((hg.continuousOn hα₀).sub continuousOn_const).aestronglyMeasurable hS)
  have hacR : rightMeasure k c ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hacL : leftMeasure k c ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hSR : ∀ᵐ x ∂rightMeasure k c, x ∈ S := ae_rightMeasure hkm hkS
  have hSL : ∀ᵐ x ∂leftMeasure k c, x ∈ S := ae_leftMeasure hkm hkS
  -- `G` is integrable for both measures: `|G| ≤ C |x - c|^α` on `S`
  have hGi : ∀ μ : Measure ℝ, μ ≪ volume → (∀ᵐ x ∂μ, x ∈ S) →
      Integrable (fun x ↦ |x - c| ^ (α : ℝ)) μ → Integrable G μ := fun μ hac hSμ hw ↦
    (hw.const_mul C).mono' ((hGm.mono_ac hac).congr
      (by filter_upwards [hSμ] with x hx using indicator_of_mem hx G))
      (by filter_upwards [hSμ] with x hx using hGb x hx)
  have hGiR := hGi _ hacR hSR (integrable_rightMeasure_rpow hk)
  have hGiL := hGi _ hacL hSL (integrable_leftMeasure_rpow hk)
  have hGTi : Integrable (fun y ↦ G (T y)) (rightMeasure k c) :=
    (hmap ▸ hGiL : Integrable G ((rightMeasure k c).map T)).comp_aemeasurable hTm
  have hTS : ∀ᵐ y ∂rightMeasure k c, T y ∈ S := ae_of_ae_map hTm (by rwa [hmap])
  -- the integral of `k G` is the difference of the two sides
  have hkG : Integrable fun x ↦ k x * G x :=
    integrable_mul_sub_of_holderOnWith hk.integrable hα₀ hS hkS hcS hg
  have hsplit : ∫ x, k x * G x = ∫ y, G y ∂rightMeasure k c - ∫ x, G x ∂leftMeasure k c := by
    rw [integral_rightMeasure hkm, integral_leftMeasure hkm,
      ← integral_add_compl measurableSet_Iio hkG, compl_Iio,
      setIntegral_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := c)).symm]
    have hl : ∫ x in Iio c, k x * G x = -∫ x in Iio c, |k x| * G x := by
      rw [← integral_neg]
      refine setIntegral_congr_ae measurableSet_Iio ?_
      filter_upwards [hk.nonpos] with x hx hxc
      rw [abs_of_nonpos (hx hxc)]
      ring
    have hr : ∫ x in Ioi c, k x * G x = ∫ x in Ioi c, |k x| * G x := by
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      filter_upwards [hk.nonneg] with x hx hxc
      rw [abs_of_nonneg (hx hxc)]
    rw [hl, hr]
    ring
  have hcv : ∫ x, G x ∂leftMeasure k c = ∫ y, G (T y) ∂rightMeasure k c := by
    rw [← hmap]
    exact integral_map hTm (by rw [hmap]; exact hGiL.aestronglyMeasurable)
  have hcost := (integrable_rightMeasure_iff hkm).2 (hk.integrableOn_transportCost hT)
  rw [hsplit, hcv, ← integral_sub hGiR hGTi]
  calc |∫ y, G y - G (T y) ∂rightMeasure k c| ≤ ∫ y, |G y - G (T y)| ∂rightMeasure k c :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, C * |y - T y| ^ (α : ℝ) ∂rightMeasure k c := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
          (hcost.const_mul _) ?_
        filter_upwards [hSR, hTS] with y hy hTy
        simpa [G, Real.dist_eq] using hg.dist_le hy hTy
    _ = C * ∫ y in Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
        rw [integral_const_mul, integral_rightMeasure hkm]

/-- The transport lemma on a measurable set `I ∋ c`, such as a bounded interval `(a, b)` or a
half-line: the hypotheses are those of `IsBalancedKernel.abs_integral_mul_sub_le` for the kernel
`k` restricted to `I`, and `g` need only be Hölder on a measurable `S ⊇ I`. -/
theorem IsBalancedKernel.abs_setIntegral_mul_sub_le {I : Set ℝ} (hI : MeasurableSet I)
    (hk : IsBalancedKernel (I.indicator k) c α) (hT : IsMassMatching (I.indicator k) c T)
    (hα₀ : 0 < α) (hS : MeasurableSet S) (hIS : I ⊆ S) (hcS : c ∈ S)
    (hg : HolderOnWith C α g S) :
    |∫ x in I, k x * (g x - g c)| ≤ C * ∫ y in I ∩ Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
  have main := hk.abs_integral_mul_sub_le hT hα₀ hS
    (Eventually.of_forall fun x hx ↦ hIS (mem_of_indicator_ne_zero hx)) hcS hg
  have hlhs : ∫ x, I.indicator k x * (g x - g c) = ∫ x in I, k x * (g x - g c) := by
    rw [← integral_indicator hI]
    exact congrArg _ (funext fun x ↦ by by_cases hx : x ∈ I <;> simp [hx])
  have hrhs : ∫ y in Ioi c, |I.indicator k y| * |y - T y| ^ (α : ℝ) =
      ∫ y in I ∩ Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
    rw [inter_comm, ← setIntegral_indicator hI]
    exact congrArg _ (funext fun y ↦ by by_cases hy : y ∈ I <;> simp [hy])
  rwa [hlhs, hrhs] at main

end Transport

section PrincipalValue

variable {k T g : ℝ → ℝ} {c : ℝ} {α C : ℝ≥0} {S : Set ℝ}

/-- The truncation region `{x | ε < |x - c|}` is measurable. -/
private theorem measurableSet_truncation (c ε : ℝ) : MeasurableSet {x : ℝ | ε < |x - c|} :=
  measurableSet_lt measurable_const
    (continuous_abs.comp (continuous_id.sub continuous_const)).measurable

/-- Away from `c` the kernel is integrable: `|k| ≤ ε^{-α} |k| |x - c|^α` on `{|x - c| > ε}`. -/
theorem integrableOn_truncation (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)) {ε : ℝ}
    (hε : 0 < ε) : IntegrableOn k {x | ε < |x - c|} := by
  refine ((hint.norm.const_mul (ε ^ (-(α : ℝ)))).integrableOn).mono'
    (aestronglyMeasurable_of_integrable_mul_rpow hint).restrict ?_
  filter_upwards [ae_restrict_mem (measurableSet_truncation c ε)] with x hx
  have h := enorm_le_enorm_mul_rpow (k := k) (α := α) hε (le_of_lt hx)
  rw [Real.enorm_eq_ofReal_abs, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at h
  rw [Real.norm_eq_abs, mul_comm]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg hε.le _))).1 h

/-- Principal values. If `∫_{|x - c| > ε} k → 0` as `ε → 0⁺`, the truncated integrals of `k g`
converge to `∫ k (g - g(c))`. So the absolute form of the transport lemma bounds the principal
value `PV ∫ k g` of Chen and Hou. -/
theorem tendsto_integral_mul_of_tendsto (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ))
    (hα₀ : 0 < α) (hS : MeasurableSet S) (hkS : ∀ᵐ x, k x ≠ 0 → x ∈ S) (hcS : c ∈ S)
    (hg : HolderOnWith C α g S)
    (hpv : Tendsto (fun ε ↦ ∫ x in {x | ε < |x - c|}, k x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε ↦ ∫ x in {x | ε < |x - c|}, k x * g x) (𝓝[>] 0)
      (𝓝 (∫ x, k x * (g x - g c))) := by
  have hkG := integrable_mul_sub_of_holderOnWith hint hα₀ hS hkS hcS hg
  have h₁ : Tendsto (fun ε ↦ ∫ x in {x | ε < |x - c|}, k x * (g x - g c)) (𝓝[>] 0)
      (𝓝 (∫ x, k x * (g x - g c))) := by
    simp_rw [← integral_indicator (measurableSet_truncation c _)]
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖k x * (g x - g c)‖)
      (Eventually.of_forall fun ε ↦
        hkG.aestronglyMeasurable.indicator (measurableSet_truncation c ε))
      (Eventually.of_forall fun ε ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)
      hkG.norm (Eventually.of_forall fun x ↦ ?_)
    rcases eq_or_ne x c with rfl | hx
    · simp [Set.indicator_apply]
    · have hpos : 0 < |x - c| := abs_pos.2 (sub_ne_zero.2 hx)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hpos)] with ε hε
      rw [indicator_of_mem (show x ∈ {x | ε < |x - c|} from hε)]
  have h₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ x in {x | ε < |x - c|}, k x * g x =
      (∫ x in {x | ε < |x - c|}, k x * (g x - g c)) + g c * ∫ x in {x | ε < |x - c|}, k x := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← integral_const_mul, ← integral_add hkG.integrableOn
      ((integrableOn_truncation hint hε).const_mul _)]
    exact congrArg _ (funext fun x ↦ by ring)
  simpa only [mul_zero, add_zero] using
    (h₁.add (hpv.const_mul (g c))).congr' (h₂.mono fun ε h ↦ h.symm)

/-- On a set where `k ≥ 0` almost everywhere, `∫_s k` is the real part of `∫⁻_s |k|`. -/
private theorem setIntegral_eq_toReal_of_nonneg {s : Set ℝ} (hs : MeasurableSet s)
    (hk : AEStronglyMeasurable k) (h : ∀ᵐ x, x ∈ s → 0 ≤ k x) :
    ∫ x in s, k x = (∫⁻ x in s, ‖k x‖ₑ).toReal := by
  rw [← integral_norm_eq_lintegral_enorm hk.restrict]
  refine setIntegral_congr_ae hs (h.mono fun x hx hxs ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hx hxs)]

/-- On a set where `k ≤ 0` almost everywhere, `∫_s k` is minus the real part of `∫⁻_s |k|`. -/
private theorem setIntegral_eq_neg_toReal_of_nonpos {s : Set ℝ} (hs : MeasurableSet s)
    (hk : AEStronglyMeasurable k) (h : ∀ᵐ x, x ∈ s → k x ≤ 0) :
    ∫ x in s, k x = -(∫⁻ x in s, ‖k x‖ₑ).toReal := by
  rw [← integral_norm_eq_lintegral_enorm hk.restrict, ← integral_neg]
  refine setIntegral_congr_ae hs (h.mono fun x hx hxs ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonpos (hx hxs), neg_neg]

/-- Two increasing limits with finite terms whose difference of real parts tends to zero are
equal, also when they are infinite. -/
private theorem eq_of_tendsto_toReal_sub {a b : ℕ → ℝ≥0∞} {A B : ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) (haA : ∀ n, a n ≤ A)
    (hbB : ∀ n, b n ≤ B) (haf : ∀ n, a n ≠ ∞) (hbf : ∀ n, b n ≠ ∞)
    (h : Tendsto (fun n ↦ (a n).toReal - (b n).toReal) atTop (𝓝 0)) : A = B := by
  wlog hle : A ≤ B generalizing a b A B
  · exact (this hb ha hbB haA hbf haf (by simpa using h.neg) (le_of_not_ge hle)).symm
  refine hle.antisymm (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨r, hAr, hrB⟩ := exists_between hlt
  obtain ⟨s, hrs, hsB⟩ := exists_between hrB
  have hs : s ≠ ∞ := hsB.ne_top
  have hr : r ≠ ∞ := (hrs.trans hsB).ne_top
  have hδ : r.toReal - s.toReal < 0 := sub_neg.2 ((ENNReal.toReal_lt_toReal hr hs).2 hrs)
  obtain ⟨n, hn₁, hn₂⟩ := ((hb.eventually (lt_mem_nhds hsB)).and
    (h.eventually (lt_mem_nhds hδ))).exists
  have h₁ : (a n).toReal ≤ r.toReal := ENNReal.toReal_mono hr ((haA n).trans hAr.le)
  have h₂ : s.toReal < (b n).toReal := (ENNReal.toReal_lt_toReal hs (hbf n)).2 hn₁
  linarith

/-- Zero principal-value mass gives equal masses on the two sides (both possibly infinite), so a
kernel with the sign and integrability hypotheses of Chen and Hou, Lemma 3.6, is balanced. -/
theorem isBalancedKernel_of_tendsto (hneg : ∀ᵐ x, x < c → k x ≤ 0)
    (hpos : ∀ᵐ x, c < x → 0 ≤ k x) (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ))
    (hpv : Tendsto (fun ε ↦ ∫ x in {x | ε < |x - c|}, k x) (𝓝[>] 0) (𝓝 0)) :
    IsBalancedKernel k c α := by
  refine ⟨hneg, hpos, hint, ?_⟩
  set ρ : Measure ℝ := volume.withDensity fun x ↦ ‖k x‖ₑ
  have hkm := aestronglyMeasurable_of_integrable_mul_rpow hint
  set ε : ℕ → ℝ := fun n ↦ 1 / (n + 1)
  have hε : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεt : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hε⟩
  -- the masses on the two sides of the truncation
  have hR : Tendsto (fun n ↦ ρ (Ioi (c + ε n))) atTop (𝓝 (ρ (Ioi c))) := by
    have hU : ⋃ n, Ioi (c + ε n) = Ioi c :=
      Subset.antisymm (iUnion_subset fun n ↦ Ioi_subset_Ioi (by linarith [hε n])) fun y hy ↦ by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
        exact mem_iUnion.2 ⟨n, show c + ε n < y by linarith⟩
    rw [← hU]
    exact tendsto_measure_iUnion_atTop (μ := ρ) (s := fun n ↦ Ioi (c + ε n))
      fun _ _ hmn ↦ Ioi_subset_Ioi (by simp only [ε]; gcongr)
  have hL : Tendsto (fun n ↦ ρ (Iio (c - ε n))) atTop (𝓝 (ρ (Iio c))) := by
    have hU : ⋃ n, Iio (c - ε n) = Iio c :=
      Subset.antisymm (iUnion_subset fun n ↦ Iio_subset_Iio (by linarith [hε n])) fun y hy ↦ by
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
        exact mem_iUnion.2 ⟨n, show y < c - ε n by linarith⟩
    rw [← hU]
    exact tendsto_measure_iUnion_atTop (μ := ρ) (s := fun n ↦ Iio (c - ε n))
      fun _ _ hmn ↦ Iio_subset_Iio (by simp only [ε]; gcongr)
  have hρ : ∀ s : Set ℝ, MeasurableSet s → ρ s = ∫⁻ x in s, ‖k x‖ₑ := fun s hs ↦
    withDensity_apply _ hs
  have hfinR : ∀ n, ρ (Ioi (c + ε n)) ≠ ∞ := fun n ↦ by
    rw [hρ _ measurableSet_Ioi]
    exact ne_top_of_le_ne_top (lintegral_Ici_ne_top hint (by linarith [hε n]))
      (lintegral_mono_set Ioi_subset_Ici_self)
  have hfinL : ∀ n, ρ (Iio (c - ε n)) ≠ ∞ := fun n ↦ by
    rw [hρ _ measurableSet_Iio]
    exact ne_top_of_le_ne_top (lintegral_Iic_ne_top hint (by linarith [hε n]))
      (lintegral_mono_set Iio_subset_Iic_self)
  -- the truncated integral is the difference of the two masses
  have htrunc : ∀ n, ∫ x in {x | ε n < |x - c|}, k x =
      (ρ (Ioi (c + ε n))).toReal - (ρ (Iio (c - ε n))).toReal := by
    intro n
    have hU : {x | ε n < |x - c|} = Iio (c - ε n) ∪ Ioi (c + ε n) := by
      ext x
      simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
      exact or_comm.trans (or_congr ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩
        ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩)
    have hint' := integrableOn_truncation hint (hε n)
    rw [hU] at hint'
    rw [hU, setIntegral_union ((Iio_disjoint_Ici (by linarith [hε n])).mono_right
        Ioi_subset_Ici_self) measurableSet_Ioi (hint'.mono_set subset_union_left)
      (hint'.mono_set subset_union_right)]
    rw [setIntegral_eq_toReal_of_nonneg measurableSet_Ioi hkm
        (hpos.mono fun x hx hxc ↦ hx (by linarith [mem_Ioi.1 hxc, hε n])),
      setIntegral_eq_neg_toReal_of_nonpos measurableSet_Iio hkm
        (hneg.mono fun x hx hxc ↦ hx (by linarith [mem_Iio.1 hxc, hε n])),
      ← hρ _ measurableSet_Ioi, ← hρ _ measurableSet_Iio]
    ring
  rw [← hρ _ measurableSet_Iio, ← hρ _ measurableSet_Ioi]
  exact (eq_of_tendsto_toReal_sub hR hL (fun n ↦ measure_mono (Ioi_subset_Ioi (by
      linarith [hε n]))) (fun n ↦ measure_mono (Iio_subset_Iio (by linarith [hε n])))
    hfinR hfinL ((hpv.comp hεt).congr htrunc)).symm

/-- The transport lemma of Chen and Hou (Part I, Lemma 3.6) for the principal value. With the
hypotheses of `IsBalancedKernel.abs_integral_mul_sub_le` and zero principal-value mass of `k`,
the principal value `v = lim_{ε → 0⁺} ∫_{|x - c| > ε} k g` satisfies
`|v| ≤ C ∫_{y > c} |k(y)| |y - T(y)|^α dy`. -/
theorem IsBalancedKernel.abs_le_of_tendsto (hk : IsBalancedKernel k c α)
    (hT : IsMassMatching k c T) (hα₀ : 0 < α) (hS : MeasurableSet S)
    (hkS : ∀ᵐ x, k x ≠ 0 → x ∈ S) (hcS : c ∈ S) (hg : HolderOnWith C α g S)
    (hpv : Tendsto (fun ε ↦ ∫ x in {x | ε < |x - c|}, k x) (𝓝[>] 0) (𝓝 0)) {v : ℝ}
    (hv : Tendsto (fun ε ↦ ∫ x in {x | ε < |x - c|}, k x * g x) (𝓝[>] 0) (𝓝 v)) :
    |v| ≤ C * ∫ y in Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
  rw [tendsto_nhds_unique hv
    (tendsto_integral_mul_of_tendsto hk.integrable hα₀ hS hkS hcS hg hpv)]
  exact hk.abs_integral_mul_sub_le hT hα₀ hS hkS hcS hg

end PrincipalValue

section Integrable

variable {k T g : ℝ → ℝ} {c : ℝ} {α C : ℝ≥0} {S : Set ℝ}

/-- For an integrable kernel with `∫ k = 0`, matching outer masses is the condition
`∫_{T y}^{y} k = 0` of Chen and Hou, Lemma 3.6. -/
theorem isMassMatching_of_integral_eq_zero (hk : Integrable k)
    (hneg : ∀ᵐ x, x < c → k x ≤ 0) (hpos : ∀ᵐ x, c < x → 0 ≤ k x) (hzero : ∫ x, k x = 0)
    (hTm : AEMeasurable T (volume.restrict (Ioi c)))
    (hTlt : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 → T y < c)
    (hTeq : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 → ∫ x in T y..y, k x = 0) :
    IsMassMatching k c T := by
  refine ⟨hTm, hTlt, ?_⟩
  filter_upwards [hTlt, hTeq, ae_restrict_mem measurableSet_Ioi] with y hlt heq hyc hky
  have hTy := hlt hky
  have hyc' : c < y := hyc
  have hTyy : T y ≤ y := (hTy.trans hyc').le
  -- split `ℝ` at `T y` and `y`
  have hsplit : ∫ x, k x = (∫ x in Iic (T y), k x) + (∫ x in Ioc (T y) y, k x) +
      ∫ x in Ioi y, k x := by
    rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hk.integrableOn
        hk.integrableOn, Iic_union_Ioc_eq_Iic hTyy, ← setIntegral_union (Iic_disjoint_Ioi le_rfl)
        measurableSet_Ioi hk.integrableOn hk.integrableOn, Iic_union_Ioi, setIntegral_univ]
  have hmid : ∫ x in Ioc (T y) y, k x = 0 := (intervalIntegral.integral_of_le hTyy).symm.trans
    (heq hky)
  have hsum : (∫ x in Iic (T y), k x) + ∫ x in Ioi y, k x = 0 := by linarith
  rw [setIntegral_eq_neg_toReal_of_nonpos measurableSet_Iic hk.aestronglyMeasurable
      (hneg.mono fun x hx hxT ↦ hx (lt_of_le_of_lt (mem_Iic.1 hxT) hTy)),
    setIntegral_eq_toReal_of_nonneg measurableSet_Ioi hk.aestronglyMeasurable
      (hpos.mono fun x hx hxy ↦ hx (hyc'.trans (mem_Ioi.1 hxy))),
    setLIntegral_congr (Ioi_ae_eq_Ici (μ := volume) (a := y))] at hsum
  have hfin : ∀ s : Set ℝ, ∫⁻ x in s, ‖k x‖ₑ ≠ ∞ := fun s ↦
    (hk.integrableOn (s := s)).hasFiniteIntegral.ne
  exact (ENNReal.toReal_eq_toReal_iff' (hfin _) (hfin _)).1 (by linarith)

/-- An integrable kernel with the sign conditions, `∫ k = 0` and `k (x) |x - c|^α` integrable is
balanced. -/
theorem isBalancedKernel_of_integral_eq_zero (hk : Integrable k)
    (hneg : ∀ᵐ x, x < c → k x ≤ 0) (hpos : ∀ᵐ x, c < x → 0 ≤ k x) (hzero : ∫ x, k x = 0)
    (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ)) : IsBalancedKernel k c α := by
  refine ⟨hneg, hpos, hint, ?_⟩
  have hsplit : ∫ x, k x = (∫ x in Iio c, k x) + ∫ x in Ioi c, k x := by
    rw [← integral_add_compl measurableSet_Iio hk, compl_Iio,
      setIntegral_congr_set (Ioi_ae_eq_Ici (μ := volume) (a := c)).symm]
  rw [setIntegral_eq_neg_toReal_of_nonpos measurableSet_Iio hk.aestronglyMeasurable hneg,
    setIntegral_eq_toReal_of_nonneg measurableSet_Ioi hk.aestronglyMeasurable hpos, hzero] at hsplit
  have hfin : ∀ s : Set ℝ, ∫⁻ x in s, ‖k x‖ₑ ≠ ∞ := fun s ↦
    (hk.integrableOn (s := s)).hasFiniteIntegral.ne
  exact (ENNReal.toReal_eq_toReal_iff' (hfin _) (hfin _)).1 (by linarith)

/-- The transport lemma of Chen and Hou (Part I, Lemma 3.6) for an integrable kernel with
`∫ k = 0`: `|∫ k g| ≤ C ∫_{y > c} |k(y)| |y - T(y)|^α dy` when
`∫_{T y}^{y} k = 0` on the support of `k` to the right of `c`. -/
theorem abs_integral_mul_le_of_integral_eq_zero (hk : Integrable k)
    (hneg : ∀ᵐ x, x < c → k x ≤ 0) (hpos : ∀ᵐ x, c < x → 0 ≤ k x) (hzero : ∫ x, k x = 0)
    (hint : Integrable fun x ↦ k x * |x - c| ^ (α : ℝ))
    (hTm : AEMeasurable T (volume.restrict (Ioi c)))
    (hTlt : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 → T y < c)
    (hTeq : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 → ∫ x in T y..y, k x = 0)
    (hα₀ : 0 < α) (hS : MeasurableSet S) (hkS : ∀ᵐ x, k x ≠ 0 → x ∈ S)
    (hcS : c ∈ S) (hg : HolderOnWith C α g S) :
    |∫ x, k x * g x| ≤ C * ∫ y in Ioi c, |k y| * |y - T y| ^ (α : ℝ) := by
  have hkG := integrable_mul_sub_of_holderOnWith hint hα₀ hS hkS hcS hg
  have h : ∫ x, k x * g x = ∫ x, k x * (g x - g c) := by
    have : (fun x ↦ k x * g x) = fun x ↦ k x * (g x - g c) + g c * k x := by
      ext x
      ring
    rw [this, integral_add hkG (hk.const_mul _), integral_const_mul, hzero, mul_zero, add_zero]
  rw [h]
  exact (isBalancedKernel_of_integral_eq_zero hk hneg hpos hzero hint).abs_integral_mul_sub_le
    (isMassMatching_of_integral_eq_zero hk hneg hpos hzero hTm hTlt hTeq) hα₀ hS hkS hcS hg

end Integrable

section Reflection

variable {k T g : ℝ → ℝ} {c : ℝ} {α C : ℝ≥0} {S : Set ℝ}

/-- The reflection `x ↦ 2c - x` preserves Lebesgue measure. -/
private theorem measurePreserving_reflect (c : ℝ) :
    MeasurePreserving (fun x : ℝ ↦ 2 * c - x) volume volume :=
  Measure.measurePreserving_sub_left volume (2 * c)

/-- The reflection `x ↦ 2c - x` is a measurable embedding. -/
private theorem measurableEmbedding_reflect (c : ℝ) :
    MeasurableEmbedding fun x : ℝ ↦ 2 * c - x :=
  (Homeomorph.subLeft (2 * c)).measurableEmbedding

/-- Under the reflection `x ↦ 2c - x` the preimage of `(-∞, c)` is `(c, ∞)`. -/
private theorem reflect_preimage_Iio (c : ℝ) : (fun x : ℝ ↦ 2 * c - x) ⁻¹' Iio c = Ioi c := by
  rw [preimage_const_sub_Iio, two_mul, add_sub_cancel_right]

/-- Under the reflection `x ↦ 2c - x` the preimage of `(c, ∞)` is `(-∞, c)`. -/
private theorem reflect_preimage_Ioi (c : ℝ) : (fun x : ℝ ↦ 2 * c - x) ⁻¹' Ioi c = Iio c := by
  rw [preimage_const_sub_Ioi, two_mul, add_sub_cancel_right]

/-- The mass of the reflected kernel on a set is the mass of `k` on the reflected set. -/
private theorem lintegral_reflect (s : Set ℝ) :
    ∫⁻ x in (fun x : ℝ ↦ 2 * c - x) ⁻¹' s, ‖-k (2 * c - x)‖ₑ = ∫⁻ y in s, ‖k y‖ₑ := by
  simp only [enorm_neg]
  exact (measurePreserving_reflect c).setLIntegral_comp_preimage_emb
    (measurableEmbedding_reflect c) (fun y ↦ ‖k y‖ₑ) s

/-- The reflection of a balanced kernel, `x ↦ -k(2c - x)`, is balanced. -/
private theorem IsBalancedKernel.reflect (hk : IsBalancedKernel k c α) :
    IsBalancedKernel (fun x ↦ -k (2 * c - x)) c α := by
  have hq := (measurePreserving_reflect c).quasiMeasurePreserving
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hq.ae hk.nonneg] with x hx hxc
    exact neg_nonpos.2 (hx (by linarith))
  · filter_upwards [hq.ae hk.nonpos] with x hx hxc
    exact neg_nonneg.2 (hx (by linarith))
  · refine ((measurePreserving_reflect c).integrable_comp_of_integrable hk.integrable).neg.congr
      (Eventually.of_forall fun x ↦ ?_)
    simp only [Function.comp_apply, Pi.neg_apply, neg_mul]
    rw [show 2 * c - x - c = -(x - c) by ring, abs_neg]
  · have e₁ : ∫⁻ x in Iio c, ‖-k (2 * c - x)‖ₑ = ∫⁻ y in Ioi c, ‖k y‖ₑ := by
      rw [← reflect_preimage_Ioi c]
      exact lintegral_reflect _
    have e₂ : ∫⁻ x in Ioi c, ‖-k (2 * c - x)‖ₑ = ∫⁻ y in Iio c, ‖k y‖ₑ := by
      rw [← reflect_preimage_Iio c]
      exact lintegral_reflect _
    rw [e₁, e₂]
    exact hk.mass_eq.symm

/-- The left-hand form of the transport lemma of Chen and Hou (Part I, Lemma 3.6): with a map `T`
from the support of `k` on `(-∞, c)` to `(c, ∞)` matching outer masses,
`∫_{t ≥ T x} |k| = ∫_{t ≤ x} |k|`, the same bound holds with the cost
`∫_{x < c} |k(x)| |T(x) - x|^α dx`. The proof reflects through `c`. -/
theorem IsBalancedKernel.abs_integral_mul_sub_le_left (hk : IsBalancedKernel k c α)
    (hTm : AEMeasurable T (volume.restrict (Iio c)))
    (hTgt : ∀ᵐ x ∂volume.restrict (Iio c), k x ≠ 0 → c < T x)
    (hTeq : ∀ᵐ x ∂volume.restrict (Iio c), k x ≠ 0 →
      ∫⁻ t in Ici (T x), ‖k t‖ₑ = ∫⁻ t in Iic x, ‖k t‖ₑ)
    (hα₀ : 0 < α) (hS : MeasurableSet S) (hkS : ∀ᵐ x, k x ≠ 0 → x ∈ S)
    (hcS : c ∈ S) (hg : HolderOnWith C α g S) :
    |∫ x, k x * (g x - g c)| ≤ C * ∫ x in Iio c, |k x| * |T x - x| ^ (α : ℝ) := by
  set r : ℝ → ℝ := fun x ↦ 2 * c - x with hr_def
  have hmp := measurePreserving_reflect c
  have hemb := measurableEmbedding_reflect c
  have hq := hmp.quasiMeasurePreserving
  have hrr : MeasurePreserving r (volume.restrict (Ioi c)) (volume.restrict (Iio c)) := by
    have := hmp.restrict_preimage_emb hemb (Iio c)
    rwa [reflect_preimage_Iio] at this
  have hc : r c = c := by simp only [r]; ring
  have hT' : IsMassMatching (fun x ↦ -k (r x)) c (fun y ↦ r (T (r y))) := by
    refine ⟨(measurable_const.sub measurable_id).comp_aemeasurable
      (hTm.comp_quasiMeasurePreserving hrr.quasiMeasurePreserving), ?_, ?_⟩
    · filter_upwards [hrr.quasiMeasurePreserving.ae hTgt] with y hy hky
      have := hy (fun h ↦ hky (by simp [h]))
      simp only [r] at this ⊢
      linarith
    · filter_upwards [hrr.quasiMeasurePreserving.ae hTeq] with y hy hky
      have h := hy (fun h ↦ hky (by simp [h]))
      simp only [r]
      rw [← preimage_const_sub_Ici, show Ici y = (fun x : ℝ ↦ 2 * c - x) ⁻¹' Iic (2 * c - y) by
          rw [preimage_const_sub_Iic, sub_sub_cancel], lintegral_reflect, lintegral_reflect]
      exact h
  have hg' : HolderOnWith C α (fun x ↦ g (r x)) (r ⁻¹' S) := fun x hx y hy ↦ by
    simpa only [r, edist_dist, Real.dist_eq, sub_sub_sub_cancel_left, abs_sub_comm y x] using
      hg (r x) hx (r y) hy
  have hkS' : ∀ᵐ x, -k (r x) ≠ 0 → x ∈ r ⁻¹' S := by
    filter_upwards [hq.ae hkS] with x hx hkx
    exact hx (fun h ↦ hkx (by simpa [r] using h))
  have hcS' : c ∈ r ⁻¹' S := by simpa only [mem_preimage, hc] using hcS
  have hS' : MeasurableSet (r ⁻¹' S) := (measurable_const.sub measurable_id) hS
  have main := hk.reflect.abs_integral_mul_sub_le hT' hα₀ hS' hkS' hcS' hg'
  have hlhs : ∫ x, -k (r x) * (g (r x) - g (r c)) = -∫ x, k x * (g x - g c) := by
    rw [hc, ← integral_sub_left_eq_self (fun u ↦ k u * (g u - g c)) volume (2 * c),
      ← integral_neg]
    congr 1
    ext x
    simp only [r]
    ring
  have hrhs : ∫ y in Ioi c, |-k (r y)| * |y - r (T (r y))| ^ (α : ℝ) =
      ∫ x in Iio c, |k x| * |T x - x| ^ (α : ℝ) := by
    have h := hmp.setIntegral_preimage_emb hemb (fun x ↦ |k x| * |T x - x| ^ (α : ℝ)) (Iio c)
    rw [reflect_preimage_Iio] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    simp only [r, abs_neg]
    rw [show y - (2 * c - T (2 * c - y)) = T (2 * c - y) - (2 * c - y) by ring]
  rwa [hlhs, abs_neg, hrhs] at main

end Reflection

section Canonical

variable {k : ℝ → ℝ} {c : ℝ} {α : ℝ≥0}

/-- The canonical transport map of a kernel balanced at `c`: the supremum of the points `x < c`
whose left mass `∫_{t ≤ x} |k|` is at most the right mass `∫_{t ≥ y} |k|`. When the right mass
of `y` lies strictly between `0` and the total mass, which holds for almost every `y > c` with
`k y ≠ 0`, the supremum is attained, lies below `c`, and has left mass equal to the right mass
of `y`; this is `IsBalancedKernel.isMassMatching_transportMap`. For other `y` the value carries
no meaning (it may be `c`, or `0` for an empty set). -/
def transportMap (k : ℝ → ℝ) (c y : ℝ) : ℝ :=
  sSup {x | x < c ∧ ∫⁻ t in Iic x, ‖k t‖ₑ ≤ ∫⁻ t in Ici y, ‖k t‖ₑ}

/-- Left masses tend to zero at `-∞`: below any positive level there is a point. -/
private theorem exists_lintegral_Iic_lt {x₁ : ℝ} (hx₁ : ∫⁻ t in Iic x₁, ‖k t‖ₑ ≠ ∞)
    {s : ℝ≥0∞} (hs₀ : 0 < s) : ∃ x₂, ∫⁻ t in Iic x₂, ‖k t‖ₑ < s := by
  set ρ : Measure ℝ := volume.withDensity fun x ↦ ‖k x‖ₑ
  have hρ : ∀ u : Set ℝ, MeasurableSet u → ρ u = ∫⁻ t in u, ‖k t‖ₑ := fun u hu ↦
    withDensity_apply _ hu
  have hanti : Antitone fun n : ℕ ↦ Iic (x₁ - n) := fun _ _ hmn ↦ Iic_subset_Iic.2 (by gcongr)
  have htend := tendsto_measure_iInter_atTop (μ := ρ)
    (fun n ↦ measurableSet_Iic.nullMeasurableSet) hanti
    ⟨0, by rw [hρ _ measurableSet_Iic]; simpa using hx₁⟩
  have hempty : (⋂ n : ℕ, Iic (x₁ - n)) = ∅ := eq_empty_of_forall_notMem fun y hy ↦ by
    obtain ⟨n, hn⟩ := exists_nat_gt (x₁ - y)
    linarith [mem_Iic.1 (mem_iInter.1 hy n)]
  rw [hempty, measure_empty] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hs₀)).exists
  exact ⟨x₁ - n, by rwa [← hρ _ measurableSet_Iic]⟩

/-- The left distribution function reaches every level strictly between `0` and the left mass,
at the largest point below that level. -/
private theorem lintegral_Iic_sSup_eq (hL : ∀ x, x < c → ∫⁻ t in Iic x, ‖k t‖ₑ ≠ ∞)
    {s : ℝ≥0∞} (hs₀ : 0 < s) (hsM : s < ∫⁻ t in Iio c, ‖k t‖ₑ) :
    sSup {x | x < c ∧ ∫⁻ t in Iic x, ‖k t‖ₑ ≤ s} < c ∧
      ∫⁻ t in Iic (sSup {x | x < c ∧ ∫⁻ t in Iic x, ‖k t‖ₑ ≤ s}), ‖k t‖ₑ = s := by
  set ρ : Measure ℝ := volume.withDensity fun x ↦ ‖k x‖ₑ
  have hρ : ∀ u : Set ℝ, MeasurableSet u → ρ u = ∫⁻ t in u, ‖k t‖ₑ := fun u hu ↦
    withDensity_apply _ hu
  have hatom : ∀ x, ρ {x} = 0 := fun x ↦
    withDensity_absolutelyContinuous _ _ Real.volume_singleton
  set A := {x | x < c ∧ ∫⁻ t in Iic x, ‖k t‖ₑ ≤ s}
  -- a point to the left of `c` with mass above `s`
  obtain ⟨x₁, hx₁c, hx₁⟩ : ∃ x₁, x₁ < c ∧ s < ∫⁻ t in Iic x₁, ‖k t‖ₑ := by
    by_contra! h
    rw [← hρ _ measurableSet_Iio] at hsM
    exact hsM.not_ge (measure_Iio_le_of_forall fun y hy ↦
      (hρ _ measurableSet_Iic).trans_le (h y hy))
  -- every point with mass at most `s` lies to the left of `x₁`, and there is one
  have hlt : ∀ x, ∫⁻ t in Iic x, ‖k t‖ₑ ≤ s → x < x₁ := fun x hx ↦ not_le.1 fun h ↦
    (hx₁.trans_le (lintegral_mono_set (Iic_subset_Iic.2 h))).not_ge hx
  obtain ⟨x₂, hx₂⟩ := exists_lintegral_Iic_lt (hL x₁ hx₁c) hs₀
  have hne : A.Nonempty := ⟨x₂, (hlt x₂ hx₂.le).trans hx₁c, hx₂.le⟩
  have hbdd : BddAbove A := ⟨x₁, fun x hx ↦ (hlt x hx.2).le⟩
  set x₀ := sSup A
  have hx₀c : x₀ < c := (csSup_le hne fun x hx ↦ (hlt x hx.2).le).trans_lt hx₁c
  refine ⟨hx₀c, ?_⟩
  rw [← hρ _ measurableSet_Iic]
  refine le_antisymm ?_ ?_
  · -- continuity from below at `x₀`
    rw [← measure_congr (Iio_ae_eq_Iic' (hatom x₀))]
    refine measure_Iio_le_of_forall fun y hy ↦ ?_
    obtain ⟨a, ha, hya⟩ := exists_lt_of_lt_csSup hne hy
    rw [hρ _ measurableSet_Iic]
    exact (lintegral_mono_set (Iic_subset_Iic.2 hya.le)).trans ha.2
  · -- continuity from above at `x₀`, through points of `(x₀, c)` outside `A`
    refine le_measure_Iic_of_forall hx₀c
      (fun y hy ↦ by rw [hρ _ measurableSet_Iic]; exact hL _ hy.2) fun y hy ↦ ?_
    rw [hρ _ measurableSet_Iic]
    exact le_of_not_ge fun h ↦ (le_csSup hbdd ⟨hy.2, h⟩).not_gt hy.1

/-- For `|k| dx` on `(c, ∞)`, almost every point has right mass strictly between `0` and the
total mass. -/
private theorem ae_tail_mem (hk : IsBalancedKernel k c α)
    (hR : ∀ y, c < y → ∫⁻ t in Ici y, ‖k t‖ₑ ≠ ∞) :
    ∀ᵐ y ∂rightMeasure k c, c < y ∧ 0 < ∫⁻ t in Ici y, ‖k t‖ₑ ∧
      ∫⁻ t in Ici y, ‖k t‖ₑ < ∫⁻ t in Iio c, ‖k t‖ₑ := by
  have hkm := hk.aemeasurable
  have hc : ∀ᵐ y ∂rightMeasure k c, c < y :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have huniv : rightMeasure k c univ = ∫⁻ t in Iio c, ‖k t‖ₑ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hk.mass_eq]
  have hanti : Antitone fun y ↦ rightMeasure k c (Ici y) := fun y y' h ↦
    measure_mono (Ici_subset_Ici.2 h)
  have hfin : ∀ y, c < y → rightMeasure k c (Ici y) ≠ ∞ := fun y hy ↦
    (rightMeasure_Ici hy).trans_ne (hR y hy)
  have h₀ : rightMeasure k c {y | c < y ∧ rightMeasure k c (Ici y) ≤ 0} = 0 :=
    measure_eq_of_tail_bounds rightMeasure_Iic hfin rightMeasure_singleton bot_le
      (fun y hy ↦ hy.1) (fun y hy y' hyy' ↦ ⟨hy.1.trans_le hyy', (hanti hyy').trans hy.2⟩)
      (fun y hy ↦ hy.2) (fun _ _ _ ↦ bot_le)
  have hpos : ∀ᵐ y ∂rightMeasure k c, c < y → 0 < ∫⁻ t in Ici y, ‖k t‖ₑ := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h₀] with y hy hyc
    rw [← rightMeasure_Ici hyc]
    exact pos_iff_ne_zero.2 fun h ↦ hy ⟨hyc, h.le⟩
  have hlt : ∀ᵐ y ∂rightMeasure k c, c < y →
      ∫⁻ t in Ici y, ‖k t‖ₑ < ∫⁻ t in Iio c, ‖k t‖ₑ := by
    by_cases hM : ∫⁻ t in Iio c, ‖k t‖ₑ = ∞
    · exact Eventually.of_forall fun y hyc ↦ hM ▸ (hR y hyc).lt_top
    · have hE : rightMeasure k c
          {y | c < y ∧ rightMeasure k c (Ici y) < ∫⁻ t in Iio c, ‖k t‖ₑ} =
            ∫⁻ t in Iio c, ‖k t‖ₑ :=
        measure_eq_of_tail_bounds rightMeasure_Iic hfin rightMeasure_singleton huniv.ge
          (fun y hy ↦ hy.1)
          (fun y hy y' hyy' ↦ ⟨hy.1.trans_le hyy', (hanti hyy').trans_lt hy.2⟩)
          (fun y hy ↦ hy.2.le) (fun y hy hyE ↦ not_lt.1 fun h ↦ hyE ⟨hy, h⟩)
      have hEm : MeasurableSet
          {y | c < y ∧ rightMeasure k c (Ici y) < ∫⁻ t in Iio c, ‖k t‖ₑ} :=
        measurableSet_Ioi.inter (measurableSet_lt hanti.measurable measurable_const)
      have hcompl : rightMeasure k c
          {y | c < y ∧ rightMeasure k c (Ici y) < ∫⁻ t in Iio c, ‖k t‖ₑ}ᶜ = 0 := by
        rw [measure_compl hEm (by rw [hE]; exact hM), hE, huniv, tsub_self]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcompl] with y hy hyc
      exact rightMeasure_Ici hyc ▸ (not_not.1 hy).2
  filter_upwards [hc, hpos, hlt] with y hyc hy₀ hyM
  exact ⟨hyc, hy₀ hyc, hyM hyc⟩

/-- The canonical transport map matches outer masses. Away from a null set of the support of `k`
to the right of `c`, the right mass `s = ∫_{t ≥ y} |k|` lies strictly between `0` and the total
mass, and the left distribution function takes the value `s` at `transportMap k c y < c`. The
map is nonincreasing where `s > 0` and constant where `s = 0`, hence measurable. -/
theorem IsBalancedKernel.isMassMatching_transportMap (hk : IsBalancedKernel k c α) :
    IsMassMatching k c (transportMap k c) := by
  have hkm := hk.aemeasurable
  have hL : ∀ x, x < c → ∫⁻ t in Iic x, ‖k t‖ₑ ≠ ∞ := fun _ hx ↦
    lintegral_Iic_ne_top hk.integrable hx
  have hmR : Antitone fun y ↦ ∫⁻ t in Ici y, ‖k t‖ₑ := fun y y' h ↦
    lintegral_mono_set (Ici_subset_Ici.2 h)
  have hmRm : Measurable fun y ↦ ∫⁻ t in Ici y, ‖k t‖ₑ := hmR.measurable
  have hR : ∀ y, c < y → ∫⁻ t in Ici y, ‖k t‖ₑ ≠ ∞ := fun _ hy ↦
    lintegral_Ici_ne_top hk.integrable hy
  have hνR := ae_tail_mem hk hR
  have hspec : ∀ᵐ y ∂volume.restrict (Ioi c), k y ≠ 0 →
      transportMap k c y < c ∧
        ∫⁻ x in Iic (transportMap k c y), ‖k x‖ₑ = ∫⁻ t in Ici y, ‖k t‖ₑ := by
    filter_upwards [(ae_withDensity_iff' hkm.enorm.restrict).1 hνR] with y hy hky
    obtain ⟨-, hy₀, hyM⟩ := hy (by simpa using hky)
    exact lintegral_Iic_sSup_eq hL hy₀ hyM
  refine ⟨?_, hspec.mono fun y hy hky ↦ (hy hky).1, hspec.mono fun y hy hky ↦ (hy hky).2⟩
  -- measurability: nonincreasing where the right mass is positive, constant where it vanishes
  have hVm : MeasurableSet {y | c < y ∧ 0 < ∫⁻ t in Ici y, ‖k t‖ₑ} :=
    measurableSet_Ioi.inter (measurableSet_lt measurable_const hmRm)
  have hWm : MeasurableSet {y | c < y ∧ ∫⁻ t in Ici y, ‖k t‖ₑ = 0} :=
    measurableSet_Ioi.inter (measurableSet_eq_fun hmRm measurable_const)
  have hVW : Ioi c = {y | c < y ∧ 0 < ∫⁻ t in Ici y, ‖k t‖ₑ} ∪
      {y | c < y ∧ ∫⁻ t in Ici y, ‖k t‖ₑ = 0} := by
    ext y
    simp only [mem_Ioi, mem_union, mem_ofPred_eq, ← and_or_left, pos_iff_ne_zero, ne_or_eq,
      and_true]
  rw [hVW, aemeasurable_union_iff]
  constructor
  · refine aemeasurable_restrict_of_antitoneOn hVm fun y _ y' hy' hyy' ↦ ?_
    obtain ⟨x₂, hx₂⟩ := exists_lintegral_Iic_lt (hL (c - 1) (by linarith)) hy'.2
    refine csSup_le_csSup ⟨c, fun x hx ↦ hx.1.le⟩ ?_ fun x hx ↦ ⟨hx.1, hx.2.trans (hmR hyy')⟩
    exact ⟨min x₂ (c - 1), by linarith [min_le_right x₂ (c - 1)],
      (lintegral_mono_set (Iic_subset_Iic.2 (min_le_left _ _))).trans hx₂.le⟩
  · refine (aemeasurable_const (b := sSup {x | x < c ∧ ∫⁻ t in Iic x, ‖k t‖ₑ ≤ 0})).congr ?_
    filter_upwards [ae_restrict_mem hWm] with y hy
    simp only [transportMap, hy.2]

end Canonical

section Shift

variable {f : ℝ → ℝ} {g : ℝ → ℝ≥0∞} {h b c : ℝ}

/-- Substitution `x = u - h` in a lintegral over an interval. -/
private theorem setLIntegral_Ioc_sub (φ : ℝ → ℝ≥0∞) (h a b : ℝ) :
    ∫⁻ x in Ioc a b, φ x = ∫⁻ u in Ioc (a + h) (b + h), φ (u - h) := by
  rw [← preimage_sub_const_Ioc h a b,
    (measurePreserving_sub_right volume h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_subRight h)]

/-- Substitution `x = u + h` in a lintegral over an interval. -/
private theorem setLIntegral_Ioc_add (φ : ℝ → ℝ≥0∞) (h a b : ℝ) :
    ∫⁻ x in Ioc a b, φ x = ∫⁻ u in Ioc (a - h) (b - h), φ (u + h) := by
  rw [← preimage_add_const_Ioc h a b,
    (measurePreserving_add_right volume h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight h)]

/-- Substitution `x = u - h` in a lintegral over a half-line. -/
private theorem setLIntegral_Ioi_sub (φ : ℝ → ℝ≥0∞) (h a : ℝ) :
    ∫⁻ x in Ioi a, φ x = ∫⁻ u in Ioi (a + h), φ (u - h) := by
  rw [← preimage_sub_const_Ioi h a,
    (measurePreserving_sub_right volume h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_subRight h)]

/-- Substitution `x = u + h` in a lintegral over a half-line. -/
private theorem setLIntegral_Ioi_add (φ : ℝ → ℝ≥0∞) (h a : ℝ) :
    ∫⁻ x in Ioi a, φ x = ∫⁻ u in Ioi (a - h), φ (u + h) := by
  rw [← preimage_add_const_Ioi h a,
    (measurePreserving_add_right volume h).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight h)]

/-- The integrand `‖f(x - h) - f(x + h)‖ g(x)` is measurable on a set where `g` is monotone. -/
private theorem aemeasurable_shift_diff (hf : AEMeasurable f) {s : Set ℝ} (hs : MeasurableSet s)
    (hg : MonotoneOn g s) :
    AEMeasurable (fun x ↦ ‖f (x - h) - f (x + h)‖ₑ * g x) (volume.restrict s) := by
  have h₁ : AEMeasurable (fun x ↦ f (x - h)) :=
    hf.comp_quasiMeasurePreserving (measurePreserving_sub_right volume h).quasiMeasurePreserving
  have h₂ : AEMeasurable (fun x ↦ f (x + h)) :=
    hf.comp_quasiMeasurePreserving (measurePreserving_add_right volume h).quasiMeasurePreserving
  exact ((h₁.sub h₂).enorm.restrict).mul (aemeasurable_restrict_of_monotoneOn hs hg)

/-- The triangle inequality `|f(x - h)| ≤ |f(x - h) - f(x + h)| + |f(x + h)|` under a weight. -/
private theorem enorm_mul_le_add (x : ℝ) :
    ‖f (x - h)‖ₑ * g x ≤ ‖f (x - h) - f (x + h)‖ₑ * g x + ‖f (x + h)‖ₑ * g x := by
  rw [← add_mul]
  refine mul_le_mul' ?_ le_rfl
  calc ‖f (x - h)‖ₑ = ‖(f (x - h) - f (x + h)) + f (x + h)‖ₑ := by rw [sub_add_cancel]
    _ ≤ _ := enorm_add_le _ _

/-- Lemma 3.10 of Chen and Hou (Part I) in `[0, ∞]`-valued form. For `h ≥ 0`, `b ≤ c`, `f`
measurable and `g` nondecreasing on `[b - h, c + h]`,
`∫_{b-h}^{b+h} |f(x - h)| g(x) ≤ ∫_{b-h}^{c-h} |f(x - h) - f(x + h)| g(x) +
  ∫_{c-h}^{c+h} |f(x - h)| g(x)`,
provided `∫_{b+h}^{c+h} |f(x - h)| g(x)` is finite. The proof compares `∫_b^c |f| g(· - h)` with
`∫_b^c |f| g(· + h)`. A real nonnegative weight enters as `fun x ↦ ENNReal.ofReal (g x)`. -/
theorem lintegral_shift_le (hh : 0 ≤ h) (hbc : b ≤ c) (hf : AEMeasurable f)
    (hg : MonotoneOn g (Icc (b - h) (c + h)))
    (hfin : ∫⁻ x in Ioc (b + h) (c + h), ‖f (x - h)‖ₑ * g x ≠ ∞) :
    ∫⁻ x in Ioc (b - h) (b + h), ‖f (x - h)‖ₑ * g x ≤
      (∫⁻ x in Ioc (b - h) (c - h), ‖f (x - h) - f (x + h)‖ₑ * g x) +
        ∫⁻ x in Ioc (c - h) (c + h), ‖f (x - h)‖ₑ * g x := by
  -- `∫_{b-h}^{c-h} |f(x + h)| g(x) ≤ ∫_{b+h}^{c+h} |f(x - h)| g(x)`
  have hA : ∫⁻ x in Ioc (b - h) (c - h), ‖f (x + h)‖ₑ * g x ≤
      ∫⁻ x in Ioc (b + h) (c + h), ‖f (x - h)‖ₑ * g x := by
    rw [setLIntegral_Ioc_sub _ h (b - h), setLIntegral_Ioc_add _ h (b + h)]
    simp only [sub_add_cancel, add_sub_cancel_right]
    refine setLIntegral_mono' measurableSet_Ioc fun u hu ↦ ?_
    obtain ⟨hbu, huc⟩ := hu
    exact mul_le_mul' le_rfl (hg ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      (by linarith))
  have hsub : Ioc (b - h) (c - h) ⊆ Icc (b - h) (c + h) := fun x hx ↦
    ⟨hx.1.le, by linarith [hx.2]⟩
  have hmeas := aemeasurable_shift_diff (h := h) hf measurableSet_Ioc (hg.mono hsub)
  have hsplit₁ : (∫⁻ x in Ioc (b - h) (b + h), ‖f (x - h)‖ₑ * g x) +
      ∫⁻ x in Ioc (b + h) (c + h), ‖f (x - h)‖ₑ * g x =
        ∫⁻ x in Ioc (b - h) (c + h), ‖f (x - h)‖ₑ * g x := by
    rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  have hsplit₂ : ∫⁻ x in Ioc (b - h) (c + h), ‖f (x - h)‖ₑ * g x =
      (∫⁻ x in Ioc (b - h) (c - h), ‖f (x - h)‖ₑ * g x) +
        ∫⁻ x in Ioc (c - h) (c + h), ‖f (x - h)‖ₑ * g x := by
    rw [← lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl),
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  have htri : ∫⁻ x in Ioc (b - h) (c - h), ‖f (x - h)‖ₑ * g x ≤
      (∫⁻ x in Ioc (b - h) (c - h), ‖f (x - h) - f (x + h)‖ₑ * g x) +
        ∫⁻ x in Ioc (b - h) (c - h), ‖f (x + h)‖ₑ * g x := by
    rw [← lintegral_add_left' hmeas]
    exact lintegral_mono fun x ↦ enorm_mul_le_add x
  refine ENNReal.le_of_add_le_add_right hfin ?_
  rw [hsplit₁, hsplit₂, add_right_comm]
  exact add_le_add (htri.trans (add_le_add le_rfl hA)) le_rfl

/-- Lemma 3.10 of Chen and Hou (Part I) on a half-line, the case `c = ∞` used in the paper:
`∫_{b-h}^{b+h} |f(x - h)| g(x) ≤ ∫_{b-h}^{∞} |f(x - h) - f(x + h)| g(x)` for `g` nondecreasing
on `[b - h, ∞)`, provided `∫_{b+h}^{∞} |f(x - h)| g(x)` is finite. Without the finiteness the
inequality fails (`f = g = 1`). -/
theorem lintegral_shift_le_of_tail (hf : AEMeasurable f) (hg : MonotoneOn g (Ici (b - h)))
    (hh : 0 ≤ h) (hfin : ∫⁻ x in Ioi (b + h), ‖f (x - h)‖ₑ * g x ≠ ∞) :
    ∫⁻ x in Ioc (b - h) (b + h), ‖f (x - h)‖ₑ * g x ≤
      ∫⁻ x in Ioi (b - h), ‖f (x - h) - f (x + h)‖ₑ * g x := by
  have hA : ∫⁻ x in Ioi (b - h), ‖f (x + h)‖ₑ * g x ≤
      ∫⁻ x in Ioi (b + h), ‖f (x - h)‖ₑ * g x := by
    rw [setLIntegral_Ioi_sub _ h (b - h), setLIntegral_Ioi_add _ h (b + h)]
    simp only [sub_add_cancel, add_sub_cancel_right]
    refine setLIntegral_mono' measurableSet_Ioi fun u hu ↦ ?_
    have hbu : b < u := hu
    exact mul_le_mul' le_rfl (hg (show b - h ≤ u - h by linarith)
      (show b - h ≤ u + h by linarith) (by linarith))
  have hmeas := aemeasurable_shift_diff (h := h) hf measurableSet_Ioi
    (hg.mono Ioi_subset_Ici_self)
  have hsplit : (∫⁻ x in Ioc (b - h) (b + h), ‖f (x - h)‖ₑ * g x) +
      ∫⁻ x in Ioi (b + h), ‖f (x - h)‖ₑ * g x = ∫⁻ x in Ioi (b - h), ‖f (x - h)‖ₑ * g x := by
    rw [← lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
      Ioc_union_Ioi_eq_Ioi (by linarith)]
  have htri : ∫⁻ x in Ioi (b - h), ‖f (x - h)‖ₑ * g x ≤
      (∫⁻ x in Ioi (b - h), ‖f (x - h) - f (x + h)‖ₑ * g x) +
        ∫⁻ x in Ioi (b - h), ‖f (x + h)‖ₑ * g x := by
    rw [← lintegral_add_left' hmeas]
    exact lintegral_mono fun x ↦ enorm_mul_le_add x
  refine ENNReal.le_of_add_le_add_right hfin ?_
  rw [hsplit]
  exact htri.trans (add_le_add le_rfl hA)

end Shift

end PDE.Analysis.Rearrangement
