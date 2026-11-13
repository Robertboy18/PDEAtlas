/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.ForwardBand
public import PDE.Analysis.Calculus.LocalExtension.TimeBand
public import PDE.Hyperbolic.Classical.ForwardLocalization
public import PDE.Hyperbolic.Models.Wave.Duhamel.Kirchhoff
import PDE.Hyperbolic.Models.Wave.Kirchhoff.Family

/-!
# Three-dimensional retarded source bounds

The displacement contributed by a source is bounded by the time integral of
its spatial amplitude, weighted by the age of the emitted wave.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis PDE.Common
open scoped Topology

namespace WaveEquation

/-- An integrable bound `M s` on the source over the time-`s` slice of the backward cone with
apex `(t, x)` controls the retarded wave at `(t, x)` without source derivatives. -/
theorem norm_oddDuhamelSolution_zero_le_source_moment {F : ℝ^4 → ℝ} {M : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hM : IntervalIntegrable (fun s ↦ (t - s) * M s) volume 0 t) (x : ℝ^3)
    (hbound : ∀ s ∈ Ioc 0 t, ∀ y : ℝ^3, ‖y - x‖ ≤ t - s → ‖F (timeSpaceCons s y)‖ ≤ M s) :
    ‖oddDuhamelSolution 0 F (timeSpaceCons t x)‖ ≤ ∫ s in (0 : ℝ)..t, (t - s) * M s := by
  rw [oddDuhamelSolution_eq_integral 0 F x ht]
  simp only [Nat.mul_zero, Nat.doubleFactorial, Nat.cast_one, inv_one,
    one_mul, oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  apply intervalIntegral.norm_integral_le_of_norm_le ht _ hM
  filter_upwards with s
  intro hs
  have havg : ‖unitSphereAverage 3 (fun y ↦ F (timeSpaceCons s y)) x (t - s)‖ ≤
      M s := by
    unfold unitSphereAverage
    rw [norm_div, Real.norm_of_nonneg (unitSphereArea_pos (n := 3)).le]
    apply (div_le_iff₀ (unitSphereArea_pos (n := 3))).mpr
    apply norm_integral_le_of_norm_le_const
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    apply hbound s hs
    have hω : ‖(ω : ℝ^3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    simp only [add_sub_cancel_left, norm_smul, hω, mul_one,
      Real.norm_of_nonneg (sub_nonneg.mpr hs.2)]
    exact le_rfl
  rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hs.2)]
  exact mul_le_mul_of_nonneg_left havg (sub_nonneg.mpr hs.2)

/-- A single integrable terminal weight bounds the source contribution at every
preterminal time. The terminal source value itself is unused. -/
theorem norm_oddDuhamelSolution_zero_le_terminal_source_moment {F : ℝ^4 → ℝ} {M : ℝ → ℝ} {t b : ℝ}
    (ht : 0 ≤ t) (htb : t < b) (hM : IntegrableOn (fun s ↦ (b - s) * M s) (Ioo 0 b) volume)
    (hbound : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, ‖F (timeSpaceCons s x)‖ ≤ M s) (x : ℝ^3) :
    ‖oddDuhamelSolution 0 F (timeSpaceCons t x)‖ ≤ ∫ s in Ioo (0 : ℝ) b, (b - s) * M s := by
  rw [oddDuhamelSolution_eq_integral 0 F x ht]
  simp only [Nat.mul_zero, Nat.doubleFactorial, Nat.cast_one, inv_one,
    one_mul, oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  rw [intervalIntegral.integral_of_le ht]
  have hsub : Ioc (0 : ℝ) t ⊆ Ioo 0 b := fun s hs ↦ ⟨hs.1, hs.2.trans_lt htb⟩
  have hnorm : ‖∫ s in Ioc (0 : ℝ) t, (t - s) *
      unitSphereAverage 3 (fun y ↦ F (timeSpaceCons s y)) x (t - s)‖ ≤
      ∫ s in Ioc (0 : ℝ) t, (b - s) * M s := by
    apply norm_integral_le_of_norm_le (hM.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have havg : ‖unitSphereAverage 3 (fun y ↦ F (timeSpaceCons s y)) x (t - s)‖ ≤
        M s := by
      unfold unitSphereAverage
      rw [norm_div, Real.norm_of_nonneg (unitSphereArea_pos (n := 3)).le]
      apply (div_le_iff₀ (unitSphereArea_pos (n := 3))).mpr
      exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun θ ↦
          hbound s (hsub hs) (x + (t - s) • (θ : ℝ^3)))
    rw [norm_mul, Real.norm_of_nonneg (sub_nonneg.mpr hs.2)]
    exact mul_le_mul (sub_le_sub_right htb.le s) havg (norm_nonneg _)
      (sub_nonneg.mpr (hsub hs).2.le)
  refine hnorm.trans (setIntegral_mono_set hM ?_ (Filter.Eventually.of_forall hsub))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact mul_nonneg (sub_nonneg.mpr hs.2.le)
    ((norm_nonneg (F (timeSpaceCons s (0 : ℝ^3)))).trans (hbound s hs 0))

/-- The retarded representation uses only regularity and the equation on the
preterminal band. No continuation of the solution beyond `b` is used. -/
theorem eq_kirchhoffFormula_add_duhamel_on_band {u F : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ} {a b t : ℝ}
    (hu : ContDiffOn ℝ 4 u {p | a < p 0 ∧ p 0 < b}) (ha : a < 0)
    (hwave : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) = F (timeSpaceCons s x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (ht : 0 ≤ t) (htb : t < b)
    (x : ℝ^3) :
    u (timeSpaceCons t x) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) +
      oddDuhamelSolution 0 F (timeSpaceCons t x) := by
  obtain ⟨U, hU, heq⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 4) (f := u) (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ)
    (by simpa using hu) ha htb
  have hlocal (s : ℝ) (hs : s ∈ Icc 0 t) (y : ℝ^3) : u =ᶠ[𝓝 (timeSpaceCons s y)] U :=
    heq _ (by simpa only [EuclideanSpace.coe_proj, timeSpaceCons_zero] using hs)
  -- The initial data are the time-zero traces of the smooth extension.
  have hg : ContDiff ℝ 3 g := by
    have hgU : g = fun y ↦ U (timeSpaceCons 0 y) :=
      funext fun y ↦ (hposition y).symm.trans (hlocal 0 ⟨le_rfl, ht⟩ y).eq_of_nhds
    rw [hgU]
    exact (hU.comp (contDiff_timeSpaceCons_spatial 3 0)).of_le (by norm_num)
  have hh : ContDiff ℝ 2 h := by
    have hhU : h = fun y ↦ (∂[0] U) (timeSpaceCons 0 y) :=
      funext fun y ↦ (hinitial y).symm.trans
        (PDE.partialDeriv_congr_nhds 0 (hlocal 0 ⟨le_rfl, ht⟩ y))
    rw [hhU]
    exact ((PDE.contDiff_partialDeriv_of_succ (m := 3) hU).comp
      (contDiff_timeSpaceCons_spatial 3 0)).of_le (by norm_num)
  have hsecond (i : Fin 4) : ContDiff ℝ 2 (∂[i] (∂[i] U)) :=
    PDE.contDiff_partialDeriv_of_succ (m := 2) (PDE.contDiff_partialDeriv_of_succ (m := 3) hU)
  have hF : ContDiff ℝ 2 (waveOperator U) := (hsecond 0).sub (ContDiff.sum fun i _ ↦ hsecond i.succ)
  have he := eq_kirchhoffFormula_add_duhamel (hU.of_le (by norm_num)) hF.contDiffOn
    hg hh (fun _ _ _ ↦ rfl) (fun y ↦ (hlocal 0 ⟨le_rfl, ht⟩ y).symm.eq_of_nhds.trans (hposition y))
    (fun y ↦ (PDE.partialDeriv_congr_nhds 0 (hlocal 0 ⟨le_rfl, ht⟩ y).symm).trans (hinitial y)) ht x
  rw [← (hlocal t ⟨ht, le_rfl⟩ x).eq_of_nhds] at he
  refine he.trans (congrArg (fun z ↦
    spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) + z) ?_)
  rw [oddDuhamelSolution_eq_integral 0 _ x ht, oddDuhamelSolution_eq_integral 0 _ x ht]
  simp only [Nat.mul_zero, Nat.doubleFactorial, Nat.cast_one, inv_one,
    one_mul, oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  apply intervalIntegral.integral_congr_ae
  filter_upwards with s hs
  have hst : s ∈ Ioc 0 t := by simpa only [uIoc_of_le ht] using hs
  have hslice : (fun y : ℝ^3 ↦ waveOperator U (timeSpaceCons s y)) =
      fun y ↦ F (timeSpaceCons s y) := by
    funext y
    rw [← waveOperator_congr_nhds (hlocal s ⟨hst.1.le, hst.2⟩ y)]
    exact hwave s ⟨hst.1, hst.2.trans_lt htb⟩ y
  rw [hslice]

/-- A weighted source bound controls the difference from the same fixed free
wave throughout the lifespan. The field is smooth only on its time band. -/
theorem norm_sub_kirchhoffFormula_le_terminal_source_moment {u F : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    {M : ℝ → ℝ} {a b t : ℝ} (hu : ContDiffOn ℝ 4 u {p | a < p 0 ∧ p 0 < b}) (ha : a < 0)
    (hwave : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) = F (timeSpaceCons s x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x)
    (hM : IntegrableOn (fun s ↦ (b - s) * M s) (Ioo 0 b) volume)
    (hbound : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, ‖F (timeSpaceCons s x)‖ ≤ M s) (ht : 0 ≤ t) (htb : t < b)
    (x : ℝ^3) :
    ‖u (timeSpaceCons t x) - spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)‖ ≤
      ∫ s in Ioo (0 : ℝ) b, (b - s) * M s := by
  rw [eq_kirchhoffFormula_add_duhamel_on_band hu ha hwave hposition hinitial ht htb,
    add_sub_cancel_left]
  exact norm_oddDuhamelSolution_zero_le_terminal_source_moment ht htb hM hbound x

/-- The forward retarded representation preserves the right initial velocity. -/
theorem eq_kirchhoffFormula_add_duhamel_on_halfOpenBand {u F : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ} {b t : ℝ}
    (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0 ∧ p 0 < b})
    (hwave : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) = F (timeSpaceCons s x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici 0) 0 = h x) (ht : 0 ≤ t)
    (htb : t < b) (x : ℝ^3) :
    u (timeSpaceCons t x) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) +
      oddDuhamelSolution 0 F (timeSpaceCons t x) := by
  have hb : 0 < b := ht.trans_lt htb
  obtain ⟨v, hv, heq⟩ := exists_contDiffOn_extension_halfOpenBand 0 hb hu
  have hlocal (s : ℝ) (hs : 0 < s) (y : ℝ^3) : v =ᶠ[𝓝 (timeSpaceCons s y)] u :=
    eventuallyEq_of_eqOn_forward heq (by simpa only [timeSpaceCons_zero] using hs)
  have hvel (y : ℝ^3) : (∂[0] v) (timeSpaceCons 0 y) = h y := by
    have hmem : {p : ℝ^4 | p 0 < b} ∈ 𝓝 (timeSpaceCons 0 y) :=
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds
        (by simpa only [mem_ofPred_eq, EuclideanSpace.coe_proj, timeSpaceCons_zero] using hb)
    have hd := (PDE.hasDerivAt_timeSpaceCons v 0 y
      ((hv.contDiffAt hmem).differentiableAt (by norm_num))).hasDerivWithinAt (s := Ici 0)
    have htrace : (fun s ↦ v (timeSpaceCons s y)) =ᶠ[𝓝[Ici 0] 0]
        (fun s ↦ u (timeSpaceCons s y)) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using (show 0 ≤ s from hs))
    rw [← hd.derivWithin (uniqueDiffWithinAt_Ici 0), htrace.derivWithin_eq_of_mem self_mem_Ici]
    exact hinitial y
  have hw (s : ℝ) (hs : s ∈ Ioo 0 b) (y : ℝ^3) :
      waveOperator v (timeSpaceCons s y) = F (timeSpaceCons s y) := by
    rw [waveOperator_congr_nhds (hlocal s hs.1 y)]
    exact hwave s hs y
  have hpos (y : ℝ^3) : v (timeSpaceCons 0 y) = g y :=
    (heq (by simp only [mem_ofPred_eq, timeSpaceCons_zero, le_refl])).trans (hposition y)
  have hrep := eq_kirchhoffFormula_add_duhamel_on_band
    (a := -1) (hv.mono fun _ hp ↦ hp.2) (by norm_num) hw hpos hvel ht htb x
  rwa [heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using ht)] at hrep

/-- An integrable terminal source moment controls the displacement relative to
the original free wave, using only forward regularity and right initial traces. -/
theorem norm_sub_kirchhoffFormula_le_terminal_source_moment_forward {u F : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    {M : ℝ → ℝ} {b t : ℝ} (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0 ∧ p 0 < b})
    (hwave : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) = F (timeSpaceCons s x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici 0) 0 = h x)
    (hM : IntegrableOn (fun s ↦ (b - s) * M s) (Ioo 0 b) volume)
    (hbound : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, ‖F (timeSpaceCons s x)‖ ≤ M s) (ht : 0 ≤ t) (htb : t < b)
    (x : ℝ^3) :
    ‖u (timeSpaceCons t x) - spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)‖ ≤
      ∫ s in Ioo (0 : ℝ) b, (b - s) * M s := by
  rw [eq_kirchhoffFormula_add_duhamel_on_halfOpenBand hu hwave hposition hinitial
    ht htb, add_sub_cancel_left]
  exact norm_oddDuhamelSolution_zero_le_terminal_source_moment ht htb hM hbound x

open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- An unbounded forward wave from fixed compact data has no integrable terminal
weighted bound on its source. This conclusion does not exclude bounded return times. -/
theorem not_integrable_terminal_source_moment_of_unbounded_amplitude {u F : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    {M : ℝ → ℝ} {b : ℝ} (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0 ∧ p 0 < b}) (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g) (hhs : HasCompactSupport h)
    (hwave : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, waveOperator u (timeSpaceCons s x) = F (timeSpaceCons s x))
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici 0) 0 = h x)
    (hunbounded : ∀ B : ℝ, ∃ t ∈ Ico 0 b, ∃ x : ℝ^3, B < ‖u (timeSpaceCons t x)‖)
    (hbound : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, ‖F (timeSpaceCons s x)‖ ≤ M s) :
    ¬ IntegrableOn (fun s ↦ (b - s) * M s) (Ioo 0 b) volume := by
  intro hM
  obtain ⟨B, _, hB⟩ := exists_bound_cauchyFreeField_of_compact_data
      (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs b
  let J : ℝ := ∫ s in Ioo (0 : ℝ) b, (b - s) * M s
  obtain ⟨t, ht, x, hx⟩ := hunbounded (J + B)
  have hfree : ‖spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)‖ ≤ B := by
    simpa only [Real.norm_eq_abs, cauchyFreeField] using hB (t, x) ⟨ht.1, ht.2.le⟩
  have hsource := norm_sub_kirchhoffFormula_le_terminal_source_moment_forward
    hu hwave hposition hinitial hM hbound ht.1 ht.2 x
  have htotal : ‖u (timeSpaceCons t x)‖ ≤ J + B := by
    calc
      ‖u (timeSpaceCons t x)‖ = ‖(u (timeSpaceCons t x) -
          spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)) +
            spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖u (timeSpaceCons t x) - spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)‖ +
            ‖spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x)‖ := norm_add_le _ _
      _ ≤ J + B := add_le_add hsource hfree
  exact (not_lt_of_ge htotal) hx

/-- For a semilinear wave from fixed compact Cauchy data, unbounded displacement
forces divergence of every terminal weighted reaction envelope. The initial velocity is the right
derivative. -/
theorem not_integrable_terminal_reaction_moment_of_unbounded_amplitude {f : ℝ → ℝ} {u : ℝ^4 → ℝ}
    {g h : ℝ^3 → ℝ} {M : ℝ → ℝ} {b : ℝ} (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0 ∧ p 0 < b})
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h)
    (hwave : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons s x) + f (u (timeSpaceCons s x)) = 0)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, HasDerivWithinAt (fun s ↦ u (timeSpaceCons s x)) (h x) (Ici 0) 0)
    (hunbounded : ∀ B : ℝ, ∃ t ∈ Ico 0 b, ∃ x : ℝ^3, B < ‖u (timeSpaceCons t x)‖)
    (hbound : ∀ s ∈ Ioo 0 b, ∀ x : ℝ^3, ‖f (u (timeSpaceCons s x))‖ ≤ M s) :
    ¬ IntegrableOn (fun s ↦ (b - s) * M s) (Ioo 0 b) volume := by
  apply not_integrable_terminal_source_moment_of_unbounded_amplitude
    (F := fun p ↦ -f (u p)) hu hg hh hgs hhs
    (fun s hs x ↦ eq_neg_of_add_eq_zero_left (hwave s hs x)) hposition
    (fun x ↦ (hinitial x).derivWithin (uniqueDiffWithinAt_Ici 0)) hunbounded
  intro s hs x
  simpa only [norm_neg] using hbound s hs x

end WaveEquation
