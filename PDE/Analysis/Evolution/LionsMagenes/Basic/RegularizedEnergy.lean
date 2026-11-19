/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.ContinuousPivotEvolution
public import PDE.Analysis.Evolution.Time.Mollification
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.Analysis.Evolution.Bochner.Duality
import PDE.Analysis.Evolution.LionsMagenes.Basic.Continuity
import PDE.Analysis.Evolution.LionsMagenes.Basic.EnergyIdentity
import PDE.Analysis.Evolution.Time.Mollification.WeakDerivative

/-!
# Regularized Lions–Magenes energy identities

Time regularization constructs a continuous pivot representative for a weak
Gelfand evolution and transfers the regularized energy law to the limit.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3, and §7.1.1 (the remark after the
  definition of weak solution). <https://doi.org/10.1090/gsm/019>
* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*,
  Vol. I, Springer, 1972, Chapter 1 (Hilbert theory of trace and interpolation spaces).
  <https://doi.org/10.1007/978-3-642-65161-8>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open IsUnifLocDoublingMeasure
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section RegularizedEnergy

open PDE.Analysis.Evolution

variable [CompleteSpace V]

/-- The duality products of simultaneous time regularizations converge to
the original `V*`--`V` pairing with respect to every measure dominated by
Lebesgue measure.  This is the Hölder step in the Lions–Magenes limiting
argument, expressed as continuity of the `L²` inner product after pointwise
Riesz transport. -/
theorem regularizeTime_duality_integral_tendsto_measure
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {ν : Measure ℝ} (hν : ν ≤ volume)
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun m ↦ ∫ t, regularizeTime (ε m) g t
        (regularizeTime (ε m) u t) ∂ν) atTop
      (𝓝 (∫ t, g t (u t) ∂ν)) := by
  have hpair := tendsto_integral_dual_pairing_of_tendsto_L2
    (regularizeTime_tendsto_toLp_monoMeasure 2 (by norm_num) hν hu ε hεpos hε0)
    ((rieszFromDualLp.continuous.tendsto _).comp
      (regularizeTime_tendsto_toLp_monoMeasure 2 (by norm_num) hν hg ε hεpos hε0))
  have hlim : (∫ t, (hg.mono_measure hν).toLp g t ((hu.mono_measure hν).toLp u t) ∂ν) =
      ∫ t, g t (u t) ∂ν := integral_congr_ae <| by
    filter_upwards [(hg.mono_measure hν).coeFn_toLp, (hu.mono_measure hν).coeFn_toLp]
      with t hgt hut
    rw [hgt, hut]
  rw [← hlim]
  refine hpair.congr fun m ↦ integral_congr_ae ?_
  filter_upwards [(regularizeTime_memLp_monoMeasure 2 (by norm_num) hν (hεpos m) hg).coeFn_toLp,
    (regularizeTime_memLp_monoMeasure 2 (by norm_num) hν (hεpos m) hu).coeFn_toLp] with t hgt hut
  rw [hgt, hut]

/-- Global Lebesgue-measure form of duality-product convergence. -/
theorem regularizeTime_duality_integral_tendsto
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto
      (fun m ↦ ∫ t, regularizeTime (ε m) g t
        (regularizeTime (ε m) u t)) atTop
      (𝓝 (∫ t, g t (u t))) :=
  regularizeTime_duality_integral_tendsto_measure le_rfl
    hu hg ε hεpos hε0

/-- Finite-interval form of duality-product convergence.  It follows from
the dominated-measure theorem by restricting Lebesgue measure to the
unordered interval and restoring the orientation sign. The statement uses no measurable
structure on `V` or its dual, so the proof chooses the Borel ones. -/
theorem regularizeTime_duality_intervalIntegral_tendsto
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (a b : ℝ) :
    Tendsto
      (fun m ↦ ∫ t in a..b, regularizeTime (ε m) g t
        (regularizeTime (ε m) u t)) atTop
      (𝓝 (∫ t in a..b, g t (u t))) := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ V) := borel _
  have : BorelSpace (StrongDual ℝ V) := ⟨rfl⟩
  let c : ℝ := if a ≤ b then 1 else -1
  have hrestricted := regularizeTime_duality_integral_tendsto_measure
    (ν := volume.restrict (uIoc a b)) Measure.restrict_le_self
    hu hg ε hεpos hε0
  have hc : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c) := tendsto_const_nhds
  have horiented := hc.smul hrestricted
  simpa [c, intervalIntegral.intervalIntegral_eq_integral_uIoc] using horiented

/-- Pairwise duality products of time regularizations become uniformly
small in the two regularization indices on every finite interval. -/
theorem regularizeTime_sub_duality_intervalIntegral_cauchy
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (a b : ℝ) :
    ∀ η > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ‖∫ t in a..b,
        (regularizeTime (ε m) g t - regularizeTime (ε n) g t)
          (regularizeTime (ε m) u t - regularizeTime (ε n) u t)‖ < η := by
  let ν : Measure ℝ := volume.restrict (uIoc a b)
  have hle : ν ≤ volume := Measure.restrict_le_self
  let U : ℕ → Lp V 2 ν := fun m ↦
    (regularizeTime_memLp_monoMeasure 2 (by norm_num) hle (hεpos m) hu).toLp
      (regularizeTime (ε m) u)
  let G : ℕ → Lp (StrongDual ℝ V) 2 ν := fun m ↦
    (regularizeTime_memLp_monoMeasure 2 (by norm_num) hle (hεpos m) hg).toLp
      (regularizeTime (ε m) g)
  intro η hη
  obtain ⟨N, hN⟩ := cauchy_integral_dual_pairing_sub G U
    ((rieszFromDualLp.continuous.tendsto _).comp (regularizeTime_tendsto_toLp_monoMeasure
      2 (by norm_num) hle hg ε hεpos hε0)).cauchySeq
    (regularizeTime_tendsto_toLp_monoMeasure
      2 (by norm_num) hle hu ε hεpos hε0).cauchySeq η hη
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  have hEq : (∫ t, (G m - G n) t ((U m - U n) t) ∂ν) = ∫ t,
      (regularizeTime (ε m) g t - regularizeTime (ε n) g t)
        (regularizeTime (ε m) u t - regularizeTime (ε n) u t) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (G m) (G n), Lp.coeFn_sub (U m) (U n),
      (regularizeTime_memLp_monoMeasure 2 (by norm_num) hle (hεpos m) hg).coeFn_toLp,
      (regularizeTime_memLp_monoMeasure 2 (by norm_num) hle (hεpos n) hg).coeFn_toLp,
      (regularizeTime_memLp_monoMeasure 2 (by norm_num) hle (hεpos m) hu).coeFn_toLp,
      (regularizeTime_memLp_monoMeasure 2 (by norm_num) hle (hεpos n) hu).coeFn_toLp]
      with t hgsub husub hgm hgn hum hun
    rw [hgsub, husub]
    change (G m t - G n t) (U m t - U n t) = _
    rw [show G m t = _ from hgm, show G n t = _ from hgn, show U m t = _ from hum,
      show U n t = _ from hun]
  have hsmall := hN m hm n hn
  rw [hEq] at hsmall
  by_cases hab : a ≤ b <;>
    simpa [ν, intervalIntegral.intervalIntegral_eq_integral_uIoc, hab, norm_neg] using hsmall

/-- The classical derivative of a regularized energy-space trajectory
represents the regularized weak derivative in `V*`.  This is the precise
Gelfand-triple commutation statement used in the Lions–Magenes proof. -/
theorem energyToDual_deriv_regularizeTime
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {ε : ℝ} (hε : 0 < ε)
    (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    (t : ℝ) :
    T.energyToDual (deriv (regularizeTime ε u) t) =
      regularizeTime ε g t := by
  have hdu := hasDerivAt_regularizeTime_of_hasWeakTimeDerivative hε hweak t
  rw [show regularizeTime ε (T.energyToDual ∘ u) = T.energyToDual ∘ regularizeTime ε u from
    funext fun s ↦ (map_regularizeTime T.energyToDual hε u hu s).symm] at hdu
  exact (T.energyToDual.hasFDerivAt.comp_hasDerivAt t
    ((regularizeTime_contDiff hε u hu).differentiable (by simp) t).hasDerivAt).unique hdu

/-- Fundamental theorem of calculus in `V*` for a regularized weak Gelfand
evolution. -/
theorem energyToDual_regularizeTime_sub_eq_intervalIntegral
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {ε : ℝ} (hε : 0 < ε)
    (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    (a b : ℝ) :
    T.energyToDual (regularizeTime ε u b) -
        T.energyToDual (regularizeTime ε u a) =
      ∫ t in a..b, regularizeTime ε g t := by
  refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := T.energyToDual ∘ regularizeTime ε u) (fun t _ ↦ ?_) ((regularizeTime_contDiff hε g
      (locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g)).continuous.intervalIntegrable
        a b)).symm
  rw [← energyToDual_deriv_regularizeTime T hε hu hweak t]
  exact T.energyToDual.hasFDerivAt.comp_hasDerivAt t
    ((regularizeTime_contDiff hε u hu).differentiable (by simp) t).hasDerivAt

/-- Exact energy identity for a positive-scale regularization of a weak
Gelfand evolution.  No pointwise derivative of the original trajectory is
assumed: time mollification creates a smooth `V`-valued trajectory, and its
classical derivative represents the mollified `V*` derivative. -/
theorem regularizeTime_energy_identity
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V} {ε : ℝ} (hε : 0 < ε)
    (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    (a b : ℝ) :
    ‖T.inclusion (regularizeTime ε u b)‖ ^ 2 -
        ‖T.inclusion (regularizeTime ε u a)‖ ^ 2 =
      2 * ∫ t in a..b,
        regularizeTime ε g t (regularizeTime ε u t) := by
  have hsmooth := regularizeTime_contDiff hε u hu
  refine gelfand_absolutelyContinuous_energy_identity T
    ((T.inclusion.contDiff.comp hsmooth).of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    (.of_forall fun t _ ↦ T.inclusion.hasFDerivAt.comp_hasDerivAt t
      (hsmooth.differentiable (by simp) t).hasDerivAt) (.of_forall fun t _ v ↦ ?_)
  rw [← energyToDual_deriv_regularizeTime T hε hu hweak t]
  exact T.energyToDual_apply _ v

/-- Energy identity for the difference of two positive-scale
regularizations of the same weak Gelfand evolution.  This is the decisive
Cauchy estimate in the Lions–Magenes proof: its right-hand side is controlled
by the product of the `L²(V*)` and `L²(V)` distances of the two
regularizations. -/
theorem regularizeTime_sub_energy_identity
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hu : LocallyIntegrable u (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    (a b : ℝ) :
    ‖T.inclusion (regularizeTime ε u b - regularizeTime δ u b)‖ ^ 2 -
        ‖T.inclusion (regularizeTime ε u a - regularizeTime δ u a)‖ ^ 2 =
      2 * ∫ t in a..b,
        (regularizeTime ε g t - regularizeTime δ g t)
          (regularizeTime ε u t - regularizeTime δ u t) := by
  have hε' := regularizeTime_contDiff hε u hu
  have hδ' := regularizeTime_contDiff hδ u hu
  refine gelfand_absolutelyContinuous_energy_identity T
    (u := fun t ↦ regularizeTime ε u t - regularizeTime δ u t)
    (g := fun t ↦ regularizeTime ε g t - regularizeTime δ g t)
    ((T.inclusion.contDiff.comp (hε'.sub hδ')).of_le
      (by simp)).contDiffOn.absolutelyContinuousOnInterval
    (.of_forall fun t _ ↦ T.inclusion.hasFDerivAt.comp_hasDerivAt t
      ((hε'.differentiable (by simp) t).hasDerivAt.fun_sub
        (hδ'.differentiable (by simp) t).hasDerivAt))
    (.of_forall fun t _ v ↦ ?_)
  rw [← energyToDual_deriv_regularizeTime T hε hu hweak t,
    ← energyToDual_deriv_regularizeTime T hδ hu hweak t, ← map_sub]
  exact T.energyToDual_apply _ v

/-- Convergence of a regularization subsequence at one anchor time propagates
to the Cauchy property in the pivot space at every time.  The proof combines
the pairwise regularized energy identity with the `L²` Hölder estimate for
the difference pairing. -/
theorem cauchySeq_inclusion_regularizeTime_of_tendsto_at
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    (ε : ℕ → ℝ) (hεpos : ∀ m, 0 < ε m)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (t₀ : ℝ) (hanchor : Tendsto
      (fun m ↦ T.inclusion (regularizeTime (ε m) u t₀)) atTop
      (𝓝 (T.inclusion (u t₀))))
    (t : ℝ) :
    CauchySeq (fun m ↦ T.inclusion (regularizeTime (ε m) u t)) := by
  refine Metric.cauchySeq_iff.2 fun ρ hρ ↦ ?_
  obtain ⟨Na, hNa⟩ := Metric.cauchySeq_iff.1 hanchor.cauchySeq (ρ / 2) (by positivity)
  obtain ⟨Np, hNp⟩ := regularizeTime_sub_duality_intervalIntegral_cauchy
    hu hg ε hεpos hε0 t₀ t (ρ ^ 2 / 8) (by positivity)
  refine ⟨max Na Np, fun m hm n hn ↦ ?_⟩
  -- the pairwise energy identity between `t₀` and `t`
  have henergy := regularizeTime_sub_energy_identity T (hεpos m) (hεpos n)
    (hu.locallyIntegrable (by norm_num)) hweak t₀ t
  have hI := hNp m (le_of_max_le_right hm) n (le_of_max_le_right hn)
  rw [Real.norm_eq_abs, abs_lt] at hI
  have hY : ‖T.inclusion (regularizeTime (ε m) u t₀ - regularizeTime (ε n) u t₀)‖ < ρ / 2 := by
    simpa [dist_eq_norm, map_sub] using hNa m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  rw [dist_eq_norm, ← map_sub]
  refine lt_of_pow_lt_pow_left₀ 2 hρ.le ?_
  linarith [mul_self_lt_mul_self (norm_nonneg _) hY, hI.2, pow_pos hρ 2]

/-- A weak Gelfand evolution has an everywhere-defined pivot-space
representative obtained as the pointwise `H`-limit of one sequence of time
regularizations.  The representative agrees almost everywhere with the
original `V`-valued trajectory after applying the dense inclusion.

Continuity is proved in the subsequent compact-uniform strengthening; this
theorem is the existence and representative-identification step. -/
theorem exists_pivot_representative_of_weakTimeDerivative
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g) :
    ∃ (uH : ℝ → H) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ t, Tendsto
        (fun m ↦ T.inclusion
          (regularizeTime ((1 : ℝ) / ((ns m : ℝ) + 1)) u t))
        atTop (𝓝 (uH t))) ∧
      (uH =ᵐ[volume] fun t ↦ T.inclusion (u t)) := by
  obtain ⟨ns, hns, hpointV⟩ := exists_subsequence_regularizeTime_tendsto_ae 2 (by norm_num) hu
    (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1)) (fun _ ↦ Nat.one_div_pos_of_nat)
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨t₀, ht₀⟩ := hpointV.exists
  choose uH huH using fun t ↦ cauchySeq_tendsto_of_complete <|
    cauchySeq_inclusion_regularizeTime_of_tendsto_at T hu hg hweak
      (fun m ↦ (1 : ℝ) / ((ns m : ℝ) + 1)) (fun _ ↦ Nat.one_div_pos_of_nat)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop) t₀
      ((T.inclusion.continuous.tendsto _).comp ht₀) t
  refine ⟨uH, ns, hns, huH, ?_⟩
  filter_upwards [hpointV] with t ht
  exact tendsto_nhds_unique (huH t) ((T.inclusion.continuous.tendsto _).comp ht)

/-- The pivot representative constructed from time regularization satisfies
the integrated `V*` fundamental theorem of calculus on every finite
interval.  Thus its endpoint values are traces determined by the
weak derivative, not arbitrary values of an almost-everywhere
representative. -/
theorem exists_pivot_representative_with_integratedDerivative
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g) :
    ∃ (uH : ℝ → H) (ns : ℕ → ℕ), StrictMono ns ∧
      (∀ t, Tendsto
        (fun m ↦ T.inclusion
          (regularizeTime ((1 : ℝ) / ((ns m : ℝ) + 1)) u t))
        atTop (𝓝 (uH t))) ∧
      (uH =ᵐ[volume] fun t ↦ T.inclusion (u t)) ∧
      ∀ a b, HasIntegratedDualDerivativeOn T uH g a b := by
  obtain ⟨uH, ns, hns, hlim, hae⟩ :=
    exists_pivot_representative_of_weakTimeDerivative T hu hg hweak
  refine ⟨uH, ns, hns, hlim, hae, fun a b ↦ ⟨?_, fun t ht ↦ ?_⟩⟩
  · have : IsFiniteMeasure (volume.restrict (uIoc a b)) := ⟨by simp⟩
    exact intervalIntegrable_iff.2
      ((hg.mono_measure Measure.restrict_le_self).integrable (by norm_num))
  let δ : ℕ → ℝ := fun m ↦ (1 : ℝ) / ((ns m : ℝ) + 1)
  have hlim' (s : ℝ) : Tendsto (fun m ↦ T.energyToDual (regularizeTime (δ m) u s)) atTop
      (𝓝 (T.pivotToDual (uH s))) := by
    simpa [δ, GelfandTriple.energyToDual, Function.comp_def] using
      (T.pivotToDual.continuous.tendsto _).comp (hlim s)
  -- the regularized fundamental theorem of calculus passes to the limit
  have hsame := ((hlim' a).add (regularizeTime_intervalIntegral_tendsto hg δ
    (fun _ ↦ Nat.one_div_pos_of_nat) (tendsto_one_div_add_atTop_nhds_zero_nat.comp
      hns.tendsto_atTop) a t)).congr fun m ↦ (sub_eq_iff_eq_add'.mp
        (energyToDual_regularizeTime_sub_eq_intervalIntegral T Nat.one_div_pos_of_nat
          (hu.locallyIntegrable (by norm_num)) hweak a t)).symm
  simpa [dualPrimitive] using tendsto_nhds_unique (hlim' t) hsame


/-- The regularized energy identities pass to the limit along scales `ε m → 0⁺` between two
times at which the regularizations converge in the pivot space. -/
private theorem sq_sub_sq_eq_of_tendsto_regularizeTime
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    {ε : ℕ → ℝ} (hεpos : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0)) {a b : ℝ} {A B : H}
    (ha : Tendsto (fun m ↦ T.inclusion (regularizeTime (ε m) u a)) atTop (𝓝 A))
    (hb : Tendsto (fun m ↦ T.inclusion (regularizeTime (ε m) u b)) atTop (𝓝 B)) :
    ‖B‖ ^ 2 - ‖A‖ ^ 2 = 2 * ∫ t in a..b, g t (u t) :=
  tendsto_nhds_unique ((hb.norm.pow 2).sub (ha.norm.pow 2))
    (((regularizeTime_duality_intervalIntegral_tendsto hu hg ε hεpos hε0 a b).const_mul 2).congr
      fun m ↦ (regularizeTime_energy_identity T (hεpos m) (hu.locallyIntegrable (by norm_num))
        hweak a b).symm)

/-- Global Lions–Magenes representative theorem for a weak Gelfand
evolution with global `L²` data.  The original `V`-valued trajectory has a
canonical almost-everywhere equal `H`-valued representative that is strongly
continuous, has the prescribed integrated `V*` derivative on every finite
interval, and satisfies the exact two-time energy identity.

This is the abstract form of Evans §5.9.2, Theorem 3, which Evans uses in §7.1.1 (the
remark after the definition of weak solution) to make sense of the initial condition. -/
theorem exists_continuous_pivot_representative
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g) :
    ∃ uH : ℝ → H,
      Continuous uH ∧
      (uH =ᵐ[volume] fun t ↦ T.inclusion (u t)) ∧
      (∀ a b, HasIntegratedDualDerivativeOn T uH g a b) ∧
      ∀ a b,
        ‖uH b‖ ^ 2 - ‖uH a‖ ^ 2 =
          2 * ∫ t in a..b, g t (u t) := by
  obtain ⟨uH, ns, hns, hlim, hae, hIntegrated⟩ :=
    exists_pivot_representative_with_integratedDerivative T hu hg hweak
  have henergy (a b : ℝ) : ‖uH b‖ ^ 2 - ‖uH a‖ ^ 2 = 2 * ∫ t in a..b, g t (u t) :=
    sq_sub_sq_eq_of_tendsto_regularizeTime T hu hg hweak
      (ε := fun m ↦ (1 : ℝ) / ((ns m : ℝ) + 1)) (fun _ ↦ Nat.one_div_pos_of_nat)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hns.tendsto_atTop) (hlim a) (hlim b)
  refine ⟨uH, continuous_iff_continuousAt.2 fun x ↦ ?_, hae, hIntegrated, henergy⟩
  -- continuity on `[x - 1, x + 1]` from the energy representation of `‖uH‖²`
  have hcontOn := (hIntegrated (x - 1) (x + 1)).continuousOn_of_energy_representation
    (integrable_dual_pairing_of_memLp hg hu).intervalIntegrable
    fun t _ ↦ by linarith [henergy (x - 1) t]
  rw [uIcc_of_le (by linarith)] at hcontOn
  exact (hcontOn x ⟨by linarith, by linarith⟩).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-- Bundled form of `exists_continuous_pivot_representative`. -/
theorem nonempty_continuousPivotEvolution
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    [CompleteSpace H]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g) :
    Nonempty (ContinuousPivotEvolution T u g) := by
  obtain ⟨uH, hcont, hae, hint, henergy⟩ :=
    exists_continuous_pivot_representative T hu hg hweak
  exact ⟨{
    representative := uH
    continuous := hcont
    ae_eq_inclusion := hae
    integratedDerivative := hint
    energyIdentity := henergy
  }⟩

/-- Removing time regularization gives the exact Gelfand energy identity at
any two continuity points of the chosen `V`-valued representative.  Global
`L²` hypotheses supply the duality-product limit; continuity is required
only at the two endpoints.  For arbitrary representatives, use
`exists_continuous_pivot_representative`, which constructs the canonical
`H`-continuous representative and discharges these endpoint hypotheses. -/
theorem weakTimeDerivative_energy_identity_at_continuityPoints
    [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    {u : ℝ → V} {g : ℝ → StrongDual ℝ V}
    (hu : MemLp u 2 (volume : Measure ℝ))
    (hg : MemLp g 2 (volume : Measure ℝ))
    (hweak : HasWeakTimeDerivativeOn Set.univ (T.energyToDual ∘ u) g)
    {a b : ℝ} (hua : ContinuousAt u a) (hub : ContinuousAt u b) :
    ‖T.inclusion (u b)‖ ^ 2 - ‖T.inclusion (u a)‖ ^ 2 =
      2 * ∫ t in a..b, g t (u t) := by
  have huLoc : LocallyIntegrable u (volume : Measure ℝ) := hu.locallyIntegrable (by norm_num)
  have hreg {s : ℝ} (hs : ContinuousAt u s) := (T.inclusion.continuous.tendsto _).comp
    (regularizeTime_tendsto_of_continuousAt huLoc (fun m : ℕ ↦ (1 : ℝ) / ((m : ℝ) + 1))
      (fun _ ↦ Nat.one_div_pos_of_nat) tendsto_one_div_add_atTop_nhds_zero_nat hs)
  exact sq_sub_sq_eq_of_tendsto_regularizeTime T hu hg hweak (fun _ ↦ Nat.one_div_pos_of_nat)
    tendsto_one_div_add_atTop_nhds_zero_nat (hreg hua) (hreg hub)

end RegularizedEnergy

end PDE.Analysis.Evolution
