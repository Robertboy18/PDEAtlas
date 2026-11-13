/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.MovingBallTransport
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Localization of classical wave energy to positive times

A smooth reparametrization of time gives a global representative of a forward smooth
field, agreeing with it above any prescribed positive time. Thus the
shrinking-ball transport formula applies locally without negative-time regularity.
-/

@[expose] public section

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis PDE.Common Real Set
open scoped Topology

variable {n : ℕ}

/-- A field smooth for positive times has a global smooth representative agreeing with
it above any fixed positive time. -/
theorem exists_contDiff_eqOn_forward {m : ℕ∞} {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ m u {p | 0 < p 0}) {a : ℝ} (ha : 0 < a) :
    ∃ v : ℝ^(n + 1) → ℝ, ContDiff ℝ m v ∧ EqOn v u {p | a ≤ p 0} := by
  let ε := a / 2
  have hε : 0 < ε := half_pos ha
  let ρ : ℝ → ℝ := fun t ↦ ε + smoothTransition ((t - ε) / ε) * (t - ε)
  have hρ : ContDiff ℝ m ρ := contDiff_const.add ((smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const ε)).mul (contDiff_id.sub contDiff_const))
  have hpos (t : ℝ) : 0 < ρ t := by
    dsimp [ρ]
    by_cases ht : t ≤ ε
    · rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr ht) hε.le), zero_mul, add_zero]
      exact hε
    · exact add_pos_of_pos_of_nonneg hε
        (mul_nonneg (smoothTransition.nonneg _) (sub_nonneg.mpr (le_of_not_ge ht)))
  have heq (t : ℝ) (ht : a ≤ t) : ρ t = t := by
    dsimp [ρ]
    rw [smoothTransition.one_of_one_le
      ((le_div_iff₀ hε).mpr (by dsimp [ε]; linarith)), one_mul, add_sub_cancel]
  let P : ℝ^(n + 1) → ℝ^(n + 1) := fun p ↦ timeSpaceCons (ρ (p 0)) (spatialPart p)
  have hP : ContDiff ℝ m P := (contDiff_timeSpaceCons_uncurry n).comp
      ((hρ.comp (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (n + 1)) 0).contDiff).prodMk
        (spatialPartCLM n).contDiff)
  refine ⟨u ∘ P, hu.comp_contDiff hP (fun p ↦ ?_), ?_⟩
  · exact hpos (p 0)
  · intro p hp
    change u (timeSpaceCons (ρ (p 0)) (spatialPart p)) = u p
    rw [heq (p 0) hp, timeSpaceCons_spatialPart]

/-- Agreement above a time slice gives agreement of germs at every later point. -/
theorem eventuallyEq_of_eqOn_forward {u v : ℝ^(n + 1) → ℝ} {a : ℝ}
    (h : EqOn u v {p | a ≤ p 0}) {p : ℝ^(n + 1)} (hp : a < p 0) :
    u =ᶠ[𝓝 p] v := by
  filter_upwards [(isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds hp]
    with q hq using h hq.le

private theorem partialDeriv_eventuallyEq {u v : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (h : u =ᶠ[𝓝 p] v) (i : Fin (n + 1)) :
    (∂[i] u) =ᶠ[𝓝 p] (∂[i] v) :=
  (h.fderiv (𝕜 := ℝ)).mono fun _ hq ↦ PDE.partialDeriv_eq_of_fderiv_eq hq i

/-- The classical wave operator depends only on the local germ. -/
theorem waveOperator_congr_nhds {u v : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)} (h : u =ᶠ[𝓝 p] v) :
    waveOperator u p = waveOperator v p := by
  simp only [waveOperator, PDE.partialDeriv_congr_nhds _ (partialDeriv_eventuallyEq h _)]

/-- The energy density depends only on the local germ. -/
theorem classicalWaveEnergyDensity_congr_nhds {u v : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (h : u =ᶠ[𝓝 p] v) :
    classicalWaveEnergyDensity u p = classicalWaveEnergyDensity v p := by
  simp only [classicalWaveEnergyDensity, classicalWaveSpatialGradient,
    PDE.partialDeriv_congr_nhds _ h]

/-- Agreement above a time slice preserves the shrinking-ball energy at later times. -/
theorem backwardConeEnergy_eq_of_eqOn_forward {u v : ℝ^(n + 1) → ℝ} {a : ℝ}
    (h : EqOn u v {p | a ≤ p 0}) (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : a < t) :
    backwardConeEnergy u c T t = backwardConeEnergy v c T t := by
  unfold backwardConeEnergy ballIntegral
  exact setIntegral_congr_fun measurableSet_ball fun x _ ↦ classicalWaveEnergyDensity_congr_nhds
    (eventuallyEq_of_eqOn_forward h (by simpa using ht))

/-- The shrinking-ball energy derivative for a wave smooth only at positive times.
The global transport theorem is applied to a smooth local representative. -/
theorem hasDerivAt_backwardConeEnergy_forward [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : 0 < t) (htT : t < T)
    (hwave : ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) = 0) :
    HasDerivAt (backwardConeEnergy u c T)
      (sphereIntegral n (classicalWaveConeBoundaryFlux u c t) c (T - t)) t := by
  obtain ⟨v, hv, heq⟩ := exists_contDiff_eqOn_forward hu (half_pos ht)
  have hhalf : t / 2 < t := half_lt_self ht
  have hgerm (x : ℝ^n) : v =ᶠ[𝓝 (timeSpaceCons t x)] u :=
    eventuallyEq_of_eqOn_forward heq (by simpa using hhalf)
  have hres : ballIntegral n (fun x ↦ classicalWaveEnergyBalanceResidual v (timeSpaceCons t x))
        c (T - t) = 0 := by
    unfold ballIntegral
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    apply classicalWaveEnergyBalanceResidual_eq_zero hv.contDiffAt
    rw [waveOperator_congr_nhds (hgerm x)]
    exact hwave x hx
  have hflux : classicalWaveConeBoundaryFlux v c t = classicalWaveConeBoundaryFlux u c t := by
    funext x
    simp only [classicalWaveConeBoundaryFlux, classicalWaveSpatialGradient,
      PDE.partialDeriv_congr_nhds _ (hgerm x), classicalWaveEnergyDensity_congr_nhds (hgerm x)]
  have hd := hasDerivAt_backwardConeEnergy hv c T htT
  rw [hres, zero_add, hflux] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hhalf] with s hs
  exact backwardConeEnergy_eq_of_eqOn_forward heq.symm c T hs

/-- Vanishing energy forces the energy density to vanish pointwise on a positive-time ball. -/
theorem classicalWaveEnergyDensity_eq_zero_on_ball_forward {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (c : ℝ^n) {t r : ℝ} (ht : 0 < t)
    (henergy : ballIntegral n (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons t x)) c r = 0) :
    ∀ x ∈ Metric.ball c r, classicalWaveEnergyDensity u (timeSpaceCons t x) = 0 := by
  obtain ⟨v, hv, heq⟩ := exists_contDiff_eqOn_forward hu (half_pos ht)
  have he (x : ℝ^n) : classicalWaveEnergyDensity v (timeSpaceCons t x) =
        classicalWaveEnergyDensity u (timeSpaceCons t x) := classicalWaveEnergyDensity_congr_nhds
      (eventuallyEq_of_eqOn_forward heq (by simpa using half_lt_self ht))
  have hz : ballIntegral n
      (fun x ↦ classicalWaveEnergyDensity v (timeSpaceCons t x)) c r = 0 := by
    simpa only [he] using henergy
  intro x hx
  rw [← he x]
  exact classicalWaveEnergyDensity_eq_zero_on_ball hv c t hz x hx

end WaveEquation
