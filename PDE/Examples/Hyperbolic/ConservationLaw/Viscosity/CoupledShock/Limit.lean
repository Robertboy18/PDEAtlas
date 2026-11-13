/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.Viscosity.CoupledShock.Profile
public import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.Limit
import PDE.Analysis.Integration.LocallyIntegrable

/-!
# The entropy limit of a coupled viscous shock family

The two shock locations are distinct. The initial data converge locally in `L¹`, and
they depend on the viscosity. The vanishing-viscosity criterion
`entropySolution_of_vanishingViscosity_convergingData` gives the initial weak equation
and every `C¹` convex entropy inequality for the limit (`isEntropyWeakSolution_limit`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common BurgersEquation.Viscosity
open PDE.Hyperbolic.ConservationLaw
open scoped Topology

namespace PDE.Examples.ConservationLaw.CoupledShock

/-- The discontinuous initial datum with two stationary jumps. -/
def datum (x : ℝ) : ℝ^2 := mix (stationaryJump (-1) x) (stationaryJump 1 x)

/-- The same discontinuous state at every time. -/
def limit (p : ℝ^2) : ℝ^2 := datum (p 1)

/-- The datum is measurable. -/
theorem measurable_datum : Measurable datum := by
  have hj (a : ℝ) : Measurable (stationaryJump a) :=
    Measurable.ite measurableSet_Iio measurable_const measurable_const
  exact ((hj (-1)).smul measurable_const).add ((hj 1).smul measurable_const)

/-- The datum is bounded by `6`. -/
theorem norm_datum_le (x : ℝ) : ‖datum x‖ ≤ 6 := by
  have hj (a : ℝ) : ‖stationaryJump a x‖ ≤ 2 := by
    unfold stationaryJump
    split_ifs <;> norm_num
  exact (norm_mix_le _ _).trans (by linarith [hj (-1), hj 1])

/-- Away from the jumps at `x = ±1` the profile curves converge to the datum. -/
theorem tendsto_curve {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    Tendsto (fun ε : ℝ ↦ curve ε x) (𝓝[>] 0) (𝓝 (datum x)) :=
  ((tendsto_stationaryProfile h₁).smul_const _).add
    ((tendsto_stationaryProfile h₂).smul_const _)

/-- The curves converge almost everywhere on the initial line. -/
theorem ae_tendsto_curve :
    ∀ᵐ x : ℝ, Tendsto (fun ε : ℝ ↦ curve ε x) (𝓝[>] 0) (𝓝 (datum x)) := by
  filter_upwards [volume.ae_ne (-1 : ℝ), volume.ae_ne (1 : ℝ)] with x h₁ h₂
  exact tendsto_curve h₁ h₂

/-- The initial slices converge to the datum in `L¹` on every compact set. -/
theorem tendsto_initial_L1 (K : Set ℝ) (hK : IsCompact K) :
    Tendsto (fun ε : ℝ ↦ ∫ x in K, ‖viscous ε !₂[0, x] - datum x‖)
      (𝓝[>] 0) (𝓝 0) := by
  have hm : AEStronglyMeasurable datum volume := measurable_datum.aestronglyMeasurable
  have hlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun ε : ℝ ↦ ‖curve ε x - datum x‖) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_of_ae ae_tendsto_curve] with x hx
    simpa using (hx.sub (tendsto_const_nhds (x := datum x))).norm
  have hint : IntegrableOn (fun _ : ℝ ↦ (12 : ℝ)) K :=
    integrableOn_const hK.measure_ne_top
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict K) (fun _ : ℝ ↦ (12 : ℝ))
    (Eventually.of_forall fun ε ↦
      (((contDiff_curve ε).continuous.aestronglyMeasurable).sub hm).norm.restrict)
    (Eventually.of_forall fun ε ↦ Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      apply (norm_sub_le _ _).trans
      have hb := add_le_add (norm_viscous_le ε !₂[0, x]) (norm_datum_le x)
      norm_num [viscous] at hb
      exact hb)
    hint hlim
  simpa [viscous] using ht

/-- Almost everywhere spacetime convergence of the same family. -/
theorem ae_tendsto_viscous :
    ∀ᵐ p ∂volume.restrict forwardHalfSpace,
      Tendsto (fun ε : ℝ ↦ viscous ε p) (𝓝[>] 0) (𝓝 (limit p)) := by
  have hp : ∀ᵐ p : ℝ × ℝ,
      Tendsto (fun ε : ℝ ↦ curve ε p.2) (𝓝[>] 0) (𝓝 (datum p.2)) :=
    Measure.quasiMeasurePreserving_snd.ae ae_tendsto_curve
  have he := measurePreserving_spaceTimePair.symm.quasiMeasurePreserving.ae hp
  apply ae_restrict_of_ae
  simpa [spaceTimePair, viscous, limit] using he

/-- The discontinuous limit satisfies the initial weak equation and all convex entropy
inequalities. -/
theorem isEntropyWeakSolution_limit :
    IsWeakInitialValueSolution flux datum limit ∧
      System.IsEntropyWeakSolution flux forwardHalfSpace limit := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  have h := System.entropySolution_of_vanishingViscosity_convergingData
    (u := viscous) (v := limit) (ε := id) (M := 6) (g := datum)
    (contDiff_flux.of_le (by simp)) (hpos.mono fun _ hε ↦ hε.le)
    nhdsWithin_le_nhds
    (Eventually.of_forall fun ε ↦ (contDiff_viscous ε).contDiffOn.of_le (by simp))
    (Eventually.of_forall fun ε ↦ (contDiff_viscous ε).continuous.continuousOn)
    (hpos.mono fun ε hε p _ ↦ viscous_equation (ne_of_gt hε) p)
    (Eventually.of_forall fun ε ↦ Eventually.of_forall (norm_viscous_le ε))
    (locallyIntegrable_of_measurable_norm_le_const measurable_datum (by norm_num) norm_datum_le)
    tendsto_initial_L1 ae_tendsto_viscous
  exact h.2.2

/-- The limiting state is nonconstant: both shock interfaces are present. -/
theorem limit_three_states :
    limit !₂[1, -2] = mix 2 2 ∧
      limit !₂[1, 0] = mix (-2) 2 ∧ limit !₂[1, 2] = mix (-2) (-2) := by
  norm_num [limit, datum, stationaryJump]

end PDE.Examples.ConservationLaw.CoupledShock
