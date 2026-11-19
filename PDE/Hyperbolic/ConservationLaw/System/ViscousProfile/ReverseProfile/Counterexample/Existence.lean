/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.EscapeRadius
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Counterexample.EndpointSpectra
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Counterexample.Family
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Reference.Construction

import CAS.ExactTactic

/-!
# One fixed flux with arbitrarily small noncompressive jumps

We first choose the selected reference and construct its compact correction.
That fixes the flux for the whole family. The endpoint calculation then gives
small nonzero right states with positive speeds, complete viscous profiles, and
failure of Lax compression in every canonical characteristic family.

Small endpoints do not make these profiles small everywhere. The local profile
theorem supplies a positive excursion radius for the fixed flux and left state.
We choose each endpoint inside both its requested tolerance and the local
endpoint neighborhood, so every resulting profile must reach that radius.

The flux satisfies the hypotheses of Evans, §11.4.1, Theorem 1: it is smooth, strictly
hyperbolic and genuinely nonlinear in every family. For `u_l = 0` and every `ε > 0` it has a
traveling wave (3)-(5) connecting `u_l` to some `u_r ≠ u_l` with `|u_r| < ε`, while `u_r`
lies in no `S_k^-(u_l)`. Each of these waves leaves a fixed ball around `u_l`. For waves
that stay near `u_l`, a traveling wave to `u_r` exists exactly when `u_r` lies in some
`S_k^-(u_l)` (`exists_small_viscousProfile_iff_lax`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (3)-(5) and (12)-(15), Theorem 1 and steps
  1-2 of its proof; §11.2.3, the definition of `S_k^-(z₀)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- A single smooth, globally strictly hyperbolic and genuinely nonlinear flux
has complete noncompressive viscous profiles joining zero to arbitrarily small
nonzero right states. All speeds are positive. Rankine–Hugoniot holds for each
connection, but no canonical characteristic family satisfies Lax compression.

The positive excursion radius is fixed before the endpoint tolerance: every
chosen profile reaches at least that distance from zero. The selected reference,
correction, and profile family are constructed within the proof. -/
theorem exists_fixed_flux_nonLax_viscous_profiles :
    ∃ f : ℝ^3 → ℝ^3,
      ContDiff ℝ ∞ f ∧
      (∀ x, IsStrictlyHyperbolicAt f x) ∧
      (∀ k : Fin 3, IsGenuinelyNonlinearFamily f k) ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ ε : ℝ, 0 < ε → ∃ (uR : ℝ^3) (speed : ℝ) (q : ℝ → ℝ^3),
          uR ≠ 0 ∧ ‖uR‖ < ε ∧ 0 < speed ∧
          IsViscousProfile f 0 uR speed q ∧
          RankineHugoniot f 0 uR speed ∧
          (∀ k : Fin 3, ¬(characteristicSpeed f k uR < speed ∧
            speed < characteristicSpeed f k 0)) ∧
          ∃ t : ℝ, ρ ≤ dist (q t) 0 := by
  obtain ⟨δ, A, B, H, tStar, c, b, Ψ, T, N, i, j, hR⟩ := exists_unconditional_selected_rank_inputs
  -- The terminal state is the same event evaluation used by the selected family.
  -- Its strictly negative middle velocity supplies the required nonvanishing.
  have hmiddle := (hR.terminal_velocity.trans (by cas : (-4 : ℝ) < 0)).ne
  obtain ⟨P, hP, hPc, hhyper, hgn, r, hr, _hrCap, _hrTail, hleft, hright, hprofiles⟩ :=
    exists_selected_fixed_flux_viscous_profiles
      hR.positive hR.small hR.threshold_order hR.forcing_smooth hR.gate_support
      hR.flow_smooth hR.parameter_open hR.selected_mem hR.event_smooth
      hR.initial hR.ode hR.event i j hR.distinct
      hR.gate_time hR.gate_state.1.1 hR.gate_state.2.1 hR.gate_state.2.2
      hR.terminal_positive hR.terminal_ratio hR.displacement_match hR.weighted_match
      hmiddle hR.gate_rank.1 hR.gate_rank.2.1 hR.gate_rank.2.2
  -- The gate height already puts the threshold beyond both unit tail segments.
  have hzNonneg : 0 ≤ Ψ (tStar, ((δ, c), (0, 0))) 2 :=
    (by cas : (0 : ℝ) ≤ 2).trans hR.gate_state.2.1.le
  have hzsq : (2 : ℝ) ^ 2 ≤ (Ψ (tStar, ((δ, c), (0, 0))) 2) ^ 2 :=
    (sq_le_sq₀ (by cas : (0 : ℝ) ≤ 2) hzNonneg).2 hR.gate_state.2.1.le
  have hA1 : 1 ≤ A ^ 2 :=
    (by cas : (1 : ℝ) ≤ 2 ^ 2).trans (hzsq.trans hR.gate_state.2.2.le)
  have hb0 : ContDiff ℝ ∞ (fun y : ℝ ↦ b (c, y)) := by
    simpa only [Function.comp_def, id_eq] using
      hR.forcing_smooth.comp ((contDiff_const (c := c)).prodMk contDiff_id)
  -- Closed support avoidance includes both limiting endpoints. The endpoint
  -- lemmas derive their spectra, Rankine–Hugoniot, and failure of compression.
  obtain ⟨hf, _hcompact, _hhyperOn, _hgn, hsmall⟩ :=
    fixed_correction_arbitrarily_small_nonLax_profiles (δ := δ)
      hA1 hR.threshold_order hb0 (hR.gate_support.trans Ioo_subset_Icc_self)
      hP hPc (fun x _ ↦ hhyper x) hgn hr (fun s hs ↦ (hleft s hs).1)
      (fun μ hμ s hs ↦ (hright μ hμ s hs).1) hprofiles
  -- Choose the local radii only after fixing the total correction, and before ε.
  obtain ⟨η, ρ, hη, hηρ, hescape⟩ :=
    exists_viscousProfile_escape_radius hf hhyper hgn (0 : ℝ^3)
  refine ⟨concreteGatedFlux δ (clockFeedback A B) (fun y ↦ b (c, y)) + P,
    hf, hhyper, hgn, ρ, hη.trans hηρ, ?_⟩
  intro ε hε
  obtain ⟨μ, q, hμ, _hμr, _hμsmall, hne, hnorm, hq, hRH, hnonLax⟩ := hsmall (min ε η) (lt_min hε hη)
  have hnear : (!₂[0, 2000000 * μ, 0] : ℝ^3) ∈ ball (0 : ℝ^3) η := by
    simpa only [mem_ball, dist_zero_right] using hnorm.trans_le (min_le_right ε η)
  obtain ⟨t, ht⟩ := hescape _ hnear hne μ q hq (by
    rintro ⟨k, hk⟩
    exact hnonLax k hk)
  exact ⟨!₂[0, 2000000 * μ, 0], μ, q, hne,
    hnorm.trans_le (min_le_left ε η), hμ, hq, hRH, hnonLax, t, ht⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
