/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Existence

/-!
# A uniform excursion for noncompressive viscous profiles

The local profile theorem controls an entire connecting curve, not just its
endpoints. Consequently, a noncompressive profile joining distinct nearby
states must leave a fixed neighborhood of the left state. That neighborhood
can be chosen before the right state, speed, and profile.

This conclusion requires no bound on the range of the supplied profile. It
isolates the additional information needed when applying the local theorem
to a complete connection.

In the notation of Evans, §11.4.1, a traveling wave (3)-(5) from `u_l` to a nearby `u_r`
that lies in no `S_k^-(u_l)` must leave a fixed ball around `u_l`. So a wave that stays in
that ball ends in some `S_k^-(u_l)`. For some fluxes that satisfy the hypotheses of that
section, `exists_fixed_flux_nonLax_viscous_profiles` gives waves that leave the ball and end at
nearby `u_r` outside every `S_k^-(u_l)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (3)-(5) and (12), Theorem 1;
  §11.2.3, the definition of `S_k^-(z₀)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Every noncompressive complete profile with distinct nearby endpoints makes
a uniformly positive excursion from its left state. The two radii depend only
on the flux and the fixed left state, not on the speed or the connecting curve. -/
theorem exists_viscousProfile_escape_radius {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ ∞ flux) (hhyper : ∀ u, IsStrictlyHyperbolicAt flux u)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) (q : ℝ^m) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < ρ ∧
      ∀ uR ∈ ball q δ, uR ≠ q → ∀ speed : ℝ, ∀ v : ℝ → ℝ^m,
        IsViscousProfile flux q uR speed v →
        (¬ ∃ k, characteristicSpeed flux k uR < speed ∧
          speed < characteristicSpeed flux k q) →
        ∃ t, ρ ≤ dist (v t) q := by
  classical
  obtain ⟨δ, ρ, hδ, hδρ, hlocal⟩ := exists_small_viscousProfile_iff_lax hflux hhyper hgn q
  refine ⟨δ, ρ, hδ, hδρ, fun uR huR hne speed v hv hnoncompressive ↦ ?_⟩
  have hleave : ¬ ∀ t, v t ∈ ball q ρ :=
    fun hball ↦ hnoncompressive ((hlocal uR huR hne speed).mp ⟨v, hv, hball⟩).2
  obtain ⟨t, ht⟩ := not_forall.mp hleave
  exact ⟨t, by simpa only [mem_ball, not_lt] using ht⟩

end PDE.Hyperbolic.ConservationLaw.System
