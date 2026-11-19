/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ShockCurve.StrictEntropy
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Entropy
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Existence

/-!
# Unrestricted profile necessity with a strictly convex entropy

Every viscous profile satisfies the jump inequality for each C¹ convex
entropy pair. A strictly convex pair therefore selects strict Lax shocks among
nearby distinct endpoints, regardless of distant excursions of the profile.
The existence of this compatible entropy is an additional hypothesis.

For a smooth globally strictly hyperbolic genuinely nonlinear flux, the
small-profile construction supplies the converse. The resulting unrestricted
equivalence retains the supplied strictly convex entropy hypothesis.

`exists_viscousProfile_iff_lax_of_strict_entropy` is Evans, §11.4.1, Theorem 1, under the
additional hypothesis of a strictly convex entropy: near `u_l`, a traveling wave (3)-(5)
exists exactly when Rankine–Hugoniot and the Lax entropy condition (42) of §11.2.3 hold for
some `k`, which near `u_l` is the condition `u_r ∈ S_k^-(u_l)` of (12). Without the entropy,
profiles that are not small can end at nearby states outside every `S_k^-(u_l)`
(`exists_fixed_flux_nonLax_viscous_profiles`). We obtain necessity from the entropy jump
inequality, the form that (28)-(29) of §11.4.2 take for the shock (6), and sufficiency from
the small-profile construction.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (3)-(6) and (12), Theorem 1 and its proof;
  §11.4.2, equations (25)-(29); §11.2.3, equation (42).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

/-- A globally strictly convex compatible C¹ entropy forces every unrestricted
viscous profile with nearby distinct endpoints to satisfy all strict Lax
inequalities. -/
theorem exists_radius_lax_of_strict_entropy_viscousProfile {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (q : ℝ^m) (hhyper : IsStrictlyHyperbolicAt flux q)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) :
    ∃ δ > 0, ∀ E : ConvexEntropyPair flux,
      StrictConvexOn ℝ univ E.entropy →
      ∀ r ∈ ball q δ, r ≠ q → ∀ speed : ℝ, ∀ v : ℝ → ℝ^m,
      IsViscousProfile flux q r speed v →
      E.entropyFlux r - E.entropyFlux q < speed * (E.entropy r - E.entropy q) ∧
        ∃ k, characteristicSpeed flux k r < speed ∧
          speed < characteristicSpeed flux k q ∧
          (∀ j, j < k → characteristicSpeed flux j q < speed) ∧
          (∀ j, k < j → speed < characteristicSpeed flux j r) := by
  obtain ⟨δ, hδ, hcriterion⟩ := exists_radius_lax_of_strict_entropy_admissible hflux q hhyper hgn
  exact ⟨δ, hδ, fun E hstrict r hr hne speed v hv ↦
    hcriterion E hstrict r hr hne speed (hv.isAdmissibleShock E)⟩

/-- For a smooth globally strictly hyperbolic genuinely nonlinear flux with a
supplied globally strictly convex compatible entropy, nearby distinct states admit
an unrestricted viscous profile exactly when they satisfy Rankine–Hugoniot and
the strict Lax inequalities. The entropy is an additional hypothesis, and the
radius is chosen before it. The sufficiency proof constructs a small profile. -/
theorem exists_viscousProfile_iff_lax_of_strict_entropy {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ ∞ flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) (q : ℝ^m) :
    ∃ δ > 0, ∀ E : ConvexEntropyPair flux,
      StrictConvexOn ℝ univ E.entropy →
      ∀ r ∈ ball q δ, r ≠ q → ∀ speed : ℝ,
        (∃ v : ℝ → ℝ^m, IsViscousProfile flux q r speed v) ↔
          RankineHugoniot flux q r speed ∧
            ∃ k, characteristicSpeed flux k r < speed ∧
              speed < characteristicSpeed flux k q := by
  obtain ⟨δ₁, hδ₁, hnecessary⟩ := exists_radius_lax_of_strict_entropy_viscousProfile
      (hflux.of_le (by simp)) q (hhyper q) hgn
  obtain ⟨δ₂, ρ, hδ₂, _hδρ, hsufficient⟩ :=
    exists_small_viscousProfile_iff_lax hflux hhyper hgn q
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun E hstrict r hr hne speed ↦ ?_⟩
  have hr₁ : r ∈ ball q δ₁ := ball_subset_ball (min_le_left _ _) hr
  have hr₂ : r ∈ ball q δ₂ := ball_subset_ball (min_le_right _ _) hr
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨_hproduction, k, hright, hleft, _hothers⟩ := hnecessary E hstrict r hr₁ hne speed v hv
    exact ⟨hv.rankineHugoniot E.flux_differentiable, k, hright, hleft⟩
  · intro hlax
    obtain ⟨v, hv, _hrange⟩ := (hsufficient r hr₂ hne speed).mpr hlax
    exact ⟨v, hv⟩

end PDE.Hyperbolic.ConservationLaw.System
