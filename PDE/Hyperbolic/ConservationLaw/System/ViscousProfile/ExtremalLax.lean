/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ExtremalSpeeds
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.LaxDichotomy

/-!
# Strict Lax necessity on an extreme characteristic branch

A genuinely nonlinear branch has two strict orientations near zero strength.
The extremal speed bounds exclude the reverse orientation for every complete
viscous profile with distinct endpoints, even if it leaves the state neighborhood.

For the first and last families, in the notation of Evans, §11.4.1: a traveling wave (3)-(5)
from `u_l` to a nearby `u_r ≠ u_l` on the branch forces `u_r ∈ S_k^-(u_l)`, as in (12). The
proof uses the speed bounds at the two endpoints, so it covers every complete profile, small or
not. For a middle family, profiles that are not small can end at nearby states outside every
`S_k^-(u_l)` (`exists_fixed_flux_nonLax_viscous_profiles`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.1, equations (3)-(5) and (12), Theorem 1 and step 2
  of its proof; §11.2.3, Theorem 2(iii) and the definition of `S_k^-(z₀)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter
open scoped Topology

/-- On the first or last genuinely nonlinear branch, every profile with distinct
nearby branch endpoints satisfies strict Lax. The parameter neighborhood is chosen before all
profiles. -/
theorem eventually_lax_of_viscousProfile_extremal {m : ℕ} {flux : ℝ^(m + 1) → ℝ^(m + 1)}
    {q r : ℝ^(m + 1)} {k : Fin (m + 1)} {S : ℝ → ℝ^(m + 1)} {speed : ℝ → ℝ}
    (hflux : ContDiff ℝ 1 flux) (hhyper : ∀ u, IsStrictlyHyperbolicAt flux u)
    (hgn : IsGenuinelyNonlinearFamily flux k)
    (hr : Module.End.HasEigenvector (fderiv ℝ flux q).toLinearMap (characteristicSpeed flux k q) r)
    (hS₀ : S 0 = q) (hspeed₀ : speed 0 = characteristicSpeed flux k q) (hS : HasDerivAt S r 0)
    (hhalf : HasDerivAt speed ((1 / 2 : ℝ) * fderiv ℝ (characteristicSpeed flux k) q r) 0)
    (hk : k = 0 ∨ k = Fin.last m) :
    ∀ᶠ s in 𝓝 0, ∀ v : ℝ → ℝ^(m + 1), S s ≠ q → IsViscousProfile flux q (S s) (speed s) v →
      characteristicSpeed flux k (S s) < speed s ∧ speed s < characteristicSpeed flux k q := by
  have horientation := eventually_lax_or_reverse (hgn q).1 hS₀ hspeed₀ hS hhalf ((hgn q).2 r hr)
  filter_upwards [horientation] with s hs v hne hv
  have hsne : s ≠ 0 := by
    rintro rfl
    exact hne hS₀
  rcases hs hsne with hLax | hreverse
  · exact hLax
  · rcases hk with rfl | rfl
    · exact (not_lt_of_ge (hv.smallest_characteristicSpeed_le hflux hne.symm (hhyper (S s)))
        hreverse.2).elim
    · exact (not_lt_of_ge (hv.le_largest_characteristicSpeed hflux hne.symm (hhyper q))
        hreverse.1).elim

end PDE.Hyperbolic.ConservationLaw.System
