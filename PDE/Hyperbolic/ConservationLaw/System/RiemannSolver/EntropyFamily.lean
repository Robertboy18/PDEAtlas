/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve.Construction
public import PDE.Hyperbolic.ConservationLaw.System.RiemannSolver.EntropyProduction

/-!
# Local wave families retaining entropy dissipation

The local elementary wave family of `WaveCurve.Construction` retains the half-speed derivative
of its shock branches at zero strength, (31) of Evans, §11.2.3. With the positive orientation
of a genuinely nonlinear family this gives entropy dissipation along the negative Hugoniot
branch, uniformly in the left state and in every convex compatible entropy pair. The wave
family, its chart and its carriers are those of
`exists_local_elementary_wave_family_with_shock_speed_deriv`, so the local inverse strength map
is the one in the proof of Theorem 4 of §11.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.3, proof of Theorem 2, equation (31); §11.2.4,
  Theorem 4; §11.4.2, equations (25)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped Topology

open Classical in
/-- A `C²` strictly hyperbolic flux whose ordered families are genuinely
nonlinear or linearly degenerate has a local elementary wave family.
The shock and flow carriers are retained, with their regularity and exact
equations, for constructing uniformly bounded self-similar fans. The negative
Hugoniot branches dissipate all convex compatible entropies on a neighborhood
chosen independently of the entropy pair. No wave curves,
admissibility inequalities, or smooth eigenframe are inputs. -/
theorem exists_local_elementary_wave_family_with_shock_entropy {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hfamilies : ∀ k, IsGenuinelyNonlinearFamily flux k ∨ IsLinearlyDegenerateFamily flux k)
    (q₀ : ℝ^m) :
    ∃ fields : Fin m → CharacteristicField flux,
      (∀ k, (fields k).speed = characteristicSpeed flux k) ∧
      ∃ states : Set (ℝ^m), IsOpen states ∧ q₀ ∈ states ∧
      ∃ W : LocalWaveFamily flux fields states, W.IsElementary ∧
      ∃ b : Module.Basis (Fin m) ℝ (ℝ^m),
        (∀ k, b k = (fields k).rightEigenvector q₀) ∧
      ∃ S : Fin m → ℝ × ℝ^m → ℝ^m,
      ∃ speed : Fin m → ℝ × ℝ^m → ℝ,
      ∃ R : Fin m → ℝ × ℝ^m → ℝ^m,
        (∀ k, ContDiffAt ℝ 1 (S k) (0, q₀) ∧
          ContDiffAt ℝ 1 (speed k) (0, q₀) ∧
          ContDiffAt ℝ 1 (R k) (0, q₀) ∧
          ContDiffAt ℝ 1 (fun p : ℝ × ℝ^m ↦ W.curve k p.1 p.2) (0, q₀)) ∧
        (∀ᶠ q in 𝓝 q₀, ∀ k,
          S k (0, q) = q ∧ R k (0, q) = q ∧
            speed k (0, q) = (fields k).speed q) ∧
        (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k,
          W.curve k p.1 p.2 =
            (if IsGenuinelyNonlinearFamily flux k then
              if p.1 ≤ 0 then S k p else R k p else R k p) ∧
          RankineHugoniot flux p.2 (S k p) (speed k p) ∧
          HasDerivAt (fun t ↦ R k (t, p.2))
            ((fields k).rightEigenvector (R k p)) p.1) ∧
        (∀ k, IsGenuinelyNonlinearFamily flux k →
          0 < fderiv ℝ (fields k).speed q₀ ((fields k).rightEigenvector q₀)) ∧
        (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), ∀ k,
          IsGenuinelyNonlinearFamily flux k → p.1 ≤ 0 → ∀ E : ConvexEntropyPair flux,
            E.entropyFlux (S k p) - E.entropyFlux p.2 ≤
              speed k p * (E.entropy (S k p) - E.entropy p.2)) := by
  obtain ⟨fields, hcanonical, states, hopen, hq₀, W, hW, b, hb, S, speed, R, hreg, hz, hcurve,
    hpositive, hhalf⟩ := exists_local_elementary_wave_family_with_shock_speed_deriv hflux hhyper
      hfamilies q₀
  refine ⟨fields, hcanonical, states, hopen, hq₀, W, hW, b, hb, S, speed, R, hreg, hz, hcurve,
    hpositive, eventually_all.mpr fun k ↦ ?_⟩
  by_cases hgn : IsGenuinelyNonlinearFamily flux k
  · exact (eventually_shock_entropy_of_positive_speed_deriv (hreg k).1 (hreg k).2.1
      (hz.mono fun _ h ↦ (h k).1) (hcurve.mono fun _ h ↦ (h k).2.1) (hhalf k)
      (mul_pos (by norm_num) (hpositive k hgn))).mono fun _ hp _ ↦ hp
  · exact Eventually.of_forall fun _ h ↦ (hgn h).elim

end PDE.Hyperbolic.ConservationLaw.System
