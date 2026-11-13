/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Basic
public import PDE.Hyperbolic.Quasilinear.RiemannInvariant

/-!
# Two-system equations in Riemann invariants

For the first invariant, its differential is parallel to the second left
eigencovector of the flux Jacobian; the second invariant uses the first
eigencovector. Consequently the two compositions with a classical solution
are transported by the opposite characteristic speeds.

The theorem on the half-space `t > 0` is Theorem 1 of Evans, §11.3.1, equation (6), for a
smooth solution. The hypothesis is the condition (2) that the differential of each invariant
is parallel to the other left eigenvector; the transport equations are derived.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.3.1, definition of Riemann invariants and Theorem 1,
  equations (2) and (5)-(6).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- A classical solution of the conservative system solves the quasilinear system whose
coefficient at each attained state is the flux Jacobian. -/
theorem IsClassicalSolutionOn.quasilinear {flux : ℝ^m → ℝ^m} {U : Set ℝ^2} {u : ℝ^2 → ℝ^m}
    (hu : IsClassicalSolutionOn flux U u) :
    Quasilinear.IsClassicalSolutionOn (fderiv ℝ flux) U u :=
  ⟨hu.differentiableAt, fun _ hp ↦ hu.quasilinearResidual_eq_zero hp⟩

/-- Flux strict hyperbolicity is the general spectral property of its Jacobian. -/
theorem IsStrictlyHyperbolicAt.quasilinear {flux : ℝ^m → ℝ^m} {state : ℝ^m}
    (hflux : IsStrictlyHyperbolicAt flux state) :
    Quasilinear.IsStrictlyHyperbolicAt (fderiv ℝ flux) state :=
  hflux.2

/-- Either invariant of a two-system satisfies transport with the other
family's speed, directly from the original covector condition. -/
theorem IsClassicalSolutionOn.riemannInvariant_transport {flux : ℝ^2 → ℝ^2} {U : Set ℝ^2}
    {u : ℝ^2 → ℝ^2} (hu : IsClassicalSolutionOn flux U u) {w : Fin 2 → ℝ^2 → ℝ}
    {speed : Fin 2 → ℝ^2 → ℝ} {left : Fin 2 → ℝ^2 → ℝ^2 →L[ℝ] ℝ}
    (hw : ∀ i state, DifferentiableAt ℝ (w i) state)
    (hleft : ∀ i state v, left i state (fderiv ℝ flux state v) = speed i state * left i state v)
    (hparallel : ∀ i state, ∃ a : ℝ, fderiv ℝ (w i) state = a • left i.rev state) {p : ℝ^2}
    (hp : p ∈ U) (i : Fin 2) :
    (∂[0] (w i ∘ u)) p + speed i.rev (u p) * (∂[1] (w i ∘ u)) p = 0 :=
  Quasilinear.riemannInvariant_transport (hu.differentiableAt p hp) (hw i (u p))
    (hu.quasilinear.residual_eq_zero p hp) (hleft i.rev (u p)) (hparallel i (u p))

/-- Both swapped-speed transport equations hold for every positive time.
Only smoothness of the solution on the forward half-space is used. -/
theorem riemannInvariants_transport_forward {flux : ℝ^2 → ℝ^2} {u : ℝ^2 → ℝ^2}
    (hflux : Differentiable ℝ flux) (hu : ContDiffOn ℝ ∞ u PDE.Common.positiveTimeDomain)
    (hpde : ∀ p ∈ PDE.Common.positiveTimeDomain, fluxResidual flux u p = 0) {w : Fin 2 → ℝ^2 → ℝ}
    {speed : Fin 2 → ℝ^2 → ℝ} {left : Fin 2 → ℝ^2 → ℝ^2 →L[ℝ] ℝ} (hw : ∀ i, Differentiable ℝ (w i))
    (hleft : ∀ i state v, left i state (fderiv ℝ flux state v) = speed i state * left i state v)
    (hparallel : ∀ i state, ∃ a : ℝ, fderiv ℝ (w i) state = a • left i.rev state) :
    ∀ p ∈ PDE.Common.positiveTimeDomain, ((∂[0] (w 0 ∘ u)) p + speed 1 (u p) * (∂[1] (w 0 ∘ u)) p =
      0) ∧ ((∂[0] (w 1 ∘ u)) p + speed 0 (u p) * (∂[1] (w 1 ∘ u)) p = 0) := by
  have hsol : IsClassicalSolutionOn flux PDE.Common.positiveTimeDomain u := by
    refine ⟨fun p hp ↦ ?_, fun p _ ↦ hflux (u p), hpde⟩
    exact (hu.contDiffAt (PDE.Common.isOpen_positiveTimeDomain.mem_nhds hp)).differentiableAt
      (by simp)
  exact fun p hp ↦ ⟨hsol.riemannInvariant_transport hw hleft hparallel hp 0,
    hsol.riemannInvariant_transport hw hleft hparallel hp 1⟩

end PDE.Hyperbolic.ConservationLaw.System
