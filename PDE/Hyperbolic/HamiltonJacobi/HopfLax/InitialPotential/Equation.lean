/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.InitialPotential.Regularity
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Differentiability
public import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The equation of the continued Hopf–Lax potential

The continuation has the same germ as the value at every positive time.
Joint differentiability identifies the scalar spatial slice derivative with its
joint Fréchet derivative. Rademacher's theorem and the pointwise
Hamilton–Jacobi equation supply the identity needed for integration by parts.

`ae_forwardValue_residual_eq_zero` is the equation `w_t + F(w_x) = 0` of (34) in the proof of
Evans, §3.4.2, Theorem 2, almost everywhere in `ℝ × (0, ∞)`, with `F = L*` the `hamiltonian` of
`L`. Evans takes it from §3.3.2, Theorem 6.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 6; §3.4.2, Theorem 2 and its
  proof, equation (34).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal

namespace HamiltonJacobi.HopfLax

/-- The continued scalar potential satisfies the dual Hamiltonian equation
through its joint derivatives. -/
theorem ae_forwardValue_residual_eq_zero {L h : ℝ → ℝ} (hL : Superlinear L)
    (hconv : ConvexOn ℝ univ L) {K : ℝ≥0} (hh : LipschitzWith K h) :
    ∀ᵐ p ∂volume.restrict (univ ×ˢ Ioi (0 : ℝ)), fderiv ℝ (forwardValue L h) p (0, 1) +
      hamiltonian L (fderiv ℝ (forwardValue L h) p (1, 0)) = 0 := by
  have hcont := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  obtain ⟨C, hC⟩ := exists_lipschitzWith_forwardValue hL hconv hh
  have hdiff := hC.ae_differentiableAt (μ := volume.prod volume)
  have hlower : ∀ y, -(-h 0) - (K : ℝ) * ‖y‖ ≤ h y := by
    intro y
    have hbound := hh.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at hbound
    linarith [(neg_le_abs (h y - h 0)).trans hbound]
  rw [Measure.volume_eq_prod]
  filter_upwards [ae_restrict_of_ae hdiff,
    ae_restrict_mem (isOpen_univ.prod isOpen_Ioi).measurableSet] with p hdW hp
  have hgerm := forwardValue_eventuallyEq L h hp.2
  have hd := hdW.congr_of_eventuallyEq hgerm.symm
  have hr := residual_eq_zero_of_differentiableAt hcont hL hconv hh.continuous hlower hp.2 hd
  have hspace := hd.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hspaceEq : deriv (value L h p.2) p.1 =
      fderiv ℝ (fun q : ℝ × ℝ ↦ value L h q.2 q.1) p (1, 0) := by
    simpa only [Function.comp_def, id_eq] using hspace.deriv
  rw [hgerm.fderiv_eq]
  simpa only [gradient_eq_deriv', hspaceEq] using hr

end HamiltonJacobi.HopfLax
