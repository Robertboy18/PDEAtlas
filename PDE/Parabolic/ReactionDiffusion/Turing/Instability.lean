/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.ReactionDiffusion.Turing.Homogeneous
public import PDE.Parabolic.ReactionDiffusion.Turing.Mode

/-!
# Diffusion-driven linear Turing instability from raw coefficients

For a real two-species reaction matrix `A = [[a,b],[c,d]]` and positive diagonal diffusion
`D = diag(d₁,d₂)`, assume

* `a + d < 0` and `ad - bc > 0`;
* `a d₂ + d d₁ > 0`;
* `(a d₂ + d d₁)² > 4 d₁ d₂ (ad - bc)`.

The homogeneous reaction ODE is asymptotically stable. Nevertheless, diffusion admits nonconstant
classical cosine solutions with arbitrarily small uniformly bounded initial data and unbounded
exponential growth at a spatial point (`turing_instability`). The frequency, positive growth rate,
and eigenvector are derived from these raw inequalities, and the solution satisfies the PDE
classically. The inequalities hold for the reaction matrix `[[1,-2],[2,-3]]` and the diffusion
`diag(1,16)` (`example_turing_instability`).

The modes live on the line and satisfy homogeneous Neumann conditions on a suitable interval
(`exists_unstable_neumann_interval`). On a prescribed bounded domain an unstable mode needs a
Laplacian eigenvalue in the unstable band (`PDE.Parabolic.ReactionDiffusion.Turing.Dirichlet`). For
a nonlinear reaction system whose Jacobian is `A`, this is instability of the linearization.

This is the Turing instability of Evans's §4.1.2, where the answer to the question whether a stable
equilibrium of the ODE (19) is stable for the reaction-diffusion system (20) is no. In his notation
`Df(0)` has entries `α, β, γ, δ` and the diffusion constants are `a₁, a₂`; the first condition is
(27), and the other two make his polynomial `p` of (29) negative at a positive squared wave number.
Evans works on a bounded smooth planar domain with Dirichlet conditions. The example has the signs
`α > 0`, `β < 0`, `γ > 0`, `δ < 0` of his activators and inhibitors, and the inhibitor diffuses
faster, `a₂ = 16 > a₁ = 1`.

## How it works

Evans studies the linearization (22) mode by mode: the coefficients of the eigenfunction expansion
(23) solve `s_j' = A_j s_j`, (24)-(25), and the characteristic polynomial of `A_j` is (28), with
constant term `p(λ_j)`. We follow the same route with one explicit mode. The conditions make the
mode determinant negative at `Coefficients.selectedFrequencySq` (`selected_mode_det_neg`), so the
characteristic quadratic has a positive root `rate` with an eigenvector whose first component is
nonzero (`exists_unstable_mode`). The cosine mode `α exp(rate t) cos(kx) v` with
`k² = selectedFrequencySq` is a classical solution (`cosineMode_isSolution`), and a small `α` makes
the initial data as small as required while the first component still grows at the origin
(`exists_small_growing_cosine_modes`). Stability of the reaction ODE
(`homogeneous_asymptoticallyStable`) comes from a quadratic Lyapunov energy rather than from the
eigenvalues of `Df(0)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.2 (Application: Turing instability), (19)-(30),
  pp. 172-174, and the interpretation of activators and inhibitors, p. 175.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ReactionDiffusion.Turing

open Filter Set
open scoped Topology

/-- A strong form of instability for the linear PDE on the line: arbitrarily
small uniformly bounded initial perturbations yield classical solutions whose
first component grows without bound at the origin. -/
def LinearlyUnstable (C : Coefficients) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ u v : ℝ^2 → ℝ, IsSolution C u v ∧
    (∀ x : ℝ, |u !₂[0, x]| + |v !₂[0, x]| ≤ ε) ∧
      Tendsto (fun t ↦ |u !₂[t, 0]|) atTop atTop

/-- The coefficient inequalities construct a positive frequency and growth
rate. At every requested initial size, a nonzero scalar multiple of the
constructed eigenvector gives a growing classical cosine solution. -/
theorem exists_small_growing_cosine_modes {C : Coefficients} (h : Conditions C) :
    ∃ frequency rate : ℝ, 0 < frequency ∧ 0 < rate ∧
      ∀ ε : ℝ, 0 < ε → ∃ first second : ℝ, first ≠ 0 ∧
        IsSolution C (cosineMode rate frequency first) (cosineMode rate frequency second) ∧
        (∀ x : ℝ, |cosineMode rate frequency first !₂[0, x]| +
          |cosineMode rate frequency second !₂[0, x]| ≤ ε) ∧
        Tendsto (fun t ↦ |cosineMode rate frequency first !₂[t, 0]|) atTop atTop := by
  obtain ⟨μ, rate, hμ, hrate, vector, hvector, hfirst⟩ := exists_unstable_mode h
  have hfrequency : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hsquare : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have heigen : Module.End.HasEigenvector
      (C.modeMatrix (Real.sqrt μ ^ 2)).toLin' rate vector := by
    simpa only [hsquare] using hvector
  refine ⟨Real.sqrt μ, rate, hfrequency, hrate, ?_⟩
  intro ε hε
  let scale := ε / (|vector 0| + |vector 1|)
  have hsum : 0 < |vector 0| + |vector 1| :=
    add_pos_of_pos_of_nonneg (abs_pos.mpr hfirst) (abs_nonneg _)
  have hscale : 0 < scale := div_pos hε hsum
  have hscaled_first : scale * vector 0 ≠ 0 := mul_ne_zero (ne_of_gt hscale) hfirst
  refine ⟨scale * vector 0, scale * vector 1, hscaled_first,
    cosineMode_isSolution C rate (Real.sqrt μ) scale heigen, ?_,
    cosineMode_abs_tendsto_atTop hrate hscaled_first _⟩
  intro x
  calc
    _ ≤ |scale * vector 0| + |scale * vector 1| :=
      add_le_add (cosineMode_initial_abs_le _ _ _ _) (cosineMode_initial_abs_le _ _ _ _)
    _ = scale * (|vector 0| + |vector 1|) := by
      rw [abs_mul, abs_mul, abs_of_pos hscale, mul_add]
    _ = ε := div_mul_cancel₀ _ (ne_of_gt hsum)

/-- Diffusion destabilizes a homogeneous reaction system which is itself
asymptotically stable. Both stability and PDE instability are proved from the
six raw coefficients; no positive eigenvalue or solution bridge is assumed. -/
theorem turing_instability {C : Coefficients} (h : Conditions C) :
    HomogeneousAsymptoticallyStable C ∧ LinearlyUnstable C := by
  refine ⟨homogeneous_asymptoticallyStable C h.trace_neg h.det_pos, ?_⟩
  obtain ⟨frequency, rate, _, _, hmodes⟩ := exists_small_growing_cosine_modes h
  intro ε hε
  obtain ⟨first, second, _, hsolution, hinitial, hgrowth⟩ := hmodes ε hε
  exact ⟨cosineMode rate frequency first, cosineMode rate frequency second,
    hsolution, hinitial, hgrowth⟩

/-- The same instability occurs on an explicitly sized Neumann interval.
The initial perturbation is spatially nonconstant, satisfies the uniform
smallness bound, and both species satisfy both boundary conditions at all times.
The interval is fixed independently of the initial perturbation size. -/
theorem exists_unstable_neumann_interval {C : Coefficients} (h : Conditions C) :
    ∃ length : ℝ, 0 < length ∧ ∀ ε : ℝ, 0 < ε →
      ∃ u v : ℝ^2 → ℝ, IsSolution C u v ∧
      (∀ x ∈ Icc (0 : ℝ) length, |u !₂[0, x]| + |v !₂[0, x]| ≤ ε) ∧
      (∀ t : ℝ,
        (∂[(1 : Fin 2)] u) !₂[t, 0] = 0 ∧ (∂[(1 : Fin 2)] u) !₂[t, length] = 0 ∧
        (∂[(1 : Fin 2)] v) !₂[t, 0] = 0 ∧ (∂[(1 : Fin 2)] v) !₂[t, length] = 0) ∧
      u !₂[0, 0] ≠ u !₂[0, length] ∧
      Tendsto (fun t ↦ |u !₂[t, 0]|) atTop atTop := by
  obtain ⟨frequency, rate, hfrequency, _, hmodes⟩ := exists_small_growing_cosine_modes h
  refine ⟨Real.pi / frequency, div_pos Real.pi_pos hfrequency, ?_⟩
  intro ε hε
  obtain ⟨first, second, hfirst, hsolution, hinitial, hgrowth⟩ := hmodes ε hε
  refine ⟨cosineMode rate frequency first, cosineMode rate frequency second,
    hsolution, fun x _ ↦ hinitial x, ?_,
    cosineMode_initial_nonconstant (ne_of_gt hfrequency) hfirst rate, hgrowth⟩
  intro t
  obtain ⟨hu₀, hu₁⟩ := cosineMode_neumann (ne_of_gt hfrequency) rate first t
  obtain ⟨hv₀, hv₁⟩ := cosineMode_neumann (ne_of_gt hfrequency) rate second t
  exact ⟨hu₀, hu₁, hv₀, hv₁⟩

/-- A concrete instance: reaction `[[1,-2],[2,-3]]`, diffusion `diag(1,16)`.
Its reaction trace is `-2`, determinant is `1`, and weighted trace is `13`. -/
def exampleCoefficients : Coefficients :=
  ⟨1, -2, 2, -3, 1, 16⟩

/-- The strict raw inequalities hold in the concrete example. -/
theorem example_conditions : Conditions exampleCoefficients := by
  constructor <;> norm_num [exampleCoefficients]

/-- A concrete stable reaction system destabilized by positive diffusion. -/
theorem example_turing_instability :
    HomogeneousAsymptoticallyStable exampleCoefficients ∧
      LinearlyUnstable exampleCoefficients :=
  turing_instability example_conditions

end ReactionDiffusion.Turing
