/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.Gradient.Basic
import PDE.Hyperbolic.Models.Transport
import CAS.ExactTactic

/-!
# Analytic transport solutions

Analytic initial data translated along a constant velocity gives jointly analytic solutions
of the transport equation. The initial trace and the transport residual are proved for the
explicit translated profile.

In one space dimension, `u_t - c u_x = 0` with an analytic datum on `{t = 0}` is covered by the
Cauchy–Kovalevskaya theorem of Evans, §4.6.3, Theorem 2, after the reduction (14)-(15) with
`x_n = t`. Here the solution is explicit and global, not only a power series near the origin.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, equations (14)-(15) and Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (spatialGradient)

namespace TransportEquation

open PDE.Common

/-- The one-dimensional translated profile used in the transport model
`u_t - c u_x = 0`, `u(0,x)=g(x)`. -/
noncomputable def translatedTransportProfile (c : ℝ) (g : ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t x ↦ g (x + c * t)

/-- The residual of the one-dimensional transport model `u_t - c u_x = 0`. -/
noncomputable def transportResidual1D (c : ℝ) (u : ℝ → ℝ → ℝ) (t x : ℝ) : ℝ :=
  deriv (fun s : ℝ ↦ u s x) t - c * deriv (fun y : ℝ ↦ u t y) x

/-- The one-dimensional transport Cauchy problem
`u_t - c u_x = 0`, `u(0,x)=g(x)`, with differentiable time and space slices.

Both slice differentiability hypotheses are stated, so the residual uses the slice derivatives.
The predicate does not require joint `C¹` regularity. -/
def SolvesTransportIVP1D (c : ℝ) (g : ℝ → ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  (∀ t x,
      DifferentiableAt ℝ (fun s ↦ u s x) t ∧
        DifferentiableAt ℝ (fun y ↦ u t y) x) ∧
    (∀ x, u 0 x = g x) ∧
      ∀ t x, transportResidual1D c u t x = 0

/-- The translated profile has the prescribed initial trace. -/
theorem translatedTransportProfile_initial (c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    translatedTransportProfile c g 0 x = g x := by
  simp [translatedTransportProfile]

/-- Analytic initial data gives an analytic translated one-dimensional transport profile. -/
theorem analytic_translatedTransportProfile
    (c : ℝ) (g : ℝ → ℝ) (hg : ∀ y, AnalyticAt ℝ g y) (p : ℝ × ℝ) :
    AnalyticAt ℝ (fun q : ℝ × ℝ ↦ translatedTransportProfile c g q.1 q.2) p := by
  have hg' : AnalyticAt ℝ g (p.2 + c * p.1) := hg (p.2 + c * p.1)
  have hfst : AnalyticAt ℝ (fun q : ℝ × ℝ ↦ q.1) p := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun q : ℝ × ℝ ↦ q.2) p := analyticAt_snd
  have hmul : AnalyticAt ℝ (fun q : ℝ × ℝ ↦ c * q.1) p := by
    rw [show (fun q : ℝ × ℝ ↦ c * q.1) =
      (fun _ : ℝ × ℝ ↦ c) * fun q ↦ q.1 by rfl]
    exact (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ × ℝ ↦ c) p).mul hfst
  have hmap : AnalyticAt ℝ (fun q : ℝ × ℝ ↦ q.2 + c * q.1) p := hsnd.add hmul
  simpa [translatedTransportProfile, Function.comp_def, add_comm, mul_comm] using (AnalyticAt.comp
      (g := g) (f := fun q : ℝ × ℝ ↦ q.2 + c * q.1) (x := p) hg' hmap)

/-- Translation along a constant vector preserves analyticity of the initial profile. -/
theorem analyticAt_translation {n : ℕ}
    (v : ℝ^n) (g : ℝ^n → ℝ) (hg : ∀ x, AnalyticAt ℝ g x) (p : ℝ × ℝ^n) :
    AnalyticAt ℝ (fun q : ℝ × ℝ^n ↦ g (q.2 + q.1 • v)) p := by
  have hg' : AnalyticAt ℝ g (p.2 + p.1 • v) := hg (p.2 + p.1 • v)
  have hfst : AnalyticAt ℝ (fun q : ℝ × ℝ^n ↦ q.1) p := analyticAt_fst
  have hsnd : AnalyticAt ℝ (fun q : ℝ × ℝ^n ↦ q.2) p := analyticAt_snd
  have hsmul : AnalyticAt ℝ (fun q : ℝ × ℝ^n ↦ q.1 • v) p := by
    rw [show (fun q : ℝ × ℝ^n ↦ q.1 • v) = (fun q : ℝ × ℝ^n ↦ q.1) •
        (fun _ : ℝ × ℝ^n ↦ v) by rfl]
    exact hfst.smul (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ × ℝ^n ↦ v) p)
  have hmap : AnalyticAt ℝ (fun q : ℝ × ℝ^n ↦ q.2 + q.1 • v) p := hsnd.add hsmul
  rw [show (fun q : ℝ × ℝ^n ↦ g (q.2 + q.1 • v)) =
    g ∘ fun q ↦ q.2 + q.1 • v by rfl]
  exact AnalyticAt.comp hg' hmap

/-- A differentiable profile translated along `v` satisfies `u_t - v · ∇u = 0`. -/
theorem translation_transport_residual_eq_zero {n : ℕ} (v : ℝ^n) (g : ℝ^n → ℝ)
    (hg : ∀ x, DifferentiableAt ℝ g x) (xt : ℝ^(n + 1)) :
    (∂[0] (fun q ↦ g (spatialPartCLM n q + q 0 • v))) xt -
        ∑ i, spatialGradient (fun q ↦ g (spatialPartCLM n q + q 0 • v)) xt i * v i = 0 := by
  classical
  let b : ℝ^n := -v
  have htransport :=
    TransportEquation.transportOperator_transportFunction_eq_zero (n := n) b g hg xt
  have hfun : TransportEquation.transportFunction (n := n) b g =
        fun q ↦ g (spatialPartCLM n q + q 0 • v) := by
    funext q
    apply congrArg g
    ext i
    simp [TransportEquation.transportInner_apply, b, spatialPartCLM_apply,
      sub_eq_add_neg, smul_eq_mul]
  rw [hfun] at htransport
  rw [TransportEquation.transportOperator_eq_timeDeriv_add_dot_spatialGradient] at htransport
  have hsum : (∑ i, b i * spatialGradient (fun q ↦ g (spatialPartCLM n q + q 0 • v)) xt i) =
        -(∑ i, spatialGradient
            (fun q ↦ g (spatialPartCLM n q + q 0 • v)) xt i * v i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    simp [b, mul_comm]
  rw [hsum] at htransport
  simpa [sub_eq_add_neg] using htransport

/-- For initial data differentiable at every point, the translated profile
`u(t,x)=g(x+c t)` has residual `u_t - c u_x = 0` at every `(t,x)`.

This calculation needs only differentiability; analyticity is used separately to prove that the
translated profile is jointly analytic. -/
theorem translatedTransportProfile_residual_eq_zero
    (c : ℝ) (g : ℝ → ℝ) (hg : ∀ y, DifferentiableAt ℝ g y) (t x : ℝ) :
    transportResidual1D c (translatedTransportProfile c g) t x = 0 := by
  change deriv (fun s : ℝ ↦ g (x + c * s)) t - c * deriv (fun y : ℝ ↦ g (y + c * t)) x = 0
  have hinner_t : deriv (fun s : ℝ ↦ x + c * s) t = c := by
    cas
  have htime :
      deriv (fun s : ℝ ↦ g (x + c * s)) t = deriv g (x + c * t) * c := by
    have hinner_diff : DifferentiableAt ℝ (fun s : ℝ ↦ x + c * s) t := by
      cas
    simpa [hinner_t, Function.comp_def] using (deriv_comp t (hg (x + c * t)) hinner_diff)
  have hinner_x : deriv (fun y : ℝ ↦ y + c * t) x = 1 := by
    cas
  have hspace :
      deriv (fun y : ℝ ↦ g (y + c * t)) x = deriv g (x + c * t) := by
    have hinner_diff : DifferentiableAt ℝ (fun y : ℝ ↦ y + c * t) x := by
      cas
    simpa [hinner_x, Function.comp_def] using (deriv_comp x (hg (x + c * t)) hinner_diff)
  rw [htime, hspace]
  ring

/-- Differentiable initial data transported by a constant velocity solves
`u_t - c u_x = 0` and has the prescribed initial trace. -/
theorem translatedTransportProfile_solves_transportIVP
    (c : ℝ) (g : ℝ → ℝ) (hg : ∀ y, DifferentiableAt ℝ g y) :
    SolvesTransportIVP1D c g (translatedTransportProfile c g) := by
  refine ⟨?_, translatedTransportProfile_initial c g,
    translatedTransportProfile_residual_eq_zero c g hg⟩
  intro t x
  constructor
  · change DifferentiableAt ℝ (fun s ↦ g (x + c * s)) t
    exact (hg (x + c * t)).comp t (by fun_prop)
  · change DifferentiableAt ℝ (fun y ↦ g (y + c * t)) x
    exact (hg (x + c * t)).comp x (by fun_prop)

/-- Analytic initial data gives an analytic solution of the transport Cauchy problem. -/
theorem analytic_translatedTransportProfile_solves_transportIVP
    (c : ℝ) (g : ℝ → ℝ) (hg : ∀ y, AnalyticAt ℝ g y) :
    (∀ p : ℝ × ℝ, AnalyticAt ℝ (fun q : ℝ × ℝ ↦ translatedTransportProfile c g q.1 q.2) p) ∧
      SolvesTransportIVP1D c g (translatedTransportProfile c g) := by
  constructor
  · exact analytic_translatedTransportProfile c g hg
  · exact translatedTransportProfile_solves_transportIVP c g (fun y ↦ (hg y).differentiableAt)

end TransportEquation
