/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.FieldSpace

/-!
# Noether currents for translations

Spatial translations act on fields by `U t y = u (y - t • a)`. Field translations
act by `U t y = u y + t • b`. In both cases the transformed gradient is computed
from the Jacobian. Invariance of `L` under small finite translations then
implies conservation; no infinitesimal invariance identity is assumed.

All regularity hypotheses concern germs at the evaluation point and its first jet.
For a coordinate direction the spatial current is, up to sign, the current of
Evans, §8.6.2, Example 1, equation (9).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.2, Example 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ}

variable {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {u : ℝ^n → ℝ^m} {x : ℝ^n}

/-- Invariance of the Lagrangian under small translations in direction `a` gives
the spatial translation current `L a - (D_P L)ᵀ Du a`.
The invariance assumption is a finite equality of `L`, local in the translation
parameter at the evaluation point, for arbitrary gradient and field values. -/
theorem noether_spatial_translation
    (hL : ContDiffAt ℝ 2
      (fun q : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L q.1 q.2.1 q.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x) (a : ℝ^n)
    (hinvariant : ∀ P z, (fun t : ℝ ↦ L P z (x + t • a)) =ᶠ[𝓝 0]
      (fun _ ↦ L P z x))
    (hEL : ∀ k, classicalEulerLagrange L u x k = 0) :
    ∇· (noetherCurrent L u (fun y ↦ -fderiv ℝ u y a) (fun _ ↦ a)) x = 0 := by
  let U := fun (t : ℝ) (y : ℝ^n) ↦ u (y - t • a)
  let Φ := fun (t : ℝ) (y : ℝ^n) ↦ y + t • a
  have hU₀ : U 0 = u := by funext y; simp [U]
  have hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x) := by
    exact (show ContDiffAt ℝ 2 u (x - (0 : ℝ) • a) by simpa using hu).comp (0, x)
      (contDiffAt_snd.sub (contDiffAt_fst.smul contDiffAt_const))
  have hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x) :=
    contDiffAt_snd.add (contDiffAt_fst.smul contDiffAt_const)
  have hΦ₀ : Φ 0 =ᶠ[𝓝 x] id := by
    filter_upwards [] with y
    simp [Φ]
  have hgenerator (y : ℝ^n) : deriv (fun t ↦ Φ t y) 0 = a := by
    have hd := ((hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const a)).deriv
    change deriv (fun t : ℝ ↦ Φ t y) 0 = (0 : ℝ^n) + (1 : ℝ) • a at hd
    simpa only [zero_add, one_smul] using hd
  have hgraph : ∀ᶠ y in 𝓝 x, (fun t ↦ U t (Φ t y)) =ᶠ[𝓝 0]
      (fun _ ↦ U 0 y) := by
    filter_upwards [] with y
    filter_upwards [] with t
    simp [U, Φ]
  have hdensity : (fun t ↦
      L (jacobianMatrix (U t) (Φ t x)) (U 0 x) (Φ t x) *
        (jacobianMatrix (Φ t) x).det) =ᶠ[𝓝 0]
      (fun _ ↦ fieldDensity L (U 0) x) := by
    filter_upwards [hinvariant (jacobianMatrix u x) (u x)] with t ht
    simpa only [U, Φ, zero_smul, sub_zero, jacobianMatrix_comp_sub, add_sub_cancel_right,
      jacobianMatrix_add_const, jacobianMatrix_id, Matrix.det_one, mul_one,
      fieldDensity] using ht
  have h := noether_field_space (Ψ := fun _ _ z ↦ z)
    (by simpa only [hU₀] using hL) hU hΦ hΦ₀
    (Filter.Eventually.of_forall fun _ ↦ differentiableAt_const _)
    hgraph hdensity (by simpa only [hU₀] using hEL)
  simpa only [hU₀, deriv_const, hgenerator, zero_sub] using h

/-- Invariance of `L` under small field translations in direction `b` conserves
the momentum contracted with `b`. The field and density need only be `C²` locally. -/
theorem noether_field_translation
    (hL : ContDiffAt ℝ 2
      (fun q : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L q.1 q.2.1 q.2.2)
      (jacobianMatrix u x, (u x, x)))
    (hu : ContDiffAt ℝ 2 u x) (b : ℝ^m)
    (hinvariant : ∀ P z, (fun t : ℝ ↦ L P (z + t • b) x) =ᶠ[𝓝 0]
      (fun _ ↦ L P z x))
    (hEL : ∀ k, classicalEulerLagrange L u x k = 0) :
    ∇· (fun y ↦ WithLp.toLp 2 (fun i ↦ ∑ k, momentum L u k i y * b k)) x = 0 := by
  let U := fun (t : ℝ) (y : ℝ^n) ↦ u y + t • b
  have hU₀ : U 0 = u := by funext y; simp [U]
  have hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x) :=
    (hu.comp (0, x) contDiffAt_snd).add (contDiffAt_fst.smul contDiffAt_const)
  have hgenerator (y : ℝ^n) : deriv (fun t ↦ U t y) 0 = b := by
    have hd := ((hasDerivAt_const (0 : ℝ) (u y)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const b)).deriv
    change deriv (fun t : ℝ ↦ U t y) 0 = (0 : ℝ^m) + (1 : ℝ) • b at hd
    simpa only [zero_add, one_smul] using hd
  have hdensity : (fun t ↦ transformedDensity L U (fun _ y ↦ y) t x) =ᶠ[𝓝 0]
      (fun _ ↦ fieldDensity L (U 0) x) := by
    filter_upwards [hinvariant (jacobianMatrix u x) (u x)] with t ht
    simpa only [transformedDensity, fieldDensity, U, zero_smul, add_zero,
      jacobianMatrix_add_const, jacobianMatrix_id, Matrix.det_one, mul_one] using ht
  have h := noether_of_invariant_variation (Φ := fun _ y ↦ y)
    (by simpa only [hU₀] using hL) hU contDiffAt_snd (Filter.EventuallyEq.rfl)
    hdensity (by simpa only [hU₀] using hEL)
  simp only [hU₀, hgenerator, deriv_const] at h
  change ∇· (noetherCurrent L u (fun _ ↦ b) (fun _ ↦ 0)) x = 0 at h
  unfold noetherCurrent at h
  simpa only [smul_zero, add_zero] using h

end PDE.CalculusOfVariations.Noether
