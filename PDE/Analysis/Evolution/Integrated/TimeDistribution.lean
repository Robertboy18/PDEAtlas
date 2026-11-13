/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.WeakEvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Time-distribution identities for weak evolution

Integration-by-parts formulas that transfer the derivative of a classical
Hilbert-valued trajectory to a scalar time test. The resulting identities are
the distributional link from pointwise weak evolution equations to the
integrated formulations used in compactness arguments.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2 (weak derivatives in time), and §7.1.2, proof of
  Theorem 3, (27). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Integration by parts for the time derivative of a Hilbert-valued
trajectory, paired with a fixed spatial test vector and a scalar test function
vanishing at both endpoints:

`∫ ⟪u'(t),v⟫ φ(t) dt = -∫ ⟪u(t),v⟫ φ'(t) dt`.

This is the distributional time-derivative identity used in the proof of Evans §7.1.2,
Theorem 3, to pass from Galerkin equations to the limiting weak parabolic equation. -/
theorem weak_time_integration_by_parts
    {a b : ℝ} {u du : ℝ → V} {φ dφ : ℝ → ℝ} (v : V)
    (hu : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt u (du t) (Set.uIcc a b) t)
    (hφ : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt φ (dφ t) (Set.uIcc a b) t)
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdφ : IntervalIntegrable dφ volume a b)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    (∫ t in a..b, inner ℝ (du t) v * φ t) =
      -(∫ t in a..b, inner ℝ (u t) v * dφ t) := by
  have hinner (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivWithinAt (fun s ↦ inner ℝ (u s) v) (inner ℝ (du t) v)
        (Set.uIcc a b) t := by
    simpa using (hu t ht).inner ℝ
      (hasDerivWithinAt_const t (Set.uIcc a b) v)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    hinner hφ hdu hdφ
  rw [hφa, hφb] at h
  simp only [mul_zero, sub_zero] at h
  linarith

/-- Integration by parts retaining the initial boundary term.  Only the final
value of the scalar test function is required to vanish:

`∫ ⟪u',v⟫ φ = -∫ ⟪u,v⟫ φ' - ⟪u(a),v⟫ φ(a)`.

This formulation carries the initial condition through weak `L²` limits
without requiring point evaluation of the limiting equivalence class. -/
theorem weak_time_integration_by_parts_initial
    {a b : ℝ} {u du : ℝ → V} {φ dφ : ℝ → ℝ} (v : V)
    (hu : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt u (du t) (Set.uIcc a b) t)
    (hφ : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt φ (dφ t) (Set.uIcc a b) t)
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdφ : IntervalIntegrable dφ volume a b)
    (hφb : φ b = 0) :
    (∫ t in a..b, inner ℝ (du t) v * φ t) =
      -(∫ t in a..b, inner ℝ (u t) v * dφ t) - inner ℝ (u a) v * φ a := by
  have hinner (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      HasDerivWithinAt (fun s ↦ inner ℝ (u s) v) (inner ℝ (du t) v)
        (Set.uIcc a b) t := by
    simpa using (hu t ht).inner ℝ
      (hasDerivWithinAt_const t (Set.uIcc a b) v)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    hinner hφ hdu hdφ
  rw [hφb] at h
  simp only [mul_zero, zero_sub] at h
  linarith

/-- Integrated distributional form of the weak evolution equation.  The
pointwise derivative term is transferred to the scalar time test function,
which is the formulation stable under weak Galerkin convergence. -/
private theorem weak_evolution_integrated_test_identity
    {a b : ℝ} (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) {u du : ℝ → V} {φ dφ : ℝ → ℝ} (v : V)
    (hu : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt u (du t) (Set.uIcc a b) t)
    (hφ : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt φ (dφ t) (Set.uIcc a b) t)
    (heq : ∀ t ∈ Set.uIcc a b,
      SatisfiesWeakEvolutionAt (B t) (ell t) (u t) (du t))
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdφ : IntervalIntegrable dφ volume a b)
    (hBφ : IntervalIntegrable (fun t ↦ B t (u t) v * φ t) volume a b)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    -(∫ t in a..b, inner ℝ (u t) v * dφ t) +
        ∫ t in a..b, B t (u t) v * φ t =
      ∫ t in a..b, ell t v * φ t := by
  have hparts := weak_time_integration_by_parts v hu hφ hdu hdφ hφa hφb
  have hφcont : ContinuousOn φ (Set.uIcc a b) :=
    HasDerivWithinAt.continuousOn hφ
  have hduφ : IntervalIntegrable (fun t ↦ inner ℝ (du t) v * φ t) volume a b :=
    hdu.mul_continuousOn hφcont
  calc
    -(∫ t in a..b, inner ℝ (u t) v * dφ t) +
          ∫ t in a..b, B t (u t) v * φ t =
        (∫ t in a..b, inner ℝ (du t) v * φ t) +
          ∫ t in a..b, B t (u t) v * φ t := by rw [hparts]
    _ = ∫ t in a..b,
          inner ℝ (du t) v * φ t + B t (u t) v * φ t := by
      rw [intervalIntegral.integral_add hduφ hBφ]
    _ = ∫ t in a..b, ell t v * φ t := by
      apply intervalIntegral.integral_congr
      intro t ht
      change inner ℝ (du t) v * φ t + B t (u t) v * φ t = ell t v * φ t
      rw [← add_mul, heq t ht v]

/-- Integrated weak evolution identity with the initial datum retained as a
boundary functional.  This is the form used to identify the initial trace of
the Galerkin limit. -/
private theorem weak_evolution_integrated_initial_identity
    {a b : ℝ} (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) {u du : ℝ → V} {φ dφ : ℝ → ℝ} (v : V)
    (hu : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt u (du t) (Set.uIcc a b) t)
    (hφ : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt φ (dφ t) (Set.uIcc a b) t)
    (heq : ∀ t ∈ Set.uIcc a b,
      SatisfiesWeakEvolutionAt (B t) (ell t) (u t) (du t))
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdφ : IntervalIntegrable dφ volume a b)
    (hBφ : IntervalIntegrable (fun t ↦ B t (u t) v * φ t) volume a b)
    (hφb : φ b = 0) :
    -(∫ t in a..b, inner ℝ (u t) v * dφ t) +
        ∫ t in a..b, B t (u t) v * φ t =
      (∫ t in a..b, ell t v * φ t) + inner ℝ (u a) v * φ a := by
  have hparts := weak_time_integration_by_parts_initial v hu hφ hdu hdφ hφb
  have hφcont : ContinuousOn φ (Set.uIcc a b) :=
    HasDerivWithinAt.continuousOn hφ
  have hduφ : IntervalIntegrable (fun t ↦ inner ℝ (du t) v * φ t) volume a b :=
    hdu.mul_continuousOn hφcont
  have heqint :
      (∫ t in a..b, inner ℝ (du t) v * φ t) +
          ∫ t in a..b, B t (u t) v * φ t =
        ∫ t in a..b, ell t v * φ t := by
    rw [← intervalIntegral.integral_add hduφ hBφ]
    apply intervalIntegral.integral_congr
    intro t ht
    change inner ℝ (du t) v * φ t + B t (u t) v * φ t = ell t v * φ t
    rw [← add_mul, heq t ht v]
  rw [hparts] at heqint
  calc
    -(∫ t in a..b, inner ℝ (u t) v * dφ t) +
          ∫ t in a..b, B t (u t) v * φ t =
        ((-(∫ t in a..b, inner ℝ (u t) v * dφ t) -
          inner ℝ (u a) v * φ a) +
          ∫ t in a..b, B t (u t) v * φ t) + inner ℝ (u a) v * φ a := by ring
    _ = (∫ t in a..b, ell t v * φ t) + inner ℝ (u a) v * φ a := by
      exact congrArg (fun x : ℝ ↦ x + inner ℝ (u a) v * φ a) heqint

namespace SatisfiesWeakEvolutionOn

/--
Integrate a weak evolution on an interval against a scalar test that vanishes
at both endpoints.
-/
theorem integrated_test_identity
    {a b : ℝ} {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V} {u du : ℝ → V} {φ dφ : ℝ → ℝ}
    (heq : SatisfiesWeakEvolutionOn B ell u du (Set.uIcc a b))
    (v : V)
    (hu : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt u (du t) (Set.uIcc a b) t)
    (hφ : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt φ (dφ t) (Set.uIcc a b) t)
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdφ : IntervalIntegrable dφ volume a b)
    (hBφ : IntervalIntegrable (fun t ↦ B t (u t) v * φ t) volume a b)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    -(∫ t in a..b, inner ℝ (u t) v * dφ t) +
        ∫ t in a..b, B t (u t) v * φ t =
      ∫ t in a..b, ell t v * φ t :=
  weak_evolution_integrated_test_identity B ell v hu hφ heq hdu hdφ hBφ hφa hφb

/--
Integrate a weak evolution on an interval while retaining its initial
boundary term.
-/
theorem integrated_initial_identity
    {a b : ℝ} {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    {ell : ℝ → StrongDual ℝ V} {u du : ℝ → V} {φ dφ : ℝ → ℝ}
    (heq : SatisfiesWeakEvolutionOn B ell u du (Set.uIcc a b))
    (v : V)
    (hu : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt u (du t) (Set.uIcc a b) t)
    (hφ : ∀ t ∈ Set.uIcc a b,
      HasDerivWithinAt φ (dφ t) (Set.uIcc a b) t)
    (hdu : IntervalIntegrable (fun t ↦ inner ℝ (du t) v) volume a b)
    (hdφ : IntervalIntegrable dφ volume a b)
    (hBφ : IntervalIntegrable (fun t ↦ B t (u t) v * φ t) volume a b)
    (hφb : φ b = 0) :
    -(∫ t in a..b, inner ℝ (u t) v * dφ t) +
        ∫ t in a..b, B t (u t) v * φ t =
      (∫ t in a..b, ell t v * φ t) + inner ℝ (u a) v * φ a :=
  weak_evolution_integrated_initial_identity B ell v hu hφ heq hdu hdφ hBφ hφb

end SatisfiesWeakEvolutionOn

end PDE.Analysis.Evolution
