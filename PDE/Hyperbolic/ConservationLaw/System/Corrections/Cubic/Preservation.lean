/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Cubic.Localization
public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Cubic.Realization

/-!
# Localized cubic corrections preserving every characteristic family

The correction scale can meet a fixed positive cap while preserving strict
hyperbolicity and genuine nonlinearity of every canonical family globally.
The compact neutral jet theorem supplies a common Jacobian and Hessian tolerance
on `tsupport A`, with neutral Hessian zero. Off the correction's topological
support the original and corrected flux agree on a neighborhood.

Compactness of the amplitude support supplies the characteristic tolerance.
Compact support of both `m` and `A` supplies the uniform derivative bounds used
by the state constructor.

The characteristic argument is carried out once for the zero-preserving
construction, and the statements here follow from it by projection.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Choose a cubic correction below a fixed positive scale cap, with support
inside `tsupport A ∩ {x | |m x| ≤ 2 * ε}`. The correction is uniformly small
through order two and has zero jets on `m = 0`, while the corrected flux remains
strictly hyperbolic with every canonical family genuinely nonlinear everywhere.

The coordinate, amplitude, and cap are fixed before choosing the scale. The
characteristic tolerance is obtained on the fixed compact set `tsupport A`. -/
theorem exists_localized_small_cubic_correction_preserving_characteristic_families {d : ℕ}
    {f : ℝ^d → ℝ^d} {m : ℝ^d → ℝ} {A : ℝ^d → ℝ^d} (hf : ContDiff ℝ ∞ f)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt f x) (hgn : ∀ i, IsGenuinelyNonlinearFamily f i)
    (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m) (hA : ContDiff ℝ ∞ A)
    (hAc : HasCompactSupport A) (εcap : ℝ) (hcap : 0 < εcap) {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (P : ℝ^d → ℝ^d),
      0 < ε ∧ ε < εcap ∧ ε ≤ 1 ∧ ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ tsupport A ∩ {x | |m x| ≤ 2 * ε} ∧
      (∀ x, |m x| ≤ ε → P x = (m x) ^ 3 • A x) ∧
      (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
      (∀ x, m x = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0) ∧
      (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
      ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  obtain ⟨ε, P, hε, hεcap, hεone, hP, hPc, hsupport, hexact, _, hsmall, hzero, hhyperP, hgnP⟩ :=
    exists_localized_small_cubic_correction_preserving_zeros_and_families
      hf hhyper hgn hm hmc hA hAc εcap hcap hη
  exact ⟨ε, P, hε, hεcap, hεone, hP, hPc, hsupport, hexact, hsmall, hzero, hhyperP, hgnP⟩

/-- A small cubic correction preserves every characteristic family globally.
This follows from the localized constructor with cap `1`. -/
theorem exists_small_cubic_correction_preserving_characteristic_families {d : ℕ} {f : ℝ^d → ℝ^d}
    {m : ℝ^d → ℝ} {A : ℝ^d → ℝ^d} (hf : ContDiff ℝ ∞ f) (hhyper : ∀ x, IsStrictlyHyperbolicAt f x)
    (hgn : ∀ i, IsGenuinelyNonlinearFamily f i) (hm : ContDiff ℝ ∞ m) (hmc : HasCompactSupport m)
    (hA : ContDiff ℝ ∞ A) (hAc : HasCompactSupport A) {η : ℝ} (hη : 0 < η) :
    ∃ (ε : ℝ) (P : ℝ^d → ℝ^d),
      0 < ε ∧ ε ≤ 1 ∧ ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ tsupport A ∧
      (∀ x, |m x| ≤ ε → P x = (m x) ^ 3 • A x) ∧
      (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
      (∀ x, m x = 0 → ∀ n ≤ 2, iteratedFDeriv ℝ n P x = 0) ∧
      (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
      ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  obtain ⟨ε, P, hε, _, hεone, hP, hPc, hsupport, hexact, hsmall, hzero, hgood⟩ :=
    exists_localized_small_cubic_correction_preserving_characteristic_families
      hf hhyper hgn hm hmc hA hAc 1 zero_lt_one hη
  exact ⟨ε, P, hε, hεone, hP, hPc, fun _ hx ↦ (hsupport hx).1, hexact, hsmall, hzero, hgood⟩

end PDE.Hyperbolic.ConservationLaw.System
