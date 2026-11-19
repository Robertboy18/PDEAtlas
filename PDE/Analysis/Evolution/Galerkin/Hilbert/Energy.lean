/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Restriction
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Core.Uniqueness

/-!
# Hilbert-mass Galerkin energy and uniqueness

Galerkin equations `⟪u', v⟫_V + B(u, v) = ℓ(t)(v)` for all `v ∈ S` on a trial subspace `S`
of an inner-product space `V`, with the inner product of `V` as mass form. Restriction to `S`
preserves coercivity and the forcing bound, so if `C ‖w‖² ≤ B(w, w)` and `‖ℓ(t)‖ ≤ M`, then
`½ ‖u(t)‖² ≤ ½ ‖u(a)‖² + M² (t - a) / (2C)`. If `B` is nonnegative, two solutions with the
same initial value agree on `[a, b]`.
-/

@[expose] public section

noncomputable section


open Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
/-- Energy estimate for the Galerkin system with mass form the inner product of `V`: if
`C ‖w‖² ≤ B(w, w)` and `‖ℓ(t)‖ ≤ M`, then `½ ‖u(t)‖² ≤ ½ ‖u(a)‖² + M² (t - a) / (2C)`. The
pivot-mass version is `gelfandGalerkin_energy_bound`. -/
theorem hilbertGalerkin_energy_bound
    (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → S)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (du t) t)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b,
      SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S (ell t))
        (u t) (du t)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖u a‖ ^ 2 + (M ^ 2 / (2 * C)) * (t - a) := by
  exact weakEvolution_energy_bound (fun _ ↦ restrictForm S B) hab
    (fun t ↦ restrictFunctional S (ell t)) u du hC hM
      (fun t ht ↦ (hu t ht).hasDerivWithinAt)
    (fun t _ ↦ restrictForm_coercive S B hcoercive (u t))
    (fun t ht ↦ (norm_restrictFunctional_le S (ell t)).trans (hell t ht)) heq

/-- If `B(w, w) ≥ 0` for all `w`, two solutions of the same Galerkin system on `S` with the
same initial value agree on `[a, b]`. -/
theorem hilbertGalerkin_unique
    (S : Submodule ℝ V) (B : V →L[ℝ] StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b) (ell : ℝ → StrongDual ℝ V)
    (u v du dv : ℝ → S)
    (hu : ∀ t ∈ Set.Icc a b, HasDerivAt u (du t) t)
    (hv : ∀ t ∈ Set.Icc a b, HasDerivAt v (dv t) t)
    (hB : ∀ w : V, 0 ≤ B w w)
    (heu : ∀ t ∈ Set.Icc a b,
      SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S (ell t))
        (u t) (du t))
    (hev : ∀ t ∈ Set.Icc a b,
      SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S (ell t))
        (v t) (dv t))
    (hinit : u a = v a) :
    ∀ t ∈ Set.Icc a b, u t = v t := by
  exact weakEvolution_unique (fun _ ↦ restrictForm S B) hab
    (fun t ↦ restrictFunctional S (ell t)) u v du dv
    (fun t ht ↦ (hu t ht).hasDerivWithinAt)
    (fun t ht ↦ (hv t ht).hasDerivWithinAt)
    (fun _ _ ↦ restrictForm_nonnegative S B hB) heu hev hinit

end Galerkin

end PDE.Analysis.Evolution
