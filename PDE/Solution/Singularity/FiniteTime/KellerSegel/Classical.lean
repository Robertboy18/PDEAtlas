/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Classical parabolic–elliptic Keller–Segel solutions

We define pointwise classical solutions of the parabolic–elliptic Keller–Segel system on an
open time domain. The sign convention is

`uₜ = div (∇u - u∇Φ)` and `-ΔΦ = u`.

The time domain is part of the predicate so a pre-singular solution can be stated on `t < T`
without asserting regularity through the candidate singular time.

The structure `IsNonnegativePointwiseClassicalSolutionOn` records the domain, regularity, sign,
and equations, and is stable under restriction and pointwise equality. Profile equations,
residual identities, and blow-up conclusions are separate predicates and theorems.

The regularity is pointwise classical: the density is jointly `C¹`, the potential is jointly
continuous, and both have `C²` spatial slices. This is enough for the displayed equations but
does not assert time-continuity of their second spatial derivatives. Virial or continuation
arguments that need anisotropic `C^{2,1}` regularity have to assume it.

The equation `-ΔΦ = u` determines `Φ` only up to a harmonic function, and the predicate fixes
neither the Newtonian normalization of `Φ` nor its decay at infinity. The whole-space virial
law does not follow from the predicate; `PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial`
assumes the virial identity instead.

## Main declarations

* `densityResidual`, `potentialResidual`: the two residuals `div (∇u - u∇Φ) - uₜ` and
  `-ΔΦ - u`, as total functions.
* `IsNonnegativePointwiseClassicalSolutionOn`: the solution predicate on an open time set.
* `IsNonnegativePointwiseClassicalSolutionOn.mono`, `.congr`: restriction to a smaller open
  time domain and invariance under pointwise equality on the domain.
* `zero_is_nonnegative_pointwise_classical_solution_on`: the trivial solution, as a check
  that the predicate is satisfiable.

## References

* E. F. Keller and L. A. Segel, "Initiation of slime mold aggregation viewed as an
  instability", *J. Theoret. Biol.* 26 (1970), 399-415.
  <https://doi.org/10.1016/0022-5193(70)90092-5>
* B. Perthame, *Transport Equations in Biology*, Frontiers in Mathematics, Birkhäuser, 2007,
  chapter "Cell motion and chemotaxis", pp. 111-149.
  <https://doi.org/10.1007/978-3-7643-7842-4_5>
-/

open scoped Gradient

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.KellerSegel

variable {d : ℕ}

/-- The density-equation residual, oriented as
`div (∇u - u∇Φ) - uₜ`.

The function is total. Regularity and time-domain assumptions enter through the theorems that
identify its vanishing with the classical Keller–Segel equation. -/
noncomputable def densityResidual
    (u Φ : ℝ^d → ℝ → ℝ) (x : ℝ^d) (t : ℝ) : ℝ :=
  ∇·
      (fun y ↦ ∇ (fun z ↦ u z t) y -
        u y t • ∇ (fun z ↦ Φ z t) y) x -
    deriv (fun s ↦ u x s) t

/-- The elliptic potential residual `-ΔΦ - u` for two spatial fields. -/
noncomputable def potentialResidual
    (density potential : ℝ^d → ℝ) (x : ℝ^d) : ℝ :=
  -laplacian potential x - density x

/-- Vanishing of the density residual is exactly the conservative density equation. -/
theorem density_residual_eq_zero_iff
    (u Φ : ℝ^d → ℝ → ℝ) (x : ℝ^d) (t : ℝ) :
    densityResidual u Φ x t = 0 ↔
      deriv (fun s ↦ u x s) t =
        ∇·
          (fun y ↦ ∇ (fun z ↦ u z t) y -
            u y t • ∇ (fun z ↦ Φ z t) y) x := by
  simp only [densityResidual, sub_eq_zero]
  exact eq_comm

/-- Vanishing of the potential residual is exactly the elliptic Keller–Segel equation. -/
theorem potential_residual_eq_zero_iff
    (density potential : ℝ^d → ℝ) (x : ℝ^d) :
    potentialResidual density potential x = 0 ↔
      -laplacian potential x = density x := by
  change -laplacian potential x - density x = 0 ↔
    -laplacian potential x = density x
  exact sub_eq_zero

/-- A nonnegative pointwise classical solution of the parabolic–elliptic Keller–Segel system on
an open time domain.

Joint spacetime `C¹` regularity of the density supplies its time derivative. The elliptic
potential needs only joint continuity in spacetime and `C²` spatial slices, since no time
derivative of the potential appears in the equations. None of this gives joint `C^{2,1}`
regularity. -/
structure IsNonnegativePointwiseClassicalSolutionOn
    (I : Set ℝ) (u Φ : ℝ^d → ℝ → ℝ) : Prop where
  /-- The time domain is open. -/
  time_domain_open : IsOpen I
  /-- Joint spacetime `C¹` regularity of the density on `ℝ^d × I`. -/
  density_spacetime_contDiffOn :
    ContDiffOn ℝ 1 (fun xt : ℝ^d × ℝ ↦ u xt.1 xt.2) (Set.univ ×ˢ I)
  /-- Joint spacetime continuity of the elliptic potential on `ℝ^d × I`. -/
  potential_spacetime_continuousOn :
    ContinuousOn (fun xt : ℝ^d × ℝ ↦ Φ xt.1 xt.2) (Set.univ ×ˢ I)
  /-- Spatial `C²` regularity of the density on each time slice. -/
  density_spatial_slice_contDiff :
    ∀ (t : ℝ), t ∈ I → ContDiff ℝ 2 (fun x ↦ u x t)
  /-- Spatial `C²` regularity of the potential on each time slice. -/
  potential_spatial_slice_contDiff :
    ∀ (t : ℝ), t ∈ I → ContDiff ℝ 2 (fun x ↦ Φ x t)
  /-- The cell density is nonnegative. -/
  density_nonnegative : ∀ (x : ℝ^d) (t : ℝ), t ∈ I → 0 ≤ u x t
  /-- The density equation in conservative form. -/
  density_equation : ∀ (x : ℝ^d) (t : ℝ), t ∈ I →
    deriv (fun s ↦ u x s) t =
      ∇·
        (fun y ↦ ∇ (fun z ↦ u z t) y -
          (u y t) • ∇ (fun z ↦ Φ z t) y) x
  /-- The elliptic equation for the chemoattractant potential. -/
  potential_equation : ∀ (x : ℝ^d) (t : ℝ), t ∈ I →
    -laplacian (fun y ↦ Φ y t) x = u x t

/-- Restrict a pointwise classical Keller–Segel solution to an open subset of its time domain. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.mono
    {I J : Set ℝ} {u Φ : ℝ^d → ℝ → ℝ}
    (h : IsNonnegativePointwiseClassicalSolutionOn (d := d) I u Φ)
    (hJ : IsOpen J) (hJI : J ⊆ I) :
    IsNonnegativePointwiseClassicalSolutionOn (d := d) J u Φ where
  time_domain_open := hJ
  density_spacetime_contDiffOn := h.density_spacetime_contDiffOn.mono fun _ hxt ↦
    ⟨hxt.1, hJI hxt.2⟩
  potential_spacetime_continuousOn := h.potential_spacetime_continuousOn.mono fun _ hxt ↦
    ⟨hxt.1, hJI hxt.2⟩
  density_spatial_slice_contDiff := fun t ht ↦
    h.density_spatial_slice_contDiff t (hJI ht)
  potential_spatial_slice_contDiff := fun t ht ↦
    h.potential_spatial_slice_contDiff t (hJI ht)
  density_nonnegative := fun x t ht ↦
    h.density_nonnegative x t (hJI ht)
  density_equation := fun x t ht ↦
    h.density_equation x t (hJI ht)
  potential_equation := fun x t ht ↦
    h.potential_equation x t (hJI ht)

/-- Time differentiability of the density follows from its joint `C¹` regularity on the open
spacetime cylinder. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.density_time_differentiable
    {I : Set ℝ} {u Φ : ℝ^d → ℝ → ℝ}
    (h : IsNonnegativePointwiseClassicalSolutionOn (d := d) I u Φ)
    (x : ℝ^d) {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (fun s ↦ u x s) t := by
  simpa using
    differentiableAt_time_slice_of_contDiffOn
      h.time_domain_open
      (fun xt : ℝ^d × ℝ ↦ u xt.1 xt.2)
      h.density_spacetime_contDiffOn x ht

/-- The density residual of a pointwise classical solution vanishes on its spacetime domain. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.density_residual_eq_zero
    {I : Set ℝ} {u Φ : ℝ^d → ℝ → ℝ}
    (h : IsNonnegativePointwiseClassicalSolutionOn (d := d) I u Φ)
    (x : ℝ^d) (t : ℝ) (ht : t ∈ I) :
    densityResidual u Φ x t = 0 :=
  (density_residual_eq_zero_iff u Φ x t).2 (h.density_equation x t ht)

/-- The potential residual of every pointwise classical time slice vanishes on the time domain. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.potential_residual_eq_zero
    {I : Set ℝ} {u Φ : ℝ^d → ℝ → ℝ}
    (h : IsNonnegativePointwiseClassicalSolutionOn (d := d) I u Φ)
    (x : ℝ^d) (t : ℝ) (ht : t ∈ I) :
    potentialResidual (fun y ↦ u y t) (fun y ↦ Φ y t) x = 0 :=
  (potential_residual_eq_zero_iff
    (fun y ↦ u y t) (fun y ↦ Φ y t) x).2 (h.potential_equation x t ht)

/-- Pointwise equal density and potential fields represent the same pointwise classical solution.

Equality is required only on the open time domain. Openness turns density equality into
equality near each admitted time, which is enough to identify the time derivatives. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.congr
    {I : Set ℝ} {u Φ v Ψ : ℝ^d → ℝ → ℝ}
    (h : IsNonnegativePointwiseClassicalSolutionOn (d := d) I u Φ)
    (huv : ∀ (x : ℝ^d) (t : ℝ), t ∈ I → u x t = v x t)
    (hΦΨ : ∀ (x : ℝ^d) (t : ℝ), t ∈ I → Φ x t = Ψ x t) :
    IsNonnegativePointwiseClassicalSolutionOn (d := d) I v Ψ where
  time_domain_open := h.time_domain_open
  density_spacetime_contDiffOn := by
    apply h.density_spacetime_contDiffOn.congr
    intro xt hxt
    exact (huv xt.1 xt.2 hxt.2).symm
  potential_spacetime_continuousOn := by
    apply h.potential_spacetime_continuousOn.congr
    intro xt hxt
    exact (hΦΨ xt.1 xt.2 hxt.2).symm
  density_spatial_slice_contDiff := by
    intro t ht
    rw [show (fun x ↦ v x t) = fun x ↦ u x t by
      funext x
      exact (huv x t ht).symm]
    exact h.density_spatial_slice_contDiff t ht
  potential_spatial_slice_contDiff := by
    intro t ht
    rw [show (fun x ↦ Ψ x t) = fun x ↦ Φ x t by
      funext x
      exact (hΦΨ x t ht).symm]
    exact h.potential_spatial_slice_contDiff t ht
  density_nonnegative := by
    intro x t ht
    rw [← huv x t ht]
    exact h.density_nonnegative x t ht
  density_equation := by
    intro x t ht
    have htime : (fun s ↦ v x s) =ᶠ[nhds t] fun s ↦ u x s := by
      filter_upwards [h.time_domain_open.mem_nhds ht] with s hs
      exact (huv x s hs).symm
    have hdensity : (fun y ↦ v y t) = fun y ↦ u y t :=
      funext fun y ↦ (huv y t ht).symm
    have hpotential : (fun y ↦ Ψ y t) = fun y ↦ Φ y t :=
      funext fun y ↦ (hΦΨ y t ht).symm
    have hflux :
        (fun y ↦ ∇ (fun z ↦ v z t) y -
          v y t • ∇ (fun z ↦ Ψ z t) y) =
          fun y ↦ ∇ (fun z ↦ u z t) y -
            u y t • ∇ (fun z ↦ Φ z t) y := by
      funext y
      rw [hdensity, hpotential, ← huv y t ht]
    rw [htime.deriv_eq, hflux]
    exact h.density_equation x t ht
  potential_equation := by
    intro x t ht
    rw [show (fun y ↦ Ψ y t) = fun y ↦ Φ y t by
      funext y
      exact (hΦΨ y t ht).symm]
    rw [← huv x t ht]
    exact h.potential_equation x t ht

/-- The zero density and zero potential solve the Keller–Segel system on every open time domain.

So the solution predicate is inhabited; this solution does not blow up. -/
theorem zero_is_nonnegative_pointwise_classical_solution_on
    (I : Set ℝ) (hI : IsOpen I) :
    IsNonnegativePointwiseClassicalSolutionOn (d := d) I
      (fun _ : ℝ^d ↦ fun _ : ℝ ↦ (0 : ℝ))
      (fun _ : ℝ^d ↦ fun _ : ℝ ↦ (0 : ℝ)) where
  time_domain_open := hI
  density_spacetime_contDiffOn := by
    fun_prop
  potential_spacetime_continuousOn := by
    fun_prop
  density_spatial_slice_contDiff := by
    intro t ht
    fun_prop
  potential_spatial_slice_contDiff := by
    intro t ht
    fun_prop
  density_nonnegative := by
    intro x t ht
    rfl
  density_equation := by
    intro x t ht
    simp [divergence, gradient, partialDeriv_const]
  potential_equation := by
    intro x t ht
    simp [PDE.laplacian_const (n := d) 0 x]

end PDE.Solution.Singularity.FiniteTime.KellerSegel
