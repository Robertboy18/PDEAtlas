/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Restriction
public import PDE.Analysis.Evolution.Hilbert.Riesz
import PDE.Analysis.Evolution.Galerkin.Hilbert.Energy

/-!
# Hilbert-mass Galerkin existence

Galerkin approximation of the linear weak evolution equation
`⟪u', v⟫ + B(u, v) = ℓ(t)(v)` on a complete subspace `S` of the Hilbert space
`V`, in the special case where the mass form is the inner product of `V`
itself (`H = V`).  Restricting `B` and `ℓ(t)` to `S` and representing by Riesz
turns the equation into the affine ODE `u' = Riesz(ℓ|_S) - A_S u` on `S`, so
global classical solutions exist by linear ODE theory whenever `ℓ` is
continuous; no radius or time-step restriction is needed. We construct these
solutions on `ℝ` and on closed intervals, state them with the interval-level
weak equation, and prove the coercive energy bound together with the `V`-norm
derivative bound `‖u'‖ ≤ M + ‖B‖ ‖u‖`.  These are the
approximate solutions of Evans's Galerkin construction for parabolic
equations, in the case where the mass form is the inner product of `V`.

## Main results

* `exists_hilbertGalerkin_global`, `exists_hilbertGalerkin_on_Icc`,
  `exists_hilbertGalerkinOn_Icc`: classical Galerkin trajectories on `ℝ` and
  on `[a, b]`, the last stated with `SatisfiesWeakEvolutionOn`.
* `exists_hilbertGalerkin_with_uniform_bounds`: the trajectory together with
  the coercive energy estimate and the derivative bound.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 1 (construction of approximate
  solutions). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open InnerProductSpace
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
/-- For continuous `ℓ`, the Galerkin system on a complete subspace `S` with mass form the
inner product of `V` has a classical solution on all of `ℝ` with `u(t₀) = u₀`. The restricted
system is affine linear, so no time-step restriction enters. -/
theorem exists_hilbertGalerkin_global
    (S : Submodule ℝ V) [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (hell : Continuous ell) (t₀ : ℝ) (u₀ : S) :
    ∃ u : ℝ → S, u t₀ = u₀ ∧ ∀ t : ℝ,
      HasDerivAt u
        (weakEvolutionVectorField (restrictForm S B)
          (fun s ↦ restrictFunctional S (ell s)) t (u t)) t ∧
      SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S (ell t))
        (u t)
        (weakEvolutionVectorField (restrictForm S B)
          (fun s ↦ restrictFunctional S (ell s)) t (u t)) := by
  exact exists_weakEvolution_global (restrictForm S B)
    (fun t ↦ restrictFunctional S (ell t))
    ((restrictFunctionalMap S).continuous.comp hell) t₀ u₀

/-- For `ℓ` continuous on `[a, b]` and `t₀ ∈ [a, b]`, the Galerkin system with mass form the
inner product of `V` has a classical solution on `[a, b]` with `u(t₀) = u₀`. -/
theorem exists_hilbertGalerkin_on_Icc
    (S : Submodule ℝ V) [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b) (hell : ContinuousOn ell (Set.Icc a b))
    (t₀ : Set.Icc a b) (u₀ : S) :
    ∃ u : ℝ → S, u t₀ = u₀ ∧ ∀ t ∈ Set.Icc a b,
      HasDerivAt u
        (weakEvolutionVectorField (restrictForm S B)
          (fun s ↦ restrictFunctional S (ell s)) t (u t)) t ∧
      SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S (ell t))
        (u t)
        (weakEvolutionVectorField (restrictForm S B)
          (fun s ↦ restrictFunctional S (ell s)) t (u t)) := by
  exact exists_weakEvolution_on_Icc (restrictForm S B)
    (fun t ↦ restrictFunctional S (ell t)) hab
    (continuousOn_restrictFunctional S hell) t₀ u₀

/--
`exists_hilbertGalerkin_on_Icc` with the restricted equation stated as
`SatisfiesWeakEvolutionOn` on `[a, b]`.
-/
theorem exists_hilbertGalerkinOn_Icc
    (S : Submodule ℝ V) [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b) (hell : ContinuousOn ell (Set.Icc a b))
    (t₀ : Set.Icc a b) (u₀ : S) :
    ∃ u du : ℝ → S,
      u t₀ = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        du t = weakEvolutionVectorField (restrictForm S B)
          (fun s ↦ restrictFunctional S (ell s)) t (u t)) ∧
      (∀ t ∈ Set.Icc a b, HasDerivAt u (du t) t) ∧
      SatisfiesWeakEvolutionOn (fun _ ↦ restrictForm S B)
        (fun t ↦ restrictFunctional S (ell t)) u du (Set.Icc a b) := by
  obtain ⟨u, hu₀, hu⟩ := exists_hilbertGalerkin_on_Icc S B ell hab hell t₀ u₀
  let du : ℝ → S := fun t ↦
    weakEvolutionVectorField (restrictForm S B)
      (fun s ↦ restrictFunctional S (ell s)) t (u t)
  refine ⟨u, du, hu₀, ?_, ?_, ?_⟩
  · intro t _ht
    rfl
  · intro t ht
    exact (hu t ht).1
  · intro t ht
    exact (hu t ht).2

/-- If `ℓ` is continuous on `[a, b]` with `‖ℓ(t)‖ ≤ M` and `C ‖w‖² ≤ B(w, w)`, there is a
classical solution on `[a, b]` with `u(a) = u₀` satisfying the energy bound
`½ ‖u(t)‖² ≤ ½ ‖u₀‖² + M² (t - a) / (2C)` and the derivative bound
`‖u'(t)‖ ≤ M + ‖B‖ ‖u(t)‖`. The second follows from `u' = Riesz(ℓ|_S) - A_S u`. -/
theorem exists_hilbertGalerkin_with_uniform_bounds
    (S : Submodule ℝ V) [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    {a b C M : ℝ} (hab : a ≤ b) (hC : 0 < C) (hM : 0 ≤ M)
    (hell_cont : ContinuousOn ell (Set.Icc a b))
    (hell_bound : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hcoercive : ∀ w : V, C * ‖w‖ ^ 2 ≤ B w w)
    (u₀ : S) :
    ∃ u : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivAt u
          (weakEvolutionVectorField (restrictForm S B)
            (fun s ↦ restrictFunctional S (ell s)) t (u t)) t ∧
        SatisfiesWeakEvolutionAt (restrictForm S B) (restrictFunctional S (ell t))
          (u t)
          (weakEvolutionVectorField (restrictForm S B)
            (fun s ↦ restrictFunctional S (ell s)) t (u t))) ∧
      (∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖u₀‖ ^ 2 + (M ^ 2 / (2 * C)) * (t - a)) ∧
      (∀ t ∈ Set.Icc a b,
        ‖weakEvolutionVectorField (restrictForm S B)
            (fun s ↦ restrictFunctional S (ell s)) t (u t)‖ ≤
          M + ‖B‖ * ‖u t‖) := by
  obtain ⟨u, hu₀, hu⟩ := exists_hilbertGalerkin_on_Icc S B ell hab hell_cont
    ⟨a, le_rfl, hab⟩ u₀
  let du : ℝ → S := fun t ↦
    weakEvolutionVectorField (restrictForm S B)
      (fun s ↦ restrictFunctional S (ell s)) t (u t)
  have henergy := hilbertGalerkin_energy_bound S B hab ell u du hC hM
    (fun t ht ↦ (hu t ht).1)
    hcoercive hell_bound (fun t ht ↦ (hu t ht).2)
  refine ⟨u, hu₀, hu, ?_, ?_⟩
  · intro t ht
    simpa [hu₀] using henergy t ht
  · intro t ht
    change ‖(toDual ℝ _).symm (restrictFunctional S (ell t)) -
        continuousLinearMapOfBilin (restrictForm S B) (u t)‖ ≤ M + ‖B‖ * ‖u t‖
    calc
      _ ≤ ‖(toDual ℝ _).symm (restrictFunctional S (ell t))‖ +
          ‖continuousLinearMapOfBilin (restrictForm S B) (u t)‖ := norm_sub_le _ _
      _ = ‖restrictFunctional S (ell t)‖ + ‖restrictForm S B (u t)‖ := by
        simp [continuousLinearMapOfBilin]
      _ ≤ M + ‖B‖ * ‖u t‖ :=
        add_le_add
          ((norm_restrictFunctional_le S (ell t)).trans (hell_bound t ht))
          (norm_restrictForm_apply_le S B (u t))

end Galerkin

end PDE.Analysis.Evolution
