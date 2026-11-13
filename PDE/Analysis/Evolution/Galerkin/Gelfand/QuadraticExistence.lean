/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.QuadraticVectorField
import Mathlib.Analysis.ODE.ExistUnique
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Galerkin.Gelfand.NonlinearEnergy
import PDE.Analysis.Evolution.ODE.FiniteContinuation

/-!
# Existence for quadratic Gelfand Galerkin equations

Galerkin approximation of an evolution equation with a bounded trilinear
term,

`⟪u', v⟫_H + A(t)(u, v) + N(t)(u, u, v) = ℓ(t)(v)` for all `v ∈ S`,

on a finite-dimensional trial space `S` of a Gelfand triple `V ↪ H ↪ V*`.
After inverting the pivot mass operator this is an ODE on `S` with a locally
Lipschitz, quadratically growing right-hand side, so Picard–Lindelöf (Mathlib's
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`) gives a
solution on a time cell whose length is controlled by the radius of a ball
around the initial state and a speed bound.

An upper bound `K` on the energy pairing for all states with pivot energy at
most `R` gives a solution on any interval where `E₀ + K (b - a) < R`.
The proof first derives the energy envelope, then converts it into a
coefficient bound using finite dimensionality. Picard solutions on a fine
arithmetic partition glue to a solution on the whole interval. The resulting
lifespan and pivot-energy bound are independent of the coefficient norms and
inverse mass constants, which affect only the internal partition.

This construction requires no positive coercivity. With coercivity and skew
cancellation it specializes to existence on every finite interval. For an
inviscid approximation the statewise energy-pairing bound for the projected
equation is a hypothesis.

## Main results

* `exists_gelfandGalerkin_quadratic_on_Icc_of_bounds`: Picard–Lindelöf
  existence on one quantitative time cell.
* `gelfandGalerkin_quadratic_derivative_eq_vectorField`: the projected
  equation determines the derivative uniquely.
* `norm_trial_le_of_half_pivot_norm_sq_le`: a pivot-energy bound controls
  the trial-space norm.
* `exists_gelfandGalerkin_quadratic_on_Icc_of_energy_pairing`: a statewise
  energy-pairing bound gives a common lifespan and affine energy envelope.
* `exists_gelfandGalerkin_quadratic_on_Icc_of_cubic_energy_growth`: a cubic
  energy-growth inequality gives an explicit common lifespan and energy cap.
* `exists_gelfandGalerkin_quadratic_on_Icc`: existence on any `[a, b]` with
  the energy bound `½ ‖u(t)‖²_H ≤ ½ ‖u₀‖²_H + M_ℓ² (t - a) / (2C)`.

## References

* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter III (the evolution Navier-Stokes equation). <https://doi.org/10.1090/chel/343>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
section GelfandGalerkinQuadraticExistence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Picard–Lindelöf construction for a quadratic Galerkin equation on one
closed interval.

The radius and speed hypotheses are the standard quantitative conditions:
the vector field is bounded by `L` on the radius-`R` ball about the initial
state, and the interval is short enough that a trajectory of speed `L`
cannot leave that ball.
-/
theorem exists_gelfandGalerkin_quadratic_on_Icc_of_bounds
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hAcont : ContinuousOn A (Set.Icc a b))
    (hNcont : IsQuadraticPointwiseContinuousOn N (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MA MN Mell R L : NNReal)
    (hAnorm : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (hNnorm : ∀ t ∈ Set.Icc a b, (N t).IsBoundedBy MN)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S)
    (hL : ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ((Mell : ℝ) + (MA : ℝ) * (‖u₀‖ + (R : ℝ)) +
          (MN : ℝ) * (‖u₀‖ + (R : ℝ)) ^ 2) ≤ L)
    (htime : (L : ℝ) * (b - a) ≤ R) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
          A t (u t : V) (v : V) +
          N t (u t : V) (u t : V) (v : V) =
        ell t (v : V)) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  let K : NNReal := ⟨‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
    ((MA : ℝ) + (MN : ℝ) * (2 * (‖u₀‖ + (R : ℝ)))), by positivity⟩
  have hPL : IsPicardLindelof (gelfandGalerkinQuadraticVectorField T S A N ell)
      (tmin := a) (tmax := b) ⟨a, le_rfl, hab⟩ u₀ R 0 L K := by
    refine ⟨fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_,
      fun x _ ↦ continuousOn_gelfandGalerkinQuadraticVectorField T S hAcont hNcont hNnorm MN.2
        hellcont continuousOn_const, fun t ht x hx ↦ ?_, ?_⟩
    · rw [dist_eq_norm, dist_eq_norm]
      calc _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
            (‖A t‖ + (MN : ℝ) * (‖x‖ + ‖y‖)) * ‖x - y‖ :=
          norm_gelfandGalerkinQuadraticVectorField_sub_le T S A N ell t x y (hNnorm t ht) MN.2
        _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
            ((MA : ℝ) + (MN : ℝ) * (2 * (‖u₀‖ + (R : ℝ)))) * ‖x - y‖ := by
          gcongr
          · exact hAnorm t ht
          · linarith [norm_le_of_mem_closedBall hx, norm_le_of_mem_closedBall hy]
    · have hx := norm_le_of_mem_closedBall hx
      have := hellnorm t ht
      have := hAnorm t ht
      refine (norm_gelfandGalerkinQuadraticVectorField_le T S A N ell t x (hNnorm t ht)
        MN.2).trans (le_trans ?_ hL)
      gcongr
    · simpa [max_eq_left (sub_nonneg.mpr hab)] using htime
  obtain ⟨u, hu₀, hu⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨u, fun t ↦ gelfandGalerkinQuadraticVectorField T S A N ell t (u t), hu₀, hu,
    continuousOn_gelfandGalerkinQuadraticVectorField T S hAcont hNcont hNnorm MN.2 hellcont
      (HasDerivWithinAt.continuousOn hu),
    fun t _ v ↦ gelfandGalerkinQuadraticVectorField_equation T S A N ell t (u t) v⟩

/--
If `d ∈ S` satisfies the projected quadratic Galerkin equation at the state `u`, then `d` is
the mass-inverted quadratic vector field at `(t, u)`.
-/
theorem gelfandGalerkin_quadratic_derivative_eq_vectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u d : S)
    (hd : ∀ v : S,
      inner ℝ (T.inclusion (d : V)) (T.inclusion (v : V)) +
          A t (u : V) (v : V) +
          N t (u : V) (u : V) (v : V) =
        ell t (v : V)) :
    d = gelfandGalerkinQuadraticVectorField T S A N ell t u := by
  let z : S := d - gelfandGalerkinQuadraticVectorField T S A N ell t u
  have hzH : T.inclusion (z : V) = 0 := inner_self_eq_zero.mp <| by
    change inner ℝ
      (T.inclusion ((d - gelfandGalerkinQuadraticVectorField T S A N ell t u : S) : V))
      (T.inclusion (z : V)) = 0
    simp only [Submodule.coe_sub, map_sub, inner_sub_left]
    linarith [hd z, gelfandGalerkinQuadraticVectorField_equation T S A N ell t u z]
  exact sub_eq_zero.mp (Subtype.ext (T.injective (hzH.trans (map_zero _).symm)))

/--
If `½ ‖ι u‖²_H ≤ E` with `E ≥ 0`, then `‖u‖_V ≤ K_S (1 + 2E)`, where `K_S` is the inverse bound
of the pivot inclusion of the finite-dimensional trial space `S`. The coarse bound
`‖ι u‖_H ≤ 1 + 2E` avoids a square root.
-/
theorem norm_trial_le_of_half_pivot_norm_sq_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] (u : S) {E : ℝ}
    (hE : 0 ≤ E)
    (hu : (1 / 2 : ℝ) * ‖T.inclusion (u : V)‖ ^ 2 ≤ E) :
    ‖u‖ ≤ (trialInclusionInverseBound T S : ℝ) * (1 + 2 * E) := by
  have hpivot :
      ‖T.inclusion (u : V)‖ ≤ 1 + 2 * E := by
    nlinarith [sq_nonneg (‖T.inclusion (u : V)‖ - 1)]
  calc
    ‖u‖ ≤ (trialInclusionInverseBound T S : ℝ) *
        ‖T.inclusion (u : V)‖ :=
      norm_trial_le_trialInclusionInverseBound_mul_norm_inclusion T S u
    _ ≤ (trialInclusionInverseBound T S : ℝ) * (1 + 2 * E) :=
      mul_le_mul_of_nonneg_left hpivot
        (NNReal.coe_nonneg (trialInclusionInverseBound T S))

/-- A Picard solution on a short cell stays under the global affine energy
envelope. The speed is controlled on the coefficient ball supplied by the energy cap. -/
private theorem exists_quadratic_cell_preserving_energy_envelope
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V)
    {a b c e : ℝ} (hab : a ≤ b) (hc : a ≤ c) (hce : c ≤ e) (he : e ≤ b)
    (hAcont : ContinuousOn A (Icc a b))
    (hNcont : IsQuadraticPointwiseContinuousOn N (Icc a b))
    (hellcont : ContinuousOn ell (Icc a b))
    (MA MN Mell X L : NNReal)
    (hAnorm : ∀ t ∈ Icc a b, ‖A t‖ ≤ MA)
    (hNnorm : ∀ t ∈ Icc a b, (N t).IsBoundedBy MN)
    (hellnorm : ∀ t ∈ Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S) {K R : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ t ∈ Icc a b, ∀ v : S,
      (1 / 2 : ℝ) * ‖T.inclusion (v : V)‖ ^ 2 ≤ R →
        ell t (v : V) - A t (v : V) (v : V) -
          N t (v : V) (v : V) (v : V) ≤ K)
    (hmargin : (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + K * (b - a) < R)
    (hX : (trialInclusionInverseBound T S : ℝ) *
      (1 + 2 * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + K * (b - a))) ≤ X)
    (hL : ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
      ((Mell : ℝ) + (MA : ℝ) * ((X : ℝ) + 1) +
        (MN : ℝ) * ((X : ℝ) + 1) ^ 2) ≤ L)
    (hstep : (L : ℝ) * (e - c) ≤ 1) (x : S)
    (hxenergy : (1 / 2 : ℝ) * ‖T.inclusion (x : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + K * (c - a)) :
    ∃ u : ℝ → S, u c = x ∧
      (∀ t ∈ Icc c e, HasDerivWithinAt u
        (gelfandGalerkinQuadraticVectorField T S A N ell t (u t)) (Icc c e) t) ∧
      ∀ t ∈ Icc c e, (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + K * (t - a) := by
  have hsub : Icc c e ⊆ Icc a b := Icc_subset_Icc hc he
  have hxnorm : ‖x‖ ≤ X := (norm_trial_le_of_half_pivot_norm_sq_le T S x (by positivity)
    (hxenergy.trans (by gcongr; exact hce.trans he))).trans hX
  have hLx : ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ((Mell : ℝ) +
      (MA : ℝ) * (‖x‖ + ((1 : NNReal) : ℝ)) + (MN : ℝ) * (‖x‖ + ((1 : NNReal) : ℝ)) ^ 2) ≤ L := by
    rw [NNReal.coe_one]
    refine le_trans ?_ hL
    gcongr
  obtain ⟨u, du, hu₀, hdu, -, heq⟩ := exists_gelfandGalerkin_quadratic_on_Icc_of_bounds
    T S A N ell hce (hAcont.mono hsub) (hNcont.mono hsub) (hellcont.mono hsub) MA MN Mell 1 L
    (fun t ht ↦ hAnorm t (hsub ht)) (fun t ht ↦ hNnorm t (hsub ht))
    (fun t ht ↦ hellnorm t (hsub ht)) x hLx hstep
  have hderiv (t : ℝ) (ht : t ∈ Icc c e) : HasDerivWithinAt u
      (gelfandGalerkinQuadraticVectorField T S A N ell t (u t)) (Icc c e) t :=
    (hdu t ht).congr_deriv
      (gelfandGalerkin_quadratic_derivative_eq_vectorField T S A N ell t (u t) (du t) (heq t ht))
  -- the energy envelope of the cell, started below the global envelope
  have henergy := gelfandGalerkin_quadratic_energy_bound_of_pairing_on_sublevel
    T S A N ell u du hce hK hdu (fun t ht v hv ↦ hpair t (hsub ht) v hv) heq (by
      rw [hu₀]
      linarith [mul_le_mul_of_nonneg_left (sub_le_sub_right he a) hK])
  refine ⟨u, hu₀, hderiv, fun t ht ↦ ?_⟩
  have h := henergy t ht
  rw [hu₀] at h
  linarith

/--
Uniform finite-interval existence from an energy pairing bound on a sublevel.

The hypothesis bounds the right-hand side of the energy identity for every
trial state in the pivot-energy ball. A first-contact argument proves that
solutions stay below the affine envelope. Finite-dimensional norm equivalence
then bounds the coefficients, and Picard solutions on a sufficiently fine
partition glue to a solution on the prescribed interval.

The time condition and the energy envelope involve only the initial pivot energy,
`K`, and `R`; the coefficient bounds and trial-space constants affect only
the internal partition. Thus the same time interval works for a family of
approximants with common initial-energy and pairing bounds, even if their
coefficient norms or inverse mass norms diverge.
-/
theorem exists_gelfandGalerkin_quadratic_on_Icc_of_energy_pairing
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hAcont : ContinuousOn A (Set.Icc a b))
    (hNcont : IsQuadraticPointwiseContinuousOn N (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MA MN Mell : NNReal)
    (hAnorm : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (hNnorm : ∀ t ∈ Set.Icc a b, (N t).IsBoundedBy MN)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S) {K R : ℝ} (hK : 0 ≤ K)
    (hpair : ∀ t ∈ Set.Icc a b, ∀ v : S,
      (1 / 2 : ℝ) * ‖T.inclusion (v : V)‖ ^ 2 ≤ R →
        ell t (v : V) - A t (v : V) (v : V) -
          N t (v : V) (v : V) (v : V) ≤ K)
    (hmargin : (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
      K * (b - a) < R) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
            A t (u t : V) (v : V) +
            N t (u t : V) (u t : V) (v : V) =
          ell t (v : V)) ∧
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
            K * (t - a) := by
  let : CompleteSpace S := FiniteDimensional.complete ℝ S
  let energy : ℝ → S → ℝ := fun _ x ↦ (1 / 2 : ℝ) * ‖T.inclusion (x : V)‖ ^ 2
  let bound : ℝ → S → ℝ := fun t _ ↦ (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + K * (t - a)
  -- the coefficient bound `X` on the energy cap and the speed `L` on the ball of radius `X + 1`
  let X : NNReal := ⟨(trialInclusionInverseBound T S : ℝ) *
    (1 + 2 * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + K * (b - a))), by positivity⟩
  let L : NNReal := ⟨‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
    ((Mell : ℝ) + (MA : ℝ) * ((X : ℝ) + 1) + (MN : ℝ) * ((X : ℝ) + 1) ^ 2), by positivity⟩
  -- a partition of `[a, b]` into `cells` intervals of length `d` with `L d ≤ 1`
  obtain ⟨cells, hcells_large⟩ := exists_nat_gt (1 + (L : ℝ) * (b - a))
  have hLba : 0 ≤ (L : ℝ) * (b - a) := mul_nonneg L.2 (sub_nonneg.mpr hab)
  have hcells : 0 < (cells : ℝ) := by linarith
  let d : ℝ := (b - a) / cells
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hab) hcells.le
  have hcells_d : (cells : ℝ) * d = b - a := by
    dsimp only [d]
    field_simp
  have hLd : (L : ℝ) * d ≤ 1 := by
    dsimp only [d]
    rw [← mul_div_assoc, div_le_iff₀ hcells]
    linarith
  obtain ⟨u, hu₀, hdu, huenergy⟩ := exists_ode_solution_Icc_of_partition_of_energyEnvelope
    (gelfandGalerkinQuadraticVectorField T S A N ell) energy bound hd cells
    (Nat.cast_pos.mp hcells) (by rw [hcells_d]; ring : a + (cells : ℝ) * d = b) u₀
    (by simp [energy, bound])
    fun n hn x hxenergy ↦ by
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ cells := by exact_mod_cast hn
      refine exists_quadratic_cell_preserving_energy_envelope T S A N ell hab
        (le_add_of_nonneg_right (mul_nonneg n.cast_nonneg hd)) (by push_cast; linarith)
        (by linarith [mul_le_mul_of_nonneg_right hn' hd]) hAcont hNcont hellcont MA MN Mell X L
        hAnorm hNnorm hellnorm u₀ hK hpair hmargin le_rfl le_rfl ?_ x hxenergy
      push_cast
      linarith
  refine ⟨u, _, hu₀, hdu, continuousOn_gelfandGalerkinQuadraticVectorField T S hAcont hNcont
    hNnorm MN.2 hellcont (HasDerivWithinAt.continuousOn hdu),
    fun t _ v ↦ gelfandGalerkinQuadraticVectorField_equation T S A N ell t (u t) v,
    fun t ht ↦ ?_⟩
  simpa [energy, bound, hu₀] using huenergy t ht

/-- A cubic energy-growth bound gives a common positive lifespan and a uniform
pivot-energy cap for quadratic Galerkin approximants.

If the initial energy is at most `E` and the energy pairing is at most
`C (1 + ‖v‖_H)³`, the interval length may be any value at most
`(2 (C (2 E + 4)³ + 1))⁻¹`. The constructed trajectory has energy at most
`E + 1/2`. The constants depend on the energy inequality, independently of the
trial dimension and the norms of the regularized coefficients. -/
theorem exists_gelfandGalerkin_quadratic_on_Icc_of_cubic_energy_growth
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hAcont : ContinuousOn A (Set.Icc a b))
    (hNcont : IsQuadraticPointwiseContinuousOn N (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MA MN Mell : NNReal)
    (hAnorm : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (hNnorm : ∀ t ∈ Set.Icc a b, (N t).IsBoundedBy MN)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (u₀ : S) {C E : ℝ} (hC : 0 ≤ C)
    (hinitial : (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 ≤ E)
    (hgrowth : ∀ t ∈ Set.Icc a b, ∀ v : S,
      ell t (v : V) - A t (v : V) (v : V) -
          N t (v : V) (v : V) (v : V) ≤
        C * (1 + ‖T.inclusion (v : V)‖) ^ 3)
    (htime : b - a ≤ (2 * (C * (2 * E + 4) ^ 3 + 1))⁻¹) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
            A t (u t : V) (v : V) +
            N t (u t : V) (u t : V) (v : V) =
          ell t (v : V)) ∧
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤ E + 1 / 2 := by
  have hE : 0 ≤ E := (mul_nonneg (by norm_num) (sq_nonneg _)).trans hinitial
  have hK : 0 ≤ C * (2 * E + 4) ^ 3 := by positivity
  set K := C * (2 * E + 4) ^ 3 with hKdef
  have hsmall : K * (b - a) < 1 / 2 :=
    (mul_le_mul_of_nonneg_left htime hK).trans_lt (by
      rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
      linarith)
  -- on the energy ball `½‖v‖² ≤ E + 1` the cubic growth bound is at most `K`
  have hpair : ∀ t ∈ Set.Icc a b, ∀ v : S,
      (1 / 2 : ℝ) * ‖T.inclusion (v : V)‖ ^ 2 ≤ E + 1 →
        ell t (v : V) - A t (v : V) (v : V) - N t (v : V) (v : V) (v : V) ≤ K :=
    fun t ht v hv ↦ (hgrowth t ht v).trans <| by
      rw [hKdef]
      gcongr C * ?_ ^ 3
      nlinarith [sq_nonneg (‖T.inclusion (v : V)‖ - 1)]
  obtain ⟨u, du, hu₀, hdu, hducont, heq, henergy⟩ :=
    exists_gelfandGalerkin_quadratic_on_Icc_of_energy_pairing
      T S A N ell hab hAcont hNcont hellcont MA MN Mell hAnorm hNnorm hellnorm
      u₀ hK hpair (by linarith)
  refine ⟨u, du, hu₀, hdu, hducont, heq, fun t ht ↦ ?_⟩
  linarith [henergy t ht, mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hK]

/--
Global finite-interval existence for a quadratic Gelfand Galerkin equation.

Coercivity and skew cancellation give a constant upper bound for the
energy pairing. Choosing an energy cap above the resulting affine envelope
reduces the construction to `exists_gelfandGalerkin_quadratic_on_Icc_of_energy_pairing`.
-/
theorem exists_gelfandGalerkin_quadratic_on_Icc
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hAcont : ContinuousOn A (Set.Icc a b))
    (hNcont : IsQuadraticPointwiseContinuousOn N (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MA MN Mell : NNReal)
    (hAnorm : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (hNnorm : ∀ t ∈ Set.Icc a b, (N t).IsBoundedBy MN)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ A t w w)
    (hskew : ∀ t ∈ Set.Icc a b, (N t).IsSkewInLastTwo)
    (u₀ : S) :
    ∃ u du : ℝ → S,
      u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (du t) (Set.Icc a b) t) ∧
      ContinuousOn du (Set.Icc a b) ∧
      (∀ t ∈ Set.Icc a b, ∀ v : S,
        inner ℝ (T.inclusion (du t : V)) (T.inclusion (v : V)) +
            A t (u t : V) (v : V) +
            N t (u t : V) (u t : V) (v : V) =
          ell t (v : V)) ∧
      ∀ t ∈ Set.Icc a b,
        (1 / 2 : ℝ) * ‖T.inclusion (u t : V)‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
            ((Mell : ℝ) ^ 2 / (2 * C)) * (t - a) := by
  have hK : 0 ≤ (Mell : ℝ) ^ 2 / (2 * C) := by positivity
  refine exists_gelfandGalerkin_quadratic_on_Icc_of_energy_pairing T S A N ell hab hAcont hNcont
    hellcont MA MN Mell hAnorm hNnorm hellnorm u₀ hK
    (R := (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 + (Mell : ℝ) ^ 2 / (2 * C) * (b - a) + 1)
    (fun t ht v _ ↦ ?_) (by linarith)
  -- `ℓ(v) ≤ ‖ℓ‖ ‖v‖ ≤ ‖ℓ‖² / (2C) + (C/2) ‖v‖²` and `C ‖v‖² ≤ A(v, v)`
  rw [(hskew t ht).energy_eq_zero (v : V), sub_zero]
  linarith [hcoercive t ht (v : V), mul_nonneg hC.le (sq_nonneg ‖(v : V)‖),
    (le_abs_self _).trans ((ell t).le_opNorm (v : V)),
    mul_le_sq_div_add_mul_sq_half hC ‖ell t‖ ‖(v : V)‖,
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hellnorm t ht) 2)
      (by positivity : 0 ≤ 2 * C)]

end GelfandGalerkinQuadraticExistence
end Galerkin

end PDE.Analysis.Evolution
