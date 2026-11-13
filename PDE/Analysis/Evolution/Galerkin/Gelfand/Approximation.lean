/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Analysis.Evolution.Galerkin.TrialProjection
import PDE.Analysis.Evolution.Galerkin.Gelfand.Energy
import PDE.Analysis.Evolution.Galerkin.ProjectedDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Gelfand Galerkin approximations

A Gelfand Galerkin approximation on a trial space `S ⊆ V` is a `C¹` trajectory `u : [a, b] → S`
with `u(a) = u₀`, satisfying the projected equation
`⟪ι u'(t), ι v⟫_H + B(t)(u(t), v) = ℓ(t)(v)` for all `v ∈ S`, together with the pivot-energy
bound and the integrated coercive bound

`½ ‖ι u(t)‖²_H + (C/2) ∫_a^t ‖u‖²_V ≤ ½ ‖ι u₀‖²_H + M² (t - a) / (2C)`.

Its `V*` derivative is `energyToDual (u'(t))`, which acts on `v ∈ V` by `⟪ι u'(t), ι v⟫_H`.
With a stable trial projection `P` of energy bound `K`, this derivative satisfies
`‖u'‖_{V*} ≤ K (‖ℓ(t)‖ + ‖B(t)‖ ‖u(t)‖_V)`, and its square integral is bounded accordingly.
Approximations exist on every trial space when `B` and `ℓ` are continuous and bounded on
`[a, b]` and `B` is uniformly coercive.

## Main definitions

* `GelfandGalerkinApproximation`: a trial-space trajectory bundled with its projected equation
  and its energy bounds.
* `GelfandGalerkinApproximation.dualDerivative`: its `V*` derivative.

## Main results

* `GelfandGalerkinApproximation.integral_norm_sq_le`: the bound on `∫_a^b ‖u‖²_V`.
* `GelfandGalerkinApproximation.norm_dualDerivative_le`,
  `GelfandGalerkinApproximation.integral_norm_dualDerivative_sq_le`: the pointwise and
  integrated bounds on `‖u'‖_{V*}`.
* `GelfandGalerkinApproximation.exists_nonauto_on_Icc`,
  `GelfandGalerkinApproximation.exists_nonauto_sequence_on_Icc`: existence on one trial space,
  and on every trial space of a sequence with the same constants.

## How it works

These are the approximate solutions of Evans, §7.1.2, Theorem 1, with the bounds of his
Theorem 2, (20), in an abstract Gelfand triple. We assume uniform coercivity
`C ‖w‖² ≤ B(t)(w, w)` in place of Gårding's inequality (22), so the energy bounds hold without
the Grönwall step (26). For the derivative, step 4 of his proof splits `v = v¹ + v²` and uses
the orthogonality of the `w_k` in `H¹₀(U)` to get `‖v¹‖ ≤ ‖v‖`. We replace this by a
`StableTrialProjection` with energy bound `K`: `dualDerivative_apply_eq_projected` evaluates
`u'(t)` at the projection `P v`, and the factor `K` in `norm_dualDerivative_le` comes from
`‖P v‖_V ≤ K ‖v‖_V`.

## Implementation notes

Stable trial projections (`StableTrialProjection`, `StableTrialSystem`) and approximation
trajectories (`GelfandGalerkinApproximation`, a trajectory bundled with its equation and its
energy bounds) are structures, because the whole Galerkin construction uses their data and
laws. Coercivity estimates, convergence facts and compatibility conditions are predicates or
explicit hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 1 (Construction of approximate
  solutions), p. 376, and Theorem 2 (Energy estimates) with its proof, (20)-(26) and step 4,
  pp. 376-378. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
section GelfandGalerkinMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A trial-space trajectory with its coefficient derivative, projected
equation, and two energy bounds. Its ambient `V*` derivative is
`T.energyToDual (du : V)`, which pairs `du` with test vectors using the
pivot-space inner product. The equation identifies this derivative with
`ell - B u` on trial-space tests. -/
structure GelfandGalerkinApproximation
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) (ell : ℝ → StrongDual ℝ V)
    (a b C M : ℝ) (u₀ : S) where
  /-- Trial-space trajectory. -/
  trajectory : ℝ → S
  /-- Time derivative of the trial-space coefficients. -/
  coefficientDerivative : ℝ → S
  /-- The trajectory assumes the prescribed initial trial vector. -/
  initial : trajectory a = u₀
  /-- The coefficient derivative is the derivative of the trajectory on the time interval. -/
  derivative : ∀ t ∈ Set.Icc a b,
    HasDerivWithinAt trajectory (coefficientDerivative t) (Set.Icc a b) t
  /-- Continuity needed to realize the derivative as a Bochner `L²` class. -/
  derivativeContinuous : ContinuousOn coefficientDerivative (Set.Icc a b)
  /-- Galerkin weak equation tested against every trial vector. -/
  equation : ∀ t ∈ Set.Icc a b, ∀ v : S,
    inner ℝ (T.inclusion (coefficientDerivative t : V))
        (T.inclusion (v : V)) +
      B t (trajectory t : V) (v : V) = ell t (v : V)
  /-- Pointwise pivot-energy estimate. -/
  energyBound : ∀ t ∈ Set.Icc a b,
    (1 / 2 : ℝ) * ‖T.inclusion (trajectory t : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (t - a)
  /-- Integrated coercive estimate, uniform in the trial-space dimension. -/
  integratedEnergyBound : ∀ t ∈ Set.Icc a b,
    (1 / 2 : ℝ) * ‖T.inclusion (trajectory t : V)‖ ^ 2 +
        (C / 2) * ∫ s in a..t, ‖(trajectory s : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (t - a)

namespace GelfandGalerkinApproximation

/-- The `V*` derivative `energyToDual (u'(t))` of a Galerkin trajectory. -/
def dualDerivative
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀) (t : ℝ) :
    StrongDual ℝ V :=
  T.energyToDual (G.coefficientDerivative t : V)

/-- The ambient dual derivative evaluates as the pivot pairing with the coefficient derivative. -/
@[simp]
theorem dualDerivative_apply
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (t : ℝ) (v : V) :
    G.dualDerivative t v =
      inner ℝ (T.inclusion (G.coefficientDerivative t : V)) (T.inclusion v) :=
  rfl

/-- For `C > 0`, `∫_a^b ‖u‖²_V ≤ (2/C) (½ ‖ι u₀‖²_H + M² (b - a) / (2C))`. -/
theorem integral_norm_sq_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (hab : a ≤ b) (hC : 0 < C) :
    ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2 ≤
      (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (b - a)) := by
  have henergy := G.integratedEnergyBound b ⟨hab, le_rfl⟩
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖T.inclusion (G.trajectory b : V)‖ ^ 2 := by
    positivity
  have hbase : (C / 2) * ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2 ≤
      (1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (b - a) := by
    linarith
  calc
    ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2 =
        (2 / C) * ((C / 2) * ∫ s in a..b, ‖(G.trajectory s : V)‖ ^ 2) := by
          field_simp
    _ ≤ (2 / C) * ((1 / 2 : ℝ) * ‖T.inclusion (u₀ : V)‖ ^ 2 +
        (M ^ 2 / (2 * C)) * (b - a)) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)

/-- For every `v ∈ V`, the `V*` derivative satisfies `u'(t)(v) = ℓ(t)(P v) - B(t)(u(t), P v)`,
where `P v` is the energy projection. This follows from pivot orthogonality of `P`. -/
theorem dualDerivative_apply_eq_projected
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {K : NNReal} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (P : StableTrialProjection T S K) {t : ℝ} (ht : t ∈ Set.Icc a b)
    (v : V) :
    G.dualDerivative t v =
      ell t (P.energyProjection v : V) -
        B t (G.trajectory t : V) (P.energyProjection v : V) := by
  exact P.energyToDual_apply_eq_projected (G.equation t ht) v

/-- Pointwise bound `‖u'(t)‖_{V*} ≤ K (‖ℓ(t)‖ + ‖B(t)‖ ‖u(t)‖_V)`, with `K` the energy bound of
the trial projection. -/
theorem norm_dualDerivative_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M : ℝ} {K : NNReal} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (P : StableTrialProjection T S K) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    ‖G.dualDerivative t‖ ≤
      (K : ℝ) * (‖ell t‖ + ‖B t‖ * ‖(G.trajectory t : V)‖) := by
  exact P.norm_energyToDual_le_of_projected_equation (G.equation t ht)

/-- If `‖ℓ(t)‖ ≤ M` and `‖B(t)‖ ≤ MB` on `[a, b]`, then
`∫_a^b ‖u'‖²_{V*} ≤ 2K² (M² (b - a) + MB² ∫_a^b ‖u‖²_V)`. -/
theorem integral_norm_dualDerivative_sq_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {a b C M MB : ℝ} {K : NNReal} {u₀ : S}
    (G : GelfandGalerkinApproximation T S B ell a b C M u₀)
    (P : StableTrialProjection T S K) (hab : a ≤ b)
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (hB : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB) :
    ∫ t in a..b, ‖G.dualDerivative t‖ ^ 2 ≤
      2 * (K : ℝ) ^ 2 *
        (M ^ 2 * (b - a) +
          MB ^ 2 * ∫ t in a..b, ‖(G.trajectory t : V)‖ ^ 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hell a ⟨le_rfl, hab⟩)
  have hMB : 0 ≤ MB := (norm_nonneg (B a)).trans (hB a ⟨le_rfl, hab⟩)
  let f : ℝ → ℝ := fun t ↦ ‖G.dualDerivative t‖ ^ 2
  let g : ℝ → ℝ := fun t ↦
    2 * (K : ℝ) ^ 2 * (M ^ 2 + MB ^ 2 * ‖(G.trajectory t : V)‖ ^ 2)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc a b) : f t ≤ g t := by
    have hdual := G.norm_dualDerivative_le P ht
    have hlinear : ‖G.dualDerivative t‖ ≤
        (K : ℝ) * (M + MB * ‖(G.trajectory t : V)‖) := by
      exact hdual.trans (mul_le_mul_of_nonneg_left
        (add_le_add (hell t ht)
          (mul_le_mul_of_nonneg_right (hB t ht) (norm_nonneg _))) K.coe_nonneg)
    dsimp [f, g]
    have hsum : (M + MB * ‖(G.trajectory t : V)‖) ^ 2 ≤
        2 * (M ^ 2 + MB ^ 2 * ‖(G.trajectory t : V)‖ ^ 2) := by
      nlinarith [sq_nonneg (M - MB * ‖(G.trajectory t : V)‖)]
    have hsq :=
      sq_le_sq₀ (norm_nonneg _) (mul_nonneg K.coe_nonneg (by positivity)) |>.2 hlinear
    nlinarith [sq_nonneg (K : ℝ)]
  have hucont : ContinuousOn (fun t ↦ (G.trajectory t : V)) (Set.Icc a b) := by
    apply S.subtypeL.continuous.comp_continuousOn
    intro t ht
    exact (G.derivative t ht).continuousWithinAt
  have hducont : ContinuousOn G.dualDerivative (Set.Icc a b) :=
    T.energyToDual.continuous.comp_continuousOn
      (S.subtypeL.continuous.comp_continuousOn G.derivativeContinuous)
  have hfcont : ContinuousOn f (Set.Icc a b) :=
    hducont.norm.pow 2
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    exact continuousOn_const.mul
      (continuousOn_const.add
        (continuousOn_const.mul (hucont.norm.pow 2)))
  have hfint : IntervalIntegrable f volume a b := by
    apply (hfcont.mono ?_).intervalIntegrable
    simp [Set.uIcc_of_le hab]
  have hgint : IntervalIntegrable g volume a b := by
    apply (hgcont.mono ?_).intervalIntegrable
    simp [Set.uIcc_of_le hab]
  have hrint : IntervalIntegrable
      (fun t ↦ ‖(G.trajectory t : V)‖ ^ 2) volume a b := by
    apply ((hucont.norm.pow 2).mono ?_).intervalIntegrable
    simp [Set.uIcc_of_le hab]
  have hmono := intervalIntegral.integral_mono_on hab hfint hgint hpoint
  dsimp [f, g] at hmono
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const
      (hrint.const_mul _),
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul] at hmono
  norm_num at hmono
  convert hmono using 1
  all_goals ring

end GelfandGalerkinApproximation

/--
A Galerkin approximation on `[a, b]` exists when `B` and `ℓ` are continuous on `[a, b]` with
`‖B(t)‖ ≤ MB`, `‖ℓ(t)‖ ≤ Mell` and `C ‖w‖² ≤ B(t)(w, w)` for some `C > 0`.

`exists_gelfandGalerkin_nonauto_on_Icc` constructs the trajectory on the whole interval, and
coercivity gives the energy estimates, whose constants do not depend on the trial space.
-/
theorem GelfandGalerkinApproximation.exists_nonauto_on_Icc
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal) {C : ℝ} (hC : 0 < C)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (u₀ : S) :
    Nonempty (GelfandGalerkinApproximation T S B ell a b C Mell u₀) := by
  obtain ⟨u, du, hu₀, hdu, hducont, heq, henergy, hintegrated⟩ :=
    exists_gelfandGalerkin_nonauto_on_Icc_with_energy
      T S B ell hab hBcont hellcont MB Mell hC hBnorm hellnorm
      hcoercive u₀
  exact ⟨⟨u, du, hu₀, hdu, hducont, heq, henergy, hintegrated⟩⟩

/--
Under the hypotheses of `exists_nonauto_on_Icc`, a Galerkin approximation with initial value
`u₀ n` exists in every trial space `S n` of a sequence, with the same constants `C` and
`Mell`. The inverse mass operators need not be uniformly bounded.
-/
theorem GelfandGalerkinApproximation.exists_nonauto_sequence_on_Icc
    (T : GelfandTriple (V := V) (H := H)) (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V)
    {a b : ℝ} (hab : a ≤ b)
    (hBcont : ContinuousOn B (Set.Icc a b))
    (hellcont : ContinuousOn ell (Set.Icc a b))
    (MB Mell : NNReal) {C : ℝ} (hC : 0 < C)
    (hBnorm : ∀ t ∈ Set.Icc a b, ‖B t‖ ≤ MB)
    (hellnorm : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ Mell)
    (hcoercive : ∀ t ∈ Set.Icc a b, ∀ w : V,
      C * ‖w‖ ^ 2 ≤ B t w w)
    (u₀ : ∀ n, S n) :
    Nonempty (∀ n,
      GelfandGalerkinApproximation T (S n) B ell a b C Mell (u₀ n)) := by
  classical
  have hex (n : ℕ) : Nonempty
      (GelfandGalerkinApproximation T (S n) B ell a b C Mell (u₀ n)) := by
    let : FiniteDimensional ℝ (S n) := hfinite n
    exact GelfandGalerkinApproximation.exists_nonauto_on_Icc
      T (S n) B ell hab hBcont hellcont MB Mell hC
      hBnorm hellnorm hcoercive (u₀ n)
  exact ⟨fun n ↦ (hex n).some⟩

end GelfandGalerkinMass

end Galerkin

end PDE.Analysis.Evolution
