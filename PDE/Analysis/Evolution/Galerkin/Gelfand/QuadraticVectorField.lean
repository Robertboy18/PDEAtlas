/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Analysis.TrilinearForm

/-!
# Quadratic Gelfand Galerkin vector fields

A continuous trilinear form `N` on `V` induces the quadratic dual-valued map
`u ↦ N(u, u, ·) ∈ V*`.  Restricting to a finite-dimensional trial space `S`,
representing by Riesz, and inverting the pivot mass operator of the Gelfand
triple gives the nonlinear part of the Galerkin ODE. Subtracting it from the affine field
`M⁻¹(ℓ - A u)` gives the complete field `M⁻¹(ℓ - A u - N(u, u))`. This field satisfies the
projected weak equation, grows at most quadratically, and is Lipschitz on bounded sets, as
Picard–Lindelöf requires. It is continuous in time along continuous trajectories when `N(t)`
is uniformly bounded and `t ↦ N(t)(u, u)` is continuous for each fixed state `u`. For the
Navier–Stokes equations `N` is the trilinear form `b(u, v, w)`.

## Main results

* `IsQuadraticPointwiseContinuousOn`, `continuousOn_quadratic_apply`:
  pointwise quadratic continuity and its upgrade along continuous paths.
* `gelfandGalerkinQuadraticTerm`, `gelfandGalerkinQuadraticVectorField`: the
  mass-inverted quadratic term and the complete field, with
  `gelfandGalerkinQuadraticVectorField_equation`.
* `norm_gelfandGalerkinQuadraticVectorField_le`,
  `norm_gelfandGalerkinQuadraticVectorField_sub_le`: quadratic growth and
  the local Lipschitz estimate.
* `continuousOn_gelfandGalerkinQuadraticVectorField`: continuity along a
  continuous trajectory.

## References

* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter III (the evolution Navier-Stokes equation). <https://doi.org/10.1090/chel/343>
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
section GelfandGalerkinQuadraticVectorField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
A time-dependent trilinear form is pointwise quadratic-continuous on a time
set if `t ↦ N(t)(u,u)` is dual-valued continuous for every fixed state `u`.
-/
def IsQuadraticPointwiseContinuousOn
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (s : Set ℝ) : Prop :=
  ∀ u : V, ContinuousOn (fun t ↦ N t u u) s

/-- Pointwise quadratic continuity restricts to smaller time sets. -/
theorem IsQuadraticPointwiseContinuousOn.mono
    {N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V}
    {s r : Set ℝ} (hN : IsQuadraticPointwiseContinuousOn N s)
    (hrs : r ⊆ s) :
    IsQuadraticPointwiseContinuousOn N r :=
  fun u ↦ (hN u).mono hrs

/--
Uniform boundedness upgrades fixed-state quadratic continuity to continuity
along every continuous state path.
-/
theorem continuousOn_quadratic_apply
    {N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V}
    {u : ℝ → V} {s : Set ℝ} {C : ℝ}
    (hNcont : IsQuadraticPointwiseContinuousOn N s)
    (hNbound : ∀ t ∈ s, (N t).IsBoundedBy C)
    (hC : 0 ≤ C) (hu : ContinuousOn u s) :
    ContinuousOn (fun t ↦ N t (u t) (u t)) s := by
  intro t ht
  have hu_t := hu t ht
  have herror :
      Tendsto
        (fun r ↦ N r (u r) (u r) - N r (u t) (u t))
        (𝓝[s] t) (nhds 0) := by
    apply squeeze_zero_norm'
      (a := fun r ↦ C * (‖u r‖ + ‖u t‖) * ‖u r - u t‖)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      apply ContinuousLinearMap.opNorm_le_bound
      · positivity
      intro z
      have hsplit :
          (N r (u r) (u r) - N r (u t) (u t)) z =
            N r (u r - u t) (u r) z +
              N r (u t) (u r - u t) z := by
        simp only [sub_apply, map_sub]
        ring
      rw [hsplit]
      calc
        ‖N r (u r - u t) (u r) z +
            N r (u t) (u r - u t) z‖ ≤
            ‖N r (u r - u t) (u r) z‖ +
              ‖N r (u t) (u r - u t) z‖ :=
          norm_add_le _ _
        _ ≤ C * ‖u r - u t‖ * ‖u r‖ * ‖z‖ +
            C * ‖u t‖ * ‖u r - u t‖ * ‖z‖ :=
          add_le_add
            ((hNbound r hr).norm_apply_le (u r - u t) (u r) z)
            ((hNbound r hr).norm_apply_le (u t) (u r - u t) z)
        _ = (C * (‖u r‖ + ‖u t‖) * ‖u r - u t‖) * ‖z‖ := by
          ring
    · have hnorm :
          Tendsto (fun r ↦ ‖u r‖) (𝓝[s] t) (nhds ‖u t‖) :=
        hu_t.norm
      have hdiff :
          Tendsto (fun r ↦ ‖u r - u t‖) (𝓝[s] t) (nhds 0) := by
        have hconst :
            ContinuousWithinAt (fun _ : ℝ ↦ u t) s t :=
          continuousWithinAt_const
        have hdiff' := (hu_t.sub hconst).norm
        change Tendsto (fun r ↦ ‖u r - u t‖) (𝓝[s] t)
          (nhds ‖u t - u t‖) at hdiff'
        simpa using hdiff'
      have hCconst :
          Tendsto (fun _ : ℝ ↦ C) (𝓝[s] t) (nhds C) :=
        tendsto_const_nhds
      have hnormConst :
          Tendsto (fun _ : ℝ ↦ ‖u t‖) (𝓝[s] t) (nhds ‖u t‖) :=
        tendsto_const_nhds
      have hbound :=
        (hCconst.mul (hnorm.add hnormConst)).mul hdiff
      simpa using hbound
  have hfixed :
      Tendsto (fun r ↦ N r (u t) (u t)) (𝓝[s] t)
        (nhds (N t (u t) (u t))) :=
    hNcont (u t) t ht
  have hsum := herror.add hfixed
  change Tendsto (fun r ↦ N r (u r) (u r)) (𝓝[s] t)
    (nhds (N t (u t) (u t)))
  simpa only [sub_add_cancel, zero_add] using hsum

/--
The mass-inverted quadratic term induced on a Galerkin trial space by a
time-dependent continuous trilinear form.
-/
def gelfandGalerkinQuadraticTerm
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V) :
    ℝ → S → S :=
  fun t u ↦ (trialMassEquiv T S).symm
    ((toDual ℝ _).symm (restrictFunctional S (N t (u : V) (u : V))))

/--
The mass-inverted quadratic Galerkin vector field
`M⁻¹(ell - A u - N(u,u))`.
-/
def gelfandGalerkinQuadraticVectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) : ℝ → S → S :=
  fun t u ↦
    gelfandGalerkinVectorField T S A ell t u -
      gelfandGalerkinQuadraticTerm T S N t u

/-- The quadratic Galerkin term represents `v ↦ N(u,u,v)` in the pivot
mass pairing. -/
theorem gelfandGalerkinQuadraticTerm_equation
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (t : ℝ) (u v : S) :
    inner ℝ
        (T.inclusion (gelfandGalerkinQuadraticTerm T S N t u : V))
        (T.inclusion (v : V)) =
      N t (u : V) (u : V) (v : V) := by
  have hmass :
      trialMassOperator T S (gelfandGalerkinQuadraticTerm T S N t u) =
        (toDual ℝ _).symm (restrictFunctional S (N t (u : V) (u : V))) := by
    exact (trialMassEquiv T S).apply_symm_apply _
  have hinner := congrArg (fun z : S ↦ inner ℝ z v) hmass
  simp only [trialMassOperator, continuousLinearMapOfBilin_apply,
    toDual_symm_apply, restrictFunctional_apply] at hinner
  exact hinner

/-- The quadratic mass-inverted field satisfies the projected weak equation
at every time. -/
theorem gelfandGalerkinQuadraticVectorField_equation
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u v : S) :
    inner ℝ
        (T.inclusion
          (gelfandGalerkinQuadraticVectorField T S A N ell t u : V))
        (T.inclusion (v : V)) +
        A t (u : V) (v : V) +
        N t (u : V) (u : V) (v : V) =
      ell t (v : V) := by
  have hlinear :=
    gelfandGalerkinVectorField_equation T S A ell t u v
  have hquadratic :=
    gelfandGalerkinQuadraticTerm_equation T S N t u v
  simp only [gelfandGalerkinQuadraticVectorField, Submodule.coe_sub,
    map_sub, inner_sub_left]
  linarith

/-- Quadratic growth: if `N(t)` is bounded by `C`, then
`‖M_S⁻¹ N(t)(u, u)‖ ≤ ‖M_S⁻¹‖ C ‖u‖²`. -/
theorem norm_gelfandGalerkinQuadraticTerm_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (t : ℝ) (u : S) {C : ℝ}
    (hN : (N t).IsBoundedBy C) (hC : 0 ≤ C) :
    ‖gelfandGalerkinQuadraticTerm T S N t u‖ ≤
      ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (C * ‖u‖ ^ 2) := by
  have hdual :
      ‖N t (u : V) (u : V)‖ ≤ C * ‖u‖ ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound
    · positivity
    intro w
    simpa [pow_two, mul_assoc] using
      hN.norm_apply_le (u : V) (u : V) w
  calc
    ‖gelfandGalerkinQuadraticTerm T S N t u‖ ≤
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          ‖(toDual ℝ _).symm (restrictFunctional S
            (N t (u : V) (u : V)))‖ :=
      (trialMassEquiv T S).symm.toContinuousLinearMap.le_opNorm _
    _ = ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ‖restrictFunctional S (N t (u : V) (u : V))‖ := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ‖N t (u : V) (u : V)‖ := by
      gcongr
      exact norm_restrictFunctional_le S _
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (C * ‖u‖ ^ 2) := by
      gcongr

/-- Local Lipschitz bound for the mass-inverted quadratic term `Q`: if `N(t)` is bounded by
`C`, then `‖Q(u) - Q(w)‖ ≤ ‖M_S⁻¹‖ C (‖u‖ + ‖w‖) ‖u - w‖`. -/
theorem norm_gelfandGalerkinQuadraticTerm_sub_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (t : ℝ) (u w : S) {C : ℝ}
    (hN : (N t).IsBoundedBy C) (hC : 0 ≤ C) :
    ‖gelfandGalerkinQuadraticTerm T S N t u -
        gelfandGalerkinQuadraticTerm T S N t w‖ ≤
      ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (C * (‖u‖ + ‖w‖) * ‖u - w‖) := by
  calc
    ‖gelfandGalerkinQuadraticTerm T S N t u -
        gelfandGalerkinQuadraticTerm T S N t w‖ =
        ‖(trialMassEquiv T S).symm
          ((toDual ℝ _).symm (restrictFunctional S
              (N t (u : V) (u : V))) -
            (toDual ℝ _).symm (restrictFunctional S
              (N t (w : V) (w : V))))‖ := by
      rw [map_sub]
      rfl
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ‖(toDual ℝ _).symm (restrictFunctional S
              (N t (u : V) (u : V))) -
          (toDual ℝ _).symm (restrictFunctional S
              (N t (w : V) (w : V)))‖ :=
      (trialMassEquiv T S).symm.toContinuousLinearMap.le_opNorm _
    _ = ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ‖restrictFunctional S
          (N t (u : V) (u : V) - N t (w : V) (w : V))‖ := by
      have hriesz :
          (toDual ℝ _).symm (restrictFunctional S
              (N t (u : V) (u : V))) -
              (toDual ℝ _).symm (restrictFunctional S
                (N t (w : V) (w : V))) =
            (toDual ℝ _).symm
              (restrictFunctional S (N t (u : V) (u : V)) -
                restrictFunctional S (N t (w : V) (w : V))) := by
        simp
      rw [hriesz, LinearIsometryEquiv.norm_map, ← restrictFunctional_sub]
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ‖N t (u : V) (u : V) - N t (w : V) (w : V)‖ := by
      gcongr
      exact norm_restrictFunctional_le S _
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (C * (‖u‖ + ‖w‖) * ‖u - w‖) := by
      gcongr
      apply ContinuousLinearMap.opNorm_le_bound
      · positivity
      intro z
      have hsplit :
          (N t (u : V) (u : V) - N t (w : V) (w : V)) z =
            N t ((u : V) - (w : V)) (u : V) z +
              N t (w : V) ((u : V) - (w : V)) z := by
        simp only [sub_apply, map_sub]
        ring
      rw [hsplit]
      calc
        ‖N t ((u : V) - (w : V)) (u : V) z +
            N t (w : V) ((u : V) - (w : V)) z‖ ≤
            ‖N t ((u : V) - (w : V)) (u : V) z‖ +
              ‖N t (w : V) ((u : V) - (w : V)) z‖ :=
          norm_add_le _ _
        _ ≤ C * ‖(u : V) - (w : V)‖ * ‖(u : V)‖ * ‖z‖ +
            C * ‖(w : V)‖ * ‖(u : V) - (w : V)‖ * ‖z‖ :=
          add_le_add
            (hN.norm_apply_le ((u : V) - (w : V)) (u : V) z)
            (hN.norm_apply_le (w : V) ((u : V) - (w : V)) z)
        _ = (C * (‖u‖ + ‖w‖) * ‖u - w‖) * ‖z‖ := by
          change
            C * ‖u - w‖ * ‖u‖ * ‖z‖ +
                C * ‖w‖ * ‖u - w‖ * ‖z‖ =
              (C * (‖u‖ + ‖w‖) * ‖u - w‖) * ‖z‖
          ring

/-- Growth of the quadratic Galerkin field:
`‖F(t, u)‖ ≤ ‖M_S⁻¹‖ (‖ℓ(t)‖ + ‖A(t)‖ ‖u‖ + C ‖u‖²)`. -/
theorem norm_gelfandGalerkinQuadraticVectorField_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u : S) {C : ℝ}
    (hN : (N t).IsBoundedBy C) (hC : 0 ≤ C) :
    ‖gelfandGalerkinQuadraticVectorField T S A N ell t u‖ ≤
      ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖ell t‖ + ‖A t‖ * ‖u‖ + C * ‖u‖ ^ 2) := by
  calc
    ‖gelfandGalerkinQuadraticVectorField T S A N ell t u‖ ≤
        ‖gelfandGalerkinVectorField T S A ell t u‖ +
          ‖gelfandGalerkinQuadraticTerm T S N t u‖ :=
      norm_sub_le _ _
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          (‖ell t‖ + ‖A t‖ * ‖u‖) +
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          (C * ‖u‖ ^ 2) :=
      add_le_add
        (norm_gelfandGalerkinVectorField_le T S A ell t u)
        (norm_gelfandGalerkinQuadraticTerm_le T S N t u hN hC)
    _ = ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖ell t‖ + ‖A t‖ * ‖u‖ + C * ‖u‖ ^ 2) := by
      ring

/-- Local Lipschitz bound for the quadratic Galerkin field at a fixed time:
`‖F(t, u) - F(t, w)‖ ≤ ‖M_S⁻¹‖ (‖A(t)‖ + C (‖u‖ + ‖w‖)) ‖u - w‖`. -/
theorem norm_gelfandGalerkinQuadraticVectorField_sub_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A : ℝ → V →L[ℝ] StrongDual ℝ V)
    (N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u w : S) {C : ℝ}
    (hN : (N t).IsBoundedBy C) (hC : 0 ≤ C) :
    ‖gelfandGalerkinQuadraticVectorField T S A N ell t u -
        gelfandGalerkinQuadraticVectorField T S A N ell t w‖ ≤
      ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖A t‖ + C * (‖u‖ + ‖w‖)) * ‖u - w‖ := by
  have hA :
      ‖gelfandGalerkinOperator T S (A t)‖ ≤
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ‖A t‖ :=
    norm_gelfandGalerkinOperator_le T S (A t)
  calc
    ‖gelfandGalerkinQuadraticVectorField T S A N ell t u -
        gelfandGalerkinQuadraticVectorField T S A N ell t w‖ ≤
        ‖gelfandGalerkinVectorField T S A ell t u -
            gelfandGalerkinVectorField T S A ell t w‖ +
          ‖gelfandGalerkinQuadraticTerm T S N t u -
            gelfandGalerkinQuadraticTerm T S N t w‖ := by
      have hsplit :
          gelfandGalerkinQuadraticVectorField T S A N ell t u -
              gelfandGalerkinQuadraticVectorField T S A N ell t w =
            (gelfandGalerkinVectorField T S A ell t u -
                gelfandGalerkinVectorField T S A ell t w) -
              (gelfandGalerkinQuadraticTerm T S N t u -
                gelfandGalerkinQuadraticTerm T S N t w) := by
        simp only [gelfandGalerkinQuadraticVectorField]
        abel
      rw [hsplit]
      exact norm_sub_le _ _
    _ ≤ ‖gelfandGalerkinOperator T S (A t)‖ * ‖u - w‖ +
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          (C * (‖u‖ + ‖w‖) * ‖u - w‖) :=
      add_le_add
        (norm_gelfandGalerkinVectorField_sub_le T S A ell t u w)
        (norm_gelfandGalerkinQuadraticTerm_sub_le T S N t u w hN hC)
    _ ≤ (‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ‖A t‖) *
          ‖u - w‖ +
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          (C * (‖u‖ + ‖w‖) * ‖u - w‖) := by
      gcongr
    _ = ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖A t‖ + C * (‖u‖ + ‖w‖)) * ‖u - w‖ := by
      ring

/-- If `N` is pointwise quadratic-continuous and bounded by `C` on `s` and `u` is continuous
on `s`, then `t ↦ M_S⁻¹ N(t)(u(t), u(t))` is continuous on `s`. -/
theorem continuousOn_gelfandGalerkinQuadraticTerm
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V}
    {u : ℝ → S} {s : Set ℝ} {C : ℝ}
    (hNcont : IsQuadraticPointwiseContinuousOn N s)
    (hNbound : ∀ t ∈ s, (N t).IsBoundedBy C)
    (hC : 0 ≤ C)
    (hu : ContinuousOn u s) :
    ContinuousOn
      (fun t ↦ gelfandGalerkinQuadraticTerm T S N t (u t)) s := by
  have huV : ContinuousOn (fun t ↦ (u t : V)) s :=
    S.subtypeL.continuous.comp_continuousOn hu
  have hdual : ContinuousOn
      (fun t ↦ N t (u t : V) (u t : V)) s :=
    continuousOn_quadratic_apply hNcont hNbound hC huV
  exact (trialMassEquiv T S).symm.continuous.comp_continuousOn
    ((toDual ℝ S).symm.continuous.comp_continuousOn
      (continuousOn_restrictFunctional S hdual))

/-- If moreover `A` and `ℓ` are continuous on `s`, then `t ↦ F(t, u(t))` is continuous on
`s`. -/
theorem continuousOn_gelfandGalerkinQuadraticVectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {A : ℝ → V →L[ℝ] StrongDual ℝ V}
    {N : ℝ → PDE.Analysis.ContinuousTrilinearForm V V V}
    {ell : ℝ → StrongDual ℝ V} {u : ℝ → S} {s : Set ℝ} {C : ℝ}
    (hA : ContinuousOn A s)
    (hNcont : IsQuadraticPointwiseContinuousOn N s)
    (hNbound : ∀ t ∈ s, (N t).IsBoundedBy C)
    (hC : 0 ≤ C)
    (hell : ContinuousOn ell s) (hu : ContinuousOn u s) :
    ContinuousOn
      (fun t ↦ gelfandGalerkinQuadraticVectorField T S A N ell t (u t)) s :=
  (continuousOn_gelfandGalerkinVectorField T S hA hell hu).sub
    (continuousOn_gelfandGalerkinQuadraticTerm
      T S hNcont hNbound hC hu)

end GelfandGalerkinQuadraticVectorField
end Galerkin

end PDE.Analysis.Evolution
