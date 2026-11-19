/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Gelfand.Mass
public import PDE.Analysis.Evolution.Galerkin.Restriction

/-!
# Gelfand Galerkin vector fields

Let `S` be a finite-dimensional trial subspace of the energy space of a Gelfand triple
`V ↪ H`, and let `M_S : S → S` be its pivot mass operator. Restricting a form
`B(t) : V → V*` and a load `ℓ(t) ∈ V*` to `S` and representing them by Riesz in `S` gives a
stiffness operator `A_S(t)` and a vector `r_S(t)`. The Galerkin vector field is

`F(t, u) = M_S⁻¹ (r_S(t) - A_S(t) u)`,

and it satisfies the projected equation `⟪ι F(t, u), ι v⟫_H + B(t)(u, v) = ℓ(t)(v)` for every
`v ∈ S`. We prove the affine growth bound `‖F(t, u)‖ ≤ ‖M_S⁻¹‖ (‖ℓ(t)‖ + ‖B(t)‖ ‖u‖)`, the
Lipschitz bound in `u`, and continuity of `t ↦ F(t, u(t))` when `B`, `ℓ` and `u` are
continuous.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, equations (14)-(16) and the proof of Theorem 1.
  <https://doi.org/10.1090/gsm/019>
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
section GelfandGalerkinMass

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The mass-inverted stiffness operator `M_S⁻¹ A_S : S → S`, where `A_S` is the Riesz
representative in `S` of the restriction of `B` to `S`. -/
def gelfandGalerkinOperator
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) : S →L[ℝ] S :=
  (trialMassEquiv T S).symm.toContinuousLinearMap.comp
    (continuousLinearMapOfBilin (restrictForm S B))

/-- `‖M_S⁻¹ A_S‖ ≤ ‖M_S⁻¹‖ ‖B‖`. -/
theorem norm_gelfandGalerkinOperator_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) :
    ‖gelfandGalerkinOperator T S B‖ ≤
      ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ‖B‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg
      (norm_nonneg (trialMassEquiv T S).symm.toContinuousLinearMap)
      (norm_nonneg B))
    fun u ↦ ?_
  calc
    ‖gelfandGalerkinOperator T S B u‖ ≤
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          ‖continuousLinearMapOfBilin (restrictForm S B) u‖ :=
      (trialMassEquiv T S).symm.toContinuousLinearMap.le_opNorm _
    _ = ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        ‖restrictForm S B u‖ := by
      congr 1
      exact (toDual ℝ S).symm.norm_map (restrictForm S B u)
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖B‖ * ‖u‖) := by
      gcongr
      exact norm_restrictForm_apply_le S B u
    _ = (‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * ‖B‖) * ‖u‖ := by
      ring

/-- The mass-inverted forcing `t ↦ M_S⁻¹ r_S(t)`, where `r_S(t)` is the Riesz
representative in `S` of the restriction of `ℓ(t)` to `S`. -/
def gelfandGalerkinForcing
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (ell : ℝ → StrongDual ℝ V) : ℝ → S :=
  fun t ↦ (trialMassEquiv T S).symm
    ((toDual ℝ _).symm (restrictFunctional S (ell t)))

/-- `M_S (M_S⁻¹ (r_S - A_S u)) = r_S - A_S u`. -/
theorem trialMassOperator_gelfandVectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V) (u : S) :
    trialMassOperator T S
        ((trialMassEquiv T S).symm
          ((toDual ℝ _).symm (restrictFunctional S ell) -
            continuousLinearMapOfBilin (restrictForm S B) u)) =
      (toDual ℝ _).symm (restrictFunctional S ell) -
        continuousLinearMapOfBilin (restrictForm S B) u := by
  exact (trialMassEquiv T S).apply_symm_apply _

/-- The vector `d = M_S⁻¹ (r_S - A_S u)` satisfies the projected Galerkin equation
`⟪ι d, ι v⟫_H + B(u, v) = ℓ(v)` for every `v ∈ S` (Evans §7.1.2, equation (16)). -/
theorem gelfandVectorField_equation
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V) (u : S) :
    let d := (trialMassEquiv T S).symm
      ((toDual ℝ _).symm (restrictFunctional S ell) -
        continuousLinearMapOfBilin (restrictForm S B) u)
    ∀ v : S,
      inner ℝ (T.inclusion (d : V)) (T.inclusion (v : V)) +
        B (u : V) (v : V) = ell (v : V) := by
  dsimp only
  intro v
  have hm := congrArg (fun z : S ↦ inner ℝ z v)
    (trialMassOperator_gelfandVectorField T S B ell u)
  simp only [inner_sub_left, continuousLinearMapOfBilin_apply,
    toDual_symm_apply, restrictFunctional_apply, trialMassOperator] at hm
  change inner ℝ (T.inclusion _) (T.inclusion (v : V)) =
    ell (v : V) - B (u : V) (v : V) at hm
  exact eq_sub_iff_add_eq.mp hm

/-- The nonautonomous Galerkin vector field `F(t, u) = M_S⁻¹ (r_S(t) - A_S(t) u)` on `S`.
Both the form and the forcing may depend on time, as in Evans §7.1.2. -/
def gelfandGalerkinVectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) : ℝ → S → S :=
  fun t u ↦ (trialMassEquiv T S).symm
    ((toDual ℝ _).symm (restrictFunctional S (ell t)) -
      continuousLinearMapOfBilin (restrictForm S (B t)) u)

/-- At every time, `⟪ι F(t, u), ι v⟫_H + B(t)(u, v) = ℓ(t)(v)` for every `v ∈ S`. -/
theorem gelfandGalerkinVectorField_equation
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u : S) :
    ∀ v : S,
      inner ℝ
          (T.inclusion (gelfandGalerkinVectorField T S B ell t u : V))
          (T.inclusion (v : V)) +
        B t (u : V) (v : V) = ell t (v : V) :=
  gelfandVectorField_equation T S (B t) (ell t) u

/-- Affine growth of the Galerkin field: `‖F(t, u)‖ ≤ ‖M_S⁻¹‖ (‖ℓ(t)‖ + ‖B(t)‖ ‖u‖)`. -/
theorem norm_gelfandGalerkinVectorField_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u : S) :
    ‖gelfandGalerkinVectorField T S B ell t u‖ ≤
      ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖ell t‖ + ‖B t‖ * ‖u‖) := by
  calc
    ‖gelfandGalerkinVectorField T S B ell t u‖ ≤
        ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
          ‖(toDual ℝ _).symm (restrictFunctional S (ell t)) -
            continuousLinearMapOfBilin (restrictForm S (B t)) u‖ :=
      (trialMassEquiv T S).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖restrictFunctional S (ell t)‖ +
          ‖restrictForm S (B t) u‖) := by
      gcongr
      simpa [continuousLinearMapOfBilin] using
        norm_sub_le ((toDual ℝ _).symm (restrictFunctional S (ell t)))
          (continuousLinearMapOfBilin (restrictForm S (B t)) u)
    _ ≤ ‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ *
        (‖ell t‖ + ‖B t‖ * ‖u‖) := by
      gcongr
      · exact norm_restrictFunctional_le S (ell t)
      · exact norm_restrictForm_apply_le S (B t) u

/-- Lipschitz bound in the state: `‖F(t, u) - F(t, w)‖ ≤ ‖M_S⁻¹ A_S(t)‖ ‖u - w‖`. -/
theorem norm_gelfandGalerkinVectorField_sub_le
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (t : ℝ) (u w : S) :
    ‖gelfandGalerkinVectorField T S B ell t u -
        gelfandGalerkinVectorField T S B ell t w‖ ≤
      ‖gelfandGalerkinOperator T S (B t)‖ * ‖u - w‖ := by
  have hfield (z : S) : gelfandGalerkinVectorField T S B ell t z =
      gelfandGalerkinForcing T S ell t -
        gelfandGalerkinOperator T S (B t) z := by
    simp [gelfandGalerkinVectorField, gelfandGalerkinForcing,
      gelfandGalerkinOperator, map_sub]
  rw [hfield u, hfield w]
  rw [sub_sub_sub_cancel_left, ← map_sub]
  calc
    ‖gelfandGalerkinOperator T S (B t) (w - u)‖ ≤
        ‖gelfandGalerkinOperator T S (B t)‖ * ‖w - u‖ :=
      (gelfandGalerkinOperator T S (B t)).le_opNorm (w - u)
    _ = ‖gelfandGalerkinOperator T S (B t)‖ * ‖u - w‖ := by
      rw [norm_sub_rev]

/-- The constant `‖M_S⁻¹‖ · M_B`. It is a Lipschitz constant of `F(t, ·)` at every time
with `‖B(t)‖ ≤ M_B`. -/
def gelfandGalerkinLipschitzBound
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S] (MB : NNReal) : NNReal :=
  ⟨‖(trialMassEquiv T S).symm.toContinuousLinearMap‖ * (MB : ℝ),
    mul_nonneg
      (norm_nonneg ((trialMassEquiv T S).symm.toContinuousLinearMap : S →L[ℝ] S))
      MB.2⟩

/-- If `B`, `ℓ` and `u` are continuous on `s`, then so is `t ↦ F(t, u(t))`. -/
theorem continuousOn_gelfandGalerkinVectorField
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    {B : ℝ → V →L[ℝ] StrongDual ℝ V} {ell : ℝ → StrongDual ℝ V}
    {u : ℝ → S} {s : Set ℝ} (hB : ContinuousOn B s)
    (hell : ContinuousOn ell s)
    (hu : ContinuousOn u s) :
    ContinuousOn (fun t ↦ gelfandGalerkinVectorField T S B ell t (u t)) s := by
  have huV : ContinuousOn (fun t ↦ (u t : V)) s :=
    S.subtypeL.continuous.comp_continuousOn hu
  have hspatial : ContinuousOn
      (fun t ↦ continuousLinearMapOfBilin (restrictForm S (B t)) (u t)) s := by
    have hrestricted : ContinuousOn
        (fun t ↦ restrictFunctional S (B t (u t : V))) s :=
      continuousOn_restrictFunctional S (hB.clm_apply huV)
    apply (isometry_subtype_coe.comp_continuousOn_iff).mp
    change ContinuousOn
      (fun t ↦ ((continuousLinearMapOfBilin (restrictForm S (B t)) (u t) : S) : V)) s
    have hriesz : ContinuousOn
        (fun t ↦ (((toDual ℝ S).symm
          (restrictFunctional S (B t (u t : V))) : S) : V)) s := by
      exact
        (S.subtypeL.continuous.comp
          (toDual ℝ S).symm.continuous).comp_continuousOn hrestricted
    change ContinuousOn
      (fun t ↦ (((toDual ℝ S).symm (restrictForm S (B t) (u t)) : S) : V)) s
    simpa only [restrictForm_apply_eq_restrictFunctional] using hriesz
  apply (trialMassEquiv T S).symm.continuous.comp_continuousOn
  exact ((toDual ℝ S).symm.continuous.comp_continuousOn
      (continuousOn_restrictFunctional S hell)).sub
    hspatial

end GelfandGalerkinMass

end Galerkin

end PDE.Analysis.Evolution
