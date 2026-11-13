/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Action
public import PDE.Spaces.Sobolev.Calculus.Pullback.Isometry
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# The axisymmetry group acting on whole-space `H¹` velocities

`actH1 θ s` is the linear isometry equivalence `w ↦ g ∘ w ∘ g⁻¹` of `H¹(ℝ^3; ℝ^3)` for
`g = groupElement θ s` (`SobolevSpace.GraphSpace.velocityIsometry`). Its representative is the
pointwise action of the representative (`representative_actH1`), an `H¹` velocity is determined
by its representative, and the even and odd whole-space sectors are exactly the fixed fields of
the action and the fields on which it acts by the character `parity`
(`mem_evenSectorH1_iff_actH1`, `mem_oddSectorH1_iff_actH1`), that is the common kernels of the
continuous linear constraints `sectorConstraint odd`, which pass to limits of approximate
corrections (`Stationary.exists_correction_of_eventually_tested_eq_of_constraints`).
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace NavierStokes.Nonuniqueness
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

local notation "H" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- The action of a group element on whole-space `H¹` velocities, `w ↦ g ∘ w ∘ g⁻¹`. -/
def actH1 (θ : ℝ) (s : Bool) : H ≃ₗᵢ[ℝ] H :=
  velocityIsometry (groupElement θ s) (isIsometryInvariant_univ _) isOpen_univ

/-- An `H¹` velocity is determined by the almost-everywhere class of its representative. -/
theorem eq_of_representative_ae {w v : H}
    (h : Stationary.representative w =ᵐ[volume] Stationary.representative v) : w = v := by
  ext1 i
  refine wkpBaseCoordinateCLM_injective isOpen_univ (Lp.ext ?_)
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [h] with x hx
  have := congrArg (fun z : ℝ^3 ↦ z i) hx
  simpa only [Stationary.representative_apply, Stationary.massCLM_apply,
    wkpBaseCoordinateCLM_apply] using this

/-- The representative of the transformed velocity is the pointwise action of the
representative. -/
theorem representative_actH1 (θ : ℝ) (s : Bool) (w : H) :
    Stationary.representative (actH1 θ s w) =ᵐ[volume]
      act θ s (Stationary.representative w) := by
  set g := groupElement θ s
  have hg := isIsometryInvariant_univ g
  have hcoord (i : Fin 3) :
      ((actH1 θ s w i : H¹(ℝ^3)) : WkpAmbientOn 3 1 2 Set.univ) (baseIndex 3 1) =
        ∑ k, (g (EuclideanSpace.single k 1)) i •
          l2CompSymm g hg ((w k : WkpAmbientOn 3 1 2 Set.univ) (baseIndex 3 1)) := by
    change ((velocityIsometry g hg isOpen_univ w i : H¹(ℝ^3)) : WkpAmbientOn 3 1 2 Set.univ)
      (baseIndex 3 1) = _
    rw [velocityIsometry_apply]
    simp [h1CompSymmCLM_coe, h1CompSymmAmbient_base]
  have hsum (i : Fin 3) := Lp.coeFn_fun_finsetSum Finset.univ (fun k ↦
    (g (EuclideanSpace.single k 1)) i •
      l2CompSymm g hg ((w k : WkpAmbientOn 3 1 2 Set.univ) (baseIndex 3 1)))
  have hsmul (i k : Fin 3) := Lp.coeFn_smul ((g (EuclideanSpace.single k 1)) i)
    (l2CompSymm g hg ((w k : WkpAmbientOn 3 1 2 Set.univ) (baseIndex 3 1)))
  have hcomp (k : Fin 3) := l2CompSymm_ae g hg ((w k : WkpAmbientOn 3 1 2 Set.univ)
    (baseIndex 3 1))
  simp only [domainMeasure, Measure.restrict_univ] at hsum hsmul hcomp
  filter_upwards [ae_all_iff.mpr hsum, ae_all_iff.mpr fun i ↦ ae_all_iff.mpr (hsmul i),
    ae_all_iff.mpr hcomp] with x hx hsx hcx
  ext i
  rw [Stationary.representative_apply, Stationary.massCLM_apply, wkpBaseCoordinateCLM_apply,
    hcoord i, hx i, act_apply, linearIsometryEquiv_apply_coord]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hsx i k, Pi.smul_apply, hcx k, smul_eq_mul, mul_comm]
  rfl

/-- The action equals a given velocity exactly when the representatives agree almost
everywhere. -/
theorem actH1_eq_iff {θ : ℝ} {s : Bool} {w v : H} :
    actH1 θ s w = v ↔
      act θ s (Stationary.representative w) =ᵐ[volume] Stationary.representative v := by
  constructor
  · rintro rfl
    exact (representative_actH1 θ s w).symm
  · intro h
    exact eq_of_representative_ae ((representative_actH1 θ s w).trans h)

/-- The even whole-space sector consists of the fields fixed by every group element. -/
theorem mem_evenSectorH1_iff_actH1 {w : H} :
    w ∈ evenSectorH1 ↔ ∀ θ s, actH1 θ s w = w := by
  rw [mem_evenSectorH1_iff, isEvenAxisymmetric_iff_act]
  exact forall₂_congr fun θ s ↦ actH1_eq_iff.symm

/-- The odd whole-space sector consists of the fields on which every group element acts by the
character `parity`. -/
theorem mem_oddSectorH1_iff_actH1 {w : H} :
    w ∈ oddSectorH1 ↔ ∀ θ s, actH1 θ s w = parity s • w := by
  rw [mem_oddSectorH1_iff, isOddAxisymmetric_iff_act]
  refine forall₂_congr fun θ s ↦ ?_
  rw [actH1_eq_iff]
  constructor
  · intro h
    exact h.trans (Stationary.representative_smul_ae (parity s) w).symm
  · intro h
    exact h.trans (Stationary.representative_smul_ae (parity s) w)

/-- The continuous linear constraints `actH1 θ s - parity (odd && s) • id`, indexed by the group
elements, that cut out the whole-space sector of parity `odd`. -/
def sectorConstraint (odd : Bool) (p : ℝ × Bool) : H →L[ℝ] H :=
  (actH1 p.1 p.2).toContinuousLinearEquiv.toContinuousLinearMap -
    parity (odd && p.2) • ContinuousLinearMap.id ℝ H

/-- The even whole-space sector is the common kernel of the constraints of parity `false`. -/
theorem mem_evenSectorH1_iff_sectorConstraint {w : H} :
    w ∈ evenSectorH1 ↔ ∀ p, sectorConstraint false p w = 0 := by
  simp only [mem_evenSectorH1_iff_actH1, sectorConstraint, Prod.forall, Bool.false_and,
    parity_false, one_smul, sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  rfl

/-- The odd whole-space sector is the common kernel of the constraints of parity `true`. -/
theorem mem_oddSectorH1_iff_sectorConstraint {w : H} :
    w ∈ oddSectorH1 ↔ ∀ p, sectorConstraint true p w = 0 := by
  simp only [mem_oddSectorH1_iff_actH1, sectorConstraint, Prod.forall, Bool.true_and,
    sub_apply, smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  rfl

end NavierStokes.Symmetry
