/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.Cylinder
public import PDE.FDeriv.SpaceTime
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Representative
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Algebra
public import PDE.Analysis.Calculus.Jet.ParameterTrace

/-!
# Classical closure jets on spacetime cylinders

Finite joint regularity restricts to the same finite spatial regularity on every
interior time slice. The continuous representative of the time partial has its
boundary values determined by the boundary time curve.
-/

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open PDE.Common Set

variable {n k : ℕ} {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^(n + 1) → ℝ}

/-- Joint classical closure regularity restricts to each interior spatial slice. -/
theorem spaceSlice (hu : ContDiffUpToBoundary k u (spaceTimeCylinder Ω I))
    (hΩ : IsOpen Ω) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I) :
    ContDiffUpToBoundary k (fun x ↦ u (timeSpaceCons t x)) Ω := by
  have hmap : MapsTo (timeSpaceCons t) Ω (spaceTimeCylinder Ω I) :=
    fun _ hx ↦ timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩
  have huc : UniformContinuous (timeSpaceCons (n := n) t) :=
    (timeSpaceContinuousLinearEquiv n).symm.toContinuousLinearMap.uniformContinuous.comp
      (uniformContinuous_const.prodMk uniformContinuous_id)
  induction k generalizing u with
  | zero =>
    exact of_uniformContinuousOn
      ((hu.uniformContinuousOn [] (Nat.zero_le _)).comp huc.uniformContinuousOn hmap)
  | succ k ih =>
    apply of_partialDeriv
      (hu.contDiffOn.comp (contDiff_timeSpaceCons_spatial n t).contDiffOn hmap)
      ((hu.uniformContinuousOn [] (Nat.zero_le _)).comp huc.uniformContinuousOn hmap)
    intro i
    apply (ih (hu.partialDeriv_of_succ (isOpen_spaceTimeCylinder hΩ hI) i.succ)).congr hΩ
    intro x hx
    exact PDE.partialDeriv_timeSpaceCons_spatial i u t x
      ((hu.contDiffOn.contDiffAt
        ((isOpen_spaceTimeCylinder hΩ hI).mem_nhds (hmap hx))).differentiableAt (by simp))

/-- A continuous spacetime representative restricts continuously to the closed
product of the spatial and time closures. -/
theorem continuousOn_uncurry_closure
    (hu : ContinuousOn u (closure (spaceTimeCylinder Ω I))) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦ u (timeSpaceCons p.2 p.1))
      (closure Ω ×ˢ closure I) := by
  apply hu.comp (spaceTimeContinuousLinearEquiv n).symm.continuous.continuousOn
  intro p hp
  rw [closure_spaceTimeCylinder]
  exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hp.2, hp.1⟩

/-- The continuous extension of the time partial vanishes on a lateral boundary
where the values are constant in time. The ambient boundary derivative
is not used. -/
theorem timePartial_extension_eq_zero_on_frontier
    {a b : ℝ} (hu : ContDiffUpToBoundary 1 u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    {D : ℝ^(n + 1) → ℝ}
    (hD : ContinuousOn D (closure (spaceTimeCylinder Ω (Ioo a b))))
    (heq : EqOn D (∂[0] u) (spaceTimeCylinder Ω (Ioo a b)))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    {x : ℝ^n} (hx : x ∈ frontier Ω) {t : ℝ} (ht : t ∈ Ioo a b) :
    D (timeSpaceCons t x) = 0 := by
  have hab : a < b := ht.1.trans ht.2
  have huc := continuousOn_uncurry_closure hc
  have hDc := continuousOn_uncurry_closure hD
  rw [closure_Ioo hab.ne] at huc hDc
  refine PDE.Analysis.parameterDerivative_eq_zero_of_constant
    (F := fun y s ↦ u (timeSpaceCons s y)) (D := fun y s ↦ D (timeSpaceCons s y))
    (c := 0) hbounded.isCompact_closure huc hDc ?_ (frontier_subset_closure hx) ?_ ht
  · intro y hy s hs
    have hp : timeSpaceCons s y ∈ spaceTimeCylinder Ω (Ioo a b) :=
      timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hy⟩
    rw [heq hp]
    exact PDE.hasDerivAt_timeSpaceCons u s y
      ((hu.contDiffOn.contDiffAt
        ((isOpen_spaceTimeCylinder hΩ isOpen_Ioo).mem_nhds hp)).differentiableAt (by simp))
  · exact fun s hs ↦ hzero x hx s (Ioo_subset_Icc_self hs)

end SobolevSpace.ContDiffUpToBoundary
