/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.EnergyMethods.Dirichlet.Classical.Cylinder
public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Cylinder.InitialTrace
import PDE.FDeriv.Calculus

/-!
# Classical wave energy on a bounded cylinder

The continuous representatives of the first partials define energy at both
endpoint times. In the open cylinder they are the derivatives themselves. The wave
equation cancels the kinetic and spatial energy derivatives; the spatial term
uses the shared Dirichlet identity.
-/

open scoped Gradient

@[expose] public noncomputable section

open PDE (laplacian)

namespace WaveEquation.Dirichlet

open MeasureTheory PDE.Common PDE.Analysis Set SobolevSpace Filter
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^(n + 1) → ℝ}

/-- Twice the usual wave energy, including the continuous first jets at the
endpoint times. The representatives are constructed from C² closure data. -/
def firstJetEnergy
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω) (t : ℝ) : ℝ :=
  ∑ i : Fin (n + 1), ∫ x in Ω,
    (hu.partialDeriv_of_succ (isOpen_spaceTimeCylinder hΩ isOpen_Ioo) i).continuousRepresentative
      (timeSpaceCons t x) ^ 2

/-- The energy of the continuous first jet is continuous on the closed time interval. -/
theorem continuousOn_firstJetEnergy (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b) :
    ContinuousOn (firstJetEnergy hu hΩ) (Icc a b) := by
  apply continuousOn_finsetSum
  intro i _
  have h := (hu.partialDeriv_of_succ (isOpen_spaceTimeCylinder hΩ isOpen_Ioo) i)
  exact continuousOn_integral_sq_of_cylinder_closure hΩ hbounded hab
    h.continuous_continuousRepresentative.continuousOn

/-- Zero initial displacement and right velocity give zero initial energy. -/
theorem firstJetEnergy_initial_eq_zero
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hpos : ∀ x ∈ Ω, u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Ω, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici a) a = 0) :
    firstJetEnergy hu hΩ a = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [hu.continuousRepresentative_partialDeriv_initial_eq_zero
    hab hΩ hbounded hc hpos hvel i hx, zero_pow (by decide : 2 ≠ 0)]
  rfl

/-- Homogeneous waves with zero lateral values conserve the first-jet energy.
Only second derivatives on the open cylinder are differentiated. -/
theorem hasDerivAt_firstJetEnergy [Fact (0 < n)]
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b))) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, waveOperator u (timeSpaceCons t x) = 0) {t : ℝ}
    (ht : t ∈ Ioo a b) :
    HasDerivAt (firstJetEnergy hu hΩ) 0 t := by
  classical
  have hQ := isOpen_spaceTimeCylinder (I := Ioo a b) hΩ isOpen_Ioo
  let hj (i : Fin (n + 1)) := hu.partialDeriv_of_succ hQ i
  let J (i : Fin (n + 1)) := (hj i).continuousRepresentative
  have hJc (i : Fin (n + 1)) : Continuous (J i) := (hj i).continuous_continuousRepresentative
  have hJreg (i : Fin (n + 1)) : ContDiffUpToBoundary 1 (J i) (spaceTimeCylinder Ω (Ioo a b)) :=
    (hj i).regular_continuousRepresentative hQ
  have hJeq (i : Fin (n + 1)) : EqOn (J i) (∂[i] u) (spaceTimeCylinder Ω (Ioo a b)) :=
    (hj i).continuousRepresentative_eqOn
  have hkin := hasDerivAt_integral_sq_of_cylinder_closure hΩ hbounded
    (hJreg 0) (hJc 0).continuousOn ht
  have hspace := PDE.EnergyMethods.hasDerivAt_dirichletEnergy_of_zero_boundary
    hΩ hbounded hgraph hu hc hzero ht
  have heq : (firstJetEnergy hu hΩ) =ᶠ[𝓝 t] fun s ↦ (∫ x in Ω, J 0 (timeSpaceCons s x) ^ 2) +
        ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons s y)) x‖ ^ 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [firstJetEnergy, Fin.sum_univ_succ]
    congr 1
    have hint (i : Fin n) : IntegrableOn (fun x ↦ J i.succ (timeSpaceCons s x) ^ 2) Ω := by
      have hr := (hJreg i.succ).spaceSlice hΩ isOpen_Ioo hs
      simpa only [pow_two] using (hr.mul hr hΩ hbounded).integrableOn hΩ hbounded
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ hint i)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hx⟩
    rw [PDE.gradient_apply_eq_partialDeriv, PDE.partialDeriv_timeSpaceCons_spatial i u s x
      ((hu.contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))]
    rw [hJeq i.succ hp]
  have hcancel : (∫ x in Ω, J 0 (timeSpaceCons t x) * (∂[0] (J 0)) (timeSpaceCons t x)) =
        ∫ x in Ω, laplacian (fun y ↦ u (timeSpaceCons t y)) x *
          (∂[0] u) (timeSpaceCons t x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩
    have hlocal := hu.contDiffOn.contDiffAt (hQ.mem_nhds hp)
    rw [hJeq 0 hp, PDE.partialDeriv_congr_nhds 0 ((hJeq 0).eventuallyEq_of_mem (hQ.mem_nhds hp))]
    have h := hPDE x hx t ht
    rw [waveOperator, ← laplacian_timeSlice_of_contDiffAt u t x hlocal, sub_eq_zero] at h
    rw [h, mul_comm]
  have hd := (hkin.add hspace).congr_of_eventuallyEq heq
  rw [hcancel] at hd
  convert hd using 1
  ring

end WaveEquation.Dirichlet
