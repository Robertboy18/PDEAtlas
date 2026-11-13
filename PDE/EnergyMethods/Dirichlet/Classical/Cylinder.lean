/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy.Cylinder.Closure
public import PDE.EnergyMethods.Dirichlet.Classical.ZeroBoundary

/-!
# Dirichlet energy along a classical cylinder

The derivative of the spatial Dirichlet energy pairs the spatial Laplacian with
the time derivative. C² regularity up to the boundary gives continuous first jets
and integrability, and zero lateral values give a zero time trace. Heat and wave
energy arguments both use this calculation.

Half of this derivative is the term `∫ Dw · Dw_t dx` in the computation of `Ė(t)` in the proof
of Evans, §2.4.3(a), Theorem 5, where it becomes `-∫ w_t Δw dx` because there is no boundary term.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3(a), Theorem 5 (Uniqueness for wave equation) and
  its proof, pp. 82-83.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.EnergyMethods

open MeasureTheory PDE.Common PDE.Analysis Set SobolevSpace Filter
open scoped Topology Gradient

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {a b : ℝ}
  {u : ℝ^(n + 1) → ℝ}

/-- Differentiate the spatial Dirichlet energy from the mixed C² jet and
constant zero lateral values. The continuous time trace vanishes on the boundary,
so integration by parts needs no third derivative or equation hypothesis. -/
theorem hasDerivAt_dirichletEnergy_of_zero_boundary
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s ↦ ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons s y)) x‖ ^ 2)
      (-2 * ∫ x in Ω, laplacian (fun y ↦ u (timeSpaceCons t y)) x *
        (∂[0] u) (timeSpaceCons t x)) t := by
  classical
  have hQ : IsOpen (spaceTimeCylinder Ω (Ioo a b)) := isOpen_spaceTimeCylinder hΩ isOpen_Ioo
  let hj (i : Fin (n + 1)) := hu.partialDeriv_of_succ hQ i
  let J (i : Fin (n + 1)) := (hj i).continuousRepresentative
  have hJc (i : Fin (n + 1)) : Continuous (J i) :=
    (hj i).continuous_continuousRepresentative
  have hJreg (i : Fin (n + 1)) :
      ContDiffUpToBoundary 1 (J i) (spaceTimeCylinder Ω (Ioo a b)) :=
    (hj i).regular_continuousRepresentative hQ
  have hJeq (i : Fin (n + 1)) : EqOn (J i) (∂[i] u)
      (spaceTimeCylinder Ω (Ioo a b)) := (hj i).continuousRepresentative_eqOn
  have hslice {s : ℝ} (hs : s ∈ Ioo a b) :=
    hu.spaceSlice hΩ isOpen_Ioo hs
  have hJspace (i : Fin n) {s : ℝ} (hs : s ∈ Ioo a b) {x : ℝ^n} (hx : x ∈ Ω) :
      J i.succ (timeSpaceCons s x) = (∂[i] (fun y ↦ u (timeSpaceCons s y))) x := by
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hx⟩
    rw [hJeq i.succ hp]
    exact (partialDeriv_timeSpaceCons_spatial i u s x
      ((hu.contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))).symm
  have hN {s : ℝ} (hs : s ∈ Ioo a b) :
      (∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons s y)) x‖ ^ 2) =
        ∑ i : Fin n, ∫ x in Ω, J i.succ (timeSpaceCons s x) ^ 2 := by
    have hint (i : Fin n) : IntegrableOn (fun x ↦ J i.succ (timeSpaceCons s x) ^ 2) Ω := by
      have hr := (hJreg i.succ).spaceSlice hΩ isOpen_Ioo hs
      simpa only [pow_two] using (hr.mul hr hΩ hbounded).integrableOn hΩ hbounded
    rw [← integral_finsetSum Finset.univ (fun i _ ↦ hint i)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [gradient_apply_eq_partialDeriv, hJspace _ hs hx]
  have hd (i : Fin n) := hasDerivAt_integral_sq_of_cylinder_closure hΩ hbounded
    (hJreg i.succ) (hJc i.succ).continuousOn ht
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hd i)
  have hNeq : (fun s ↦ ∫ x in Ω, ‖∇ (fun y ↦ u (timeSpaceCons s y)) x‖ ^ 2) =ᶠ[𝓝 t]
      fun s ↦ ∑ i : Fin n, ∫ x in Ω, J i.succ (timeSpaceCons s x) ^ 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hN hs
  have hder := hsum.congr_of_eventuallyEq hNeq
  let v : ℝ^n → ℝ := fun x ↦ J 0 (timeSpaceCons t x)
  have hv : ContDiffUpToBoundary 1 v Ω := (hJreg 0).spaceSlice hΩ isOpen_Ioo ht
  have hvc : Continuous v :=
    (hJc 0).comp (contDiff_timeSpaceCons_spatial n t (m := 0)).continuous
  have hvzero : ∀ x ∈ frontier Ω, v x = 0 := fun x hx ↦
    (hu.of_le (by omega)).timePartial_extension_eq_zero_on_frontier
      hΩ hbounded hc (hJc 0).continuousOn (hJeq 0) hzero hx ht
  have hmixed (i : Fin n) {x : ℝ^n} (hx : x ∈ Ω) :
      (∂[0] (J i.succ)) (timeSpaceCons t x) = (∂[i] v) x := by
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩
    have heqi := (hJeq i.succ).eventuallyEq_of_mem (hQ.mem_nhds hp)
    have heq0 := (hJeq 0).eventuallyEq_of_mem (hQ.mem_nhds hp)
    calc
      _ = (∂[0] (∂[i.succ] u)) (timeSpaceCons t x) :=
        congrArg (fun f : ℝ^(n + 1) →L[ℝ] ℝ ↦ f (EuclideanSpace.single 0 1))
          (heqi.fderiv_eq (𝕜 := ℝ))
      _ = (∂[i.succ] (∂[0] u)) (timeSpaceCons t x) :=
        partialDeriv_partialDeriv_comm_at 0 i.succ
          (hu.contDiffOn.contDiffAt (hQ.mem_nhds hp))
      _ = (∂[i.succ] (J 0)) (timeSpaceCons t x) :=
        (congrArg (fun f : ℝ^(n + 1) →L[ℝ] ℝ ↦ f (EuclideanSpace.single i.succ 1))
          (heq0.fderiv_eq (𝕜 := ℝ))).symm
      _ = (∂[i] v) x :=
        (partialDeriv_timeSpaceCons_spatial i (J 0) t x
          (((hJreg 0).contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt
            (by simp))).symm
  have hprod (i : Fin n) :
      (∫ x in Ω, J i.succ (timeSpaceCons t x) * (∂[0] (J i.succ)) (timeSpaceCons t x)) =
        ∫ x in Ω, (∂[i] (fun y ↦ u (timeSpaceCons t y))) x * (∂[i] v) x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [hJspace i ht hx, hmixed i hx]
  have hIBP := sum_integral_partialDeriv_mul_eq_neg_integral_laplacian_mul
    hΩ hbounded hgraph (hslice ht) hv hvc.continuousOn hvzero
  have hlast : (∫ x in Ω, laplacian (fun y ↦ u (timeSpaceCons t y)) x * v x) =
      ∫ x in Ω, laplacian (fun y ↦ u (timeSpaceCons t y)) x *
        (∂[0] u) (timeSpaceCons t x) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    rw [show v x = (∂[0] u) (timeSpaceCons t x) from
      hJeq 0 (timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩)]
  simp only [hprod, ← Finset.mul_sum, hIBP, hlast] at hder
  convert hder using 1
  ring

end PDE.EnergyMethods
