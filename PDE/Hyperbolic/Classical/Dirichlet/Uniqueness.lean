/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.Dirichlet.ZeroData

/-!
# Classical wave uniqueness on a bounded cylinder

Evans, §2.4.3, Theorem 5, gives uniqueness for the bounded-domain wave problem (45). Here both
solutions have joint `C²` closure data. Their values, initial right velocities, and common
forcing are arbitrary. The energy argument is applied to their difference.

The conclusion includes both time faces and spatial corners. Right differentiability is derived
before subtracting the initial `derivWithin` expressions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3, Theorem 5 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Common Set SobolevSpace

/-- Two classical solutions with common forcing, lateral values, initial
displacement, and right velocity agree on the entire closed cylinder. -/
theorem eq_on_closedCylinder_of_initial_eq {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {u v f : ℝ^(n + 1) → ℝ}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hab : a < b) (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b)))
    (hv : ContDiffUpToBoundary 2 v (spaceTimeCylinder Ω (Ioo a b)))
    (huc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hvc : ContinuousOn v (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hPu : SatisfiesPDEProblem (nonhomogeneousWaveEquation (spaceTimeCylinder Ω (Ioo a b)) f) u)
    (hPv : SatisfiesPDEProblem (nonhomogeneousWaveEquation (spaceTimeCylinder Ω (Ioo a b)) f) v)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = v (timeSpaceCons t x))
    (hpos : ∀ x ∈ Ω, u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvel : ∀ x ∈ Ω, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici a) a =
      derivWithin (fun s ↦ v (timeSpaceCons s x)) (Ici a) a) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  have hQ := isOpen_spaceTimeCylinder (I := Ioo a b) hΩ isOpen_Ioo
  have hw : ContDiffUpToBoundary 2 (fun p ↦ u p - v p)
      (spaceTimeCylinder Ω (Ioo a b)) := hu.sub hv hQ
  have hwvel : ∀ x ∈ Ω,
      derivWithin (fun s ↦ u (timeSpaceCons s x) - v (timeSpaceCons s x)) (Ici a) a = 0 := by
    intro x hx
    have hud := (hu.of_le (by omega)).differentiableWithinAt_initial_time hab hΩ huc hx
    have hvd := (hv.of_le (by omega)).differentiableWithinAt_initial_time hab hΩ hvc hx
    rw [derivWithin_fun_sub hud hvd, hvel x hx, sub_self]
  have hwPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b,
      waveOperator (fun p ↦ u p - v p) (timeSpaceCons t x) = 0 := by
    intro x hx t ht
    have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩
    rw [waveOperator_sub (hu.contDiffOn.contDiffAt (hQ.mem_nhds hp))
      (hv.contDiffOn.contDiffAt (hQ.mem_nhds hp)), nonhomogeneousWaveEquation.residual_eq hPu hp,
      nonhomogeneousWaveEquation.residual_eq hPv hp, sub_self]
  have hzero := Dirichlet.eq_zero_on_closedCylinder_of_zero_data
    hw hΩ hbounded hgraph (huc.sub hvc) (fun x hx t ht ↦ sub_eq_zero.mpr (hboundary x hx t ht))
    (fun x hx ↦ sub_eq_zero.mpr (hpos x hx)) hwvel hwPDE
  exact fun x hx t ht ↦ sub_eq_zero.mp (hzero x hx t ht)

end WaveEquation
