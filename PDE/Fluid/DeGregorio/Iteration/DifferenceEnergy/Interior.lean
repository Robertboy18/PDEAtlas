/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy.Cylinder
public import PDE.Analysis.Evolution.Time.GronwallInterior
public import PDE.Fluid.DeGregorio.Iteration.DifferenceEnergy
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Frozen difference energy with spatially C¹ velocities

The transport cancellation uses spatial velocity derivatives only. The
vorticities are classical in the open time cylinder, while the integrated
comparison needs only a continuous energy trace at the endpoints.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped Topology

namespace DeGregorio

/-- The estimate `norm_deriv_frozen_differenceEnergy_le` at an interior time `t ∈ (a, b)`,
for vorticities that are jointly C¹ only on `ℝ × (a, b)` and velocities that are
spatially C¹ at time `t`. -/
theorem norm_deriv_frozen_differenceEnergy_le_interior
    {fields other : Fields} {f g : ℝ → ℝ} {L C a b t : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hg : ContDiffOn ℝ 1 (Function.uncurry other.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiff ℝ 1 (fun x ↦ fields.velocity x t))
    (hv : ContDiff ℝ 1 (fun x ↦ other.velocity x t))
    (hpde : SatisfiesTransportEquationOn 1 fields (Ioo a b))
    (hother : SatisfiesTransportEquationOn 1 other (Ioo a b)) (ht : t ∈ Ioo a b)
    (hpair : IsHilbertPair f (deriv (fun x ↦ fields.velocity x t)))
    (hpairOther : IsHilbertPair g (deriv (fun x ↦ other.velocity x t)))
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hleft : fields.vorticity (-L) t = other.vorticity (-L) t)
    (hright : fields.vorticity L t = other.vorticity L t)
    (hzero : fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C) :
    ‖deriv (differenceEnergy fields other L) t‖ ≤
      C * (5 * differenceEnergy fields other L t +
        (1 + 2 * L ^ 2) * ∫ x, (f x - g x) ^ 2) := by
  let d := fun x ↦ fields.vorticity x t - other.vorticity x t
  let u := fun x ↦ fields.velocity x t
  let v := fun x ↦ fields.velocity x t - other.velocity x t
  let w := fun x ↦ other.vorticity x t
  have hfs := contDiff_slice_of_contDiffOn_cylinder hf ht
  have hgs := contDiff_slice_of_contDiffOn_cylinder hg ht
  have hus := hu
  have hvs := hv
  have hd : ContDiff ℝ 1 d := hfs.sub hgs
  have hpairDiff : IsHilbertPair (f - g) (deriv v) :=
    isHilbertPair_sub_of_differentiable (hus.differentiable (by simp))
      (hvs.differentiable (by simp)) hpair hpairOther
  have htime {f : ℝ → ℝ → ℝ}
      (h : ContDiffOn ℝ 1 (Function.uncurry f) (univ ×ˢ Ioo a b)) (x : ℝ) :
      DifferentiableAt ℝ (f x) t :=
    ((h.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)).differentiableAt
      (by simp)).comp t ((hasDerivAt_const t x).prodMk (hasDerivAt_id t)).differentiableAt
  have hrate : deriv (differenceEnergy fields other L) t =
      ∫ x in Icc (-L) L, 3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
        2 * d x * v x * deriv w x := by
    simpa only [zero_mul, mul_zero, zero_add, add_zero] using
      deriv_differenceEnergy_eq (cl := 0) (cw := 0) hfs hgs hus hvs
      (htime hf) (htime hg)
      (hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder
        (f := fun x s ↦ fields.vorticity x s - other.vorticity x s)
        (hf.sub hg) ht (-L) L)
      (fun x ↦ by simpa only [one_mul, zero_mul, zero_add] using hpde (x := x) ht)
      (fun x ↦ by simpa only [one_mul, zero_mul, zero_add] using hother (x := x) ht)
      hleft hright
  rw [hrate]
  exact norm_integral_frozen_terms_le hd hus (hus.sub hvs) hgs hL hC hpairDiff
    (sub_eq_zero.mpr hzero) hbound

/-- Interior frozen PDEs and a continuous energy trace give the difference bound on
the closed interval `[a, b]`. -/
theorem differenceEnergy_le_gronwallBound_of_frozen_transport_interior
    {fields other : Fields} {f g : ℝ → ℝ → ℝ} {L C M a b : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hg : ContDiffOn ℝ 1 (Function.uncurry other.vorticity) (univ ×ˢ Ioo a b))
    (hu : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (fun x ↦ fields.velocity x t))
    (hv : ∀ t ∈ Ioo a b, ContDiff ℝ 1 (fun x ↦ other.velocity x t))
    (hpde : SatisfiesTransportEquationOn 1 fields (Ioo a b))
    (hother : SatisfiesTransportEquationOn 1 other (Ioo a b))
    (hpair : ∀ t ∈ Ioo a b, IsHilbertPair (fun x ↦ f x t)
      (deriv (fun x ↦ fields.velocity x t)))
    (hpairOther : ∀ t ∈ Ioo a b, IsHilbertPair (fun x ↦ g x t)
      (deriv (fun x ↦ other.velocity x t)))
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hboundary : ∀ t ∈ Ioo a b,
      fields.vorticity (-L) t = other.vorticity (-L) t ∧
        fields.vorticity L t = other.vorticity L t)
    (hzero : ∀ t ∈ Ioo a b, fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ t ∈ Ioo a b, ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C)
    (htrace : ContinuousOn (differenceEnergy fields other L) (Icc a b))
    (hinitial : differenceEnergy fields other L a = 0)
    (hinput : ∀ t ∈ Ioo a b, (∫ x, (f x t - g x t) ^ 2) ≤ M) :
    ∀ t ∈ Icc a b, differenceEnergy fields other L t ≤
      M * gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) (t - a) := by
  have hestimate := le_gronwallBound_of_deriv_le_interior
    (e := differenceEnergy fields other L) (δ := 0) (K := 5 * C)
    (ε := C * (1 + 2 * L ^ 2) * M) htrace
    (fun t ht ↦
      (hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder
        (f := fun x s ↦ fields.vorticity x s - other.vorticity x s)
        (hf.sub hg) ht (-L) L).differentiableAt)
    (le_of_eq hinitial) (by
      intro t ht
      calc
        _ ≤ ‖deriv (differenceEnergy fields other L) t‖ := le_abs_self _
        _ ≤ C * (5 * differenceEnergy fields other L t +
            (1 + 2 * L ^ 2) * ∫ x, (f x t - g x t) ^ 2) :=
          norm_deriv_frozen_differenceEnergy_le_interior hf hg (hu t ht) (hv t ht)
            hpde hother ht (hpair t ht) (hpairOther t ht) hL hC
            (hboundary t ht).1 (hboundary t ht).2 (hzero t ht) (hbound t ht)
        _ ≤ C * (5 * differenceEnergy fields other L t + (1 + 2 * L ^ 2) * M) := by
          gcongr
          exact hinput t ht
        _ = _ := by cas)
  intro t ht
  apply (hestimate t ht).trans_eq
  by_cases hK : 5 * C = 0
  · simp only [hK, gronwallBound_K0, zero_add]
    cas
  · simp only [gronwallBound_of_K_ne_0 hK, zero_mul, zero_add]
    cas using hK

end DeGregorio
