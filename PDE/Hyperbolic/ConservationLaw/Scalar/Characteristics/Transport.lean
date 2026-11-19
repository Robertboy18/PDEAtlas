/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.GlobalInverse
import Mathlib.Analysis.ODE.Gronwall
import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Transport of classical solutions along scalar characteristics

For a classical solution of `u_t + a(u) u_x = 0`, the speed difference along
the straight line of an initial state satisfies a homogeneous linear ODE.
Grönwall's inequality forces this difference to vanish, and the solution is
then constant along that line. The characteristic identity is derived from
the PDE.

Evans obtains the same fact, equations (59)-(60) of §3.2.5, Example 5, from the characteristic
equations of §3.2.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.1, Theorem 1; §3.2.5, Example 5, equations (58)-(60).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Common
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- Chain rule along a straight spacetime line. -/
theorem hasDerivAt_along_characteristic {u : ℝ^2 → ℝ} (c ξ t : ℝ)
    (hu : DifferentiableAt ℝ u !₂[t, ξ + t * c]) :
    HasDerivAt (fun s : ℝ ↦ u !₂[s, ξ + s * c])
      ((∂[(0 : Fin 2)] u) !₂[t, ξ + t * c] + c * (∂[(1 : Fin 2)] u) !₂[t, ξ + t * c]) t := by
  have heq : (fun s : ℝ ↦ !₂[s, ξ + s * c]) =
      fun s : ℝ ↦ !₂[0, ξ] + s • !₂[1, c] := by
    funext s
    ext i
    fin_cases i <;> simp
  have hline : HasDerivAt (fun s : ℝ ↦ !₂[s, ξ + s * c]) !₂[1, c] t := by
    rw [heq]
    simpa using ((hasDerivAt_id t).smul_const !₂[1, c]).const_add !₂[0, ξ]
  convert hu.hasFDerivAt.comp_hasDerivAt t hline using 1
  · rfl
  · rw [fderiv_apply_eq_sum_partialDeriv_mul]
    simp [Fin.sum_univ_two, mul_comm]

/-- A classical solution transports a state along its straight characteristic.
Only C¹ regularity and the PDE on this compact line segment are required. -/
theorem classical_solution_eq_along_characteristic {a : ℝ → ℝ} {u : ℝ^2 → ℝ} (ha : ContDiff ℝ 1 a)
    (ξ v : ℝ) {s t : ℝ} (hst : s ≤ t) (hu : ∀ r ∈ Icc s t, ContDiffAt ℝ 1 u !₂[r, ξ + r * a v])
    (hpde : ∀ r ∈ Icc s t, (∂[(0 : Fin 2)] u) !₂[r, ξ + r * a v] + a (u !₂[r, ξ + r * a v]) *
      (∂[(1 : Fin 2)] u) !₂[r, ξ + r * a v] = 0)
    (hinit : u !₂[s, ξ + s * a v] = v) :
    u !₂[t, ξ + t * a v] = v := by
  let γ : ℝ → ℝ^2 := fun r ↦ !₂[r, ξ + r * a v]
  let w : ℝ → ℝ := fun r ↦ a (u (γ r)) - a v
  let b : ℝ → ℝ := fun r ↦ -(deriv a (u (γ r)) * (∂[(1 : Fin 2)] u) (γ r))
  have hγ : Continuous γ := by dsimp [γ]; fun_prop
  have hv : ∀ r ∈ Icc s t,
      HasDerivAt (fun r ↦ u (γ r)) (-(w r) * (∂[(1 : Fin 2)] u) (γ r)) r := by
    intro r hr
    apply (hasDerivAt_along_characteristic (a v) ξ r (hu r hr).differentiableAt_one).congr_deriv
    have h := hpde r hr
    dsimp [γ, w]
    nlinarith
  have huc : ContinuousOn (fun r ↦ u (γ r)) (Icc s t) :=
    fun r hr ↦ (hv r hr).continuousAt.continuousWithinAt
  have hw : ContinuousOn w (Icc s t) := (ha.continuous.comp_continuousOn huc).sub continuousOn_const
  have hb : ContinuousOn b (Icc s t) := by
    apply ContinuousOn.neg
    apply ContinuousOn.mul
    · exact (ha.continuous_deriv le_rfl).comp_continuousOn huc
    · intro r hr
      have hc : ContinuousAt (∂[(1 : Fin 2)] u) (γ r) :=
        (contDiffAt_partialDeriv 0 (hu r hr) 1).continuousAt
      exact (hc.comp hγ.continuousAt).continuousWithinAt
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hb.norm
  have hw' : ∀ r ∈ Icc s t, HasDerivAt w (b r * w r) r := by
    intro r hr
    apply (((ha.differentiable_one (u (γ r))).hasDerivAt.comp r
      (hv r hr)).sub_const (a v)).congr_deriv
    dsimp [b]
    cas
  have hwzero : ∀ r ∈ Icc s t, w r = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right hw
      (fun r hr ↦ (hw' r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt)
    · simp [w, γ, hinit]
    · intro r hr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hK ⟨r, ⟨hr.1, hr.2.le⟩, rfl⟩) (norm_nonneg _)
  have hvzero : ∀ r ∈ Ico s t, HasDerivWithinAt (fun r ↦ u (γ r)) 0 (Ici r) r := by
    intro r hr
    simpa [hwzero r ⟨hr.1, hr.2.le⟩] using (hv r ⟨hr.1, hr.2.le⟩).hasDerivWithinAt
  exact eq_of_has_deriv_right_eq hvzero (fun r _ ↦ (hasDerivAt_const r v).hasDerivWithinAt)
    huc continuousOn_const hinit t ⟨hst, le_rfl⟩

/-- Every classical solution with the stated initial data satisfies the characteristic identity. -/
theorem classical_solution_characteristic {a u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ} (ha : ContDiff ℝ 1 a) {t : ℝ}
    (ht : 0 ≤ t) (hu : ∀ p : ℝ^2, p 0 ∈ Icc 0 t → ContDiffAt ℝ 1 u p)
    (hpde : ∀ p : ℝ^2, p 0 ∈ Icc 0 t → (∂[(0 : Fin 2)] u) p + a (u p) * (∂[(1 : Fin 2)] u) p = 0)
    (hinit : ∀ x : ℝ, u !₂[0, x] = u₀ x) (ξ : ℝ) :
    u !₂[t, conservationCharPosition a u₀ t ξ] = u₀ ξ := by
  apply classical_solution_eq_along_characteristic ha ξ (u₀ ξ) ht
  · exact fun r hr ↦ hu _ hr
  · exact fun r hr ↦ hpde _ hr
  · simpa using hinit ξ

/-- Differentiating the transported field with respect to the initial label
introduces the characteristic Jacobian. -/
theorem hasDerivAt_characteristic_label {a u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (ha : Differentiable ℝ a) (hu₀ : Differentiable ℝ u₀) (t ξ : ℝ)
    (hu : DifferentiableAt ℝ u !₂[t, conservationCharPosition a u₀ t ξ]) :
    HasDerivAt (fun η ↦ u !₂[t, conservationCharPosition a u₀ t η])
      ((∂[(1 : Fin 2)] u) !₂[t, conservationCharPosition a u₀ t ξ] *
        (1 + t * deriv a (u₀ ξ) * deriv u₀ ξ)) ξ := by
  have heq : (fun η ↦ !₂[t, conservationCharPosition a u₀ t η]) =
      fun η ↦ !₂[t, 0] + conservationCharPosition a u₀ t η • !₂[0, 1] := by
    funext η
    ext i
    fin_cases i <;> simp
  have hline : HasDerivAt (fun η ↦ !₂[t, conservationCharPosition a u₀ t η])
      ((1 + t * deriv a (u₀ ξ) * deriv u₀ ξ) • !₂[0, 1]) ξ := by
    rw [heq]
    exact ((hasDerivAt_conservationCharPosition ha hu₀ t ξ).smul_const
      (!₂[0, 1] : ℝ^2)).const_add !₂[t, 0]
  convert hu.hasFDerivAt.comp_hasDerivAt ξ hline using 1
  · rfl
  · rw [fderiv_apply_eq_sum_partialDeriv_mul]
    simp [Fin.sum_univ_two]

/-- The characteristic Jacobian identity for an arbitrary classical solution
is a consequence of its PDE and initial condition. -/
theorem classical_solution_spatial_jacobian {a u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ} (ha : ContDiff ℝ 1 a)
    (hu₀ : Differentiable ℝ u₀) {t : ℝ} (ht : 0 ≤ t)
    (hu : ∀ p : ℝ^2, p 0 ∈ Icc 0 t → ContDiffAt ℝ 1 u p)
    (hpde : ∀ p : ℝ^2, p 0 ∈ Icc 0 t → (∂[(0 : Fin 2)] u) p + a (u p) * (∂[(1 : Fin 2)] u) p = 0)
    (hinit : ∀ x : ℝ, u !₂[0, x] = u₀ x) (ξ : ℝ) :
    (∂[(1 : Fin 2)] u) !₂[t, conservationCharPosition a u₀ t ξ] *
      (1 + t * deriv a (u₀ ξ) * deriv u₀ ξ) = deriv u₀ ξ := by
  have heq : (fun η ↦ u !₂[t, conservationCharPosition a u₀ t η]) = u₀ :=
    funext (classical_solution_characteristic ha ht hu hpde hinit)
  have hd := hasDerivAt_characteristic_label ha.differentiable_one hu₀ t ξ
    (hu _ ⟨ht, le_rfl⟩).differentiableAt_one
  rw [heq] at hd
  exact hd.deriv.symm

/-- Uniqueness of the global characteristic construction among classical
solutions with the same initial data. The datum is differentiable because it is the trace of
`u` at time `0`. -/
theorem classical_solution_eq_conservationClassicalSolution {a u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (ha : ContDiff ℝ 1 a) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (t : WithTop ℝ) < conservationShockTime a u₀)
    (hu : ∀ p : ℝ^2, p 0 ∈ Icc 0 t → ContDiffAt ℝ 1 u p)
    (hpde : ∀ p : ℝ^2, p 0 ∈ Icc 0 t → (∂[(0 : Fin 2)] u) p + a (u p) * (∂[(1 : Fin 2)] u) p = 0)
    (hinit : ∀ x : ℝ, u !₂[0, x] = u₀ x) (x : ℝ) :
    u !₂[t, x] = conservationClassicalSolution a u₀ !₂[t, x] := by
  have hu₀ : Differentiable ℝ u₀ := by
    have heq : u₀ = fun y ↦ u (y • !₂[0, 1]) := by
      funext y
      rw [← hinit y]
      congr 1
      ext i
      fin_cases i <;> simp
    rw [heq]
    intro y
    have hp : (y • (!₂[0, 1] : ℝ^2)) 0 ∈ Icc 0 t := by simp [ht0]
    exact (hu _ hp).differentiableAt_one.comp y (differentiableAt_id.smul_const _)
  have h := classical_solution_characteristic ha ht0 hu hpde hinit
    (conservationFootpoint a u₀ !₂[t, x])
  have hpos : conservationCharPosition a u₀ t (conservationFootpoint a u₀ !₂[t, x]) = x :=
    (conservationFootpoint_relation ha.differentiable_one hu₀ ht0 ht).symm
  rwa [hpos] at h

end PDE.Hyperbolic.ConservationLaw.Scalar
