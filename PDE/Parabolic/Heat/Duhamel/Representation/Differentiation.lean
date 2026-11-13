/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Regularity
public import PDE.Parabolic.Heat.InitialValue
public import PDE.FDeriv.Laplacian.Continuity
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.Calculus.ParametricIntegral.CompactSupport
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.FDeriv.Calculus
import PDE.Parabolic.Heat.Kernel.SpatialDerivatives
import PDE.Parabolic.Heat.Kernel.TimeDerivative
import CAS.ExactTactic

/-!
# Differentiating a backward heat-kernel pairing

For a spatially compact `C^{2,1}` function, differentiation of its pairing with the backward
Gaussian gives its heat residual paired with the same Gaussian. Compact support supplies domination;
two spatial integrations by parts transfer the Laplacian from the kernel to the function. No mixed
or second time derivative is required. Integrating the identity in time gives
`eq_initialValueSolution_add_integral_heatResidual`, the representation used in place of (36) in
Evans's proof of §2.3.3(b), Theorem 8.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.3(b), the proof of Theorem 8, (33)-(36), pp. 60-61.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace HeatEquation

variable {n : ℕ}

/-- Differentiate the backward Gaussian pairing of a continuous family having
a jointly continuous time derivative and a common compact spatial support. -/
theorem hasDerivAt_integral_backwardHeatKernel_mul
    {u D : ℝ → ℝ^n → ℝ} {a b : ℝ} {K : Set (ℝ^n)}
    (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (Ioo a b ×ˢ univ))
    (hD : ContinuousOn D.uncurry (Ioo a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ y, HasDerivAt (fun r ↦ u r y) (D s y) s)
    (hsupport : ∀ s ∈ Ioo a b, ∀ y ∉ K, u s y = 0)
    (x : ℝ^n) {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt
      (fun r ↦ ∫ y, fundamentalSolutionHeat (y - x) (b - r) * u r y)
      (∫ y, fundamentalSolutionHeat (y - x) (b - s) * D s y -
        (‖y - x‖ ^ 2 / (4 * (b - s) ^ 2) - (n : ℝ) / (2 * (b - s))) *
          fundamentalSolutionHeat (y - x) (b - s) * u s y) s := by
  have hkernel : ContinuousOn
      (fun p : ℝ × ℝ^n ↦ fundamentalSolutionHeat (p.2 - x) (b - p.1))
      (Ioo a b ×ˢ univ) := by
    intro p hp
    exact ((contDiffAt_fundamentalSolutionHeat_of_time_pos (m := 0)
      (sub_pos.mpr hp.1.2)).continuousAt.comp
        ((continuous_snd.sub continuous_const).prodMk
          (continuous_const.sub continuous_fst)).continuousAt).continuousWithinAt
  have hcoefficient : ContinuousOn
      (fun p : ℝ × ℝ^n ↦ ‖p.2 - x‖ ^ 2 / (4 * (b - p.1) ^ 2) -
        (n : ℝ) / (2 * (b - p.1))) (Ioo a b ×ˢ univ) := by
    intro p hp
    have htime : b - p.1 ≠ 0 := ne_of_gt (sub_pos.mpr hp.1.2)
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  apply PDE.hasDerivAt_integral_of_locally_uniform_compact_support
    (f := fun r y ↦ fundamentalSolutionHeat (y - x) (b - r) * u r y)
    (D := fun r y ↦ fundamentalSolutionHeat (y - x) (b - r) * D r y -
      (‖y - x‖ ^ 2 / (4 * (b - r) ^ 2) - (n : ℝ) / (2 * (b - r))) *
        fundamentalSolutionHeat (y - x) (b - r) * u r y)
    isOpen_Ioo hK (hkernel.mul hu) ?_ ?_ ?_ hs
  · intro p hp
    exact ((hkernel p hp).mul (hD p hp)).sub
      (((hcoefficient p hp).mul (hkernel p hp)).mul (hu p hp))
  · intro r hr y
    have htime : 0 < b - r := sub_pos.mpr hr.2
    have hk := (differentiableAt_fundamentalSolutionHeat_time (y - x)
      (b - r) htime).hasDerivAt
    rw [fundamentalSolutionHeat_deriv_t _ _ htime] at hk
    have hback := hk.comp r ((hasDerivAt_id r).const_sub b)
    convert hback.mul (hd r hr y) using 1 <;>
      dsimp only [Function.comp_def] <;> first | rfl | cas
  · intro r hr y hy
    simp [hsupport r hr y hy]

/-- For `C²` spatial slices, two integrations by parts identify the derivative
of the backward Gaussian pairing with the Gaussian pairing of the heat residual. -/
theorem hasDerivAt_initialValueSolution_backward
    {u D : ℝ → ℝ^n → ℝ} {a b : ℝ} {K : Set (ℝ^n)}
    (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (Ioo a b ×ˢ univ))
    (hD : ContinuousOn D.uncurry (Ioo a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ y, HasDerivAt (fun r ↦ u r y) (D s y) s)
    (hsupport : ∀ s ∈ Ioo a b, ∀ y ∉ K, u s y = 0)
    (hspace : ∀ s ∈ Ioo a b, ContDiff ℝ 2 (u s))
    (x : ℝ^n) {s : ℝ} (hs : s ∈ Ioo a b) :
    HasDerivAt (fun r ↦ initialValueSolution (u r) x (b - r))
      (initialValueSolution (fun y ↦ D s y - laplacian (u s) y) x (b - s)) s := by
  have htime : 0 < b - s := sub_pos.mpr hs.2
  let G : ℝ^n → ℝ := fun y ↦ fundamentalSolutionHeat (y - x) (b - s)
  have hG : ContDiff ℝ 2 G := contDiff_iff_contDiffAt.2 fun y ↦
    (contDiffAt_fundamentalSolutionHeat_of_time_pos (m := 2) htime).comp y
      ((contDiffAt_id.sub contDiffAt_const).prodMk contDiffAt_const)
  have hcompact : HasCompactSupport (u s) :=
    HasCompactSupport.intro hK (hsupport s hs)
  have hDzero (y : ℝ^n) (hy : y ∉ K) : D s y = 0 := by
    apply (hd s hs y).unique
    apply (hasDerivAt_const s 0).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr using hsupport r hr y hy
  have hDc : Continuous (D s) :=
    continuousOn_univ.mp (hD.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ ↦ ⟨hs, mem_univ y⟩))
  have hDcpt : HasCompactSupport (D s) := HasCompactSupport.intro hK hDzero
  have hLcpt : HasCompactSupport (laplacian (u s)) :=
    hcompact.coordinate_laplacian
  have hL := (hspace s hs).continuous_coordinate_laplacian
  have hGD : Integrable (fun y ↦ G y * D s y) :=
    (hG.continuous.mul hDc).integrable_of_hasCompactSupport hDcpt.mul_left
  have hGL : Integrable (fun y ↦ G y * laplacian (u s) y) :=
    (hG.continuous.mul hL).integrable_of_hasCompactSupport hLcpt.mul_left
  have hLG : Integrable (fun y ↦ laplacian G y * u s y) :=
    Continuous.integrable_of_hasCompactSupport
      (hG.continuous_coordinate_laplacian.mul (hspace s hs).continuous) hcompact.mul_left
  have hLap (y : ℝ^n) : laplacian G y =
      (‖y - x‖ ^ 2 / (4 * (b - s) ^ 2) - (n : ℝ) / (2 * (b - s))) * G y := by
    have hslice : ContDiffAt ℝ 2 (fun z ↦ fundamentalSolutionHeat z (b - s)) (y - x) :=
      (contDiffAt_fundamentalSolutionHeat_of_time_pos (m := 2) htime).comp (y - x)
        (contDiffAt_id.prodMk contDiffAt_const)
    exact (PDE.laplacian_comp_sub_right (fun z ↦ fundamentalSolutionHeat z (b - s))
      x y hslice).trans (laplacian_fundamentalSolutionHeat _ _ htime)
  have heven (y : ℝ^n) (r : ℝ) :
      fundamentalSolutionHeat (x - y) r = fundamentalSolutionHeat (y - x) r := by
    simp only [fundamentalSolutionHeat, norm_sub_rev]
  have hvalue :
      (∫ y, G y * D s y -
        (‖y - x‖ ^ 2 / (4 * (b - s) ^ 2) - (n : ℝ) / (2 * (b - s))) *
          G y * u s y) =
        initialValueSolution (fun y ↦ D s y - laplacian (u s) y) x (b - s) := by
    simp_rw [← hLap]
    rw [integral_sub hGD hLG]
    have hibp := PDE.DistributionTheory.integral_mul_laplacian_eq G (hspace s hs) hG hcompact
    simp_rw [mul_comm (u s _), mul_comm (laplacian (u s) _)] at hibp
    rw [hibp]
    simp only [initialValueSolution, ite_eq_right htime.not_ge, heven, mul_sub]
    exact (integral_sub hGD hGL).symm
  have hderiv := hasDerivAt_integral_backwardHeatKernel_mul hK hu hD hd hsupport x hs
  rw [show (∫ y, fundamentalSolutionHeat (y - x) (b - s) * D s y -
      (‖y - x‖ ^ 2 / (4 * (b - s) ^ 2) - (n : ℝ) / (2 * (b - s))) *
        fundamentalSolutionHeat (y - x) (b - s) * u s y) =
      initialValueSolution (fun y ↦ D s y - laplacian (u s) y) x (b - s) from hvalue]
    at hderiv
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
  simp only [initialValueSolution, ite_eq_right (sub_pos.mpr hr.2).not_ge, heven]

end HeatEquation
