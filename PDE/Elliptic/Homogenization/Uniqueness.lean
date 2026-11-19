/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.Dirichlet

/-!
# Uniqueness on the physical interval

The solution class asks for continuity up to the endpoints, differentiability in the
interior, and a continuous flux whose interior derivative equals the negative source.
The coefficient itself need not be differentiable. Integrating the flux and then the
solution determines the integration constant from the right boundary condition.
-/

@[expose] public section

noncomputable section

open PDE.Analysis (primitive hasDerivAt_primitive continuous_primitive)

namespace PDE.Elliptic.Homogenization

open MeasureTheory Set
open PDE.Analysis.PeriodicAveraging
open scoped Topology

/-- The homogeneous Dirichlet problem on `[0,1]`, in classical flux regularity. -/
structure IsFluxDirichletSolution (b f u : ℝ → ℝ) : Prop where
  /-- The solution is continuous up to both endpoints. -/
  continuous : ContinuousOn u (Icc 0 1)
  /-- Only interior differentiability is needed. -/
  differentiable : DifferentiableOn ℝ u (Ioo 0 1)
  /-- An independent continuous flux agrees with `b u'` only in the interior.
  Its endpoint values do not use derivatives of an extension of `u`. -/
  exists_flux : ∃ q : ℝ → ℝ, ContinuousOn q (Icc 0 1) ∧
    EqOn q (fun x ↦ b x * deriv u x) (Ioo 0 1) ∧
    ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt q (-f x) x
  /-- The left homogeneous Dirichlet trace. -/
  left : u 0 = 0
  /-- The right homogeneous Dirichlet trace. -/
  right : u 1 = 0

/-- The interval solution class is unchanged by any alteration outside the closed interval. -/
theorem IsFluxDirichletSolution.congr {b f u v : ℝ → ℝ}
    (hu : IsFluxDirichletSolution b f u) (h : EqOn v u (Icc (0 : ℝ) 1)) :
    IsFluxDirichletSolution b f v := by
  have he (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : v =ᶠ[𝓝 x] u :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx)
      (fun y hy ↦ h (Ioo_subset_Icc_self hy))
  obtain ⟨q, hq, hmatch, hderiv⟩ := hu.exists_flux
  refine ⟨hu.continuous.congr h, ?_, ⟨q, hq, ?_, hderiv⟩, ?_, ?_⟩
  · intro x hx
    exact (((hu.differentiable x hx).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt.congr_of_eventuallyEq
      (he x hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    change q x = b x * deriv v x
    rw [(he x hx).deriv_eq]
    exact hmatch hx
  · rw [h (by simp : (0 : ℝ) ∈ Icc 0 1), hu.left]
  · rw [h (by simp : (1 : ℝ) ∈ Icc 0 1), hu.right]

namespace PeriodicMedium

variable (a : PeriodicMedium)

/-- The integral construction belongs to the flux solution class. -/
theorem solution_isFluxDirichletSolution {f : ℝ → ℝ} (hf : Continuous f) (ε : ℝ) :
    IsFluxDirichletSolution (fun x ↦ a.coefficient (x / ε)) f (a.solution f ε) where
  continuous := (a.contDiff_solution hf ε).continuous.continuousOn
  differentiable := fun x _ ↦ (a.hasDerivAt_solution hf ε x).differentiableAt.differentiableWithinAt
  exists_flux := ⟨fun x ↦ a.fluxConstant f ε - primitive f x,
    (continuous_const.sub (continuous_primitive hf)).continuousOn,
    fun x _ ↦ (a.solution_flux hf ε x).symm,
    fun x _ ↦ by
      convert (hasDerivAt_primitive hf x).const_sub (a.fluxConstant f ε) using 1⟩
  left := a.solution_zero f ε
  right := a.solution_one f ε

/-- The limiting profile solves the Dirichlet problem for the harmonic-mean coefficient. -/
theorem homogenizedSolution_isFluxDirichletSolution {f : ℝ → ℝ} (hf : Continuous f) :
    IsFluxDirichletSolution (fun _ ↦ a.effective) f (a.homogenizedSolution f) where
  continuous := (a.contDiff_homogenizedSolution hf).continuous.continuousOn
  differentiable := fun x _ ↦
    (a.hasDerivAt_homogenizedSolution hf x).differentiableAt.differentiableWithinAt
  exists_flux := ⟨fun x ↦ primitive (primitive f) 1 - primitive f x,
    (continuous_const.sub (continuous_primitive hf)).continuousOn,
    fun x _ ↦ (a.homogenizedSolution_flux hf x).symm,
    fun x _ ↦ by
      convert (hasDerivAt_primitive hf x).const_sub (primitive (primitive f) 1) using 1⟩
  left := a.homogenizedSolution_zero f
  right := a.homogenizedSolution_one f

/-- Every flux solution agrees with the explicitly constructed solution on the physical interval. -/
theorem solution_unique {f v : ℝ → ℝ} (hf : Continuous f) (ε : ℝ)
    (hv : IsFluxDirichletSolution (fun x ↦ a.coefficient (x / ε)) f v) :
    EqOn v (a.solution f ε) (Icc (0 : ℝ) 1) := by
  obtain ⟨q, hq, hmatch, hderiv⟩ := hv.exists_flux
  let C := q 0
  let g (y : ℝ) := (C - primitive f y) * a.reciprocal (y / ε)
  let W (y : ℝ) := C * a.resistance ε y - a.weightedResistance f ε y
  have hg : Continuous g :=
    (continuous_const.sub (continuous_primitive hf)).mul (a.continuous_rescaled_reciprocal ε)
  have hW (y : ℝ) : HasDerivAt W (g y) y := by
    dsimp [W, g]
    convert ((a.hasDerivAt_resistance ε y).const_mul C).fun_sub
      (a.hasDerivAt_weightedResistance hf ε y) using 1
    ring
  have hflux (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      q x = C - primitive f x := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hq.mono (Icc_subset_Icc le_rfl hx.2))
      (fun y hy ↦ hderiv y ⟨hy.1, hy.2.trans_le hx.2⟩)
      (hf.neg.intervalIntegrable 0 x)
    rw [intervalIntegral.integral_neg] at hi
    dsimp [C, primitive]
    linarith
  have hdv (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : HasDerivAt v (g y) y := by
    have hd := (hv.differentiable y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
    have heq : deriv v y = g y := by
      have he := hflux y (Ioo_subset_Icc_self hy)
      rw [hmatch hy] at he
      have ha := (a.positive (y / ε)).ne'
      dsimp [g, reciprocal]
      rw [← he]
      field_simp
    exact heq ▸ hd.hasDerivAt
  have hrepr (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : v x = W x := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
      (hv.continuous.mono (Icc_subset_Icc le_rfl hx.2))
      (fun y hy ↦ hdv y ⟨hy.1, hy.2.trans_le hx.2⟩) (hg.intervalIntegrable 0 x)
    have hj := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := x) (fun y _ ↦ hW y) (hg.intervalIntegrable 0 x)
    have hW0 : W 0 = 0 := by simp [W, resistance, weightedResistance]
    rw [hv.left, sub_zero] at hi
    rw [hW0, sub_zero] at hj
    exact hi.symm.trans hj
  have hC : C = a.fluxConstant f ε := by
    have he := hrepr 1 (by simp)
    rw [hv.right] at he
    dsimp [W] at he
    unfold fluxConstant
    apply (eq_div_iff (a.resistance_one_pos ε).ne').mpr
    linarith
  intro x hx
  rw [hrepr x hx]
  dsimp [W, solution]
  rw [hC]

end PeriodicMedium

end PDE.Elliptic.Homogenization
