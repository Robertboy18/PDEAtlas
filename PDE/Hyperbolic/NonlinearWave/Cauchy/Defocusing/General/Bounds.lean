/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Equations

/-!
# Whole-space bounds from a nonnegative wave potential

Conservation controls the gradient and velocity in every dimension. Integrating
`uₜ = v` supplies the L² displacement bound missing from massless energy.
The resulting full H¹ × L² estimate needs no Poincaré inequality and applies
to every spatial nonlinearity in the nonnegative-potential class.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Interval Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity

variable {n : ℕ} (N : Nonlinearity n)

/-- The whole-space gradient form is nonnegative, without a Poincaré inequality. -/
theorem gradientForm_nonneg (u : H¹(ℝ^n)) : 0 ≤ gradientForm n u u := by
  rw [gradientForm_apply]
  exact Finset.sum_nonneg fun _ _ ↦ real_inner_self_nonneg

/-- The H¹ norm splits into its L² displacement and gradient parts. -/
theorem norm_h1_sq (u : H¹(ℝ^n)) :
    ‖u‖ ^ 2 = ‖(energyTriple n).inclusion u‖ ^ 2 + gradientForm n u u := by
  change ‖u‖ ^ 2 = ‖(energyTriple n).inclusion u‖ ^ 2 +
    (⟪u, u⟫_ℝ - ⟪(energyTriple n).inclusion u, (energyTriple n).inclusion u⟫_ℝ)
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- The physical energy is nonnegative for every energy datum. -/
theorem energy_nonneg (z : H¹(ℝ^n) × DerivLp n 2 univ) : 0 ≤ N.energy z :=
  add_nonneg (mul_nonneg (by norm_num)
    (add_nonneg (gradientForm_nonneg z.1) (sq_nonneg _))) (N.potential_nonneg z.1)

/-- Physical energy controls the gradient and velocity squares. -/
theorem gradient_velocity_le_energy (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    gradientForm n z.1 z.1 + ‖z.2‖ ^ 2 ≤ 2 * N.energy z := by
  have h := N.potential_nonneg z.1
  unfold energy
  linarith

/-- The velocity bound obtained from positive defocusing energy. -/
theorem norm_velocity_le (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    ‖z.2‖ ≤ Real.sqrt (2 * N.energy z) := by
  apply Real.le_sqrt_of_sq_le
  have h := N.gradient_velocity_le_energy z
  have hg := gradientForm_nonneg z.1
  linarith

/-- A bound on L² displacement completes the missing coercivity of physical energy. -/
theorem norm_state_le (z : H¹(ℝ^n) × DerivLp n 2 univ) {A : ℝ} (hA : 0 ≤ A)
    (hbase : ‖(energyTriple n).inclusion z.1‖ ≤ A) :
    ‖z‖ ≤ A + Real.sqrt (2 * N.energy z) := by
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (N.energy_nonneg z))
  have hc := Real.sqrt_nonneg (2 * N.energy z)
  have hq := norm_h1_sq z.1
  have he := N.gradient_velocity_le_energy z
  have hb : ‖(energyTriple n).inclusion z.1‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbase 2
  have hu : ‖z.1‖ ≤ A + Real.sqrt (2 * N.energy z) := by
    nlinarith [sq_nonneg ‖z.2‖, norm_nonneg z.1]
  rw [Prod.norm_def]
  exact max_le hu ((N.norm_velocity_le z).trans (le_add_of_nonneg_left hA))

/-- Every finite mild solution has a uniform velocity bound from its initial energy. -/
theorem norm_velocity_of_mildSolutionOn {x : H¹(ℝ^n) × DerivLp n 2 univ} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : (productSemigroup n).IsMildSolutionOn N.vectorField x τ u) (t : Icc (0 : ℝ) (τ : ℝ)) :
    ‖(u t).2‖ ≤ Real.sqrt (2 * N.energy x) := by
  simpa only [N.energy_of_mildSolutionOn hu t] using N.norm_velocity_le (u t)

/-- The displacement equation supplies the L² bound absent from massless energy. -/
theorem norm_displacement_of_mildSolutionOn {x : H¹(ℝ^n) × DerivLp n 2 univ} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : (productSemigroup n).IsMildSolutionOn N.vectorField x τ u) (t : Icc (0 : ℝ) (τ : ℝ)) :
    ‖(energyTriple n).inclusion (u t).1‖ ≤
      ‖(energyTriple n).inclusion x.1‖ + t * Real.sqrt (2 * N.energy x) := by
  have hbound (s : ℝ) (hs : s ∈ Ι (0 : ℝ) (t : ℝ)) :
      ‖(IccExtend τ.coe_nonneg u s).2‖ ≤ Real.sqrt (2 * N.energy x) := by
    rw [uIoc_of_le t.property.1] at hs
    have hsτ : s ∈ Icc (0 : ℝ) (τ : ℝ) := ⟨hs.1.le, hs.2.trans t.property.2⟩
    rw [IccExtend_of_mem τ.coe_nonneg u hsτ]
    exact N.norm_velocity_of_mildSolutionOn hu ⟨s, hsτ⟩
  have hi : ‖∫ s in (0 : ℝ)..(t : ℝ), (IccExtend τ.coe_nonneg u s).2‖ ≤
      Real.sqrt (2 * N.energy x) * t := by
    simpa only [sub_zero, abs_of_nonneg t.property.1] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have he := (N.mild_integrated_equations hu t).1
  have heq := (eq_add_of_sub_eq he.symm)
  calc
    ‖(energyTriple n).inclusion (u t).1‖ =
        ‖(∫ s in (0 : ℝ)..(t : ℝ), (IccExtend τ.coe_nonneg u s).2) +
          (energyTriple n).inclusion x.1‖ := congrArg norm heq
    _ ≤ ‖∫ s in (0 : ℝ)..(t : ℝ), (IccExtend τ.coe_nonneg u s).2‖ +
        ‖(energyTriple n).inclusion x.1‖ := norm_add_le _ _
    _ ≤ ‖(energyTriple n).inclusion x.1‖ + t * Real.sqrt (2 * N.energy x) := by
      linarith

/-- The derived full energy-space bound grows at most linearly with the horizon. -/
theorem norm_of_mildSolutionOn {x : H¹(ℝ^n) × DerivLp n 2 univ} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : (productSemigroup n).IsMildSolutionOn N.vectorField x τ u) (t : Icc (0 : ℝ) (τ : ℝ)) :
    ‖u t‖ ≤ ‖(energyTriple n).inclusion x.1‖ + (t + 1) * Real.sqrt (2 * N.energy x) := by
  have h := N.norm_state_le (u t) (A :=
      ‖(energyTriple n).inclusion x.1‖ + t * Real.sqrt (2 * N.energy x))
    (add_nonneg (norm_nonneg _) (mul_nonneg t.property.1 (Real.sqrt_nonneg _)))
    (N.norm_displacement_of_mildSolutionOn hu t)
  rw [N.energy_of_mildSolutionOn hu t] at h
  linarith

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity
