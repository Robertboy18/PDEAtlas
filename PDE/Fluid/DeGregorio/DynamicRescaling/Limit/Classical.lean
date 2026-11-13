/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling.Limit
public import PDE.Fluid.DeGregorio.DynamicRescaling

/-!
# Stationary limits of rescaled solutions

The limiting argument applies to classical De Gregorio solutions in the sense of
`Model`. Its time derivative is the derivative of the given vorticity field;
its spatial derivative agrees almost everywhere with the H¹ coordinate.
The normalized velocity is recovered from its Hilbert-transform derivative
by the fundamental theorem of calculus.

The hypotheses are strong L² convergence of vorticity, a uniform H¹ bound,
decay of the time derivative in L², and convergence of the rates.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory PDE.Analysis SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio

/-- Integrating the L² representative of a classical velocity derivative recovers
the velocity increment from the origin. -/
theorem IsClassicalRescaledSolutionOn.intervalIntegral_toLp_velocity_deriv
    {a : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {t : ℝ} (ht : t ∈ times) (x : ℝ) :
    (∫ y in (0 : ℝ)..x,
      (hsol.biotSavart ht).memLp_right.toLp (deriv (fun z ↦ fields.velocity z t)) y) =
        fields.velocity x t - fields.velocity 0 t := by
  calc
    _ = ∫ y in (0 : ℝ)..x, deriv (fun z ↦ fields.velocity z t) y := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [(hsol.biotSavart ht).memLp_right.coeFn_toLp] with y hy _hmem
      exact hy
    _ = fields.velocity x t - fields.velocity 0 t :=
      intervalIntegral.integral_deriv_eq_sub
        (fun _ _ ↦ hsol.regularity.velocity_differentiableAt ht)
        (((hsol.biotSavart ht).memLp_right.locallyIntegrable
          (by norm_num)).integrableOn_isCompact isCompact_uIcc).intervalIntegrable

/-- A bounded H¹ family of normalized classical rescaled solutions with
a strong L² limit satisfies the stationary equation when the time
derivatives vanish in L² and the normalization rates converge. The Hilbert
relation and transport equation come from the given solutions. -/
theorem IsClassicalRescaledSolutionOn.exists_stationaryResidual_eq_zero_of_bounded_h1
    {a : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ : ι → ℝ} (hτ : ∀ n, τ n ∈ times)
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    (hrep : ∀ n, realLineRepresentative (f n) = fun x ↦ fields.vorticity x (τ n))
    (hnormalized : ∀ n, fields.velocity 0 (τ n) = 0)
    (ht : ∀ n, MemLp (fun x ↦ deriv (fields.vorticity x) (τ n)) 2 volume)
    {B : ℝ} (hbound : ∀ n, ‖f n‖ ≤ B)
    (hf : Tendsto (fun n ↦ realLineCoordinateCLM (baseIndex 1 1) (f n)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    (hdecay : Tendsto
      (fun n ↦ (ht n).toLp (fun x ↦ deriv (fields.vorticity x) (τ n))) l (𝓝 0))
    {cl₀ cw₀ : ℝ}
    (hcl : Tendsto (cl ∘ τ) l (𝓝 cl₀))
    (hcw : Tendsto (cw ∘ τ) l (𝓝 cw₀)) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u 0 = 0 ∧
      Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
      IsHilbertPair (realLineRepresentative F) (deriv u) ∧
      ∀ᵐ x ∂volume, stationaryResidual a cl₀ cw₀ (realLineRepresentative F) u x = 0 := by
  let h : ι → Lp ℝ 2 (volume : Measure ℝ) := fun n ↦
    (hsol.biotSavart (hτ n)).memLp_right.toLp (deriv (fun x ↦ fields.velocity x (τ n)))
  have hh (n : ι) :
      (h n : ℝ → ℝ) =ᵐ[volume] deriv (fun x ↦ fields.velocity x (τ n)) :=
    (hsol.biotSavart (hτ n)).memLp_right.coeFn_toLp
  have hpair (n : ι) : IsHilbertPair (realLineRepresentative (f n)) (h n) := by
    rw [hrep n]
    exact (hsol.biotSavart (hτ n)).congr_right_ae (hh n).symm
  have hvelocity (n : ι) (x : ℝ) :
      (∫ y in (0 : ℝ)..x, h n y) = fields.velocity x (τ n) := by
    simpa only [hnormalized n, sub_zero] using
      hsol.intervalIntegral_toLp_velocity_deriv (hτ n) x
  have hspace (n : ι) :
      (realLineCoordinateCLM (singleDerivIndex 1 0) (f n) : ℝ → ℝ) =ᵐ[volume]
        deriv (fun x ↦ fields.vorticity x (τ n)) := by
    have hloc := locallyIntegrableOn_univ.mp
      (hasWeakTimeDerivativeOn_realLineCoordinates (f n)).locallyIntegrable_g
    have hderiv :
        ∀ᵐ x ∂volume, HasDerivAt (realLineRepresentative (f n))
          (realLineCoordinateCLM (singleDerivIndex 1 0) (f n) x) x :=
      SobolevSpace.Slices.ae_hasDerivAt_lineRepresentative_of_locallyIntegrable hloc
    rw [hrep n] at hderiv
    filter_upwards [hderiv] with x hx
    exact hx.deriv.symm
  apply DeGregorio.exists_stationaryResidual_eq_zero_of_bounded_h1
    hbound hf hpair hdecay hcl hcw
  intro n
  filter_upwards [(ht n).coeFn_toLp, hh n, hspace n] with x htx hhx hsx
  rw [htx, hhx, hsx, hvelocity n x, hrep n]
  exact hsol.transport (hτ n)

end DeGregorio
