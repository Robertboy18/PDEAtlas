/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.TestedEnergy
public import PDE.Fluid.NavierStokes.LocalEnergy.Pointwise
public import PDE.Fluid.NavierStokes.Suitable
import PDE.Analysis.MeasureTheory.Lp.Continuous
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.FDeriv.PartialDeriv.Support
import PDE.FDeriv.SpaceTime.Gradient.Regularity

/-!
# Testing the positive-time Navier–Stokes energy equality

Local velocity and pressure regularity on the open physical slab make every
compact energy pairing integrable. Testing the classical momentum equation
then gives the distributional local energy equality. The hypotheses concern
positive times, as required when the initial datum is singular at the origin.
-/

@[expose] public noncomputable section

namespace NavierStokes

open EuclideanSpace IncompressibleFlow MeasureTheory PDE

set_option linter.missingDocs true

private theorem contDiffAt_energy {n : ℕ} {u : ℝ^(n + 1) → ℝ^n}
    {x : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 2 (specificKineticEnergy u) x :=
  contDiffAt_const.mul (hu.norm_sq ℝ)

/-- A `C²` velocity has a continuous spatial gradient. -/
theorem continuousAt_spatialVelocityGradient {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u x) :
    ContinuousAt (spatialVelocityGradient n u) x := by
  have h : ContDiffAt ℝ 0 (spatialVelocityGradient n u) x := by
    apply (contDiffAt_piLp 2).mpr
    intro ij
    rcases ij with ⟨i, j⟩
    simpa only [spatialVelocityGradient_apply] using
      (((contDiffAt_piLp 2).mp hu i).partialDeriv j.succ
        (k := 0) (by norm_num))
  exact h.continuousAt

private theorem spatialLaplacian_test_zero {n : ℕ} {φ : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hx : x ∉ tsupport φ) : spatialLaplacian n φ x = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  apply partialDeriv_eq_zero_of_notMem_tsupport
  exact fun h ↦ hx (tsupport_partialDeriv_subset (f := φ) j.succ h)

private theorem continuous_spatialLaplacian {n : ℕ} {φ : ℝ^(n + 1) → ℝ}
    (hφ : ContDiff ℝ 2 φ) : Continuous (spatialLaplacian n φ) :=
  (show ContDiff ℝ 0 (spatialLaplacian n φ) from ContDiff.sum fun j _ ↦
    (hφ.partialDeriv j.succ (k := 1) (by norm_num)).partialDeriv j.succ (k := 0)
      (by norm_num)).continuous

private theorem energy_flux_sum {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (p φ : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) :
    (∑ j : Fin n, (∂[j.succ] φ) x *
      ((specificKineticEnergy u x + p x) * u x j)) = localEnergyFluxDensity u p φ x := by
  simp only [localEnergyFluxDensity, PiLp.inner_apply, RCLike.inner_apply,
    spatialGradient_apply, starRingEnd_apply, star_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- All classical local energy pairings are integrable for interior compact tests
when velocity is locally `C²`, pressure locally `C¹`, and forcing vanishes. -/
theorem localEnergyIntegrable_of_positiveTime_regular {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hforce : nse.forcing = 0)
    (hu : ∀ x ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u x)
    (hp : ∀ x ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p x)
    {φ : ℝ^(n + 1) → ℝ} (hφ : IsLocalEnergyTest T φ) :
    LocalEnergyIntegrable nse u p (spatialVelocityGradient n u) φ := by
  have hφ₂ : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_num)
  have he (x : ℝ^(n + 1)) (hx : x ∈ tsupport φ) :=
    contDiffAt_energy (hu x (hφ.2.2.1 hx))
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine hφ.2.1.integrable_of_continuousOn_tsupport (fun x hx ↦ ?_) fun x hx ↦ by
      simp [localEnergyDissipationDensity, image_eq_zero_of_notMem_tsupport hx]
    have hG := (continuousAt_spatialVelocityGradient (hu x (hφ.2.2.1 hx))).norm.pow 2
    exact ((continuousAt_const.mul hG).mul hφ₂.continuous.continuousAt).continuousWithinAt
  · refine hφ.2.1.integrable_of_continuousOn_tsupport (fun x hx ↦ ?_) fun x hx ↦ ?_
    · have hΔ := (continuous_spatialLaplacian hφ₂).continuousAt (x := x)
      exact ((he x hx).continuousAt.mul ((hφ₂.partialDeriv 0 (k := 1)
        (by norm_num)).continuous.continuousAt.add (continuousAt_const.mul hΔ))).continuousWithinAt
    · change specificKineticEnergy u x *
        ((∂[0] φ) x + (nse.kinematicViscosity : ℝ) * spatialLaplacian n φ x) = 0
      rw [partialDeriv_eq_zero_of_notMem_tsupport 0 hx, spatialLaplacian_test_zero hx]
      simp
  · have hgrad : Continuous (spatialGradient φ) :=
      (contDiff_spatialGradient_of_succ (m := 1) hφ₂).continuous
    refine hφ.2.1.integrable_of_continuousOn_tsupport (fun x hx ↦
      (((he x hx).continuousAt.add (hp x (hφ.2.2.1 hx)).continuousAt).mul
        ((hu x (hφ.2.2.1 hx)).continuousAt.inner hgrad.continuousAt)).continuousWithinAt)
      fun x hx ↦ ?_
    have hz : spatialGradient φ x = 0 := by
      ext j
      simpa only [spatialGradient_apply, PiLp.zero_apply] using
        partialDeriv_eq_zero_of_notMem_tsupport j.succ hx
    simp [localEnergyFluxDensity, hz]
  · rw [show localEnergyForceDensity nse u φ = 0 from
      funext fun x ↦ by simp [localEnergyForceDensity, hforce]]
    exact integrable_zero _ _ _

/-- The classical energy equality gives the tested local energy equality on the
open positive-time slab, without imposing regularity at the initial surface. -/
theorem local_energy_tested_equality_of_positiveTime_regular {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hforce : nse.forcing = 0)
    (hu : ∀ x ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u x)
    (hp : ∀ x ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p x)
    (hdiv : ∀ x ∈ finiteTimeDomain n T, DivergenceFreeAt u x)
    (hmom : ∀ x ∈ finiteTimeDomain n T, MomentumEquationAt nse u p x)
    {φ : ℝ^(n + 1) → ℝ} (hφ : IsLocalEnergyTest T φ) :
    localEnergyDissipation nse (spatialVelocityGradient n u) φ =
      localEnergyInput nse u p φ := by
  let e := specificKineticEnergy u
  let F (j : Fin n) (x : ℝ^(n + 1)) := (e x + p x) * u x j
  have hφ₂ : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_num)
  have he (x : ℝ^(n + 1)) (hx : x ∈ tsupport φ) : ContDiffAt ℝ 2 e x :=
    contDiffAt_energy (hu x (hφ.2.2.1 hx))
  have hF (j : Fin n) (x : ℝ^(n + 1)) (hx : x ∈ tsupport φ) :
      ContDiffAt ℝ 1 (F j) x :=
    ((he x hx).of_le (by norm_num) |>.add (hp x (hφ.2.2.1 hx))).mul
      (((contDiffAt_piLp 2).mp (hu x (hφ.2.2.1 hx)) j).of_le (by norm_num))
  have hint := localEnergyIntegrable_of_positiveTime_regular hforce hu hp hφ
  have hdsame : (fun x ↦ φ x *
      ((nse.kinematicViscosity : ℝ) * ‖spatialVelocityGradient n u x‖ ^ 2)) =
        localEnergyDissipationDensity nse (spatialVelocityGradient n u) φ :=
    funext fun x ↦ by dsimp only [localEnergyDissipationDensity]; ring
  have hd : Integrable (fun x ↦ φ x *
      ((nse.kinematicViscosity : ℝ) * ‖spatialVelocityGradient n u x‖ ^ 2)) := hdsame ▸ hint.1
  have hbalance (x : ℝ^(n + 1)) (hx : x ∈ tsupport φ) :
      (∂[0] e) x - (nse.kinematicViscosity : ℝ) *
        (∑ j : Fin n, (∂[j.succ] (∂[j.succ] e)) x) +
        (nse.kinematicViscosity : ℝ) * ‖spatialVelocityGradient n u x‖ ^ 2 +
        (∑ j : Fin n, (∂[j.succ] (F j)) x) = 0 := by
    have hx' := hφ.2.2.1 hx
    have hud (j : Fin n) : DifferentiableAt ℝ (fun y ↦ u y j) x :=
      ((contDiffAt_piLp 2).mp (hu x hx') j).differentiableAt (by norm_num)
    have h := NavierStokes.local_energy_balance (hu x hx')
      ((hp x hx').differentiableAt (by norm_num)) (hdiv x hx') (hmom x hx')
    have hflux := spatialDivergence_pressureFlux_eq_pressurePower_add
      (fun y ↦ e y + p y) u x
      (((he x hx).of_le (by norm_num) |>.add (hp x hx')).differentiableAt (by norm_num))
      hud
    change (∑ j : Fin n, (∂[j.succ] (F j)) x) =
      bernoulliTransport u p x + (e x + p x) * spatialDivergence n u x at hflux
    rw [show spatialDivergence n u x = 0 from hdiv x hx', mul_zero, add_zero,
      bernoulliTransport_eq_kineticEnergyTransport_add_pressurePower u p x hud
        ((hp x hx').differentiableAt (by norm_num)),
      kineticEnergyTransport_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt
        u x hud (hdiv x hx'),
      pressurePower_eq_spatialDivergence_pressureFlux_of_divergenceFreeAt
        p u x ((hp x hx').differentiableAt (by norm_num)) hud (hdiv x hx')] at hflux
    simp only [hforce, Pi.zero_apply, inner_zero_left] at h
    rw [hflux]
    simpa only [e, spatialLaplacian, add_assoc] using h
  have htested := PDE.Analysis.integral_tested_energy_balance (0 : Fin (n + 1))
    Fin.succ (nse.kinematicViscosity : ℝ) hφ₂ hφ.2.1 he hF hd hbalance
  have ht : Integrable (fun x ↦ (∂[0] φ) x * e x) :=
    hφ.2.1.integrable_of_continuousOn_tsupport (fun x hx ↦
      (((hφ₂.partialDeriv 0 (k := 1) (by norm_num)).continuous.continuousAt).mul
        (he x hx).continuousAt).continuousWithinAt)
      fun x hx ↦ by simp [partialDeriv_eq_zero_of_notMem_tsupport 0 hx]
  have hΔ : Integrable (fun x ↦ spatialLaplacian n φ x * e x) :=
    hφ.2.1.integrable_of_continuousOn_tsupport (fun x hx ↦
      ((continuous_spatialLaplacian hφ₂).continuousAt.mul
        (he x hx).continuousAt).continuousWithinAt)
      fun x hx ↦ by rw [spatialLaplacian_test_zero hx, zero_mul]
  have hdiff : (∫ x, localEnergyDiffusionDensity nse u φ x) =
      (∫ x, (∂[0] φ) x * e x) +
        (nse.kinematicViscosity : ℝ) * ∫ x, spatialLaplacian n φ x * e x := by
    have hid : localEnergyDiffusionDensity nse u φ =
        fun x ↦ (∂[0] φ) x * e x +
          (nse.kinematicViscosity : ℝ) * (spatialLaplacian n φ x * e x) :=
      funext fun x ↦ by dsimp only [localEnergyDiffusionDensity, e]; ring
    rw [hid, integral_add ht (hΔ.const_mul _), integral_const_mul]
  have hf : localEnergyForceDensity nse u φ = 0 :=
    funext fun x ↦ by simp [localEnergyForceDensity, hforce]
  have hFsum : (fun x ↦ ∑ j : Fin n, (∂[j.succ] φ) x * F j x) =
      localEnergyFluxDensity u p φ := funext (energy_flux_sum u p φ)
  rw [hdsame, hFsum] at htested
  change (∫ x, localEnergyDissipationDensity nse (spatialVelocityGradient n u) φ x) =
    (∫ x, (∂[0] φ) x * e x) +
      (nse.kinematicViscosity : ℝ) * (∫ x, spatialLaplacian n φ x * e x) +
      (∫ x, localEnergyFluxDensity u p φ x) + (∫ x : ℝ^(n + 1), φ x * 0) at htested
  rw [← hdiff] at htested
  simpa only [localEnergyDissipation, localEnergyInput, hf, Pi.zero_apply,
    mul_zero, integral_zero, add_zero] using htested

/-- Positive-time classical regularity and momentum imply the local energy inequality. -/
theorem localEnergyInequality_of_positiveTime_regular {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hforce : nse.forcing = 0)
    (hu : ∀ x ∈ finiteTimeDomain n T, ContDiffAt ℝ 2 u x)
    (hp : ∀ x ∈ finiteTimeDomain n T, ContDiffAt ℝ 1 p x)
    (hdiv : ∀ x ∈ finiteTimeDomain n T, DivergenceFreeAt u x)
    (hmom : ∀ x ∈ finiteTimeDomain n T, MomentumEquationAt nse u p x) :
    LocalEnergyInequality nse u p (spatialVelocityGradient n u) T := by
  intro φ hφ
  exact ⟨localEnergyIntegrable_of_positiveTime_regular hforce hu hp hφ,
    (local_energy_tested_equality_of_positiveTime_regular hforce hu hp hdiv hmom hφ).le⟩

/-- Interior continuity gives every local energy integrability exponent. -/
theorem localEnergyMemLp_of_positiveTime_continuous {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : ℝ^(n + 1) → E} {T : ℝ} {q : ENNReal}
    (hf : ∀ x ∈ finiteTimeDomain n T, ContinuousAt f x) : LocalEnergyMemLp f q T := by
  intro K hK hKT
  have hc : ContinuousOn f K := fun x hx ↦ (hf x (hKT hx)).continuousWithinAt
  exact hc.memLp_of_subset_isCompact hK hK.measurableSet Set.Subset.rfl

/-- Changing the gradient representative almost everywhere in the interior slab
preserves the local energy inequality. -/
theorem LocalEnergyInequality.congr_gradient {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ}
    {D E : SpatialGradientField n} {T : ℝ}
    (hD : LocalEnergyInequality nse u p D T)
    (hDE : ∀ᵐ x, x ∈ finiteTimeDomain n T → D x = E x) :
    LocalEnergyInequality nse u p E T := by
  intro φ hφ
  obtain ⟨hint, hineq⟩ := hD φ hφ
  have heq : localEnergyDissipationDensity nse D φ =ᵐ[volume]
      localEnergyDissipationDensity nse E φ := by
    filter_upwards [hDE] with x hx
    by_cases hs : x ∈ tsupport φ
    · simp only [localEnergyDissipationDensity, hx (hφ.2.2.1 hs)]
    · simp [localEnergyDissipationDensity, image_eq_zero_of_notMem_tsupport hs]
  refine ⟨⟨hint.1.congr heq, hint.2⟩, ?_⟩
  unfold localEnergyDissipation at hineq ⊢
  rw [← integral_congr_ae heq]
  exact hineq

/-- A pressure-retaining Leray–Hopf solution with classical positive-time
momentum and compatible weak gradient is suitable. Regularity at time zero
is not required; the existing initial trace and global energy inequality are retained. -/
def PressureRepresentativeLerayHopfSolution.toSuitableOfPositiveTimeRegular
    {n : ℕ} {nse : Problem n} (sol : PressureRepresentativeLerayHopfSolution nse)
    (hforce : nse.forcing = 0)
    (hu : ∀ x ∈ finiteTimeDomain n sol.T, ContDiffAt ℝ 2 sol.u x)
    (hp : ∀ x ∈ finiteTimeDomain n sol.T, ContDiffAt ℝ 1 sol.p x)
    (hdiv : ∀ x ∈ finiteTimeDomain n sol.T, DivergenceFreeAt sol.u x)
    (hmom : ∀ x ∈ finiteTimeDomain n sol.T, MomentumEquationAt nse sol.u sol.p x)
    (hDu : ∀ᵐ x, x ∈ finiteTimeDomain n sol.T →
      spatialVelocityGradient n sol.u x = sol.Du x) :
    SuitableLerayHopfSolution nse where
  toPressureRepresentativeLerayHopfSolution := sol
  velocity_local_memLp_three :=
    localEnergyMemLp_of_positiveTime_continuous fun x hx ↦ (hu x hx).continuousAt
  pressure_local_memLp_three_halves :=
    localEnergyMemLp_of_positiveTime_continuous fun x hx ↦ (hp x hx).continuousAt
  local_energy_inequality :=
    (localEnergyInequality_of_positiveTime_regular hforce hu hp hdiv hmom).congr_gradient hDu

end NavierStokes
