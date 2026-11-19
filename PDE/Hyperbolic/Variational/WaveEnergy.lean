/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.QuadraticEnergy
public import PDE.Analysis.Calculus.PivotChainRule
public import PDE.Analysis.Evolution.Semigroup.Semilinear.Maximal
public import PDE.Hyperbolic.Variational.EnergyLimit

/-!
# Potential energy along mild wave trajectories

The homogeneous wave semigroup preserves the quadratic wave energy. Continuous
pivot forcing changes half that energy by its work against the velocity. For a
source with a pivot gradient potential, the potential chain rule cancels this
work along a semilinear mild solution.

The sign is appropriate to `q_tt + B q = N(q)`: the conserved quantity is half
the quadratic energy minus the source potential. This total energy need not be
coercive, so no global existence follows.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology InnerProductSpace Interval ENNReal

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution PDE.Analysis.Calculus

variable {V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The symmetric pairing whose diagonal is the quadratic wave energy. -/
def waveEnergyForm (B : V →L[ℝ] V →L[ℝ] ℝ) :
    (V × H) →L[ℝ] (V × H) →L[ℝ] ℝ :=
  B.bilinearComp (ContinuousLinearMap.fst ℝ V H) (ContinuousLinearMap.fst ℝ V H) +
    (LinearMap.mkContinuous₂ (innerₗ H) 1 (fun x y ↦ by
      simpa only [innerₗ_apply_apply, one_mul] using norm_inner_le_norm x y)).bilinearComp
      (ContinuousLinearMap.snd ℝ V H) (ContinuousLinearMap.snd ℝ V H)

/-- The pairing combines the spatial form and the pivot inner product. -/
@[simp] theorem waveEnergyForm_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (x y : V × H) :
    waveEnergyForm B x y = B x.1 y.1 + ⟪x.2, y.2⟫_ℝ := rfl

variable [CompleteSpace V] [CompleteSpace H]

/-- A continuous pivot force changes the physical quadratic wave energy by
its work. The displacement and velocity have only their energy-space regularity. -/
theorem forced_autonomousWaveEnergy (S : StronglyContinuousSemigroup (V × H))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (henergy : ∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x) {f : ℝ → H}
    (hf : Continuous f) (x₀ : V × H) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ S s.toNNReal x₀ + S.duhamel (fun r ↦ ((0 : V), f r)) s; (1 / 2 : ℝ) *
      autonomousWaveEnergy B (z t) - (1 / 2 : ℝ) * autonomousWaveEnergy B x₀ = ∫ s in (0 : ℝ)..t,
      ⟪(z s).2, f s⟫_ℝ := by
  have hsymm' (x y : V × H) : waveEnergyForm B x y = waveEnergyForm B y x := by
    simp only [waveEnergyForm_apply, hsymm x.1 y.1, real_inner_comm x.2 y.2]
  have hdiag (x : V × H) : waveEnergyForm B x x = autonomousWaveEnergy B x := by
    simp only [waveEnergyForm_apply, real_inner_self_eq_norm_sq, autonomousWaveEnergy]
  have hpres (t : NNReal) (x : V × H) :
      waveEnergyForm B (S t x) (S t x) = waveEnergyForm B x x := by
    rw [hdiag, hdiag, henergy]
  simpa only [hdiag, waveEnergyForm_apply, map_zero, zero_add] using
    S.quadratic_energy_duhamel (waveEnergyForm B) hsymm' hpres
      ((continuous_const (y := (0 : V))).prodMk hf) x₀ ht

omit [CompleteSpace V] in
/-- The integrated displacement equation differentiates in the pivot space
at positive times. It does not differentiate the displacement in `V`. -/
theorem hasDerivAt_pivot_of_integral_eq (J : V →L[ℝ] H) {z : ℝ → V × H} (hz : Continuous z) (q₀ : V)
    (hkin : ∀ t, 0 ≤ t → (∫ s in (0 : ℝ)..t, (z s).2) = J (z t).1 - J q₀) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ J (z s).1) (z t).2 t := by
  have hp := hz.snd
  have hprimitive := (intervalIntegral.integral_hasDerivAt_right
    (hp.intervalIntegrable (μ := volume) 0 t)
    hp.aestronglyMeasurable.stronglyMeasurableAtFilter hp.continuousAt).const_add (J q₀)
  apply hprimitive.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have h := hkin s hs.le
  change J (z s).1 = J q₀ + ∫ r in (0 : ℝ)..s, (z r).2
  rw [h]
  abel

/-- Conservation of quadratic energy minus the source potential on a finite
mild interval. The linear kinematic identity is the one supplied by the spectral
wave constructor; the nonlinear conservation law is derived here. -/
theorem potential_energy_of_mildSolutionOn (S : StronglyContinuousSemigroup (V × H))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (henergy : ∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x) (J : V →L[ℝ] H)
    (hkin : ∀ (f : ℝ → H), Continuous f → ∀ (x : V × H) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : V), f r)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = J (z t).1 - J x.1)
    (N : C(V × H, H)) (Φ : V → ℝ)
    (hgradient : ∀ (q : V) (p : H), HasFDerivAt Φ ((innerSL ℝ (N (q, p))).comp J) q) {x₀ : V × H}
    {τ : NNReal} {u : C(Icc (0 : ℝ) (τ : ℝ), V × H)}
    (hu : S.IsMildSolutionOn ((ContinuousMap.const (V × H) (0 : V)).prodMk N) x₀ τ u)
    (t : Icc (0 : ℝ) (τ : ℝ)) :
    (1 / 2 : ℝ) * autonomousWaveEnergy B (u t) - Φ (u t).1 =
      (1 / 2 : ℝ) * autonomousWaveEnergy B x₀ - Φ x₀.1 := by
  let v := IccExtend τ.coe_nonneg u
  let f := fun s ↦ N (v s)
  let z := fun s ↦ S s.toNNReal x₀ + S.duhamel (fun r ↦ ((0 : V), f r)) s
  have hv : Continuous v := u.continuous.Icc_extend'
  have hf : Continuous f := N.continuous.comp hv
  have hz : Continuous z := ((S.continuous_orbit x₀).comp continuous_real_toNNReal).add
      (S.continuous_duhamel ((continuous_const (y := (0 : V))).prodMk hf))
  have hzu : ∀ s (hs : s ∈ Icc (0 : ℝ) (τ : ℝ)), z s = u ⟨s, hs⟩ := fun s hs ↦ (hu ⟨s, hs⟩).symm
  have hzv : EqOn z v (Icc (0 : ℝ) (τ : ℝ)) :=
    fun s hs ↦ (hzu s hs).trans (IccExtend_of_mem τ.coe_nonneg u hs).symm
  have hΦcont : Continuous Φ := continuous_iff_continuousAt.mpr fun q ↦ (hgradient q 0).continuousAt
  have hwork : Continuous (fun s ↦ ⟪f s, (z s).2⟫_ℝ) := hf.inner hz.snd
  have hderiv (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivAt (fun r ↦ Φ (z r).1) ⟪f s, (z s).2⟫_ℝ s := by
    have hsτ : s ∈ Icc (0 : ℝ) (τ : ℝ) := ⟨hs.1.le, hs.2.le.trans t.property.2⟩
    have hp := hasDerivAt_pivot_of_integral_eq J hz x₀.1 (hkin f hf x₀) hs.1
    let G : V → H →L[ℝ] ℝ := fun q ↦ innerSL ℝ (N (q, (z s).2))
    have hG : Continuous G := (innerSL ℝ).continuous.comp
        (N.continuous.comp (continuous_id.prodMk continuous_const))
    have hchain := hasDerivAt_of_pivot_gradient J Φ G
      (fun q ↦ hgradient q (z s).2) hG.continuousAt hz.fst.continuousAt hp
    change HasDerivAt (fun r ↦ Φ (z r).1) ⟪N (z s), (z s).2⟫_ℝ s at hchain
    simpa only [f, hzv hsτ] using hchain
  have hpotential := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    t.property.1 (hΦcont.comp hz.fst).continuousOn hderiv
    (hwork.intervalIntegrable (μ := volume) 0 t)
  have hzero : z 0 = x₀ := by
    simp only [z, Real.toNNReal_zero, S.map_zero_apply, S.duhamel_zero, add_zero]
  simp only [Function.comp_apply] at hpotential
  rw [hzero] at hpotential
  have hquadratic := forced_autonomousWaveEnergy S B hsymm henergy hf x₀ t.property.1
  change (1 / 2 : ℝ) * autonomousWaveEnergy B (z t) -
      (1 / 2 : ℝ) * autonomousWaveEnergy B x₀ = _ at hquadratic
  have hworkeq : (∫ s in (0 : ℝ)..(t : ℝ), ⟪(z s).2, f s⟫_ℝ) =
        ∫ s in (0 : ℝ)..(t : ℝ), ⟪f s, (z s).2⟫_ℝ :=
    intervalIntegral.integral_congr fun s _ ↦ real_inner_comm _ _
  rw [hworkeq, hpotential, hzu t t.property] at hquadratic
  linarith

/-- The maximal Picard trajectory conserves the potential energy at every
nonnegative time strictly below its lifespan. -/
theorem potential_energy_maximalMildSolution (S : StronglyContinuousSemigroup (V × H))
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ v w, B v w = B w v)
    (henergy : ∀ t x, autonomousWaveEnergy B (S t x) = autonomousWaveEnergy B x) (J : V →L[ℝ] H)
    (hkin : ∀ (f : ℝ → H), Continuous f → ∀ (x : V × H) (t : ℝ), 0 ≤ t →
      let z := fun s ↦ S s.toNNReal x + S.duhamel (fun r ↦ ((0 : V), f r)) s;
      (∫ s in (0 : ℝ)..t, (z s).2) = J (z t).1 - J x.1)
    (N : C(V × H, H)) (Φ : V → ℝ)
    (hgradient : ∀ (q : V) (p : H), HasFDerivAt Φ ((innerSL ℝ (N (q, p))).comp J) q)
    (hN : LocallyLipschitz ((ContinuousMap.const (V × H) (0 : V)).prodMk N)) (x₀ : V × H) {t : ℝ}
    (ht : 0 ≤ t)
    (hlt : ENNReal.ofReal t < S.mildLifespan ((ContinuousMap.const (V × H) (0 : V)).prodMk N) x₀) :
    let z := S.maximalMildSolution hN x₀; (1 / 2 : ℝ) * autonomousWaveEnergy B (z t) - Φ (z t).1 =
      (1 / 2 : ℝ) * autonomousWaveEnergy B x₀ - Φ x₀.1 := by
  obtain ⟨u, hu, heq⟩ :=
    S.exists_mildSolutionOn_eqOn_maximalMildSolution hN x₀ (τ := t.toNNReal) hlt
  have htmem : t ∈ Icc (0 : ℝ) (t.toNNReal : ℝ) := ⟨ht, (Real.coe_toNNReal t ht).symm.le⟩
  have hpoint : u ⟨t, htmem⟩ = S.maximalMildSolution hN x₀ t :=
    (IccExtend_of_mem t.toNNReal.coe_nonneg u htmem).symm.trans (heq htmem)
  simpa only [hpoint] using
    potential_energy_of_mildSolutionOn S B hsymm henergy J hkin N Φ hgradient hu ⟨t, htmem⟩

end Hyperbolic.Variational
