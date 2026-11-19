/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling.Limit.Classical
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2.OddSupport
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev
public import PDE.Fluid.DeGregorio.DynamicRescaling.TimeDerivative
public import CAS.ExactTactic

/-!
# The normalization rates converge with the L² profile

For the endpoint normalization `c = -u(L)/L`, convergence of the rates
follows from convergence of vorticity. The Hilbert transform carries
vorticity convergence to convergence of `u'` in L². Since `u(0)=0`,
integrating over `[0,L]` gives convergence of `u(L)` and hence of `c`.

Combining this with the stationary-limit theorem uses strong L² convergence,
a uniform H¹ bound, and decay of the time derivative in L².
The velocities converge to the normalized weak primitive of the
limiting Hilbert transform, retaining the identity `c = -u(L)/L`.

Exponential decay of the time derivative in L², or of a weighted time energy,
gives convergence of the boundary rate with an explicit rate of convergence.

## Main results

* `IsClassicalRescaledSolutionOn.exists_rate_limit_of_L2_limit`: the equal endpoint rates
  converge along a strongly L²-convergent family.
* `IsClassicalRescaledSolutionOn.exists_normalized_stationary_limit_of_bounded_h1`: the
  stationary limit with velocity limit `u` and common rate `-u(L)/L`.
* `exists_boundary_rate_limit_of_time_L2_decay`,
  `exists_boundary_rate_limit_of_weighted_time_energy`: convergence of the boundary rate
  as `t → ∞`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio

/-- The equal endpoint-normalized rates have a common limit whenever the
vorticity slices converge strongly in L². -/
theorem IsClassicalRescaledSolutionOn.exists_rate_limit_of_L2_limit
    {a L : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ : ι → ℝ} (hτ : ∀ n, τ n ∈ times)
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    (hrep : ∀ n, realLineRepresentative (f n) = fun x ↦ fields.vorticity x (τ n))
    (hnormalized : ∀ n, fields.velocity 0 (τ n) = 0)
    (hcl : ∀ n, cl (τ n) = -fields.velocity L (τ n) / L)
    (hcw : ∀ n, cw (τ n) = cl (τ n))
    (hf : Tendsto (fun n ↦ realLineCoordinateCLM (baseIndex 1 1) (f n)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F))) :
    ∃ c : ℝ, Tendsto (cl ∘ τ) l (𝓝 c) ∧ Tendsto (cw ∘ τ) l (𝓝 c) := by
  have hpair (n : ι) :
      IsHilbertPair (realLineRepresentative (f n))
        (deriv (fun x ↦ fields.velocity x (τ n))) := by
    rw [hrep n]
    exact hsol.biotSavart (hτ n)
  obtain ⟨H, _hH, hHlim⟩ := exists_hilbertPair_limit_of_tendsto_realLineCoordinate hf hpair
  have hvelocity (n : ι) :
      (∫ x in (0 : ℝ)..L,
        (hpair n).memLp_right.toLp (deriv (fun y ↦ fields.velocity y (τ n))) x) =
          fields.velocity L (τ n) := by
    simpa only [hnormalized n, sub_zero] using
      hsol.intervalIntegral_toLp_velocity_deriv (hτ n) L
  have hlim := ((tendsto_intervalIntegral_of_tendsto_L2 hHlim 0 L).neg).div_const L
  have hcllim : Tendsto (cl ∘ τ) l (𝓝 (-(∫ x in (0 : ℝ)..L, H x) / L)) :=
    hlim.congr' (.of_forall fun n ↦ by simp only [hvelocity n, Function.comp_apply, hcl n])
  exact ⟨_, hcllim, hcllim.congr' (.of_forall fun n ↦ (hcw n).symm)⟩

/-- Strong L² convergence, a uniform H¹ bound, and decay of the time derivative
identify a stationary limit for the equal endpoint normalization. Convergence of
the normalization rates is derived from the vorticity convergence. -/
theorem IsClassicalRescaledSolutionOn.exists_stationary_limit_of_bounded_h1_normalization
    {a L : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ : ι → ℝ} (hτ : ∀ n, τ n ∈ times)
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    (hrep : ∀ n, realLineRepresentative (f n) = fun x ↦ fields.vorticity x (τ n))
    (hnormalized : ∀ n, fields.velocity 0 (τ n) = 0)
    (hcl : ∀ n, cl (τ n) = -fields.velocity L (τ n) / L)
    (hcw : ∀ n, cw (τ n) = cl (τ n))
    {B : ℝ} (hbound : ∀ n, ‖f n‖ ≤ B)
    (ht : ∀ n, MemLp (fun x ↦ deriv (fields.vorticity x) (τ n)) 2 volume)
    (hf : Tendsto (fun n ↦ realLineCoordinateCLM (baseIndex 1 1) (f n)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    (hdecay : Tendsto
      (fun n ↦ (ht n).toLp (fun x ↦ deriv (fields.vorticity x) (τ n))) l (𝓝 0)) :
    ∃ (c : ℝ) (u : ℝ → ℝ),
      Tendsto (cl ∘ τ) l (𝓝 c) ∧ Tendsto (cw ∘ τ) l (𝓝 c) ∧
      Continuous u ∧ u 0 = 0 ∧
      Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
      IsHilbertPair (realLineRepresentative F) (deriv u) ∧
      ∀ᵐ x ∂volume, stationaryResidual a c c (realLineRepresentative F) u x = 0 := by
  obtain ⟨c, hcllim, hcwlim⟩ :=
    hsol.exists_rate_limit_of_L2_limit hτ hrep hnormalized hcl hcw hf
  obtain ⟨u, hu, hu0, hweak, hpair, hstationary⟩ :=
    hsol.exists_stationaryResidual_eq_zero_of_bounded_h1
      hτ hrep hnormalized ht hbound hf hdecay hcllim hcwlim
  exact ⟨c, u, hcllim, hcwlim, hu, hu0, hweak, hpair, hstationary⟩

/-- The velocities converge pointwise to any continuous normalized
weak primitive of the limiting Hilbert transform. L² convergence gives
the Hilbert output convergence, and weak primitive uniqueness identifies
the limit. -/
theorem IsClassicalRescaledSolutionOn.tendsto_velocity_of_L2_limit
    {a : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ : ι → ℝ} (hτ : ∀ n, τ n ∈ times)
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    (hrep : ∀ n, realLineRepresentative (f n) = fun x ↦ fields.vorticity x (τ n))
    (hnormalized : ∀ n, fields.velocity 0 (τ n) = 0)
    (hf : Tendsto (fun n ↦ realLineCoordinateCLM (baseIndex 1 1) (f n)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    {u : ℝ → ℝ} (hu : Continuous u) (hu0 : u 0 = 0)
    (hweak : Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u))
    (hpair : IsHilbertPair (realLineRepresentative F) (deriv u)) (x : ℝ) :
    Tendsto (fun n ↦ fields.velocity x (τ n)) l (𝓝 (u x)) := by
  have hp (n : ι) :
      IsHilbertPair (realLineRepresentative (f n))
        (deriv (fun y ↦ fields.velocity y (τ n))) := by
    rw [hrep n]
    exact hsol.biotSavart (hτ n)
  obtain ⟨H, hH, hHlim⟩ := exists_hilbertPair_limit_of_tendsto_realLineCoordinate hf hp
  have hlimit : (∫ y in (0 : ℝ)..x, H y) = u x := by
    calc
      _ = ∫ y in (0 : ℝ)..x, deriv u y := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hH.ae_eq_right hpair] with y hy _hmem
        exact hy
      _ = u x - u 0 := hweak.intervalIntegral_eq_sub hu 0 x
      _ = u x := by rw [hu0, sub_zero]
  have hvelocity (n : ι) :
      (∫ y in (0 : ℝ)..x,
        (hp n).memLp_right.toLp (deriv (fun z ↦ fields.velocity z (τ n))) y) =
          fields.velocity x (τ n) := by
    simpa only [hnormalized n, sub_zero] using
      hsol.intervalIntegral_toLp_velocity_deriv (hτ n) x
  simpa only [hvelocity, hlimit] using
    tendsto_intervalIntegral_of_tendsto_L2 hHlim 0 x

/-- The stationary limit retains the equal endpoint normalization.
The returned velocity is the pointwise limit of the velocities,
and the common rate is exactly `-u(L)/L`. -/
theorem IsClassicalRescaledSolutionOn.exists_normalized_stationary_limit_of_bounded_h1
    {a L : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ : ι → ℝ} (hτ : ∀ n, τ n ∈ times)
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    (hrep : ∀ n, realLineRepresentative (f n) = fun x ↦ fields.vorticity x (τ n))
    (hnormalized : ∀ n, fields.velocity 0 (τ n) = 0)
    (hcl : ∀ n, cl (τ n) = -fields.velocity L (τ n) / L)
    (hcw : ∀ n, cw (τ n) = cl (τ n))
    {B : ℝ} (hbound : ∀ n, ‖f n‖ ≤ B)
    (ht : ∀ n, MemLp (fun x ↦ deriv (fields.vorticity x) (τ n)) 2 volume)
    (hf : Tendsto (fun n ↦ realLineCoordinateCLM (baseIndex 1 1) (f n)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    (hdecay : Tendsto
      (fun n ↦ (ht n).toLp (fun x ↦ deriv (fields.vorticity x) (τ n))) l (𝓝 0)) :
    ∃ (c : ℝ) (u : ℝ → ℝ),
      Tendsto (cl ∘ τ) l (𝓝 c) ∧ Tendsto (cw ∘ τ) l (𝓝 c) ∧
      Continuous u ∧ u 0 = 0 ∧
      Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
      IsHilbertPair (realLineRepresentative F) (deriv u) ∧
      (∀ x, Tendsto (fun n ↦ fields.velocity x (τ n)) l (𝓝 (u x))) ∧
      c = -u L / L ∧
      ∀ᵐ x ∂volume, stationaryResidual a c c (realLineRepresentative F) u x = 0 := by
  obtain ⟨c, u, hcllim, hcwlim, hu, hu0, hweak, hpair, hstationary⟩ :=
    hsol.exists_stationary_limit_of_bounded_h1_normalization
      hτ hrep hnormalized hcl hcw hbound ht hf hdecay
  have hvelocity := hsol.tendsto_velocity_of_L2_limit hτ hrep hnormalized hf hu hu0 hweak hpair
  have hrate : Tendsto (cl ∘ τ) l (𝓝 (-u L / L)) :=
    ((hvelocity L).neg.div_const L).congr'
      (.of_forall fun n ↦ by simp only [Function.comp_apply, hcl n])
  exact ⟨c, u, hcllim, hcwlim, hu, hu0, hweak, hpair, hvelocity,
    tendsto_nhds_unique hcllim hrate, hstationary⟩

/-- Exponential L² decay of the time derivative forces convergence of
the boundary rate. The Hilbert pair for the differentiated fields comes from
differentiating Biot–Savart in L². -/
theorem exists_boundary_rate_limit_of_time_L2_decay
    {fields : Fields} {rate : ℝ → ℝ} {L a C δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ)
    (hu : ∀ t ∈ Ici a, DifferentiableAt ℝ (fields.velocity L) t)
    (hnormalization : ∀ t ∈ Ici a,
      ∀ᶠ s in 𝓝 t, rate s = -fields.velocity L s / L)
    (hzero : ∀ t ∈ Ici a, ∀ᶠ s in 𝓝 t, fields.velocity 0 s = 0)
    (hv : ∀ t ∈ Ici a,
      ContDiff ℝ 1 (fun x ↦ (timeDifferentiatedFields fields).velocity x t))
    (hpair : ∀ t ∈ Ici a,
      IsHilbertPair (fun x ↦ (timeDifferentiatedFields fields).vorticity x t)
        (deriv (fun x ↦ (timeDifferentiatedFields fields).velocity x t)))
    (hbound : ∀ t (ht : t ∈ Ici a),
      ‖(hpair t ht).memLp_left.toLp
        (fun x ↦ (timeDifferentiatedFields fields).vorticity x t)‖ ≤
          C * Real.exp (-δ * t)) :
    ∃ rateLimit : ℝ, Tendsto rate atTop (𝓝 rateLimit) ∧
      ∀ t ∈ Ici a, |rateLimit - rate t| ≤
        ((√L / L) * C) * Real.exp (-δ * t) / δ := by
  have hderiv (t : ℝ) (ht : t ∈ Ici a) :
      HasDerivAt rate (-(timeDifferentiatedFields fields).velocity L t / L) t :=
    hasDerivAt_boundary_normalization (hu t ht) (hnormalization t ht)
  have hmeas : AEStronglyMeasurable
      (fun t ↦ -(timeDifferentiatedFields fields).velocity L t / L)
      (volume.restrict (Ioi a)) :=
    ((measurable_deriv (fields.velocity L)).neg.div_const L).aestronglyMeasurable
  have hdecay : ∀ t ∈ Ioi a,
      ‖-(timeDifferentiatedFields fields).velocity L t / L‖ ≤
        ((√L / L) * C) * Real.exp (-δ * t) := by
    intro t ht
    have hvzero : (timeDifferentiatedFields fields).velocity 0 t = 0 := by
      change deriv (fields.velocity 0) t = 0
      have hz : fields.velocity 0 =ᶠ[𝓝 t] (fun _ ↦ 0) := hzero t ht.le
      simpa only [deriv_const] using hz.deriv_eq
    rw [Real.norm_eq_abs]
    exact (IsHilbertPair.abs_boundary_normalization_le_L2 hL
      (hpair t ht.le) (hv t ht.le) hvzero).trans
      ((mul_le_mul_of_nonneg_left (hbound t ht.le)
        (div_nonneg (Real.sqrt_nonneg _) hL.le)).trans_eq (mul_assoc _ _ _).symm)
  simpa only [Real.norm_eq_abs] using
    Evolution.exists_limit_of_hasDerivAt_norm_le_exp hδ hderiv hmeas hdecay

/-- Weighted energy decay provides both the boundary-rate limit and
its convergence estimate. Oddness, support, and the positive weight floor
turn weighted energy into the L² bound used by normalization. -/
theorem exists_boundary_rate_limit_of_weighted_time_energy
    {fields : Fields} {rate φ : ℝ → ℝ} {L c a E δ : ℝ}
    (hL : 0 < L) (hc : 0 < c) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hu : ∀ t ∈ Ici a, DifferentiableAt ℝ (fields.velocity L) t)
    (hnormalization : ∀ t ∈ Ici a,
      ∀ᶠ s in 𝓝 t, rate s = -fields.velocity L s / L)
    (hzero : ∀ t ∈ Ici a, ∀ᶠ s in 𝓝 t, fields.velocity 0 s = 0)
    (hv : ∀ t ∈ Ici a,
      ContDiff ℝ 1 (fun x ↦ (timeDifferentiatedFields fields).velocity x t))
    (hpair : ∀ t ∈ Ici a,
      IsHilbertPair (fun x ↦ (timeDifferentiatedFields fields).vorticity x t)
        (deriv (fun x ↦ (timeDifferentiatedFields fields).velocity x t)))
    (hodd : ∀ t ∈ Ici a,
      Function.Odd (fun x ↦ (timeDifferentiatedFields fields).vorticity x t))
    (hsupport : ∀ t ∈ Ici a, ∀ x, L ≤ x →
      (timeDifferentiatedFields fields).vorticity x t = 0)
    (hφ : ∀ᵐ x ∂volume.restrict (Ioo 0 L), c ≤ φ x)
    (hint : ∀ t ∈ Ici a, IntegrableOn
      (fun x ↦ (timeDifferentiatedFields fields).vorticity x t ^ 2 * φ x) (Ioo 0 L))
    (hbound : ∀ t ∈ Ici a,
      (∫ x in Ioo 0 L, (timeDifferentiatedFields fields).vorticity x t ^ 2 * φ x) ≤
        E * Real.exp (-(2 * δ) * (t - a))) :
    ∃ rateLimit : ℝ, Tendsto rate atTop (𝓝 rateLimit) ∧
      ∀ t ∈ Ici a, |rateLimit - rate t| ≤
        ((√L / L) * (√(2 * (E / c)) * Real.exp (δ * a))) *
          Real.exp (-δ * t) / δ := by
  apply exists_boundary_rate_limit_of_time_L2_decay hL hδ hu hnormalization hzero hv hpair
  intro t ht
  calc
    _ ≤ √(2 * (E / c)) * Real.exp (-δ * (t - a)) :=
      norm_toLp_le_exp_of_weighted_energy_bound hc hE (hpair t ht).memLp_left
        (hodd t ht) (hsupport t ht) hφ (hint t ht) (hbound t ht)
    _ = (√(2 * (E / c)) * Real.exp (δ * a)) * Real.exp (-δ * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      cas

end DeGregorio
