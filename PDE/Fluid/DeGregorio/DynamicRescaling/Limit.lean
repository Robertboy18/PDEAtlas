/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.Limit
public import PDE.Fluid.DeGregorio.DynamicRescaling.Stationary
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence
public import PDE.Fluid.DeGregorio.DynamicRescaling.Limit.Transport

/-!
# The stationary equation at a bounded H¹ limit

A limit of rescaled states is a stationary profile when the time derivatives tend
to zero in L². Strong L² convergence of vorticity, a uniform H¹ bound, and convergent
normalization rates suffice to pass the rescaled equation to its limit.

The Hilbert transform is continuous on L². Its normalized primitive
converges uniformly on compact intervals, while the spatial derivative of
vorticity converges weakly in L². Testing the transport equation pairs
these two factors and identifies the stationary equation. The resulting
velocity is continuous and satisfies Biot–Savart almost everywhere.

Strong H¹ convergence also gives a direct pointwise passage through the
equation. Both arguments use the same construction of the limiting velocity.

## Main results

* `exists_stationary_equation_of_bounded_h1`: the stationary equation at a strong L²
  limit of a bounded H¹ family.
* `exists_stationaryResidual_eq_zero_of_bounded_h1`: the same limit has a continuous
  velocity `u` with `u 0 = 0` and `u' = HF`, and its stationary residual vanishes a.e.
* `exists_h1_stationaryResidual_eq_zero_of_L2_limit`: the L² limit itself carries an
  H¹ graph with the same bound.
* `exists_stationaryResidual_eq_zero_of_h1_limit`: the version for strong H¹ convergence.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory PDE.Analysis SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace DeGregorio

/-- A transport equation with a vanishing L² time derivative becomes
stationary when its spatial factors converge. The derivative and stretching
factors need only converge in L²; the vorticity and velocity converge pointwise. -/
theorem stationary_equation_ae_of_tendsto_L2
    {f u : ℕ → ℝ → ℝ} {f₀ u₀ : ℝ → ℝ}
    {g h w : ℕ → Lp ℝ 2 (volume : Measure ℝ)}
    {g₀ h₀ : Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ : ℝ} {cl cw : ℕ → ℝ}
    (hf : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (f₀ x)))
    (hu : ∀ x, Tendsto (fun n ↦ u n x) atTop (𝓝 (u₀ x)))
    (hg : Tendsto g atTop (𝓝 g₀)) (hh : Tendsto h atTop (𝓝 h₀))
    (hw : Tendsto w atTop (𝓝 0))
    (hcl : Tendsto cl atTop (𝓝 cl₀)) (hcw : Tendsto cw atTop (𝓝 cw₀))
    (heq : ∀ n, ∀ᵐ x ∂volume,
      w n x + (cl n * x + a * u n x) * g n x = (cw n + h n x) * f n x) :
    ∀ᵐ x ∂volume, (cl₀ * x + a * u₀ x) * g₀ x = (cw₀ + h₀ x) * f₀ x := by
  obtain ⟨s, hs, hgs⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  obtain ⟨r, hr, hhr⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hh.comp hs.tendsto_atTop)).exists_seq_tendsto_ae
  obtain ⟨q, hq, hwq⟩ :=
    (tendstoInMeasure_of_tendsto_Lp
      ((hw.comp hs.tendsto_atTop).comp hr.tendsto_atTop)).exists_seq_tendsto_ae
  have hindex := hs.tendsto_atTop.comp (hr.tendsto_atTop.comp hq.tendsto_atTop)
  filter_upwards [hgs, hhr, hwq, Lp.coeFn_zero ℝ 2 volume, ae_all_iff.mpr heq]
    with x hgx hhx hwx hzero hx
  have hleft := hwx.add
    ((((hcl.comp hindex).mul_const x).add
      (((hu x).comp hindex).const_mul a)).mul
        (hgx.comp (hr.tendsto_atTop.comp hq.tendsto_atTop)))
  have hright := ((hcw.comp hindex).add (hhx.comp hq.tendsto_atTop)).mul
    ((hf x).comp hindex)
  have heqLimit := tendsto_nhds_unique hleft
    (hright.congr' (.of_forall fun n ↦ (hx (s (r (q n)))).symm))
  simpa only [hzero, Pi.zero_apply, zero_add] using heqLimit

/-- H¹ convergence gives the limiting vorticity and spatial derivative.
Biot–Savart gives the velocity derivative limit, and integration gives the
normalized velocity limit. The analytic hypotheses are convergence of the rates
and decay of the time-derivative coordinate. -/
theorem exists_stationary_equation_of_h1_limit
    {f : ℕ → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    {h w : ℕ → Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ : ℝ} {cl cw : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 F))
    (hpair : ∀ n, IsHilbertPair (realLineRepresentative (f n)) (h n))
    (hw : Tendsto w atTop (𝓝 0))
    (hcl : Tendsto cl atTop (𝓝 cl₀)) (hcw : Tendsto cw atTop (𝓝 cw₀))
    (heq : ∀ n, ∀ᵐ x ∂volume,
      w n x + (cl n * x + a * ∫ y in (0 : ℝ)..x, h n y) *
          realLineCoordinateCLM (singleDerivIndex 1 0) (f n) x =
        (cw n + h n x) * realLineRepresentative (f n) x) :
    ∃ H : Lp ℝ 2 (volume : Measure ℝ),
      IsHilbertPair (realLineRepresentative F) H ∧
        ∀ᵐ x ∂volume,
          (cl₀ * x + a * ∫ y in (0 : ℝ)..x, H y) *
              realLineCoordinateCLM (singleDerivIndex 1 0) F x =
            (cw₀ + H x) * realLineRepresentative F x := by
  obtain ⟨H, hH, hHlim⟩ := exists_hilbertPair_limit_of_tendsto_H1 hf hpair
  simp only [Lp.toLp_coeFn] at hHlim
  refine ⟨H, hH, stationary_equation_ae_of_tendsto_L2 ?_ ?_ ?_ hHlim hw hcl hcw heq⟩
  · intro x
    exact ((lipschitzWith_realLineRepresentative_eval x).continuous.tendsto F).comp hf
  · intro x
    exact tendsto_intervalIntegral_of_tendsto_L2 hHlim 0 x
  · exact ((realLineCoordinateCLM (singleDerivIndex 1 0)).continuous.tendsto F).comp hf

/-- A Sobolev stationary equation gives a continuous normalized velocity
whose almost-everywhere derivative is the Hilbert transform. The stationary
residual then uses derivatives of the two continuous representatives. -/
theorem exists_stationaryResidual_eq_zero_of_stationary_equation
    {F : W^{1,2}((Set.univ : Set (ℝ^1)))} {H : Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ : ℝ}
    (hH : IsHilbertPair (realLineRepresentative F) H)
    (hstationary : ∀ᵐ x ∂volume,
      (cl₀ * x + a * ∫ y in (0 : ℝ)..x, H y) *
          realLineCoordinateCLM (singleDerivIndex 1 0) F x =
        (cw₀ + H x) * realLineRepresentative F x) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u 0 = 0 ∧
      Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
      IsHilbertPair (realLineRepresentative F) (deriv u) ∧
      ∀ᵐ x ∂volume, stationaryResidual a cl₀ cw₀ (realLineRepresentative F) u x = 0 := by
  let u : ℝ → ℝ := fun x ↦ ∫ y in (0 : ℝ)..x, H y
  have hloc : LocallyIntegrable (H : ℝ → ℝ) volume :=
    (Lp.memLp H).locallyIntegrable (by norm_num)
  have hcontinuous : Continuous u :=
    intervalIntegral.continuous_primitive
      (fun _ _ ↦ (hloc.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) 0
  have hu : ∀ᵐ x ∂volume, HasDerivAt u (H x) x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hloc] with x hx
    exact hx 0
  have hderiv : (H : ℝ → ℝ) =ᵐ[volume] deriv u := by
    filter_upwards [hu] with x hx
    exact hx.deriv.symm
  have hweak := (Evolution.hasWeakTimeDerivativeOn_intervalPrimitive hloc 0).congr_ae
    Filter.EventuallyEq.rfl hderiv
  refine ⟨u, hcontinuous, by simp [u], hweak, hH.congr_right_ae hderiv, ?_⟩
  have hFloc := locallyIntegrableOn_univ.mp
    (hasWeakTimeDerivativeOn_realLineCoordinates F).locallyIntegrable_g
  have hFderiv :
      ∀ᵐ x ∂volume, HasDerivAt (realLineRepresentative F)
        (realLineCoordinateCLM (singleDerivIndex 1 0) F x) x :=
    SobolevSpace.Slices.ae_hasDerivAt_lineRepresentative_of_locallyIntegrable hFloc
  filter_upwards [hstationary, hu, hFderiv] with x hx hux hFx
  unfold stationaryResidual
  rw [hux.deriv, hFx.deriv]
  exact sub_eq_zero.mpr hx.symm

/-- A uniform H¹ bound and strong L² convergence of vorticity suffice to
pass the rescaled equation to a stationary limit. The first derivative
converges weakly; the Hilbert transform and its normalized primitive provide
the strongly convergent factors needed to test the transport term. -/
theorem exists_stationary_equation_of_bounded_h1
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    {h w : ι → Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ B : ℝ} {cl cw : ι → ℝ}
    (hbound : ∀ i, ‖f i‖ ≤ B)
    (hf : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (f i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    (hpair : ∀ i, IsHilbertPair (realLineRepresentative (f i)) (h i))
    (hw : Tendsto w l (𝓝 0))
    (hcl : Tendsto cl l (𝓝 cl₀)) (hcw : Tendsto cw l (𝓝 cw₀))
    (heq : ∀ i, ∀ᵐ x ∂volume,
      w i x + (cl i * x + a * ∫ y in (0 : ℝ)..x, h i y) *
          realLineCoordinateCLM (singleDerivIndex 1 0) (f i) x =
        (cw i + h i x) * realLineRepresentative (f i) x) :
    ∃ H : Lp ℝ 2 (volume : Measure ℝ),
      IsHilbertPair (realLineRepresentative F) H ∧
        ∀ᵐ x ∂volume,
          (cl₀ * x + a * ∫ y in (0 : ℝ)..x, H y) *
              realLineCoordinateCLM (singleDerivIndex 1 0) F x =
            (cw₀ + H x) * realLineRepresentative F x := by
  obtain ⟨H, hH, hHlim⟩ :=
    exists_hilbertPair_limit_of_tendsto_realLineCoordinate hf hpair
  simp only [Lp.toLp_coeFn] at hHlim
  have hg := tendsto_weak_realLineCoordinate_of_h1_bound f F hbound hf
    (singleDerivIndex 1 0)
  have hgBound : ∀ i, ‖realLineCoordinateCLM (singleDerivIndex 1 0) (f i)‖ ≤ B :=
    fun i ↦ (norm_realLineCoordinateCLM_le _ _).trans (hbound i)
  have heqBase : ∀ i, ∀ᵐ x ∂volume,
      w i x + (cl i * x + a * l2Primitive (h i) x) *
          realLineCoordinateCLM (singleDerivIndex 1 0) (f i) x =
        (cw i + h i x) * realLineCoordinateCLM (baseIndex 1 1) (f i) x := by
    intro i
    filter_upwards [heq i, realLineCoordinate_ae_representative (f i)] with x hx hfx
    simpa only [l2Primitive, hfx] using hx
  have hstationary := Evolution.ae_stationary_transport_of_strong_weak_L2_limits
    hf hHlim hw hg hgBound hcl hcw heqBase
  refine ⟨H, hH, ?_⟩
  filter_upwards [hstationary, realLineCoordinate_ae_representative F] with x hx hfx
  simpa only [l2Primitive, hfx] using hx

/-- Strong L² convergence, a uniform H¹ bound, and decay of the
time derivative produce a stationary Sobolev profile and its Biot–Savart
velocity. -/
theorem exists_stationaryResidual_eq_zero_of_bounded_h1
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    {h w : ι → Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ B : ℝ} {cl cw : ι → ℝ}
    (hbound : ∀ i, ‖f i‖ ≤ B)
    (hf : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (f i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) F)))
    (hpair : ∀ i, IsHilbertPair (realLineRepresentative (f i)) (h i))
    (hw : Tendsto w l (𝓝 0))
    (hcl : Tendsto cl l (𝓝 cl₀)) (hcw : Tendsto cw l (𝓝 cw₀))
    (heq : ∀ i, ∀ᵐ x ∂volume,
      w i x + (cl i * x + a * ∫ y in (0 : ℝ)..x, h i y) *
          realLineCoordinateCLM (singleDerivIndex 1 0) (f i) x =
        (cw i + h i x) * realLineRepresentative (f i) x) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u 0 = 0 ∧
      Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
      IsHilbertPair (realLineRepresentative F) (deriv u) ∧
      ∀ᵐ x ∂volume, stationaryResidual a cl₀ cw₀ (realLineRepresentative F) u x = 0 := by
  obtain ⟨H, hH, hstationary⟩ :=
    exists_stationary_equation_of_bounded_h1 hbound hf hpair hw hcl hcw heq
  exact exists_stationaryResidual_eq_zero_of_stationary_equation hH hstationary

/-- The limiting L² class acquires its own H¹ graph from the uniform bound.
When the time derivative vanishes and the rates converge, that graph is a
stationary profile with a continuous normalized Biot–Savart velocity. -/
theorem exists_h1_stationaryResidual_eq_zero_of_L2_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {f : ι → W^{1,2}((Set.univ : Set (ℝ^1)))} {F₀ : Lp ℝ 2 (volume : Measure ℝ)}
    {h w : ι → Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ B : ℝ} {cl cw : ι → ℝ}
    (hbound : ∀ i, ‖f i‖ ≤ B)
    (hf : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (f i)) l (𝓝 F₀))
    (hpair : ∀ i, IsHilbertPair (realLineRepresentative (f i)) (h i))
    (hw : Tendsto w l (𝓝 0))
    (hcl : Tendsto cl l (𝓝 cl₀)) (hcw : Tendsto cw l (𝓝 cw₀))
    (heq : ∀ i, ∀ᵐ x ∂volume,
      w i x + (cl i * x + a * ∫ y in (0 : ℝ)..x, h i y) *
          realLineCoordinateCLM (singleDerivIndex 1 0) (f i) x =
        (cw i + h i x) * realLineRepresentative (f i) x) :
    ∃ F : W^{1,2}((Set.univ : Set (ℝ^1))), ‖F‖ ≤ B ∧
      realLineCoordinateCLM (baseIndex 1 1) F = F₀ ∧
      ∃ u : ℝ → ℝ, Continuous u ∧ u 0 = 0 ∧
        Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
        IsHilbertPair (realLineRepresentative F) (deriv u) ∧
        ∀ᵐ x ∂volume, stationaryResidual a cl₀ cw₀ (realLineRepresentative F) u x = 0 := by
  obtain ⟨F, hF, hFbase⟩ := exists_h1_of_tendsto_realLineCoordinate f F₀ hbound hf
  refine ⟨F, hF, hFbase, ?_⟩
  exact exists_stationaryResidual_eq_zero_of_bounded_h1 hbound
    (hFbase ▸ hf) hpair hw hcl hcw heq

/-- Under strong H¹ convergence, the limit `F` has a continuous velocity `u` with
`u 0 = 0` and `u' = HF`, and the stationary residual of `(F, u)` vanishes almost
everywhere. -/
theorem exists_stationaryResidual_eq_zero_of_h1_limit
    {f : ℕ → W^{1,2}((Set.univ : Set (ℝ^1)))} {F : W^{1,2}((Set.univ : Set (ℝ^1)))}
    {h w : ℕ → Lp ℝ 2 (volume : Measure ℝ)}
    {a cl₀ cw₀ : ℝ} {cl cw : ℕ → ℝ}
    (hf : Tendsto f atTop (𝓝 F))
    (hpair : ∀ n, IsHilbertPair (realLineRepresentative (f n)) (h n))
    (hw : Tendsto w atTop (𝓝 0))
    (hcl : Tendsto cl atTop (𝓝 cl₀)) (hcw : Tendsto cw atTop (𝓝 cw₀))
    (heq : ∀ n, ∀ᵐ x ∂volume,
      w n x + (cl n * x + a * ∫ y in (0 : ℝ)..x, h n y) *
          realLineCoordinateCLM (singleDerivIndex 1 0) (f n) x =
        (cw n + h n x) * realLineRepresentative (f n) x) :
    ∃ u : ℝ → ℝ, Continuous u ∧ u 0 = 0 ∧
      Evolution.HasWeakTimeDerivativeOn Set.univ u (deriv u) ∧
      IsHilbertPair (realLineRepresentative F) (deriv u) ∧
      ∀ᵐ x ∂volume, stationaryResidual a cl₀ cw₀ (realLineRepresentative F) u x = 0 := by
  obtain ⟨H, hH, hstationary⟩ := exists_stationary_equation_of_h1_limit
    hf hpair hw hcl hcw heq
  exact exists_stationaryResidual_eq_zero_of_stationary_equation hH hstationary

end DeGregorio
