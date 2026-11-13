/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.VectorHarmonics
public import PDE.CoordinateSystems.Spherical.AxisymmetricIntegration
import PDE.CoordinateSystems.Spherical.Symmetry

/-!
# Expansion of axisymmetric vector fields on the unit sphere

A vector field `u` on `ℝ³` that commutes with the rotations about the symmetry axis is
determined on the unit sphere by its meridian profile `v θ = u (point 1 θ 0)`. The sphere
measure `σ` of an axisymmetric function is `2π` times `sin θ dθ` on `(0, π)`, so `u` is square
integrable on the sphere exactly when its profile is square integrable for `sin θ dθ`, with
`‖u‖²_{L²(σ)} = 2π ‖v‖²`. The profile expands in the meridian vector harmonics `Y_l, X_l, Z_l`;
rotating each term to the azimuth of the point gives the expansion of `u` itself, and the
partial sums converge to `u` in `L²(σ)`.

## Main results

* `aestronglyMeasurable_meridian_of_sphere`: the profile of an equivariant field that is almost
  everywhere strongly measurable on the sphere is measurable for `sin θ dθ`.
* `axisymmetric_vectorHarmonic_expansion_sphere`: the profile is square integrable, the sphere
  norm is `2π` times the profile norm, and the rotated partial sums converge in `L²(σ)`.
* `ae_memLp_meridian`: for a square-integrable measurable equivariant field on a ball, the
  meridian profile `θ ↦ u (point r θ 0)` is square integrable for `sin θ dθ` at almost every
  radius; `lintegral_meridian_ofReal` converts the meridian lintegrals of the polar formula.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open MeasureTheory Filter Set Topology PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ENNReal

/-- A point of the unit sphere with polar angle in `(0, π)` is off the symmetry axis. -/
theorem radialFrame_notMem_symmetryAxis {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) (φ : ℝ) :
    radialFrame θ φ ∉ symmetryAxis := by
  simpa [point] using point_notMem_symmetryAxis one_pos hθ φ

/-- The azimuth of the meridian point of azimuth zero and polar angle in `(0, π)` is `0`. -/
theorem azimuthalAngle_radialFrame_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    azimuthalAngle (radialFrame θ 0) = 0 := by
  have h : (⟨radialFrame θ 0 0, radialFrame θ 0 1⟩ : ℂ) = ((Real.sin θ : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [radialFrame, Complex.sin_ofReal_re]
  rw [azimuthalAngle, h, Complex.arg_ofReal_of_nonneg (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).le]

/-- Rotations about the axis keep the symmetry axis and its complement. -/
theorem axisRotation_mem_symmetryAxis_iff (φ : ℝ) (x : ℝ^3) :
    axisRotation φ x ∈ symmetryAxis ↔ x ∈ symmetryAxis := by
  simp [symmetryAxis]

/-- The rotated vector harmonic at a meridian point of azimuth zero is the vector harmonic. -/
theorem axisRotation_vectorHarmonic_radialFrame_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) (l : ℕ)
    (k : Fin 3) :
    axisRotation (azimuthalAngle (radialFrame θ 0))
        (vectorHarmonic l k (polarAngle (radialFrame θ 0))) = vectorHarmonic l k θ := by
  rw [azimuthalAngle_radialFrame_zero hθ, axisRotation_zero,
    polarAngle_radialFrame (Ioo_subset_Icc_self hθ)]

/-- Off the symmetry axis, the vector harmonic rotated to the azimuth of a point commutes with
the rotations about the axis. -/
theorem axisRotation_vectorHarmonic_axisRotation {x : ℝ^3} (hx : x ∉ symmetryAxis) (φ : ℝ)
    (l : ℕ) (k : Fin 3) :
    axisRotation (azimuthalAngle (axisRotation φ x))
        (vectorHarmonic l k (polarAngle (axisRotation φ x))) =
      axisRotation φ (axisRotation (azimuthalAngle x) (vectorHarmonic l k (polarAngle x))) := by
  rw [polarAngle_axisRotation, axisRotation_vectorHarmonic, axisRotation_vectorHarmonic,
    axisRotation_smul, ← axialRotation_apply φ x, frame_azimuthalAngle_axialRotation _ _ hx,
    axialRotation_apply]

/-- The points of the unit sphere on the symmetry axis form a null set. -/
theorem toSphere_symmetryAxis :
    (volume : Measure (ℝ^3)).toSphere {ω | (ω : ℝ^3) ∈ symmetryAxis} = 0 := by
  have hclosed : IsClosed symmetryAxis :=
    isClosed_eq (by unfold cylindricalRadius cylindricalRadiusSq; fun_prop) continuous_const
  have hmeas : MeasurableSet {ω : Metric.sphere (0 : ℝ^3) 1 | (ω : ℝ^3) ∈ symmetryAxis} :=
    measurable_subtype_coe hclosed.measurableSet
  rw [toSphere_eq_map_anglePoint, Measure.map_apply measurableEmbedding_anglePoint.measurable hmeas]
  convert measure_empty (μ := angleMeasure)
  ext p
  simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  exact radialFrame_notMem_symmetryAxis p.2.1 p.1.2

/-- The meridian profile of an equivariant field that is almost everywhere strongly measurable on
the unit sphere is almost everywhere strongly measurable for `sin θ dθ` on `(0, π)`. -/
theorem aestronglyMeasurable_meridian_of_sphere {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u)
    (hm : AEStronglyMeasurable (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ u ω)
      (volume : Measure (ℝ^3)).toSphere) :
    AEStronglyMeasurable (fun θ ↦ u (point 1 θ 0)) polarAngleMeasure := by
  rw [toSphere_eq_map_anglePoint, measurableEmbedding_anglePoint.aestronglyMeasurable_map_iff]
    at hm
  set ν : Measure (ℝ × ℝ) := (volume : Measure (ℝ × ℝ)).withDensity
    fun p ↦ ENNReal.ofReal (Real.sin p.1) with hν
  have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ u (radialFrame q.1 q.2))
      (ν.restrict angleDomain) := by
    rw [← map_comap_subtype_coe measurableSet_angleDomain,
      (MeasurableEmbedding.subtype_coe measurableSet_angleDomain).aestronglyMeasurable_map_iff]
    exact hm
  have h2 : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ u (radialFrame q.1 q.2))
      (volume.restrict angleDomain) := by
    refine h1.mono_ac ?_
    rw [hν, restrict_withDensity measurableSet_angleDomain]
    refine withDensity_absolutelyContinuous' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_angleDomain] with q hq
    exact (ENNReal.ofReal_pos.mpr (Real.sin_pos_of_pos_of_lt_pi hq.1.1 hq.1.2)).ne'
  have hrot : Continuous (Function.uncurry fun (φ : ℝ) (v : ℝ^3) ↦ axisRotation φ v) :=
    contDiff_axialRotation_apply.continuous
  have h3 : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ u (point 1 q.1 0))
      (volume.restrict angleDomain) := by
    refine (hrot.comp_aestronglyMeasurable₂ (continuous_snd.neg.aestronglyMeasurable) h2).congr
      (ae_of_all _ fun q ↦ ?_)
    have h := eq_axisRotation_of_isEquivariantUnderAxisRotation hu 1 q.1 q.2
    simp only [point, one_smul, Pi.neg_apply] at h ⊢
    rw [h, axisRotation_neg_apply]
  rw [angleDomain, Measure.volume_eq_prod, ← Measure.prod_restrict] at h3
  have hne : (volume.restrict (Ioo 0 (2 * Real.pi)) : Measure ℝ) ≠ 0 := by
    simp [Real.pi_pos]
  exact (h3.of_comp_fst hne).mono_ac (withDensity_absolutelyContinuous _ _)

/-- The norm of an equivariant field is invariant under the rotations about the axis. -/
theorem norm_apply_axisRotation_of_isEquivariant {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) (φ : ℝ) (x : ℝ^3) :
    ‖u (axisRotation φ x)‖ = ‖u x‖ := by
  rw [hu, ← axialRotation_apply, LinearIsometryEquiv.norm_map]

/-- The meridian profile of an equivariant field that is square integrable on the unit sphere is
square integrable for `sin θ dθ` on `(0, π)`. -/
theorem memLp_meridian_of_sphere {u : ℝ^3 → ℝ^3} (hu : IsEquivariantUnderAxisRotation u)
    (hL2 : MemLp (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ u ω) 2
      (volume : Measure (ℝ^3)).toSphere) :
    MemLp (fun θ ↦ u (point 1 θ 0)) 2 polarAngleMeasure := by
  have hm := aestronglyMeasurable_meridian_of_sphere hu hL2.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ⟨hm.norm.pow 2, ?_⟩
  have hfin :=
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).mp hL2).hasFiniteIntegral
  unfold HasFiniteIntegral at hfin ⊢
  have hinv : IsInvariantUnderAxisRotation (fun x : ℝ^3 ↦ ‖‖u x‖ ^ 2‖ₑ) := fun φ x ↦ by
    simp only [norm_apply_axisRotation_of_isEquivariant hu]
  rw [lintegral_sphere_of_axisymmetric hinv] at hfin
  have h2π : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by simp [Real.pi_pos]
  have hX : ∫⁻ θ in Ioo 0 Real.pi, ENNReal.ofReal (Real.sin θ) * ‖‖u (radialFrame θ 0)‖ ^ 2‖ₑ
      < ∞ := by
    rcases ENNReal.mul_lt_top_iff.mp hfin with h | h | h
    · exact h.2
    · exact absurd h h2π
    · rw [h]
      exact ENNReal.zero_lt_top
  rw [polarAngleMeasure, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    (by fun_prop) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simpa [point] using hX

/-- The squared `L²` norm of an equivariant field on the unit sphere is `2π` times the squared
norm of its meridian profile for `sin θ dθ`. No integrability hypothesis is needed. -/
theorem integral_sphere_norm_sq_of_isEquivariant {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u) :
    ∫ ω, ‖u ω‖ ^ 2 ∂(volume : Measure (ℝ^3)).toSphere =
      2 * Real.pi * ∫ θ, ‖u (point 1 θ 0)‖ ^ 2 ∂polarAngleMeasure := by
  have hinv : IsInvariantUnderAxisRotation (fun x : ℝ^3 ↦ ‖u x‖ ^ 2) := fun φ x ↦ by
    simp only [norm_apply_axisRotation_of_isEquivariant hu]
  rw [integral_sphere_of_axisymmetric hinv, integral_polarAngleMeasure_eq]
  simp [point]

/-- The partial sum of rotated vector harmonics with coefficients `a`. -/
private def rotatedPartialSum (a : ℕ → Fin 3 → ℝ) (N : ℕ) (x : ℝ^3) : ℝ^3 :=
  ∑ l ∈ Finset.range N, ∑ k : Fin 3,
    a l k • axisRotation (azimuthalAngle x) (vectorHarmonic l k (polarAngle x))

private theorem rotatedPartialSum_axisRotation (a : ℕ → Fin 3 → ℝ) (N : ℕ) {x : ℝ^3}
    (hx : x ∉ symmetryAxis) (φ : ℝ) :
    rotatedPartialSum a N (axisRotation φ x) = axisRotation φ (rotatedPartialSum a N x) := by
  simp only [rotatedPartialSum, axisRotation_vectorHarmonic_axisRotation hx]
  simp only [← axialRotation_apply, map_sum, map_smul]

/-- **Expansion of an axisymmetric field on the unit sphere.** Let `u` commute with the
rotations about the symmetry axis and be square integrable on the unit sphere for its surface
measure `σ`. Then the meridian profile `v θ = u (point 1 θ 0)` is square integrable for
`sin θ dθ` on `(0, π)`, `∫ ‖u‖² dσ = 2π ∫ ‖v‖² sin θ dθ`, and the partial sums
`∑_{l < N} ∑_k v_l^k R_φ (Y_{l,k} (θ))` of the vector harmonic expansion of `v`, rotated to the
azimuth `φ` of the point, converge to `u` in `L²(σ)`. The parity selection of
`axisymmetric_vectorHarmonic_expansion` applies to the coefficients of `v`. -/
theorem axisymmetric_vectorHarmonic_expansion_sphere {u : ℝ^3 → ℝ^3}
    (hu : IsEquivariantUnderAxisRotation u)
    (hL2 : MemLp (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ u ω) 2
      (volume : Measure (ℝ^3)).toSphere) :
    ∃ hv : MemLp (fun θ ↦ u (point 1 θ 0)) 2 polarAngleMeasure,
      ∫ ω, ‖u ω‖ ^ 2 ∂(volume : Measure (ℝ^3)).toSphere =
          2 * Real.pi * ∫ θ, ‖u (point 1 θ 0)‖ ^ 2 ∂polarAngleMeasure ∧
        Tendsto (fun N ↦ ∫ ω, ‖u ω - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
            vectorHarmonicCoeff (hv.toLp _) l k •
              axisRotation (azimuthalAngle ω) (vectorHarmonic l k (polarAngle ω))‖ ^ 2
            ∂(volume : Measure (ℝ^3)).toSphere) atTop (𝓝 0) := by
  have hv := memLp_meridian_of_sphere hu hL2
  refine ⟨hv, integral_sphere_norm_sq_of_isEquivariant hu, ?_⟩
  set V : Lp (ℝ^3) 2 polarAngleMeasure := hv.toLp _ with hV
  set a : ℕ → Fin 3 → ℝ := vectorHarmonicCoeff V with ha
  set P : ℕ → Lp (ℝ^3) 2 polarAngleMeasure := fun N ↦
    ∑ l ∈ Finset.range N, ∑ k : Fin 3, a l k • vectorHarmonicLp l k with hP
  set G : ℕ → ℝ^3 → ℝ := fun N ↦
    symmetryAxisᶜ.indicator fun x ↦ ‖u x - rotatedPartialSum a N x‖ ^ 2 with hG
  have hGinv (N : ℕ) : IsInvariantUnderAxisRotation (G N) := by
    intro φ x
    by_cases hx : x ∈ symmetryAxis
    · have hx' : axisRotation φ x ∈ symmetryAxis := (axisRotation_mem_symmetryAxis_iff φ x).mpr hx
      simp [hG, hx, hx']
    · have hx' : axisRotation φ x ∉ symmetryAxis :=
        fun h ↦ hx ((axisRotation_mem_symmetryAxis_iff φ x).mp h)
      simp only [hG]
      rw [indicator_of_mem (show axisRotation φ x ∈ symmetryAxisᶜ from hx'),
        indicator_of_mem (show x ∈ symmetryAxisᶜ from hx), hu,
        rotatedPartialSum_axisRotation a N hx, ← axialRotation_apply, ← axialRotation_apply,
        ← map_sub, LinearIsometryEquiv.norm_map]
  have hae (N : ℕ) : (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
      ‖u ω - rotatedPartialSum a N ω‖ ^ 2) =ᵐ[(volume : Measure (ℝ^3)).toSphere]
        fun ω ↦ G N ω := by
    have h0 := measure_eq_zero_iff_ae_notMem.mp toSphere_symmetryAxis
    filter_upwards [h0] with ω hω
    simp only [hG, indicator_of_mem (show (ω : ℝ^3) ∈ symmetryAxisᶜ from hω)]
  have hcoe (N : ℕ) : (V - P N : Lp (ℝ^3) 2 polarAngleMeasure) =ᵐ[polarAngleMeasure]
      fun θ ↦ u (point 1 θ 0) - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
        a l k • vectorHarmonic l k θ := by
    have hPN : (P N : ℝ → ℝ^3) =ᵐ[polarAngleMeasure] ∑ l ∈ Finset.range N,
        ∑ k : Fin 3, fun θ ↦ a l k • vectorHarmonic l k θ := by
      refine (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun l _ ↦
        (Lp.coeFn_finsetSum _ _).trans (eventuallyEq_sum fun k _ ↦ ?_))
      filter_upwards [Lp.coeFn_smul (a l k) (vectorHarmonicLp l k),
        coeFn_vectorHarmonicLp l k] with θ h1 h2
      rw [h1, Pi.smul_apply, h2]
    filter_upwards [Lp.coeFn_sub V (P N), hv.coeFn_toLp, hPN] with θ h1 h2 h3
    rw [h1, Pi.sub_apply, hV, h2, h3]
    simp only [Finset.sum_apply]
  have hint (N : ℕ) : ∫ ω, ‖u ω - ∑ l ∈ Finset.range N, ∑ k : Fin 3,
      a l k • axisRotation (azimuthalAngle ω) (vectorHarmonic l k (polarAngle ω))‖ ^ 2
        ∂(volume : Measure (ℝ^3)).toSphere = 2 * Real.pi * ‖V - P N‖ ^ 2 := by
    change ∫ ω, ‖u ω - rotatedPartialSum a N ω‖ ^ 2 ∂(volume : Measure (ℝ^3)).toSphere = _
    rw [integral_congr_ae (hae N), integral_sphere_of_axisymmetric (hGinv N),
      ← integral_polarAngleMeasure_eq, ← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_Ioo_polarAngleMeasure, hcoe N] with θ hθ h
    simp only [hG]
    rw [h, real_inner_self_eq_norm_sq, indicator_of_mem (show radialFrame θ 0 ∈ symmetryAxisᶜ from
        radialFrame_notMem_symmetryAxis hθ 0)]
    simp only [rotatedPartialSum, axisRotation_vectorHarmonic_radialFrame_zero hθ, point,
      one_smul]
  simp only [hint]
  have hsum := (hasSum_vectorHarmonicCoeff_smul V).tendsto_sum_nat
  have hnorm : Tendsto (fun N ↦ ‖V - P N‖) atTop (𝓝 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.mp hsum
    simpa only [norm_sub_rev] using this
  simpa using (hnorm.pow 2).const_mul (2 * Real.pi)

section MeridianProfiles

open Real

/-- The meridian lintegral of `ofReal (r² sin θ) ofReal (g θ)` for a nonnegative integrable `g`
is `ofReal r² · ofReal (∫ g dσ)` with `σ = sin θ dθ`. -/
theorem lintegral_meridian_ofReal {r : ℝ} {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : Integrable g polarAngleMeasure) (hg0 : ∀ θ, 0 ≤ g θ) :
    ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * ENNReal.ofReal (g θ) =
      ENNReal.ofReal (r ^ 2) * ENNReal.ofReal (∫ θ, g θ ∂polarAngleMeasure) := by
  have hsin : Measurable fun θ : ℝ ↦ ENNReal.ofReal (sin θ) :=
    continuous_sin.measurable.ennreal_ofReal
  have hgm' : Measurable fun θ ↦ ENNReal.ofReal (g θ) := hgm.ennreal_ofReal
  have h1 : ∀ θ ∈ Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * ENNReal.ofReal (g θ) =
      ENNReal.ofReal (r ^ 2) * (ENNReal.ofReal (sin θ) * ENNReal.ofReal (g θ)) := by
    intro θ _
    rw [ENNReal.ofReal_mul (sq_nonneg r), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioo h1,
    lintegral_const_mul (f := fun θ ↦ ENNReal.ofReal (sin θ) * ENNReal.ofReal (g θ)) _
      (hsin.mul hgm'),
    ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg0), polarAngleMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hsin hgm']
  rfl

/-- At almost every radius of the ball, the meridian profile of a square-integrable measurable
equivariant field is square integrable for `sin θ dθ`. -/
theorem ae_memLp_meridian {R : ℝ} {W : ℝ^3 → ℝ^3} (hWm : Measurable W)
    (hW : IsEquivariantUnderAxisRotation W)
    (hW2 : MemLp W 2 (volume.restrict (Metric.ball (0 : ℝ^3) R))) :
    ∀ᵐ r ∂(volume.restrict (Ioo 0 R)), MemLp (fun θ ↦ W (point r θ 0)) 2 polarAngleMeasure := by
  set B := Metric.ball (0 : ℝ^3) R
  have hsq : Integrable (fun x ↦ ‖W x‖ ^ 2) (volume.restrict B) :=
    (memLp_two_iff_integrable_sq_norm hW2.aestronglyMeasurable).mp hW2
  set f : ℝ^3 → ENNReal := B.indicator fun x ↦ ENNReal.ofReal (‖W x‖ ^ 2) with hf
  have hfm : Measurable f := ((hWm.norm.pow_const 2).ennreal_ofReal).indicator
    Metric.isOpen_ball.measurableSet
  have hfinv : IsInvariantUnderAxisRotation f :=
    (isInvariantUnderAxisRotation_comp_norm hW fun t ↦ ENNReal.ofReal (t ^ 2)).indicator_ball R
  have hfin : ∫⁻ x, f x < ⊤ := by
    rw [hf, MeasureTheory.lintegral_indicator Metric.isOpen_ball.measurableSet]
    exact hsq.lintegral_lt_top
  rw [lintegral_volume_of_axisymmetric hfinv hfm] at hfin
  have hH : Measurable fun r ↦ ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) * f (point r θ 0) :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦
      ENNReal.ofReal (p.1 ^ 2 * sin p.2) * f (point p.1 p.2 0))
      ((((continuous_fst.pow 2).mul
        (continuous_sin.comp continuous_snd)).measurable.ennreal_ofReal).mul
        (hfm.comp continuous_point_meridian.measurable))
  have hfin' : ∫⁻ r in Ioi 0, ∫⁻ θ in Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) *
      f (point r θ 0) ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by simp [pi_pos])] at hfin
    exact lt_irrefl _ hfin
  have hae := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self : Ioo (0 : ℝ) R ⊆ Ioi 0)
    (ae_lt_top hH hfin')
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with r hr hrI
  have hmeas : AEStronglyMeasurable (fun θ ↦ W (point r θ 0)) polarAngleMeasure :=
    (hWm.comp (continuous_point_meridian_angle r).measurable).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).mpr ⟨hmeas.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun θ ↦ sq_nonneg _)]
  have hpt (θ : ℝ) : f (point r θ 0) = ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2) := by
    rw [hf, Set.indicator_of_mem]
    simp only [B, Metric.mem_ball, dist_zero_right, norm_point hrI.1]
    exact hrI.2
  simp only [hpt] at hr
  have hsin : Measurable fun θ : ℝ ↦ ENNReal.ofReal (sin θ) :=
    continuous_sin.measurable.ennreal_ofReal
  have hgm : Measurable fun θ ↦ ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2) :=
    ((hWm.comp (continuous_point_meridian_angle r).measurable).norm.pow_const 2).ennreal_ofReal
  have h1 : ∀ θ ∈ Ioo 0 π, ENNReal.ofReal (r ^ 2 * sin θ) *
      ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2) = ENNReal.ofReal (r ^ 2) *
        (ENNReal.ofReal (sin θ) * ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2)) := by
    intro θ _
    rw [ENNReal.ofReal_mul (sq_nonneg r), mul_assoc]
  rw [setLIntegral_congr_fun measurableSet_Ioo h1, lintegral_const_mul (f := fun θ ↦
    ENNReal.ofReal (sin θ) * ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2)) _ (hsin.mul hgm)] at hr
  rw [polarAngleMeasure, lintegral_withDensity_eq_lintegral_mul _ hsin hgm]
  have hr0 : ENNReal.ofReal (r ^ 2) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    exact pow_pos hrI.1 2
  rcases ENNReal.mul_lt_top_iff.mp hr with ⟨_, h⟩ | h | h
  · exact h
  · exact absurd h hr0
  · rw [show (fun θ ↦ ENNReal.ofReal (sin θ)) * (fun θ ↦ ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2)) =
      fun θ ↦ ENNReal.ofReal (sin θ) * ENNReal.ofReal (‖W (point r θ 0)‖ ^ 2) from rfl, h]
    exact ENNReal.zero_lt_top

end MeridianProfiles

end PDE.Analysis.SpecialFunctions
