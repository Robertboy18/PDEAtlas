/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import PDE.Common.Euclidean
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Polar integration

Mathlib's `homeomorphUnitSphereProd` identifies `E \ {0}` with `S × (0,∞)`, where
`S` is the unit sphere, and `Measure.measurePreserving_homeomorphUnitSphereProd`
transports an additive Haar measure `μ` on `E` to the product of the angular
measure `μ.toSphere` with the radial measure `volumeIoiPow (n - 1)`, that is
`r^(n-1) dr` on `(0,∞)` with `n = dim E`. We turn that measure-level
statement into formulas for Bochner integrals of an integrable `g : E → F`:

  `∫ x, g x ∂μ = ∫_0^∞ r^(n-1) (∫_S g (r ω) dσ) dr = ∫_S (∫_0^∞ r^(n-1) g (r ω) dr) dσ`.

The radial measure already contains the `r^(n-1)` Jacobian, so no separate
change-of-variables computation is needed.

The coordinate splitting `ℝ^(m+n) ≃ ℝ^m × ℝ^n` is also measure preserving;
it is used before applying Fubini in cylindrical and
axisymmetric integration.

## Main results

* `integral_polar_addHaar`: the integral over `E` as an integral over
  `S × (0,∞)` against `μ.toSphere ⊗ volumeIoiPow (n-1)`.
* `integrable_polar_addHaar`: integrability transfers to the polar product.
* `integral_polar_addHaar_iterated`: the radius-first iterated formula.
* `integral_polar_addHaar_iterated_sphereFirst`: the sphere-first formula.
* `integrableOn_polar_angular`: for real `g`, the radial profile
  `r ↦ r^(n-1) ∫_S g (r ω) dσ` is integrable on `(0,∞)`.
* `euclideanSumMeasurableEquiv_measurePreserving`, `integral_euclideanSum`:
  the orthogonal split `ℝ^(m+n) ≃ ℝ^m × ℝ^n` preserves volume.
* `integral_upperHalfPlane_polar`, `lintegral_upperHalfPlane_polar`: planar polar coordinates
  on the upper half-plane `{(a, b) : b > 0}` of `ℝ × ℝ`, with the angle ranging over `(0, π)`
  and Jacobian `r`.

For Lebesgue measure, `integral_polar_addHaar_iterated` is Evans's polar coordinates formula
(App. C.3, Theorem 4(i)) with center `0`, for any integrable function rather than a continuous
summable one; the sphere `∂B(0, r)` carries `r^(n-1)` times the angular measure.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.3, Theorem 4(i), p. 712.
  <https://doi.org/10.1090/gsm/019>
* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley,
  1999.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE
namespace Analysis

/-- The orthogonal coordinate splitting `ℝ^(m+n) ≃ ℝ^m × ℝ^n`, with the `L²`
product norm on the target. -/
def euclideanSumLinearIsometry (m n : ℕ) :
    ℝ^(m + n) ≃ₗᵢ[ℝ]
      WithLp 2 (ℝ^m × ℝ^n) :=
  ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : Fin m ⊕ Fin n ↦ ℝ)))

/-- Orthogonal coordinate splitting of Euclidean space, with the `Fin m`
coordinates first and the `Fin n` coordinates second. -/
def euclideanSumMeasurableEquiv (m n : ℕ) :
    ℝ^(m + n) ≃ᵐ
      (ℝ^m × ℝ^n) :=
  (euclideanSumLinearIsometry m n).toMeasurableEquiv.trans
    (MeasurableEquiv.toLp 2 (ℝ^m × ℝ^n)).symm

/-- The orthogonal Euclidean coordinate split preserves canonical volume,
including its normalization. -/
theorem euclideanSumMeasurableEquiv_measurePreserving (m n : ℕ) :
    MeasurePreserving (euclideanSumMeasurableEquiv m n) volume volume := by
  apply MeasurePreserving.trans
  · exact LinearIsometryEquiv.measurePreserving _
  · exact WithLp.volume_preserving_symm_measurableEquiv_toLp_prod
      (ℝ^m) (ℝ^n)

/-- Fubini-ready integral form of the orthogonal Euclidean coordinate split. -/
theorem integral_euclideanSum (m n : ℕ)
    (g : ℝ^(m + n) → ℝ) :
    (∫ x : ℝ^(m + n), g x) =
      ∫ p : ℝ^m × ℝ^n,
        g ((euclideanSumMeasurableEquiv m n).symm p) := by
  exact ((euclideanSumMeasurableEquiv_measurePreserving m n).symm
    (euclideanSumMeasurableEquiv m n) |>.integral_comp
      (euclideanSumMeasurableEquiv m n).symm.measurableEmbedding g).symm

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Polar decomposition of a whole-space Bochner integral. The radial measure
includes the Jacobian factor determined by the real dimension of `E`.

This is the function-level form of
`Measure.measurePreserving_homeomorphUnitSphereProd`.
-/
theorem integral_polar_addHaar
    (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → F) :
    (∫ x : E, g x ∂μ) =
      ∫ z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
        g (z.2.1 • (z.1.1 : E))
        ∂(μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  calc
    (∫ x : E, g x ∂μ) =
        ∫ x : (({(0 : E)}ᶜ) : Set E), g x.1 ∂(μ.comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl
        (fun x ↦ g x), restrict_compl_singleton]
    _ = ∫ z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ),
        g (z.2.1 • (z.1.1 : E))
        ∂(μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      let h : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → F :=
        fun z ↦ g (z.2.1 • (z.1.1 : E))
      have hp := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E)) h
      have heq :
          (fun x : (({(0 : E)}ᶜ) : Set E) ↦
            h ((homeomorphUnitSphereProd E) x)) =
          fun x : (({(0 : E)}ᶜ) : Set E) ↦ g x.1 := by
        funext x
        simp [h, homeomorphUnitSphereProd_apply_fst_coe,
          homeomorphUnitSphereProd_apply_snd_coe,
          smul_inv_smul₀ (norm_ne_zero_iff.2 x.2)]
      change (∫ x : (({(0 : E)}ᶜ) : Set E),
          h ((homeomorphUnitSphereProd E) x) ∂(μ.comap (↑))) =
        ∫ z, h z ∂(μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) at hp
      rw [heq] at hp
      simpa [h] using hp

omit [Nontrivial E] [NormedSpace ℝ F] in
/-- Pulling an integrable function back to polar coordinates preserves
integrability for the angular-times-radial product measure. -/
theorem integrable_polar_addHaar
    (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → F)
    (hg : Integrable g μ) :
    Integrable
      (fun z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦
        g (z.2.1 • (z.1.1 : E)))
      (μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  let H : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → F :=
    fun z ↦ g (z.2.1 • (z.1.1 : E))
  have hgComap : Integrable
      (g ∘ (Subtype.val : (({(0 : E)}ᶜ) : Set E) → E))
      (μ.comap Subtype.val) := by
    have hgOn : IntegrableOn g (({(0 : E)}ᶜ) : Set E) μ := hg.integrableOn
    exact (integrableOn_iff_comap_subtypeVal
      (μ := μ) (s := (({(0 : E)}ᶜ) : Set E))
      (f := g) ((measurableSet_singleton (0 : E)).compl)).1 hgOn
  have hcomp : H ∘ homeomorphUnitSphereProd E =
      g ∘ (Subtype.val : (({(0 : E)}ᶜ) : Set E) → E) := by
    funext x
    simp [H, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe,
      smul_inv_smul₀ (norm_ne_zero_iff.2 x.2)]
  have hp := μ.measurePreserving_homeomorphUnitSphereProd
  have he := Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E)
  apply (MeasurePreserving.integrable_comp_emb hp he (g := H)).1
  simpa [hcomp] using hgComap

/-- Polar integration with the angular integral outermost.  This is the
Fubini-swapped companion to `integral_polar_addHaar_iterated`. -/
theorem integral_polar_addHaar_iterated_sphereFirst
    (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → F)
    (hg : Integrable g μ) :
    (∫ x : E, g x ∂μ) =
      ∫ ω : Metric.sphere (0 : E) 1,
        (∫ r in Set.Ioi (0 : ℝ),
          r ^ (Module.finrank ℝ E - 1) • g (r • (ω : E)))
        ∂μ.toSphere := by
  let H : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → F :=
    fun z ↦ g (z.2.1 • (z.1.1 : E))
  have hH : Integrable H
      (μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    simpa [H] using integrable_polar_addHaar μ g hg
  calc
    (∫ x : E, g x ∂μ) =
        ∫ z : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ), H z
          ∂(μ.toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa [H] using integral_polar_addHaar μ g
    _ = ∫ ω : Metric.sphere (0 : E) 1,
        (∫ r : Set.Ioi (0 : ℝ), H (ω, r)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)))
        ∂μ.toSphere := by
      exact integral_prod H hH
    _ = ∫ ω : Metric.sphere (0 : E) 1,
        (∫ r in Set.Ioi (0 : ℝ),
          r ^ (Module.finrank ℝ E - 1) • g (r • (ω : E)))
        ∂μ.toSphere := by
      apply integral_congr_ae
      filter_upwards with ω
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul
        ((measurable_subtype_coe.pow_const
          (Module.finrank ℝ E - 1)).real_toNNReal)
        (fun r : Set.Ioi (0 : ℝ) ↦ H (ω, r))]
      have hSub :
          (∫ r : Set.Ioi (0 : ℝ),
              (Real.toNNReal ((r : ℝ) ^ (Module.finrank ℝ E - 1))) • H (ω, r)
              ∂Measure.comap Subtype.val volume) =
            ∫ r in Set.Ioi (0 : ℝ),
              (Real.toNNReal (r ^ (Module.finrank ℝ E - 1))) •
                g (r • (ω : E)) := by
        simpa [H] using integral_subtype_comap
          (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
          measurableSet_Ioi
          (fun r : ℝ ↦
            (Real.toNNReal (r ^ (Module.finrank ℝ E - 1))) •
              g (r • (ω : E)))
      rw [hSub]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 ≤ r ^ (Module.finrank ℝ E - 1) :=
        pow_nonneg (le_of_lt hr) _
      simp [NNReal.smul_def, Real.coe_toNNReal _ hr0]

/-- Polar integration with the angular and radial integrals exposed. The
radial density is the radius raised to one less than the real dimension of
`E`. -/
theorem integral_polar_addHaar_iterated
    (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → F)
    (hg : Integrable g μ) :
    (∫ x : E, g x ∂μ) =
      ∫ r in Set.Ioi (0 : ℝ),
        r ^ (Module.finrank ℝ E - 1) •
          ∫ ω : Metric.sphere (0 : E) 1, g (r • (ω : E)) ∂μ.toSphere := by
  let H : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → F :=
    fun z ↦ g (z.2.1 • (z.1.1 : E))
  have hgComap : Integrable
      (g ∘ (Subtype.val : (({(0 : E)}ᶜ) : Set E) → E))
      (μ.comap Subtype.val) := by
    have hgOn : IntegrableOn g (({(0 : E)}ᶜ) : Set E) μ := hg.integrableOn
    exact (integrableOn_iff_comap_subtypeVal
      (μ := μ) (s := (({(0 : E)}ᶜ) : Set E))
      (f := g) ((measurableSet_singleton (0 : E)).compl)).1 hgOn
  have hcomp : H ∘ homeomorphUnitSphereProd E =
      g ∘ (Subtype.val : (({(0 : E)}ᶜ) : Set E) → E) := by
    funext x
    simp [H, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe,
      smul_inv_smul₀ (norm_ne_zero_iff.2 x.2)]
  have hH : Integrable H
      (μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    have hp := μ.measurePreserving_homeomorphUnitSphereProd
    have he := Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E)
    apply (MeasurePreserving.integrable_comp_emb hp he (g := H)).1
    simpa [hcomp] using hgComap
  calc
    (∫ x : E, g x ∂μ) =
        ∫ z, H z ∂(μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa [H] using integral_polar_addHaar μ g
    _ = ∫ r : Set.Ioi (0 : ℝ),
        ∫ ω : Metric.sphere (0 : E) 1, H (ω, r) ∂μ.toSphere
        ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa using integral_prod_symm H hH
    _ = ∫ r in Set.Ioi (0 : ℝ),
        r ^ (Module.finrank ℝ E - 1) •
          ∫ ω : Metric.sphere (0 : E) 1, g (r • (ω : E)) ∂μ.toSphere := by
      let inner : ℝ → F := fun r ↦
        ∫ ω : Metric.sphere (0 : E) 1, g (r • (ω : E)) ∂μ.toSphere
      simp only [Measure.volumeIoiPow, ENNReal.ofReal]
      rw [integral_withDensity_eq_integral_smul
        ((measurable_subtype_coe.pow_const
          (Module.finrank ℝ E - 1)).real_toNNReal)
        (fun r : Set.Ioi (0 : ℝ) ↦ inner r.1)]
      have hSub :
          (∫ r : Set.Ioi (0 : ℝ),
              (Real.toNNReal ((r : ℝ) ^ (Module.finrank ℝ E - 1))) • inner r.1
              ∂Measure.comap Subtype.val volume) =
            ∫ r in Set.Ioi (0 : ℝ),
              (Real.toNNReal (r ^ (Module.finrank ℝ E - 1))) • inner r := by
        simpa using integral_subtype_comap
          (μ := (volume : Measure ℝ)) (s := Set.Ioi (0 : ℝ))
          measurableSet_Ioi
          (fun r : ℝ ↦
            (Real.toNNReal (r ^ (Module.finrank ℝ E - 1))) • inner r)
      rw [hSub]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hr0 : 0 ≤ r ^ (Module.finrank ℝ E - 1) :=
        pow_nonneg (le_of_lt hr) _
      simp [inner, NNReal.smul_def, Real.coe_toNNReal _ hr0]

omit [Nontrivial E] in
/-- The radial-angular average appearing in polar coordinates is integrable
with its Jacobian whenever the original real-valued function is integrable. -/
theorem integrableOn_polar_angular
    (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → ℝ)
    (hg : Integrable g μ) :
    IntegrableOn (fun r : ℝ ↦
      r ^ (Module.finrank ℝ E - 1) *
        ∫ ω : Metric.sphere (0 : E) 1, g (r • (ω : E)) ∂μ.toSphere)
      (Set.Ioi 0) volume := by
  let H : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) → ℝ :=
    fun z ↦ g (z.2.1 • (z.1.1 : E))
  let inner : ℝ → ℝ := fun r ↦
    ∫ ω : Metric.sphere (0 : E) 1, g (r • (ω : E)) ∂μ.toSphere
  have hgComap : Integrable
      (g ∘ (Subtype.val : (({(0 : E)}ᶜ) : Set E) → E))
      (μ.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal
      (μ := μ) (s := (({(0 : E)}ᶜ) : Set E))
      (f := g) ((measurableSet_singleton (0 : E)).compl)).1 hg.integrableOn
  have hcomp : H ∘ homeomorphUnitSphereProd E =
      g ∘ (Subtype.val : (({(0 : E)}ᶜ) : Set E) → E) := by
    funext x
    simp [H, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe,
      smul_inv_smul₀ (norm_ne_zero_iff.2 x.2)]
  have hH : Integrable H
      (μ.toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    have hp := μ.measurePreserving_homeomorphUnitSphereProd
    have he := Homeomorph.measurableEmbedding (homeomorphUnitSphereProd E)
    apply (MeasurePreserving.integrable_comp_emb hp he (g := H)).1
    simpa [hcomp] using hgComap
  have hinner : Integrable (fun r : Set.Ioi (0 : ℝ) ↦ inner r.1)
      (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
    simpa [H, inner] using hH.integral_prod_right
  rw [Measure.volumeIoiPow] at hinner
  have hdensity : Measurable
      (fun r : Set.Ioi (0 : ℝ) ↦
        ENNReal.ofReal (r.1 ^ (Module.finrank ℝ E - 1))) := by
    fun_prop
  have hfinite : ∀ᵐ r : Set.Ioi (0 : ℝ)
      ∂Measure.comap Subtype.val volume,
      ENNReal.ofReal (r.1 ^ (Module.finrank ℝ E - 1)) < ⊤ := by
    filter_upwards [] with r
    exact ENNReal.ofReal_lt_top
  have hweighted :=
    (integrable_withDensity_iff hdensity hfinite).1 hinner
  apply (integrableOn_iff_comap_subtypeVal
    (μ := volume) (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi).2
  apply hweighted.congr
  filter_upwards [] with r
  have hr0 : 0 ≤ r.1 ^ (Module.finrank ℝ E - 1) :=
    pow_nonneg r.2.le _
  simp [inner, ENNReal.toReal_ofReal hr0, mul_comm]

/-- Polar change of variables on the upper half-plane, with angular range
`(0,π)` and Jacobian `r`. -/
theorem integral_upperHalfPlane_polar (f : ℝ × ℝ → ℝ) :
    (∫ p in {p : ℝ × ℝ | 0 < p.2}, f p) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
        p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
  let U : Set (ℝ × ℝ) := {p | 0 < p.2}
  let D : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi
  let g : ℝ × ℝ → ℝ := U.indicator f
  have hU : MeasurableSet U := measurableSet_lt measurable_const measurable_snd
  have hD : MeasurableSet D := measurableSet_Ioi.prod measurableSet_Ioo
  have hpolar := integral_comp_polarCoord_symm g
  calc
    (∫ p in {p : ℝ × ℝ | 0 < p.2}, f p) = ∫ p, g p := by
      rw [integral_indicator hU]
    _ = ∫ p in polarCoord.target,
        p.1 * g (polarCoord.symm p) := by
      simpa [smul_eq_mul] using hpolar.symm
    _ = ∫ p in D,
        p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
      rw [← integral_indicator polarCoord.open_target.measurableSet,
        ← integral_indicator hD]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hpA : p ∈ polarCoord.target
      · have hr : 0 < p.1 := hpA.1
        have hθlo : -Real.pi < p.2 := hpA.2.1
        have hθhi : p.2 < Real.pi := hpA.2.2
        by_cases hθ : 0 < p.2
        · have hpD : p ∈ D := ⟨hr, hθ, hθhi⟩
          have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi hθ hθhi
          rw [Set.indicator_of_mem hpA, Set.indicator_of_mem hpD]
          rw [polarCoord_symm_apply]
          congr 1
          exact Set.indicator_of_mem (s := U) (mul_pos hr hsin) f
        · have hpD : p ∉ D := by simp [D, hθ]
          have hsin : Real.sin p.2 ≤ 0 := by
            have hpnonpos : p.2 ≤ 0 := le_of_not_gt hθ
            have hnegpi : -Real.pi ≤ p.2 := hθlo.le
            exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hpnonpos hnegpi
          simp [hpD, g, U, D,
            polarCoord_symm_apply, not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos
              hr.le hsin)]
      · have hpD : p ∉ D := fun hp ↦ hpA ⟨hp.1, by
          exact ⟨(neg_lt_zero.mpr Real.pi_pos).trans hp.2.1, hp.2.2⟩⟩
        rw [Set.indicator_of_notMem hpA, Set.indicator_of_notMem hpD]

/-- Polar change of variables on the upper half-plane for nonnegative functions, with angular
range `(0,π)` and Jacobian `r`. No measurability hypothesis is needed. -/
theorem lintegral_upperHalfPlane_polar (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, f p) =
      ∫⁻ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi,
        ENNReal.ofReal p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
  let U : Set (ℝ × ℝ) := {p | 0 < p.2}
  let D : Set (ℝ × ℝ) := Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (0 : ℝ) Real.pi
  have hU : MeasurableSet U := measurableSet_lt measurable_const measurable_snd
  have hD : MeasurableSet D := measurableSet_Ioi.prod measurableSet_Ioo
  calc (∫⁻ p in {p : ℝ × ℝ | 0 < p.2}, f p) = ∫⁻ p, U.indicator f p :=
        (lintegral_indicator hU f).symm
    _ = ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • U.indicator f (polarCoord.symm p) :=
        (lintegral_comp_polarCoord_symm _).symm
    _ = ∫⁻ p in polarCoord.target, D.indicator
          (fun p ↦ ENNReal.ofReal p.1 * f (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) p := by
        refine setLIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp ↦ ?_
        obtain ⟨hr, hθ⟩ := hp
        simp only [Set.mem_Ioi, Set.mem_Ioo] at hr hθ
        simp only [polarCoord_symm_apply, smul_eq_mul]
        by_cases h : 0 < p.2
        · have hsin : 0 < p.1 * Real.sin p.2 :=
            mul_pos hr (Real.sin_pos_of_pos_of_lt_pi h hθ.2)
          have hp : p ∈ D := ⟨hr, h, hθ.2⟩
          rw [Set.indicator_of_mem (s := U) hsin, Set.indicator_of_mem hp]
        · have hsin : ¬ 0 < p.1 * Real.sin p.2 := not_lt.2 (mul_nonpos_of_nonneg_of_nonpos
            hr.le (Real.sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.1 h) hθ.1.le))
          have hp : p ∉ D := fun hp ↦ h hp.2.1
          rw [Set.indicator_of_notMem (s := U) hsin, Set.indicator_of_notMem hp, mul_zero]
    _ = _ := by
        rw [setLIntegral_indicator hD, Set.inter_eq_left.2]
        rintro p ⟨hr, hθ⟩
        exact ⟨hr, (neg_lt_zero.2 Real.pi_pos).trans hθ.1, hθ.2⟩

end Analysis
end PDE
