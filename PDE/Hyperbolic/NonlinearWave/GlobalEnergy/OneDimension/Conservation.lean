/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.OneDimension.LocalBounds
import PDE.Analysis.Integration.EndpointFlux
import PDE.Analysis.Integration.Rectangle.Balance
import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# One-dimensional energy conservation with a continuous reaction

A normalized C1 potential and a C3 wave with separately compact
spatial displacement slices conserve physical energy at every forward time.
Characteristic transport gives local uniform bounds on the first derivatives;
compact displacement makes the spatial flux vanish separately at every time.
Dominated convergence removes the ends of finite rectangular balances, and
local constancy on the connected forward time ray gives conservation.

The closed-forward theorem uses the right differential at time zero.
This is the one-dimensional case of Evans, §12.1.1, Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE PDE.Common
open scoped ContDiff

namespace WaveEquation

/-- The planar balance is the physical wave-energy balance in one
spatial dimension, with the Euclidean spatial volume preserved. -/
private theorem semilinearWaveSpatialEnergy_eq_of_line_endpoint_flux_zero {V : ℝ → ℝ} {u : ℝ^2 → ℝ}
    {a b : ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (hab : a ≤ b)
    (hwave : ∀ t ∈ Icc a b, ∀ x : ℝ^1, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (ha : Integrable (semilinearWaveSpatialEnergyDensity V u a))
    (hb : Integrable (semilinearWaveSpatialEnergyDensity V u b))
    (hflux : Tendsto (fun R : ℝ ↦ ∫ t in Icc a b, classicalWaveEnergyFlux u 0
      (timeSpaceCons t ((OrthonormalBasis.singleton (Fin 1) ℝ).repr R)) -
      classicalWaveEnergyFlux u 0 (timeSpaceCons t ((OrthonormalBasis.singleton (Fin 1) ℝ).repr
      (-R)))) atTop (nhds 0)) :
    semilinearWaveSpatialEnergy V u b = semilinearWaveSpatialEnergy V u a := by
  let L := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  let A : (ℝ × ℝ) ≃L[ℝ] ℝ^2 :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr L.toContinuousLinearEquiv).trans
      (timeSpaceContinuousLinearEquiv 1).symm
  have hA (p : ℝ × ℝ) : A p = timeSpaceCons p.1 (L p.2) := rfl
  have hA0 : A (1, 0) = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i
    · simp [hA, L]
    · change (timeSpaceCons 1 (L 0)) (Fin.succ (0 : Fin 1)) = 0
      rw [timeSpaceCons_succ]
      simp [L]
  have hA1 : A (0, 1) = EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i
    · simp [hA, L]
    · change (timeSpaceCons 0 (L 1)) (Fin.succ (0 : Fin 1)) = 1
      rw [timeSpaceCons_succ]
      simp [L]
  let e := semilinearWaveEnergyDensity V u ∘ A
  let j := classicalWaveEnergyFlux u 0 ∘ A
  have he : ContDiff ℝ 1 e := (contDiff_semilinearWaveEnergyDensity hV hu).comp A.contDiff
  have hj : ContDiff ℝ 1 j := (contDiff_classicalWaveEnergyFlux hu 0).comp A.contDiff
  have hde (p : ℝ × ℝ) : fderiv ℝ e p (1, 0) =
      (∂[0] (semilinearWaveEnergyDensity V u)) (A p) := by
    have h := ((contDiff_semilinearWaveEnergyDensity hV hu).differentiable
      one_ne_zero (A p)).hasFDerivAt.comp p A.hasFDerivAt
    rw [h.fderiv]
    change fderiv ℝ (semilinearWaveEnergyDensity V u) (A p) (A (1, 0)) = _
    rw [hA0]
    rfl
  have hdj (p : ℝ × ℝ) : fderiv ℝ j p (0, 1) =
      (∂[1] (classicalWaveEnergyFlux u 0)) (A p) := by
    have h := ((contDiff_classicalWaveEnergyFlux hu 0).differentiable
      one_ne_zero (A p)).hasFDerivAt.comp p A.hasFDerivAt
    rw [h.fderiv]
    change fderiv ℝ (classicalWaveEnergyFlux u 0) (A p) (A (0, 1)) = _
    rw [hA1]
    rfl
  have heq := PDE.Analysis.integral_energy_eq_of_tendsto_endpoint_flux_zero
    he hj hab (fun p hp ↦ ?_) ?_ ?_ hflux
  · have hint (t : ℝ) : (∫ x, e (t, x)) = semilinearWaveSpatialEnergy V u t :=
      L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding
        (semilinearWaveSpatialEnergyDensity V u t)
    rwa [hint b, hint a] at heq
  · rw [hde, hdj]
    have h := semilinearWaveEnergyBalanceResidual_eq_zero hV hu.contDiffAt (hwave p.1 hp (L p.2))
    rw [semilinearWaveEnergyBalanceResidual_eq_partialDeriv_sub_sum hV hu.contDiffAt] at h
    simpa only [Fin.sum_univ_one, Fin.succ_zero_eq_one, sub_eq_zero, hA] using h
  · exact L.measurePreserving.integrable_comp_of_integrable ha
  · exact L.measurePreserving.integrable_comp_of_integrable hb

/-- On a finite time band a bounded first jet and separate compact
spatial displacement slices remove the endpoint flux. The source endpoint
derives this bound by characteristic transport. -/
private theorem semilinearWaveSpatialEnergy_eq_of_line_partialDeriv_bound {V : ℝ → ℝ} {u : ℝ^2 → ℝ}
    {a b C : ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (hab : a ≤ b) (hC : 0 ≤ C)
    (hwave : ∀ t ∈ Icc a b, ∀ x : ℝ^1, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (ha : Integrable (semilinearWaveSpatialEnergyDensity V u a))
    (hb : Integrable (semilinearWaveSpatialEnergyDensity V u b))
    (hs : ∀ t ∈ Icc a b, HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x)))
    (hbound : ∀ p : ℝ^2, p 0 ∈ Icc a b → ∀ i : Fin 2, ‖(∂[i] u) p‖ ≤ C) :
    semilinearWaveSpatialEnergy V u b = semilinearWaveSpatialEnergy V u a := by
  let L := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  apply semilinearWaveSpatialEnergy_eq_of_line_endpoint_flux_zero hV hu hab hwave ha hb
  apply PDE.Analysis.tendsto_integral_endpoint_flux_zero (C := C * C)
  · exact fun x ↦ ((contDiff_classicalWaveEnergyFlux hu 0).continuous.comp
      ((contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
  · exact fun t ht ↦ (hasCompactSupport_semilinearWaveSpatialEnergyFlux
      (fun x ↦ hu.differentiable (by norm_num) (timeSpaceCons t x))
      (hs t ht) 0).comp_homeomorph L.toHomeomorph
  · intro t ht x
    change ‖classicalWaveEnergyFlux u 0 (timeSpaceCons t (L x))‖ ≤ C * C
    rw [classicalWaveEnergyFlux, norm_mul]
    exact mul_le_mul (hbound _ (by simpa using ht) 0)
      (hbound _ (by simpa using ht) 1) (norm_nonneg _) hC

/-- In one space dimension, separate compact displacement slices suffice for
energy conservation with a C1 potential. Characteristic transport derives local current bounds. -/
theorem semilinearWaveSpatialEnergy_eq_of_compact_slices_one {V : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^1, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x))) {t : ℝ}
    (ht : 0 ≤ t) :
    semilinearWaveSpatialEnergy V u t = semilinearWaveSpatialEnergy V u 0 := by
  let : Fact (0 < (1 : ℕ)) := ⟨by decide⟩
  let : PreconnectedSpace (Ici (0 : ℝ)) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hi0 := integrable_forwardSemilinearWaveEnergyDensity_initial_of_compact_slices
    hV hVzero hu.contDiffOn hwave hs
  have he0 : forwardSemilinearWaveEnergyDensity V u 0 =
      semilinearWaveSpatialEnergyDensity V u 0 := funext fun x ↦
    forwardSemilinearWaveEnergyDensity_eq_of_extension V hu2 (fun _ _ ↦ rfl) le_rfl x
  rw [he0] at hi0
  have hi (r : ℝ) (hr : 0 ≤ r) : Integrable (semilinearWaveSpatialEnergyDensity V u r) := by
    rcases hr.eq_or_lt with rfl | hrpos
    · exact hi0
    exact integrable_semilinearWaveSpatialEnergyDensity_of_compact_slices
      hV hVzero hu hwave hs hrpos
  have hpde (r : ℝ) (hr : 0 ≤ r) (x : ℝ^1) :=
    semilinearWaveOperator_eq_zero_of_nonneg hV.continuous_deriv_one hu2 hwave hr x
  have hc : IsLocallyConstant (fun r : Ici (0 : ℝ) ↦ semilinearWaveSpatialEnergy V u r) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro a
    obtain ⟨δ, hδ, C, hC, hb⟩ := exists_uniform_partialDeriv_bound_near_of_compact_slices
      hu hV.continuous_deriv_one hwave hs a.property
    have hn : ∀ᶠ r : Ici (0 : ℝ) in nhds a, (r : ℝ) ∈ Ioo ((a : ℝ) - δ) ((a : ℝ) + δ) :=
      continuous_subtype_val.continuousAt.eventually
        (Ioo_mem_nhds (by linarith) (by linarith))
    filter_upwards [hn] with r hr
    rcases le_total (a : ℝ) r with har | hra
    · apply semilinearWaveSpatialEnergy_eq_of_line_partialDeriv_bound hV hu2 har hC
        (fun q hq x ↦ hpde q (a.property.trans hq.1) x) (hi a a.property)
        (hi r r.property) (fun q hq ↦ hs q (a.property.trans hq.1))
      intro p hp i
      apply hb p ⟨max_le (a.property.trans hp.1) (by linarith [hp.1]), hp.2.trans hr.2.le⟩ i
    · symm
      apply semilinearWaveSpatialEnergy_eq_of_line_partialDeriv_bound hV hu2 hra hC
        (fun q hq x ↦ hpde q (r.property.trans hq.1) x) (hi r r.property)
        (hi a a.property) (fun q hq ↦ hs q (r.property.trans hq.1))
      intro p hp i
      apply hb p ⟨max_le (r.property.trans hp.1) (hr.1.le.trans hp.1),
        by linarith [hp.2]⟩ i
  exact hc.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨0, le_rfl⟩

/-- Conservation for the forward differential of a C3 one-dimensional
wave. No smoothness or wave equation is prescribed at negative times. -/
theorem forwardSemilinearWaveEnergy_eq_of_compact_slices_one {V : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiffOn ℝ 3 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^1, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^1 ↦ u (timeSpaceCons t x))) {t : ℝ}
    (ht : 0 ≤ t) :
    forwardSemilinearWaveEnergy V u t = forwardSemilinearWaveEnergy V u 0 := by
  obtain ⟨U, hU, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace 0 3 hu
  have hU2 : ContDiff ℝ 2 U := hU.of_le (by norm_num)
  rw [forwardSemilinearWaveEnergy_eq_of_extension V hU2 heq ht,
    forwardSemilinearWaveEnergy_eq_of_extension V hU2 heq le_rfl]
  apply semilinearWaveSpatialEnergy_eq_of_compact_slices_one hV hVzero hU _ _ ht
  · intro s hs' x
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons s x) 0 by simpa only [timeSpaceCons_zero] using hs')
    unfold semilinearWaveOperator
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave s hs' x
  · intro s hs'
    have hslice : (fun x : ℝ^1 ↦ U (timeSpaceCons s x)) =
        (fun x : ℝ^1 ↦ u (timeSpaceCons s x)) := by
      funext x
      exact heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using hs')
    rw [hslice]
    exact hs s hs'

end WaveEquation
