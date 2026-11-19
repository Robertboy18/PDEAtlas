/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.Fan
public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.Phase
public import PDE.Hyperbolic.ConservationLaw.System.InitialValue
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.Trace
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.VectorTesting

/-!
# Continuous rarefaction fans with their initial datum

The weak fan is given by the clipped-profile formula. Its endpoint
identities make this formula continuous across both fronts. Finite propagation
gives the strong initial trace, and the time-cutoff theorem recovers the full
initial weak equation and arbitrary compact vector tests.

`exists_continuous_rarefaction_of_integralCurve` is Evans, §11.2.2, Theorem 1: for a
genuinely nonlinear family and `u_r ∈ R_k^+(u_l)`, here a segment of an integral curve along
which the characteristic speed increases, there is a continuous integral solution of Riemann's
problem (1)-(2) of §11.2 that is constant along lines through the origin. Evans composes the
curve `v` with the rarefaction wave of the scalar problem (7), (14), given by §3.4.4,
Theorem 4, and treats `w_l > w_r` in the same way. We parametrize the curve by the
characteristic speed instead; at `x/t` in the fan both give the state of the curve where
`λ_k = x/t`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2, equations (1)-(2); §11.2.1, equations (6)-(9) and the
  notation `R_k^±(z₀)`; §11.2.2, Theorem 1 and its proof, equations (13)-(14); §3.4.4,
  Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter MeasureTheory Set
open PDE.Common PDE.Hyperbolic.ConservationLaw.Scalar
open scoped ContDiff ENNReal Topology Distributions InnerProductSpace

/-- A conservative `C¹` profile on a closed speed interval yields a continuous
bounded initial weak solution, with a literal formula at both fronts and
strong initial trace. The profile hypotheses follow from an integral curve by the whole-segment
construction. -/
theorem exists_continuous_initialValue_rarefaction {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : ContDiff ℝ 1 flux) {profile : ℝ → ℝ^m} {a b K : ℝ} {left right : ℝ^m} (hab : a ≤ b)
    (hreg : ∀ ξ ∈ Icc a b, ContDiffAt ℝ 1 profile ξ)
    (hode : ∀ ξ ∈ Icc a b, fderiv ℝ flux (profile ξ) (deriv profile ξ) = ξ • deriv profile ξ)
    (hleft : profile a = left) (hright : profile b = right)
    (hbound : ∀ ξ ∈ Icc a b, ‖profile ξ‖ ≤ K) :
    ∃ u : ℝ^2 → ℝ^m,
      IsWeakInitialValueSolution flux (riemannData left right) u ∧
      HasInitialTraceLocallyL1 u (riemannData left right) ∧
      Measurable u ∧ ContinuousOn u forwardHalfSpace ∧
      MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
      (∀ p : ℝ^2, 0 < p 0 →
        u p = profile (max a (min b (similarityVariable p)))) ∧
      (∀ ψ : 𝓓^{1}((⊤ : TopologicalSpace.Opens ℝ^2), ℝ^m),
        IntegrableOn (fun p ↦
          ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪flux (u p), (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ)
          forwardHalfSpace volume ∧
        Integrable (fun x : ℝ ↦ ⟪riemannData left right x, ψ !₂[0, x]⟫_ℝ) volume ∧
        (∫ p in forwardHalfSpace,
          ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪flux (u p), (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ) +
          ∫ x : ℝ, ⟪riemannData left right x, ψ !₂[0, x]⟫_ℝ = 0) := by
  obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, hmiddle⟩ :=
    exists_bounded_weak_rarefaction hflux hab hreg hode hleft hright hbound
  have hformula (p : ℝ^2) (ht : 0 < p 0) :
      u p = profile (max a (min b (similarityVariable p))) := by
    by_cases ha : p 1 < a * p 0
    · have hξ : similarityVariable p < a := (div_lt_iff₀ ht).mpr ha
      rw [hlu p ha, min_eq_right (hξ.le.trans hab), max_eq_left hξ.le, hleft]
    · have ha' : a ≤ similarityVariable p := (le_div_iff₀ ht).mpr (not_lt.mp ha)
      by_cases hb : p 1 < b * p 0
      · have hb' : similarityVariable p < b := (div_lt_iff₀ ht).mpr hb
        rw [min_eq_right hb'.le, max_eq_right ha']
        exact hmiddle p ht (not_lt.mp ha) hb
      · have hb' : b ≤ similarityVariable p := (le_div_iff₀ ht).mpr (not_lt.mp hb)
        rw [hru p ht (not_lt.mp hb), min_eq_left hb', max_eq_right hab, hright]
  have hξ : ContinuousOn similarityVariable forwardHalfSpace := fun p hp ↦
    ((by fun_prop : ContinuousAt (fun q : ℝ^2 ↦ q 1) p).div (by fun_prop) hp.ne').continuousWithinAt
  have hcontinuous : ContinuousOn u forwardHalfSpace :=
    (ContinuousOn.comp (fun ξ hξ ↦ (hreg ξ hξ).continuousAt.continuousWithinAt)
      ((continuous_const.max (continuous_const.min continuous_id)).comp_continuousOn hξ)
      fun p _ ↦ ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩).congr fun p hp ↦ hformula p hp
  let M := max |a| |b|
  have hma : -M ≤ a := (neg_le_neg (le_max_left |a| |b|)).trans (neg_abs_le a)
  have hbm : b ≤ M := (le_abs_self b).trans (le_max_right |a| |b|)
  have htrace := hasInitialTraceLocallyL1_riemannData_of_finitePropagation hmu hbu
    (fun p ht hp ↦ hlu p (hp.trans_le (mul_le_mul_of_nonneg_right hma ht.le)))
    (fun p ht hp ↦ hru p ht ((mul_le_mul_of_nonneg_right hbm ht.le).trans hp))
  have hlocal : ∀ D : Set (ℝ^2), IsCompact D → ∃ B : ℝ, ∀ p ∈ D, p ∈ forwardHalfSpace → ‖u p‖ ≤ B :=
    fun _ _ ↦ ⟨K, fun p _ hp ↦ hbu p hp⟩
  have hui := locallyIntegrable_restrict_of_bound_on_compacts (μ := volume)
    forwardHalfSpace.isOpen.measurableSet hmu.aestronglyMeasurable hlocal
  have hfi := locallyIntegrable_comp_restrict_of_bound_on_compacts (μ := volume)
    forwardHalfSpace.isOpen.measurableSet hmu.aestronglyMeasurable hlocal hflux.continuous
  have hinitial := isWeakInitialValueSolution_of_interior_of_initialTrace hui hfi htrace
    (fun φ ↦ by simpa only [weakIntegrand, InteriorWeakForm.integrand] using hu.weak_eq φ)
  exact ⟨u, hinitial, htrace, hmu, hcontinuous, memLp_top_of_bound hmu.aestronglyMeasurable K
      ((ae_restrict_mem forwardHalfSpace.isOpen.measurableSet).mono fun p hp ↦ hbu p hp),
    hbu, hsu, hformula, fun ψ ↦ ⟨integrableOn_initialVectorWeakIntegrand hui hfi ψ,
      integrable_initialVectorBoundary htrace.initial_locallyIntegrable ψ,
      (initialWeak_eq_zero_iff_vectorTests hui hfi
        htrace.initial_locallyIntegrable).mp hinitial.weak_initial_eq ψ⟩⟩

/-- Every expanding segment of a genuinely nonlinear characteristic
curve gives a continuous bounded centered rarefaction with its initial
equation. The whole prescribed segment is retained, in either parameter
orientation. -/
theorem exists_continuous_rarefaction_of_integralCurve {m : ℕ} {flux : ℝ^m → ℝ^m} (k : Fin m)
    (hflux : ContDiff ℝ 2 flux) (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (hgn : IsGenuinelyNonlinearFamily flux k) (C : CharacteristicField flux)
    (hspeed : C.speed = characteristicSpeed flux k) {I : Set ℝ} (hI : IsOpen I)
    (hconn : OrdConnected I) {v : ℝ → ℝ^m} (hv : IsIntegralCurveOn v C.vectorField I) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) (hexpands : C.speed (v a) < C.speed (v b)) :
    ∃ l r K : ℝ, ∃ u : ℝ^2 → ℝ^m,
      uIcc a b ⊆ Ioo l r ∧ Icc l r ⊆ I ∧
      ContDiffOn ℝ 1 (C.speedProfile v l r) ((C.speed ∘ v) '' Ioo l r) ∧
      C.speedInverse v l r '' Icc (C.speed (v a)) (C.speed (v b)) = uIcc a b ∧
      IsWeakInitialValueSolution flux (riemannData (v a) (v b)) u ∧
      HasInitialTraceLocallyL1 u (riemannData (v a) (v b)) ∧
      Measurable u ∧ ContinuousOn u forwardHalfSpace ∧
      MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
      (∀ p : ℝ^2, 0 < p 0 →
        u p = C.speedProfile v l r
          (max (C.speed (v a)) (min (C.speed (v b)) (similarityVariable p)))) ∧
      (∀ p : ℝ^2, 0 < p 0 → u p = simpleWave v (C.rarefactionPhase v l r a b) p) ∧
      Set.range (fun x : ℝ ↦ u !₂[1, x]) = v '' uIcc a b ∧
      (∀ p : ℝ^2, C.rarefactionPhase v l r a b p ∈ uIcc a b) ∧
      (∀ p : ℝ^2, 0 < p 0 →
        p 1 ≠ C.speed (v a) * p 0 → p 1 ≠ C.speed (v b) * p 0 →
        DifferentiableAt ℝ (C.rarefactionPhase v l r a b) p ∧
        (∂[0] (C.rarefactionPhase v l r a b)) p +
          C.speed (v (C.rarefactionPhase v l r a b p)) *
            (∂[1] (C.rarefactionPhase v l r a b)) p = 0) ∧
      (∀ᵐ p ∂volume.restrict forwardHalfSpace,
        DifferentiableAt ℝ (C.rarefactionPhase v l r a b) p ∧
        (∂[0] (C.rarefactionPhase v l r a b)) p +
          C.speed (v (C.rarefactionPhase v l r a b p)) *
            (∂[1] (C.rarefactionPhase v l r a b)) p = 0) ∧
      (∀ ψ : 𝓓^{1}((⊤ : TopologicalSpace.Opens ℝ^2), ℝ^m),
        IntegrableOn (fun p ↦
          ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪flux (u p), (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ)
          forwardHalfSpace volume ∧
        Integrable (fun x : ℝ ↦ ⟪riemannData (v a) (v b) x, ψ !₂[0, x]⟫_ℝ) volume ∧
        (∫ p in forwardHalfSpace,
          ⟪u p, (∂[0] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ + ⟪flux (u p), (∂[1] (ψ : ℝ^2 → ℝ^m)) p⟫_ℝ) +
          ∫ x : ℝ, ⟪riemannData (v a) (v b) x, ψ !₂[0, x]⟫_ℝ = 0) := by
  obtain ⟨l, r, hsegment, hclosure⟩ :=
    PDE.Analysis.exists_Ioo_between_uIcc_of_isOpen_ordConnected hI hconn ha hb
  have hvD := hv.mono (Ioo_subset_Icc_self.trans hclosure)
  have haD := hsegment (left_mem_uIcc : a ∈ uIcc a b)
  have hbD := hsegment (right_mem_uIcc : b ∈ uIcc a b)
  have hC := (isGenuinelyNonlinearFamily_iff hhyper k C hspeed).mp hgn
  have hσ : ContinuousOn (C.speed ∘ v) (Ioo l r) :=
    fun s hs ↦ (C.hasDerivAt_speed_comp isOpen_Ioo hvD hC hs).continuousAt.continuousWithinAt
  have hopen := PDE.Analysis.isOpen_image_Ioo_of_continuousOn_injOn hσ
    (C.injOn_speed_comp isOpen_Ioo ordConnected_Ioo hvD hC)
  have hspeedmem : Icc (C.speed (v a)) (C.speed (v b)) ⊆
      (C.speed ∘ v) '' Ioo l r := by
    rw [← C.speed_image_uIcc hvD hC haD hbD hexpands.le]
    exact image_mono hsegment
  have hprofile := C.contDiffOn_speedProfile hflux hhyper hgn hspeed hvD
  have hreg : ∀ ξ ∈ Icc (C.speed (v a)) (C.speed (v b)), ContDiffAt ℝ 1 (C.speedProfile v l r) ξ :=
    fun ξ hξ ↦ hprofile.contDiffAt (hopen.mem_nhds (hspeedmem hξ))
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (fun ξ hξ ↦ (hreg ξ hξ).continuousAt.continuousWithinAt)
  have hleft : C.speedProfile v l r (C.speed (v a)) = v a := by
    simp only [CharacteristicField.speedProfile, Function.comp_apply,
      C.speedInverse_speed hvD hC haD]
  have hright : C.speedProfile v l r (C.speed (v b)) = v b := by
    simp only [CharacteristicField.speedProfile, Function.comp_apply,
      C.speedInverse_speed hvD hC hbD]
  obtain ⟨u, hu, htrace, hm, hc, hL, hbound, hray, hformula, htests⟩ :=
    exists_continuous_initialValue_rarefaction (hflux.of_le (by norm_num))
      hexpands.le hreg (fun ξ hξ ↦ C.fderiv_flux_speedProfile hvD hC (hspeedmem hξ)) hleft hright hK
  have hsimple (p : ℝ^2) (ht : 0 < p 0) :
      u p = simpleWave v (C.rarefactionPhase v l r a b) p := hformula p ht
  refine ⟨l, r, K, u, hsegment, hclosure, hprofile,
    C.speedInverse_image_Icc hvD hC haD hbD hexpands.le,
    hu, htrace, hm, hc, hL, hbound, hray, hformula, hsimple, ?_,
    C.rarefactionPhase_mem hvD hC haD hbD hexpands.le,
    fun _ ht hpa hpb ↦ C.differentiableAt_rarefactionPhase_and_transport
      hvD hC haD hbD hexpands.le ht hpa hpb,
    C.ae_rarefactionPhase_transport hvD hC haD hbD hexpands.le, htests⟩
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    change u !₂[1, x] ∈ v '' uIcc a b
    rw [hsimple !₂[1, x] (by norm_num), simpleWave_apply]
    exact mem_image_of_mem _ (C.rarefactionPhase_mem hvD hC haD hbD hexpands.le _)
  · rintro ⟨s, hs, rfl⟩
    refine ⟨C.speed (v s), ?_⟩
    change u !₂[1, C.speed (v s)] = v s
    rw [hsimple !₂[1, C.speed (v s)] (by norm_num), simpleWave_apply,
      C.rarefactionPhase_at_speed hvD hC haD hbD hexpands.le hs]

end PDE.Hyperbolic.ConservationLaw.System
