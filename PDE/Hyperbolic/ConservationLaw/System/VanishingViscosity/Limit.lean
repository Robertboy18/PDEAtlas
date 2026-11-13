/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.Entropy
public import PDE.Hyperbolic.ConservationLaw.System.VanishingViscosity.InitialValue
public import PDE.Hyperbolic.ConservationLaw.InitialBoundary.SmoothTesting
public import PDE.Hyperbolic.ConservationLaw.System.InitialValue

/-!
# Entropy and vanishing viscosity, including the initial datum

A given almost everywhere limit of uniformly bounded classical viscous solutions
inherits measurability, the same bound, the initial weak equation, and every
C¹ convex entropy inequality. With common initial data this is Theorem 2 of Evans, §11.4.2: the
viscous problems are (31) and the convergence hypothesis is (32). Evans's entropy pairs are
smooth; ours are `C¹`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.2, Theorem 2 and its proof, equations (30)-(34).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot]
  {flux : ℝ^m → ℝ^m} {u : ι → ℝ^2 → ℝ^m} {v : ℝ^2 → ℝ^m}
  {ε : ι → ℝ} {M : ℝ} {g : ℝ → ℝ^m}

private theorem initialWeak_of_vanishingViscosity_of_pairing_limit (hflux : ContDiff ℝ 1 flux)
    (hεlim : Tendsto ε l (𝓝 0)) (hu : ∀ᶠ i in l, ContDiffOn ℝ 2 (u i) forwardHalfSpace)
    (hclosed : ∀ᶠ i in l, ContinuousOn (u i) {p : ℝ^2 | 0 ≤ p 0})
    (hpde : ∀ᶠ i in l, ∀ p ∈ forwardHalfSpace, fluxResidual flux (u i) p =
      ε i • (∂[1] (∂[1] (u i))) p)
    (hM : ∀ᶠ i in l, ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u i p‖ ≤ M)
    (hlim : ∀ᵐ p ∂volume.restrict forwardHalfSpace, Tendsto (fun i ↦ u i p) l (𝓝 (v p)))
    (hg : LocallyIntegrable g volume)
    (hinitial : ∀ φ : 𝓓((⊤ : Opens ℝ^2), ℝ),
      Tendsto (fun i ↦ ∫ x : ℝ, φ !₂[0, x] • u i !₂[0, x]) l (𝓝 (∫ x : ℝ, φ !₂[0, x] • g x))) :
    IsWeakInitialValueSolution flux g v := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (u i) (volume.restrict forwardHalfSpace) :=
    hu.mono fun _ hi ↦ hi.continuousOn.aestronglyMeasurable forwardHalfSpace.isOpen.measurableSet
  obtain ⟨hvm, hvM⟩ := aestronglyMeasurable_and_ae_norm_le_of_tendsto hm hM hlim
  have hvi : LocallyIntegrable v (volume.restrict forwardHalfSpace) :=
    locallyIntegrable_comp_of_ae_bound hvm hvM continuous_id
  have hfi := locallyIntegrable_comp_of_ae_bound hvm hvM hflux.continuous
  refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict hvi,
    locallyIntegrableOn_of_locallyIntegrable_restrict hfi, hg,
    integrableOn_initialWeakIntegrand hvi hfi, initialWeak_eq_zero_of_smooth hvi hfi hg fun φ ↦ ?_⟩
  let ψ : InitialValueTestFunction :=
    .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
  have hpair {f : ℝ^m → ℝ^m} (hf : Continuous f) {a : ℝ^2 → ℝ} (ha : Integrable a) :
      Tendsto (fun i ↦ ∫ p in forwardHalfSpace, a p • f (u i p)) l
        (𝓝 (∫ p in forwardHalfSpace, a p • f (v p))) :=
    tendsto_integral_smul_comp_of_ae_bound hm hM hlim hf ha.restrict
  have ht := hpair continuous_id (ψ.integrable_partialDeriv 0)
  have hx := hpair hflux.continuous (ψ.integrable_partialDeriv 1)
  have hxx := hpair continuous_id
    (PDE.DistributionTheory.integrable_partialDeriv_of_hasCompactSupport 1
      (contDiff_partialDeriv_of_succ (φ.contDiff.of_le (by simp)))
      (φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single 1 1)))
  have hz : Tendsto (fun i ↦ ε i • ∫ p in forwardHalfSpace,
      (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p • u i p) l (𝓝 0) := by
    simpa using hεlim.smul hxx
  have hall := (((ht.add hx).add (hinitial φ)).add hz)
  have hint (w : ℝ^2 → ℝ^m)
      (hw : LocallyIntegrable w (volume.restrict forwardHalfSpace)) (r : Fin 2) :
      IntegrableOn (fun p ↦ (∂[r] (φ : ℝ^2 → ℝ)) p • w p) forwardHalfSpace :=
    hw.integrable_smul_left_of_hasCompactSupport
      (ψ.continuous_partialDeriv r) (ψ.hasCompactSupport_partialDeriv r)
  change Tendsto (fun i ↦ ((∫ p in forwardHalfSpace, (∂[0] (φ : ℝ^2 → ℝ)) p • u i p) +
      ∫ p in forwardHalfSpace, (∂[1] (φ : ℝ^2 → ℝ)) p • flux (u i p)) +
        (∫ x : ℝ, φ !₂[0, x] • u i !₂[0, x]) +
        ε i • ∫ p in forwardHalfSpace, (∂[1] (∂[1] (φ : ℝ^2 → ℝ))) p • u i p) l
    (𝓝 (((∫ p in forwardHalfSpace, (∂[0] (φ : ℝ^2 → ℝ)) p • v p) +
      ∫ p in forwardHalfSpace, (∂[1] (φ : ℝ^2 → ℝ)) p • flux (v p)) +
        (∫ x : ℝ, φ !₂[0, x] • g x) + 0)) at hall
  rw [add_zero, ← integral_add (hint v hvi 0) (hint (fun p ↦ flux (v p)) hfi 1)] at hall
  refine tendsto_nhds_unique hall (tendsto_const_nhds.congr' ?_)
  filter_upwards [hu, hclosed, hpde, hm, hM] with i hi hc hp hmi hMi
  have hui : LocallyIntegrable (u i) (volume.restrict forwardHalfSpace) :=
    locallyIntegrable_comp_of_ae_bound hmi hMi continuous_id
  have hfui := locallyIntegrable_comp_of_ae_bound hmi hMi hflux.continuous
  rw [← integral_add (hint (u i) hui 0) (hint (fun p ↦ flux (u i p)) hfui 1)]
  exact (integral_initialWeakIntegrand_add_viscous_eq_zero hflux hi hc hui hfui hp φ).symm

/-- The vanishing-viscosity criterion of Evans, §11.4.2, Theorem 2, with common initial data:
the original a.e. limit is measurable, has the same essential bound, satisfies
the initial weak equation, and is an entropy weak solution for every
C¹ convex entropy pair. The state dimension may be zero. -/
theorem entropySolution_of_vanishingViscosity_commonData (hflux : ContDiff ℝ 1 flux)
    (hε : ∀ᶠ i in l, 0 ≤ ε i) (hεlim : Tendsto ε l (𝓝 0))
    (hu : ∀ᶠ i in l, ContDiffOn ℝ 2 (u i) forwardHalfSpace)
    (hclosed : ∀ᶠ i in l, ContinuousOn (u i) {p : ℝ^2 | 0 ≤ p 0})
    (hpde : ∀ᶠ i in l, ∀ p ∈ forwardHalfSpace, fluxResidual flux (u i) p =
      ε i • (∂[1] (∂[1] (u i))) p)
    (hM : ∀ᶠ i in l, ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u i p‖ ≤ M)
    (hinitial : ∀ᶠ i in l, ∀ x : ℝ, u i !₂[0, x] = g x)
    (hlim : ∀ᵐ p ∂volume.restrict forwardHalfSpace, Tendsto (fun i ↦ u i p) l (𝓝 (v p))) :
    AEStronglyMeasurable v (volume.restrict forwardHalfSpace) ∧
      (∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) ∧
      IsWeakInitialValueSolution flux g v ∧ IsEntropyWeakSolution flux forwardHalfSpace v := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (u i) (volume.restrict forwardHalfSpace) :=
    hu.mono fun _ hi ↦ hi.continuousOn.aestronglyMeasurable forwardHalfSpace.isOpen.measurableSet
  obtain ⟨hvm, hvM⟩ := aestronglyMeasurable_and_ae_norm_le_of_tendsto hm hM hlim
  obtain ⟨i, hic, hig⟩ := (hclosed.and hinitial).exists
  have hgcont : Continuous g :=
    (hic.comp_continuous (by fun_prop) fun x ↦ by simp).congr hig
  have hw := initialWeak_of_vanishingViscosity_of_pairing_limit
    hflux hεlim hu hclosed hpde hM hlim hgcont.locallyIntegrable fun φ ↦
      tendsto_const_nhds.congr' <| hinitial.mono fun i hi ↦ by simp only [hi]
  exact ⟨hvm, hvM, hw, IsWeakInitialValueSolution.interior hw,
    satisfiesEntropyInequality_of_vanishingViscosity hε hεlim hu hpde hM hlim⟩

/-- The converging-data variant uses the initial slices of the viscous
family and local L¹ convergence to the prescribed datum. It applies to viscous shock
profiles. -/
theorem entropySolution_of_vanishingViscosity_convergingData (hflux : ContDiff ℝ 1 flux)
    (hε : ∀ᶠ i in l, 0 ≤ ε i) (hεlim : Tendsto ε l (𝓝 0))
    (hu : ∀ᶠ i in l, ContDiffOn ℝ 2 (u i) forwardHalfSpace)
    (hclosed : ∀ᶠ i in l, ContinuousOn (u i) {p : ℝ^2 | 0 ≤ p 0})
    (hpde : ∀ᶠ i in l, ∀ p ∈ forwardHalfSpace, fluxResidual flux (u i) p =
      ε i • (∂[1] (∂[1] (u i))) p)
    (hM : ∀ᶠ i in l, ∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖u i p‖ ≤ M)
    (hg : LocallyIntegrable g volume)
    (hinitial : ∀ K : Set ℝ, IsCompact K → Tendsto (fun i ↦ ∫ x in K, ‖u i !₂[0, x] - g x‖) l (𝓝 0))
    (hlim : ∀ᵐ p ∂volume.restrict forwardHalfSpace, Tendsto (fun i ↦ u i p) l (𝓝 (v p))) :
    AEStronglyMeasurable v (volume.restrict forwardHalfSpace) ∧
      (∀ᵐ p ∂volume.restrict forwardHalfSpace, ‖v p‖ ≤ M) ∧
      IsWeakInitialValueSolution flux g v ∧ IsEntropyWeakSolution flux forwardHalfSpace v := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (u i) (volume.restrict forwardHalfSpace) :=
    hu.mono fun _ hi ↦ hi.continuousOn.aestronglyMeasurable forwardHalfSpace.isOpen.measurableSet
  obtain ⟨hvm, hvM⟩ := aestronglyMeasurable_and_ae_norm_le_of_tendsto hm hM hlim
  have hgi : ∀ᶠ i in l, LocallyIntegrable (fun x : ℝ ↦ u i !₂[0, x]) volume :=
    hclosed.mono fun i hi ↦ (hi.comp_continuous (by fun_prop) fun x ↦ by simp).locallyIntegrable
  have hw := initialWeak_of_vanishingViscosity_of_pairing_limit
    hflux hεlim hu hclosed hpde hM hlim hg (fun φ ↦ by
      let ψ : InitialValueTestFunction :=
        .mk φ (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset
      exact tendsto_integral_smul_of_locallyL1 hgi hg hinitial
        (ψ.contDiff.continuous.comp (by fun_prop)) ψ.hasCompactSupport_initialSlice)
  exact ⟨hvm, hvM, hw, IsWeakInitialValueSolution.interior hw,
    satisfiesEntropyInequality_of_vanishingViscosity hε hεlim hu hpde hM hlim⟩

end PDE.Hyperbolic.ConservationLaw.System
