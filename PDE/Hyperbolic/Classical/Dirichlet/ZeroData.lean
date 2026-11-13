/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.Dirichlet.Energy
public import PDE.Analysis.Calculus.MeanValue.ClosedInterval
import PDE.FDeriv.Calculus

/-!
# Zero-data rigidity on a closed wave cylinder

Energy conservation forces the time derivative to vanish in positive
dimension. In dimension zero the same assertion follows directly from the
second-order ODE. Time integration and continuity then give equality on the
whole closed cylinder, with no connectedness assumption on the spatial domain.
-/

@[expose] public noncomputable section

namespace WaveEquation.Dirichlet

open MeasureTheory PDE.Common PDE.Analysis Set SobolevSpace Filter
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {u : ℝ^(n + 1) → ℝ}

/-- Zero initial data and zero lateral values force the interior time
partial to vanish. Dimension zero is the scalar ODE branch. -/
theorem timePartial_eq_zero_of_zero_data
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b))) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Ω, u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Ω, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici a) a = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, waveOperator u (timeSpaceCons t x) = 0) {t : ℝ}
    (ht : t ∈ Ioo a b) {x : ℝ^n} (hx : x ∈ Ω) :
    (∂[0] u) (timeSpaceCons t x) = 0 := by
  classical
  have hQ := isOpen_spaceTimeCylinder (I := Ioo a b) hΩ isOpen_Ioo
  let hj := hu.partialDeriv_of_succ hQ 0
  let J := hj.continuousRepresentative
  have hJc : Continuous J := hj.continuous_continuousRepresentative
  have hJreg : ContDiffUpToBoundary 1 J (spaceTimeCylinder Ω (Ioo a b)) :=
    hj.regular_continuousRepresentative hQ
  have hJeq : EqOn J (∂[0] u) (spaceTimeCylinder Ω (Ioo a b)) := hj.continuousRepresentative_eqOn
  have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩
  rw [← hJeq hp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hd : ∀ s ∈ Ioo a b, HasDerivAt (fun r ↦ J (timeSpaceCons r x)) 0 s := by
      intro s hs
      have hq := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨hs, hx⟩
      have hdiff := (hJreg.contDiffOn.contDiffAt (hQ.mem_nhds hq)).differentiableAt
        (by simp)
      have hder := PDE.hasDerivAt_timeSpaceCons J s x hdiff
      have hsecond : (∂[0] J) (timeSpaceCons s x) = 0 := by
        rw [PDE.partialDeriv_congr_nhds 0 (hJeq.eventuallyEq_of_mem (hQ.mem_nhds hq))]
        simpa only [waveOperator, Fin.sum_univ_zero, sub_zero] using hPDE x hx s hs
      rwa [hsecond] at hder
    have hcurve : Continuous (fun s ↦ J (timeSpaceCons s x)) :=
      hJc.comp ((contDiff_timeSpaceCons_uncurry 0 (m := 1)).continuous.comp
        (continuous_id.prodMk continuous_const))
    rw [PDE.constantOn_Icc_of_hasDerivAt_zero hab hcurve.continuousOn hd t (Ioo_subset_Icc_self ht)]
    exact hu.continuousRepresentative_partialDeriv_initial_eq_zero hab hΩ hbounded hc hpos hvel 0 hx
  · let : Fact (0 < n) := ⟨hn⟩
    have hEzero : ∀ s ∈ Icc a b, firstJetEnergy hu hΩ s = 0 := by
      intro s hs
      rw [PDE.constantOn_Icc_of_hasDerivAt_zero hab (continuousOn_firstJetEnergy hu hΩ hbounded hab)
        (fun r hr ↦ hasDerivAt_firstJetEnergy hu hΩ hbounded hgraph hc hzero hPDE hr) s hs]
      exact firstJetEnergy_initial_eq_zero hu hΩ hbounded hab hc hpos hvel
    have hr := hJreg.spaceSlice hΩ isOpen_Ioo ht
    have hint : IntegrableOn (fun y ↦ J (timeSpaceCons t y) ^ 2) Ω := by
      simpa only [pow_two] using (hr.mul hr hΩ hbounded).integrableOn hΩ hbounded
    have hle : (∫ y in Ω, J (timeSpaceCons t y) ^ 2) ≤ firstJetEnergy hu hΩ t := by
      apply Finset.single_le_sum (f := fun i : Fin (n + 1) ↦ ∫ y in Ω,
        (hu.partialDeriv_of_succ hQ i).continuousRepresentative (timeSpaceCons t y) ^ 2)
        (s := Finset.univ) (a := 0)
      · exact fun i _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _)
      · exact Finset.mem_univ _
    have hintzero : (∫ y in Ω, J (timeSpaceCons t y) ^ 2) = 0 := by
      rw [hEzero t (Ioo_subset_Icc_self ht)] at hle
      exact le_antisymm hle (integral_nonneg (fun _ ↦ sq_nonneg _))
    have hae := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hint).mp hintzero
    have heqzero : EqOn (fun y ↦ J (timeSpaceCons t y)) (fun _ ↦ 0) Ω := by
      apply Measure.eqOn_open_of_ae_eq (μ := volume) _ hΩ
        hr.contDiffOn.continuousOn continuousOn_const
      filter_upwards [hae] with y hy using sq_eq_zero_iff.mp hy
    exact heqzero hx

/-- A homogeneous wave with zero initial displacement, right velocity,
and zero lateral values vanishes on the entire closed cylinder. -/
theorem eq_zero_on_closedCylinder_of_zero_data
    (hu : ContDiffUpToBoundary 2 u (spaceTimeCylinder Ω (Ioo a b))) (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (hc : ContinuousOn u (closure (spaceTimeCylinder Ω (Ioo a b))))
    (hzero : ∀ x ∈ frontier Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Ω, u (timeSpaceCons a x) = 0)
    (hvel : ∀ x ∈ Ω, derivWithin (fun s ↦ u (timeSpaceCons s x)) (Ici a) a = 0)
    (hPDE : ∀ x ∈ Ω, ∀ t ∈ Ioo a b, waveOperator u (timeSpaceCons t x) = 0) :
    ∀ x ∈ closure Ω, ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0 := by
  rcases lt_or_ge a b with hab | hba
  swap
  · intro x hx t ht
    by_cases hxΩ : x ∈ Ω
    · rw [le_antisymm (ht.2.trans hba) ht.1]
      exact hpos x hxΩ
    · exact hzero x ⟨hx, by rwa [hΩ.interior_eq]⟩ t ht
  have hQ := isOpen_spaceTimeCylinder (I := Ioo a b) hΩ isOpen_Ioo
  have hslicezero {x : ℝ^n} (hx : x ∈ Ω) : ∀ t ∈ Icc a b, u (timeSpaceCons t x) = 0 := by
    have hcurve := (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_id.prodMk (continuous_const (y := x)))
    have hcont : ContinuousOn (fun t ↦ u (timeSpaceCons t x)) (Icc a b) := by
      refine hc.comp hcurve.continuousOn fun t ht ↦ ?_
      rw [closure_spaceTimeCylinder, closure_Ioo hab.ne]
      exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, subset_closure hx⟩
    have hd : ∀ t ∈ Ioo a b, HasDerivAt (fun s ↦ u (timeSpaceCons s x)) 0 t := by
      intro t ht
      have hp := timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩
      have h := PDE.hasDerivAt_timeSpaceCons u t x
        ((hu.contDiffOn.contDiffAt (hQ.mem_nhds hp)).differentiableAt (by simp))
      rwa [timePartial_eq_zero_of_zero_data
        hu hΩ hbounded hgraph hab hc hzero hpos hvel hPDE ht hx] at h
    intro t ht
    rw [PDE.constantOn_Icc_of_hasDerivAt_zero hab hcont hd t ht, hpos x hx]
  have hQzero : EqOn u (fun _ ↦ 0) (spaceTimeCylinder Ω (Ioo a b)) := by
    intro p hp
    change p 0 ∈ Ioo a b ∧ spatialPartCLM n p ∈ Ω at hp
    simpa only [timeSpaceCons_spatialPartCLM] using hslicezero hp.2 (p 0) (Ioo_subset_Icc_self hp.1)
  have hclosed := hQzero.of_subset_closure hc continuousOn_const subset_closure Subset.rfl
  intro x hx t ht
  apply hclosed
  rw [closure_spaceTimeCylinder, closure_Ioo hab.ne]
  exact timeSpaceCons_mem_spaceTimeCylinder.mpr ⟨ht, hx⟩

end WaveEquation.Dirichlet
