/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.Classical.Data.LpCurves
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Sobolev
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Sobolev time derivatives constructed from raw smooth spacetime data

A single function smooth up to the cylinder boundary determines every spatial
Sobolev time-derivative curve. Endpoint slices are constructed from its canonical
continuous mixed derivatives. Continuity in the finite Sobolev graph follows
coordinate by coordinate; the injective base-coordinate map then detects the
weak time links.

Outside the closed time interval the curves are set to zero, so that they are
total functions. On the interval, every endpoint value, restriction, and time
derivative comes from the raw function; no higher regularity family is assumed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Evolution.Classical

open Filter MeasureTheory Set PDE.Common GraphSpace
open PDE.Analysis.Evolution
open scoped Topology ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : ℝ^(n + 1) → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

/-- The Sobolev curve of the `j`-th time derivative, at spatial order `r`. -/
def sobolevCurve (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) (t : ℝ) :
    W^{r,2}(Ω) :=
  if ht : t ∈ Icc a b then
    (derivativeSlice_regular hopen hbounded hab hf (List.replicate j 0) r ht).toWkpSpaceOn
      hopen hbounded 2
  else 0

/-- On the closed interval the curve is exactly the classical slice's Sobolev class. -/
theorem sobolevCurve_eq_toWkpSpaceOn
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    sobolevCurve hopen hbounded hab hf r j t =
      (derivativeSlice_regular hopen hbounded hab hf (List.replicate j 0) r ht).toWkpSpaceOn
        hopen hbounded 2 := by
  simp [sobolevCurve, ht]

/-- Every coordinate of the Sobolev curve is its canonical mixed derivative class. -/
theorem wkpCoordinate_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) (d : DerivIndex n r)
    {t : ℝ} (ht : t ∈ Icc a b) :
    wkpCoordinateCLM d (sobolevCurve hopen hbounded hab hf r j t) =
      derivativeLpCurve hopen hbounded hf (d.toList.map Fin.succ ++ List.replicate j 0) t := by
  rw [sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf r j ht]
  apply Lp.ext
  filter_upwards [(derivativeSlice_regular hopen hbounded hab hf
    (List.replicate j 0) r ht).toWkpSpaceOn_apply_ae hopen hbounded 2 d,
    derivativeLpCurve_ae hopen hbounded hf (d.toList.map Fin.succ ++ List.replicate j 0) t,
    ae_restrict_mem hopen.measurableSet] with x hclass hcurve hx
  exact hclass.trans ((iteratedPartialDeriv_derivativeSlice hopen hbounded hab hf
    (List.replicate j 0) d.toList ht hx).trans hcurve.symm)

/-- The canonical derivative curves are continuous in every finite Sobolev norm. -/
theorem continuousOn_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) :
    ContinuousOn (sobolevCurve hopen hbounded hab hf r j) (Icc a b) := by
  apply Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
  apply (PiLp.homeomorph 2 (fun _ : DerivIndex n r ↦ DerivLp n 2 Ω)).isEmbedding
    |>.continuousOn_iff.mpr
  apply continuousOn_pi.mpr
  intro d
  exact (continuous_derivativeLpCurve hopen hbounded hf
    (d.toList.map Fin.succ ++ List.replicate j 0)).continuousOn.congr
      (fun t ht ↦ wkpCoordinate_sobolevCurve hopen hbounded hab hf r j d ht)

/-- The base class is the canonical time derivative of the original raw function. -/
theorem wkpBaseCoordinate_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf r j t) =
      derivativeLpCurve hopen hbounded hf (List.replicate j 0) t := by
  simpa only [wkpBaseCoordinateCLM, baseIndex_toList, List.map_nil, List.nil_append] using
    wkpCoordinate_sobolevCurve hopen hbounded hab hf r j (baseIndex n r) ht

/-- The base coordinate represents the canonical derivative slice. -/
theorem wkpBaseCoordinate_sobolevCurve_ae
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    (wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf r j t) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] derivativeSlice hopen hf (List.replicate j 0) t := by
  rw [wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf r j ht]
  exact derivativeLpCurve_ae hopen hbounded hf (List.replicate j 0) t

/-- The constructed value curve has any prescribed `L²` class of the original
continuous slice. The equality includes the initial and terminal slices. -/
theorem wkpBaseCoordinate_sobolevCurve_zero_eq
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hc : ContinuousOn f (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    (r : ℕ) {t : ℝ} (ht : t ∈ Icc a b) {v : DerivLp n 2 Ω}
    (hv : (fun x ↦ f (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω] (v : ℝ^n → ℝ)) :
    wkpBaseCoordinateCLM (sobolevCurve hopen hbounded hab hf r 0 t) = v := by
  apply Lp.ext
  filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf r 0 ht,
    hv, ae_restrict_mem hopen.measurableSet] with x hx hv hxΩ
  exact hx.trans ((derivativeSlice_nil hopen hab hf hc ht (subset_closure hxΩ)).trans hv)

/-- The Sobolev curves have their adjacent weak time derivatives. -/
theorem hasWeakTimeDerivativeOn_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (sobolevCurve hopen hbounded hab hf r j)
      (sobolevCurve hopen hbounded hab hf r (j + 1)) := by
  have hA := wkpBaseCoordinateCLM_injective (p := 2) (r := r) hopen
  have hc₀ := (continuousOn_sobolevCurve hopen hbounded hab hf r j).mono Ioo_subset_Icc_self
  have hc₁ := (continuousOn_sobolevCurve hopen hbounded hab hf r (j + 1)).mono
    Ioo_subset_Icc_self
  have hi₀ := hc₀.locallyIntegrableOn (μ := volume) measurableSet_Ioo
  have hi₁ := hc₁.locallyIntegrableOn (μ := volume) measurableSet_Ioo
  apply HasWeakTimeDerivativeOn.of_map
    (wkpBaseCoordinateCLM (n := n) (m := r) (p := 2) (Ω := Ω)) hA hi₀ hi₁
  apply (hasWeakTimeDerivativeOn_derivativeLpCurve hopen hbounded hf
    (List.replicate j 0)).congr_ae_restrict measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf r j
      (Ioo_subset_Icc_self ht)).symm
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [List.replicate_succ] using
      (wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf r (j + 1)
        (Ioo_subset_Icc_self ht)).symm

/-- The weak links give derivatives on the closed interval,
with the prescribed canonical values at both endpoints. -/
theorem hasDerivWithinAt_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (sobolevCurve hopen hbounded hab hf r j)
      (sobolevCurve hopen hbounded hab hf r (j + 1) t) (Icc a b) t := by
  have h := hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hf r j
  exact h.hasDerivWithinAt_of_continuousOn hab
    (continuousOn_sobolevCurve hopen hbounded hab hf r j)
    (continuousOn_sobolevCurve hopen hbounded hab hf r (j + 1)) ht

/-- Spatial order restriction commutes with the construction at every time. -/
theorem lowerOrder_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) {q r : ℕ} (hqr : q ≤ r) (j : ℕ) (t : ℝ) :
    lowerOrderCLM hqr (sobolevCurve hopen hbounded hab hf r j t) =
      sobolevCurve hopen hbounded hab hf q j t := by
  by_cases ht : t ∈ Icc a b
  · rw [sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf r j ht,
      sobolevCurve_eq_toWkpSpaceOn hopen hbounded hab hf q j ht]
    exact ContDiffUpToBoundary.lowerOrder_toWkpSpaceOn _ hopen hbounded 2 hqr
  · simp [sobolevCurve, ht]

/-- Compact time continuity supplies every finite Bochner integrability exponent. -/
theorem memLp_sobolevCurve
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) (p : ℝ≥0∞) :
    MemLp (sobolevCurve hopen hbounded hab hf r j) p (volume.restrict (Ioc a b)) := by
  have hc := continuousOn_sobolevCurve hopen hbounded hab hf r j
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  apply MemLp.of_bound ((hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hC t (Ioc_subset_Icc_self ht)

/-- The constructed square-integrable Sobolev derivative as a Bochner class. -/
def sobolevTimeDerivative (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) :
    Lp (W^{r,2}(Ω)) 2 (volume.restrict (Ioc a b)) :=
  (memLp_sobolevCurve hopen hbounded hab hf r j 2).toLp
    (sobolevCurve hopen hbounded hab hf r j)

/-- The Bochner class retains the concrete continuous curve almost everywhere. -/
theorem sobolevTimeDerivative_ae
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r j : ℕ) :
    (sobolevTimeDerivative hopen hbounded hab hf r j : ℝ → W^{r,2}(Ω))
      =ᵐ[volume.restrict (Ioc a b)] sobolevCurve hopen hbounded hab hf r j :=
  (memLp_sobolevCurve hopen hbounded hab hf r j 2).coeFn_toLp

/-- The constructed Bochner classes commute with spatial order restriction. -/
theorem lowerOrder_sobolevTimeDerivative
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) {q r : ℕ} (hqr : q ≤ r) (j : ℕ) :
    (lowerOrderCLM (n := n) (p := 2) (Ω := Ω) hqr).compLpL
        2 (volume.restrict (Ioc a b)) (sobolevTimeDerivative hopen hbounded hab hf r j) =
      sobolevTimeDerivative hopen hbounded hab hf q j := by
  apply Lp.ext
  filter_upwards [(lowerOrderCLM (n := n) (p := 2) (Ω := Ω) hqr).coeFn_compLpL
    (sobolevTimeDerivative hopen hbounded hab hf r j),
    sobolevTimeDerivative_ae hopen hbounded hab hf r j,
    sobolevTimeDerivative_ae hopen hbounded hab hf q j] with t hmap hr hq
  rw [hmap, hr, hq]
  exact lowerOrder_sobolevCurve hopen hbounded hab hf hqr j t

/-- Every spatial Sobolev order realizes the same time-dependent base class. -/
theorem wkpBaseCoordinate_sobolevTimeDerivative_eq
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r s j : ℕ) :
    (wkpBaseCoordinateCLM (n := n) (m := r) (p := 2) (Ω := Ω)).compLpL
        2 (volume.restrict (Ioc a b)) (sobolevTimeDerivative hopen hbounded hab hf r j) =
      (wkpBaseCoordinateCLM (n := n) (m := s) (p := 2) (Ω := Ω)).compLpL
        2 (volume.restrict (Ioc a b)) (sobolevTimeDerivative hopen hbounded hab hf s j) := by
  apply Lp.ext
  filter_upwards [wkpBaseCoordinateCLM.coeFn_compLpL
      (sobolevTimeDerivative hopen hbounded hab hf r j),
    wkpBaseCoordinateCLM.coeFn_compLpL
      (sobolevTimeDerivative hopen hbounded hab hf s j),
    sobolevTimeDerivative_ae hopen hbounded hab hf r j,
    sobolevTimeDerivative_ae hopen hbounded hab hf s j,
    ae_restrict_mem measurableSet_Ioc] with t hr hs hcr hcs ht
  rw [hr, hs, hcr, hcs,
    wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf r j (Ioc_subset_Icc_self ht),
    wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf s j (Ioc_subset_Icc_self ht)]

/-- At any two spatial orders, adjacent constructed Bochner classes retain
the time derivative of their common base coordinate. -/
theorem hasWeakTimeDerivativeOn_base_sobolevTimeDerivative
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (r s j : ℕ) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (sobolevTimeDerivative hopen hbounded hab hf r j t))
      (fun t ↦ wkpBaseCoordinateCLM
        (sobolevTimeDerivative hopen hbounded hab hf s (j + 1) t)) := by
  apply (hasWeakTimeDerivativeOn_derivativeLpCurve hopen hbounded hf
    (List.replicate j 0)).congr_ae_restrict measurableSet_Ioo
  · filter_upwards [(sobolevTimeDerivative_ae hopen hbounded hab hf r j).filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
      ae_restrict_mem measurableSet_Ioo] with t hclass ht
    rw [hclass]
    exact (wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf r j
      (Ioo_subset_Icc_self ht)).symm
  · filter_upwards [(sobolevTimeDerivative_ae hopen hbounded hab hf s (j + 1)).filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
      ae_restrict_mem measurableSet_Ioo] with t hclass ht
    rw [hclass]
    simpa only [List.replicate_succ] using
      (wkpBaseCoordinate_sobolevCurve hopen hbounded hab hf s (j + 1)
        (Ioo_subset_Icc_self ht)).symm

end SobolevSpace.Evolution.Classical
