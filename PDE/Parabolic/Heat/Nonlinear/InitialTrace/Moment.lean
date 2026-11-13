/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.InitialLimit
public import PDE.Parabolic.Heat.Nonlinear.InitialTrace.NegativeMoment
public import PDE.Parabolic.Heat.Nonlinear.InitialTrace.Reaction
public import PDE.Spaces.Sobolev.Boundary.Collar.Volume
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Initial eigenfunction moments for signed quadratic heat solutions

The quadratic equation, separate initial and lateral continuity, and
nonnegative initial values imply initial weighted integrability and the Kaplan
moment bound. The proof uses vanishing negative moments along a sequence;
it imposes no bound or joint continuity at the omitted initial/lateral corner.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 1 (Blow-up for large data) and its proof,
  (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
* S. Kaplan, "On the growth of solutions of quasi-linear parabolic equations",
  *Comm. Pure Appl. Math.* 16 (1963), 305-330.
  <https://doi.org/10.1002/cpa.3160160307>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology ENNReal

namespace HeatEquation.Nonlinear

/-- A linear domain-collar volume estimate removes the negative initial
weighted defect for the signed quadratic heat equation. Initial
weighted integrability is part of the conclusion. -/
theorem integrable_initial_moment_and_le_eigenvalue_of_collar_bound
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}
    {w : ℝ^n → ℝ} {C lambda : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hgraph : SobolevSpace.Boundary.HasC1GraphBoundary Ω)
    (hw : ContDiffOn ℝ 2 w Ω)
    (hwup : SobolevSpace.ContDiffUpToBoundary 1 w Ω)
    (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hC : 0 < C)
    (hlayer : ∀ r > 0,
      volume.real {x : ℝ^n | x ∈ Ω ∧ Metric.infDist x Ωᶜ ≤ r} ≤ C * r)
    (hc0 : ContinuousOn u.uncurry (Ici 0 ×ˢ Ω))
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    (hinit : ∀ x ∈ Ω, 0 ≤ u 0 x) :
    IntegrableOn (fun x ↦ w x * u 0 x) Ω ∧ (∫ x in Ω, w x * u 0 x) ≤ lambda := by
  let : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hcompl : Ωᶜ.Nonempty := Set.nonempty_compl.mpr fun heq ↦
    hb.isCompact_closure.ne_univ (by rw [heq, closure_univ])
  obtain ⟨K, _, hnegative⟩ := exists_uniform_negative_moment_of_collar_bound
    hΩ hne hb hgraph hwup hwc hwzero (fun x hx ↦ (hwpos x hx).le) hC hlayer
    hc0 hc hs heq hboundary hinit
  have hreaction := integrableOn_weighted_square_of_negative_moment hΩ hb hw hwc
    hwzero hwpos hunit heigen hlambda hc hs heq hboundary hnegative zero_lt_one
  obtain ⟨L, hL, hwL⟩ := hwup.exists_norm_le_mul_infDist_compl hΩ hb hgraph hwc hwzero
  let ν : Measure (ℝ^n) := volume.restrict Ω
  let μ : Measure (ℝ^n) := ν.withDensity (fun x ↦ ENNReal.ofReal (w x))
  let : IsFiniteMeasure ν := ⟨by simpa [ν] using hb.measure_lt_top (μ := volume)⟩
  have hwi : Integrable w ν :=
    (hwc.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hac : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hmemν : ∀ᵐ x ∂ν, x ∈ Ω := ae_restrict_mem hΩ.measurableSet
  have hmem : ∀ᵐ x ∂μ, x ∈ Ω := hac.ae_le hmemν
  have hwposν : 0 ≤ᵐ[ν] w := hmemν.mono fun x hx ↦ (hwpos x hx).le
  have hI (f : ℝ^n → ℝ) : (∫ x, f x ∂μ) = ∫ x in Ω, w x * f x := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hwposν] with x hx
    simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
  let d : ℝ^n → ℝ := fun x ↦ Metric.infDist x Ωᶜ
  have hdmeas : Measurable d := (Metric.continuous_infDist_pt _).measurable
  have hdpos : ∀ᵐ x ∂μ, 0 < d x := hmem.mono fun x hx ↦
    (hΩ.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (not_not.mpr hx)
  have hvol (r : ℝ) (hr : 0 < r) : ν.real {x | d x ≤ r} ≤ C * r := by
    rw [measureReal_restrict_apply (measurableSet_le hdmeas measurable_const)]
    convert hlayer r hr using 1
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, and_comm, d]
  have hwbound : ∀ᵐ x ∂ν, w x ≤ L * d x := hmemν.mono fun x hx ↦
    (le_abs_self _).trans (hwL x hx)
  have hgrowth (r : ℝ) (hr : 0 < r) : μ.real {x | d x ^ 2 ≤ r} ≤ (L * C) * r :=
    measureReal_withDensity_sq_sublevel_le hwi hwposν hL.le hr hdmeas hwbound hvol
  let D : ℝ := 16 * (4 * (n : ℝ) + 40) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have huLp (t : ℝ) (ht : t ∈ Ioo 0 1) : MemLp (u t) 2 μ := by
    have huc : ContinuousOn (u t) (closure Ω) :=
      hc.comp (continuous_const.prodMk continuous_id).continuousOn fun x hx ↦ ⟨ht.1, hx⟩
    obtain ⟨B, hB⟩ := hb.isCompact_closure.exists_bound_of_continuousOn huc
    exact MemLp.of_bound (AEStronglyMeasurable.mono_ac hac
      ((huc.mono subset_closure).aestronglyMeasurable hΩ.measurableSet)) B
      (hmem.mono fun x hx ↦ hB x (subset_closure hx))
  have henv (t : ℝ) (ht : t ∈ Ioo 0 1) :
      ∀ᵐ x ∂μ, -u t x ≤ D * t / (d x ^ 2) ^ 2 := by
    filter_upwards [hmem] with x hx
    have hp := neg_le_infDist_bound_of_square_equation hΩ hcompl
      (hc0.mono (prod_mono Icc_subset_Ici_self Subset.rfl)) hs heq hinit
      ⟨ht.1.le, ht.2.le⟩ hx
    simpa only [D, d, ← pow_mul] using hp
  have henergy : IntegrableOn (fun t ↦ ∫ x, u t x ^ 2 ∂μ) (Ioo 0 1) := by
    simpa only [hI] using hreaction.mono_set Ioo_subset_Ioc_self
  have hmoment (t : ℝ) (ht : t ∈ Ioo 0 1) : (∫ x, u t x ∂μ) ≤ lambda := by
    rw [hI]
    exact moment_le_eigenvalue_of_global_dirichlet_square_solution hΩ hb hw hwc
      hwzero hwpos hunit heigen hlambda hc hs heq hboundary ht.1
  have htrace : ∀ᵐ x ∂μ, Tendsto (fun t ↦ u t x) (𝓝[>] 0) (𝓝 (u 0 x)) := by
    filter_upwards [hmem] with x hx
    have hcAt : ContinuousOn (fun t ↦ u t x) (Ici 0) :=
      hc0.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht ↦ ⟨ht, hx⟩
    exact (hcAt.continuousWithinAt (by exact le_rfl)).mono Ioi_subset_Ici_self
  have hg := integrable_and_integral_le_of_inverse_sq_neg_bound
    (mul_nonneg hL.le hC.le) hD zero_lt_one huLp (hdmeas.pow_const 2)
    (hdpos.mono fun x hx ↦ pow_pos hx 2) henv hgrowth henergy hmoment
    (hmem.mono fun x hx ↦ hinit x hx) htrace
  have hgi := (integrable_withDensity_iff_integrable_smul₀'
    hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hg.1
  refine ⟨hgi.congr ?_, ?_⟩
  · filter_upwards [hwposν] with x hx
    simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
  · simpa only [hI] using hg.2

/-- Nonnegative initial values have integrable eigenfunction-weighted trace
with moment at most the eigenvalue, even when the signed candidate is not
bounded near the omitted initial/lateral corner. -/
theorem integrable_initial_moment_and_le_eigenvalue_of_nonnegative_initial
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}
    {w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hgraph : SobolevSpace.Boundary.HasC1GraphBoundary Ω)
    (hw : ContDiffOn ℝ 2 w Ω)
    (hwup : SobolevSpace.ContDiffUpToBoundary 1 w Ω)
    (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda)
    (hc0 : ContinuousOn u.uncurry (Ici 0 ×ˢ Ω))
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    (hinit : ∀ x ∈ Ω, 0 ≤ u 0 x) :
    IntegrableOn (fun x ↦ w x * u 0 x) Ω ∧ (∫ x in Ω, w x * u 0 x) ≤ lambda := by
  obtain ⟨C, hC, hlayer⟩ := hgraph.exists_pos_volume_collar_le hΩ hb
  exact integrable_initial_moment_and_le_eigenvalue_of_collar_bound hΩ hne hb hgraph
    hw hwup hwc hwzero hwpos hunit heigen hlambda hC hlayer hc0 hc hs heq hboundary hinit

end HeatEquation.Nonlinear
