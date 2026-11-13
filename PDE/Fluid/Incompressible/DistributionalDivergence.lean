/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
import PDE.Analysis.Calculus.Divergence.Locality
import PDE.Analysis.Integration.PuncturedDivergence
import PDE.FDeriv.PartialDeriv.Regularity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Classical divergence of distributionally divergence-free fields

A vector field that is distributionally divergence free and `C¹` on an open set `U` has zero
classical divergence on `U`. The classical divergence is continuous on `U`. For a smooth test
function `g` supported in `U`, the compactly supported field `g v` is differentiable everywhere,
so its divergence `∇g · v + g div v` has integral zero, and the weak pairing removes `∇g · v`.
The fundamental lemma of the calculus of variations gives `div v = 0` almost everywhere on `U`,
and continuity gives it at every point of `U`. The opposite implication, from classical to
distributional incompressibility, is `distributionallyDivergenceFree_of_continuous_off_countable`.

Distributional incompressibility is also preserved by negation, differences, constant
multiples and almost-everywhere changes of the field.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

open MeasureTheory Filter
open scoped Topology

set_option linter.missingDocs true

/-- A distributionally divergence-free field which is `C¹` on an open set has zero classical
divergence at every point of that set. -/
theorem DistributionallyDivergenceFree.divergence_eq_zero_of_contDiffOn {n : ℕ}
    {v : ℝ^(n + 1) → ℝ^(n + 1)} {U : Set (ℝ^(n + 1))}
    (hv : DistributionallyDivergenceFree v) (hU : IsOpen U) (hvU : ContDiffOn ℝ 1 v U)
    {x : ℝ^(n + 1)} (hx : x ∈ U) : PDE.divergence v x = 0 := by
  have hcont : ContinuousOn (PDE.divergence v) U := by
    have hi (i : Fin (n + 1)) : ContinuousOn (PDE.partialDeriv i (fun y ↦ v y i)) U :=
      ((EuclideanSpace.proj i : ℝ^(n + 1) →L[ℝ] ℝ).contDiff.comp_contDiffOn
        hvU).continuousOn_partialDeriv i hU
    exact continuousOn_finsetSum (Finset.univ : Finset (Fin (n + 1))) (fun i _ ↦ hi i)
  have hdiffU (y : ℝ^(n + 1)) (hy : y ∈ U) : DifferentiableAt ℝ v y :=
    (hvU.contDiffAt (hU.mem_nhds hy)).differentiableAt one_ne_zero
  have htest : ∀ g : ℝ^(n + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ U → ∫ y, g y • PDE.divergence v y = 0 := by
    intro g hg hgc hgU
    have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
    have hzero (y : ℝ^(n + 1)) (hy : y ∉ U) : g =ᶠ[𝓝 y] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp fun h ↦ hy (hgU h)
    have hzeroV (y : ℝ^(n + 1)) (hy : y ∉ U) : (fun z ↦ g z • v z) =ᶠ[𝓝 y] 0 :=
      (hzero y hy).mono fun z hz ↦ by simp [hz]
    have hdiffV (y : ℝ^(n + 1)) : DifferentiableAt ℝ (fun z ↦ g z • v z) y := by
      by_cases hy : y ∈ U
      · exact (hg1 y).smul (hdiffU y hy)
      · exact (hzeroV y hy).differentiableAt_iff.mpr (differentiableAt_const 0)
    have hcontV : Continuous (fun z ↦ g z • v z) :=
      continuous_iff_continuousAt.mpr fun y ↦ (hdiffV y).continuousAt
    have hdivV (y : ℝ^(n + 1)) : PDE.divergence (fun z ↦ g z • v z) y =
        weakDivergencePairingDensity v g y + g y * PDE.divergence v y := by
      by_cases hy : y ∈ U
      · rw [PDE.Analysis.divergence_smul (hg1 y) (hdiffU y hy)]
        simp [weakDivergencePairingDensity]
      · have hg0 := hzero y hy
        rw [(hzeroV y hy).divergence_eq_zero]
        have hgy : g y = 0 := hg0.eq_of_nhds
        have hdg : fderiv ℝ g y = 0 := by rw [hg0.fderiv_eq]; exact fderiv_const_apply _
        simp [weakDivergencePairingDensity, hgy, hdg]
    have hgf : Continuous (fun y ↦ g y * PDE.divergence v y) := by
      refine continuous_iff_continuousAt.mpr fun y ↦ ?_
      by_cases hy : y ∈ U
      · exact hg.continuous.continuousAt.mul (hcont.continuousAt (hU.mem_nhds hy))
      · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
        exact (hzero y hy).mono fun z hz ↦ by simp [hz]
    have hint_gf : Integrable (fun y ↦ g y * PDE.divergence v y) :=
      hgf.integrable_of_hasCompactSupport hgc.mul_right
    have hdens := hv.weakDivergencePairingDensity_integrable g hg hgc
    have hpair := hv.weakDivergencePairing_eq_zero g hg hgc
    have hfun : PDE.divergence (fun z ↦ g z • v z) =
        fun y ↦ weakDivergencePairingDensity v g y + g y * PDE.divergence v y := funext hdivV
    have hintV : Integrable (PDE.divergence (fun z ↦ g z • v z)) := by
      rw [hfun]; exact hdens.add hint_gf
    have h0 := PDE.Analysis.integral_divergence_eq_zero_of_continuous_off_countable hcontV
      hgc.smul_right Set.countable_empty (fun y _ ↦ hdiffV y) hintV
    rw [hfun, integral_add hdens hint_gf] at h0
    rw [weakDivergencePairing] at hpair
    simp only [smul_eq_mul]
    linarith
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hU.measurableSet) htest
  have heq : Set.EqOn (PDE.divergence v) (fun _ ↦ 0) U :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).mpr hae) hU hcont
      continuousOn_const
  exact heq hx

/-- Distributional incompressibility is preserved by negation. -/
theorem DistributionallyDivergenceFree.neg {n : ℕ} {v : ℝ^n → ℝ^n}
    (hv : DistributionallyDivergenceFree v) : DistributionallyDivergenceFree (-v) := by
  intro ψ hψ hc
  obtain ⟨hi, h0⟩ := hv ψ hψ hc
  have hd : weakDivergencePairingDensity (-v) ψ =
      fun x ↦ -weakDivergencePairingDensity v ψ x := by
    funext x
    simp only [weakDivergencePairingDensity, Pi.neg_apply, inner_neg_left]
  refine ⟨hd ▸ hi.neg, ?_⟩
  rw [weakDivergencePairing] at h0 ⊢
  rw [hd, integral_neg, h0, neg_zero]

/-- Distributional incompressibility is preserved by differences. -/
theorem DistributionallyDivergenceFree.sub {n : ℕ} {u v : ℝ^n → ℝ^n}
    (hu : DistributionallyDivergenceFree u) (hv : DistributionallyDivergenceFree v) :
    DistributionallyDivergenceFree (u - v) := by
  rw [sub_eq_add_neg]
  exact hu.add hv.neg

/-- Distributional incompressibility is preserved by constant multiples. -/
theorem DistributionallyDivergenceFree.const_smul {n : ℕ} {v : ℝ^n → ℝ^n} (c : ℝ)
    (hv : DistributionallyDivergenceFree v) : DistributionallyDivergenceFree (c • v) := by
  intro ψ hψ hc
  obtain ⟨hi, h0⟩ := hv ψ hψ hc
  have hd : weakDivergencePairingDensity (c • v) ψ =
      fun x ↦ c * weakDivergencePairingDensity v ψ x := by
    funext x
    simp only [weakDivergencePairingDensity, Pi.smul_apply, real_inner_smul_left]
  refine ⟨hd ▸ hi.const_mul c, ?_⟩
  rw [weakDivergencePairing] at h0 ⊢
  rw [hd, integral_const_mul, h0, mul_zero]

/-- Distributional incompressibility depends only on the almost-everywhere class of the
field. -/
theorem DistributionallyDivergenceFree.congr_ae {n : ℕ} {u v : ℝ^n → ℝ^n}
    (hu : DistributionallyDivergenceFree u) (h : u =ᵐ[volume] v) :
    DistributionallyDivergenceFree v := by
  intro ψ hψ hc
  obtain ⟨hi, h0⟩ := hu ψ hψ hc
  have hd : weakDivergencePairingDensity u ψ =ᵐ[volume] weakDivergencePairingDensity v ψ := by
    filter_upwards [h] with x hx
    simp only [weakDivergencePairingDensity, hx]
  refine ⟨hi.congr hd, ?_⟩
  rw [weakDivergencePairing] at h0 ⊢
  rw [← integral_congr_ae hd, h0]

end IncompressibleFlow
