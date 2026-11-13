/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PDE.Analysis.Calculus.Gradient

/-!
# Limits of distributionally divergence-free fields

Distributional incompressibility passes to `L²` limits, because every weak divergence pairing
is the `L²` inner product with the gradient of the test, which is continuous in `L²`. For `L²`
classes this is the closedness `isClosed_l2Solenoidal` of the solenoidal subspace together with
`mem_l2Solenoidal_iff_distributionallyDivergenceFree`; the statement here is for representatives
along an arbitrary filter.

It also passes to almost everywhere limits of sequences under a locally integrable majorant:
the pairing is an integral against a continuous compactly supported gradient, so dominated
convergence applies. Fields with a singularity, such as `‖x‖⁻¹ A(x)` in three dimensions, are
reached this way from fields without one.
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace MeasureTheory Filter
open scoped Topology Gradient

set_option linter.missingDocs true

variable {n : ℕ}

/-- Distributional incompressibility passes to `L²` limits. -/
theorem DistributionallyDivergenceFree.of_tendsto_eLpNorm {ι : Type*} {l : Filter ι} [l.NeBot]
    {v : ι → ℝ^n → ℝ^n} {w : ℝ^n → ℝ^n}
    (hv : ∀ᶠ k in l, DistributionallyDivergenceFree (v k))
    (hvm : ∀ᶠ k in l, MemLp (v k) 2 volume) (hw : MemLp w 2 volume)
    (hlim : Tendsto (fun k ↦ eLpNorm (v k - w) 2 volume) l (𝓝 0)) :
    DistributionallyDivergenceFree w := by
  intro ψ hψ hψc
  have hgrad : MemLp (∇ ψ) 2 volume :=
    (PDE.Analysis.continuous_gradient_of_contDiff (hψ.of_le (by simp))).memLp_of_hasCompactSupport
      hψc.gradient
  let G : Lp (ℝ^n) 2 (volume : Measure (ℝ^n)) := hgrad.toLp (∇ ψ)
  have hpair : ∀ {u : ℝ^n → ℝ^n} (hu : MemLp u 2 volume),
      inner ℝ (hu.toLp u) G = weakDivergencePairing u ψ := by
    intro u hu
    rw [L2.inner_def, weakDivergencePairing]
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, hgrad.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂, weakDivergencePairingDensity]
  refine ⟨?_, ?_⟩
  · apply (L2.integrable_inner (𝕜 := ℝ) (hw.toLp w) G).congr
    filter_upwards [hw.coeFn_toLp, hgrad.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂, weakDivergencePairingDensity]
  · have hbound : ∀ᶠ k in l, |weakDivergencePairing w ψ| ≤
        (eLpNorm (v k - w) 2 volume).toReal * ‖G‖ := by
      filter_upwards [hv, hvm] with k hk hkm
      have hk0 : inner ℝ (hkm.toLp (v k)) G = 0 := by
        rw [hpair hkm]
        exact hk.weakDivergencePairing_eq_zero ψ hψ hψc
      rw [← hpair hw, ← Real.norm_eq_abs, ← sub_zero (inner ℝ (hw.toLp w) G), ← hk0,
        ← inner_sub_left, ← Lp.norm_toLp _ (hkm.sub hw), MemLp.toLp_sub, norm_sub_rev]
      exact norm_inner_le_norm _ _
    have hzero : Tendsto (fun k ↦ (eLpNorm (v k - w) 2 volume).toReal * ‖G‖) l (𝓝 0) := by
      rw [← zero_mul ‖G‖, ← ENNReal.toReal_zero]
      exact ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).mul_const _
    exact abs_nonpos_iff.1 (ge_of_tendsto hzero hbound)

/-- Distributional incompressibility passes to almost everywhere limits of sequences dominated
by a locally integrable function. -/
theorem DistributionallyDivergenceFree.of_tendsto_of_norm_le {v : ℕ → ℝ^n → ℝ^n}
    {w : ℝ^n → ℝ^n} {g : ℝ^n → ℝ} (hv : ∀ k, DistributionallyDivergenceFree (v k))
    (hvm : ∀ k, AEStronglyMeasurable (v k) volume) (hg : LocallyIntegrable g volume)
    (hbound : ∀ k, ∀ᵐ x, ‖v k x‖ ≤ g x)
    (hlim : ∀ᵐ x, Tendsto (fun k ↦ v k x) atTop (𝓝 (w x))) :
    DistributionallyDivergenceFree w := by
  intro ψ hψ hψc
  have hcont : Continuous (∇ ψ) :=
    PDE.Analysis.continuous_gradient_of_contDiff (hψ.of_le (by simp))
  have hmaj : Integrable (fun x ↦ g x * ‖∇ ψ x‖) volume :=
    hg.integrable_smul_right_of_hasCompactSupport hcont.norm hψc.gradient.norm
  have hdens_meas (k : ℕ) :
      AEStronglyMeasurable (weakDivergencePairingDensity (v k) ψ) volume :=
    (hvm k).inner hcont.aestronglyMeasurable
  have hdens_bound (k : ℕ) : ∀ᵐ x, ‖weakDivergencePairingDensity (v k) ψ x‖ ≤
      g x * ‖∇ ψ x‖ := by
    filter_upwards [hbound k] with x hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hdens_lim : ∀ᵐ x, Tendsto (fun k ↦ weakDivergencePairingDensity (v k) ψ x) atTop
      (𝓝 (weakDivergencePairingDensity w ψ x)) := by
    filter_upwards [hlim] with x hx
    exact hx.inner tendsto_const_nhds
  have hwm : AEStronglyMeasurable (weakDivergencePairingDensity w ψ) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop hdens_meas hdens_lim
  have hwbound : ∀ᵐ x, ‖weakDivergencePairingDensity w ψ x‖ ≤ g x * ‖∇ ψ x‖ := by
    filter_upwards [hdens_lim, ae_all_iff.mpr hdens_bound] with x hx hxk
    exact le_of_tendsto' hx.norm hxk
  refine ⟨hmaj.mono' hwm hwbound, ?_⟩
  have hint := tendsto_integral_of_dominated_convergence (fun x ↦ g x * ‖∇ ψ x‖)
    hdens_meas hmaj hdens_bound hdens_lim
  have hzero : (fun k ↦ ∫ x, weakDivergencePairingDensity (v k) ψ x) = fun _ ↦ 0 :=
    funext fun k ↦ (hv k).weakDivergencePairing_eq_zero ψ hψ hψc
  rw [hzero] at hint
  exact tendsto_nhds_unique hint tendsto_const_nhds

end IncompressibleFlow
