/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.CollarEstimate
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.WeightedCollar

/-!
# Surface bounds from graph collar energy

Cauchy--Schwarz combines a normalized volume energy bound with the exact
squared-conormal collar limit. The vector field needs only L² regularity.
The compact chart window is fixed before the scalar test is chosen.
-/

@[expose] public noncomputable section

open Set MeasureTheory Filter
open scoped Gradient Topology

namespace SobolevSpace.GraphSpace.Rellich

open Boundary.Flux.Graph

variable {m : ℕ}

/-- A convergent collar pairing is controlled by the graph surface integral.
This analytic statement is independent of the equation producing the pairing. -/
theorem sq_le_graphSurfaceIntegral_of_collar_energy
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ}
    (hg : ContDiff ℝ 1 g) {K : Set ℝ^(m + 1)} (hK : IsCompact K)
    {φ : ℝ^(m + 1) → ℝ} (hφ : Continuous φ) (hsupp : tsupport φ ⊆ K)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) {Z : ℝ^(m + 1) → ℝ^(m + 1)}
    (hZ : MemLp Z 2 volume) {L B : ℝ}
    (henergy : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∫ x in K ∩ {x | linearGraphHeight A g x ∈ Ioo 0 t}, ‖Z x‖ ^ 2) ≤ t * B)
    (hpair : Tendsto (fun t : ℝ ↦ t⁻¹ *
      ∫ x in K ∩ {x | linearGraphHeight A g x ∈ Ioo 0 t},
        φ x * ψ (linearGraphHeight A g x / t) * inner ℝ (Z x) (∇ (linearGraphHeight A g) x))
      (𝓝[>] 0) (𝓝 L)) :
    L ^ 2 ≤ B * ((∫ s : ℝ in (0 : ℝ)..1, ψ s ^ 2) *
      ∫ x in frontier (linearEpigraph A g),
        φ x ^ 2 * ‖fderiv ℝ (linearGraphHeight A g) x‖
          ∂Measure.euclideanHausdorffMeasure m) := by
  let d := linearGraphHeight A g
  have hd : ContDiff ℝ 1 d := by
    unfold d linearGraphHeight
    exact ((EuclideanSpace.proj (Fin.last m)).contDiff.comp A.contDiff).sub
      (hg.comp ((ContinuousLinearMap.fst ℝ (ℝ^m) ℝ).contDiff.comp
        (Trace.HalfSpace.tangentialNormalContinuousLinearEquiv.contDiff.comp A.contDiff)))
  have hgd : Continuous (∇ d) :=
    (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.continuous.comp
      (hd.continuous_fderiv one_ne_zero)
  have hcφ : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport φ) hsupp
  let S (t : ℝ) : Set ℝ^(m + 1) := K ∩ {x | d x ∈ Ioo 0 t}
  let W (t : ℝ) (x : ℝ^(m + 1)) : ℝ^(m + 1) := (φ x * ψ (d x / t)) • ∇ d x
  have hmW (t : ℝ) : MemLp (W t) 2 volume :=
    ((hφ.mul (hψ.comp (hd.continuous.div_const t))).smul hgd).memLp_of_hasCompactSupport
      hcφ.mul_right.smul_right
  have hnorm (t : ℝ) (x : ℝ^(m + 1)) :
      ‖W t x‖ ^ 2 = ψ (d x / t) ^ 2 * (φ x ^ 2 * ‖fderiv ℝ d x‖ ^ 2) := by
    have hdual : ‖∇ d x‖ = ‖fderiv ℝ d x‖ :=
      (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm.norm_map _
    change ‖(φ x * ψ (d x / t)) • ∇ d x‖ ^ 2 = _
    rw [norm_smul, norm_mul, mul_pow, mul_pow, hdual]
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  have htest := tendsto_normalized_linearGraphCollar_sq_integral A hg hφ hcφ hψ
  have htest' : Tendsto (fun t : ℝ ↦ t⁻¹ * ∫ x in S t, ‖W t x‖ ^ 2)
      (𝓝[>] 0)
      (𝓝 ((∫ s : ℝ in (0 : ℝ)..1, ψ s ^ 2) *
        ∫ x in frontier (linearEpigraph A g), φ x ^ 2 * ‖fderiv ℝ d x‖
          ∂Measure.euclideanHausdorffMeasure m)) := by
    have heq (t : ℝ) : (∫ x in S t, ‖W t x‖ ^ 2) =
        ∫ x in {x | d x ∈ Ioo 0 t},
          ψ (d x / t) ^ 2 * (φ x ^ 2 * ‖fderiv ℝ d x‖ ^ 2) := by
      simp_rw [hnorm]
      rw [show S t = K ∩ {x | d x ∈ Ioo 0 t} from rfl,
        ← Measure.restrict_restrict hK.measurableSet]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
      simp [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupp h))]
    simpa only [heq, d] using htest
  apply sq_le_mul_of_tendsto_normalized_inner
    (ν := fun t ↦ volume.restrict (S t))
    (F := fun _ ↦ Z) (G := W)
    (Eventually.of_forall fun t ↦ hZ.restrict (S t))
    (Eventually.of_forall fun t ↦ (hmW t).restrict (S t))
  · filter_upwards [henergy, self_mem_nhdsWithin] with t he (ht : 0 < t)
    exact (inv_mul_le_iff₀ ht).2 he
  · simpa only [W, inner_smul_right, RCLike.conj_to_real] using hpair
  · exact htest'

end SobolevSpace.GraphSpace.Rellich
