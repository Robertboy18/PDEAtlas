/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence.Compact
public import PDE.Analysis.Fourier.HilbertTransform.RealL2
public import PDE.Analysis.MeasureTheory.Lp.Primitive
import PDE.Analysis.Fourier.HilbertTransform.RealPair.WeakDerivative
import PDE.Analysis.MeasureTheory.Lp.Primitive.CompactConvergence

/-!
# Hilbert and velocity traces from bounded H¹ graphs

The spectral Hilbert transform preserves a weak H¹ derivative. Strong convergence
of the vorticity in L² therefore gives weak H¹ convergence of its Hilbert transform,
and compact uniform convergence of continuous coefficient representatives.
The normalized velocity converges uniformly on compact sets directly from the
L² primitive estimate.

These are the parts of terminal matching that need only H¹ control. Restarting the
Picard iteration (`IsHkFrozenOutput.exists_restart`) needs an H² terminal vorticity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The Hilbert transform of an H¹ base has an H¹ graph, constructed by
commutation with the weak derivative. -/
theorem exists_h1_hilbert_graph (U : W^{1,2}(ℝ^1)) :
    ∃ V : W^{1,2}(ℝ^1), ‖V‖ ≤ 2 * ‖U‖ ∧
      realLineCoordinateCLM (baseIndex 1 1) V =
        realHilbertTransformL2 (realLineCoordinateCLM (baseIndex 1 1) U) := by
  let f := realLineCoordinateCLM (baseIndex 1 1) U
  let g := realLineCoordinateCLM (singleDerivIndex 1 0) U
  have hweak := (isHilbertPair_realHilbertTransformL2 f).hasWeakTimeDerivativeOn
    (isHilbertPair_realHilbertTransformL2 g) (hasWeakTimeDerivativeOn_realLineCoordinates U)
  let V := mkW12OfWeakDerivative (Lp.memLp (realHilbertTransformL2 f))
    (Lp.memLp (realHilbertTransformL2 g)) hweak
  refine ⟨V, ?_, ?_⟩
  · change ‖realLineH1Jet _ _‖ ≤ _
    simp only [Lp.toLp_coeFn]
    apply (norm_realLineH1Jet_le _ _).trans
    simp only [norm_realHilbertTransformL2]
    have h₀ := norm_realLineCoordinateCLM_le (baseIndex 1 1) U
    have h₁ := norm_realLineCoordinateCLM_le (singleDerivIndex 1 0) U
    change ‖f‖ + ‖g‖ ≤ 2 * ‖U‖
    linarith
  · simp only [V, realLineCoordinateCLM_mkW12_base, Lp.toLp_coeFn, f]

/-- Uniform H¹ control and strong L² convergence determine the compact uniform
limit of continuous Hilbert coefficients. -/
theorem tendstoUniformlyOn_hilbert_of_h1_bound
    {ι : Type*} {l : Filter ι} {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)}
    {B : ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    {c : ι → ℝ → ℝ} {d : ℝ → ℝ}
    (hc : ∀ i, Continuous (c i)) (hd : Continuous d)
    (hpair : ∀ i, IsHilbertPair (realLineCoordinateCLM (baseIndex 1 1) (u i)) (c i))
    (hdpair : IsHilbertPair (realLineCoordinateCLM (baseIndex 1 1) U) d)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn c d l K := by
  choose v hv hvbase using fun i ↦ exists_h1_hilbert_graph (u i)
  obtain ⟨V, _, hVbase⟩ := exists_h1_hilbert_graph U
  have heq (i : ι) : realLineRepresentative (v i) = c i := by
    apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) (hc i)).mp
    have hrep := realLineCoordinate_ae_representative (v i)
    rw [hvbase i] at hrep
    exact hrep.symm.trans
      ((isHilbertPair_realHilbertTransformL2 _).ae_eq_right (hpair i))
  have hdeq : realLineRepresentative V = d := by
    apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) hd).mp
    have hrep := realLineCoordinate_ae_representative V
    rw [hVbase] at hrep
    exact hrep.symm.trans
      ((isHilbertPair_realHilbertTransformL2 _).ae_eq_right hdpair)
  have hVlim : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (v i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) V)) := by
    simpa only [hvbase, hVbase, Function.comp_def] using
      (realHilbertTransformL2.continuous.tendsto _).comp hbase
  have hbounded (i : ι) : ‖v i‖ ≤ 2 * B :=
    (hv i).trans (mul_le_mul_of_nonneg_left (hbound i) (by norm_num))
  have hlim := tendstoUniformlyOn_realLineRepresentative_of_weak hbounded
    (tendsto_weak_h1_of_realLineCoordinate v V hbounded hVlim) hK
  simpa only [heq, hdeq] using hlim

/-- Strong L² convergence of vorticity determines its normalized Hilbert
velocity uniformly on every compact spatial set. -/
theorem tendstoUniformlyOn_normalized_hilbert_velocity
    {ι : Type*} {l : Filter ι}
    {f : ι → DerivLp 1 2 univ} {g : DerivLp 1 2 univ}
    (hbase : Tendsto f l (𝓝 g)) {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun i ↦ l2Primitive (realHilbertTransformL2 (oneDimensionalPushforwardL2 (f i))))
      (l2Primitive (realHilbertTransformL2 (oneDimensionalPushforwardL2 g))) l K := by
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  apply tendstoUniformlyOn_l2Primitive_of_tendsto (R := R)
    ((realHilbertTransformL2.continuous.tendsto _).comp
      ((oneDimensionalPushforwardL2.continuous.tendsto _).comp hbase))
  intro x hx
  simpa only [Real.norm_eq_abs, id_eq] using hR x hx

end DeGregorio.Iteration
