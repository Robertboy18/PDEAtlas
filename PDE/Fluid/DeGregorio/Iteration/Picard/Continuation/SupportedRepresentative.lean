/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall

/-!
# Support of a Sobolev graph from its real representative

The real-coordinate representative determines both the L² base and its
almost-everywhere support. In particular a constructed H² graph with the
physical support enclosure belongs to the supported iteration class.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace DeGregorio.Iteration

/-- A real representative supported in `K` puts its bounded Sobolev base in
the supported ball used by the Picard iteration. -/
theorem mem_supportedHkBaseBall_of_real_representative
    {k : ℕ} {K : Set ℝ} {B : ℝ} {f : DerivLp 1 2 univ} {v : ℝ → ℝ}
    (hK : MeasurableSet K) (hf : f ∈ hkBaseBall 1 k univ B)
    (hrep : (oneDimensionalPushforwardL2 f : ℝ → ℝ) =ᵐ[volume] v)
    (hs : Function.support v ⊆ K) :
    f ∈ supportedHkBaseBall 1 k univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' K) B := by
  have hv : MeasureTheory.MemLp v 2 volume :=
    (memLp_congr_ae hrep).mp (MeasureTheory.Lp.memLp (oneDimensionalPushforwardL2 f))
  have hbase : f = oneDimensionalPullbackL2 (hv.toLp v) := by
    apply oneDimensionalPushforwardL2.injective
    rw [oneDimensionalPushforwardL2_pullback]
    exact Lp.ext (hrep.trans (hv.coeFn_toLp).symm)
  apply (mem_supportedHkBaseBall_iff
    (hK.preimage (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).continuous.measurable) f).mpr
  refine ⟨hf, ?_⟩
  rw [hbase]
  filter_upwards [oneDimensionalPullbackL2_toLp_ae hv] with x hx
  intro hnot
  rw [hx]
  exact Function.notMem_support.mp fun hn ↦ hnot (hs hn)

end DeGregorio.Iteration
