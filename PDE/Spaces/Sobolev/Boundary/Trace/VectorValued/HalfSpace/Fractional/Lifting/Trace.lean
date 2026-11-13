/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.AverageLimit
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.HeightAverage

/-!
# The trace of a Sobolev representative of the mollified extension

The positive-height averages of a Sobolev function converge to its trace.
For the cutoff mollified extension, those same averages converge to the
boundary datum. Uniqueness of the limit identifies the trace whenever the
Sobolev function's base coordinate represents this extension almost everywhere.
The argument applies in every boundary dimension and at every finite `p > 1`.
-/

@[expose] public noncomputable section

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open MeasureTheory Filter Set SobolevSpace.Approximation
open GraphSpace SobolevSpace.Trace.HalfSpace
open scoped ENNReal Sobolev Topology

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Any Sobolev function represented by the cutoff mollified extension has
the prescribed boundary trace. -/
theorem traceLp_eq_of_base_ae_mollifiedExtension
    (μ : Mollifier n) (hp : 1 < p)
    {g : ℝ^n → F} (hg : MemLp g (ENNReal.ofReal p) volume)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, HalfSpace.isOpen_upper (n + 1)⟩; F))
    (hU : (coordinateCLM (baseIndex (n + 1) 1) U : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] mollifiedExtension μ g) :
    traceLp n p hp.le U = hg.toLp g := by
  let : (comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ))).NeBot :=
    Filter.comap_coe_neBot_of_le_principal inf_le_right
  have hbase : coordinateCLM (baseIndex (n + 1) 1) U =
      (memLp_mollifiedExtension μ ENNReal.ofReal_ne_top hg).toLp
        (mollifiedExtension μ g) := by
    apply Lp.ext
    exact hU.trans (memLp_mollifiedExtension μ ENNReal.ofReal_ne_top hg).coeFn_toLp.symm
  apply tendsto_nhds_unique (tendsto_heightAverageLp n p hp U)
  simpa only [hbase] using tendsto_heightAverageLp_mollifiedExtension μ p hp.le hg
    (fun ε : Ioi (0 : ℝ) ↦ (ε : ℝ)) (fun ε ↦ ε.2) tendsto_comap

/-- The physical boundary values of a Sobolev representative of the mollified
extension agree almost everywhere with the original datum. -/
theorem coeFn_traceLp_eq_of_base_ae_mollifiedExtension
    (μ : Mollifier n) (hp : 1 < p)
    {g : ℝ^n → F} (hg : MemLp g (ENNReal.ofReal p) volume)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, HalfSpace.isOpen_upper (n + 1)⟩; F))
    (hU : (coordinateCLM (baseIndex (n + 1) 1) U : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] mollifiedExtension μ g) :
    (traceLp n p hp.le U : ℝ^n → F) =ᵐ[volume] g := by
  rw [traceLp_eq_of_base_ae_mollifiedExtension μ hp hg U hU]
  exact hg.coeFn_toLp

end SobolevSpace.VectorValued.Trace.HalfSpace
