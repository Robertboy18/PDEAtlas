/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity
public import PDE.Spaces.Sobolev.Fractional.Integer.ClassicalRepresentation
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData

/-!
# Smooth compact data as classical initial values

Two facts that turn a Sobolev wave built from smooth compactly supported data into a classical
solution with those data.

* `classicalRepresentative_mkWkpSpaceOnOfContDiff`: above the classical Sobolev threshold, the
  canonical continuous representative of the Sobolev class of a smooth compactly supported
  function is that function at every point.
* `deriv_deriv_eq_of_wave_derivatives`: if `q` has the derivative `v` and `v` has the derivative
  `a` within a closed time strip `[0, b]`, then the second derivative of `q` is `a` at every
  interior time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ}

/-- The canonical representative of smooth compact data is the original
function at every point, not just almost everywhere. -/
theorem classicalRepresentative_mkWkpSpaceOnOfContDiff (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    {g : ℝ^n → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    (classicalRepresentativeCLM hk
      (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) g hg hc) : ℝ^n → ℝ) = g := by
  symm
  apply eq_classicalRepresentativeCLM_of_ae_eq hk _ hg.continuous
  simpa only [baseRepresentative, wkpBaseCoordinateCLM_apply,
    domainMeasure, Measure.restrict_univ] using
    (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (k := k) (Ω := univ) hg hc).symm

/-- Continuous derivative fields on a closed strip identify the
iterated time derivative at interior times. -/
theorem deriv_deriv_eq_of_wave_derivatives {b : ℝ} {q v a : ℝ → ℝ}
    (h : ∀ t ∈ Icc 0 b, HasDerivWithinAt q (v t) (Icc 0 b) t ∧ HasDerivWithinAt v (a t) (Icc 0 b) t)
    {t : ℝ} (ht : t ∈ Ioo 0 b) :
    deriv (deriv q) t = a t := by
  have heq : deriv q =ᶠ[𝓝 t] v := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact ((h r ⟨hr.1.le, hr.2.le⟩).1.hasDerivAt (Icc_mem_nhds hr.1 hr.2)).deriv
  rw [heq.deriv_eq]
  exact ((h t ⟨ht.1.le, ht.2.le⟩).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)).deriv

end PDE.Hyperbolic.NonlinearWave.Cauchy
