/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Duhamel.Representation.Differentiation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PDE.FDeriv.Laplacian.Congruence
import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Duhamel representation of a given compactly supported function

A `C^{2,1}` function with a common compact spatial support equals the heat evolution of its initial
slice plus the Duhamel integral of its heat residual. The proof differentiates the backward Gaussian
pairing. Continuity at the terminal time follows from the Gaussian approximate identity, including
when the datum itself varies with time.

The time derivatives at the two endpoints are relative to the closed interval. Neither a future
extension nor a mixed spatial-time derivative is assumed.

The identity takes the place of (36) in Evans's proof of §2.3.3(b), Theorem 8, which he obtains from
Theorems 2 and 7 for a cutoff that vanishes at the initial time. Our identity keeps the initial
slice and uses no uniqueness theorem. `spatialCutoff_eq_initialValueSolution_add_integral` applies
it to spatial cutoffs of local solutions.

## Main results

* `eq_initialValueSolution_add_integral_heatResidual`: Duhamel's identity on a closed time interval.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), Theorem 2 (Solution of nonhomogeneous problem),
  pp. 49-50, and §2.3.3(b), the proof of Theorem 8, (33)-(36), pp. 60-61.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

open Filter MeasureTheory Set PDE.Common
open scoped Topology Interval

namespace HeatEquation

variable {n : ℕ}

/-- A continuous compactly indexed family with common compact spatial support
has continuous heat evolution, including zero heat age. -/
theorem continuous_initialValueSolution_compact_family
    {I : Set ℝ} {K : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}
    (hI : IsCompact I) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (I ×ˢ univ))
    (hsupport : ∀ s ∈ I, ∀ y ∉ K, u s y = 0) :
    Continuous (fun p : I × ℝ^n × ℝ ↦
      initialValueSolution (u p.1) p.2.1 p.2.2) := by
  have hfamily : Continuous (fun p : I × ℝ^n ↦ u p.1 p.2) :=
    hu.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun p ↦ ⟨p.1.property, mem_univ _⟩)
  obtain ⟨M, hM⟩ := (hI.prod hK).exists_bound_of_continuousOn
    (hu.mono (prod_mono_right (subset_univ K)))
  apply continuous_initialValueSolution_family hfamily (M := max M 0)
  intro p
  by_cases hy : p.2 ∈ K
  · exact (hM (p.1, p.2) ⟨p.1.property, hy⟩).trans (le_max_left _ _)
  · simp only [hsupport p.1 p.1.property p.2 hy, norm_zero]
    exact le_max_right _ _

/-- Duhamel's identity for a spatially compact `C^{2,1}` function on a closed
time interval. Integrability and endpoint convergence follow from the
continuity, derivative, and support hypotheses. -/
theorem eq_initialValueSolution_add_integral_heatResidual
    {u D : ℝ → ℝ^n → ℝ} {a b : ℝ} {K : Set (ℝ^n)}
    (hab : a ≤ b) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (Icc a b ×ˢ univ))
    (hD : ContinuousOn D.uncurry (Icc a b ×ˢ univ))
    (hL : ContinuousOn (fun p : ℝ × ℝ^n ↦ laplacian (u p.1) p.2)
      (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Icc a b, ∀ y,
      HasDerivWithinAt (fun r ↦ u r y) (D s y) (Icc a b) s)
    (hsupport : ∀ s ∈ Icc a b, ∀ y ∉ K, u s y = 0)
    (hspace : ∀ s ∈ Icc a b, ContDiff ℝ 2 (u s))
    (x : ℝ^n) :
    u b x = initialValueSolution (u a) x (b - a) +
      ∫ s in a..b, initialValueSolution (fun y ↦ D s y - laplacian (u s) y)
        x (b - s) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp [initialValueSolution_of_t_eq_zero]
  have hDzero (s : ℝ) (hs : s ∈ Icc a b) (y : ℝ^n) (hy : y ∉ K) :
      D s y = 0 := by
    apply (uniqueDiffOn_Icc hab s hs).eq_deriv (Icc a b) (hd s hs y)
    exact (hasDerivWithinAt_const s (Icc a b) (0 : ℝ)).congr_of_mem
      (fun r hr ↦ hsupport r hr y hy) hs
  have hLzero (s : ℝ) (hs : s ∈ Icc a b) (y : ℝ^n) (hy : y ∉ K) :
      laplacian (u s) y = 0 := by
    have heq : u s =ᶠ[𝓝 y] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with z hz
      exact hsupport s hs z hz
    simpa [laplacian, partialDeriv] using
      EuclideanLaplacian.laplacian_congr_nhds heq
  have hRsupport : ∀ s ∈ Icc a b, ∀ y ∉ K,
      D s y - laplacian (u s) y = 0 := by
    intro s hs y hy
    rw [hDzero s hs y hy, hLzero s hs y hy, sub_self]
  have hcont (v : ℝ → ℝ^n → ℝ)
      (hv : ContinuousOn v.uncurry (Icc a b ×ˢ univ))
      (hvs : ∀ s ∈ Icc a b, ∀ y ∉ K, v s y = 0) :
      ContinuousOn (fun s ↦ initialValueSolution (v s) x (b - s)) (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_initialValueSolution_compact_family isCompact_Icc hK hv hvs).comp
      (continuous_id.prodMk (continuous_const.prodMk
        (continuous_const.sub continuous_subtype_val)))
  have hF := hcont u hu hsupport
  have hR := hcont (fun s y ↦ D s y - laplacian (u s) y) (hD.sub hL) hRsupport
  have hderiv (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r ↦ initialValueSolution (u r) x (b - r))
        (initialValueSolution (fun y ↦ D s y - laplacian (u s) y) x (b - s)) s := by
    apply hasDerivAt_initialValueSolution_backward hK
      (hu.mono (prod_mono_left Ioo_subset_Icc_self))
      (hD.mono (prod_mono_left Ioo_subset_Icc_self))
      (fun r hr y ↦ (hd r ⟨hr.1.le, hr.2.le⟩ y).hasDerivAt
        (Icc_mem_nhds hr.1 hr.2))
      (fun r hr ↦ hsupport r ⟨hr.1.le, hr.2.le⟩)
      (fun r hr ↦ hspace r ⟨hr.1.le, hr.2.le⟩) x hs
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hF hderiv
    (hR.intervalIntegrable_of_Icc hab.le)
  simpa only [sub_self, initialValueSolution_of_t_eq_zero, add_comm] using
    (eq_add_of_sub_eq hFTC.symm)

end HeatEquation
