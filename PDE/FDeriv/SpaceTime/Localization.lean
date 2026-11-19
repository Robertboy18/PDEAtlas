/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Localization.Spatial
public import PDE.FDeriv.SpaceTime.ContinuousJets
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity
import PDE.FDeriv.Laplacian.Product
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Spatial cutoffs of fields with continuous coordinate jets

A cutoff supported inside the spatial domain produces a global spatial field
with continuous Laplacian and the expected time derivative. The time
set remains arbitrary. Local regularity of the original field suffices because
the cutoff product is identically zero near every point outside its support.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.FDeriv

variable {n : ℕ}

/-- Spatial localization preserves joint continuity of the coordinate Laplacian.
Only the original field, its first spatial derivatives, and its Laplacian
need be jointly continuous on the local cylinder. -/
theorem continuousOn_laplacian_spatial_cutoff
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → ℝ} {χ : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hχ : ContDiff ℝ 2 χ) (hχΩ : tsupport χ ⊆ Ω)
    (hu : ContinuousOn u.uncurry (Ω ×ˢ I))
    (hfirst : ∀ i : Fin n, ContinuousOn
      (fun p : ℝ^n × ℝ ↦ (∂[i] (fun x ↦ u x p.2)) p.1) (Ω ×ˢ I))
    (hL : ContinuousOn (fun p : ℝ^n × ℝ ↦ laplacian (fun x ↦ u x p.2) p.1)
      (Ω ×ˢ I))
    (hspace : ∀ t ∈ I, ContDiffOn ℝ 2 (fun x ↦ u x t) Ω) :
    ContinuousOn (fun p : ℝ^n × ℝ ↦
      laplacian (fun x ↦ χ x * u x p.2) p.1) (univ ×ˢ I) := by
  apply Analysis.continuousOn_of_spatial_support_subset hΩ
    (isClosed_tsupport χ) hχΩ
  · have hcross : ContinuousOn (fun p : ℝ^n × ℝ ↦
        ∑ i : Fin n, (∂[i] χ) p.1 *
          (∂[i] (fun x ↦ u x p.2)) p.1) (Ω ×ˢ I) := by
      apply continuousOn_finsetSum
      intro i _
      exact (((contDiff_partialDeriv_of_succ (i := i) (m := 1) hχ).continuous).comp
        continuous_fst).continuousOn.mul (hfirst i)
    have hformula : ContinuousOn (fun p : ℝ^n × ℝ ↦
        laplacian χ p.1 * u p.1 p.2 +
          2 * (∑ i : Fin n, (∂[i] χ) p.1 *
            (∂[i] (fun x ↦ u x p.2)) p.1) +
          χ p.1 * laplacian (fun x ↦ u x p.2) p.1) (Ω ×ˢ I) := by
      exact (((hχ.continuous_coordinate_laplacian.comp continuous_fst).continuousOn.mul hu).add
        (continuousOn_const.mul hcross)).add
        ((hχ.continuous.comp continuous_fst).continuousOn.mul hL)
    apply hformula.congr
    intro p hp
    exact laplacian_mul hχ.contDiffAt
      ((hspace p.2 hp.2).contDiffAt (hΩ.mem_nhds hp.1))
  · intro p _ hp
    exact EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport
      (fun hx ↦ hp (tsupport_mul_subset_left hx))

/-- The time derivative of a spatially localized field, including at
an endpoint of the time set. No time regularity is required outside the
spatial domain. -/
theorem hasDerivWithinAt_spatial_cutoff
    {Ω : Set (ℝ^n)} {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    {D : ℝ^n × ℝ → ℝ} {χ : ℝ^n → ℝ}
    (hχΩ : tsupport χ ⊆ Ω)
    (htime : ∀ p ∈ Ω ×ˢ I, HasDerivWithinAt (u p.1) (D p) I p.2)
    (x : ℝ^n) {t : ℝ} (ht : t ∈ I) :
    HasDerivWithinAt (fun s ↦ χ x * u x s) (χ x * D (x, t)) I t := by
  by_cases hx : χ x = 0
  · simpa only [hx, zero_mul] using hasDerivWithinAt_const t I (0 : ℝ)
  · have hxΩ : x ∈ Ω := hχΩ (subset_tsupport χ (by simpa using hx))
    exact HasDerivWithinAt.const_mul (χ x) (htime (x, t) ⟨hxΩ, ht⟩)

end PDE.FDeriv
