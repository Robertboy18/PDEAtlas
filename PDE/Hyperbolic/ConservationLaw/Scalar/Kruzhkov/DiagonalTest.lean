/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Doubling
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core

/-!
# Tests concentrated near the spacetime diagonal

The test `φ(x) ρ(x - y)` is compactly supported in both variables. Differentiating
simultaneously in the two copies of a coordinate cancels the derivatives of the kernel.
The support condition ensures that both spacetime points remain in the entropy domain.

Step 3 of the proof of Evans, §11.4.3, Theorem 3, uses the symmetric test
`η_ε((x - y)/2) η_ε((t - s)/2) φ((x + y)/2, (t + s)/2)`. We evaluate the base test at the
first point instead of the midpoint; the kernel derivatives cancel in the same way as in the
passage from (45) to (46).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 3, equations (45)-(46).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

variable {U : Opens ℝ^2}

/-- The diagonal kernel has compact support because both the base point and the displacement
are confined to compact sets. -/
theorem hasCompactSupport_diagonal (φ : 𝓓^{1}(U, ℝ)) {ρ : ℝ^2 → ℝ} (hρ : HasCompactSupport ρ) :
    HasCompactSupport (fun p : ℝ^2 × ℝ^2 ↦ φ p.1 * ρ (p.1 - p.2)) := by
  apply HasCompactSupport.of_support_subset_isCompact ((φ.hasCompactSupport.prod hρ).image
      (continuous_fst.prodMk (continuous_fst.sub continuous_snd)))
  intro p hp
  have hm : φ p.1 ≠ 0 ∧ ρ (p.1 - p.2) ≠ 0 := mul_ne_zero_iff.mp hp
  exact ⟨(p.1, p.1 - p.2),
    ⟨subset_tsupport _ hm.1, subset_tsupport _ hm.2⟩, by simp⟩

/-- A compactly supported test concentrated near the diagonal of the product domain. -/
def diagonalTest (φ : 𝓓^{1}(U, ℝ)) (ρ : ℝ^2 → ℝ)
    (hρ : ContDiff ℝ 1 ρ) (hc : HasCompactSupport ρ)
    (hU : ∀ x ∈ tsupport (φ : ℝ^2 → ℝ), ∀ z ∈ tsupport ρ, x - z ∈ U) :
    𝓓^{1}(productDomain U U, ℝ) where
  toFun p := φ p.1 * ρ (p.1 - p.2)
  contDiff' := (φ.contDiff.comp contDiff_fst).mul
    (hρ.comp (contDiff_fst.sub contDiff_snd))
  hasCompactSupport' := hasCompactSupport_diagonal φ hc
  tsupport_subset' := by
    intro p hp
    have hx : p.1 ∈ tsupport (φ : ℝ^2 → ℝ) :=
      tsupport_comp_subset_preimage φ continuous_fst (tsupport_mul_subset_left hp)
    have hz : p.1 - p.2 ∈ tsupport ρ :=
      tsupport_comp_subset_preimage ρ (continuous_fst.sub continuous_snd)
        (tsupport_mul_subset_right hp)
    exact ⟨φ.tsupport_subset hx, by simpa using hU p.1 hx (p.1 - p.2) hz⟩

/-- The paired derivative of the kernel test contains no derivative of the kernel. -/
theorem fderiv_diagonalTest (φ : 𝓓^{1}(U, ℝ)) (ρ : ℝ^2 → ℝ) (hρ : ContDiff ℝ 1 ρ)
    (hc : HasCompactSupport ρ) (hU : ∀ x ∈ tsupport (φ : ℝ^2 → ℝ), ∀ z ∈ tsupport ρ, x - z ∈ U)
    (p : ℝ^2 × ℝ^2) (i : Fin 2) :
    fderiv ℝ (diagonalTest φ ρ hρ hc hU) p (EuclideanSpace.single i 1, EuclideanSpace.single i 1) =
      ρ (p.1 - p.2) * (∂[i] (φ : ℝ^2 → ℝ)) p.1 := by
  have hφ := (φ.contDiff.differentiable_one p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have hk := (hρ.differentiable_one (p.1 - p.2)).hasFDerivAt.comp p
    (hasFDerivAt_fst.sub hasFDerivAt_snd)
  change fderiv ℝ (⇑φ ∘ Prod.fst * ρ ∘ (Prod.fst - Prod.snd)) p _ = _
  rw [(hφ.mul hk).fderiv]
  simp [partialDeriv]

/-- Substitution of a diagonal test leaves the entropy density and flux multiplied by
the kernel and by the corresponding derivatives of the base test. -/
theorem doubledWeakIntegrand_diagonalTest (flux : ℝ → ℝ) (u v : ℝ^2 → ℝ) (φ : 𝓓^{1}(U, ℝ))
    (ρ : ℝ^2 → ℝ) (hρ : ContDiff ℝ 1 ρ) (hc : HasCompactSupport ρ)
    (hU : ∀ x ∈ tsupport (φ : ℝ^2 → ℝ), ∀ z ∈ tsupport ρ, x - z ∈ U) (p : ℝ^2 × ℝ^2) :
    doubledWeakIntegrand flux u v (diagonalTest φ ρ hρ hc hU) p =
      ρ (p.1 - p.2) * (|u p.1 - v p.2| * (∂[0] (φ : ℝ^2 → ℝ)) p.1 +
        kruzhkovFlux flux (v p.2) (u p.1) * (∂[1] (φ : ℝ^2 → ℝ)) p.1) := by
  simp only [doubledWeakIntegrand, fderiv_diagonalTest, mul_add]
  congr 1 <;> ac_rfl

open SobolevSpace.Approximation

/-- All sufficiently small diagonal tests use points in a fixed compact neighborhood
of the base support, still contained in the open entropy domain. -/
theorem exists_compact_diagonal_neighborhood (φ : 𝓓^{1}(U, ℝ)) (μ : Mollifier 2)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    ∃ L : Set ℝ^2, IsCompact L ∧ L ⊆ U ∧ tsupport (φ : ℝ^2 → ℝ) ⊆ L ∧ ∀ᶠ n in atTop, ∀ x ∈
      tsupport (φ : ℝ^2 → ℝ), ∀ z ∈ tsupport (scaled μ (ε n)), x - z ∈ L := by
  obtain ⟨δ, hδ, hδU⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    U.isOpen φ.tsupport_subset
  refine ⟨Metric.cthickening δ (tsupport (φ : ℝ^2 → ℝ)),
    φ.hasCompactSupport.cthickening, hδU, Metric.self_subset_cthickening _, ?_⟩
  obtain ⟨R, hR⟩ := μ.compactSupport.isBounded.subset_closedBall (0 : ℝ^2)
  have hsmall : ∀ᶠ n in atTop, ε n * R < δ :=
    (hlim.mul_const R).eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [hsmall] with n hn x hx z hz
  have hs : tsupport (scaled μ (ε n)) ⊆ Metric.closedBall (0 : ℝ^2) (ε n * R) :=
    closure_minimal (support_scaled_subset_closedBall μ (hε n) hR) Metric.isClosed_closedBall
  have hzR : ‖z‖ ≤ ε n * R := by simpa using hs hz
  apply Metric.mem_cthickening_of_dist_le (x - z) x δ _ hx
  simpa [dist_eq_norm] using hzR.trans hn.le

/-- Shrinking a mollifier eventually makes its diagonal test admissible on any open
spacetime domain containing the compact support of the base test. -/
theorem eventually_diagonalTest_admissible (φ : 𝓓^{1}(U, ℝ)) (μ : Mollifier 2)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ x ∈ tsupport (φ : ℝ^2 → ℝ), ∀ z ∈ tsupport (scaled μ (ε n)), x - z ∈ U := by
  obtain ⟨L, _, hLU, _, hL⟩ := exists_compact_diagonal_neighborhood φ μ hε hlim
  filter_upwards [hL] with n hn x hx z hz using hLU (hn x hx z hz)

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
