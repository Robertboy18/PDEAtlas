/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.SobolevExponent

/-!
# A uniform Sobolev constant on interior subdomains

Zero extension embeds every `H¹₀(V)`, for open `V ⊆ Ω`, into `H¹₀(Ω)` while
preserving the gradient norm and each scalar `Lᑫ` norm. Consequently the
Sobolev constant of one bounded ambient domain works on all its open
subdomains. No regularity of the boundary of the smaller domain is required.

This supplies the uniform constant needed when the De Giorgi argument uses
a sequence of shrinking domains, in every positive dimension.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω V : Set ℝ^n}

private theorem eLpNorm_zeroExtend_coordinate
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω)
    (u : H¹₀(V)) (a : DerivIndex n 1) (q : ℝ≥0∞) :
    eLpNorm (wkpCoordinateCLM a
      (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω))) q (domainMeasure n Ω) =
        eLpNorm (wkpCoordinateCLM a (u : H¹(V))) q (domainMeasure n V) := by
  have he : (wkpCoordinateCLM a
      (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω)) : ℝ^n → ℝ) =ᵐ[
        domainMeasure n Ω] V.indicator (wkpCoordinateCLM a (u : H¹(V)) : ℝ^n → ℝ) :=
    ZeroTrace.zeroExtendH10ToSuperset_coordinate_apply_ae hV hΩ hVΩ u a
  rw [eLpNorm_congr_ae he,
    eLpNorm_indicator_eq_eLpNorm_restrict hV.measurableSet.nullMeasurableSet]
  congr 1
  rw [domainMeasure, Measure.restrict_restrict hV.measurableSet,
    inter_eq_left.mpr hVΩ]

private theorem norm_gradient_zeroExtend_to_superset
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hVΩ : V ⊆ Ω) (u : H¹₀(V)) :
    ‖∇ (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω))‖ =
      ‖∇ (u : H¹(V))‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have he : ‖∇ (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω))‖ ^ 2 =
      ∑ i, ‖wkpCoordinateCLM (singleDerivIndex n i)
        (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω))‖ ^ 2 :=
    Lp.norm_euclideanTuple_sq _
  have hu : ‖∇ (u : H¹(V))‖ ^ 2 =
      ∑ i, ‖wkpCoordinateCLM (singleDerivIndex n i) (u : H¹(V))‖ ^ 2 :=
    Lp.norm_euclideanTuple_sq _
  rw [he, hu]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact eLpNorm_zeroExtend_coordinate hV hΩ hVΩ u (singleDerivIndex n i) 2

/-- `exists_uniform_eLpNorm_le_gradient_on_subdomains` for an open ambient set. -/
private theorem exists_uniform_eLpNorm_le_gradient_on_subdomains_of_isOpen
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hn : (0 : ℝ) < n)
    {q : ℝ≥0∞} (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Set ℝ^n), IsOpen V → V ⊆ Ω → ∀ u : H¹₀(V),
        MemLp (baseRepresentative (u : H¹(V))) q (domainMeasure n V) ∧
          eLpNorm (baseRepresentative (u : H¹(V))) q (domainMeasure n V) ≤
            ENNReal.ofReal (C * ‖∇ (u : H¹(V))‖) := by
  have hqt : q ≠ ∞ := (hq.trans_lt ENNReal.coe_lt_top).ne
  have hnN : 0 < n := by exact_mod_cast hn
  have hqr : 2 ≤ q.toReal := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono hqt hq2
  have hcritical (hn2 : 2 < n) : q.toReal ≤ 2 * (n : ℝ) / ((n : ℝ) - 2) := by
    have hq' : q ≤ (Inequalities.pStar n 2 : ℝ≥0∞) := by
      simpa only [ite_eq_left hn2] using hq
    have hh := ENNReal.toReal_mono ENNReal.coe_ne_top hq'
    have hnR : (2 : ℝ) < n := by exact_mod_cast hn2
    simpa only [ENNReal.coe_toReal,
      Inequalities.pStar_coe (p := 2) hnN (by simpa only [NNReal.coe_ofNat] using hnR),
      NNReal.coe_ofNat] using hh
  obtain ⟨C, hC, hSob⟩ := exists_eLpNorm_le_gradient_of_sobolevExponent
    hnN hΩ hΩb hqr hcritical
  simp only [ENNReal.ofReal_toReal hqt] at hSob
  refine ⟨C, hC, ?_⟩
  intro V hV hVΩ u
  obtain ⟨hmem, hs⟩ := hSob (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u)
  refine ⟨?_, ?_⟩
  · change eLpNorm (wkpCoordinateCLM (baseIndex n 1) (u : H¹(V)))
      q (domainMeasure n V) < ∞
    rw [← eLpNorm_zeroExtend_coordinate hV hΩ hVΩ]
    exact hmem
  change eLpNorm (wkpCoordinateCLM (baseIndex n 1)
    (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω))) q
      (domainMeasure n Ω) ≤ ENNReal.ofReal
        (C * ‖∇ (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hVΩ u : H¹(Ω))‖) at hs
  rw [eLpNorm_zeroExtend_coordinate hV hΩ hVΩ,
    norm_gradient_zeroExtend_to_superset hV hΩ hVΩ] at hs
  exact hs

/-- One positive constant controls the `Lᑫ` norm by the gradient on every
open subdomain of a fixed bounded set. In dimensions above two the
critical exponent is included; in dimensions one and two, `q ≤ 4` suffices
for the strict gain used here. Open subdomains lie in the interior, so the
ambient set need not be open. -/
theorem exists_uniform_eLpNorm_le_gradient_on_subdomains
    (hΩb : Bornology.IsBounded Ω) (hn : (0 : ℝ) < n)
    {q : ℝ≥0∞} (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Set ℝ^n), IsOpen V → V ⊆ Ω → ∀ u : H¹₀(V),
        MemLp (baseRepresentative (u : H¹(V))) q (domainMeasure n V) ∧
          eLpNorm (baseRepresentative (u : H¹(V))) q (domainMeasure n V) ≤
            ENNReal.ofReal (C * ‖∇ (u : H¹(V))‖) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_eLpNorm_le_gradient_on_subdomains_of_isOpen
    isOpen_interior (hΩb.subset interior_subset) hn hq2 hq
  exact ⟨C, hC, fun V hV hVΩ u ↦ h V hV (hV.subset_interior_iff.mpr hVΩ) u⟩

end SobolevSpace.GraphSpace
