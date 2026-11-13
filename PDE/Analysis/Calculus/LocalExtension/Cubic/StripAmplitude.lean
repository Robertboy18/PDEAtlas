/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Coordinates.Strip.Compact
public import PDE.Analysis.Calculus.LocalExtension.Cubic.Construction

/-!
# Strip widths and compact amplitudes

Compactness supplies a uniform signed strip inside the open parameter domain.
The amplitude statement then projects the generic zero-preserving localization,
keeping its chosen amplitude and support bound. Neither statement requires a
flux or characteristic-family hypothesis.
-/

@[expose] public noncomputable section

open Function Set
open scoped ContDiff

namespace PDE.Analysis

/-- Shrink a supplied chart width once so that a fixed compact strip lies in an
open parameter domain. This choice precedes amplitude localization and every
later small correction scale. -/
theorem exists_pos_strip_width_in_open_domain
    {K : Set ℝ} {Ω : Set (ℝ × ℝ)} (hK : IsCompact K) (hΩ : IsOpen Ω)
    (hbase : ∀ t ∈ K, (t, (0 : ℝ)) ∈ Ω) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ K ×ˢ Icc (-r) r ⊆ Ω := by
  have hzero : ((K ×ˢ {(0 : ℝ)}) ×ˢ {(0 : ℝ)}) ⊆ Ω ×ˢ (univ : Set ℝ) := by
    rintro ⟨⟨t, μ⟩, n⟩ ⟨⟨ht, hμ⟩, _⟩
    have hμzero : μ = 0 := mem_singleton_iff.mp hμ
    subst μ
    exact ⟨hbase t ht, mem_univ n⟩
  obtain ⟨T, s, _, hKT, hs, hbox⟩ :=
    exists_uniform_strip_box hK (hΩ.prod isOpen_univ) hzero
  refine ⟨min ρ s, lt_min hρ hs, min_le_left _ _, ?_⟩
  rintro ⟨t, μ⟩ ⟨ht, hμ⟩
  have hμs : μ ∈ Icc (-s) s :=
    ⟨(neg_le_neg (min_le_right ρ s)).trans hμ.1, hμ.2.trans (min_le_right ρ s)⟩
  have hpoint : ((t, μ), (0 : ℝ)) ∈ (T ×ˢ Icc (-s) s) ×ˢ Icc (-s) s :=
    ⟨⟨hKT ht, hμs⟩, ⟨neg_nonpos.mpr hs.le, hs.le⟩⟩
  exact (hbox hpoint).1

/-- Localize a parameter residual in state space around the whole fixed strip.
The amplitude is globally smooth even when `R` is only smooth on the open set
`Ω`. Its topological support stays inside the allowed state domain and the
preimage of `Ω` under the first two coordinate components.

Only recovery on the strip is required. No global inverse property of `coord`
is used, and this construction has no small-scale parameter. -/
theorem exists_compact_amplitude_of_strip_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {w R : ℝ × ℝ → E} {coord : E → (ℝ × ℝ) × ℝ}
    {K : Set ℝ} {Ω : Set (ℝ × ℝ)} {U : Set E} {r : ℝ}
    (hw : Continuous w) (hK : IsCompact K) (hcoord : ContDiff ℝ ∞ coord)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hR : ContDiffOn ℝ ∞ R Ω)
    (hstate : MapsTo w (K ×ˢ Icc (-r) r) U)
    (hdomain : K ×ˢ Icc (-r) r ⊆ Ω)
    (hrecover : ∀ p ∈ K ×ˢ Icc (-r) r, coord (w p) = (p, 0)) :
    ∃ A : E → E, ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
      tsupport A ⊆ U ∩ (fun x ↦ (coord x).1) ⁻¹' Ω ∧
      ∀ p ∈ K ×ˢ Icc (-r) r, A (w p) = R p := by
  obtain ⟨A, hA, hAc, hsupport, hstrip, _⟩ :=
    exists_compact_amplitude_of_strip_coordinates_preserving_zeros
      hw hK hcoord hU hΩ hR hstate hdomain hrecover
  exact ⟨A, hA, hAc, hsupport, hstrip⟩

end PDE.Analysis
