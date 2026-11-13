/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Keeping a strip correction off the outer branches

There are two reasons a correction can vanish along an outer branch. In the
coordinate neighborhood, the interpolation residual vanishes on each constant
collar. Away from that neighborhood, compactness gives a common parameter width
on which the outer branch misses the fixed closed support.

The first argument outside the realized compact set uses the global zero
implications of the amplitude and scalar cutoff. Those implications follow from
the construction formulas; retaining them in the existential owner is separate
work. On the realized compact set, the existing cubic identity already suffices.

All ODE conclusions concern the supplied curve on its supplied native domain.
Far times range over compact sets. Unbounded physical tails and the full axis
segments belong to the separate tail-isolation and attachment owners.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

/-- On the realized strip, a locally constant cutoff preserves the corresponding
actual outer branch and its differential equation, even inside the amplitude's
support neighborhood. Both the cubic identity and the residual-zero implication
are already outputs of the interpolation realization owner.

This applies on its prescribed compact time set and chosen speed interval. The
two ODE premises retain their original time and speed and assert no extension
beyond the native intervals. The coordinate version below handles further
chart collars once the constructor's global zero output is retained. -/
theorem interpolation_collar_preserves_outer_equations
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f P : E → E} {u v w R : ℝ × ℝ → E}
    {θ : ℝ → ℝ} {p : ℝ × ℝ} {c : ℝ}
    (hblend : w p = u p + θ p.1 • (v p - u p))
    (hrealize : P (w p) = p.2 ^ 3 • R p)
    (hresidual : (θ p.1 = 0 ∨ θ p.1 = 1) → deriv θ p.1 = 0 → R p = 0)
    (hflat : θ =ᶠ[𝓝 p.1] (fun _ ↦ c)) (hc : c = 0 ∨ c = 1)
    (hu : HasDerivAt (fun s ↦ u (s, p.2)) (f (u p) - p.2 • u p) p.1)
    (hv : HasDerivAt (fun s ↦ v (s, p.2)) (f (v p) - p.2 • v p) p.1) :
    P (w p) = 0 ∧
      (c = 0 → P (u p) = 0 ∧
        HasDerivAt (fun s ↦ u (s, p.2)) ((f + P) (u p) - p.2 • u p) p.1) ∧
      (c = 1 → P (v p) = 0 ∧
        HasDerivAt (fun s ↦ v (s, p.2)) ((f + P) (v p) - p.2 • v p) p.1) := by
  have hvalue : θ p.1 = c := hflat.self_of_nhds
  have hderiv : deriv θ p.1 = 0 := by
    simpa only [deriv_const] using hflat.deriv_eq
  have hR : R p = 0 := hresidual (by simpa only [hvalue] using hc) hderiv
  have hP : P (w p) = 0 := by rw [hrealize, hR, smul_zero]
  refine ⟨hP, ?_, ?_⟩
  · intro hc0
    have hw : w p = u p := by
      rw [hblend, hvalue, hc0, zero_smul, add_zero]
    have hPu : P (u p) = 0 := by rw [← hw]; exact hP
    exact ⟨hPu, by simpa only [Pi.add_apply, hPu, add_zero] using hu⟩
  · intro hc1
    have hw : w p = v p := by
      rw [hblend, hvalue, hc1, one_smul, add_sub_cancel]
    have hPv : P (v p) = 0 := by rw [← hw]; exact hP
    exact ⟨hPv, by simpa only [Pi.add_apply, hPv, add_zero] using hv⟩

/-- The same preservation holds on a further chart collar, without requiring
that collar to lie in the compact realization set. The only extra constructor
output is the global implication that a zero coordinate residual gives a zero
correction. It follows by composing the amplitude-zero and cutoff-zero outputs.

Recovery is required at the actual interpolated state. The compact extension of
the inverse is not treated as an inverse outside its agreement neighborhood. -/
theorem interpolation_collar_preserves_outer_equations_of_coordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f P : E → E} {u v w R : ℝ × ℝ → E}
    {coord : E → (ℝ × ℝ) × ℝ} {θ : ℝ → ℝ} {p : ℝ × ℝ} {c : ℝ}
    (hblend : w p = u p + θ p.1 • (v p - u p))
    (hrecover : (coord (w p)).1 = p)
    (hzero : ∀ x, R (coord x).1 = 0 → P x = 0)
    (hresidual : (θ p.1 = 0 ∨ θ p.1 = 1) → deriv θ p.1 = 0 → R p = 0)
    (hflat : θ =ᶠ[𝓝 p.1] (fun _ ↦ c)) (hc : c = 0 ∨ c = 1)
    (hu : HasDerivAt (fun s ↦ u (s, p.2)) (f (u p) - p.2 • u p) p.1)
    (hv : HasDerivAt (fun s ↦ v (s, p.2)) (f (v p) - p.2 • v p) p.1) :
    P (w p) = 0 ∧
      (c = 0 → P (u p) = 0 ∧
        HasDerivAt (fun s ↦ u (s, p.2)) ((f + P) (u p) - p.2 • u p) p.1) ∧
      (c = 1 → P (v p) = 0 ∧
        HasDerivAt (fun s ↦ v (s, p.2)) ((f + P) (v p) - p.2 • v p) p.1) := by
  have hvalue : θ p.1 = c := hflat.self_of_nhds
  have hderiv : deriv θ p.1 = 0 := by
    simpa only [deriv_const] using hflat.deriv_eq
  have hR : R p = 0 := hresidual (by simpa only [hvalue] using hc) hderiv
  have hP : P (w p) = 0 := hzero _ (by rw [hrecover, hR])
  have hrealize : P (w p) = p.2 ^ 3 • R p := by rw [hP, hR, smul_zero]
  exact interpolation_collar_preserves_outer_equations
    hblend hrealize hresidual hflat hc hu hv

/-- A continuous family missing a closed set along a compact zero section still
misses it on one open time neighborhood and one closed parameter interval.
The radius is uniform in time; pointwise continuity alone would not provide it. -/
theorem exists_uniform_avoidance_of_compact_zero_section
    {X E : Type*} [TopologicalSpace X] [TopologicalSpace E]
    {B : X × ℝ → E} {K : Set X} {C : Set E}
    (hB : Continuous B) (hK : IsCompact K) (hC : IsClosed C)
    (hbase : ∀ t ∈ K, B (t, 0) ∉ C) :
    ∃ (T : Set X) (r : ℝ), IsOpen T ∧ K ⊆ T ∧ 0 < r ∧
      ∀ t ∈ T, ∀ μ : ℝ, |μ| ≤ r → B (t, μ) ∉ C := by
  have hzero : K ×ˢ {(0 : ℝ)} ⊆ B ⁻¹' Cᶜ := by
    rintro ⟨t, μ⟩ ⟨ht, hμ⟩
    have hμ0 : μ = 0 := hμ
    subst μ
    exact hbase t ht
  obtain ⟨T, M, hT, hM, hKT, hzeroM, hbox⟩ :=
    generalized_tube_lemma hK isCompact_singleton (hC.isOpen_compl.preimage hB) hzero
  obtain ⟨r, hr, hball⟩ :
      ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ℝ) r ⊆ M :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hM.mem_nhds (hzeroM rfl))
  refine ⟨T, r, hT, hKT, hr, ?_⟩
  intro t ht μ hμ
  apply hbox
  refine ⟨ht, hball ?_⟩
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hμ

/-- Disjoint compact time sets on an injective base orbit have disjoint state
images. A thin strip around the first set therefore avoids the entire far image.

This chooses a permissible amplitude neighborhood before choosing the amplitude:
intersect the chart neighborhood with the complement of `q '' D`, then shrink
only the transverse width. It does not assert avoidance for an amplitude whose
support was already chosen without that restriction. -/
theorem exists_uniform_strip_avoiding_far_base_image
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {q : ℝ → E} {w : ℝ × ℝ → E} {K D : Set ℝ}
    (hq : Continuous q) (hw : Continuous w) (hK : IsCompact K) (hD : IsCompact D)
    (hinj : InjOn q (K ∪ D)) (hdisjoint : Disjoint K D)
    (hbase : ∀ t ∈ K, w (t, 0) = q t) :
    ∃ (T : Set ℝ) (r : ℝ), IsOpen T ∧ K ⊆ T ∧ 0 < r ∧
      ∀ t ∈ T, ∀ μ : ℝ, |μ| ≤ r → w (t, μ) ∉ q '' D := by
  apply exists_uniform_avoidance_of_compact_zero_section hw hK (hD.image hq).isClosed
  intro t ht
  rintro ⟨s, hs, hst⟩
  have hst' : s = t := hinj (Or.inr hs) (Or.inl ht) (hst.trans (hbase t ht))
  exact Set.disjoint_left.mp hdisjoint ht (hst' ▸ hs)

/-- Every correction supported in one fixed closed set preserves the outer
family on a common speed interval, provided the compact base segment misses
that set. The radius precedes the correction, flux and ODE domain.

The derivative conclusion only changes the vector field at the same point. It
keeps the supplied within-derivative domain, including its endpoints. Global
smooth representatives do not enlarge that domain. -/
theorem exists_uniform_outer_equations_of_support_separation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : ℝ × ℝ → E} {D : Set ℝ} {C : Set E}
    (hB : Continuous B) (hD : IsCompact D) (hC : IsClosed C)
    (hbase : ∀ t ∈ D, B (t, 0) ∉ C) :
    ∃ r : ℝ, 0 < r ∧ ∀ P : E → E, tsupport P ⊆ C →
      ∀ μ : ℝ, |μ| ≤ r → ∀ t ∈ D,
        P (B (t, μ)) = 0 ∧ ∀ (f : E → E) (J : Set ℝ),
          HasDerivWithinAt (fun s ↦ B (s, μ))
            (f (B (t, μ)) - μ • B (t, μ)) J t →
          HasDerivWithinAt (fun s ↦ B (s, μ))
            ((f + P) (B (t, μ)) - μ • B (t, μ)) J t := by
  obtain ⟨T, r, _, hDT, hr, havoid⟩ :=
    exists_uniform_avoidance_of_compact_zero_section hB hD hC hbase
  refine ⟨r, hr, ?_⟩
  intro P hsupport μ hμ t ht
  have hnot : B (t, μ) ∉ tsupport P :=
    fun hx ↦ havoid t (hDT ht) μ hμ (hsupport hx)
  have hP : P (B (t, μ)) = 0 := image_eq_zero_of_notMem_tsupport hnot
  refine ⟨hP, ?_⟩
  intro f J hode
  simpa only [Pi.add_apply, hP, add_zero] using hode

/-- Combine constant-residual chart collars with far support avoidance on one
compact outer-time envelope. Its part outside the open chart time set is compact,
so one speed radius handles all far times. Inside the chart, recovery and the
constructor's zero implication give pointwise vanishing, without asserting that
those points lie outside the topological support.

The collar residual hypothesis is obtained from the interpolation owner's
constant-cutoff conclusion on its actual parameter domain. The base-avoidance
hypothesis concerns the fixed closed support set, not a nonzero-speed branch.
The same correction is retained on both parts and for all smaller speeds. -/
theorem exists_uniform_outer_equations_of_chart_collars
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B R : ℝ × ℝ → E} {P : E → E} {coord : E → (ℝ × ℝ) × ℝ}
    {D T : Set ℝ} {C : Set E} {ρ : ℝ}
    (hB : Continuous B) (hD : IsCompact D) (hT : IsOpen T) (hC : IsClosed C)
    (hsupport : tsupport P ⊆ C) (hρ : 0 < ρ)
    (hbase : ∀ t ∈ D \ T, B (t, 0) ∉ C)
    (hrecover : ∀ t ∈ D ∩ T, ∀ μ : ℝ, |μ| ≤ ρ →
      (coord (B (t, μ))).1 = (t, μ))
    (hcollar : ∀ t ∈ D ∩ T, ∀ μ : ℝ, |μ| ≤ ρ → R (t, μ) = 0)
    (hzero : ∀ x, R (coord x).1 = 0 → P x = 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ ∀ μ : ℝ, |μ| ≤ r → ∀ t ∈ D,
      P (B (t, μ)) = 0 ∧ ∀ (f : E → E) (J : Set ℝ),
        HasDerivWithinAt (fun s ↦ B (s, μ))
          (f (B (t, μ)) - μ • B (t, μ)) J t →
        HasDerivWithinAt (fun s ↦ B (s, μ))
          ((f + P) (B (t, μ)) - μ • B (t, μ)) J t := by
  obtain ⟨rFar, hrFar, hfar⟩ :=
    exists_uniform_outer_equations_of_support_separation hB (hD.diff hT) hC hbase
  refine ⟨min ρ rFar, lt_min hρ hrFar, min_le_left _ _, ?_⟩
  intro μ hμ t ht
  have hμρ : |μ| ≤ ρ := hμ.trans (min_le_left _ _)
  have hμFar : |μ| ≤ rFar := hμ.trans (min_le_right _ _)
  by_cases htT : t ∈ T
  · have hP : P (B (t, μ)) = 0 := by
      apply hzero
      rw [hrecover t ⟨ht, htT⟩ μ hμρ]
      exact hcollar t ⟨ht, htT⟩ μ hμρ
    refine ⟨hP, ?_⟩
    intro f J hode
    simpa only [Pi.add_apply, hP, add_zero] using hode
  · exact hfar P hsupport μ hμFar t ⟨ht, htT⟩

end PDE.Analysis
