/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Harnack.Compact
public import PDE.Analysis.Topology.Connected.CompactNeighborhood
public import PDE.Analysis.Order.SupInfComparison

/-!
# Parabolic Harnack inequality for C²,¹ solutions

The main theorem is `exists_harnack_constant_of_space_time_derivatives`: a nonnegative solution of a
nondivergence-form parabolic equation satisfies `u x s ≤ C * u y t` for `x y ∈ closure V` and
`0 < s < t ≤ T`, and hence `sup_V u(·, s) ≤ C inf_V u(·, t)`. The coefficients are jointly
continuous, the principal matrix is symmetric and uniformly elliptic, and the potential may have
either sign. Coefficient bounds come from an interior compact cylinder, so nothing is assumed near
the spatial boundary. The ambient open set may be unbounded; only the preconnected comparison set
needs compact closure in it.

This is Evans's §7.1.4(b), Theorem 10, (69), for continuous coefficients. Evans notes that the
theorem holds for continuous, or even bounded measurable, coefficients, with a reference to
Lieberman, and proves it only for `bⁱ ≡ c ≡ 0` and smooth `aⁱʲ`, by estimates for `v = log u`.

The constant is chosen before the solution or its jets. Spatial second derivatives and one time
derivative suffice; no mixed or second time derivative is assumed. Continuity through the terminal
time gives the comparison when the later time is `T`. Empty comparison sets and zero spatial
dimension are included.

## How it works

In place of Evans's estimates for `log u`, we use parabolic contacts and measure propagation,
following the contact-set and growth method in the notes of Imbert and Silvestre. In
`PDE.Parabolic.Harnack.Local.ContactMeasure`,
`ParabolicHarnack.vertex_measure_le_mul_sublevel_measure` combines the Jacobian estimate of
`Local.ContactJacobian` with a covering by contact images. `Local.Growth` and
`Local.PeakPropagation` propagate low-level measure and peaks; `Local.SignedPotential` handles the
potential by exponential extension. `Local.Classical` passes to the stated regularity through
space-time averaging.

Imbert and Silvestre treat viscosity solutions and Pucci inequalities: §4.1 of their notes has the
monotone envelope and contact Jacobian, and §§4.2.2-4.2.3 the barrier and basic measure estimate.
Our local argument uses classical contact maps and an expanding barrier, followed by measure and
peak propagation; bounded drift and a signed potential are handled before localization to the
continuous-coefficient theorem.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.4(b), Theorem 10 (Parabolic Harnack inequality),
  (68)-(69), pp. 391-392.
  <https://doi.org/10.1090/gsm/019>
* C. Imbert and L. Silvestre, "Introduction to fully nonlinear parabolic equations", HAL preprint
  hal-00798300v1, 2013.
  <https://hal.science/hal-00798300v1>
-/

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis ParabolicMaximum Set
open scoped RealInnerProductSpace Matrix.Norms.Elementwise

variable {n : ℕ}

/-- The parabolic Harnack inequality with continuous coefficients. The solution is
assumed to have continuous spatial first and second jets and a continuous first time
derivative on the open cylinder, and to be continuous up to the terminal time `T`. -/
theorem exists_harnack_constant_of_space_time_derivatives
    {U V : Set (ℝ^n)} (hU : IsOpen U) (hcompact : IsCompact (closure V))
    (hV : IsPreconnected V) (hVU : closure V ⊆ U)
    {T s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ T)
    {a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ}
    {d : ℝ^n → ℝ → ℝ^n} {c : ℝ^n → ℝ → ℝ}
    (ha : ContinuousOn (Function.uncurry a) (U ×ˢ Ioc 0 T))
    (hd : ContinuousOn (Function.uncurry d) (U ×ˢ Ioc 0 T))
    (hc : ContinuousOn (Function.uncurry c) (U ×ˢ Ioc 0 T))
    (hsymm : ∀ p ∈ U ×ˢ Ioc 0 T, (a p.1 p.2).IsSymm)
    (hell : ∃ α : ℝ, 0 < α ∧ ∀ p ∈ U ×ˢ Ioc 0 T, ∀ w : ℝ^n,
      α * ‖w‖ ^ 2 ≤ ⟪w, (a p.1 p.2).toEuclideanLin w⟫) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ^n → ℝ → ℝ)
      (Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ) (Dt : ℝ^n × ℝ → ℝ)
      (Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ),
      ContinuousOn (Function.uncurry u) (U ×ˢ Ioc 0 T) →
      ContinuousOn Dx (U ×ˢ Ioo 0 T) →
      ContinuousOn Dt (U ×ˢ Ioo 0 T) →
      ContinuousOn Dxx (U ×ˢ Ioo 0 T) →
      (∀ p ∈ U ×ˢ Ioo 0 T, HasFDerivAt (fun x ↦ u x p.2) (Dx p) p.1) →
      (∀ p ∈ U ×ˢ Ioo 0 T, HasFDerivAt (fun x ↦ Dx (x, p.2)) (Dxx p) p.1) →
      (∀ p ∈ U ×ˢ Ioo 0 T, HasDerivAt (u p.1) (Dt p) p.2) →
      (∀ p ∈ U ×ˢ Ioc 0 T, 0 ≤ u p.1 p.2) →
      (∀ p ∈ U ×ˢ Ioo 0 T, matrixParabolicOperator a d c u p.1 p.2 = 0) →
      (∀ x ∈ closure V, ∀ y ∈ closure V, u x s ≤ C * u y t) ∧
        sSup ((fun x ↦ u x s) '' V) ≤ C * sInf ((fun x ↦ u x t) '' V) := by
  obtain ⟨α, hα, hellpoint⟩ := hell
  obtain ⟨W, hW, hWconn, hVW, hWcompact, hWU⟩ :=
    exists_preconnected_open_compact_closure hcompact hV.closure hU hVU
  let ℓ := s / 2
  have hℓ : 0 < ℓ := half_pos hs
  have hℓs : ℓ < s := half_lt_self hs
  let H := closure W ×ˢ Icc ℓ T
  have hH : IsCompact H := hWcompact.prod isCompact_Icc
  have hHU : H ⊆ U ×ˢ Ioc 0 T := by
    intro p hp
    exact ⟨hWU hp.1, hℓ.trans_le hp.2.1, hp.2.2⟩
  have hWD : W ×ˢ Ioo ℓ T ⊆ U ×ˢ Ioo 0 T := by
    intro p hp
    exact ⟨hWU (subset_closure hp.1), hℓ.trans hp.2.1, hp.2.2⟩
  have hWC : W ×ˢ Ioc ℓ T ⊆ U ×ˢ Ioc 0 T := by
    intro p hp
    exact ⟨hWU (subset_closure hp.1), hℓ.trans hp.2.1, hp.2.2⟩
  have hWH : W ×ˢ Ioo ℓ T ⊆ H := by
    intro p hp
    exact ⟨subset_closure hp.1, hp.2.1.le, hp.2.2.le⟩
  obtain ⟨M, hM⟩ :=
    (hH.image_of_continuousOn (ha.mono hHU)).isBounded.exists_norm_le
  obtain ⟨B, hB⟩ :=
    (hH.image_of_continuousOn (hd.mono hHU)).isBounded.exists_norm_le
  obtain ⟨K, hK⟩ :=
    (hH.image_of_continuousOn (hc.mono hHU)).isBounded.exists_norm_le
  obtain ⟨C, hC, hcompare⟩ := exists_harnack_comparison_on_isCompact
    hW hWconn hcompact hVW hℓs hst ht
    (τ := (n : ℝ) * max M 0) (B := max B 0) (K := max K 0) hα
    (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _))
    (le_max_right _ _) (le_max_right _ _)
  have hpoint (p : ℝ^n × ℝ) (hp : p ∈ W ×ˢ Ioo ℓ T) :
      p ∈ U ×ˢ Ioc 0 T := hHU (hWH hp)
  refine ⟨C, hC, ?_⟩
  intro u Dx Dt Dxx hu hDx hDt hDxx hux huxx hut hnonneg hsol
  have hpair := hcompare a d c (ha.mono fun p hp ↦ hpoint p hp)
    (fun p hp ↦ posSemidef_of_elliptic (hsymm p (hpoint p hp)) hα.le
      (hellpoint p (hpoint p hp)))
    (fun p hp ↦ hellpoint p (hpoint p hp))
    (fun p hp ↦ trace_le_dim_mul_of_norm_le
      ((hM _ (mem_image_of_mem _ (hWH hp))).trans (le_max_left M 0)))
    (fun p hp ↦ (hB _ (mem_image_of_mem _ (hWH hp))).trans (le_max_left B 0))
    (fun p hp ↦ (hK _ (mem_image_of_mem _ (hWH hp))).trans (le_max_left K 0))
    u Dx Dt Dxx (hu.mono hWC) (hDx.mono hWD) (hDt.mono hWD) (hDxx.mono hWD)
    (fun p hp ↦ hux p (hWD hp)) (fun p hp ↦ huxx p (hWD hp))
    (fun p hp ↦ hut p (hWD hp)) (fun p hp ↦ hnonneg p (hWC hp))
    (fun p hp ↦ hsol p (hWD hp))
  exact ⟨hpair, sSup_image_le_mul_sInf_image_of_pairwise hC
    (fun x hx y hy ↦ hpair x (subset_closure hx) y (subset_closure hy))⟩

end ParabolicHarnack
