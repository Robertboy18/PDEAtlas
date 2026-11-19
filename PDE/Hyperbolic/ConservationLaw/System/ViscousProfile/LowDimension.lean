/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ExtremalLax
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Existence

/-!
# Small-jump viscous profiles in one or two state dimensions

Every characteristic family is extreme in these dimensions. The strict branch
orientation and the global tail obstruction therefore give necessity for every
complete profile, without restricting its range. The local construction
supplies the converse. Both directions use one radius fixed before the right state,
wave speed and profile.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

open Filter Metric Set
open scoped ContDiff Topology

/-- In at most two state dimensions, every complete viscous profile with a sufficiently
small nonzero jump satisfies strict Lax for some characteristic family. The radius
depends only on the flux and the fixed left state. -/
theorem exists_radius_lax_of_viscousProfile_of_dimension_le_two {m : ℕ} (hm₂ : m ≤ 2)
    {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ ∞ flux) (hhyper : ∀ u, IsStrictlyHyperbolicAt flux u)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) (q : ℝ^m) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ uR ∈ ball q δ, uR ≠ q → ∀ speed : ℝ, ∀ v : ℝ → ℝ^m, IsViscousProfile flux q uR speed v →
        ∃ k, characteristicSpeed flux k uR < speed ∧
      speed < characteristicSpeed flux k q := by
  classical
  cases m with
  | zero => exact ⟨1, one_pos, fun uR _ hne ↦ (hne (Subsingleton.elim uR q)).elim⟩
  | succ m =>
    obtain ⟨b, S, σ, I₀, V₀, C, _hC, hdiag, hI₀, hzero₀, hV₀, hqV₀, _hVU, hcurves, hclass₀⟩ :=
      exists_local_shock_curves_with_quadratic_speed (n := 2)
        (by norm_num) isOpen_univ (mem_univ q)
        (hflux.of_le (by simp)).contDiffOn (hhyper q)
    have hextreme (k : Fin (m + 1)) : k = 0 ∨ k = Fin.last m := by
      by_cases hk : k = 0
      · exact Or.inl hk
      · right
        apply Fin.ext
        have hkzero : k.val ≠ 0 := fun h ↦ hk (Fin.ext h)
        have hklt := k.isLt
        change k.val = m
        omega
    have hsign (k : Fin (m + 1)) : ∀ᶠ s in 𝓝 0, ∀ v : ℝ → ℝ^(m + 1), S k s ≠ q →
          IsViscousProfile flux q (S k s) (σ k s) v → characteristicSpeed flux k (S k s) < σ k s ∧
              σ k s < characteristicSpeed flux k q :=
      eventually_lax_of_viscousProfile_extremal (hflux.of_le (by simp)) hhyper (hgn k)
        ⟨Module.End.mem_eigenspace_iff.mpr (hdiag k), b.ne_zero k⟩
        (hcurves k).1 (hcurves k).2.1 (hcurves k).2.2.2.2.1 (hcurves k).2.2.2.2.2.1 (hextreme k)
    obtain ⟨I, hIsub, hI, hzero⟩ := _root_.mem_nhds_iff.mp
      (Filter.inter_mem (hI₀.mem_nhds hzero₀) (eventually_all.mpr hsign))
    obtain ⟨V, hV, hqV, _hVV, hclass⟩ :=
      exists_shock_classification_on_parameter_neighborhood b hI hzero
        (fun s hs ↦ (hIsub hs).1) hV₀ hqV₀
        (fun k s hs ↦ ((hcurves k).2.2.2.2.2.2 s hs).2.2.1) hclass₀
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hqV)
    refine ⟨δ, hδ, fun uR huR hne speed v hv ↦ ?_⟩
    obtain ⟨k, s, hs, _hsne, hstate, hspeed⟩ := (hclass uR (hδsub huR) speed hne).mp
        (hv.rankineHugoniot (hflux.differentiable (by simp)))
    refine ⟨k, ?_⟩
    subst uR speed
    exact ((hIsub hs).2 k) v hne hv

/-- In at most two state dimensions, a small nonzero jump has a complete viscous
profile exactly when it satisfies Rankine–Hugoniot and strict Lax. The existence
statement has no whole-profile confinement hypothesis. -/
theorem exists_radius_viscousProfile_iff_lax_of_dimension_le_two {m : ℕ} (hm₂ : m ≤ 2)
    {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ ∞ flux) (hhyper : ∀ u, IsStrictlyHyperbolicAt flux u)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily flux k) (q : ℝ^m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ uR ∈ ball q δ, uR ≠ q → ∀ speed : ℝ,
      ((∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR speed v) ↔
        RankineHugoniot flux q uR speed ∧
          ∃ k, characteristicSpeed flux k uR < speed ∧
            speed < characteristicSpeed flux k q) := by
  obtain ⟨δ₁, hδ₁, hnecessity⟩ :=
    exists_radius_lax_of_viscousProfile_of_dimension_le_two hm₂ hflux hhyper hgn q
  obtain ⟨δ₀, ρ, hδ₀, _hδρ, hlocal⟩ := exists_small_viscousProfile_iff_lax hflux hhyper hgn q
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun uR huR hne speed ↦ ?_⟩
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨hv.rankineHugoniot (hflux.differentiable (by simp)),
      hnecessity uR (ball_subset_ball (min_le_right _ _) huR) hne speed v hv⟩
  · intro h
    obtain ⟨v, hv, _hrange⟩ := (hlocal uR (ball_subset_ball (min_le_left _ _) huR) hne speed).mpr h
    exact ⟨v, hv⟩

end PDE.Hyperbolic.ConservationLaw.System
