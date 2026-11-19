/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Construction
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Connection
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Neighborhoods
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Orbits
public import PDE.Analysis.Convex.Function.Parameter

/-!
# Small profiles in one characteristic family

The smooth flux constructs the invariant graph and the scalar curvature.
Rankine–Hugoniot places both physical states on that graph. A nonzero jump
therefore has nonzero amplitude, and strict curvature determines exactly
which orientation admits a connection.

The physical radius is chosen before the right state and speed. It may be
decreased before choosing the state and speed neighborhoods, so finitely many
families can subsequently use one common physical range bound.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis PDE.Analysis.Evolution.Scalar

/-- For one genuinely nonlinear family, nearby Rankine–Hugoniot states admit
a small complete profile exactly in the compressive amplitude orientation.
The graph, scalar equation, and connecting orbit are constructed from the
flux; the speed neighborhood is an intermediate local conclusion. -/
theorem exists_profile_radius_iff_amplitude_sign {m : ℕ} (b : Module.Basis (Fin m) ℝ (ℝ^m))
    {flux : ℝ^m → ℝ^m} (hflux : ContDiff ℝ ∞ flux) (q : ℝ^m) (eig : Fin m → ℝ)
    (heig : Function.Injective eig) (k : Fin m) (hdiag : ∀ i, fderiv ℝ flux q (b i) = eig i • b i)
    {r : ℝ^m → ℝ^m} {a : ℝ^m → ℝ} (hr : DifferentiableAt ℝ r q) (ha : DifferentiableAt ℝ a q)
    (hrq : r q = b k) (haq : a q = eig k) (heigen : ∀ᶠ y in 𝓝 q, fderiv ℝ flux y (r y) = a y • r y)
    (hc : fderiv ℝ a q (b k) ≠ 0) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ δ η : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < η ∧
      ∀ uR ∈ ball q δ, uR ≠ q → ∀ μ ∈ ball 0 η, RankineHugoniot flux q uR (eig k + μ) →
        ((∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR (eig k + μ) v ∧ ∀ t, v t ∈ ball q ρ) ↔
        fderiv ℝ a q (b k) * b.equivFunL (uR - q) k < 0) := by
  obtain ⟨r₀, φ, hr₀, _hr₀R, hφ, hφ0, _hDφ, _hproj, hφproj, _hparameter,
      hinvariant, hcurvature, heq, horbit⟩ :=
    exists_local_profile_graph b hflux q eig heig k hdiag hr ha hrq haq
      heigen (show (0 : ℝ) < 1 by norm_num)
  let Q := reducedProfileField flux q b.equivFunL k φ
  let c := fderiv ℝ a q (b k)
  have hQ : ContDiff ℝ 2 Q :=
    contDiff_reducedProfileField (hflux.of_le (by simp)) q b.equivFunL k hφ
  have hshape : ∃ rconv : ℝ, 0 < rconv ∧ (0 < c → ∀ μ ∈ ball 0 rconv,
        StrictConvexOn ℝ (Ioo (-rconv) rconv) (fun s ↦ Q (s, μ))) ∧ (c < 0 → ∀ μ ∈ ball 0 rconv,
        StrictConcaveOn ℝ (Ioo (-rconv) rconv) (fun s ↦ Q (s, μ))) := by
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · obtain ⟨rconv, hrconv, hconc⟩ :=
        exists_uniform_strictConcaveOn_of_iteratedDeriv_neg hQ.contDiffAt (hcurvature.trans_lt hneg)
      exact ⟨rconv, hrconv, fun hpos ↦ (not_lt_of_ge hneg.le hpos).elim, fun _ ↦ hconc⟩
    · obtain ⟨rconv, hrconv, hconv⟩ :=
        exists_uniform_strictConvexOn_of_iteratedDeriv_pos hQ.contDiffAt (hcurvature.symm ▸ hpos)
      exact ⟨rconv, hrconv, fun _ ↦ hconv, fun hneg ↦ (not_lt_of_ge hpos.le hneg).elim⟩
  obtain ⟨rconv, hrconv, hconv, hconc⟩ := hshape
  obtain ⟨ρ₀, hρ₀, hneighborhoods⟩ :=
    exists_profileGraph_neighborhoods q b.equivFunL k hφ.continuous hφ0 hr₀ hrconv
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρmax ↦ ?_⟩
  obtain ⟨δ, η, τ, hδ, hδρ, hη, hτ, hτconv, hητ,
      hphysical, hgraph, hamplitude⟩ := hneighborhoods ρ hρ hρmax
  refine ⟨δ, η, hδ, hδρ, hη, fun uR huR hne μ hμ hRH ↦ ?_⟩
  let A := b.equivFunL (uR - q) k
  let I := Ioo (-τ) τ
  have hzero : (0 : ℝ) ∈ I := ⟨neg_neg_of_pos hτ, hτ⟩
  have hAI : A ∈ I := hamplitude uR huR
  have hμconv : μ ∈ ball 0 rconv := ball_subset_ball (hητ.trans hτconv.le) hμ
  have hends (u : ℝ^m) (hu : u ∈ ball q ρ) (hRu : RankineHugoniot flux q u (eig k + μ)) :
      profileGraph q b.equivFunL k φ (b.equivFunL (u - q) k, μ) = u ∧
        Q (b.equivFunL (u - q) k, μ) = 0 := by
    have hequilibrium :=
      augmentedProfile_equilibrium_of_rankine_hugoniot b flux q eig k hdiag u μ hRu
    exact profileGraph_eq_and_reducedProfileField_eq_zero_of_equilibrium
      b flux q eig heig k hφproj u μ (heq _ (hphysical u hu μ hμ) hequilibrium) hequilibrium
  have hleft : profileGraph q b.equivFunL k φ (0, μ) = q ∧ Q (0, μ) = 0 := by
    simpa only [sub_self, map_zero, Pi.zero_apply] using
      hends q (mem_ball_self hρ) (by simp [RankineHugoniot])
  have hright : profileGraph q b.equivFunL k φ (A, μ) = uR ∧ Q (A, μ) = 0 :=
    hends uR (ball_subset_ball hδρ.le huR) hRH
  have hA : A ≠ 0 := fun he ↦ hne (by rw [← hright.1, he, hleft.1])
  have hconvI (hpos : 0 < c) : StrictConvexOn ℝ I (fun s ↦ Q (s, μ)) := (hconv hpos μ hμconv).subset
      (Ioo_subset_Ioo (neg_le_neg hτconv.le) hτconv.le) (convex_Ioo _ _)
  have hconcI (hneg : c < 0) : StrictConcaveOn ℝ I (fun s ↦ Q (s, μ)) :=
    (hconc hneg μ hμconv).subset (Ioo_subset_Ioo (neg_le_neg hτconv.le) hτconv.le) (convex_Ioo _ _)
  constructor
  · rintro ⟨v, hv, hvsmall⟩
    obtain ⟨_hsame, hode, hlimleft, hlimright⟩ :=
      hv.scalar_reduction (hflux.differentiable (by simp)) b q uR eig heig k hdiag
        hφproj horbit (fun t ↦ hphysical (v t) (hvsmall t) μ hμ)
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have hApos := lt_of_heteroclinic_of_strictConcaveOn
        (hconcI hneg) hzero hAI hleft.2 hright.2 hA.symm hode hlimleft hlimright
      exact mul_neg_of_neg_of_pos hneg hApos
    · have hAneg := lt_of_heteroclinic_of_strictConvexOn
        (hconvI hpos) hzero hAI hleft.2 hright.2 hA.symm hode hlimleft hlimright
      exact mul_neg_of_pos_of_neg hpos hAneg
  · intro hsign
    have hC1 : ContDiffOn ℝ 1 (fun s ↦ Q (s, μ)) I :=
      ((hQ.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)).contDiffOn
    have hinv (s : ℝ) (hs : s ∈ I) :
        fderiv ℝ (profileGraph q b.equivFunL k φ) (s, μ) (Q (s, μ), 0) =
          flux (profileGraph q b.equivFunL k φ (s, μ)) - flux q -
            (eig k + μ) • (profileGraph q b.equivFunL k φ (s, μ) - q) :=
      hinvariant (s, μ) (hgraph s hs μ hμ).1
    have hrange (s : ℝ) (hs : s ∈ I) : profileGraph q b.equivFunL k φ (s, μ) ∈ ball q ρ :=
      (hgraph s hs μ hμ).2
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · have hApos : 0 < A := ((mul_neg_iff.mp hsign).resolve_left fun h ↦ lt_asymm hneg h.1).2
      exact exists_viscousProfile_of_strictConcaveOn_reducedField
        (hflux.differentiable (by simp)) q uR b.equivFunL k hφ (eig k + μ) μ A
        (hconcI hneg) hC1 hzero hAI hleft.2 hright.2 hApos hinv hleft.1 hright.1 hRH hrange
    · have hAneg : A < 0 := ((mul_neg_iff.mp hsign).resolve_right fun h ↦ lt_asymm hpos h.1).2
      exact exists_viscousProfile_of_strictConvexOn_reducedField
        (hflux.differentiable (by simp)) q uR b.equivFunL k hφ (eig k + μ) μ A
        (hconvI hpos) hC1 hzero hAI hleft.2 hright.2 hAneg hinv hleft.1 hright.1 hRH hrange

end PDE.Hyperbolic.ConservationLaw.System
