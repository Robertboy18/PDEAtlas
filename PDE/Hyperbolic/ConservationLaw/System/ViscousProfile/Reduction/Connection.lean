/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Lifting
public import PDE.Analysis.Evolution.ODE.Autonomous.Scalar.ConvexConnection

/-!
# Constructing profiles between two graph equilibria

Strict curvature fixes the sign of the scalar field between its two
zeros. The scalar connection theorem constructs an orbit through an interior
point; lifting gives a physical viscous profile. A prescribed graph range is
inherited by this constructed orbit.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.Evolution.Scalar

/-- Negative amplitude and strict convexity construct a decreasing connection
on the graph, with all physical profile conditions and the prescribed range. -/
theorem exists_viscousProfile_of_strictConvexOn_reducedField {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : Differentiable ℝ flux) (q uR : ℝ^m) (e : ℝ^m ≃L[ℝ] (Fin m → ℝ)) (k : Fin m)
    {φ : (Option (Fin m) → ℝ) → (Option (Fin m) → ℝ)} (hφ : ContDiff ℝ 2 φ) (speed μ a : ℝ)
    {I : Set ℝ} {V : Set (ℝ^m)}
    (hconv : StrictConvexOn ℝ I (fun s ↦ reducedProfileField flux q e k φ (s, μ)))
    (hC1 : ContDiffOn ℝ 1 (fun s ↦ reducedProfileField flux q e k φ (s, μ)) I) (hzero : (0 : ℝ) ∈ I)
    (haI : a ∈ I) (hroot0 : reducedProfileField flux q e k φ (0, μ) = 0)
    (hroota : reducedProfileField flux q e k φ (a, μ) = 0) (ha : a < 0)
    (hinvariant : ∀ s ∈ I, fderiv ℝ (profileGraph q e k φ) (s, μ)
      (reducedProfileField flux q e k φ (s, μ), 0) =
      flux (profileGraph q e k φ (s, μ)) - flux q - speed • (profileGraph q e k φ (s, μ) - q))
    (hend0 : profileGraph q e k φ (0, μ) = q) (henda : profileGraph q e k φ (a, μ) = uR)
    (hRH : RankineHugoniot flux q uR speed) (hrange : ∀ s ∈ I, profileGraph q e k φ (s, μ) ∈ V) :
    ∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR speed v ∧ ∀ t, v t ∈ V := by
  obtain ⟨x₀, hx₀⟩ := nonempty_Ioo.mpr ha
  obtain ⟨x, _hx0, hx, hode, hxI, _hmono, hleft, hright, _hdleft, _hdright⟩ :=
    exists_heteroclinic_of_strictConvexOn hconv hC1 hzero haI hroot0 hroota hx₀
  have hmem (t : ℝ) : x t ∈ I := hconv.1.ordConnected.out haI hzero ⟨(hxI t).1.le, (hxI t).2.le⟩
  refine ⟨fun t ↦ profileGraph q e k φ (x t, μ), ?_, fun t ↦ hrange _ (hmem t)⟩
  exact isViscousProfile_profileGraph_of_scalar hflux q uR e k hφ speed μ 0 a I
    hinvariant hend0 henda hRH hx hmem hode hleft hright

/-- Positive amplitude and strict concavity construct the increasing connection,
with the same physical equation and four end conditions. -/
theorem exists_viscousProfile_of_strictConcaveOn_reducedField {m : ℕ} {flux : ℝ^m → ℝ^m}
    (hflux : Differentiable ℝ flux) (q uR : ℝ^m) (e : ℝ^m ≃L[ℝ] (Fin m → ℝ)) (k : Fin m)
    {φ : (Option (Fin m) → ℝ) → (Option (Fin m) → ℝ)} (hφ : ContDiff ℝ 2 φ) (speed μ a : ℝ)
    {I : Set ℝ} {V : Set (ℝ^m)}
    (hconc : StrictConcaveOn ℝ I (fun s ↦ reducedProfileField flux q e k φ (s, μ)))
    (hC1 : ContDiffOn ℝ 1 (fun s ↦ reducedProfileField flux q e k φ (s, μ)) I) (hzero : (0 : ℝ) ∈ I)
    (haI : a ∈ I) (hroot0 : reducedProfileField flux q e k φ (0, μ) = 0)
    (hroota : reducedProfileField flux q e k φ (a, μ) = 0) (ha : 0 < a)
    (hinvariant : ∀ s ∈ I, fderiv ℝ (profileGraph q e k φ) (s, μ)
      (reducedProfileField flux q e k φ (s, μ), 0) =
      flux (profileGraph q e k φ (s, μ)) - flux q - speed • (profileGraph q e k φ (s, μ) - q))
    (hend0 : profileGraph q e k φ (0, μ) = q) (henda : profileGraph q e k φ (a, μ) = uR)
    (hRH : RankineHugoniot flux q uR speed) (hrange : ∀ s ∈ I, profileGraph q e k φ (s, μ) ∈ V) :
    ∃ v : ℝ → ℝ^m, IsViscousProfile flux q uR speed v ∧ ∀ t, v t ∈ V := by
  obtain ⟨x₀, hx₀⟩ := nonempty_Ioo.mpr ha
  obtain ⟨x, _hx0, hx, hode, hxI, _hmono, hleft, hright, _hdleft, _hdright⟩ :=
    exists_heteroclinic_of_strictConcaveOn hconc hC1 hzero haI hroot0 hroota hx₀
  have hmem (t : ℝ) : x t ∈ I := hconc.1.ordConnected.out hzero haI ⟨(hxI t).1.le, (hxI t).2.le⟩
  refine ⟨fun t ↦ profileGraph q e k φ (x t, μ), ?_, fun t ↦ hrange _ (hmem t)⟩
  exact isViscousProfile_profileGraph_of_scalar hflux q uR e k hφ speed μ 0 a I
    hinvariant hend0 henda hRH hx hmem hode hleft hright

end PDE.Hyperbolic.ConservationLaw.System
