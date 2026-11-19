/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Quantitative
public import PDE.Analysis.Calculus.LocalExtension.Tube.DerivativeVariation
public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Neutral.Preservation

import CAS.ExactTactic

/-!
# Compact neutral corrections of a flux

The supplied chart and compact bilinear family determine a logarithmic
cutoff extension. Fixed pilot bounds and the compact neutral-family tolerance
are chosen before its radius and logarithmic width. The resulting correction
preserves the full curve jet, is arbitrarily small in value and first derivative,
and preserves strict hyperbolicity and every genuinely nonlinear family globally.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis

/-- Realize a compact symmetric, tangent-annihilating neutral Hessian family by
a smooth correction supported in the supplied isolating open set.

The complete supplied curve retains zero value and first derivative and the
prescribed full Hessian. Both lower-order norms are uniformly smaller than `η`.
The prescribed Hessian may be large: the characteristic argument uses its neutral cutoff multiples
and controls only the remaining jet error. -/
theorem exists_actual_neutral_tube_correction {m : ℕ} (f : ℝ^m → ℝ^m) (hf : ContDiff ℝ 3 f)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt f x) (hgn : ∀ i, IsGenuinelyNonlinearFamily f i)
    (ell : ℝ^m →L[ℝ] ℝ) (e : OpenPartialHomeomorph (ℝ × ell.ker) (ℝ^m)) (γ : ℝ → ℝ^m) (J : Set ℝ)
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : ℝ^m)) e.source) (hγtarget : MapsTo γ J e.target)
    (htmap : MapsTo (fun x : ℝ^m ↦ (e.symm x).1) e.target J)
    (ht : ContDiffOn ℝ ∞ (fun x : ℝ^m ↦ (e.symm x).1) e.target)
    (hz : ContDiffOn ℝ ∞ (fun x : ℝ^m ↦ ((e.symm x).2 : ℝ^m)) e.target)
    (hcoord : ∀ s ∈ J, e.symm (γ s) = (s, (0 : ell.ker)))
    (hmod : ∀ s ∈ J, ∀ v : ℝ^m, fderiv ℝ (fun x : ℝ^m ↦ ((e.symm x).2 : ℝ^m)) (γ s) v - v ∈
      Submodule.span ℝ ({deriv γ s} : Set (ℝ^m)))
    (B : ℝ → ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ^m) (hB : ContDiff ℝ ∞ B) (hBcompact : HasCompactSupport B)
    (hBsupport : tsupport B ⊆ J) (hsym : ∀ s ∈ J, ∀ v w, B s v w = B s w v)
    (hker : ∀ s ∈ J, ∀ v, B s (deriv γ s) v = 0) (hγ : ContinuousOn γ (tsupport B))
    (hneutral : ∀ t ∈ tsupport B, ∃ (b : Module.Basis (Fin m) ℝ (ℝ^m)) (eig : Fin m → ℝ), StrictMono
      eig ∧ (∀ i, fderiv ℝ f (γ t) (b i) = eig i • b i) ∧ ∀ i, b.repr (B t (b i) (b i)) i = 0)
    (q : ℝ → ℝ^m) (hq : EqOn q γ J) (U : Set (ℝ^m)) (hU : IsOpen U)
    (hsupportU : γ '' tsupport B ⊆ U) (hisolate : q ⁻¹' U ⊆ J) (η : ℝ) (hη : 0 < η) :
    ∃ P : ℝ^m → ℝ^m, ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      tsupport P ⊆ U ∧
      (∀ s : ℝ, P (q s) = 0 ∧ fderiv ℝ P (q s) = 0 ∧
        fderiv ℝ (fderiv ℝ P) (q s) = B s) ∧
      (∀ x : ℝ^m, ‖P x‖ < η ∧ ‖fderiv ℝ P x‖ < η) ∧
      (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
        ∀ i, IsGenuinelyNonlinearFamily (f + P) i := by
  classical
  obtain ⟨ρ, Cp, hρ, hCp, hpilot, hbuild⟩ :=
    exists_quantitative_logarithmic_tube_extension ell e γ J he hγtarget htmap ht hz
      hcoord hmod B hB hBcompact hBsupport hsym hker q hq U hU hsupportU hisolate
  have hsource : tsupport B ×ˢ closedBall (0 : ell.ker) ρ ⊆ e.source := fun _ hp ↦ (hpilot hp).1
  obtain ⟨Cf, hCf, hvariation⟩ := exists_pos_compact_tube_derivative_variation_bounds (f := f)
      hBcompact.isCompact (isCompact_closedBall (0 : ell.ker) ρ) hρ he hsource
      (fun _ _ ↦ hf.contDiffAt)
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by decide)
  obtain ⟨ε, hε, hpreserve⟩ := exists_pos_tolerance_for_neutral_flux_corrections
    hf₂ hhyper hgn hBcompact.isCompact hγ hB.continuous.continuousOn hneutral
  -- The neutral-family tolerance and both pilot constants precede the cutoff choices.
  obtain ⟨l, _, hl⟩ := exists_pos_lt_mul (half_pos hε) Cp
  let L : ℝ := max 1 l
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hwidth : Cp / L < ε / 2 := (div_lt_iff₀ hLpos).2 (by linarith
    [(mul_le_mul_of_nonneg_right (le_max_right 1 l) (half_pos hε).le : l * (ε / 2) ≤ L * (ε / 2))])
  obtain ⟨d, hd, hsmall⟩ := exists_pos_mul_lt (lt_min hη (half_pos hε)) (Cf + Cp)
  obtain ⟨δ, hδ, hδsmall⟩ := exists_between (lt_min hρ (lt_min zero_lt_one hd))
  have hδρ : δ < ρ := hδsmall.trans_le (min_le_left _ _)
  have hδone : δ ≤ 1 := (hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδd : δ ≤ d := (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hsum : (Cf + Cp) * δ < min η (ε / 2) :=
    (mul_le_mul_of_nonneg_left hδd (add_pos hCf hCp).le).trans_lt hsmall
  have hradius : (Cf + Cp) * δ < ε / 2 := hsum.trans_le (min_le_right _ _)
  have hCpsmall : Cp * δ < η :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCf.le) hδ.le).trans_lt
      (hsum.trans_le (min_le_left _ _))
  have herrors : (Cf + Cp) * δ + Cp / L < ε := by linarith [add_lt_add hradius hwidth]
  let t : ℝ^m → ℝ := fun x ↦ (e.symm x).1
  let z : ℝ^m → ℝ^m := fun x ↦ ((e.symm x).2 : ℝ^m)
  let Q : ℝ^m → ℝ^m := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
  let P : ℝ^m → ℝ^m := (e.target ∩ U).indicator (fun x ↦ radialLogarithmicCutoff δ L (z x) • Q x)
  let θ : ℝ^m → ℝ := fun x ↦ radialLogarithmicCutoff δ L (z x)
  obtain ⟨hP, hPcompact, hPK, hPΩ, hjet, hbounds⟩ := hbuild δ L hδ hδρ hδone hL
  have hP₂ : ContDiff ℝ 2 P := hP.of_le (by simp)
  have htime : MapsTo t (tsupport P) (tsupport B) := fun x hx ↦ ((hbounds x).2.2 hx).1
  obtain ⟨_, _, hradial⟩ := exists_pos_radialLogarithmicCutoff_bounds (E := ℝ^m)
  have hθ : MapsTo θ (tsupport P) (Icc (0 : ℝ) 1) := fun x _ ↦ (hradial δ L hδ hL).2.2.2.1 (z x)
  have hDadd (x : ℝ^m) : fderiv ℝ (f + P) x = fderiv ℝ f x + fderiv ℝ P x :=
    fderiv_add (hf₂.differentiable two_ne_zero x) (hP₂.differentiable two_ne_zero x)
  have hHadd (x : ℝ^m) : fderiv ℝ (fderiv ℝ (f + P)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ P) x := by
    rw [show fderiv ℝ (f + P) = (fun y ↦ fderiv ℝ f y + fderiv ℝ P y) from funext hDadd]
    exact fderiv_fun_add ((hf₂.fderiv_right le_rfl).differentiable one_ne_zero x)
      ((hP₂.fderiv_right le_rfl).differentiable one_ne_zero x)
  have hfirst (x : ℝ^m) (hx : x ∈ tsupport P) :
      ‖fderiv ℝ (f + P) x - fderiv ℝ f (γ (t x))‖ < ε := by
    have hfbound := (hvariation δ hδρ.le x (hPK hx)).1
    calc
      ‖fderiv ℝ (f + P) x - fderiv ℝ f (γ (t x))‖ =
          ‖(fderiv ℝ f x - fderiv ℝ f (γ (t x))) + fderiv ℝ P x‖ := by
        rw [hDadd]
        congr 1
        abel
      _ ≤ ‖fderiv ℝ f x - fderiv ℝ f (γ (t x))‖ + ‖fderiv ℝ P x‖ := norm_add_le _ _
      _ ≤ Cf * δ + Cp * δ := add_le_add hfbound (hbounds x).2.1
      _ = (Cf + Cp) * δ := by ring
      _ < ε := hradius.trans (half_lt_self hε)
  have hsecond (x : ℝ^m) (hx : x ∈ tsupport P) : ‖fderiv ℝ (fderiv ℝ (f + P)) x -
        (fderiv ℝ (fderiv ℝ f) (γ (t x)) + θ x • B (t x))‖ < ε := by
    have hfbound := (hvariation δ hδρ.le x (hPK hx)).2
    have hPbound := ((hbounds x).2.2 hx).2
    calc
      ‖fderiv ℝ (fderiv ℝ (f + P)) x - (fderiv ℝ (fderiv ℝ f) (γ (t x)) + θ x • B (t x))‖ =
          ‖(fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) (γ (t x))) +
            (fderiv ℝ (fderiv ℝ P) x - θ x • B (t x))‖ := by
        rw [hHadd]
        congr 1
        abel
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) x - fderiv ℝ (fderiv ℝ f) (γ (t x))‖ +
          ‖fderiv ℝ (fderiv ℝ P) x - θ x • B (t x)‖ := @norm_add_le (ℝ^m →L[ℝ] ℝ^m →L[ℝ] ℝ^m)
          (ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
            (σ₁₂ := RingHom.id ℝ) (E := ℝ^m) (F := ℝ^m →L[ℝ] ℝ^m)).toSeminormedAddGroup _ _
      _ ≤ Cf * δ + (Cp * δ + Cp / L) := add_le_add hfbound hPbound
      _ = (Cf + Cp) * δ + Cp / L := by ring
      _ < ε := herrors
  obtain ⟨hcorrectedHyper, hcorrectedGN⟩ := hpreserve P hP₂ t θ htime hθ hfirst hsecond
  refine ⟨P, hP, hPcompact, (fun _ hx ↦ (hPΩ hx).2), hjet, fun x ↦ ⟨((hbounds x).1.trans
    (mul_le_mul_of_nonneg_left (pow_le_of_le_one hδ.le hδone two_ne_zero) hCp.le)).trans_lt
      hCpsmall, (hbounds x).2.1.trans_lt hCpsmall⟩, hcorrectedHyper, hcorrectedGN⟩

end PDE.Hyperbolic.ConservationLaw.System
