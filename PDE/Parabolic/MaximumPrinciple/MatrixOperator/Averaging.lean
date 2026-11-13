/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Averaging.Approximation
public import PDE.Analysis.Calculus.SpaceTime.Averaging.Differentiation
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator.Jets
import CAS.ExactTactic

/-!
# Approximation of parabolic residuals by time averages

Uniform approximation of the value and its spatial and temporal derivatives
controls the matrix operator on compact sets. The coefficients need
only be bounded for this step. Averaging does not preserve the equation
exactly, and the conclusion records the resulting residual error.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open PDE.Analysis Filter MeasureTheory Set
open scoped Topology Interval

variable {n : ℕ}

/-- Time averages approximate the parabolic residual uniformly along windows in
a compact set. The only regularity used is the continuous C²,¹ derivative fields. -/
theorem exists_timeAverage_residual_sub_le
    {Ω : Set (ℝ^n)} {I : Set ℝ} {S : Set (ℝ^n × ℝ)}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (hS : IsCompact S) (hsub : S ⊆ Ω ×ˢ I)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {A B K : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (ha : ∀ p ∈ S, (∑ i : Fin n, ∑ j : Fin n, |a p.1 p.2 i j|) ≤ A)
    (hb : ∀ p ∈ S, ‖b p.1 p.2‖ ≤ B) (hc : ∀ p ∈ S, |c p.1 p.2| ≤ K)
    {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ} {Dt : ℝ^n × ℝ → ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    (hu : ContinuousOn (Function.uncurry u) (Ω ×ˢ I))
    (hDx : ContinuousOn Dx (Ω ×ˢ I)) (hDt : ContinuousOn Dt (Ω ×ˢ I))
    (hDxx : ContinuousOn Dxx (Ω ×ˢ I))
    (hd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ u y p.2) (Dx p) p.1)
    (hdd : ∀ p ∈ Ω ×ˢ I, HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1)
    (ht : ∀ p ∈ Ω ×ˢ I, HasDerivAt (u p.1) (Dt p) p.2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ p ∈ S,
      uIcc p.2 (p.2 + h) ⊆ I →
      (∀ s ∈ Icc (0 : ℝ) 1, (p.1, p.2 + h * s) ∈ S) →
      |matrixParabolicOperator a b c
          (fun x t ↦ ∫ s in (0 : ℝ)..1, u x (t + h * s)) p.1 p.2 -
        matrixParabolicOperator a b c u p.1 p.2| ≤ ε := by
  let η := ε / (1 + A + B + K)
  have hden : 0 < 1 + A + B + K := by positivity
  have hη : 0 < η := div_pos hε hden
  have hfactor (a b k z : ℝ) :
      z + (a * z + b * z + k * z) = (1 + a + b + k) * z := by cas
  obtain ⟨δu, hδu, hvalue⟩ :=
    exists_timeAverage_norm_sub_le (f := Function.uncurry u) hS (hu.mono hsub) hη
  obtain ⟨δx, hδx, hfirst⟩ :=
    exists_timeAverage_norm_sub_le (f := Dx) hS (hDx.mono hsub) hη
  obtain ⟨δxx, hδxx, hsecond⟩ :=
    exists_timeAverage_norm_sub_le (f := Dxx) hS (hDxx.mono hsub) hη
  obtain ⟨δt, hδt, htime⟩ :=
    exists_timeAverage_norm_sub_le (f := Dt) hS (hDt.mono hsub) hη
  refine ⟨min δu (min δx (min δxx δt)), by positivity, ?_⟩
  intro h hh hδ p hp hsegment hwindow
  have hpΩ := (hsub hp).1
  have hpI := (hsub hp).2
  have hwindowI (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      p.2 + h * s ∈ I := (hsub (hwindow s hs)).2
  have hdu : ∀ᶠ y in 𝓝 p.1,
      HasFDerivAt (fun z ↦ u z p.2) (Dx (y, p.2)) y := by
    filter_upwards [hΩ.mem_nhds hpΩ] with y hy
    exact hd (y, p.2) ⟨hy, hpI⟩
  have hdv : ∀ᶠ y in 𝓝 p.1,
      HasFDerivAt (fun z ↦ ∫ s in (0 : ℝ)..1, u z (p.2 + h * s))
        (∫ s in (0 : ℝ)..1, Dx (y, p.2 + h * s)) y := by
    filter_upwards [hΩ.mem_nhds hpΩ] with y hy
    exact hasFDerivAt_timeAverage_space hΩ hI hu hDx hd hy hwindowI
  have hddv := hasFDerivAt_timeAverage_space hΩ hI hDx hDxx hdd hpΩ hwindowI
  have htv := hasDerivAt_timeAverage_of_derivative
    (f := u p.1) (D := fun t ↦ Dt (p.1, t)) (t := p.2) (h := h) hI
    (hDt.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hs ↦ ⟨hpΩ, hs⟩))
    (fun t htI ↦ ht (p.1, t) ⟨hpΩ, htI⟩) hh.ne' hsegment
  obtain ⟨hδu', hδx', hδxx', hδt'⟩ : |h| < δu ∧ |h| < δx ∧ |h| < δxx ∧ |h| < δt := by
    simpa only [abs_of_pos hh, lt_min_iff] using hδ
  have hv := hvalue p hp h hδu' hwindow
  have hx := hfirst p hp h hδx' hwindow
  have hxx := hsecond p hp h hδxx' hwindow
  have hdt := htime p hp h hδt' hwindow
  have hres := abs_matrixParabolicOperator_sub_le_of_hasDerivAt a b c
    (u := fun x t ↦ ∫ s in (0 : ℝ)..1, u x (t + h * s)) (v := u)
    (Du := fun x ↦ ∫ s in (0 : ℝ)..1, Dx (x, p.2 + h * s))
    (Dv := fun x ↦ Dx (x, p.2))
    hdv hddv htv hdu (hdd p (hsub hp)) (ht p (hsub hp))
  apply hres.trans
  calc
    _ ≤ η + (A * η + B * η + K * η) := by
      gcongr
      · simpa only [Real.norm_eq_abs] using hdt
      · exact ha p hp
      · exact hb p hp
      · exact hc p hp
      · simpa only [Real.norm_eq_abs, Function.uncurry] using hv
    _ = ε := by
      rw [hfactor]
      dsimp only [η]
      exact mul_div_cancel₀ ε hden.ne'

end ParabolicMaximum
