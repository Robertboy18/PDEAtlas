/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.SelectedFamily
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.TerminalGerm

import CAS.ExactTactic

/-!
# A full terminal germ for the selected clock moments

The passage gap selects one signed gate and its matching coefficient.
The selected coupled family then supplies a full terminal germ on the same
closed time slab. A common smaller product retains the original candidates and
terminal times, together with the invertible coefficient derivative of the candidate
residual.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The selected clock moments extend to a full terminal germ while retaining
one gate, coefficient, and closed time slab. On a common zero-delta product,
the full trajectories and terminal times agree with the original candidates.
The candidate terminal residual has its selected zero and invertible coefficient
derivative, expressed using those same candidate terminal coordinates. -/
theorem exists_prescribed_clock_selected_full_terminal {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {L Bhit : ℝ × ℝ → ℝ} {N : Set (ℝ × ℝ)} {A B rUp rDown τ0 Hmax : ℝ} (hF : ContDiff ℝ ∞ F)
    (hN : IsOpen N) (hbase : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (hLbase : L (0, 0) = τ0) (hrDown : 0 ≤ rDown) (hrτ : rDown < τ0) (hHmax : τ0 < Hmax)
    (hHslab : Hmax < τ0 + 1) (hAB : A ^ 2 < B ^ 2) (hB : 0 ≤ B) (hmargin : B < (F (τ0, (0, 0))).2)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ N, F (0, p) = (p.2, 1))
    (hearly : ∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) rUp, (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧
      (F (t, p)).2 ^ 2 < A ^ 2)
    (hmiddle : ∀ p ∈ N, ∀ t ∈ Icc rUp rDown, (205 : ℝ) < (F (t, p)).1)
    (hlate : ∀ p ∈ N, ∀ t ∈ Icc rDown Hmax, (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 <
      (F (t, p)).2 ^ 2)
    (hlocalize : ∀ b : ℝ → ℝ, Continuous b → tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10) → ∀ p ∈ N,
      (∫ t in (0 : ℝ)..L p, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) =
      prescribedClockWeightMoment b L Bhit p)
    (hgap : ∀ y ∈ Ioo (205 : ℝ) (2051 / 10), (8 / 5 : ℝ) ≤ (parameterizedClockPassageData L Bhit
      (0, 0)).tMinus y - (parameterizedClockPassageData L Bhit (0, 0)).tPlus y)
    (hBmem : Bhit (0, 0) ∈ Icc (0 : ℝ) (τ0 + 1)) (hLlevel : ∀ p ∈ N, (F (L p, p)).1 = 0)
    (hBlevel : ∀ p ∈ N, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) (L (0, 0)))
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (MiddleClock.g 205 + 1) (Bhit (0, 0))) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let W : ℝ → Fin 3 → ℝ := fun y ↦ ![1, D0.R y, D0.Q y]
    let z : ℝ × ℝ → ℝ := fun p ↦ (F (L p, p)).2
    let v : Fin 3 → ℝ := ![1, 0,
      -(2 * deriv (fun μ ↦ z (μ, 0)) 0 +
        2000000 * deriv (fun a ↦ z (0, a)) 0) / z (0, 0)]
    ∃ (β : Fin 3 → ℝ → ℝ) (cStar : Fin 3 → ℝ)
      (H : ℝ) (U : Set (ℝ × ℝ)) (V : Set (Fin 3 → ℝ)),
      let b : (Fin 3 → ℝ) × ℝ → ℝ := fun w ↦
        (Ioo (205 : ℝ) (2051 / 10)).indicator
          (fun y ↦ (∑ j, w.1 j * β j y) / D0.wMinus y) w.2
      let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
        !₂[(F (t, p)).2 * scalarLinearSolution (fun _ : ℝ ↦ 4)
            (fun s ↦ b (c, (F (s, p)).1)) 0 0 t,
          (F (t, p)).1, (F (t, p)).2]
      let x0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ q u.2 u.1 (L u.2) 0
      let z0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ q u.2 u.1 (L u.2) 2
      let ρ0 : (Fin 3 → ℝ) × (ℝ × ℝ) → ℝ := fun u ↦ x0 u / z0 u
      let M := bumpMomentMatrix W β
      let d := deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0
      let A_G : Matrix (Fin 3) (Fin 3) ℝ :=
        !![1, 1, 0; 0, -4 * d, 0; 0, 0, z (0, 0)]
      let Gold : (Fin 3 → ℝ) → Fin 3 → ℝ := fun c ↦
        ![ρ0 (c, (0, 0)) - 1,
          deriv (fun a : ℝ ↦ ρ0 (c, (0, a))) 0,
          z0 (c, (0, 0)) * deriv (fun μ : ℝ ↦ ρ0 (c, (μ, 0))) 0 +
            2 * deriv (fun μ : ℝ ↦ z0 (c, (μ, 0))) 0 +
            2000000 * deriv (fun a : ℝ ↦ z0 (c, (0, a))) 0]
      let J := (Matrix.toLin' (A_G * M)).toContinuousLinearMap
      (∀ j, ContDiff ℝ ∞ (β j) ∧ HasCompactSupport (β j) ∧
        tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) ∧
        (∀ t, 0 ≤ β j t) ∧ (∫ t, β j t) = 1 ∧
        ∀ i, Integrable (fun t ↦ β j t * W t i)) ∧
      Pairwise (fun j k ↦ Disjoint (tsupport (β j)) (tsupport (β k))) ∧
      M.det ≠ 0 ∧ M *ᵥ cStar = v ∧ ContDiff ℝ ∞ b ∧
      (∀ c, HasCompactSupport (fun y ↦ b (c, y)) ∧
        tsupport (fun y ↦ b (c, y)) ⊆ ⋃ j, tsupport (β j) ∧
        tsupport (fun y ↦ b (c, y)) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100)) ∧
      H ∈ Ioo τ0 Hmax ∧ IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧
      IsOpen V ∧ cStar ∈ V ∧ (∀ p ∈ U, 0 < z p) ∧
      (∀ p ∈ U, L p ∈ Ioo rDown H ∧ ∀ c ∈ V,
        (∀ t ∈ Icc (0 : ℝ) H,
          HasDerivAt (q p c)
            (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B)
              (fun y ↦ b (c, y)) (q p c t) - p.1 • q p c t) t) ∧
        ρ0 (c, p) = prescribedClockWeightMoment (fun y ↦ b (c, y)) L Bhit p) ∧
      HasFDerivAt Gold J cStar ∧ IsUnit J ∧ Gold cStar = 0 ∧
      ∃ (Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3)
        (T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ)
        (Nfull : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)))
        (U0 : Set (ℝ × ℝ)) (V0 : Set (Fin 3 → ℝ)),
        IsOpen Nfull ∧ ((0, cStar), (0, 0)) ∈ Nfull ∧ ContDiff ℝ ∞ Ψ ∧
        (∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3)) ∧
        (∀ θ ∈ Nfull, ∀ t ∈ Icc (0 : ℝ) H,
          HasDerivAt (fun s ↦ Ψ (s, θ))
            (concreteGatedFlux θ.1.1 (clockFeedback A B)
              (fun y ↦ b (θ.1.2, y)) (Ψ (t, θ)) - θ.2.1 • Ψ (t, θ)) t) ∧
        ContDiffOn ℝ ∞ T Nfull ∧ T ((0, cStar), (0, 0)) = τ0 ∧
        (∀ θ ∈ Nfull, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) ∧
        (∀ᶠ w in 𝓝 (((0, cStar), (0, 0)), τ0),
          Ψ (w.2, w.1) 1 = 0 ↔ T w.1 = w.2) ∧
        IsOpen U0 ∧ (0, 0) ∈ U0 ∧ U0 ⊆ U ∧
        IsOpen V0 ∧ cStar ∈ V0 ∧ V0 ⊆ V ∧
        ∀ p ∈ U0, ∀ c ∈ V0,
          ((0, c), p) ∈ Nfull ∧ T ((0, c), p) = L p ∧
          EqOn (fun t ↦ Ψ (t, ((0, c), p))) (q p c) (Icc (0 : ℝ) H) ∧
          Ψ (T ((0, c), p), ((0, c), p)) = q p c (L p) := by
  intro D0 W z v
  obtain ⟨β, cStar, H, U, V, hβ, hdisjoint, hdet, hselected, hb, hbsupport,
    hH, hU, h0U, hUN, hV, hcV, hzpos, hfamily, hderiv, hunit, hzero⟩ :=
    exists_prescribed_clock_selected_moment_family
      hF hN hbase hL hBhit hLbase hrDown hrτ hHmax hHslab hAB hB hmargin
      hode hinitial hearly hmiddle hlate hlocalize hgap hBmem hLlevel hBlevel hLtime hBtime
  refine ⟨β, cStar, H, U, V, ?_⟩
  intro b q x0 z0 ρ0 M d A_G Gold J
  -- The candidate fast coordinate is independent of the selected coefficients.
  obtain ⟨Ψ, T, Nfull, U0, V0, hfull⟩ :=
    exists_prescribed_clock_full_terminal_germ A B (F := F) (b := b) (L := L)
      (U := U) (V := V) (H := H) (τ0 := τ0) (v := (-8 : ℝ)) cStar
      (fun p hp ↦ hinitial p (hUN hp)) hb hU h0U hV hcV
      (hL.mono hUN).continuousOn hLbase ⟨hrDown.trans_lt hrτ, hH.1⟩
      (fun p hp ↦ ⟨hrDown.trans (hfamily p hp).1.1.le, (hfamily p hp).1.2.le⟩)
      (fun p hp ↦ hLlevel p (hUN hp)) (by simpa only [hLbase] using hLtime) (by norm_num)
      (fun p hp c hc ↦ ((hfamily p hp).2 c hc).1)
  exact ⟨hβ, hdisjoint, hdet, hselected, hb, hbsupport, hH, hU, h0U, hUN,
    hV, hcV, hzpos, hfamily, hderiv, hunit, hzero, Ψ, T, Nfull, U0, V0, hfull⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
