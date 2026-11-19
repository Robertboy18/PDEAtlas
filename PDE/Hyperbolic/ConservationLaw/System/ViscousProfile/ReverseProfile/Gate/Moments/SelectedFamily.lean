/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.CoupledFamily
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Independence
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.CoefficientRank

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.FastVariation
import CAS.ExactTactic

/-!
# Selected clock moments and their retained coupled family

The base passage gap supplies one nonsingular family of three bumps.
Surjectivity selects signed coefficients for the physical matching residual.
The coupled-family and coefficient-rank theorems then apply to these same data.

The fixed normalizer uses the supplied events, including their speed anchor.
The rank calculation uses the original slab through `τ0 + 1`, so its upward
base event need not lie before the smaller coupled-family endpoint `H`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Matrix

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Choose moment bumps and a matching signed coefficient, retaining one
coupled family on an open physical-parameter and coefficient product.

The event levels, base time derivatives, and base upward-event containment are
inputs from the supplied speed-event family. The raw moment determinant, matching
coefficient, physical residual derivative, and its invertibility are conclusions.
The ordinary parameter derivatives in the residual use the same terminal map. -/
theorem exists_prescribed_clock_selected_moment_family {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
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
        !₂[(F (t, p)).2 * scalarLinearSolution (fun _ ↦ 4)
            (fun s ↦ b (c, (F (s, p)).1)) 0 0 t,
          (F (t, p)).1, (F (t, p)).2]
      let ρ : (Fin 3 → ℝ) → (ℝ × ℝ) → ℝ := fun c p ↦
        (q p c (L p)) 0 / (q p c (L p)) 2
      let M := bumpMomentMatrix W β
      let d := deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0
      let A_G : Matrix (Fin 3) (Fin 3) ℝ :=
        !![1, 1, 0; 0, -4 * d, 0; 0, 0, z (0, 0)]
      let G : (Fin 3 → ℝ) → Fin 3 → ℝ := fun c ↦
        ![ρ c (0, 0) - 1,
          deriv (fun a ↦ ρ c (0, a)) 0,
          z (0, 0) * deriv (fun μ ↦ ρ c (μ, 0)) 0 +
            2 * deriv (fun μ ↦ z (μ, 0)) 0 +
            2000000 * deriv (fun a ↦ z (0, a)) 0]
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
        ρ c p = prescribedClockWeightMoment (fun y ↦ b (c, y)) L Bhit p) ∧
      HasFDerivAt G J cStar ∧ IsUnit J ∧ G cStar = 0 := by
  classical
  intro D0 W z v
  have hbumps := exists_clock_bumps_moment_matrix_det_ne_zero
    205 (Bhit (0, 0)) (L (0, 0)) (prescribedSpeedAnchorConstant L Bhit)
    (by simpa only [parameterizedClockPassageData_zero] using hgap)
  rw [← parameterizedClockPassageData_zero L Bhit] at hbumps
  obtain ⟨β, hβ, hdisjoint, hdet, hsurj⟩ := hbumps
  have hβsmooth (j : Fin 3) : ContDiff ℝ ∞ (β j) := (hβ j).1
  have hβcompact (j : Fin 3) : HasCompactSupport (β j) := (hβ j).2.1
  have hβsupport (j : Fin 3) :
      tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) := (hβ j).2.2.1
  have hβint (j i : Fin 3) : Integrable (fun y ↦ β j y * W y i) :=
    (hβ j).2.2.2.2.2 i
  -- Division is total when choosing the target. Fast positivity is proved below.
  obtain ⟨cStar, hcStar⟩ := hsurj v
  have hselected : bumpMomentMatrix W β *ᵥ cStar = v :=
    (funext fun i ↦ bumpMomentMatrix_mulVec_eq_integral W β hβint cStar i).trans hcStar
  have hv : v 0 + v 1 = 1 := add_zero 1
  have hfastzero (p : ℝ × ℝ) (hp : p ∈ N) : (F (0, p)).2 = 1 :=
    congrArg Prod.snd (hinitial p hp)
  obtain ⟨H, U, V, hH, hU, h0U, hUN, hV, hcV, hfamily⟩ :=
    exists_prescribed_clock_coupled_moment_family
      hF hN hbase hL hBhit hLbase hrDown hrτ hHmax hHslab hAB hB hmargin
      hode hfastzero hearly hmiddle hlate hlocalize β cStar v
      hβsmooth hβsupport hβint hcStar hv
  refine ⟨β, cStar, H, U, V, ?_⟩
  intro b q ρ M d A_G G J
  have hb : ContDiff ℝ ∞ b :=
    contDiff_prescribed_clock_gate L Bhit β hβsmooth hβcompact hβsupport hβint
  have hLU : ContDiffOn ℝ ∞ L U := hL.mono hUN
  have hBU : ContDiffOn ℝ ∞ Bhit U := hBhit.mono hUN
  -- The rank theorem needs the upward base event on its ODE slab, not on [0,H].
  have hodeRank (p : ℝ × ℝ) (hp : p ∈ U) (t : ℝ)
      (ht : t ∈ Icc (0 : ℝ) (τ0 + 1)) :
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t :=
    hode p (hUN hp) t ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans ht.1, ht.2⟩
  have hLslab (p : ℝ × ℝ) (hp : p ∈ U) : L p ∈ Icc (0 : ℝ) (τ0 + 1) :=
    ⟨hrDown.trans (hfamily p hp).1.1.le,
      (hfamily p hp).1.2.le.trans (hH.2.le.trans hHslab.le)⟩
  have hfast := prescribed_clock_fast_terminal_variation hU h0U
    (hLU.of_le (by simp)) hodeRank (fun p hp ↦ hfastzero p (hUN hp)) hLslab
  have hrank := hasFDerivAt_prescribed_clock_physical_coefficient_residual
    (A := A) (B := B) (H := τ0 + 1)
    hF hU h0U hV cStar hcV hLU hBU hodeRank
    (fun p hp ↦ hinitial p (hUN hp)) (hLslab (0, 0) h0U) hBmem
    (fun p hp ↦ hLlevel p (hUN hp)) (fun p hp ↦ hBlevel p (hUN hp))
    hLtime hBtime β hβsmooth hβsupport hβint
    (fun p hp c hc ↦ ((hfamily p hp).2 c hc).2) hdet
  have hderiv : HasFDerivAt G J cStar := hrank.1
  have hunit : IsUnit J := by rw [← hderiv.fderiv]; exact hrank.2.2.2.1
  refine ⟨hβ, hdisjoint, hdet, hselected, hb, fun c ↦ ?_, hH, hU, h0U, hUN, hV, hcV,
    fun p hp ↦ show 0 < (F (L p, p)).2 by rw [hfast.1 p hp]; exact Real.exp_pos _, hfamily,
    hderiv, hunit, hrank.2.2.2.2 hselected⟩
  obtain ⟨-, h1, h2, h3, -⟩ := prescribed_clock_fixed_gate_of_selected_moments L Bhit hN hbase
    hL hBhit β c (fun i ↦ ∫ y, (∑ j, c j * β j y) * W y i) hβsmooth hβcompact hβsupport hβint rfl
  exact ⟨h1, h2, h3⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
