/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Candidate.Neighborhood
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.TerminalRatio
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Matched

import CAS.ExactTactic

/-!
# A coupled candidate family with its terminal weight moment

One fixed base-normalized gate family is built from the supplied signed bump
coefficients. Localization of the candidate's time integral and one selected base
moment give a matched base tail. The neighborhood theorem then supplies
the coupled equation on a common parameter and coefficient neighborhood.

The terminal ratio is obtained from the same explicit candidate. Its fast equation
and unit initial value supply the nonzero denominator through the terminal
ratio theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis.Evolution PDE.Analysis.NormalizedPulse
open scoped BigOperators ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- A single open product neighborhood supports the coupled equation and
terminal moment identity for the same explicit candidate. Localization is supplied
for every supported continuous gate on the same parameter neighborhood. Only the
retained base coefficient is normalized; nearby coefficients remain signed and free.
The fast initial condition proves the terminal denominator is positive. -/
theorem exists_prescribed_clock_coupled_moment_family {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ}
    {N : Set (ℝ × ℝ)} {A B rUp rDown τ0 Hmax : ℝ} (hF : ContDiff ℝ ∞ F) (hN : IsOpen N)
    (hbase : (0, 0) ∈ N) (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (hLbase : L (0, 0) = τ0) (hrDown : 0 ≤ rDown) (hrτ : rDown < τ0) (hHmax : τ0 < Hmax)
    (hHslab : Hmax < τ0 + 1) (hAB : A ^ 2 < B ^ 2) (hB : 0 ≤ B) (hmargin : B < (F (τ0, (0, 0))).2)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hfastzero : ∀ p ∈ N, (F (0, p)).2 = 1)
    (hearly : ∀ p ∈ N, ∀ t ∈ Icc (0 : ℝ) rUp, (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧
      (F (t, p)).2 ^ 2 < A ^ 2)
    (hmiddle : ∀ p ∈ N, ∀ t ∈ Icc rUp rDown, (205 : ℝ) < (F (t, p)).1)
    (hlate : ∀ p ∈ N, ∀ t ∈ Icc rDown Hmax, (F (t, p)).1 ∈ Ioo (-1 : ℝ) (20501 / 100) ∧ B ^ 2 <
      (F (t, p)).2 ^ 2)
    (hlocalize : ∀ b : ℝ → ℝ, Continuous b → tsupport b ⊆ Ioo (205 : ℝ) (2051 / 10) → ∀ p ∈ N,
      (∫ t in (0 : ℝ)..L p, b ((F (t, p)).1) * Real.exp (-4 * (L p - t))) =
      prescribedClockWeightMoment b L Bhit p)
    (β : Fin 3 → ℝ → ℝ) (cStar v : Fin 3 → ℝ) (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint : let D0 := parameterizedClockPassageData L Bhit (0, 0); ∀ j i : Fin 3,
      Integrable (fun y ↦ β j y * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i))
    (hcStar : let D0 := parameterizedClockPassageData L Bhit (0, 0);
      (fun i : Fin 3 ↦ ∫ y, (∑ j, cStar j * β j y) * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i) = v)
    (hv : v 0 + v 1 = 1) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : (Fin 3 → ℝ) × ℝ → ℝ := fun z ↦
      (Ioo (205 : ℝ) (2051 / 10)).indicator
        (fun y ↦ (∑ j, z.1 j * β j y) / D0.wMinus y) z.2
    let xhat : ℝ × ((ℝ × ℝ) × (Fin 3 → ℝ)) → ℝ := fun z ↦
      (F (z.1, z.2.1)).2 * scalarLinearSolution (fun _ ↦ 4)
        (fun s ↦ b (z.2.2, (F (s, z.2.1)).1)) 0 0 z.1
    let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
      !₂[xhat (t, (p, c)), (F (t, p)).1, (F (t, p)).2]
    ∃ (H : ℝ) (U : Set (ℝ × ℝ)) (V : Set (Fin 3 → ℝ)),
      H ∈ Ioo τ0 Hmax ∧ IsOpen U ∧ (0, 0) ∈ U ∧ U ⊆ N ∧
        IsOpen V ∧ cStar ∈ V ∧
        ∀ p ∈ U, L p ∈ Ioo rDown H ∧ ∀ c ∈ V,
          (∀ t ∈ Icc (0 : ℝ) H,
            HasDerivAt (q p c)
              (GatedFlux.flux (fun s ↦ 2 * s) MiddleClock.g cutoff (clockFeedback A B)
                (fun y ↦ b (c, y)) (q p c t) - p.1 • q p c t) t) ∧
          (q p c (L p)) 0 / (q p c (L p)) 2 =
            prescribedClockWeightMoment (fun y ↦ b (c, y)) L Bhit p := by
  intro D0 b xhat q
  have hβcompact (j : Fin 3) : HasCompactSupport (β j) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((hβsupport j).trans Ioo_subset_Icc_self)
  have hb : ContDiff ℝ ∞ b :=
    contDiff_prescribed_clock_gate L Bhit β hβsmooth hβcompact hβsupport hβint
  have hbcont (c : Fin 3 → ℝ) : Continuous (fun y : ℝ ↦ b (c, y)) :=
    hb.continuous.comp (continuous_const.prodMk continuous_id)
  have hsmall (c : Fin 3 → ℝ) : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100) :=
    (prescribed_clock_fixed_gate_of_selected_moments L Bhit hN hbase hL hBhit β c
      (fun i ↦ ∫ y, (∑ j, c j * β j y) * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i)
      hβsmooth hβcompact hβsupport hβint rfl).2.2.2.1
  have hfull (c : Fin 3 → ℝ) : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10) :=
    (hsmall c).trans (Ioo_subset_Ioo (by norm_num) (by norm_num))
  have htail : EqOn (fun t ↦ xhat (t, ((0, 0), cStar)))
      (fun t ↦ (F (τ0, (0, 0))).2 * Real.exp (2 * (τ0 - t))) (Icc rDown Hmax) :=
    prescribed_clock_selected_matched_tail
      (F := F) (L := L) (Bhit := Bhit) (A := A) (B := B) (H := Hmax)
      hF.continuous hN hbase hL hBhit hode hLbase hrDown hrτ ⟨hHmax, hHslab⟩
      (fun t ht ↦ (hlate (0, 0) hbase t ht).1.2)
      β cStar v hβsmooth hβcompact hβsupport hβint hcStar hv
      (hlocalize (fun y ↦ b (cStar, y)) (hbcont cStar) (hfull cStar) (0, 0) hbase)
  have hodeShort (p : ℝ × ℝ) (hp : p ∈ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Hmax) :
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t :=
    hode p hp t ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans ht.1, ht.2.trans hHslab.le⟩
  obtain ⟨H, U, V, hH, hU, hbaseU, hUN, hV, hcV, hcoupled⟩ :=
    exists_prescribed_clock_coupled_neighborhood
      (F := F) (L := L) (Bhit := Bhit) (β := β) (cStar := cStar)
      hF hN hbase hL.continuousOn hLbase hrτ hHmax hAB hB hmargin
      hodeShort hearly hmiddle hlate hb hsmall htail
  refine ⟨H, U, V, hH, hU, hbaseU, hUN, hV, hcV, fun p hp ↦ ⟨(hcoupled p hp).1, fun c hc ↦
    ⟨(hcoupled p hp).2 c hc, ?_⟩⟩⟩
  have hpN : p ∈ N := hUN hp
  let X : ℝ → ℝ := fun t ↦ (F (t, p)).1
  let Z : ℝ → ℝ := fun t ↦ (F (t, p)).2
  have hfast (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) :
      HasDerivAt Z ((2 - p.1) * Z t) t := by
    have hpair := hodeShort p hpN t ⟨ht.1, ht.2.trans hH.2.le⟩
    simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', prescribedSpeedField, Z]
      using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hpair
  exact prescribed_clock_terminal_ratio_eq_weight_moment
    (X := X) (Z := Z) (b := fun y ↦ b (c, y)) (L := L) (Bhit := Bhit) (p := p) (H := H) (q := q p c)
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).snd.continuousOn hfast
    (hfastzero p hpN) ⟨hrDown.trans (hcoupled p hp).1.1.le, (hcoupled p hp).1.2.le⟩ (fun _ _ ↦ rfl)
    (hlocalize (fun y ↦ b (c, y)) (hbcont c) (hfull c) p hpN)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
