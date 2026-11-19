/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
public import PDE.Analysis.Integration.BumpMoments.Finite
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Matching.PhysicalJet

import CAS.ExactTactic

/-!
# Coefficient derivative of the physical first-match residual

The supplied terminal identity holds for the same explicit candidate on one open
parameter and coefficient product neighborhood. The physical ordinary parameter
jet and the canonical bump-moment identity give an affine coefficient germ there.
Its derivative retains the raw moment row transformations and is invertible.

The event-gap displacement factor is derived from the prescribed family
and its two events. The fast terminal factor is positive by scalar ODE uniqueness.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis PDE.Analysis.Evolution
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- On the retained coupled-family neighborhood, the first-match residual
has coefficient derivative `A_G * M`, where `M` is the canonical matrix of raw
`(1,R,Q)` moments. The terminal identity is a hypothesis on the family; the
ordinary parameter derivatives and the affine coefficient identity are derived.
All clock, event, bump, and base-normalizer data remain fixed. -/
theorem hasFDerivAt_prescribed_clock_physical_coefficient_residual {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {L Bhit : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {V : Set (Fin 3 → ℝ)} {A B H : ℝ} (hF : ContDiff ℝ ∞ F)
    (hU : IsOpen U) (h0 : (0, 0) ∈ U) (hV : IsOpen V) (cStar : Fin 3 → ℝ) (hcStar : cStar ∈ V)
    (hL : ContDiffOn ℝ ∞ L U) (hBhit : ContDiffOn ℝ ∞ Bhit U)
    (hode : ∀ p ∈ U, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hinitial : ∀ p ∈ U, F (0, p) = (p.2, 1)) (hLmem : L (0, 0) ∈ Icc (0 : ℝ) H)
    (hBmem : Bhit (0, 0) ∈ Icc (0 : ℝ) H) (hLlevel : ∀ p ∈ U, (F (L p, p)).1 = 0)
    (hBlevel : ∀ p ∈ U, (F (Bhit p, p)).1 = 205)
    (hLtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (-8) (L (0, 0)))
    (hBtime : HasDerivAt (fun t ↦ (F (t, (0, 0))).1) (MiddleClock.g 205 + 1) (Bhit (0, 0)))
    (β : Fin 3 → ℝ → ℝ) (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint : let D0 := parameterizedClockPassageData L Bhit (0, 0); ∀ j i : Fin 3,
      Integrable (fun y ↦ β j y * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i)) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : (Fin 3 → ℝ) → ℝ → ℝ := fun c ↦
      (Ioo (205 : ℝ) (2051 / 10)).indicator
        (fun y ↦ (∑ j, c j * β j y) / D0.wMinus y)
    let q : (ℝ × ℝ) → (Fin 3 → ℝ) → ℝ → ℝ^3 := fun p c t ↦
      !₂[(F (t, p)).2 * scalarLinearSolution (fun _ ↦ 4)
          (fun s ↦ b c ((F (s, p)).1)) 0 0 t,
        (F (t, p)).1, (F (t, p)).2]
    let ρ : (Fin 3 → ℝ) → (ℝ × ℝ) → ℝ := fun c p ↦
      (q p c (L p)) 0 / (q p c (L p)) 2
    let z : ℝ × ℝ → ℝ := fun p ↦ (F (L p, p)).2
    let M := bumpMomentMatrix (fun y ↦ (![1, D0.R y, D0.Q y] : Fin 3 → ℝ)) β
    let d := deriv (fun a ↦ L (0, a) - Bhit (0, a)) 0
    let A_G : Matrix (Fin 3) (Fin 3) ℝ :=
      !![1, 1, 0; 0, -4 * d, 0; 0, 0, z (0, 0)]
    let G : (Fin 3 → ℝ) → Fin 3 → ℝ := fun c ↦
      ![ρ c (0, 0) - 1,
        deriv (fun a ↦ ρ c (0, a)) 0,
        z (0, 0) * deriv (fun μ ↦ ρ c (μ, 0)) 0 +
          2 * deriv (fun μ ↦ z (μ, 0)) 0 +
          2000000 * deriv (fun a ↦ z (0, a)) 0]
    (∀ p ∈ U, ∀ c ∈ V, ρ c p = prescribedClockWeightMoment (b c) L Bhit p) →
    M.det ≠ 0 →
    HasFDerivAt G (Matrix.toLin' (A_G * M)).toContinuousLinearMap cStar ∧
      (fderiv ℝ G cStar).det = -4 * d * z (0, 0) * M.det ∧
      (fderiv ℝ G cStar).det ≠ 0 ∧ IsUnit (fderiv ℝ G cStar) ∧
      (M *ᵥ cStar = ![1, 0,
        -(2 * deriv (fun μ ↦ z (μ, 0)) 0 +
          2000000 * deriv (fun a ↦ z (0, a)) 0) / z (0, 0)] → G cStar = 0) := by
  classical
  intro D0 b q ρ z M d A_G G hterminal hdet
  have hβcompact (j : Fin 3) : HasCompactSupport (β j) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) ((hβsupport j).trans Ioo_subset_Icc_self)
  have hLone : ContDiffOn ℝ 1 L U := hL.of_le (by simp)
  have hBone : ContDiffOn ℝ 1 Bhit U := hBhit.of_le (by simp)
  have hgap : 0 < fderiv ℝ (fun p ↦ L p - Bhit p) (0, 0) (0, 1) :=
    fderiv_prescribed_event_gap_displacement_pos
      (hLmem.1.trans hLmem.2) hLmem hBmem hF hU h0 hode hinitial
      hLone hBone rfl rfl hLlevel hBlevel hLtime hBtime
  have hdpos : 0 < d := hgap.trans_eq (deriv_prod_timeSlice (fun p : ℝ × ℝ ↦ L p - Bhit p) 0 0
    ((hLone.contDiffAt (hU.mem_nhds h0)).differentiableAt_one.fun_sub
      (hBone.contDiffAt (hU.mem_nhds h0)).differentiableAt_one)).symm
  let Z : ℝ → ℝ := fun t ↦ (F (t, (0, 0))).2
  have hZcont : Continuous Z :=
    (hF.continuous.comp (continuous_id.prodMk continuous_const)).snd
  have hZzero : Z 0 = 1 := congrArg Prod.snd (hinitial (0, 0) h0)
  have hZend : z (0, 0) = Real.exp (2 * L (0, 0)) := by
    have heq := eq_scalarLinearSolution_const_of_hasDerivAt
      (r := Z) (f := fun _ ↦ 0) (κ := -(2 : ℝ)) hLmem.1
      hZcont.continuousOn continuousOn_const (fun t ht ↦ by
        simpa only [neg_neg, add_zero, Z] using
          hasDerivAt_prescribed_base_fast h0 hode
            ⟨ht.1.le, ht.2.le.trans hLmem.2⟩)
    rw [scalarLinearSolution_const_eq_exp_mul_add_integral] at heq
    simpa only [hZzero, neg_neg, sub_zero, mul_one, mul_zero,
      intervalIntegral.integral_zero, add_zero] using heq
  have hzpos : 0 < z (0, 0) := hZend ▸ Real.exp_pos _
  have hjet := prescribed_clock_physical_jet_of_terminal_identity
    L Bhit hU h0 hL hBhit β q hβsmooth hβcompact hβsupport hβint hterminal
  have hjetM (c : Fin 3 → ℝ) (hc : c ∈ V) :
      ρ c (0, 0) = (M *ᵥ c) 0 + (M *ᵥ c) 1 ∧
      HasDerivAt (fun μ ↦ ρ c (μ, 0)) ((M *ᵥ c) 2) 0 ∧
      HasDerivAt (fun a ↦ ρ c (0, a)) (-4 * d * (M *ᵥ c) 1) 0 := by
    rw [show M *ᵥ c = fun i ↦ ∫ y, (∑ j, c j * β j y) * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i
      from funext fun i ↦ bumpMomentMatrix_mulVec_eq_integral _ β hβint c i]
    exact hjet c hc
  let J : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    (Matrix.toLin' (A_G * M)).toContinuousLinearMap
  let offset : Fin 3 → ℝ :=
    ![-1, 0, 2 * deriv (fun μ ↦ z (μ, 0)) 0 +
      2000000 * deriv (fun a ↦ z (0, a)) 0]
  have hrow (v : Fin 3 → ℝ) :
      A_G *ᵥ v = ![v 0 + v 1, -4 * d * v 1, z (0, 0) * v 2] := by
    ext i
    fin_cases i <;> simp [A_G, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have haffine (c : Fin 3 → ℝ) (hc : c ∈ V) : G c = J c + offset := by
    obtain ⟨hvalue, hspeed, hdisplacement⟩ := hjetM c hc
    have hJc : J c = A_G *ᵥ (M *ᵥ c) := (Matrix.mulVec_mulVec c A_G M).symm
    rw [hJc, hrow]
    simp only [G, offset]
    rw [hvalue, hspeed.deriv, hdisplacement.deriv]
    ext i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Pi.add_apply, Matrix.cons_val] <;> ring
  have hderiv : HasFDerivAt G J cStar := (J.hasFDerivAt.add_const offset).congr_of_eventuallyEq
    (eventually_of_mem (hV.mem_nhds hcStar) haffine)
  have hAdet : A_G.det = -4 * d * z (0, 0) := by simp [A_G, Matrix.det_fin_three]
  have hJdet : J.det = -4 * d * z (0, 0) * M.det := by
    change LinearMap.det (Matrix.toLin' (A_G * M)) = -4 * d * z (0, 0) * M.det
    rw [LinearMap.det_toLin', Matrix.det_mul, hAdet]
  have hJne : J.det ≠ 0 := by
    rw [hJdet]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hdpos.ne') hzpos.ne') hdet
  have hJUnit : IsUnit J :=
    ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
      ((LinearMap.isUnit_iff_isUnit_det J.toLinearMap).mpr (isUnit_iff_ne_zero.mpr hJne))
  refine ⟨hderiv, hderiv.fderiv ▸ hJdet, hderiv.fderiv ▸ hJne, hderiv.fderiv ▸ hJUnit,
    fun hselected ↦ ?_⟩
  have hJstar : J cStar = A_G *ᵥ (M *ᵥ cStar) := (Matrix.mulVec_mulVec cStar A_G M).symm
  rw [haffine cStar hcStar, hJstar, hrow, hselected]
  ext i
  fin_cases i <;> simp [offset, mul_div_cancel₀ _ hzpos.ne']

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
