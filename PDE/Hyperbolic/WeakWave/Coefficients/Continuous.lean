/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.FiniteTimeFamily
public import PDE.Hyperbolic.WeakWave.Coefficients.LInfinity

/-!
# Weak waves from continuous scalar coefficient fields

Continuous scalar fields and their continuous time derivatives on the closed
space-time cylinder construct the coefficient classes in `L∞`. Their norm
derivatives and strong measurability follow from the compact-cylinder estimates.
Uniform ellipticity and symmetry of the principal matrix then give a weak wave.

The conclusion identifies the principal, drift and potential coefficients almost
everywhere with the supplied fields. It includes both initial values and uniform
energy regularity.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The compact-cylinder construction gives principal `L∞` coefficients with an
identified norm derivative. Their scalar representatives transfer symmetry and
uniform ellipticity to the coefficient classes. -/
private theorem exists_principal_coefficients_of_continuousOn_compact {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (A Adot : ℝ → Fin n → Fin n → ℝ^n → ℝ)
    (hA : ∀ i j, ContinuousOn (fun p ↦ A p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAdot : ∀ i j, ContinuousOn (fun p ↦ Adot p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAderiv : ∀ i j, ∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ A s i j x) (Adot t i j x) (Icc a b) t)
    (hsymm : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ i j, A t i j x = A t j i x) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i : Fin n, ξ i * ξ i ≤ ∑ i :
      Fin n, ∑ j : Fin n, A t i j x * ξ j * ξ i) :
    ∃ (coeff coeffDot : ℝ → Fin n → Fin n → DerivLp n ∞ Ω) (N : ℝ≥0),
      (∀ t ∈ Icc a b, ∀ i j,
        (coeff t i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A t i j) ∧
      AbsolutelyContinuousOnInterval coeff a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt coeff (coeffDot t) t) ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N) ∧
      (∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t)) ∧
      (∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha) := by
  classical
  have hK : IsCompact (closure Ω) := hΩbounded.isCompact_closure
  have hμΩ : ∀ᵐ x ∂domainMeasure n Ω, x ∈ Ω := ae_restrict_mem hΩopen.measurableSet
  have hμK : ∀ᵐ x ∂domainMeasure n Ω, x ∈ closure Ω := hμΩ.mono fun x hx ↦ subset_closure hx
  obtain ⟨F, D, _, N, hFrep, _, _, hDbound, hFLip, hFderiv⟩ :=
    exists_lp_top_family_with_derivative_of_continuousOn_compact hK hμK
      (fun ij : Fin n × Fin n ↦ fun t x ↦ A t ij.1 ij.2 x)
      (fun ij : Fin n × Fin n ↦ fun t x ↦ Adot t ij.1 ij.2 x)
      (fun ij ↦ hA ij.1 ij.2) (fun ij ↦ hAdot ij.1 ij.2) (fun ij ↦ hAderiv ij.1 ij.2)
  let coeff (t : ℝ) (i j : Fin n) := F t (i, j)
  let coeffDot (t : ℝ) (i j : Fin n) := D t (i, j)
  have hcoeffLip : LipschitzOnWith N coeff (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
    rw [dist_eq_norm]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg N.coe_nonneg dist_nonneg)).mpr fun i ↦ ?_
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg N.coe_nonneg dist_nonneg)).mpr fun j ↦ ?_
    have hdist : ‖F s - F t‖ ≤ (N : ℝ) * dist s t := by
      simpa only [dist_eq_norm] using hFLip.dist_le_mul s hs t ht
    exact (norm_le_pi_norm (F s - F t) (i, j)).trans hdist
  have hcoeffAC : AbsolutelyContinuousOnInterval coeff a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab.le] using hcoeffLip
  have hcoeffDeriv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt coeff (coeffDot t) t := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hwithin : HasDerivWithinAt coeff (coeffDot t) (Icc a b) t :=
      hasDerivWithinAt_pi.mpr fun i ↦ hasDerivWithinAt_pi.mpr fun j ↦
        (hasDerivWithinAt_pi.mp (hFderiv t ⟨ht.1.le, ht.2.le⟩)) (i, j)
    exact hwithin.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hcoeffDot : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖coeffDot t‖ ≤ N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine (pi_norm_le_iff_of_nonneg N.coe_nonneg).mpr fun i ↦ ?_
    refine (pi_norm_le_iff_of_nonneg N.coe_nonneg).mpr fun j ↦ ?_
    exact (norm_le_pi_norm (D t) (i, j)).trans (hDbound t (Ioc_subset_Icc_self ht))
  have hsymmAE : ∀ t ∈ Icc a b, AESymmetricCoefficient (coeff t) := by
    intro t ht i j
    filter_upwards [hμΩ, hFrep (i, j) t ht, hFrep (j, i) t ht] with x hx hij hji
    exact hij.trans ((hsymm t ht x hx i j).trans hji.symm)
  have hellipticAE : ∀ t ∈ Icc a b, AEUniformlyElliptic (coeff t) alpha := by
    intro t ht
    refine ⟨halpha, ?_⟩
    have hrep : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j, coeff t i j x = A t i j x :=
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ hFrep (i, j) t ht
    filter_upwards [hμΩ, hrep] with x hx hxeq ξ
    simpa only [hxeq] using helliptic t ht x hx ξ
  exact ⟨coeff, coeffDot, N, (fun t ht i j ↦ hFrep (i, j) t ht),
    hcoeffAC, hcoeffDeriv, hcoeffDot, hsymmAE, hellipticAE⟩

/-- Continuous drift and potential fields give bounded, strongly measurable `L∞` classes. -/
private theorem exists_lower_coefficients_of_continuousOn_compact {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (B : ℝ → Fin n → ℝ^n → ℝ)
    (C : ℝ → ℝ^n → ℝ) (hB : ∀ i, ContinuousOn (fun p ↦ B p.1 i p.2) (Icc a b ×ˢ closure Ω))
    (hC : ContinuousOn (Function.uncurry C) (Icc a b ×ˢ closure Ω)) :
    ∃ (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω) (Z : ℝ≥0),
      (∀ t ∈ Icc a b, ∀ i,
        ((z t).1 i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] B t i) ∧
      (∀ t ∈ Icc a b, ((z t).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] C t) ∧
      AEStronglyMeasurable z (volume.restrict (Ioc a b)) ∧
      (∀ t ∈ Icc a b, ‖z t‖ ≤ Z) := by
  classical
  have hK : IsCompact (closure Ω) := hΩbounded.isCompact_closure
  have hμK : ∀ᵐ x ∂domainMeasure n Ω, x ∈ closure Ω :=
    (ae_restrict_mem hΩopen.measurableSet).mono fun x hx ↦ subset_closure hx
  let lower (k : Option (Fin n)) (t : ℝ) (x : ℝ^n) :=
    match k with | none => C t x | some i => B t i x
  have hlower (k) : ContinuousOn (Function.uncurry (lower k))
      (Icc a b ×ˢ closure Ω) := by
    cases k with
    | none => exact hC
    | some i => exact hB i
  choose G M hG using fun k ↦
    exists_lp_top_curve_of_continuousOn_compact hK hμK (lower k) (hlower k)
  let Z : ℝ≥0 := ∑ k, M k
  have hM (k : Option (Fin n)) : (M k : ℝ) ≤ Z := by
    exact_mod_cast Finset.single_le_sum (fun j _ ↦ (M j).coe_nonneg) (Finset.mem_univ k)
  have hGcont (k) : ContinuousOn (G k) (Icc a b) :=
    continuousOn_lp_top_of_continuousOn_compact hK hμK (lower k) (G k) (hlower k)
      (fun t ht ↦ (hG k t ht).1)
  let z (t : ℝ) := ((fun i : Fin n ↦ G (some i) t), G none t)
  have hzbound : ∀ t ∈ Icc a b, ‖z t‖ ≤ Z := by
    intro t ht
    apply norm_prod_le_iff.mpr
    constructor
    · exact (pi_norm_le_iff_of_nonneg Z.coe_nonneg).mpr
        fun i ↦ (hG (some i) t ht).2.trans (hM (some i))
    · exact (hG none t ht).2.trans (hM none)
  have hzcont : ContinuousOn z (Icc a b) :=
    (continuousOn_pi.mpr fun i ↦ hGcont (some i)).prodMk (hGcont none)
  have hzmeas : AEStronglyMeasurable z (volume.restrict (Ioc a b)) :=
    AEStronglyMeasurable.mono_set Ioc_subset_Icc_self
      (hzcont.aestronglyMeasurable_of_isCompact (μ := volume) isCompact_Icc measurableSet_Icc)
  exact ⟨z, Z, (fun t ht i ↦ (hG (some i) t ht).1), (fun t ht ↦ (hG none t ht).1), hzmeas, hzbound⟩

/-- Continuous coefficients on the closed cylinder, with continuous time derivatives
of the principal matrix, construct a weak Dirichlet wave with natural `L²` forcing. The principal
matrix is symmetric and uniformly elliptic on the domain; the lower-order coefficients have no
symmetry or sign assumption.

The proof constructs the `L∞` coefficient classes, their norm derivatives and the
weak solution. The representative identities identify its form with the supplied
scalar coefficients. Both initial values and the uniform energy regularity are
included in the conclusion. -/
theorem exists_weakWave_of_continuousOn_compact_coefficients {n : ℕ} {Ω : Set (ℝ^n)} (hn : 0 < n)
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (A Adot : ℝ → Fin n → Fin n → ℝ^n → ℝ) (B : ℝ → Fin n → ℝ^n → ℝ) (C : ℝ → ℝ^n → ℝ)
    (hA : ∀ i j, ContinuousOn (fun p ↦ A p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAdot : ∀ i j, ContinuousOn (fun p ↦ Adot p.1 i j p.2) (Icc a b ×ˢ closure Ω))
    (hAderiv : ∀ i j, ∀ x ∈ closure Ω, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s ↦ A s i j x) (Adot t i j x) (Icc a b) t)
    (hB : ∀ i, ContinuousOn (fun p ↦ B p.1 i p.2) (Icc a b ×ˢ closure Ω))
    (hC : ContinuousOn (Function.uncurry C) (Icc a b ×ˢ closure Ω))
    (hsymm : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ i j, A t i j x = A t j i x) {alpha : ℝ} (halpha : 0 < alpha)
    (helliptic : ∀ t ∈ Icc a b, ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i : Fin n, ξ i * ξ i ≤ ∑ i :
      Fin n, ∑ j : Fin n, A t i j x * ξ j * ξ i)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) (q₀ : H¹₀(Ω)) (p₀ : DerivLp n 2 Ω) :
    let T := h10L2GelfandTriple hΩopen
    ∃ (coeff : ℝ → Fin n → Fin n → DerivLp n ∞ Ω)
        (z : ℝ → (Fin n → DerivLp n ∞ Ω) × DerivLp n ∞ Ω),
      (∀ t ∈ Icc a b, ∀ i j,
        (coeff t i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] A t i j) ∧
      (∀ t ∈ Icc a b, ∀ i,
        ((z t).1 i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] B t i) ∧
      (∀ t ∈ Icc a b, ((z t).2 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] C t) ∧
      ∃ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
          (velocity : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
          (acceleration :
            Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
        Hyperbolic.Variational.IsGelfandWeakWaveSolution T
            (fun t ↦ fullDivergenceForm (multiplicationCoefficientOperator (coeff t))
              (fun i ↦ mulLpLeft ((z t).1 i)) (mulLpLeft (z t).2))
            (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
            u velocity acceleration q₀ p₀ ∧
          MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
          MemLp (fun t ↦ velocity t) ∞ (volume.restrict (Ioc a b)) := by
  classical
  -- Choose the coefficient data without eliminating existentials over the solution goal.
  have hprincipal := exists_principal_coefficients_of_continuousOn_compact hΩopen hΩbounded hab
      A Adot hA hAdot hAderiv hsymm halpha helliptic
  let coeff := hprincipal.choose
  let coeffDot := hprincipal.choose_spec.choose
  let N := hprincipal.choose_spec.choose_spec.choose
  have hcoeff := hprincipal.choose_spec.choose_spec.choose_spec
  have hcoeffRep := hcoeff.1
  have hcoeffAC := hcoeff.2.1
  have hcoeffDeriv := hcoeff.2.2.1
  have hcoeffDot := hcoeff.2.2.2.1
  have hsymmAE := hcoeff.2.2.2.2.1
  have hellipticAE := hcoeff.2.2.2.2.2
  have hlower := exists_lower_coefficients_of_continuousOn_compact hΩopen hΩbounded B C hB hC
  let z := hlower.choose
  let Z := hlower.choose_spec.choose
  have hz := hlower.choose_spec.choose_spec
  have hzRep := hz.1
  have hzPotential := hz.2.1
  have hzmeas := hz.2.2.1
  have hzbound := hz.2.2.2
  refine ⟨coeff, z, hcoeffRep, hzRep, hzPotential, ?_⟩
  exact exists_weakWave_of_linf_coefficients hn hΩopen hΩbounded hab
    coeff coeffDot z hcoeffAC hcoeffDeriv N Z hcoeffDot hzmeas hzbound hsymmAE hellipticAE f q₀ p₀

end SobolevSpace.GraphSpace
