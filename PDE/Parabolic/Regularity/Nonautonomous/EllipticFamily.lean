/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.StrongLoad

/-!
# Continuous families of elliptic `H²` inverses

The Dirichlet domain is independent of time. Fixing one elliptic inverse therefore
reduces dependence on the coefficients to inversion of bounded operators on `L²`.
Continuity in the spatial `W¹,∞` coefficient norm then gives a continuous family
of `L² → H²` inverses, uniformly bounded on a compact time interval.
-/

@[expose] public noncomputable section

open scoped Sobolev
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace PDE.Parabolic.DivergenceFormHeat

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem continuousOn_inverse_endomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {L : ℝ → E →L[ℝ] E} {s : Set ℝ}
    (hL : ContinuousOn L s) (hinv : ∀ t ∈ s, (L t).IsInvertible) :
    ContinuousOn (fun t ↦ (L t).inverse) s := by
  intro t ht
  obtain ⟨e, he⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr (hinv t ht).bijective
  have hc := NormedRing.inverse_continuousAt e
  rw [he, ContinuousLinearMap.ringInverse_eq_inverse] at hc
  exact hc.comp_continuousWithinAt (hL t ht)

/-- Spatially `W¹,∞` coefficients continuous in time have a continuous, uniformly
bounded family of Dirichlet `L² → H²` inverses on a compact time interval.

The chosen `C¹` representatives and ellipticity are needed only on that interval.
The inverse and its bound are constructed before any forcing or solution is supplied. -/
theorem exists_continuous_spatial_h2_solution_family
    [Fact (0 < n)] (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    {t₀ t₁ : ℝ} (htime : t₀ ≤ t₁)
    (A : ℝ → Fin n → Fin n → W^{1,∞}(Ω))
    (hA : ContinuousOn A (Icc t₀ t₁))
    (a : ℝ → ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ t ∈ Icc t₀ t₁, ∀ i j,
      ⇑((A t i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1))
        =ᵐ[domainMeasure n Ω] fun x ↦ a t x i j)
    (haC1 : ∀ t ∈ Icc t₀ t₁, ∀ i j, ContDiff ℝ 1 (fun x ↦ a t x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ Ω,
      MatrixEllipticLowerBound (a t x) alpha) :
    ∃ (S : ℝ → DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω)) (C : ℝ),
      0 < C ∧ ContinuousOn S (Icc t₀ t₁) ∧
      (∀ t ∈ Icc t₀ t₁, ‖S t‖ ≤ C) ∧
      ∀ t ∈ Icc t₀ t₁, ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
        IsWeakDivergenceSolution (coefficientBase (A t)) f u →
          lowerOrderCLM (k := 1) (m := 2) (by omega) (S t f) = h10SubtypeL u := by
  let ht₀ : t₀ ∈ Icc t₀ t₁ := ⟨le_rfl, htime⟩
  let S₀ := globalH2SolveCLM hΩ (A t₀) (a t₀) (haRep t₀ ht₀)
    (haC1 t₀ ht₀) alpha halpha (hElliptic t₀ ht₀)
  let L := fun t ↦ strongLoadCLM (A t)
  let S := fun t ↦ S₀.comp ((L t).comp S₀).inverse
  have hslice (t : ℝ) (ht : t ∈ Icc t₀ t₁) :
      ((L t).comp S₀).IsInvertible ∧
        S t = globalH2SolveCLM hΩ (A t) (a t) (haRep t ht)
          (haC1 t ht) alpha halpha (hElliptic t ht) := by
    let St := globalH2SolveCLM hΩ (A t) (a t) (haRep t ht)
      (haC1 t ht) alpha halpha (hElliptic t ht)
    have hreset₀ (f : DerivLp n 2 Ω) : S₀ (L t₀ (St f)) = St f :=
      globalH2SolveCLM_strongLoadCLM hΩ (A t₀) (a t₀) (haRep t₀ ht₀)
        (haC1 t₀ ht₀) alpha halpha (hElliptic t₀ ht₀) _ _
        (globalH2SolveCLM_orderOne hΩ (A t) (a t) (haRep t ht)
          (haC1 t ht) alpha halpha (hElliptic t ht) f)
    have hreset (f : DerivLp n 2 Ω) : St (L t (S₀ f)) = S₀ f :=
      globalH2SolveCLM_strongLoadCLM hΩ (A t) (a t) (haRep t ht)
        (haC1 t ht) alpha halpha (hElliptic t ht) _ _
        (globalH2SolveCLM_orderOne hΩ (A t₀) (a t₀) (haRep t₀ ht₀)
          (haC1 t₀ ht₀) alpha halpha (hElliptic t₀ ht₀) f)
    have hright : ((L t).comp S₀).comp ((L t₀).comp St) = .id ℝ (DerivLp n 2 Ω) := by
      apply ContinuousLinearMap.ext
      intro f
      change L t (S₀ (L t₀ (St f))) = f
      rw [hreset₀]
      exact strongLoadCLM_globalH2SolveCLM hΩ (A t) (a t) (haRep t ht)
        (haC1 t ht) alpha halpha (hElliptic t ht) f
    have hleft : ((L t₀).comp St).comp ((L t).comp S₀) = .id ℝ (DerivLp n 2 Ω) := by
      apply ContinuousLinearMap.ext
      intro f
      change L t₀ (St (L t (S₀ f))) = f
      rw [hreset]
      exact strongLoadCLM_globalH2SolveCLM hΩ (A t₀) (a t₀) (haRep t₀ ht₀)
        (haC1 t₀ ht₀) alpha halpha (hElliptic t₀ ht₀) f
    refine ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft, ?_⟩
    change S₀.comp ((L t).comp S₀).inverse = St
    rw [ContinuousLinearMap.inverse_eq hright hleft]
    exact ContinuousLinearMap.ext hreset₀
  have hL : ContinuousOn L (Icc t₀ t₁) :=
    continuous_strongLoadCLM.comp_continuousOn hA
  have hS : ContinuousOn S (Icc t₀ t₁) :=
    continuousOn_const.clm_comp (continuousOn_inverse_endomorphism
      (hL.clm_comp continuousOn_const) (fun t ht ↦ (hslice t ht).1))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (E := DerivLp n 2 Ω →L[ℝ] W^{2,2}(Ω)) hS
  refine ⟨S, max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hS,
    fun t ht ↦ (hC t ht).trans (le_max_left _ _), ?_⟩
  intro t ht f u hu
  rw [(hslice t ht).2, globalH2SolveCLM_orderOne]
  rw [eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution
    hΩ (A t) (a t) (haRep t ht) alpha halpha (hElliptic t ht) f u hu]

end PDE.Parabolic.DivergenceFormHeat
