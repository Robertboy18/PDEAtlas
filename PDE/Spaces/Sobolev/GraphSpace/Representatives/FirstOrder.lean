/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# First-order Sobolev representatives with a prescribed weak gradient

The weak-row constructor bundles a scalar function and its vector-valued weak
gradient into the Sobolev graph space. Conversely, each coordinate of the graph-space
gradient satisfies the defining distributional derivative identity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The coordinates of the vector-valued Sobolev gradient are the weak partial
derivatives of its base representative. -/
theorem hasWeakDerivativeOn_wkpGradientCLM (U : W^{1,p}(Ω)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (baseRepresentative U) (fun x ↦ ∇ U x i) := by
  have h := U.property (singleDerivIndex n i)
  simp only [singleDerivIndex_toList] at h
  exact h.congr_ae Filter.EventuallyEq.rfl
    ((wkpGradientCLM_apply_ae U).mono fun _ hx ↦ (hx i).symm)

/-- A scalar `Lᵖ` function with an `Lᵖ` vector-valued weak gradient determines a
`W¹ᵖ` element with those representatives. -/
theorem exists_of_weakGradient {f : ℝ^n → ℝ} {g : ℝ^n → ℝ^n}
    (hf : MemLp f p (domainMeasure n Ω)) (hg : MemLp g p (domainMeasure n Ω))
    (hweak : ∀ i : Fin n, HasWeakDerivativeOn Ω [i] f (fun x ↦ g x i)) :
    ∃ U : W^{1,p}(Ω), baseRepresentative U =ᵐ[domainMeasure n Ω] f ∧
      (∇ U : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] g := by
  let d : DerivIndex n 1 → ℝ^n → ℝ := firstOrderRows f (fun i x ↦ g x i)
  have hd : d (baseIndex n 1) = f := firstOrderRows_baseIndex _ _
  have hmem (a : DerivIndex n 1) : MemLp (d a) p (domainMeasure n Ω) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, firstOrderRows_baseIndex] using hf
    · simpa only [d, firstOrderRows_singleDerivIndex, EuclideanSpace.coe_proj,
        Function.comp_def] using
        (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hg
  have hderiv (a : DerivIndex n 1) : HasWeakDerivativeOn Ω a.toList f (d a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, firstOrderRows_baseIndex, baseIndex_toList] using
        hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hf (Fact.out : 1 ≤ p))
    · simpa only [d, firstOrderRows_singleDerivIndex, singleDerivIndex_toList] using hweak i
  let U := mkWkpSpaceOnOfWeakDerivatives f d hd hmem hderiv
  have hU (a : DerivIndex n 1) : (U.val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] d a :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae f d hd hmem hderiv a
  refine ⟨U, ?_, ?_⟩
  · simpa only [baseRepresentative, hd] using hU (baseIndex n 1)
  have hrows : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      U.val (singleDerivIndex n i) x = g x i := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hU (singleDerivIndex n i)] with x hx
    simpa only [d, firstOrderRows_singleDerivIndex] using hx
  filter_upwards [wkpGradientCLM_apply_ae U, hrows] with x hx hy
  exact PiLp.ext fun i ↦ (hx i).trans (hy i)

/-- Coordinate `Lᵖ` weak derivatives reconstruct the graph-space element.
The conclusion identifies the stored coordinates as `Lᵖ` elements, so subsequent
operator calculations do not depend on a choice of representatives. -/
theorem exists_of_weakDerivative_coordinates
    (f : DerivLp n p Ω) (df : Fin n → DerivLp n p Ω)
    (hweak : ∀ i : Fin n,
      HasWeakDerivativeOn Ω [i] (f : ℝ^n → ℝ) (df i : ℝ^n → ℝ)) :
    ∃ U : W^{1,p}(Ω), U.val (baseIndex n 1) = f ∧
      ∀ i : Fin n, U.val (singleDerivIndex n i) = df i := by
  let g := Lp.euclideanTuple df
  have hg := Lp.euclideanTuple_apply_ae df
  obtain ⟨U, hU, hDU⟩ := exists_of_weakGradient (Lp.memLp f) (Lp.memLp g)
    (fun i ↦ (hweak i).congr_ae Filter.EventuallyEq.rfl
      (hg.mono fun _ hx ↦ (hx i).symm))
  refine ⟨U, Lp.ext hU, fun i ↦ Lp.ext ?_⟩
  filter_upwards [wkpGradientCLM_apply_ae U, hDU, hg] with x hx hy hz
  exact (hx i).symm.trans ((congrArg (fun z : ℝ^n ↦ z i) hy).trans (hz i))

end SobolevSpace.GraphSpace
