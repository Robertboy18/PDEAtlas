/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ConvolutionL2Derivative
public import PDE.Spaces.Sobolev.Approximation.Mollification.L2Operator
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.StrongDerivative

/-!
# H¹ regularity of the constructed L² mollifier

The derivative-kernel operator is the strong translation derivative and hence the weak
coordinate derivative of mollification. These L² rows construct a scalar H¹ element.
Bounded coordinate projection commutes with convolution, giving H¹ representatives for
every component of a Euclidean-valued mollified field.

No spatial derivative of the input is assumed. The derivative-kernel norm can depend on ε,
so the resulting H¹ bound is not uniform in ε. When the input already belongs
to H¹, uniqueness of the strong translation derivative identifies the derivative-kernel
output with mollification of the weak derivative, also componentwise.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open MeasureTheory Set
open scoped Convolution ENNReal Topology Sobolev

namespace SobolevSpace.Approximation

open PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-- The derivative-kernel operator is the strong `L²` coordinate derivative of
mollification, expressed by differentiating positive spatial translation. -/
theorem hasDerivAt_translate_mollifierL2CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : Lp E 2 (volume : Measure (ℝ^n))) (j : Fin n) :
    HasDerivAt
      (fun t : ℝ ↦ translateL2 ℝ (-(t • EuclideanSpace.single j 1))
        (mollifierL2CLM μ hε u))
      (mollifierDerivativeL2CLM μ hε j u) 0 := by
  simpa only [mollifierL2CLM, mollifierDerivativeL2CLM, convolutionL2CLM_apply,
    partialDeriv] using
    hasDerivAt_translate_convolutionL2CLM
      ((scaled_contDiff μ).of_le (by simp))
      (scaled_hasCompactSupport μ hε) u (EuclideanSpace.single j 1)

end SobolevSpace.Approximation

namespace SobolevSpace.Approximation

open PDE.Analysis

variable {n : ℕ}

/-- Mollification of arbitrary scalar `L²` data has an `L²` weak coordinate derivative,
given by the constructed derivative-kernel operator. No weak derivative of the input is
assumed. -/
theorem hasWeakDerivativeOn_mollifierL2CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : Lp ℝ 2 (volume : Measure (ℝ^n))) (j : Fin n) :
    HasWeakDerivativeOn Set.univ [j]
      (mollifierL2CLM μ hε u : ℝ^n → ℝ)
      (mollifierDerivativeL2CLM μ hε j u : ℝ^n → ℝ) :=
  hasWeakDerivativeOn_of_hasDerivAt_translateL2 j _ _
    (hasDerivAt_translate_mollifierL2CLM μ hε u j)

end SobolevSpace.Approximation

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

/-- The mollification of scalar L² data has an H1 representative with the prescribed
base row and derivative-kernel rows. No weak derivative of the input is required. -/
theorem exists_H1_mollifierL2CLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
    ∃ U : W^{1,2}(ℝ^n),
      ((U : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) : ℝ^n → ℝ)
        =ᵐ[volume] (mollifierL2CLM μ hε u : ℝ^n → ℝ) ∧
      ∀ j : Fin n,
        ((U : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n j) : ℝ^n → ℝ)
          =ᵐ[volume] (mollifierDerivativeL2CLM μ hε j u : ℝ^n → ℝ) := by
  let f0 : ℝ^n → ℝ := mollifierL2CLM μ hε u
  let d : DerivIndex n 1 → ℝ^n → ℝ :=
    firstOrderRows f0 fun j ↦ (mollifierDerivativeL2CLM μ hε j u : ℝ^n → ℝ)
  have hbase : d (baseIndex n 1) = f0 := by simp [d]
  have hmem : ∀ a : DerivIndex n 1,
      MemLp (d a) 2 (domainMeasure n Set.univ) := by
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨j, ha⟩
    · subst a
      simpa [d, f0, domainMeasure] using Lp.memLp (mollifierL2CLM μ hε u)
    · subst a
      simpa [d, domainMeasure] using Lp.memLp (mollifierDerivativeL2CLM μ hε j u)
  have hu0 : HasWeakDerivativeOn Set.univ [] f0 f0 := by
    have hf0 : MemLp f0 2 (domainMeasure n Set.univ) := by
      simpa only [hbase] using hmem (baseIndex n 1)
    have hloc := memLp_locallyIntegrableOn_domain hf0 (by norm_num)
    exact hasWeakDerivativeOn_nil hloc
  have hweak : ∀ a : DerivIndex n 1,
      HasWeakDerivativeOn Set.univ a.toList f0 (d a) := by
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨j, ha⟩
    · subst a
      simpa [d] using hu0
    · subst a
      simpa [d, f0] using hasWeakDerivativeOn_mollifierL2CLM μ hε u j
  let U := mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
      f0 d hbase hmem hweak
  refine ⟨U, ?_, ?_⟩
  · simpa [U, d, f0, domainMeasure] using mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
        f0 d hbase hmem hweak (baseIndex n 1)
  · intro j
    simpa [U, d, domainMeasure] using mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Set.univ)
        f0 d hbase hmem hweak (singleDerivIndex n j)

end SobolevSpace.Approximation

namespace SobolevSpace.Approximation

open PDE.Analysis GraphSpace

variable {n : ℕ}

/-- Each component of mollification has an H1 representative, with derivative coordinates
obtained by projecting the vector-valued derivative-kernel operator. -/
theorem exists_H1_coordinates_mollifierL2CLM {m : ℕ}
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (u : Lp (ℝ^m) 2 (volume : Measure (ℝ^n))) :
    ∃ U : Fin m → W^{1,2}(ℝ^n),
      (∀ p, ((U p : WkpAmbientOn n 1 2 Set.univ) (baseIndex n 1) : ℝ^n → ℝ)
        =ᵐ[volume] fun x ↦ (mollifierL2CLM μ hε u x) p) ∧
      ∀ j p,
        ((U p : WkpAmbientOn n 1 2 Set.univ) (singleDerivIndex n j) : ℝ^n → ℝ)
          =ᵐ[volume] fun x ↦ (mollifierDerivativeL2CLM μ hε j u x) p := by
  let P : Fin m → (ℝ^m →L[ℝ] ℝ) := fun p ↦ PiLp.proj 2 (fun _ : Fin m ↦ ℝ) p
  choose U hbase hderiv using fun p ↦ exists_H1_mollifierL2CLM μ hε ((P p).compLp u)
  have hcomm (p : Fin m) (k : ℝ^n → ℝ) (hk : Integrable k volume) :
      (convolutionL2CLM k hk ((P p).compLp u) : ℝ^n → ℝ) =ᵐ[volume]
        fun x ↦ (convolutionL2CLM k hk u x) p := by
    rw [← compLp_convolutionL2CLM]
    exact (P p).coeFn_compLp _
  refine ⟨U, ?_, ?_⟩
  · intro p
    exact (hbase p).trans (hcomm p _ _)
  · intro j p
    exact (hderiv p j).trans (hcomm p _ _)

end SobolevSpace.Approximation

namespace SobolevSpace.Approximation

open PDE.Analysis GraphSpace

variable {n : ℕ}

/-- On scalar H1 input, convolution by the derivative kernel equals mollification of the
weak derivative. The equality follows from uniqueness of the strong derivative. -/
theorem mollifierDerivativeL2CLM_eq_of_H1 (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (i : Fin n) (U : W^{1,2}(ℝ^n)) (u g : Lp ℝ 2 (volume : Measure (ℝ^n)))
    (hu : ((U : WkpAmbientOn n 1 2 univ) (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[volume] u)
    (hg : ((U : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[volume] g) :
    mollifierDerivativeL2CLM μ hε i u = mollifierL2CLM μ hε g := by
  exact (hasDerivAt_translate_mollifierL2CLM μ hε u i).unique
    (hasDerivAt_translate_convolutionL2CLM_of_hasDerivAt
      (scaled μ ε) (integrable_scaled μ hε) (EuclideanSpace.single i 1) u g
      (hasDerivAt_translateL2_of_H1 i U u g hu hg))

/-- The derivative-kernel identity holds for Euclidean-valued H1 fields, with the weak
derivative identified coordinatewise. Bounded coordinate projections commute with both
convolution operators, so no pointwise evaluation of an L2 integral is needed. -/
theorem mollifierDerivativeL2CLM_eq_of_H1_coordinates {m : ℕ}
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (i : Fin n) (U : Fin m → W^{1,2}(ℝ^n))
    (u g : Lp (ℝ^m) 2 (volume : Measure (ℝ^n)))
    (hu : ∀ p, ((U p : WkpAmbientOn n 1 2 univ) (baseIndex n 1) : ℝ^n → ℝ)
      =ᵐ[volume] fun x ↦ u x p)
    (hg : ∀ p, ((U p : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[volume] fun x ↦ g x p) :
    mollifierDerivativeL2CLM μ hε i u = mollifierL2CLM μ hε g := by
  let P : Fin m → (ℝ^m →L[ℝ] ℝ) := fun p ↦ PiLp.proj 2 (fun _ : Fin m ↦ ℝ) p
  have hscalar (p : Fin m) :
      (P p).compLp (mollifierDerivativeL2CLM μ hε i u) =
        (P p).compLp (mollifierL2CLM μ hε g) := by
    change (P p).compLp (convolutionL2CLM _ _ u) =
      (P p).compLp (convolutionL2CLM _ _ g)
    rw [compLp_convolutionL2CLM, compLp_convolutionL2CLM]
    exact mollifierDerivativeL2CLM_eq_of_H1 μ hε i (U p) ((P p).compLp u)
      ((P p).compLp g) ((hu p).trans (Filter.EventuallyEq.symm ((P p).coeFn_compLp u)))
      ((hg p).trans (Filter.EventuallyEq.symm ((P p).coeFn_compLp g)))
  have hpoint (p : Fin m) :
      (fun x ↦ mollifierDerivativeL2CLM μ hε i u x p) =ᵐ[volume]
        fun x ↦ mollifierL2CLM μ hε g x p := by
    filter_upwards [(P p).coeFn_compLp (mollifierDerivativeL2CLM μ hε i u),
      (P p).coeFn_compLp (mollifierL2CLM μ hε g)] with x hleft hright
    have h := congrArg (fun w : Lp ℝ 2 (volume : Measure (ℝ^n)) ↦ w x) (hscalar p)
    exact hleft.symm.trans (h.trans hright)
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hpoint] with x hx
  ext p
  exact hx p

end SobolevSpace.Approximation
