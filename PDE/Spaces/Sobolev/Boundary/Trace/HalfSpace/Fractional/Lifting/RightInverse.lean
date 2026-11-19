/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Lifting.RightInverse
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Gagliardo

/-!
# A bounded lifting of real fractional boundary data

Cutoff mollification extends data of order `1 - 1 / p` to the upper half-space,
and the derivative estimates place this formula in `W¹ᵖ`. For real data we read
the Banach-valued extension at `F := ℝ` through the canonical isometry between
the two Sobolev graphs. This gives the unique Sobolev representative
`mollifiedExtensionSobolev`, its norm bound, and the bounded linear lifting
`mollifiedLifting`.

The extension's positive-height averages converge to its boundary datum.
They also converge to the Sobolev trace. The two limits agree, first as
physical `Lᵖ` classes and then in the fractional graph. Every fractional
datum is therefore the trace of a Sobolev function.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Trace.HalfSpace

open Approximation Fractional GraphSpace
open VectorValued.Trace.HalfSpace (upperScalarEquiv)

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The cutoff mollified formula, represented in the first-order Sobolev space. -/
def mollifiedExtensionSobolev (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊) :=
  upperScalarEquiv n p (VectorValued.Trace.HalfSpace.mollifiedExtensionSobolev μ hp g)

/-- The function coordinate of the extension is its defining formula. -/
theorem mollifiedExtensionSobolev_base_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    (wkpBaseCoordinateCLM (mollifiedExtensionSobolev μ hp g) : ℝ^(n + 1) → ℝ)
      =ᵐ[volume.restrict ℝ^(n + 1)₊]
        mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g) :=
  VectorValued.Trace.HalfSpace.mollifiedExtensionSobolev_base_ae μ hp g

/-- The stored weak partials agree with the classical partials of the interior formula. -/
theorem mollifiedExtensionSobolev_partialDeriv_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) (i : Fin (n + 1)) :
    (wkpCoordinateCLM (singleDerivIndex (n + 1) i) (mollifiedExtensionSobolev μ hp g) :
        ℝ^(n + 1) → ℝ)
      =ᵐ[volume.restrict ℝ^(n + 1)₊]
        ∂[i] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g)) :=
  VectorValued.Trace.HalfSpace.mollifiedExtensionSobolev_partialDeriv_ae μ hp g i

/-- Fractional boundary data have a unique Sobolev representative of
their mollified extension, with the classical first derivatives. -/
theorem existsUnique_mollifiedExtension (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    ∃! U : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊),
      (wkpBaseCoordinateCLM U : ℝ^(n + 1) → ℝ)
          =ᵐ[volume.restrict ℝ^(n + 1)₊]
            mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g) ∧
        ∀ i : Fin (n + 1),
          (wkpCoordinateCLM (singleDerivIndex (n + 1) i) U : ℝ^(n + 1) → ℝ)
            =ᵐ[volume.restrict ℝ^(n + 1)₊]
              ∂[i] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g)) := by
  refine ⟨mollifiedExtensionSobolev μ hp g, ⟨mollifiedExtensionSobolev_base_ae μ hp g,
    mollifiedExtensionSobolev_partialDeriv_ae μ hp g⟩, fun U hU ↦ ?_⟩
  have h := (VectorValued.Trace.HalfSpace.existsUnique_mollifiedExtension μ hp g).unique
    (y₁ := (upperScalarEquiv n p).symm U) hU
    ⟨VectorValued.Trace.HalfSpace.mollifiedExtensionSobolev_base_ae μ hp g,
      VectorValued.Trace.HalfSpace.mollifiedExtensionSobolev_partialDeriv_ae μ hp g⟩
  rw [← (upperScalarEquiv n p).apply_symm_apply U, h]
  rfl

/-- The Sobolev norm of the extension is bounded by the fractional
boundary norm, with one positive constant independent of the datum. -/
theorem exists_pos_norm_mollifiedExtensionSobolev_bound (μ : Mollifier n) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p),
        ‖mollifiedExtensionSobolev μ hp g‖ ≤ C * ‖g‖ := by
  simpa only [mollifiedExtensionSobolev, LinearIsometryEquiv.norm_map] using
    VectorValued.Trace.HalfSpace.exists_pos_norm_mollifiedExtensionSobolev_bound (F := ℝ) μ hp

/-- The cutoff mollified extension as a bounded linear map into `W¹ᵖ`.
The boundary space has intrinsic fractional order `1 - 1 / p`. -/
def mollifiedLifting (μ : Mollifier n) (hp : 1 < p) :
    GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) →L[ℝ]
      W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊) :=
  ((upperScalarEquiv n p).toContinuousLinearEquiv : _ →L[ℝ] _).comp
    (VectorValued.Trace.HalfSpace.mollifiedLifting μ hp)

/-- The bounded lifting retains the cutoff and convolution formula. -/
theorem mollifiedLifting_base_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    (wkpBaseCoordinateCLM (mollifiedLifting μ hp g) : ℝ^(n + 1) → ℝ)
      =ᵐ[volume.restrict ℝ^(n + 1)₊]
        mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g) :=
  VectorValued.Trace.HalfSpace.mollifiedLifting_base_ae μ hp g

/-- Any Sobolev function represented by the cutoff mollified extension has
the prescribed boundary trace. -/
theorem traceLp_eq_of_base_ae_mollifiedExtension
    (μ : Mollifier n) (hp : 1 < p)
    {g : ℝ^n → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume)
    (U : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊))
    (hU : (wkpBaseCoordinateCLM U : ℝ^(n + 1) → ℝ)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] mollifiedExtension μ g) :
    traceLp n p hp.le U = hg.toLp g := by
  rw [← (upperScalarEquiv n p).apply_symm_apply U,
    ← VectorValued.Trace.HalfSpace.traceLp_eq_scalar_traceLp]
  exact VectorValued.Trace.HalfSpace.traceLp_eq_of_base_ae_mollifiedExtension μ hp hg _ hU

/-- The physical boundary values of a Sobolev representative of the mollified
extension agree almost everywhere with the original datum. -/
theorem coeFn_traceLp_eq_of_base_ae_mollifiedExtension
    (μ : Mollifier n) (hp : 1 < p)
    {g : ℝ^n → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume)
    (U : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊))
    (hU : (wkpBaseCoordinateCLM U : ℝ^(n + 1) → ℝ)
      =ᵐ[volume.restrict ℝ^(n + 1)₊] mollifiedExtension μ g) :
    (traceLp n p hp.le U : ℝ^n → ℝ) =ᵐ[volume] g := by
  rw [traceLp_eq_of_base_ae_mollifiedExtension μ hp hg U hU]
  exact hg.coeFn_toLp

/-- The physical trace of the lifting agrees almost everywhere with its boundary datum. -/
theorem traceLp_mollifiedLifting_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    (traceLp n p hp.le (mollifiedLifting μ hp g) : ℝ^n → ℝ) =ᵐ[volume]
      (GagliardoSpace.toLp n (1 - 1 / p) univ g : ℝ^n → ℝ) := by
  apply coeFn_traceLp_eq_of_base_ae_mollifiedExtension μ hp
    (U := mollifiedLifting μ hp g)
  · simpa only [Measure.restrict_univ] using
      Lp.memLp (GagliardoSpace.toLp n (1 - 1 / p) univ g)
  · exact mollifiedLifting_base_ae μ hp g

/-- Taking the fractional trace after lifting recovers the original datum. -/
@[simp]
theorem traceGagliardo_mollifiedLifting (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p)) :
    traceGagliardo n p hp (mollifiedLifting μ hp g) = g := by
  apply GagliardoSpace.toLp_injective
  apply Lp.ext
  simpa only [Measure.restrict_univ] using
    (toLp_traceGagliardo_apply_ae n p hp (mollifiedLifting μ hp g)).trans
      (traceLp_mollifiedLifting_ae μ hp g)

/-- The trace and lifting compose to the identity as bounded linear maps. -/
theorem traceGagliardo_comp_mollifiedLifting (μ : Mollifier n) (hp : 1 < p) :
    (traceGagliardo n p hp).comp (mollifiedLifting μ hp) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro g
  exact traceGagliardo_mollifiedLifting μ hp g

/-- Every intrinsic fractional boundary datum occurs as a `W¹ᵖ` trace. -/
theorem traceGagliardo_surjective (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) :
    Function.Surjective (traceGagliardo n p hp) :=
  fun g ↦ ⟨mollifiedLifting (standardMollifier n) hp g,
    traceGagliardo_mollifiedLifting (standardMollifier n) hp g⟩

end SobolevSpace.Trace.HalfSpace
