/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Infinity.Embedding

/-!
# Boundary values of Banach-valued W¹,∞ extensions

Restricting the whole-space Lipschitz representative to the domain closure gives
a bounded continuous representative. Its Lipschitz constant is the sum of the extended
derivative-row norms, bounded by `n * ‖E‖ * ‖U‖` for a bounded extension operator `E`.
Thus the geometry enters through the extension norm.

Any two extensions of the same class agree on the closure: almost-everywhere agreement
on the open domain gives pointwise agreement there, then continuity gives boundary agreement.
These statements include empty domains and dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A whole-space extension represents the original base function almost everywhere
on the domain. -/
theorem lipschitzRepresentative_ae_of_restrict_eq
    (V : W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F))
    (hV : restrictCLM (le_top : Ω ≤ ⊤) V = U) :
    (lipschitzRepresentative V : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      (U.val (baseIndex n 1) : ℝ^n → F) := by
  have h := restrictCLM_apply_ae (le_top : Ω ≤ ⊤) V (baseIndex n 1)
  rw [hV] at h
  have hrep : (lipschitzRepresentative V : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      (V.val (baseIndex n 1) : ℝ^n → F) :=
    ae_mono Measure.restrict_le_self (lipschitzRepresentative_ae V)
  exact hrep.trans h.symm

/-- Any representative continuous on the closure agrees there with the representative
of an extension. Only almost-everywhere agreement inside the domain is needed. -/
theorem lipschitzRepresentative_eqOn_closure
    (V : W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F))
    (hV : restrictCLM (le_top : Ω ≤ ⊤) V = U) {f : ℝ^n → F}
    (hf : ContinuousOn f (closure (Ω : Set ℝ^n)))
    (hU : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f) :
    EqOn (lipschitzRepresentative V) f (closure (Ω : Set ℝ^n)) := by
  have h := Measure.eqOn_open_of_ae_eq
    ((lipschitzRepresentative_ae_of_restrict_eq V U hV).trans hU)
    Ω.isOpen (lipschitzRepresentative V).continuous.continuousOn
    (hf.mono subset_closure)
  exact h.of_subset_closure (lipschitzRepresentative V).continuous.continuousOn
    hf subset_closure Subset.rfl

/-- Whole-space extensions of the same Sobolev class have the same values on the closure.
Their values outside the closure need not coincide. -/
theorem lipschitzRepresentative_eqOn_closure_of_restrict_eq
    (V W : W^{1,∞}(ℝ^n; F))
    (h : restrictCLM (le_top : Ω ≤ ⊤) V = restrictCLM (le_top : Ω ≤ ⊤) W) :
    EqOn (lipschitzRepresentative V) (lipschitzRepresentative W)
      (closure (Ω : Set ℝ^n)) :=
  lipschitzRepresentative_eqOn_closure V _ h
    (lipschitzRepresentative W).continuous.continuousOn
    (lipschitzRepresentative_ae_of_restrict_eq W _ rfl).symm

/-- Restrict the endpoint embedding of a bounded extension to the domain closure.
The right-inverse hypothesis is used by the agreement and injectivity theorems. -/
def closureLipschitzEmbedding
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) :
    W^{1,∞}(Ω; F) →L[ℝ] (closure (Ω : Set ℝ^n) →ᵇ F) :=
  (BoundedContinuousFunction.compContinuousCLM F ℝ
    ⟨Subtype.val, continuous_subtype_val⟩).comp (lipschitzEmbedding.comp E)

/-- Evaluation uses the whole-space representative of the extended class. -/
@[simp] theorem closureLipschitzEmbedding_apply
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (U : W^{1,∞}(Ω; F)) (x : closure (Ω : Set ℝ^n)) :
    closureLipschitzEmbedding E U x = lipschitzRepresentative (E U) x := rfl

/-- The closure representative agrees with the base coordinate almost everywhere.
The membership proof affects neither its value nor the exceptional set. -/
theorem closureLipschitzEmbedding_ae
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (hE : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (E U) = U) (U : W^{1,∞}(Ω; F)) :
    ∀ᵐ x ∂domainMeasure n Ω, ∀ hx : x ∈ closure (Ω : Set ℝ^n),
      closureLipschitzEmbedding E U ⟨x, hx⟩ = U.val (baseIndex n 1) x := by
  filter_upwards [lipschitzRepresentative_ae_of_restrict_eq (E U) U (hE U)] with x hx
  exact fun _ ↦ hx

/-- The extended derivative rows give a Lipschitz constant on the closure. -/
theorem lipschitzWith_closureLipschitzEmbedding
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F)) :
    LipschitzWith (∑ j : Fin n, ‖(E U).val (singleDerivIndex n j)‖₊)
      (closureLipschitzEmbedding E U) := by
  change LipschitzWith _ (lipschitzRepresentative (E U) ∘ Subtype.val)
  simpa only [mul_one] using
    (lipschitzWith_lipschitzRepresentative (E U)).comp
      (LipschitzWith.subtype_val (closure (Ω : Set ℝ^n)))

/-- The extension norm supplies the geometric factor in the Euclidean Lipschitz bound. -/
theorem lipschitzWith_closureLipschitzEmbedding_norm
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F)) :
    LipschitzWith (n * ‖E‖₊ * ‖U‖₊) (closureLipschitzEmbedding E U) := by
  change LipschitzWith _ (lipschitzRepresentative (E U) ∘ Subtype.val)
  have h := (lipschitzWith_lipschitzRepresentative_norm (E U)).weaken
    (mul_le_mul_of_nonneg_left (E.le_opNNNorm U) (show 0 ≤ (n : ℝ≥0) from zero_le))
  simpa only [mul_one, mul_assoc] using
    h.comp (LipschitzWith.subtype_val (closure (Ω : Set ℝ^n)))

/-- Uniform boundedness follows from the base bound for the extended class. -/
theorem norm_closureLipschitzEmbedding_apply_le
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F)) :
    ‖closureLipschitzEmbedding E U‖ ≤ ‖E‖ * ‖U‖ :=
  (BoundedContinuousFunction.norm_compContinuous_le (lipschitzRepresentative (E U))
    ⟨Subtype.val, continuous_subtype_val⟩).trans
      ((norm_lipschitzRepresentative_le (E U)).trans (E.le_opNorm U))

/-- The closure embedding has operator norm bounded by the chosen extension norm. -/
theorem norm_closureLipschitzEmbedding_le
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) :
    ‖closureLipschitzEmbedding E‖ ≤ ‖E‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E)
    (norm_closureLipschitzEmbedding_apply_le E)

/-- The closure representative determines the original Sobolev class. -/
theorem closureLipschitzEmbedding_injective
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (hE : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (E U) = U) :
    Function.Injective (closureLipschitzEmbedding E) := by
  intro U V h
  apply WkpSpaceOn.ext_of_base_ae
  filter_upwards [closureLipschitzEmbedding_ae E hE U,
    closureLipschitzEmbedding_ae E hE V, ae_restrict_mem Ω.isOpen.measurableSet]
    with x hU hV hx
  exact (hU (subset_closure hx)).symm.trans
    ((congrArg (fun f ↦ f ⟨x, subset_closure hx⟩) h).trans (hV (subset_closure hx)))

/-- Any two bounded right inverses give exactly the same closure embedding. -/
theorem closureLipschitzEmbedding_eq
    (E D : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (hE : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (E U) = U)
    (hD : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (D U) = U) :
    closureLipschitzEmbedding E = closureLipschitzEmbedding D := by
  ext U x
  exact lipschitzRepresentative_eqOn_closure_of_restrict_eq (E U) (D U)
    ((hE U).trans (hD U).symm) x.property

/-- In dimension zero the Lipschitz constant is zero for every extension and domain. -/
theorem lipschitzWith_closureLipschitzEmbedding_dimension_zero
    {Ω : Opens ℝ^0} (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^0; F))
    (U : W^{1,∞}(Ω; F)) :
    LipschitzWith 0 (closureLipschitzEmbedding E U) := by
  simpa using lipschitzWith_closureLipschitzEmbedding_norm E U

/-- The closure of the empty domain has the unique empty representative. -/
@[simp] theorem closureLipschitzEmbedding_bot
    (E : W^{1,∞}((⊥ : Opens ℝ^n); F) →L[ℝ] W^{1,∞}(ℝ^n; F)) :
    closureLipschitzEmbedding E = 0 := by
  ext U x
  have hx := x.property
  simp at hx

end SobolevSpace.VectorValued
