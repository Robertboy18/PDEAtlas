/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.HigherOrder.Norm
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding

/-!
# Continuity of higher Hölder inclusions

An existence theorem for classical Hölder representatives gives a bounded
linear inclusion. The representative is unique on the closure, and convergence
in measure closes the graph. This converts analytic membership into the full
derivative sum norm estimate without assuming any embedding bound. The proof uses Mathlib's
closed graph theorem `ContinuousLinearMap.ofSeqClosedGraph`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, the norm (3), p. 255.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Sobolev

namespace HolderSpace.CKGammaOn

variable {n m : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- Representatives of the same Sobolev function agree on the closure, even when
their orders or Hölder exponents differ. Thus changing the exponent retains one function. -/
theorem toBoundedContinuousFunction_eq_of_ae_eq
    {l : ℕ} {δ : Exponent} (hΩ : IsOpen Ω)
    {f : CKGammaOn n m Ω γ} {g : CKGammaOn n l Ω δ}
    (h : f.interiorDerivative 0 =ᵐ[volume.restrict Ω] g.interiorDerivative 0) :
    f.toBoundedContinuousFunction = g.toBoundedContinuousFunction := by
  have hi := Measure.eqOn_open_of_ae_eq h hΩ
    ((f.derivative 0).continuousOn_extend_zero.mono subset_closure)
    ((g.derivative 0).continuousOn_extend_zero.mono subset_closure)
  have hc := hi.of_subset_closure (f.derivative 0).continuousOn_extend_zero
    (g.derivative 0).continuousOn_extend_zero subset_closure Subset.rfl
  apply BoundedContinuousFunction.ext
  intro x
  simpa only [toBoundedContinuousFunction, interiorDerivative_apply _ _ x.2] using hc x.2

/-- Almost-everywhere equality on an open domain determines its classical Hölder function. -/
theorem ext_of_ae_eq (hΩ : IsOpen Ω) {f g : CKGammaOn n m Ω γ}
    (h : f.interiorDerivative 0 =ᵐ[volume.restrict Ω] g.interiorDerivative 0) : f = g :=
  ext_of_eqOn (Measure.eqOn_open_of_ae_eq h hΩ
    ((f.derivative 0).continuousOn_extend_zero.mono subset_closure)
    ((g.derivative 0).continuousOn_extend_zero.mono subset_closure))

end HolderSpace.CKGammaOn

namespace SobolevSpace.Inequalities

open GraphSpace HolderSpace

variable {n k m : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)} {γ : Exponent}

/-- Select the unique classical representative supplied by an analytic existence theorem. -/
def holderRepresentativeOfExists
    (hrep : ∀ U : W^{k,p}(Ω), ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (U : W^{k,p}(Ω)) : CKGammaOn n m Ω γ :=
  (hrep U).choose

/-- The selected function represents the same Sobolev equivalence class. -/
theorem holderRepresentativeOfExists_ae
    (hrep : ∀ U : W^{k,p}(Ω), ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (U : W^{k,p}(Ω)) :
    (holderRepresentativeOfExists hrep U).interiorDerivative 0
      =ᵐ[domainMeasure n Ω] baseRepresentative U :=
  (hrep U).choose_spec

variable [Fact (1 ≤ p)]

/-- Existence of higher Hölder representatives on a finite-volume open set implies
continuity of the inclusion into the complete classical derivative graph. -/
def holderEmbeddingCLMOfExists [IsFiniteMeasure (domainMeasure n Ω)] (hΩ : IsOpen Ω)
    (hrep : ∀ U : W^{k,p}(Ω), ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    W^{k,p}(Ω) →L[ℝ] CKGammaOn n m Ω γ := by
  have : Fact (IsOpen Ω) := ⟨hΩ⟩
  let I := holderRepresentativeOfExists hrep
  have hI := holderRepresentativeOfExists_ae hrep
  let inclusion : W^{k,p}(Ω) →ₗ[ℝ] CKGammaOn n m Ω γ :=
    { toFun := I
      map_add' := fun U V ↦ by
        apply CKGammaOn.ext_of_ae_eq hΩ
        change _ =ᵐ[domainMeasure n Ω] _
        simp only [CKGammaOn.interiorDerivative, CKGammaOn.derivative_add,
          BoundedContinuousFunction.extend_zero_add]
        exact (hI (U + V)).trans ((baseRepresentative_add_ae U V).trans
          ((hI U).add (hI V)).symm)
      map_smul' := fun c U ↦ by
        apply CKGammaOn.ext_of_ae_eq hΩ
        change _ =ᵐ[domainMeasure n Ω] _
        simp only [CKGammaOn.interiorDerivative, CKGammaOn.derivative_smul,
          BoundedContinuousFunction.extend_zero_smul]
        exact (hI (c • U)).trans ((baseRepresentative_smul_ae c U).trans
          ((hI U).const_smul c).symm) }
  refine ContinuousLinearMap.ofSeqClosedGraph (g := inclusion) ?_
  intro u x y hux huy
  have hfield : Tendsto (fun j ↦ (inclusion (u j)).derivative 0)
      atTop (𝓝 (y.derivative 0)) :=
    (((continuous_apply 0).comp continuous_fst).comp continuous_subtype_val).tendsto y
      |>.comp huy
  have hpoint := (BoundedContinuousFunction.tendstoUniformly_extend_zero hfield).tendsto_at
  have htarget := tendstoInMeasure_of_tendsto_ae
    (fun j ↦ (Lp.aestronglyMeasurable (wkpBaseCoordinateCLM (u j))).congr (hI (u j)).symm)
    (Filter.Eventually.of_forall hpoint)
  have hbase := tendstoInMeasure_of_tendsto_Lp
    ((wkpBaseCoordinateCLM.continuous.tendsto x).comp hux)
  apply CKGammaOn.ext_of_ae_eq hΩ
  exact (tendstoInMeasure_ae_unique
    (htarget.congr (fun j ↦ hI (u j)) Filter.EventuallyEq.rfl) hbase).trans (hI x).symm

/-- The bounded inclusion is the selected representative. -/
@[simp]
theorem holderEmbeddingCLMOfExists_apply [IsFiniteMeasure (domainMeasure n Ω)]
    (hΩ : IsOpen Ω)
    (hrep : ∀ U : W^{k,p}(Ω), ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (U : W^{k,p}(Ω)) :
    holderEmbeddingCLMOfExists hΩ hrep U = holderRepresentativeOfExists hrep U :=
  rfl

/-- Let `Ω` be open with finite measure. If every `U ∈ W^{k,p}(Ω)` has a representative in
`C^{m,γ}(Ω̄)`, then there is `C > 0` such that every `U` has such a representative `F` with
`F.evansNorm ≤ C * ‖U‖`, where `evansNorm` is the norm (3) of Evans §5.1. -/
theorem exists_pos_evansNorm_bound_of_representatives
    [IsFiniteMeasure (domainMeasure n Ω)] (hΩ : IsOpen Ω)
    (hrep : ∀ U : W^{k,p}(Ω), ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,p}(Ω), ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U ∧
      F.evansNorm ≤ C * ‖U‖ := by
  let T := holderEmbeddingCLMOfExists hΩ hrep
  let d : ℝ := Fintype.card (MultiIndex n m) + Fintype.card (MultiIndex.Top n m)
  have hd : 0 ≤ d := by positivity
  refine ⟨d * ‖T‖ + 1, by positivity, fun U ↦ ⟨T U, ?_, ?_⟩⟩
  · exact holderRepresentativeOfExists_ae hrep U
  · exact (CKGammaOn.evansNorm_le (T U)).trans
      ((mul_le_mul_of_nonneg_left (T.le_opNorm U) hd).trans
        (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg U)))

end SobolevSpace.Inequalities
