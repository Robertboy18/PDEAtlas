/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# One-dimensional Euclidean transport

The time-regularization theory is stated for functions on `ℝ`, while the
underlying Sobolev mollifier is formulated on Euclidean spaces. We record
the local-integrability transport through the canonical
measure-preserving equivalence between `ℝ` and `ℝ^1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X]

/-- Pulling a locally integrable Banach-valued function on `ℝ` back to
LeanPDE's one-dimensional Euclidean space preserves local integrability. -/
theorem locallyIntegrable_comp_oneDimensionalEquiv_symm
    (f : ℝ → X) (hf : LocallyIntegrable f (volume : Measure ℝ)) :
    LocallyIntegrable
      (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)))
      (volume : Measure (ℝ^1)) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hmp : MeasurePreserving e.symm
      (volume : Measure (ℝ^1)) (volume : Measure ℝ) :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  refine (locallyIntegrable_iff (X := ℝ^1)
    (μ := (volume : Measure (ℝ^1)))
    (f := f ∘ e.symm)).2 ?_
  intro K hK
  have hKimage : IsCompact (e.symm '' K) :=
    hK.image e.symm.continuous
  have hOn : IntegrableOn f (e.symm '' K) (volume : Measure ℝ) :=
    hf.integrableOn_isCompact hKimage
  have hiff := MeasurePreserving.integrableOn_image
    (μ := (volume : Measure (ℝ^1))) (ν := (volume : Measure ℝ))
    hmp e.symm.toHomeomorph.measurableEmbedding (f := f) (s := K)
  simpa [e, Function.comp_def] using hiff.1 hOn

end PDE.Analysis.Evolution
