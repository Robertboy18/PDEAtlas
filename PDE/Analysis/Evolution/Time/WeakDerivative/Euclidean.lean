/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.Analysis.Evolution.Time.Euclidean

/-!
# Euclidean transport of weak time derivatives

The generic weak-time-derivative predicate is formulated directly on `ℝ`.
We transport it to one-dimensional Euclidean coordinates, where the
Euclidean Sobolev and mollification results apply. No Lions–Magenes or
Gelfand-triple assumptions enter this transport.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

open SobolevSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace HasWeakTimeDerivativeOn

/-- Transport a scalarized weak derivative on `ℝ` to the one-dimensional
Euclidean Sobolev formulation. The global weak-derivative witness supplies
the Bochner data required by `SobolevSpace.HasWeakDerivativeOn`. -/
theorem to_hasWeakDerivativeOn
    {f g : ℝ → X}
    (h : HasWeakTimeDerivativeOn Set.univ f g)
    (ell : StrongDual ℝ X) :
    SobolevSpace.HasWeakDerivativeOn (n := 1) Set.univ [0]
      (fun x ↦ ell (f
        ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x)))
      (fun x ↦ ell (g
        ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x))) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  let qf : ℝ → ℝ := ell ∘ f
  let qg : ℝ → ℝ := ell ∘ g
  let fE : ℝ^1 → ℝ := qf ∘ e.symm
  let gE : ℝ^1 → ℝ := qg ∘ e.symm
  have hqf : LocallyIntegrable qf (volume : Measure ℝ) :=
    locallyIntegrableOn_univ.mp
      (ell.locallyIntegrableOn_comp h.locallyIntegrable_f)
  have hqg : LocallyIntegrable qg (volume : Measure ℝ) :=
    locallyIntegrableOn_univ.mp
      (ell.locallyIntegrableOn_comp h.locallyIntegrable_g)
  have hfE : LocallyIntegrable fE (volume : Measure (ℝ^1)) := by
    simpa [fE, e] using locallyIntegrable_comp_oneDimensionalEquiv_symm qf hqf
  have hgE : LocallyIntegrable gE (volume : Measure (ℝ^1)) := by
    simpa [gE, e] using locallyIntegrable_comp_oneDimensionalEquiv_symm qg hqg
  refine ⟨hfE.locallyIntegrableOn Set.univ,
    hgE.locallyIntegrableOn Set.univ, ?_⟩
  intro ψ _hψsupp
  let φ : ℝ → ℝ := ψ.toFun ∘ e
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := ψ.contDiff.comp e.contDiff
  have hφcompact : HasCompactSupport φ :=
    ψ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  have hdist := h.integral_eq ell φ hφ hφcompact (Set.subset_univ _)
  have hderivφ (t : ℝ) :
      deriv φ t = iteratedPartialDeriv (n := 1) [0] ψ.toFun (e t) := by
    have he := deriv_comp_equivOfUnique_symm
      (u := ψ.toFun) (t := t) (ψ.contDiff.differentiable (by simp) _)
    change deriv (ψ.toFun ∘
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) t =
        (∂[0] ψ.toFun)
          ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm t)
    exact he
  have hmp :=
    (PiLp.volume_preserving_toLp (Fin 1)).comp
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)
  have hleft :
      (∫ t : ℝ, qf t * deriv φ t) =
        ∫ x : ℝ^1, fE x * iteratedPartialDeriv (n := 1) [0] ψ.toFun x := by
    have htransport := hmp.integral_comp
      e.toHomeomorph.measurableEmbedding
      (fun x : ℝ^1 ↦ fE x * iteratedPartialDeriv (n := 1) [0] ψ.toFun x)
    rw [← htransport]
    apply integral_congr_ae
    filter_upwards with t
    rw [hderivφ]
    change qf t * iteratedPartialDeriv (n := 1) [0] ψ.toFun (e t) =
      qf (e.symm (e t)) * iteratedPartialDeriv (n := 1) [0] ψ.toFun (e t)
    rw [e.symm_apply_apply]
  have hright :
      (∫ t : ℝ, qg t * φ t) = ∫ x : ℝ^1, gE x * ψ.toFun x := by
    have htransport := hmp.integral_comp
      e.toHomeomorph.measurableEmbedding
      (fun x : ℝ^1 ↦ gE x * ψ.toFun x)
    rw [← htransport]
    apply integral_congr_ae
    filter_upwards with t
    change qg t * ψ.toFun (e t) = qg (e.symm (e t)) * ψ.toFun (e t)
    rw [e.symm_apply_apply]
  have hdist' : (∫ t, qg t * φ t) = -(∫ t, qf t * deriv φ t) := by
    simpa [qf, qg, φ] using hdist
  simp only [SobolevSpace.domainMeasure, Measure.restrict_univ]
  change (∫ x : ℝ^1, fE x *
      iteratedPartialDeriv (n := 1) [0] ψ.toFun x) =
    (-1 : ℝ) ^ ([0] : List (Fin 1)).length *
      ∫ x : ℝ^1, gE x * ψ.toFun x
  rw [← hleft, ← hright, hdist']
  simp

end HasWeakTimeDerivativeOn

end PDE.Analysis.Evolution
