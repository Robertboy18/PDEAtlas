/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Returning a one-dimensional Euclidean weak pair to the real line

The canonical coordinate equivalence preserves volume. Transporting compactly
supported smooth tests through it gives the real weak-derivative identity,
including local integrability, from the Euclidean Sobolev relation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- The inverse coordinate map from the real line preserves volume. -/
theorem measurePreserving_equivOfUnique_symm :
    MeasurePreserving (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
      (volume : Measure ℝ) (volume : Measure (ℝ^1)) :=
  (PiLp.volume_preserving_toLp (Fin 1)).comp
    ((volume_preserving_funUnique (Fin 1) ℝ).symm _)

/-- Local integrability is preserved when returning from the Euclidean line
to ordinary real coordinates. -/
theorem locallyIntegrable_comp_equivOfUnique_symm
    {f : ℝ^1 → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact (measurePreserving_equivOfUnique_symm.integrableOn_image
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toHomeomorph.measurableEmbedding).mp
      (hf.integrableOn_isCompact
        (hK.image (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.continuous))

/-- A Euclidean weak derivative on the whole line gives the real
weak-derivative identity after the canonical coordinate change. -/
theorem hasWeakTimeDerivativeOn_of_euclidean {f g : ℝ^1 → ℝ}
    (h : SobolevSpace.HasWeakDerivativeOn univ [0] f g) :
    HasWeakTimeDerivativeOn univ
      (f ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm)
      (g ∘ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  refine ⟨(locallyIntegrable_comp_equivOfUnique_symm
      (locallyIntegrableOn_univ.mp h.locallyIntegrable_f)).locallyIntegrableOn univ,
    (locallyIntegrable_comp_equivOfUnique_symm
      (locallyIntegrableOn_univ.mp h.locallyIntegrable_g)).locallyIntegrableOn univ, ?_⟩
  intro ell φ hφ hφcompact _hsupp
  let ψ : TestFunction (⊤ : TopologicalSpace.Opens (ℝ^1)) ℝ ⊤ :=
    ⟨φ ∘ e.symm, hφ.comp e.symm.contDiff,
      hφcompact.comp_homeomorph e.symm.toHomeomorph, subset_univ _⟩
  have hpartial (t : ℝ) :
      (∂[0] ψ.toFun) (e t) = deriv φ t := by
    have hd := deriv_comp_equivOfUnique_symm ψ.toFun t
      (ψ.contDiff.differentiable (by simp) _)
    have hcomp : ψ.toFun ∘ e = φ := by
      funext x
      exact congrArg φ (e.symm_apply_apply x)
    change deriv (ψ.toFun ∘ e) t = _ at hd
    rw [hcomp] at hd
    exact hd.symm
  have htest := h.integral_identity ψ (subset_univ _)
  simp only [SobolevSpace.domainMeasure, Measure.restrict_univ,
    iteratedPartialDeriv, List.length_singleton, pow_one, neg_one_mul] at htest
  have hleft := measurePreserving_equivOfUnique_symm.integral_comp
    e.toHomeomorph.measurableEmbedding (fun x ↦ f x * (∂[0] ψ.toFun) x)
  have hright := measurePreserving_equivOfUnique_symm.integral_comp
    e.toHomeomorph.measurableEmbedding (fun x ↦ g x * ψ.toFun x)
  rw [← hleft, ← hright] at htest
  change (∫ t, f (e t) * (∂[0] ψ.toFun) (e t)) =
    -(∫ t, g (e t) * ψ.toFun (e t)) at htest
  have hscalar : (∫ t, g (e t) * φ t) = -(∫ t, f (e t) * deriv φ t) := by
    have htest' : (∫ t, f (e t) * deriv φ t) = -(∫ t, g (e t) * φ t) := by
      simpa only [hpartial, ψ, Function.comp_apply, TestFunction.coe_mk,
        e.symm_apply_apply] using htest
    linarith
  have hell (r : ℝ) : ell r = ell 1 * r := by
    calc
      ell r = ell (r • (1 : ℝ)) := by simp
      _ = r • ell 1 := ell.map_smul r 1
      _ = ell 1 * r := mul_comm _ _
  have hprod (q η : ℝ → ℝ) :
      (∫ t, ell (q t) * η t) = ell 1 * ∫ t, q t * η t := by
    calc
      _ = ∫ t, ell 1 * (q t * η t) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [hell (q t), mul_assoc]
      _ = _ := integral_const_mul _ _
  change (∫ t, ell (g (e t)) * φ t) = -(∫ t, ell (f (e t)) * deriv φ t)
  rw [hprod, hprod, hscalar]
  ring

end PDE.Analysis.Evolution
