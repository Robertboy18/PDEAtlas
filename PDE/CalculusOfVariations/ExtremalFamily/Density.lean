/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtremalFamily.ClosureFlux

/-!
# Integrability of parameter-graph energies from closure jets

The derivative extensions determine a continuous extension of the graph density.
Compactness of the spatial closure gives integrability of the interior
energy, without differentiating the prescribed exterior values.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis Noether

/-- On a bounded domain the energy of a smooth parameter graph is integrable
when the family and Lagrangian have continuous closure jets. -/
theorem integrableOn_fieldDensity_parameter_graph
    {n m : ℕ} {Ω : Set (ℝ^n)} {J : Set ℝ}
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
    {U : ℝ → ℝ^n → ℝ^m} {θ : ℝ^n → ℝ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hJ : IsOpen J)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hU : ContinuousSecondJetOn (fun p : ℝ^n × ℝ ↦ U p.2 p.1) (Ω ×ˢ J))
    (hθ : ContDiff ℝ 1 θ) (hθJ : MapsTo θ (closure Ω) J) :
    IntegrableOn (fieldDensity L (fun x ↦ U (θ x) x)) Ω := by
  let V (x : ℝ^n) : Matrix (Fin m) (Fin n) ℝ :=
    fun k i ↦ hU.first (x, θ x) (EuclideanSpace.single i 1,
      fderiv ℝ θ x (EuclideanSpace.single i 1)) k
  have hmap : MapsTo (fun x ↦ (x, θ x)) (closure Ω) (closure (Ω ×ˢ J)) := by
    intro x hx
    rw [closure_prod_eq]
    exact ⟨hx, subset_closure (hθJ hx)⟩
  have hAc := hU.continuousOn_first.comp
    (continuousOn_id.prodMk hθ.continuous.continuousOn) hmap
  have hUc := hU.continuousOn.comp
    (continuousOn_id.prodMk hθ.continuous.continuousOn) hmap
  have hVc : ContinuousOn V (closure Ω) := by
    apply continuousOn_pi.mpr
    intro k
    apply continuousOn_pi.mpr
    intro i
    exact (EuclideanSpace.proj k).continuous.comp_continuousOn
      (hAc.clm_apply (continuousOn_const.prodMk
        (((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)))
  have heq (x : ℝ^n) (hx : x ∈ Ω) :
      V x = jacobianMatrix (fun y ↦ U (θ y) y) x := by
    have hd := (hU.hasFDerivAt (hopen.prod hJ) ⟨hx, hθJ (subset_closure hx)⟩).comp x
      ((hasFDerivAt_id x).prodMk ((hθ.differentiable (by norm_num) x).hasFDerivAt))
    dsimp only [Function.comp_def] at hd
    ext k i
    erw [jacobianMatrix_apply_eq_fderiv hd.differentiableAt, hd.fderiv]
    rfl
  have hc : ContinuousOn (fun x ↦ L (V x) (U (θ x) x) x) (closure Ω) := by
    apply hL.continuousOn.comp (hVc.prodMk (hUc.prodMk continuousOn_id))
    intro x hx
    have heq : {a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) | a.2.2 ∈ Ω} =
        univ ×ˢ (univ ×ˢ Ω) := by
      ext a
      change a.2.2 ∈ Ω ↔ (a.1 ∈ univ ∧ a.2.1 ∈ univ ∧ a.2.2 ∈ Ω)
      simp
    rw [heq, closure_prod_eq, closure_prod_eq, closure_univ, closure_univ]
    exact ⟨mem_univ _, mem_univ _, hx⟩
  apply ((hc.integrableOn_compact hbounded.isCompact_closure).mono_set subset_closure).congr
  filter_upwards [ae_restrict_mem hopen.measurableSet] with x hx
  rw [heq x hx]
  rfl

end PDE.CalculusOfVariations.ExtremalFamily
