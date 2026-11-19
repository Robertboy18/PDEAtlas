/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Closure
public import PDE.Analysis.Calculus.Jet.ParameterTrace
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Spatial derivatives on the closed faces of a slab

A raw continuous closure jet determines the spatial derivatives on both
time faces. Compact rectangles supply the uniform derivative convergence;
no differentiability across either time face is used.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.ContinuousSecondJetOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {a b : ℝ} {f : ℝ × ℝ → E}

/-- The continuous spatial first-jet trace is the spatial derivative at
every time in the closed interval, including both endpoints. -/
theorem hasDerivAt_spatial_of_mem_Icc
    (h : ContinuousSecondJetOn f (Ioo a b ×ˢ univ)) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    HasDerivAt (fun y ↦ f (t, y)) (h.first (t, x) (0, 1)) x := by
  have hclosure : closure (Ioo a b ×ˢ (univ : Set ℝ)) = Icc a b ×ˢ univ := by
    rw [closure_prod_eq, closure_Ioo hab.ne, closure_univ]
  have hf : ContinuousOn f (Icc a b ×ˢ univ) := hclosure ▸ h.continuousOn
  have hd : ContinuousOn (fun p ↦ h.first p (0, 1)) (Icc a b ×ˢ univ) :=
    (hclosure ▸ h.continuousOn_first).clm_apply continuousOn_const
  have hspatial : ∀ s ∈ Ioo a b, ∀ y : ℝ,
      HasDerivAt (fun z ↦ f (s, z)) (h.first (s, y) (0, 1)) y := by
    intro s hs y
    exact (h.hasFDerivAt (isOpen_Ioo.prod isOpen_univ) ⟨hs, mem_univ y⟩).comp_hasDerivAt y
      ((hasDerivAt_const y s).prodMk (hasDerivAt_id y))
  apply hasDerivAt_parameter_of_mem_closure
    (A := Ioo a b) (F := fun s y ↦ f (s, y))
    (D := fun s y ↦ h.first (s, y) (0, 1))
    (a := x - 1) (b := x + 1)
  · rw [closure_Ioo hab.ne]
    exact isCompact_Icc
  · rw [closure_Ioo hab.ne]
    exact hf.mono (prod_mono_right (subset_univ _))
  · rw [closure_Ioo hab.ne]
    exact hd.mono (prod_mono_right (subset_univ _))
  · intro s hs y _
    exact hspatial s hs y
  · rwa [closure_Ioo hab.ne]
  · constructor <;> linarith

/-- Prescribed initial values determine their spatial slope from the closure jet,
without a separate initial-derivative hypothesis. -/
theorem hasDerivAt_initial_data
    (h : ContinuousSecondJetOn f (Ioo a b ×ˢ univ)) (hab : a < b)
    {g : ℝ → E} (hinit : ∀ x, f (a, x) = g x) (x : ℝ) :
    HasDerivAt g (h.first (a, x) (0, 1)) x := by
  have heq : (fun y ↦ f (a, y)) = g := funext hinit
  rw [← heq]
  exact h.hasDerivAt_spatial_of_mem_Icc hab ⟨le_rfl, hab.le⟩ x

end PDE.Analysis.ContinuousSecondJetOn
