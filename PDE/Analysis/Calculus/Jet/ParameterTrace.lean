/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Parameter derivatives at boundary indices

A continuous extension of a parameter derivative remains the actual parameter
derivative at a limiting spatial index. Uniform convergence on a compact time
interval provides this conclusion without differentiability across the spatial
boundary.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

variable {X E : Type*} [UniformSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : Set X} {a b : ℝ} {F D : X → ℝ → E}

/-- Extend an actual time derivative to the closure of its spatial indices. -/
theorem hasDerivAt_parameter_of_mem_closure
    (hA : IsCompact (closure A))
    (hF : ContinuousOn F.uncurry (closure A ×ˢ Icc a b))
    (hD : ContinuousOn D.uncurry (closure A ×ˢ Icc a b))
    (hd : ∀ x ∈ A, ∀ t ∈ Ioo a b, HasDerivAt (F x) (D x t) t)
    {x : X} (hx : x ∈ closure A) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (F x) (D x t) t := by
  have : NeBot (𝓝[A] x) := mem_closure_iff_nhdsWithin_neBot.mp hx
  have hU := (hA.prod isCompact_Icc).uniformContinuousOn_of_continuous hD
  have hlim : TendstoUniformlyOn D (D x) (𝓝[A] x) (Ioo a b) :=
    ((hU.tendstoUniformlyOn hx).tendstoUniformlyOnFilter.mono_left
      (nhdsWithin_mono x subset_closure)).tendstoUniformlyOn.mono Ioo_subset_Icc_self
  apply hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hlim
    (eventually_mem_nhdsWithin.mono hd) _ ht
  intro s hs
  have hc : ContinuousOn (fun y ↦ F y s) (closure A) :=
    hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hy ↦ ⟨hy, Ioo_subset_Icc_self hs⟩)
  exact (hc x hx).mono_left (nhdsWithin_mono x subset_closure)

/-- Constant boundary values force the continuous time-derivative trace to vanish. -/
theorem parameterDerivative_eq_zero_of_constant
    (hA : IsCompact (closure A))
    (hF : ContinuousOn F.uncurry (closure A ×ˢ Icc a b))
    (hD : ContinuousOn D.uncurry (closure A ×ˢ Icc a b))
    (hd : ∀ x ∈ A, ∀ t ∈ Ioo a b, HasDerivAt (F x) (D x t) t)
    {x : X} (hx : x ∈ closure A) {c : E}
    (hc : ∀ t ∈ Ioo a b, F x t = c) {t : ℝ} (ht : t ∈ Ioo a b) :
    D x t = 0 := by
  have h := hasDerivAt_parameter_of_mem_closure hA hF hD hd hx ht
  have heq : F x =ᶠ[𝓝 t] fun _ ↦ c := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hc s hs
  exact h.unique ((hasDerivAt_const t c).congr_of_eventuallyEq heq)

end PDE.Analysis
