/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval

/-!
# Parameter families near a finite trajectory

Keep the parameter as an extra state variable with derivative zero. The smooth
flow near the augmented trajectory then supplies one neighborhood of parameters
and initial states for the entire time interval. Uniqueness for the zero field
shows that the parameter stays fixed, so the projected curves solve the original
parameter-dependent equation.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis.ODE

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth parameter-dependent field admits a jointly smooth family near any
trajectory on a compact time interval. One open neighborhood controls both the
parameter and the initial state throughout that interval. -/
theorem exists_contDiff_infty_parameterized_family_near_solution_Icc
    (v : P × E → E) (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (p₀ : P) (γ : ℝ → E) (hγ : ContinuousOn γ (Icc a b))
    (hγode : ∀ t ∈ Ioo a b, HasDerivAt γ (v (p₀, γ t)) t)
    (q₀ : E) (hγ₀ : γ 0 = q₀) :
    ∃ (F : ℝ × (P × E) → E) (U : Set (P × E)),
      IsOpen U ∧ (p₀, q₀) ∈ U ∧ ContDiff ℝ ∞ F ∧
      (∀ q, F (0, q) = q.2) ∧
      EqOn (fun t ↦ F (t, (p₀, q₀))) γ (Icc a b) ∧
      ∀ q ∈ U, ∀ t ∈ Icc a b,
        HasDerivAt (fun s ↦ F (s, q)) (v (q.1, F (t, q))) t := by
  let w : P × E → P × E := fun q ↦ (0, v q)
  have hw : ContDiff ℝ ∞ w := contDiff_const.prodMk hv
  obtain ⟨Φ, U, hU, hmem, hΦ, hsame, hΦode⟩ :=
    exists_contDiff_infty_flow_near_solution_Icc w hw ha hb
      (fun t ↦ (p₀, γ t)) (continuousOn_const.prodMk hγ)
      (fun t ht ↦ (hasDerivAt_const t p₀).prodMk (hγode t ht))
      (p₀, q₀) (Prod.ext rfl hγ₀)
  have hparameter (q : P × E) (hq : q ∈ U) :
      EqOn (fun t ↦ (Φ t q).1) (fun _ ↦ q.1) (Icc a b) := by
    apply PDE.Analysis.Evolution.eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls
      (F := fun _ : P ↦ 0)
      (fun _ _ ↦ ⟨0, (LipschitzWith.const (0 : P)).lipschitzOnWith⟩)
      (show (0 : ℝ) ∈ Ioo a b from ⟨ha, hb⟩)
      ((hΦ.continuous.comp (continuous_id.prodMk continuous_const)).fst.continuousOn)
      (fun t ht ↦ (hΦode q hq t (Ioo_subset_Icc_self ht)).fst)
      continuousOn_const (fun t _ ↦ hasDerivAt_const t q.1)
    exact congrArg Prod.fst (Φ.map_zero_apply q)
  refine ⟨fun p ↦ (Φ p.1 p.2).2, U, hU, hmem, hΦ.snd, ?_, ?_, ?_⟩
  · intro q
    exact congrArg Prod.snd (Φ.map_zero_apply q)
  · intro t ht
    exact congrArg Prod.snd (hsame ht)
  · intro q hq t ht
    have hparam : (Φ t q).1 = q.1 := hparameter q hq ht
    have hstate : HasDerivAt (fun s ↦ (Φ s q).2) (v (Φ t q)) t :=
      (ContinuousLinearMap.snd ℝ P E).hasFDerivAt.comp_hasDerivAt t (hΦode q hq t ht)
    simpa only [← hparam, Prod.mk.eta] using hstate

end PDE.Analysis.ODE
