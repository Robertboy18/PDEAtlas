/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Weak.Integral
public import PDE.Analysis.Evolution.Time.WeakDerivative.InitialPrimitive

/-!
# Passing primitive identities through weak velocity limits

Strong convergence of states and weak Bochner `L²` convergence of velocities preserve
the fundamental theorem at every time, including both endpoints. Constant-vector
indicator tests identify the integral in an arbitrary Hilbert space.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A pointwise strong limit of primitives is the primitive of a weak `L²` limit.
The conclusion concerns the prescribed limiting state, rather than a replacement
representative or an almost-everywhere choice of its values. -/
theorem eq_initial_add_integral_of_tendsto_strong_weak_L2
    {a b : ℝ} {l : Filter ι} [l.NeBot]
    {u : ι → ℝ → H} {u₀ : ℝ → H} {q : H}
    {v : ι → Lp H 2 (volume.restrict (Ioc a b))}
    {v₀ : Lp H 2 (volume.restrict (Ioc a b))}
    (hu : ∀ t ∈ Icc a b, Tendsto (fun i ↦ u i t) l (𝓝 (u₀ t)))
    (hv : Tendsto
      (fun i ↦ toWeakSpace ℝ (Lp H 2 (volume.restrict (Ioc a b))) (v i)) l
      (𝓝 (toWeakSpace ℝ (Lp H 2 (volume.restrict (Ioc a b))) v₀)))
    (hFTC : ∀ᶠ i in l, ∀ t ∈ Icc a b, u i t = q + ∫ r in a..t, v i r)
    {t : ℝ} (ht : t ∈ Icc a b) :
    u₀ t = q + ∫ r in a..t, v₀ r := by
  have hsubset : Ioc a t ⊆ Ioc a b := Ioc_subset_Ioc_right ht.2
  have hrestrict :
      (volume.restrict (Ioc a b)).restrict (Ioc a t) = volume.restrict (Ioc a t) :=
    Measure.restrict_restrict_of_subset hsubset
  apply ext_inner_left ℝ
  intro h
  have hint := tendsto_inner_setIntegral_of_tendsto_weak_L2 hv
    (s := Ioc a t) measurableSet_Ioc (measure_ne_top _ _) h
  simp only [hrestrict, ← intervalIntegral.integral_of_le ht.1] at hint
  have hsum : Tendsto
      (fun i ↦ inner ℝ h (q + ∫ r in a..t, v i r)) l
      (𝓝 (inner ℝ h (q + ∫ r in a..t, v₀ r))) := by
    simpa only [inner_add_right] using hint.const_add (inner ℝ h q)
  exact tendsto_nhds_unique
    (show Tendsto (fun i ↦ inner ℝ h (u i t)) l (𝓝 (inner ℝ h (u₀ t))) from
      tendsto_const_nhds.inner (hu t ht))
    (hsum.congr' (hFTC.mono fun i hi ↦ congrArg (inner ℝ h) (hi t ht).symm))

end PDE.Analysis.Evolution
