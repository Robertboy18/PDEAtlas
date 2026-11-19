/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative
import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrder

/-!
# Product-space closure of absolutely continuous line representatives

This is the measure-theoretic closure step in the ACL theorem.
Suppose integrable value/derivative pairs on a product space converge in
`L¹`, and every approximating one-dimensional slice equals its canonical
normalized primitive. A diagonal Fubini subsequence then shows that almost
every limiting slice also equals its canonical absolutely continuous
representative.

The ACL construction in `Slicing.ACL` specializes this product-space theorem
with Euclidean Sobolev density and coordinate differentiation.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Slices

open Filter MeasureTheory
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]
  {μ : Measure α} [SFinite μ]

/-- Product-space `L¹` closure of canonical absolutely continuous line
representatives. -/
theorem ae_lineRepresentative_eq_of_prod_L1_approximation
    {u g : α × ℝ → ℝ} {u_m g_m : ℕ → α × ℝ → ℝ}
    (hu : Integrable u (μ.prod volume))
    (hg : Integrable g (μ.prod volume))
    (hu_m : ∀ m, Integrable (u_m m) (μ.prod volume))
    (hg_m : ∀ m, Integrable (g_m m) (μ.prod volume))
    (huconv : Tendsto
      (fun m ↦ eLpNorm (u_m m - u) 1 (μ.prod volume))
      atTop (𝓝 0))
    (hgconv : Tendsto
      (fun m ↦ eLpNorm (g_m m - g) 1 (μ.prod volume))
      atTop (𝓝 0))
    (hrep : ∀ m y,
      lineRepresentative (fun t ↦ u_m m (y, t))
        (fun t ↦ g_m m (y, t)) =
      fun t ↦ u_m m (y, t)) :
    ∀ᵐ y ∂μ,
      Integrable (fun t ↦ u (y, t)) volume ∧
      Integrable (fun t ↦ g (y, t)) volume ∧
      lineRepresentative (fun t ↦ u (y, t)) (fun t ↦ g (y, t))
        =ᵐ[volume] fun t ↦ u (y, t) := by
  let U : ℕ → α × ℝ → ℝ := fun m z ↦ |u_m m z - u z|
  have hUInt (m : ℕ) : Integrable (U m) (μ.prod volume) := by
    simpa [U, Pi.sub_apply] using ((hu_m m).sub hu).abs
  have hUconv :
      Tendsto (fun m ↦ eLpNorm (U m) 1 (μ.prod volume))
        atTop (𝓝 0) := by
    convert huconv using 1
    funext m
    calc
      eLpNorm (U m) 1 (μ.prod volume) =
          eLpNorm (fun z ↦ ‖(u_m m - u) z‖) 1
            (μ.prod volume) := by
            simp [U, Real.norm_eq_abs]
      _ = eLpNorm (u_m m - u) 1 (μ.prod volume) :=
        eLpNorm_norm _ ((hu_m m).sub hu).aestronglyMeasurable
  obtain ⟨ns, hns, huSlice⟩ :=
    exists_subseq_ae_integral_prod_right_tendsto_zero U hUInt hUconv
  let G : ℕ → α × ℝ → ℝ := fun i z ↦ |g_m (ns i) z - g z|
  have hGInt (i : ℕ) : Integrable (G i) (μ.prod volume) := by
    simpa [G, Pi.sub_apply] using ((hg_m (ns i)).sub hg).abs
  have hGconv :
      Tendsto (fun i ↦ eLpNorm (G i) 1 (μ.prod volume))
        atTop (𝓝 0) := by
    have hsub := hgconv.comp hns.tendsto_atTop
    convert hsub using 1
    funext i
    calc
      eLpNorm (G i) 1 (μ.prod volume) =
          eLpNorm (fun z ↦ ‖(g_m (ns i) - g) z‖) 1
            (μ.prod volume) := by
            simp [G, Real.norm_eq_abs]
      _ = eLpNorm (g_m (ns i) - g) 1 (μ.prod volume) :=
        eLpNorm_norm _ ((hg_m (ns i)).sub hg).aestronglyMeasurable
  obtain ⟨ks, hks, hgSlice⟩ :=
    exists_subseq_ae_integral_prod_right_tendsto_zero G hGInt hGconv
  have huSlices :
      ∀ᵐ y ∂μ, Integrable (fun t ↦ u (y, t)) volume :=
    hu.prod_right_ae
  have hgSlices :
      ∀ᵐ y ∂μ, Integrable (fun t ↦ g (y, t)) volume :=
    hg.prod_right_ae
  have hu_mSlices :
      ∀ᵐ y ∂μ, ∀ m, Integrable (fun t ↦ u_m m (y, t)) volume := by
    rw [ae_all_iff]
    intro m
    exact (hu_m m).prod_right_ae
  have hg_mSlices :
      ∀ᵐ y ∂μ, ∀ m, Integrable (fun t ↦ g_m m (y, t)) volume := by
    rw [ae_all_iff]
    intro m
    exact (hg_m m).prod_right_ae
  filter_upwards
    [huSlices, hgSlices, hu_mSlices, hg_mSlices, huSlice, hgSlice]
      with y huy hgy huym hgym huyconv hgyconv
  refine ⟨huy, hgy, ?_⟩
  apply ae_eq_lineRepresentative_of_integral_abs_tendsto_zero
    huy hgy
    (fun i ↦ huym (ns (ks i)))
    (fun i ↦ hgym (ns (ks i)))
  · simpa [U, Function.comp_def] using
      huyconv.comp hks.tendsto_atTop
  · simpa [G] using hgyconv
  · intro i
    exact hrep (ns (ks i)) y

end SobolevSpace.Slices
