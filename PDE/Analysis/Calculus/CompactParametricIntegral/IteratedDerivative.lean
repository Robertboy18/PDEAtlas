/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.CompactParametricIntegral

/-!
# Integrating finite spatial jets

Jointly continuous actual spatial jets commute with integration over a compact
index space. The index carries no differentiable structure. Compactness supplies
the local domination needed at each derivative order.
-/

@[expose] public noncomputable section

open MeasureTheory

variable {T E F : Type*} [TopologicalSpace T] [CompactSpace T]
  [MeasurableSpace T] [OpensMeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure T} [IsFiniteMeasure μ] {k : ℕ} {f : E → T → F}

namespace PDE

/-- The integral of a spatial jet has the integral of its actual derivative
as derivative; no derivative in the compact index is required. -/
theorem hasFDerivAt_integral_iteratedFDeriv_of_compact
    (hf : ∀ t, ContDiff ℝ k (fun x ↦ f x t))
    (hjet : ∀ j ≤ k, Continuous
      (fun p : E × T ↦ iteratedFDeriv ℝ j (fun x ↦ f x p.2) p.1))
    {j : ℕ} (hj : j < k) (x : E) :
    HasFDerivAt (fun y ↦ ∫ t, iteratedFDeriv ℝ j (fun z ↦ f z t) y ∂μ)
      (∫ t, fderiv ℝ (iteratedFDeriv ℝ j (fun z ↦ f z t)) x ∂μ) x := by
  refine hasFDerivAt_integral_of_compact
    (f := fun y t ↦ iteratedFDeriv ℝ j (fun z ↦ f z t) y)
    (D := fun y t ↦ fderiv ℝ (iteratedFDeriv ℝ j (fun z ↦ f z t)) y)
    (hjet j hj.le) ?_ ?_ x
  · exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E)
      F).continuous.comp (hjet (j + 1) hj)
  · intro y t
    exact ((hf t).differentiable_iteratedFDeriv (by exact_mod_cast hj) y).hasFDerivAt

/-- Every available finite spatial derivative commutes with compact integration. -/
theorem iteratedFDeriv_integral_of_compact
    (hf : ∀ t, ContDiff ℝ k (fun x ↦ f x t))
    (hjet : ∀ j ≤ k, Continuous
      (fun p : E × T ↦ iteratedFDeriv ℝ j (fun x ↦ f x p.2) p.1))
    {j : ℕ} (hj : j ≤ k) (x : E) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ t, f y t ∂μ) x =
      ∫ t, iteratedFDeriv ℝ j (fun y ↦ f y t) x ∂μ := by
  induction j generalizing x with
  | zero =>
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (E := F) (F := E [×0]→L[ℝ] F)
        (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv
        (fun t ↦ f x t)).symm
  | succ j ih =>
    have heq := funext (ih (Nat.le_of_succ_le hj))
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, heq,
      (hasFDerivAt_integral_iteratedFDeriv_of_compact hf hjet hj x).fderiv]
    simpa only [LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      iteratedFDeriv_succ_eq_comp_left, Function.comp_apply] using
      (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := μ)
        (E := E →L[ℝ] E [×j]→L[ℝ] F)
        (F := E [×(j + 1)]→L[ℝ] F)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ E)
          F).symm.toContinuousLinearEquiv
        (fun t ↦ fderiv ℝ (iteratedFDeriv ℝ j (fun z ↦ f z t)) x)).symm

/-- Continuous spatial jets through order `k` give `C^k` compact integrals. -/
theorem contDiff_integral_of_compact
    (hf : ∀ t, ContDiff ℝ k (fun x ↦ f x t))
    (hjet : ∀ j ≤ k, Continuous
      (fun p : E × T ↦ iteratedFDeriv ℝ j (fun x ↦ f x p.2) p.1)) :
    ContDiff ℝ k (fun x ↦ ∫ t, f x t ∂μ) := by
  apply contDiff_nat_iff_continuous_differentiable.mpr
  constructor
  · intro j hj
    simp_rw [iteratedFDeriv_integral_of_compact hf hjet hj]
    exact continuous_integral_of_compact (hjet j hj)
  · intro j hj
    have heq := funext (iteratedFDeriv_integral_of_compact (μ := μ) hf hjet hj.le)
    rw [heq]
    exact fun x ↦ (hasFDerivAt_integral_iteratedFDeriv_of_compact hf hjet hj x).differentiableAt

/-- Compact integration preserves joint continuity of every available spatial jet
with an additional continuous parameter. -/
theorem continuous_iteratedFDeriv_integral_family
    {A : Type*} [TopologicalSpace A] [FirstCountableTopology A] {f : A → E → T → F}
    (hf : ∀ a t, ContDiff ℝ k (fun x ↦ f a x t))
    (hjet : ∀ j ≤ k, Continuous
      (fun p : (A × E) × T ↦ iteratedFDeriv ℝ j (fun x ↦ f p.1.1 x p.2) p.1.2))
    {j : ℕ} (hj : j ≤ k) :
    Continuous (fun p : A × E ↦
      iteratedFDeriv ℝ j (fun x ↦ ∫ t, f p.1 x t ∂μ) p.2) := by
  have heq (a : A) (x : E) := iteratedFDeriv_integral_of_compact (μ := μ) (hf a)
    (fun i hi ↦ (hjet i hi).comp
      ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)) hj x
  simp_rw [heq]
  exact continuous_integral_of_compact (hjet j hj)

end PDE
