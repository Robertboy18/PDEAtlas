/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.CompactParametricIntegral
public import PDE.FDeriv.Calculus

/-!
# Continuous families of spatially C¹ functions

A topological parameter need not carry a derivative. Joint continuity of the
spatial first derivatives suffices for algebraic operations and differentiation
under integration over a compact parameter space.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common PDE.FDeriv

namespace PDE.Analysis.Calculus

variable {n : ℕ}

/-- Joint continuity of a scalar field and its first spatial derivatives.
The parameter needs only a topology; no parameter derivative is assumed. -/
def JointC1 {T : Type*} [TopologicalSpace T] (f : T → (ℝ^n → ℝ)) : Prop :=
  (∀ t, ContDiff ℝ 1 (f t)) ∧ Continuous (fun p : T × (ℝ^n) ↦ f p.1 p.2) ∧
    ∀ i : Fin n, Continuous (fun p : T × (ℝ^n) ↦ (∂[i] (f p.1)) p.2)

/-- Joint spatial C¹ regularity is preserved by addition. -/
theorem JointC1.add {T : Type*} [TopologicalSpace T]
    {f g : T → (ℝ^n → ℝ)} (hf : JointC1 f) (hg : JointC1 g) :
    JointC1 (fun t x ↦ f t x + g t x) := by
  refine ⟨fun t ↦ (hf.1 t).add (hg.1 t), hf.2.1.add hg.2.1, fun i ↦ ?_⟩
  have heq : (fun p : T × (ℝ^n) ↦ (∂[i] (fun x ↦ f p.1 x + g p.1 x)) p.2) =
      fun p ↦ (∂[i] (f p.1)) p.2 + (∂[i] (g p.1)) p.2 := by
    funext p
    exact partialDeriv_add ((hf.1 p.1).differentiable (by norm_num) p.2)
      ((hg.1 p.1).differentiable (by norm_num) p.2)
  rw [heq]
  exact (hf.2.2 i).add (hg.2.2 i)

/-- Joint spatial C¹ regularity is preserved by subtraction. -/
theorem JointC1.sub {T : Type*} [TopologicalSpace T]
    {f g : T → (ℝ^n → ℝ)} (hf : JointC1 f) (hg : JointC1 g) :
    JointC1 (fun t x ↦ f t x - g t x) := by
  refine ⟨fun t ↦ (hf.1 t).sub (hg.1 t), hf.2.1.sub hg.2.1, fun i ↦ ?_⟩
  have heq : (fun p : T × (ℝ^n) ↦ (∂[i] (fun x ↦ f p.1 x - g p.1 x)) p.2) =
      fun p ↦ (∂[i] (f p.1)) p.2 - (∂[i] (g p.1)) p.2 := by
    funext p
    exact partialDeriv_sub ((hf.1 p.1).differentiable (by norm_num) p.2)
      ((hg.1 p.1).differentiable (by norm_num) p.2)
  rw [heq]
  exact (hf.2.2 i).sub (hg.2.2 i)

/-- Joint spatial C¹ regularity is preserved by multiplication. -/
theorem JointC1.mul {T : Type*} [TopologicalSpace T]
    {f g : T → (ℝ^n → ℝ)} (hf : JointC1 f) (hg : JointC1 g) :
    JointC1 (fun t x ↦ f t x * g t x) := by
  refine ⟨fun t ↦ (hf.1 t).mul (hg.1 t), hf.2.1.mul hg.2.1, fun i ↦ ?_⟩
  have heq : (fun p : T × (ℝ^n) ↦ (∂[i] (fun x ↦ f p.1 x * g p.1 x)) p.2) =
      fun p ↦ (∂[i] (f p.1)) p.2 * g p.1 p.2 +
        f p.1 p.2 * (∂[i] (g p.1)) p.2 := by
    funext p
    exact partialDeriv_mul ((hf.1 p.1).differentiable (by norm_num) p.2)
      ((hg.1 p.1).differentiable (by norm_num) p.2)
  rw [heq]
  exact ((hf.2.2 i).mul hg.2.1).add (hf.2.1.mul (hg.2.2 i))

/-- A fixed C¹ spatial function has jointly continuous first derivatives. -/
theorem JointC1.fixed {T : Type*} [TopologicalSpace T]
    {f : (ℝ^n → ℝ)} (hf : ContDiff ℝ 1 f) : JointC1 (fun _ : T ↦ f) := by
  refine ⟨fun _ ↦ hf, hf.continuous.comp continuous_snd, fun i ↦ ?_⟩
  exact (contDiff_partialDeriv_of_succ (m := 0) hf).continuous.comp continuous_snd

/-- A continuous parameter function is spatially constant and jointly C¹. -/
theorem JointC1.timeConst {T : Type*} [TopologicalSpace T]
    {a : T → ℝ} (ha : Continuous a) : JointC1 (n := n) (fun t _ ↦ a t) := by
  refine ⟨fun _ ↦ contDiff_const, ha.comp continuous_fst, fun i ↦ ?_⟩
  simp only [partialDeriv_const]
  exact continuous_const

/-- Joint continuity of the coordinate derivatives gives continuity of the Fréchet derivative. -/
theorem JointC1.continuous_fderiv {T : Type*} [TopologicalSpace T]
    {f : T → (ℝ^n → ℝ)} (hf : JointC1 f) :
    Continuous (fun p : T × (ℝ^n) ↦ fderiv ℝ (f p.1) p.2) := by
  have heq : (fun p : T × (ℝ^n) ↦ fderiv ℝ (f p.1) p.2) =
      fun p ↦ ∑ i : Fin n, (∂[i] (f p.1)) p.2 •
        PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i := by
    funext p
    ext v
    rw [fderiv_apply_eq_sum_smul_partialDeriv]
    simp [mul_comm]
  rw [heq]
  exact continuous_finsetSum _ fun i _ ↦ (hf.2.2 i).smul continuous_const

/-- Integration over a compact parameter space commutes with the spatial Fréchet derivative. -/
theorem JointC1.hasFDerivAt_integral {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [MeasurableSpace T] [BorelSpace T]
    (η : Measure T) [IsFiniteMeasure η] {f : T → (ℝ^n → ℝ)} (hf : JointC1 f) (x : (ℝ^n)) :
    HasFDerivAt (fun y ↦ ∫ t, f t y ∂η) (∫ t, fderiv ℝ (f t) x ∂η) x := by
  exact hasFDerivAt_integral_of_compact (μ := η)
    (f := fun y t ↦ f t y) (D := fun y t ↦ fderiv ℝ (f t) y)
    (hf.2.1.comp continuous_swap)
    (hf.continuous_fderiv.comp continuous_swap)
    (fun y t ↦ ((hf.1 t).differentiable one_ne_zero y).hasFDerivAt) x

/-- The integral of a jointly spatially C¹ field over a compact parameter space is C¹. -/
theorem JointC1.integral {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] (η : Measure T) [IsFiniteMeasure η]
    {f : T → (ℝ^n → ℝ)} (hf : JointC1 f) :
    ContDiff ℝ 1 (fun x ↦ ∫ t, f t x ∂η) := by
  exact contDiff_one_integral_of_compact (μ := η)
    (f := fun x t ↦ f t x) (D := fun x t ↦ fderiv ℝ (f t) x)
    (hf.2.1.comp continuous_swap)
    (hf.continuous_fderiv.comp continuous_swap)
    (fun y t ↦ ((hf.1 t).differentiable one_ne_zero y).hasFDerivAt)

/-- Coordinate differentiation commutes with integration over the compact parameter space. -/
theorem JointC1.partialDeriv_integral {T : Type*} [TopologicalSpace T]
    [CompactSpace T] [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (η : Measure T) [IsFiniteMeasure η] {f : T → (ℝ^n → ℝ)}
    (hf : JointC1 f) (i : Fin n) (x : (ℝ^n)) :
    (∂[i] (fun y ↦ ∫ t, f t y ∂η)) x = ∫ t, (∂[i] (f t)) x ∂η := by
  have hc : Continuous (fun t ↦ fderiv ℝ (f t) x) :=
    hf.continuous_fderiv.comp (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun t ↦ fderiv ℝ (f t) x) η := by
    simpa only [MeasureTheory.integrableOn_univ] using
      hc.continuousOn.integrableOn_compact (K := Set.univ) isCompact_univ
  unfold partialDeriv
  rw [(hf.hasFDerivAt_integral η x).fderiv]
  exact ContinuousLinearMap.integral_apply hi _

/-- Jointly continuous spatial jets through order two give jointly C¹ first derivatives. -/
theorem JointC1.of_iteratedPartialDeriv {T : Type*} [TopologicalSpace T] (f : T → (ℝ^n → ℝ))
    (hf : ∀ t, ContDiff ℝ 2 (f t))
    (hjet : ∀ α : List (Fin n), α.length ≤ 2 →
      Continuous (fun p : T × (ℝ^n) ↦ iteratedPartialDeriv α (f p.1) p.2))
    (α : List (Fin n)) (hα : α.length ≤ 1) :
    JointC1 (fun t ↦ iteratedPartialDeriv α (f t)) := by
  refine ⟨fun t ↦ ?_, hjet α (by omega), fun i ↦ ?_⟩
  · exact (contDiff_iteratedPartialDeriv_of_le (k := 2) (hf t) α (by omega)).of_le (by
      exact_mod_cast (show 1 ≤ 2 - α.length by omega))
  · exact hjet (i :: α) (by simp only [List.length_cons]; omega)

end PDE.Analysis.Calculus
