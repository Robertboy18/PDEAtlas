/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import PDE.Analysis.MeasureTheory.Lp.Continuous
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Endpoint

/-!
# Poincaré's inequality for `C¹` functions

Poincaré's inequality with the mean is proved for the elements of `W^{1,p}(Ω)`. For a `C¹`
function `v` on the whole space it reads, in terms of `v` and its Fréchet derivative and with no
Sobolev space in the statement,

`‖v - ⨍_Ω v‖_{Lᵖ(Ω)} ≤ C ‖Dv‖_{Lᵖ(Ω)}`,

for a bounded connected open set `Ω ⊆ ℝ^(n+1)` with `C¹` graph boundary, every `1 ≤ p ≤ ∞` and
a constant `C` independent of `v`. Functions that are `C¹` on `Ω` only, with a derivative in
`Lᵖ(Ω)`, are not treated; the proof would be the same once such a function is known to be in
`W^{1,p}(Ω)`.

## Main results

* `SobolevSpace.exists_eLpNorm_sub_average_le`: the inequality above.

## How it works

Restricted to `Ω`, a `C¹` function on the whole space is an element of `W^{1,p}(Ω)`
(`SobolevSpace.GraphSpace.exists_of_weakGradient`): it and its derivative are bounded on the
compact closure of `Ω`, and its classical partial derivatives are the weak ones. Its weak
gradient is the vector that represents `Dv`, so the two have the same norm at every point, and
`SobolevSpace.GraphSpace.exists_poincare_mean_of_c1GraphBoundary` gives the inequality.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.1, Theorem 1, p. 290.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Sobolev

namespace SobolevSpace

/-- **Poincaré's inequality for `C¹` functions.** Let `Ω ⊆ ℝ^(n+1)` be open, bounded and
connected with `C¹` graph boundary, and `1 ≤ p ≤ ∞`. There is a constant `C` such that every `C¹`
function `v` on the whole space satisfies `‖v - ⨍_Ω v‖_{Lᵖ(Ω)} ≤ C ‖Dv‖_{Lᵖ(Ω)}`, with the
operator norm of the Fréchet derivative. The statement names no Sobolev space. The proof reads
`v` as an element of `W^{1,p}(Ω)` and applies the inequality proved there. -/
theorem exists_eLpNorm_sub_average_le {n : ℕ} {Ω : Set (ℝ^(n + 1))} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C : ℝ≥0, ∀ v : ℝ^(n + 1) → ℝ, ContDiff ℝ 1 v →
      eLpNorm (fun x ↦ v x - ⨍ y in Ω, v y) p (volume.restrict Ω) ≤
        C * eLpNorm (fderiv ℝ v) p (volume.restrict Ω) := by
  obtain ⟨C, hC, hP⟩ :=
    GraphSpace.exists_poincare_mean_of_c1GraphBoundary hΩ hbounded hconn hgraph (p := p)
  refine ⟨C.toNNReal, fun v hv ↦ ?_⟩
  change _ ≤ ENNReal.ofReal C * _
  -- continuous functions are in `Lᵖ(Ω)`
  have hmem {G : Type} [NormedAddCommGroup G] {f : ℝ^(n + 1) → G} (hf : Continuous f) :
      MemLp f p (volume.restrict Ω) :=
    hf.continuousOn.memLp_of_subset_isCompact hbounded.isCompact_closure hΩ.measurableSet
      subset_closure
  have hDc : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  -- the vector that represents the derivative
  let g : ℝ^(n + 1) → ℝ^(n + 1) := fun x ↦
    (InnerProductSpace.toDual ℝ (ℝ^(n + 1))).symm (fderiv ℝ v x)
  have hgc : Continuous g := (LinearIsometryEquiv.continuous _).comp hDc
  have hgn (x : ℝ^(n + 1)) : ‖g x‖ = ‖fderiv ℝ v x‖ := LinearIsometryEquiv.norm_map _ _
  have hgi (i : Fin (n + 1)) : (fun x ↦ g x i) = fun x ↦ (∂[i] v) x := by
    funext x
    have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i (1 : ℝ))
      (y := fderiv ℝ v x)
    rw [real_inner_comm, EuclideanSpace.inner_single_left] at h
    have h' : g x i = fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ)) := by simpa using h
    exact h'
  obtain ⟨U, hU0, hU1⟩ := GraphSpace.exists_of_weakGradient (p := p) (Ω := Ω)
    (hmem hv.continuous) (hmem hgc)
    (fun i ↦ by rw [hgi i]; exact WeakChangeOfVariables.hasWeakDerivativeOn_of_contDiff_one hv)
  have h := hP U
  have h0 : (GraphSpace.wkpBaseCoordinateCLM U : ℝ^(n + 1) → ℝ) =ᵐ[volume.restrict Ω] v := hU0
  have hbase : (fun x ↦ GraphSpace.wkpBaseCoordinateCLM U x -
      ⨍ y, GraphSpace.wkpBaseCoordinateCLM U y ∂domainMeasure (n + 1) Ω)
        =ᵐ[volume.restrict Ω] fun x ↦ v x - ⨍ y in Ω, v y := by
    have havg : ⨍ y, GraphSpace.wkpBaseCoordinateCLM U y ∂domainMeasure (n + 1) Ω =
        ⨍ y in Ω, v y := average_congr h0
    filter_upwards [h0] with x hx
    rw [hx, havg]
  have hgrad : ‖∇ U‖ = (eLpNorm (fderiv ℝ v) p (volume.restrict Ω)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hU1]
    exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae hgc.aestronglyMeasurable
      hDc.aestronglyMeasurable (Eventually.of_forall hgn))
  rw [eLpNorm_congr_ae hbase, hgrad] at h
  have hfin1 : eLpNorm (fun x ↦ v x - ⨍ y in Ω, v y) p (volume.restrict Ω) ≠ ⊤ :=
    (hmem (hv.continuous.sub continuous_const)).eLpNorm_ne_top
  have hfin2 : eLpNorm (fderiv ℝ v) p (volume.restrict Ω) ≠ ⊤ := (hmem hDc).eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hfin1, ← ENNReal.ofReal_toReal hfin2,
    ← ENNReal.ofReal_mul hC.le]
  exact ENNReal.ofReal_le_ofReal h

end SobolevSpace
