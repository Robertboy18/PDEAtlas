/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.Fractional.Integer.ClassicalRepresentation
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.WholeSpace

/-!
# Smooth reaction lifts above the classical Sobolev threshold

The constructed Sobolev embedding supplies the boundedness needed by the higher
weak chain rule. Thus a smooth scalar reaction fixing zero has a uniquely
determined lift on Hᵏ whenever `n < 2(k - 1)`, in every positive dimension.
Its classical representative is the pointwise composition.

This is a membership and identification result. Continuity in the Hᵏ norm
does not follow from the closed graph assertion below for a nonlinear map.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

omit [NeZero n] in
/-- The whole-space embedding bounds the base row almost everywhere. -/
theorem ae_norm_baseRepresentative_le (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (u : W^{k,2}(ℝ^n)) :
    ∀ᵐ x ∂volume, ‖baseRepresentative u x‖ ≤ ‖classicalRepresentativeCLM hk‖ * ‖u‖ := by
  filter_upwards [classicalRepresentativeCLM_ae hk u] with x hx
  rw [← hx]
  exact ((classicalRepresentativeCLM hk u).norm_coe_le_norm x).trans
    ((classicalRepresentativeCLM hk).le_opNorm u)

/-- Smooth composition has a unique Hᵏ realization above the stated threshold.
There is no bound on the input or its derivatives among the hypotheses. -/
theorem existsUnique_higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (u : W^{k,2}(ℝ^n)) :
    ∃! v : W^{k,2}(ℝ^n), baseRepresentative v =ᵐ[volume] fun x ↦ f (baseRepresentative u x) := by
  obtain ⟨v, hv⟩ := Composition.exists_hk_composition_of_bounded k hf hf0
    (toRepresentative u) (ae_norm_baseRepresentative_le hk u)
  refine ⟨v, hv, fun w hw ↦ ?_⟩
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ _ _
  simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using hw.trans hv.symm

/-- The higher Sobolev reaction, constructed by the bounded weak chain rule. -/
def higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (u : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  (existsUnique_higherComposition hk hf hf0 u).choose

/-- The higher lift is the prescribed scalar reaction almost everywhere. -/
theorem higherComposition_ae (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (u : W^{k,2}(ℝ^n)) :
    baseRepresentative (higherComposition hk hf hf0 u) =ᵐ[volume]
      fun x ↦ f (baseRepresentative u x) :=
  (existsUnique_higherComposition hk hf hf0 u).choose_spec.1

/-- At every spatial point the canonical representative is the scalar reaction
of the input representative. -/
theorem classicalRepresentative_higherComposition (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (u : W^{k,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherComposition hk hf hf0 u) x =
      f (classicalRepresentativeCLM hk u x) := by
  have heq := eq_classicalRepresentativeCLM_of_ae_eq hk (higherComposition hk hf hf0 u)
    (hf.continuous.comp (classicalRepresentativeCLM hk u).continuous) (by
      filter_upwards [classicalRepresentativeCLM_ae hk u,
        higherComposition_ae hk hf hf0 u] with y hy hz
      simp only [Function.comp_apply, hy, hz])
  exact (congrFun heq x).symm

omit [NeZero n] in
/-- Distinct Sobolev data have distinct canonical classical representatives. -/
theorem classicalRepresentativeCLM_injective (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    Function.Injective (classicalRepresentativeCLM hk) := by
  intro u v huv
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ _ _
  have heq := classicalRepresentativeCLM_ae hk u
  rw [huv] at heq
  simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using
    heq.symm.trans (classicalRepresentativeCLM_ae hk v)

/-- Higher composition has a sequentially closed graph. This alone is not a
nonlinear continuity theorem. -/
theorem higherComposition_seqClosedGraph (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {u : ℕ → W^{k,2}(ℝ^n)} {U V : W^{k,2}(ℝ^n)}
    (hu : Tendsto u atTop (𝓝 U))
    (hv : Tendsto (fun j ↦ higherComposition hk hf hf0 (u j)) atTop (𝓝 V)) :
    V = higherComposition hk hf hf0 U := by
  apply classicalRepresentativeCLM_injective hk
  refine BoundedContinuousFunction.ext fun x ↦ ?_
  let E := (BoundedContinuousFunction.evalCLM ℝ x).comp (classicalRepresentativeCLM hk)
  have hleft := (E.continuous.tendsto V).comp hv
  have hright := hf.continuous.continuousAt.tendsto.comp ((E.continuous.tendsto U).comp hu)
  rw [classicalRepresentative_higherComposition]
  exact tendsto_nhds_unique hleft
    (hright.congr fun j ↦ (classicalRepresentative_higherComposition hk hf hf0 (u j) x).symm)

end PDE.Hyperbolic.NonlinearWave.Cauchy
