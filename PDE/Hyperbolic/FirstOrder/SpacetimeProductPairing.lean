/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.SpacetimeTestRegularity
public import PDE.Analysis.MeasureTheory.Lp.Fubini

/-!
# Product-space pairings with smooth spacetime tests

The smooth derivatives represent the first-order Sobolev coordinates of each
spatial slice. Fubini and L² duality then identify product-space scalar integrals with
the time integrals of spatial L² pairings. Finite component sums preserve
integrability. The initial term is a spatial pairing with the prescribed datum; a
joint representative of a Bochner curve need not have a prescribed initial slice.

Only the smooth test has time regularity. The state is only Bochner L² on Ioc, and the spatial
volume may be infinite.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal NNReal InnerProductSpace Topology Distributions ContDiff

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "ν" => volume.restrict (Ioc a b)
local notation "σ" => domainMeasure n univ

/-- The smooth spacetime derivatives represent every first-order coordinate
of the spatial H¹ slice. This is an almost-everywhere identity in space at each time;
it does not choose values for a weak state or coefficient. -/
theorem spacetimeTestH1Slice_coordinate_ae (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (t : ℝ)
    (p : Fin m) (d : DerivIndex n 1) :
    (wkpCoordinateCLM d (spacetimeTestH1Slice Φ t p) : ℝ^n → ℝ) =ᵐ[σ] fun x ↦
      (firstOrderRows (Φ p) (fun j ↦ TestFunction.lineDerivCLM ℝ
      (0, EuclideanSpace.single j (1 : ℝ)) (Φ p)) d) (t, x) := by
  have h := globalTestFunctionToWkpOn_coordinate_ae
    (p := 2) (Ω := univ) (TestFunction.sliceRight t (Φ p)) d
  change ((globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ)
    (TestFunction.sliceRight t (Φ p)) : WkpAmbientOn n 1 2 univ) d : ℝ^n → ℝ) =ᵐ[σ] _
  rcases d.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨j, rfl⟩
  · simp only [baseIndex_toList, iteratedPartialDeriv] at h
    filter_upwards [h] with x hx
    rw [hx, firstOrderRows_baseIndex]
    rfl
  · filter_upwards [h] with x hx
    rw [hx, singleDerivIndex_toList, firstOrderRows_singleDerivIndex]
    change (∂[j] (TestFunction.sliceRight t (Φ p)).toFun) x = _
    change (∂[j] (TestFunction.sliceRight t (Φ p)).toFun) x = (TestFunction.sliceRight t
        (TestFunction.lineDerivCLM ℝ (0, EuclideanSpace.single j (1 : ℝ)) (Φ p))) x
    rw [← TestFunction.lineDerivCLM_sliceRight,
      TestFunction.lineDerivCLM_apply_of_le (by simp),
      ((TestFunction.sliceRight t (Φ p)).contDiff.differentiable
        (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    rfl

/-- A smooth spacetime test paired with a joint representative of a Bochner L² state
is integrable for the time-space product measure. Its integral equals the time integral
of the spatial L² pairing. -/
theorem integral_spacetime_test_pairing {u : ℝ → H} (hu : MemLp u 2 ν) (U : Fin m → ℝ × ℝ^n → ℝ)
    (hU : ∀ p, AEStronglyMeasurable (U p) ((ν).prod σ))
    (hUsec : ∀ p, ∀ᵐ t ∂ν, (fun x ↦ U p (t, x)) =ᵐ[σ] (u t p : ℝ^n → ℝ))
    (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :
    Integrable (fun z ↦ ∑ p, U p z * Φ p z) ((ν).prod σ) ∧
      (∫ z, ∑ p, U p z * Φ p z ∂(ν).prod σ) = ∫ t,
        inner ℝ (u t) (transportBaseCLM (spacetimeTestH1Slice Φ t)) ∂ν := by
  classical
  have hucoord (p : Fin m) : MemLp (fun t ↦ u t p) 2 ν := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) p).comp_memLp' hu
  have htest : MemLp (fun t ↦ transportBaseCLM (spacetimeTestH1Slice Φ t)) 2 ν :=
    memLp_restrict_Ioc_of_continuousOn
      (transportBaseCLM.continuous.comp (continuous_spacetimeTestH1Slice Φ)).continuousOn
  have htestcoord (p : Fin m) : MemLp
      (fun t ↦ transportBaseCLM (spacetimeTestH1Slice Φ t) p) 2 ν := by
    simpa only [Function.comp_def, PiLp.proj_apply] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m ↦ D) p).comp_memLp' htest
  have htestsec (p : Fin m) : ∀ᵐ t ∂ν, (fun x ↦ Φ p (t, x)) =ᵐ[σ]
      (transportBaseCLM (spacetimeTestH1Slice Φ t) p : ℝ^n → ℝ) :=
    Eventually.of_forall fun t ↦ by
      simpa only [transportBaseCLM_apply, firstOrderRows_baseIndex] using
        (spacetimeTestH1Slice_coordinate_ae Φ t p (baseIndex n 1)).symm
  have hprod (p : Fin m) : Integrable (fun z ↦ U p z * Φ p z) ((ν).prod σ) := by
    simpa only [Real.inner_apply] using integrable_inner_prod_of_ae_eq_L2_sections
      (hucoord p) (htestcoord p) (hU p) (Φ p).continuous.aestronglyMeasurable (hUsec p) (htestsec p)
  have htime (p : Fin m) : Integrable (fun t ↦
      inner ℝ (u t p) (transportBaseCLM (spacetimeTestH1Slice Φ t) p)) ν :=
    memLp_one_iff_integrable.1 ((innerSL ℝ (E := D)).memLp_of_bilin 1 (hucoord p) (htestcoord p))
  have hpair (p : Fin m) : (∫ z, U p z * Φ p z ∂(ν).prod σ) =
        ∫ t, inner ℝ (u t p) (transportBaseCLM (spacetimeTestH1Slice Φ t) p) ∂ν := by
    simpa only [Real.inner_apply] using integral_inner_prod_eq_integral_L2_inner
      (hucoord p) (htestcoord p) (hU p) (Φ p).continuous.aestronglyMeasurable (hUsec p) (htestsec p)
  refine ⟨integrable_finsetSum Finset.univ (fun p _ ↦ hprod p), ?_⟩
  calc
    (∫ z, ∑ p, U p z * Φ p z ∂(ν).prod σ) = ∑ p, ∫ z, U p z * Φ p z ∂(ν).prod σ :=
      integral_finsetSum Finset.univ (fun p _ ↦ hprod p)
    _ = ∑ p, ∫ t, inner ℝ (u t p) (transportBaseCLM (spacetimeTestH1Slice Φ t) p) ∂ν :=
      Finset.sum_congr rfl (fun p _ ↦ hpair p)
    _ = ∫ t, ∑ p, inner ℝ (u t p) (transportBaseCLM (spacetimeTestH1Slice Φ t) p) ∂ν :=
      (integral_finsetSum Finset.univ (fun p _ ↦ htime p)).symm
    _ = ∫ t, inner ℝ (u t) (transportBaseCLM (spacetimeTestH1Slice Φ t)) ∂ν := by
      simp only [PiLp.inner_apply]

/-- The initial boundary term is the spatial integral against the prescribed L² datum.
It uses the datum's spatial representative, not a value of a joint time-space
representative at the initial time. -/
theorem integral_spacetime_initial_pairing
    (x₀ : H) (Φ : Fin m → 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (a : ℝ) :
    Integrable (fun x ↦ ∑ p, (x₀ p) x * Φ p (a, x)) σ ∧
      (∫ x, ∑ p, (x₀ p) x * Φ p (a, x) ∂σ) =
        inner ℝ x₀ (transportBaseCLM (spacetimeTestH1Slice Φ a)) := by
  classical
  let v : H := transportBaseCLM (spacetimeTestH1Slice Φ a)
  have hv (p : Fin m) : (v p : ℝ^n → ℝ) =ᵐ[σ] fun x ↦ Φ p (a, x) := by
    simpa only [v, transportBaseCLM_apply, firstOrderRows_baseIndex] using
      spacetimeTestH1Slice_coordinate_ae Φ a p (baseIndex n 1)
  have hi (p : Fin m) : Integrable (fun x ↦ (x₀ p) x * Φ p (a, x)) σ := by
    apply (L2.integrable_inner (𝕜 := ℝ) (x₀ p) (v p)).congr
    filter_upwards [hv p] with x hx
    simp only [Real.inner_apply, hx]
  have heq (p : Fin m) :
      (∫ x, (x₀ p) x * Φ p (a, x) ∂σ) = inner ℝ (x₀ p) (v p) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv p] with x hx
    simp only [Real.inner_apply, hx]
  refine ⟨integrable_finsetSum Finset.univ (fun p _ ↦ hi p), ?_⟩
  rw [integral_finsetSum Finset.univ (fun p _ ↦ hi p)]
  change (∑ p, ∫ x, (x₀ p) x * Φ p (a, x) ∂σ) = inner ℝ x₀ v
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun p _ ↦ heq p)

end PDE.Hyperbolic.FirstOrder
