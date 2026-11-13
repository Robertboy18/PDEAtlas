/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
public import PDE.Fluid.NavierStokes.Stationary.Exhaustion
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Pointwise representatives of whole-space Sobolev velocity fields

A velocity correction in the Hilbert product of scalar `H¹(ℝ^n)` spaces is a tuple of
equivalence classes. `representative w` is the Euclidean vector field whose components are the
chosen representatives of the mass coordinates `massCLM w`, and
`gradientRepresentative w x i j` is the chosen representative of the weak partial derivative
`∂ⱼ wᵢ` from `gradientCLM w`. Statements that hold almost everywhere, such as tested weak
equations and symmetry conditions, do not depend on these choices. The representative is
square integrable and linear up to null sets, its components are locally `H¹` with the chosen
gradient entries, also square integrable, as weak derivatives, and it is distributionally
divergence-free when the weak divergence vanishes.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Distributions

namespace NavierStokes.Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))

/-- The Euclidean vector field whose `i`th component is the chosen representative of the
`i`th mass coordinate of `w`. -/
def representative (w : H) : ℝ^n → ℝ^n :=
  fun x ↦ WithLp.toLp 2 fun i ↦ (massCLM w i : ℝ^n → ℝ) x

/-- The components of the representative are the representatives of the mass coordinates. -/
@[simp]
theorem representative_apply (w : H) (x : ℝ^n) (i : Fin n) :
    representative w x i = (massCLM w i : ℝ^n → ℝ) x :=
  rfl

/-- The squared Euclidean length of the representative integrates to the squared mass norm. -/
theorem integral_norm_representative_sq (w : H) :
    ∫ x, ‖representative w x‖ ^ 2 = ‖massCLM w‖ ^ 2 := by
  have hint (i : Fin n) : Integrable (fun x ↦ representative w x i ^ 2) := by
    have hi := Lp.memLp (massCLM w i)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    exact hi.integrable_sq
  have hcomp (i : Fin n) : ∫ x, representative w x i ^ 2 = ‖massCLM w i‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    simp only [representative_apply, domainMeasure, Measure.restrict_univ]
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun i _ ↦ hint i, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_congr rfl fun i _ ↦ hcomp i

/-- The chosen representative of the weak partial derivative `∂ⱼ wᵢ`, the `(i, j)` entry
of `gradientCLM w`. -/
def gradientRepresentative (w : H) (x : ℝ^n) (i j : Fin n) : ℝ :=
  (gradientCLM w i j : ℝ^n → ℝ) x

/-- Each mass coordinate of a sum is the sum of the mass coordinates, almost everywhere. -/
private theorem massCLM_add_apply_ae (v w : H) (i : Fin n) :
    (massCLM (v + w) i : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ (massCLM v i : ℝ^n → ℝ) x + (massCLM w i : ℝ^n → ℝ) x := by
  have h := Lp.coeFn_add (massCLM v i) (massCLM w i)
  simp only [domainMeasure, Measure.restrict_univ] at h
  rw [map_add, PiLp.add_apply]
  exact h

/-- The representative of a sum is the sum of the representatives, almost everywhere. -/
theorem representative_add_ae (v w : H) :
    representative (v + w) =ᵐ[volume] representative v + representative w := by
  have h : ∀ᵐ x ∂volume, ∀ i : Fin n, (massCLM (v + w) i : ℝ^n → ℝ) x =
      (massCLM v i : ℝ^n → ℝ) x + (massCLM w i : ℝ^n → ℝ) x :=
    ae_all_iff.mpr fun i ↦ massCLM_add_apply_ae v w i
  filter_upwards [h] with x hx
  ext i
  simpa only [representative_apply, Pi.add_apply, PiLp.add_apply] using hx i

/-- The representative of a scalar multiple is the multiple of the representative, almost
everywhere. -/
theorem representative_smul_ae (c : ℝ) (w : H) :
    representative (c • w) =ᵐ[volume] c • representative w := by
  have h : ∀ᵐ x ∂volume, ∀ i : Fin n,
      (massCLM (c • w) i : ℝ^n → ℝ) x = c * (massCLM w i : ℝ^n → ℝ) x := by
    refine ae_all_iff.mpr fun i ↦ ?_
    have hi := Lp.coeFn_smul c (massCLM w i)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    rw [map_smul, PiLp.smul_apply]
    exact hi
  filter_upwards [h] with x hx
  ext i
  simpa only [representative_apply, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul] using hx i

/-- The representative of the zero field vanishes almost everywhere. -/
theorem representative_zero_ae : representative (0 : H) =ᵐ[volume] 0 := by
  have h : ∀ᵐ x ∂volume, ∀ i : Fin n, (massCLM (0 : H) i : ℝ^n → ℝ) x = 0 := by
    refine ae_all_iff.mpr fun i ↦ ?_
    have hi := Lp.coeFn_zero ℝ 2 (domainMeasure n univ)
    simp only [domainMeasure, Measure.restrict_univ] at hi
    rw [map_zero, PiLp.zero_apply]
    exact hi
  filter_upwards [h] with x hx
  ext i
  simpa only [representative_apply, Pi.zero_apply, PiLp.zero_apply] using hx i

/-- The representative of a whole-space `H¹` velocity is square integrable. -/
theorem memLp_representative (w : H) : MemLp (representative w) 2 volume := by
  refine memLp_piLp_iff.mpr fun i ↦ ?_
  have hi := Lp.memLp (massCLM w i)
  simp only [domainMeasure, Measure.restrict_univ] at hi
  exact hi

/-- The `i`th mass coordinate is the base coordinate of the `i`th component. -/
theorem massCLM_apply (w : H) (i : Fin n) : massCLM w i = wkpBaseCoordinateCLM (w i) :=
  rfl

/-- The `(i, j)` gradient entry is the coordinate of the `i`th component in the derivative
direction `j`. -/
theorem gradientCLM_apply (w : H) (i j : Fin n) :
    gradientCLM w i j = wkpCoordinateCLM (singleDerivIndex n j) (w i) :=
  rfl

/-- `gradientRepresentative w · i j` is a weak partial derivative `∂ⱼ` of the `i`th component
of `representative w` on the whole space. -/
theorem hasWeakDerivativeOn_gradientRepresentative (w : H) (i j : Fin n) :
    HasWeakDerivativeOn univ [j] (fun x ↦ representative w x i)
      (fun x ↦ gradientRepresentative w x i j) := by
  simpa only [representative_apply, massCLM_apply, gradientRepresentative, gradientCLM_apply,
    wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply, singleDerivIndex_toList] using
    (w i).property (singleDerivIndex n j)

/-- The chosen weak gradient entries of a whole-space `H¹` velocity are square integrable. -/
theorem memLp_gradientRepresentative (w : H) (i j : Fin n) :
    MemLp (fun x ↦ gradientRepresentative w x i j) 2 volume := by
  have h := Lp.memLp (gradientCLM w i j)
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

/-- The weak derivative identity of a whole-space `H¹` velocity against a smooth compactly
supported scalar test: `∫ wᵢ ∂ⱼψ = -∫ (∂ⱼwᵢ) ψ`. -/
theorem integral_representative_mul_partialDeriv (w : H) (i j : Fin n) {ψ : ℝ^n → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, representative w x i * PDE.partialDeriv j ψ x =
      -∫ x, gradientRepresentative w x i j * ψ x := by
  let φ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.mk ψ hψ hψc (subset_univ _)
  have h := (hasWeakDerivativeOn_gradientRepresentative w i j).integral_identity φ
    (subset_univ _)
  simpa [domainMeasure, Measure.restrict_univ, iteratedPartialDeriv, φ] using h

/-- Every component of the representative of a whole-space `H¹` velocity is locally `H¹`. -/
theorem isLocallyWkpOn_representative (w : H) (i : Fin n) :
    IsLocallyWkpOn 1 2 univ (fun x ↦ representative w x i) := by
  intro V hV _ _
  refine ⟨restrictCLM hV.measurableSet (subset_univ V) (w i), ?_⟩
  simpa only [baseRepresentative, representative_apply, massCLM_apply,
    wkpBaseCoordinateCLM_apply] using
    restrictCLM_apply_ae (k := 1) (p := 2) hV.measurableSet (subset_univ V) (w i)
      (baseIndex n 1)

/-- A whole-space `H¹` velocity with zero weak divergence has a distributionally
divergence-free representative: `∫ w · ∇ψ = -∫ (div w) ψ = 0` for every test `ψ`. -/
theorem distributionallyDivergenceFree_representative {w : H}
    (hw : divergenceCLM w = 0) :
    IncompressibleFlow.DistributionallyDivergenceFree (representative w) := by
  intro ψ hψ hψc
  let φ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.mk ψ hψ hψc (subset_univ _)
  let g : Fin n → DerivLp n 2 univ := fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) (w i)
  have hweak (i : Fin n) : ∫ x, (massCLM w i : ℝ^n → ℝ) x * (∂[i] ψ) x =
      -∫ x, (g i : ℝ^n → ℝ) x * ψ x := by
    have h := ((w i).property (singleDerivIndex n i)).integral_identity φ (subset_univ _)
    simpa [domainMeasure, Measure.restrict_univ, singleDerivIndex_toList,
      iteratedPartialDeriv, massCLM_apply, φ, g] using h
  have hL2 (f : DerivLp n 2 univ) : MemLp (f : ℝ^n → ℝ) 2 volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp f
  have hψ2 : MemLp ψ 2 volume := hψ.continuous.memLp_of_hasCompactSupport hψc
  have hdψ2 (i : Fin n) : MemLp (∂[i] ψ) 2 volume :=
    (hψ.partialDeriv i (k := 0)).continuous.memLp_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ)))
  have hint (i : Fin n) :
      Integrable (fun x ↦ (massCLM w i : ℝ^n → ℝ) x * (∂[i] ψ) x) :=
    (hL2 _).integrable_mul (hdψ2 i)
  have hint' (i : Fin n) : Integrable (fun x ↦ (g i : ℝ^n → ℝ) x * ψ x) :=
    (hL2 _).integrable_mul hψ2
  have hdens : IncompressibleFlow.weakDivergencePairingDensity (representative w) ψ =
      fun x ↦ ∑ i, (massCLM w i : ℝ^n → ℝ) x * (∂[i] ψ) x := by
    funext x
    rw [IncompressibleFlow.weakDivergencePairingDensity_eq_sum]
    rfl
  have hdiv : (fun x ↦ ∑ i, (g i : ℝ^n → ℝ) x) =ᵐ[volume] 0 := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ g
    have h0 := Lp.coeFn_zero ℝ 2 (domainMeasure n univ)
    have hsum : ∑ i, g i = 0 := by
      rw [← hw, divergenceCLM_apply]
    rw [hsum] at hs
    simp only [domainMeasure, Measure.restrict_univ] at hs h0
    exact hs.symm.trans h0
  refine ⟨hdens ▸ integrable_finsetSum _ fun i _ ↦ hint i, ?_⟩
  rw [IncompressibleFlow.weakDivergencePairing, hdens, integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [hweak]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun i _ ↦ hint' i, neg_eq_zero]
  calc ∫ x, ∑ i, (g i : ℝ^n → ℝ) x * ψ x = ∫ x, (∑ i, (g i : ℝ^n → ℝ) x) * ψ x := by
        simp only [Finset.sum_mul]
    _ = ∫ _x, (0 : ℝ) := integral_congr_ae (hdiv.mono fun x hx ↦ by simp [hx])
    _ = 0 := integral_zero _ _

end NavierStokes.Stationary
