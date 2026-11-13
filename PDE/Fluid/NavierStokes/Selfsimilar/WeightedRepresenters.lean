/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Selfsimilar.GraphWeighted
public import PDE.Fluid.NavierStokes.Selfsimilar.PairingIntegrals

/-!
# Square-integrable representers of functionals on the weighted energy space

A square-integrable vector field `g` on `ℝⁿ` defines a point `massField g` of the mass
coordinates `L²(ℝⁿ)ⁿ` of vector `H¹`, with `⟪massField g, massField g'⟫ = ∫ g·g'` and
`⟪massField g, massCLM v⟫ = ∫ g·v` for the representative of `v`. On the weighted copy
`T.weighted c` of a closed span, `T.weightedMass hc` reads off the mass coordinates; the energy
norm `‖∇v‖² + c ‖v‖²` gives `‖T.weightedMass hc h‖² ≤ c⁻¹ ‖h‖²`. Hence
`T.weightedPairing hc q : h ↦ ⟪q, T.weightedMass hc h⟫` is a bounded functional, the `L²`
pairing with `q`, and its dual norm is at most `c^{-1/2} ‖q‖`. These are the coordinate
functionals and the residual functionals of the finite-rank determinant criterion.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert RealInnerProductSpace

namespace NavierStokes.Selfsimilar

open Stationary

variable {n : ℕ}

local notation "H" => PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))
local notation "Mass" => PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ)
local notation "Grad" => PiLp 2 (fun _ : Fin n ↦ PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 univ))

/-- The components of a square-integrable vector field are square integrable. -/
theorem memLp_two_component {g : ℝ^n → ℝ^n} (hg : MemLp g 2 volume) (i : Fin n) :
    MemLp (fun x ↦ g x i) 2 (domainMeasure n univ) := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hg
  simpa [domainMeasure, Function.comp_def] using h

/-- The mass coordinates of a square-integrable vector field. -/
def massField (g : ℝ^n → ℝ^n) (hg : MemLp g 2 volume) : Mass :=
  WithLp.toLp 2 fun i ↦ (memLp_two_component hg i).toLp (fun x ↦ g x i)

theorem massField_apply_ae (g : ℝ^n → ℝ^n) (hg : MemLp g 2 volume) (i : Fin n) :
    (massField g hg i : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ g x i := by
  have h := (memLp_two_component hg i).coeFn_toLp
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h

private theorem integrable_component_mul {f g : ℝ^n → ℝ^n} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (i : Fin n) : Integrable (fun x ↦ f x i * g x i) volume := by
  have h1 := memLp_two_component hf i
  have h2 := memLp_two_component hg i
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2
  exact h1.integrable_mul h2

/-- The `L²` pairing of mass coordinates with a vector field whose components are
representatives of the coordinates. -/
theorem inner_massField_eq_integral {g : ℝ^n → ℝ^n} (hg : MemLp g 2 volume) (u : Mass)
    {U : ℝ^n → ℝ^n} (hU : MemLp U 2 volume)
    (hu : ∀ i, (u i : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ U x i) :
    ⟪massField g hg, u⟫ = ∫ x, ⟪g x, U x⟫ := by
  rw [PiLp.inner_apply]
  have hterm (i : Fin n) : ⟪massField g hg i, u i⟫ = ∫ x, g x i * U x i :=
    inner_eq_integral_mul_of_ae (massField_apply_ae g hg i) (hu i)
  simp only [hterm]
  rw [← integral_finsetSum _ fun i _ ↦ integrable_component_mul hg hU i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- The Gram entries of mass fields are the integrals of the inner products. -/
theorem inner_massField_massField {g g' : ℝ^n → ℝ^n} (hg : MemLp g 2 volume)
    (hg' : MemLp g' 2 volume) : ⟪massField g hg, massField g' hg'⟫ = ∫ x, ⟪g x, g' x⟫ :=
  inner_massField_eq_integral hg _ hg' (massField_apply_ae g' hg')

/-- The pairing of a mass field with the mass coordinates of a vector `H¹` field whose
representative agrees almost everywhere with a square-integrable `U`. -/
theorem inner_massField_massCLM {g : ℝ^n → ℝ^n} (hg : MemLp g 2 volume) (v : H)
    {U : ℝ^n → ℝ^n} (hU : MemLp U 2 volume) (hv : representative v =ᵐ[volume] U) :
    ⟪massField g hg, massCLM v⟫ = ∫ x, ⟪g x, U x⟫ := by
  refine inner_massField_eq_integral hg _ hU fun i ↦ ?_
  filter_upwards [hv] with x hx
  rw [← hx]
  rfl

namespace DilationTestSpace

variable (T : DilationTestSpace n) {c : ℝ}

/-- The mass coordinates of a point of the weighted copy. -/
def weightedMass (hc : 0 < c) : T.weighted c →L[ℝ] Mass :=
  massCLM.comp (T.space.subtypeL.comp (T.weightedEquiv hc).symm.toContinuousLinearMap)

theorem weightedMass_apply (hc : 0 < c) (h : T.weighted c) :
    T.weightedMass hc h = massCLM (((T.weightedEquiv hc).symm h : T.space) : H) :=
  rfl

theorem weightedMass_weightedEquiv (hc : 0 < c) (v : T.space) :
    T.weightedMass hc (T.weightedEquiv hc v) = massCLM (v : H) := by
  rw [weightedMass_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The energy norm controls the mass coordinates: `c ‖v‖² ≤ ‖∇v‖² + c ‖v‖²`. -/
theorem norm_weightedMass_sq_le (hc : 0 < c) (h : T.weighted c) :
    ‖T.weightedMass hc h‖ ^ 2 ≤ c⁻¹ * ‖h‖ ^ 2 := by
  have hn := T.norm_weightedEquiv_sq hc ((T.weightedEquiv hc).symm h)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hn
  rw [weightedMass_apply, hn, le_inv_mul_iff₀ hc]
  nlinarith [sq_nonneg ‖gradientCLM (((T.weightedEquiv hc).symm h : T.space) : H)‖]

/-- The `L²` pairing with `q` as a functional on the weighted copy. -/
def weightedPairing (hc : 0 < c) (q : Mass) : StrongDual ℝ (T.weighted c) :=
  (innerSL ℝ q).comp (T.weightedMass hc)

theorem weightedPairing_apply (hc : 0 < c) (q : Mass) (h : T.weighted c) :
    T.weightedPairing hc q h = ⟪q, T.weightedMass hc h⟫ :=
  rfl

end DilationTestSpace

end NavierStokes.Selfsimilar
