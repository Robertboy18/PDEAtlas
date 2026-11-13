/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.CellProblem
public import PDE.Spaces.Sobolev.Periodic.ClosedGradient
public import PDE.Spaces.Sobolev.Periodic.Dilation
public import PDE.Spaces.Sobolev.Periodic.WeakDerivative

/-!
# Periodic Sobolev cell correctors

The closed gradient space used in the variational cell problem consists exactly
of gradients of mean-zero periodic Sobolev potentials. Poincaré reconstructs the
potential from the cell gradient of `PeriodicCell.CellProblem`. Its coordinate derivative
is a Euclidean weak derivative after periodic lifting.
The lift is represented in the canonical Sobolev space on each unit cell.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging SobolevSpace.Periodic
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

/-- Every gradient in the cell closure has a unique mean-zero Sobolev potential. -/
theorem exists_unique_periodicPotential {n : ℕ} (g : gradientSpace n) :
    ∃! u : meanZeroSpace n,
      meanZeroGradientCLM n u = (g : Lp (ℝ^n) 2 (cellMeasure n)) := by
  have hg : (g : Lp (ℝ^n) 2 (cellMeasure n)) ∈
      Set.range (meanZeroGradientCLM n) := by
    apply closure_minimal ?_ (isClosed_range_meanZeroGradientCLM n) g.property
    rintro v ⟨a, b, hb, rfl⟩
    exact ⟨meanZeroOfContinuous a b hb, meanZeroGradientCLM_meanZeroOfContinuous a b hb⟩
  obtain ⟨u, hu⟩ := hg
  exact ⟨u, hu, fun v hv ↦ meanZeroGradientCLM_injective n (hv.trans hu.symm)⟩

/-- Reconstruct the mean-zero potential of a field in the closed gradient space. -/
def periodicPotential {n : ℕ} (g : gradientSpace n) : meanZeroSpace n :=
  (exists_unique_periodicPotential g).choose

/-- The reconstructed potential has the prescribed gradient. -/
@[simp] theorem meanZeroGradientCLM_periodicPotential {n : ℕ} (g : gradientSpace n) :
    meanZeroGradientCLM n (periodicPotential g) =
      (g : Lp (ℝ^n) 2 (cellMeasure n)) :=
  (exists_unique_periodicPotential g).choose_spec.1

/-- Reconstruction is a bounded linear map in the gradient norm. -/
def periodicPotentialCLM (n : ℕ) : gradientSpace n →L[ℝ] meanZeroSpace n := by
  let L : gradientSpace n →ₗ[ℝ] meanZeroSpace n :=
    { toFun := periodicPotential
      map_add' := fun g h ↦ by
        apply meanZeroGradientCLM_injective n
        simp
      map_smul' := fun c g ↦ by
        apply meanZeroGradientCLM_injective n
        simp }
  exact L.mkContinuous 2 fun g ↦ by
    have h := norm_le_two_mul_gradient (periodicPotential g)
    rw [meanZeroGradientCLM_periodicPotential] at h
    convert! h using 1

/-- A periodic Sobolev gradient belongs to the cell gradient closure. -/
theorem gradientCLM_mem_gradientSpace {n : ℕ} (u : h1Space n) :
    gradientCLM n u ∈ gradientSpace n := by
  let S : AmbientSpace n →L[ℝ] Lp (ℝ^n) 2 (cellMeasure n) := WithLp.sndL 2 ℝ _ _
  have hc : IsClosed ((gradientSpace n).comap S.toLinearMap : Set (AmbientSpace n)) :=
    (continuousGradientSpace n).isClosed_topologicalClosure.preimage S.continuous
  have hle : continuousGraph n ≤ (gradientSpace n).comap S.toLinearMap := by
    rintro v ⟨a, g, hg, rfl⟩
    exact (continuousGradientSpace n).le_topologicalClosure ⟨a, g, hg, rfl⟩
  exact (continuousGraph n).topologicalClosure_minimal hle hc u.property

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
variable {α : ℝ} (hα : 0 < α)
  (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)

/-- The mean-zero periodic Sobolev corrector for a uniformly elliptic coefficient. -/
def correctorPotential : (ℝ^n) →L[ℝ] meanZeroSpace n :=
  (periodicPotentialCLM n).comp (correctorGradient A hα hA)

/-- The Sobolev corrector reconstructs the variationally determined cell gradient. -/
@[simp] theorem meanZeroGradientCLM_correctorPotential (ξ : ℝ^n) :
    meanZeroGradientCLM n (correctorPotential A hα hA ξ) =
      (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n)) := by
  change meanZeroGradientCLM n (periodicPotential (correctorGradient A hα hA ξ)) = _
  exact meanZeroGradientCLM_periodicPotential _

/-- The constructed corrector is normalized by its zero integral. -/
theorem integral_correctorPotential_eq_zero (ξ : ℝ^n) :
    (∫ x, valueCLM n (correctorPotential A hα hA ξ).val x ∂cellMeasure n) = 0 :=
  integral_value_eq_zero _

/-- Integration by parts identifies the weak derivative of the corrector. -/
theorem correctorPotential_weak_derivative (ξ : ℝ^n)
    (φ ψ : C(UnitAddTorus (Fin n), ℝ)) (i : Fin n)
    (hφ : ∀ x t, HasDerivAt (fun s ↦ φ (x + coordinateShift i s))
      (ψ (x + coordinateShift i t)) t) :
    (∫ x, valueCLM n (correctorPotential A hα hA ξ).val x * ψ x ∂cellMeasure n) =
      -(∫ x, (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n)) x i *
        φ x ∂cellMeasure n) := by
  have h := integral_value_mul_derivative (correctorPotential A hα hA ξ).val φ ψ i hφ
  change (∫ x, valueCLM n (correctorPotential A hα hA ξ).val x * ψ x ∂cellMeasure n) =
    -(∫ x, meanZeroGradientCLM n (correctorPotential A hα hA ξ) x i * φ x ∂cellMeasure n)
    at h
  simpa only [meanZeroGradientCLM_correctorPotential] using h

/-- The cell corrector has the canonical Euclidean weak derivative after periodic lifting. -/
theorem correctorPotential_hasWeakDerivativeOn (ξ : ℝ^n) (i : Fin n) :
    SobolevSpace.HasWeakDerivativeOn univ [i]
      (fun x ↦ valueCLM n (correctorPotential A hα hA ξ).val (toTorus n x))
      (fun x ↦ (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n))
        (toTorus n x) i) := by
  have h := hasWeakDerivativeOn_toTorus (correctorPotential A hα hA ξ).val i
  change SobolevSpace.HasWeakDerivativeOn univ [i] _
    (fun x ↦ meanZeroGradientCLM n (correctorPotential A hα hA ξ) (toTorus n x) i) at h
  simpa only [meanZeroGradientCLM_correctorPotential] using h

/-- The rescaled cell potential has the oscillating cell gradient as its weak derivative. -/
theorem scaledCorrector_hasWeakDerivativeOn (ξ : ℝ^n)
    (ε : ℝ) (hε : ε ≠ 0) (i : Fin n) :
    SobolevSpace.HasWeakDerivativeOn univ [i]
      (fun x ↦ ε * valueCLM n (correctorPotential A hα hA ξ).val
        (toTorus n (ε⁻¹ • x)))
      (fun x ↦ (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n))
        (toTorus n (ε⁻¹ • x)) i) := by
  have h := hasWeakDerivativeOn_scaledPotential (correctorPotential A hα hA ξ).val ε hε i
  change SobolevSpace.HasWeakDerivativeOn univ [i] _
    (fun x ↦ meanZeroGradientCLM n (correctorPotential A hα hA ξ)
      (toTorus n (ε⁻¹ • x)) i) at h
  simpa only [meanZeroGradientCLM_correctorPotential] using h

/-- On each cell, the corrector is represented in the Euclidean Sobolev space. -/
theorem correctorPotential_unitCell_sobolev (ξ : ℝ^n) (a : Fin n → ℝ) :
    ∃ U : W^{1,2}(unitCell a),
      SobolevSpace.GraphSpace.baseRepresentative U
        =ᵐ[SobolevSpace.domainMeasure n (unitCell a)]
          (fun x ↦ valueCLM n (correctorPotential A hα hA ξ).val (toTorus n x)) ∧
      (SobolevSpace.GraphSpace.wkpGradientCLM U : ℝ^n → ℝ^n)
        =ᵐ[SobolevSpace.domainMeasure n (unitCell a)]
          (fun x ↦ (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n))
            (toTorus n x)) := by
  obtain ⟨U, hU, hG⟩ := exists_unitCell_sobolev (correctorPotential A hα hA ξ).val a
  refine ⟨U, hU, ?_⟩
  change (SobolevSpace.GraphSpace.wkpGradientCLM U : ℝ^n → ℝ^n)
    =ᵐ[SobolevSpace.domainMeasure n (unitCell a)]
      (fun x ↦ meanZeroGradientCLM n (correctorPotential A hα hA ξ) (toTorus n x)) at hG
  simpa only [meanZeroGradientCLM_correctorPotential] using hG

/-- The cell equation holds against every periodic Sobolev test potential. -/
theorem correctorPotential_equation (ξ : ℝ^n) (v : h1Space n) :
    (∫ x, ⟪A x (correctedField A hα hA ξ x),
      gradientCLM n v x⟫_ℝ ∂cellMeasure n) = 0 :=
  correctorGradient_equation A hα hA ξ ⟨gradientCLM n v, gradientCLM_mem_gradientSpace v⟩

/-- The corrected field is the imposed constant plus the Sobolev gradient. -/
theorem correctedField_eq_add_gradient (ξ : ℝ^n) :
    correctedField A hα hA ξ =
      constantField n ξ + gradientCLM n (correctorPotential A hα hA ξ).val := by
  change constantField n ξ + (correctorGradient A hα hA ξ).val =
    constantField n ξ + meanZeroGradientCLM n (correctorPotential A hα hA ξ)
  rw [meanZeroGradientCLM_correctorPotential]

/-- Mean zero and the cell equation uniquely determine the Sobolev corrector. -/
theorem correctorPotential_unique (ξ : ℝ^n) {u : meanZeroSpace n}
    (hu : ∀ v : h1Space n,
      (∫ x, ⟪A x ((constantField n ξ + gradientCLM n u.val) x),
        gradientCLM n v x⟫_ℝ ∂cellMeasure n) = 0) :
    u = correctorPotential A hα hA ξ := by
  let g : gradientSpace n := ⟨gradientCLM n u.val, gradientCLM_mem_gradientSpace u.val⟩
  have hg : g = correctorGradient A hα hA ξ := by
    apply correctorGradient_unique A hα hA ξ
    intro h
    have ht := hu (periodicPotential h).val
    change (∫ x, ⟪A x ((constantField n ξ + (g : Lp (ℝ^n) 2 (cellMeasure n))) x),
      meanZeroGradientCLM n (periodicPotential h) x⟫_ℝ ∂cellMeasure n) = 0 at ht
    simpa only [meanZeroGradientCLM_periodicPotential] using ht
  apply meanZeroGradientCLM_injective n
  rw [meanZeroGradientCLM_correctorPotential]
  exact congrArg Subtype.val hg

/-- The effective coefficient is the mean flux of the constructed Sobolev corrector. -/
theorem effectiveOperator_eq_mean_corrector_flux (ξ : ℝ^n) :
    effectiveOperator A hα hA ξ =
      ∫ x, A x ((constantField n ξ +
        gradientCLM n (correctorPotential A hα hA ξ).val) x) ∂cellMeasure n := by
  rw [← correctedField_eq_add_gradient, effectiveOperator_eq_mean_flux]

end PDE.Elliptic.Homogenization.PeriodicCell
