/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Lower-order terms for interior weak solutions

The drift and potential map H¹ to L². Adding their load functional to the principal
form gives the full divergence operator on arbitrary H¹ states and H¹₀ tests.
Moving these terms to the forcing recovers the principal weak equation.
No boundary condition is imposed on the state.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The bounded map `u ↦ b · Du + cu` from H¹ to L². -/
def interiorLowerOrderOperator (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) :
    H¹(Ω) →L[ℝ] DerivLp n 2 Ω :=
  (∑ i, (mulLpLeft (p := 2) (b i)).comp (wkpCoordinateCLM (singleDerivIndex n i))) +
    (mulLpLeft (p := 2) c).comp wkpBaseCoordinateCLM

/-- Evaluation of the lower-order operator in the weak derivative coordinates. -/
@[simp]
theorem interiorLowerOrderOperator_apply
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) (u : H¹(Ω)) :
    interiorLowerOrderOperator b c u =
      (∑ i, b i • wkpCoordinateCLM (singleDerivIndex n i) u) +
        c • wkpBaseCoordinateCLM u := by
  simp [interiorLowerOrderOperator, mulLpLeft_apply]

/-- The full divergence-form operator, tested against H¹₀, on arbitrary H¹ states. -/
def interiorFullDivergenceOperator
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω) :
    H¹(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
  interiorVariableCoeffForm (multiplicationCoefficientOperator a) +
    loadFunctionalCLM.comp (interiorLowerOrderOperator b c)

/-- The weak equation for the full divergence operator without a trace condition. -/
def IsInteriorWeakFullDivergenceSolution
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) : Prop :=
  IsOpen Ω ∧ interiorFullDivergenceOperator a b c u = loadFunctional f

/-- The full weak equation is exactly the principal equation with the lower-order
terms subtracted from the forcing. In particular, that forcing belongs to L². -/
theorem isInteriorWeakFullDivergenceSolution_iff
    (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) :
    IsInteriorWeakFullDivergenceSolution a b c f u ↔
      IsInteriorWeakDivergenceSolution a (f - interiorLowerOrderOperator b c u) u := by
  simp only [IsInteriorWeakFullDivergenceSolution, IsInteriorWeakDivergenceSolution,
    interiorFullDivergenceOperator, add_apply,
    ContinuousLinearMap.comp_apply, ← loadFunctionalCLM_apply, map_sub]
  simp only [← ContinuousLinearMap.ext_iff, eq_sub_iff_add_eq]

/-- Evaluation of the full equation gives the usual principal, drift, and potential
pairings. Every term is an L² inner product. -/
theorem IsInteriorWeakFullDivergenceSolution.equation
    {a : Fin n → Fin n → DerivLp n ∞ Ω}
    {b : Fin n → DerivLp n ∞ Ω} {c : DerivLp n ∞ Ω}
    {f : DerivLp n 2 Ω} {u : H¹(Ω)}
    (hu : IsInteriorWeakFullDivergenceSolution a b c f u) (v : H¹₀(Ω)) :
    (∑ i, ∑ j, ⟪a i j • wkpCoordinateCLM (singleDerivIndex n j) u,
      derivCoordCLM i v⟫_ℝ) +
      (∑ i, ⟪b i • wkpCoordinateCLM (singleDerivIndex n i) u, baseCoordCLM v⟫_ℝ) +
      ⟪c • wkpBaseCoordinateCLM u, baseCoordCLM v⟫_ℝ =
        ⟪f, baseCoordCLM v⟫_ℝ := by
  have h := DFunLike.congr_fun hu.2 v
  simpa [interiorFullDivergenceOperator, loadFunctional_apply,
    inner_add_left, sum_inner, add_assoc] using h

/-- The operator equation is equivalent to the usual variational identity for all
H¹₀ tests. This imposes no zero-trace condition on the H¹ state. -/
theorem isInteriorWeakFullDivergenceSolution_iff_forall
    (hΩ : IsOpen Ω) (a : Fin n → Fin n → DerivLp n ∞ Ω)
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    (f : DerivLp n 2 Ω) (u : H¹(Ω)) :
    IsInteriorWeakFullDivergenceSolution a b c f u ↔
      ∀ v : H¹₀(Ω),
        (∑ i, ∑ j, ⟪a i j • wkpCoordinateCLM (singleDerivIndex n j) u,
          derivCoordCLM i v⟫_ℝ) +
        (∑ i, ⟪b i • wkpCoordinateCLM (singleDerivIndex n i) u, baseCoordCLM v⟫_ℝ) +
        ⟪c • wkpBaseCoordinateCLM u, baseCoordCLM v⟫_ℝ =
          ⟪f, baseCoordCLM v⟫_ℝ := by
  refine ⟨fun hu ↦ hu.equation, fun h ↦ ⟨hΩ, ?_⟩⟩
  ext v
  simpa [interiorFullDivergenceOperator, loadFunctional_apply,
    inner_add_left, sum_inner, add_assoc] using h v

/-- Lower-order terms commute with restriction to an open subdomain. -/
theorem interiorLowerOrderOperator_restrict
    (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)
    {V : Set (ℝ^n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) (u : H¹(Ω)) :
    interiorLowerOrderOperator (fun i ↦ restrictDerivLp hVΩ (b i))
        (restrictDerivLp hVΩ c) (restrictCLM hV.measurableSet hVΩ u) =
      restrictDerivLp hVΩ (interiorLowerOrderOperator b c u) := by
  simp only [interiorLowerOrderOperator_apply]
  change (∑ i, restrictDerivLp hVΩ (b i) •
    (restrictCLM hV.measurableSet hVΩ u : WkpAmbientOn n 1 2 V)
      (singleDerivIndex n i)) + restrictDerivLp hVΩ c •
      (restrictCLM hV.measurableSet hVΩ u : WkpAmbientOn n 1 2 V) (baseIndex n 1) = _
  simp only [restrictCLM_apply_coe, restrictAmbient_apply,
    ← restrictDerivLp_lpSMul hV.measurableSet, map_add, map_sum]
  rfl

/-- The full interior weak equation restricts to every smaller open set. -/
theorem IsInteriorWeakFullDivergenceSolution.restrict
    {a : Fin n → Fin n → DerivLp n ∞ Ω}
    {b : Fin n → DerivLp n ∞ Ω} {c : DerivLp n ∞ Ω}
    {f : DerivLp n 2 Ω} {u : H¹(Ω)}
    (hu : IsInteriorWeakFullDivergenceSolution a b c f u)
    {V : Set (ℝ^n)} (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    IsInteriorWeakFullDivergenceSolution
      (fun i j ↦ restrictDerivLp hVΩ (a i j))
      (fun i ↦ restrictDerivLp hVΩ (b i)) (restrictDerivLp hVΩ c)
      (restrictDerivLp hVΩ f) (restrictCLM hV.measurableSet hVΩ u) := by
  rw [isInteriorWeakFullDivergenceSolution_iff] at hu ⊢
  rw [interiorLowerOrderOperator_restrict b c hV, ← map_sub]
  exact hu.restrict hV hVΩ

end SobolevSpace.GraphSpace
