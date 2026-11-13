/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Operators
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Derivatives of Banach-valued Sobolev functions

If `u ∈ W^{m,p}(Ω; F)`, then `D^α u ∈ W^{r,p}(Ω; F)` whenever `|α| + r ≤ m`.
The coordinate for `D^β D^α u` is the original coordinate for `D^(α ++ β) u`.
Testing with continuous linear functionals reduces this identity to the scalar
weak-derivative theorem; the Sobolev norm bound then follows by forgetting
coordinates. No geometric assumption on the open domain is needed.
-/

@[expose] public noncomputable section

open PDE (partialDeriv)

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n m r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Within a Sobolev graph, differentiating a derivative gives the
coordinate for the concatenated derivative word. -/
theorem WkpSpaceOn.hasWeakDerivativeOn_from_coordinate (U : W^{m,p}(Ω; F))
    (α β : List (Fin n)) (hαβ : α.length + β.length ≤ m) :
    HasWeakDerivativeOn Ω β
      (U.val (derivIndexOfList α (by omega)))
      (U.val (derivIndexOfList (α ++ β) (by simpa only [List.length_append] using hαβ))) := by
  have hloc (a : DerivIndex n m) : LocallyIntegrableOn (U.val a) Ω volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp (U.val a)).locallyIntegrable Fact.out)
  apply (hasWeakDerivativeOn_iff_forall_dual (hloc _) (hloc _)).mpr
  intro L
  have hscalar := (scalarEquiv (mapCLM L U)).property.hasWeakDerivativeOn_from_coordinate
    α β hαβ
  exact (SobolevSpace.hasWeakDerivativeOn_congr_ae
    (mapCLM_apply_ae L U _) (mapCLM_apply_ae L U _)).mp hscalar

/-- Extract the derivative coordinates prefixed by a fixed word. -/
def derivativeWordAmbientCLM (α : List (Fin n)) (hα : α.length + r ≤ m) :
    WkpAmbientOn n m p Ω F →L[ℝ] WkpAmbientOn n r p Ω F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n r ↦ Lp F p (domainMeasure n Ω))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      PiLp.proj p (fun _ : DerivIndex n m ↦ Lp F p (domainMeasure n Ω))
        (derivativeWordIndex α hα a))

omit [CompleteSpace F] in
/-- An extracted coordinate is the original coordinate with the derivative prefix. -/
@[simp] theorem derivativeWordAmbientCLM_apply (α : List (Fin n))
    (hα : α.length + r ≤ m) (U : WkpAmbientOn n m p Ω F) (a : DerivIndex n r) :
    derivativeWordAmbientCLM α hα U a = U (derivativeWordIndex α hα a) :=
  rfl

/-- Weak differentiation as a bounded map between Banach-valued Sobolev spaces. -/
def derivativeWordCLM (α : List (Fin n)) (hα : α.length + r ≤ m) :
    W^{m,p}(Ω; F) →L[ℝ] W^{r,p}(Ω; F) :=
  ((derivativeWordAmbientCLM α hα).comp (wkpSubmoduleOn n m p Ω F).subtypeL).codRestrict
    (wkpSubmoduleOn n r p Ω F) fun U a ↦ by
      simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        derivativeWordAmbientCLM_apply, derivativeWordIndex, baseIndex_toList,
        List.append_nil] using
        WkpSpaceOn.hasWeakDerivativeOn_from_coordinate U α a.toList
          ((Nat.add_le_add_left a.toList_length_le α.length).trans hα)

/-- The derivative bundle retains the expected `Lp` coordinates. -/
@[simp] theorem derivativeWordCLM_apply (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : W^{m,p}(Ω; F)) (a : DerivIndex n r) :
    (derivativeWordCLM α hα U).val a = U.val (derivativeWordIndex α hα a) :=
  rfl

/-- Taking a weak derivative does not increase the remaining Sobolev graph norm. -/
theorem norm_derivativeWordCLM_apply_le (α : List (Fin n)) (hα : α.length + r ≤ m)
    (U : W^{m,p}(Ω; F)) : ‖derivativeWordCLM α hα U‖ ≤ ‖U‖ :=
  PiLp.norm_mono_of_injective
    (derivativeWordIndex α hα) (derivativeWordIndex_injective α hα) _ _ fun _ ↦ le_rfl

/-- Weak derivative extraction has operator norm at most one. -/
theorem norm_derivativeWordCLM_le (α : List (Fin n)) (hα : α.length + r ≤ m) :
    ‖derivativeWordCLM (F := F) (p := p) (Ω := Ω) α hα‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  simpa only [one_mul] using norm_derivativeWordCLM_apply_le α hα U

/-- Successive weak derivatives concatenate their derivative words. -/
theorem derivativeWordCLM_comp {s : ℕ} (α : List (Fin n)) (hα : α.length + s ≤ m)
    (β : List (Fin n)) (hβ : β.length + r ≤ s) :
    (derivativeWordCLM (F := F) (p := p) (Ω := Ω) β hβ).comp (derivativeWordCLM α hα) =
      derivativeWordCLM (α ++ β) (by simp only [List.length_append]; omega) := by
  ext U : 1
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, derivativeWordCLM_apply]
  apply congrArg (fun b : DerivIndex n m ↦ U.val b)
  apply derivativeWordIndex_eq_of_perm
  simpa only [List.append_assoc] using
    List.Perm.append_left α (derivativeWordIndex_toList_perm β hβ a)

/-- The order of weak coordinate differentiation does not matter. -/
theorem derivativeWordCLM_perm {α β : List (Fin n)} (h : α.Perm β)
    (hα : α.length + r ≤ m) :
    derivativeWordCLM (F := F) (p := p) (Ω := Ω) α hα =
      derivativeWordCLM β (by simpa only [← h.length_eq] using hα) := by
  ext U : 1
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [derivativeWordCLM_apply]
  exact congrArg (fun b : DerivIndex n m ↦ U.val b)
    (derivativeWordIndex_eq_of_perm _ _ _ _ _ _ (h.append_right a.toList))

/-- The weak partial derivative lowers the Sobolev order by one. -/
def partialDerivCLM (i : Fin n) : W^{m + 1,p}(Ω; F) →L[ℝ] W^{m,p}(Ω; F) :=
  derivativeWordCLM [i] (by simp [Nat.add_comm])

/-- Banach-valued weak partial derivatives for the shared `∂[i] u` notation. -/
instance instPartialDerivative :
    PDE.PartialDerivative n (W^{m + 1,p}(Ω; F)) (W^{m,p}(Ω; F)) where
  partialDeriv i u := partialDerivCLM i u

/-- The dispatch projection applies the bounded Banach-valued weak partial-derivative operator. -/
@[simp] theorem partialDerivative_eq (i : Fin n) (u : W^{m + 1,p}(Ω; F)) :
    PDE.PartialDerivative.partialDeriv i u = partialDerivCLM i u :=
  rfl

/-- Taking a weak partial derivative does not increase the remaining graph norm. -/
theorem norm_partialDeriv_le (i : Fin n) (u : W^{m + 1,p}(Ω; F)) :
    ‖∂[i] u‖ ≤ ‖u‖ :=
  norm_derivativeWordCLM_apply_le [i] _ u

/-- Mixed weak partial derivatives commute as Sobolev functions. -/
theorem partialDeriv_commute (i j : Fin n) (u : W^{m + 2,p}(Ω; F)) :
    (∂[i] (∂[j] u) : W^{m,p}(Ω; F)) = ∂[j] (∂[i] u) := by
  change ((derivativeWordCLM [i] _).comp (derivativeWordCLM [j] _)) u =
    ((derivativeWordCLM [j] _).comp (derivativeWordCLM [i] _)) u
  rw [derivativeWordCLM_comp, derivativeWordCLM_comp]
  exact congrArg (fun L ↦ L u) (derivativeWordCLM_perm (List.Perm.swap _ _ []) _)

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display an applied weak derivative, leaving the unapplied bounded map visible. -/
@[delab app.DFunLike.coe]
def delabPartialDeriv : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  guard <| (e.getArg! 4).isAppOf ``partialDerivCLM
  let i ← withNaryArg 4 <| withAppArg delab
  let u ← withAppArg delab
  `(∂[$i] $u)

end

end SobolevSpace.VectorValued
