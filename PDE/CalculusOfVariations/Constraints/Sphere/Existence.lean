/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Sphere.Dirichlet
import PDE.Analysis.Normed.Reflexivity
import PDE.CalculusOfVariations.DirectMethod.CompactConstraint
import PDE.CalculusOfVariations.DirichletEnergy.FiniteProduct.Estimates
import PDE.CalculusOfVariations.WeakLowerSemicontinuity
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# Existence of sphere-valued Dirichlet minimizers

On a bounded open domain of positive dimension, every nonempty sphere-valued
Sobolev boundary class contains a Dirichlet minimizer. Rellich compactness
preserves the nonlinear constraint, since the pointwise norm is continuous in
L². Poincaré bounds the energy sublevels after subtracting the boundary data.
Neither boundary smoothness nor a restriction on the target dimension is needed
for existence. On a C¹ domain, the normalized-variation theorem then gives the
nonlinear weak harmonic-map equation for this minimizer.

Evans, §8.4.3, states the existence of a minimizer in a nonempty admissible class as
straightforward before proving the equation in Theorem 5.

## Main results

* `exists_sphere_dirichlet_minimizer`: a minimizer in every nonempty boundary class.
* `exists_sphere_dirichlet_minimizer_weak_equation`: on a bounded C¹ graph domain, a minimizer
  that also satisfies the weak harmonic-map equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.3, Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition
open scoped ENNReal InnerProductSpace Sobolev

private theorem isCompactOperator_baseCoord_family
    {n m : ℕ} {Ω : Set ℝ^n} (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    IsCompactOperator
      (ContinuousLinearMap.piMap fun _ : Fin m ↦ baseCoordCLM (n := n) (Ω := Ω)) := by
  classical
  let T := ContinuousLinearMap.piMap fun _ : Fin m ↦ baseCoordCLM (n := n) (Ω := Ω)
  have hsum : T = ∑ j : Fin m, (ContinuousLinearMap.single ℝ
      (fun _ : Fin m ↦ DerivLp n 2 Ω) j).comp
        (baseCoordCLM.comp (ContinuousLinearMap.proj j)) := by
    apply ContinuousLinearMap.ext
    intro v
    funext j
    simp [T, ContinuousLinearMap.piMap, Finset.sum_apply]
  change T ∈ compactOperator (RingHom.id ℝ) (Fin m → H¹₀(Ω)) (Fin m → DerivLp n 2 Ω)
  rw [hsum]
  apply Submodule.sum_mem
  intro j _
  exact ((baseCoordCLM.isCompactOperator_of_bounded hopen.measurableSet hbounded).comp_clm
    (ContinuousLinearMap.proj j : (Fin m → H¹₀(Ω)) →L[ℝ] H¹₀(Ω))).clm_comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin m ↦ DerivLp n 2 Ω) j)

private theorem norm_base_add_ae
    {n m : ℕ} {Ω : Set ℝ^n} (g : Fin m → H¹(Ω)) (v : Fin m → H¹₀(Ω)) :
    lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : ℝ^m)‖ = 0)
      (Lp.euclideanTuple (fun j ↦ wkpBaseCoordinateCLM (g j) + baseCoordCLM (v j))) =ᵐ[
        domainMeasure n Ω] fun x ↦ ‖values (fun j ↦ g j + (v j : H¹(Ω))) x‖ := by
  let q := fun j ↦ wkpBaseCoordinateCLM (g j) + baseCoordCLM (v j)
  have hbase : ∀ᵐ x ∂domainMeasure n Ω, ∀ j : Fin m,
      q j x = wkpBaseCoordinateCLM (g j + (v j : H¹(Ω))) x := by
    apply ae_all_iff.mpr
    intro j
    simp only [q, map_add]
    exact Filter.EventuallyEq.rfl
  filter_upwards [lipschitzWith_one_norm.coeFn_compLp (norm_zero : ‖(0 : ℝ^m)‖ = 0)
    (Lp.euclideanTuple q), Lp.euclideanTuple_apply_ae q, hbase] with x hn hx hb
  rw [hn, Function.comp_apply]
  congr 1
  exact PiLp.ext fun j ↦ (hx j).trans (hb j)

/-- A sphere-valued Dirichlet minimizer exists in every nonempty prescribed
Sobolev boundary class on a bounded open domain of positive dimension. The
boundary extension `g` itself need not take values on the sphere. -/
theorem exists_sphere_dirichlet_minimizer
    {n m : ℕ} (hn : 0 < n) {Ω : Set ℝ^n}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (g : Fin m → H¹(Ω))
    (hne : ∃ w : Fin m → H¹(Ω),
      (∀ᵐ x ∂domainMeasure n Ω, ‖values w x‖ = 1) ∧
      ∀ j, w j - g j ∈ (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule) :
    ∃ U : Fin m → H¹(Ω),
      (∀ᵐ x ∂domainMeasure n Ω, ‖values U x‖ = 1) ∧
      (∀ j, U j - g j ∈ (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule) ∧
      ∀ W : Fin m → H¹(Ω),
        (∀ᵐ x ∂domainMeasure n Ω, ‖values W x‖ = 1) →
        (∀ j, W j - g j ∈ (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule) →
        vectorDirichletEnergy U ≤ vectorDirichletEnergy W := by
  classical
  let μ := domainMeasure n Ω
  let : IsFiniteMeasure μ := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let E := Fin m → H¹₀(Ω)
  let Q := Fin m → Lp ℝ 2 μ
  let T : E →L[ℝ] Q := ContinuousLinearMap.piMap fun _ ↦ baseCoordCLM
  have hT : IsCompactOperator T := isCompactOperator_baseCoord_family hopen hbounded
  let G : Q := fun j ↦ wkpBaseCoordinateCLM (g j)
  let Ψ (q : Q) : Lp ℝ 2 μ :=
    lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : ℝ^m)‖ = 0)
      (Lp.euclideanTuple (G + q))
  have hΨ : Continuous Ψ :=
    (lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : ℝ^m)‖ = 0)).comp
      (Lp.euclideanTuple.continuous.comp (continuous_const.add continuous_id))
  let A : E →ᵃ[ℝ] (Fin m → H¹(Ω)) :=
    AffineMap.const ℝ E g +
      (ContinuousLinearMap.piMap
        fun _ : Fin m ↦ h10SubtypeL (n := n) (Ω := Ω)).toLinearMap.toAffineMap
  have hA (v : E) : A v = fun j ↦ g j + (v j : H¹(Ω)) := rfl
  have hrep (v : E) :
      Ψ (T v) =ᵐ[μ] fun x ↦ ‖values (A v) x‖ := norm_base_add_ae g v
  have hconstraint (v : E) :
      Ψ (T v) = Lp.const 2 μ (1 : ℝ) ↔
        ∀ᵐ x ∂μ, ‖values (A v) x‖ = 1 := by
    rw [Lp.ext_iff]
    constructor
    · intro hv
      filter_upwards [hv, hrep v, Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hy hz
      exact hy.symm.trans (hx.trans hz)
    · intro hv
      filter_upwards [hv, hrep v, Lp.coeFn_const 2 μ (1 : ℝ)] with x hx hy hz
      exact hy.trans (hx.trans hz.symm)
  let F := vectorDirichletEnergy ∘ A
  have hFconv : ConvexOn ℝ univ F := by
    simpa only [preimage_univ] using
      convexOn_vectorDirichletEnergy.comp_affineMap A
  have hFcont : Continuous F := by
    apply continuous_vectorDirichletEnergy.comp
    change Continuous (fun v : E ↦ g +
      (ContinuousLinearMap.piMap fun _ : Fin m ↦ h10SubtypeL (n := n) (Ω := Ω)) v)
    exact continuous_const.add (ContinuousLinearMap.piMap _).continuous
  obtain ⟨w, hwunit, hwboundary⟩ := hne
  let v₀ : E := fun j ↦ ⟨w j - g j, hwboundary j⟩
  have hv₀ : A v₀ = w := by
    funext j
    simp [hA, v₀]
  have hfeasible : Ψ (T v₀) ∈ ({Lp.const 2 μ (1 : ℝ)} : Set (Lp ℝ 2 μ)) := by
    apply (hconstraint v₀).mpr
    simpa only [hv₀] using hwunit
  have hreflexive : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ E) := by
    exact NormedSpace.surjective_inclusionInDoubleDual_pi (fun _ : Fin m ↦ H¹₀(Ω))
      (fun _ ↦ PDE.Analysis.inclusionInDoubleDual_surjective (H := H¹₀(Ω)))
  have hweak : LowerSemicontinuous
      (fun w : WeakSpace ℝ E ↦ F ((toWeakSpace ℝ E).symm w)) :=
    lowerSemicontinuous_weakSpace_of_convex F hFconv hFcont.lowerSemicontinuous
  have hboundedF : Bornology.IsBounded {v : E | F v ≤ F v₀} := by
    change Bornology.IsBounded {v : Fin m → H¹₀(Ω) |
      vectorDirichletEnergy (fun j ↦ g j + (v j : H¹(Ω))) ≤ F v₀}
    exact isBounded_sublevel_vectorDirichletEnergy hn hbounded g (F v₀)
  obtain ⟨v, hvunit, hvmin⟩ := exists_isMinOn_of_compact_constraint
    hreflexive T hT Ψ hΨ isClosed_singleton F hweak hfeasible hboundedF
  refine ⟨A v, (hconstraint v).mp hvunit, ?_, ?_⟩
  · intro j
    simpa only [hA, add_sub_cancel_left, h10SubmoduleOn] using (v j).property
  · intro W hWunit hWboundary
    let z : E := fun j ↦ ⟨W j - g j, hWboundary j⟩
    have hz : A z = W := by
      funext j
      simp [hA, z]
    have hzc : Ψ (T z) ∈ ({Lp.const 2 μ (1 : ℝ)} : Set (Lp ℝ 2 μ)) :=
      (hconstraint z).mpr (by simpa only [hz] using hWunit)
    have hzmin : F v ≤ F z := hvmin hzc
    change vectorDirichletEnergy (A v) ≤ vectorDirichletEnergy (A z) at hzmin
    rwa [hz] at hzmin

/-- A nonempty sphere-valued boundary class on a bounded C¹ graph domain (such a domain is
open) has a Dirichlet minimizer satisfying the nonlinear weak harmonic-map equation.
The equation is derived from the constructed minimum by normalized admissible
variations; no first-variation identity or additional regularity is assumed. -/
theorem exists_sphere_dirichlet_minimizer_weak_equation
    {n m : ℕ} {Ω : Set ℝ^(n + 1)}
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (g : Fin m → H¹(Ω))
    (hne : ∃ w : Fin m → H¹(Ω),
      (∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values w x‖ = 1) ∧
      ∀ j, w j - g j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule) :
    ∃ U : Fin m → H¹(Ω),
      (∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1) ∧
      (∀ j, U j - g j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule) ∧
      (∀ W : Fin m → H¹(Ω),
        (∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values W x‖ = 1) →
        (∀ j, W j - g j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule) →
        vectorDirichletEnergy U ≤ vectorDirichletEnergy W) ∧
      ∀ V : Fin m → H¹₀(Ω),
        MemLp (values (fun j ↦ (V j : H¹(Ω)))) ∞ (domainMeasure (n + 1) Ω) →
        (∫ x, ∑ i : Fin (n + 1),
          ⟪derivatives U i x, derivatives (fun j ↦ (V j : H¹(Ω))) i x⟫_ℝ
            ∂domainMeasure (n + 1) Ω) =
          ∫ x, (∑ i : Fin (n + 1), ‖derivatives U i x‖ ^ 2) *
            ⟪values U x, values (fun j ↦ (V j : H¹(Ω))) x⟫_ℝ
            ∂domainMeasure (n + 1) Ω := by
  have hopen : IsOpen Ω := by
    refine interior_eq_iff_isOpen.mp (interior_subset.antisymm fun x hx ↦ ?_)
    by_contra hint
    obtain ⟨e, g, -, hxg, hev⟩ := hgraph x ⟨subset_closure hx, hint⟩
    have h := hev.self_of_nhds.mp hx
    rw [hxg] at h
    exact lt_irrefl _ h
  obtain ⟨U, hunit, hboundary, hmin⟩ :=
    exists_sphere_dirichlet_minimizer (Nat.succ_pos n) hopen hbounded g hne
  exact ⟨U, hunit, hboundary, hmin,
    integral_inner_derivatives_eq_of_sphere_minimizer_of_local_graph
      hopen hbounded hgraph g U hunit hboundary hmin⟩

end PDE.CalculusOfVariations
