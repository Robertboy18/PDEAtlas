/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.FirstVariation
public import PDE.Elliptic.Regularity.Quasilinear.Global.H2
public import PDE.Spaces.Sobolev.Calculus.Composition.Flux.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Composition.Flux.L2
public import PDE.Spaces.Sobolev.Calculus.Divergence.FirstOrder
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# The domain of the L² gradient-energy subdifferential

Every L² subgradient supplies the weak divergence equation. Nonlinear
boundary regularity then gives an H² representative whose order-one
restriction is the original H¹₀ field. Conversely, the Sobolev chain
rule constructs the H¹ flux of an H² field; integration by parts gives
its L² subgradient. Density of H¹₀ in L² makes that subgradient unique.

This is Evans, §9.6.3, Theorem 4 (ii) and the single-valuedness in (iii),
for a bounded open set with `C²` graph boundary (Evans takes a smooth
boundary) and a `C²` density satisfying the Hessian bounds (28)-(29).
No regularity of the solution is assumed.

## Main results

* `subdifferentialDomain_l2DirichletGradientEnergy`: the domain of the
  subdifferential is `H² ∩ H¹₀`.
* `exists_flux_subdifferential_l2DirichletGradientEnergy_eq_singleton`: on
  that domain the subdifferential is the singleton of the negative
  divergence of an `H¹` flux.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.3, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev Gradient

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal NNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

local notation "μ" => domainMeasure n Ω

/-- The space `H² ∩ H¹₀` viewed in `L²`. The order restriction
requires agreement of the entire first-order Sobolev field. -/
def l2H2DirichletDomain (n : ℕ) (Ω : Set (ℝ^n)) : Set (DerivLp n 2 Ω) :=
  {x | ∃ W : W^{2,2}(Ω),
    lowerOrderCLM (by omega : 1 ≤ 2) W ∈ (h10SubmoduleOn (n := n) (Ω := Ω)) ∧
      wkpBaseCoordinateCLM W = x}

/-- Subgradient regularity recovers the original H¹₀ field.
The H² estimate depends on the load alone; its constant is chosen before
the field and load. Affine parts of the density require no normalization. -/
theorem exists_H2_of_mem_subdifferential_l2DirichletGradientEnergy [Fact (0 < n)]
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : H¹₀(Ω)) (f : DerivLp n 2 Ω),
      f ∈ subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u) →
      ∃ W : W^{2,2}(Ω),
        lowerOrderCLM (by omega : 1 ≤ 2) W = u.val ∧ ‖W‖ ≤ M * ‖f‖ := by
  have hLip := Analysis.lipschitzWith_gradient_of_hessian_bound hL hupper
  obtain ⟨M, hM, hregularity⟩ :=
    Elliptic.Regularity.Quasilinear.exists_H2_of_monotone_weakEquation_of_graphBoundary
      hΩ hbounded hgraph (∇ L) hθ
      (Analysis.strongMonotonicity_gradient_of_hessian_bound hL hlower) hLip
  refine ⟨M, hM, ?_⟩
  intro u f hf
  obtain ⟨q, hq⟩ := exists_L2_flux_of_lipschitz hbounded hLip (u : H¹(Ω))
  have hweak := (mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
    hΩ hbounded hL hθ hlower hupper u f q hq).mp hf
  obtain ⟨W, hW, hWnorm⟩ := hregularity u q f hq hweak
  refine ⟨W, WkpSpaceOn.ext_of_base_ae hΩ _ _ ?_, hWnorm⟩
  change baseRepresentative (lowerOrderCLM (by omega : 1 ≤ 2) W) =ᵐ[μ] _
  rw [baseRepresentative_lowerOrderCLM]
  exact hW

/-- The L² load represented by the first variation is unique, by density
of the Dirichlet space in the ambient L² space. -/
theorem eq_of_mem_subdifferential_l2DirichletGradientEnergy
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (u : H¹₀(Ω)) {f g : DerivLp n 2 Ω}
    (hf : f ∈ subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u))
    (hg : g ∈ subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u)) : f = g := by
  obtain ⟨q, hq⟩ := exists_L2_flux_of_lipschitz hbounded
    (Analysis.lipschitzWith_gradient_of_hessian_bound hL hupper) (u : H¹(Ω))
  have hf' := (mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
    hΩ hbounded hL hθ hlower hupper u f q hq).mp hf
  have hg' := (mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
    hΩ hbounded hL hθ hlower hupper u g q hq).mp hg
  exact (baseCoordCLM_denseRange hΩ).eq_of_inner_left ℝ
    fun v ↦ (hf' v).symm.trans (hg' v)

/-- The negative weak divergence of the H¹ flux is the unique L² subgradient.
The next theorem constructs this flux from the density and the geometry. -/
theorem subdifferential_l2DirichletGradientEnergy_eq_singleton_of_flux
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (u : H¹₀(Ω)) (Q : Fin n → H¹(Ω))
    (hQ : ∀ᵐ x ∂μ, ∀ i, wkpBaseCoordinateCLM (Q i) x =
      ∇ L (WithLp.toLp 2 (fun j ↦ derivCoordCLM j u x)) i) :
    subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u) =
      {negativeDivergence Q} := by
  have hq : ∀ᵐ x ∂μ,
      ∇ L (WithLp.toLp 2 (fun j ↦ derivCoordCLM j u x)) =
        WithLp.toLp 2 (fun i ↦ wkpBaseCoordinateCLM (Q i) x) :=
    hQ.mono fun _ hx ↦ PiLp.ext fun i ↦ (hx i).symm
  have hmem : negativeDivergence Q ∈
      subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u) :=
    (mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
      hΩ hbounded hL hθ hlower hupper u (negativeDivergence Q)
      (fun i ↦ wkpBaseCoordinateCLM (Q i)) hq).mpr
        fun v ↦ (negativeDivergence_pairing Q v).symm
  ext f
  constructor
  · intro hf
    exact mem_singleton_iff.mpr
      (eq_of_mem_subdifferential_l2DirichletGradientEnergy
        hΩ hbounded hL hθ hlower hupper u hf hmem)
  · rintro rfl
    exact hmem

/-- Every H² Dirichlet field has an H¹ nonlinear flux, and the
subdifferential is the singleton of its negative divergence. The regularity
comes from the graph boundary and the Hessian assumptions. -/
theorem exists_flux_subdifferential_l2DirichletGradientEnergy_eq_singleton [Fact (0 < n)]
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (W : W^{2,2}(Ω)) (u : H¹₀(Ω))
    (hu : lowerOrderCLM (by omega : 1 ≤ 2) W = u.val) :
    ∃ Q : Fin n → H¹(Ω),
      (∀ᵐ x ∂μ, ∀ i, wkpBaseCoordinateCLM (Q i) x =
        ∇ L (WithLp.toLp 2 (fun j ↦ derivCoordCLM j u x)) i) ∧
      (∀ᵐ x ∂μ, ∀ i j,
        wkpCoordinateCLM (singleDerivIndex n j) (Q i) x =
          fderiv ℝ (∇ L)
            (FiniteProductComposition.values (h2FirstDerivativeFamily W) x)
            (FiniteProductComposition.derivatives (h2FirstDerivativeFamily W) j x) i) ∧
      subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u) =
        {negativeDivergence Q} := by
  let P := hgraph.c2BoundaryAtlas le_rfl hΩ hbounded
  obtain ⟨Q, hQ, hDQ⟩ := exists_H1_flux_of_H2 P.toC1ExtensionAtlas
    (Analysis.contDiff_gradient_of_contDiff_two hL)
    (Analysis.lipschitzWith_gradient_of_hessian_bound hL hupper) W
  have hQ' : ∀ᵐ x ∂μ, ∀ i, wkpBaseCoordinateCLM (Q i) x =
      ∇ L (WithLp.toLp 2 (fun j ↦ derivCoordCLM j u x)) i := by
    simpa only [hu, wkpCoordinateCLM_apply, derivCoordCLM_apply] using hQ
  exact ⟨Q, hQ', hDQ, subdifferential_l2DirichletGradientEnergy_eq_singleton_of_flux
    hΩ hbounded hL hθ hlower hupper u Q hQ'⟩

/-- The full domain is exactly H² with the homogeneous
Dirichlet boundary condition, in every positive dimension. -/
theorem subdifferentialDomain_l2DirichletGradientEnergy [Fact (0 < n)]
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    subdifferentialDomain (l2DirichletGradientEnergy (Ω := Ω) L) =
      l2H2DirichletDomain n Ω := by
  obtain ⟨M, _, hregularity⟩ := exists_H2_of_mem_subdifferential_l2DirichletGradientEnergy
    hΩ hbounded hgraph hL hθ hlower hupper
  ext x
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨u, rfl⟩ := (l2DirichletGradientEnergy_ne_top_iff hΩ L x).mp
      (ne_top_of_mem_subdifferential (isProper_l2DirichletGradientEnergy L) hf)
    obtain ⟨W, hW, _⟩ := hregularity u f hf
    refine ⟨W, by rw [hW]; exact u.property, ?_⟩
    have hb := congrArg wkpBaseCoordinateCLM hW
    simpa only [wkpBaseCoordinateCLM_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex, baseCoordCLM_apply] using hb
  · rintro ⟨W, hW, rfl⟩
    let u : H¹₀(Ω) := ⟨lowerOrderCLM (by omega : 1 ≤ 2) W, hW⟩
    obtain ⟨Q, _, _, hQ⟩ := exists_flux_subdifferential_l2DirichletGradientEnergy_eq_singleton
      hΩ hbounded hgraph hL hθ hlower hupper W u rfl
    have hu : baseCoordCLM u = wkpBaseCoordinateCLM W := by
      simp only [baseCoordCLM_apply, u, lowerOrderCLM_apply,
        DerivIndex.castOrder_baseIndex, wkpBaseCoordinateCLM_apply]
    change (subdifferential (l2DirichletGradientEnergy L) (wkpBaseCoordinateCLM W)).Nonempty
    rw [← hu, hQ]
    exact singleton_nonempty _

end PDE.CalculusOfVariations
