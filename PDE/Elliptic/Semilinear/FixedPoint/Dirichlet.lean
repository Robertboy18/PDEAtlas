/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.DirichletNemytskii
import PDE.Elliptic.Semilinear.FixedPoint.Contraction
import PDE.Elliptic.Semilinear.Monotonicity

/-!
# Picard theory for a small-Lipschitz semilinear Dirichlet problem

We specialize the abstract Chapter 9 contraction theorem to
`H¹₀(Ω)`.  A scalar Lipschitz function vanishing at zero acts on `L²(Ω)` by
composition.  Pairing that Nemytskii map with test functions gives a
Lipschitz nonlinear load on `H¹₀(Ω)`.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory ENNReal
open scoped InnerProductSpace NNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The `L²(Ω)` Nemytskii map induced by a Lipschitz scalar nonlinearity
vanishing at zero. -/
noncomputable def dirichletNemytskii
    (g : ℝ → ℝ) {K : NNReal}
    (hg : LipschitzWith K g) (hg0 : g 0 = 0)
    (u : H¹₀(Ω)) :
    DerivLp n 2 Ω :=
  hg.compLp hg0 (baseCoordCLM u)

/-- The `L²` representative of `dirichletNemytskii` is pointwise composition
with the scalar nonlinearity. -/
theorem dirichletNemytskii_ae_eq
    (g : ℝ → ℝ) {K : NNReal}
    (hg : LipschitzWith K g) (hg0 : g 0 = 0)
    (u : H¹₀(Ω)) :
    ((dirichletNemytskii g hg hg0 u : DerivLp n 2 Ω) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ g
        ((baseCoordCLM u : DerivLp n 2 Ω) x) := by
  change
    (hg.compLp hg0 (baseCoordCLM u) :
        ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      g ∘ (baseCoordCLM u : DerivLp n 2 Ω)
  exact hg.coeFn_compLp hg0 (baseCoordCLM u)

/-- The nonlinear dual load
`v ↦ ⟪g(u), v⟫_{L²(Ω)}` induced by a Lipschitz scalar nonlinearity. -/
noncomputable def dirichletNemytskiiLoad
    (g : ℝ → ℝ) {K : NNReal}
    (hg : LipschitzWith K g) (hg0 : g 0 = 0)
    (u : H¹₀(Ω)) :
    StrongDual ℝ (H¹₀(Ω)) :=
  loadFunctional
    (dirichletNemytskii g hg hg0 u)

/-- The `H¹₀(Ω)` Nemytskii load has the same Lipschitz constant as the scalar
nonlinearity.  Both the base-coordinate projection and the `L²` load map have
operator norm at most one. -/
theorem dirichletNemytskiiLoad_lipschitzWith
    (g : ℝ → ℝ) {K : NNReal}
    (hg : LipschitzWith K g) (hg0 : g 0 = 0) :
    LipschitzWith K
      (dirichletNemytskiiLoad (n := n) (Ω := Ω) g hg hg0) := by
  apply LipschitzWith.of_dist_le_mul
  intro u w
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖dirichletNemytskiiLoad g hg hg0 u -
        dirichletNemytskiiLoad g hg hg0 w‖ =
        ‖loadFunctional
          (hg.compLp hg0 (baseCoordCLM u) -
           hg.compLp hg0 (baseCoordCLM w))‖ := by
      rw [loadFunctional_sub]
      rfl
    _ ≤ ‖hg.compLp hg0 (baseCoordCLM u) -
            hg.compLp hg0 (baseCoordCLM w)‖ :=
      norm_loadFunctional_le _
    _ ≤ (K : ℝ) *
          ‖baseCoordCLM u - baseCoordCLM w‖ :=
      hg.norm_compLp_sub_le hg0 _ _
    _ = (K : ℝ) * ‖baseCoordCLM (u - w)‖ := by
      rw [map_sub]
    _ ≤ (K : ℝ) * ‖u - w‖ :=
      mul_le_mul_of_nonneg_left
        (baseCoordCLM_norm_le (u - w))
        (NNReal.coe_nonneg K)

/-- The Nemytskii-load form of the semilinear weak Dirichlet equation

`B(u,v) + ⟪g(u),v⟫_{L²} = ⟪f,v⟫_{L²}`

has a unique `H¹₀(Ω)` solution when the scalar Lipschitz constant is smaller
than an explicit coercivity modulus of the Dirichlet form. -/
theorem existsUnique_dirichlet_nemytskii_load_of_lipschitz_lt_coercivity
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ u : H¹₀(Ω),
      c * ‖u‖ * ‖u‖ ≤ dirichletForm u u)
    (g : ℝ → ℝ) {K : NNReal} (hg : LipschitzWith K g)
    (hg0 : g 0 = 0) (hsmall : (K : ℝ) < c)
    (f : DerivLp n 2 Ω) :
    ∃! u : H¹₀(Ω),
      ∀ v : H¹₀(Ω),
        dirichletForm u v +
            dirichletNemytskiiLoad g hg hg0 u v =
          loadFunctional f v := by
  exact @Weak.existsUnique_semilinear_of_lipschitz_lt_coercivity
    (H¹₀(Ω))
    inferInstance
    inferInstance
    inferInstance
    (dirichletForm) c hc hcoercive
    (dirichletNemytskiiLoad g hg hg0) K
    (dirichletNemytskiiLoad_lipschitzWith g hg hg0)
    hsmall (loadFunctional f)

/-- The semilinear Dirichlet problem

`-Δu + g(u) = f`, `u|∂Ω = 0`,

has a unique weak solution when the Lipschitz constant of `g` is smaller than
an explicit coercivity modulus of the Dirichlet form. -/
theorem existsUnique_dirichlet_semilinear_of_lipschitz_lt_coercivity
    (c : ℝ) (hc : 0 < c)
    (hcoercive : ∀ u : H¹₀(Ω),
      c * ‖u‖ * ‖u‖ ≤ dirichletForm u u)
    (g : ℝ → ℝ) {K : NNReal} (hg : LipschitzWith K g)
    (hg0 : g 0 = 0) (hsmall : (K : ℝ) < c)
    (f : DerivLp n 2 Ω) :
    ∃! u : H¹₀(Ω),
      IsDirichletSemilinearWeakSolution (fun _ ↦ g) f u := by
  obtain ⟨u, hu, hunique⟩ :=
    existsUnique_dirichlet_nemytskii_load_of_lipschitz_lt_coercivity
      c hc hcoercive g hg hg0 hsmall f
  refine ⟨u, ?_, fun w hw ↦ hunique w ?_⟩
  · exact
      (isDirichletSemilinearWeakSolution_iff_nemytskii_load
        (fun _ ↦ g)
        (dirichletNemytskii g hg hg0)
        (dirichletNemytskii_ae_eq g hg hg0)
        f u).mpr hu
  · exact
      (isDirichletSemilinearWeakSolution_iff_nemytskii_load
        (fun _ ↦ g)
        (dirichletNemytskii g hg hg0)
        (dirichletNemytskii_ae_eq g hg hg0)
        f w).mp hw

/-- Solutions of the small-Lipschitz semilinear Dirichlet equation depend
continuously on the `L²` forcing. The stability constant is the reciprocal of
the same coercivity gap `c - K` that drives the contraction argument. -/
theorem norm_sub_le_forcing_sub_norm_div_of_nemytskii_load
    (c : ℝ)
    (hcoercive : ∀ u : H¹₀(Ω),
      c * ‖u‖ * ‖u‖ ≤ dirichletForm u u)
    (g : ℝ → ℝ) {K : NNReal} (hg : LipschitzWith K g)
    (hg0 : g 0 = 0) (hKc : (K : ℝ) < c)
    {f₁ f₂ : DerivLp n 2 Ω}
    {u₁ u₂ : H¹₀(Ω)}
    (hu₁ : ∀ v : H¹₀(Ω),
      dirichletForm u₁ v +
          dirichletNemytskiiLoad g hg hg0 u₁ v =
        loadFunctional f₁ v)
    (hu₂ : ∀ v : H¹₀(Ω),
      dirichletForm u₂ v +
          dirichletNemytskiiLoad g hg hg0 u₂ v =
        loadFunctional f₂ v) :
    ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / (c - K) := by
  calc
    ‖u₁ - u₂‖ ≤
        ‖loadFunctional f₁ - loadFunctional f₂‖ /
          (c - K) :=
      @Weak.norm_sub_le_load_sub_norm_div_of_lipschitz_lt_coercivity
        (H¹₀(Ω))
        inferInstance
        inferInstance
        (dirichletForm) c hcoercive
        (dirichletNemytskiiLoad g hg hg0) K
        (dirichletNemytskiiLoad_lipschitzWith g hg hg0)
        hKc
        (loadFunctional f₁)
        (loadFunctional f₂)
        u₁ u₂ hu₁ hu₂
    _ ≤ ‖f₁ - f₂‖ / (c - K) := by
      apply div_le_div_of_nonneg_right _ (sub_pos.mpr hKc).le
      rw [← loadFunctional_sub f₁ f₂]
      exact norm_loadFunctional_le (f₁ - f₂)

/-- Weak solutions of the small-Lipschitz semilinear Dirichlet equation depend
continuously on the `L²` forcing, with stability constant `(c - K)⁻¹`. -/
theorem norm_sub_le_forcing_sub_norm_div_of_lipschitz_lt_coercivity
    (c : ℝ)
    (hcoercive : ∀ u : H¹₀(Ω),
      c * ‖u‖ * ‖u‖ ≤ dirichletForm u u)
    (g : ℝ → ℝ) {K : NNReal} (hg : LipschitzWith K g)
    (hg0 : g 0 = 0) (hKc : (K : ℝ) < c)
    {f₁ f₂ : DerivLp n 2 Ω}
    {u₁ u₂ : H¹₀(Ω)}
    (hu₁ : IsDirichletSemilinearWeakSolution
      (fun _ ↦ g) f₁ u₁)
    (hu₂ : IsDirichletSemilinearWeakSolution
      (fun _ ↦ g) f₂ u₂) :
    ‖u₁ - u₂‖ ≤ ‖f₁ - f₂‖ / (c - K) := by
  apply norm_sub_le_forcing_sub_norm_div_of_nemytskii_load
    c hcoercive g hg hg0 hKc
  · exact
      (isDirichletSemilinearWeakSolution_iff_nemytskii_load
        (fun _ ↦ g)
        (dirichletNemytskii g hg hg0)
        (dirichletNemytskii_ae_eq g hg hg0)
        f₁ u₁).mp hu₁
  · exact
      (isDirichletSemilinearWeakSolution_iff_nemytskii_load
        (fun _ ↦ g)
        (dirichletNemytskii g hg hg0)
        (dirichletNemytskii_ae_eq g hg hg0)
        f₂ u₂).mp hu₂

end SobolevSpace.GraphSpace
