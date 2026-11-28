/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.HalfPlaneSystem.APrioriHolder
public import PDE.Fluid.HalfPlaneSystem.Forcing
import PDE.Analysis.Calculus.SliceDerivative
import PDE.Analysis.Integration.Primitive.Local
import PDE.Fluid.Boussinesq.HalfPlane.CarriedFields

/-!
# The top-order derivatives of solutions of a half-plane system along trajectories

The gradient of the vorticity and the Hessian of the temperature are the highest derivatives of the
class of the data. This module derives the equations they solve along the particle trajectories and
shows that these equations need no derivative of the solution beyond that class, which is what lets
the continuation estimate close. No bound is proved here: the equations are identities, and their
Grönwall bounds are in `APrioriTopBounds.lean`.

For a solution on `[0, b]` whose velocity is a `C¹` field, whose vorticity is a `C^{1,α}` history
and whose slices are of the class `IsHolderData`, the field of the law `lawField U ω` is a `C²`
field whose flow and first variation agree on the closed half-plane `H̄` with those of the
solution's velocity. Along a trajectory `X(r, a)` of this flow, with first variation `J`, inverse
first variation `W` and second variation `S`:

* the Hessian of the temperature satisfies `D²θ_r(X)[J u, J w] + Dθ_r(X)(S[u, w]) = D²θ₀(a)[u, w]`,
  hence `H(r, a) = D²θ_r(X(r, a))` has the closed form
  `H[u, w] = D²θ₀(a)[W u, W w] - Dθ₀(a)(W S[W u, W w])` and solves
  `∂ᵣ H = -H[Du ·, ·] - H[·, Du ·] - Dθ_r(X) ∘ D²u`;
* the vorticity is the forced amplitude of the extended data at the label with the weighted forcing
  `κ(X) ∂₀θ`, so its gradient has a label form and `Z(r, a) = Dω_r(X(r, a))` solves
  `∂ᵣ Z = κ(X) H[·, e₀] + (∂₀θ_r(X)) Dκ(X) - Z ∘ Du`.

These equations need no second derivative of the vorticity and no third derivative of the
temperature: the closed forms are differentiated in time, not in space. Their coefficients involve
`Du` only through its size and `D²u` only linearly.

## Main results

* `IsSolutionOn.exists_isC1VorticityHistory`: the vorticity of a solution is a `C^{1,α}` history on
  a compact interval of times on which its gradient is `α`-Hölder with a common constant, with a
  support radius less than `R₀`.
* `IsSolutionOn.flowOn_eq_lawField`, `IsSolutionOn.variationOn_eq_lawField`,
  `IsSolutionOn.velocityFieldDeriv_eq_lawFieldDeriv`, `IsSolutionOn.mapsTo_flowOn_lawField`: on `H̄`
  the flow, the first variation and the derivative of the velocity of the solution are those of the
  field of the law, and that flow keeps `H̄`.
* `IsSolutionOn.hessian_flowOn_comp`, `IsSolutionOn.hessian_flowOn_eq`,
  `IsSolutionOn.hasDerivWithinAt_hessian`: the identity, the closed form and the equation of the
  Hessian of the temperature along a trajectory.
* `IsSolutionOn.vorticity_eq_forcedAmplitude`, `IsSolutionOn.fderivWithin_vorticity_eq`,
  `IsSolutionOn.hasDerivWithinAt_vorticityGradient`: the label form of the vorticity and of its
  gradient, and the equation of the gradient along a trajectory.
* `vorticityGradientTransport`, `norm_vorticityGradientTransport_le`,
  `norm_vorticityGradientTransport_sub_le`: the right-hand side of the equation of the vorticity
  gradient, its size and the size of the difference of two such terms.
* `IsSolutionOn.continuousOn_gradient_flowOn`, `IsSolutionOn.continuousOn_hessian_flowOn`,
  `IsSolutionOn.continuousOn_vorticityGradient_flowOn`, `IsSolutionOn.continuousOn_deriv₂_flowOn`:
  the quantities along a trajectory are continuous in time.

`APrioriTopBounds.lean` applies Grönwall's inequality to the two equations, `APriori.lean` uses the
identification of the two flows, and `APrioriEstimate.lean` uses
`IsSolutionOn.exists_isC1VorticityHistory`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory PDE.Analysis.ODE IncompressibleFlow PDE.Hyperbolic.Transport
  Boussinesq.HalfPlane
open scoped Topology NNReal

namespace HalfPlaneSystem

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The right-hand side `k H[·, e₀] + (G e₀) Dk - Z ∘ D` of the equation of the gradient `Z` of
the vorticity along a trajectory, with `k` and `Dk` the forcing coefficient and its derivative,
`H` and `G` the Hessian and the gradient of the temperature and `D` the derivative of the
field. -/
def vorticityGradientTransport (k : ℝ) (Dk : ℝ^2 →L[ℝ] ℝ) (H : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ)
    (G Z : ℝ^2 →L[ℝ] ℝ) (D : ℝ^2 →L[ℝ] ℝ^2) : ℝ^2 →L[ℝ] ℝ :=
  k • (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 0 1 : ℝ^2)).comp H +
    G (EuclideanSpace.single 0 1) • Dk - Z.comp D

/-- `‖H[·, e₀]‖ ≤ ‖H‖`. -/
theorem norm_apply_single_comp_le (H : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ) :
    ‖(ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 0 1 : ℝ^2)).comp H‖ ≤ ‖H‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H) fun u ↦ by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
    calc ‖H u (EuclideanSpace.single 0 1)‖ ≤ ‖H u‖ * 1 := by
          simpa [he] using (H u).le_opNorm (EuclideanSpace.single 0 1)
      _ ≤ ‖H‖ * ‖u‖ := by rw [mul_one]; exact H.le_opNorm u

/-- `|G e₀| ≤ ‖G‖`. -/
theorem abs_apply_single_le (G : ℝ^2 →L[ℝ] ℝ) : |G (EuclideanSpace.single 0 1)| ≤ ‖G‖ := by
  have he : ‖(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2)‖ = 1 := by simp
  rw [← Real.norm_eq_abs]
  simpa [he] using G.le_opNorm (EuclideanSpace.single 0 1)

/-- `‖k H[·, e₀] + (G e₀) Dk - Z ∘ D‖ ≤ |k| ‖H‖ + ‖G‖ ‖Dk‖ + ‖D‖ ‖Z‖`. -/
theorem norm_vorticityGradientTransport_le (k : ℝ) (Dk : ℝ^2 →L[ℝ] ℝ)
    (H : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ) (G Z : ℝ^2 →L[ℝ] ℝ) (D : ℝ^2 →L[ℝ] ℝ^2) :
    ‖vorticityGradientTransport k Dk H G Z D‖ ≤ |k| * ‖H‖ + ‖G‖ * ‖Dk‖ + ‖D‖ * ‖Z‖ := by
  have h1 : ‖k • (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 0 1 : ℝ^2)).comp H‖ ≤
      |k| * ‖H‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_apply_single_comp_le H) (abs_nonneg _)
  have h2 : ‖G (EuclideanSpace.single 0 1) • Dk‖ ≤ ‖G‖ * ‖Dk‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_apply_single_le G) (norm_nonneg _)
  have h3 : ‖Z.comp D‖ ≤ ‖D‖ * ‖Z‖ := (Z.opNorm_comp_le D).trans_eq (mul_comm _ _)
  have h4 := norm_add_le
    (k • (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 0 1 : ℝ^2)).comp H)
    (G (EuclideanSpace.single 0 1) • Dk)
  rw [vorticityGradientTransport]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The difference of two such fields is at most
`|k| ‖H - H'‖ + |k - k'| ‖H'‖ + ‖G - G'‖ ‖Dk‖ + ‖G'‖ ‖Dk - Dk'‖ + ‖D‖ ‖Z - Z'‖ + ‖Z'‖ ‖D - D'‖`. -/
theorem norm_vorticityGradientTransport_sub_le (k k' : ℝ) (Dk Dk' : ℝ^2 →L[ℝ] ℝ)
    (H H' : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ) (G G' Z Z' : ℝ^2 →L[ℝ] ℝ) (D D' : ℝ^2 →L[ℝ] ℝ^2) :
    ‖vorticityGradientTransport k Dk H G Z D - vorticityGradientTransport k' Dk' H' G' Z' D'‖ ≤
      |k| * ‖H - H'‖ + |k - k'| * ‖H'‖ + ‖G - G'‖ * ‖Dk‖ + ‖G'‖ * ‖Dk - Dk'‖ +
        ‖D‖ * ‖Z - Z'‖ + ‖Z'‖ * ‖D - D'‖ := by
  set P := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single 0 1 : ℝ^2))
  set e : ℝ^2 := EuclideanSpace.single 0 1
  have hsplit : vorticityGradientTransport k Dk H G Z D -
      vorticityGradientTransport k' Dk' H' G' Z' D' =
        (k • P.comp (H - H') + (k - k') • P.comp H') +
          ((G - G') e • Dk + G' e • (Dk - Dk')) - ((Z - Z').comp D + Z'.comp (D - D')) := by
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simp only [vorticityGradientTransport, P, e, add_apply, sub_apply,
      smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.apply_apply, smul_eq_mul, map_sub]
    ring
  have h1 : ‖k • P.comp (H - H')‖ ≤ |k| * ‖H - H'‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_apply_single_comp_le _) (abs_nonneg _)
  have h2 : ‖(k - k') • P.comp H'‖ ≤ |k - k'| * ‖H'‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_apply_single_comp_le _) (abs_nonneg _)
  have h3 : ‖(G - G') e • Dk‖ ≤ ‖G - G'‖ * ‖Dk‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_apply_single_le _) (norm_nonneg _)
  have h4 : ‖G' e • (Dk - Dk')‖ ≤ ‖G'‖ * ‖Dk - Dk'‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_apply_single_le _) (norm_nonneg _)
  have h5 : ‖(Z - Z').comp D‖ ≤ ‖D‖ * ‖Z - Z'‖ :=
    ((Z - Z').opNorm_comp_le D).trans_eq (mul_comm _ _)
  have h6 : ‖Z'.comp (D - D')‖ ≤ ‖Z'‖ * ‖D - D'‖ := Z'.opNorm_comp_le _
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have := norm_add_le (k • P.comp (H - H') + (k - k') • P.comp H')
    ((G - G') e • Dk + G' e • (Dk - Dk'))
  have := norm_add_le (k • P.comp (H - H')) ((k - k') • P.comp H')
  have := norm_add_le ((G - G') e • Dk) (G' e • (Dk - Dk'))
  have := norm_add_le ((Z - Z').comp D) (Z'.comp (D - D'))
  linarith

variable {U : (ℝ^2 → ℝ) → ℝ^2 → ℝ^2} {R₀ : ℝ} {C : ℕ → ℝ → ℝ} {κ : ℝ^2 → ℝ} {Bκ : ℕ → ℝ}

namespace IsSolutionOn

variable {sol : Fields} {I : Set ℝ} {b : ℝ}

set_option quotPrecheck false in
/-- The field of the law at the vorticity history. -/
local notation "𝐯" => lawField U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its spatial derivative. -/
local notation "𝐃𝐯" => lawFieldDeriv U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- Its second spatial derivative. -/
local notation "𝐃²𝐯" => lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t

set_option quotPrecheck false in
/-- The position at time `ρ` of the particle of label `a` for the flow of the history. -/
local notation "𝐗 " ρ:max a:max => flowOn 𝐯 0 b ρ 0 a

set_option quotPrecheck false in
/-- The temperature gradient along the particle of label `a`. -/
local notation "𝐆 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The Hessian of the temperature along the particle of label `a`. -/
local notation "𝐇 " ρ:max a:max =>
  fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (𝐗 ρ a)

set_option quotPrecheck false in
/-- The vorticity gradient along the particle of label `a`. -/
local notation "𝐙 " ρ:max a:max => fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (𝐗 ρ a)

/-- **The vorticity of a solution is a `C^{1,α}` history** on compact intervals of times on which
its gradient within the closed half-plane is `α`-Hölder with a common constant `M₁`, with a
support radius less than `R₀`. -/
theorem exists_isC1VorticityHistory (h : IsSolutionOn U κ R₀ sol I) {a α M₁ : ℝ} (hab : a < b)
    (hI : Icc a b ⊆ I) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hM₁ : ∀ t ∈ Icc a b, ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ y -
        fderivWithin ℝ (fun x ↦ sol.vorticity x t) H̄ z‖ ≤ M₁ * ‖y - z‖ ^ α) :
    ∃ R < R₀, ∃ B M B₁ : ℝ,
      IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) a b α R B M B₁ M₁ := by
  obtain ⟨R, hRR₀, hR⟩ := h.support a b hI
  obtain ⟨B, B₁, -, -, hB, hB₁, hu, hu₁⟩ :=
    PDE.Analysis.exists_bounds_of_contDiffOn (f := sol.vorticity) hab hI
      h.vorticity_contDiffOn fun t ht x hx hxR ↦ (hR t ht x hx hxR).1
  have hc (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (fun x ↦ sol.vorticity x t) :=
    h.contDiff_vorticity (hI ht)
  have hfd (t : ℝ) (ht : t ∈ Icc a b) {x : ℝ^2} (hx : 0 ≤ x 1) :
      fderivWithin ℝ (fun y ↦ sol.vorticity y t) H̄ x =
        fderiv ℝ (fun y ↦ sol.vorticity y t) x :=
    ((hc t ht).differentiable (by norm_num) x).fderivWithin (uniqueDiffOn_closedUpper x hx)
  refine ⟨R, hRR₀, B, max B₁ (2 * B), B₁,
    { toIsVorticityHistory := IsVorticityHistory.of_fderivWithin_le
        (fun t ht ↦ (hc t ht).contDiffOn) (fun t ht x hx hxR ↦ (hR t ht x hx hxR).1) hB
        (fun t ht x hx ↦ by rw [hfd t ht hx]; exact hB₁ t ht x hx) hu hα0 hα1
      contDiffOn := fun t ht ↦ (hc t ht).contDiffOn
      norm_fderivWithin_le := fun t ht x hx ↦ by rw [hfd t ht hx]; exact hB₁ t ht x hx
      holder_fderivWithin := hM₁
      uniform_fderivWithin := fun t ht ε hε ↦ ?_ }⟩
  obtain ⟨δ, hδ, hδε⟩ := hu₁ t ht ε hε
  exact ⟨δ, hδ, fun s hs hst x hx ↦ by rw [hfd s hs hx, hfd t ht hx]; exact hδε s hs hst x hx⟩

section Bridge

variable {α R B M B₁ M₁ : ℝ} {K : ℝ≥0}
  (hU : IsVelocityLaw U R₀ C) (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R B M B₁ M₁) (hR : R ≤ R₀)
  (hα : 0 < α) (hα1 : α < 1)

include hU hω hR in
/-- The flow of the field of the history keeps the closed half-plane. -/
theorem mapsTo_flowOn_lawField {K₁ : ℝ≥0} (hv₁ : IsLipschitzFieldOn 𝐯 0 b K₁) :
    ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, MapsTo (flowOn 𝐯 0 b s t) H̄ H̄ :=
  fun _ hs _ ht ↦ (hv₁.bijOn_flowOn_nonneg (j := 1)
    (fun _ hr _ hx ↦ lawField_normal_eq_zero hU hω.toIsVorticityHistory hR hr hx) hs ht).mapsTo

/-- On the closed half-plane the velocity field of the solution is the field of the law at its
vorticity history. -/
theorem velocityField_eq_lawField (r : ℝ) {y : ℝ^2} (hy : 0 ≤ y 1) :
    velocityField U sol r y = 𝐯 r y := by
  rw [velocityField_eq hy, lawField_of_nonneg U _ r hy]

include hU h hb hI hω hR hα hα1 in
/-- On the closed half-plane the derivatives of the two velocity fields agree. -/
theorem velocityFieldDeriv_eq_lawFieldDeriv {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2}
    (hy : 0 ≤ y 1) : velocityFieldDeriv U sol r y = 𝐃𝐯 r y := by
  rw [h.velocityFieldDeriv_eq hU hb hI hr hy, lawFieldDeriv_eq hU hω hR hα hα1 hr hy]

include hU hv hω hR in
/-- **The two flows agree** on the closed half-plane. -/
theorem flowOn_eq_lawField {K₁ : ℝ≥0} (hv₁ : IsLipschitzFieldOn 𝐯 0 b K₁) {s t : ℝ}
    (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    flowOn (velocityField U sol) 0 b s t x = flowOn 𝐯 0 b s t x :=
  flowOn_eq_of_eqOn hv.isLipschitzFieldOn hv₁ (mapsTo_flowOn_lawField hU hω hR hv₁)
    (fun r _ _ hy ↦ velocityField_eq_lawField r hy) hs ht hx

include hU h hb hI hv hω hR hα hα1 in
/-- **The two first variations agree** on the closed half-plane. -/
theorem variationOn_eq_lawField {K₁ : ℝ≥0} (hv₁ : IsC1FieldOn 𝐯 𝐃𝐯 0 b K₁) {s t : ℝ}
    (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    variationOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b s t x =
      variationOn 𝐯 𝐃𝐯 0 b s t x :=
  hv.variationOn_eq_of_eqOn hv₁ (mapsTo_flowOn_lawField hU hω hR hv₁.isLipschitzFieldOn)
    (fun r _ _ hy ↦ velocityField_eq_lawField r hy)
    (fun _ hr _ hy ↦ h.velocityFieldDeriv_eq_lawFieldDeriv hU hb hI hω hR hα hα1 hr hy) hs ht hx

end Bridge

section Hessian

variable {α R B M B₁ M₁ Rq Nq : ℝ} {K K₁ K₂ : ℝ≥0}
  (hU : IsVelocityLaw U R₀ C) (hκ : IsForcingCoefficient κ Bκ)
  (h : IsSolutionOn U κ R₀ sol I) (hb : 0 < b) (hI : Icc 0 b ⊆ I)
  (hv : IsC1FieldOn (velocityField U sol) (velocityFieldDeriv U sol) 0 b K)
  (hω : IsC1VorticityHistory (fun t x ↦ sol.vorticity x t) 0 b α R B M B₁ M₁) (hR : R ≤ R₀)
  (hα : 0 < α) (hα1 : α < 1)
  (hv₂ : IsC2FieldOn (lawField U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv U fun t x ↦ sol.vorticity x t)
    (lawFieldDeriv₂ U fun t x ↦ sol.vorticity x t) 0 b K₁ K₂)
  (hreg : ∀ t ∈ Icc 0 b,
    IsHolderData (fun x ↦ sol.vorticity x t) (fun x ↦ sol.temperature x t) α Rq Nq)

include hU h hb hI hv hω hR hv₂ in
/-- The temperature is carried by the flow of the field of the history. -/
theorem temperature_flowOn_lawField {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    sol.temperature (flowOn 𝐯 0 b r 0 a) r = sol.temperature a 0 := by
  rw [← flowOn_eq_lawField hU hv hω hR hv₂.toIsC1FieldOn.isLipschitzFieldOn hr ⟨le_rfl, hb.le⟩
    ha]
  exact h.temperature_trajectory hU hb hI hv ha hr

include hU h hb hI hv hω hR hv₂ hreg in
/-- **The gradient identity within the closed half-plane** along the flow of the history:
`Dθ_r(Φ(r, y)) ∘ J(r, y) = Dθ₀(y)` for derivatives within `H̄`. -/
theorem fderivWithin_temperature_flowOn_comp {r : ℝ} (hr : r ∈ Icc 0 b) {y : ℝ^2}
    (hy : 0 ≤ y 1) :
    (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 y)).comp
        (variationOn 𝐯 𝐃𝐯 0 b r 0 y) =
      fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ y := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hΦH := mapsTo_flowOn_lawField hU hω hR hv₂.toIsC1FieldOn.isLipschitzFieldOn r hr 0 h0
  have hθr := (hreg r hr).temperature_contDiffOn
  have hθ0 := (hreg 0 h0).temperature_contDiffOn
  have hc : HasFDerivWithinAt (fun x ↦ sol.temperature (flowOn 𝐯 0 b r 0 x) r)
      ((fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 y)).comp
        (variationOn 𝐯 𝐃𝐯 0 b r 0 y)) H̄ y :=
    ((hθr.differentiableOn (by norm_num) _ (hΦH hy)).hasFDerivWithinAt).comp y
      (hv₂.toIsC1FieldOn.hasFDerivAt_flowOn hr h0 y).hasFDerivWithinAt hΦH
  have hc' := hc.congr
    (fun z hz ↦ (h.temperature_flowOn_lawField hU hb hI hv hω hR hv₂ hr hz).symm)
    (h.temperature_flowOn_lawField hU hb hI hv hω hR hv₂ hr hy).symm
  exact (uniqueDiffOn_closedUpper y hy).eq hc'
    (hθ0.differentiableOn (by norm_num) y hy).hasFDerivWithinAt

include hU h hb hI hv hω hR hv₂ hreg in
/-- **The Hessian identity along the flow of the history:**
`D²θ_r(Φ)[J u, J w] + Dθ_r(Φ)(S[u, w]) = D²θ₀(a)[u, w]`, for derivatives within the closed
half-plane, with `J` and `S` the first and second variations of `Φ = Φ(r, ·)` at `a`. -/
theorem hessian_flowOn_comp {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1)
    (u w : ℝ^2) :
    fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ (flowOn 𝐯 0 b r 0 a)
        (variationOn 𝐯 𝐃𝐯 0 b r 0 a u) (variationOn 𝐯 𝐃𝐯 0 b r 0 a w) +
      fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 a)
        (secondVariationOn 𝐯 𝐃𝐯 𝐃²𝐯 0 b r 0 a u w) =
    fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a u w := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hΦH := mapsTo_flowOn_lawField hU hω hR hv₂.toIsC1FieldOn.isLipschitzFieldOn r hr 0 h0
  have hθr := (hreg r hr).temperature_contDiffOn
  have hθ0 := (hreg 0 h0).temperature_contDiffOn
  have hDθr : ContDiffOn ℝ 1 (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ :=
    hθr.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have hDθ0 : ContDiffOn ℝ 1 (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ :=
    hθ0.fderivWithin uniqueDiffOn_closedUpper (by norm_num)
  have hc2 : HasFDerivWithinAt
      (fun y ↦ fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 y))
      ((fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄
        (flowOn 𝐯 0 b r 0 a)).comp (variationOn 𝐯 𝐃𝐯 0 b r 0 a)) H̄ a :=
    ((hDθr.differentiableOn one_ne_zero _ (hΦH ha)).hasFDerivWithinAt).comp a
      (hv₂.toIsC1FieldOn.hasFDerivAt_flowOn hr h0 a).hasFDerivWithinAt hΦH
  have hd2 := (hv₂.hasFDerivAt_variationOn hr h0 a).hasFDerivWithinAt (s := H̄)
  have hprod := hc2.clm_comp hd2
  have hprod' := hprod.congr
    (fun y hy ↦ (h.fderivWithin_temperature_flowOn_comp hU hb hI hv hω hR hv₂ hreg hr hy).symm)
    (h.fderivWithin_temperature_flowOn_comp hU hb hI hv hω hR hv₂ hreg hr ha).symm
  have heq := (uniqueDiffOn_closedUpper a ha).eq hprod'
    (hDθ0.differentiableOn one_ne_zero a ha).hasFDerivWithinAt
  have happ := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ ↦ L u w) heq
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply] at happ
  rw [← happ, add_comm]

include hU h hb hI hv hω hR hv₂ hreg in
/-- The gradient of the temperature at `Φ(r, a)` is `Dθ₀(a) ∘ W`, with `W` the inverse first
variation. -/
theorem fderivWithin_temperature_flowOn {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) :
    fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄ (flowOn 𝐯 0 b r 0 a) =
      (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a).comp
        (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a)) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  rw [← h.fderivWithin_temperature_flowOn_comp hU hb hI hv hω hR hv₂ hreg hr ha,
    ContinuousLinearMap.comp_assoc, hv₂.toIsC1FieldOn.variationOn_comp_variationOn_flowOn hr h0 a,
    ContinuousLinearMap.comp_id]

include hU h hb hI hv hω hR hv₂ hreg in
/-- **The closed form of the Hessian along the flow:** with `W` the inverse first variation and
`S` the second variation, `H[u, w] = D²θ₀(a)[W u, W w] - Dθ₀(a)(W S[W u, W w])`. -/
theorem hessian_flowOn_eq {r : ℝ} (hr : r ∈ Icc 0 b) {a : ℝ^2} (ha : 0 ≤ a 1) (u w : ℝ^2) :
    fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x r) H̄) H̄ (flowOn 𝐯 0 b r 0 a) u w =
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a
          (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) u)
          (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) w) -
        fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a
          (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a)
            (secondVariationOn 𝐯 𝐃𝐯 𝐃²𝐯 0 b r 0 a
              (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) u)
              (variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a) w))) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  set W := variationOn 𝐯 𝐃𝐯 0 b 0 r (flowOn 𝐯 0 b r 0 a)
  have hJW (x : ℝ^2) : variationOn 𝐯 𝐃𝐯 0 b r 0 a (W x) = x := by
    have := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 ↦ L x)
      (hv₂.toIsC1FieldOn.variationOn_comp_variationOn_flowOn hr h0 a)
    simpa using this
  have hH := h.hessian_flowOn_comp hU hb hI hv hω hR hv₂ hreg hr ha (W u) (W w)
  rw [hJW, hJW, h.fderivWithin_temperature_flowOn hU hb hI hv hω hR hv₂ hreg hr ha] at hH
  rw [← hH, ContinuousLinearMap.comp_apply]
  ring

include hU h hb hI hv hω hR hv₂ hreg in
/-- **The equation of the Hessian of the temperature along the flow:**
`∂ᵣ H = -H[Du ·, ·] - H[·, Du ·] - Dθ_r(Φ) ∘ D²u` with `H(r) = D²θ_r(Φ(r, a))`,
`Du = Dv(r, Φ(r, a))` and `D²u = D²v(r, Φ(r, a))`. The second variation has cancelled. The
equation needs no third derivative of the temperature, so it can be used in the class of the
data. Proof: differentiate in time the closed form of `hessian_flowOn_eq`, with the equations of
the inverse first variation and of the second variation. -/
theorem hasDerivWithinAt_hessian {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ} (hr : r ∈ Icc 0 b) :
    HasDerivWithinAt (fun ρ ↦ 𝐇 ρ a)
      (hessianTransport (𝐇 r a) (𝐃𝐯 r (𝐗 r a)) (𝐆 r a) (𝐃²𝐯 r (𝐗 r a))) (Icc 0 b) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  set W : ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun ρ ↦ variationOn 𝐯 𝐃𝐯 0 b 0 ρ (flowOn 𝐯 0 b ρ 0 a)
  set S : ℝ → ℝ^2 →L[ℝ] ℝ^2 →L[ℝ] ℝ^2 := fun ρ ↦ secondVariationOn 𝐯 𝐃𝐯 𝐃²𝐯 0 b ρ 0 a
  set J : ℝ^2 →L[ℝ] ℝ^2 := variationOn 𝐯 𝐃𝐯 0 b r 0 a
  set T := fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a
  set Q := fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄) H̄ a
  set Dv := 𝐃𝐯 r (flowOn 𝐯 0 b r 0 a)
  set D2v := 𝐃²𝐯 r (flowOn 𝐯 0 b r 0 a)
  have hJW (x : ℝ^2) : J (W r x) = x := by
    have := congrArg (fun L : ℝ^2 →L[ℝ] ℝ^2 ↦ L x)
      (hv₁.variationOn_comp_variationOn_flowOn hr h0 a)
    simpa using this
  -- The equations in time of the inverse first variation `W` and of the second variation `S`.
  have hW : HasDerivWithinAt W (-(W r).comp Dv) (Icc 0 b) r :=
    hv₁.hasDerivWithinAt_variationOn_inverse hr h0 a
  have hS : HasDerivWithinAt S ((ContinuousLinearMap.compL ℝ (ℝ^2) (ℝ^2) (ℝ^2) Dv).comp (S r) +
      secondVariationForcing D2v J) (Icc 0 b) r := hv₂.hasDerivWithinAt_secondVariationOn hr h0 a
  -- Differentiate in time the closed form `H[u, w] = Q[W u, W w] - T (W S[W u, W w])`, with
  -- `Q` and `T` the Hessian and the gradient of the datum at the label.
  refine hasDerivWithinAt_of_forall_apply_apply fun u w ↦ ?_
  have hWu := hW.clm_apply (hasDerivWithinAt_const r (Icc 0 b) u)
  have hWw := hW.clm_apply (hasDerivWithinAt_const r (Icc 0 b) w)
  have hQ := (Q.hasFDerivAt.comp_hasDerivWithinAt r hWu).clm_apply hWw
  have hSm := (hS.clm_apply hWu).clm_apply hWw
  have hT := T.hasFDerivAt.comp_hasDerivWithinAt r (hW.clm_apply hSm)
  have hf := hQ.sub hT
  have hcongr : ∀ ρ ∈ Icc 0 b,
      fderivWithin ℝ (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (flowOn 𝐯 0 b ρ 0 a) u w =
        Q (W ρ u) (W ρ w) - T (W ρ (S ρ (W ρ u) (W ρ w))) := fun ρ hρ ↦
    h.hessian_flowOn_eq hU hb hI hv hω hR hv₂ hreg hρ ha u w
  have hf' : HasDerivWithinAt (fun ρ ↦ fderivWithin ℝ
      (fderivWithin ℝ (fun x ↦ sol.temperature x ρ) H̄) H̄ (flowOn 𝐯 0 b ρ 0 a) u w) _
      (Icc 0 b) r :=
    hf.congr_of_mem (fun ρ hρ ↦ by rw [hcongr ρ hρ]; rfl) hr
  -- The derivative is the right-hand side of the equation: the terms with `S` cancel.
  convert hf' using 1
  rw [h.fderivWithin_temperature_flowOn hU hb hI hv hω hR hv₂ hreg hr ha]
  simp only [hessianTransport, sub_apply, neg_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, h.hessian_flowOn_eq hU hb hI hv hω hR hv₂ hreg hr ha,
    add_apply, map_add, map_neg, map_zero, add_zero,
    secondVariationForcing_apply, hJW]
  ring

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg in
/-- **The vorticity in label form along the flow of the history.** On the closed half-plane the
vorticity at time `r` is the amplitude `ω̃₀(Y) + ∫₀ʳ κ(X(ρ, Y)) Dθ̃₀(Y)(W e₀) dρ` at the label
`Y = Φ(0, r, x)`, with `ω̃₀`, `θ̃₀` the extended data. -/
theorem vorticity_eq_forcedAmplitude {r : ℝ} (hr : r ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    sol.vorticity x r = forcedAmplitude (dataVorticity fun y ↦ sol.vorticity y 0)
      (weightedForcing 𝐯 𝐃𝐯 0 b κ (dataTemperature fun y ↦ sol.temperature y 0)
        (EuclideanSpace.single 0 1)) (flowOn 𝐯 0 b 0 r x) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv.isLipschitzFieldOn
  have hθ₀d : Differentiable ℝ (fun y ↦ sol.temperature y 0) :=
    (h.contDiff_temperature (hI h0)).differentiable one_ne_zero
  have hY : label U sol b x r = flowOn 𝐯 0 b 0 r x :=
    flowOn_eq_lawField hU hv hω hR hv₁.isLipschitzFieldOn h0 hr hx
  have hYm : 0 ≤ label U sol b x r 1 := h.label_mem hU hI hL hb.le hr hx
  rw [h.vorticity_eq_label hU hκ.contDiff_one.continuous hb hI hv hr hx, forcedAmplitude, ← hY,
    dataVorticity_of_nonneg _ hYm]
  congr 1
  refine intervalIntegral.integral_congr fun ρ hρ ↦ ?_
  have hρ' : ρ ∈ Icc 0 b := by
    rw [uIcc_of_le hr.1] at hρ
    exact ⟨hρ.1, hρ.2.trans hr.2⟩
  have hX : trajectory U sol b ρ (label U sol b x r) = flowOn 𝐯 0 b ρ 0 (label U sol b x r) :=
    flowOn_eq_lawField hU hv hω hR hv₁.isLipschitzFieldOn hρ' h0 hYm
  have hXm := h.trajectory_mem hU hI hL hb.le hρ' hYm
  simp only [weightedForcing, labelForcing]
  rw [h.variationOn_eq_lawField hU hb hI hv hω hR hα hα1 hv₁ h0 hρ' hXm, hX,
    (hreg 0 h0).fderiv_dataTemperature hYm,
    ← (hθ₀d _).fderivWithin (uniqueDiffOn_closedUpper _ hYm)]

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg in
/-- **The gradient of the vorticity in label form:** on the closed half-plane,
`Dω_r(x) = (Dω̃₀(Y) + ∫₀ʳ ∂_Y weightedForcing(Y, ρ) dρ) ∘ D_x Y` with `Y = Φ(0, r, x)`. -/
theorem fderivWithin_vorticity_eq {r : ℝ} (hr : r ∈ Icc 0 b) {x : ℝ^2} (hx : 0 ≤ x 1) :
    fderivWithin ℝ (fun y ↦ sol.vorticity y r) H̄ x =
      (fderiv ℝ (dataVorticity fun y ↦ sol.vorticity y 0) (flowOn 𝐯 0 b 0 r x) +
        ∫ ρ in (0)..r, weightedForcingDeriv 𝐯 𝐃𝐯 𝐃²𝐯 0 b κ
          (dataTemperature fun y ↦ sol.temperature y 0) (EuclideanSpace.single 0 1)
          (flowOn 𝐯 0 b 0 r x) ρ).comp (variationOn 𝐯 𝐃𝐯 0 b 0 r x) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hd := hreg 0 h0
  have hθ := hd.contDiff_dataTemperature
  have hF := (hasFDerivAt_forcedAmplitude
      (G := weightedForcing 𝐯 𝐃𝐯 0 b κ (dataTemperature fun y ↦ sol.temperature y 0)
        (EuclideanSpace.single 0 1))
      hd.contDiff_dataVorticity.differentiable_one
      (continuousOn_weightedForcing hv₁ h0 hκ.contDiff_one.continuous (hθ.of_le (by norm_num)))
      (fun ρ hρ y ↦ hasFDerivAt_weightedForcing hv₂ h0
        (hκ.contDiff_one.differentiable one_ne_zero) hθ hρ y)
      (continuousOn_weightedForcingDeriv hv₂ h0 hκ.contDiff_one hθ) h0 hr
      (flowOn 𝐯 0 b 0 r x)).comp x (hv₁.hasFDerivAt_flowOn h0 hr x)
  exact (hF.hasFDerivWithinAt.congr
    (fun y hy ↦ h.vorticity_eq_forcedAmplitude hU hκ hb hI hv hω hR hα hα1 hv₂ hreg hr hy)
    (h.vorticity_eq_forcedAmplitude hU hκ hb hI hv hω hR hα hα1 hv₂ hreg hr hx)).fderivWithin
    (uniqueDiffOn_closedUpper x hx)

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg in
/-- **The equation of the gradient of the vorticity along the flow:** with
`Z(r) = Dω_r(Φ(r, a))`, `H(r) = D²θ_r(Φ(r, a))`, `G(r) = Dθ_r(Φ(r, a))` and
`Du = Dv(r, Φ(r, a))`, `∂ᵣ Z = κ(Φ) H[·, e₀] + (G e₀) Dκ(Φ) - Z ∘ Du`. The equation needs no
second derivative of the vorticity. Proof: by `fderivWithin_vorticity_eq` the gradient is
`P(r) ∘ W(r)` with `P` the derivative of the forced amplitude in the label and `W` the inverse
first variation; differentiate the product in time and rewrite the forcing with the Hessian. -/
theorem hasDerivWithinAt_vorticityGradient {a : ℝ^2} (ha : 0 ≤ a 1) {r : ℝ}
    (hr : r ∈ Icc 0 b) :
    HasDerivWithinAt (fun ρ ↦ 𝐙 ρ a)
      (vorticityGradientTransport (κ (𝐗 r a)) (fderiv ℝ κ (𝐗 r a)) (𝐇 r a) (𝐆 r a) (𝐙 r a)
        (𝐃𝐯 r (𝐗 r a))) (Icc 0 b) r := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hv₁ := hv₂.toIsC1FieldOn
  have hL := hv₁.isLipschitzFieldOn
  have hd := hreg 0 h0
  have hθ := hd.contDiff_dataTemperature
  set e : ℝ^2 := EuclideanSpace.single 0 1
  set Gd : ℝ → ℝ^2 →L[ℝ] ℝ := fun ρ ↦ weightedForcingDeriv 𝐯 𝐃𝐯 𝐃²𝐯 0 b κ
    (dataTemperature fun y ↦ sol.temperature y 0) e a ρ
  set P : ℝ → ℝ^2 →L[ℝ] ℝ := fun ρ ↦
    fderiv ℝ (dataVorticity fun y ↦ sol.vorticity y 0) a + ∫ σ in (0)..ρ, Gd σ
  set W : ℝ → ℝ^2 →L[ℝ] ℝ^2 := fun ρ ↦ variationOn 𝐯 𝐃𝐯 0 b 0 ρ (flowOn 𝐯 0 b ρ 0 a)
  have hGc : ContinuousOn Gd (Icc 0 b) :=
    (continuousOn_weightedForcingDeriv (e := e) hv₂ h0 hκ.contDiff_one hθ).comp
      (f := fun ρ : ℝ ↦ (a, ρ)) (continuousOn_const.prodMk continuousOn_id)
      fun ρ hρ ↦ ⟨mem_univ _, hρ⟩
  -- `P` is the derivative of the forced amplitude in the label; its time derivative is the
  -- derivative `Gd` of the weighted forcing.
  have hP : HasDerivWithinAt P (Gd r) (Icc 0 b) r := by
    have hu : uIcc (0 : ℝ) b = Icc 0 b := uIcc_of_le hb.le
    have := PDE.Analysis.hasDerivWithinAt_intervalIntegral_uIcc (f := Gd) (c := 0) (x := r)
      (by rwa [hu]) left_mem_uIcc (by rwa [hu])
    rw [hu] at this
    exact this.const_add _
  have hW : HasDerivWithinAt W (-(W r).comp (𝐃𝐯 r (flowOn 𝐯 0 b r 0 a))) (Icc 0 b) r :=
    hv₁.hasDerivWithinAt_variationOn_inverse hr h0 a
  -- The gradient of the vorticity along the trajectory is `P ∘ W`.
  have hZ : ∀ ρ ∈ Icc 0 b,
      fderivWithin ℝ (fun x ↦ sol.vorticity x ρ) H̄ (flowOn 𝐯 0 b ρ 0 a) = (P ρ).comp (W ρ) := by
    intro ρ hρ
    have hΦ := mapsTo_flowOn_lawField hU hω hR hL ρ hρ 0 h0 ha
    simp only [P, W, Gd]
    rw [h.fderivWithin_vorticity_eq hU hκ hb hI hv hω hR hα hα1 hv₂ hreg hρ hΦ,
      flowOn_zero_flowOn hL h0 hρ]
  -- The product rule in time. The forcing `Gd ∘ W` is then written with the Hessian and the
  -- gradient of the temperature at the particle.
  have hPW := (hP.clm_comp hW).congr_of_mem (fun ρ hρ ↦ hZ ρ hρ) hr
  convert hPW using 1
  have hLW : (labelForcingDeriv 𝐯 𝐃𝐯 𝐃²𝐯 0 b (dataTemperature fun y ↦ sol.temperature y 0) e
      a r).comp (W r) = (ContinuousLinearMap.apply ℝ ℝ e).comp (𝐇 r a) := by
    refine ContinuousLinearMap.ext fun u ↦ ?_
    simp only [W, labelForcingDeriv, sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.apply_apply,
      h.hessian_flowOn_eq hU hb hI hv hω hR hv₂ hreg hr ha u e,
      hd.fderiv_fderiv_dataTemperature ha, hd.fderiv_dataTemperature ha]
  have hJW : ((fderiv ℝ κ (𝐗 r a)).comp (variationOn 𝐯 𝐃𝐯 0 b r 0 a)).comp (W r) =
      fderiv ℝ κ (𝐗 r a) := by
    rw [ContinuousLinearMap.comp_assoc, hv₁.variationOn_comp_variationOn_flowOn hr h0 a,
      ContinuousLinearMap.comp_id]
  have hlab : labelForcing 𝐯 𝐃𝐯 0 b (dataTemperature fun y ↦ sol.temperature y 0) e a r =
      (𝐆 r a) e := by
    rw [h.fderivWithin_temperature_flowOn hU hb hI hv hω hR hv₂ hreg hr ha, labelForcing,
      hd.fderiv_dataTemperature ha]
    rfl
  have hGW : (Gd r).comp (W r) = κ (𝐗 r a) • (ContinuousLinearMap.apply ℝ ℝ e).comp (𝐇 r a) +
      (𝐆 r a) e • fderiv ℝ κ (𝐗 r a) := by
    simp only [Gd, weightedForcingDeriv, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.smul_comp, hLW, hJW, hlab]
  rw [hZ r hr, ContinuousLinearMap.comp_neg, ← ContinuousLinearMap.comp_assoc, hGW,
    vorticityGradientTransport, ← hZ r hr]
  abel

include hU h hb hI hv hω hR hv₂ hreg in
/-- The temperature gradient along a trajectory is continuous in time. -/
theorem continuousOn_gradient_flowOn {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun ρ ↦ 𝐆 ρ a) (Icc 0 b) := by
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩
  have hW : ContinuousOn (fun ρ ↦ variationOn 𝐯 𝐃𝐯 0 b 0 ρ (𝐗 ρ a)) (Icc 0 b) := fun ρ hρ ↦
    (hv₂.toIsC1FieldOn.hasDerivWithinAt_variationOn_inverse hρ h0 a).hasFDerivWithinAt
      |>.continuousWithinAt
  have hc : ContinuousOn (fun ρ ↦ (fderivWithin ℝ (fun x ↦ sol.temperature x 0) H̄ a).comp
      (variationOn 𝐯 𝐃𝐯 0 b 0 ρ (𝐗 ρ a))) (Icc 0 b) := continuousOn_const.clm_comp hW
  intro ρ hρ
  have heq := h.fderivWithin_temperature_flowOn hU hb hI hv hω hR hv₂ hreg hρ ha
  exact (hc ρ hρ).congr
    (fun σ hσ ↦ h.fderivWithin_temperature_flowOn hU hb hI hv hω hR hv₂ hreg hσ ha) heq

include hb hv₂ in
/-- The second derivative of the field along a trajectory is continuous in time. -/
theorem continuousOn_deriv₂_flowOn (a : ℝ^2) :
    ContinuousOn (fun ρ ↦ 𝐃²𝐯 ρ (𝐗 ρ a)) (Icc 0 b) :=
  hv₂.continuousOn_deriv₂.comp (f := fun ρ ↦ (ρ, 𝐗 ρ a)) (continuousOn_id.prodMk
    (hv₂.toIsC1FieldOn.isLipschitzFieldOn.continuousOn_flowOn_time ⟨le_rfl, hb.le⟩ a))
    fun _ hρ ↦ ⟨hρ, mem_univ _⟩

include hU h hb hI hv hω hR hv₂ hreg in
/-- The Hessian of the temperature along a trajectory is continuous in time. -/
theorem continuousOn_hessian_flowOn {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun ρ ↦ 𝐇 ρ a) (Icc 0 b) := fun _ hρ ↦
  (h.hasDerivWithinAt_hessian hU hb hI hv hω hR hv₂ hreg ha hρ).hasFDerivWithinAt
    |>.continuousWithinAt

include hU hκ h hb hI hv hω hR hα hα1 hv₂ hreg in
/-- The vorticity gradient along a trajectory is continuous in time. -/
theorem continuousOn_vorticityGradient_flowOn {a : ℝ^2} (ha : 0 ≤ a 1) :
    ContinuousOn (fun ρ ↦ 𝐙 ρ a) (Icc 0 b) := fun _ hρ ↦
  (h.hasDerivWithinAt_vorticityGradient hU hκ hb hI hv hω hR hα hα1 hv₂ hreg ha
    hρ).hasFDerivWithinAt.continuousWithinAt

end Hessian

end IsSolutionOn

end HalfPlaneSystem
