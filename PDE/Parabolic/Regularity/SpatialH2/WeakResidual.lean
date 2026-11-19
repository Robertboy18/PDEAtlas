/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
public import PDE.Analysis.Evolution.Integrated.Solution
import PDE.Analysis.Evolution.Integrated.Regularity
import PDE.Elliptic.Regularity.Global.H2

/-!
# Spatial `H²` regularity from a parabolic weak residual

Suppose an integrated parabolic solution has a pivot-valued weak time
derivative `u_t ∈ L²(a,b;L²(Ω))`. Uniqueness of weak time derivatives gives
the evolution equation in `H⁻¹(Ω)` almost everywhere. Testing that identity
turns `u_t - ∂ᵢ(aⁱʲ ∂ⱼu) = f`, for almost every fixed time, into the elliptic
equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - u_t`.

The global elliptic `H²` theorem (Evans's §6.3.2, Theorem 4) then gives spatial `H²`
regularity, first at one time (`exists_spatial_h2_of_weak_residual_identity`)
and then in `L²_t H²_x` (`exists_spatial_h2_lp_of_ae_weak_residual_identity`),
where the bounded solution operator `globalH2SolveCLM` provides a measurable
lift. This is step 3 of Evans's proof of §7.1.3, Theorem 5, where `h := f - u'`.

The domain hypothesis is a `C2BoundaryAtlas`. It carries the openness and
boundedness used by the energy theory and the boundary charts used by elliptic
regularity; the global `H²` solution operator is built from it. A bounded open set with
`C²` graph boundary has such an atlas, by
`SobolevSpace.Boundary.HasContDiffGraphBoundary.c2BoundaryAtlas`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), (38)-(42),
  p. 334; §7.1.3, step 3 of the proof of Theorem 5, (49), p. 384.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace PDE.Parabolic.DivergenceFormHeat

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ}
variable {Ω : Set (ℝ^n)}

/--
An integrated divergence-form solution with a pivot-valued weak time
derivative satisfies the concrete variational equation almost everywhere.

Uniqueness of weak time derivatives identifies the dual-valued evolution
equation. The proof takes the Bochner representatives of the pivot
embeddings and evaluates the resulting equality in `H⁻¹(Ω)` on a test
function.
-/
theorem ae_weak_residual_identity_of_integrated_solution
    {t₀ t₁ : ℝ}
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f ut : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (u : Lp (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (uInit : DerivLp n 2 Ω)
    (hu : IsGelfandIntegratedWeakSolution
      (h10L2GelfandTriple hΩopen)
      (fun _ ↦
        variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω)
            (coefficientBase A)))
      (fun t ↦
        (h10L2GelfandTriple hΩopen).pivotToDual.compLpL 2
          (volume.restrict (Set.Ioc t₀ t₁)) f t)
      u uInit)
    (hut : HasGelfandWeakTimeDerivativeOn
      (h10L2GelfandTriple hΩopen) u
      ((h10L2GelfandTriple hΩopen).pivotToDual.compLpL 2
        (volume.restrict (Set.Ioc t₀ t₁)) ut)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ∀ v : H¹₀(Ω),
        ⟪ut t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ +
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A))
            ((u : ℝ → H¹₀(Ω)) t) v =
          ⟪f t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ := by
  let formA := variableCoeffForm (n := n) (Ω := Ω)
    (multiplicationCoefficientOperator (n := n) (Ω := Ω) (coefficientBase A))
  have hEquation := IsGelfandIntegratedWeakSolution.ae_weak_equation (V := H¹₀(Ω))
    (H := DerivLp n 2 Ω) (fun v ↦ aestronglyMeasurable_const.apply_continuousLinearMap v)
    ‖formA‖ (.of_forall fun _ ↦ le_rfl) hu hut
  filter_upwards [hEquation, (h10L2GelfandTriple hΩopen).pivotToDual.coeFn_compLpL ut,
    (h10L2GelfandTriple hΩopen).pivotToDual.coeFn_compLpL f] with t hEq hutRep hfRep v
  have hEqv := congrArg (fun ell : StrongDual ℝ (H¹₀(Ω)) ↦ ell v) hEq
  rw [hutRep, hfRep] at hEqv
  exact hEqv

/--
Rewrite a parabolic weak residual identity as the corresponding elliptic
divergence-form equation.

Both the pointwise and the Bochner regularity theorems use this step: at a
fixed time, the elliptic right-hand side is `f - uₜ`.
-/
theorem is_weak_divergence_solution_of_weak_residual_identity
    (hΩopen : IsOpen Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (f ut : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : ∀ v : H¹₀(Ω),
      ⟪ut, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ +
        variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω)
            (coefficientBase A)) u v =
        ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ) :
    IsWeakDivergenceSolution
      (n := n) (Ω := Ω)
      (coefficientBase A) (f - ut) u := by
  refine (isWeakSolution_iff_isWeakDivergenceSolution (n := n) (Ω := Ω) hΩopen
    (coefficientBase A) (f - ut) u).mp fun v ↦ ?_
  change _ = ⟪f - ut, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ
  rw [inner_sub_left]
  linarith [hu v]

/--
Spatial `H²` regularity at one admissible time, for an operator without lower-order
terms, as in step 3 of Evans's proof of §7.1.3, Theorem 5.

Let `u(t) ∈ H¹₀(Ω)` and suppose both the forcing `f(t)` and time derivative
`u_t(t)` belong to `L²(Ω)`.  If the weak parabolic equation holds at this
time, then `u(t)` is the weak Dirichlet solution of the elliptic
divergence-form equation with right-hand side `f(t) - u_t(t)`. On a domain
with a `C2BoundaryAtlas`, with uniformly elliptic `W¹,∞` principal
coefficients represented by global `C¹` functions, the global elliptic
regularity theorem gives an `H²(Ω)` representative.

The coefficients `A i j` and their pointwise representatives `a x i j` are
the same data as in `exists_global_h2_of_isWeakDivergenceSolution`.
-/
theorem exists_spatial_h2_of_weak_residual_identity
    [Fact (0 < n)]
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f ut : DerivLp n 2 Ω)
    (u : H¹₀(Ω))
    (hu : ∀ v : H¹₀(Ω),
      ⟪ut, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ +
        variableCoeffForm (n := n) (Ω := Ω)
          (multiplicationCoefficientOperator (n := n) (Ω := Ω)
            (coefficientBase A)) u v =
        ⟪f, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(Ω),
      ⇑((W : WkpAmbientOn n 2 2 Ω)
          (baseIndex n 2) : DerivLp n 2 Ω)
        =ᵐ[domainMeasure n Ω]
          ⇑(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
            (baseIndex n 1) : DerivLp n 2 Ω) := by
  obtain ⟨W, hW⟩ := exists_global_h2_of_isWeakDivergenceSolution hΩ A a haRep haC1 (f - ut) u
    (is_weak_divergence_solution_of_weak_residual_identity hΩ.toC1ExtensionAtlas.isOpen A f ut u
      hu) alpha halpha hElliptic
  exact ⟨W, by simpa [baseRepresentative] using hW⟩

/--
Bochner `L²_t H²_x` regularity for an operator without lower-order terms, as in step 3 of
Evans's proof of §7.1.3, Theorem 5.

Assume the weak parabolic equation holds for almost every time and that both
the forcing and pivot-valued time derivative lie in `L²_t L²_x`, so the
elliptic residual `f - u_t` is a Bochner `L²` family. Applying the bounded
global elliptic solution operator pointwise gives an element of `L²_t H²_x`.
Uniqueness of the `H¹₀` weak elliptic solution identifies its
order-zero `H¹` slice with the original parabolic trajectory almost
everywhere.

The estimate is the integrated form of the global elliptic estimate,

`‖u‖_{L²_t H²_x} ≤ C ‖f - u_t‖_{L²_t L²_x}`,

with `C` the norm of `globalH2SolveCLM`; Evans's pointwise estimate (49) also
carries `‖u‖_{L²(U)}`.
-/
theorem exists_spatial_h2_lp_of_ae_weak_residual_identity
    [Fact (0 < n)]
    (t₀ t₁ : ℝ)
    (hΩ : SobolevSpace.C2BoundaryAtlas n Ω)
    (A : Fin n → Fin n → W^{1,∞}(Ω))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Ω)
          (baseIndex n 1) : DerivLp n ∞ Ω)
        =ᵐ[domainMeasure n Ω] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f ut : Lp (DerivLp n 2 Ω) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (u : Lp
      (H¹₀(Ω)) 2
      (volume.restrict (Set.Ioc t₀ t₁)))
    (hu : ∀ᵐ t ∂(volume.restrict (Set.Ioc t₀ t₁)),
      ∀ v : H¹₀(Ω),
        ⟪ut t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ +
          variableCoeffForm (n := n) (Ω := Ω)
            (multiplicationCoefficientOperator (n := n) (Ω := Ω)
              (coefficientBase A))
            ((u : ℝ → H¹₀(Ω)) t) v =
          ⟪f t, baseCoordCLM (n := n) (Ω := Ω) v⟫_ℝ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    ∃ h2Lift : Lp (W^{2,2}(Ω)) 2
        (volume.restrict (Set.Ioc t₀ t₁)),
      ((fun t ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Ω)
            (by omega)
            ((h2Lift : ℝ → W^{2,2}(Ω)) t))
        =ᵐ[volume.restrict (Set.Ioc t₀ t₁)]
          fun t ↦
            h10SubtypeL (n := n) (Ω := Ω)
              ((u : ℝ → H¹₀(Ω)) t)) ∧
      ‖h2Lift‖ ≤
        ‖globalH2SolveCLM hΩ A a haRep haC1
          alpha halpha hElliptic‖ * ‖f - ut‖ := by
  let μ := volume.restrict (Set.Ioc t₀ t₁)
  refine ⟨globalH2SolveLpCLM μ hΩ A a haRep haC1 alpha halpha hElliptic (f - ut), ?_,
    globalH2SolveLpCLM_norm_le μ hΩ A a haRep haC1 alpha halpha hElliptic (f - ut)⟩
  filter_upwards [globalH2SolveLpCLM_apply_ae μ hΩ A a haRep haC1 alpha halpha hElliptic
    (f - ut), hu, Lp.coeFn_sub f ut] with t hLift hut hrhs
  have huDiv : IsWeakDivergenceSolution (n := n) (Ω := Ω) (coefficientBase A) ((f - ut) t)
      ((u : ℝ → H¹₀(Ω)) t) := by
    simpa only [hrhs, Pi.sub_apply] using is_weak_divergence_solution_of_weak_residual_identity
      hΩ.toC1ExtensionAtlas.isOpen A (f t) (ut t) _ hut
  rw [hLift, globalH2SolveCLM_orderOne hΩ A a haRep haC1 alpha halpha hElliptic,
    eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution hΩ A a haRep alpha halpha hElliptic _ _
      huDiv]

end PDE.Parabolic.DivergenceFormHeat
