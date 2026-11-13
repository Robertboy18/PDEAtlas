/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Analysis.Variational.LaxMilgram
public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
import PDE.Analysis.Evolution.Galerkin.Gelfand.Existence

/-!
# Ritz initial data for differentiated parabolic Galerkin schemes

The second improved regularity theorem (Evans §7.1.3, Theorem 5(ii)) differentiates the
Galerkin equation in time, so the differentiated problem needs a bounded initial velocity.
Evans starts from the `L²` projection `u_m(0) = Σ_k (g, w_k) w_k` onto eigenfunctions of
`-Δ` and bounds `u_m'(0)` through the equation and the estimate
`‖u_m(0)‖_{H²} ≤ C ‖g‖_{H²}` (steps 4 and 5 of the proof). We start instead from the Ritz
projection of the initial datum for the autonomous elliptic form. This choice turns the
differentiated initial value into the ordinary pivot projection of the compatibility datum
`f(0) - Lg`. The argument is written for an abstract autonomous Gelfand evolution,
independent of any Sobolev realization.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, equation (15), and §7.1.3, proof of Theorem 5,
  steps 4 and 5 (the bound for `u_m'(0)` with the eigenfunction basis).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter
open PDE.Analysis.Variational
open scoped InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace RitzInitialCompatibility

variable
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v)

local instance : CompleteSpace S := FiniteDimensional.complete ℝ S

/-- The restriction of a coercive form to any trial subspace is coercive. -/
theorem restrictedForm_isCoercive
    (S : Submodule ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v) :
    IsCoercive (restrictForm S B) := by
  refine ⟨C, hC, fun v ↦ ?_⟩
  change C * ‖(v : V)‖ * ‖(v : V)‖ ≤ B (v : V) (v : V)
  simpa only [pow_two, mul_assoc] using hcoercive (v : V)

/-- The autonomous Ritz projection associated with `B`.

It is defined by the finite-dimensional variational problem

`B(R_S v,w) = B(v,w)` for every `w ∈ S`.
-/
def projection
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v) :
    V →L[ℝ] S :=
  (solveCLM
      (restrictForm S B)
      (restrictedForm_isCoercive S B hC hcoercive)).comp
    ((restrictFunctionalMap S).comp B)

/-- The Ritz projection satisfies its defining variational identity. -/
theorem projection_orthogonal
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v)
    (v : V) (w : S) :
    B (projection S B hC hcoercive v : V) (w : V) =
      B v (w : V) := by
  have hweak :=
    solveCLM.isWeakSolution
      (restrictForm S B)
      (restrictedForm_isCoercive S B hC hcoercive)
      (((restrictFunctionalMap S).comp B) v)
      w
  change B
      ((solveCLM
        (restrictForm S B)
        (restrictedForm_isCoercive S B hC hcoercive))
        (restrictFunctional S (B v)) : V)
      (w : V) =
    B v (w : V)
  exact hweak

/-- Coercivity gives the elementary operator bound for the Ritz projection. -/
theorem norm_projection_le
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v)
    (v : V) :
    ‖(projection S B hC hcoercive v : S)‖ ≤
      (‖B‖ / C) * ‖v‖ := by
  let r : S := projection S B hC hcoercive v
  change ‖(r : V)‖ ≤ (‖B‖ / C) * ‖v‖
  by_cases hr : r = 0
  · rw [hr]
    simpa using
      mul_nonneg (div_nonneg (norm_nonneg B) hC.le) (norm_nonneg v)
  have hrnorm : 0 < ‖(r : V)‖ := norm_pos_iff.mpr (by
    intro hzero
    apply hr
    exact Subtype.ext hzero)
  have hcoer := hcoercive (r : V)
  have hritz := projection_orthogonal S B hC hcoercive v r
  have hform :
      B (r : V) (r : V) ≤ ‖B‖ * ‖v‖ * ‖(r : V)‖ := by
    rw [hritz]
    calc
      B v (r : V) ≤ |B v (r : V)| := le_abs_self _
      _ = ‖B v (r : V)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖B v‖ * ‖(r : V)‖ := (B v).le_opNorm _
      _ ≤ (‖B‖ * ‖v‖) * ‖(r : V)‖ := by
        gcongr
        exact B.le_opNorm v
  have hmain :
      C * ‖(r : V)‖ ≤ ‖B‖ * ‖v‖ := by
    nlinarith [hcoer, hform]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hC).2 (by simpa only [mul_comm] using hmain)

/-- Céa's estimate for the autonomous Ritz projection. -/
theorem norm_sub_projection_le
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v)
    (v : V) (w : S) :
    ‖v - (projection S B hC hcoercive v : V)‖ ≤
      (‖B‖ / C) * ‖v - (w : V)‖ := by
  let r : S := projection S B hC hcoercive v
  let e : V := v - (r : V)
  change ‖e‖ ≤ (‖B‖ / C) * ‖v - (w : V)‖
  by_cases he : e = 0
  · rw [he]
    simpa using
      mul_nonneg (div_nonneg (norm_nonneg B) hC.le)
        (norm_nonneg (v - (w : V)))
  have henorm : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hortho : B e ((r - w : S) : V) = 0 := by
    change B (v - (r : V)) ((r - w : S) : V) = 0
    rw [map_sub, sub_apply]
    have hritz :=
      projection_orthogonal S B hC hcoercive v (r - w)
    simpa only [r] using sub_eq_zero.mpr hritz.symm
  have hdecomp :
      v - (w : V) = e + ((r - w : S) : V) := by
    dsimp only [e]
    simp only [Submodule.coe_sub]
    abel
  have heq : B e e = B e (v - (w : V)) := by
    rw [hdecomp, map_add, hortho, add_zero]
  have hcoer := hcoercive e
  have hform :
      B e e ≤ ‖B‖ * ‖e‖ * ‖v - (w : V)‖ := by
    rw [heq]
    calc
      B e (v - (w : V)) ≤ |B e (v - (w : V))| := le_abs_self _
      _ = ‖B e (v - (w : V))‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖B e‖ * ‖v - (w : V)‖ := (B e).le_opNorm _
      _ ≤ (‖B‖ * ‖e‖) * ‖v - (w : V)‖ := by
        gcongr
        exact B.le_opNorm e
  have hmain : C * ‖e‖ ≤ ‖B‖ * ‖v - (w : V)‖ := by
    nlinarith [hcoer, hform]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hC).2 (by simpa only [mul_comm] using hmain)

/-- Energy-density of trial spaces implies strong convergence of their Ritz
projections in the energy norm. -/
theorem tendsto_projection_of_eventually_approximable
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v)
    {Sseq : ℕ → Submodule ℝ V}
    [∀ k, FiniteDimensional ℝ (Sseq k)]
    (hdense : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in atTop, ∃ w : Sseq k, ‖v - (w : V)‖ < ε)
    (v : V) :
    Tendsto
      (fun k ↦ (projection (Sseq k) B hC hcoercive v : V))
      atTop (𝓝 v) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hscale : 0 < C / (‖B‖ + C) := by positivity
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hdense v (ε * (C / (‖B‖ + C))) (mul_pos hε hscale))
  refine ⟨N, fun k hk ↦ ?_⟩
  obtain ⟨w, hw⟩ := hN k hk
  rw [dist_eq_norm, norm_sub_rev]
  have hcea :=
    norm_sub_projection_le (Sseq k) B hC hcoercive v w
  calc
    ‖v - (projection (Sseq k) B hC hcoercive v : V)‖ ≤
        (‖B‖ / C) * ‖v - (w : V)‖ := hcea
    _ ≤ (‖B‖ / C) * (ε * (C / (‖B‖ + C))) :=
      mul_le_mul_of_nonneg_left (le_of_lt hw)
        (div_nonneg (norm_nonneg B) hC.le)
    _ < ε := by
      have hBC : 0 < ‖B‖ + C := by positivity
      have hratio : ‖B‖ / (‖B‖ + C) < 1 := by
        rw [div_lt_one hBC]
        linarith [norm_nonneg B]
      rw [show
        (‖B‖ / C) * (ε * (C / (‖B‖ + C))) =
          ε * (‖B‖ / (‖B‖ + C)) by field_simp]
      nlinarith

/-- Compatibility at the initial time identifies the mass-inverted
Galerkin velocity with the pivot projection of the ambient compatibility
datum.

The hypothesis

`ell(a)(v) = ⟪hInit,Jv⟫ + B(g,v)`

is the abstract form of `hInit = f(0) - Lg`.  The Ritz identity eliminates
the spatial projection error exactly.
-/
theorem initialVelocity_eq_pivotProjection
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (B : V →L[ℝ] StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    (hcoercive : ∀ v : V, C * ‖v‖ ^ 2 ≤ B v v)
    {K : NNReal} (P : StableTrialProjection T S K)
    (ell : ℝ → StrongDual ℝ V) (a : ℝ)
    (g : V) (hInit : H)
    (hcompat : ∀ v : V,
      ell a v = inner ℝ hInit (T.inclusion v) + B g v) :
    gelfandGalerkinVectorField T S (fun _ ↦ B) ell a
        (projection S B hC hcoercive g) =
      P.projection hInit := by
  symm
  apply gelfandGalerkin_derivative_eq_vectorField
    T S (fun _ ↦ B) ell a
      (projection S B hC hcoercive g) (P.projection hInit)
  intro v
  rw [projection_orthogonal S B hC hcoercive g v,
    hcompat (v : V)]
  have horth := P.pivotOrthogonal v hInit
  have horth' :
      inner ℝ (T.inclusion (v : V)) hInit =
        inner ℝ (T.inclusion (v : V))
          (T.inclusion (P.projection hInit : V)) := by
    exact sub_eq_zero.mp (by simpa only [inner_sub_right] using horth)
  have hsplit :
      inner ℝ hInit (T.inclusion (v : V)) =
        inner ℝ (T.inclusion (P.projection hInit : V))
          (T.inclusion (v : V)) := by
    calc
      inner ℝ hInit (T.inclusion (v : V)) =
          inner ℝ (T.inclusion (v : V)) hInit :=
        real_inner_comm _ _
      _ = inner ℝ (T.inclusion (v : V))
          (T.inclusion (P.projection hInit : V)) := horth'
      _ = inner ℝ (T.inclusion (P.projection hInit : V))
          (T.inclusion (v : V)) := real_inner_comm _ _
  rw [hsplit]

end RitzInitialCompatibility

end PDE.Analysis.Evolution
