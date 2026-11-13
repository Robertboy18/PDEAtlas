/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Strong
public import PDE.Analysis.Variational.QuadraticEnergy
import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import PDE.CalculusOfVariations.SecondVariation
import PDE.CalculusOfVariations.WeakLowerSemicontinuity
import PDE.Elliptic.Semilinear.Monotonicity

/-!
# Variational semilinear elliptic equations

We give an abstract Hilbert-space specialization of the direct method
of the calculus of variations developed in Evans, §8.2. For a symmetric
elliptic form `B`, a nonlinear potential `Phi`, and a load `ell`, the energy is

`J(u) = (1 / 2) B(u,u) + Phi(u) - ell(u)`.

A coercive quadratic part and a convex lower-semicontinuous potential with an
affine lower bound make `J` coercive and weakly lower semicontinuous.  Hence
`J` has a minimizer.  The ellipticity bound makes the whole energy strongly
convex, so that minimizer is unique.  When `Phi` is Fréchet differentiable,
the first variation gives the semilinear weak equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 2 (Existence of minimizer) and
  Theorem 3 (Uniqueness of minimizer), and §8.2.3, Theorem 4 (Solution of Euler-Lagrange
  equation).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set

namespace PDE.Elliptic.Semilinear

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The energy `J(u) = ½ B(u,u) - ell(u) + Phi(u)` for a symmetric elliptic form, a
continuous load, and a nonlinear potential: the quadratic energy
`PDE.Analysis.Variational.energy B ell` plus `Phi`. -/
def variationalEnergy
    (B : V →L[ℝ] V →L[ℝ] ℝ) (Phi : V → ℝ)
    (ell : StrongDual ℝ V) (u : V) : ℝ :=
  PDE.Analysis.Variational.energy B ell u + Phi u

/-- A symmetric quadratic form inherits the strong-convexity modulus in its
diagonal ellipticity estimate. -/
theorem strongConvexOn_quadratic
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u) :
    StrongConvexOn Set.univ c (fun u ↦ (1 / 2 : ℝ) * B u u) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have hcoercive := hBcoercive (x - y)
  have hidentity :
      (1 / 2 : ℝ) * B (a • x + b • y) (a • x + b • y) =
        a * ((1 / 2 : ℝ) * B x x) +
          b * ((1 / 2 : ℝ) * B y y) -
            a * b * ((1 / 2 : ℝ) * B (x - y) (x - y)) := by
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
      map_sub, sub_apply]
    rw [hBsymm y x]
    rw [show b = 1 - a by linarith]
    ring
  change
    (1 / 2 : ℝ) * B (a • x + b • y) (a • x + b • y) ≤
      a * ((1 / 2 : ℝ) * B x x) +
        b * ((1 / 2 : ℝ) * B y y) -
          a * b * ((c / 2) * ‖x - y‖ ^ 2)
  rw [hidentity]
  have hscaled :
      a * b * ((c / 2) * ‖x - y‖ ^ 2) ≤
        a * b * ((1 / 2 : ℝ) * B (x - y) (x - y)) := by
    have hhalf :
        (c / 2) * ‖x - y‖ ^ 2 ≤
          (1 / 2 : ℝ) * B (x - y) (x - y) := by
      calc
        (c / 2) * ‖x - y‖ ^ 2 =
            (1 / 2 : ℝ) * (c * ‖x - y‖ * ‖x - y‖) := by ring
        _ ≤ (1 / 2 : ℝ) * B (x - y) (x - y) :=
          mul_le_mul_of_nonneg_left hcoercive (by norm_num)
    exact mul_le_mul_of_nonneg_left hhalf hab_nonneg
  linarith

/-- The semilinear energy is strongly convex when the quadratic form is
symmetric and elliptic and the nonlinear potential is convex. -/
theorem strongConvexOn_variationalEnergy
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (ell : StrongDual ℝ V) :
    StrongConvexOn Set.univ c (variationalEnergy B Phi ell) := by
  rw [strongConvexOn_iff_convex]
  have hquadratic :=
    (strongConvexOn_iff_convex.mp
      (strongConvexOn_quadratic B hBsymm c hBcoercive))
  have hell : ConcaveOn ℝ Set.univ (fun u : V ↦ ell u) :=
    ell.toLinearMap.concaveOn convex_univ
  have hconvex := (hquadratic.add hPhiConvex).sub hell
  rw [show (fun u : V ↦ variationalEnergy B Phi ell u - c / 2 * ‖u‖ ^ 2) =
      ((fun u : V ↦ (1 / 2 : ℝ) * B u u - c / 2 * ‖u‖ ^ 2) +
        Phi - fun u ↦ ell u) by
    funext u
    simp only [variationalEnergy, PDE.Analysis.Variational.energy, Pi.add_apply,
      Pi.sub_apply]
    ring]
  exact hconvex

/-- A nonnegative symmetric quadratic form and a convex potential give a
convex variational energy. -/
theorem convexOn_variationalEnergy
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : V → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (ell : StrongDual ℝ V) :
    ConvexOn ℝ Set.univ (variationalEnergy B Phi ell) := by
  simpa only [strongConvexOn_zero] using
    strongConvexOn_variationalEnergy B hBsymm 0
      (by simpa using hBnonneg) Phi hPhiConvex ell

/-- Strict convexity of the nonlinear potential also gives strict convexity
of the full energy when the symmetric quadratic form is nonnegative. -/
theorem strictConvexOn_variationalEnergy_of_potential
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : V → ℝ) (hPhiStrict : StrictConvexOn ℝ Set.univ Phi)
    (ell : StrongDual ℝ V) :
    StrictConvexOn ℝ Set.univ (variationalEnergy B Phi ell) := by
  have hquadraticStrong :
      StrongConvexOn Set.univ 0 (fun u : V ↦ (1 / 2 : ℝ) * B u u) :=
    strongConvexOn_quadratic B hBsymm 0 (by simpa using hBnonneg)
  have hquadratic :
      ConvexOn ℝ Set.univ (fun u : V ↦ (1 / 2 : ℝ) * B u u) := by
    simpa only [strongConvexOn_zero] using hquadraticStrong
  have hell : ConcaveOn ℝ Set.univ (fun u : V ↦ ell u) :=
    ell.toLinearMap.concaveOn convex_univ
  have hstrict := (hquadratic.add_strictConvexOn hPhiStrict).sub_concaveOn hell
  rw [show variationalEnergy B Phi ell =
      (fun u : V ↦ (1 / 2 : ℝ) * B u u) + Phi - fun u ↦ ell u by
    funext u
    simp only [variationalEnergy, PDE.Analysis.Variational.energy, Pi.add_apply,
      Pi.sub_apply]
    ring]
  exact hstrict

/-- Norm lower semicontinuity of the potential passes to the full energy,
since its quadratic and load terms are continuous. -/
theorem lowerSemicontinuous_variationalEnergy
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (Phi : V → ℝ) (hPhiLsc : LowerSemicontinuous Phi)
    (ell : StrongDual ℝ V) :
    LowerSemicontinuous (variationalEnergy B Phi ell) := by
  have hcontinuous :
      Continuous (fun u : V ↦ (1 / 2 : ℝ) * B u u - ell u) := by
    fun_prop
  exact hcontinuous.lowerSemicontinuous.add hPhiLsc

/-- An affine lower bound on the potential, together with ellipticity of the
quadratic form, makes the semilinear energy coercive. -/
theorem tendsto_variationalEnergy_atTop
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ) (a b : ℝ) (ha : 0 ≤ a)
    (hPhiLower : ∀ u, -(a * ‖u‖ + b) ≤ Phi u)
    (ell : StrongDual ℝ V) :
    Tendsto (variationalEnergy B Phi ell)
      (Bornology.cobounded V) atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  let d : ℝ := a + ‖ell‖
  filter_upwards [eventually_cobounded_le_norm (max 1 (max (4 * d / c) (4 * (max R 0 + b) / c)))]
    with u hu
  obtain ⟨hu1, hud, huR⟩ : 1 ≤ ‖u‖ ∧ 4 * d / c ≤ ‖u‖ ∧ 4 * (max R 0 + b) / c ≤ ‖u‖ := by
    simpa only [max_le_iff] using hu
  rw [div_le_iff₀ hc] at hud huR
  have hd : 0 ≤ d := add_nonneg ha (norm_nonneg ell)
  have hell : ell u ≤ ‖ell‖ * ‖u‖ := (Real.le_norm_self _).trans (ell.le_opNorm u)
  have henergy : c / 2 * ‖u‖ * ‖u‖ - d * ‖u‖ - b ≤ variationalEnergy B Phi ell u := by
    dsimp only [variationalEnergy, PDE.Analysis.Variational.energy, d]
    nlinarith [hBcoercive u, hPhiLower u]
  linarith [hd, le_max_left R 0, mul_le_mul_of_nonneg_right hud (norm_nonneg u),
    mul_le_mul_of_nonneg_left hu1 (mul_nonneg hc.le (norm_nonneg u))]

/-- The semilinear energy attains its global minimum by the direct method. -/
theorem exists_variationalEnergy_minimizer
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (hPhiLsc : LowerSemicontinuous Phi)
    (a b : ℝ) (ha : 0 ≤ a)
    (hPhiLower : ∀ u, -(a * ‖u‖ + b) ≤ Phi u)
    (ell : StrongDual ℝ V) :
    ∃ u, ∀ v, variationalEnergy B Phi ell u ≤
      variationalEnergy B Phi ell v := by
  exact
    PDE.CalculusOfVariations.exists_global_minimizer_of_convex_lowerSemicontinuous_of_coercive
      (variationalEnergy B Phi ell)
      ((strongConvexOn_variationalEnergy
        B hBsymm c hBcoercive Phi hPhiConvex ell).strictConvexOn hc).convexOn
      (lowerSemicontinuous_variationalEnergy B Phi hPhiLsc ell)
      (tendsto_variationalEnergy_atTop
        B c hc hBcoercive Phi a b ha hPhiLower ell)

/-- The direct-method minimizer is unique because ellipticity makes the full
energy strongly convex. -/
theorem existsUnique_variationalEnergy_minimizer
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (hPhiLsc : LowerSemicontinuous Phi)
    (a b : ℝ) (ha : 0 ≤ a)
    (hPhiLower : ∀ u, -(a * ‖u‖ + b) ≤ Phi u)
    (ell : StrongDual ℝ V) :
    ∃! u, ∀ v, variationalEnergy B Phi ell u ≤
      variationalEnergy B Phi ell v := by
  obtain ⟨u, hu⟩ :=
    exists_variationalEnergy_minimizer
      B hBsymm c hc hBcoercive Phi hPhiConvex hPhiLsc
        a b ha hPhiLower ell
  refine ⟨u, hu, fun v hv ↦ ?_⟩
  exact
    ((strongConvexOn_variationalEnergy
      B hBsymm c hBcoercive Phi hPhiConvex ell).strictConvexOn hc).eq_of_isMinOn
      (fun w _ ↦ hv w) (fun w _ ↦ hu w) (Set.mem_univ v) (Set.mem_univ u)

/-- Fréchet differentiation of the semilinear energy. Symmetry combines the
two derivatives of `B(u,u)` into the weak elliptic term `B(u,-)`. -/
theorem hasFDerivAt_variationalEnergy
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (Phi : V → ℝ) (ell : StrongDual ℝ V)
    {u : V} {DPhi : StrongDual ℝ V}
    (hPhiDiff : HasFDerivAt Phi DPhi u) :
    HasFDerivAt (variationalEnergy B Phi ell)
      (B u + DPhi - ell) u := by
  have h := (PDE.CalculusOfVariations.quadraticEnergy_hasFDerivAt B hBsymm ell u).add hPhiDiff
  rwa [sub_add_eq_add_sub] at h

/-- Every differentiable global minimizer satisfies the semilinear weak
Euler equation `B(u,v) + D Phi(u)[v] = ell(v)`. -/
theorem weakEquation_of_variationalEnergy_minimizer
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (Phi : V → ℝ) (ell : StrongDual ℝ V)
    {u : V} {DPhi : StrongDual ℝ V}
    (hmin : ∀ v, variationalEnergy B Phi ell u ≤
      variationalEnergy B Phi ell v)
    (hPhiDiff : HasFDerivAt Phi DPhi u) :
    ∀ v, B u v + DPhi v = ell v := by
  have hlocal : IsLocalMin (variationalEnergy B Phi ell) u :=
    Filter.Eventually.of_forall hmin
  have hzero :
      B u + DPhi - ell = 0 :=
    hlocal.hasFDerivAt_eq_zero
      (hasFDerivAt_variationalEnergy B hBsymm Phi ell hPhiDiff)
  intro v
  have happ := congrArg (fun L : StrongDual ℝ V ↦ L v) hzero
  apply sub_eq_zero.mp
  simpa using happ

/-- Convexity of a differentiable potential makes the full semilinear
operator quantitatively invertible on its range. -/
theorem norm_sub_le_semilinear_operator_sub_norm_div_of_convex_potential
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : V → StrongDual ℝ V)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (u w : V) :
    ‖u - w‖ ≤
      ‖(B u + DPhi u) - (B w + DPhi w)‖ / c := by
  apply SobolevSpace.Weak.norm_sub_le_semilinear_operator_sub_norm_div
    B c hc hBcoercive DPhi
  exact
    PDE.Analysis.sub_apply_sub_nonneg_of_convex_of_hasFDerivAt
      hPhiConvex (hPhiDiff u) (hPhiDiff w)

/-- Convexity of a differentiable potential makes its derivative monotone.
Consequently, coercivity bounds the distance between two weak solutions by
the distance between their loads. -/
theorem norm_sub_le_load_sub_norm_div_of_convex_potential
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ z, c * ‖z‖ * ‖z‖ ≤ B z z)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : V → StrongDual ℝ V)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    {ell₁ ell₂ : StrongDual ℝ V} {u w : V}
    (hu : ∀ v, B u v + DPhi u v = ell₁ v)
    (hw : ∀ v, B w v + DPhi w v = ell₂ v) :
    ‖u - w‖ ≤ ‖ell₁ - ell₂‖ / c := by
  apply SobolevSpace.Weak.norm_sub_le_load_sub_norm_div
    B c hc hBcoercive DPhi hu hw
  exact
    PDE.Analysis.sub_apply_sub_nonneg_of_convex_of_hasFDerivAt
      hPhiConvex (hPhiDiff u) (hPhiDiff w)

/-- Under differentiability of the potential, the direct method produces the
unique solution of the semilinear weak equation. The supporting hyperplane at
the origin supplies the affine lower bound needed for coercivity. -/
theorem existsUnique_variational_weak_solution
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : V → StrongDual ℝ V)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (ell : StrongDual ℝ V) :
    ∃! u, ∀ v, B u v + DPhi u v = ell v := by
  have hPhiLsc : LowerSemicontinuous Phi :=
    (continuous_iff_continuousAt.2 fun u ↦
      (hPhiDiff u).continuousAt).lowerSemicontinuous
  have hPhiLower :
      ∀ u, -(‖DPhi 0‖ * ‖u‖ + (-Phi 0)) ≤ Phi u := by
    intro u
    have h :=
      PDE.Analysis.sub_norm_mul_norm_sub_le_of_convex_of_hasFDerivAt
        hPhiConvex (hPhiDiff 0) u
    simp only [sub_zero] at h
    linarith
  obtain ⟨u, hu⟩ :=
    exists_variationalEnergy_minimizer
      B hBsymm c hc hBcoercive Phi hPhiConvex hPhiLsc
        ‖DPhi 0‖ (-Phi 0) (norm_nonneg _) hPhiLower ell
  have huWeak :=
    weakEquation_of_variationalEnergy_minimizer
      B hBsymm Phi ell hu (hPhiDiff u)
  refine ⟨u, huWeak, fun w hw ↦ ?_⟩
  have hnorm :
      ‖u - w‖ ≤ ‖ell - ell‖ / c :=
    norm_sub_le_load_sub_norm_div_of_convex_potential
      B c hc hBcoercive Phi hPhiConvex DPhi hPhiDiff huWeak hw
  have hzero : ‖u - w‖ = 0 :=
    le_antisymm (by simpa using hnorm) (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

/-- The variational semilinear operator `u ↦ B u + D Phi u` is surjective
onto the strong dual. -/
theorem surjective_semilinear_operator_of_convex_potential
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : V → StrongDual ℝ V)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u) :
    Function.Surjective fun u ↦ B u + DPhi u := by
  intro ell
  obtain ⟨u, hu, _⟩ :=
    existsUnique_variational_weak_solution
      B hBsymm c hc hBcoercive Phi hPhiConvex DPhi hPhiDiff ell
  refine ⟨u, ?_⟩
  ext v
  exact hu v

/-- A coercive symmetric form plus the derivative of a convex potential is a
bijection from the Hilbert space onto its strong dual. -/
theorem bijective_semilinear_operator_of_convex_potential
    [CompleteSpace V]
    (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (c : ℝ) (hc : 0 < c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : V → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : V → StrongDual ℝ V)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u) :
    Function.Bijective fun u ↦ B u + DPhi u := by
  refine ⟨?_, surjective_semilinear_operator_of_convex_potential
    B hBsymm c hc hBcoercive Phi hPhiConvex DPhi hPhiDiff⟩
  apply SobolevSpace.Weak.injective_semilinear_operator_of_monotone
    B c hc hBcoercive DPhi
  intro u w
  exact
    PDE.Analysis.sub_apply_sub_nonneg_of_convex_of_hasFDerivAt
      hPhiConvex (hPhiDiff u) (hPhiDiff w)

end PDE.Elliptic.Semilinear
