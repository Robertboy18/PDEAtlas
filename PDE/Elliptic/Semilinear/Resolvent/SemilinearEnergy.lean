/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.Analysis.InnerProductSpace.Dual
import PDE.Elliptic.Semilinear.Resolvent.ConvexGradient.Basic
import PDE.Elliptic.Semilinear.Variational

/-!
# Semilinear-energy resolvents

We specialize the convex-gradient resolvent to the full semilinear
energy

`u ↦ (1 / 2) * B u u + Phi u`

on a real Hilbert space `H`. Its derivative is the strong-dual-valued operator
`u ↦ B u + DPhi u`. Symmetry and nonnegativity of `B`, together with convexity
of `Phi`, make the energy convex, so for every `lambda ≥ 0` and `x ∈ H` the
resolvent equation

`⟪u, v⟫ + lambda * (B u v + DPhi u v) = ⟪x, v⟫  for all v`

has exactly one solution `u = J_lambda x`. This is the convex-gradient case of
the resolvent `(I + lambda A)⁻¹` of a maximal monotone operator `A`. If `B`
has coercivity modulus `c`, the usual firm nonexpansivity of `J_lambda`
sharpens to the contraction factor `1 / (1 + lambda * c)`.

The development uses direct propositions and functions; no operator or
problem structure is introduced.

## Main results

* `existsUnique_semilinearEnergy_resolvent`: unique solvability of the resolvent equation.
* `semilinearEnergyResolvent`, `semilinearEnergyResolvent_equation`: the resolvent and the
  identity `J_lambda x + lambda • (B (J_lambda x) + DPhi (J_lambda x)) = x` under the Riesz
  identification of `H` with its dual.
* `semilinearEnergyResolvent_norm_sub_le`, `semilinearEnergyResolvent_lipschitzWith`: the
  contraction estimate `‖J_lambda x - J_lambda y‖ ≤ ‖x - y‖ / (1 + lambda * c)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, Theorem 1 (iv) and the definition of the nonlinear
  resolvent, pp. 561-563.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 7 (The Hille–Yosida Theorem), pp. 181-199, for the
  resolvent and the Yosida approximation of a linear maximal monotone operator.
  <https://doi.org/10.1007/978-0-387-70914-7_7>
* H. Brezis, *Opérateurs maximaux monotones et semi-groupes de contractions dans les espaces
  de Hilbert*, North-Holland Mathematics Studies, North-Holland, 1973, Chapitre II
  (Opérateurs maximaux monotones), pp. 19-51.
  <https://doi.org/10.1016/S0304-0208(08)72383-1>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The resolvent equation for the derivative of the full semilinear energy
has a unique solution. -/
theorem existsUnique_semilinearEnergy_resolvent
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) :
    ∃! u, ∀ v,
      inner ℝ u v + lambda * (B u v + DPhi u v) = inner ℝ x v := by
  have hEnergyDiff :
      ∀ u, HasFDerivAt (variationalEnergy B Phi 0) (B u + DPhi u) u := by
    intro u
    simpa only [sub_zero] using
      hasFDerivAt_variationalEnergy B hBsymm Phi 0 (hPhiDiff u)
  simpa only [add_apply] using
    existsUnique_convex_gradient_resolvent
      (variationalEnergy B Phi 0)
      (convexOn_variationalEnergy
        B hBsymm hBnonneg Phi hPhiConvex 0)
      (fun u ↦ B u + DPhi u) hEnergyDiff lambda hlambda x

/-- The resolvent of the derivative `u ↦ B u + DPhi u` of the full
semilinear energy. -/
noncomputable def semilinearEnergyResolvent
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) : H :=
  Classical.choose <|
    existsUnique_semilinearEnergy_resolvent
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff lambda hlambda x

/-- The semilinear-energy resolvent satisfies its weak equation. -/
theorem semilinearEnergyResolvent_weak_equation
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x v : H) :
    inner ℝ
          (semilinearEnergyResolvent
            B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
              lambda hlambda x)
          v +
        lambda *
          (B
              (semilinearEnergyResolvent
                B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
                  lambda hlambda x)
              v +
            DPhi
              (semilinearEnergyResolvent
                B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
                  lambda hlambda x)
              v) =
      inner ℝ x v := by
  exact
    (Classical.choose_spec
      (existsUnique_semilinearEnergy_resolvent
        B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda x)).1 v

/-- Under the Riesz identification, the semilinear resolvent solves
`J_lambda x + lambda * (B (J_lambda x) + DPhi (J_lambda x)) = x`. -/
theorem semilinearEnergyResolvent_equation
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) :
    InnerProductSpace.toDual ℝ H
          (semilinearEnergyResolvent
            B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
              lambda hlambda x) +
        lambda •
          (B
              (semilinearEnergyResolvent
                B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
                  lambda hlambda x) +
            DPhi
              (semilinearEnergyResolvent
                B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
                  lambda hlambda x)) =
      InnerProductSpace.toDual ℝ H x := by
  ext v
  simpa only [add_apply, smul_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply] using
    semilinearEnergyResolvent_weak_equation
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        lambda hlambda x v

/-- A point is the semilinear-energy resolvent value exactly when it
satisfies the defining weak equation. -/
theorem semilinearEnergyResolvent_eq_iff
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x u : H) :
    semilinearEnergyResolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda x = u ↔
      ∀ v, inner ℝ u v + lambda * (B u v + DPhi u v) =
        inner ℝ x v := by
  constructor
  · rintro rfl
    exact semilinearEnergyResolvent_weak_equation
      B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
        lambda hlambda x
  · intro hu
    exact
      ((Classical.choose_spec
        (existsUnique_semilinearEnergy_resolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda x)).2 u hu).symm

/-- Coercivity of the quadratic form improves firm nonexpansivity to the
quantitative norm estimate

`‖J_lambda x - J_lambda y‖ ≤ ‖x - y‖ / (1 + lambda * c)`.
-/
theorem semilinearEnergyResolvent_norm_sub_le
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (c : ℝ) (hc : 0 ≤ c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x y : H) :
    ‖semilinearEnergyResolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda x -
        semilinearEnergyResolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda y‖ ≤
      ‖x - y‖ / (1 + lambda * c) := by
  let u := semilinearEnergyResolvent B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
  let w := semilinearEnergyResolvent B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff lambda hlambda y
  let d := u - w
  have hu : inner ℝ u d + lambda * (B u d + DPhi u d) = inner ℝ x d :=
    semilinearEnergyResolvent_weak_equation B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
      lambda hlambda x d
  have hw : inner ℝ w d + lambda * (B w d + DPhi w d) = inner ℝ y d :=
    semilinearEnergyResolvent_weak_equation B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
      lambda hlambda y d
  have hmonotone : 0 ≤ (DPhi u - DPhi w) d :=
    PDE.Analysis.sub_apply_sub_nonneg_of_convex_of_hasFDerivAt hPhiConvex (hPhiDiff u)
      (hPhiDiff w)
  have hbalance : ‖d‖ ^ 2 + lambda * (B d d + (DPhi u - DPhi w) d) = inner ℝ (x - y) d := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left x y, ← hu, ← hw]
    simp only [d, inner_sub_left, map_sub, sub_apply]
    ring
  have henergy : (1 + lambda * c) * ‖d‖ ^ 2 ≤ ‖x - y‖ * ‖d‖ := by
    nlinarith [mul_nonneg hlambda hmonotone, mul_le_mul_of_nonneg_left (hBcoercive d) hlambda,
      real_inner_le_norm (x - y) d]
  change ‖d‖ ≤ ‖x - y‖ / (1 + lambda * c)
  rw [le_div_iff₀ (by positivity)]
  rcases (norm_nonneg d).eq_or_lt with hd | hd
  · rw [← hd, zero_mul]
    exact norm_nonneg _
  · nlinarith

/-- The full semilinear-energy resolvent is globally Lipschitz with constant
`1 / (1 + lambda * c)`. -/
theorem semilinearEnergyResolvent_lipschitzWith
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hBsymm : ∀ u v, B u v = B v u)
    (hBnonneg : ∀ u, 0 ≤ B u u)
    (c : ℝ) (hc : 0 ≤ c)
    (hBcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    (Phi : H → ℝ) (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    LipschitzWith (Real.toNNReal (1 / (1 + lambda * c)))
      (semilinearEnergyResolvent
        B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
          lambda hlambda) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  have h :=
    semilinearEnergyResolvent_norm_sub_le
      B hBsymm hBnonneg c hc hBcoercive
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖semilinearEnergyResolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda x -
        semilinearEnergyResolvent
          B hBsymm hBnonneg Phi hPhiConvex DPhi hPhiDiff
            lambda hlambda y‖ ≤
        ‖x - y‖ / (1 + lambda * c) :=
      h
    _ = (1 / (1 + lambda * c)) * ‖x - y‖ := by ring

end PDE.Elliptic.Semilinear
