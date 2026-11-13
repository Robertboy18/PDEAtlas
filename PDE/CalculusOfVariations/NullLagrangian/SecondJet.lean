/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jacobian.SecondJet
public import PDE.Analysis.Calculus.Jet.Quadratic
public import PDE.CalculusOfVariations.NullLagrangian.Basic

/-!
# Null Lagrangians on C² maps

For a jointly `C²` density `L(P,z,x)`, the Euler–Lagrange expression at a point
depends only on the value and the first two Fréchet derivatives of the map there.
A globally smooth quadratic polynomial realizes this second jet. Consequently the
null-Lagrangian property, defined by testing smooth maps, also gives the classical
equation on `C²` maps.

This is the local differential implication used in Evans, §8.1.4(b), where
the interpolation in the proof of Theorem 1 is only `C²`. The open-domain result
requires joint density regularity on the full matrix/value cylinder above the domain.
The target and domain dimensions are independent.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), Definition and proof of Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Elementwise ContDiff

namespace PDE.CalculusOfVariations

variable {n m : ℕ}

/-- A frozen matrix derivative, evaluated in an entry direction, is `C¹` in all three
density variables when the density has a joint `C²` germ. -/
theorem contDiffAt_lagrangianGradientEntry
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
    {a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n)}
    (hL : ContDiffAt ℝ 2
      (fun b : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L b.1 b.2.1 b.2.2) a) (k : Fin m) (i : Fin n) :
    ContDiffAt ℝ 1
      (fun b : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        fderiv ℝ (fun P ↦ L P b.2.1 b.2.2) b.1 (Matrix.single k i 1)) a := by
  have hparam : ContDiffAt ℝ 2
      (Function.uncurry
        (fun (b : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n))
          (P : Matrix (Fin m) (Fin n) ℝ) ↦ L P b.2.1 b.2.2)) (a, a.1) :=
    hL.comp (a, a.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  have hderiv := hparam.fderiv (m := 1) contDiffAt_fst (by norm_num)
  exact hderiv.clm_apply contDiffAt_const

/-- The expression `-div D_P L + D_z L` depends on the complete second jet.
Joint regularity includes the spatial and value dependence of the density. -/
theorem classicalEulerLagrange_congr_secondJet
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
    {u v : ℝ^n → ℝ^m} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x)
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L a.1 a.2.1 a.2.2) (Analysis.jacobianMatrix u x, (u x, x)))
    (hvalue : u x = v x) (hfirst : fderiv ℝ u x = fderiv ℝ v x)
    (hsecond : fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ v) x)
    (k : Fin m) :
    classicalEulerLagrange L u x k = classicalEulerLagrange L v x k := by
  have hdu := hu.differentiableAt (by norm_num)
  have hdv := hv.differentiableAt (by norm_num)
  have hJ : Analysis.jacobianMatrix u x = Analysis.jacobianMatrix v x := by
    ext j i
    rw [Analysis.jacobianMatrix_apply_eq_fderiv hdu,
      Analysis.jacobianMatrix_apply_eq_fderiv hdv, hfirst]
  have hDJ := Analysis.fderiv_jacobianMatrix_eq_of_secondJet hu hv hsecond
  let Φu := fun y ↦ (Analysis.jacobianMatrix u y, (u y, y))
  let Φv := fun y ↦ (Analysis.jacobianMatrix v y, (v y, y))
  have hpoint : Φu x = Φv x := by simp only [Φu, Φv, hJ, hvalue]
  have hΦu := ((Analysis.contDiffAt_jacobianMatrix hu).differentiableAt
    (by norm_num)).hasFDerivAt.prodMk
      (hdu.hasFDerivAt.prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  have hΦv := ((Analysis.contDiffAt_jacobianMatrix hv).differentiableAt
    (by norm_num)).hasFDerivAt.prodMk
      (hdv.hasFDerivAt.prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  have hentry (i : Fin n) :
      (∂[i]
          (fun y ↦ fderiv ℝ (fun P ↦ L P (u y) y) (Analysis.jacobianMatrix u y)
            (Matrix.single k i 1))) x =
        (∂[i]
          (fun y ↦ fderiv ℝ (fun P ↦ L P (v y) y) (Analysis.jacobianMatrix v y)
            (Matrix.single k i 1))) x := by
    let a := fun b : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
      fderiv ℝ (fun P ↦ L P b.2.1 b.2.2) b.1 (Matrix.single k i 1)
    have ha : DifferentiableAt ℝ a (Φu x) :=
      (contDiffAt_lagrangianGradientEntry hL k i).differentiableAt (by norm_num)
    have ha' : DifferentiableAt ℝ a (Φv x) := hpoint ▸ ha
    have heq : fderiv ℝ (a ∘ Φu) x = fderiv ℝ (a ∘ Φv) x := by
      rw [(ha.hasFDerivAt.comp x hΦu).fderiv, (ha'.hasFDerivAt.comp x hΦv).fderiv]
      congr 1
      · exact congrArg (fderiv ℝ a) hpoint
      · congr 1
        exact congrArg (fun A : ℝ^n →L[ℝ] ℝ^m ↦
          A.prod (ContinuousLinearMap.id ℝ (ℝ^n))) hfirst
    exact congrArg (fun A : ℝ^n →L[ℝ] ℝ ↦
      A (EuclideanSpace.single i (1 : ℝ))) heq
  unfold classicalEulerLagrange
  simp_rw [hentry, hJ, hvalue]

/-- Smooth-test nullity implies the equation at any `C²` germ. The domain need not be
open in this local formulation: the original map and density have ambient germs at `x`. -/
theorem IsNullLagrangianOn.classicalEulerLagrange_eq_zero_of_contDiffAt
    {Ω : Set (ℝ^n)}
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
    {u : ℝ^n → ℝ^m} {x : ℝ^n}
    (hnull : IsNullLagrangianOn Ω L) (hx : x ∈ Ω) (hu : ContDiffAt ℝ 2 u x)
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L a.1 a.2.1 a.2.2) (Analysis.jacobianMatrix u x, (u x, x)))
    (k : Fin m) : classicalEulerLagrange L u x k = 0 := by
  obtain ⟨q, hq, hvalue, hfirst, hsecond⟩ := Analysis.exists_contDiff_same_secondJet hu
  rw [classicalEulerLagrange_congr_secondJet hu
    (hq.contDiffAt.of_le (by simp)) hL hvalue.symm hfirst.symm hsecond.symm k]
  exact hnull q hq.contDiffOn x hx k

/-- On an open domain, smooth-test nullity gives the classical equation for every
`C²` map. Density regularity is joint on the full matrix/value cylinder over the domain. -/
theorem IsNullLagrangianOn.classicalEulerLagrange_eq_zero_of_contDiffOn
    {Ω : Set (ℝ^n)}
    {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
    {u : ℝ^n → ℝ^m}
    (hnull : IsNullLagrangianOn Ω L) (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hL : ContDiffOn ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦
        L a.1 a.2.1 a.2.2) {a | a.2.2 ∈ Ω}) :
    ∀ x ∈ Ω, ∀ k, classicalEulerLagrange L u x k = 0 := by
  intro x hx k
  have hopen : IsOpen
      {a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) | a.2.2 ∈ Ω} :=
    hΩ.preimage (continuous_snd.snd)
  exact hnull.classicalEulerLagrange_eq_zero_of_contDiffAt hx
    (hu.contDiffAt (hΩ.mem_nhds hx)) (hL.contDiffAt (hopen.mem_nhds hx)) k

end PDE.CalculusOfVariations
