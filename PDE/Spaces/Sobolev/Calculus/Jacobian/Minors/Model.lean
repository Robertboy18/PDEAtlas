/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Jacobian
public import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative
public import PDE.Analysis.Calculus.Jacobian.Basic
public import PDE.Analysis.Matrix.Submatrix.ContinuousLinearMap
public import PDE.Analysis.MeasureTheory.Lp.Matrix.Determinant

/-!
# Minors of the weak Jacobian

For a tuple of scalar Sobolev components and a selection of spatial directions,
the selected weak Jacobian is a continuous linear matrix-valued map. Its
determinant belongs to the Lebesgue space with exponent divided by the minor's
degree. These are the original weak derivative representatives, simultaneously
identified almost everywhere.

Evans calls the `(n - 1) × (n - 1)` minors of `Du`, with signs, the cofactor matrix `cof Du`
(§8.1.4(b)), and bounds `det Du` in `L^{q/n}` by `|det Du| ≤ C |Du|ⁿ` (§8.2.4(b)).
`isBounded_wkpJacobianMinorLp_range` is the corresponding bound for a minor of degree `m` in
`L^{p/m}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), Notation, p. 462, for `cof`; and §8.2.4(b), step 4
  of the proof of the Lemma (Weak continuity of determinants), p. 478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μΩ" => domainMeasure n Ω

/-- For `σ : Fin m → Fin n`, the `m × m` matrix `(∂_{σ j} u_i)_{i,j}` of weak partial
derivatives of `u : Fin m → W^{1,p}(Ω)`, as a continuous linear map into `L^p`. -/
def wkpSelectedJacobianCLM (σ : Fin m → Fin n) :
    (Fin m → W^{1,p}(Ω)) →L[ℝ] Lp (Matrix (Fin m) (Fin m) ℝ) p μΩ :=
  ((Matrix.submatrixCLM (𝕜 := ℝ) id σ).compLpL p μΩ).comp vectorWkpJacobianCLM

/-- Almost everywhere, every entry `(i, j)` of `wkpSelectedJacobianCLM σ u` is the weak
derivative coordinate `∂_{σ j} u_i` of the graph of `u i`. -/
theorem wkpSelectedJacobianCLM_apply_ae (σ : Fin m → Fin n) (u : Fin m → W^{1,p}(Ω)) :
    ∀ᵐ x ∂μΩ, ∀ i j, wkpSelectedJacobianCLM σ u x i j =
      wkpCoordinateCLM (singleDerivIndex n (σ j)) (u i) x := by
  filter_upwards [(Matrix.submatrixCLM (𝕜 := ℝ) id σ).coeFn_compLpL
    (vectorWkpJacobianCLM u), vectorWkpJacobianCLM_apply_ae u] with x hx hg
  intro i j
  change ((Matrix.submatrixCLM (𝕜 := ℝ) id σ).compLpL p μΩ
    (vectorWkpJacobianCLM u)) x i j = _
  rw [hx]
  exact hg i (σ j)

/-- The minor `det (∂_{σ j} u_i)_{i,j}` of the weak Jacobian of `u : Fin m → W^{1,p}(Ω)`, as an
element of `L^{p/m}`. -/
def wkpJacobianMinorLp (σ : Fin m → Fin n) (u : Fin m → W^{1,p}(Ω)) :
    Lp ℝ (p / ENNReal.ofReal (m : ℝ)) μΩ :=
  Lp.matrixDet (wkpSelectedJacobianCLM σ u)

/-- Almost everywhere, `wkpJacobianMinorLp σ u` is the determinant of the matrix of weak
partial derivatives `∂_{σ j} u_i`. -/
theorem coeFn_wkpJacobianMinorLp (σ : Fin m → Fin n) (u : Fin m → W^{1,p}(Ω)) :
    wkpJacobianMinorLp σ u =ᵐ[μΩ] fun x ↦
      Matrix.det (Matrix.of fun i j ↦
        wkpCoordinateCLM (singleDerivIndex n (σ j)) (u i) x) := by
  filter_upwards [Lp.coeFn_matrixDet (wkpSelectedJacobianCLM σ u),
    wkpSelectedJacobianCLM_apply_ae σ u] with x hx hg
  rw [show wkpJacobianMinorLp σ u x = (wkpSelectedJacobianCLM σ u x).det from hx]
  exact congrArg Matrix.det (Matrix.ext fun i j ↦ hg i j)

/-- On an open `Ω`, if `f` is C¹ on `Ω` and each `u i` is represented almost everywhere by the
component `f · i`, then `wkpJacobianMinorLp σ u` agrees almost everywhere with the minor
`det ((Df)_{i, σ j})` of the Fréchet Jacobian of `f`. -/
theorem wkpJacobianMinorLp_ae_eq_of_contDiffOn (hΩ : IsOpen Ω)
    (σ : Fin m → Fin n) (u : Fin m → W^{1,p}(Ω)) {f : ℝ^n → ℝ^m}
    (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : ∀ i, baseRepresentative (u i) =ᵐ[μΩ] fun x ↦ f x i) :
    wkpJacobianMinorLp σ u =ᵐ[μΩ] fun x ↦
      ((PDE.Analysis.jacobianMatrix f x).submatrix id σ).det := by
  have hcoords : ∀ᵐ x ∂μΩ, ∀ i j,
      wkpCoordinateCLM (singleDerivIndex n (σ j)) (u i) x =
        (∂[σ j] (fun y ↦ f y i)) x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
      wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hΩ (u i)
        ((EuclideanSpace.proj i : ℝ^m →L[ℝ] ℝ).contDiff.comp_contDiffOn hf)
        (hbase i) (σ j)
  filter_upwards [coeFn_wkpJacobianMinorLp σ u, hcoords] with x hx hd
  rw [hx]
  exact congrArg Matrix.det (Matrix.ext fun i j ↦ hd i j)

/-- For `0 < m`, `p ≠ ∞` and `1 ≤ p/m`, the minor `wkpJacobianMinorLp σ` is continuous from
`(W^{1,p}(Ω))^m` to `L^{p/m}`. -/
theorem continuous_wkpJacobianMinorLp [Fact (1 ≤ p / ENNReal.ofReal (m : ℝ))]
    (hm : 0 < m) (hp : p ≠ ∞) (σ : Fin m → Fin n) :
    Continuous (wkpJacobianMinorLp (p := p) (Ω := Ω) σ) :=
  (Lp.continuous_matrixDet hm hp).comp (wkpSelectedJacobianCLM σ).continuous

/-- For `0 < m` and `1 ≤ p/m`, the minors `wkpJacobianMinorLp σ (u k)` of a bounded family `u`
form a bounded set in `L^{p/m}`, by the Hölder estimate for determinants. -/
theorem isBounded_wkpJacobianMinorLp_range [Fact (1 ≤ p / ENNReal.ofReal (m : ℝ))]
    (hm : 0 < m) (σ : Fin m → Fin n) {ι : Type*} {u : ι → Fin m → W^{1,p}(Ω)}
    (hu : Bornology.IsBounded (range u)) :
    Bornology.IsBounded (range fun k ↦ wkpJacobianMinorLp σ (u k)) := by
  apply Lp.isBounded_matrixDet_range hm
  simpa only [← range_comp, Function.comp_def] using
    (wkpSelectedJacobianCLM σ).lipschitzWith.isBounded_image hu

end SobolevSpace.GraphSpace
