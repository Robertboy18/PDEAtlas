/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.SourcePullback
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability -- shake: keep
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Jacobian multipliers for C¹ boundary flattening

When a Sobolev function `v` on `Ω` is straightened by a `C¹` chart `Φᵢ`, its
first derivatives transform by the chain rule

  `∂ₖ(v ∘ Φᵢ⁻¹)(y) = ∑ⱼ (∂ⱼ v)(Φᵢ⁻¹ y) · ∂ₖ(Φᵢ⁻¹)ⱼ(y)`,

with the weak derivatives of `v` on the right. This is the change of variables used in the extension
theorem for `C¹` domains (Evans §5.4, Theorem 1). We handle the coefficients. The Jacobian entry
`flattenJacobianCoefficient i k j = ∂ₖ(Φᵢ⁻¹)ⱼ` is continuous because the inverse chart is globally
`C¹`, hence bounded on the compact flattened support `boundarySupportInTarget i`, and therefore acts
as an `L^∞` multiplier on `L^p` of that set. Composing the pulled-back derivative coordinates of
`Flattening.SourcePullback` with these multipliers and summing over `j` gives the transformed
derivative coordinate on the compact support; zero extension to the upper half-space is carried out
in `Flattening.Assembly`.

## Main definitions and results

* `flattenJacobianCoefficient i k j`: the `(k, j)` entry of the Jacobian of
  `Φᵢ⁻¹`.
* `flattenDerivativeCompactLp i k`: the bounded map sending the family of
  first derivatives `(∂ⱼ v)ⱼ ∈ L^p(Ω)ⁿ` to the transformed `k`-th derivative
  in `L^p(boundarySupportInTarget i)`.
* `flattenDerivativeCompactLp_apply_ae`: its almost-everywhere formula, the
  chain-rule sum above with the pulled-back derivatives cut off to
  `boundarySupport i` and `Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; the proof flattens the boundary
  near each boundary point (step 5, p. 270), extends across the flat boundary, and glues the pieces
  with a partition of unity (step 6, (9), p. 270).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization
open Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The `(k,j)` chain-rule coefficient `∂ₖ(Φᵢ⁻¹)ʲ` for the inverse chart. -/
def flattenJacobianCoefficient
    (i : Fin hΩ.N) (k j : Fin n) : ℝ^n → ℝ :=
  fun y ↦ ((fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y)
    (EuclideanSpace.single k (1 : ℝ))) j

/-- Each inverse-chart Jacobian coefficient is continuous, since the inverse chart is `C¹`. -/
theorem continuous_flattenJacobianCoefficient
    (i : Fin hΩ.N) (k j : Fin n) :
    Continuous (flattenJacobianCoefficient (n := n) (Ω := Ω) i k j) := by
  have hfderiv : Continuous fun y : ℝ^n ↦
      fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y :=
    (hΩ.chart_symm_contDiff i).continuous_fderiv (hn := by simp)
  have happly : Continuous fun y : ℝ^n ↦
      (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) y)
        (EuclideanSpace.single k (1 : ℝ)) :=
    hfderiv.clm_apply continuous_const
  have hcoord : Continuous fun v : ℝ^n ↦ v j := by
    simpa [EuclideanSpace.proj] using (EuclideanSpace.proj j).continuous
  exact hcoord.comp happly

/-- An inverse-chart Jacobian coefficient as an `L∞` multiplier on the
compact flattened support. -/
noncomputable def flattenJacobianCoefficientLpTop
    (i : Fin hΩ.N) (k j : Fin n) :
    SobolevSpace.GraphSpace.DerivLp n ∞
      (boundarySupportInTarget (n := n) (Ω := Ω) i) :=
  let hmem := SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous
    (n := n)
    (isCompact_boundarySupportInTarget
      (n := n) (Ω := Ω) i).isBounded
    (continuous_flattenJacobianCoefficient (n := n) (Ω := Ω) i k j)
  hmem.toLp (flattenJacobianCoefficient (n := n) (Ω := Ω) i k j)

private theorem flattenJacobianCoefficientLpTop_apply_ae
    (i : Fin hΩ.N) (k j : Fin n) :
    ((flattenJacobianCoefficientLpTop (n := n) (Ω := Ω) i k j :
        SobolevSpace.GraphSpace.DerivLp n ∞
          (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n
        (boundarySupportInTarget (n := n) (Ω := Ω) i)]
        flattenJacobianCoefficient (n := n) (Ω := Ω) i k j := by
  let hmem := SobolevSpace.WeakChangeOfVariables.memLp_top_on_bounded_of_continuous
    (n := n)
    (isCompact_boundarySupportInTarget
      (n := n) (Ω := Ω) i).isBounded
    (continuous_flattenJacobianCoefficient (n := n) (Ω := Ω) i k j)
  simpa [flattenJacobianCoefficientLpTop, hmem] using hmem.coeFn_toLp

/-- One Jacobian-weighted derivative coordinate on `boundarySupportInTarget i`. -/
noncomputable def flattenDerivativeTermCompactLp
    (i : Fin hΩ.N) (k j : Fin n) :
    SobolevSpace.GraphSpace.DerivLp n p Ω →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p
        (boundarySupportInTarget (n := n) (Ω := Ω) i) :=
  (SobolevSpace.GraphSpace.mulLpLeft
    (n := n) (p := p)
    (Ω := boundarySupportInTarget (n := n) (Ω := Ω) i)
    (flattenJacobianCoefficientLpTop (n := n) (Ω := Ω) i k j)).comp
      (flattenCompactLp (n := n) (p := p) (Ω := Ω) i)

/-- Almost-everywhere formula for one Jacobian-weighted compact derivative
term. -/
private theorem flattenDerivativeTermCompactLp_apply_ae
    (i : Fin hΩ.N) (k j : Fin n)
    (u : SobolevSpace.GraphSpace.DerivLp n p Ω) :
    ((flattenDerivativeTermCompactLp
        (n := n) (p := p) (Ω := Ω) i k j u :
        SobolevSpace.GraphSpace.DerivLp n p
          (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n
        (boundarySupportInTarget (n := n) (Ω := Ω) i)]
        fun y ↦ flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
          (boundarySupport (n := n) (Ω := Ω) i).indicator
            (Ω.indicator fun x ↦ u x) ((hΩ.chart i).symm y) := by
  let c := flattenJacobianCoefficientLpTop (n := n) (Ω := Ω) i k j
  let pulled := flattenCompactLp (n := n) (p := p) (Ω := Ω) i u
  have hmul := SobolevSpace.GraphSpace.mulLpLeft_apply_ae
    (n := n) (p := p)
    (Ω := boundarySupportInTarget (n := n) (Ω := Ω) i) c pulled
  have hc := flattenJacobianCoefficientLpTop_apply_ae
    (n := n) (Ω := Ω) i k j
  have hpulled := flattenCompactLp_apply_ae
    (n := n) (p := p) (Ω := Ω) i u
  filter_upwards [hmul, hc, hpulled] with y hymul hyc hypulled
  simpa [flattenDerivativeTermCompactLp, c, pulled, hyc, hypulled] using hymul

/-- The complete inverse-Jacobian derivative transformation on the compact
flattened support. -/
noncomputable def flattenDerivativeCompactLp
    (i : Fin hΩ.N) (k : Fin n) :
    (Fin n → SobolevSpace.GraphSpace.DerivLp n p Ω) →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p
        (boundarySupportInTarget (n := n) (Ω := Ω) i) := by
  classical
  exact ∑ j : Fin n,
    (flattenDerivativeTermCompactLp (n := n) (p := p) (Ω := Ω) i k j).comp
      (ContinuousLinearMap.proj j)

private theorem flattenDerivativeCompactLp_apply
    (i : Fin hΩ.N) (k : Fin n)
    (du : Fin n → SobolevSpace.GraphSpace.DerivLp n p Ω) :
    flattenDerivativeCompactLp (n := n) (p := p) (Ω := Ω) i k du =
      ∑ j : Fin n,
        flattenDerivativeTermCompactLp (n := n) (p := p) (Ω := Ω) i k j (du j) := by
  classical
  simp [flattenDerivativeCompactLp]

/-- Almost-everywhere formula for the full compact inverse-Jacobian
derivative. -/
theorem flattenDerivativeCompactLp_apply_ae
    (i : Fin hΩ.N) (k : Fin n)
    (du : Fin n → SobolevSpace.GraphSpace.DerivLp n p Ω) :
    ((flattenDerivativeCompactLp (n := n) (p := p) (Ω := Ω) i k du :
        SobolevSpace.GraphSpace.DerivLp n p
          (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n
        (boundarySupportInTarget (n := n) (Ω := Ω) i)]
        fun y ↦ ∑ j : Fin n,
          flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
            (boundarySupport (n := n) (Ω := Ω) i).indicator
              (Ω.indicator fun x ↦ du j x) ((hΩ.chart i).symm y) := by
  classical
  let μK := domainMeasure n
    (boundarySupportInTarget (n := n) (Ω := Ω) i)
  let term : Fin n → SobolevSpace.GraphSpace.DerivLp n p
      (boundarySupportInTarget (n := n) (Ω := Ω) i) := fun j ↦
    flattenDerivativeTermCompactLp (n := n) (p := p) (Ω := Ω) i k j (du j)
  have hsum :
      (((∑ j : Fin n, term j) : SobolevSpace.GraphSpace.DerivLp n p
          (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
          ℝ^n → ℝ)
        =ᵐ[μK] fun y ↦ ∑ j : Fin n, (term j : ℝ^n → ℝ) y := by
    have haux : ∀ s : Finset (Fin n),
        (((∑ j ∈ s, term j) : SobolevSpace.GraphSpace.DerivLp n p
            (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
            ℝ^n → ℝ)
          =ᵐ[μK] fun y ↦ ∑ j ∈ s, (term j : ℝ^n → ℝ) y := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simp only [Finset.sum_empty]
          change ∀ᵐ y ∂ μK,
            (((0 : SobolevSpace.GraphSpace.DerivLp n p
              (boundarySupportInTarget
                (n := n) (Ω := Ω) i)) : ℝ^n → ℝ) y) = 0
          have hzero := MeasureTheory.Lp.coeFn_zero
            (E := ℝ) (p := p) (μ := μK)
          change ∀ᵐ y ∂ μK,
            (((0 : SobolevSpace.GraphSpace.DerivLp n p
              (boundarySupportInTarget
                (n := n) (Ω := Ω) i)) : ℝ^n → ℝ) y) = 0 at hzero
          exact hzero
      | @insert a s ha ih =>
          have hadd := MeasureTheory.Lp.coeFn_add (term a) (∑ j ∈ s, term j)
          filter_upwards [hadd, ih] with y hyadd hysum
          simp only [Finset.sum_insert ha]
          calc
            (((term a + ∑ j ∈ s, term j) :
                SobolevSpace.GraphSpace.DerivLp n p
                  (boundarySupportInTarget
                    (n := n) (Ω := Ω) i)) : ℝ^n → ℝ) y =
                (term a : ℝ^n → ℝ) y +
                  (((∑ j ∈ s, term j) :
                    SobolevSpace.GraphSpace.DerivLp n p
                      (boundarySupportInTarget
                        (n := n) (Ω := Ω) i)) : ℝ^n → ℝ) y := by
              simpa using hyadd
            _ = (term a : ℝ^n → ℝ) y +
                ∑ j ∈ s, (term j : ℝ^n → ℝ) y := by rw [hysum]
    simpa using haux Finset.univ
  have hterms : ∀ᵐ y ∂ μK, ∀ j : Fin n,
      (term j : ℝ^n → ℝ) y =
        flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
          (boundarySupport (n := n) (Ω := Ω) i).indicator
            (Ω.indicator fun x ↦ du j x) ((hΩ.chart i).symm y) :=
    MeasureTheory.ae_all_iff.2 fun j ↦ by
      have hj := flattenDerivativeTermCompactLp_apply_ae
        (n := n) (p := p) (Ω := Ω) i k j (du j)
      change ∀ᵐ y ∂ domainMeasure n
          (boundarySupportInTarget (n := n) (Ω := Ω) i),
        ((flattenDerivativeTermCompactLp
            (n := n) (p := p) (Ω := Ω) i k j (du j) :
            SobolevSpace.GraphSpace.DerivLp n p
              (boundarySupportInTarget
                (n := n) (Ω := Ω) i)) : ℝ^n → ℝ) y =
          flattenJacobianCoefficient (n := n) (Ω := Ω) i k j y *
            (boundarySupport
              (n := n) (Ω := Ω) i).indicator
              (Ω.indicator fun x ↦ du j x) ((hΩ.chart i).symm y) at hj
      simpa only [term, μK] using hj
  rw [flattenDerivativeCompactLp_apply]
  filter_upwards [hsum, hterms] with y hysum hyterms
  rw [hysum]
  exact Finset.sum_congr rfl fun j _ ↦ hyterms j

end BoundaryPiece

end C1

end Extension

end SobolevSpace
