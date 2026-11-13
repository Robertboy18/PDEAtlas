/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartCoefficientRegularity
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Boundary.H2.FlattenedEstimate
import PDE.Elliptic.Regularity.Boundary.HigherOrder.ChartPullback
import PDE.Elliptic.Regularity.Boundary.HigherOrder.WeakEquation
import PDE.Elliptic.Regularity.HigherOrder.UpperRegularityHigher
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Arbitrary-order boundary chart piece

`exists_boundaryChart_higherOrder_localized_piece` composes higher-order boundary localization and
flattening, the upper-half-space regularity induction, and the direct chart pullback. The preceding
step of the global induction on the order enters explicitly as a physical `W^{k+1,2}` representative
of the weak solution. This is the chart step of the higher-order theory, step 5 of Evans's proof of
§6.3.2, Theorem 5, which straightens the boundary as in the proof of Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity) and step 5 of
  its proof, pp. 340-343.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]

/--
For positive forcing order `k`, the boundary partition piece of a Dirichlet
solution belongs to `W^{k+2,2}`.

The selected forward chart is `C^{k+2}`, its inverse is `C^{k+1}`, and the
physical `W^{k+1,2}` representative is the output of the preceding step of
the global induction on the order.
-/
theorem exists_boundaryChart_higherOrder_localized_piece
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (hChart : ContDiff ℝ (k + 2)
      (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ContDiff ℝ (k + 1)
      (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ⇑((A r s : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x r s)
    (haContDiff : ∀ r s, ContDiff ℝ (k + 1) (fun x ↦ a x r s))
    (F : W^{k,2}(Omega))
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n (k + 1) ∞ Omega)
        (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
        DerivLp n 2 Omega)
      u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha)
    (U : W^{k + 1,2}(Omega))
    (hU :
      ⇑((U : WkpAmbientOn n (k + 1) 2 Omega)
          (baseIndex n (k + 1)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega)) :
    ∃ W : W^{k + 2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦ (hOmega.toC1ExtensionAtlas.boundaryCutoff i).toFun x *
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  classical
  let hC1 := hOmega.toC1ExtensionAtlas
  let upper := HalfSpace.upper n
  let hUpper := HalfSpace.measurableSet_upper (n := n)
  let U0 : W^{1,2}(Omega) := lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) U
  have hU0eq : U0 = (u : H¹(Omega)) :=
    WkpSpaceOn.ext_of_base_ae hC1.isOpen _ _ (by simpa [U0] using hU)
  have htrace0 : U0 ∈ (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule := hU0eq ▸ u.property
  obtain ⟨Jzero, hJzero, hJacobian⟩ :=
    exists_inverseChartJacobianWeight_lowerBound_on_cutoff hOmega i
  obtain ⟨m, hm, hGradient⟩ := exists_gradientLowerBound_on_cutoff hOmega i
  let beta := Jzero * alpha * m ^ 2
  obtain ⟨upperForcing, hFlattenedWeakEquation⟩ :=
    exists_flattenedLocalized_equation_on_upper k hk hOmega i hChartSymm A a haRep F U htrace0
      (by convert hu using 1; exact Subtype.ext hU0eq) beta
  let aUpper : Fin n → Fin n → ℝ^n → ℝ := fun r s y ↦
    extendedFlattenedPrincipalCoefficientAt (n := n) hC1 i beta a y r s
  have hExtended (r s : Fin n) : ContDiff ℝ (k + 1) (aUpper r s) :=
    contDiff_extendedFlattenedPrincipalCoefficientAt_of_chartRegularity hC1 a haContDiff i
      hChart hChartSymm beta r s
  have hExtendedC1 (r s : Fin n) : ContDiff ℝ 1 (aUpper r s) := (hExtended r s).of_le (by simp)
  let coeff : Fin n → Fin n → W^{k + 1,∞}(upper) := fun r s ↦
    extendedFlattenedPrincipalCoefficientWkTop (n := n) hC1 i beta a r s (hExtended r s) upper
  let coeff0 : Fin n → Fin n → DerivLp n ∞ upper := fun r s ↦
    ((coeff r s : WkpAmbientOn n (k + 1) ∞ upper) (baseIndex n (k + 1)) : DerivLp n ∞ upper)
  have hCoeffRep (r s : Fin n) : ⇑((coeff r s : WkpAmbientOn n (k + 1) ∞ upper)
      (baseIndex n (k + 1)) : DerivLp n ∞ upper) =ᵐ[domainMeasure n upper] aUpper r s := by
    simpa [coeff, aUpper, upper, hUpper, hC1] using
      extendedFlattenedPrincipalCoefficientWkTop_base_ae (n := n) hC1 i beta a r s (hExtended r s)
        upper
  have hCoeffRepAll : ∀ᵐ y ∂domainMeasure n upper, ∀ r s : Fin n,
      (coeff0 r s : ℝ^n → ℝ) y = aUpper r s y :=
    ae_all_iff.2 fun r ↦ ae_all_iff.2 fun s ↦ hCoeffRep r s
  have hAElliptic : AEUniformlyElliptic (n := n) (Ω := upper) coeff0 beta := by
    refine ⟨mul_pos (mul_pos hJzero halpha) (sq_pos_of_pos hm), ?_⟩
    filter_upwards [hCoeffRepAll, ae_restrict_mem hUpper] with y hy hyUpper xi
    simpa [MatrixEllipticLowerBound, dotProduct, principalEnergy, pow_two, hy, aUpper, beta,
      mul_comm, mul_left_comm, mul_assoc] using
      matrixEllipticLowerBound_extendedFlattenedPrincipalCoefficientAt_on_upper hC1 i beta a Jzero
        alpha m hJzero.le halpha.le (by simp [beta]) hElliptic hJacobian hGradient y hyUpper xi
  have hnormal : 2 ≤ k → NormalCoefficientCompactPerturbation k coeff := fun _ ↦
    let l := PDE.Common.lastIndex (n := n)
    { representative := aUpper l l
      constant := scalarIdentityMatrix (n := n) beta l l
      contDiff := (hExtended l l).of_le (by simp)
      compactSupport_sub_constant :=
        hasCompactSupport_extendedFlattenedPrincipalCoefficientDeviation (n := n) hC1 i beta a l l
      base_ae := hCoeffRep l l }
  let uFlat : H¹₀(upper) := Extension.C1.BoundaryPiece.flattenH10 hC1 i u
  have hdu (r : Fin n) : (derivCoordCLM (n := n) (Ω := upper) r uFlat : ℝ^n → ℝ) =
      flattenedChartGradient hC1 i U0 r := by
    rw [hU0eq]
    rfl
  let gUpper : DerivLp n 2 upper :=
    ((upperForcing : WkpAmbientOn n k 2 upper) (baseIndex n k) : DerivLp n 2 upper)
  have hWeak : IsWeakDivergenceSolution (n := n) (Ω := upper) coeff0 gUpper uFlat := by
    refine ⟨HalfSpace.isOpen_upper (n := n), fun phi ↦ ?_⟩
    refine (integral_principalPairing_test_eq_sum coeff0 uFlat phi).symm.trans
      ((integral_congr_ae ?_).trans (show (∫ y, principalPairing (fun r s ↦ aUpper r s y)
        (fun r ↦ (derivCoordCLM (n := n) (Ω := upper) r uFlat : ℝ^n → ℝ) y)
        (fun r ↦ (∂[r] phi.1.toFun) y) ∂domainMeasure n upper) = _ by
          simp_rw [hdu]
          simpa [aUpper, gUpper, upper, hC1, U0] using hFlattenedWeakEquation phi))
    filter_upwards [hCoeffRepAll] with y hy
    simp only [principalPairing, hy]
  obtain ⟨Uupper, hUupper⟩ := exists_principal_higherOrder_on_upper k coeff aUpper
    (extendedFlattenedPrincipalCoefficientLipConsts (n := n) hC1 i beta a hExtendedC1)
    (lipschitzWith_extendedFlattenedPrincipalCoefficient_entries (n := n) hC1 i beta a hExtendedC1)
    hCoeffRep hAElliptic hnormal upperForcing uFlat hWeak
  exact exists_boundaryChart_pullback_localized_piece (k + 2) (by omega) hOmega i hChart u
    Uupper hUupper

end SobolevSpace.GraphSpace.BoundaryRegularity
