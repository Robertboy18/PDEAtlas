/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
import PDE.Elliptic.Regularity.Coefficients.GlobalExtension
import PDE.Elliptic.Regularity.Interior.H2Compactness
import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension

/-!
# The interior `H²` partition piece

`exists_interior_h2_localized_piece` puts the interior difference-quotient theorem, Evans's §6.3.1,
Theorem 1, into the form needed by our partition-of-unity proof of global `H²` regularity. Evans's
proof of §6.3.2, Theorem 4 covers the boundary by finitely many sets and adds the interior estimate
to the boundary ones; the partition of unity is ours.

The coefficient field is assumed `C¹` on a global representative but only uniformly elliptic on the
physical domain. The ellipticity-preserving extension theorem constructs the globally bounded and
Lipschitz coefficients required by the whole-space difference-quotient argument.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, Theorem 1 (Interior H²-regularity), pp. 327-331, and
  §6.3.2, step 10 of the proof of Theorem 4, p. 340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ}

variable [Fact (0 < n)]

/-- Evans's §6.3.1, Theorem 1, as the interior partition piece.

Only ellipticity on the physical domain is assumed.  A globally bounded,
Lipschitz, elliptic extension is constructed internally. -/
theorem exists_interior_h2_localized_piece
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ((((A i j : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) : ℝ^n → ℝ))
          =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦ hOmega.interiorCutoff.toFun x *
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  classical
  obtain ⟨aext, C, Aglobal, hEqOn, hLip, hglobalRep, hglobalElliptic⟩ :=
    exists_global_ellipticCoefficientExtension hOmega a haC1 halpha hElliptic
  have hcoeff : (fun i j ↦ ((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) :
      DerivLp n ∞ Omega)) = fun i j ↦
        restrictDerivLp (n := n) (p := ∞) (subset_univ Omega) (Aglobal i j) := by
    funext i j
    refine Lp.ext ?_
    filter_upwards [restrictDerivLp_apply_ae (p := ∞) (subset_univ Omega) (Aglobal i j),
      ae_restrict_of_ae (hglobalRep i j), haRep i j,
      ae_restrict_mem hOmega.isOpen.measurableSet] with x hrest hglob hphys hx
    rw [hrest, hglob, hphys, hEqOn hx]
  obtain ⟨V, hVopen, hK0V, hVOmega, Wlocal, hWlocal, -⟩ :=
    exists_zeroTrace_local_h2_open_neighborhood_of_compact hOmega.isOpen Aglobal
      (fun i j x ↦ aext x i j) C hLip hglobalRep (half_pos halpha) hglobalElliptic f u
      ((isWeakSolution_iff_isWeakDivergenceSolution hOmega.isOpen _ f u).2 (hcoeff ▸ hu))
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport (n := n) (Ω := Omega))
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_interiorSupport (n := n) (Ω := Omega))
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport_subset_domain
        (n := n) (Ω := Omega))
  have hlocal : ∀ᵐ x ∂volume, x ∈ V → baseRepresentative Wlocal x =
      ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega) (baseIndex n 1) : DerivLp n 2 Omega) x := by
    refine (ae_restrict_iff' hVopen.measurableSet).1 ?_
    filter_upwards [hWlocal, ae_restrict_of_ae (ZeroTrace.zeroExtendH10_coordinate_apply_ae
      hOmega.isOpen.measurableSet u (baseIndex n 1)), ae_restrict_mem hVopen.measurableSet]
      with x hl hz hxV
    rw [baseRepresentative, hl, hz, indicator_of_mem (hVOmega hxV)]
  refine ⟨_, (CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
    hVopen hVOmega hOmega.interiorCutoff hK0V Wlocal).trans ?_⟩
  filter_upwards [ae_restrict_of_ae hlocal] with x hx
  by_cases hxV : x ∈ V
  · rw [hx hxV]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hxV (hK0V h)]

end SobolevSpace.GraphSpace.BoundaryRegularity
