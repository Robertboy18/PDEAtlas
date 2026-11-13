/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Diffeomorph
public import PDE.Analysis.Calculus.Jet.Pullback
public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Ordered
public import PDE.Hyperbolic.ConservationLaw.System.RiemannInvariant

/-!
# Global Riemann coordinates and the diagonal gradient equation

The coordinate map is a global diffeomorphism. Evans makes the same standing assumption when he
takes the Riemann invariants (4) of §11.3.1 as new coordinates with inverse `z(w)`, and Theorem
2 of §11.3.2 states its condition (27) on all of `ℝ²`. Its components use Mathlib's finite
product space. The flux and the original spacetime retain the Euclidean norm.
The canonical ordered speeds are transported through the inverse coordinate
map; each invariant travels with the opposite family's speed, as in (6) of §11.3.1.

Global coordinates are data. Strict hyperbolicity alone does not supply a global coordinate
diffeomorphism.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.3.1, equations (4)-(6); §11.3.2, Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Manifold
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System

/-- The transport speed of invariant `i` in global Riemann coordinates. -/
def invariantSpeed (flux : ℝ^2 → ℝ^2) (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ))
    (i : Fin 2) (z : Fin 2 → ℝ) : ℝ :=
  characteristicSpeed flux i.rev (Φ.symm z)

/-- A C² strictly hyperbolic flux has C¹ transport speeds in the given
global smooth coordinates. -/
theorem contDiff_invariantSpeed {flux : ℝ^2 → ℝ^2} (hflux : ContDiff ℝ 2 flux)
    (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q) (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ)) (i : Fin 2) :
    ContDiff ℝ 1 (invariantSpeed flux Φ i) :=
  (contDiff_iff_contDiffAt.mpr (fun q ↦ contDiffAt_characteristicSpeed hflux (hhyper q) i.rev)).comp
      (Φ.symm.contDiff.of_le (by simp))

/-- Ordering gives a nonzero signed gap for both invariant families. -/
theorem invariantSpeed_ne_rev {flux : ℝ^2 → ℝ^2} (hhyper : ∀ q, IsStrictlyHyperbolicAt flux q)
    (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ)) (i : Fin 2) (z : Fin 2 → ℝ) :
    invariantSpeed flux Φ i z ≠ invariantSpeed flux Φ i.rev z := by
  apply (characteristicSpeed_spec (hhyper (Φ.symm z))).1.injective.ne
  fin_cases i <;> decide

/-- A closure jet transforms through the coordinate map and the
canonical linear identification of two-dimensional spacetime with a pair. -/
def invariantJet {u : ℝ^2 → ℝ^2} {J : Set ℝ} (hJ : IsOpen J)
    (hu : ContinuousSecondJetOn u {p : ℝ^2 | p 0 ∈ J})
    (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ)) :
    ContinuousSecondJetOn (fun p : ℝ × ℝ ↦ Φ (u !₂[p.1, p.2])) (J ×ˢ univ) := by
  let L : (ℝ × ℝ) ≃L[ℝ] ℝ^2 :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hs : IsOpen {p : ℝ^2 | p 0 ∈ J} :=
    hJ.preimage (EuclideanSpace.proj 0).continuous
  exact (ContinuousSecondJetOn.comp (Φ.contDiff.of_le (by simp)) hu hs).compContinuousLinearMap
    hs L.toContinuousLinearMap (hJ.prod isOpen_univ)
      (fun _ hp ↦ hp.1)

/-- The original conservative residual and the coordinate covector identity
give the diagonal transport equation for the transformed original solution.
The covector identity is a statement about the flux and coordinates alone. -/
theorem invariant_transport {flux : ℝ^2 → ℝ^2} (hflux : Differentiable ℝ flux)
    (Φ : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ))
    (hcoord : ∀ i q v, fderiv ℝ (fun z ↦ Φ z i) q (fderiv ℝ flux q v) =
      characteristicSpeed flux i.rev q * fderiv ℝ (fun z ↦ Φ z i) q v)
    {u : ℝ^2 → ℝ^2} {p : ℝ × ℝ} (hu : DifferentiableAt ℝ u !₂[p.1, p.2])
    (hpde : fluxResidual flux u !₂[p.1, p.2] = 0) (i : Fin 2) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ Φ (u !₂[q.1, q.2])) p
      (1, invariantSpeed flux Φ i (Φ (u !₂[p.1, p.2]))) i = 0 := by
  let L : (ℝ × ℝ) ≃L[ℝ] ℝ^2 := (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  let w : Fin 2 → ℝ^2 → ℝ := fun j z ↦ Φ z j
  have hw (j : Fin 2) : Differentiable ℝ (w j) :=
    (contDiff_pi.mp Φ.contDiff j).differentiable (by simp)
  have hsol : IsClassicalSolutionOn flux { !₂[p.1, p.2] } u :=
    ⟨fun q hq ↦ (mem_singleton_iff.mp hq) ▸ hu, fun q _ ↦ hflux (u q),
      fun q hq ↦ (mem_singleton_iff.mp hq) ▸ hpde⟩
  have ht := hsol.riemannInvariant_transport (fun j z ↦ hw j z)
    (left := fun j z ↦ fderiv ℝ (w j.rev) z)
    (fun j z v ↦ by simpa only [Fin.rev_rev] using hcoord j.rev z v)
    (fun j z ↦ ⟨1, by simp only [Fin.rev_rev, one_smul]⟩) (mem_singleton _) i
  have hPhi := (Φ.contDiff.differentiable (by simp) (u (L p))).hasFDerivAt
  have hd := (hPhi.comp (L p) hu.hasFDerivAt).comp p L.hasFDerivAt
  have hscalar := ((hw i (u (L p))).hasFDerivAt.comp (L p) hu.hasFDerivAt)
  have hcomponent := (ContinuousLinearMap.proj i).hasFDerivAt.comp (L p)
    (hPhi.comp (L p) hu.hasFDerivAt)
  have heq := hscalar.unique hcomponent
  change (fderiv ℝ ((Φ ∘ u) ∘ L) p _ ) i = 0
  rw [hd.fderiv]
  change (fderiv ℝ Φ (u (L p))
    (fderiv ℝ u (L p) (L (1, invariantSpeed flux Φ i (Φ (u (L p))))))) i = 0
  have hL (b : ℝ) :
      L (1, b) = EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1 := by
    ext j
    fin_cases j <;> simp [L]
  rw [hL]
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change ((fderiv ℝ Φ (u (L p))).comp (fderiv ℝ u (L p))) (EuclideanSpace.single 0 1) i +
    invariantSpeed flux Φ i (Φ (u (L p))) * ((fderiv ℝ Φ (u (L p))).comp (fderiv ℝ u (L p)))
        (EuclideanSpace.single 1 1) i = 0
  have heq' (v : ℝ^2) : ((fderiv ℝ Φ (u (L p))).comp (fderiv ℝ u (L p))) v i =
        fderiv ℝ (w i ∘ u) (L p) v := by
    rw [hscalar.fderiv]
    exact congrArg (fun A : ℝ^2 →L[ℝ] ℝ ↦ A v) heq.symm
  rw [heq', heq']
  have hLp : L p = !₂[p.1, p.2] := by
    ext j
    fin_cases j <;> rfl
  simpa only [invariantSpeed, Φ.symm_apply_apply, partialDeriv, hLp] using ht

end PDE.Hyperbolic.ConservationLaw.System
