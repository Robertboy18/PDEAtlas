/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2

/-!
# Spatial H2 regularity for divergence-form weak waves

At almost every time, the wave equation rewrites the elliptic residual as
`L u = f - u_{tt}`. We apply the global elliptic solution operator
to that residual and construct the canonical essentially bounded
`H²`-valued representative of the wave trajectory.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, step 3, equations (59)-(60).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.Variational

namespace DivergenceFormWave

open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)]
variable {Omega : Set (ℝ^n)}

/--
Evans, §7.2.3: the elliptic step in Theorem 5(ii).

Assume the divergence-form weak wave identity holds almost everywhere in
time and that both `f(t)` and `u_{tt}(t)` are essentially bounded in
`L²(Omega)`. On a domain carrying the operational `C2BoundaryAtlas`, assume
uniformly elliptic `W¹,∞` principal coefficients with global `C¹` representatives.
The wave trajectory then has a canonical `L∞_t H²_x` representative. Constructing
the atlas from an ordinary geometric `C²` boundary is not part of this theorem.

The pointwise estimate retained by the theorem is

`‖u(t)‖_{H²} ≤ ‖S₂‖ (C_f + C_tt)`,

where `S₂ : L²(Omega) → H²(Omega)` is the global elliptic solution operator.
This is the operator form of Evans's estimates (59)-(60). In particular,
the constant is independent of the Galerkin dimension and of time.
-/
theorem exists_spatialH2Top_of_ae_weak_wave
    (t0 t1 : ℝ) (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (f utt : Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
    (u : Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (hu : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), ∀ v : H¹₀(Omega),
      ⟪utt t, baseCoordCLM (n := n) (Ω := Omega) v⟫_ℝ + variableCoeffForm (n := n) (Ω := Omega)
          (multiplicationCoefficientOperator (n := n) (Ω := Omega) (coefficientBase A))
          ((u : ℝ → H¹₀(Omega)) t) v =
        ⟪f t, baseCoordCLM (n := n) (Ω := Omega) v⟫_ℝ)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) (Cf Ctt : ℝ)
    (hfBound : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), ‖f t‖ ≤ Cf)
    (huttBound : ∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)), ‖utt t‖ ≤ Ctt) :
    ∃ U2 : Lp (W^{2,2}(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)),
      ((fun t ↦ lowerOrderCLM (n := n) (k := 1) (m := 2) (p := 2) (Ω := Omega) (by omega)
            ((U2 : ℝ → W^{2,2}(Omega)) t))
        =ᵐ[volume.restrict (Set.Ioc t0 t1)]
          fun t ↦ h10SubtypeL (n := n) (Ω := Omega) ((u : ℝ → H¹₀(Omega)) t)) ∧
      MemLp (fun t ↦ U2 t) (⊤ : ENNReal) (volume.restrict (Set.Ioc t0 t1)) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioc t0 t1)),
        ‖U2 t‖ ≤ ‖globalH2SolveCLM hOmega A a haRep haC1 alpha halpha hElliptic‖ * (Cf + Ctt)) := by
  let μ := volume.restrict (Set.Ioc t0 t1)
  let solve2 := globalH2SolveCLM hOmega A a haRep haC1 alpha halpha hElliptic
  let rhs : Lp (DerivLp n 2 Omega) 2 μ := f - utt
  have hU2Coe := globalH2SolveLpCLM_apply_ae μ hOmega A a haRep haC1 alpha halpha hElliptic rhs
  have hrhsBound : ∀ᵐ t ∂μ, ‖rhs t‖ ≤ Cf + Ctt := by
    filter_upwards [hfBound, huttBound, Lp.coeFn_sub f utt] with t hft hutt hsub
    rw [show rhs t = f t - utt t by simpa [rhs] using hsub]
    exact (norm_sub_le (f t) (utt t)).trans (add_le_add hft hutt)
  refine ⟨_, ?_, ((memLp_top_of_bound (Lp.aestronglyMeasurable rhs) (Cf + Ctt)
    hrhsBound).continuousLinearMap_comp solve2).ae_eq hU2Coe.symm, ?_⟩
  · filter_upwards [hU2Coe, hu, Lp.coeFn_sub f utt] with t hU2t hut hrhsCoe
    rw [hU2t]
    -- Match the normed-space instance used to construct the elliptic form.
    -- Leaving it implicit creates a second subtype-instance inference path.
    have huElliptic : @PDE.Analysis.Variational.IsWeakSolution
        (H¹₀(Omega)) inferInstance (Submodule.normedSpace (h10Submodule (n := n) (Ω := Omega)))
        (variableCoeffForm (n := n) (Ω := Omega)
          (multiplicationCoefficientOperator (n := n) (Ω := Omega) (coefficientBase A)))
        (loadFunctional (n := n) (Ω := Omega) (rhs t)) ((u : ℝ → H¹₀(Omega)) t) := by
      intro v
      have hv := hut v
      change variableCoeffForm (n := n) (Ω := Omega)
          (multiplicationCoefficientOperator (n := n) (Ω := Omega) (coefficientBase A))
          ((u : ℝ → H¹₀(Omega)) t) v = ⟪rhs t, baseCoordCLM (n := n) (Ω := Omega) v⟫_ℝ
      rw [show rhs t = f t - utt t by simpa [rhs] using hrhsCoe, inner_sub_left]
      linarith
    rw [globalH2SolveCLM_orderOne hOmega A a haRep haC1 alpha halpha hElliptic (rhs t),
      eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution hOmega A a haRep alpha halpha hElliptic
        (rhs t) _ ((isWeakSolution_iff_isWeakDivergenceSolution (n := n) (Ω := Omega)
          hOmega.toC1ExtensionAtlas.isOpen (coefficientBase A) (rhs t)
          ((u : ℝ → H¹₀(Omega)) t)).mp huElliptic)]
  · filter_upwards [hU2Coe, hrhsBound] with t hU2t hrhs
    rw [hU2t]
    exact (solve2.le_opNorm (rhs t)).trans (mul_le_mul_of_nonneg_left hrhs (norm_nonneg solve2))

end DivergenceFormWave

end Hyperbolic.Variational
