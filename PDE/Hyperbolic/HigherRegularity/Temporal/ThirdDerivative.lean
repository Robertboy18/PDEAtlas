/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.Basic

/-!
# Third weak time derivative for autonomous wave equations

For an autonomous spatial operator, differentiating the residual identity
`u_{tt} = ell - B u` identifies `u_{ttt}` with `ellDot - B u_t`. We
construct that residual as a Bochner `L²` function, prove that it is the
weak time derivative of the acceleration, and bound its norm.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 5(ii) and step 4 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Hyperbolic.Variational

open PDE.Analysis.Evolution

namespace IsGelfandWeakWaveSolution

variable
  {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {a b : ℝ}
  {T : GelfandTriple (V := V) (H := H)}
  {B : V →L[ℝ] StrongDual ℝ V}
  {ell ellDot : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {u velocityV : Lp V 2 (volume.restrict (Set.Ioc a b))}
  {velocity : Lp H 2 (volume.restrict (Set.Ioc a b))}
  {acceleration : Lp (StrongDual ℝ V) 2
    (volume.restrict (Set.Ioc a b))}
  {q0 : V} {p0 : H}

/--
Evans, §7.2.3: the `u_{ttt}` conclusion in Theorem 5(ii).

For an autonomous spatial operator, suppose the improved compactness
argument has identified an energy-valued weak derivative
`u_t = velocityV`, and suppose the forcing has weak derivative `ellDot`.
Differentiating the already-proved wave equation

`u_{tt} = ell - B u`

in distributions gives

`u_{ttt} = ellDot - B velocityV`.

The right-hand side is constructed as a Bochner `L²(a,b;V*)`
element and satisfies the quantitative bound

`‖u_{ttt}‖_{L²(V*)} ≤ ‖ellDot‖_{L²(V*)}
  + ‖B‖ ‖velocityV‖_{L²(V)}`.

Thus this theorem proves membership in `L²_t V*`; it does not merely attach
the name `u_{ttt}` to an unverified expression.
-/
theorem exists_thirdTimeDerivative_of_autonomous
    (h : IsGelfandWeakWaveSolution T (fun _ ↦ B) ell u velocity acceleration q0 p0)
    (huDerivative : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
      (Set.Ioo a b) (fun t ↦ u t) (fun t ↦ velocityV t))
    (hellDerivative : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
      (Set.Ioo a b) (fun t ↦ ell t) (fun t ↦ ellDot t)) :
    ∃ third : Lp (StrongDual ℝ V) 2 (volume.restrict (Set.Ioc a b)),
      PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
          (Set.Ioo a b) (fun t ↦ acceleration t) (fun t ↦ third t) ∧
        ((fun t ↦ third t) =ᵐ[volume.restrict (Set.Ioc a b)]
          fun t ↦ ellDot t - B (velocityV t)) ∧
        ‖third‖ ≤ ‖ellDot‖ + ‖B‖ * ‖velocityV‖ := by
  let μ := volume.restrict (Set.Ioc a b)
  let Bvelocity : Lp (StrongDual ℝ V) 2 μ := B.compLpL 2 μ velocityV
  have hthirdCoe : (fun t ↦ (ellDot - Bvelocity) t) =ᵐ[μ] fun t ↦ ellDot t - B (velocityV t) := by
    filter_upwards [Lp.coeFn_sub ellDot Bvelocity, B.coeFn_compLpL (p := 2) (μ := μ) velocityV] with
      t hsub hBv
    simpa [Bvelocity, hBv] using hsub
  have hmeasure : volume.restrict (Set.Ioo a b) ≤ μ :=
    (volume : Measure ℝ).restrict_mono_set Set.Ioo_subset_Ioc_self
  have hresidual : PDE.Analysis.Evolution.HasWeakTimeDerivativeOn (Set.Ioo a b)
      (fun t ↦ ell t - B (u t)) (fun t ↦ ellDot t - B (velocityV t)) := by
    simpa only [Function.comp_def] using hellDerivative.sub (huDerivative.map B)
  refine ⟨ellDot - Bvelocity, hresidual.congr_ae_restrict measurableSet_Ioo
      ((h.acceleration_eq_residualAE.filter_mono (ae_mono hmeasure)).mono fun t ht ↦ ht.symm)
      (hthirdCoe.filter_mono (ae_mono hmeasure)).symm, hthirdCoe,
    (norm_sub_le ellDot Bvelocity).trans ?_⟩
  gcongr
  exact ((B.compLpL 2 μ).le_opNorm velocityV).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compLpL_le B) (norm_nonneg velocityV))

end IsGelfandWeakWaveSolution

end Hyperbolic.Variational
