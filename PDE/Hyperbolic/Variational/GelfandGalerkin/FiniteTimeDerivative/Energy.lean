/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.Forcing
public import PDE.Analysis.Evolution.Galerkin.Gelfand.VectorField
public import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Basic
public import PDE.Hyperbolic.Variational.SecondOrder.Basic
import PDE.Hyperbolic.Variational.GelfandGalerkin.Energy.Integral

/-!
# Energy bounds for finite differentiated Galerkin families

Uniform energy estimates for a Galerkin trajectory of the autonomous abstract wave equation
`q'' + (A + R) q = ell(t)` on a Gelfand triple `V ↪ H ↪ V'`, and for all of its finite time
derivatives at once. The principal form `A` is symmetric and coercive, `c ‖q‖² ≤ A(q, q)`, the
lower-order form satisfies the mixed bound `|R(q, p)| ≤ L_R ‖q‖_V ‖J p‖_H`, and the forcing is
pivot-valued, `ell(s) = J* f(s)` with `f : ℝ → H` almost everywhere. With
`E(t) = ½ ‖J q'‖_H² + ½ A(q, q)` (`gelfandWaveEnergy`), the estimate reads

`E(t) ≤ (E(a) + G) exp((2 + L_R² / c)(t - a))`,

where `G` bounds the prefix integrals `∫ₐᵗ ½ ‖f‖_H²`. The proof feeds the Cauchy-Schwarz and
Young bounds on the work terms into `GelfandGalerkin.gelfandWaveEnergy_le_exp`. Both the
exponent and the budget are independent of the trial-space dimension, and, since a
time-differentiated trajectory solves the same equation with differentiated forcing, of the
derivative level as well. This is the mechanism of the regularity theorem for second-order
hyperbolic equations in Evans, §7.2.3.

## Main results

* `gelfandWaveEnergy_le_exp_of_pivot_forcing`: the estimate for a single trajectory.
* `exists_uniform_forcingBudget_finite`: a finite family of square-integrable forcings has one
  common prefix budget `G ≥ 0`, namely the sum of the full-interval integrals.
* `finiteTimeDerivativeFamily_gelfandWaveEnergy_le_exp`: the estimate at every level of a
  finite differentiated family, with the same `G`, `c`, `L_R`.
* `SobolevTimeJet.exists_dirichletLoadForcingChain_with_uniformBudget`: for the Dirichlet
  problem on an open set, a Sobolev forcing jet yields a coherent chain of differentiated dual
  forcings on `H¹₀`, their pivot realizations, and a common budget, in the form the
  previous theorem needs.

## Implementation notes

The exponent `2 + L_R² / c` is the coefficient in the pointwise work bound
`gelfandWaveEnergyWork_le` specialized to a constant principal part (`L_A = 0`): Young's
inequality gives `|ell(q')| ≤ ½ ‖f‖² + ½ ‖J q'‖²` and
`|R(q, q')| ≤ ½ (L_R² / c) A(q, q) + ½ ‖J q'‖²`, and each right-hand side is controlled by `E`.
The forcing hypothesis is stated for a dual forcing `ell` agreeing almost everywhere with
`J* f`, so `Lp` representatives of the data can be used directly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, Theorem 2, and §7.2.3, proof of Theorem 5, step 2,
  equations (54)-(55).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open AbsolutelyContinuousOnInterval MeasureTheory Set
open scoped Topology

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Evans's autonomous wave-energy estimate for one Galerkin trajectory with
pivot-valued forcing.

The dual forcing need only agree almost everywhere with the pivot embedding.
The forcing contribution is controlled by a prefix budget for
`‖f‖_H^2 / 2`; coercivity and the `V x H` lower-order estimate give the
dimension-independent exponential coefficient.
-/
theorem gelfandWaveEnergy_le_exp_of_pivot_forcing (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] [CompleteSpace S] (A R : V →L[ℝ] StrongDual ℝ V)
    (ell : ℝ → StrongDual ℝ V) (f : ℝ → H) {a b : ℝ} {q₀ p₀ : S}
    (U : SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T S (A + R))
      (gelfandGalerkinForcing T S ell) a b q₀ p₀)
    (hab : a ≤ b) (hellPivot : ∀ᵐ s ∂volume.restrict (Set.Ioc a b), ell s = T.pivotToDual (f s))
    (hfSqIntegrable : IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) * ‖f s‖ ^ 2) volume a b) (G c LR : ℝ)
    (hforcingBudget : ∀ t ∈ Set.Icc a b, (∫ s in a..t, (1 / 2 : ℝ) * ‖f s‖ ^ 2) ≤ G) (hc : 0 < c)
    (hA_symmetric : ∀ x y : V, A x y = A y x) (hcoercive : ∀ q : V, c * ‖q‖ ^ 2 ≤ A q q)
    (hRbound : ∀ q p : V, |R q p| ≤ LR * ‖q‖ * ‖T.inclusion p‖) :
    ∀ t ∈ Set.Icc a b, gelfandWaveEnergy T S (fun _ ↦ A) U.displacement U.velocity t ≤
      (gelfandWaveEnergy T S (fun _ ↦ A) U.displacement U.velocity a + G) *
      Real.exp ((2 + LR ^ 2 / c) * (t - a)) := by
  have hAAC : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ A) a b :=
    (LipschitzWith.const' (K := 0) A).lipschitzOnWith.absolutelyContinuousOnInterval
  refine GelfandGalerkin.gelfandWaveEnergy_le_exp T S (fun _ ↦ A) (fun _ ↦ R) ell U hab hAAC
    (.of_forall fun s ↦ hasDerivAt_const s A) (fun _ _ x y ↦ hA_symmetric x y) _ G
    (by positivity) fun t ht ↦ ?_
  simp only [zero_apply, mul_zero, add_zero]
  let E := gelfandWaveEnergy T S (fun _ ↦ A) U.displacement U.velocity
  have hE : IntervalIntegrable E volume a t :=
    ((GelfandGalerkin.continuousOn_gelfandWaveEnergy T S _ U hab hAAC).mono
      (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hf := hfSqIntegrable.mono_set (uIcc_subset_uIcc_left (by rwa [uIcc_of_le hab]))
  rw [intervalIntegral.integral_congr_ae_restrict (g := fun s ↦
      T.pivotToDual (f s) (U.velocity s : V) - R (U.displacement s : V) (U.velocity s : V))
    (by
      rw [uIoc_of_le ht.1]
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right ht.2)
        hellPivot] with s hs
      rw [hs])]
  by_cases hw : IntervalIntegrable (fun s ↦
      T.pivotToDual (f s) (U.velocity s : V) - R (U.displacement s : V) (U.velocity s : V))
    volume a t
  · calc _ ≤ ∫ s in a..t, (2 + LR ^ 2 / c) * E s + (1 / 2 : ℝ) * ‖f s‖ ^ 2 :=
          intervalIntegral.integral_mono_on ht.1 hw ((hE.const_mul _).add hf) fun s _ ↦ by
            simpa only [E, gelfandWaveEnergy, zero_apply, mul_zero, add_zero] using
              Hyperbolic.Variational.gelfandWaveEnergyWork_le T A R 0 (U.displacement s : V)
                (U.velocity s : V) (f s) c LR 0 hc le_rfl (hcoercive _) (hRbound _ _) (by simp)
      _ ≤ _ := by
        rw [intervalIntegral.integral_add (hE.const_mul _) hf, intervalIntegral.integral_const_mul]
        linarith [hforcingBudget t ht]
  · rw [intervalIntegral.integral_undef hw]
    have hG : 0 ≤ G := by simpa using hforcingBudget a ⟨le_rfl, hab⟩
    have hEnonneg : 0 ≤ ∫ s in a..t, E s := intervalIntegral.integral_nonneg ht.1 fun s _ ↦
      add_nonneg (by positivity) (mul_nonneg (by norm_num)
        ((by positivity : 0 ≤ c * ‖(U.displacement s : V)‖ ^ 2).trans (hcoercive _)))
    positivity

/--
A finite family of square-integrable pivot forcings has one common prefix
budget.  The budget is the sum of the full-interval quadratic forcing
integrals, so it is independent of both time and the derivative index.
-/
theorem exists_uniform_forcingBudget_finite {E : Type*} [NormedAddCommGroup E] {m : ℕ}
    (forcing : Fin (m + 1) → ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hforcingSqIntegrable : ∀ r : Fin (m + 1),
      IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2) volume a b) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      (∫ s in a..t, (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2) ≤ G := by
  have hfull (r : Fin (m + 1)) : 0 ≤ ∫ s in a..b, (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun s _ ↦ by positivity
  refine ⟨_, Finset.sum_nonneg fun r _ ↦ hfull r, fun r t ht ↦
    (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (.of_forall fun s ↦ by positivity)
      (hforcingSqIntegrable r)).trans
    (Finset.single_le_sum (fun i _ ↦ hfull i) (Finset.mem_univ r))⟩

/--
Evans's autonomous energy estimate simultaneously at every level of a
finite differentiated Galerkin family.

The same forcing budget, coercivity constant, and lower-order bound apply at
all levels, so the exponential coefficient is independent of both the
Galerkin dimension and the derivative index.
-/
theorem finiteTimeDerivativeFamily_gelfandWaveEnergy_le_exp
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V)
    [FiniteDimensional ℝ S] [CompleteSpace S]
    (A R : V →L[ℝ] StrongDual ℝ V) {m : ℕ} (dualForcing : Fin (m + 1) → ℝ → StrongDual ℝ V)
    (forcing : Fin (m + 1) → ℝ → H) {a b : ℝ} (q0 p0 : Fin (m + 1) → S)
    (U : (r : Fin (m + 1)) → SecondOrderSolutionOn
      (fun _ ↦ gelfandGalerkinOperator T S (A + R))
      (gelfandGalerkinForcing T S (dualForcing r)) a b (q0 r) (p0 r))
    (hab : a ≤ b)
    (hdualForcing : ∀ r : Fin (m + 1),
      ∀ᵐ s ∂volume.restrict (Set.Ioc a b), dualForcing r s = T.pivotToDual (forcing r s))
    (hforcingSqIntegrable : ∀ r : Fin (m + 1),
      IntervalIntegrable (fun s ↦ (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2) volume a b)
    (G c LR : ℝ)
    (hforcingBudget : ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      (∫ s in a..t, (1 / 2 : ℝ) * ‖forcing r s‖ ^ 2) ≤ G)
    (hc : 0 < c) (hA_symmetric : ∀ x y : V, A x y = A y x)
    (hcoercive : ∀ q : V, c * ‖q‖ ^ 2 ≤ A q q)
    (hRbound : ∀ q p : V, |R q p| ≤ LR * ‖q‖ * ‖T.inclusion p‖) :
    ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc a b,
      gelfandWaveEnergy T S (fun _ ↦ A) (U r).displacement (U r).velocity t ≤
        (gelfandWaveEnergy T S (fun _ ↦ A) (U r).displacement (U r).velocity a + G) *
          Real.exp ((2 + LR ^ 2 / c) * (t - a)) := fun r ↦
  gelfandWaveEnergy_le_exp_of_pivot_forcing T S A R (dualForcing r) (forcing r) (U r) hab
    (hdualForcing r) (hforcingSqIntegrable r) G c LR (hforcingBudget r) hc hA_symmetric hcoercive
    hRbound

end Hyperbolic.Variational.GelfandGalerkin

namespace Hyperbolic.HigherRegularity

open SobolevSpace
open SobolevSpace.GraphSpace

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
An Evans Sobolev forcing jet supplies one coherent differentiated dual
forcing chain and one common quadratic forcing budget.

The pivot-valued family in the energy estimate is the base coordinate of
each iterated jet tail.  Thus the returned pivot realization, integrability,
and prefix budget are directly the forcing hypotheses of
`finiteTimeDerivativeFamily_gelfandWaveEnergy_le_exp`.
-/
theorem SobolevTimeJet.exists_dirichletLoadForcingChain_with_uniformBudget
    (F : SobolevTimeJet n m Omega t0 t1) (hOmegaOpen : IsOpen Omega) (ht : t0 < t1) :
    ∃ dualForcing : Fin (m + 1) → ℝ → StrongDual ℝ (H¹₀(Omega)), ∃ G : ℝ,
      (∀ r : Fin (m + 1),
        (dirichletLoadTimeLp hOmegaOpen (F.iteratedTimeDerivative r).head :
            ℝ → StrongDual ℝ (H¹₀(Omega)))
          =ᵐ[volume.restrict (Set.Ioc t0 t1)] dualForcing r) ∧
      (∀ r : Fin m,
        AbsolutelyContinuousOnInterval (dualForcing r.succ) t0 t1 ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
          HasDerivAt (dualForcing r.succ) (dualForcing r.castSucc t) t) ∧
      (∀ r : Fin (m + 1), ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
        dualForcing r t = (h10L2GelfandTriple hOmegaOpen).pivotToDual
          (baseCoordinateTimeLp (F.iteratedTimeDerivative r).head t)) ∧
      (∀ r : Fin (m + 1), IntervalIntegrable (fun t ↦
          (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (F.iteratedTimeDerivative r).head t‖ ^ 2)
        volume t0 t1) ∧
      0 ≤ G ∧
      ∀ r : Fin (m + 1), ∀ t ∈ Set.Icc t0 t1,
        (∫ s in t0..t,
          (1 / 2 : ℝ) * ‖baseCoordinateTimeLp (F.iteratedTimeDerivative r).head s‖ ^ 2) ≤ G := by
  obtain ⟨dualForcing, hrepresents, hadjacent⟩ := F.exists_dirichletLoadForcingChain hOmegaOpen ht
  have hsquareIntegrable := F.intervalIntegrable_norm_sq_baseCoordinateTimeLp ht.le
  obtain ⟨G, hG, hbudget⟩ :=
    Hyperbolic.Variational.GelfandGalerkin.exists_uniform_forcingBudget_finite
      (fun r t ↦ baseCoordinateTimeLp (F.iteratedTimeDerivative r).head t) ht.le hsquareIntegrable
  exact ⟨dualForcing, G, hrepresents, hadjacent,
    F.forcing_eq_pivotToDual_baseCoordinateTimeLp hOmegaOpen dualForcing hrepresents,
    hsquareIntegrable, hG, hbudget⟩

end Hyperbolic.HigherRegularity
