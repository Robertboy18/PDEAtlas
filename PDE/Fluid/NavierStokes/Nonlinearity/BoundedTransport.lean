/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Sobolev
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Linearized transport with bounded coefficients

Actual `L∞` multiplication and weak derivative coordinates give a bounded
map from vector `H¹` to vector `H⁰`. The coefficient norm bound is a finite
sum, without any smallness assumption. Composition with the actual Leray
projection retains the bound and gives a solenoidal physical output.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open scoped ENNReal Sobolev

namespace NavierStokes.BoundedTransport

variable {n : ℕ}

/-- The sum of all coefficient norms gives a coarse finite transport bound. -/
def coefficientBound (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) : ℝ :=
  ∑ j : Fin n, ∑ i : Fin n, (‖b i‖ + ‖c j i‖)

theorem coefficientBound_nonneg (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    0 ≤ coefficientBound b c :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity

/-- One component of bounded-coefficient transport, using the weak derivative
and base coordinates of the input Sobolev graphs. -/
def scalarTransport (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (j : Fin n) :
    VectorH n 1 →L[ℝ] DerivLp n 2 Set.univ :=
  ∑ i : Fin n,
    ((mulLpLeft (b i)).comp
        ((wkpCoordinateCLM (singleDerivIndex n i)).comp (PiLp.proj 2 _ j)) +
      (mulLpLeft (c j i)).comp
        (wkpBaseCoordinateCLM.comp (PiLp.proj 2 _ i)))

theorem scalarTransport_apply (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (j : Fin n) (v : VectorH n 1) :
    scalarTransport b c j v = ∑ i : Fin n,
      (mulLpLeft (b i) (wkpCoordinateCLM (singleDerivIndex n i) (v j)) +
        mulLpLeft (c j i) (wkpBaseCoordinateCLM (v i))) := by
  simp only [scalarTransport, sum_apply, add_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply]

/-- The component estimate uses only coefficient norms and coordinate contractions. -/
theorem norm_scalarTransport_le (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (j : Fin n) (v : VectorH n 1) :
    ‖scalarTransport b c j v‖ ≤
      (∑ i : Fin n, (‖b i‖ + ‖c j i‖)) * ‖v‖ := by
  rw [scalarTransport_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖mulLpLeft (b i) (wkpCoordinateCLM (singleDerivIndex n i) (v j))‖ +
        ‖mulLpLeft (c j i) (wkpBaseCoordinateCLM (v i))‖ := norm_add_le _ _
    _ ≤ ‖b i‖ * ‖v‖ + ‖c j i‖ * ‖v‖ := by
      apply add_le_add
      · exact (norm_mulLpLeft_apply_le _ _).trans
          (mul_le_mul_of_nonneg_left
            ((wkpCoordinateCLM_norm_le _ _).trans (PiLp.norm_apply_le v j))
            (norm_nonneg _))
      · exact (norm_mulLpLeft_apply_le _ _).trans
          (mul_le_mul_of_nonneg_left
            ((wkpBaseCoordinateCLM_norm_le _).trans (PiLp.norm_apply_le v i))
            (norm_nonneg _))
    _ = _ := (add_mul _ _ _).symm

/-- The finite vector transport operator takes `H¹` inputs to actual `H⁰` graphs. -/
def transport (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    VectorH n 1 →L[ℝ] VectorH n 0 :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin n ↦ W^{0,2}(ℝ^n))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun j ↦
        (lpEquivZeroOrder (n := n) (p := 2)
          (Ω := Set.univ)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (scalarTransport b c j))

/-- The order-zero lift retains the computed scalar `L²` coordinate. -/
theorem transport_base (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (v : VectorH n 1) (j : Fin n) :
    wkpBaseCoordinateCLM (transport b c v j) = scalarTransport b c j v :=
  rfl

theorem norm_transport_apply_le (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (v : VectorH n 1) :
    ‖transport b c v‖ ≤ coefficientBound b c * ‖v‖ := by
  apply (PiLp.norm_le_sum_norm _).trans
  unfold coefficientBound
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  change ‖lpEquivZeroOrder (scalarTransport b c j v)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_scalarTransport_le b c j v

/-- A finite coefficient sum bounds the operator norm. -/
theorem norm_transport_le (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    ‖transport b c‖ ≤ coefficientBound b c :=
  ContinuousLinearMap.opNorm_le_bound _ (coefficientBound_nonneg b c)
    (norm_transport_apply_le b c)

/-- Component representatives agree with the literal weak transport formula. -/
theorem transport_base_ae (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (v : VectorH n 1) (j : Fin n) :
    (wkpBaseCoordinateCLM (transport b c v j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ] fun x ↦ ∑ i : Fin n,
        (b i x * wkpCoordinateCLM (singleDerivIndex n i) (v j) x +
          c j i x * wkpBaseCoordinateCLM (v i) x) := by
  rw [transport_base, scalarTransport_apply]
  let f (i : Fin n) :=
    mulLpLeft (b i) (wkpCoordinateCLM (singleDerivIndex n i) (v j))
  let g (i : Fin n) := mulLpLeft (c j i) (wkpBaseCoordinateCLM (v i))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ f i + g i),
    ae_all_iff.mpr (fun i ↦ Lp.coeFn_add (f i) (g i)),
    ae_all_iff.mpr (fun i ↦ mulLpLeft_apply_ae (b i)
      (wkpCoordinateCLM (singleDerivIndex n i) (v j))),
    ae_all_iff.mpr (fun i ↦ mulLpLeft_apply_ae (c j i)
      (wkpBaseCoordinateCLM (v i)))] with x hsum hadd hb hc
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact (hadd i).trans (congrArg₂ (· + ·) (hb i) (hc i))

/-- Pressure elimination uses the actual whole-space Leray projection. -/
def projectedTransport (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    VectorH n 1 →L[ℝ] VectorH n 0 :=
  (leraySobolev n 0).comp (transport b c)

theorem norm_projectedTransport_apply_le (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (v : VectorH n 1) :
    ‖projectedTransport b c v‖ ≤ coefficientBound b c * ‖v‖ :=
  (norm_leraySobolev_le _).trans (norm_transport_apply_le b c v)

theorem norm_projectedTransport_le (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) :
    ‖projectedTransport b c‖ ≤ coefficientBound b c :=
  ContinuousLinearMap.opNorm_le_bound _ (coefficientBound_nonneg b c)
    (norm_projectedTransport_apply_le b c)

/-- The physical output is distributionally divergence free. -/
theorem projectedTransport_base_mem_solenoidal
    (b : Fin n → DerivLp n ∞ Set.univ)
    (c : Fin n → Fin n → DerivLp n ∞ Set.univ) (v : VectorH n 1) :
    l2SobolevRow (baseIndex n 0) (projectedTransport b c v) ∈ l2Solenoidal n := by
  change l2SobolevRow (baseIndex n 0) (leraySobolev n 0 (transport b c v)) ∈ _
  rw [l2SobolevRow_leraySobolev]
  exact lerayProjection_mem n _

end NavierStokes.BoundedTransport
