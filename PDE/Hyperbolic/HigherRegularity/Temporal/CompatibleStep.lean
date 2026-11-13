/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Temporal.FiniteChain
public import PDE.Hyperbolic.HigherRegularity.Compatibility.BoundaryTraces
public import PDE.Hyperbolic.HigherRegularity.Data.TraceEstimate
public import PDE.Elliptic.Variational.DivergenceSolution

/-!
# Integrating the differentiated problem with computed initial data

The forcing jet supplies its initial trace and fundamental theorem.
The compatibility recurrence then fixes the acceleration needed to integrate
a differentiated weak wave. The resulting wave retains the prescribed
displacement and velocity at the initial endpoint.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The dual forcing satisfies the fundamental theorem with its
canonical initial trace, including the initial endpoint. -/
theorem SobolevTimeJet.dirichletLoad_eq_trace_add_integral (F : SobolevTimeJet n (m + 1) Ω a b)
    (hopen : IsOpen Ω) (hab : a < b) (traces : InitialTraceData (F := F)) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), dirichletLoadTimeLp hopen F.head t =
      loadFunctional (wkpBaseCoordinateCLM traces.head) + ∫ s in a..t,
      dirichletLoadTimeLp hopen F.timeDerivative.head s := by
  obtain ⟨R, _, hrep, hRa, hFTC, _⟩ := traces.exists_head_representative_norm_le hab
  let K : W^{m,2}(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)) :=
    (h10L2GelfandTriple hopen).pivotToDual.comp wkpBaseCoordinateCLM
  have hd : (fun s ↦ K (F.timeDerivative.head s)) =ᵐ[volume.restrict (Ioc a b)]
      dirichletLoadTimeLp hopen F.timeDerivative.head :=
    (dirichletLoadTimeLp_apply_ae hopen F.timeDerivative.head).symm
  filter_upwards [dirichletLoadTimeLp_apply_ae hopen F.head, hrep,
    ae_restrict_mem measurableSet_Ioc] with t ht hr htI
  have hint := (intervalIntegrable_coeFn_L2_restrict_Ioc F.timeDerivative.head
    hab.le).mono_set (uIcc_subset_uIcc_left (Icc_subset_uIcc (Ioc_subset_Icc_self htI)))
  have hInt : K (∫ s in a..t, F.timeDerivative.head s) =
      ∫ s in a..t, dirichletLoadTimeLp hopen F.timeDerivative.head s := by
    rw [← K.intervalIntegral_comp_comm hint]
    rw [intervalIntegral.integral_of_le htI.1.le, intervalIntegral.integral_of_le htI.1.le]
    exact integral_congr_ae (hd.filter_mono
      (ae_mono (volume.restrict_mono_set (Ioc_subset_Ioc_right htI.2))))
  have hRt := congrArg K (hFTC a ⟨le_rfl, hab.le⟩ t (Ioc_subset_Icc_self htI))
  rw [hRa, map_add, hInt] at hRt
  rw [ht]
  change K (lowerOrderCLM (Nat.le_succ m) (F.head t)) = _
  rw [hr]
  exact hRt

/-- One adjacent pair of the generic finite chain, with compatibility data
computed from the forcing trace and the full spatial operator. -/
theorem WaveProblemData.exists_integrated_compatible_wave (D : WaveProblemData n (m + 1) Ω a b)
    (hopen : IsOpen Ω) (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (L : ∀ r, W^{(r + 2),2}(Ω) →L[ℝ] W^{r,2}(Ω))
    (hL : ∀ (G : W^{(m + 2),2}(Ω)) (g : H¹₀(Ω)), wkpBaseCoordinateCLM G = baseCoordCLM g → A g =
      loadFunctional (wkpBaseCoordinateCLM (L m G)))
    (hD : D.HasCompatibleBoundaryTraces L) {du : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))}
    {dv : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))}
    {dw : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))}
    (hdu : Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen) (fun _ ↦ A)
      (dirichletLoadTimeLp hopen D.forcing.timeDerivative.head) du dv dw
      (WaveProblemData.initialPosition hD.2)
      (wkpBaseCoordinateCLM (D.forcingTraces.head - L m D.displacement))) :
    ∃ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ A) (dirichletLoadTimeLp hopen D.forcing.head) u
        ((h10L2GelfandTriple hopen).inclusion.compLpL 2 (volume.restrict (Ioc a b)) du)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) dv)
        (WaveProblemData.initialPosition hD) (wkpBaseCoordinateCLM D.velocity) ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b),
        u t = WaveProblemData.initialPosition hD + ∫ s in a..t, du s := by
  let T := h10L2GelfandTriple hopen
  let q : Fin 2 → H¹₀(Ω) :=
    ![WaveProblemData.initialPosition hD.2, WaveProblemData.initialPosition hD]
  let p : Fin 2 → DerivLp n 2 Ω :=
    ![wkpBaseCoordinateCLM (D.forcingTraces.head - L m D.displacement),
      wkpBaseCoordinateCLM D.velocity]
  let ell : Fin 2 → Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)) :=
    ![dirichletLoadTimeLp hopen D.forcing.timeDerivative.head,
      dirichletLoadTimeLp hopen D.forcing.head]
  let ell₀ : Fin 1 → StrongDual ℝ (H¹₀(Ω)) :=
    fun _ ↦ loadFunctional (wkpBaseCoordinateCLM D.forcingTraces.head)
  have hforcing : ∀ r : Fin 1, ∀ᵐ t ∂volume.restrict (Ioc a b),
      ell r.succ t = ell₀ r + ∫ s in a..t, ell r.castSucc s := by
    intro r
    fin_cases r
    exact D.forcing.dirichletLoad_eq_trace_add_integral hopen D.time_lt D.forcingTraces
  have hposition : ∀ r : Fin 1, p r.succ = T.inclusion (q r.castSucc) := by
    intro r
    fin_cases r
    rfl
  have hcompat : ∀ r : Fin 1, T.pivotToDual (p r.castSucc) + A (q r.succ) = ell₀ r := by
    intro r
    fin_cases r
    change loadFunctional (wkpBaseCoordinateCLM (D.forcingTraces.head - L m D.displacement)) +
        A (WaveProblemData.initialPosition hD) = _
    rw [hL D.displacement _ rfl, map_sub, loadFunctional_sub]
    exact sub_add_cancel _ _
  obtain ⟨u, v, w, hu, hv, _, hwave, hvelocity, hacceleration, _, hprimitive⟩ :=
    Hyperbolic.Variational.exists_finite_weakWaveChain
      ell ell₀ q p hforcing hposition hcompat du dv dw hdu
  have h1 : (0 : Fin 1).succ = (1 : Fin 2) := by decide
  have hv1 := hvelocity 0
  have hw1 := hacceleration 0
  rw [h1, Fin.castSucc_zero, hu] at hv1
  rw [h1, Fin.castSucc_zero, hv] at hw1
  refine ⟨u 1, ?_, ?_⟩
  · have h := hwave 1
    rwa [hv1, hw1] at h
  · have h := hprimitive 0
    rwa [h1, Fin.castSucc_zero, hu, show q 1 = WaveProblemData.initialPosition hD from rfl] at h

end Hyperbolic.HigherRegularity
