/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Solution.Coordinates
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple
public import PDE.Analysis.Evolution.Gelfand.DifferentiatedEquation
import PDE.Analysis.Evolution.Time.WeakDerivative.L2Representative

/-!
# The weak equation and initial trace of the velocity

The original strong transport-diffusion solution determines a dual equation.
Time differentiation and Lions–Magenes then produce its continuous L² velocity,
with the initial trace fixed by the original equation and forcing trace.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev Laplacian

private theorem absolutelyContinuous_of_continuous_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (hab : a < b) {C dC : ℝ → X}
    (hdC : ContinuousOn dC (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t) :
    AbsolutelyContinuousOnInterval C a b := by
  have hCdiff : ContDiffOn ℝ 1 C (Icc a b) := by
    apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)).mpr
    refine ⟨fun t ht ↦ (hderiv t ht).differentiableWithinAt, ?_⟩
    apply hdC.congr
    intro t ht
    exact (hderiv t ht).derivWithin (uniqueDiffOn_Icc hab t ht)
  apply ContDiffOn.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hab.le] using hCdiff

private theorem weakTimeDerivative_compLpL
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {a b : ℝ} (L : X →L[ℝ] Y)
    {F : Lp X 2 (volume.restrict (Ioc a b))}
    {dF : Lp Y 2 (volume.restrict (Ioc a b))}
    (hF : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ L (F t)) dF) :
    HasWeakTimeDerivativeOn (Ioo a b) (L.compLpL 2 (volume.restrict (Ioc a b)) F) dF := by
  apply hF.congr_ae_restrict measurableSet_Ioo
  · rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact (L.coeFn_compLpL F).symm
  · rfl

private theorem exists_continuous_compLpL_trace
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {a b : ℝ} (hab : a < b) (L : X →L[ℝ] Y)
    {F : Lp X 2 (volume.restrict (Ioc a b))}
    {dF : Lp Y 2 (volume.restrict (Ioc a b))}
    (hF : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ L (F t)) dF) :
    HasWeakTimeDerivativeOn (Ioo a b) (L.compLpL 2 (volume.restrict (Ioc a b)) F) dF ∧
      ∃ Fc : ℝ → Y, Continuous Fc ∧
        (L.compLpL 2 (volume.restrict (Ioc a b)) F : ℝ → Y)
          =ᵐ[volume.restrict (Ioc a b)] Fc ∧
        ∀ t ∈ Icc a b, ‖Fc t‖ ≤ (((b - a)⁻¹ + 1) * max 1 (b - a)) *
          (‖L.compLpL 2 (volume.restrict (Ioc a b)) F‖ + ‖dF‖) := by
  have hFH := weakTimeDerivative_compLpL L hF
  obtain ⟨Fc, hFc, hFcAE, _, hFcBound⟩ :=
    hFH.exists_continuous_L2_representative_norm_le hab
  exact ⟨hFH, Fc, hFc, hFcAE, hFcBound⟩

private theorem ae_hasDerivAt_of_hasDerivWithinAt_Icc
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} {C dC : ℝ → X}
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt C (dC t) t := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact (hderiv t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

namespace PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution

variable {n m : ℕ} {ε a b : ℝ}

attribute [local instance] coordinateProductNormedSpace

local notation "EnergySpace" => PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))
local notation "StateSpace" => PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))
local notation "PivotSpace" => PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)
local notation "T" => vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ

variable {B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ}
  {f : Fin m → ℝ × ℝ^n → ℝ}
  {q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}
  {U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
    (volume.restrict (Ioc a b))}
  {z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))}

open scoped SobolevSpace.WholeSpaceHilbert

/-- The original strong equation holds in the canonical H¹ dual space.
The transport map is identified with the matrix-gradient contraction. -/
theorem dual_equation
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hB : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Lp EnergySpace 2 (volume.restrict (Ioc a b)))
    (hf : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM ((F : ℝ → EnergySpace) t p) x = f p (t, x))
    (C : ℝ → EnergySpace →L[ℝ] PivotSpace)
    (hC : ∀ t ∈ Icc a b, ∀ v : EnergySpace, ∀ p,
      C t v p = vectorTransportCLM
        (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun q ↦ v q) p) :
    ∀ᵐ t ∂(volume.restrict (Ioc a b)), (T).energyToDual ((G : ℝ → EnergySpace) t) =
      ε • vectorWeakLaplacianCLM
        (vectorLowerOrderCLM (by decide : 1 ≤ 3) ((U : ℝ → StateSpace) t)) +
        (T).pivotToDual
          (C t (vectorLowerOrderCLM (by decide : 1 ≤ 3) ((U : ℝ → StateSpace) t)) +
            (T).inclusion ((F : ℝ → EnergySpace) t)) := by
  filter_upwards [h.native_equation A hB (fun p t ↦ (F : ℝ → EnergySpace) t p) hf,
    ae_restrict_mem measurableSet_Ioc] with t ht htime
  let U₂ : PiLp 2 (fun _ : Fin m ↦ W^{2,2}(ℝ^n)) :=
    vectorLowerOrderCLM (by decide : 2 ≤ 3) ((U : ℝ → StateSpace) t)
  let u : EnergySpace :=
    vectorLowerOrderCLM (by decide : 1 ≤ 3) ((U : ℝ → StateSpace) t)
  have hlow : vectorLowerOrderCLM (by decide : 1 ≤ 2) U₂ = u := by
    apply PiLp.ext
    intro p
    simp only [vectorLowerOrderCLM_apply, U₂, u, lowerOrderCLM_trans_apply]
  have hLap : (vectorWeakLaplacianCLM (n := n) (m := m)) u =
      (T).pivotToDual (WithLp.toLp 2 (fun p ↦ Δ (U₂ p))) := by
    rw [← hlow]
    exact vectorWeakLaplacianCLM_lowerOrder_univ U₂
  have hEq : (T).inclusion ((G : ℝ → EnergySpace) t) =
      ε • WithLp.toLp 2 (fun p ↦ Δ (U₂ p)) + (C t u + (T).inclusion ((F : ℝ → EnergySpace) t)) := by
    apply PiLp.ext
    intro p
    have hp := congrArg wkpBaseCoordinateCLM (ht p)
    simp only [map_add, map_smul, higherOrderLaplacianCLM_base,
      vectorTransportH1CLM_base, lowerOrderCLM_trans_apply] at hp
    change wkpBaseCoordinateCLM ((G : ℝ → EnergySpace) t p) = _
    simp only [PiLp.add_apply, PiLp.smul_apply,
      vectorHOneLTwoGelfandTriple_inclusion_apply]
    rw [hC t (Ioc_subset_Icc_self htime) u p]
    exact hp.trans (by simp only [U₂, u, vectorLowerOrderCLM_apply]; abel)
  change (T).pivotToDual ((T).inclusion ((G : ℝ → EnergySpace) t)) = _
  rw [hEq, map_add, map_smul, ← hLap]

private theorem exists_vector_velocityEvolution
    (hab : a < b)
    {u v : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
      (volume.restrict (Ioc a b))}
    (hu : HasWeakTimeDerivativeOn (Ioo a b) u v)
    {F dF : Lp PivotSpace 2 (volume.restrict (Ioc a b))}
    (hF : HasWeakTimeDerivativeOn (Ioo a b) F dF)
    {C dC : ℝ → EnergySpace →L[ℝ] PivotSpace}
    (hCAC : AbsolutelyContinuousOnInterval C a b)
    (hdC : ContinuousOn dC (Icc a b))
    (hCderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt C (dC t) t)
    (heq : ∀ᵐ t ∂volume.restrict (Ioc a b), (T).energyToDual (v t) =
      (ε • vectorWeakLaplacianCLM) (u t) + (T).pivotToDual (C t (u t) + F t))
    (hz : ContinuousOn z (Icc a b)) (hzu : z =ᵐ[volume.restrict (Ioc a b)] u)
    {Fc : ℝ → PivotSpace} (hFc : ContinuousOn Fc (Icc a b))
    (hFcF : Fc =ᵐ[volume.restrict (Ioc a b)] F) (hza : z a = q) :
    ∃ (g : Lp (StrongDual ℝ EnergySpace) 2 (volume.restrict (Ioc a b)))
      (E : ContinuousPivotEvolutionOn T (fun t ↦ v t) (fun t ↦ g t) a b),
      ((fun t ↦ g t) =ᵐ[volume.restrict (Ioc a b)] fun t ↦
        ε • vectorWeakLaplacianCLM (v t) +
          (T).pivotToDual (dC t (z t) + C t (v t) + dF t)) ∧
      (T).pivotToDual (E.representative a) = ε • vectorWeakLaplacianCLM q +
        (T).pivotToDual (C a q + Fc a) := by
  let : MeasurableSpace EnergySpace := borel EnergySpace
  let : BorelSpace EnergySpace := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ EnergySpace) := borel (StrongDual ℝ EnergySpace)
  let : BorelSpace (StrongDual ℝ EnergySpace) := ⟨rfl⟩
  obtain ⟨g, E, hg, htrace⟩ :=
    exists_continuousPivotEvolutionOn_of_differentiated_equation
      (V := EnergySpace) (H := PivotSpace) T hab hu hF
      (ε • vectorWeakLaplacianCLM) hCAC hdC hCderiv heq hz hzu hFc hFcF
  refine ⟨g, E, ?_, ?_⟩
  · filter_upwards [hg, hzu] with t ht hzt
    simpa only [smul_apply, ← hzt] using ht
  · have ht := htrace a ⟨le_rfl, hab.le⟩
    rw [hza] at ht
    exact ht

/-- The strong solution has a continuous L² velocity. Its weak equation
is obtained by differentiation, and its initial trace follows from the original
PDE. The forcing trace is constructed from its given L² weak derivative. -/
theorem exists_velocityEvolution
    (h : IsStrongTransportDiffusionSolution ε a b B f q U G z)
    (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hB : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (F : Lp EnergySpace 2 (volume.restrict (Ioc a b)))
    (hf : ∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM ((F : ℝ → EnergySpace) t p) x = f p (t, x))
    (dF : Lp PivotSpace 2 (volume.restrict (Ioc a b)))
    (hF : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ (T).inclusion ((F : ℝ → EnergySpace) t)) dF)
    (C dC : ℝ → EnergySpace →L[ℝ] PivotSpace)
    (hC : ∀ t ∈ Icc a b, ∀ v : EnergySpace, ∀ p,
      C t v p = vectorTransportCLM
        (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun q ↦ v q) p)
    (hdC : ContinuousOn dC (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t) :
    ∃ (Fc : ℝ → PivotSpace) (g : Lp (StrongDual ℝ EnergySpace) 2 (volume.restrict (Ioc a b)))
      (E : ContinuousPivotEvolutionOn T ((G : ℝ → EnergySpace)) (fun t ↦ g t) a b),
      Continuous Fc ∧
      (Fc =ᵐ[(volume.restrict (Ioc a b))] fun t ↦ (T).inclusion ((F : ℝ → EnergySpace) t)) ∧
      (∀ t ∈ Icc a b, ‖Fc t‖ ≤ (((b - a)⁻¹ + 1) * max 1 (b - a)) *
        (‖(T).inclusion.compLpL 2 (volume.restrict (Ioc a b)) F‖ + ‖dF‖)) ∧
      ((fun t ↦ g t) =ᵐ[(volume.restrict (Ioc a b))] fun t ↦
        ε • vectorWeakLaplacianCLM ((G : ℝ → EnergySpace) t) +
        (T).pivotToDual (dC t (z t) + C t ((G : ℝ → EnergySpace) t) + dF t)) ∧
      (T).pivotToDual (E.representative a) = ε • (vectorWeakLaplacianCLM (n := n) (m := m)) q +
        (T).pivotToDual (C a q + Fc a) := by
  let J : StateSpace →L[ℝ] EnergySpace := vectorLowerOrderCLM (by decide : 1 ≤ 3)
  let u : Lp EnergySpace 2 (volume.restrict (Ioc a b)) := J.compLpL 2 (volume.restrict (Ioc a b)) U
  let FH : Lp PivotSpace 2 (volume.restrict (Ioc a b)) :=
    (T).inclusion.compLpL 2 (volume.restrict (Ioc a b)) F
  have huAE : (fun t ↦ u t) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ J ((U : ℝ → StateSpace) t) := J.coeFn_compLpL U
  have hFHAE : (fun t ↦ FH t) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ (T).inclusion ((F : ℝ → EnergySpace) t) :=
    (T).inclusion.coeFn_compLpL F
  have hu : HasWeakTimeDerivativeOn (Ioo a b) u G :=
    weakTimeDerivative_compLpL J h.weakTimeDerivative
  obtain ⟨hFH, Fc, hFc, hFcAE, hFcBound⟩ :=
    exists_continuous_compLpL_trace hab (T).inclusion hF
  have hCAC : AbsolutelyContinuousOnInterval C a b :=
    absolutelyContinuous_of_continuous_derivative hab hdC hderiv
  have hCderiv : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt C (dC t) t :=
    ae_hasDerivAt_of_hasDerivWithinAt_Icc hderiv
  have heq : ∀ᵐ t ∂(volume.restrict (Ioc a b)), (T).energyToDual ((G : ℝ → EnergySpace) t) =
      (ε • (vectorWeakLaplacianCLM (n := n) (m := m))) (u t) +
        (T).pivotToDual (C t (u t) + FH t) := by
    filter_upwards [h.dual_equation A hB F hf C hC, huAE, hFHAE] with t ht hut hft
    simpa only [smul_apply, hut, hft] using ht
  have hzu : z =ᵐ[(volume.restrict (Ioc a b))] u := h.representative.trans huAE.symm
  obtain ⟨g, E, hg, htrace⟩ :=
    exists_vector_velocityEvolution hab hu hFH hCAC hdC hCderiv heq
      h.continuousOn hzu hFc.continuousOn hFcAE.symm h.initial_eq
  exact ⟨Fc, g, E, hFc, hFcAE.symm.trans hFHAE, hFcBound, hg, htrace⟩

end PDE.Parabolic.Systems.IsStrongTransportDiffusionSolution
