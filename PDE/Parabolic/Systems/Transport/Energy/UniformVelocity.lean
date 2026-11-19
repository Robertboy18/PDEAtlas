/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Systems.Transport.Energy.Velocity.Continuous
public import PDE.Spaces.Sobolev.Approximation.Mollification.DerivativeBounds.Vector
import PDE.Parabolic.Systems.Transport.Energy.Uniform
import PDE.Parabolic.Systems.Transport.Energy.Pivot
import PDE.Spaces.Sobolev.Approximation.Mollification.ProductHk

/-!
# A data-independent closed-time velocity bound

A fixed coefficient curve and finite time slab determine the constant before
the data, viscosity, or solution. The scale-ε mollification of H¹ initial
data supplies the initial velocity bound. The differentiated equation then gives
a continuous L² velocity and the maximum of the sum of the two state norms.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal InnerProductSpace Sobolev Laplacian
open scoped SobolevSpace.WholeSpaceHilbert

namespace PDE.Parabolic.Systems

variable {n m : ℕ} {a b : ℝ}

private theorem velocity_budget_le
    {initial q f ft S R C Ct B Kd L Cs : ℝ}
    (hinit : initial ≤ R * S) (hq : q ≤ S) (hf : f ≤ B * S) (hft : ft ≤ S)
    (hC : 0 ≤ C) (hCt : 0 ≤ Ct) :
    initial + C * q + Ct * (f + ft) + ft + Kd * (L * (Cs * S)) ≤
      (R + C + Ct * (B + 1) + 1 + Kd * L * Cs) * S := by
  linarith [mul_le_mul_of_nonneg_left hq hC, mul_le_mul_of_nonneg_left (add_le_add hf hft) hCt]

private theorem exists_velocity_maximum_of_bounds
    (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (C dC : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ))
    (hC : ∀ t ∈ Icc a b, ∀ v : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)), ∀ p,
      C t v p = vectorTransportCLM
        (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun q ↦ v q) p)
    (hdC : ContinuousOn dC (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t)
    (ρ : Mollifier n) {Cs K Kd : ℝ} (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hKd : 0 ≤ Kd)
    (henergy : ∀ t ∈ Icc a b, ∀ v : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)),
      2 * ⟪C t v, (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion v⟫_ℝ
        ≤ K * ‖(vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion v‖ ^ 2)
    (hdBound : ∀ t ∈ Icc a b, ‖dC t‖ ≤ Kd)
    (g : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
    (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
    (Ft : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2 (volume.restrict (Ioc a b)))
    (hF : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦
      (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion (F t)) Ft)
    (ε : ℝ) (hε : 0 < ε)
    (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ)
    (hB : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q)
    (f : Fin m → ℝ × ℝ^n → ℝ)
    (hf : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ᵐ x ∂volume, ∀ p,
      wkpBaseCoordinateCLM (F t p) x = f p (t, x))
    (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
    (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
    (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
    (h : IsStrongTransportDiffusionSolution ε a b B f
      (ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM ρ hε) g) U G z)
    (hz : ∀ t ∈ Icc a b, ‖z t‖ ≤ Cs * (‖g‖ + ‖F‖ + ‖Ft‖)) :
    ∃ v : ℝ → PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ), ContinuousOn v (Icc a b) ∧
      (v =ᵐ[volume.restrict (Ioc a b)] fun t ↦
        (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion (G t)) ∧
      ∃ t ∈ Icc a b, IsMaxOn (fun s ↦ ‖z s‖ + ‖v s‖) (Icc a b) t ∧
        ‖z t‖ + ‖v t‖ ≤ (Cs + Real.exp ((K + 1) * (b - a)) *
          ((∑ j : Fin n, ∫ x, ‖fderiv ℝ ρ.ρ x (EuclideanSpace.single j 1)‖) + ‖C a‖ +
            (((b - a)⁻¹ + 1) * max 1 (b - a)) *
              (‖(vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion‖ + 1) +
            1 + Kd * ((measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^
              ((2 : ENNReal).toReal⁻¹)) * Cs) + 1) * (‖g‖ + ‖F‖ + ‖Ft‖) := by
  let triple := vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ
  let Rρ := ∑ j : Fin n, ∫ x, ‖fderiv ℝ ρ.ρ x (EuclideanSpace.single j 1)‖
  have hRρ : 0 ≤ Rρ := Finset.sum_nonneg fun j _ ↦ integral_nonneg fun x ↦ norm_nonneg _
  let L := (measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^ ((2 : ENNReal).toReal⁻¹)
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab.le
  let Ct := (((b - a)⁻¹ + 1) * max 1 (b - a))
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  let D := Rρ + ‖C a‖ + Ct * (‖triple.inclusion‖ + 1) + 1 + Kd * L * Cs
  let E := Real.exp ((K + 1) * (b - a))
  have hE : 0 ≤ E := Real.exp_nonneg _
  let S := ‖g‖ + ‖F‖ + ‖Ft‖
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hgS : ‖g‖ ≤ S :=
    (le_add_of_nonneg_right (norm_nonneg F)).trans (le_add_of_nonneg_right (norm_nonneg Ft))
  have hFS : ‖F‖ ≤ S :=
    (le_add_of_nonneg_left (norm_nonneg g)).trans (le_add_of_nonneg_right (norm_nonneg Ft))
  have hFtS : ‖Ft‖ ≤ S := le_add_of_nonneg_left (by positivity)
  let q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM ρ hε) g
  have hqnorm : ‖q‖ ≤ ‖g‖ := norm_piLpMap_mollifierHkCLM_le ρ hε g
  let Q : PiLp 2 (fun _ : Fin m ↦ W^{2,2}(ℝ^n)) :=
    WithLp.toLp 2 (fun p ↦ mollifierSmoothingCLM 2 ρ hε (wkpBaseCoordinateCLM (g p)))
  have hQ : ContinuousLinearMap.piLpMap 2
      (fun _ : Fin m ↦ lowerOrderCLM (by decide : 1 ≤ 2)) Q = q := PiLp.ext fun p ↦ by
    simp only [ContinuousLinearMap.piLpMap_apply, Q, q,
      lowerOrderCLM_mollifierSmoothingCLM, mollifierSmoothingCLM_baseCoordinate]
  have hLap : ε * ‖WithLp.toLp 2 (fun p ↦ Δ (Q p))‖ ≤ Rρ * ‖g‖ :=
    mul_norm_piLp_laplacian_mollifierSmoothingCLM_le ρ hε g
  obtain ⟨v, hv, hvAE, hvbound⟩ := h.exists_velocity_bound hab hε.le A hB F hf Ft hF
    C dC hC hdC hderiv hK hKd (mul_nonneg hCs hS) henergy hdBound hz Q hQ
  have hbase : ‖triple.inclusion.compLpL 2 (volume.restrict (Ioc a b)) F‖ ≤
      ‖triple.inclusion‖ * ‖F‖ :=
    triple.inclusion.norm_compLp_le F
  have hvUniform (t : ℝ) (ht : t ∈ Icc a b) : ‖v t‖ ≤ E * D * S := by
    refine (hvbound t ht).trans ?_
    rw [mul_assoc E D S]
    exact mul_le_mul_of_nonneg_left (velocity_budget_le
      (hLap.trans (mul_le_mul_of_nonneg_left hgS hRρ)) (hqnorm.trans hgS)
      (hbase.trans (mul_le_mul_of_nonneg_left hFS (norm_nonneg triple.inclusion)))
      hFtS (norm_nonneg (C a)) hCt) hE
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le)
    (h.continuousOn.norm.add hv.norm)
  exact ⟨v, hv, hvAE, t, ht, hmax,
    (add_le_add (hz t ht) (hvUniform t ht)).trans (by nlinarith only [hS])⟩

/-- The original strong solution with mollified H¹ data has a uniform closed-time
H¹-state plus L²-velocity maximum. The constant is fixed before every datum and
positive viscosity at most one. No velocity equation or initial velocity bound
is added to the strong-solution assumptions. -/
theorem exists_uniform_transport_velocity_constant
    (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b))
    (hsym : ∀ t ∈ Icc a b, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) = wkpBaseCoordinateCLM (A t j q p))
    (C dC : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ))
    (hC : ∀ t ∈ Icc a b, ∀ v : (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))), ∀ p,
      C t v p = vectorTransportCLM
        (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun q ↦ v q) p)
    (hdC : ContinuousOn dC (Icc a b))
    (hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt C (dC t) (Icc a b) t)
    (ρ : Mollifier n) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (g : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
        (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
        (Ft : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2
          (volume.restrict (Ioc a b))),
      HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦
      (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion (F t)) Ft →
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (B : Fin n → ℝ × ℝ^n → Fin m → Fin m → ℝ),
      (∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ j p q,
        wkpBaseCoordinateCLM (A t j p q) x = B j (t, x) p q) →
      ∀ (f : Fin m → ℝ × ℝ^n → ℝ),
      (∀ᵐ t ∂(volume.restrict (Ioc a b)), ∀ᵐ x ∂volume, ∀ p,
        wkpBaseCoordinateCLM (F t p) x = f p (t, x)) →
      ∀ (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
        (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2 (volume.restrict (Ioc a b)))
        (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε a b B f
        (ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM ρ hε) g) U G z →
      ∃ v : ℝ → (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)), ContinuousOn v (Icc a b) ∧
        (v =ᵐ[(volume.restrict (Ioc a b))] fun t ↦
        (vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ).inclusion (G t)) ∧
        ∃ t ∈ Icc a b, IsMaxOn (fun s ↦ ‖z s‖ + ‖v s‖) (Icc a b) t ∧
          ‖z t‖ + ‖v t‖ ≤ C₀ * (‖g‖ + ‖F‖ + ‖Ft‖) := by
  let triple := vectorHOneLTwoGelfandTriple (n := n) (m := m) isOpen_univ
  obtain ⟨Cs, hCs, hstate⟩ := exists_uniform_transport_diffusion_constant hab A hA hsym
  obtain ⟨K, hK, henergy⟩ := exists_vectorTransportCLM_uniform_pivot_energy_bound A hA hsym
  obtain ⟨Kd₀, hKd₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := dC) hdC
  let Kd := max Kd₀ 0
  have hKd : 0 ≤ Kd := le_max_right _ _
  have hdBound : ∀ t ∈ Icc a b, ‖dC t‖ ≤ Kd :=
    fun t ht ↦ (hKd₀ t ht).trans (le_max_left _ _)
  let Rρ := ∑ j : Fin n, ∫ x, ‖fderiv ℝ ρ.ρ x (EuclideanSpace.single j 1)‖
  have hRρ : 0 ≤ Rρ := Finset.sum_nonneg fun j _ ↦ integral_nonneg fun x ↦ norm_nonneg _
  let L := (measureUnivNNReal (volume.restrict (Ioc a b)) : ℝ) ^ ((2 : ENNReal).toReal⁻¹)
  have hL : 0 ≤ L := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hlength : 0 ≤ b - a := sub_nonneg.mpr hab.le
  let Ct := (((b - a)⁻¹ + 1) * max 1 (b - a))
  have hCt : 0 ≤ Ct := by dsimp only [Ct]; positivity
  let D := Rρ + ‖C a‖ + Ct * (‖triple.inclusion‖ + 1) + 1 + Kd * L * Cs
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let E := Real.exp ((K + 1) * (b - a))
  have hE : 0 ≤ E := Real.exp_nonneg _
  refine ⟨Cs + E * D + 1, by positivity, ?_⟩
  intro g F Ft hF ε hε hε1 B hB f hf U G z h
  let S := ‖g‖ + ‖F‖ + ‖Ft‖
  let q : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)) :=
    ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦ mollifierHkCLM ρ hε) g
  have hqnorm : ‖q‖ ≤ ‖g‖ := norm_piLpMap_mollifierHkCLM_le ρ hε g
  obtain ⟨s, _hs, hsmax, hsbound⟩ := hstate ε hε.le hε1 B hB f F hf q U G z h
  have hz : ∀ t ∈ Icc a b, ‖z t‖ ≤ Cs * S := fun t ht ↦ by
    have htmax : ‖z t‖ ≤ ‖z s‖ := hsmax ht
    have hh : Cs * (‖q‖ + ‖F‖) ≤ Cs * S := mul_le_mul_of_nonneg_left
      ((add_le_add hqnorm le_rfl).trans (le_add_of_nonneg_right (norm_nonneg Ft))) hCs.le
    have hn := norm_nonneg ((ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
      (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ))).compLpL
        2 (volume.restrict (Ioc a b)) G)
    linarith only [hsbound, hh, htmax, hn]
  have henergy' : ∀ t ∈ Icc a b, ∀ w : (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      2 * ⟪C t w, triple.inclusion w⟫_ℝ ≤ K * ‖triple.inclusion w‖ ^ 2 := fun t ht w ↦ by
    rw [show C t w = WithLp.toLp 2 (vectorTransportCLM
      (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)) (fun p ↦ w p)) from PiLp.ext (hC t ht w)]
    exact henergy t ht w
  exact exists_velocity_maximum_of_bounds hab A C dC hC hdC hderiv ρ hCs.le hK hKd
    henergy' hdBound g F Ft hF ε hε B hB f hf U G z h hz

end PDE.Parabolic.Systems
