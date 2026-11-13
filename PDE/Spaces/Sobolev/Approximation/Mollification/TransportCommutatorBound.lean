/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.TransportCommutator
import PDE.Analysis.Integration.ConvolutionCommutator
import PDE.Spaces.Sobolev.Approximation.Mollification.KernelMoment
import PDE.Spaces.Sobolev.GraphSpace.Representatives.Lipschitz

/-!
# A uniform L² transport commutator bound

For a W¹,∞ coefficient, the difference
`a Dεⱼu - Dεⱼ(a u) + Jε((∂ⱼa)u)` is uniformly bounded on L² as `ε > 0`
varies. The principal two terms are bounded using a Lipschitz representative of `a`
and the scale-independent first moment of the differentiated kernel. The final term
uses the L∞ derivative coordinate and the L² contraction of `Jε`.

The weak product rule already proves convergence to zero for H¹ inputs.
The uniform bound makes this family equicontinuous, so density extends that
convergence to every L² input. No weak derivative of the input is required.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace PDE.Analysis

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- Passing from the restricted whole-space measure to volume preserves multiplication
by an L∞ coefficient. The two representatives need only agree almost everywhere. -/
private theorem wholeSpaceL2Equiv_lpSMul_of_ae_eq
    (a : DerivLp n ∞ univ) (a' : Lp ℝ ∞ (volume : Measure (ℝ^n)))
    (ha : (a' : ℝ^n → ℝ) =ᵐ[volume] a) (u : L2) :
    wholeSpaceL2Equiv (a • u) = a' • wholeSpaceL2Equiv u := by
  have hproduct : (a • u : L2) =ᵐ[volume] fun x ↦ a x • u x := by
    have h := Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a u
    change (a • u : L2) =ᵐ[domainMeasure n univ] (fun x ↦ a x • u x) at h
    simpa only [domainMeasure, Measure.restrict_univ] using h
  apply Lp.ext
  filter_upwards [wholeSpaceL2Equiv_ae (a • u), wholeSpaceL2Equiv_ae u,
    hproduct, Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) a' (wholeSpaceL2Equiv u),
    ha] with x hleft hu hproduct hright ha
  rw [hleft, hproduct, hright, Pi.smul_apply', hu, ha]

/-- The L² transport commutator has a bound independent of every positive scale.
The constants are the L∞ derivative-row norms and the first absolute
moment of the unscaled directional kernel derivative. -/
theorem norm_mollifierTransportCommutatorCLM_apply_le
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (A : W^{1,∞}(ℝ^n))
    (j : Fin n) (u : L2) :
    ‖mollifierTransportCommutatorCLM μ hε A j u‖ ≤
      ((∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) *
          (∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖) +
        ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖) * ‖u‖ := by
  let a : DerivLp n ∞ univ := (A : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let da : DerivLp n ∞ univ :=
    (A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)
  let K : ℝ≥0 :=
    ∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖₊
  let M : ℝ := ∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖
  have hK : (K : ℝ) =
      ∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖ := by
    simp only [K, NNReal.coe_sum, coe_nnnorm]
  have hmp : MeasurePreserving (id : ℝ^n → ℝ^n)
      (volume : Measure (ℝ^n)) (domainMeasure n univ) := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      MeasurePreserving.id (volume : Measure (ℝ^n))
  let a' : Lp ℝ ∞ (volume : Measure (ℝ^n)) :=
    Lp.compMeasurePreserving id hmp a
  have ha : (a' : ℝ^n → ℝ) =ᵐ[volume] a :=
    Lp.coeFn_compMeasurePreserving a hmp
  obtain ⟨v, hv, hva⟩ := A.exists_lipschitzWith_baseRepresentative
  have hva' : v =ᵐ[volume] a' := hva.trans ha.symm
  have hprincipal :
      ‖a • mollifierDerivativeRowCLM μ hε j u -
        mollifierDerivativeRowCLM μ hε j (a • u)‖ ≤ (K : ℝ) * M * ‖u‖ := by
    rw [← wholeSpaceL2Equiv.norm_map
      (a • mollifierDerivativeRowCLM μ hε j u -
        mollifierDerivativeRowCLM μ hε j (a • u))]
    rw [map_sub, wholeSpaceL2Equiv_lpSMul_of_ae_eq a a' ha,
      wholeSpaceL2Equiv_mollifierDerivativeRowCLM,
      wholeSpaceL2Equiv_mollifierDerivativeRowCLM,
      wholeSpaceL2Equiv_lpSMul_of_ae_eq a a' ha]
    have h := norm_lpSMul_convolutionL2CLM_sub_le a' hv hva'
      (fun x ↦ fderiv ℝ (scaled μ ε) x (EuclideanSpace.single j 1))
      (integrable_fderiv_scaled_apply μ hε j)
      (integrable_norm_mul_norm_fderiv_scaled_apply μ hε (EuclideanSpace.single j 1))
      (wholeSpaceL2Equiv u)
    rw [integral_norm_mul_norm_fderiv_scaled_apply μ hε,
      wholeSpaceL2Equiv.norm_map] at h
    exact h
  have hzero : ‖mollifierRowCLM μ hε (da • u)‖ ≤ ‖da‖ * ‖u‖ :=
    (norm_mollifierRowCLM_apply_le μ hε (da • u)).trans (Lp.norm_smul_le da u)
  rw [mollifierTransportCommutatorCLM_apply]
  change ‖(a • mollifierDerivativeRowCLM μ hε j u -
      mollifierDerivativeRowCLM μ hε j (a • u)) +
      mollifierRowCLM μ hε (da • u)‖ ≤ _
  calc
    _ ≤ ‖a • mollifierDerivativeRowCLM μ hε j u -
          mollifierDerivativeRowCLM μ hε j (a • u)‖ +
        ‖mollifierRowCLM μ hε (da • u)‖ := norm_add_le _ _
    _ ≤ (K : ℝ) * M * ‖u‖ + ‖da‖ * ‖u‖ := add_le_add hprincipal hzero
    _ = ((K : ℝ) * M + ‖da‖) * ‖u‖ := (add_mul _ _ _).symm
    _ = _ := by rw [hK]

/-- Along positive scales tending to zero, the transport commutator converges
strongly to zero on every L² input. The proof extends the weak-product-rule
cancellation on the dense H¹₀ base coordinates using the uniform bound above. -/
theorem tendsto_mollifierTransportCommutatorCLM
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (A : W^{1,∞}(ℝ^n))
    (j : Fin n) (u : L2) :
    Tendsto (fun k ↦ mollifierTransportCommutatorCLM μ (hε k) A j u)
      atTop (𝓝 (0 : L2)) := by
  let R : ℕ → L2 →L[ℝ] L2 := fun k ↦
    mollifierTransportCommutatorCLM μ (hε k) A j
  let B : ℝ :=
    (∑ l : Fin n, ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) *
        (∫ x, ‖x‖ * ‖(∂[j] μ.ρ) x‖) +
      ‖(A : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖
  have hbound (k : ℕ) (w : L2) : ‖R k w‖ ≤ B * ‖w‖ :=
    norm_mollifierTransportCommutatorCLM_apply_le μ (hε k) A j w
  have hmod : Tendsto (fun r : ℝ ↦ B * r) (𝓝 0) (𝓝 0) := by
    have hB : Tendsto (fun _ : ℝ ↦ B) (𝓝 0) (𝓝 B) := tendsto_const_nhds
    simpa only [mul_zero, id_eq] using
      hB.mul (tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 0) (𝓝 0))
  have heq : Equicontinuous (fun k w ↦ R k w) :=
    Metric.equicontinuous_of_continuity_modulus (fun r ↦ B * r) hmod
      (fun k w ↦ R k w) (fun x y k ↦ by
        rw [dist_eq_norm, ← map_sub, dist_eq_norm]
        exact hbound k (x - y))
  apply (heq u).tendsto_of_mem_closure
    (f := fun _ : L2 ↦ (0 : L2))
    (s := Set.range (baseCoordCLM (n := n) (Ω := univ)))
    tendsto_const_nhds
  · rintro _ ⟨U, rfl⟩
    exact tendsto_mollifierTransportCommutatorCLM_base μ ε hε hε0 A j U.1
  · exact baseCoordCLM_denseRange isOpen_univ u

end SobolevSpace.Approximation
