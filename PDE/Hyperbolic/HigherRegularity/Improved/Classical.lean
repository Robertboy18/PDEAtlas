/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Improved.Temporal
public import PDE.Hyperbolic.HigherRegularity.Improved.Spatial
public import PDE.Hyperbolic.HigherRegularity.Improved.InitialData

/-!
# Improved regularity for every classical-coefficient weak wave

For the full autonomous divergence operator, an `H² ∩ H¹₀` displacement, an `H¹₀`
velocity and an `H¹`-in-time `L²` forcing give the four regularity conclusions of
Evans, §7.2.3, Theorem 5(ii). The forcing trace, compatible differentiated solve and
spatial lift are constructed from these data. Weak uniqueness transfers them to
any solution in the original weak class. A `C²` graph boundary and `C¹` principal
and drift coefficients suffice; the potential only needs continuity up to the boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 5(ii), estimate (51).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set PDE.Analysis.Evolution Hyperbolic.Variational
open scoped ENNReal

namespace SobolevSpace.GraphSpace

open BoundaryRegularity

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

private theorem improved_time_data_bound {f ft h ell K L D : ℝ} (hf : f ≤ D) (hft : ft ≤ D)
    (hfh : ft + h ≤ D) (hell : ell ≤ L * D) (hK : 0 ≤ K) :
    ft + h + K * (f + ft) + ell ≤ (1 + 2 * K + L) * D := by
  have hp := mul_le_mul_of_nonneg_left (add_le_add hf hft) hK
  nlinarith only [hp, hfh, hell]

/-- The improved regularity estimate (51) of Evans, §7.2.3, Theorem 5(ii), for the full autonomous
operator and every weak solution.
All time derivatives are identified in the ordinary weak sense, the spatial lift
represents the same `H¹₀` function, and the constant precedes all solution data.
The square root on the right is the Hilbert `H¹` time norm of the forcing. -/
theorem exists_classical_improved_wave_regularity
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    {a b : ℝ} (hab : a < b)
    {A : ℝ^n → Fin n → Fin n → ℝ} {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ}
    (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary 1 (B i) Ω) (hC : ContDiffUpToBoundary 0 C Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ,
      alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i) :
    let T := h10L2GelfandTriple hopen
    let F := classicalAutonomousWaveForm hopen hbounded hA hB hC
    ∃ K : ℝ, 0 < K ∧
      ∀ (f ft : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (G : W^{2,2}(Ω)) (g h : H¹₀(Ω)),
        lowerOrderCLM (k := 1) (m := 2) (by omega) G = h10SubtypeL g →
        HasWeakTimeDerivativeOn (Ioo a b) f ft →
        ∀ (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
          (velocity : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
          (acceleration : Lp (StrongDual ℝ (H¹₀(Ω))) 2
            (volume.restrict (Ioc a b))),
          IsGelfandWeakWaveSolution T (fun _ ↦ F)
            (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f)
            u velocity acceleration g (T.inclusion h) →
          ∃ (U : Lp (W^{2,2}(Ω)) 2 (volume.restrict (Ioc a b)))
            (v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
            (w : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
            (z : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
            (∀ᵐ t ∂volume.restrict (Ioc a b),
              lowerOrderCLM (k := 1) (m := 2) (by omega) (U t) = h10SubtypeL (u t)) ∧
            velocity = T.inclusion.compLpL 2 (volume.restrict (Ioc a b)) v ∧
            acceleration = T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) w ∧
            HasWeakTimeDerivativeOn (Ioo a b) u v ∧
            HasWeakTimeDerivativeOn (Ioo a b) velocity w ∧
            HasWeakTimeDerivativeOn (Ioo a b) acceleration z ∧
            MemLp (fun t ↦ U t) ∞ (volume.restrict (Ioc a b)) ∧
            MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧
            MemLp (fun t ↦ w t) ∞ (volume.restrict (Ioc a b)) ∧
            (eLpNormEssSup (fun t ↦ ‖U t‖ + ‖v t‖ + ‖w t‖)
              (volume.restrict (Icc a b))).toReal + ‖z‖ ≤
                K * (Real.sqrt (‖f‖ ^ 2 + ‖ft‖ ^ 2) + ‖G‖ + ‖h‖) := by
  let μ := volume.restrict (Ioc a b)
  let T := h10L2GelfandTriple hopen
  let F := classicalAutonomousWaveForm hopen hbounded hA hB hC
  have henergyExists := exists_uniform_energy_bound_of_classical_autonomous_coefficients
    (n := n) (Ω := Ω) (a := a) (b := b) (A := A) (B := B) (C := C)
    (Fact.out : 0 < n) hopen hbounded hab hA hB hC hsymm halpha hell
  let M := henergyExists.choose
  have hM : 0 < M := henergyExists.choose_spec.1
  have henergy := henergyExists.choose_spec.2
  have hloadExists := exists_initial_full_load_bound
    (n := n) (Ω := Ω) (A := A) (B := B) (C := C) hopen hbounded hA hB hC
  let L := hloadExists.choose
  have hL : 0 ≤ L := hloadExists.choose_spec.1
  have hload := hloadExists.choose_spec.2
  have hEll : ∀ x ∈ Ω, MatrixEllipticLowerBound (A x) alpha := by
    intro x hx ξ
    simpa only [MatrixEllipticLowerBound, dotProduct, principalEnergy,
      mul_assoc, mul_comm, mul_left_comm] using hell x hx ξ
  have hSpatial := exists_classical_full_h2_lift hopen hbounded hgraph A hA
    (fun i ↦ (hB i).toLp hopen hbounded ∞) (hC.toLp hopen hbounded ∞) halpha hEll
  let mu := hSpatial.choose
  let S := hSpatial.choose_spec.choose
  have hS := hSpatial.choose_spec.choose_spec
  let Kf := (((b - a)⁻¹ + 1) * max 1 (b - a))
  let Vc := M * (1 + 2 * Kf + L)
  let Sc := ‖S‖ * (2 * Kf + Vc + |mu| * M)
  let tc := (measureUnivNNReal μ : ℝ) ^ (2 : ℝ)⁻¹
  let Zc := ‖T.pivotToDual‖ + ‖F‖ * tc * Vc
  let K := Sc + Vc + Zc + 1
  have hKf : 0 ≤ Kf := by dsimp only [Kf]; positivity
  have hVc : 0 ≤ Vc := by dsimp only [Vc]; positivity
  have hSc : 0 ≤ Sc := by dsimp only [Sc]; positivity
  have htc : 0 ≤ tc := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hZc : 0 ≤ Zc := by dsimp only [Zc]; positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro f ft G g h hG hft u velocity acceleration hweak
  let D := Real.sqrt (‖f‖ ^ 2 + ‖ft‖ ^ 2) + ‖G‖ + ‖h‖
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hfroot : ‖f‖ ≤ Real.sqrt (‖f‖ ^ 2 + ‖ft‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg ‖ft‖))
  have hftroot : ‖ft‖ ≤ Real.sqrt (‖f‖ ^ 2 + ‖ft‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg ‖f‖))
  have := Real.sqrt_nonneg (‖f‖ ^ 2 + ‖ft‖ ^ 2)
  have hDdef : D = Real.sqrt (‖f‖ ^ 2 + ‖ft‖ ^ 2) + ‖G‖ + ‖h‖ := rfl
  have hfD : ‖f‖ ≤ D := by linarith [norm_nonneg G, norm_nonneg h]
  have hftD : ‖ft‖ ≤ D := by linarith [norm_nonneg G, norm_nonneg h]
  have hGD : ‖G‖ ≤ D := by linarith [norm_nonneg h]
  have hgG : ‖g‖ ≤ ‖G‖ := by
    have hh := norm_lowerOrderCLM_apply_le (p := 2) (by omega : 1 ≤ 2) G
    rwa [hG] at hh
  have hfg : ‖f‖ + ‖g‖ + ‖T.inclusion h‖ ≤ D := by
    have hh := baseCoordCLM_norm_le h
    change ‖T.inclusion h‖ ≤ ‖h‖ at hh
    linarith
  let Lg := (hload G g hG).choose
  have hLg := (hload G g hG).choose_spec.1
  have hLgBound := (hload G g hG).choose_spec.2
  have hsolve : ∀ (f₁ : Lp (DerivLp n 2 Ω) 2 μ) (g₁ : H¹₀(Ω)) (h₁ : DerivLp n 2 Ω), ∃ u₁ v₁ w₁,
      IsGelfandWeakWaveSolution T (fun _ ↦ F) (T.pivotToDual.compLpL 2 μ f₁)
        u₁ v₁ w₁ g₁ h₁ ∧ MemLp (fun t ↦ u₁ t) ∞ μ ∧ MemLp (fun t ↦ v₁ t) ∞ μ ∧
        ∀ᵐ t ∂μ, ‖u₁ t‖ + ‖v₁ t‖ ≤ M * (‖f₁‖ + ‖g₁‖ + ‖h₁‖) := by
    intro f₁ g₁ h₁
    obtain ⟨⟨u₁, v₁, w₁, hu₁⟩, hb₁⟩ := henergy f₁ g₁ h₁
    exact ⟨u₁, v₁, w₁, hu₁, hb₁ u₁ v₁ w₁ hu₁⟩
  choose u₀ v w z h₀ huv hvw hwz hvtop hwtop hvbound hfbound hzbound using
    exists_improved_wave_of_energy_bound hab hM hsolve f ft hft g h Lg hLg
  have heq := weakWave_eq_of_classical_autonomous_coefficients
    (n := n) (Ω := Ω) (a := a) (b := b) (A := A) (B := B) (C := C)
    (Fact.out : 0 < n) hopen hbounded hA hB hC hsymm halpha hell hweak h₀
  have hvelocity := heq.2.1
  have hacceleration := heq.2.2
  rw [← heq.1] at h₀ huv
  have hMD : M * (‖ft‖ + ‖h‖ + Kf * (‖f‖ + ‖ft‖) + ‖Lg‖) ≤ Vc * D := by
    simpa only [Vc, mul_assoc] using mul_le_mul_of_nonneg_left (improved_time_data_bound hfD
      hftD (by linarith [norm_nonneg G]) (hLgBound.trans (mul_le_mul_of_nonneg_left hGD hL))
      hKf) hM.le
  have hvwBound : ∀ᵐ t ∂μ, ‖v t‖ + ‖w t‖ ≤ Vc * D := by
    filter_upwards [hvbound] with t ht
    exact (show ‖v t‖ + ‖w t‖ ≤ M * (‖ft‖ + ‖h‖ + Kf * (‖f‖ + ‖ft‖) + ‖Lg‖) from ht).trans hMD
  have hfBound : ∀ᵐ t ∂μ, ‖f t‖ ≤ (2 * Kf) * D := hfbound.mono fun t ht ↦ ht.trans (by
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hfD hftD) hKf])
  have hwBound : ∀ᵐ t ∂μ, ‖w t‖ ≤ Vc * D :=
    hvwBound.mono fun t ht ↦ (le_add_of_nonneg_left (norm_nonneg (v t))).trans ht
  have huBound : ∀ᵐ t ∂μ, ‖u t‖ ≤ M * D :=
    ((henergy f g (T.inclusion h)).2 u velocity acceleration hweak).2.2.mono fun t ht ↦
      ((le_add_of_nonneg_right (norm_nonneg (velocity t))).trans ht).trans
        (mul_le_mul_of_nonneg_left hfg hM.le)
  choose U hU hUtop hUbound using exists_h2_trajectory_of_full_weakWave hopen
    (fun i j ↦ (hA i j).toLp hopen hbounded ∞) (fun i ↦ (hB i).toLp hopen hbounded ∞)
    (hC.toLp hopen hbounded ∞) mu S hS h₀ hfBound hwBound huBound
  have hzestimate : ‖z‖ ≤ Zc * D := calc
    ‖z‖ ≤ ‖T.pivotToDual‖ * ‖ft‖ +
        ‖F‖ * (tc * (M * (‖ft‖ + ‖h‖ + Kf * (‖f‖ + ‖ft‖) + ‖Lg‖))) := hzbound
    _ ≤ ‖T.pivotToDual‖ * D + ‖F‖ * (tc * (Vc * D)) :=
      add_le_add (mul_le_mul_of_nonneg_left hftD (norm_nonneg T.pivotToDual))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMD htc) (norm_nonneg F))
    _ = _ := by simp only [Zc, add_mul, mul_assoc]
  have hsmall : volume.restrict (Ioo a b) ≤ μ := volume.restrict_mono_set Ioo_subset_Ioc_self
  have hvelocityAE : (velocity : ℝ → DerivLp n 2 Ω) =ᵐ[μ] fun t ↦ T.inclusion (v t) := by
    rw [hvelocity]
    exact T.inclusion.coeFn_compLpL v
  have haccelerationAE :
      (acceleration : ℝ → StrongDual ℝ (H¹₀(Ω))) =ᵐ[μ] fun t ↦ T.pivotToDual (w t) := by
    rw [hacceleration]
    exact T.pivotToDual.coeFn_compLpL w
  refine ⟨U, v, w, z, hU, hvelocity, hacceleration, huv, hvw.congr_ae_restrict measurableSet_Ioo
      (hvelocityAE.symm.filter_mono (ae_mono hsmall)) Filter.EventuallyEq.rfl,
    hwz.congr_ae_restrict measurableSet_Ioo
      (haccelerationAE.symm.filter_mono (ae_mono hsmall)) Filter.EventuallyEq.rfl,
    hUtop, hvtop, hwtop, ?_⟩
  have hsum : ∀ᵐ t ∂μ, ‖‖U t‖ + ‖v t‖ + ‖w t‖‖ ≤ (Sc + Vc) * D := by
    filter_upwards [hUbound, hvwBound] with t hUt hvwt
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : ‖U t‖ ≤ Sc * D := hUt.trans_eq (by simp only [Sc, mul_add, add_mul, mul_assoc])
    linarith
  have hsup := (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hsum)).trans_eq (ENNReal.toReal_ofReal (by positivity))
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  change _ ≤ (Sc + Vc + Zc + 1) * D
  linarith

end SobolevSpace.GraphSpace
