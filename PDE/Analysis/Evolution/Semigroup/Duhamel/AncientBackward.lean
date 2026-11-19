/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientWeighted

/-!
# Backward Duhamel operators on ancient weighted paths

Unstable modes are evolved backward from their terminal value. Their forcing
contribution is an integral from the current time to the terminal time, with a
minus sign in the mild equation. If the backward kernel decays at rate `κ ≥ η`
and the forcing has weight `β > η`, its weighted operator norm is at most
`M / (β - η) * exp ((β - η) * a)` on `(-∞, a]`.

Equality `κ = η` is allowed. In Hou--Wang--Yang, Section 2.2, equation (2.15),
a Jordan-block estimate at rate `Re λ - δ` and the solution weight `η = δ` can
meet at that threshold.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The future forcing integral for a backward evolution. The kernel is
evaluated at the nonnegative lag `s - t` when `t ≤ a`. -/
def backwardDuhamel (K : ℝ → F →L[ℝ] E) (f : ℝ → F) (a t : ℝ) : E :=
  ∫ s in t..a, K (s - t) (f s)

/-- The future forcing vanishes at the prescribed terminal time. -/
@[simp]
theorem backwardDuhamel_self (K : ℝ → F →L[ℝ] E) (f : ℝ → F) (a : ℝ) :
    backwardDuhamel K f a a = 0 := by
  simp [backwardDuhamel]

/-- Continuous kernels and forcings give continuous future integrands. -/
theorem continuous_backwardIntegrand {K : ℝ → F →L[ℝ] E} {f : ℝ → F}
    (hK : Continuous K) (hf : Continuous f) (t : ℝ) :
    Continuous (fun s ↦ K (s - t) (f s)) :=
  (hK.comp (continuous_id.sub continuous_const)).clm_apply hf

/-- Both moving integration limits and the backward kernel depend continuously
on the current time. -/
theorem continuous_backwardDuhamel {K : ℝ → F →L[ℝ] E} {f : ℝ → F}
    (hK : Continuous K) (hf : Continuous f) (a : ℝ) :
    Continuous (backwardDuhamel K f a) := by
  have hkernel : Continuous (fun p : ℝ × ℝ ↦ K (p.2 - p.1) (f p.2)) :=
    (hK.comp (continuous_snd.sub continuous_fst)).clm_apply (hf.comp continuous_snd)
  have hprimitive := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (a₀ := 0) (f := fun t s : ℝ ↦ K (s - t) (f s)) hkernel
  have hc : Continuous (fun t : ℝ ↦
      (∫ s in (0 : ℝ)..a, K (s - t) (f s)) - ∫ s in (0 : ℝ)..t, K (s - t) (f s)) :=
    (hprimitive.comp (continuous_id.prodMk continuous_const)).sub
      (hprimitive.comp (continuous_id.prodMk continuous_id))
  apply hc.congr
  intro t
  exact intervalIntegral.integral_interval_sub_left
    ((continuous_backwardIntegrand hK hf t).intervalIntegrable 0 a)
    ((continuous_backwardIntegrand hK hf t).intervalIntegrable 0 t)

private theorem norm_backwardIntegrand_le
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {κ η β M D t s : ℝ}
    (hκ : η ≤ κ) (hM : 0 ≤ M) (hD : 0 ≤ D) (hts : t ≤ s)
    (hK : ‖K (s - t)‖ ≤ M * Real.exp (-(κ * (s - t))))
    (hf : ‖f s‖ ≤ D * Real.exp (β * s)) :
    ‖Real.exp (-(η * t)) • K (s - t) (f s)‖ ≤
      (M * D) * Real.exp ((β - η) * s) := by
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hexp : Real.exp (-(η * t)) * Real.exp (-(κ * (s - t))) *
      Real.exp (β * s) = Real.exp ((β - η) * s) *
        Real.exp (-((κ - η) * (s - t))) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ Real.exp (-(η * t)) *
        ((M * Real.exp (-(κ * (s - t)))) * (D * Real.exp (β * s))) :=
      mul_le_mul_of_nonneg_left
        (((K (s - t)).le_opNorm _).trans
          (mul_le_mul hK hf (norm_nonneg _) (by positivity))) (Real.exp_nonneg _)
    _ = ((M * D) * Real.exp ((β - η) * s)) *
        Real.exp (-((κ - η) * (s - t))) := by
      calc
        _ = (M * D) * (Real.exp (-(η * t)) *
            Real.exp (-(κ * (s - t))) * Real.exp (β * s)) := by ring
        _ = _ := by rw [hexp]; ring
    _ ≤ (M * D) * Real.exp ((β - η) * s) :=
      mul_le_of_le_one_right (by positivity)
        (Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hκ) (sub_nonneg.mpr hts))))

/-- A strict forcing weight gap controls the finite future integral even when
the backward kernel decay rate equals the solution weight. -/
theorem norm_weighted_backwardDuhamel_le
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {κ η β M D a t : ℝ}
    (hκ : η ≤ κ) (hgap : η < β) (hM : 0 ≤ M) (hD : 0 ≤ D) (ht : t ≤ a)
    (hK : ∀ r, 0 ≤ r → ‖K r‖ ≤ M * Real.exp (-(κ * r)))
    (hf : ∀ s, s ≤ a → ‖f s‖ ≤ D * Real.exp (β * s)) :
    ‖Real.exp (-(η * t)) • backwardDuhamel K f a t‖ ≤
      (M / (β - η) * Real.exp ((β - η) * a)) * D := by
  rw [backwardDuhamel, ← intervalIntegral.integral_smul]
  have hg : Continuous (fun s : ℝ ↦ (M * D) * Real.exp ((β - η) * s)) := by fun_prop
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) ht
    (Filter.Eventually.of_forall fun s hs ↦ norm_backwardIntegrand_le hκ hM hD hs.1.le
      (hK _ (sub_nonneg.mpr hs.1.le)) (hf s hs.2)) (hg.intervalIntegrable t a)
  have hd : ∀ s ∈ uIcc t a,
      HasDerivAt (fun s : ℝ ↦ (M * D / (β - η)) * Real.exp ((β - η) * s))
        ((M * D) * Real.exp ((β - η) * s)) s := by
    intro s _
    convert (((hasDerivAt_id s).const_mul (β - η)).exp.const_mul
      (M * D / (β - η))) using 1
    · rfl
    · dsimp only [id_eq]
      field_simp [(sub_pos.mpr hgap).ne']
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg.intervalIntegrable t a)] at hi
  calc
    _ ≤ (M * D / (β - η)) * Real.exp ((β - η) * a) -
        (M * D / (β - η)) * Real.exp ((β - η) * t) := hi
    _ ≤ (M * D / (β - η)) * Real.exp ((β - η) * a) :=
      sub_le_self _ (by positivity)
    _ = _ := by ring

variable {κ η β M a : ℝ} {K : ℝ → F →L[ℝ] E}

/-- The weighted future integral acting on bounded representatives of ancient
forcing paths. Its sign is positive; the mixed Green operator subtracts it. -/
def backwardDuhamelOperator
    (hκ : η ≤ κ) (hgap : η < β) (hM : 0 ≤ M)
    (hKcont : Continuous K)
    (hK : ∀ r, 0 ≤ r → ‖K r‖ ≤ M * Real.exp (-(κ * r))) :
    (Iic a →ᵇ F) →L[ℝ] (Iic a →ᵇ E) := by
  let C := M / (β - η) * Real.exp ((β - η) * a)
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hM (sub_pos.mpr hgap).le)
    (Real.exp_nonneg _)
  let I (u : Iic a →ᵇ F) : C(Iic a, E) :=
    { toFun t := Real.exp (-(η * (t : ℝ))) • backwardDuhamel K (ancientLift β u) a t
      continuous_toFun :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val).neg).smul
          ((continuous_backwardDuhamel hKcont (ancientLift β u).continuous a).comp
            continuous_subtype_val) }
  have hI (u : Iic a →ᵇ F) (t : Iic a) : ‖I u t‖ ≤ C * ‖u‖ :=
    norm_weighted_backwardDuhamel_le hκ hgap hM (norm_nonneg u) t.property hK
      (fun s _ ↦ norm_ancientLift_le β u s)
  let T : (Iic a →ᵇ F) →ₗ[ℝ] (Iic a →ᵇ E) :=
    { toFun u := ofNormedAddCommGroup (I u) (I u).continuous (C * ‖u‖) (hI u)
      map_add' u v := by
        ext t
        change Real.exp (-(η * (t : ℝ))) •
            backwardDuhamel K (ancientLift β (u + v)) a t =
          Real.exp (-(η * (t : ℝ))) • backwardDuhamel K (ancientLift β u) a t +
            Real.exp (-(η * (t : ℝ))) • backwardDuhamel K (ancientLift β v) a t
        have hlift : (ancientLift β (u + v) : ℝ → F) =
            fun s ↦ ancientLift β u s + ancientLift β v s := by
          funext s
          change Real.exp (β * s) • (u _ + v _) =
            Real.exp (β * s) • u _ + Real.exp (β * s) • v _
          exact smul_add _ _ _
        rw [hlift]
        simp only [backwardDuhamel, map_add]
        rw [intervalIntegral.integral_add
          ((continuous_backwardIntegrand hKcont (ancientLift β u).continuous t)
            |>.intervalIntegrable t a)
          ((continuous_backwardIntegrand hKcont (ancientLift β v).continuous t)
            |>.intervalIntegrable t a), smul_add]
      map_smul' c u := by
        ext t
        change Real.exp (-(η * (t : ℝ))) •
            backwardDuhamel K (ancientLift β (c • u)) a t =
          c • (Real.exp (-(η * (t : ℝ))) • backwardDuhamel K (ancientLift β u) a t)
        have hlift : (ancientLift β (c • u) : ℝ → F) =
            fun s ↦ c • ancientLift β u s := by
          funext s
          change Real.exp (β * s) • (c • u _) = c • (Real.exp (β * s) • u _)
          exact smul_comm _ _ _
        rw [hlift]
        simp only [backwardDuhamel, map_smul, intervalIntegral.integral_smul]
        rw [smul_comm] }
  exact T.mkContinuous C (fun u ↦ norm_ofNormedAddCommGroup_le (I u).continuous
    (mul_nonneg hC (norm_nonneg u)) (hI u))

/-- Evaluation is the normalized future forcing integral. -/
@[simp]
theorem backwardDuhamelOperator_apply
    (hκ : η ≤ κ) (hgap : η < β) (hM : 0 ≤ M)
    (hKcont : Continuous K)
    (hK : ∀ r, 0 ≤ r → ‖K r‖ ≤ M * Real.exp (-(κ * r)))
    (u : Iic a →ᵇ F) (t : Iic a) :
    backwardDuhamelOperator hκ hgap hM hKcont hK u t =
      Real.exp (-(η * (t : ℝ))) • backwardDuhamel K (ancientLift β u) a t :=
  rfl

/-- The explicit weighted norm bound for backward forcing. -/
theorem norm_backwardDuhamelOperator_le
    (hκ : η ≤ κ) (hgap : η < β) (hM : 0 ≤ M)
    (hKcont : Continuous K)
    (hK : ∀ r, 0 ≤ r → ‖K r‖ ≤ M * Real.exp (-(κ * r))) :
    ‖backwardDuhamelOperator (a := a) hκ hgap hM hKcont hK‖ ≤
      M / (β - η) * Real.exp ((β - η) * a) := by
  unfold backwardDuhamelOperator
  apply LinearMap.mkContinuous_norm_le
  exact mul_nonneg (div_nonneg hM (sub_pos.mpr hgap).le) (Real.exp_nonneg _)

end PDE.Analysis.Evolution
