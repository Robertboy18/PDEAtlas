/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.ProfileTransport
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileSemigroup

/-!
# The self-similar evolution around a profile on `Hᵏ`

Let the transport coefficients `b` and the stretching coefficients `c` on `ℝ³` have `k` weak
derivatives in `L∞`. The transport `B v = Σᵢ bᵢ ∂ᵢ v + c v` is then bounded from vector `Hᵏ⁺¹`
to vector `Hᵏ`, and the self-similar evolution `S` with generator `L₀ - Π B` is a strongly
continuous semigroup on vector `Hᵏ`. It solves the Duhamel equation, has an exponential bound,
gains one derivative with the bound `C t^{-1/2} e^{ω t}`, and preserves fields fixed by the
Leray projection.

The evolutions of different orders are compatible. With coefficient bounds of order `k + 1`,
the transport on `Hᵏ⁺²` agrees with the transport on `Hᵏ⁺¹` once the top order is forgotten,
so the evolution on `Hᵏ⁺¹` is the restriction of the evolution on `Hᵏ`, and it continues the
gaining path from `Hᵏ`. Composing the gains of successive orders at half times, the evolution
on `Hʲ` maps into `Hʲ⁺ᵐ` at positive times with the bound `C t^{-m/2} e^{ω t}`. At order zero
the evolution is the evolution on `L²` built from the bounded coefficients.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open HeatEquation.WholeSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace NavierStokes.Selfsimilar

variable {b : Fin 3 → DerivLp 3 ∞ Set.univ} {c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ}

namespace ProfileCoefficientBounds

variable {k : ℕ}

/-- The `W^{k,∞}` field whose base function is the transport coefficient `bᵢ`. -/
def transportField (hk : ProfileCoefficientBounds k b c) (i : Fin 3) : W^{k,∞}(ℝ^3) :=
  (hk.transport_mem i).choose

/-- The chosen transport field has base function `bᵢ`. -/
theorem wkpBaseCoordinateCLM_transportField (hk : ProfileCoefficientBounds k b c) (i : Fin 3) :
    wkpBaseCoordinateCLM (hk.transportField i) = b i :=
  (hk.transport_mem i).choose_spec

/-- The base row of the chosen transport field is `bᵢ`, in simp normal form. -/
@[simp]
theorem transportField_baseIndex (hk : ProfileCoefficientBounds k b c) (i : Fin 3) :
    (hk.transportField i : WkpAmbientOn 3 k ∞ univ) (baseIndex 3 k) = b i :=
  hk.wkpBaseCoordinateCLM_transportField i

/-- The `W^{k,∞}` field whose base function is the stretching coefficient `cⱼᵢ`. -/
def stretchingField (hk : ProfileCoefficientBounds k b c) (j i : Fin 3) : W^{k,∞}(ℝ^3) :=
  (hk.stretching_mem j i).choose

/-- The chosen stretching field has base function `cⱼᵢ`. -/
theorem wkpBaseCoordinateCLM_stretchingField (hk : ProfileCoefficientBounds k b c)
    (j i : Fin 3) : wkpBaseCoordinateCLM (hk.stretchingField j i) = c j i :=
  (hk.stretching_mem j i).choose_spec

/-- The base row of the chosen stretching field is `cⱼᵢ`, in simp normal form. -/
@[simp]
theorem stretchingField_baseIndex (hk : ProfileCoefficientBounds k b c) (j i : Fin 3) :
    (hk.stretchingField j i : WkpAmbientOn 3 k ∞ univ) (baseIndex 3 k) = c j i :=
  hk.wkpBaseCoordinateCLM_stretchingField j i

/-- Coefficient bounds of order `k` give coefficient bounds of every lower order. -/
theorem of_le {j : ℕ} (hjk : j ≤ k) (hk : ProfileCoefficientBounds k b c) :
    ProfileCoefficientBounds j b c :=
  ⟨fun i ↦ ⟨lowerOrderCLM hjk (hk.transportField i), by
      rw [wkpBaseCoordinateCLM_lowerOrderCLM, wkpBaseCoordinateCLM_transportField]⟩,
    fun j i ↦ ⟨lowerOrderCLM hjk (hk.stretchingField j i), by
      rw [wkpBaseCoordinateCLM_lowerOrderCLM, wkpBaseCoordinateCLM_stretchingField]⟩⟩

/-- The transport `v ↦ Σᵢ bᵢ ∂ᵢ v + c v` from vector `Hᵏ⁺¹` to vector `Hᵏ`. -/
def transport (hk : ProfileCoefficientBounds k b c) : VectorH 3 (k + 1) →L[ℝ] VectorH 3 k :=
  SobolevConvection.linearTransport k hk.transportField hk.stretchingField

/-- At order zero the transport is the bounded transport with the coefficients `b` and `c`. -/
theorem transport_zero (hk : ProfileCoefficientBounds 0 b c) :
    hk.transport = BoundedTransport.transport b c := by
  rw [transport, SobolevConvection.linearTransport_zero]
  simp only [wkpBaseCoordinateCLM_transportField, wkpBaseCoordinateCLM_stretchingField]

/-- Forgetting the top order of the transport field of order `k + 1` gives the transport field
of order `k`, since the base function determines a Sobolev field. -/
theorem lowerOrderCLM_transportField (hk : ProfileCoefficientBounds (k + 1) b c)
    (hk' : ProfileCoefficientBounds k b c) (i : Fin 3) :
    lowerOrderCLM (Nat.le_succ k) (hk.transportField i) = hk'.transportField i := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [wkpBaseCoordinateCLM_lowerOrderCLM, wkpBaseCoordinateCLM_transportField,
    wkpBaseCoordinateCLM_transportField]

/-- Forgetting the top order of the stretching field of order `k + 1` gives the stretching
field of order `k`. -/
theorem lowerOrderCLM_stretchingField (hk : ProfileCoefficientBounds (k + 1) b c)
    (hk' : ProfileCoefficientBounds k b c) (j i : Fin 3) :
    lowerOrderCLM (Nat.le_succ k) (hk.stretchingField j i) = hk'.stretchingField j i := by
  apply wkpBaseCoordinateCLM_injective isOpen_univ
  rw [wkpBaseCoordinateCLM_lowerOrderCLM, wkpBaseCoordinateCLM_stretchingField,
    wkpBaseCoordinateCLM_stretchingField]

/-- With bounds of order `k + 1`, the transport on `Hᵏ⁺²` with the top order of the result
forgotten is the transport on `Hᵏ⁺¹` of the field with the top order forgotten. -/
theorem vectorLower_transport (hk : ProfileCoefficientBounds (k + 1) b c)
    (hk' : ProfileCoefficientBounds k b c) (v : VectorH 3 (k + 2)) :
    vectorLower 3 k (hk.transport v) = hk'.transport (vectorLower 3 (k + 1) v) := by
  have h := SobolevConvection.vectorLowerOrderCLM_linearTransport (Nat.le_succ k)
    hk.transportField hk.stretchingField v
  simp only [lowerOrderCLM_transportField hk hk', lowerOrderCLM_stretchingField hk hk'] at h
  exact h

/-- The transport is the linear transport of any `W^{k,∞}` fields with the base functions `b` and
`c`. -/
theorem transport_eq_linearTransport (hk : ProfileCoefficientBounds k b c)
    {B : Fin 3 → W^{k,∞}(ℝ^3)} {C : Fin 3 → Fin 3 → W^{k,∞}(ℝ^3)}
    (hB : ∀ i, wkpBaseCoordinateCLM (B i) = b i)
    (hC : ∀ j i, wkpBaseCoordinateCLM (C j i) = c j i) :
    hk.transport = SobolevConvection.linearTransport k B C := by
  have h1 : hk.transportField = B := funext fun i ↦
    wkpBaseCoordinateCLM_injective isOpen_univ (by rw [wkpBaseCoordinateCLM_transportField, hB])
  have h2 : hk.stretchingField = C := funext fun j ↦ funext fun i ↦
    wkpBaseCoordinateCLM_injective isOpen_univ (by rw [wkpBaseCoordinateCLM_stretchingField, hC])
  rw [transport, h1, h2]

/-- A velocity `U` with `k + 1` weak derivatives in `L∞` gives coefficient bounds of order `k`
for the transport coefficients `Uᵢ` and the stretching coefficients `cⱼᵢ = ∂ᵢ Uⱼ`. -/
theorem of_profile (U : Fin 3 → W^{k + 1,∞}(ℝ^3)) :
    ProfileCoefficientBounds k (fun i ↦ wkpBaseCoordinateCLM (U i))
      (fun j i ↦ wkpBaseCoordinateCLM (partialDerivCLM i (U j))) :=
  ⟨fun i ↦ ⟨lowerOrderCLM (Nat.le_succ k) (U i), wkpBaseCoordinateCLM_lowerOrderCLM _ _⟩,
    fun j i ↦ ⟨partialDerivCLM i (U j), rfl⟩⟩

/-- For the coefficients of a velocity `U`, the projected transport is minus the profile
transport: `Π B v = Π (U·∇v + v·∇U)`. The generator `L₀ - Π B` of the evolution is therefore
`L₀ + profileTransport k U`. -/
theorem leraySobolev_comp_transport (U : Fin 3 → W^{k + 1,∞}(ℝ^3))
    (hk : ProfileCoefficientBounds k (fun i ↦ wkpBaseCoordinateCLM (U i))
      (fun j i ↦ wkpBaseCoordinateCLM (partialDerivCLM i (U j)))) :
    (leraySobolev 3 k).comp hk.transport = -SobolevConvection.profileTransport k U := by
  rw [hk.transport_eq_linearTransport (B := fun i ↦ lowerOrderCLM (Nat.le_succ k) (U i))
    (C := fun j i ↦ partialDerivCLM i (U j)) (fun i ↦ wkpBaseCoordinateCLM_lowerOrderCLM _ _)
    (fun j i ↦ rfl)]
  ext1 v
  simp only [ContinuousLinearMap.comp_apply, neg_apply, neg_neg,
    SobolevConvection.profileTransport_apply, SobolevConvection.profileConvection]

end ProfileCoefficientBounds

/-! ### The semigroup on `Hᵏ` -/

/-- The self-similar evolution around a profile with transport coefficients `b` and stretching
coefficients `c` in `W^{k,∞}`, as a strongly continuous semigroup on vector `Hᵏ`. Its generator
is `L₀ - Π B`, where `B v = Σᵢ bᵢ ∂ᵢ v + c v`. -/
def profileSemigroup (k : ℕ) (b : Fin 3 → DerivLp 3 ∞ Set.univ)
    (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ) (hk : ProfileCoefficientBounds k b c) :
    StronglyContinuousSemigroup (VectorH 3 k) :=
  transportSemigroup hk.transport

/-- The gaining path of the evolution on `Hᵏ`: at positive times it maps `Hᵏ` into `Hᵏ⁺¹`, and
forgetting the gained derivative gives the semigroup. It is zero at nonpositive times. -/
def profileGain (k : ℕ) (b : Fin 3 → DerivLp 3 ∞ Set.univ)
    (c : Fin 3 → Fin 3 → DerivLp 3 ∞ Set.univ) (hk : ProfileCoefficientBounds k b c) (t : ℝ) :
    VectorH 3 k →L[ℝ] VectorH 3 (k + 1) :=
  transportGain hk.transport t

section Order

variable {k : ℕ} (hk : ProfileCoefficientBounds k b c)

/-- The Duhamel formula of the semigroup on `Hᵏ`. The transport loses one derivative, so it acts
on the gaining path in `Hᵏ⁺¹`; the projected free gain returns to `Hᵏ⁺¹`, and the integral is
lowered to `Hᵏ`. -/
theorem profileSemigroup_duhamel (t : ℝ≥0) (u : VectorH 3 k) :
    profileSemigroup k b c hk t u = vectorSelfsimilarHeatSemigroup 3 k t u -
      vectorLower 3 k (∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 k (t - s)
        (hk.transport (profileGain k b c hk s u))) :=
  transportSemigroup_duhamel hk.transport t u

/-- The Duhamel formula of the semigroup in `Hᵏ`, with the projected free evolution as
kernel. -/
theorem profileSemigroup_duhamel_lower (t : ℝ≥0) (u : VectorH 3 k) :
    profileSemigroup k b c hk t u = vectorSelfsimilarHeatSemigroup 3 k t u -
      ∫ s in (0 : ℝ)..t, leraySobolev 3 k (vectorSelfsimilarHeat 3 k (t - s).toNNReal
        (hk.transport (profileGain k b c hk s u))) :=
  transportSemigroup_duhamel_lower hk.transport t u

/-- The gaining path solves the Duhamel equation in `Hᵏ⁺¹`. -/
theorem profileGain_eq {t : ℝ} (ht : 0 < t) (u : VectorH 3 k) :
    profileGain k b c hk t u = vectorSelfsimilarHeatGainKernel 3 k t u -
      ∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 k (t - s)
        (hk.transport (profileGain k b c hk s u)) :=
  transportGain_eq_forwardDuhamel hk.transport ht u

/-- The gaining path is continuous at positive times. -/
theorem continuousOn_profileGain_apply (u : VectorH 3 k) :
    ContinuousOn (fun t ↦ profileGain k b c hk t u) (Ioi 0) :=
  continuousOn_transportGain_apply hk.transport u

/-- The gaining path is the only solution of the `Hᵏ⁺¹` Duhamel equation that is continuous at
positive times and has a singular bound `C t^{-1/2} e^{ω t}`, for any rate `ω`. -/
theorem eq_profileGain_of_duhamel {u : VectorH 3 k} {v : ℝ → VectorH 3 (k + 1)}
    (hvc : ContinuousOn v (Ioi 0)) {C ω : ℝ}
    (hvb : ∀ t, 0 < t → ‖v t‖ ≤ C * t ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t))
    (hv : ∀ t, 0 < t → v t = vectorSelfsimilarHeatGainKernel 3 k t u -
      ∫ s in (0 : ℝ)..t, projectedSelfsimilarHeatGainKernel 3 k (t - s) (hk.transport (v s)))
    {t : ℝ} (ht : 0 < t) : v t = profileGain k b c hk t u :=
  eq_transportGain_of_duhamel hk.transport hvc hvb hv ht

/-- At positive time the semigroup is the gaining path with the gained derivative forgotten. -/
theorem vectorLower_comp_profileGain {t : ℝ≥0} (ht : 0 < t) :
    (vectorLower 3 k).comp (profileGain k b c hk t) = profileSemigroup k b c hk t :=
  vectorLower_comp_transportGain hk.transport ht

/-- The gaining path has the singular bound `C t^{-1/2} e^{ω t}` in operator norm. -/
theorem norm_profileGain_le {t : ℝ} (ht : 0 < t) :
    ‖profileGain k b c hk t‖ ≤ transportGainConstant hk.transport * t ^ (-(1 / 2 : ℝ)) *
      Real.exp (transportWeight hk.transport * t) :=
  norm_transportGain_le hk.transport ht

/-- The semigroup on `Hᵏ` gains one derivative with the bound `C t^{-1/2} e^{ω t}`. The
semigroup maps `Hᵏ` to `Hᵏ`, so its norm into `Hᵏ⁺¹` is stated through a lift: an operator `G`
into `Hᵏ⁺¹` whose lowering is `S(t)`. The lift is unique, since forgetting the top order is
injective, and it is the gaining path `profileGain k b c hk t`. -/
theorem profileSemigroup_exists_gain :
    ∃ C ω : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0, 0 < t →
      ∃ G : VectorH 3 k →L[ℝ] VectorH 3 (k + 1),
        (vectorLower 3 k).comp G = profileSemigroup k b c hk t ∧
          ‖G‖ ≤ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t) :=
  transportSemigroup_exists_gain hk.transport

/-- The semigroup on `Hᵏ` has an exponential bound. -/
theorem profileSemigroup_exists_norm_le :
    ∃ M ω : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, ‖profileSemigroup k b c hk t‖ ≤ M * Real.exp (ω * t) :=
  transportSemigroup_exists_norm_le hk.transport

/-- The semigroup on `Hᵏ` preserves fields fixed by the Leray projection. -/
theorem leraySobolev_profileSemigroup (t : ℝ≥0) {u : VectorH 3 k}
    (hu : leraySobolev 3 k u = u) :
    leraySobolev 3 k (profileSemigroup k b c hk t u) = profileSemigroup k b c hk t u :=
  leraySobolev_transportSemigroup hk.transport t hu

/-- The gaining path of a field fixed by the Leray projection is fixed by the Leray
projection. -/
theorem leraySobolev_profileGain {t : ℝ} (ht : 0 < t) {u : VectorH 3 k}
    (hu : leraySobolev 3 k u = u) :
    leraySobolev 3 (k + 1) (profileGain k b c hk t u) = profileGain k b c hk t u :=
  leraySobolev_transportGain hk.transport ht hu

/-- The gradient part of the evolution is the free evolution: `(1 - Π) S(t) = S₀(t) (1 - Π)`,
since the transport enters the Duhamel formula only through its Leray projection. -/
theorem sub_leraySobolev_profileSemigroup (t : ℝ≥0) (u : VectorH 3 k) :
    profileSemigroup k b c hk t u - leraySobolev 3 k (profileSemigroup k b c hk t u) =
      vectorSelfsimilarHeatSemigroup 3 k t (u - leraySobolev 3 k u) := by
  set f : ℝ → VectorH 3 k := fun s ↦ leraySobolev 3 k (vectorSelfsimilarHeat 3 k (t - s).toNNReal
    (hk.transport (profileGain k b c hk s u)))
  have hf : leraySobolev 3 k (∫ s in (0 : ℝ)..t, f s) = ∫ s in (0 : ℝ)..t, f s := by
    by_cases hint : IntervalIntegrable f volume 0 t
    · rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
      exact intervalIntegral.integral_congr fun s _ ↦ leraySobolev_idempotent _
    · rw [intervalIntegral.integral_undef hint, map_zero]
  rw [profileSemigroup_duhamel_lower hk t u, map_sub, hf, map_sub,
    vectorSelfsimilarHeatSemigroup_apply, vectorSelfsimilarHeatSemigroup_apply,
    leraySobolev_vectorSelfsimilarHeat]
  abel

/-- The action of the gaining path is jointly continuous in the time and the datum at positive
times. -/
theorem continuousOn_profileGain_apply_prod :
    ContinuousOn (fun p : ℝ × VectorH 3 k ↦ profileGain k b c hk p.1 p.2) (Ioi 0 ×ˢ univ) :=
  continuousOn_transportGain_apply_prod hk.transport

/-- Restarting at a positive time: the gaining path at `t + s` is the gaining path at `t` of the
evolved datum. -/
theorem profileGain_add {t : ℝ} (ht : 0 < t) {s : ℝ≥0} (hs : 0 < (s : ℝ)) (u : VectorH 3 k) :
    profileGain k b c hk (t + s) u = profileGain k b c hk t (profileSemigroup k b c hk s u) :=
  transportGain_add hk.transport ht hs u

end Order

/-! ### Compatibility of the orders -/

variable {k : ℕ}

/-- The gaining path on `Hᵏ⁺¹`, with the top order forgotten, is the gaining path on `Hᵏ` of the
datum with the top order forgotten. -/
theorem vectorLower_profileGain (hk : ProfileCoefficientBounds (k + 1) b c)
    (hk' : ProfileCoefficientBounds k b c) {t : ℝ} (ht : 0 < t) (u : VectorH 3 (k + 1)) :
    vectorLower 3 (k + 1) (profileGain (k + 1) b c hk t u) =
      profileGain k b c hk' t (vectorLower 3 k u) :=
  vectorLower_transportGain hk'.transport hk.transport (hk.vectorLower_transport hk') ht u

/-- The semigroup on `Hᵏ⁺¹` is the restriction of the semigroup on `Hᵏ`. -/
theorem profileSemigroup_level_compat (hk : ProfileCoefficientBounds (k + 1) b c)
    (hk' : ProfileCoefficientBounds k b c) (t : ℝ≥0) (u : VectorH 3 (k + 1)) :
    vectorLower 3 k (profileSemigroup (k + 1) b c hk t u) =
      profileSemigroup k b c hk' t (vectorLower 3 k u) :=
  vectorLower_transportSemigroup hk'.transport hk.transport (hk.vectorLower_transport hk') t u

/-- The semigroup on `Hᵏ⁺¹` continues the gaining path from `Hᵏ` at a positive time. -/
theorem profileSemigroup_profileGain (hk : ProfileCoefficientBounds (k + 1) b c)
    (hk' : ProfileCoefficientBounds k b c) (t : ℝ≥0) {s : ℝ} (hs : 0 < s) (u : VectorH 3 k) :
    profileSemigroup (k + 1) b c hk t (profileGain k b c hk' s u) =
      profileGain k b c hk' (t + s) u :=
  transportSemigroup_transportGain hk'.transport hk.transport (hk.vectorLower_transport hk') t hs u

/-- The semigroup on `Hʲ⁺ᵐ` is the restriction of the semigroup on `Hʲ`. -/
theorem vectorLowerOrderCLM_profileSemigroup (j m : ℕ)
    (hk : ProfileCoefficientBounds (j + m) b c) (hj : ProfileCoefficientBounds j b c) (t : ℝ≥0)
    (u : VectorH 3 (j + m)) :
    vectorLowerOrderCLM (Nat.le_add_right j m) (profileSemigroup (j + m) b c hk t u) =
      profileSemigroup j b c hj t (vectorLowerOrderCLM (Nat.le_add_right j m) u) := by
  induction m with
  | zero =>
    exact (vectorLowerOrderCLM_refl_apply _).trans
      (congrArg (profileSemigroup j b c hj t) (vectorLowerOrderCLM_refl_apply u)).symm
  | succ m ih =>
    have hstep : vectorLower 3 (j + m) (profileSemigroup (j + (m + 1)) b c hk t u) =
        profileSemigroup (j + m) b c (hk.of_le (Nat.le_succ _)) t (vectorLower 3 (j + m) u) :=
      profileSemigroup_level_compat (k := j + m) hk (hk.of_le (Nat.le_succ _)) t u
    calc
      _ = vectorLowerOrderCLM (Nat.le_add_right j m)
            (vectorLower 3 (j + m) (profileSemigroup (j + (m + 1)) b c hk t u)) :=
        (vectorLowerOrderCLM_trans_apply (Nat.le_add_right j m) (Nat.le_succ _) _).symm
      _ = profileSemigroup j b c hj t
            (vectorLowerOrderCLM (Nat.le_add_right j m) (vectorLower 3 (j + m) u)) := by
        rw [hstep, ih]
      _ = _ := congrArg (profileSemigroup j b c hj t)
        (vectorLowerOrderCLM_trans_apply (Nat.le_add_right j m) (Nat.le_succ _) u)

/-- Smoothing over several orders: with coefficient bounds of order `j + m`, the semigroup on
`Hʲ` maps into `Hʲ⁺ᵐ` at positive times, with the bound `C t^{-m/2} e^{ω t}`. -/
theorem profileSemigroup_exists_smoothing (j m : ℕ) (hk : ProfileCoefficientBounds (j + m) b c)
    (hj : ProfileCoefficientBounds j b c) :
    ∃ C ω : ℝ, 0 ≤ C ∧ ∀ t : ℝ≥0, 0 < t →
      ∃ G : VectorH 3 j →L[ℝ] VectorH 3 (j + m),
        (vectorLowerOrderCLM (Nat.le_add_right j m)).comp G = profileSemigroup j b c hj t ∧
          ‖G‖ ≤ C * (t : ℝ) ^ (-((m : ℝ) / 2)) * Real.exp (ω * t) := by
  induction m with
  | zero =>
    obtain ⟨M, ω, hM, hbound⟩ := profileSemigroup_exists_norm_le hj
    refine ⟨M, ω, hM, fun t _ ↦ ⟨profileSemigroup j b c hj t, ?_, ?_⟩⟩
    · ext1 v
      exact vectorLowerOrderCLM_refl_apply _
    · simpa using hbound t
  | succ m ih =>
    obtain ⟨C₀, ω₀, hC₀, h₀⟩ := ih (hk.of_le (Nat.le_succ _))
    obtain ⟨C₁, ω₁, hC₁, h₁⟩ :=
      profileSemigroup_exists_gain (k := j + m) (hk.of_le (Nat.le_succ (j + m)))
    refine ⟨C₁ * C₀ * 2 ^ (((m : ℝ) + 1) / 2), (ω₁ + ω₀) / 2, by positivity, fun t ht ↦ ?_⟩
    have ht2 : 0 < t / 2 := half_pos ht
    obtain ⟨G₀, hG₀, hG₀b⟩ := h₀ (t / 2) ht2
    obtain ⟨G₁, hG₁, hG₁b⟩ := h₁ (t / 2) ht2
    refine ⟨G₁.comp G₀, ?_, ?_⟩
    · ext1 v
      have h1 := congrArg (fun L ↦ L (G₀ v)) hG₁
      have h0 := congrArg (fun L ↦ L v) hG₀
      simp only [ContinuousLinearMap.comp_apply] at h1 h0 ⊢
      calc
        _ = vectorLowerOrderCLM (Nat.le_add_right j m) (vectorLower 3 (j + m) (G₁ (G₀ v))) :=
          (vectorLowerOrderCLM_trans_apply (Nat.le_add_right j m) (Nat.le_succ _) _).symm
        _ = _ := by
          rw [h1, vectorLowerOrderCLM_profileSemigroup j m _ hj, h0,
            ← StronglyContinuousSemigroup.map_add_apply, add_halves]
    · have hx : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := ht2
      have hxe : ((t / 2 : ℝ≥0) : ℝ) = (t : ℝ) / 2 := by
        rw [NNReal.coe_div, NNReal.coe_ofNat]
      have hpow : ((t / 2 : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((t / 2 : ℝ≥0) : ℝ) ^ (-((m : ℝ) / 2)) =
            2 ^ (((m : ℝ) + 1) / 2) * (t : ℝ) ^ (-(((m + 1 : ℕ) : ℝ) / 2)) := by
        rw [← Real.rpow_add hx, hxe, Real.div_rpow (NNReal.coe_nonneg t) zero_le_two,
          show -(1 / 2 : ℝ) + -((m : ℝ) / 2) = -(((m + 1 : ℕ) : ℝ) / 2) by push_cast; ring,
          Real.rpow_neg zero_le_two, div_inv_eq_mul,
          show (((m + 1 : ℕ) : ℝ) / 2) = ((m : ℝ) + 1) / 2 by push_cast; ring]
        ring
      have hexp : Real.exp (ω₁ * ((t / 2 : ℝ≥0) : ℝ)) * Real.exp (ω₀ * ((t / 2 : ℝ≥0) : ℝ)) =
          Real.exp ((ω₁ + ω₀) / 2 * t) := by
        rw [← Real.exp_add, hxe]
        ring_nf
      calc
        ‖G₁.comp G₀‖ ≤ ‖G₁‖ * ‖G₀‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (C₁ * ((t / 2 : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (ω₁ * ((t / 2 : ℝ≥0) : ℝ))) *
            (C₀ * ((t / 2 : ℝ≥0) : ℝ) ^ (-((m : ℝ) / 2)) *
              Real.exp (ω₀ * ((t / 2 : ℝ≥0) : ℝ))) :=
          mul_le_mul hG₁b hG₀b (ContinuousLinearMap.opNorm_nonneg G₀) (by positivity)
        _ = C₁ * C₀ * (((t / 2 : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((t / 2 : ℝ≥0) : ℝ) ^ (-((m : ℝ) / 2))) *
            (Real.exp (ω₁ * ((t / 2 : ℝ≥0) : ℝ)) * Real.exp (ω₀ * ((t / 2 : ℝ≥0) : ℝ))) := by
          ring
        _ = _ := by
          rw [hpow, hexp]
          ring

/-- At order zero the gaining path is the gaining path of the evolution on `L²` with bounded
coefficients. -/
theorem profileGain_zero (hk : ProfileCoefficientBounds 0 b c) {t : ℝ} :
    profileGain 0 b c hk t = profileGain0 b c t := by
  rw [profileGain, hk.transport_zero]
  rfl

/-- At order zero the semigroup is the semigroup on `L²` with bounded coefficients. -/
theorem profileSemigroup_zero (hk : ProfileCoefficientBounds 0 b c) :
    profileSemigroup 0 b c hk = profileSemigroup0 b c hk := by
  rw [profileSemigroup, hk.transport_zero]
  rfl

end NavierStokes.Selfsimilar
