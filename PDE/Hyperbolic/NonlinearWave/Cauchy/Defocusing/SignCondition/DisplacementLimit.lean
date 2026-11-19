/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Compactness

/-!
# Displacement limits of sign-preserving energy waves

The energy equation supplies the common L² time modulus used in local
compactness. Weak convergence retains this modulus, the initial displacement,
and the global gradient bound. The full H¹ bound grows with time, as required
for a massless equation on the whole space.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Topology InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert Distributions

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- Convergence of all Hilbert pairings gives convergence in the weak topology. -/
theorem tendsto_weakSpace_of_tendsto_inner {H ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {l : Filter ι} {v : ι → H} {w : H}
    (hv : ∀ z, Tendsto (fun i ↦ inner ℝ z (v i)) l (𝓝 (inner ℝ z w))) :
    Tendsto (fun i ↦ toWeakSpace ℝ H (v i)) l (𝓝 (toWeakSpace ℝ H w)) := by
  have hinj : Function.Injective (topDualPairing ℝ H).flip := by
    intro x y h
    apply ext_inner_left ℝ
    intro z
    exact DFunLike.congr_fun h (innerSL ℝ z)
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
  intro ell
  change Tendsto (fun i ↦ ell (v i)) l (𝓝 (ell w))
  simpa only [InnerProductSpace.toDual_symm_apply] using
    hv ((InnerProductSpace.toDual ℝ H).symm ell)

/-- Pointwise weak limits preserve a common Lipschitz constant. -/
theorem lipschitzWith_of_tendsto_weak {X E ι : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {l : Filter ι} [l.NeBot] {v : ι → X → E} {w : X → E} {C : NNReal}
    (hv : ∀ i, LipschitzWith C (v i))
    (hw : ∀ x, Tendsto (fun i ↦ toWeakSpace ℝ E (v i x)) l (𝓝 (toWeakSpace ℝ E (w x)))) :
    LipschitzWith C w := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hlim := (hw x).sub (hw y)
  have hb : ∀ᶠ i in l, ‖v i x - v i y‖ ≤ C * dist x y :=
    Eventually.of_forall fun i ↦ by simpa only [dist_eq_norm] using (hv i).dist_le_mul x y
  simpa only [← map_sub, LinearEquiv.symm_apply_apply, dist_eq_norm] using
    PDE.Analysis.WeakCompactness.norm_le_of_tendsto_of_norm_le hlim hb

/-- Positive symmetric continuous bilinear energies are weakly lower semicontinuous,
expressed as preservation of an eventual energy bound. -/
theorem bilinear_self_le_of_tendsto_weak {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} [l.NeBot] (B : E →L[ℝ] StrongDual ℝ E) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x) {v : ι → E} {w : E} {C : ℝ}
    (hv : Tendsto (fun i ↦ toWeakSpace ℝ E (v i)) l (𝓝 (toWeakSpace ℝ E w)))
    (hb : ∀ᶠ i in l, B (v i) (v i) ≤ C) :
    B w w ≤ C := by
  have hp : Tendsto (fun i ↦ 2 * B w (v i)) l (𝓝 (2 * B w w)) := by
    simpa only [LinearEquiv.symm_apply_apply] using
      (PDE.Analysis.WeakCompactness.tendsto_evaluation hv (B w)).const_mul 2
  have hbound : ∀ᶠ i in l, 2 * B w (v i) ≤ C + B w w := by
    filter_upwards [hb] with i hi
    have h := hpos (v i - w)
    simp only [map_sub, sub_apply, hsym (v i) w] at h
    linarith
  have h := le_of_tendsto hp hbound
  linarith

/-- Sign-preserving energy waves with a common physical-energy bound have
one displacement limit. It attains the initial H¹ datum, is weakly continuous in
H¹ and Lipschitz in L², and obeys a global homogeneous gradient bound. Every
compact spatial observation converges strongly and uniformly on finite windows. -/
theorem exists_energy_displacement_limit {n : ℕ} {g : ℕ → ℝ → ℝ} {K : ℕ → NNReal}
    (hg : ∀ i, LipschitzWith (K i) (g i)) (hg0 : ∀ i, g i 0 = 0) (hs : ∀ i z, 0 ≤ z * g i z)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) (u : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ))
    (hu : ∀ i, Cauchy.IsEnergySolution (hg i) (hg0 i) x (u i)) {E : ℝ}
    (he : ∀ i t, 0 ≤ t → physicalEnergy (g i) (u i t) ≤ E) :
    ∃ q : Ici (0 : ℝ) → H¹(ℝ^n), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      q ⟨0, le_rfl⟩ = x.1 ∧
      Continuous (fun t ↦ toWeakSpace ℝ H¹(ℝ^n) (q t)) ∧
      LipschitzWith ⟨Real.sqrt (2 * E), Real.sqrt_nonneg _⟩
        (fun t ↦ (energyTriple n).inclusion (q t)) ∧
      (∀ t, ‖q t‖ ≤ ‖(energyTriple n).inclusion x.1‖ +
        (t.val + 1) * Real.sqrt (2 * E)) ∧
      (∀ t, gradientForm n (q t) (q t) ≤ 2 * E) ∧
      (∀ k : ℕ, ∀ v : H¹(ℝ^n), TendstoUniformly
        (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ inner ℝ v (u (φ i) t).1)
        (fun t : Icc (0 : ℝ) (k : ℝ) ↦ inner ℝ v (q ⟨t.val, t.property.1⟩)) atTop) ∧
      ∀ k : ℕ, ∀ χ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ),
        let A := (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := univ)).comp
          (cutoffCLM (n := n) (p := 2) (Ω := univ) χ)
        TendstoUniformly (fun i (t : Icc (0 : ℝ) (k : ℝ)) ↦ A (u (φ i) t).1)
          (fun t : Icc (0 : ℝ) (k : ℝ) ↦ A (q ⟨t.val, t.property.1⟩)) atTop := by
  let J := (energyTriple n).inclusion
  let C : NNReal := ⟨Real.sqrt (2 * E), Real.sqrt_nonneg _⟩
  let M (k : ℕ) := ‖J x.1‖ + ((k : ℝ) + 1) * Real.sqrt (2 * E)
  let qSeq (i : ℕ) : C(ℝ, H¹(ℝ^n)) := ⟨fun t ↦ (u i t).1, (u i).continuous.fst⟩
  have hN (i : ℕ) : (lipschitzNonlinearity (hg i) (hs i)).IsEnergySolution x (u i) :=
    (isEnergySolution_lipschitzNonlinearity_iff (hg i) (hs i) x (u i)).mpr (hu i)
  have hv (i : ℕ) (t : ℝ) (ht : 0 ≤ t) : ‖(u i t).2‖ ≤ C :=
    norm_velocity_le_of_energy_le (hg i) (hs i) (he i t ht)
  have hnorm (i : ℕ) (t : ℝ) (ht : 0 ≤ t) : ‖(u i t).1‖ ≤
      ‖J x.1‖ + (t + 1) * Real.sqrt (2 * E) := by
    have hbase := norm_displacement_le (hN i) (hv i) ht
    have hb := (lipschitzNonlinearity (hg i) (hs i)).norm_state_le (u i t)
      (add_nonneg (norm_nonneg (J x.1)) (mul_nonneg ht (Real.sqrt_nonneg _))) hbase
    have hsq := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (he i t ht)
      (by norm_num : (0 : ℝ) ≤ 2))
    have hp := norm_fst_le (u i t)
    change ‖u i t‖ ≤ ‖J x.1‖ + t * Real.sqrt (2 * E) +
      Real.sqrt (2 * physicalEnergy (g i) (u i t)) at hb
    linarith
  have hbound (i k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (k : ℝ)) : ‖qSeq i t‖ ≤ M k :=
    (hnorm i t ht.1).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (add_le_add ht.2 le_rfl) (Real.sqrt_nonneg _)))
  have hlip (i : ℕ) : LipschitzOnWith C (fun t ↦ J (qSeq i t)) (Ici 0) :=
    lipschitzOnWith_displacement (hN i) (hv i)
  obtain ⟨q, φ, hφ, _, hc, hp, hcut⟩ := exists_displacement_subsequence qSeq M C hbound hlip
  have hweak (t : Ici (0 : ℝ)) : Tendsto (fun i ↦ toWeakSpace ℝ H¹(ℝ^n) (u (φ i) t).1) atTop
      (𝓝 (toWeakSpace ℝ H¹(ℝ^n) (q t))) := by
    obtain ⟨k, hk⟩ := exists_nat_gt t.val
    exact tendsto_weakSpace_of_tendsto_inner fun v ↦ (hp k v).tendsto_at ⟨t.val, t.property, hk.le⟩
  refine ⟨q, φ, hφ, ?_, hc, ?_, ?_, ?_, hp, hcut⟩
  · apply ext_inner_left ℝ
    intro v
    have h := (hp 0 v).tendsto_at ⟨0, le_rfl, by norm_num⟩
    have hzero (i : ℕ) : (u (φ i) 0).1 = x.1 := congrArg Prod.fst (hu (φ i)).initial
    change Tendsto (fun i ↦ inner ℝ v (u (φ i) 0).1) atTop (𝓝 (inner ℝ v (q ⟨0, le_rfl⟩))) at h
    simp only [hzero] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · apply lipschitzWith_of_tendsto_weak (l := (atTop : Filter ℕ)) (fun i ↦ (hlip (φ i)).to_restrict)
    intro t
    exact (WeakSpace.map J).continuous.continuousAt.tendsto.comp (hweak t)
  · intro t
    simpa only [LinearEquiv.symm_apply_apply] using
      PDE.Analysis.WeakCompactness.norm_le_of_tendsto_of_norm_le (hweak t)
        (Eventually.of_forall fun i ↦ hnorm (φ i) t t.property)
  · intro t
    have hsym (v w : H¹(ℝ^n)) : gradientForm n v w = gradientForm n w v := by
      change inner ℝ v w - inner ℝ (J v) (J w) = inner ℝ w v - inner ℝ (J w) (J v)
      rw [real_inner_comm v w, real_inner_comm (J v) (J w)]
    apply bilinear_self_le_of_tendsto_weak (gradientForm n) hsym
      General.Nonlinearity.gradientForm_nonneg (hweak t)
    filter_upwards with i
    have h := (lipschitzNonlinearity (hg (φ i)) (hs (φ i))).gradient_velocity_le_energy (u (φ i) t)
    have he' := he (φ i) t t.property
    change gradientForm n (u (φ i) t).1 (u (φ i) t).1 + ‖(u (φ i) t).2‖ ^ 2 ≤
        2 * physicalEnergy (g (φ i)) (u (φ i) t) at h
    linarith [sq_nonneg ‖(u (φ i) t).2‖]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
