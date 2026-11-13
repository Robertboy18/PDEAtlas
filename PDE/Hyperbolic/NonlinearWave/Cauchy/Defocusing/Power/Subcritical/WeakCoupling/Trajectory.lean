/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalFreeField
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalIntegral
import CAS.ExactTactic

/-!
# Weak coupling on physical backward cones

The parameter in the cone contraction can be scaled independently of physical
time. The resulting family is jointly C¹ in the coupling parameter and spacetime.
Its full physical first derivative converges locally uniformly to that of the
free field when the coupling tends to zero. The free input may itself depend
C¹ on the parameter.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A family whose joint map is continuous at every `(0, p)` converges locally uniformly to its
slice at zero. -/
private theorem tendstoLocallyUniformly_zero {Y : Type*} [UniformSpace Y]
    {F : ℝ → ℝ × ℝ^3 → Y} (hF : ∀ p, ContinuousAt (Function.uncurry F) (0, p)) :
    TendstoLocallyUniformly F (F 0) (𝓝 0) :=
  tendstoLocallyUniformly_iff_forall_tendsto.mpr fun p ↦ by
    rw [← nhds_prod_eq]
    exact (((hF p).comp_of_eq (continuousAt_const.prodMk continuousAt_snd) rfl).prodMk
      (hF p)).tendsto.mono_right (nhds_le_uniformity _)

/-- A globally Lipschitz C¹ reaction constructs a jointly C¹ family with
coupling `κ²`. Both the field and its physical derivative converge locally
uniformly to the free input at parameter zero, allowing a C¹ family of inputs. -/
theorem exists_weakCoupling_cone_trajectory_of_lipschitz {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {C : NNReal} (hLip : LipschitzWith C f) :
    ∃ T : ℝ, 0 < T ∧
      ∀ H : ℝ × (ℝ × ℝ^3) → ℝ, ContDiff ℝ 1 H → ∃ v a : ℝ → (ℝ × ℝ^3) → ℝ,
        ContDiffOn ℝ 1 (Function.uncurry v) {z | |z.1 * z.2.1| < T} ∧
      ContDiffOn ℝ 1 (Function.uncurry a) {z | |z.1 * z.2.1| < T} ∧
      (∀ κ p, |κ * p.1| < T → v κ p = H (κ, p) + (κ * p.1) ^ 2 * a κ p) ∧
      (∀ κ p, |κ * p.1| < T → a κ p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        f (v κ (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      (∀ B : ℝ, 0 ≤ B → (∀ z, |f z| ≤ B) → ∀ κ p, |κ * p.1| < T → |a κ p| ≤ ‖duhamelOperator‖ * B) ∧
      TendstoLocallyUniformly v (fun p ↦ H (0, p)) (𝓝 0) ∧
      TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p) (fderiv ℝ (fun p ↦ H (0, p))) (𝓝 0) := by
  let N := composeCompact (α := Cone) ⟨f, hf.continuous⟩
  have hNLip : LipschitzWith C N := by
    convert BoundedContinuousFunction.lipschitz_comp (α := Cone) hLip using 1
    ext w q
    rfl
  obtain ⟨T, hT, ψ, hψreg, hψeq, hψunique⟩ :=
    exists_integral_solution_arbitrary_input duhamelOperator (contDiff_composeCompact hf) hNLip
  refine ⟨T, hT, fun H hH ↦ ?_⟩
  let Hκ : ℝ → C(ℝ × ℝ^3, ℝ) := fun κ ↦
    ⟨fun p ↦ H (κ, p), hH.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let coordinates : Cone →ᵇ (ℝ × (ℝ × ℝ^3)) :=
    mkOfCompact ⟨fun q ↦ (0, q.val), continuous_const.prodMk continuous_subtype_val⟩
  let B : ℝ × (ℝ × ℝ^3) → Cone →ᵇ (ℝ × (ℝ × ℝ^3)) := fun z ↦
    constCLM Cone ℝ (ℝ × (ℝ × ℝ^3)) (z.1, (0, z.2.2)) + z.2.1 • coordinates
  have hB : ContDiff ℝ 1 B :=
    ((constCLM Cone ℝ (ℝ × (ℝ × ℝ^3))).contDiff.comp
      (contDiff_fst.prodMk (contDiff_const.prodMk contDiff_snd.snd))).add
      (contDiff_snd.fst.smul contDiff_const)
  have hcone : ContDiff ℝ 1 (fun z : ℝ × (ℝ × ℝ^3) ↦ coneField (Hκ z.1) z.2) := by
    have he : (fun z : ℝ × (ℝ × ℝ^3) ↦ coneField (Hκ z.1) z.2) =
        composeCompact ⟨H, hH.continuous⟩ ∘ B := by
      funext z
      ext q
      simp only [Function.comp_apply, coneField_apply, composeCompact_apply,
        B, BoundedContinuousFunction.add_apply, constCLM_apply, const_apply,
        BoundedContinuousFunction.smul_apply, coordinates, mkOfCompact_apply]
      change H (z.1, physicalPoint z.2 q) = H ((z.1, (0, z.2.2)) + z.2.1 • (0, q.val))
      congr 1
      ext <;> simp [physicalPoint, coneTime, coneSpace]
    rw [he]
    exact (contDiff_composeCompact hH).comp hB
  let A : ℝ × (ℝ × ℝ^3) → ℝ × (Cone →ᵇ ℝ) :=
    fun z ↦ (z.1 * z.2.1, coneField (Hκ z.1) z.2)
  have hrestrict {κ : ℝ} {p : ℝ × ℝ^3} (hp : |κ * p.1| < T) (q : Cone) :
      ψ (A (κ, physicalPoint p q)) = restrictCone q (ψ (A (κ, p))) := by
    have hsmall : |κ * (physicalPoint p q).1| < T := by
      change |κ * (p.1 * coneTime q)| < T
      rw [← mul_assoc, abs_mul, abs_of_nonneg (coneTime_mem q).1]
      exact (mul_le_mul_of_nonneg_left (coneTime_mem q).2 (abs_nonneg _)).trans_lt
        (by simpa using hp)
    apply hψunique _ hsmall
    have he := hψeq (A (κ, p)) hp
    change ψ (A (κ, p)) = coneField (Hκ κ) p +
      (κ * p.1) ^ 2 • duhamelOperator (N (ψ (A (κ, p)))) at he
    calc
      restrictCone q (ψ (A (κ, p))) =
          restrictCone q (coneField (Hκ κ) p) +
            (κ * p.1) ^ 2 • restrictCone q (duhamelOperator (N (ψ (A (κ, p))))) := by
        conv_lhs => rw [he]
        rw [map_add, map_smul]
      _ = (A (κ, physicalPoint p q)).2 + (A (κ, physicalPoint p q)).1 ^ 2 •
          duhamelOperator (N (restrictCone q (ψ (A (κ, p))))) := by
        rw [restrictCone_coneField]
        apply congrArg (fun w ↦ coneField (Hκ κ) (physicalPoint p q) + w)
        have hN : restrictCone q (N (ψ (A (κ, p)))) =
            N (restrictCone q (ψ (A (κ, p)))) := by
          ext z
          rfl
        ext z
        simp only [BoundedContinuousFunction.smul_apply, restrictCone_apply,
          duhamelOperator_descend, hN, smul_eq_mul]
        change (κ * p.1) ^ 2 * (coneTime q ^ 2 * _) = (κ * (p.1 * coneTime q)) ^ 2 * _
        cas
  let v : ℝ → (ℝ × ℝ^3) → ℝ := fun κ p ↦ ψ (A (κ, p)) vertex
  have hv {κ : ℝ} {p : ℝ × ℝ^3} (hp : |κ * p.1| < T) (q : Cone) :
      v κ (physicalPoint p q) = ψ (A (κ, p)) q := by
    dsimp only [v]
    rw [hrestrict hp q, restrictCone_apply, descend_vertex_right]
  let a : ℝ → (ℝ × ℝ^3) → ℝ := fun κ p ↦ duhamelOperator (N (ψ (A (κ, p)))) vertex
  have hAc : ContDiff ℝ 1 A :=
    (contDiff_fst.mul contDiff_snd.fst).prodMk hcone
  have hw := hψreg.comp hAc.contDiffOn (fun _ hp ↦ hp)
  have ha := duhamelOperator.contDiff.comp_contDiffOn
    ((contDiff_composeCompact hf).comp_contDiffOn hw)
  have hvc : ContDiffOn ℝ 1 (Function.uncurry v) {z | |z.1 * z.2.1| < T} :=
    (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn hw
  have heq (κ : ℝ) (p : ℝ × ℝ^3) (hp : |κ * p.1| < T) :
      v κ p = H (κ, p) + (κ * p.1) ^ 2 * a κ p := by
    have he := congrArg (fun w : Cone →ᵇ ℝ ↦ w vertex) (hψeq (A (κ, p)) hp)
    change v κ p = coneField (Hκ κ) p vertex + (κ * p.1) ^ 2 * a κ p at he
    simpa only [coneField_apply, physicalPoint, vertex, coneTime, coneSpace,
      mul_one, smul_zero, add_zero, Hκ, ContinuousMap.coe_mk] using he
  have hzero : v 0 = fun p ↦ H (0, p) := by
    funext p
    simpa using heq 0 p (by simpa using hT)
  have hopen : IsOpen {z : ℝ × (ℝ × ℝ^3) | |z.1 * z.2.1| < T} :=
    isOpen_lt (continuous_fst.mul continuous_snd.fst).abs continuous_const
  have hnear (p : ℝ × ℝ^3) := hopen.mem_nhds (x := (0, p)) (by simpa using hT)
  refine ⟨v, a, hvc, ?_, heq, ?_, ?_, ?_, ?_⟩
  · exact (evalCLM ℝ vertex : (Cone →ᵇ ℝ) →L[ℝ] ℝ).contDiff.comp_contDiffOn ha
  · intro κ p hp
    change duhamelOperator (N (ψ (A (κ, p)))) vertex = _
    rw [duhamelOperator_apply]
    simp only [N, composeCompact_apply, descend_vertex_left]
    simp only [vertex, coneTime, one_pow, one_mul]
    congr 1 with s
    congr 3 with ω
    exact congrArg f (hv hp (rim s ω)).symm
  · intro B hB hbound κ p _
    have hn : ‖N (ψ (A (κ, p)))‖ ≤ B :=
      (BoundedContinuousFunction.norm_le hB).mpr fun q ↦ hbound (ψ (A (κ, p)) q)
    exact (duhamelOperator (N (ψ (A (κ, p))))).norm_coe_le_norm vertex |>.trans
      ((duhamelOperator.le_opNorm _).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg _)))
  · rw [← hzero]
    exact tendstoLocallyUniformly_zero fun p ↦ (hvc.contDiffAt (hnear p)).continuousAt
  · rw [← hzero]
    refine tendstoLocallyUniformly_zero (F := fun κ p ↦ fderiv ℝ (v κ) p) fun p ↦ ?_
    refine (((hvc.contDiffAt (hnear p)).continuousAt_fderiv one_ne_zero).clm_comp
      (continuousAt_const (y := .inr ℝ ℝ (ℝ × ℝ^3)))).congr_of_eventuallyEq ?_
    filter_upwards [hnear p] with z hz
    exact (((hvc.contDiffAt (hopen.mem_nhds hz)).differentiableAt one_ne_zero).hasFDerivAt.comp
      z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
