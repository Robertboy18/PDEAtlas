/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.ProfileScalingSobolev

/-!
# Dilations of an unstable profile in every Sobolev space

The profile `Ũ` is not square integrable, but its dilations `a Ũ(a ·)` differ from it by the
square-integrable field `∫₁ᵃ (Ũ + ξ·∇Ũ)(b ·) db`. In every `Hᴺ` this is the integral
`profileIncrement D N a` of the dilated scaling field `D.dilatedScaling N b`, a continuous path
of dilations of `2 Π ((Ũ·∇)Ũ - ΔŨ)`, so it is differentiable in `a > 0`
(`UnstableProfile.hasDerivAt_profileIncrement`), and it is the smooth field `a Ũ(a ·) - Ũ`
(`UnstableProfile.profileIncrement_eq`).

An `L²`-valued interval integral of a continuous path of classes of a jointly continuous
function is the class of the pointwise integral (`coeFn_intervalIntegral_ae`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open IncompressibleFlow HeatEquation.WholeSpace
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- **Interval integrals of `L²` paths.** If a continuous path `h` in `L²(ℝ³)` has classes
`f μ` with `f` jointly continuous, its interval integral is the class of
`x ↦ ∫ μ in a..b, f μ x`. -/
theorem coeFn_intervalIntegral_ae {ν : Measure (ℝ^3)} (hν : ν = volume) {a b : ℝ} (hab : a ≤ b)
    {h : ℝ → Lp ℝ 2 ν} (hh : ContinuousOn h (Icc a b))
    {f : ℝ → ℝ^3 → ℝ} (hf : Continuous (Function.uncurry f))
    (hae : ∀ μ ∈ Icc a b, (h μ : ℝ^3 → ℝ) =ᵐ[ν] f μ) :
    ((∫ μ in a..b, h μ : Lp ℝ 2 ν) : ℝ^3 → ℝ) =ᵐ[ν] fun x ↦ ∫ μ in a..b, f μ x := by
  subst hν
  have hcont : Continuous fun x ↦ ∫ μ in a..b, f μ x := by
    have hf' : Continuous (Function.uncurry fun (x : ℝ^3) (μ : ℝ) ↦ f μ x) :=
      hf.comp continuous_swap
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (a₀ := a) hf' continuous_const
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    hcont.locallyIntegrable fun g hg hgc ↦ ?_
  have hG := hg.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hgc
  set G := hG.toLp g
  have hpair (F : Lp ℝ 2 (volume : Measure (ℝ^3))) :
      ∫ x, g x • (F : ℝ^3 → ℝ) x = inner ℝ G F := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hG.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hint : IntervalIntegrable h volume a b :=
    (hh.mono (by rw [uIcc_of_le hab])).intervalIntegrable
  rw [hpair, ← innerSL_apply_apply ℝ G, ← (innerSL ℝ G).intervalIntegral_comp_comm hint]
  have hinner : ∀ μ ∈ uIcc a b, innerSL ℝ G (h μ) = ∫ x, g x * f μ x := fun μ hμ ↦ by
    rw [uIcc_of_le hab] at hμ
    rw [innerSL_apply_apply, ← hpair]
    refine integral_congr_ae ?_
    filter_upwards [hae μ hμ] with x hx
    rw [hx, smul_eq_mul]
  rw [intervalIntegral.integral_congr hinner]
  -- Fubini on `Ioc a b × ℝ³`
  have hF : Continuous (Function.uncurry fun (μ : ℝ) (x : ℝ^3) ↦ g x * f μ x) :=
    (hg.continuous.comp continuous_snd).mul hf
  have hK : IsCompact (Icc a b ×ˢ tsupport g) := isCompact_Icc.prod hgc
  have hon : IntegrableOn (Function.uncurry fun (μ : ℝ) (x : ℝ^3) ↦ g x * f μ x)
      (Ioc a b ×ˢ univ) (volume.prod volume) := by
    refine (hF.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
      (measurableSet_Ioc.prod MeasurableSet.univ) fun p hp ↦ ?_
    have hp2 : p.2 ∉ tsupport g := fun h2 ↦ hp.2 ⟨Ioc_subset_Icc_self hp.1.1, h2⟩
    change g p.2 * f p.1 p.2 = 0
    rw [image_eq_zero_of_notMem_tsupport hp2, zero_mul]
  have hprod : Integrable (Function.uncurry fun (μ : ℝ) (x : ℝ^3) ↦ g x * f μ x)
      ((volume.restrict (Ioc a b)).prod volume) := by
    have hr := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (ℝ^3)))
      (Ioc a b) univ
    rw [Measure.restrict_univ] at hr
    rw [hr]
    exact hon
  rw [intervalIntegral.integral_of_le hab, integral_integral_swap hprod]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_of_le hab, integral_const_mul]

namespace UnstableProfile

variable (D : UnstableProfile)

/-- The dilated scaling field `(Ũ + ξ·∇Ũ)(b ·)` in vector `Hᴺ` (zero at `b = 0`). -/
def dilatedScaling (N : ℕ) (b : ℝ) : VectorH 3 N :=
  if h : b = 0 then 0 else vectorDilation 3 N b h (D.profileScalingSobolev N)

/-- The dilated scaling field away from `b = 0`. -/
theorem dilatedScaling_of_ne (N : ℕ) {b : ℝ} (hb : b ≠ 0) :
    D.dilatedScaling N b = vectorDilation 3 N b hb (D.profileScalingSobolev N) := by
  simp [dilatedScaling, hb]

/-- The dilated scaling field is continuous in the factor `b > 0`. -/
theorem continuousOn_dilatedScaling (N : ℕ) : ContinuousOn (D.dilatedScaling N) (Ioi 0) := by
  intro b hb
  have hb' : (0 : ℝ) < b := hb
  have hδ : (0 : ℝ) < b / 2 := by linarith
  have hc := continuous_vectorDilation_Ici (n := 3) (k := N) hδ
  have hpath : Continuous (fun c : ℝ ↦ (D.profileScalingSobolev N,
      (⟨max c (b / 2), le_max_right _ _⟩ : Ici (b / 2)))) :=
    continuous_const.prodMk ((continuous_id.max continuous_const).subtype_mk _)
  have h2 := (hc.comp hpath).continuousAt (x := b)
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [Ioi_mem_nhds (by linarith : b / 2 < b)] with c hc'
  have hcpos : 0 < c := lt_trans hδ hc'
  have hm : max c (b / 2) = c := max_eq_left hc'.le
  simp only [Function.comp_apply]
  rw [D.dilatedScaling_of_ne N hcpos.ne']
  exact congrFun (congrArg DFunLike.coe (vectorDilation_congr hm _ _)) _

/-- The increment `∫₁ᵃ (Ũ + ξ·∇Ũ)(b ·) db` of the dilations of the profile in vector `Hᴺ`. -/
def profileIncrement (N : ℕ) (a : ℝ) : VectorH 3 N :=
  ∫ b in (1 : ℝ)..a, D.dilatedScaling N b

/-- The interval between `1` and `a > 0` is positive. -/
theorem uIcc_one_subset_Ioi {a : ℝ} (ha : 0 < a) : uIcc 1 a ⊆ Ioi 0 := fun _ hx ↦
  lt_of_lt_of_le (lt_min one_pos ha) hx.1

/-- The increment is differentiable in `a > 0`, with the dilated scaling field as
derivative. -/
theorem hasDerivAt_profileIncrement (N : ℕ) {a : ℝ} (ha : 0 < a) :
    HasDerivAt (D.profileIncrement N) (D.dilatedScaling N a) a := by
  have hc := D.continuousOn_dilatedScaling N
  have _ : SecondCountableTopologyEither ℝ (VectorH 3 N) :=
    secondCountableTopologyEither_of_left ℝ _
  exact intervalIntegral.integral_hasDerivAt_right
    ((hc.mono (uIcc_one_subset_Ioi ha)).intervalIntegrable)
    (hc.stronglyMeasurableAtFilter isOpen_Ioi a ha) (hc.continuousAt (Ioi_mem_nhds ha))

/-- The components of the dilated scaling field. -/
theorem baseRepresentative_dilatedScaling_ae (N : ℕ) {b : ℝ} (hb : b ≠ 0) (j : Fin 3) :
    baseRepresentative (D.dilatedScaling N b j) =ᵐ[volume]
      fun x ↦ SpectralProfile.velocityDrift D.U (b • x) j := by
  rw [D.dilatedScaling_of_ne N hb, vectorDilation_apply]
  have h₁ := dilationWkpCLM_base_ae (by norm_num) b hb (D.profileScalingSobolev N j)
  have h₂ := (Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) hb).ae_eq_comp
    (D.baseRepresentative_profileScalingSobolev_ae N j)
  simp only [domainMeasure, Measure.restrict_univ] at h₁
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  rw [hx₁]
  exact hx₂

/-- The scaling field is continuous. -/
theorem continuous_velocityDrift : Continuous (SpectralProfile.velocityDrift D.U) :=
  D.contDiff_U.continuous.add
    ((contDiff_fderiv_of_top D.contDiff_U).continuous.clm_apply continuous_id)

/-- Pointwise, the increment of the dilations is the integral of the dilated scaling field. -/
theorem integral_velocityDrift_smul (a : ℝ) (x : ℝ^3) (j : Fin 3) :
    ∫ b in (1 : ℝ)..a, SpectralProfile.velocityDrift D.U (b • x) j =
      (dilateField a D.U x - D.U x) j := by
  have hd : ∀ b ∈ uIcc (1 : ℝ) a, HasDerivAt (fun c ↦ (dilateField c D.U x) j)
      (SpectralProfile.velocityDrift D.U (b • x) j) b := fun b _ ↦
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt b
      (hasDerivAt_dilateField_apply D.contDiff_U b x)
  have hi : IntervalIntegrable (fun b ↦ SpectralProfile.velocityDrift D.U (b • x) j) volume 1 a :=
    (((EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp
      (D.continuous_velocityDrift.comp (continuous_id.smul continuous_const))).intervalIntegrable
        _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp [dilateField]

/-- The base coordinate of the component `j`, as a map to `L²`. -/
def baseComponentCLM (N : ℕ) (j : Fin 3) : VectorH 3 N →L[ℝ] DerivLp 3 2 univ :=
  (wkpBaseCoordinateCLM (n := 3) (m := N) (p := 2) (Ω := univ)).comp (PiLp.proj 2 _ j)

theorem coeFn_baseComponentCLM (N : ℕ) (j : Fin 3) (u : VectorH 3 N) :
    (baseComponentCLM N j u : ℝ^3 → ℝ) = baseRepresentative (u j) := by
  simp only [baseComponentCLM, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    wkpBaseCoordinateCLM_apply]
  rfl

/-- **The increment is `a Ũ(a ·) - Ũ`.** -/
theorem baseRepresentative_profileIncrement_ae (N : ℕ) {a : ℝ} (ha : 0 < a) (j : Fin 3) :
    baseRepresentative (D.profileIncrement N a j) =ᵐ[volume]
      fun x ↦ (dilateField a D.U x - D.U x) j := by
  set T := baseComponentCLM N j
  set f : ℝ → ℝ^3 → ℝ := fun b x ↦ SpectralProfile.velocityDrift D.U (b • x) j with hfdef
  have hf : Continuous (Function.uncurry f) :=
    (EuclideanSpace.proj j : ℝ^3 →L[ℝ] ℝ).continuous.comp
      (D.continuous_velocityDrift.comp (continuous_fst.smul continuous_snd))
  have hc := D.continuousOn_dilatedScaling N
  have key : ∀ c d : ℝ, 0 < c → c ≤ d →
      ((∫ b in c..d, T (D.dilatedScaling N b) : DerivLp 3 2 univ) : ℝ^3 → ℝ)
        =ᵐ[domainMeasure 3 univ] fun x ↦ ∫ b in c..d, f b x := fun c d hc0 hcd ↦ by
    refine coeFn_intervalIntegral_ae (by simp [domainMeasure]) hcd
      (T.continuous.comp_continuousOn (hc.mono fun b hb ↦ lt_of_lt_of_le hc0 hb.1)) hf
      fun b hb ↦ ?_
    have hb0 : b ≠ 0 := (lt_of_lt_of_le hc0 hb.1).ne'
    rw [Function.comp_apply, coeFn_baseComponentCLM]
    simpa only [domainMeasure, Measure.restrict_univ] using
      D.baseRepresentative_dilatedScaling_ae N hb0 j
  have hint : IntervalIntegrable (D.dilatedScaling N) volume 1 a :=
    (hc.mono (uIcc_one_subset_Ioi ha)).intervalIntegrable
  have hcomm : T (D.profileIncrement N a) = ∫ b in (1 : ℝ)..a, T (D.dilatedScaling N b) :=
    (T.intervalIntegral_comp_comm hint).symm
  have hgoal : ((T (D.profileIncrement N a) : DerivLp 3 2 univ) : ℝ^3 → ℝ)
      =ᵐ[domainMeasure 3 univ] fun x ↦ ∫ b in (1 : ℝ)..a, f b x := by
    rw [hcomm]
    rcases le_or_gt 1 a with h1 | h1
    · exact key 1 a one_pos h1
    · rw [intervalIntegral.integral_symm]
      filter_upwards [Lp.coeFn_neg (∫ b in a..(1 : ℝ), T (D.dilatedScaling N b)),
        key a 1 ha h1.le] with x hx₁ hx₂
      rw [hx₁, Pi.neg_apply, hx₂, intervalIntegral.integral_symm, neg_neg]
  rw [coeFn_baseComponentCLM] at hgoal
  simp only [domainMeasure, Measure.restrict_univ] at hgoal
  filter_upwards [hgoal] with x hx
  rw [hx, hfdef, D.integral_velocityDrift_smul a x j]

/-- The dilations of the profile differ from it by a square-integrable field. -/
theorem memLp_dilateField_sub {a : ℝ} (ha : 0 < a) :
    MemLp (dilateField a D.U - D.U) 2 volume := by
  set u := D.profileIncrement 0 a
  have hae : (l2SobolevRow (baseIndex 3 0) u : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 univ]
      dilateField a D.U - D.U := by
    rw [l2SobolevRow_apply]
    have hc := fun j : Fin 3 ↦ D.baseRepresentative_profileIncrement_ae 0 ha j
    filter_upwards [Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex 3 0) (u j)),
      (by simpa only [domainMeasure, Measure.restrict_univ] using ae_all_iff.mpr hc :
        ∀ᵐ x ∂(domainMeasure 3 univ), ∀ j : Fin 3,
          baseRepresentative (u j) x = (dilateField a D.U x - D.U x) j)] with x ht hx
    refine PiLp.ext fun j ↦ ?_
    rw [ht j, Pi.sub_apply, ← hx j, wkpCoordinateCLM_apply]
    rfl
  have h := (Lp.memLp (l2SobolevRow (baseIndex 3 0) u)).ae_eq hae
  simpa only [domainMeasure, Measure.restrict_univ] using h

/-- The derivatives of `a Ũ(a ·) - Ũ` are square integrable. -/
theorem memLp_iteratedFDeriv_dilateField_sub {a : ℝ} (ha : 0 < a) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m (dilateField a D.U - D.U)) 2 volume := by
  have hd := contDiff_dilateField a D.contDiff_U
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    exact (D.memLp_dilateField_sub ha).of_le
      ((hd.sub D.contDiff_U).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_zero])
  · have heq : iteratedFDeriv ℝ m (dilateField a D.U - D.U) =
        iteratedFDeriv ℝ m (dilateField a D.U) - iteratedFDeriv ℝ m D.U := by
      funext x
      exact iteratedFDeriv_sub_apply (hd.contDiffAt.of_le (by exact_mod_cast le_top))
        (D.contDiff_U.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [heq]
    exact (memLp_iteratedFDeriv_dilateField ha.ne' D.contDiff_U
      (D.derivatives_memLp_two m hpos)).sub (D.derivatives_memLp_two m hpos)

/-- **The increment is the smooth field `a Ũ(a ·) - Ũ`** in vector `Hᴺ`. -/
theorem profileIncrement_eq (N : ℕ) {a : ℝ} (ha : 0 < a) :
    D.profileIncrement N a = WithLp.toLp 2 (vectorWkpOfContDiff (dilateField a D.U - D.U)
      ((contDiff_dilateField a D.contDiff_U).sub D.contDiff_U)
      fun m _ ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) := by
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [D.baseRepresentative_profileIncrement_ae N ha j,
    baseRepresentative_vectorWkpOfContDiff (dilateField a D.U - D.U)
      ((contDiff_dilateField a D.contDiff_U).sub D.contDiff_U)
      (fun m (_ : m ≤ N) ↦ D.memLp_iteratedFDeriv_dilateField_sub ha m) j] with x h₁ h₂
  rw [h₁]
  exact h₂.symm

end UnstableProfile

end NavierStokes.Nonuniqueness
