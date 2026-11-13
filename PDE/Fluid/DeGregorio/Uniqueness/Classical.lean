/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Uniqueness.Interior
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.VelocityIdentification
public import PDE.Analysis.Fourier.HilbertTransform.CompactBounds

/-!
# Uniqueness of classical De Gregorio solutions on a half-open interval

A classical solution of the De Gregorio equation `ω_t + u ω_x = u_x ω`, `u_x = H ω`, on
`[0, T)` from a datum `w₀` is a pair of fields such that

* the vorticity is jointly `C¹` on `ℝ × [0, T)`, with a one-sided time derivative at `t = 0`;
* the equation holds at every point of `ℝ × (0, T)`;
* at every time of `[0, T)` the velocity slice is differentiable, its derivative is the Hilbert
  transform of the vorticity slice, and the velocity vanishes at `x = 0`;
* on every `[0, T']` with `T' < T` the vorticity vanishes outside one bounded interval;
* the vorticity starts from `w₀`.

The equation is not required at `t = 0`, and no regularity of the velocity is assumed beyond
spatial differentiability. The normalization `u(0, t) = 0` fixes the additive constant left free
by `u_x = H ω`, so it is part of the uniqueness statement. The intended lifespan is `T > 0`; for
`T ≤ 0` the class only fixes the initial slice. Two such solutions from the same datum coincide
on `ℝ × [0, T)`.

The velocity of such a solution is the normalized principal-value primitive of its vorticity,
so its slices are `C¹`. The velocity gradient is bounded on every `[0, T']` by the local
Lipschitz cancellation of the principal value. The difference energy on a common support
interval is continuous up to `t = 0`, so the interior energy argument of
`differenceEnergy_eq_zero_of_same_initialData_interior` applies on `[0, T']`.

## Main results

* `IsClassicalSolutionFrom`: the class of classical solutions described above.
* `IsClassicalSolutionFrom.velocity_eq`: the velocity is `hilbertPVVelocity` of the vorticity.
* `IsClassicalSolutionFrom.eq`: two solutions from the same datum agree on `ℝ × [0, T)`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped NNReal Topology ContDiff

namespace DeGregorio

/-- Classical solutions of the De Gregorio equation with `a = 1` on `[0, T)` from the datum
`w₀`. The vorticity is jointly `C¹` on `ℝ × [0, T)`, the transport equation holds at positive
times, the Biot–Savart relation and the normalization `u(0, t) = 0` hold at every time of
`[0, T)`, and on every `[0, T']` with `T' < T` the vorticity vanishes outside one bounded
interval. -/
structure IsClassicalSolutionFrom (w₀ : ℝ → ℝ) (T : ℝ) (fields : Fields) : Prop where
  /-- The vorticity is jointly `C¹` up to the initial line. -/
  vorticity_contDiffOn : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ico 0 T)
  /-- Every velocity slice is differentiable. -/
  velocity_differentiable : ∀ t ∈ Ico 0 T, Differentiable ℝ (fun x ↦ fields.velocity x t)
  /-- Transport and stretching at every positive time. -/
  transport : SatisfiesTransportEquationOn 1 fields (Ioo 0 T)
  /-- The velocity derivative is the Hilbert transform of the vorticity. -/
  biotSavart : SatisfiesBiotSavartOn fields (Ico 0 T)
  /-- The velocity vanishes at the origin. -/
  velocity_zero : ∀ t ∈ Ico 0 T, fields.velocity 0 t = 0
  /-- The vorticity vanishes outside one bounded interval on every `[0, T']` with `T' < T`. -/
  support : ∀ T' < T, ∃ L, ∀ t ∈ Icc 0 T', ∀ x, L ≤ |x| → fields.vorticity x t = 0
  /-- The initial vorticity is the datum. -/
  initial : ∀ x, fields.vorticity x 0 = w₀ x

namespace IsClassicalSolutionFrom

variable {w₀ : ℝ → ℝ} {T : ℝ} {fields other : Fields}

/-- Each vorticity slice of `[0, T)` is `C¹`. -/
theorem contDiff_one_vorticity (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ}
    (ht : t ∈ Ico 0 T) : ContDiff ℝ 1 (fun x ↦ fields.vorticity x t) :=
  h.vorticity_contDiffOn.comp_contDiff (contDiff_id.prodMk contDiff_const)
    (fun x ↦ ⟨mem_univ x, ht⟩)

/-- Each vorticity slice of `[0, T)` vanishes outside a bounded interval. -/
theorem exists_support_slice (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ}
    (ht : t ∈ Ico 0 T) : ∃ L, ∀ x, L ≤ |x| → fields.vorticity x t = 0 := by
  obtain ⟨L, hL⟩ := h.support t ht.2
  exact ⟨L, hL t ⟨ht.1, le_rfl⟩⟩

/-- Each vorticity slice of `[0, T)` has compact support. -/
theorem hasCompactSupport_vorticity (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ}
    (ht : t ∈ Ico 0 T) : HasCompactSupport (fun x ↦ fields.vorticity x t) := by
  obtain ⟨L, hL⟩ := h.exists_support_slice ht
  apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
  intro x hx
  exact hL x (le_of_not_ge fun h ↦ hx (abs_le.mp h))

/-- The velocity is the normalized principal-value primitive of the vorticity. -/
theorem velocity_eq (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ} (ht : t ∈ Ico 0 T) :
    (fun x ↦ fields.velocity x t) = hilbertPVVelocity (fun x ↦ fields.vorticity x t) := by
  have hs := h.hasCompactSupport_vorticity ht
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs (h.contDiff_one_vorticity ht)
    one_ne_zero
  exact (h.biotSavart ht).eq_hilbertPVVelocity_of_normalized (h.velocity_differentiable t ht)
    hK hs (h.velocity_zero t ht)

/-- Each velocity slice of `[0, T)` is `C¹`. -/
theorem contDiff_one_velocity (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ}
    (ht : t ∈ Ico 0 T) : ContDiff ℝ 1 (fun x ↦ fields.velocity x t) := by
  rw [h.velocity_eq ht]
  have hs := h.hasCompactSupport_vorticity ht
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs (h.contDiff_one_vorticity ht)
    one_ne_zero
  exact contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hK hs

/-- A solution on `[0, T)` is classical in LeanPDE's sense on every set of positive times. -/
theorem isClassicalSolutionOn (h : IsClassicalSolutionFrom w₀ T fields) {s : Set ℝ}
    (hs : s ⊆ Ioo 0 T) : IsClassicalSolutionOn 1 fields s where
  regularity :=
    { vorticity_differentiableAt := fun ht ↦
        (h.vorticity_contDiffOn.differentiableOn one_ne_zero).differentiableAt
          (prod_mem_nhds univ_mem (Ico_mem_nhds (hs ht).1 (hs ht).2))
      velocity_differentiableAt := fun ht ↦
        h.velocity_differentiable _ (Ioo_subset_Ico_self (hs ht)) _ }
  transport := fun _ _ ht ↦ h.transport (hs ht)
  biotSavart := fun _ ht ↦ h.biotSavart (Ioo_subset_Ico_self (hs ht))

/-- The spatial derivative of the vorticity is jointly continuous on `ℝ × [0, T)`. -/
theorem continuousOn_deriv_vorticity (h : IsClassicalSolutionFrom w₀ T fields) :
    ContinuousOn (fun p : ℝ × ℝ ↦ deriv (fun y ↦ fields.vorticity y p.2) p.1)
      (univ ×ˢ Ico 0 T) := by
  have hU : UniqueDiffOn ℝ ((univ : Set ℝ) ×ˢ Ico 0 T) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 T)
  have hD := h.vorticity_contDiffOn.continuousOn_fderivWithin hU le_rfl
  have hE : ContinuousOn (fun p : ℝ × ℝ ↦
      fderivWithin ℝ (Function.uncurry fields.vorticity) (univ ×ˢ Ico 0 T) p (1, 0))
      (univ ×ˢ Ico 0 T) :=
    hD.clm_apply continuousOn_const
  apply hE.congr
  intro p hp
  have hf := ((h.vorticity_contDiffOn.differentiableOn one_ne_zero) p hp).hasFDerivWithinAt
  have hcurve : HasFDerivWithinAt (fun y : ℝ ↦ (y, p.2))
      ((ContinuousLinearMap.id ℝ ℝ).prod 0) univ p.1 :=
    ((hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)).hasFDerivWithinAt
  have hmaps : MapsTo (fun y : ℝ ↦ (y, p.2)) univ (univ ×ˢ Ico 0 T) :=
    fun y _ ↦ ⟨mem_univ y, hp.2⟩
  have hcomp := hf.comp p.1 hcurve hmaps
  have hderiv : HasDerivAt (fun y ↦ fields.vorticity y p.2)
      (fderivWithin ℝ (Function.uncurry fields.vorticity) (univ ×ˢ Ico 0 T) p (1, 0)) p.1 := by
    have h1 := hcomp.hasFDerivAt (univ_mem)
    simpa [Function.comp_def] using h1.hasDerivAt
  exact hderiv.deriv

/-- On `[0, T']`, `T' < T`, the vorticity vanishes for `|x| ≥ L` and the vorticity and its
spatial derivative are bounded by one constant. -/
theorem exists_bounds (h : IsClassicalSolutionFrom w₀ T fields) {T' : ℝ} (hT' : T' < T) :
    ∃ L C : ℝ, 0 ≤ L ∧ 0 ≤ C ∧
      (∀ t ∈ Icc 0 T', ∀ x, L ≤ |x| → fields.vorticity x t = 0) ∧
      ∀ t ∈ Icc 0 T', ∀ x,
        |fields.vorticity x t| ≤ C ∧ |deriv (fun y ↦ fields.vorticity y t) x| ≤ C := by
  obtain ⟨L₀, hL₀⟩ := h.support T' hT'
  set L := max L₀ 0 + 1 with hLdef
  have hL : 0 ≤ L := by positivity
  have hsupp : ∀ t ∈ Icc 0 T', ∀ x, max L₀ 0 ≤ |x| → fields.vorticity x t = 0 :=
    fun t ht x hx ↦ hL₀ t ht x ((le_max_left _ _).trans hx)
  have hsub : Icc (-L) L ×ˢ Icc 0 T' ⊆ univ ×ˢ Ico 0 T :=
    fun p hp ↦ ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt hT'⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦
      (fields.vorticity p.1 p.2, deriv (fun y ↦ fields.vorticity y p.2) p.1))
      (Icc (-L) L ×ˢ Icc 0 T') :=
    (h.vorticity_contDiffOn.continuousOn.mono hsub).prodMk
      (h.continuousOn_deriv_vorticity.mono hsub)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨max L₀ 0, max B 0, le_max_right _ _, le_max_right _ _, hsupp, ?_⟩
  intro t ht x
  by_cases hx : |x| ≤ L
  · have hb := (hB (x, t) ⟨abs_le.mp hx, ht⟩).trans (le_max_left B 0)
    simp only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] at hb
    exact hb
  · have hx : L < |x| := not_le.mp hx
    have hzero : (fun y ↦ fields.vorticity y t) =ᶠ[nhds x] fun _ ↦ 0 := by
      have hopen : {y : ℝ | max L₀ 0 < |y|} ∈ nhds x :=
        (isOpen_lt continuous_const continuous_abs).mem_nhds
          (show max L₀ 0 < |x| by linarith)
      filter_upwards [hopen] with y hy
      exact hsupp t ht y hy.le
    rw [hzero.deriv_eq, deriv_const, hsupp t ht x (by linarith)]
    simp only [abs_zero]
    exact ⟨le_max_right _ _, le_max_right _ _⟩

/-- On `[0, T']`, `T' < T`, the velocity gradient is bounded on every bounded interval. -/
theorem exists_velocity_deriv_bound (h : IsClassicalSolutionFrom w₀ T fields) {T' : ℝ}
    (hT' : T' < T) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T', ∀ x, |x| ≤ R →
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C := by
  obtain ⟨L, C, hL, hC, hsupp, hbound⟩ := h.exists_bounds hT'
  set M := max L R with hM
  refine ⟨(2 * C + 4 * M * C) / Real.pi, by positivity, ?_⟩
  intro t ht x hx
  have htT : t ∈ Ico 0 T := ⟨ht.1, ht.2.trans_lt hT'⟩
  have hdiff : Differentiable ℝ (fun y ↦ fields.vorticity y t) :=
    (h.contDiff_one_vorticity htT).differentiable one_ne_zero
  have hK : LipschitzWith ⟨C, hC⟩ (fun y ↦ fields.vorticity y t) :=
    lipschitzWith_of_nnnorm_deriv_le hdiff fun y ↦ by
      apply NNReal.coe_le_coe.mp
      change ‖deriv (fun y ↦ fields.vorticity y t) y‖ ≤ C
      rw [Real.norm_eq_abs]
      exact (hbound t ht y).2
  rw [h.velocity_eq htT,
    (hasDerivAt_hilbertPVVelocity_of_lipschitzWith_compactSupport hK
      (h.hasCompactSupport_vorticity htT) x).deriv]
  exact abs_hilbertPV_le_of_lipschitzWith_of_support hK (h.hasCompactSupport_vorticity htT)
    (fun y ↦ (hbound t ht y).1)
    (fun y hy ↦ hsupp t ht y ((le_max_left L R).trans hy)) (hx.trans (le_max_right L R))

/-- The difference energy of two solutions is continuous on every `[0, T']`, `T' < T`. -/
theorem continuousOn_differenceEnergy (h : IsClassicalSolutionFrom w₀ T fields)
    (h' : IsClassicalSolutionFrom w₀ T other) {T' : ℝ} (hT' : T' < T) (hT'0 : 0 ≤ T')
    (L : ℝ) : ContinuousOn (differenceEnergy fields other L) (Icc 0 T') := by
  have hsub : (univ : Set ℝ) ×ˢ Icc 0 T' ⊆ univ ×ˢ Ico 0 T :=
    fun p hp ↦ ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt hT'⟩
  have hp : Continuous (fun p : ℝ × ℝ ↦ (p.1, (projIcc 0 T' hT'0 p.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp
      ((continuous_projIcc).comp continuous_snd))
  have hmaps (p : ℝ × ℝ) :
      (p.1, (projIcc 0 T' hT'0 p.2 : ℝ)) ∈ (univ : Set ℝ) ×ˢ Icc 0 T' :=
    ⟨mem_univ _, (projIcc 0 T' hT'0 p.2).property⟩
  have hf := (h.vorticity_contDiffOn.continuousOn.mono hsub).comp_continuous hp hmaps
  have hg := (h'.vorticity_contDiffOn.continuousOn.mono hsub).comp_continuous hp hmaps
  have hint : Continuous (fun s : ℝ ↦ ∫ x in Icc (-L) L,
      (fields.vorticity x (projIcc 0 T' hT'0 s) -
        other.vorticity x (projIcc 0 T' hT'0 s)) ^ 2) := by
    apply continuous_parametric_integral_of_continuous (f := fun s x ↦
      (fields.vorticity x (projIcc 0 T' hT'0 s) -
        other.vorticity x (projIcc 0 T' hT'0 s)) ^ 2) _ isCompact_Icc
    have hs := ((hf.sub hg).pow 2).comp continuous_swap
    exact hs
  apply hint.continuousOn.congr
  intro s hs
  simp only [differenceEnergy, projIcc_of_mem hT'0 hs]

/-- A solution on `[0, T)` is a solution on every shorter interval `[0, T')`. -/
theorem mono (h : IsClassicalSolutionFrom w₀ T fields) {T' : ℝ} (hT : T' ≤ T) :
    IsClassicalSolutionFrom w₀ T' fields where
  vorticity_contDiffOn := h.vorticity_contDiffOn.mono
    (prod_mono subset_rfl (Ico_subset_Ico_right hT))
  velocity_differentiable := fun t ht ↦ h.velocity_differentiable t ⟨ht.1, ht.2.trans_le hT⟩
  transport := fun _ _ ht ↦ h.transport ⟨ht.1, ht.2.trans_le hT⟩
  biotSavart := fun _ ht ↦ h.biotSavart ⟨ht.1, ht.2.trans_le hT⟩
  velocity_zero := fun t ht ↦ h.velocity_zero t ⟨ht.1, ht.2.trans_le hT⟩
  support := fun T'' hT'' ↦ h.support T'' (hT''.trans_le hT)
  initial := h.initial

/-- The velocity slices are smooth wherever the vorticity slices are. -/
theorem contDiff_velocity (h : IsClassicalSolutionFrom w₀ T fields) {t : ℝ} (ht : t ∈ Ico 0 T)
    (hw : ContDiff ℝ ∞ (fun x ↦ fields.vorticity x t)) :
    ContDiff ℝ ∞ (fun x ↦ fields.velocity x t) := by
  rw [h.velocity_eq ht]
  exact contDiff_hilbertPVVelocity_of_contDiff_compactSupport hw
    (h.hasCompactSupport_vorticity ht)

/-- Two solutions from the same datum have the same vorticity and velocity at every time
of `[0, T)`. -/
theorem eq (h : IsClassicalSolutionFrom w₀ T fields)
    (h' : IsClassicalSolutionFrom w₀ T other) :
    ∀ t ∈ Ico 0 T, ∀ x,
      fields.vorticity x t = other.vorticity x t ∧ fields.velocity x t = other.velocity x t := by
  intro t ht
  have hw : ∀ x, fields.vorticity x t = other.vorticity x t := by
    rcases ht.1.eq_or_lt with h0 | hpos
    · intro x
      rw [← h0, h.initial, h'.initial]
    obtain ⟨L₁, C₁, hL₁, hC₁, hs₁, hb₁⟩ := h.exists_bounds ht.2
    obtain ⟨L₂, C₂, hL₂, hC₂, hs₂, hb₂⟩ := h'.exists_bounds ht.2
    set L := max L₁ L₂ with hL
    obtain ⟨Cu, hCu, hbu⟩ := h.exists_velocity_deriv_bound ht.2 L
    set C := max Cu (max C₁ C₂) with hC
    have hsub : Ioo 0 t ⊆ Ioo 0 T := fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
    have hsubIco : Ioo 0 t ⊆ Ico 0 T := fun s hs ↦ ⟨hs.1.le, hs.2.trans ht.2⟩
    have hsubIcc : Ioo 0 t ⊆ Icc 0 t := Ioo_subset_Icc_self
    have hcyl : (univ : Set ℝ) ×ˢ Ioo 0 t ⊆ univ ×ˢ Ico 0 T :=
      fun p hp ↦ ⟨mem_univ _, hsubIco hp.2⟩
    have henergy := differenceEnergy_eq_zero_of_same_initialData_interior
      (fields := fields) (other := other) (L := L) (C := C) (a := 0) (b := t)
      (h.vorticity_contDiffOn.mono hcyl) (h'.vorticity_contDiffOn.mono hcyl)
      (fun s hs ↦ h.contDiff_one_velocity (hsubIco hs))
      (fun s hs ↦ h'.contDiff_one_velocity (hsubIco hs))
      (h.isClassicalSolutionOn hsub) (h'.isClassicalSolutionOn hsub) (le_max_of_le_left hL₁)
      (le_max_of_le_left hCu)
      (fun s hs x hx ↦ by
        have hx' : L ≤ |x| := by
          by_contra hlt
          exact hx (abs_lt.mp (not_le.mp hlt))
        exact ⟨hs₁ s (hsubIcc hs) x ((le_max_left _ _).trans hx'),
          hs₂ s (hsubIcc hs) x ((le_max_right _ _).trans hx')⟩)
      (fun s hs ↦ by
        rw [h.velocity_zero s (hsubIco hs), h'.velocity_zero s (hsubIco hs)])
      (fun s hs x hx ↦
        ⟨(hbu s (hsubIcc hs) x (abs_le.mpr hx)).trans (le_max_left _ _),
          (hb₂ s (hsubIcc hs) x).1.trans ((le_max_right C₁ C₂).trans (le_max_right Cu _)),
          (hb₂ s (hsubIcc hs) x).2.trans ((le_max_right C₁ C₂).trans (le_max_right Cu _))⟩)
      (h.continuousOn_differenceEnergy h' ht.2 ht.1 L)
      (by simp only [differenceEnergy, h.initial, h'.initial, sub_self,
        zero_pow (by norm_num : 2 ≠ 0), integral_zero])
    have hzeroE := henergy t ⟨ht.1, le_rfl⟩
    let d : ℝ → ℝ := fun x ↦ fields.vorticity x t - other.vorticity x t
    have hd : Continuous d :=
      (h.contDiff_one_vorticity ht).continuous.sub (h'.contDiff_one_vorticity ht).continuous
    have hdout : ∀ x, x ∉ Icc (-L) L → d x ^ 2 = 0 := by
      intro x hx
      have hx' : L ≤ |x| := by
        by_contra hlt
        have hlt := abs_lt.mp (not_le.mp hlt)
        exact hx ⟨hlt.1.le, hlt.2.le⟩
      simp only [d, hs₁ t ⟨ht.1, le_rfl⟩ x ((le_max_left _ _).trans hx'),
        hs₂ t ⟨ht.1, le_rfl⟩ x ((le_max_right _ _).trans hx'), sub_self, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have hintegral : (∫ x, d x ^ 2) = 0 := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hdout]
      exact hzeroE
    have hcs : HasCompactSupport (fun x ↦ d x ^ 2) := by
      apply HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc
      exact hdout
    have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (d x))
      ((hd.pow 2).integrable_of_hasCompactSupport hcs)).mp hintegral
    have hae' : d =ᵐ[volume] 0 := hae.mono fun _ hx ↦ sq_eq_zero_iff.mp hx
    have hd0 : d = 0 := Measure.eq_of_ae_eq hae' hd continuous_const
    exact fun x ↦ sub_eq_zero.mp (congrFun hd0 x)
  intro x
  refine ⟨hw x, ?_⟩
  have hu := congrFun (h.velocity_eq ht) x
  have hv := congrFun (h'.velocity_eq ht) x
  have hslice : (fun y ↦ fields.vorticity y t) = fun y ↦ other.vorticity y t := funext hw
  rw [hu, hv, hslice]

/-- Two solutions from the same datum, on `[0, T)` and on `[0, T')`, have the same vorticity
and velocity at every time of `[0, min T T')`. -/
theorem eq_of_min (h : IsClassicalSolutionFrom w₀ T fields) {T' : ℝ}
    (h' : IsClassicalSolutionFrom w₀ T' other) :
    ∀ t ∈ Ico 0 (min T T'), ∀ x,
      fields.vorticity x t = other.vorticity x t ∧ fields.velocity x t = other.velocity x t :=
  (h.mono (min_le_left T T')).eq (h'.mono (min_le_right T T'))

end IsClassicalSolutionFrom

end DeGregorio
