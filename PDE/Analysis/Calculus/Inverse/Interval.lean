/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Inverses on real interval images

A nonvanishing derivative on an interval forces injectivity, even when the
derivative is not continuous. On an open interval the inverse is continuous and
has the reciprocal derivative. Continuous differentiability of the original
function is needed only for the corresponding upgrade of the inverse.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- A prescribed compact segment in an open interval lies in a bounded open
subinterval whose closure endpoints still belong to the original interval. -/
theorem exists_Ioo_between_uIcc_of_isOpen_ordConnected
    {I : Set ℝ} (hI : IsOpen I) (hconn : OrdConnected I)
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    ∃ l r, uIcc a b ⊆ Ioo l r ∧ Icc l r ⊆ I := by
  have hmin : min a b ∈ I := by rcases le_total a b with h | h <;> simp_all
  have hmax : max a b ∈ I := by rcases le_total a b with h | h <;> simp_all
  obtain ⟨L, U, hLU, hsubL⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hmin)
  obtain ⟨l, hLl, hl⟩ := exists_between hLU.1
  have hlI : l ∈ I := hsubL ⟨hLl, hl.trans hLU.2⟩
  obtain ⟨L', U', hLU', hsubR⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hmax)
  obtain ⟨r, hr, hrU⟩ := exists_between hLU'.2
  have hrI : r ∈ I := hsubR ⟨hLU'.1.trans hr, hrU⟩
  exact ⟨l, r, fun _ hs ↦ ⟨hl.trans_le hs.1, hs.2.trans_lt hr⟩, hconn.out hlI hrI⟩

/-- Rolle's theorem gives injectivity on an interval without continuity of the
derivative or a uniform lower bound for its absolute value. -/
theorem injOn_of_hasDerivAt_ne_zero
    {f f' : ℝ → ℝ} {s : Set ℝ} (hs : OrdConnected s)
    (hf : ∀ x ∈ s, HasDerivAt f (f' x) x) (hne : ∀ x ∈ s, f' x ≠ 0) :
    InjOn f s := by
  have hneq {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
      f x ≠ f y := by
    intro heq
    have hsub := hs.out hx hy
    obtain ⟨z, hz, hzero⟩ := exists_hasDerivAt_eq_zero hxy
      (fun t ht ↦ (hf t (hsub ht)).continuousAt.continuousWithinAt) heq
      (fun t ht ↦ hf t (hsub (Ioo_subset_Icc_self ht)))
    exact hne z (hsub (Ioo_subset_Icc_self hz)) hzero
  intro x hx y hy heq
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact (hneq hx hy hxy heq).elim
  · exact hxy
  · exact (hneq hy hx hxy heq.symm).elim

/-- A continuous injection sends an open real interval to an open set. The
proof brackets each image point by the images of two interior parameter values. -/
theorem isOpen_image_Ioo_of_continuousOn_injOn
    {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Ioo a b))
    (hinj : InjOn f (Ioo a b)) :
    IsOpen (f '' Ioo a b) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨l, hal, hlx⟩ := exists_between hx.1
  obtain ⟨r, hxr, hrb⟩ := exists_between hx.2
  have hl : l ∈ Ioo a b := ⟨hal, hlx.trans hx.2⟩
  have hr : r ∈ Ioo a b := ⟨hx.1.trans hxr, hrb⟩
  have hsub : Icc l r ⊆ Ioo a b := ordConnected_Ioo.out hl hr
  have hcont := hf.mono hsub
  rcases hf.strictMonoOn_of_injOn_Ioo (hx.1.trans hx.2) hinj with hmono | hanti
  · apply mem_of_superset (Ioo_mem_nhds (hmono hl hx hlx) (hmono hx hr hxr))
    intro y hy
    have himage := intermediate_value_Icc (hlx.trans hxr).le hcont
      (Ioo_subset_Icc_self hy)
    obtain ⟨z, hz, rfl⟩ := himage
    exact mem_image_of_mem f (hsub hz)
  · apply mem_of_superset (Ioo_mem_nhds (hanti hx hr hxr) (hanti hl hx hlx))
    intro y hy
    have himage := hcont.image_Icc_of_antitoneOn (hlx.trans hxr).le
      (hanti.antitoneOn.mono hsub)
    have hy' : y ∈ f '' Icc l r := by rw [himage]; exact Ioo_subset_Icc_self hy
    exact image_mono hsub hy'

/-- The chosen interval inverse is continuous on its actual image, for either
orientation of the original injection. -/
theorem continuousAt_invFunOn_Ioo
    {f : ℝ → ℝ} {a b y : ℝ} (hf : ContinuousOn f (Ioo a b))
    (hinj : InjOn f (Ioo a b)) (hy : y ∈ f '' Ioo a b) :
    ContinuousAt (Function.invFunOn f (Ioo a b)) y := by
  let g := Function.invFunOn f (Ioo a b)
  have hmem {z : ℝ} (hz : z ∈ f '' Ioo a b) : g z ∈ Ioo a b :=
    Function.invFunOn_mem hz
  have hright {z : ℝ} (hz : z ∈ f '' Ioo a b) : f (g z) = z :=
    Function.invFunOn_eq hz
  have himage : g '' (f '' Ioo a b) = Ioo a b := hinj.invFunOn_image Subset.rfl
  have hsource := (isOpen_image_Ioo_of_continuousOn_injOn hf hinj).mem_nhds hy
  have htarget : g '' (f '' Ioo a b) ∈ 𝓝 (g y) := by
    rw [himage]
    exact isOpen_Ioo.mem_nhds (hmem hy)
  rcases hf.strictMonoOn_of_injOn_Ioo ((hmem hy).1.trans (hmem hy).2) hinj with
    hmono | hanti
  · have hg : StrictMonoOn g (f '' Ioo a b) := by
      intro z hz w hw hzw
      apply (hmono.lt_iff_lt (hmem hz) (hmem hw)).mp
      simpa only [hright hz, hright hw] using hzw
    exact hg.continuousAt_of_image_mem_nhds hsource htarget
  · have hg : StrictAntiOn g (f '' Ioo a b) := by
      intro z hz w hw hzw
      apply (hanti.lt_iff_gt (hmem hz) (hmem hw)).mp
      simpa only [hright hz, hright hw] using hzw
    exact hg.dual_right.continuousAt_of_image_mem_nhds hsource htarget

/-- The actual derivative of the interval inverse is the reciprocal derivative
at its preimage. No continuity of the original derivative is assumed. -/
theorem hasDerivAt_invFunOn_Ioo
    {f f' : ℝ → ℝ} {a b y : ℝ}
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hne : ∀ x ∈ Ioo a b, f' x ≠ 0) (hy : y ∈ f '' Ioo a b) :
    HasDerivAt (Function.invFunOn f (Ioo a b))
      (f' (Function.invFunOn f (Ioo a b) y))⁻¹ y := by
  have hcont : ContinuousOn f (Ioo a b) :=
    fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hinj := injOn_of_hasDerivAt_ne_zero ordConnected_Ioo hf hne
  have hmem := Function.invFunOn_mem hy
  apply HasDerivAt.of_local_left_inverse (continuousAt_invFunOn_Ioo hcont hinj hy)
    (hf _ hmem) (hne _ hmem)
  filter_upwards [(isOpen_image_Ioo_of_continuousOn_injOn hcont hinj).mem_nhds hy] with z hz
  exact Function.invFunOn_eq hz

/-- The image of the whole prescribed closed segment is the whole interval
between its endpoint images, for either orientation of an interval injection. -/
theorem image_uIcc_of_continuousOn_injOn_Ioo
    {f : ℝ → ℝ} {l r a b : ℝ}
    (hf : ContinuousOn f (Ioo l r)) (hinj : InjOn f (Ioo l r))
    (ha : a ∈ Ioo l r) (hb : b ∈ Ioo l r) :
    f '' uIcc a b = uIcc (f a) (f b) := by
  have hsub := ordConnected_Ioo.uIcc_subset ha hb
  rcases hf.strictMonoOn_of_injOn_Ioo (ha.1.trans ha.2) hinj with hmono | hanti
  · exact (hf.mono hsub).image_uIcc_of_monotoneOn (hmono.monotoneOn.mono hsub)
  · exact (hf.mono hsub).image_uIcc_of_antitoneOn (hanti.antitoneOn.mono hsub)

/-- Continuous differentiability of the original function upgrades the same
chosen inverse to `C¹` on its open image. -/
theorem contDiffOn_invFunOn_Ioo
    {f : ℝ → ℝ} {l r : ℝ} (hf : ContDiffOn ℝ 1 f (Ioo l r))
    (hne : ∀ x ∈ Ioo l r, deriv f x ≠ 0) :
    ContDiffOn ℝ 1 (Function.invFunOn f (Ioo l r)) (f '' Ioo l r) := by
  have hderiv : ∀ x ∈ Ioo l r, HasDerivAt f (deriv f x) x :=
    fun _ hx ↦ (hf.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt_one.hasDerivAt
  have hinj := injOn_of_hasDerivAt_ne_zero ordConnected_Ioo hderiv hne
  have hopen := isOpen_image_Ioo_of_continuousOn_injOn hf.continuousOn hinj
  have hg := fun y hy ↦ hasDerivAt_invFunOn_Ioo hderiv hne (y := y) hy
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hopen]
  refine ⟨fun y hy ↦ (hg y hy).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply contDiffOn_zero.mpr
  intro y hy
  have hmem := Function.invFunOn_mem hy
  have hc := ((hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl _ hmem).continuousAt
    (isOpen_Ioo.mem_nhds hmem)).comp
      (continuousAt_invFunOn_Ioo hf.continuousOn hinj hy)
  apply ((hc.inv₀ (hne _ hmem)).continuousWithinAt).congr
  · intro z hz
    exact (hg z hz).deriv
  · exact (hg y hy).deriv

end PDE.Analysis
