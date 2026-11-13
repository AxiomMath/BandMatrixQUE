module

public import BlockBand.GaussianBulk.ExternalSineHomologyLoop
public import BlockBand.GaussianBulk.GraftedMDELoop

/-!
# Piecewise-C¹ path calculus and the grafted level loop

The loop is `nativeGraftedLevelLoop`: finite raised meshes, the exact central level graph, vertical
grafts and the reflected closure (`GraftedLevelEnclosure`).

`GoodPath γ` records the two facts about a path used in the contour deformation, for scalar one-forms
`scalarForm f = f(z) dz` (Mathlib `curveIntegral`, real Lebesgue measure on the parameter):
every `f` continuous on `range γ` is curve integrable, and the fundamental theorem of calculus
holds for every primitive `F` with `F' = f` on `range γ`. It holds for C¹ `ofLine` pieces and is
closed under `cast`, `trans`, `symm` and complex conjugation; hence for segments, finite meshes,
the central level graph and the whole grafted loop (`goodPath_nativeGraftedLevelLoop`).
`graftedLoopCalculus` packages the loop as a `LoopCalculus` on any ball `ball 0 ρ` containing
it, with poles the source points `d_j` (winding from
`nativeGraftedLevelLoop_resolvent`).

Domain: `N > 0`, `0 < t ≤ tmax`, `0 < eta ≤ levelHeight d t x₀`, arbitrary real `d`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology
open scoped unitInterval

/-- The scalar one-form `f(z) dz`. -/
def scalarForm (f : ℂ → ℂ) (z : ℂ) : ℂ →L[ℂ] ℂ := f z • ContinuousLinearMap.id ℂ ℂ

@[simp] theorem scalarForm_apply (f : ℂ → ℂ) (z v : ℂ) : scalarForm f z v = f z * v := by
  simp [scalarForm]

/-- Integrability of continuous scalar forms and the FTC along a path. -/
structure GoodPath {a b : ℂ} (γ : Path a b) : Prop where
  integrable : ∀ f : ℂ → ℂ, ContinuousOn f (range γ) → CurveIntegrable (scalarForm f) γ
  ftc : ∀ F f : ℂ → ℂ, ContinuousOn f (range γ) → (∀ z ∈ range γ, HasDerivAt F (f z) z) →
    curveIntegral (scalarForm f) γ = F b - F a

theorem curveIntegralFun_ofLine_eq (φ φ' : ℝ → ℂ) (hφ : ContinuousOn φ (Icc 0 1))
    (hdφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' s) s) (f : ℂ → ℂ) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (scalarForm f) (Path.ofLine hφ rfl rfl) s = f (φ s) * φ' s := by
  have he : EqOn (Path.ofLine hφ rfl rfl).extend φ (Icc 0 1) := by
    intro t ht
    rw [Path.extend_apply _ ht]
    rfl
  rw [curveIntegralFun_def, he hs, derivWithin_congr he (he hs),
    (hdφ s hs).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one s hs), scalarForm_apply]

theorem range_ofLine_subset (φ : ℝ → ℂ) (hφ : ContinuousOn φ (Icc 0 1)) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) : φ s ∈ range (Path.ofLine hφ rfl rfl) :=
  ⟨⟨s, hs⟩, rfl⟩

/-- A C¹ parametrization on `[0,1]` gives a good path. -/
theorem goodPath_ofLine (φ φ' : ℝ → ℂ) (hφ : ContinuousOn φ (Icc 0 1))
    (hdφ : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' s) s) (hφ' : ContinuousOn φ' (Icc 0 1)) :
    GoodPath (Path.ofLine hφ rfl rfl) := by
  have hcomp : ∀ f : ℂ → ℂ, ContinuousOn f (range (Path.ofLine hφ rfl rfl)) →
      ContinuousOn (fun s => f (φ s) * φ' s) (Icc 0 1) := fun f hf =>
    (hf.comp hφ (fun s hs => range_ofLine_subset φ hφ s hs)).mul hφ'
  constructor
  · intro f hf
    unfold CurveIntegrable
    apply (intervalIntegrable_congr (g := fun s => f (φ s) * φ' s) ?_).mpr
      ((hcomp f hf).intervalIntegrable_of_Icc zero_le_one)
    intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    exact curveIntegralFun_ofLine_eq φ φ' hφ hdφ f s ⟨hs.1.le, hs.2⟩
  · intro F f hf hF
    rw [curveIntegral_def]
    rw [intervalIntegral.integral_congr (g := fun s => f (φ s) * φ' s) (fun s hs => by
      rw [uIcc_of_le zero_le_one] at hs
      exact curveIntegralFun_ofLine_eq φ φ' hφ hdφ f s hs)]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => F (φ s)) (fun s hs => ?_)
      ((hcomp f hf).intervalIntegrable_of_Icc zero_le_one)
    rw [uIcc_of_le zero_le_one] at hs
    exact (hF (φ s) (range_ofLine_subset φ hφ s hs)).comp s (hdφ s hs)

theorem GoodPath.cast {a b c d : ℂ} {γ : Path a b} (hγ : GoodPath γ) (hc : c = a) (hd : d = b) :
    GoodPath (γ.cast hc hd) := by
  have hr : range (γ.cast hc hd) = range γ := rfl
  constructor
  · intro f hf
    exact (hγ.integrable f (hr ▸ hf)).cast hc hd
  · intro F f hf hF
    rw [curveIntegral_cast, hγ.ftc F f (hr ▸ hf) (hr ▸ hF), hc, hd]

theorem GoodPath.trans {a b c : ℂ} {γ : Path a b} {δ : Path b c} (hγ : GoodPath γ)
    (hδ : GoodPath δ) : GoodPath (γ.trans δ) := by
  have hr : range (γ.trans δ) = range γ ∪ range δ := Path.trans_range γ δ
  constructor
  · intro f hf
    rw [hr] at hf
    exact (hγ.integrable f (hf.mono subset_union_left)).trans
      (hδ.integrable f (hf.mono subset_union_right))
  · intro F f hf hF
    rw [hr] at hf hF
    rw [curveIntegral_trans (hγ.integrable f (hf.mono subset_union_left))
        (hδ.integrable f (hf.mono subset_union_right)),
      hγ.ftc F f (hf.mono subset_union_left) (fun z hz => hF z (Or.inl hz)),
      hδ.ftc F f (hf.mono subset_union_right) (fun z hz => hF z (Or.inr hz))]
    ring

theorem GoodPath.symm {a b : ℂ} {γ : Path a b} (hγ : GoodPath γ) : GoodPath γ.symm := by
  have hr : range γ.symm = range γ := Path.symm_range γ
  constructor
  · intro f hf
    exact (hγ.integrable f (hr ▸ hf)).symm
  · intro F f hf hF
    rw [curveIntegral_symm, hγ.ftc F f (hr ▸ hf) (hr ▸ hF)]
    ring

theorem curveIntegralFun_map_conj {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) :
    curveIntegralFun (scalarForm f) (γ.map Complex.continuous_conj) =
      fun s => star (curveIntegralFun (scalarForm (fun z => star (f (star z)))) γ s) := by
  have he : ((γ.map Complex.continuous_conj).extend : ℝ → ℂ) = fun s => star (γ.extend s) := rfl
  funext s
  rw [curveIntegralFun_def, he, derivWithin.star, curveIntegralFun_def]
  simp [star_mul, mul_comm]

theorem range_map_conj {a b : ℂ} (γ : Path a b) (z : ℂ) :
    z ∈ range (γ.map Complex.continuous_conj) ↔ star z ∈ range γ := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, by change γ s = star (star (γ s)); rw [star_star]⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, by change star (γ s) = z; rw [hs, star_star]⟩

theorem GoodPath.map_conj {a b : ℂ} {γ : Path a b} (hγ : GoodPath γ) :
    GoodPath (γ.map Complex.continuous_conj) := by
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (range (γ.map Complex.continuous_conj)) →
      ContinuousOn (fun z => star (f (star z))) (range γ) := by
    intro f hf
    refine continuous_star.comp_continuousOn (hf.comp continuous_star.continuousOn ?_)
    intro z hz
    exact (range_map_conj γ (star z)).mpr (by simpa using hz)
  constructor
  · intro f hf
    have h := hγ.integrable _ (hcont f hf)
    unfold CurveIntegrable at h ⊢
    rw [curveIntegralFun_map_conj]
    exact ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp h.2⟩
  · intro F f hf hF
    have hG : ∀ z ∈ range γ, HasDerivAt (fun z => star (F (star z))) (star (f (star z))) z := by
      intro z hz
      have h1 := hF (star z) ((range_map_conj γ (star z)).mpr (by simpa using hz))
      have h2 := h1.conj_conj
      simpa [Function.comp_def] using h2
    have h := hγ.ftc _ _ (hcont f hf) hG
    rw [curveIntegral_def, curveIntegralFun_map_conj]
    simp only [Complex.star_def] at h ⊢
    rw [intervalIntegral.intervalIntegral_conj, ← curveIntegral_def, h]
    simp

theorem goodPath_refl (a : ℂ) : GoodPath (Path.refl a) := by
  have h := goodPath_ofLine (fun _ => a) (fun _ => 0) continuousOn_const
    (fun s _ => hasDerivAt_const s a) continuousOn_const
  have he : (Path.ofLine (continuousOn_const : ContinuousOn (fun _ : ℝ => a) (Icc 0 1))
      rfl rfl) = Path.refl a := by
    ext s
    rfl
  rw [← he]
  exact h

/-- Every affine segment is a good path. -/
theorem goodPath_segment (a b : ℂ) : GoodPath (Path.segment a b) := by
  let φ : ℝ → ℂ := AffineMap.lineMap a b
  have hφ : ContinuousOn φ (Icc 0 1) := by dsimp [φ]; fun_prop
  have hdφ (s : ℝ) (_ : s ∈ Icc (0 : ℝ) 1) : HasDerivAt φ (b - a) s :=
    AffineMap.hasDerivAt_lineMap
  have h := goodPath_ofLine φ (fun _ => b - a) hφ hdφ continuousOn_const
  have h0 : a = φ 0 := by simp [φ]
  have h1 : b = φ 1 := by simp [φ]
  have he : (Path.ofLine hφ rfl rfl).cast h0 h1 = Path.segment a b := by
    ext s
    rfl
  rw [← he]
  exact h.cast h0 h1

theorem goodPath_finiteLevelMeshPath (v : ℕ → ℂ) (M : ℕ) : GoodPath (finiteLevelMeshPath v M) := by
  induction M with
  | zero => exact goodPath_refl _
  | succ M ih => exact ih.trans (goodPath_segment _ _)

/-- The exact central level graph over `[a,b]` is a good path when the level is active. -/
theorem goodPath_actualLevelGraphPath {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x) :
    GoodPath (actualLevelGraphPath hN d t a b ht) := by
  let f : ℝ → ℂ := fun s => actualLevelGraphPoint d t (AffineMap.lineMap a b s)
  let f' : ℝ → ℂ := fun s => (b - a) •
    deriv (actualLevelGraphPoint d t) (AffineMap.lineMap a b s)
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : AffineMap.lineMap a b s ∈ Icc a b := by
    have hh : (Path.segment a b) ⟨s, hs⟩ ∈ range (Path.segment a b) := mem_range_self _
    rw [Path.range_segment, segment_eq_Icc hab] at hh
    exact hh
  have hactive (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      LevelActive d t (AffineMap.lineMap a b s) :=
    (levelHeight_pos_iff hN d t _ ht).mp (hheight _ (hp s hs))
  have hG : Continuous (actualLevelGraphPoint d t) := by
    unfold actualLevelGraphPoint
    exact Complex.continuous_ofReal.add
      ((Complex.continuous_ofReal.comp (levelHeight_continuous hN d t ht)).mul continuous_const)
  have hf : ContinuousOn f (Icc 0 1) := by dsimp [f]; fun_prop
  have hdf (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' s) s := by
    exact ((hasDerivAt_actualLevelGraphPoint hN d t _ ht (hactive s hs)).differentiableAt.hasDerivAt).scomp
      s AffineMap.hasDerivAt_lineMap
  have hC := (actualLevelGraphPoint_contDiffOn_active hN d t ht).continuousOn_deriv_of_isOpen
    (isOpen_levelActive hN d t ht) (by norm_num)
  have hdf' : ContinuousOn f' (Icc 0 1) :=
    (hC.comp (by fun_prop) hactive).const_smul (b - a)
  have hh := goodPath_ofLine f f' hf hdf hdf'
  have h0 : actualLevelGraphPoint d t a = f 0 := by simp [f]
  have h1 : actualLevelGraphPoint d t b = f 1 := by simp [f]
  have he : (Path.ofLine hf rfl rfl).cast h0 h1 = actualLevelGraphPath hN d t a b ht := by
    ext s
    rfl
  rw [← he]
  exact hh.cast h0 h1

theorem goodPath_graftedLevelUpperPath {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hab : a ≤ b) (vL vR : ℕ → ℂ) (ML MR : ℕ)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x) :
    GoodPath (graftedLevelUpperPath hN d t a b ht vL vR ML MR) :=
  (goodPath_finiteLevelMeshPath vL ML).trans ((goodPath_segment _ _).trans
    ((goodPath_actualLevelGraphPath hN d t a b ht hab hheight).trans
      ((goodPath_segment _ _).trans (goodPath_finiteLevelMeshPath vR MR))))

theorem GoodPath.reflectedLevelLoop {a b : ℂ} {upper : Path a b} (h : GoodPath upper) :
    GoodPath (reflectedLevelLoop upper) :=
  h.symm.trans ((goodPath_segment _ _).trans (h.map_conj.trans (goodPath_segment _ _)))

/-- The grafted level loop is a good path. -/
theorem goodPath_nativeGraftedLevelLoop {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) :
    GoodPath (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) := by
  have hg := graftedCentralGeometry hN d t tmax eta x₀ ht htmax heta hheight
  apply GoodPath.reflectedLevelLoop
  apply goodPath_graftedLevelUpperPath hN d t _ _ ht (le_trans hg.2.1.le hg.2.2.1.le)
  intro x hx
  have hh := levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight
    (hg.2.2.2.2 x hx)
  linarith

/-!
## Loop calculus of a good closed path
-/

theorem curveIntegral_congr_range {a b : ℂ} (γ : Path a b) (f g : ℂ → ℂ)
    (h : EqOn f g (range γ)) :
    curveIntegral (scalarForm f) γ = curveIntegral (scalarForm g) γ := by
  rw [curveIntegral_def, curveIntegral_def]
  congr 1
  funext s
  rw [curveIntegralFun_def, curveIntegralFun_def, scalarForm_apply, scalarForm_apply,
    h (show γ.extend s ∈ range γ from ⟨Set.projIcc 0 1 zero_le_one s, rfl⟩)]

/-- Primitive of `(z-p)^{-k}`, `k ≥ 2`, away from `p`. -/
theorem hasDerivAt_zpow_primitive (p z : ℂ) (k : ℕ) (hk : 2 ≤ k) (hz : z ≠ p) :
    HasDerivAt (fun w => (w - p) ^ ((1 : ℤ) - k) / ((1 : ℂ) - k)) (((z - p) ^ k)⁻¹) z := by
  have hzp : z - p ≠ 0 := sub_ne_zero.mpr hz
  have hk1 : (1 : ℂ) - k ≠ 0 := by
    intro h
    have h2 : (k : ℂ) = 1 := by linear_combination -h
    have : k = 1 := by exact_mod_cast h2
    omega
  have h1 := ((hasDerivAt_zpow ((1 : ℤ) - k) (z - p) (Or.inl hzp)).comp z
    ((hasDerivAt_id z).sub_const p)).div_const ((1 : ℂ) - k)
  convert h1 using 1
  · rfl
  · rw [show (1 : ℤ) - k - 1 = -(k : ℤ) by ring, zpow_neg, zpow_natCast]
    push_cast
    field_simp

/-- A good closed path inside `ball 0 ρ`, avoiding the poles `P ⊆ ball 0 ρ` and winding once
around each of them, is a loop calculus. -/
theorem GoodPath.loopCalculus {b : ℂ} {γ : Path b b} (hγ : GoodPath γ) {ρ : ℝ}
    (hρ : range γ ⊆ Metric.ball 0 ρ) {P : Set ℂ} (hP : P ⊆ Metric.ball 0 ρ)
    (havoid : ∀ p ∈ P, p ∉ range γ)
    (hres : ∀ p ∈ P, curveIntegral (scalarForm (fun z => (z - p)⁻¹)) γ =
      2 * Real.pi * Complex.I) :
    LoopCalculus (fun f => curveIntegral (scalarForm f) γ) (range γ) (Metric.ball 0 ρ) P where
  isOpen := Metric.isOpen_ball
  range_sub := hρ
  poles_sub := hP
  avoid := havoid
  congr := fun f g h => curveIntegral_congr_range γ f g h
  add := by
    intro f g hf hg
    have : scalarForm (fun z => f z + g z) = scalarForm f + scalarForm g := by
      funext z; simp only [scalarForm, Pi.add_apply]; exact add_smul (f z) (g z) (ContinuousLinearMap.id ℂ ℂ)
    rw [this, curveIntegral_add (hγ.integrable f hf) (hγ.integrable g hg)]
  smul := by
    intro c f
    have : scalarForm (fun z => c * f z) = c • scalarForm f := by
      funext z; simp only [scalarForm, Pi.smul_apply]; exact mul_smul c (f z) (ContinuousLinearMap.id ℂ ℂ)
    rw [this, curveIntegral_smul, smul_eq_mul]
  holo := by
    intro G hG
    obtain ⟨F, hF⟩ := hG.isExactOn_ball
    rw [hγ.ftc F G (hG.continuousOn.mono hρ) (fun z hz => hF z (hρ hz)), sub_self]
  res := hres
  pow := by
    intro p hp k hk
    have hne : ∀ z ∈ range γ, z ≠ p := fun z hz h => havoid p hp (h ▸ hz)
    have hcont : ContinuousOn (fun z => ((z - p) ^ k)⁻¹) (range γ) :=
      ((continuous_id.sub continuous_const).pow k).continuousOn.inv₀
        (fun z hz => pow_ne_zero _ (sub_ne_zero.mpr (hne z hz)))
    rw [hγ.ftc (fun w => (w - p) ^ ((1 : ℤ) - k) / ((1 : ℂ) - k)) _ hcont
      (fun z hz => hasDerivAt_zpow_primitive p z k hk (hne z hz)), sub_self]

/-- The poles of a real source, as a set of complex points. -/
def sourcePoles {N : ℕ} (d : Fin N → ℝ) : Set ℂ := {p | ∃ j, p = (d j : ℂ)}

/-- **The grafted level loop is a loop calculus** on any ball `ball 0 ρ` containing it
and the poles; poles are the source points, each wound once
(`nativeGraftedLevelLoop_resolvent`). -/
theorem graftedLoopCalculus {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) {ρ : ℝ}
    (hρ : range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) ⊆ Metric.ball 0 ρ)
    (hP : ∀ j, ‖(d j : ℂ)‖ < ρ) :
    LoopCalculus (fun f => curveIntegral (scalarForm f) (nativeGraftedLevelLoop hN d t tmax eta x₀ ht))
      (range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht)) (Metric.ball 0 ρ) (sourcePoles d) := by
  apply (goodPath_nativeGraftedLevelLoop hN d t tmax eta x₀ ht htmax heta hheight).loopCalculus hρ
  · rintro p ⟨j, rfl⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact hP j
  · rintro p ⟨j, rfl⟩ hp
    exact nativeGraftedLevelLoop_ne_pole hN d t tmax eta x₀ ht htmax heta hheight j _ hp rfl
  · rintro p ⟨j, rfl⟩
    exact (nativeGraftedLevelLoop_resolvent hN d t tmax eta x₀ ht htmax heta hheight j).2

/-- Every path lies in some ball about the origin. -/
theorem exists_range_subset_ball {a b : ℂ} (γ : Path a b) :
    ∃ ρ : ℝ, range γ ⊆ Metric.ball 0 ρ :=
  (isCompact_range γ.continuous).isBounded.subset_ball 0

end BlockBand.GaussianBulk
