module

public import BlockBand.GaussianBulk.ExternalSineHomologyCauchy
public import BlockBand.GaussianBulk.OrientedSineResidue

/-!
# The residue over the part of `γ` right of `Γ`

Moving the `w`-line onto `Γ` picks up a residue on the part of the grafted level loop `γ` to
the right of `Γ`; this file computes it and writes the kernel as residue plus remainder.

Here `γ = nativeGraftedLevelLoop hN d t tmax eta x₀ ht`, `Γ = x₀ + iℝ`,
`z₀ = actualLevelGraphPoint d t x₀ = x₀ + i·levelHeight d t x₀`, `κ = (u - v)/S` real.

* `residueIndicator κ x₀ z = 1_{Re z > x₀} · exp(κ z)`.
* `curveIntegral_residueIndicator_nativeGraftedLevelLoop`: `∫_γ 1_{Re z > x₀} e^{κz} dz =
  P(z₀) - P(z̄₀)`, `P` the exact primitive (arc ⇒ segment, by the FTC on each loop piece,
  splitting the central level graph at `x₀`).
* `residuePrimitive_sub_conj`: `P(x+iy) - P(x-iy) = upwardExponentialSegment x y κ`, the
  upward segment integral (whose normalization is the sine kernel,
  `normalizedSegmentResidue_eq`).
* `kernel_eq_residue_add_remainder`: **residue representation of the kernel**
  `kernel S d R L u v = pref · (∫_γ W dz + 2πi · upwardExponentialSegment x₀ y₀ κ)`, with the
  remainder integrand `W = V_{L'} - 2πi · residueIndicator κ x₀`, and
  `remainderIntegrand_eq_vertical`: `W(z) = V_{x₀}(z)` for every `z` with `Re z ≠ x₀`,
  `Re z < L'`, `z ∉ {d_j}` (in particular on `γ` minus the two saddles `z₀, z̄₀`).

Domain: `N > 0`, `S > 0`, arbitrary real (possibly repeated) source `d`, admissible `(R, L)`,
`0 < t ≤ tmax`, `0 < eta ≤ levelHeight d t x₀`, any `L' ≥ L` with `γ ⊆ ball 0 L'`.
All statements are exact identities.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology
open BlockBand.External
open scoped NNReal unitInterval

/-- `exp(κ z)`. -/
def residueExp (κ : ℝ) (z : ℂ) : ℂ := Complex.exp ((κ : ℂ) * z)

/-- The exact primitive of `exp(κ z)`. -/
def residuePrimitive (κ : ℝ) (z : ℂ) : ℂ :=
  if κ = 0 then z else Complex.exp ((κ : ℂ) * z) / (κ : ℂ)

/-- `1_{Re z > x₀} exp(κ z)`. -/
def residueIndicator (κ x₀ : ℝ) (z : ℂ) : ℂ := if x₀ < z.re then residueExp κ z else 0

theorem hasDerivAt_residuePrimitive (κ : ℝ) (z : ℂ) :
    HasDerivAt (residuePrimitive κ) (residueExp κ z) z := by
  unfold residuePrimitive residueExp
  by_cases hκ : κ = 0
  · simp only [hκ, ↓reduceIte, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    exact hasDerivAt_id z
  · simp only [hκ, ↓reduceIte]
    have hκ' : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ
    have h := ((hasDerivAt_id z).const_mul (κ : ℂ)).cexp.div_const (κ : ℂ)
    convert h using 1
    · rfl
    · simp only [id, mul_one]
      field_simp

theorem continuous_residueExp (κ : ℝ) : Continuous (residueExp κ) := by
  unfold residueExp; fun_prop

theorem residuePrimitive_conj (κ : ℝ) (z : ℂ) :
    residuePrimitive κ (star z) = star (residuePrimitive κ z) := by
  unfold residuePrimitive
  by_cases hκ : κ = 0
  · simp [hκ]
  · simp only [hκ, ↓reduceIte, Complex.star_def, map_div₀, Complex.conj_ofReal]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal]

theorem residueIndicator_conj (κ x₀ : ℝ) (z : ℂ) :
    star (residueIndicator κ x₀ (star z)) = residueIndicator κ x₀ z := by
  unfold residueIndicator residueExp
  simp only [Complex.star_def, Complex.conj_re]
  split_ifs
  · rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  · simp

theorem measurable_residueIndicator (κ x₀ : ℝ) : Measurable (residueIndicator κ x₀) := by
  unfold residueIndicator
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_re)
    (continuous_residueExp κ).measurable measurable_const

/-!
## Bounded measurable forms on good paths
-/

theorem GoodPath.integrable_of_bdd {a b : ℂ} {γ : Path a b} (hγ : GoodPath γ) (f : ℂ → ℂ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ z ∈ range γ, ‖f z‖ ≤ C) :
    CurveIntegrable (scalarForm f) γ := by
  have h1 := hγ.integrable (fun _ => 1) continuousOn_const
  have heq : curveIntegralFun (scalarForm f) γ =
      fun s => f (γ.extend s) * curveIntegralFun (scalarForm (fun _ => 1)) γ s := by
    funext s
    simp [curveIntegralFun_def]
  unfold CurveIntegrable at h1 ⊢
  rw [heq]
  rw [intervalIntegrable_iff] at h1 ⊢
  refine Integrable.bdd_mul (c := C) h1
    ((hf.comp γ.extend.continuous.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun s => hC _ ⟨Set.projIcc 0 1 zero_le_one s, rfl⟩)

theorem GoodPath.integrable_residueIndicator {a b : ℂ} {γ : Path a b} (hγ : GoodPath γ)
    (κ x₀ : ℝ) : CurveIntegrable (scalarForm (residueIndicator κ x₀)) γ := by
  obtain ⟨C, hC⟩ := (isCompact_range γ.continuous).exists_bound_of_continuousOn
    (continuous_residueExp κ).continuousOn
  refine hγ.integrable_of_bdd _ (measurable_residueIndicator κ x₀) C (fun z hz => ?_)
  unfold residueIndicator
  split_ifs
  · exact hC z hz
  · simpa using (norm_nonneg _).trans (hC z hz)

theorem GoodPath.residueIndicator_left {a b : ℂ} {γ : Path a b} (hγ : GoodPath γ) (κ x₀ : ℝ)
    (h : ∀ z ∈ range γ, z.re ≤ x₀) :
    curveIntegral (scalarForm (residueIndicator κ x₀)) γ = 0 := by
  rw [curveIntegral_congr_range γ _ (fun _ => 0) (fun z hz => by
    simp [residueIndicator, not_lt.mpr (h z hz)])]
  rw [hγ.ftc (fun _ => 0) (fun _ => 0) continuousOn_const (fun z _ => hasDerivAt_const z 0),
    sub_self]

theorem GoodPath.residueIndicator_right {a b : ℂ} {γ : Path a b} (hγ : GoodPath γ) (κ x₀ : ℝ)
    (h : ∀ z ∈ range γ, x₀ < z.re) :
    curveIntegral (scalarForm (residueIndicator κ x₀)) γ =
      residuePrimitive κ b - residuePrimitive κ a := by
  rw [curveIntegral_congr_range γ _ (residueExp κ) (fun z hz => by
    simp [residueIndicator, h z hz])]
  exact hγ.ftc _ _ (continuous_residueExp κ).continuousOn
    (fun z _ => hasDerivAt_residuePrimitive κ z)

theorem segment_re_bounds' {a b : ℂ} {lo hi : ℝ}
    (ha : lo ≤ a.re ∧ a.re ≤ hi) (hb : lo ≤ b.re ∧ b.re ≤ hi)
    (z : ℂ) (hz : z ∈ range (Path.segment a b)) : lo ≤ z.re ∧ z.re ≤ hi := by
  obtain ⟨s, rfl⟩ := hz
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, Complex.add_re,
    Complex.smul_re, smul_eq_mul]
  have hs0 := s.property.1
  have hs1 : 0 ≤ 1 - (s : ℝ) := sub_nonneg.mpr s.property.2
  have hlA := mul_le_mul_of_nonneg_left ha.1 hs1
  have hlB := mul_le_mul_of_nonneg_left hb.1 hs0
  have huA := mul_le_mul_of_nonneg_left ha.2 hs1
  have huB := mul_le_mul_of_nonneg_left hb.2 hs0
  constructor <;> nlinarith

/-!
## The central level graph, split at `x₀`
-/

theorem actualLevelGraphPath_residueIndicator {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x)
    (κ x₀ : ℝ) (hax : a < x₀) (hxb : x₀ < b) :
    curveIntegral (scalarForm (residueIndicator κ x₀)) (actualLevelGraphPath hN d t a b ht) =
      residuePrimitive κ (actualLevelGraphPoint d t b) -
        residuePrimitive κ (actualLevelGraphPoint d t x₀) := by
  have hab : a ≤ b := by linarith
  let f : ℝ → ℂ := fun s => actualLevelGraphPoint d t (AffineMap.lineMap a b s)
  let f' : ℝ → ℂ := fun s => (b - a) •
    deriv (actualLevelGraphPoint d t) (AffineMap.lineMap a b s)
  have hlm : ∀ s : ℝ, AffineMap.lineMap a b s = a + s * (b - a) := by
    intro s; rw [AffineMap.lineMap_apply_ring']; ring
  have hp (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : AffineMap.lineMap a b s ∈ Icc a b := by
    rw [hlm]
    constructor <;> nlinarith [hs.1, hs.2]
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
  have h0 : actualLevelGraphPoint d t a = f 0 := by simp [f]
  have h1 : actualLevelGraphPoint d t b = f 1 := by simp [f]
  have he : (Path.ofLine hf rfl rfl).cast h0 h1 = actualLevelGraphPath hN d t a b ht := by
    ext s
    rfl
  have hre : ∀ s : ℝ, (f s).re = a + s * (b - a) := by
    intro s; simp [f, actualLevelGraphPoint, hlm]
  set s₀ : ℝ := (x₀ - a) / (b - a) with hs₀
  have hba : 0 < b - a := by linarith
  have hs₀0 : 0 < s₀ := div_pos (by linarith) hba
  have hs₀1 : s₀ < 1 := (div_lt_one hba).mpr (by linarith)
  have hxs : a + s₀ * (b - a) = x₀ := by rw [hs₀]; field_simp; ring
  have hfs₀ : f s₀ = actualLevelGraphPoint d t x₀ := by
    simp only [f]; rw [hlm, hxs]
  set g : ℝ → ℂ := fun s => residueIndicator κ x₀ (f s) * f' s with hg
  set g₁ : ℝ → ℂ := fun s => residueExp κ (f s) * f' s with hg₁
  have hcont₁ : ContinuousOn g₁ (Icc 0 1) :=
    ((continuous_residueExp κ).comp_continuousOn hf).mul hdf'
  have hleft : EqOn g (fun _ => 0) (uIoc 0 s₀) := by
    intro s hs
    rw [uIoc_of_le hs₀0.le] at hs
    have : ¬ x₀ < (f s).re := by
      rw [hre]; push Not
      have := mul_le_mul_of_nonneg_right hs.2 hba.le
      linarith
    simp [hg, residueIndicator, this]
  have hright : EqOn g g₁ (uIoc s₀ 1) := by
    intro s hs
    rw [uIoc_of_le hs₀1.le] at hs
    have : x₀ < (f s).re := by
      rw [hre]
      have := mul_lt_mul_of_pos_right hs.1 hba
      linarith
    simp [hg, hg₁, residueIndicator, this]
  have hIcc : Icc s₀ 1 ⊆ Icc 0 1 := Icc_subset_Icc hs₀0.le le_rfl
  have hint₁ : IntervalIntegrable g₁ volume s₀ 1 :=
    (hcont₁.mono hIcc).intervalIntegrable_of_Icc hs₀1.le
  have hintL : IntervalIntegrable g volume 0 s₀ :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr (fun s hs => (hleft hs).symm)
  have hintR : IntervalIntegrable g volume s₀ 1 :=
    hint₁.congr (fun s hs => (hright hs).symm)
  rw [← he, curveIntegral_cast, curveIntegral_def]
  rw [intervalIntegral.integral_congr (g := g) (fun s hs => by
    rw [uIcc_of_le zero_le_one] at hs
    exact curveIntegralFun_ofLine_eq f f' hf hdf _ s hs)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hintL hintR,
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => hleft hs),
    intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => hright hs),
    intervalIntegral.integral_zero, zero_add, h1, ← hfs₀]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => residuePrimitive κ (f s))
    (fun s hs => ?_) hint₁
  rw [uIcc_of_le hs₀1.le] at hs
  exact (hasDerivAt_residuePrimitive κ (f s)).comp s (hdf s (hIcc hs))

/-!
## The upper path and the reflected loop
-/

theorem graftedLevelUpperPath_residueIndicator {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (vL vR : ℕ → ℂ) (ML MR : ℕ)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x)
    (κ x₀ loL hiR : ℝ) (hax : a < x₀) (hxb : x₀ < b)
    (hL : ∀ j ≤ ML, loL ≤ (vL j).re ∧ (vL j).re ≤ a)
    (hR : ∀ j ≤ MR, b ≤ (vR j).re ∧ (vR j).re ≤ hiR) :
    curveIntegral (scalarForm (residueIndicator κ x₀))
        (graftedLevelUpperPath hN d t a b ht vL vR ML MR) =
      residuePrimitive κ (vR MR) - residuePrimitive κ (actualLevelGraphPoint d t x₀) := by
  have hab : a ≤ b := by linarith
  have gL := goodPath_finiteLevelMeshPath vL ML
  have gR := goodPath_finiteLevelMeshPath vR MR
  have gG := goodPath_actualLevelGraphPath hN d t a b ht hab hheight
  have g1 := goodPath_segment (vL ML) (actualLevelGraphPoint d t a)
  have g2 := goodPath_segment (actualLevelGraphPoint d t b) (vR 0)
  have hGa : (actualLevelGraphPoint d t a).re = a := by simp [actualLevelGraphPoint]
  have hGb : (actualLevelGraphPoint d t b).re = b := by simp [actualLevelGraphPoint]
  have iL := gL.integrable_residueIndicator κ x₀
  have iR := gR.integrable_residueIndicator κ x₀
  have iG := gG.integrable_residueIndicator κ x₀
  have i1 := g1.integrable_residueIndicator κ x₀
  have i2 := g2.integrable_residueIndicator κ x₀
  have eL := gL.residueIndicator_left κ x₀ (fun z hz => by
    have := (finiteLevelMeshPath_re_bounds vL ML loL a hL z hz).2
    linarith)
  have e1 := g1.residueIndicator_left κ x₀ (fun z hz => by
    have hM := hL ML le_rfl
    have := (segment_re_bounds' (lo := loL) (hi := a) hM ⟨by linarith, by linarith⟩ z hz).2
    linarith)
  have eG := actualLevelGraphPath_residueIndicator hN d t a b ht hheight κ x₀ hax hxb
  have e2 := g2.residueIndicator_right κ x₀ (fun z hz => by
    have h0 := hR 0 (Nat.zero_le _)
    have := (segment_re_bounds' (lo := b) (hi := hiR) ⟨by linarith, by linarith⟩ h0 z hz).1
    linarith)
  have eR := gR.residueIndicator_right κ x₀ (fun z hz => by
    have := (finiteLevelMeshPath_re_bounds vR MR b hiR hR z hz).1
    linarith)
  unfold graftedLevelUpperPath
  rw [curveIntegral_trans iL (i1.trans (iG.trans (i2.trans iR))),
    curveIntegral_trans i1 (iG.trans (i2.trans iR)),
    curveIntegral_trans iG (i2.trans iR), curveIntegral_trans i2 iR, eL, e1, eG, e2, eR]
  ring

theorem curveIntegral_residueIndicator_map_conj {a b : ℂ} (γ : Path a b) (κ x₀ : ℝ) :
    curveIntegral (scalarForm (residueIndicator κ x₀)) (γ.map Complex.continuous_conj) =
      star (curveIntegral (scalarForm (residueIndicator κ x₀)) γ) := by
  have hf : (fun z => star (residueIndicator κ x₀ (star z))) = residueIndicator κ x₀ :=
    funext (residueIndicator_conj κ x₀)
  rw [curveIntegral_def, curveIntegralFun_map_conj, hf, curveIntegral_def]
  simp only [Complex.star_def]
  exact intervalIntegral.intervalIntegral_conj

theorem reflectedLevelLoop_residueIndicator {A Bn : ℂ} (upper : Path A Bn) (hup : GoodPath upper)
    (κ x₀ : ℝ) (z₀ : ℂ) (hA : A.re < x₀) (hB : x₀ < Bn.re)
    (hval : curveIntegral (scalarForm (residueIndicator κ x₀)) upper =
      residuePrimitive κ Bn - residuePrimitive κ z₀) :
    curveIntegral (scalarForm (residueIndicator κ x₀)) (reflectedLevelLoop upper) =
      residuePrimitive κ z₀ - residuePrimitive κ (star z₀) := by
  have gA := goodPath_segment A (star A)
  have gB := goodPath_segment (star Bn) Bn
  have gC := hup.map_conj
  have iU := hup.integrable_residueIndicator κ x₀
  have iA := gA.integrable_residueIndicator κ x₀
  have iB := gB.integrable_residueIndicator κ x₀
  have iC := gC.integrable_residueIndicator κ x₀
  have eA := gA.residueIndicator_left κ x₀ (fun z hz => by
    have := (segment_re_bounds' (lo := A.re) (hi := A.re) ⟨le_rfl, le_rfl⟩ (by simp) z hz).2
    linarith)
  have eB := gB.residueIndicator_right κ x₀ (fun z hz => by
    have := (segment_re_bounds' (lo := Bn.re) (hi := Bn.re) (by simp) ⟨le_rfl, le_rfl⟩ z hz).1
    linarith)
  have eC : curveIntegral (scalarForm (residueIndicator κ x₀)) (upper.map Complex.continuous_conj) =
      residuePrimitive κ (star Bn) - residuePrimitive κ (star z₀) := by
    rw [curveIntegral_residueIndicator_map_conj, hval, star_sub, ← residuePrimitive_conj,
      ← residuePrimitive_conj]
  unfold reflectedLevelLoop
  rw [curveIntegral_trans iU.symm (iA.trans (iC.trans iB)), curveIntegral_symm,
    curveIntegral_trans iA (iC.trans iB), curveIntegral_trans iC iB, hval, eA, eC, eB]
  ring

/-- **Arc ⇒ segment** on the grafted level loop: the residue integrated over the part
of `γ` to the right of `Γ = x₀ + iℝ` is `P(z₀) - P(z̄₀)`. -/
theorem curveIntegral_residueIndicator_nativeGraftedLevelLoop {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀) (κ : ℝ) :
    curveIntegral (scalarForm (residueIndicator κ x₀))
        (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) =
      residuePrimitive κ (actualLevelGraphPoint d t x₀) -
        residuePrimitive κ (star (actualLevelGraphPoint d t x₀)) := by
  have hg := graftedCentralGeometry hN d t tmax eta x₀ ht htmax heta hheight
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcap : 0 < Real.sqrt t / (2 * (N : ℝ) ^ 2) := by positivity
  have hLa := hg.1
  have hbR := hg.2.2.2.1
  have hleft := (graftedLevelMesh_endpoint_re d t _ _ _ hLa hcap).1
  have hright := (graftedLevelMesh_endpoint_re d t _ _ _ hbR hcap).2
  have hheight' : ∀ x ∈ Icc (x₀ - graftedCentralRadius tmax eta)
      (x₀ + graftedCentralRadius tmax eta), 0 < levelHeight d t x := by
    intro x hx
    have hh := levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight
      (hg.2.2.2.2 x hx)
    linarith
  unfold nativeGraftedLevelLoop actualGraftedLevelLoop
  apply reflectedLevelLoop_residueIndicator _
    (goodPath_graftedLevelUpperPath hN d t _ _ ht (le_trans hg.2.1.le hg.2.2.1.le) _ _ _ _
      hheight')
  · rw [hleft]; linarith [hg.2.1]
  · rw [hright]; linarith [hg.2.2.1]
  · exact graftedLevelUpperPath_residueIndicator hN d t _ _ ht _ _ _ _ hheight' κ x₀ _ _
      hg.2.1 hg.2.2.1 (graftedLevelMeshVertex_re_bounds d t _ _ _ hLa hcap)
      (graftedLevelMeshVertex_re_bounds d t _ _ _ hbR hcap)

/-- The segment `z̄ → z` of the residue: `P(x+iy) - P(x-iy)` is the upward segment
integral `upwardExponentialSegment x y κ = ∫_{-1}^{1} e^{κ(x+iys)} iy ds`. -/
theorem residuePrimitive_sub_conj (κ x y : ℝ) :
    residuePrimitive κ ((x : ℂ) + (y : ℂ) * Complex.I) -
        residuePrimitive κ (star ((x : ℂ) + (y : ℂ) * Complex.I)) =
      upwardExponentialSegment x y κ := by
  set ψ : ℝ → ℂ := fun s => (x : ℂ) + ((y * s : ℝ) : ℂ) * Complex.I with hψ
  have hdψ : ∀ s : ℝ, HasDerivAt ψ ((y : ℂ) * Complex.I) s := by
    intro s
    have h := (((hasDerivAt_id s).const_mul y).ofReal_comp).mul_const Complex.I
    have h2 := h.const_add (x : ℂ)
    convert h2 using 1
    · funext s; simp [hψ]
    · simp
  have hcont : Continuous (fun s : ℝ => residueExp κ (ψ s) * ((y : ℂ) * Complex.I)) :=
    ((continuous_residueExp κ).comp (by rw [hψ]; fun_prop)).mul continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => residuePrimitive κ (ψ s)) (a := -1) (b := 1)
    (fun s _ => (hasDerivAt_residuePrimitive κ (ψ s)).comp s (hdψ s))
    (hcont.intervalIntegrable _ _)
  have h1 : ψ 1 = (x : ℂ) + (y : ℂ) * Complex.I := by simp [hψ]
  have hm1 : ψ (-1) = star ((x : ℂ) + (y : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp [hψ]
  rw [← hm1, ← h1]
  unfold upwardExponentialSegment
  rw [← h]
  rfl

/-!
## The residue representation
-/

/-- The remainder integrand `W = V_{L'} - 2πi · 1_{Re z > x₀} e^{κ z}`, `κ = (u-v)/S`. -/
def remainderIntegrand {N : ℕ} (S : ℝ≥0) (d : Fin N → ℝ) (u v L' x₀ : ℝ) (z : ℂ) : ℂ :=
  Johansson.verticalIntegral S d u v L' z -
    2 * Real.pi * Complex.I * residueIndicator ((u - v) / S) x₀ z

/-- Off the vertical line `Re z = x₀` (and the poles), the remainder integrand is the vertical
integral on `Γ = x₀ + iℝ` itself: `W(z) = V_{x₀}(z)`. -/
theorem remainderIntegrand_eq_vertical {N : ℕ} (S : ℝ≥0) (hS : 0 < S) (d : Fin N → ℝ)
    (u v L' x₀ : ℝ) (z : ℂ) (hz : z.re ≠ x₀) (hzL : z.re < L')
    (hzd : ∀ j, z ≠ (d j : ℂ)) :
    remainderIntegrand S d u v L' x₀ z = Johansson.verticalIntegral S d u v x₀ z := by
  unfold remainderIntegrand residueIndicator
  rcases lt_or_gt_of_ne hz with h | h
  · simp only [not_lt.mpr h.le, ↓reduceIte, mul_zero, sub_zero]
    apply verticalIntegral_shift S hS d u v L' x₀ z
    exact lt_min hzL h
  · simp only [h, ↓reduceIte]
    have hc := verticalIntegral_cross S hS d u v L' x₀ z h hzL hzd
    have he : residueExp ((u - v) / S) z = Complex.exp (((u : ℂ) - v) * z / S) := by
      unfold residueExp
      congr 1
      push_cast
      ring
    rw [he]
    linear_combination hc

/-- **Residue representation of the kernel.** For `N > 0`, `S > 0`, any real source `d`,
admissible `(R, L)`, the loop `γ = nativeGraftedLevelLoop hN d t tmax eta x₀ ht` and any
`L' ≥ L` with `γ ⊆ ball 0 L'`:
`kernel S d R L u v = exp((v²-u²)/(2S))/((2πi)² S) ·
  (∫_γ W(z) dz + 2πi · upwardExponentialSegment x₀ y₀ ((u-v)/S))`,
`y₀ = levelHeight d t x₀`, `W = remainderIntegrand` (`= V_{x₀}` off `Re z = x₀`). -/
theorem kernel_eq_residue_add_remainder {N : ℕ} (hN : 0 < N) (S : ℝ≥0) (hS : 0 < S)
    (d : Fin N → ℝ) (R L : ℝ) (hC : Johansson.AdmissibleContours d R L) (u v : ℝ)
    (t tmax eta x₀ : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀) (L' : ℝ) (hLL' : L ≤ L')
    (hball : range (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) ⊆ Metric.ball 0 L') :
    Johansson.kernel S d R L u v =
      Complex.exp (((v : ℂ) ^ 2 - (u : ℂ) ^ 2) / (2 * (S : ℂ))) /
        (((2 * (Real.pi : ℂ) * Complex.I) ^ 2) * (S : ℂ)) *
        (curveIntegral (scalarForm (remainderIntegrand S d u v L' x₀))
            (nativeGraftedLevelLoop hN d t tmax eta x₀ ht) +
          2 * Real.pi * Complex.I *
            upwardExponentialSegment x₀ (levelHeight d t x₀) ((u - v) / S)) := by
  set γ := nativeGraftedLevelLoop hN d t tmax eta x₀ ht with hγdef
  set κ : ℝ := (u - v) / S with hκ
  set c : ℂ := 2 * Real.pi * Complex.I with hc
  have gγ := goodPath_nativeGraftedLevelLoop hN d t tmax eta x₀ ht htmax heta hheight
  rw [kernel_eq_graftedLoop hN S hS d R L hC u v t tmax eta x₀ ht htmax heta hheight L' hLL'
    hball]
  congr 1
  -- integrability of `V_{L'}` on `γ`
  have hnot : ∀ z ∈ range γ, ∀ p ∈ sourcePoleList d, z ≠ p := by
    intro z hz p hp h
    obtain ⟨j, rfl⟩ := mem_sourcePoles_of_mem_list d p hp
    exact nativeGraftedLevelLoop_ne_pole hN d t tmax eta x₀ ht htmax heta hheight j z hz h
  have hVc : ContinuousOn (Johansson.verticalIntegral S d u v L') (range γ) := by
    rw [show Johansson.verticalIntegral S d u v L' =
        fun z => kernelNumerator S d u v L' z * (poleProd (sourcePoleList d) z)⁻¹ from
      funext (verticalIntegral_eq_numerator S d u v L')]
    exact ((differentiableOn_kernelNumerator S hS d u v L').continuousOn.mono
      (hball.trans (ball_subset_re_lt L'))).mul
      ((continuous_poleProd _).continuousOn.inv₀ (fun z hz => poleProd_ne_zero (hnot z hz)))
  have iV := gγ.integrable _ hVc
  have iI := gγ.integrable_residueIndicator κ x₀
  obtain ⟨C, hCb⟩ := (isCompact_range γ.continuous).exists_bound_of_continuousOn
    (continuous_residueExp κ).continuousOn
  have icI : CurveIntegrable (scalarForm (fun z => c * residueIndicator κ x₀ z)) γ := by
    refine gγ.integrable_of_bdd _ (measurable_const.mul (measurable_residueIndicator κ x₀))
      (‖c‖ * C) (fun z hz => ?_)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold residueIndicator
    split_ifs
    · exact hCb z hz
    · simpa using (norm_nonneg _).trans (hCb z hz)
  have hW : scalarForm (remainderIntegrand S d u v L' x₀) =
      scalarForm (Johansson.verticalIntegral S d u v L') -
        scalarForm (fun z => c * residueIndicator κ x₀ z) := by
    funext z
    simp only [scalarForm, remainderIntegrand, Pi.sub_apply, hc, hκ]
    exact sub_smul (Johansson.verticalIntegral S d u v L' z)
      (2 * Real.pi * Complex.I * residueIndicator ((u - v) / S) x₀ z) (ContinuousLinearMap.id ℂ ℂ)
  have hsm : scalarForm (fun z => c * residueIndicator κ x₀ z) =
      c • scalarForm (residueIndicator κ x₀) := by
    funext z
    simp only [scalarForm, Pi.smul_apply]
    exact mul_smul c _ (ContinuousLinearMap.id ℂ ℂ)
  rw [hW, curveIntegral_sub iV icI, hsm, curveIntegral_smul, smul_eq_mul,
    curveIntegral_residueIndicator_nativeGraftedLevelLoop hN d t tmax eta x₀ ht htmax heta
      hheight κ]
  unfold actualLevelGraphPoint
  rw [residuePrimitive_sub_conj]
  ring

end BlockBand.GaussianBulk
