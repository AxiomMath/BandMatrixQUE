module

public import BlockBand.GaussianBulk.ExternalSineHomologyResidue
public import BlockBand.GaussianBulk.LocalCrossingIntegral

/-!
# Norm bounds for curve integrals on the loop pieces

Length and graph bounds for curve integrals over the pieces of the grafted level loop.

* `PieceIntegrable f K`: `f dz` is curve integrable on every good path with range in `K`;
* `curveIntegral_map_conj_eq`: `∫_{γ̄} f = conj ∫_γ f*`, `f* = conj ∘ f ∘ conj`;
* `norm_curveIntegral_segment_le`, `norm_curveIntegral_finiteLevelMeshPath_le`: constant
  majorant times Euclidean length;
* `norm_curveIntegral_actualLevelGraphPath_le`: on the central graph `x ↦ x + i y(x)`,
  `‖∫ f‖ ≤ ∫_a^b g` whenever `‖f(x+iy(x))‖·|1 + i y'(x)| ≤ g(x)` for `x ≠ p` (one excluded
  point: the saddle, where the remainder integrand is not the vertical integral).

Domain: arbitrary complex endpoints; for the graph, `N > 0`, `t > 0`, `a < b`, positive level
height on `[a,b]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.GaussianBulk

open Set MeasureTheory Filter Topology
open scoped unitInterval

/-- `f dz` is curve integrable along every good path whose range lies in `K`. -/
def PieceIntegrable (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ {a b : ℂ} (δ : Path a b), GoodPath δ → range δ ⊆ K → CurveIntegrable (scalarForm f) δ

/-- `∫_{γ̄} f dz = conj (∫_γ f* dz)` with `f*(z) = conj (f (conj z))`. -/
theorem curveIntegral_map_conj_eq {a b : ℂ} (γ : Path a b) (f : ℂ → ℂ) :
    curveIntegral (scalarForm f) (γ.map Complex.continuous_conj) =
      star (curveIntegral (scalarForm (fun z => star (f (star z)))) γ) := by
  rw [curveIntegral_def, curveIntegralFun_map_conj, curveIntegral_def]
  simp only [Complex.star_def]
  exact intervalIntegral.intervalIntegral_conj

/-- Piecewise integrability passes to `f*` on the conjugate set. -/
theorem PieceIntegrable.conj {f : ℂ → ℂ} {K : Set ℂ} (hf : PieceIntegrable f K)
    (hK : ∀ z ∈ K, star z ∈ K) : PieceIntegrable (fun z => star (f (star z))) K := by
  intro a b δ hδ hr
  have hr' : range (δ.map Complex.continuous_conj) ⊆ K := by
    intro z hz
    have h1 := (range_map_conj δ z).mp hz
    simpa using hK _ (hr h1)
  have h := hf _ hδ.map_conj hr'
  unfold CurveIntegrable at h ⊢
  rw [curveIntegralFun_map_conj] at h
  have h2 : IntervalIntegrable (fun s => star (star
      (curveIntegralFun (scalarForm fun z => star (f (star z))) δ s))) volume 0 1 :=
    ⟨Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1,
      Complex.conjCLE.toContinuousLinearMap.integrable_comp h.2⟩
  simpa only [star_star] using h2

/-- Splitting a bound along `trans`. -/
theorem norm_curveIntegral_trans_le {f : ℂ → ℂ} {K : Set ℂ} (hf : PieceIntegrable f K)
    {a b c : ℂ} {γ : Path a b} {δ : Path b c} (hγ : GoodPath γ) (hδ : GoodPath δ)
    (hK : range (γ.trans δ) ⊆ K) {B₁ B₂ : ℝ}
    (h₁ : ‖curveIntegral (scalarForm f) γ‖ ≤ B₁) (h₂ : ‖curveIntegral (scalarForm f) δ‖ ≤ B₂) :
    ‖curveIntegral (scalarForm f) (γ.trans δ)‖ ≤ B₁ + B₂ := by
  rw [Path.trans_range] at hK
  rw [curveIntegral_trans (hf γ hγ (subset_union_left.trans hK))
    (hf δ hδ (subset_union_right.trans hK))]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

/-- Constant majorant on a segment: `‖∫_{[a,b]} f dz‖ ≤ K ‖b - a‖`. -/
theorem norm_curveIntegral_segment_le (f : ℂ → ℂ) (a b : ℂ) (K : ℝ)
    (hK : ∀ z ∈ range (Path.segment a b), ‖f z‖ ≤ K) :
    ‖curveIntegral (scalarForm f) (Path.segment a b)‖ ≤ K * ‖b - a‖ := by
  rw [curveIntegral_segment]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := K * ‖b - a‖)
    (f := fun s => (scalarForm f (AffineMap.lineMap a b s)) (b - a)) (fun s hs => by
      rw [uIoc_of_le zero_le_one] at hs
      have hmem : AffineMap.lineMap a b s ∈ range (Path.segment a b) := by
        refine ⟨⟨s, hs.1.le, hs.2⟩, ?_⟩
        simp [Path.segment_apply]
      rw [scalarForm_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right (hK _ hmem) (norm_nonneg _))
  simpa using h

/-- Constant majorant on a finite polygon: `K` times the sum of the edge lengths. -/
theorem norm_curveIntegral_finiteLevelMeshPath_le {f : ℂ → ℂ} {K : Set ℂ}
    (hf : PieceIntegrable f K) (v : ℕ → ℂ) (Kc : ℝ) (M : ℕ)
    (hr : range (finiteLevelMeshPath v M) ⊆ K)
    (hK : ∀ z ∈ range (finiteLevelMeshPath v M), ‖f z‖ ≤ Kc) :
    ‖curveIntegral (scalarForm f) (finiteLevelMeshPath v M)‖ ≤
      Kc * ∑ j : Fin M, ‖v (j.val + 1) - v j.val‖ := by
  induction M with
  | zero =>
    have h0 : curveIntegral (scalarForm f) (finiteLevelMeshPath v 0) = 0 := by
      rw [show finiteLevelMeshPath v 0 = Path.refl (v 0) from rfl, curveIntegral_refl]
    simp [h0]
  | succ M ih =>
    have hrange : range (finiteLevelMeshPath v (M + 1)) =
        range (finiteLevelMeshPath v M) ∪ range (Path.segment (v M) (v (M + 1))) :=
      Path.trans_range _ _
    have hr1 : range (finiteLevelMeshPath v M) ⊆ K := fun z hz => hr (hrange ▸ Or.inl hz)
    have hK1 : ∀ z ∈ range (finiteLevelMeshPath v M), ‖f z‖ ≤ Kc :=
      fun z hz => hK z (hrange ▸ Or.inl hz)
    have hK2 : ∀ z ∈ range (Path.segment (v M) (v (M + 1))), ‖f z‖ ≤ Kc :=
      fun z hz => hK z (hrange ▸ Or.inr hz)
    have h := norm_curveIntegral_trans_le hf (goodPath_finiteLevelMeshPath v M)
      (goodPath_segment _ _) hr (ih hr1 hK1)
      (norm_curveIntegral_segment_le f (v M) (v (M + 1)) Kc hK2)
    refine h.trans (le_of_eq ?_)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring

/-- The parametrization of the central graph path: `curveIntegralFun` at `s ∈ [0,1]` is
`f(z(x)) · (b - a)(1 + i y'(x))`, `x = a + s(b - a)`. -/
theorem curveIntegralFun_actualLevelGraphPath {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x) (f : ℂ → ℂ) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    curveIntegralFun (scalarForm f) (actualLevelGraphPath hN d t a b ht) s =
      f (actualLevelGraphPoint d t (AffineMap.lineMap a b s)) *
        ((b - a : ℝ) * levelGraphVelocity d t (AffineMap.lineMap a b s)) := by
  let φ : ℝ → ℂ := fun s => actualLevelGraphPoint d t (AffineMap.lineMap a b s)
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
  have hφ : ContinuousOn φ (Icc 0 1) := by dsimp [φ]; fun_prop
  have hdφ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt φ ((b - a) • levelGraphVelocity d t (AffineMap.lineMap a b s)) s := by
    have h1 := hasDerivAt_actualLevelGraphPoint hN d t _ ht (hactive s hs)
    exact h1.scomp s AffineMap.hasDerivAt_lineMap
  have he : EqOn (actualLevelGraphPath hN d t a b ht).extend φ (Icc 0 1) := by
    intro u hu
    rw [Path.extend_apply _ hu]
    rfl
  rw [curveIntegralFun_def, he hs, derivWithin_congr he (he hs),
    (hdφ s hs).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one s hs), scalarForm_apply]
  simp only [φ, Complex.real_smul]

/-- **Graph majorant.** On the central graph over `[a,b]`, if
`‖f(x + i y(x))‖ · ‖1 + i y'(x)‖ ≤ g x` for all `x ∈ [a,b]`, `x ≠ p`, with `g` interval
integrable, then `‖∫ f dz‖ ≤ ∫_a^b g`. -/
theorem norm_curveIntegral_actualLevelGraphPath_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hab : a < b)
    (hheight : ∀ x ∈ Icc a b, 0 < levelHeight d t x) (f : ℂ → ℂ) (g : ℝ → ℝ) (p : ℝ)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ x ∈ Icc a b, x ≠ p →
      ‖f (actualLevelGraphPoint d t x)‖ * ‖levelGraphVelocity d t x‖ ≤ g x) :
    ‖curveIntegral (scalarForm f) (actualLevelGraphPath hN d t a b ht)‖ ≤ ∫ x in a..b, g x := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hline (s : ℝ) : AffineMap.lineMap a b s = (b - a) * s + a := by
    simp [AffineMap.lineMap_apply]; ring
  -- change of variables `x = (b-a) s + a`
  have hcv : (∫ s in (0 : ℝ)..1, (b - a) * g ((b - a) * s + a)) = ∫ x in a..b, g x := by
    have h := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1) g (b - a) a
    simp only [smul_eq_mul, mul_zero, zero_add, mul_one, sub_add_cancel] at h
    rw [intervalIntegral.integral_const_mul]
    exact h
  have hgi : IntervalIntegrable (fun s => (b - a) * g ((b - a) * s + a)) volume 0 1 := by
    have h := (hg.comp_add_right a).comp_mul_left (c := b - a)
    have h' : IntervalIntegrable (fun s => g ((b - a) * s + a)) volume 0 1 := by
      have e0 : (a - a) / (b - a) = 0 := by simp
      have e1 : (b - a) / (b - a) = 1 := div_self hba.ne'
      rw [e0, e1] at h
      exact h
    exact h'.const_mul (b - a)
  rw [curveIntegral_def, ← hcv]
  refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ hgi
  -- the excluded parameter
  have hfin : ∀ᵐ s : ℝ, s ≠ (p - a) / (b - a) := by
    have : ({(p - a) / (b - a)} : Set ℝ)ᶜ ∈ ae volume := by
      rw [compl_mem_ae_iff]; exact measure_singleton _
    filter_upwards [this] with s hs
    simpa using hs
  filter_upwards [hfin] with s hsne hs
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  rw [curveIntegralFun_actualLevelGraphPath hN d t a b ht hab.le hheight f s hsI, hline,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hba.le]
  have hx : (b - a) * s + a ∈ Icc a b := by
    constructor <;> nlinarith [hsI.1, hsI.2]
  have hxp : (b - a) * s + a ≠ p := by
    intro h
    apply hsne
    field_simp
    linarith
  have := hfg _ hx hxp
  nlinarith [norm_nonneg (f (actualLevelGraphPoint d t ((b - a) * s + a))),
    norm_nonneg (levelGraphVelocity d t ((b - a) * s + a))]

end BlockBand.GaussianBulk
