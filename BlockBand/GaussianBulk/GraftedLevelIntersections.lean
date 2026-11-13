module
public import BlockBand.GaussianBulk.GraftedLevelContour

/-!
# Intersections of the grafted level loop with the saddle line

The upper path of the grafted loop meets the vertical line through an interior point `x` only at
the level graph point over `x`; hence the closed loop meets the saddle line exactly at the
conjugate saddle pair.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set
open scoped unitInterval

private theorem segment_re_bounds {a b : ℂ} {lo hi : ℝ}
    (ha : lo ≤ a.re ∧ a.re ≤ hi) (hb : lo ≤ b.re ∧ b.re ≤ hi)
    (z : ℂ) (hz : z ∈ range (Path.segment a b)) : lo ≤ z.re ∧ z.re ≤ hi := by
  obtain ⟨s,rfl⟩ := hz
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module,Complex.add_re,
    Complex.smul_re,smul_eq_mul]
  have hs0 := s.property.1
  have hs1 : 0 ≤ 1-(s : ℝ) := sub_nonneg.mpr s.property.2
  have hlA := mul_le_mul_of_nonneg_left ha.1 hs1
  have hlB := mul_le_mul_of_nonneg_left hb.1 hs0
  have huA := mul_le_mul_of_nonneg_left ha.2 hs1
  have huB := mul_le_mul_of_nonneg_left hb.2 hs0
  constructor <;> nlinarith

/-- Every point of a polygonal mesh lies in any real interval containing the real parts of its
vertices. -/
theorem finiteLevelMeshPath_re_bounds (v : ℕ → ℂ) (M : ℕ) (lo hi : ℝ)
    (hv : ∀ j ≤ M, lo ≤ (v j).re ∧ (v j).re ≤ hi) :
    ∀ z ∈ range (finiteLevelMeshPath v M), lo ≤ z.re ∧ z.re ≤ hi := by
  induction M with
  | zero =>
    intro z hz
    have hz' : z = v 0 := by simpa [finiteLevelMeshPath] using hz
    exact hz' ▸ hv 0 (by omega)
  | succ M ih =>
    intro z hz
    change z ∈ range ((finiteLevelMeshPath v M).trans (Path.segment (v M) (v (M+1)))) at hz
    rw [Path.trans_range] at hz
    exact hz.elim (ih (fun j hj => hv j (by omega)) z)
      (segment_re_bounds (hv M (by omega)) (hv (M+1) le_rfl) z)

/-- Every vertex of the ceiling partition lies in its real interval. -/
theorem graftedLevelMeshVertex_re_bounds {N : ℕ} (d : Fin N → ℝ)
    (t a b h : ℝ) (hab : a < b) (hh : 0 < h) (j : ℕ)
    (hj : j ≤ graftedLevelMeshCount a b h) :
    a ≤ (raisedLevelMeshVertex d t a (graftedLevelMeshSpacing a b h) j).re ∧
      (raisedLevelMeshVertex d t a (graftedLevelMeshSpacing a b h) j).re ≤ b := by
  have hs := (graftedLevelMeshSpacing_bounds a b h hab hh).1.le
  have hM := (graftedLevelMesh_endpoint_re d t a b h hab hh).2
  simp [raisedLevelMeshVertex] at hM ⊢
  have hj' : (j : ℝ) ≤ (graftedLevelMeshCount a b h : ℝ) := by exact_mod_cast hj
  have hlo := mul_nonneg (show 0 ≤ (j : ℝ) by positivity) hs
  have hhi := mul_le_mul_of_nonneg_right hj' hs
  constructor <;> linarith

/-- For `x` strictly between the graft endpoints, the upper path meets the vertical line
`Re z = x` only at the level graph point over `x`. -/
theorem actualGraftedLevelUpperPath_vertical {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t L a b R h x : ℝ) (ht : 0 < t)
    (hLa : L < a) (hax : a < x) (hxb : x < b) (hbR : b < R) (hh : 0 < h) :
    ∀ z ∈ range (graftedLevelUpperPath hN d t a b ht
      (raisedLevelMeshVertex d t L (graftedLevelMeshSpacing L a h))
      (raisedLevelMeshVertex d t b (graftedLevelMeshSpacing b R h))
      (graftedLevelMeshCount L a h) (graftedLevelMeshCount b R h)),
      z.re = x → z = actualLevelGraphPoint d t x := by
  have hl := finiteLevelMeshPath_re_bounds
    (raisedLevelMeshVertex d t L (graftedLevelMeshSpacing L a h))
    (graftedLevelMeshCount L a h) L a
    (graftedLevelMeshVertex_re_bounds d t L a h hLa hh)
  have hr := finiteLevelMeshPath_re_bounds
    (raisedLevelMeshVertex d t b (graftedLevelMeshSpacing b R h))
    (graftedLevelMeshCount b R h) b R
    (graftedLevelMeshVertex_re_bounds d t b R h hbR hh)
  have hleft := (graftedLevelMesh_endpoint_re d t L a h hLa hh).2
  have hright := (graftedLevelMesh_endpoint_re d t b R h hbR hh).1
  intro z hz hx
  unfold graftedLevelUpperPath at hz
  simp only [Path.trans_range,mem_union] at hz
  rcases hz with hz | hz | hz | hz | hz
  · have hb := (hl z hz).2
    linarith
  · have hb := segment_re_bounds (lo := a) (hi := a)
      (by rw [hleft];exact ⟨le_rfl,le_rfl⟩)
      (by simp [actualLevelGraphPoint]) z hz
    linarith [hb.2]
  · have hz' := (actualLevelGraphPath_mem hN d t a b ht (by linarith) z hz).2
    simpa only [hx] using hz'
  · have hb := segment_re_bounds (lo := b) (hi := b)
      (by simp [actualLevelGraphPoint])
      (by rw [hright];exact ⟨le_rfl,le_rfl⟩) z hz
    linarith [hb.1]
  · have hb := (hr z hz).1
    linarith

/-- If the upper arc meets a vertical line in a single point, the reflected loop meets it exactly
in that point and its conjugate. -/
theorem reflectedLevelLoop_vertical_pair {a b : ℂ} (upper : Path a b)
    (x : ℝ) (z₀ : ℂ) (hx₀ : z₀.re = x)
    (hax : a.re < x) (hxb : x < b.re)
    (hu : ∀ z ∈ range upper, z.re = x → z = z₀)
    (z : ℂ) (hz : z ∈ range (reflectedLevelLoop upper)) :
    z.re = x ↔ z = z₀ ∨ z = star z₀ := by
  constructor
  · intro hx
    unfold reflectedLevelLoop at hz
    simp only [Path.trans_range,Path.symm_range,mem_union] at hz
    rcases hz with hz | hz | hz | hz
    · exact Or.inl (hu z hz hx)
    · have hb := segment_re_bounds (lo := a.re) (hi := a.re)
        ⟨le_rfl,le_rfl⟩ (by simp) z hz
      linarith [hb.2]
    · obtain ⟨s,rfl⟩ := hz
      have hx' : (upper s).re = x := by
        change (star (upper s)).re = x at hx
        simpa only [Complex.star_def,Complex.conj_re] using hx
      have he := hu (upper s) (mem_range_self s) hx'
      exact Or.inr (congrArg star he)
    · have hb := segment_re_bounds (lo := b.re) (hi := b.re)
        (by simp) ⟨le_rfl,le_rfl⟩ z hz
      linarith [hb.1]
  · rintro (rfl | rfl)
    · exact hx₀
    · simpa only [Complex.star_def,Complex.conj_re] using hx₀

/-- The grafted level loop meets the saddle vertical line exactly at the conjugate saddle pair. -/
theorem actualGraftedLevelLoop_vertical_pair {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t L a b R h x₀ : ℝ) (ht : 0 < t)
    (hLa : L < a) (hax : a < x₀) (hxb : x₀ < b) (hbR : b < R) (hh : 0 < h)
    (z : ℂ) (hz : z ∈ range (actualGraftedLevelLoop hN d t L a b R h ht)) :
    z.re = x₀ ↔ z = actualLevelGraphPoint d t x₀ ∨
      z = star (actualLevelGraphPoint d t x₀) := by
  have hleft := (graftedLevelMesh_endpoint_re d t L a h hLa hh).1
  have hright := (graftedLevelMesh_endpoint_re d t b R h hbR hh).2
  apply reflectedLevelLoop_vertical_pair
    (graftedLevelUpperPath hN d t a b ht
      (raisedLevelMeshVertex d t L (graftedLevelMeshSpacing L a h))
      (raisedLevelMeshVertex d t b (graftedLevelMeshSpacing b R h))
      (graftedLevelMeshCount L a h) (graftedLevelMeshCount b R h))
    x₀ (actualLevelGraphPoint d t x₀)
  · simp [actualLevelGraphPoint]
  · simpa only [hleft] using lt_trans hLa hax
  · simpa only [hright] using lt_trans hxb hbR
  · exact actualGraftedLevelUpperPath_vertical hN d t L a b R h x₀ ht hLa hax hxb hbR hh
  · exact hz

end BlockBand.GaussianBulk
