module
public import BlockBand.GaussianBulk.RaisedLevelPolygon
public import Mathlib.Analysis.Convex.PathConnected

/-!
# The grafted level contour

Construction of the closed contour used for the steepest-descent analysis: finite polygonal
meshes above the real axis, the central level graph `x ↦ x + i y(x)` through the saddle,
vertical grafts joining them, and the reflected lower half. The loop avoids every real pole
enclosed by its endpoints and passes through the conjugate saddle pair.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set
open scoped unitInterval

/-- The polygonal path through the vertices `v 0, …, v M`. -/
def finiteLevelMeshPath (v : ℕ → ℂ) : (M : ℕ) → Path (v 0) (v M)
  | 0 => Path.refl (v 0)
  | M+1 => (finiteLevelMeshPath v M).trans (Path.segment (v M) (v (M+1)))

private theorem segment_im_pos {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (z : ℂ) (hz : z ∈ range (Path.segment a b)) : 0 < z.im := by
  obtain ⟨s, rfl⟩ := hz
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
    Complex.add_im, Complex.smul_im, smul_eq_mul]
  have hs0 := s.property.1
  have hs1 := s.property.2
  by_cases hs : (s : ℝ) = 0
  · simpa only [hs,sub_zero,one_mul,zero_mul,add_zero] using ha
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr hs1) ha.le)
      (mul_pos (lt_of_le_of_ne hs0 (Ne.symm hs)) hb)

private theorem trans_range_property {a b c : ℂ} (p : Path a b) (q : Path b c)
    (P : ℂ → Prop) (hp : ∀ z ∈ range p, P z) (hq : ∀ z ∈ range q, P z) :
    ∀ z ∈ range (p.trans q), P z := by
  intro z hz
  rw [Path.trans_range] at hz
  exact hz.elim (hp z) (hq z)

/-- If all vertices lie in the open upper half-plane, so does the whole polygonal path. -/
theorem finiteLevelMeshPath_im_pos (v : ℕ → ℂ) (M : ℕ)
    (hv : ∀ j ≤ M, 0 < (v j).im) :
    ∀ z ∈ range (finiteLevelMeshPath v M), 0 < z.im := by
  induction M with
  | zero =>
    intro z hz
    have hz' : z = v 0 := by simpa [finiteLevelMeshPath] using hz
    exact hz' ▸ hv 0 (by omega)
  | succ M ih =>
    exact trans_range_property _ _ _ (ih (fun j hj => hv j (by omega)))
      (segment_im_pos (hv M (by omega)) (hv (M+1) le_rfl))

/-- The raised mesh has strictly positive height for every `h > 0`. -/
theorem raisedLevelMeshVertex_im_pos {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t L h : ℝ) (ht : 0 < t) (hh : 0 < h) (j : ℕ) :
    0 < (raisedLevelMeshVertex d t L h j).im := by
  have hy := (levelHeight_bounds hN d t (L+(j : ℝ)*h) ht).1
  have he : 0 < Real.sqrt (2*Real.sqrt t*h) := by positivity
  simp only [raisedLevelMeshVertex, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, zero_add]
  linarith

/-- The point `x + i y(x)` of the level graph. -/
def actualLevelGraphPoint {N : ℕ} (d : Fin N → ℝ) (t x : ℝ) : ℂ :=
  (x : ℂ)+(levelHeight d t x : ℂ)*Complex.I

/-- The central level graph arc as a continuous path. -/
def actualLevelGraphPath {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) :
    Path (actualLevelGraphPoint d t a) (actualLevelGraphPoint d t b) :=
  (Path.segment a b).map (show Continuous (actualLevelGraphPoint d t) by
    unfold actualLevelGraphPoint
    exact Complex.continuous_ofReal.add
      ((Complex.continuous_ofReal.comp (levelHeight_continuous hN d t ht)).mul
        continuous_const))

/-- Every point of the graph arc lies at its level height. -/
theorem actualLevelGraphPath_mem {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hab : a ≤ b) (z : ℂ)
    (hz : z ∈ range (actualLevelGraphPath hN d t a b ht)) :
    z.re ∈ Icc a b ∧ z = actualLevelGraphPoint d t z.re := by
  obtain ⟨s, rfl⟩ := hz
  change (actualLevelGraphPoint d t ((Path.segment a b) s)).re ∈ Icc a b ∧
    actualLevelGraphPoint d t ((Path.segment a b) s) =
      actualLevelGraphPoint d t (actualLevelGraphPoint d t ((Path.segment a b) s)).re
  have hx : (Path.segment a b) s ∈ Icc a b := by
    simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_eq_mul]
    constructor <;> nlinarith [s.property.1, s.property.2]
  simpa [actualLevelGraphPoint] using hx

/-- The upper path: central level arc between two meshes, joined to the mesh endpoints by
vertical grafts. -/
def graftedLevelUpperPath {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (vL vR : ℕ → ℂ) (ML MR : ℕ) :
    Path (vL 0) (vR MR) :=
  (finiteLevelMeshPath vL ML).trans
    ((Path.segment (vL ML) (actualLevelGraphPoint d t a)).trans
      ((actualLevelGraphPath hN d t a b ht).trans
        ((Path.segment (actualLevelGraphPoint d t b) (vR 0)).trans
          (finiteLevelMeshPath vR MR))))

/-- Positive height on the central graph and on the meshes gives positive height on the whole
upper path. -/
theorem graftedLevelUpperPath_im_pos {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (vL vR : ℕ → ℂ) (ML MR : ℕ)
    (hL : ∀ j ≤ ML, 0 < (vL j).im) (hR : ∀ j ≤ MR, 0 < (vR j).im)
    (hgraph : ∀ x ∈ Icc a b, 0 < levelHeight d t x) :
    ∀ z ∈ range (graftedLevelUpperPath hN d t a b ht vL vR ML MR), 0 < z.im := by
  have ha : 0 < (actualLevelGraphPoint d t a).im := by
    simpa [actualLevelGraphPoint] using hgraph a ⟨le_rfl,hab⟩
  have hb : 0 < (actualLevelGraphPoint d t b).im := by
    simpa [actualLevelGraphPoint] using hgraph b ⟨hab,le_rfl⟩
  have hg : ∀ z ∈ range (actualLevelGraphPath hN d t a b ht), 0 < z.im := by
    intro z hz
    have hz' := actualLevelGraphPath_mem hN d t a b ht hab z hz
    rw [hz'.2]
    simpa [actualLevelGraphPoint] using hgraph z.re hz'.1
  exact trans_range_property _ _ _ (finiteLevelMeshPath_im_pos vL ML hL)
    (trans_range_property _ _ _ (segment_im_pos (hL ML le_rfl) ha)
      (trans_range_property _ _ _ hg
        (trans_range_property _ _ _ (segment_im_pos hb (hR 0 (by omega)))
          (finiteLevelMeshPath_im_pos vR MR hR))))

/-- Closed oriented loop: upper arc right-to-left, left connector downward,
reflected lower arc left-to-right, right connector upward. -/
def reflectedLevelLoop {a b : ℂ} (upper : Path a b) : Path b b :=
  upper.symm.trans
    ((Path.segment a (star a)).trans
      ((upper.map Complex.continuous_conj).trans (Path.segment (star b) b)))

private theorem segment_re_eq {a b : ℂ} (hab : a.re = b.re) (z : ℂ)
    (hz : z ∈ range (Path.segment a b)) : z.re = a.re := by
  obtain ⟨s,rfl⟩ := hz
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module,
    Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [← hab]
  ring

/-- The reflected loop avoids each real pole lying strictly between its endpoints, provided the
upper arc has positive height. -/
theorem reflectedLevelLoop_ne_real {a b : ℂ} (upper : Path a b) (p : ℝ)
    (hpL : a.re < p) (hpR : p < b.re)
    (hu : ∀ z ∈ range upper, 0 < z.im) :
    ∀ z ∈ range (reflectedLevelLoop upper), z ≠ (p : ℂ) := by
  have ht : ∀ z ∈ range upper.symm, z ≠ (p : ℂ) := by
    intro z hz he
    rw [Path.symm_range] at hz
    have hh := hu z hz
    rw [he,Complex.ofReal_im] at hh
    linarith
  have hl : ∀ z ∈ range (Path.segment a (star a)), z ≠ (p : ℂ) := by
    intro z hz he
    have hh := segment_re_eq (by simp) z hz
    rw [he,Complex.ofReal_re] at hh
    linarith
  have hb : ∀ z ∈ range (upper.map Complex.continuous_conj), z ≠ (p : ℂ) := by
    intro z hz he
    obtain ⟨s,rfl⟩ := hz
    have hh := hu (upper s) (mem_range_self s)
    change star (upper s) = (p : ℂ) at he
    have hi := congrArg Complex.im he
    simp only [Complex.star_def,Complex.conj_im,Complex.ofReal_im] at hi
    linarith
  have hr : ∀ z ∈ range (Path.segment (star b) b), z ≠ (p : ℂ) := by
    intro z hz he
    have hh := segment_re_eq (by simp) z hz
    rw [he,Complex.ofReal_re] at hh
    simp only [Complex.star_def,Complex.conj_re] at hh
    linarith
  exact trans_range_property _ _ _ ht
    (trans_range_property _ _ _ hl (trans_range_property _ _ _ hb hr))

/-- Every central graph point lies on the graph arc, including its endpoints. -/
theorem actualLevelGraphPath_contains {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b x : ℝ) (ht : 0 < t) (hab : a ≤ b) (hx : x ∈ Icc a b) :
    actualLevelGraphPoint d t x ∈ range (actualLevelGraphPath hN d t a b ht) := by
  have hx' : x ∈ range (Path.segment a b) := by
    simpa only [Path.range_segment, segment_eq_Icc hab] using hx
  obtain ⟨s,hs⟩ := hx'
  refine ⟨s,?_⟩
  change actualLevelGraphPoint d t ((Path.segment a b) s) = _
  rw [hs]

/-- Every central graph point lies on the upper path. -/
theorem graftedLevelUpperPath_contains {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b x : ℝ) (ht : 0 < t) (hab : a ≤ b) (hx : x ∈ Icc a b)
    (vL vR : ℕ → ℂ) (ML MR : ℕ) :
    actualLevelGraphPoint d t x ∈
      range (graftedLevelUpperPath hN d t a b ht vL vR ML MR) := by
  have hx' := actualLevelGraphPath_contains hN d t a b x ht hab hx
  unfold graftedLevelUpperPath
  simp only [Path.trans_range, mem_union]
  exact Or.inr (Or.inr (Or.inl hx'))

/-- The upper saddle point and its conjugate both lie on the closed loop. -/
theorem reflectedLevelLoop_contains_pair {a b : ℂ} (upper : Path a b)
    (z : ℂ) (hz : z ∈ range upper) :
    z ∈ range (reflectedLevelLoop upper) ∧ star z ∈ range (reflectedLevelLoop upper) := by
  constructor
  · unfold reflectedLevelLoop
    rw [Path.trans_range,Path.symm_range]
    exact Or.inl hz
  · obtain ⟨s,rfl⟩ := hz
    unfold reflectedLevelLoop
    simp only [Path.trans_range,mem_union]
    refine Or.inr (Or.inr (Or.inl ?_))
    exact ⟨s,rfl⟩

/-- Number of mesh steps for an interval and a mesh cap `h`. -/
def graftedLevelMeshCount (a b h : ℝ) : ℕ := Nat.ceil ((b-a)/h)

/-- The mesh spacing, which reaches the interval endpoint exactly. -/
def graftedLevelMeshSpacing (a b h : ℝ) : ℝ :=
  (b-a)/(graftedLevelMeshCount a b h : ℝ)

/-- A nonempty interval and a positive mesh cap give a positive step count. -/
theorem graftedLevelMeshCount_pos (a b h : ℝ) (hab : a < b) (hh : 0 < h) :
    0 < graftedLevelMeshCount a b h := by
  exact Nat.ceil_pos.mpr (div_pos (sub_pos.mpr hab) hh)

/-- The mesh spacing is positive and at most the cap. -/
theorem graftedLevelMeshSpacing_bounds (a b h : ℝ) (hab : a < b) (hh : 0 < h) :
    0 < graftedLevelMeshSpacing a b h ∧ graftedLevelMeshSpacing a b h ≤ h := by
  have hM : 0 < (graftedLevelMeshCount a b h : ℝ) := by
    exact_mod_cast graftedLevelMeshCount_pos a b h hab hh
  have hc : (b-a)/h ≤ (graftedLevelMeshCount a b h : ℝ) := Nat.le_ceil _
  constructor
  · exact div_pos (sub_pos.mpr hab) hM
  · apply (div_le_iff₀ hM).mpr
    have hc' := (div_le_iff₀ hh).mp hc
    simpa only [mul_comm] using hc'

/-- The mesh starts at `a` and ends exactly at `b` in real part. -/
theorem graftedLevelMesh_endpoint_re {N : ℕ} (d : Fin N → ℝ)
    (t a b h : ℝ) (hab : a < b) (hh : 0 < h) :
    (raisedLevelMeshVertex d t a (graftedLevelMeshSpacing a b h) 0).re = a ∧
      (raisedLevelMeshVertex d t a (graftedLevelMeshSpacing a b h)
        (graftedLevelMeshCount a b h)).re = b := by
  have hM : (graftedLevelMeshCount a b h : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast graftedLevelMeshCount_pos a b h hab hh)
  simp only [raisedLevelMeshVertex,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,
    sub_zero,add_zero,Nat.cast_zero,zero_mul,graftedLevelMeshSpacing]
  constructor
  · trivial
  · field_simp
    ring

/-- The grafted level loop built from the source and four real endpoints; the outer meshes use
ceiling counts and exact endpoint spacing. -/
def actualGraftedLevelLoop {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t L a b R h : ℝ) (ht : 0 < t) :
    Path
      (raisedLevelMeshVertex d t b (graftedLevelMeshSpacing b R h)
        (graftedLevelMeshCount b R h))
      (raisedLevelMeshVertex d t b (graftedLevelMeshSpacing b R h)
        (graftedLevelMeshCount b R h)) :=
  reflectedLevelLoop (graftedLevelUpperPath hN d t a b ht
    (raisedLevelMeshVertex d t L (graftedLevelMeshSpacing L a h))
    (raisedLevelMeshVertex d t b (graftedLevelMeshSpacing b R h))
    (graftedLevelMeshCount L a h) (graftedLevelMeshCount b R h))

/-- The closed grafted loop avoids every real pole when its endpoints enclose the spectrum and
the central interval lies within `eta²/(4√tmax)` of a point `x₀` of level height at least `eta`. -/
theorem actualGraftedLevelLoop_ne_pole {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ L a b R h : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (heta : 0 < eta) (hheight : eta ≤ levelHeight d t x₀)
    (hLa : L < a) (hab : a ≤ b) (hbR : b < R) (hh : 0 < h)
    (hclose : ∀ x ∈ Icc a b, |x-x₀| ≤ eta^2/(4*Real.sqrt tmax))
    (hd : ∀ j, L < d j ∧ d j < R) (j : Fin N) :
    ∀ z ∈ range (actualGraftedLevelLoop hN d t L a b R h ht), z ≠ (d j : ℂ) := by
  have hl := (graftedLevelMeshSpacing_bounds L a h hLa hh).1
  have hr := (graftedLevelMeshSpacing_bounds b R h hbR hh).1
  have hleft := (graftedLevelMesh_endpoint_re d t L a h hLa hh).1
  have hright := (graftedLevelMesh_endpoint_re d t b R h hbR hh).2
  apply reflectedLevelLoop_ne_real
  · simpa only [hleft] using (hd j).1
  · simpa only [hright] using (hd j).2
  · apply graftedLevelUpperPath_im_pos hN d t a b ht hab
    · intro k _
      exact raisedLevelMeshVertex_im_pos hN d t L _ ht hl k
    · intro k _
      exact raisedLevelMeshVertex_im_pos hN d t b _ ht hr k
    · intro x hx
      have hy := levelHeight_neighborhood_lower hN d t tmax eta x₀ x
        ht htmax heta hheight (hclose x hx)
      linarith

/-- The closed grafted loop contains the conjugate saddle pair whenever `x₀` lies between the
central endpoints. -/
theorem actualGraftedLevelLoop_contains_saddles {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t L a b R h x₀ : ℝ) (ht : 0 < t)
    (hab : a ≤ b) (hx : x₀ ∈ Icc a b) :
    actualLevelGraphPoint d t x₀ ∈ range (actualGraftedLevelLoop hN d t L a b R h ht) ∧
      star (actualLevelGraphPoint d t x₀) ∈ range (actualGraftedLevelLoop hN d t L a b R h ht) := by
  exact reflectedLevelLoop_contains_pair _ _
    (graftedLevelUpperPath_contains hN d t a b x₀ ht hab hx _ _ _ _)

end BlockBand.GaussianBulk
