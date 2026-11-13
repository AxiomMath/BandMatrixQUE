module
public import BlockBand.GaussianBulk.LevelVerticalAction
public import BlockBand.GaussianBulk.LevelNeighborhood

/-!
# Raised polygons above the level graph

The outer parts of the grafted loop are polygons whose vertices are graph points lifted by
`√(2√t h)`. The lifted chords stay above the graph and keep the pole clearance `t/N`; their
edges have explicit length; and the real phase loses at most `3/N` on them when the mesh is
`h = √t/(2N²)`, uniformly in the source `d`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open scoped BigOperators

/-- Every graph denominator `(x - d_j)² + y(x)²` is at least `t/N`. -/
theorem levelGraph_denominator_ge_variance {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (j : Fin N) :
    t/(N : ℝ) ≤ (x-d j)^2+(levelHeight d t x)^2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hq := levelGraph_denominator_pos hN d t x ht j
  have hs : ((x-d j)^2+(levelHeight d t x)^2)⁻¹ ≤
      ∑ i, ((x-d i)^2+(levelHeight d t x)^2)⁻¹ :=
    Finset.single_le_sum (fun i _ => inv_nonneg.mpr (levelGraph_denominator_pos hN d t x ht i).le)
      (Finset.mem_univ j)
  have havg := levelGraph_level_le hN d t x ht
  have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hNr.le)
  have hi := le_trans hm havg
  have hprod : 1/((N : ℝ)*((x-d j)^2+(levelHeight d t x)^2)) ≤ 1/t := by
    simpa only [one_div,mul_inv_rev,mul_comm] using hi
  have hh := (one_div_le_one_div (mul_pos hNr hq) ht).mp hprod
  exact (div_le_iff₀ hNr).mpr (by nlinarith)

private theorem square_sub_le_square_diff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a-b)^2 ≤ |a^2-b^2| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (by nlinarith : a^2-b^2 ≤ 0)]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hab)]
  · rw [abs_of_nonneg (by nlinarith : 0 ≤ a^2-b^2)]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hba)]

/-- Half-Hölder modulus of the level height: `|y(b) - y(a)| ≤ √(2√t h)` for `|b - a| ≤ h`. -/
theorem levelHeight_mesh_modulus {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b h : ℝ) (ht : 0 < t) (hh : 0 ≤ h) (hab : |b-a| ≤ h) :
    |levelHeight d t b-levelHeight d t a| ≤ Real.sqrt (2*Real.sqrt t*h) := by
  have hA := (levelHeight_bounds hN d t a ht).1
  have hB := (levelHeight_bounds hN d t b ht).1
  have hd := square_sub_le_square_diff (levelHeight d t b) (levelHeight d t a) hB hA
  have hl := levelHeight_sq_abs_sub_le hN d t a b ht
  have hscale := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2*Real.sqrt t by positivity)
  have hs : (levelHeight d t b-levelHeight d t a)^2 ≤ 2*Real.sqrt t*h :=
    le_trans hd (le_trans hl hscale)
  have he := Real.sq_sqrt (show 0 ≤ 2*Real.sqrt t*h by positivity)
  nlinarith [sq_abs (levelHeight d t b-levelHeight d t a),
    abs_nonneg (levelHeight d t b-levelHeight d t a),Real.sqrt_nonneg (2*Real.sqrt t*h)]

/-- The chord between the graph points over `a` and `b`, lifted by `√(2√t h)`. -/
def raisedLevelChord {N : ℕ} (d : Fin N → ℝ)
    (t a b h θ : ℝ) : ℝ :=
  (1-θ)*levelHeight d t a+θ*levelHeight d t b+Real.sqrt (2*Real.sqrt t*h)

/-- The raised chord lies above the graph, within `2√(2√t h)` of it, and has height at most
`√t + √(2√t h)`. -/
theorem raisedLevelChord_bounds {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b h θ : ℝ) (ht : 0 < t) (hab : a ≤ b) (hh : b-a ≤ h)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let x := (1-θ)*a+θ*b
    0 ≤ raisedLevelChord d t a b h θ-levelHeight d t x ∧
      raisedLevelChord d t a b h θ-levelHeight d t x ≤ 2*Real.sqrt (2*Real.sqrt t*h) ∧
      raisedLevelChord d t a b h θ ≤ Real.sqrt t+Real.sqrt (2*Real.sqrt t*h) := by
  let x := (1-θ)*a+θ*b
  have hh0 : 0 ≤ h := le_trans (sub_nonneg.mpr hab) hh
  have hxa : |x-a| ≤ h := by
    have he : x-a=θ*(b-a) := by dsimp only [x];ring
    rw [he,abs_of_nonneg (mul_nonneg hθ (sub_nonneg.mpr hab))]
    nlinarith
  have hxb : |x-b| ≤ h := by
    have he : x-b= -(1-θ)*(b-a) := by dsimp only [x];ring
    rw [he,abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sub_nonneg.mpr hab))]
    nlinarith
  have hA := levelHeight_mesh_modulus hN d t a x h ht hh0 hxa
  have hB := levelHeight_mesh_modulus hN d t b x h ht hh0 hxb
  have ha := abs_le.mp hA
  have hb := abs_le.mp hB
  have haa := (levelHeight_bounds hN d t a ht).2
  have hbb := (levelHeight_bounds hN d t b ht).2
  have hl₁ := mul_le_mul_of_nonneg_left ha.1 (sub_nonneg.mpr hθ1)
  have hl₂ := mul_le_mul_of_nonneg_left hb.1 hθ
  have hu₁ := mul_le_mul_of_nonneg_left ha.2 (sub_nonneg.mpr hθ1)
  have hu₂ := mul_le_mul_of_nonneg_left hb.2 hθ
  have ht₁ := mul_le_mul_of_nonneg_left haa (sub_nonneg.mpr hθ1)
  have ht₂ := mul_le_mul_of_nonneg_left hbb hθ
  dsimp only [raisedLevelChord]
  change 0 ≤ (1-θ)*levelHeight d t a+θ*levelHeight d t b+
      Real.sqrt (2*Real.sqrt t*h)-levelHeight d t x ∧ _
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- The raised chord keeps the pole clearance `t/N`. -/
theorem raisedLevelChord_denominator_ge_variance {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t a b h θ : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (hh : b-a ≤ h) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : Fin N) :
    t/(N : ℝ) ≤ (((1-θ)*a+θ*b)-d j)^2+(raisedLevelChord d t a b h θ)^2 := by
  let x := (1-θ)*a+θ*b
  have hp := (raisedLevelChord_bounds hN d t a b h θ ht hab hh hθ hθ1).1
  have hy := (levelHeight_bounds hN d t x ht).1
  have hd := levelGraph_denominator_ge_variance hN d t x ht j
  nlinarith

/-- Raising the vertical point above the graph loses at most the quadratic term:
`0 ≤ Λ(x) - S(x, P) ≤ (P² - y(x)²)/(2t)` for `P ≥ y(x)`. -/
theorem verticalRealAction_raised_graph_loss {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x P : ℝ) (ht : 0 < t)
    (hP : levelHeight d t x ≤ P) :
    0 ≤ levelAction d E t x-verticalRealAction d E t x P ∧
      levelAction d E t x-verticalRealAction d E t x P ≤
        (P^2-(levelHeight d t x)^2)/(2*t) := by
  have hy := (levelHeight_bounds hN d t x ht).1
  have hs : (levelHeight d t x)^2 ≤ P^2 := by nlinarith
  have hd : VerticalActionDomain d x P := by
    intro j
    have hp := levelGraph_denominator_pos hN d t x ht j
    nlinarith
  have hmax := verticalRealAction_max hN d E t x P ht hd
  have hm : realMean (fun j => Real.log ((x-d j)^2+(levelHeight d t x)^2)) ≤
      realMean (fun j => Real.log ((x-d j)^2+P^2)) := by
    apply mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => (Real.log_le_log_iff
        (levelGraph_denominator_pos hN d t x ht j) (hd j)).mpr (by linarith)))
      (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  constructor
  · exact sub_nonneg.mpr hmax
  · unfold levelAction verticalRealAction levelEnvelopeAction
    have he : ((x-E)^2-(levelHeight d t x)^2)/(2*t)-((x-E)^2-P^2)/(2*t)=
        (P^2-(levelHeight d t x)^2)/(2*t) := by ring
    linarith

/-- The phase loss on a raised chord is between `0` and `√(2√t h)(2√t + √(2√t h))/t`. -/
theorem raisedLevelChord_phase_loss {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t a b h θ : ℝ) (ht : 0 < t) (hab : a ≤ b) (hh : b-a ≤ h)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let x := (1-θ)*a+θ*b
    0 ≤ levelAction d E t x-verticalRealAction d E t x (raisedLevelChord d t a b h θ) ∧
      levelAction d E t x-verticalRealAction d E t x (raisedLevelChord d t a b h θ) ≤
        Real.sqrt (2*Real.sqrt t*h)*(2*Real.sqrt t+Real.sqrt (2*Real.sqrt t*h))/t := by
  let x := (1-θ)*a+θ*b
  let P := raisedLevelChord d t a b h θ
  let ε := Real.sqrt (2*Real.sqrt t*h)
  have hb := raisedLevelChord_bounds hN d t a b h θ ht hab hh hθ hθ1
  have hy := levelHeight_bounds hN d t x ht
  have hP : levelHeight d t x ≤ P := by linarith [hb.1]
  have hl := verticalRealAction_raised_graph_loss hN d E t x P ht hP
  constructor
  · exact hl.1
  · have hs : P^2-(levelHeight d t x)^2 ≤ 2*ε*(2*Real.sqrt t+ε) := by
      have hp0 : 0 ≤ P := le_trans hy.1 hP
      have hdiff : 0 ≤ P-levelHeight d t x := sub_nonneg.mpr hP
      have hsum : P+levelHeight d t x ≤ 2*Real.sqrt t+ε := by linarith [hb.2.2]
      have hmul := mul_le_mul hb.2.1 hsum (add_nonneg hp0 hy.1)
        (show 0 ≤ 2*ε by dsimp only [ε];positivity)
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hs (show 0 ≤ 2*t by positivity)
    have he : (2*ε*(2*Real.sqrt t+ε))/(2*t)=ε*(2*Real.sqrt t+ε)/t := by ring
    rw [he] at hdiv
    exact le_trans hl.2 hdiv

/-- The vertex `L + jh + i(y(L + jh) + √(2√t h))` of the raised mesh. -/
def raisedLevelMeshVertex {N : ℕ} (d : Fin N → ℝ) (t L h : ℝ) (j : ℕ) : ℂ :=
  ((L+(j : ℝ)*h : ℝ) : ℂ)+
    ((levelHeight d t (L+(j : ℝ)*h)+Real.sqrt (2*Real.sqrt t*h) : ℝ) : ℂ)*Complex.I

/-- Each polygon edge has length at most `h + √(2√t h)`. -/
theorem raisedLevelMesh_edge_length {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t L h : ℝ) (ht : 0 < t) (hh : 0 ≤ h) (j : ℕ) :
    ‖raisedLevelMeshVertex d t L h (j+1)-raisedLevelMeshVertex d t L h j‖ ≤
      h+Real.sqrt (2*Real.sqrt t*h) := by
  have hdist : |(L+((j+1 : ℕ) : ℝ)*h)-(L+(j : ℝ)*h)| ≤ h := by
    have he : (L+((j+1 : ℕ) : ℝ)*h)-(L+(j : ℝ)*h)=h := by push_cast;ring
    rw [he,abs_of_nonneg hh]
  have hm := levelHeight_mesh_modulus hN d t (L+(j : ℝ)*h)
    (L+((j+1 : ℕ) : ℝ)*h) h ht hh hdist
  have hb := Complex.norm_le_abs_re_add_abs_im
    (raisedLevelMeshVertex d t L h (j+1)-raisedLevelMeshVertex d t L h j)
  simp only [raisedLevelMeshVertex,Complex.sub_re,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,sub_zero,
    add_zero,Complex.sub_im,Complex.add_im,Complex.mul_im,mul_one,zero_add] at hb
  have he : (levelHeight d t (L+((j+1 : ℕ) : ℝ)*h)+Real.sqrt (2*Real.sqrt t*h))-
      (levelHeight d t (L+(j : ℝ)*h)+Real.sqrt (2*Real.sqrt t*h)) =
        levelHeight d t (L+((j+1 : ℕ) : ℝ)*h)-levelHeight d t (L+(j : ℝ)*h) := by ring
  rw [he] at hb
  have hb' : ‖raisedLevelMeshVertex d t L h (j+1)-raisedLevelMeshVertex d t L h j‖ ≤
      |(L+((j+1 : ℕ) : ℝ)*h)-(L+(j : ℝ)*h)|+
        |levelHeight d t (L+((j+1 : ℕ) : ℝ)*h)-levelHeight d t (L+(j : ℝ)*h)| := by
    simpa only [raisedLevelMeshVertex] using hb
  exact le_trans hb' (add_le_add hdist hm)

/-- The polygon with `M` edges has total length at most `M(h + √(2√t h))`. -/
theorem raisedLevelMesh_total_length {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t L h : ℝ) (ht : 0 < t) (hh : 0 ≤ h) (M : ℕ) :
    (∑ j : Fin M, ‖raisedLevelMeshVertex d t L h (j.val+1)-raisedLevelMeshVertex d t L h j.val‖) ≤
      (M : ℝ)*(h+Real.sqrt (2*Real.sqrt t*h)) := by
  have hb := Finset.sum_le_sum (s := Finset.univ)
    (fun (j : Fin M) _ => raisedLevelMesh_edge_length hN d t L h ht hh j.val)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hb

/-- With `h = √t/(2N²)` (lift `√t/N`), the phase loss on every raised chord is at most `3/N`. -/
theorem raisedLevelChord_phase_loss_explicit {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t a b θ : ℝ) (ht : 0 < t) (hab : a ≤ b)
    (hh : b-a ≤ Real.sqrt t/(2*(N : ℝ)^2)) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let x := (1-θ)*a+θ*b
    levelAction d E t x-
      verticalRealAction d E t x (raisedLevelChord d t a b (Real.sqrt t/(2*(N : ℝ)^2)) θ) ≤
        3/(N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hb := (raisedLevelChord_phase_loss hN d E t a b
    (Real.sqrt t/(2*(N : ℝ)^2)) θ ht hab hh hθ hθ1).2
  have he : Real.sqrt (2*Real.sqrt t*(Real.sqrt t/(2*(N : ℝ)^2))) = Real.sqrt t/(N : ℝ) := by
    have hs : (Real.sqrt t/(N : ℝ))^2 = 2*Real.sqrt t*(Real.sqrt t/(2*(N : ℝ)^2)) := by
      field_simp [ne_of_gt hNr]
    have hsq := Real.sq_sqrt
      (show 0 ≤ 2*Real.sqrt t*(Real.sqrt t/(2*(N : ℝ)^2)) by positivity)
    have hp : 0 ≤ Real.sqrt t/(N : ℝ) := by positivity
    nlinarith [Real.sqrt_nonneg (2*Real.sqrt t*(Real.sqrt t/(2*(N : ℝ)^2)))]
  rw [he] at hb
  have herror : (Real.sqrt t/(N : ℝ))*(2*Real.sqrt t+Real.sqrt t/(N : ℝ))/t =
      2/(N : ℝ)+1/(N : ℝ)^2 := by
    field_simp [ne_of_gt hNr,ne_of_gt ht]
    nlinarith [Real.sq_sqrt ht.le]
  rw [herror] at hb
  have hn2 : (N : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  have hi := one_div_le_one_div_of_le hNr hn2
  have he3 : 3/(N : ℝ)=2/(N : ℝ)+1/(N : ℝ) := by ring
  rw [he3]
  linarith

end BlockBand.GaussianBulk
