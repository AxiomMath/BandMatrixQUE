module
public import BlockBand.GaussianBulk.LevelEnvelope
public import BlockBand.GaussianBulk.LevelDifferentiation

/-!
# The real action along a vertical line

The real part of the Johansson saddle phase along a vertical line `x + iv` is even in `v`,
increases on `(0, y)` and decreases on `(y, ∞)` for a positive level root `y`, and has its only
global maxima at `v = ±y`, with curvature at most `-2η²/tmax²` there. For `v² ≥ y²` it has an
explicit Gaussian tail `-v²/(4 tmax)` plus a constant depending only on `η` and `tmax`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Filter Topology
open scoped BigOperators

/-- The vertical line avoids the real poles (where the totalized `Real.log` is not the phase). -/
def VerticalActionDomain {N : ℕ} (d : Fin N → ℝ) (x v : ℝ) : Prop :=
  ∀ j, 0 < (x-d j)^2+v^2

/-- The real Johansson phase along the vertical line through `x`. -/
def verticalRealAction {N : ℕ} (d : Fin N → ℝ) (E t x v : ℝ) : ℝ :=
  levelEnvelopeAction d E t x (v^2)

private theorem vertical_domain_positive {N : ℕ} (d : Fin N → ℝ)
    (x v : ℝ) (hv : 0 < v) : VerticalActionDomain d x v :=
  fun j => level_denominator_pos (x-d j) v hv

/-- The vertical real action is the real part of the Johansson saddle phase. -/
theorem verticalRealAction_eq_saddlePhase_re {N : ℕ} (d : Fin N → ℝ)
    (E t x v : ℝ) : verticalRealAction d E t x v =
      (saddlePhase d E t ((x : ℂ)+(v : ℂ)*Complex.I)).re := by
  have hquad :
      (((((x : ℂ)+(v : ℂ)*Complex.I)-(E : ℂ))^2)/(2*(t : ℂ))).re =
        ((x-E)^2-v^2)/(2*t) := by
    rw [show 2*(t : ℂ)=((2*t : ℝ):ℂ) by norm_cast,Complex.div_ofReal_re]
    simp only [pow_two,Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.sub_im,Complex.mul_im,mul_one,zero_add]
  have hmean : (complexMean (fun j => Complex.log
      ((x : ℂ)+(v : ℂ)*Complex.I-(d j : ℂ)))).re =
        realMean (fun j => Real.log ((x-d j)^2+v^2))/2 := by
    unfold complexMean realMean
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [show (∑ j,Complex.log ((x : ℂ)+(v : ℂ)*Complex.I-(d j : ℂ))).re =
      ∑ j,(Complex.log ((x : ℂ)+(v : ℂ)*Complex.I-(d j : ℂ))).re from
      map_sum Complex.reAddGroupHom _ _]
    simp_rw [log_graph_real_part]
    simp only [div_eq_mul_inv,← Finset.sum_mul]
    ring
  unfold verticalRealAction levelEnvelopeAction saddlePhase
  rw [Complex.add_re,hquad,hmean]

/-- The vertical real action is even in `v`. -/
theorem verticalRealAction_even {N : ℕ} (d : Fin N → ℝ)
    (E t x v : ℝ) : verticalRealAction d E t x (-v) = verticalRealAction d E t x v := by
  simp [verticalRealAction]

/-- The vertical real action is maximized at the graph height. -/
theorem verticalRealAction_max {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x v : ℝ) (ht : 0 < t) (hv : VerticalActionDomain d x v) :
    verticalRealAction d E t x v ≤ verticalRealAction d E t x (levelHeight d t x) :=
  levelHeight_sq_envelope_max hN d E t x ht (v^2) ⟨sq_nonneg _,hv⟩

/-- The only admissible global maxima are `v = ±y(x)` (which coincide when `y(x) = 0`). -/
theorem verticalRealAction_eq_max_iff {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x v : ℝ) (ht : 0 < t) (hv : VerticalActionDomain d x v) :
    verticalRealAction d E t x v = verticalRealAction d E t x (levelHeight d t x) ↔
      v=levelHeight d t x ∨ v= -levelHeight d t x := by
  constructor
  · intro he
    have hs : v^2=(levelHeight d t x)^2 := by
      by_contra hn
      exact (ne_of_lt (levelHeight_sq_unique_envelope_max hN d E t x ht (v^2)
        ⟨sq_nonneg _,hv⟩ hn)) he
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hs
  · intro he
    rcases he with he | he
    · rw [he]
    · rw [he,verticalRealAction_even]

/-- At a solution of the finite MDE with `Im m > 0`, the imaginary part of the saddle point is a
positive level root over its real part. -/
theorem positiveLevelRoot_at_saddle {N : ℕ} (d : Fin N → ℝ)
    (E t : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m) :
    PositiveLevelRoot d t (saddlePoint E t m).re (saddlePoint E t m).im := by
  constructor
  · rw [saddlePoint_im]
    exact mul_pos ht hm
  · rw [verticalLevel_eq_levelAverage]
    exact levelAverage_saddle_eq d E t m ht hm hMDE

/-- On the vertical line through the MDE saddle, the global maxima are the saddle point and its
conjugate. -/
theorem verticalRealAction_saddle_max_iff {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t v : ℝ) (m : ℂ) (ht : 0 < t) (hm : 0 < m.im)
    (hMDE : FiniteMDE d E t m)
    (hv : VerticalActionDomain d (saddlePoint E t m).re v) :
    verticalRealAction d E t (saddlePoint E t m).re v =
      verticalRealAction d E t (saddlePoint E t m).re (saddlePoint E t m).im ↔
      v=(saddlePoint E t m).im ∨ v= -(saddlePoint E t m).im := by
  simpa only [levelHeight_at_saddle hN d E t m ht hm hMDE] using
    verticalRealAction_eq_max_iff hN d E t (saddlePoint E t m).re v ht hv

/-- The vertical derivative `v (level(v) - 1/t)` on the pole-safe line. -/
theorem hasDerivAt_verticalRealAction {N : ℕ} (d : Fin N → ℝ)
    (E t x v : ℝ) (ht : 0 < t) (hv : VerticalActionDomain d x v) :
    HasDerivAt (verticalRealAction d E t x)
      (v*(verticalLevel d x v-1/t)) v := by
  have hs : HasDerivAt (fun u : ℝ => u^2) (2*v) v := by
    convert! (hasDerivAt_id v).pow 2 using 1
    simp
  have h := (hasDerivAt_levelEnvelope_vertical d E t x (v^2) ht
    ⟨sq_nonneg _,hv⟩).comp v (h := fun u : ℝ => u^2) hs
  apply h.congr_deriv
  change ((verticalLevel d x v-1/t)/2)*(2*v) = _
  ring

/-- The vertical real action is strictly increasing on `(0, y)`. -/
theorem verticalRealAction_strictMonoOn {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x y : ℝ) (ht : 0 < t) (hr : PositiveLevelRoot d t x y) :
    StrictMonoOn (verticalRealAction d E t x) (Set.Ioo 0 y) := by
  intro a ha b hb hab
  have hsq : a^2 < b^2 := by nlinarith [ha.1]
  have hyb : b^2 < y^2 := by nlinarith [hb.1,hb.2,hr.1]
  have hdb : LevelEnvelopeDomain d x (b^2) :=
    ⟨sq_nonneg _,vertical_domain_positive d x b hb.1⟩
  have hdy : LevelEnvelopeDomain d x (y^2) :=
    ⟨sq_nonneg _,vertical_domain_positive d x y hr.1⟩
  have hs := levelEnvelopeSlope_strictAnti hN d t x (b^2) (y^2) hdb hdy hyb
  have hz : levelEnvelopeSlope d t x (y^2)=0 := by
    change (verticalLevel d x y-1/t)/2=0
    rw [hr.2]; ring
  rw [hz] at hs
  have h := levelEnvelope_strict_support hN d E t x (b^2) (a^2) ht hdb
    ⟨sq_nonneg _,vertical_domain_positive d x a ha.1⟩ (ne_of_lt hsq)
  have hp := mul_neg_of_neg_of_pos (sub_neg.mpr hsq) hs
  change levelEnvelopeAction d E t x (a^2) < levelEnvelopeAction d E t x (b^2)
  linarith

/-- The vertical real action is strictly decreasing on `(y, ∞)`. -/
theorem verticalRealAction_strictAntiOn {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x y : ℝ) (ht : 0 < t) (hr : PositiveLevelRoot d t x y) :
    StrictAntiOn (verticalRealAction d E t x) (Set.Ioi y) := by
  intro a ha b hb hab
  change y < a at ha
  change y < b at hb
  have hsq : a^2 < b^2 := by nlinarith [hr.1,ha]
  have hya : y^2 < a^2 := by nlinarith [hr.1,ha]
  have hda : LevelEnvelopeDomain d x (a^2) :=
    ⟨sq_nonneg _,vertical_domain_positive d x a (lt_trans hr.1 ha)⟩
  have hs := levelEnvelopeSlope_strictAnti hN d t x (y^2) (a^2)
    ⟨sq_nonneg _,vertical_domain_positive d x y hr.1⟩ hda hya
  have hz : levelEnvelopeSlope d t x (y^2)=0 := by
    change (verticalLevel d x y-1/t)/2=0
    rw [hr.2]; ring
  rw [hz] at hs
  have h := levelEnvelope_strict_support hN d E t x (a^2) (b^2) ht hda
    ⟨sq_nonneg _,vertical_domain_positive d x b (lt_trans hr.1 hb)⟩ (ne_of_gt hsq)
  have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hsq) hs
  change levelEnvelopeAction d E t x (b^2) < levelEnvelopeAction d E t x (a^2)
  linarith

private theorem verticalLevel_derivative_safe {N : ℕ} (d : Fin N → ℝ)
    (x v : ℝ) (hv : VerticalActionDomain d x v) :
    HasDerivAt (verticalLevel d x) (-2*v*levelB d x v) v := by
  have ht (j : Fin N) : HasDerivAt (fun w : ℝ => ((x-d j)^2+w^2)⁻¹)
      (-2*v*(((x-d j)^2+v^2)⁻¹)^2) v := by
    have h := ((hasDerivAt_const v ((x-d j)^2)).add
      ((hasDerivAt_id v).pow 2)).inv (ne_of_gt (hv j))
    have h' : HasDerivAt (fun w : ℝ => ((x-d j)^2+w^2)⁻¹)
        (-(2*v)/((x-d j)^2+v^2)^2) v := by
      convert! h using 1
      all_goals first | rfl | (funext w) | simp
    apply h'.congr_deriv
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have hs := (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht j)).const_mul (N : ℝ)⁻¹
  apply hs.congr_deriv
  unfold levelB realMean
  rw [← Finset.mul_sum]
  ring

/-- The second vertical derivative on the pole-safe line. -/
theorem hasDerivAt_deriv_verticalRealAction {N : ℕ} (d : Fin N → ℝ)
    (E t x v : ℝ) (ht : 0 < t) (hv : VerticalActionDomain d x v) :
    HasDerivAt (deriv (verticalRealAction d E t x))
      (verticalLevel d x v-1/t-2*v^2*levelB d x v) v := by
  have h := (hasDerivAt_id v).mul ((verticalLevel_derivative_safe d x v hv).sub_const (1/t))
  have he : deriv (verticalRealAction d E t x) =ᶠ[nhds v]
      (fun u => u*(verticalLevel d x u-1/t)) := by
    have hd : ∀ᶠ u in nhds v, VerticalActionDomain d x u := by
      unfold VerticalActionDomain
      rw [eventually_all]
      intro j
      have hc : Continuous (fun u : ℝ => (x-d j)^2+u^2) := by fun_prop
      exact hc.continuousAt.eventually (eventually_gt_nhds (hv j))
    filter_upwards [hd] with u hu
    exact (hasDerivAt_verticalRealAction d E t x u ht hu).deriv
  apply (h.congr_of_eventuallyEq he).congr_deriv
  simp only [id_eq]
  ring

/-- At `v = ±y`, the second vertical derivative is `-2y²B`. -/
theorem verticalRealAction_curvature_at_root {N : ℕ} (d : Fin N → ℝ)
    (E t x y v : ℝ) (ht : 0 < t) (hr : PositiveLevelRoot d t x y)
    (hv : v=y ∨ v= -y) :
    deriv (deriv (verticalRealAction d E t x)) v = -2*y^2*levelB d x y := by
  have hs : v^2=y^2 := sq_eq_sq_iff_eq_or_eq_neg.mpr hv
  have hd : VerticalActionDomain d x v := by
    intro j
    rw [hs]
    exact level_denominator_pos (x-d j) y hr.1
  rw [(hasDerivAt_deriv_verticalRealAction d E t x v ht hd).deriv]
  have hl : verticalLevel d x v=verticalLevel d x y := by simp only [verticalLevel,hs]
  have hb : levelB d x v=levelB d x y := by simp only [levelB,hs]
  rw [hl,hb,hs,hr.2]
  ring

/-- At `v = ±y` with `y ≥ η` and `t ≤ tmax`, the second vertical derivative is at most
`-2η²/tmax²`. -/
theorem verticalRealAction_curvature_uniform {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x y v η tmax : ℝ) (ht : 0 < t) (hr : PositiveLevelRoot d t x y)
    (hv : v=y ∨ v= -y) (hη : 0 < η) (hheight : η ≤ y) (htmax : t ≤ tmax) :
    deriv (deriv (verticalRealAction d E t x)) v ≤ -2*η^2/tmax^2 := by
  rw [verticalRealAction_curvature_at_root d E t x y v ht hr hv]
  have hJ := levelB_ge_inv_sq hN d t x y hr
  have hyη : η^2 ≤ y^2 := by nlinarith
  have htM : 0 < tmax := lt_of_lt_of_le ht htmax
  have ht2 : t^2 ≤ tmax^2 := by nlinarith
  have hq : 1/tmax^2 ≤ 1/t^2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ht) ht2
  have hB : 0 ≤ levelB d x y := (levelB_pos hN d x y hr.1).le
  have hprod := mul_le_mul hyη (le_trans hq hJ)
    (by positivity : 0 ≤ 1/tmax^2) (sq_nonneg y)
  have he : η^2*(1/tmax^2)=η^2/tmax^2 := by ring
  rw [he] at hprod
  have he2 : -2*η^2/tmax^2= -2*(η^2/tmax^2) := by ring
  rw [he2]
  linarith

/-- The logarithmic quotient identity for vertical action differences. -/
theorem verticalRealAction_difference {N : ℕ} (d : Fin N → ℝ)
    (E t x y v : ℝ) (hy : 0 < y) (hv : VerticalActionDomain d x v) :
    verticalRealAction d E t x v-verticalRealAction d E t x y =
      -(v^2-y^2)/(2*t)+
        realMean (fun j => Real.log (((x-d j)^2+v^2)/((x-d j)^2+y^2)))/2 := by
  have he (j : Fin N) :
      Real.log (((x-d j)^2+v^2)/((x-d j)^2+y^2)) =
        Real.log ((x-d j)^2+v^2)-Real.log ((x-d j)^2+y^2) :=
    Real.log_div (ne_of_gt (hv j)) (ne_of_gt (level_denominator_pos (x-d j) y hy))
  simp_rw [he]
  unfold verticalRealAction levelEnvelopeAction realMean
  rw [Finset.sum_sub_distrib]
  ring

private theorem vertical_mean_le_const {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ)
    (c : ℝ) (hf : ∀ j, f j ≤ c) : realMean f ≤ c := by
  have hs : (∑ j, f j) ≤ ∑ _j : Fin N, c := Finset.sum_le_sum (fun j _ => hf j)
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (N : ℝ)⁻¹ by positivity)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  simpa [realMean,Finset.sum_const,Fintype.card_fin,hn] using h

/-- The logarithmic tail bound `S(v) - S(y) ≤ -(v² - y²)/(2t) + log(1 + v²/y²)/2`. -/
theorem verticalRealAction_log_tail {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x y v : ℝ) (hy : 0 < y) (hv : VerticalActionDomain d x v) :
    verticalRealAction d E t x v-verticalRealAction d E t x y ≤
      -(v^2-y^2)/(2*t)+Real.log (1+v^2/y^2)/2 := by
  rw [verticalRealAction_difference d E t x y v hy hv]
  have hm : realMean (fun j => Real.log (((x-d j)^2+v^2)/((x-d j)^2+y^2))) ≤
      Real.log (1+v^2/y^2) := by
    apply vertical_mean_le_const hN
    intro j
    have hden := level_denominator_pos (x-d j) y hy
    have hy2 := sq_pos_of_pos hy
    have hr : ((x-d j)^2+v^2)/((x-d j)^2+y^2) ≤ 1+v^2/y^2 := by
      apply (div_le_iff₀ hden).mpr
      apply (mul_le_mul_iff_left₀ hy2).mp
      have he : (1+v^2/y^2)*((x-d j)^2+y^2)*y^2 =
          (y^2+v^2)*((x-d j)^2+y^2) := by field_simp
      rw [he]
      nlinarith [sq_nonneg (x-d j),sq_nonneg v,
        mul_nonneg (sq_nonneg (x-d j)) (sq_nonneg v)]
    exact (Real.log_le_log_iff (div_pos (hv j) hden) (by positivity)).mpr hr
  linarith

/-- Gaussian tail: for `v² ≥ y²`, `y ≥ η` and `t ≤ tmax`,
`S(v) - S(y) ≤ -v²/(4 tmax) + log(2 tmax/η²)/2 + η²/(4 tmax)`. -/
theorem verticalRealAction_gaussian_tail {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x y v η tmax : ℝ) (ht : 0 < t) (hr : PositiveLevelRoot d t x y)
    (hη : 0 < η) (hheight : η ≤ y) (htmax : t ≤ tmax) (hvy : y^2 ≤ v^2) :
    verticalRealAction d E t x v-verticalRealAction d E t x y ≤
      -v^2/(4*tmax)+Real.log (2*tmax/η^2)/2+η^2/(4*tmax) := by
  have htM : 0 < tmax := lt_of_lt_of_le ht htmax
  have hy2 : y^2 ≤ t := by
    have hs := positiveLevelRoot_le_sqrt hN d t x y ht hr
    nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  have hd : VerticalActionDomain d x v := by
    intro j
    have hypos := sq_pos_of_pos hr.1
    nlinarith [sq_nonneg (x-d j)]
  have htail := verticalRealAction_log_tail hN d E t x y v hr.1 hd
  have hηy : η^2 ≤ y^2 := by nlinarith [hr.1]
  have hq : v^2/y^2 ≤ v^2/η^2 :=
    div_le_div_of_nonneg_left (sq_nonneg v) (sq_pos_of_pos hη) hηy
  have hlog : Real.log (1+v^2/y^2) ≤ Real.log (1+v^2/η^2) :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mpr (by linarith)
  have hvariance : -(v^2-y^2)/(2*t) ≤ -v^2/(2*tmax)+1/2 := by
    have h1 : (v^2-y^2)/(2*tmax) ≤ (v^2-y^2)/(2*t) :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr hvy) (by positivity) (by linarith)
    have h2 : y^2/(2*tmax) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2*tmax)).mpr
      linarith
    have he : -(v^2-y^2)/(2*tmax)= -v^2/(2*tmax)+y^2/(2*tmax) := by ring
    have h1' : -(v^2-y^2)/(2*t) ≤ -(v^2-y^2)/(2*tmax) := by
      simpa only [neg_div] using neg_le_neg h1
    linarith only [h1',h2,he]
  have hsupport : Real.log (1+v^2/η^2) ≤ Real.log (2*tmax/η^2)+
      (1+v^2/η^2)/(2*tmax/η^2)-1 := by
    have h := Real.log_le_sub_one_of_pos
      (show 0 < (1+v^2/η^2)/(2*tmax/η^2) by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at h
    linarith
  have he : -v^2/(2*tmax)+1/2+
      (Real.log (2*tmax/η^2)+(1+v^2/η^2)/(2*tmax/η^2)-1)/2 =
      -v^2/(4*tmax)+Real.log (2*tmax/η^2)/2+η^2/(4*tmax) := by
    field_simp [ne_of_gt htM,ne_of_gt hη]
    ring
  linarith

/-- The Gaussian tail at the saddle of a solution of the finite MDE, with `η = tmin · vbulk`. -/
theorem verticalRealAction_saddle_gaussian_tail {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax vbulk v : ℝ) (m : ℂ)
    (htmin : 0 < tmin) (ht : tmin ≤ t) (htmax : t ≤ tmax)
    (hvbulk : 0 < vbulk) (hm : vbulk ≤ m.im) (hMDE : FiniteMDE d E t m)
    (hvy : (saddlePoint E t m).im^2 ≤ v^2) :
    verticalRealAction d E t (saddlePoint E t m).re v-
      verticalRealAction d E t (saddlePoint E t m).re (saddlePoint E t m).im ≤
      -v^2/(4*tmax)+Real.log (2*tmax/(tmin*vbulk)^2)/2+
        (tmin*vbulk)^2/(4*tmax) := by
  have htpos := lt_of_lt_of_le htmin ht
  exact verticalRealAction_gaussian_tail hN d E t (saddlePoint E t m).re
    (saddlePoint E t m).im v (tmin*vbulk) tmax htpos
    (positiveLevelRoot_at_saddle d E t m htpos (lt_of_lt_of_le hvbulk hm) hMDE)
    (mul_pos htmin hvbulk) (saddlePoint_im_lower E t tmin vbulk m htmin ht hvbulk.le hm)
    htmax hvy

end BlockBand.GaussianBulk
