module
public import BlockBand.GaussianBulk.LevelVerticalAction

/-!
# Vertical localization near the two saddles

On the vertical line through a positive level root `y ≥ η`, the real action drops quadratically
near `v = ±y` and by at least `η⁴/(64 tmax²)` away from them, giving the global two-saddle bound
`(η²/(16 tmax²)) min((|v| - y)², (η/2)²) ≤ S(y) - S(v)`, uniformly in `N` and `d`.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
namespace BlockBand.GaussianBulk
open Set Filter Topology
open scoped BigOperators

def verticalCrossLevel {N : ℕ} (d : Fin N → ℝ) (x y v : ℝ) : ℝ :=
  realMean (fun j => ((x-d j)^2+y^2)⁻¹*((x-d j)^2+v^2)⁻¹)

private theorem vertical_mean_mul {N : ℕ} (c : ℝ) (f : Fin N → ℝ) :
    realMean (fun j => c*f j)=c*realMean f := by
  unfold realMean
  rw [← Finset.mul_sum]
  ring

/-- Factorization of the level difference: `level(v) - level(y) = (y² - v²) · crossLevel`. -/
theorem verticalLevel_difference_cross {N : ℕ} (d : Fin N → ℝ)
    (x y v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    verticalLevel d x v-verticalLevel d x y=
      (y^2-v^2)*verticalCrossLevel d x y v := by
  have he (j : Fin N) : ((x-d j)^2+v^2)⁻¹-((x-d j)^2+y^2)⁻¹=
      (y^2-v^2)*(((x-d j)^2+y^2)⁻¹*((x-d j)^2+v^2)⁻¹) := by
    field_simp [ne_of_gt (level_denominator_pos (x-d j) y hy),
      ne_of_gt (level_denominator_pos (x-d j) v hv)]
    ring
  unfold verticalLevel verticalCrossLevel realMean
  rw [← mul_sub,← Finset.sum_sub_distrib]
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- For `y/2 ≤ v ≤ 3y/2`, the cross level is at least `1/(4 tmax²)`. -/
theorem verticalCrossLevel_neighborhood_lower {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (t tmax x y v : ℝ) (ht : 0 < t) (htmax : t ≤ tmax)
    (hr : PositiveLevelRoot d t x y) (hv : v ∈ Icc (y/2) (3*y/2)) :
    1/(4*tmax^2) ≤ verticalCrossLevel d x y v := by
  have hvp : 0 < v := by linarith [hr.1,hv.1]
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hs : (1/4:ℝ)*levelB d x y ≤ verticalCrossLevel d x y v := by
    unfold levelB verticalCrossLevel realMean
    rw [← mul_assoc,mul_comm (1/4:ℝ) (N:ℝ)⁻¹,mul_assoc,Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply Finset.sum_le_sum
    intro j _
    have hqy := level_denominator_pos (x-d j) y hr.1
    have hqv := level_denominator_pos (x-d j) v hvp
    have hcompare : (x-d j)^2+v^2 ≤ 4*((x-d j)^2+y^2) := by
      nlinarith [hv.2,hr.1,sq_nonneg (x-d j),sq_nonneg (3*y/2-v),sq_nonneg v]
    have hi : 1/(4*((x-d j)^2+y^2)) ≤ ((x-d j)^2+v^2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hqv hcompare
    have hm := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hqy.le)
    convert! hm using 1
    field_simp
  have hb := levelB_ge_inv_sq hN d t x y hr
  have hsq : t^2 ≤ tmax^2 := by nlinarith
  have hi := one_div_le_one_div_of_le (sq_pos_of_pos ht) hsq
  have hm := mul_le_mul_of_nonneg_left (le_trans hi hb) (by norm_num : (0:ℝ) ≤ 1/4)
  have he : (1/4:ℝ)*(1/tmax^2)=1/(4*tmax^2) := by ring
  rw [he] at hm
  exact le_trans hm hs

private theorem quadratic_deriv (C y u : ℝ) :
    HasDerivAt (fun z => (C/2)*(z-y)^2) (C*(u-y)) u := by
  have hh := (((hasDerivAt_id u).sub_const y).pow 2).const_mul (C/2)
  convert! hh using 1
  simp only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
  ring

/-- Quadratic drop: for `y/2 ≤ v ≤ 3y/2`, `(η²/(16 tmax²))(v - y)² ≤ S(y) - S(v)`. -/
theorem verticalRealAction_neighborhood_quadratic_drop {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmax x y eta v : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hr : PositiveLevelRoot d t x y) (heta : 0 < eta)
    (hheight : eta ≤ y) (hv : v ∈ Icc (y/2) (3*y/2)) :
    eta^2/(16*tmax^2)*(v-y)^2 ≤
      verticalRealAction d E t x y-verticalRealAction d E t x v := by
  let C := eta^2/(8*tmax^2)
  let g : ℝ → ℝ := fun u => verticalRealAction d E t x u+(C/2)*(u-y)^2
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hd (u : ℝ) (hu : 0 < u) : HasDerivAt g
      ((u-y)*(C-u*(u+y)*verticalCrossLevel d x y u)) u := by
    have hf := hasDerivAt_verticalRealAction d E t x u ht
      (fun j => level_denominator_pos (x-d j) u hu)
    have hh := hf.add (quadratic_deriv C y u)
    apply hh.congr_deriv
    rw [← hr.2,verticalLevel_difference_cross d x y u hr.1 hu]
    ring
  have hcoef (u : ℝ) (hu : u ∈ Icc (y/2) (3*y/2)) :
      C ≤ u*(u+y)*verticalCrossLevel d x y u := by
    have hup : 0 < u := by linarith [hr.1,hu.1]
    have hfirst : eta^2/2 ≤ u*(u+y) := by
      have hysq : eta^2 ≤ y^2 := by nlinarith [hr.1]
      nlinarith [hu.1,hr.1,sq_nonneg (u-y/2)]
    have hcross := verticalCrossLevel_neighborhood_lower hN d t tmax x y u ht htmax hr hu
    have hm := mul_le_mul hfirst hcross
      (by positivity : 0 ≤ 1/(4*tmax^2)) (by nlinarith : 0 ≤ u*(u+y))
    have he : (eta^2/2)*(1/(4*tmax^2))=C := by dsimp only [C];ring
    rw [he] at hm
    exact hm
  have hmax : g v ≤ g y := by
    rcases lt_trichotomy v y with hlt | heq | hlt
    · have hc : ContinuousOn g (Icc v y) := by
        intro u hu
        exact (hd u (by linarith [hv.1,hu.1,hr.1])).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ g (Ioo v y) := by
        intro u hu
        exact (hd u (by linarith [hv.1,hu.1,hr.1])).differentiableAt.differentiableWithinAt
      obtain ⟨u,hu,hs⟩ := exists_deriv_eq_slope g hlt hc hdiff
      have hloc : u ∈ Icc (y/2) (3*y/2) := ⟨by linarith [hv.1,hu.1],by linarith [hr.1,hu.2]⟩
      have hnonneg : 0 ≤ deriv g u := by
        rw [(hd u (by linarith [hloc.1,hr.1])).deriv]
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith [hu.2]) (sub_nonpos.mpr (hcoef u hloc))
      rw [hs] at hnonneg
      have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp hnonneg
      linarith
    · rw [heq]
    · have hc : ContinuousOn g (Icc y v) := by
        intro u hu
        exact (hd u (lt_of_lt_of_le hr.1 hu.1)).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ g (Ioo y v) := by
        intro u hu
        exact (hd u (lt_trans hr.1 hu.1)).differentiableAt.differentiableWithinAt
      obtain ⟨u,hu,hs⟩ := exists_deriv_eq_slope g hlt hc hdiff
      have hloc : u ∈ Icc (y/2) (3*y/2) := ⟨by linarith [hr.1,hu.1],by linarith [hv.2,hu.2]⟩
      have hnonpos : deriv g u ≤ 0 := by
        rw [(hd u (lt_trans hr.1 hu.1)).deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith [hu.1]) (sub_nonpos.mpr (hcoef u hloc))
      rw [hs] at hnonpos
      have hh := (div_le_iff₀ (sub_pos.mpr hlt)).mp hnonpos
      linarith
  dsimp only [g] at hmax
  simp only [sub_self,zero_pow (by norm_num : 2 ≠ 0),mul_zero,add_zero] at hmax
  have he : C/2=eta^2/(16*tmax^2) := by dsimp only [C];ring
  rw [he] at hmax
  linarith

/-- The vertical real action depends only on `|v|`. -/
theorem verticalRealAction_abs {N : ℕ} (d : Fin N → ℝ)
    (E t x v : ℝ) : verticalRealAction d E t x |v|=verticalRealAction d E t x v := by
  simp only [verticalRealAction,sq_abs]

private theorem vertical_below_root_le {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t x y a b : ℝ) (ht : 0 < t)
    (hr : PositiveLevelRoot d t x y) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : 0 < b) (hby : b < y) (hda : VerticalActionDomain d x a) :
    verticalRealAction d E t x a ≤ verticalRealAction d E t x b := by
  have hdb : LevelEnvelopeDomain d x (b^2) :=
    ⟨sq_nonneg _,fun j => level_denominator_pos (x-d j) b hb⟩
  have hdy : LevelEnvelopeDomain d x (y^2) :=
    ⟨sq_nonneg _,fun j => level_denominator_pos (x-d j) y hr.1⟩
  have hs := levelEnvelopeSlope_strictAnti hN d t x (b^2) (y^2) hdb hdy
    (by nlinarith [hr.1])
  have hz : levelEnvelopeSlope d t x (y^2)=0 := by
    change (verticalLevel d x y-1/t)/2=0
    rw [hr.2]
    ring
  rw [hz] at hs
  have h := levelEnvelope_support hN d E t x (b^2) (a^2) ht hdb
    ⟨sq_nonneg _,hda⟩
  have hsq : a^2 ≤ b^2 := by nlinarith
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsq) hs.le
  change levelEnvelopeAction d E t x (a^2) ≤ levelEnvelopeAction d E t x (b^2)
  linarith

/-- Off-saddle drop: if `||v| - y| ≥ η/2`, then `η⁴/(64 tmax²) ≤ S(y) - S(v)`. -/
theorem verticalRealAction_off_saddle_drop {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmax x y eta v : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hr : PositiveLevelRoot d t x y) (heta : 0 < eta)
    (hheight : eta ≤ y) (hv : VerticalActionDomain d x v)
    (hfar : eta/2 ≤ abs (|v|-y)) :
    eta^4/(64*tmax^2) ≤ verticalRealAction d E t x y-verticalRealAction d E t x v := by
  have hsafe : VerticalActionDomain d x |v| := by simpa only [VerticalActionDomain,sq_abs] using hv
  have hh (b : ℝ) (hb : b ∈ Icc (y/2) (3*y/2)) (he : (b-y)^2=(eta/2)^2) :
      eta^4/(64*tmax^2) ≤ verticalRealAction d E t x y-verticalRealAction d E t x b := by
    have h := verticalRealAction_neighborhood_quadratic_drop hN d E t tmax x y eta b
      ht htmax hr heta hheight hb
    rw [he] at h
    convert! h using 1
    ring
  rcases le_total |v| y with hleft | hright
  · let b := y-eta/2
    have hb : b ∈ Icc (y/2) (3*y/2) := ⟨by dsimp only [b];linarith,by dsimp only [b];linarith [hr.1]⟩
    have hbp : 0 < b := by dsimp only [b];linarith
    have hab : |v| ≤ b := by
      rw [abs_of_nonpos (sub_nonpos.mpr hleft)] at hfar
      dsimp only [b]
      linarith
    have h := vertical_below_root_le hN d E t x y |v| b ht hr (abs_nonneg _) hab hbp
      (by dsimp only [b];linarith) hsafe
    rw [verticalRealAction_abs] at h
    have hq := hh b hb (by dsimp only [b];ring)
    linarith
  · let b := y+eta/2
    have hb : b ∈ Icc (y/2) (3*y/2) := ⟨by dsimp only [b];linarith [hr.1],by dsimp only [b];linarith⟩
    have hbp : y < b := by dsimp only [b];linarith
    have hab : b ≤ |v| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hright)] at hfar
      dsimp only [b]
      linarith
    have h := (verticalRealAction_strictAntiOn hN d E t x y ht hr).antitoneOn
      (show b ∈ Ioi y from hbp) (show |v| ∈ Ioi y from lt_of_lt_of_le hbp hab) hab
    rw [verticalRealAction_abs] at h
    have hq := hh b hb (by dsimp only [b];ring)
    linarith

/-- Global two-saddle bound `(η²/(16 tmax²)) min((|v| - y)², (η/2)²) ≤ S(y) - S(v)` on the
pole-safe line. -/
theorem verticalRealAction_global_two_saddle_drop {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmax x y eta v : ℝ) (ht : 0 < t)
    (htmax : t ≤ tmax) (hr : PositiveLevelRoot d t x y) (heta : 0 < eta)
    (hheight : eta ≤ y) (hv : VerticalActionDomain d x v) :
    eta^2/(16*tmax^2)*min ((|v|-y)^2) ((eta/2)^2) ≤
      verticalRealAction d E t x y-verticalRealAction d E t x v := by
  have hc : 0 ≤ eta^2/(16*tmax^2) := by positivity
  by_cases hnear : abs (|v|-y) ≤ eta/2
  · have hloc : |v| ∈ Icc (y/2) (3*y/2) := by
      rcases abs_le.mp hnear with ⟨hl,hu⟩
      exact ⟨by linarith,by linarith⟩
    have h := verticalRealAction_neighborhood_quadratic_drop hN d E t tmax x y eta |v|
      ht htmax hr heta hheight hloc
    rw [verticalRealAction_abs] at h
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hc) h
  · have h := verticalRealAction_off_saddle_drop hN d E t tmax x y eta v ht htmax hr
      heta hheight hv (le_of_lt (lt_of_not_ge hnear))
    have he : eta^2/(16*tmax^2)*(eta/2)^2=eta^4/(64*tmax^2) := by ring
    rw [← he] at h
    exact le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hc) h

/-- The two-saddle bound at the saddle of a solution of the finite MDE, with `η = tmin · vbulk`. -/
theorem verticalRealAction_MDE_two_saddle_drop {N : ℕ} (hN : 0 < N)
    (d : Fin N → ℝ) (E t tmin tmax vbulk v : ℝ) (m : ℂ)
    (htmin : 0 < tmin) (ht : tmin ≤ t) (htmax : t ≤ tmax)
    (hvbulk : 0 < vbulk) (hm : vbulk ≤ m.im) (hMDE : FiniteMDE d E t m)
    (hv : VerticalActionDomain d (saddlePoint E t m).re v) :
    (tmin*vbulk)^2/(16*tmax^2)*
      min ((|v|-(saddlePoint E t m).im)^2) ((tmin*vbulk/2)^2) ≤
        verticalRealAction d E t (saddlePoint E t m).re (saddlePoint E t m).im-
          verticalRealAction d E t (saddlePoint E t m).re v := by
  have htp := lt_of_lt_of_le htmin ht
  have hmp := lt_of_lt_of_le hvbulk hm
  apply verticalRealAction_global_two_saddle_drop hN d E t tmax _ _ (tmin*vbulk) v
    htp htmax (positiveLevelRoot_at_saddle d E t m htp hmp hMDE) (mul_pos htmin hvbulk) _ hv
  exact saddlePoint_im_lower E t tmin vbulk m htmin ht hvbulk.le hm

end BlockBand.GaussianBulk
