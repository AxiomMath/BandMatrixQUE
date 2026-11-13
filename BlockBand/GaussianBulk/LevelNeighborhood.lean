module

public import BlockBand.GaussianBulk.LevelAction

/-!
# A uniform neighborhood of positive level height

The squared level height is globally Lipschitz with constant `2√t`. Hence, if the height at
`x₀` is at least `η` and `t ≤ tmax`, it is at least `η/2` on `|x - x₀| ≤ η²/(4√tmax)`, and there
`ψ' ≥ η²/tmax` and the level action has second derivative at least `η²/tmax²`. The constants
are uniform in `N` and in the source `d`.
-/

set_option autoImplicit false
@[expose] public section
namespace BlockBand.GaussianBulk
noncomputable section
open Set Filter Topology

private theorem continuous_nonneg_upper_bound (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (hd : ∀ x, 0 < f x → DifferentiableAt ℝ f x)
    (hb : ∀ x, 0 < f x → |deriv f x| ≤ C)
    (a b : ℝ) (hab : a ≤ b) : f b-f a ≤ C*(b-a) := by
  by_cases hba : f b ≤ f a
  · exact le_trans (sub_nonpos.mpr hba) (mul_nonneg hC (sub_nonneg.mpr hab))
  · have hfab : f a < f b := lt_of_not_ge hba
    let s : Set ℝ := Icc a b ∩ {x | f x=f a}
    have hs : IsCompact s := isCompact_Icc.inter_right (isClosed_eq hf continuous_const)
    have hne : s.Nonempty := ⟨a,⟨⟨le_rfl,hab⟩,rfl⟩⟩
    obtain ⟨c,hc,hmax⟩ := hs.exists_isMaxOn hne continuousOn_id
    have hcb : c < b := by
      apply lt_of_le_of_ne hc.1.2
      intro he
      have hfc : f b=f a := he ▸ hc.2
      exact (ne_of_gt hfab) hfc
    have hpos (x : ℝ) (hx : x ∈ Ioo c b) : 0 < f x := by
      have hfx : f a < f x := by
        by_contra hnfx
        have hle : f x ≤ f a := le_of_not_gt hnfx
        obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc (le_of_lt hx.2)
          hf.continuousOn ⟨hle,le_of_lt hfab⟩
        have hzS : z ∈ s := ⟨⟨le_trans hc.1.1 (le_trans (le_of_lt hx.1) hz.1),hz.2⟩,hfz⟩
        have hzle : z ≤ c := hmax hzS
        exact (not_lt_of_ge hzle) (lt_of_lt_of_le hx.1 hz.1)
      exact lt_of_le_of_lt (hn a) hfx
    have hdOn : DifferentiableOn ℝ f (Ioo c b) :=
      fun x hx => (hd x (hpos x hx)).differentiableWithinAt
    obtain ⟨z,hz,hder⟩ := exists_deriv_eq_slope f hcb hf.continuousOn hdOn
    have hbound : (f b-f c)/(b-c) ≤ C := by
      rw [← hder]
      exact le_trans (le_abs_self _) (hb z (hpos z hz))
    have hdiff := (div_le_iff₀ (sub_pos.mpr hcb)).mp hbound
    rw [hc.2] at hdiff
    exact le_trans hdiff (mul_le_mul_of_nonneg_left (by linarith [hc.1.1]) hC)

/-- A continuous nonnegative function that is differentiable with `|f'| ≤ C` wherever it is
positive is globally `C`-Lipschitz, even with corners at its zeros. -/
theorem continuous_nonneg_abs_sub_le (f : ℝ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : Continuous f) (hn : ∀ x, 0 ≤ f x)
    (hd : ∀ x, 0 < f x → DifferentiableAt ℝ f x)
    (hb : ∀ x, 0 < f x → |deriv f x| ≤ C) (a b : ℝ) :
    |f b-f a| ≤ C*|b-a| := by
  let g : ℝ → ℝ := fun x => f (-x)
  have hg : Continuous g := hf.comp continuous_neg
  have hgn : ∀ x, 0 ≤ g x := fun x => hn (-x)
  have hgd (x : ℝ) (hx : 0 < g x) : DifferentiableAt ℝ g x :=
    (hd (-x) hx).comp x (hasDerivAt_neg x).differentiableAt
  have hgb (x : ℝ) (hx : 0 < g x) : |deriv g x| ≤ C := by
    have hh := (hd (-x) hx).hasDerivAt.comp x (hasDerivAt_neg x)
    have he : deriv g x= -deriv f (-x) := by
      simpa only [mul_neg_one,Function.comp_def,g] using hh.deriv
    rw [he,abs_neg]
    exact hb (-x) hx
  have hordered (a b : ℝ) (hab : a ≤ b) : |f b-f a| ≤ C*|b-a| := by
    have hu := continuous_nonneg_upper_bound f C hC hf hn hd hb a b hab
    have hl := continuous_nonneg_upper_bound g C hC hg hgn hgd hgb (-b) (-a) (neg_le_neg hab)
    dsimp only [g] at hl
    simp only [neg_neg] at hl
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    apply abs_le.mpr
    constructor <;> linarith
  rcases le_total a b with hab | hba
  · exact hordered a b hab
  · simpa only [abs_sub_comm] using hordered b a hba

/-- The derivative of the squared level height has magnitude at most `2√t` at every active point. -/
theorem abs_deriv_levelHeight_sq_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    |deriv (fun a => (levelHeight d t a)^2) x| ≤ 2*Real.sqrt t := by
  have hy := (levelHeight_root hN d t x ht hx).1
  have hY := (hasDerivAt_levelHeight hN d t x ht hx)
  have hder : deriv (fun a => (levelHeight d t a)^2) x =
      2*levelHeight d t x*deriv (levelHeight d t) x := by
    have hh := (hY.pow 2).deriv
    have hfun : (levelHeight d t)^2=(fun a => (levelHeight d t a)^2) := by
      funext a
      simp only [Pi.pow_apply]
    rw [hfun,← hY.deriv] at hh
    simpa only [Nat.cast_ofNat,Nat.reduceSub,pow_one] using hh
  rw [hder,abs_mul,abs_of_pos (mul_pos (by norm_num) hy)]
  calc
    _ ≤ (2*levelHeight d t x)*(Real.sqrt t/levelHeight d t x) :=
      mul_le_mul_of_nonneg_left (abs_deriv_levelHeight_le hN d t x ht hx) (by positivity)
    _ = 2*Real.sqrt t := by field_simp [ne_of_gt hy]

/-- The squared level height is globally `2√t`-Lipschitz. -/
theorem levelHeight_sq_abs_sub_le {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t a b : ℝ) (ht : 0 < t) :
    |(levelHeight d t b)^2-(levelHeight d t a)^2| ≤ 2*Real.sqrt t*|b-a| := by
  have hfun : (levelHeight d t)^2=(fun a => (levelHeight d t a)^2) := by
    funext a
    simp only [Pi.pow_apply]
  have hcont : Continuous (fun a => (levelHeight d t a)^2) := by
    rw [← hfun]
    exact (levelHeight_continuous hN d t ht).pow 2
  apply continuous_nonneg_abs_sub_le (fun a => (levelHeight d t a)^2) _ (by positivity)
    hcont (fun x => sq_nonneg _)
  · intro x hx
    have hy : 0 < levelHeight d t x := by
      have hnonneg := (levelHeight_bounds hN d t x ht).1
      nlinarith
    rw [← hfun]
    exact ((hasDerivAt_levelHeight hN d t x ht
      ((levelHeight_pos_iff hN d t x ht).mp hy)).pow 2).differentiableAt
  · intro x hx
    have hy : 0 < levelHeight d t x := by
      have hnonneg := (levelHeight_bounds hN d t x ht).1
      nlinarith
    exact abs_deriv_levelHeight_sq_le hN d t x ht
      ((levelHeight_pos_iff hN d t x ht).mp hy)

/-- If the height at `x₀` is at least `η`, the squared height is at least `η²/2` on
`|x - x₀| ≤ η²/(4√tmax)`. -/
theorem levelHeight_sq_neighborhood_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀)
    (hclose : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    eta^2/2 ≤ (levelHeight d t x)^2 := by
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hsq : 0 < Real.sqrt tmax := Real.sqrt_pos.mpr htm
  have hvar := levelHeight_sq_abs_sub_le hN d t x₀ x ht
  have hvar' : |(levelHeight d t x)^2-(levelHeight d t x₀)^2| ≤
      2*Real.sqrt tmax*|x-x₀| :=
    le_trans hvar (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htmax) (by norm_num)) (abs_nonneg _))
  have hc := mul_le_mul_of_nonneg_left hclose (show 0 ≤ 2*Real.sqrt tmax by positivity)
  have he : 2*Real.sqrt tmax*(eta^2/(4*Real.sqrt tmax))=eta^2/2 := by
    field_simp [ne_of_gt hsq]
    ring
  rw [he] at hc
  have hbase : eta^2 ≤ (levelHeight d t x₀)^2 := by nlinarith
  have hh := neg_le_of_abs_le (le_trans hvar' hc)
  linarith

/-- If the height at `x₀` is at least `η`, the height is at least `η/2` on
`|x - x₀| ≤ η²/(4√tmax)`. -/
theorem levelHeight_neighborhood_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀)
    (hclose : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    eta/2 ≤ levelHeight d t x := by
  have hs := levelHeight_sq_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight hclose
  have hn := (levelHeight_bounds hN d t x ht).1
  nlinarith

/-- At every active point, the derivative of the level action has derivative `ψ'/t`. -/
theorem hasDerivAt_deriv_levelAction {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t x : ℝ) (ht : 0 < t) (hx : LevelActive d t x) :
    HasDerivAt (deriv (levelAction d E t)) (deriv (levelPsi d t) x/t) x := by
  have hpsi := (hasDerivAt_levelPsi hN d t x ht hx).differentiableAt.hasDerivAt
  have hfun := (hpsi.sub_const E).div_const t
  have hact : ∀ᶠ a in nhds x, LevelActive d t a :=
    (isOpen_levelActive hN d t ht).mem_nhds hx
  have heq : deriv (levelAction d E t) =ᶠ[nhds x] (fun a => (levelPsi d t a-E)/t) := by
    filter_upwards [hact] with a ha
    exact (hasDerivAt_levelAction hN d E t a ht ha).deriv
  exact hfun.congr_of_eventuallyEq heq

/-- The lower bound `ψ' ≥ η²/tmax` on the neighborhood. -/
theorem deriv_levelPsi_neighborhood_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀)
    (hclose : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    eta^2/tmax ≤ deriv (levelPsi d t) x := by
  have hs := levelHeight_sq_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight hclose
  have hy := levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight hclose
  have hx := (levelHeight_pos_iff hN d t x ht).mp (lt_of_lt_of_le (by linarith : 0 < eta/2) hy)
  calc
    eta^2/tmax ≤ eta^2/t := div_le_div_of_nonneg_left (sq_nonneg eta) ht htmax
    _ ≤ 2*(levelHeight d t x)^2/t :=
      div_le_div_of_nonneg_right (by linarith [hs]) (le_of_lt ht)
    _ ≤ deriv (levelPsi d t) x := deriv_levelPsi_lower hN d t x ht hx

/-- The lower bound `η²/tmax²` on the second derivative of the level action on the neighborhood. -/
theorem deriv2_levelAction_neighborhood_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmax eta x₀ x : ℝ) (ht : 0 < t) (htmax : t ≤ tmax) (heta : 0 < eta)
    (hheight : eta ≤ levelHeight d t x₀)
    (hclose : |x-x₀| ≤ eta^2/(4*Real.sqrt tmax)) :
    eta^2/tmax^2 ≤ deriv (deriv (levelAction d E t)) x := by
  have hy := levelHeight_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight hclose
  have hx := (levelHeight_pos_iff hN d t x ht).mp (lt_of_lt_of_le (by linarith : 0 < eta/2) hy)
  rw [(hasDerivAt_deriv_levelAction hN d E t x ht hx).deriv]
  have htm : 0 < tmax := lt_of_lt_of_le ht htmax
  have hnonneg : 0 ≤ eta^2/tmax := div_nonneg (sq_nonneg eta) (le_of_lt htm)
  calc
    eta^2/tmax^2 = (eta^2/tmax)/tmax := by simp only [div_div,pow_two]
    _ ≤ (eta^2/tmax)/t := div_le_div_of_nonneg_left hnonneg ht htmax
    _ ≤ deriv (levelPsi d t) x/t := div_le_div_of_nonneg_right
      (deriv_levelPsi_neighborhood_lower hN d t tmax eta x₀ x ht htmax heta hheight hclose)
      (le_of_lt ht)

/-- At the saddle of a solution of the finite MDE with `Im m ≥ v`, the height is at least
`tmin · v/2` on `|x - Re z₀| ≤ (tmin v)²/(4√tmax)`. -/
theorem levelHeight_MDE_neighborhood_lower {N : ℕ} (hN : 0 < N) (d : Fin N → ℝ)
    (E t tmin tmax v x : ℝ) (m : ℂ) (htmin : 0 < tmin)
    (ht : tmin ≤ t) (htmax : t ≤ tmax) (hv : 0 < v) (hm : v ≤ m.im)
    (hMDE : FiniteMDE d E t m)
    (hclose : |x-(saddlePoint E t m).re| ≤ (tmin*v)^2/(4*Real.sqrt tmax)) :
    (tmin*v)/2 ≤ levelHeight d t x := by
  have htp : 0 < t := lt_of_lt_of_le htmin ht
  have hmp : 0 < m.im := lt_of_lt_of_le hv hm
  apply levelHeight_neighborhood_lower hN d t tmax (tmin*v) _ x htp htmax
    (mul_pos htmin hv) _ hclose
  rw [levelHeight_at_saddle hN d E t m htp hmp hMDE]
  exact saddlePoint_im_lower E t tmin v m htmin ht (le_of_lt hv) hm

end
end BlockBand.GaussianBulk
