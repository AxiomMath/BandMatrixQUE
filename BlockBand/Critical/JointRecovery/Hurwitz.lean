module

public import Mathlib

/-!
# A one-variable Hurwitz kit (zero persistence, simple and multiple zeros)

* `eventually_ne_zero_of_isCompact` (H1): zero-free compacts of `g` are eventually zero-free.
* `eventually_exists_zero_mem_ball` (H2): zeros of `g ≢ 0` persist in every ball.
* `exists_eventually_injOn_of_deriv_ne_zero` (H3): near a point with `g' ≠ 0` the
  approximants are eventually injective with nonvanishing derivative (so near a simple zero
  of `g` they have exactly one zero, and it is simple).
* `eventually_multiple_or_two_zeros` (H4): near a multiple zero of `g ≢ 0` every approximant
  eventually has a multiple zero or two distinct zeros. Proof by `dslope` and the maximum
  modulus principle; no argument principle is used.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set Metric

variable {ι : Type*} {l : Filter ι} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}

/-- Locally uniform convergence is uniform on every compact set (metric form). -/
theorem eventually_dist_lt_of_isCompact (hconv : TendstoLocallyUniformly f g l)
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ w ∈ K, dist (g w) (f i w) < ε :=
  Metric.tendstoUniformlyOn_iff.mp
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv K hK) ε hε

/-- Isolated zeros: an entire function with one nonzero value is nonzero on a punctured
neighbourhood of every point. -/
theorem eventually_ne_zero_punctured (hg : Differentiable ℂ g) {w₁ : ℂ} (hw₁ : g w₁ ≠ 0)
    (x₀ : ℂ) : ∀ᶠ w in 𝓝[≠] x₀, g w ≠ 0 := by
  rcases (hg.analyticAt x₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hana : AnalyticOnNhd ℂ g univ := fun z _ => hg.analyticAt z
    have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ x₀) h (mem_univ w₁)
    exact hw₁ this
  · exact h

/-- Radius form of isolated zeros. -/
theorem exists_ball_punctured_ne_zero {x₀ : ℂ} (hiso : ∀ᶠ w in 𝓝[≠] x₀, g w ≠ 0) :
    ∃ ε > 0, ∀ w, dist w x₀ < ε → w ≠ x₀ → g w ≠ 0 := by
  rcases Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hiso) with ⟨ε, hε, h⟩
  exact ⟨ε, hε, fun w hw hne => h hw hne⟩

/-- A positive lower bound of `‖g‖` on a nonempty compact zero-free set. -/
theorem exists_pos_le_norm_of_isCompact (hg : Continuous g) {K : Set ℂ} (hK : IsCompact K)
    (hKne : K.Nonempty) (hgK : ∀ w ∈ K, g w ≠ 0) : ∃ c > 0, ∀ w ∈ K, c ≤ ‖g w‖ := by
  obtain ⟨w₀, hw₀, hmin⟩ := hK.exists_isMinOn hKne hg.norm.continuousOn
  exact ⟨‖g w₀‖, norm_pos_iff.mpr (hgK w₀ hw₀), fun w hw => hmin hw⟩

/-- **H1.** If `g` has no zero on the compact `K`, then eventually neither has `f i`; more
precisely `‖f i‖ ≥ c/2` on `K` when `‖g‖ ≥ c` on `K`. -/
theorem eventually_half_le_norm_of_isCompact (hconv : TendstoLocallyUniformly f g l)
    {K : Set ℂ} (hK : IsCompact K) {c : ℝ} (hc : 0 < c) (hgK : ∀ w ∈ K, c ≤ ‖g w‖) :
    ∀ᶠ i in l, ∀ w ∈ K, c / 2 ≤ ‖f i w‖ := by
  filter_upwards [eventually_dist_lt_of_isCompact hconv hK (half_pos hc)] with i hi w hw
  have h1 := hgK w hw
  have h2 := hi w hw
  rw [dist_eq_norm] at h2
  have h3 : ‖g w‖ ≤ ‖g w - f i w‖ + ‖f i w‖ := by
    simpa using norm_add_le (g w - f i w) (f i w)
  linarith

/-- **H1** (zero-free form). -/
theorem eventually_ne_zero_of_isCompact (hconv : TendstoLocallyUniformly f g l)
    (hg : Continuous g) {K : Set ℂ} (hK : IsCompact K) (hgK : ∀ w ∈ K, g w ≠ 0) :
    ∀ᶠ i in l, ∀ w ∈ K, f i w ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact .of_forall fun _ w hw => absurd hw (notMem_empty w)
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_norm_of_isCompact hg hK hKne hgK
  filter_upwards [eventually_half_le_norm_of_isCompact hconv hK hc hcK] with i hi w hw h0
  have := hi w hw
  rw [h0, norm_zero] at this
  linarith

/-- Maximum modulus for `1/φ` on a ball: if `φ` is entire-on-a-neighbourhood of the closed
ball, zero-free there, and `‖φ‖ ≥ c > 0` on the sphere, then `‖φ‖ ≥ c` at the centre. -/
theorem le_norm_of_zero_free_closedBall {φ : ℂ → ℂ} {x₀ : ℂ} {s c : ℝ} (hs : 0 < s)
    (hc : 0 < c) (hφ : DifferentiableOn ℂ φ (closedBall x₀ s))
    (hne : ∀ w ∈ closedBall x₀ s, φ w ≠ 0) (hsph : ∀ w ∈ sphere x₀ s, c ≤ ‖φ w‖)
    {z : ℂ} (hz : z ∈ closedBall x₀ s) : c ≤ ‖φ z‖ := by
  have hd : DiffContOnCl ℂ (fun w => (φ w)⁻¹) (ball x₀ s) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball x₀ hs.ne']
    exact hφ.inv hne
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (C := c⁻¹) (by
      intro w hw
      rw [frontier_ball x₀ hs.ne'] at hw
      rw [norm_inv]
      exact inv_anti₀ hc (hsph w hw))
    (by rw [closure_ball x₀ hs.ne']; exact hz)
  rw [norm_inv] at hbound
  have hpos : 0 < ‖φ z‖ := norm_pos_iff.mpr (hne z hz)
  exact (inv_le_inv₀ hpos hc).mp hbound

/-- **H2. Zero persistence.** If `g` is entire with an isolated zero at `x₀`, then for every
`r > 0`, eventually `f i` has a zero in `ball x₀ r`. -/
theorem eventually_exists_zero_mem_ball (hconv : TendstoLocallyUniformly f g l)
    (hfd : ∀ i, Differentiable ℂ (f i)) (hg : Continuous g) {x₀ : ℂ} (hx₀ : g x₀ = 0)
    (hiso : ∀ᶠ w in 𝓝[≠] x₀, g w ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, ∃ w ∈ ball x₀ r, f i w = 0 := by
  obtain ⟨ε, hε, hpunct⟩ := exists_ball_punctured_ne_zero hiso
  set s := min (ε / 2) (r / 2) with hs_def
  have hs : 0 < s := lt_min (half_pos hε) (half_pos hr)
  have hsε : s < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hsr : s < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  have hsph : ∀ w ∈ sphere x₀ s, g w ≠ 0 := by
    intro w hw
    rw [mem_sphere] at hw
    exact hpunct w (hw ▸ hsε) (fun h => by rw [h, dist_self] at hw; exact hs.ne' hw.symm)
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_norm_of_isCompact hg (isCompact_sphere x₀ s)
    (NormedSpace.sphere_nonempty.mpr hs.le) hsph
  have hcentre : ∀ᶠ i in l, ‖f i x₀‖ < c / 2 := by
    filter_upwards [eventually_dist_lt_of_isCompact hconv (isCompact_singleton (x := x₀))
      (half_pos hc)] with i hi
    have := hi x₀ rfl
    rwa [dist_eq_norm, hx₀, zero_sub, norm_neg] at this
  filter_upwards [eventually_half_le_norm_of_isCompact hconv (isCompact_sphere x₀ s) hc hcK,
    hcentre] with i hi hi0
  by_contra hno
  push Not at hno
  have hne : ∀ w ∈ closedBall x₀ s, f i w ≠ 0 := fun w hw =>
    hno w (closedBall_subset_ball hsr hw)
  have := le_norm_of_zero_free_closedBall hs (half_pos hc) (hfd i).differentiableOn hne hi
    (mem_closedBall_self hs.le)
  linarith

/-- Locally uniform convergence of derivatives (Weierstrass), entire setting. -/
theorem tendstoLocallyUniformly_deriv (hconv : TendstoLocallyUniformly f g l)
    (hfd : ∀ i, Differentiable ℂ (f i)) :
    TendstoLocallyUniformly (fun i => deriv (f i)) (deriv g) l := by
  have h := (tendstoLocallyUniformlyOn_univ.mpr hconv).deriv
    (Eventually.of_forall fun i => (hfd i).differentiableOn) isOpen_univ
  exact tendstoLocallyUniformlyOn_univ.mp h

/-- **H3. Local injectivity.** If `g' (x₀) ≠ 0` (`g` entire), there is `r > 0` such that
eventually `f i` is injective on `ball x₀ r` with nonvanishing derivative there. -/
theorem exists_eventually_injOn_of_deriv_ne_zero (hconv : TendstoLocallyUniformly f g l)
    (hfd : ∀ i, Differentiable ℂ (f i)) (hg : Differentiable ℂ g) {x₀ : ℂ}
    (hd : deriv g x₀ ≠ 0) :
    ∃ r > 0, ∀ᶠ i in l, (∀ a ∈ ball x₀ r, ∀ b ∈ ball x₀ r, f i a = f i b → a = b) ∧
      ∀ a ∈ ball x₀ r, deriv (f i) a ≠ 0 := by
  set c := ‖deriv g x₀‖ with hc_def
  have hc : 0 < c := norm_pos_iff.mpr hd
  have hcont : Continuous (deriv g) :=
    ((hg.differentiableOn (s := univ)).deriv isOpen_univ).continuousOn.comp_continuous
      continuous_id (fun _ => mem_univ _) |>.congr fun _ => rfl
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuous_iff.mp hcont x₀ (c / 4) (by positivity)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  filter_upwards [eventually_dist_lt_of_isCompact (tendstoLocallyUniformly_deriv hconv hfd)
    (isCompact_closedBall x₀ (δ / 2)) (show 0 < c / 4 by positivity)] with i hi
  have hbound : ∀ w ∈ ball x₀ (δ / 2), ‖deriv (f i) w - deriv g x₀‖ ≤ c / 2 := by
    intro w hw
    have h1 := hi w (ball_subset_closedBall hw)
    have h2 := hδc w ((mem_ball.mp hw).trans (half_lt_self hδ))
    rw [dist_eq_norm] at h1 h2
    calc ‖deriv (f i) w - deriv g x₀‖
        ≤ ‖deriv g w - deriv (f i) w‖ + ‖deriv g w - deriv g x₀‖ := by
          rw [← norm_neg (deriv g w - deriv (f i) w)]
          refine (norm_add_le _ _).trans_eq' ?_
          congr 1; ring
      _ ≤ c / 2 := by linarith
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    set d := deriv g x₀
    have hφ : ∀ w, HasDerivAt (fun w => f i w - d * w) (deriv (f i) w - d) w := fun w => by
      have h := ((hfd i) w).hasDerivAt.sub ((hasDerivAt_id w).const_mul d)
      rw [mul_one] at h
      exact h
    have hmv := (convex_ball x₀ (δ / 2)).norm_image_sub_le_of_norm_deriv_le
      (f := fun w => f i w - d * w) (C := c / 2)
      (fun w _ => (hφ w).differentiableAt)
      (fun w hw => by rw [(hφ w).deriv]; exact hbound w hw) ha hb
    have heq : (f i b - d * b) - (f i a - d * a) = -(d * (b - a)) := by rw [hab]; ring
    rw [heq, norm_neg, norm_mul] at hmv
    have hba : ‖b - a‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖b - a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have : c * ‖b - a‖ ≤ c / 2 * ‖b - a‖ := hmv
      nlinarith
    exact (sub_eq_zero.mp (norm_eq_zero.mp hba)).symm
  · intro a ha h0
    have := hbound a ha
    rw [h0, zero_sub, norm_neg] at this
    linarith

/-- **H4. Multiple zeros split or persist.** If the entire `g` has an isolated zero at `x₀` with
`g' (x₀) = 0`, then for every `r > 0`, eventually `f i` has a zero `a ∈ ball x₀ r` which is
either multiple (`f i' a = 0`) or accompanied by a second zero `b ≠ a` in `ball x₀ r`. -/
theorem eventually_multiple_or_two_zeros (hconv : TendstoLocallyUniformly f g l)
    (hfd : ∀ i, Differentiable ℂ (f i)) (hg : Differentiable ℂ g) {x₀ : ℂ} (hx₀ : g x₀ = 0)
    (hd : deriv g x₀ = 0) (hiso : ∀ᶠ w in 𝓝[≠] x₀, g w ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ i in l, ∃ a ∈ ball x₀ r, f i a = 0 ∧
      (deriv (f i) a = 0 ∨ ∃ b ∈ ball x₀ r, b ≠ a ∧ f i b = 0) := by
  obtain ⟨ε, hε, hpunct⟩ := exists_ball_punctured_ne_zero hiso
  set ρ := min (ε / 2) (r / 2) with hρ_def
  have hρ : 0 < ρ := lt_min (half_pos hε) (half_pos hr)
  have hρε : ρ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hρr : ρ < r := (min_le_right _ _).trans_lt (half_lt_self hr)
  have hsph : ∀ w ∈ sphere x₀ ρ, g w ≠ 0 := by
    intro w hw
    rw [mem_sphere] at hw
    exact hpunct w (hw ▸ hρε) (fun h => by rw [h, dist_self] at hw; exact hρ.ne' hw.symm)
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_norm_of_isCompact hg.continuous (isCompact_sphere x₀ ρ)
    (NormedSpace.sphere_nonempty.mpr hρ.le) hsph
  -- the slope `h = dslope g x₀` is continuous and vanishes at `x₀`
  have hh : Continuous (dslope g x₀) := by
    have : DifferentiableOn ℂ (dslope g x₀) univ :=
      (Complex.differentiableOn_dslope (Filter.univ_mem)).mpr hg.differentiableOn
    exact differentiableOn_univ.mp this |>.continuous
  have hh0 : dslope g x₀ x₀ = 0 := by rw [dslope_same, hd]
  set η := c / (16 * ρ) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁c⟩ := Metric.continuous_iff.mp hh x₀ η hη
  set δ := min (δ₁ / 3) (ρ / 3) with hδ_def
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδδ₁ : 2 * δ < δ₁ := by
    have := min_le_left (δ₁ / 3) (ρ / 3); linarith
  have hδρ : 2 * δ < ρ := by
    have := min_le_right (δ₁ / 3) (ρ / 3); linarith
  set ε' := min (c / 2) (c * δ / (16 * ρ)) with hε'_def
  have hε' : 0 < ε' := lt_min (half_pos hc) (by positivity)
  filter_upwards [eventually_exists_zero_mem_ball hconv hfd hg.continuous hx₀ hiso hδ,
    eventually_dist_lt_of_isCompact hconv (isCompact_closedBall x₀ ρ) hε'] with i hzero hunif
  obtain ⟨a, ha, hfa⟩ := hzero
  refine ⟨a, ball_subset_ball (by have := min_le_right (δ₁ / 3) (ρ / 3); linarith) ha, hfa, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨hda, hother⟩ := hno
  have haδ : dist a x₀ < δ := mem_ball.mp ha
  -- the slope of `f i` at its zero `a`
  set H := dslope (f i) a with hH_def
  have hHw : ∀ w, w ≠ a → H w = (w - a)⁻¹ * f i w := by
    intro w hw
    rw [hH_def, dslope_of_ne _ hw, slope_def_field, hfa, sub_zero, div_eq_inv_mul]
  have hHne : ∀ w ∈ closedBall x₀ ρ, H w ≠ 0 := by
    intro w hw
    by_cases hwa : w = a
    · rw [hwa, hH_def, dslope_same]; exact hda
    · rw [hHw w hwa]
      exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hwa))
        (hother w (closedBall_subset_ball hρr hw) hwa)
  have hHd : DifferentiableOn ℂ H (closedBall x₀ ρ) :=
    ((Complex.differentiableOn_dslope (Filter.univ_mem)).mpr (hfd i).differentiableOn).mono
      (subset_univ _)
  -- lower bound of `‖H‖` on the sphere
  have hsphH : ∀ w ∈ sphere x₀ ρ, c / (4 * ρ) ≤ ‖H w‖ := by
    intro w hw
    have hwx : dist w x₀ = ρ := mem_sphere.mp hw
    have hwa : w ≠ a := by
      intro h; rw [h] at hwx; linarith
    rw [hHw w hwa, norm_mul, norm_inv]
    have hfw : c / 2 ≤ ‖f i w‖ := by
      have h1 := hcK w hw
      have h2 := hunif w (sphere_subset_closedBall hw)
      rw [dist_eq_norm] at h2
      have h3 : ‖g w‖ ≤ ‖g w - f i w‖ + ‖f i w‖ := by
        simpa using norm_add_le (g w - f i w) (f i w)
      have := min_le_left (c / 2) (c * δ / (16 * ρ))
      linarith
    have hwad : ‖w - a‖ ≤ 2 * ρ := by
      have := dist_triangle w x₀ a
      rw [dist_comm x₀ a] at this
      rw [← dist_eq_norm]; linarith
    have hwapos : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwa)
    calc c / (4 * ρ) = (c / 2) / (2 * ρ) := by field_simp; ring
      _ ≤ ‖f i w‖ / ‖w - a‖ := div_le_div₀ (norm_nonneg _) hfw hwapos hwad
      _ = ‖w - a‖⁻¹ * ‖f i w‖ := by rw [div_eq_inv_mul]
  -- evaluate at `w⋆ = x₀ + 2δ`
  set wstar : ℂ := x₀ + ((2 * δ : ℝ) : ℂ) with hwstar_def
  have hwstarx : dist wstar x₀ = 2 * δ := by
    rw [hwstar_def, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hwstar_mem : wstar ∈ closedBall x₀ ρ := mem_closedBall.mpr (by rw [hwstarx]; linarith)
  have hlow := le_norm_of_zero_free_closedBall hρ (by positivity) hHd hHne hsphH hwstar_mem
  have hwa : wstar ≠ a := by
    intro h; rw [h] at hwstarx; linarith
  have hwad : δ ≤ ‖wstar - a‖ := by
    have := dist_triangle wstar a x₀
    rw [← dist_eq_norm]; linarith
  have hgw : ‖g wstar‖ ≤ η * (2 * δ) := by
    have hslope : dslope g x₀ wstar = (wstar - x₀)⁻¹ * g wstar := by
      rw [dslope_of_ne _ (fun h => by rw [h, dist_self] at hwstarx; linarith), slope_def_field,
        hx₀, sub_zero, div_eq_inv_mul]
    have hne : wstar - x₀ ≠ 0 := sub_ne_zero.mpr
      (fun h => by rw [h, dist_self] at hwstarx; linarith)
    have hgeq : g wstar = (wstar - x₀) * dslope g x₀ wstar := by
      rw [hslope, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    have hsl := hδ₁c wstar (by rw [hwstarx]; exact hδδ₁)
    rw [dist_eq_norm, hh0, sub_zero] at hsl
    rw [hgeq, norm_mul, ← dist_eq_norm, hwstarx]
    nlinarith [norm_nonneg (dslope g x₀ wstar)]
  have hfw : ‖f i wstar‖ ≤ η * (2 * δ) + c * δ / (16 * ρ) := by
    have h2 := hunif wstar hwstar_mem
    rw [dist_eq_norm] at h2
    have h3 : ‖f i wstar‖ ≤ ‖g wstar‖ + ‖g wstar - f i wstar‖ := by
      simpa using norm_sub_le (g wstar) (g wstar - f i wstar)
    have := min_le_right (c / 2) (c * δ / (16 * ρ))
    linarith
  have hHup : ‖H wstar‖ ≤ (η * (2 * δ) + c * δ / (16 * ρ)) / δ := by
    rw [hHw wstar hwa, norm_mul, norm_inv, ← div_eq_inv_mul]
    exact div_le_div₀ (by positivity) hfw hδ hwad
  have hcalc : (η * (2 * δ) + c * δ / (16 * ρ)) / δ = 3 * c / (16 * ρ) := by
    rw [hη_def]; field_simp; ring
  rw [hcalc] at hHup
  have : c / (4 * ρ) ≤ 3 * c / (16 * ρ) := hlow.trans hHup
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
  nlinarith

end BlockBand.Critical.JointRecovery
