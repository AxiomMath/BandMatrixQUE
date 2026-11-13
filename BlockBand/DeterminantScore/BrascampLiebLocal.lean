module

public import BlockBand.DeterminantScore.BrascampLiebPrekopa

/-!
# Brascamp–Lieb on a relatively compact convex piece

No input is used in this module (it only imports the Prékopa step).

* `convexOn_of_line_deriv2`, `hasDerivAt_line`: convexity from second derivatives along lines.
* `convexOn_tilt`: joint convexity of `tilt 𝒰 f Φ (t, x) = 𝒰(x) - t f(x) + t² Φ(x)/2` on
  `(-t₀, t₀) × D` from a pointwise inequality for its second derivative along `(σ, u)`.
* `dualQ`, `dualQ_square`, `dualQ_le_energy`: `q(L,B) = sup_{‖b‖≤R} (2Lb - B(b,b))`; the
  completed square `B(a,a) - 2sLa + s²q ≥ 0` when `B ≥ c‖·‖²`, `‖L‖ ≤ G`, `R = 2G/c`; and
  `q ≤ Σ_j L(e_j)²/w_j` when `B(a,a) ≥ Σ_j w_j a_j²`.
* `exists_coercive`: uniform coercivity of the Hessian on a compact set.
* `exists_contDiff_near`: `C²` Stone–Weierstrass approximation on a compact set.
* `tilt_hessian_nonneg`: the scalar inequality making the tilted Hessian nonnegative.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convexity from nonnegative second derivatives along all lines through an open convex set. -/
theorem convexOn_of_line_deriv2 {S : Set E} (hS : Convex ℝ S) (hSo : IsOpen S) {W : E → ℝ}
    (h : ∀ x ∈ S, ∀ v : E, ∃ g' g'' : ℝ → ℝ, ∀ r : ℝ, x + r • v ∈ S →
      HasDerivAt (fun r => W (x + r • v)) (g' r) r ∧ HasDerivAt g' (g'' r) r ∧ 0 ≤ g'' r) :
    ConvexOn ℝ S W := by
  refine ⟨hS, fun x hx y hy a b ha hb hab => ?_⟩
  set v := y - x
  set L : ℝ → E := fun s => x + s • v with hL
  have hLc : Continuous L := continuous_const.add (continuous_id.smul continuous_const)
  set T := L ⁻¹' S
  have hTo : IsOpen T := hSo.preimage hLc
  have hTc : Convex ℝ T := by
    refine fun p hp q hq c d hc hd hcd => ?_
    have : L (c • p + d • q) = c • L p + d • L q := by
      simp only [hL, smul_eq_mul, add_smul, smul_add, mul_smul]
      have hx' : x = c • x + d • x := by rw [← add_smul, hcd, one_smul]
      calc x + (c • p • v + d • q • v) = (c • x + d • x) + (c • p • v + d • q • v) := by
            rw [← hx']
        _ = _ := by abel
    show L (c • p + d • q) ∈ S
    rw [this]; exact hS hp hq hc hd hcd
  obtain ⟨g', g'', hg⟩ := h x hx v
  have hconv : ConvexOn ℝ T (fun r => W (L r)) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg hTc (f' := g') (f'' := g'')
      (fun r hr => (hg r hr).1.continuousAt.continuousWithinAt) ?_ ?_ ?_ <;>
      rw [hTo.interior_eq]
    · exact fun r hr => (hg r hr).1.hasDerivWithinAt
    · exact fun r hr => (hg r hr).2.1.hasDerivWithinAt
    · exact fun r hr => (hg r hr).2.2
  have h0 : (0 : ℝ) ∈ T := by show L 0 ∈ S; simpa [hL] using hx
  have h1 : (1 : ℝ) ∈ T := by show L 1 ∈ S; simpa [hL, v] using hy
  have key := hconv.2 h0 h1 ha hb hab
  have e : L (a • (0 : ℝ) + b • 1) = a • x + b • y := by
    simp only [hL, v, smul_eq_mul, mul_zero, zero_add, mul_one]
    rw [show a = 1 - b by linarith, sub_smul, one_smul, smul_sub]; abel
  simp only at key
  rw [e] at key
  simpa [hL, v] using key

/-- First and second derivatives along a line of a `C²` function. -/
theorem hasDerivAt_line {O : Set E} (hO : IsOpen O) {h : E → ℝ} (hh : ContDiffOn ℝ 2 h O)
    (x v : E) {r : ℝ} (hr : x + r • v ∈ O) :
    HasDerivAt (fun r => h (x + r • v)) (fderiv ℝ h (x + r • v) v) r ∧
      HasDerivAt (fun r => fderiv ℝ h (x + r • v) v)
        (fderiv ℝ (fderiv ℝ h) (x + r • v) v v) r := by
  have hLd : HasDerivAt (fun s : ℝ => x + s • v) v r := by
    have := ((hasDerivAt_id r).smul_const v).const_add x
    rwa [one_smul] at this
  have hat : ContDiffAt ℝ 2 h (x + r • v) := hh.contDiffAt (hO.mem_nhds hr)
  refine ⟨?_, ?_⟩
  · exact ((hat.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt r hLd
  · have hd := (((hat.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt)
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt r
      (hd.comp_hasDerivAt r hLd)

end Line

section Tilt

variable {m : ℕ}

/-- The tilted potential `W(t, x) = 𝒰(x) - t f(x) + t² Φ(x)/2`. -/
def tilt (𝒰 f Φ : (Fin m → ℝ) → ℝ) (p : ℝ × (Fin m → ℝ)) : ℝ :=
  𝒰 p.2 - p.1 * f p.2 + p.1 ^ 2 / 2 * Φ p.2

/-- Joint convexity of the tilted potential from a pointwise second-derivative inequality. -/
theorem convexOn_tilt {O D : Set (Fin m → ℝ)} (hO : IsOpen O) (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hDO : D ⊆ O) {𝒰 f Φ : (Fin m → ℝ) → ℝ} (h𝒰 : ContDiffOn ℝ 2 𝒰 O)
    (hf : ContDiffOn ℝ 2 f O) (hΦ : ContDiffOn ℝ 2 Φ O) {t₀ : ℝ}
    (hpos : ∀ x ∈ D, ∀ T : ℝ, |T| < t₀ → ∀ (σ : ℝ) (u : Fin m → ℝ),
      0 ≤ fderiv ℝ (fderiv ℝ 𝒰) x u u - 2 * σ * fderiv ℝ f x u + σ ^ 2 * Φ x +
        T * (-fderiv ℝ (fderiv ℝ f) x u u + 2 * σ * fderiv ℝ Φ x u) +
        T ^ 2 / 2 * fderiv ℝ (fderiv ℝ Φ) x u u) :
    ConvexOn ℝ (Set.Ioo (-t₀) t₀ ×ˢ D) (tilt 𝒰 f Φ) := by
  refine convexOn_of_line_deriv2 (convex_Ioo _ _ |>.prod hDc) (isOpen_Ioo.prod hDo) ?_
  rintro p - ⟨σ, u⟩
  set T : ℝ → ℝ := fun r => p.1 + r * σ
  set y : ℝ → (Fin m → ℝ) := fun r => p.2 + r • u
  refine ⟨fun r => fderiv ℝ 𝒰 (y r) u - (σ * f (y r) + T r * fderiv ℝ f (y r) u) +
      (σ * T r * Φ (y r) + T r ^ 2 / 2 * fderiv ℝ Φ (y r) u),
    fun r => fderiv ℝ (fderiv ℝ 𝒰) (y r) u u -
      (2 * σ * fderiv ℝ f (y r) u + T r * fderiv ℝ (fderiv ℝ f) (y r) u u) +
      (σ ^ 2 * Φ (y r) + 2 * σ * T r * fderiv ℝ Φ (y r) u +
        T r ^ 2 / 2 * fderiv ℝ (fderiv ℝ Φ) (y r) u u), fun r hr => ?_⟩
  have hr1 : T r ∈ Set.Ioo (-t₀) t₀ := by
    have := hr.1; simpa [T, smul_eq_mul] using this
  have hr2 : y r ∈ D := by
    have := hr.2; simpa [y] using this
  have hyO : p.2 + r • u ∈ O := hDO hr2
  obtain ⟨hU1, hU2⟩ := hasDerivAt_line hO h𝒰 p.2 u hyO
  obtain ⟨hf1, hf2⟩ := hasDerivAt_line hO hf p.2 u hyO
  obtain ⟨hΦ1, hΦ2⟩ := hasDerivAt_line hO hΦ p.2 u hyO
  have hT : ∀ r, HasDerivAt T σ r := fun r => by
    have := ((hasDerivAt_id r).mul_const σ).const_add p.1
    rw [one_mul] at this
    exact this
  have hfun : (fun r => tilt 𝒰 f Φ (p + r • (σ, u))) =
      fun r => 𝒰 (y r) - T r * f (y r) + T r ^ 2 / 2 * Φ (y r) := by
    funext r
    simp [tilt, T, y, smul_eq_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    have := (hU1.sub ((hT r).mul hf1)).add ((((hT r).pow 2).div_const 2).mul hΦ1)
    convert this using 1
    simp only [y, T, Pi.pow_apply]
    push_cast
    ring
  · have hT2 := ((hT r).pow 2).div_const 2
    have := (hU2.sub (((hasDerivAt_const r σ).mul hf1).add ((hT r).mul hf2))).add
      ((((hasDerivAt_const r σ).mul (hT r)).mul hΦ1).add (hT2.mul hΦ2))
    convert this using 1
    simp only [y, T, Pi.pow_apply, Pi.mul_apply]
    push_cast
    ring
  · have h := hpos (y r) hr2 (T r) (abs_lt.2 ⟨hr1.1, hr1.2⟩) σ u
    linarith

end Tilt

section Dual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `q(L, B) = sup_{‖b‖ ≤ R} (2 L b - B(b, b))`; for `B` coercive and `R` large this is
`⟨B⁻¹ L, L⟩`. -/
def dualQ (R : ℝ) (L : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  sSup ((fun b => 2 * L b - B b b) '' Metric.closedBall 0 R)

theorem continuous_dualQ (R : ℝ) :
    Continuous fun p : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) => dualQ R p.1 p.2 := by
  have hc : Continuous fun z : ((E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ)) × E =>
      2 * z.1.1 z.2 - z.1.2 z.2 z.2 :=
    (continuous_const.mul (continuous_fst.fst.clm_apply continuous_snd)).sub
      ((continuous_fst.snd.clm_apply continuous_snd).clm_apply continuous_snd)
  exact (isCompact_closedBall (0 : E) R).continuous_sSup (f := fun (p : (E →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ)) (b : E) => 2 * p.1 b - p.2 b b)
    hc

theorem bddAbove_dualQ (R : ℝ) (L : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    BddAbove ((fun b => 2 * L b - B b b) '' Metric.closedBall 0 R) :=
  (isCompact_closedBall (0 : E) R).bddAbove_image
    ((continuous_const.mul L.continuous).sub (B.continuous.clm_apply continuous_id)).continuousOn

theorem le_dualQ {R : ℝ} (L : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) {b : E} (hb : ‖b‖ ≤ R) :
    2 * L b - B b b ≤ dualQ R L B :=
  le_csSup (bddAbove_dualQ R L B) ⟨b, by simpa using hb, rfl⟩

theorem dualQ_nonneg {R : ℝ} (hR : 0 ≤ R) (L : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    0 ≤ dualQ R L B := by
  have := le_dualQ L B (b := 0) (by simpa using hR)
  simpa using this

omit [FiniteDimensional ℝ E] in
theorem dualQ_le {R : ℝ} (hR : 0 ≤ R) (L : E →L[ℝ] ℝ) (B : E →L[ℝ] E →L[ℝ] ℝ) {e : ℝ}
    (he : ∀ b, 2 * L b - B b b ≤ e) : dualQ R L B ≤ e :=
  csSup_le ⟨_, ⟨0, by simpa using hR, rfl⟩⟩ (by rintro _ ⟨b, -, rfl⟩; exact he b)

/-- The completed square: `B(a,a) - 2 s L a + s² q(L,B) ≥ 0` when `B ≥ c‖·‖²`, `‖L‖ ≤ G` and
`R = 2G/c`. -/
theorem dualQ_square {c G : ℝ} (hc : 0 < c) (hG : 0 ≤ G) (L : E →L[ℝ] ℝ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ a, c * ‖a‖ ^ 2 ≤ B a a) (hL : ‖L‖ ≤ G) (a : E) (s : ℝ) :
    0 ≤ B a a - 2 * s * L a + s ^ 2 * dualQ (2 * G / c) L B := by
  have hR : 0 ≤ 2 * G / c := by positivity
  have hq0 := dualQ_nonneg hR L B
  have hLa : |L a| ≤ G * ‖a‖ := by
    rw [← Real.norm_eq_abs]
    exact (L.le_opNorm a).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  by_cases hs : s = 0
  · subst hs
    have := hB a
    have : 0 ≤ c * ‖a‖ ^ 2 := by positivity
    simp only [mul_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    linarith
  by_cases hb : ‖s⁻¹ • a‖ ≤ 2 * G / c
  · have h := le_dualQ L B hb
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    have hs2 : 0 < s ^ 2 := by positivity
    have e : s ^ 2 * (2 * (s⁻¹ * L a) - s⁻¹ * (s⁻¹ * B a a)) = 2 * s * L a - B a a := by
      field_simp
    nlinarith [mul_le_mul_of_nonneg_left h hs2.le]
  · push Not at hb
    rw [norm_smul, norm_inv, Real.norm_eq_abs, div_lt_iff₀ hc] at hb
    have hsa : 2 * G * |s| ≤ c * ‖a‖ := by
      have habs : 0 < |s| := abs_pos.2 hs
      have := mul_lt_mul_of_pos_left hb habs
      have e : |s| * (|s|⁻¹ * ‖a‖ * c) = c * ‖a‖ := by field_simp
      linarith
    have h1 : 2 * s * L a ≤ 2 * |s| * (G * ‖a‖) := by
      have := le_abs_self (2 * s * L a)
      rw [abs_mul, abs_mul, abs_two] at this
      nlinarith [abs_nonneg s, hLa]
    have h2 := hB a
    have h3 : 0 ≤ s ^ 2 * dualQ (2 * G / c) L B := by positivity
    nlinarith [norm_nonneg a]

end Dual

section Compact

variable {m : ℕ}

/-- Continuity of the Hessian of a `C²` function on an open set. -/
theorem continuousOn_fderiv_fderiv {O : Set (Fin m → ℝ)} (hO : IsOpen O)
    {h : (Fin m → ℝ) → ℝ} (hh : ContDiffOn ℝ 2 h O) :
    ContinuousOn (fun x => fderiv ℝ (fderiv ℝ h) x) O :=
  (hh.fderiv_of_isOpen hO (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen hO le_rfl

/-- Positivity of the diagonal form. -/
theorem sum_weight_pos {w : Fin m → ℝ} (hw : ∀ j, 0 < w j) {a : Fin m → ℝ} (ha : a ≠ 0) :
    0 < ∑ j, w j * a j ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 ha
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))
    ⟨j, Finset.mem_univ _, mul_pos (hw j) (by simpa using pow_pos (abs_pos.2 hj) 2)⟩

/-- **Uniform coercivity on a compact set.** A pointwise positive diagonal lower bound of a
continuous Hessian gives a uniform bound `c‖a‖² ≤ ∇²𝒰(x)[a,a]` on a compact `K ⊆ O`. -/
theorem exists_coercive {O K : Set (Fin m → ℝ)} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) {𝒰 : (Fin m → ℝ) → ℝ} (h𝒰 : ContDiffOn ℝ 2 𝒰 O)
    {w : (Fin m → ℝ) → Fin m → ℝ} (hw : ∀ x ∈ O, ∀ j, 0 < w x j)
    (hH : ∀ x ∈ O, ∀ a, ∑ j, w x j * a j ^ 2 ≤ fderiv ℝ (fderiv ℝ 𝒰) x a a) :
    ∃ c > 0, ∀ x ∈ K, ∀ a, c * ‖a‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ 𝒰) x a a := by
  set S := K ×ˢ Metric.sphere (0 : Fin m → ℝ) 1
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hψ : ContinuousOn (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      fderiv ℝ (fderiv ℝ 𝒰) p.1 p.2 p.2) S := by
    have h1 : ContinuousOn (fun p : (Fin m → ℝ) × (Fin m → ℝ) => fderiv ℝ (fderiv ℝ 𝒰) p.1) S :=
      ((continuousOn_fderiv_fderiv hO h𝒰).mono hKO).comp continuous_fst.continuousOn
        (fun p hp => hp.1)
    exact (h1.clm_apply continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  have hscale : ∀ x a, a ≠ 0 → fderiv ℝ (fderiv ℝ 𝒰) x a a =
      ‖a‖ ^ 2 * fderiv ℝ (fderiv ℝ 𝒰) x (‖a‖⁻¹ • a) (‖a‖⁻¹ • a) := by
    intro x a ha
    have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  have hsph : ∀ a : Fin m → ℝ, a ≠ 0 → ‖a‖⁻¹ • a ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
    intro a ha
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 ha)]
  by_cases hne : S.Nonempty
  · obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hne hψ
    have hp₀O : p₀.1 ∈ O := hKO hp₀.1
    have ha₀ : p₀.2 ≠ 0 := by
      intro h0
      have := hp₀.2
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at this
      exact zero_ne_one this
    refine ⟨_, (sum_weight_pos (hw _ hp₀O) ha₀).trans_le (hH _ hp₀O _), fun x hx a => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp
    · rw [hscale x a ha, mul_comm]
      exact mul_le_mul_of_nonneg_left (hmin (show (x, ‖a‖⁻¹ • a) ∈ S from ⟨hx, hsph a ha⟩))
        (sq_nonneg _)
  · refine ⟨1, one_pos, fun x hx a => ?_⟩
    by_cases ha : a = 0
    · subst ha; simp
    · exact absurd ⟨(x, ‖a‖⁻¹ • a), hx, hsph a ha⟩ hne

/-- **Smooth uniform approximation on a compact set** (Stone–Weierstrass for the algebra of
restrictions of `C²` functions). -/
theorem exists_contDiff_near {K : Set (Fin m → ℝ)} (hK : IsCompact K) {g : (Fin m → ℝ) → ℝ}
    (hg : ContinuousOn g K) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : (Fin m → ℝ) → ℝ, ContDiff ℝ 2 F ∧ ∀ x ∈ K, |F x - g x| < ε := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let A : Subalgebra ℝ C(K, ℝ) :=
    { carrier := {h | ∃ F : (Fin m → ℝ) → ℝ, ContDiff ℝ 2 F ∧ ∀ x : K, h x = F x}
      mul_mem' := by
        rintro _ _ ⟨F, hF, hFe⟩ ⟨G, hG, hGe⟩
        exact ⟨fun x => F x * G x, hF.mul hG, fun x => by simp [hFe, hGe]⟩
      add_mem' := by
        rintro _ _ ⟨F, hF, hFe⟩ ⟨G, hG, hGe⟩
        exact ⟨fun x => F x + G x, hF.add hG, fun x => by simp [hFe, hGe]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => rfl⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : (x : Fin m → ℝ) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨j, hj⟩ := Function.ne_iff.1 this
    refine ⟨_, ⟨⟨fun z : K => (z : Fin m → ℝ) j, (continuous_apply j).comp continuous_subtype_val⟩,
      ⟨fun z => z j, contDiff_apply ℝ ℝ j, fun z => rfl⟩, rfl⟩, hj⟩
  obtain ⟨⟨h, F, hF, hFe⟩, hh⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
    A hsep (fun x : K => g x) (hg.domRestrict) ε hε
  refine ⟨F, hF, fun x hx => ?_⟩
  have := hh ⟨x, hx⟩
  simp only [Real.norm_eq_abs] at this
  rwa [show (h ⟨x, hx⟩ : ℝ) = F x from hFe ⟨x, hx⟩] at this

end Compact

section LocalBL

variable {m : ℕ}

/-- A linear functional on `ℝ^m` in coordinates. -/
theorem clm_apply_eq_sum (L : (Fin m → ℝ) →L[ℝ] ℝ) (b : Fin m → ℝ) :
    L b = ∑ j, b j * L (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single b]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (Pi.single j (b j) : Fin m → ℝ) = b j • Pi.single j 1 by
    ext i; by_cases h : i = j <;> simp [h], map_smul, smul_eq_mul]

/-- The dual form is dominated by the diagonal energy `Σ_j L(e_j)²/w_j`. -/
theorem dualQ_le_energy {R : ℝ} (hR : 0 ≤ R) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) {w : Fin m → ℝ} (hw : ∀ j, 0 < w j)
    (hB : ∀ a, ∑ j, w j * a j ^ 2 ≤ B a a) :
    dualQ R L B ≤ ∑ j, (L (Pi.single j 1)) ^ 2 / w j := by
  refine dualQ_le hR L B fun b => ?_
  have key : ∀ j, 2 * (b j * L (Pi.single j 1)) - w j * b j ^ 2 ≤
      L (Pi.single j 1) ^ 2 / w j := by
    intro j
    rw [le_div_iff₀ (hw j)]
    nlinarith [sq_nonneg (w j * b j - L (Pi.single j 1))]
  calc 2 * L b - B b b ≤ 2 * L b - ∑ j, w j * b j ^ 2 := by linarith [hB b]
    _ = ∑ j, (2 * (b j * L (Pi.single j 1)) - w j * b j ^ 2) := by
        rw [clm_apply_eq_sum L b, Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum fun j _ => key j

/-- `q ≤ G²/c` under coercivity. -/
theorem dualQ_le_sq_div {R c G : ℝ} (hR : 0 ≤ R) (hc : 0 < c) (L : (Fin m → ℝ) →L[ℝ] ℝ)
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) (hB : ∀ a, c * ‖a‖ ^ 2 ≤ B a a)
    (hL : ‖L‖ ≤ G) : dualQ R L B ≤ G ^ 2 / c := by
  refine dualQ_le hR L B fun b => ?_
  have h1 : L b ≤ G * ‖b‖ := by
    have := (le_abs_self (L b)).trans ((L.le_opNorm b).trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _)))
    simpa [Real.norm_eq_abs] using this
  rw [le_div_iff₀ hc]
  nlinarith [hB b, sq_nonneg (c * ‖b‖ - G)]

/-- Elementary inequality behind the uniform positivity of the tilted Hessian. -/
theorem tilt_quadratic_lower {h l s φ q lam c nu δ G : ℝ} (hlam : 0 < lam) (hlam2 : lam ≤ 1 / 2)
    (hδ : 0 < δ) (hh : c * nu ^ 2 ≤ h)
    (hsq : 0 ≤ h - 2 * s * l + s ^ 2 * q) (hφ : q + δ ≤ φ) (hqG : q ≤ G ^ 2 / c)
    (hlamG : lam * (G ^ 2 / c) ≤ δ / 4) :
    δ / 8 * ((1 - lam) * s) ^ 2 + lam * c * nu ^ 2 ≤
      h - 2 * ((1 - lam) * s) * l + ((1 - lam) * s) ^ 2 * φ := by
  have hb : 0 < 1 - lam := by linarith
  have h1 : 0 ≤ (1 - lam) * (h - 2 * s * l + s ^ 2 * q) := mul_nonneg hb.le hsq
  have h2 : lam * (c * nu ^ 2) ≤ lam * h := mul_le_mul_of_nonneg_left hh hlam.le
  have hlq : lam * q ≤ δ / 4 := (mul_le_mul_of_nonneg_left hqG hlam.le).trans hlamG
  have h3 : 0 ≤ (1 - lam) * φ - q - δ / 8 * (1 - lam) := by nlinarith
  have h4 : 0 ≤ (1 - lam) * s ^ 2 * ((1 - lam) * φ - q - δ / 8 * (1 - lam)) :=
    mul_nonneg (mul_nonneg hb.le (sq_nonneg s)) h3
  nlinarith

/-- Uniform positivity of the tilted Hessian, in scalar form. -/
theorem tilt_hessian_nonneg {h l φ q lam c nu δ G σ T M a b d : ℝ} (hlam : 0 < lam)
    (hlam2 : lam ≤ 1 / 2) (hδ : 0 < δ) (hh : c * nu ^ 2 ≤ h)
    (hsq : ∀ s : ℝ, 0 ≤ h - 2 * s * l + s ^ 2 * q) (hφ : q + δ ≤ φ) (hqG : q ≤ G ^ 2 / c)
    (hlamG : lam * (G ^ 2 / c) ≤ δ / 4) (hM : 0 < M) (ha : |a| ≤ M * nu ^ 2)
    (hb : |b| ≤ M * nu) (hd : |d| ≤ M * nu ^ 2) (hT1 : |T| ≤ 1)
    (hTκ : |T| * (4 * M) ≤ min (δ / 8) (lam * c)) :
    0 ≤ h - 2 * σ * l + σ ^ 2 * φ + T * (-a + 2 * σ * b) + T ^ 2 / 2 * d := by
  have hb1 : 0 < 1 - lam := by linarith
  set s := σ / (1 - lam) with hsdef
  have hσ : σ = (1 - lam) * s := by rw [hsdef]; field_simp
  have hlow := tilt_quadratic_lower (h := h) (l := l) (s := s) (φ := φ) (q := q) (nu := nu)
    hlam hlam2 hδ hh (hsq s) hφ hqG hlamG
  rw [← hσ] at hlow
  have hσu : 2 * |σ| * nu ≤ σ ^ 2 + nu ^ 2 := by
    nlinarith [sq_nonneg (|σ| - nu), sq_abs σ]
  have hTa : 0 ≤ |T| := abs_nonneg T
  have a1 : |T * (-a + 2 * σ * b)| ≤ |T| * (M * nu ^ 2 + M * (σ ^ 2 + nu ^ 2)) := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ hTa
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg, abs_mul, abs_mul, abs_two]
    have i1 : |σ| * |b| ≤ |σ| * (M * nu) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    have i2 : M * (2 * |σ| * nu) ≤ M * (σ ^ 2 + nu ^ 2) := mul_le_mul_of_nonneg_left hσu hM.le
    have i3 : |σ| * (M * nu) = M * (|σ| * nu) := by ring
    linarith
  have a2 : |T ^ 2 / 2 * d| ≤ |T| * (M * nu ^ 2) := by
    rw [abs_mul, abs_div, abs_two, abs_pow]
    have i1 : |T| ^ 2 / 2 ≤ |T| := by nlinarith
    exact mul_le_mul i1 hd (abs_nonneg _) hTa
  have i4 : 0 ≤ |T| * M * (3 * σ ^ 2 + nu ^ 2) := by positivity
  have i5 : |T| * (4 * M) * (σ ^ 2 + nu ^ 2) =
      |T| * (M * nu ^ 2 + M * (σ ^ 2 + nu ^ 2)) + |T| * (M * nu ^ 2) +
        |T| * M * (3 * σ ^ 2 + nu ^ 2) := by ring
  have hE : |T * (-a + 2 * σ * b) + T ^ 2 / 2 * d| ≤ |T| * (4 * M) * (σ ^ 2 + nu ^ 2) := by
    have := abs_add_le (T * (-a + 2 * σ * b)) (T ^ 2 / 2 * d)
    linarith
  have hκ := hE.trans (mul_le_mul_of_nonneg_right hTκ (by positivity))
  have hκ1 : min (δ / 8) (lam * c) * σ ^ 2 ≤ δ / 8 * σ ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
  have hκ2 : min (δ / 8) (lam * c) * nu ^ 2 ≤ lam * c * nu ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
  have := (abs_le.1 hκ).1
  linarith

end LocalBL

end BlockBand.DeterminantScore.SpectralConvexity.BrascampLieb
