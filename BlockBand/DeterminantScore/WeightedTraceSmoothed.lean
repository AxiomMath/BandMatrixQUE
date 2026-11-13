module

public import BlockBand.DeterminantScore.WeightedTraceFrame

/-!
# The smoothed trace and the deterministic good-event bound

Deterministic estimates for the weighted trace on the good event, at a fixed matrix.

* `trace_smoothed_eq` (from the identity `K₀R_η = I + iηR_η - G_dR_η`):
  for Hermitian `K₀`, `A = K₀ + G` Hermitian and real `g₀`,
  `Tr (K₀ - g₀) Re R_η = d - η Im Tr R_η - g₀ Re Tr R_η - Re Tr GR_η`.
* `smoothed_scalar_bound`: if `Tr R_η = d a + O(e₁)`, `Tr GR_η = -sd a² + O(e₂)`, `|a - σ| ≤ r ≤ 1`,
  `|σ| = 1` and `|g₀ - 2s Re σ| ≤ e₃`, then
  `|Tr (K₀ - g₀) Re R_η - d(1 - s)| ≤ ηe₁ + |g₀|e₁ + e₂ + d(2η + 2e₃ + 4r)`
  (`σ = m_sc(E)`, `Re σ = -E/2`, `|m_sc| = 1`).
* `good_bound`: on the event where the hypotheses of score unsmoothing hold
  (`ScoreUnsmoothing.score_unsmoothing_of_unit_eigenvectors_nearSum`), together with the
  smoothed-trace inputs, `|d(1 - s) - Re Tr (K₀ + sE)R| ≤ C a₀ √(dη) ‖R‖_HS + C dη + C dη²
  + ηe₁ + C₀e₁ + e₂ + d(2η + 2e₃ + 4r) + e₃ √d ‖R‖_HS` (the three terms:
  unsmoothing, smoothed trace, replacing `g(0)` by `-sE`).
* `matchedA_norm`: `m_sc(E) = conj(matchedA E)` has modulus one and real part `-E/2` on
  `|E| ≤ 2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section
noncomputable section

namespace BlockBand.DeterminantScore.WeightedTrace

open Matrix
open BlockBand.Internal.Contracts.Layers
open BlockBand.DeterminantScore.ScoreUnsmoothing
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-!
## The semicircle point
-/

theorem matchedA_norm {E : ℝ} (hE : |E| ≤ 2) :
    (conj (matchedA E)).re ^ 2 + (conj (matchedA E)).im ^ 2 = 1 ∧
      (conj (matchedA E)).re = -E / 2 := by
  have h4 : 0 ≤ 4 - E ^ 2 := by
    have := sq_abs E; nlinarith [abs_nonneg E]
  have hs := Real.sq_sqrt h4
  refine ⟨?_, ?_⟩
  · simp only [Complex.conj_re, Complex.conj_im, matchedA]
    nlinarith
  · simp [matchedA]

/-!
## The smoothed trace identity
-/

section Smoothed

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem resolvent_mul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {η : ℝ} (hη : 0 < η) :
    (A - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ)) *
      (A - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹ = 1 := by
  have hAU := eq_eigenvectorUnitary_decomp hA
  rw [resolvent_eq_specFun _ _ hAU hη, sub_smul_one_eq_specFun _ _ hAU, specFun_mul]
  have e : (fun x : ℝ => ((x : ℂ) - (η : ℂ) * Complex.I) * ((x : ℂ) - (η : ℂ) * Complex.I)⁻¹) =
      fun _ => (1 : ℂ) := by
    funext x; exact mul_inv_cancel₀ (ofReal_sub_mul_I_ne_zero hη x)
  rw [e, specFun_const, one_smul]

/-- **`Tr (K₀ - g₀) Re R_η = d - η Im Tr R_η - g₀ Re Tr R_η - Re Tr GR_η`** (from
`K₀R_η = I + iηR_η - GR_η`). -/
theorem trace_smoothed_eq {A K₀ G : Matrix ι ι ℂ} (hA : A.IsHermitian) (hK : K₀.IsHermitian)
    (hAK : A = K₀ + G) {η : ℝ} (hη : 0 < η) (g₀ : ℝ) :
    let Rη := (A - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹
    ((K₀ - (g₀ : ℂ) • 1) * ((1 / 2 : ℂ) • (Rη + Rηᴴ))).trace =
      (((Fintype.card ι : ℝ) - η * Rη.trace.im - g₀ * Rη.trace.re - (G * Rη).trace.re : ℝ) : ℂ) := by
  intro Rη
  have hmul := resolvent_mul hA hη
  set w := ((K₀ - (g₀ : ℂ) • 1) * Rη).trace with hw
  have hKg : (K₀ - (g₀ : ℂ) • 1)ᴴ = K₀ - (g₀ : ℂ) • 1 := by
    rw [conjTranspose_sub, hK.eq, conjTranspose_smul, conjTranspose_one]; simp
  have h1 : ((K₀ - (g₀ : ℂ) • 1) * Rηᴴ).trace = conj w := by
    have : (K₀ - (g₀ : ℂ) • 1) * Rηᴴ = (Rη * (K₀ - (g₀ : ℂ) • 1))ᴴ := by
      rw [conjTranspose_mul, hKg]
    rw [this, trace_conjTranspose, trace_mul_comm, hw]; rfl
  have hK0 : K₀ - (g₀ : ℂ) • 1 = (A - ((η : ℂ) * Complex.I) • 1) - G +
      ((η : ℂ) * Complex.I - g₀) • (1 : Matrix ι ι ℂ) := by
    rw [hAK, sub_smul]; abel
  have hw' : w = (Fintype.card ι : ℂ) - (G * Rη).trace + ((η : ℂ) * Complex.I - g₀) * Rη.trace := by
    rw [hw, hK0, Matrix.add_mul, Matrix.sub_mul, hmul, Matrix.smul_mul, Matrix.one_mul, trace_add,
      trace_sub, trace_one, trace_smul, smul_eq_mul]
  rw [Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, ← hw, h1, smul_eq_mul]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.add_im, Complex.conj_im,
      Complex.ofReal_re, hw']
    simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp only [Complex.mul_im, Complex.add_re, Complex.conj_re, Complex.add_im, Complex.conj_im,
      Complex.ofReal_im]
    norm_num

end Smoothed

/-!
## The scalar bound
-/

theorem smoothed_scalar_bound {d η g₀ s e₁ e₂ e₃ r : ℝ} {τ γ a σ : ℂ} (hd : 0 ≤ d)
    (hη : 0 < η) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hτ : ‖τ - (d : ℂ) * a‖ ≤ e₁)
    (hγ : ‖γ + (s : ℂ) * d * a ^ 2‖ ≤ e₂) (ha : ‖a - σ‖ ≤ r) (hr : r ≤ 1)
    (hσ : σ.re ^ 2 + σ.im ^ 2 = 1) (hg : |g₀ - 2 * s * σ.re| ≤ e₃) :
    |d - η * τ.im - g₀ * τ.re - γ.re - d * (1 - s)| ≤
      η * e₁ + |g₀| * e₁ + e₂ + d * (2 * η + 2 * e₃ + 4 * r) := by
  set u := τ - (d : ℂ) * a with hu
  set w := γ + (s : ℂ) * d * a ^ 2 with hwd
  have hur : |u.re| ≤ e₁ := (Complex.abs_re_le_norm u).trans hτ
  have hui : |u.im| ≤ e₁ := (Complex.abs_im_le_norm u).trans hτ
  have hwr : |w.re| ≤ e₂ := (Complex.abs_re_le_norm w).trans hγ
  have hτr : τ.re = d * a.re + u.re := by simp [hu]
  have hτi : τ.im = d * a.im + u.im := by simp [hu]
  have hγr : γ.re = w.re - s * d * (a.re ^ 2 - a.im ^ 2) := by
    simp [hwd, pow_two, Complex.mul_re, Complex.mul_im]
  have har : |a.re - σ.re| ≤ r := by
    have := Complex.abs_re_le_norm (a - σ); simp only [Complex.sub_re] at this; linarith
  have hai : |a.im - σ.im| ≤ r := by
    have := Complex.abs_im_le_norm (a - σ); simp only [Complex.sub_im] at this; linarith
  have hσi : |σ.im| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg σ.re, sq_nonneg (σ.im + 1),
      sq_nonneg (σ.im - 1)]
  have hσr : |σ.re| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg σ.im, sq_nonneg (σ.re + 1),
      sq_nonneg (σ.re - 1)]
  have hr0 : 0 ≤ r := (abs_nonneg _).trans har
  have hare : |a.re| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub a.re σ.re; linarith
  have haim : |a.im| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub a.im σ.im; linarith
  set e := g₀ - 2 * s * σ.re with he
  -- the main bracket
  have hkey : -η * a.im - g₀ * a.re + s * (a.re ^ 2 - a.im ^ 2) + s =
      -η * a.im - e * a.re + s * ((a.re - σ.re) ^ 2 + (σ.im - a.im) * (σ.im + a.im)) := by
    rw [he]; linear_combination (-s) * hσ
  have hb1 : |(a.re - σ.re) ^ 2| ≤ r := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, pow_two]
    calc |a.re - σ.re| * |a.re - σ.re| ≤ r * 1 :=
          mul_le_mul har (har.trans hr) (abs_nonneg _) hr0
      _ = r := mul_one r
  have hb2 : |(σ.im - a.im) * (σ.im + a.im)| ≤ 3 * r := by
    rw [abs_mul]
    have h1 : |σ.im - a.im| ≤ r := by rw [abs_sub_comm]; exact hai
    have h2 : |σ.im + a.im| ≤ 3 := (abs_add_le _ _).trans (by linarith)
    calc |σ.im - a.im| * |σ.im + a.im| ≤ r * 3 := mul_le_mul h1 h2 (abs_nonneg _) hr0
      _ = 3 * r := mul_comm _ _
  have he₃ : 0 ≤ e₃ := (abs_nonneg _).trans hg
  have hbracket : |-η * a.im - e * a.re + s * ((a.re - σ.re) ^ 2 + (σ.im - a.im) * (σ.im + a.im))|
      ≤ 2 * η + 2 * e₃ + 4 * r := by
    have t1 : |-η * a.im| ≤ 2 * η := by
      rw [abs_mul, abs_neg, abs_of_pos hη]
      have := mul_le_mul_of_nonneg_left haim hη.le
      linarith
    have t2 : |e * a.re| ≤ 2 * e₃ := by
      rw [abs_mul]
      have := mul_le_mul hg hare (abs_nonneg _) he₃
      linarith
    have t3 : |s * ((a.re - σ.re) ^ 2 + (σ.im - a.im) * (σ.im + a.im))| ≤ 4 * r := by
      rw [abs_mul, abs_of_nonneg hs]
      have h := (abs_add_le ((a.re - σ.re) ^ 2) ((σ.im - a.im) * (σ.im + a.im))).trans
        (add_le_add hb1 hb2)
      have := mul_le_mul hs1 h (abs_nonneg _) zero_le_one
      linarith
    calc _ ≤ |-η * a.im - e * a.re| + |s * ((a.re - σ.re) ^ 2 + (σ.im - a.im) * (σ.im + a.im))| :=
          abs_add_le _ _
      _ ≤ (|-η * a.im| + |e * a.re|) + 4 * r := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  have hexpr : d - η * τ.im - g₀ * τ.re - γ.re - d * (1 - s) =
      (-η * u.im - g₀ * u.re - w.re) +
        d * (-η * a.im - e * a.re + s * ((a.re - σ.re) ^ 2 + (σ.im - a.im) * (σ.im + a.im))) := by
    rw [← hkey, hτr, hτi, hγr]; ring
  rw [hexpr]
  have hp1 : |-η * u.im - g₀ * u.re - w.re| ≤ η * e₁ + |g₀| * e₁ + e₂ := by
    have a1 : |-η * u.im| ≤ η * e₁ := by
      rw [abs_mul, abs_neg, abs_of_pos hη]; exact mul_le_mul_of_nonneg_left hui hη.le
    have a2 : |g₀ * u.re| ≤ |g₀| * e₁ := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hur (abs_nonneg _)
    calc _ ≤ |-η * u.im - g₀ * u.re| + |w.re| := abs_sub _ _
      _ ≤ (|-η * u.im| + |g₀ * u.re|) + |w.re| := by gcongr; exact abs_sub _ _
      _ ≤ _ := by linarith
  calc _ ≤ |-η * u.im - g₀ * u.re - w.re| +
        |d * (-η * a.im - e * a.re + s * ((a.re - σ.re) ^ 2 + (σ.im - a.im) * (σ.im + a.im)))| :=
        abs_add_le _ _
    _ ≤ (η * e₁ + |g₀| * e₁ + e₂) + d * (2 * η + 2 * e₃ + 4 * r) := by
        gcongr
        rw [abs_mul, abs_of_nonneg hd]
        exact mul_le_mul_of_nonneg_left hbracket hd
    _ = _ := by ring

/-!
## The deterministic good-event bound
-/

/-- **Deterministic good-event bound**: the unsmoothing lemma, the smoothed
trace and the centre replacement. `d = |ι|`. -/
theorem good_bound (C₀ δ : ℝ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A K₀ G R : Matrix ι ι ℂ)
      (hA : A.IsHermitian) (g : ℝ → ℝ) (a₀ η s E e₁ e₂ e₃ r : ℝ) (a σ : ℂ),
      A = K₀ + G → K₀.IsHermitian → IsMoorePenroseInverse A R →
      0 < η → η ≤ δ → δ < 1 → ‖G‖ ≤ C₀ → |g 0| ≤ C₀ →
      (∀ x ∈ Set.Icc (-δ) δ, ∀ y ∈ Set.Icc (-δ) δ, |g x - g y| ≤ C₀ * |x - y|) →
      0 ≤ a₀ →
      (∀ (lam : ℝ) (v : ι → ℂ), lam ≠ 0 → |lam| ≤ δ → A *ᵥ v = (lam : ℂ) • v →
        star v ⬝ᵥ v = 1 → ‖star v ⬝ᵥ (K₀ *ᵥ v) - ((g lam : ℝ) : ℂ)‖ ≤ a₀) →
      ∑ j ∈ Finset.univ.filter (fun j => hA.eigenvalues j ≠ 0 ∧ |hA.eigenvalues j| ≤ δ),
          η ^ 2 / (hA.eigenvalues j ^ 2 + η ^ 2) ≤ C₀ * (Fintype.card ι : ℝ) * η →
      0 ≤ s → s ≤ 1 →
      ‖(A - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹.trace -
          ((Fintype.card ι : ℝ) : ℂ) * a‖ ≤ e₁ →
      ‖(G * (A - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹).trace +
          (s : ℂ) * ((Fintype.card ι : ℝ) : ℂ) * a ^ 2‖ ≤ e₂ →
      ‖a - σ‖ ≤ r → r ≤ 1 → σ.re ^ 2 + σ.im ^ 2 = 1 → σ.re = -E / 2 →
      |g 0 + s * E| ≤ e₃ →
      |(Fintype.card ι : ℝ) * (1 - s) - ((K₀ + ((s * E : ℝ) : ℂ) • 1) * R).trace.re| ≤
        Cu * a₀ * Real.sqrt ((Fintype.card ι : ℝ) * η) * hsNorm R +
          Cu * (Fintype.card ι : ℝ) * η + Cu * (Fintype.card ι : ℝ) * η ^ 2 +
          (η * e₁ + C₀ * e₁ + e₂ + (Fintype.card ι : ℝ) * (2 * η + 2 * e₃ + 4 * r)) +
          e₃ * Real.sqrt (Fintype.card ι : ℝ) * hsNorm R := by
  obtain ⟨C, hC⟩ := score_unsmoothing_of_unit_eigenvectors_nearSum.{0} C₀ δ
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ι _ _ A K₀ G R hA g a₀ η s E e₁ e₂ e₃ r a σ hAK hK hR hη hηδ hδ1 hG hg0 hLip ha₀ hETH
    hW hs hs1 he₁ he₂ har hr hσ hσE he₃
  set d : ℝ := (Fintype.card ι : ℝ)
  set Rη := (A - ((η : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ))⁻¹
  set X := (1 / 2 : ℂ) • (Rη + Rηᴴ)
  have hU := hC ι A K₀ G R hA g a₀ η hAK hR hη hηδ hδ1 hG hg0 hLip ha₀ hETH hW
  have hU' : ‖((K₀ - ((g 0 : ℝ) : ℂ) • 1) * (R - X)).trace‖ ≤
      max C 0 * a₀ * Real.sqrt (d * η) * hsNorm R + max C 0 * d * η + max C 0 * d * η ^ 2 := by
    refine hU.trans ?_
    have h1 : 0 ≤ a₀ * Real.sqrt (d * η) * hsNorm R :=
      mul_nonneg (mul_nonneg ha₀ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have h2 : 0 ≤ d * η := mul_nonneg (Nat.cast_nonneg _) hη.le
    have h3 : 0 ≤ d * η ^ 2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    have hm := le_max_left C 0
    nlinarith [mul_le_mul_of_nonneg_right hm h1, mul_le_mul_of_nonneg_right hm h2,
      mul_le_mul_of_nonneg_right hm h3]
  have hT2 := trace_smoothed_eq hA hK hAK hη (g 0)
  simp only at hT2
  have hsc := smoothed_scalar_bound (d := d) (η := η) (g₀ := g 0) (e₃ := e₃) (Nat.cast_nonneg _) hη hs hs1
    he₁ he₂ har hr hσ (by rw [hσE]; convert he₃ using 2; ring)
  have hdec := trace_decomp K₀ R X ((g 0 : ℝ) : ℂ) ((s * E : ℝ) : ℂ)
  have hTr := norm_trace_le R
  have hre : ((K₀ + ((s * E : ℝ) : ℂ) • 1) * R).trace.re =
      ((K₀ - ((g 0 : ℝ) : ℂ) • 1) * (R - X)).trace.re +
        (d - η * Rη.trace.im - g 0 * Rη.trace.re - (G * Rη).trace.re) +
        (g 0 + s * E) * R.trace.re := by
    rw [hdec, Complex.add_re, Complex.add_re, hT2, Complex.ofReal_re, ← Complex.ofReal_add,
      Complex.re_ofReal_mul]
  rw [hre]
  have hg0 : |g 0| * e₁ ≤ C₀ * e₁ :=
    mul_le_mul_of_nonneg_right hg0 ((abs_nonneg _).trans (by
      have := Complex.abs_re_le_norm (Rη.trace - (d : ℂ) * a); linarith))
  have hlast : |(g 0 + s * E) * R.trace.re| ≤ e₃ * Real.sqrt d * hsNorm R := by
    rw [abs_mul, mul_assoc]
    exact mul_le_mul he₃ ((Complex.abs_re_le_norm _).trans hTr) (abs_nonneg _)
      ((abs_nonneg _).trans he₃)
  have hfirst : |((K₀ - ((g 0 : ℝ) : ℂ) • 1) * (R - X)).trace.re| ≤
      max C 0 * a₀ * Real.sqrt (d * η) * hsNorm R + max C 0 * d * η + max C 0 * d * η ^ 2 :=
    (Complex.abs_re_le_norm _).trans hU'
  set T1 := ((K₀ - ((g 0 : ℝ) : ℂ) • 1) * (R - X)).trace.re
  set T2 := d - η * Rη.trace.im - g 0 * Rη.trace.re - (G * Rη).trace.re
  set T3 := (g 0 + s * E) * R.trace.re
  have key : |d * (1 - s) - (T1 + T2 + T3)| ≤ |T2 - d * (1 - s)| + |T1| + |T3| := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le T1, le_abs_self T1, neg_abs_le T3, le_abs_self T3,
      neg_abs_le (T2 - d * (1 - s)), le_abs_self (T2 - d * (1 - s))]
  linarith [key, hsc, hg0, hfirst, hlast]

end BlockBand.DeterminantScore.WeightedTrace
