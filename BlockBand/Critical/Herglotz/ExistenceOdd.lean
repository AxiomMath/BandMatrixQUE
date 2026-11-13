module

public import BlockBand.Critical.Herglotz.ExistenceTail

/-!
# Existence of `𝖢_r`, part 2: the conditionally convergent odd sum

The symmetric cutoff of the canonical series converges in probability. The only conditionally
convergent part of the canonical series is the `z`-independent odd sum
`A_L = π⁻¹ Σ_j χ_L(x_j) oddTail(x_j) g_j g_j^*`. Its weight is odd, so its mean is `0`, and its
`L²` increments are controlled by the second moments of the decorated sine process
(`signedProductTest_variance`); `A_L` is Cauchy in `L²(P)` and converges in probability
(`exists_tendstoInMeasure_oddSum`).

Law: `Ξ` decorated sine (`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`.

* `polMark i j c g = |g_i + c g_j|²`, `four_mul_entryMark` (polarization of `g_i conj(g_j)`).
* `entryStat_L2`: for continuous compactly supported real `w` with `∫ w = 0`, the entry
  statistic `X = ∫ w(x) g_i conj(g_j) dΞ` is in `L²(P)` and `E|X|² ≤ 32 ∫w² ∫ (Σ_k|g_k|²)² dγ`.
* `oddWeight`, `oddSum`, `integral_sq_oddWeight_sub_le` (`∫ (a_L - a_{L'})² ≤ 2 π⁻² τ(N)` for
  `L, L' ≥ N`).
* `exists_tendstoInMeasure_oddSum`: a measurable `A` with `A_L → A` in probability as `L → ∞`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal ComplexConjugate

namespace BlockBand.Critical.Herglotz

open BlockBand.Internal.Contracts.CriticalEntire
open BlockBand.Internal.Contracts.CoareaPalm (circularVectorLaw)

variable {r : ℕ}

/-!
## Polarization of the entry mark
-/

/-- `polMark i j c g = |g_i + c g_j|²`. -/
def polMark (i j : Fin r) (c : ℂ) (g : Fin r → ℂ) : ℝ := ‖g i + c * g j‖ ^ 2

theorem polMark_nonneg (i j : Fin r) (c : ℂ) (g : Fin r → ℂ) : 0 ≤ polMark i j c g :=
  sq_nonneg _

theorem continuous_polMark (i j : Fin r) (c : ℂ) : Continuous (polMark (r := r) i j c) := by
  unfold polMark; fun_prop

theorem norm_sq_apply_le_euclidMark (g : Fin r → ℂ) (i : Fin r) : ‖g i‖ ^ 2 ≤ euclidMark g :=
  Finset.single_le_sum (f := fun k => ‖g k‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem polMark_le (i j : Fin r) {c : ℂ} (hc : ‖c‖ = 1) (g : Fin r → ℂ) :
    polMark i j c g ≤ 4 * euclidMark g := by
  have h1 : ‖g i + c * g j‖ ≤ ‖g i‖ + ‖g j‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hc, one_mul]
  have hi := norm_sq_apply_le_euclidMark g i
  have hj := norm_sq_apply_le_euclidMark g j
  unfold polMark
  have h0 := norm_nonneg (g i + c * g j)
  nlinarith [sq_nonneg (‖g i‖ - ‖g j‖), norm_nonneg (g i), norm_nonneg (g j)]

theorem integrable_polMark_sq (i j : Fin r) {c : ℂ} (hc : ‖c‖ = 1) :
    Integrable (fun g => polMark i j c g ^ 2) (circularVectorLaw (Fin r)) := by
  refine (integrable_euclidMark_sq.const_mul 16).mono'
    ((continuous_polMark i j c).pow 2).aestronglyMeasurable (Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := polMark_le i j hc g
  have h0 := polMark_nonneg i j c g
  nlinarith

theorem integral_polMark_sq_le (i j : Fin r) {c : ℂ} (hc : ‖c‖ = 1) :
    ∫ g, polMark i j c g ^ 2 ∂circularVectorLaw (Fin r) ≤
      16 * ∫ g, euclidMark g ^ 2 ∂circularVectorLaw (Fin r) := by
  rw [← integral_const_mul]
  refine integral_mono (integrable_polMark_sq i j hc) (integrable_euclidMark_sq.const_mul 16)
    fun g => ?_
  have h := polMark_le i j hc g
  have h0 := polMark_nonneg i j c g
  dsimp only
  nlinarith

/-- **Polarization:** `4 g_i conj(g_j) = |g_i + g_j|² - |g_i - g_j|² + i |g_i + i g_j|²
- i |g_i - i g_j|²`. -/
theorem four_mul_entryMark (i j : Fin r) (g : Fin r → ℂ) :
    4 * entryMark i j g = (polMark i j 1 g : ℂ) - (polMark i j (-1) g : ℂ) +
      Complex.I * (polMark i j Complex.I g : ℂ) - Complex.I * (polMark i j (-Complex.I) g : ℂ) := by
  have hpm (c : ℂ) : (polMark i j c g : ℂ) = (g i + c * g j) * conj (g i + c * g j) := by
    rw [polMark, Complex.mul_conj']; push_cast; rfl
  rw [hpm, hpm, hpm, hpm, entryMark]
  simp only [map_add, map_mul, map_neg, map_one, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-!
## `L²` bound for signed entry statistics
-/

theorem sq_add_four_le (a b c d : ℝ) :
    (|a| + |b| + |c| + |d|) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - |c|), sq_nonneg (|a| - |d|),
    sq_nonneg (|b| - |c|), sq_nonneg (|b| - |d|), sq_nonneg (|c| - |d|), sq_abs a, sq_abs b,
    sq_abs c, sq_abs d]

theorem norm_polCombo_sq_le (a b c d : ℝ) :
    ‖(4 : ℂ)⁻¹ * ((a : ℂ) - b + Complex.I * c - Complex.I * d)‖ ^ 2 ≤
      4⁻¹ * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  have h : ‖(4 : ℂ)⁻¹ * ((a : ℂ) - b + Complex.I * c - Complex.I * d)‖ ≤
      4⁻¹ * (|a| + |b| + |c| + |d|) := by
    rw [norm_mul, norm_inv, show ‖(4 : ℂ)‖ = 4 by norm_num]
    gcongr
    have e1 := norm_sub_le ((a : ℂ) - b + Complex.I * c) (Complex.I * d)
    have e2 := norm_add_le ((a : ℂ) - b) (Complex.I * c)
    have e3 := norm_sub_le (a : ℂ) (b : ℂ)
    simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at e1 e2 e3
    linarith
  have h0 : 0 ≤ ‖(4 : ℂ)⁻¹ * ((a : ℂ) - b + Complex.I * c - Complex.I * d)‖ := norm_nonneg _
  have h2 := sq_add_four_le a b c d
  calc _ ≤ (4⁻¹ * (|a| + |b| + |c| + |d|)) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 16⁻¹ * (|a| + |b| + |c| + |d|) ^ 2 := by ring
    _ ≤ 16⁻¹ * (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) := by gcongr
    _ = _ := by ring

/-- **`L²` bound for signed entry statistics** (second moments with polarization). Law: `Ξ`
decorated sine (`IsDecoratedSineProcess`), `γ = circularVectorLaw (Fin r)`. For continuous
compactly supported real `w` with `∫ w = 0` and entries `i, j`, `X(ω) = ∫ w(x) g_i conj(g_j) dΞ(ω)`:
almost surely the integrand is `Ξ(ω)`-integrable, `X ∈ L²(P)`, and
`E|X|² ≤ 32 (∫ w²) ∫ (Σ_k |g_k|²)² dγ`. -/
theorem entryStat_L2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    {w : ℝ → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hw0 : ∫ x, w x = 0)
    (i j : Fin r) :
    (∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) => (w p.1 : ℂ) * entryMark i j p.2)
      (Ξ ω).measure) ∧
    MemLp (fun ω => ∫ p, (w p.1 : ℂ) * entryMark i j p.2 ∂(Ξ ω).measure) 2 P ∧
    ∫ ω, ‖∫ p, (w p.1 : ℂ) * entryMark i j p.2 ∂(Ξ ω).measure‖ ^ 2 ∂P ≤
      32 * (∫ x, w x ^ 2) * ∫ g, euclidMark g ^ 2 ∂circularVectorLaw (Fin r) := by
  have := h.prob
  set γ := circularVectorLaw (Fin r) with hγ
  set E := ∫ g, euclidMark g ^ 2 ∂γ with hE
  have hW0 : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hc1 : ‖(1 : ℂ)‖ = 1 := norm_one
  have hc2 : ‖(-1 : ℂ)‖ = 1 := by simp
  have hc3 : ‖Complex.I‖ = 1 := Complex.norm_I
  have hc4 : ‖-Complex.I‖ = 1 := by simp
  -- the four polarized statistics
  have hS (c : ℂ) (hc : ‖c‖ = 1) := signedProductTest_variance h hw hwc
    (continuous_polMark i j c) (polMark_nonneg i j c) (integrable_polMark_sq i j hc)
  set Y : ℂ → Ω → ℝ := fun c ω => ∫ p, w p.1 * polMark i j c p.2 ∂(Ξ ω).measure with hY
  have hYae (c : ℂ) (hc : ‖c‖ = 1) := (hS c hc).1
  have hYi (c : ℂ) (hc : ‖c‖ = 1) : Integrable (Y c) P := (hS c hc).2.1
  have hYsq (c : ℂ) (hc : ‖c‖ = 1) : Integrable (fun ω => Y c ω ^ 2) P := by
    have := (hS c hc).2.2.2.1
    simpa [hw0] using this
  have hYV (c : ℂ) (hc : ‖c‖ = 1) : ∫ ω, Y c ω ^ 2 ∂P ≤ 32 * (∫ x, w x ^ 2) * E := by
    have h1 := (hS c hc).2.2.2.2
    simp only [hw0, zero_mul, sub_zero] at h1
    have h2 := integral_polMark_sq_le i j hc
    calc ∫ ω, Y c ω ^ 2 ∂P ≤ 2 * ((∫ x, w x ^ 2) * ∫ g, polMark i j c g ^ 2 ∂γ) := h1
      _ ≤ 2 * ((∫ x, w x ^ 2) * (16 * E)) := by gcongr
      _ = 32 * (∫ x, w x ^ 2) * E := by ring
  have hYm (c : ℂ) (hc : ‖c‖ = 1) : MemLp (Y c) 2 P :=
    (memLp_two_iff_integrable_sq (hYi c hc).aestronglyMeasurable).2 (hYsq c hc)
  -- pointwise identity of integrands
  have hpt (p : ℝ × (Fin r → ℂ)) : (w p.1 : ℂ) * entryMark i j p.2 =
      (4 : ℂ)⁻¹ * (((w p.1 * polMark i j 1 p.2 : ℝ) : ℂ) - ((w p.1 * polMark i j (-1) p.2 : ℝ) : ℂ)
        + Complex.I * ((w p.1 * polMark i j Complex.I p.2 : ℝ) : ℂ)
        - Complex.I * ((w p.1 * polMark i j (-Complex.I) p.2 : ℝ) : ℂ)) := by
    have h4 := four_mul_entryMark i j p.2
    have : entryMark i j p.2 = (4 : ℂ)⁻¹ * (4 * entryMark i j p.2) := by field_simp
    rw [this, h4]
    push_cast
    ring
  set Z : Ω → ℂ := fun ω => (4 : ℂ)⁻¹ * ((Y 1 ω : ℂ) - (Y (-1) ω : ℂ) +
    Complex.I * (Y Complex.I ω : ℂ) - Complex.I * (Y (-Complex.I) ω : ℂ)) with hZ
  have hae : ∀ᵐ ω ∂P, Integrable (fun p : ℝ × (Fin r → ℂ) => (w p.1 : ℂ) * entryMark i j p.2)
      (Ξ ω).measure ∧ ∫ p, (w p.1 : ℂ) * entryMark i j p.2 ∂(Ξ ω).measure = Z ω := by
    filter_upwards [hYae 1 hc1, hYae (-1) hc2, hYae Complex.I hc3, hYae (-Complex.I) hc4]
      with ω h1 h2 h3 h4
    have i1 : Integrable (fun p : ℝ × (Fin r → ℂ) => ((w p.1 * polMark i j 1 p.2 : ℝ) : ℂ))
        (Ξ ω).measure := h1.ofReal (𝕜 := ℂ)
    have i2 : Integrable (fun p : ℝ × (Fin r → ℂ) => ((w p.1 * polMark i j (-1) p.2 : ℝ) : ℂ))
        (Ξ ω).measure := h2.ofReal (𝕜 := ℂ)
    have i3 : Integrable (fun p : ℝ × (Fin r → ℂ) =>
        Complex.I * ((w p.1 * polMark i j Complex.I p.2 : ℝ) : ℂ)) (Ξ ω).measure :=
      (h3.ofReal (𝕜 := ℂ)).const_mul Complex.I
    have i4 : Integrable (fun p : ℝ × (Fin r → ℂ) =>
        Complex.I * ((w p.1 * polMark i j (-Complex.I) p.2 : ℝ) : ℂ)) (Ξ ω).measure :=
      (h4.ofReal (𝕜 := ℂ)).const_mul Complex.I
    have i12 : Integrable (fun p : ℝ × (Fin r → ℂ) => ((w p.1 * polMark i j 1 p.2 : ℝ) : ℂ) -
        ((w p.1 * polMark i j (-1) p.2 : ℝ) : ℂ)) (Ξ ω).measure := i1.sub i2
    have i123 : Integrable (fun p : ℝ × (Fin r → ℂ) => ((w p.1 * polMark i j 1 p.2 : ℝ) : ℂ) -
        ((w p.1 * polMark i j (-1) p.2 : ℝ) : ℂ) +
        Complex.I * ((w p.1 * polMark i j Complex.I p.2 : ℝ) : ℂ)) (Ξ ω).measure := i12.add i3
    have i1234 : Integrable (fun p : ℝ × (Fin r → ℂ) => ((w p.1 * polMark i j 1 p.2 : ℝ) : ℂ) -
        ((w p.1 * polMark i j (-1) p.2 : ℝ) : ℂ) +
        Complex.I * ((w p.1 * polMark i j Complex.I p.2 : ℝ) : ℂ) -
        Complex.I * ((w p.1 * polMark i j (-Complex.I) p.2 : ℝ) : ℂ)) (Ξ ω).measure :=
      i123.sub i4
    simp_rw [hpt]
    refine ⟨i1234.const_mul _, ?_⟩
    rw [integral_const_mul, integral_sub i123 i4, integral_add i12 i3,
      integral_sub i1 i2, integral_const_mul, integral_const_mul, integral_complex_ofReal,
      integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal]
  have hXZ : (fun ω => ∫ p, (w p.1 : ℂ) * entryMark i j p.2 ∂(Ξ ω).measure) =ᵐ[P] Z :=
    hae.mono fun ω hω => hω.2
  have hZm : MemLp Z 2 P := by
    have m1 := (hYm 1 hc1).ofReal (K := ℂ)
    have m2 := (hYm (-1) hc2).ofReal (K := ℂ)
    have m3 := ((hYm Complex.I hc3).ofReal (K := ℂ)).const_mul Complex.I
    have m4 := ((hYm (-Complex.I) hc4).ofReal (K := ℂ)).const_mul Complex.I
    exact (((m1.sub m2).add m3).sub m4).const_mul _
  have hXm := hZm.ae_eq hXZ.symm
  refine ⟨hae.mono fun ω hω => hω.1, hXm, ?_⟩
  have hZsq : Integrable (fun ω => ‖Z ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm hZm.aestronglyMeasurable).1 hZm
  have hsum4 : Integrable (fun ω => 4⁻¹ * (Y 1 ω ^ 2 + Y (-1) ω ^ 2 + Y Complex.I ω ^ 2 +
      Y (-Complex.I) ω ^ 2)) P :=
    ((((hYsq 1 hc1).add (hYsq (-1) hc2)).add (hYsq Complex.I hc3)).add
      (hYsq (-Complex.I) hc4)).const_mul _
  have hsqeq : (fun ω => ‖∫ p, (w p.1 : ℂ) * entryMark i j p.2 ∂(Ξ ω).measure‖ ^ 2) =ᵐ[P]
      fun ω => ‖Z ω‖ ^ 2 := hXZ.mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω
  rw [integral_congr_ae hsqeq]
  calc ∫ ω, ‖Z ω‖ ^ 2 ∂P ≤ ∫ ω, 4⁻¹ * (Y 1 ω ^ 2 + Y (-1) ω ^ 2 + Y Complex.I ω ^ 2 +
        Y (-Complex.I) ω ^ 2) ∂P :=
        integral_mono hZsq hsum4 fun ω => norm_polCombo_sq_le _ _ _ _
    _ = 4⁻¹ * (∫ ω, Y 1 ω ^ 2 ∂P + ∫ ω, Y (-1) ω ^ 2 ∂P + ∫ ω, Y Complex.I ω ^ 2 ∂P +
        ∫ ω, Y (-Complex.I) ω ^ 2 ∂P) := by
        have j12 : Integrable (fun ω => Y 1 ω ^ 2 + Y (-1) ω ^ 2) P :=
          (hYsq 1 hc1).add (hYsq (-1) hc2)
        have j123 : Integrable (fun ω => Y 1 ω ^ 2 + Y (-1) ω ^ 2 + Y Complex.I ω ^ 2) P :=
          j12.add (hYsq Complex.I hc3)
        rw [integral_const_mul, integral_add j123 (hYsq (-Complex.I) hc4),
          integral_add j12 (hYsq Complex.I hc3), integral_add (hYsq 1 hc1) (hYsq (-1) hc2)]
    _ ≤ 4⁻¹ * (4 * (32 * (∫ x, w x ^ 2) * E)) := by
        have := hYV 1 hc1
        have := hYV (-1) hc2
        have := hYV Complex.I hc3
        have := hYV (-Complex.I) hc4
        gcongr
        linarith
    _ = 32 * (∫ x, w x ^ 2) * E := by ring

/-!
## The odd sum
-/

/-- The odd weight `a_L(x) = π⁻¹ χ_L(x) oddTail(x)`. -/
def oddWeight (L x : ℝ) : ℝ := Real.pi⁻¹ * smoothCutoff L x * oddTail x

theorem continuous_oddWeight (L : ℝ) : Continuous (oddWeight L) :=
  (continuous_const.mul (continuous_smoothCutoff L)).mul continuous_oddTail

theorem hasCompactSupport_oddWeight (L : ℝ) : HasCompactSupport (oddWeight L) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (L + 1)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  simp [oddWeight, smoothCutoff_eq_zero hx.le]

theorem oddWeight_neg (L x : ℝ) : oddWeight L (-x) = -oddWeight L x := by
  simp only [oddWeight, smoothCutoff_neg, oddTail_neg, mul_neg]

/-- `π⁻¹ Σ_j χ_L(x_j) oddTail(x_j) (g_j)_i conj((g_j)_j)`. -/
def oddSum (ξ : VaguePointMeasure (ℝ × (Fin r → ℂ))) (L : ℝ) (i j : Fin r) : ℂ :=
  ∫ p, ((oddWeight L p.1 : ℝ) : ℂ) * entryMark i j p.2 ∂ξ.measure

theorem integral_odd_eq_zero {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have h := integral_neg_eq_self f volume
  simp_rw [hf, integral_neg] at h
  linarith

theorem abs_smoothCutoff_sub_le {N L L' : ℝ} (hL : N ≤ L) (hL' : N ≤ L') (x : ℝ) :
    |smoothCutoff L x - smoothCutoff L' x| ≤ 1 - smoothCutoff N x := by
  have h1 := smoothCutoff_mono hL x
  have h2 := smoothCutoff_mono hL' x
  have h3 := smoothCutoff_le_one L x
  have h4 := smoothCutoff_le_one L' x
  rw [abs_le]; constructor <;> linarith

theorem sq_oddWeight_sub_le {N L L' : ℝ} (hL : N ≤ L) (hL' : N ≤ L') (x : ℝ) :
    (oddWeight L x - oddWeight L' x) ^ 2 ≤
      2 * (Real.pi⁻¹) ^ 2 * ((1 - smoothCutoff N x) * tailWeight x) := by
  have heq : oddWeight L x - oddWeight L' x =
      Real.pi⁻¹ * (smoothCutoff L x - smoothCutoff L' x) * oddTail x := by
    unfold oddWeight; ring
  rw [heq, mul_pow, mul_pow]
  have h1 := abs_smoothCutoff_sub_le hL hL' x
  have h0 := one_sub_smoothCutoff_nonneg N x
  have h1' := one_sub_smoothCutoff_le_one N x
  have hsq : (smoothCutoff L x - smoothCutoff L' x) ^ 2 ≤ 1 - smoothCutoff N x := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (smoothCutoff L x - smoothCutoff L' x)]
  have ho := oddTail_sq_le x
  have hw := (tailWeight_pos x).le
  have hpi : 0 ≤ (Real.pi⁻¹) ^ 2 := sq_nonneg _
  calc (Real.pi⁻¹) ^ 2 * (smoothCutoff L x - smoothCutoff L' x) ^ 2 * oddTail x ^ 2
      ≤ (Real.pi⁻¹) ^ 2 * (1 - smoothCutoff N x) * (2 * tailWeight x) := by
        gcongr
    _ = _ := by ring

/-- `∫ (a_L - a_{L'})² ≤ 2 π⁻² τ(N)` for `L, L' ≥ N`. -/
theorem integral_sq_oddWeight_sub_le {N L L' : ℝ} (hL : N ≤ L) (hL' : N ≤ L') :
    ∫ x, (oddWeight L x - oddWeight L' x) ^ 2 ≤ 2 * (Real.pi⁻¹) ^ 2 * tailWeightMass N := by
  unfold tailWeightMass
  rw [← integral_const_mul]
  refine integral_mono ?_ ((integrable_one_sub_smoothCutoff_mul_tailWeight N).const_mul _)
    (sq_oddWeight_sub_le hL hL')
  exact (((continuous_oddWeight L).sub (continuous_oddWeight L')).pow 2).integrable_of_hasCompactSupport
    (hasCompactSupport_sq ((hasCompactSupport_oddWeight L).sub (hasCompactSupport_oddWeight L')))

/-- `eLpNorm f 2 ≤ √B` from `∫ |f|² ≤ B`. -/
theorem eLpNorm_two_le_of_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℂ}
    (hf : MemLp f 2 P) {B : ℝ} (hB : ∫ ω, ‖f ω‖ ^ 2 ∂P ≤ B) :
    eLpNorm f 2 P ≤ ENNReal.ofReal (Real.sqrt B) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg _) hB (by norm_num)

/-- **The odd sum converges in probability.** Law: `Ξ` decorated sine
(`IsDecoratedSineProcess`). For each entry `(i, j)` there is a measurable `A : Ω → ℂ` with
`oddSum (Ξ ·) L i j → A` in `P`-probability as `L → ∞` (indeed in `L²(P)`, with
`‖A_L - A‖_{L²} ≤ (64 π⁻² τ(L) ∫ (Σ_k|g_k|²)² dγ)^{1/2}`). -/
theorem exists_tendstoInMeasure_oddSum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Ξ : Ω → VaguePointMeasure (ℝ × (Fin r → ℂ))} (h : IsDecoratedSineProcess r P Ξ)
    (i j : Fin r) :
    ∃ A : Ω → ℂ, Measurable A ∧
      TendstoInMeasure P (fun L ω => oddSum (Ξ ω) L i j) atTop A := by
  have := h.prob
  set E := ∫ g, euclidMark g ^ 2 ∂circularVectorLaw (Fin r) with hE
  have hE0 : 0 ≤ E := integral_nonneg fun g => sq_nonneg _
  set K := 32 * (2 * (Real.pi⁻¹) ^ 2) * E with hK
  have hK0 : 0 ≤ K := by positivity
  set X : ℝ → Ω → ℂ := fun L ω => oddSum (Ξ ω) L i j with hX
  have hL2 (L : ℝ) := entryStat_L2 h (continuous_oddWeight L) (hasCompactSupport_oddWeight L)
    (integral_odd_eq_zero (oddWeight_neg L)) i j
  have hmem (L : ℝ) : MemLp (X L) 2 P := (hL2 L).2.1
  have hbound {N L L' : ℝ} (hL : N ≤ L) (hL' : N ≤ L') :
      eLpNorm (X L - X L') 2 P ≤ ENNReal.ofReal (Real.sqrt (K * tailWeightMass N)) := by
    set w := fun x => oddWeight L x - oddWeight L' x with hw
    have hw0 : ∫ x, w x = 0 := integral_odd_eq_zero fun x => by
      simp only [hw, oddWeight_neg]; ring
    have hD := entryStat_L2 h ((continuous_oddWeight L).sub (continuous_oddWeight L'))
      ((hasCompactSupport_oddWeight L).sub (hasCompactSupport_oddWeight L')) hw0 i j
    have heq : X L - X L' =ᵐ[P] fun ω => ∫ p, (w p.1 : ℂ) * entryMark i j p.2 ∂(Ξ ω).measure := by
      filter_upwards [(hL2 L).1, (hL2 L').1] with ω h1 h2
      simp only [Pi.sub_apply, hX, oddSum]
      rw [← integral_sub h1 h2]
      congr 1; funext p; simp only [hw]; push_cast; ring
    rw [eLpNorm_congr_ae heq]
    refine eLpNorm_two_le_of_integral hD.2.1 (hD.2.2.trans ?_)
    have := integral_sq_oddWeight_sub_le (N := N) hL hL'
    calc 32 * (∫ x, w x ^ 2) * E ≤ 32 * (2 * (Real.pi⁻¹) ^ 2 * tailWeightMass N) * E := by gcongr
      _ = K * tailWeightMass N := by rw [hK]; ring
  have hsq : Tendsto (fun N : ℝ => ENNReal.ofReal (Real.sqrt (K * tailWeightMass N))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℝ => Real.sqrt (K * tailWeightMass N)) atTop (𝓝 0) := by
      have h2 := tendsto_tailWeightMass.const_mul K
      rw [mul_zero] at h2
      have := (Real.continuous_sqrt.tendsto 0).comp h2
      rw [Real.sqrt_zero] at this
      exact this
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp h1
  -- the `L²` limit along the integers
  set u : ℕ → Lp ℂ 2 P := fun n => (hmem n).toLp (X n) with hu
  have hdist (n m : ℕ) : dist (u n) (u m) = (eLpNorm (X n - X m) 2 P).toReal := by
    rw [Lp.dist_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hmem n).coeFn_toLp, (hmem m).coeFn_toLp] with ω h1 h2
    simp only [Pi.sub_apply, hu, h1, h2]
  have hcau : CauchySeq u := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := (ENNReal.tendsto_nhds_zero.1 hsq) (ENNReal.ofReal (ε / 2)) (by simpa using hε)
    obtain ⟨N₀, hN₀⟩ := (eventually_atTop.1 hev)
    obtain ⟨N, hN⟩ := exists_nat_ge N₀
    refine ⟨N, fun n hn => ?_⟩
    rw [hdist]
    have hb := (hbound (N := (N : ℝ)) (L := (n : ℝ)) (L' := (N : ℝ)) (by exact_mod_cast hn)
      le_rfl).trans (hN₀ N hN)
    have hfin : eLpNorm (X n - X N) 2 P ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
    have := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2 hb
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  obtain ⟨F, hF⟩ := cauchySeq_tendsto_of_complete hcau
  have hFn : Tendsto (fun n : ℕ => eLpNorm (X n - (F : Ω → ℂ)) 2 P) atTop (𝓝 0) := by
    have := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' u F).1 hF
    refine this.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [(hmem n).coeFn_toLp] with ω h1
    simp only [Pi.sub_apply, hu, h1]
  refine ⟨F, (Lp.stronglyMeasurable F).measurable, ?_⟩
  refine tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero ?_
  have hle (L : ℝ) : eLpNorm (X L - (F : Ω → ℂ)) 2 P ≤
      ENNReal.ofReal (Real.sqrt (K * tailWeightMass L)) := by
    have hev : ∀ᶠ n : ℕ in atTop, eLpNorm (X L - (F : Ω → ℂ)) 2 P ≤
        ENNReal.ofReal (Real.sqrt (K * tailWeightMass L)) + eLpNorm (X n - (F : Ω → ℂ)) 2 P := by
      filter_upwards [eventually_ge_atTop ⌈L⌉₊] with n hn
      have hLn : L ≤ n := (Nat.le_ceil L).trans (by exact_mod_cast hn)
      have htri : X L - (F : Ω → ℂ) = (X L - X n) + (X n - (F : Ω → ℂ)) := by abel
      rw [htri]
      exact (eLpNorm_add_le one_le_two).trans (add_le_add_left (hbound le_rfl hLn) _)
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (K * tailWeightMass L)) +
        eLpNorm (X n - (F : Ω → ℂ)) 2 P) atTop (𝓝 (ENNReal.ofReal (Real.sqrt (K * tailWeightMass L)) + 0)) :=
      tendsto_const_nhds.add hFn
    rw [add_zero] at hlim
    exact ge_of_tendsto hlim hev
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq (fun _ => zero_le) hle

end BlockBand.Critical.Herglotz
