module

public import BlockBand.Critical.RelativeVectors.IntervalTime
public import BlockBand.Critical.RelativeVectors.IntervalSum

/-!
# The middle line of the interval bound at one time

Deterministic. *Domain:* `N ≥ 1`, `FreshConstants`, `F` in `FreshClass`, `V^*ΓV = I_r`,
`s ∈ [c - s₀, c]`, a Hermitian `H` with simple spectrum satisfying the three conclusions of
`interval_time_bounds` (at `h = N^{-1/100}`), and `K` with `2^K h ≤ 1 < 2^{K+1} h`.

* `rIm_eq_sum`, `rTr_eq_sum`: the spectral forms `Im w^*G(e+iη)w = Σ_i |w^*u_i|² pk η (λ_i - e)`
  and `Im Tr G(e+iη) = Σ_i pk η (λ_i - e)`.
* `interval_det`: for every energy interval `[x, y] ⊂ [E - r₀/4, E + r₀/4]` and `p ∈ ℂ^r`,
  with `S = {i : λ_i ∈ [x, y]}` and `z_i = frameArray V H i = √N V^*u_i`:
  `|Σ_{i∈S} (|p^*z_i|² - p^*V^*Γ(s, λ_i)Vp)| ≤ B₄ N h (K + 2) ‖p‖²`.
  Rank intervals in the window are the case `x = λ_{i₁}`, `y = λ_{i₂}` (on simple spectrum
  `S` is then exactly the rank interval `[i₁, i₂]`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Matrix Set
open BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Palm.MomentFlow BlockBand.Palm.CoarseRelative
open BlockBand.Critical.WeightedDensity

variable {N r : ℕ}

theorem rIm_eq_sum {H : Matrix (Fin N) (Fin N) ℂ} (hH : SimpleSpectrum H) (w : Fin N → ℂ)
    (e : ℝ) {η : ℝ} (hη : 0 < η) :
    rIm H w ⟨e, η⟩ = ∑ i, Complex.normSq (star w ⬝ᵥ freshEigenvector H i) *
      pk η (freshEigenvalue H i - e) := by
  unfold rIm
  rw [im_resolvent_quad_eq_at hH w e η hη.ne']
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold pk; ring

theorem sum_normSq_freshEigenvector {H : Matrix (Fin N) (Fin N) ℂ} (hH : SimpleSpectrum H)
    (i : Fin N) : ∑ k, Complex.normSq (freshEigenvector H i k) = 1 := by
  have h := hH.orthonormal i i
  simp only [↓reduceIte] at h
  have h2 := congrArg Complex.re h
  rw [Complex.one_re] at h2
  rw [← h2]
  unfold dotProduct
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re]

theorem rTr_eq_sum {H : Matrix (Fin N) (Fin N) ℂ} (hH : SimpleSpectrum H) (e : ℝ) {η : ℝ}
    (hη : 0 < η) : rTr H ⟨e, η⟩ = ∑ i, pk η (freshEigenvalue H i - e) := by
  unfold rTr
  rw [trace_im_eq_sum]
  have : ∀ k : Fin N, (star (Pi.single k (1 : ℂ)) ⬝ᵥ
      ((H - (⟨e, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ *ᵥ Pi.single k 1)).im =
      ∑ i, Complex.normSq (freshEigenvector H i k) * pk η (freshEigenvalue H i - e) := by
    intro k
    have := rIm_eq_sum hH (Pi.single k 1) e hη
    unfold rIm at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    simp [dotProduct, Pi.single_apply]
  simp only [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_mul, sum_normSq_freshEigenvector hH i, one_mul]

/-- `Σ_i μ_i dyW h K (λ_i - e) = h (Σ_{k ≤ K} Σ_i μ_i pk(2^kh) + Σ_i μ_i pk 1)`. -/
theorem sum_dyW_eq (lam μ : Fin N → ℝ) (h : ℝ) (K : ℕ) (e : ℝ) :
    ∑ i, μ i * dyW h K (lam i - e) =
      h * (∑ k ∈ Finset.range (K + 1), ∑ i, μ i * pk (2 ^ k * h) (lam i - e) +
        ∑ i, μ i * pk 1 (lam i - e)) := by
  unfold dyW
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- `R = max(r₀, 1)`. -/
def intR (r₀ : ℝ) : ℝ := max r₀ 1

/-- The constant `B₄` of `interval_det`. -/
def intB4 (c r₀ s₀ v₀ : ℝ) (r : ℕ) : ℝ :=
  (2 * intR r₀ ^ 2 + 4) * (2 * intB1 c r₀ s₀ v₀ r +
      2 * (c * dysonGammaConst c r₀ s₀ v₀) * intB2 v₀ +
      c * dysonShiftConst c r₀ s₀ v₀ * dysonGammaConst c r₀ s₀ v₀ * intR r₀ * intB2 v₀) +
    intR r₀ * intB3 c r₀ s₀ v₀ r

theorem dysonGammaConst_nonneg {c r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    0 ≤ dysonGammaConst c r₀ s₀ v₀ := by
  have := dysonShiftConst_nonneg hK
  have hc := hK.1
  have hr := hK.2.2.1
  have hs := hK.2.2.2.1
  unfold dysonGammaConst; positivity

/-- The final arithmetic of `interval_det` (abstract reals). -/
theorem interval_det_arith {R C' Cs B₁ B₂ B₃ c n h k P d Sμ S1 : ℝ} (hR : 1 ≤ R)
    (hC' : 0 ≤ C') (hCs : 0 ≤ Cs) (hB₂ : 0 ≤ B₂) (hB₃ : 0 ≤ B₃) (hc : 0 ≤ c)
    (hn : 0 ≤ n) (hh : 0 ≤ h) (hk : 1 ≤ k) (hP : 0 ≤ P) (hd0 : 0 ≤ d) (hd : d ≤ R)
    (hSμ : Sμ ≤ 2 * (h * (k * (B₁ * P)))) (hS1 : S1 ≤ 2 * (h * (k * (n * B₂)))) :
    (2 * R ^ 2 + 4) * (n * Sμ + c * C' * P * S1 + c * Cs * C' * P * d * (h * (k * (n * B₂))) /
        Real.pi) + d * (n * B₃ * h * P) / Real.pi ≤
      ((2 * R ^ 2 + 4) * (2 * B₁ + 2 * (c * C') * B₂ + c * Cs * C' * R * B₂) + R * B₃) *
        (n * h * k * P) := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hT0 : 0 ≤ n * h * k * P := by have : 0 ≤ k := by linarith
                                     positivity
  have e1 : n * Sμ ≤ 2 * B₁ * (n * h * k * P) := by
    calc n * Sμ ≤ n * (2 * (h * (k * (B₁ * P)))) := mul_le_mul_of_nonneg_left hSμ hn
      _ = 2 * B₁ * (n * h * k * P) := by ring
  have e2 : c * C' * P * S1 ≤ 2 * (c * C') * B₂ * (n * h * k * P) := by
    calc c * C' * P * S1 ≤ c * C' * P * (2 * (h * (k * (n * B₂)))) :=
          mul_le_mul_of_nonneg_left hS1 (by positivity)
      _ = 2 * (c * C') * B₂ * (n * h * k * P) := by ring
  have e3 : c * Cs * C' * P * d * (h * (k * (n * B₂))) / Real.pi ≤
      c * Cs * C' * R * B₂ * (n * h * k * P) := by
    have hX : 0 ≤ c * Cs * C' * P * (h * (k * (n * B₂))) := by
      have : 0 ≤ k := by linarith
      positivity
    have ha : 0 ≤ c * Cs * C' * P * d * (h * (k * (n * B₂))) := by
      have : 0 ≤ k := by linarith
      positivity
    refine (div_le_self ha hpi).trans ?_
    calc c * Cs * C' * P * d * (h * (k * (n * B₂)))
        = d * (c * Cs * C' * P * (h * (k * (n * B₂)))) := by ring
      _ ≤ R * (c * Cs * C' * P * (h * (k * (n * B₂)))) := mul_le_mul_of_nonneg_right hd hX
      _ = c * Cs * C' * R * B₂ * (n * h * k * P) := by ring
  have e4 : d * (n * B₃ * h * P) / Real.pi ≤ R * B₃ * (n * h * k * P) := by
    have hX : 0 ≤ n * B₃ * h * P := by positivity
    refine (div_le_self (mul_nonneg hd0 hX) hpi).trans ?_
    calc d * (n * B₃ * h * P) ≤ R * (n * B₃ * h * P) := mul_le_mul_of_nonneg_right hd hX
      _ = R * B₃ * (n * h * 1 * P) := by ring
      _ ≤ R * B₃ * (n * h * k * P) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hP
          exact mul_le_mul_of_nonneg_left hk (by positivity)
  have hC0 : 0 ≤ 2 * R ^ 2 + 4 := by positivity
  calc (2 * R ^ 2 + 4) * (n * Sμ + c * C' * P * S1 + c * Cs * C' * P * d * (h * (k * (n * B₂))) /
        Real.pi) + d * (n * B₃ * h * P) / Real.pi
      ≤ (2 * R ^ 2 + 4) * (2 * B₁ * (n * h * k * P) + 2 * (c * C') * B₂ * (n * h * k * P) +
          c * Cs * C' * R * B₂ * (n * h * k * P)) + R * B₃ * (n * h * k * P) :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) e3) hC0) e4
    _ = _ := by ring

/-- **The middle line of the interval bound at one time.** See the module docstring. -/
theorem interval_det {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1) {s : ℝ}
    (hs : s ∈ Icc (c - s₀) c) {H : Matrix (Fin N) (Fin N) ℂ} (hHs : SimpleSpectrum H)
    (h1 : ∀ x : ℝ, |x - E| ≤ r₀ / 2 → ∀ η : ℝ, (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 →
      ∀ p : Fin r → ℂ, rIm H (V *ᵥ p) ⟨x, η⟩ ≤ intB1 c r₀ s₀ v₀ r * nsq p)
    (h2 : ∀ x : ℝ, |x - E| ≤ r₀ / 2 → ∀ η : ℝ, (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ η → η ≤ 1 →
      rTr H ⟨x, η⟩ ≤ N * intB2 v₀)
    (h3 : ∀ x : ℝ, |x - E| ≤ r₀ / 2 → ∀ p : Fin r → ℂ,
      |(N : ℝ) * rIm H (V *ᵥ p) ⟨x, (N : ℝ) ^ (-(1 / 100 : ℝ))⟩ -
        quadForm (freshGamma F s x) (V *ᵥ p) * rTr H ⟨x, (N : ℝ) ^ (-(1 / 100 : ℝ))⟩| ≤
      N * intB3 c r₀ s₀ v₀ r * (N : ℝ) ^ (-(1 / 100 : ℝ)) * nsq p)
    {K : ℕ} (hK1 : 1 < 2 ^ (K + 1) * (N : ℝ) ^ (-(1 / 100 : ℝ)))
    (hK2 : 2 ^ K * (N : ℝ) ^ (-(1 / 100 : ℝ)) ≤ 1)
    {x y : ℝ} (hx : E - r₀ / 4 ≤ x) (hxy : x ≤ y) (hy : y ≤ E + r₀ / 4) (p : Fin r → ℂ) :
    |∑ i ∈ Finset.univ.filter (fun i => freshEigenvalue H i ∈ Icc x y),
        (‖star p ⬝ᵥ frameArray V H i‖ ^ 2 -
          quadForm (freshGamma F s (freshEigenvalue H i)) (V *ᵥ p))| ≤
      intB4 c r₀ s₀ v₀ r * ((N : ℝ) * (N : ℝ) ^ (-(1 / 100 : ℝ)) * (K + 2)) * nsq p := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h := (N : ℝ) ^ (-(1 / 100 : ℝ)) with hhdef
  have hh : 0 < h := Real.rpow_pos_of_pos hNr _
  have hh1 : h ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  set w := V *ᵥ p with hw
  set lam : Fin N → ℝ := freshEigenvalue H with hlam
  set μ : Fin N → ℝ := fun i => Complex.normSq (star w ⬝ᵥ freshEigenvector H i) with hμ
  set φ : ℝ → ℝ := fun e => quadForm (freshGamma F s e) w with hφ
  set R := intR r₀ with hRdef
  have hR : 1 ≤ R := le_max_right _ _
  have hRr : r₀ ≤ R := le_max_left _ _
  have hyx : y - x ≤ R := by linarith
  have hp0 := nsq_nonneg p
  have hΓw : quadForm (freshGamma F c E) w = nsq p := quadForm_frame hV p
  have hwin : ∀ e ∈ Icc x y, |e - E| ≤ r₀ / 4 := fun e he => by
    rw [abs_le]; constructor <;> linarith [he.1, he.2]
  set C' := dysonGammaConst c r₀ s₀ v₀
  set Cs := dysonShiftConst c r₀ s₀ v₀
  have hC'0 : 0 ≤ C' := dysonGammaConst_nonneg hK
  have hCs0 : 0 ≤ Cs := dysonShiftConst_nonneg hK
  set B₁ := intB1 c r₀ s₀ v₀ r
  set B₂ := intB2 v₀
  set B₃ := intB3 c r₀ s₀ v₀ r
  have hKc0 := (gammaCompConst_pos hK).le
  have hB₁ : 0 ≤ B₁ := by simp only [B₁, intB1]; positivity
  have hB₂ : 0 ≤ B₂ := by simp only [B₂, intB2]; positivity
  have hB₃ : 0 ≤ B₃ := by simp only [B₃, intB3]; positivity
  -- the hypotheses of the abstract comparison
  have hφL : ∀ e ∈ Icc x y, ∀ e' ∈ Icc x y, |φ e - φ e'| ≤ (c * Cs * C' * nsq p) * |e - e'| := by
    intro e he e' he'
    have := phi_lipschitz hN hK hC hs (by linarith [hwin e he]) (by linarith [hwin e' he']) w
    rw [hΓw] at this
    calc |φ e - φ e'| ≤ c * Cs * C' * |e - e'| * nsq p := this
      _ = _ := by ring
  have hφc : ContinuousOn φ (Icc x y) :=
    (LipschitzOnWith.of_dist_le' (K := c * Cs * C' * nsq p) fun e he e' he' => by
      rw [Real.dist_eq, Real.dist_eq]; exact hφL e he e' he').continuousOn
  have hφb : ∀ e ∈ Icc x y, |φ e| ≤ c * C' * nsq p := by
    intro e he
    have h0 := quadForm_freshGamma_nonneg F (le_trans (by linarith) hs.1) e w
    rw [abs_of_nonneg h0]
    have := phi_le hN hK hC hs (by linarith [hwin e he]) w
    rwa [hΓw] at this
  have hL0 : 0 ≤ c * Cs * C' * nsq p := by positivity
  have hab1 : ∀ e ∈ Icc x y,
      |(N : ℝ) * (∑ i, μ i * pk h (lam i - e)) - φ e * ∑ i, pk h (lam i - e)| ≤
        N * B₃ * h * nsq p := by
    intro e he
    have := h3 e (by linarith [hwin e he]) p
    rwa [rIm_eq_sum hHs w e hh, rTr_eq_sum hHs e hh] at this
  have hdy : ∀ (ν : Fin N → ℝ) (B : ℝ) (e : ℝ),
      (∀ η, h ≤ η → η ≤ 1 → ∑ i, ν i * pk η (lam i - e) ≤ B) →
      ∑ i, ν i * dyW h K (lam i - e) ≤ h * ((K + 2) * B) := by
    intro ν B e hν
    rw [sum_dyW_eq]
    apply mul_le_mul_of_nonneg_left _ hh.le
    have hk : ∀ k ∈ Finset.range (K + 1), ∑ i, ν i * pk (2 ^ k * h) (lam i - e) ≤ B := by
      intro k hk
      have hk' : k ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      apply hν
      · exact le_mul_of_one_le_left hh.le (one_le_pow₀ (by norm_num))
      · exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk') hh.le) hK2
    have h1' := hν 1 hh1 le_rfl
    have := Finset.sum_le_sum hk
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    push_cast at this ⊢
    linarith
  have hBW : ∀ e ∈ Icc x y,
      ∑ i ∈ Finset.univ.filter (fun i => lam i ∈ Icc x y), dyW h K (lam i - e) ≤
        h * ((K + 2) * (N * B₂)) := by
    intro e he
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => dyW_nonneg hh.le K _).trans ?_
    have := hdy (fun _ => 1) (N * B₂) e fun η hη hη1 => by
      have := h2 e (by linarith [hwin e he]) η hη hη1
      rw [rTr_eq_sum hHs e (lt_of_lt_of_le hh hη)] at this
      simpa using this
    simpa using this
  have hSμ : ∑ i, μ i * (dyW h K (lam i - x) + dyW h K (lam i - y)) ≤
      2 * (h * ((K + 2) * (B₁ * nsq p))) := by
    have hμx := hdy μ (B₁ * nsq p) x fun η hη hη1 => by
      have := h1 x (by linarith [hwin x ⟨le_rfl, hxy⟩]) η hη hη1 p
      rwa [rIm_eq_sum hHs w x (lt_of_lt_of_le hh hη)] at this
    have hμy := hdy μ (B₁ * nsq p) y fun η hη hη1 => by
      have := h1 y (by linarith [hwin y ⟨hxy, le_rfl⟩]) η hη hη1 p
      rwa [rIm_eq_sum hHs w y (lt_of_lt_of_le hh hη)] at this
    simp only [mul_add, Finset.sum_add_distrib]
    linarith
  have hS1 : ∑ i, (dyW h K (lam i - x) + dyW h K (lam i - y)) ≤
      2 * (h * ((K + 2) * (N * B₂))) := by
    have hx' := hdy (fun _ => 1) (N * B₂) x fun η hη hη1 => by
      have := h2 x (by linarith [hwin x ⟨le_rfl, hxy⟩]) η hη hη1
      rw [rTr_eq_sum hHs x (lt_of_lt_of_le hh hη)] at this
      simpa using this
    have hy' := hdy (fun _ => 1) (N * B₂) y fun η hη hη1 => by
      have := h2 y (by linarith [hwin y ⟨hxy, le_rfl⟩]) η hη hη1
      rw [rTr_eq_sum hHs y (lt_of_lt_of_le hh hη)] at this
      simpa using this
    simp only [one_mul] at hx' hy'
    rw [Finset.sum_add_distrib]
    linarith
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => Complex.normSq_nonneg _
  have hmain := interval_sum_compare hh hR hK1 hxy hyx lam μ hμ0 hNr.le hφc hL0 hφb hφL hab1 hBW
  -- rewrite the target
  have htarget : ∑ i ∈ Finset.univ.filter (fun i => freshEigenvalue H i ∈ Icc x y),
      (‖star p ⬝ᵥ frameArray V H i‖ ^ 2 - quadForm (freshGamma F s (freshEigenvalue H i)) (V *ᵥ p)) =
      (N : ℝ) * (∑ i ∈ Finset.univ.filter (fun i => lam i ∈ Icc x y), μ i) -
        ∑ i ∈ Finset.univ.filter (fun i => lam i ∈ Icc x y), φ (lam i) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_star_frameArray_sq]
  rw [htarget]
  refine hmain.trans ?_
  -- arithmetic
  have hk1 : (1 : ℝ) ≤ K + 2 := by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
  have := interval_det_arith hR hC'0 hCs0 hB₂ hB₃ hc0.le hNr.le hh.le hk1 hp0
    (sub_nonneg.2 hxy) hyx hSμ hS1
  refine this.trans (le_of_eq ?_)
  simp only [intB4, R, B₁, B₂, B₃, C', Cs]
  ring

end BlockBand.Critical.RelativeVectors
