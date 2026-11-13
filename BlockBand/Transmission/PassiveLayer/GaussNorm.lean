module

public import BlockBand.Transmission.PassiveLayer.Net
public import BlockBand.Transmission.PassiveLayer.GaussLinear
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# Uniform operator-norm moments of Gaussian matrices (ε-net argument)

Law: `gaussPi κ v = Π_k N(0,v)`. A random matrix `G : (κ → ℝ) → Matrix (Fin n) (Fin n) ℂ` is
`IsGaussMatrix v s G` when every bilinear form `y*G(ρ)x` is a linear form `Σ ρ_k c_k` with
`vΣ|c_k|² ≤ s‖x‖²‖y‖²`.

* `norm_le_of_net`: `‖M‖ ≤ 2 max_{u,w∈N} |w*Mu|` for a `1/4`-net `N` of the unit ball
  (`exists_vec_net`, at most `9^{2n}` points).
* `measure_norm_gt`: `P(‖G‖ > 2r) ≤ 4·9^{4n} exp(-r²/(4s))` (union bound and
  `measure_complex_linear_gt`).
* `measure_norm_gt_uniform`: for `s = τ/n`, `n ≥ 1`, `r² ≥ 32τ log 9`:
  `P(‖G‖ > 2r) ≤ 4 exp(-r²/(8τ))`, uniformly in `n`.
* `lintegral_norm_rpow_le`: for `s = τ/n` and each `p ≥ 1`, `E‖G‖^p ≤ C(τ,p)`, uniformly in
  `n ≥ 1`, the coordinate type, `v` and `G` (layer-cake formula).

Norms: Euclidean operator norm (`Matrix.Norms.L2Operator`); `vecNorm` on vectors.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.PassiveLayer

open MeasureTheory ProbabilityTheory Matrix
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped ENNReal NNReal Matrix.Norms.L2Operator

variable {n : ℕ}

theorem vecNorm_smul (c : ℂ) (x : Fin n → ℂ) : vecNorm (c • x) = ‖c‖ * vecNorm x := by
  rw [vecNorm_eq, vecNorm_eq, WithLp.toLp_smul, norm_smul]

theorem vecNorm_eq_zero {x : Fin n → ℂ} (h : vecNorm x = 0) : x = 0 := by
  rw [vecNorm_eq, norm_eq_zero] at h
  simpa using congrArg WithLp.ofLp h

/-- A `1/4`-net of the unit ball of `ℂⁿ` in plain coordinates. -/
theorem exists_vec_net (n : ℕ) : ∃ N : Finset (Fin n → ℂ), N.card ≤ 9 ^ (2 * n) ∧
    (∀ u ∈ N, vecNorm u ≤ 1) ∧ ∀ x : Fin n → ℂ, vecNorm x ≤ 1 →
      ∃ u ∈ N, vecNorm (x - u) ≤ 1 / 4 := by
  obtain ⟨N, hc, hN, hcov⟩ := exists_quarter_net n
  refine ⟨N.image WithLp.ofLp, Finset.card_image_le.trans hc, ?_, ?_⟩
  · intro u hu
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
    rw [vecNorm_eq]; simpa using hN u' hu'
  · intro x hx
    obtain ⟨u, hu, hxu⟩ := hcov (WithLp.toLp 2 x) (by rwa [vecNorm_eq] at hx)
    refine ⟨u.ofLp, Finset.mem_image_of_mem _ hu, ?_⟩
    rw [vecNorm_eq]; simpa using hxu

/-- `‖M‖ ≤ 2 max_{u,w ∈ N} |w*Mu|` for a `1/4`-net `N` of the unit ball. -/
theorem norm_le_of_net (N : Finset (Fin n → ℂ)) (hN : ∀ u ∈ N, vecNorm u ≤ 1)
    (hcov : ∀ x : Fin n → ℂ, vecNorm x ≤ 1 → ∃ u ∈ N, vecNorm (x - u) ≤ 1 / 4)
    (M : Matrix (Fin n) (Fin n) ℂ) {m : ℝ} (hm : 0 ≤ m)
    (hM : ∀ u ∈ N, ∀ w ∈ N, ‖star w ⬝ᵥ (M *ᵥ u)‖ ≤ m) : ‖M‖ ≤ 2 * m := by
  have hM0 := norm_nonneg M
  have hunit : ∀ x : Fin n → ℂ, vecNorm x ≤ 1 → vecNorm (M *ᵥ x) ≤ m + ‖M‖ / 2 := by
    intro x hx
    set y := M *ᵥ x
    rcases (vecNorm_nonneg y).eq_or_lt with hy | hy
    · rw [← hy]; positivity
    set e : Fin n → ℂ := ((vecNorm y)⁻¹ : ℂ) • y
    have he : vecNorm e = 1 := by
      rw [vecNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hy.le,
        inv_mul_cancel₀ hy.ne']
    have hey : star e ⬝ᵥ y = (vecNorm y : ℂ) := by
      rw [star_smul, smul_dotProduct, star_self_eq]
      simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
      push_cast
      field_simp
    obtain ⟨u, hu, hxu⟩ := hcov x hx
    obtain ⟨w, hw, hew⟩ := hcov e he.le
    have hid : star e ⬝ᵥ (M *ᵥ x) = star w ⬝ᵥ (M *ᵥ u) + star (e - w) ⬝ᵥ (M *ᵥ x) +
        star w ⬝ᵥ (M *ᵥ (x - u)) := by
      simp only [star_sub, sub_dotProduct, mulVec_sub, dotProduct_sub]; ring
    have h1 := hM u hu w hw
    have h2 : ‖star (e - w) ⬝ᵥ (M *ᵥ x)‖ ≤ 1 / 4 * ‖M‖ := by
      refine (norm_star_dotProduct_le _ _).trans ?_
      have := vecNorm_mulVec_le M x
      calc vecNorm (e - w) * vecNorm (M *ᵥ x) ≤ 1 / 4 * (‖M‖ * 1) := by
            gcongr
            · exact this.trans (by gcongr)
        _ = _ := by ring
    have h3 : ‖star w ⬝ᵥ (M *ᵥ (x - u))‖ ≤ ‖M‖ * (1 / 4) := by
      refine (norm_star_dotProduct_le _ _).trans ?_
      have := vecNorm_mulVec_le M (x - u)
      calc vecNorm w * vecNorm (M *ᵥ (x - u)) ≤ 1 * (‖M‖ * (1 / 4)) :=
            mul_le_mul (hN w hw) (this.trans (by gcongr)) (vecNorm_nonneg _) zero_le_one
        _ = _ := by ring
    have : vecNorm y = ‖star e ⬝ᵥ (M *ᵥ x)‖ := by
      rw [hey, Complex.norm_real, Real.norm_of_nonneg hy.le]
    rw [this, hid]
    calc _ ≤ ‖star w ⬝ᵥ (M *ᵥ u)‖ + ‖star (e - w) ⬝ᵥ (M *ᵥ x)‖ +
          ‖star w ⬝ᵥ (M *ᵥ (x - u))‖ := norm_add₃_le
      _ ≤ _ := by linarith
  have hall : ∀ x : Fin n → ℂ, vecNorm (M *ᵥ x) ≤ (m + ‖M‖ / 2) * vecNorm x := by
    intro x
    rcases (vecNorm_nonneg x).eq_or_lt with hx | hx
    · rw [vecNorm_eq_zero hx.symm, mulVec_zero]
      simp [vecNorm]
    · have hx1 : vecNorm (((vecNorm x)⁻¹ : ℂ) • x) = 1 := by
        rw [vecNorm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hx.le,
          inv_mul_cancel₀ hx.ne']
      have := hunit _ hx1.le
      rw [mulVec_smul, vecNorm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hx.le] at this
      rwa [inv_mul_le_iff₀ hx, mul_comm] at this
  have := opNorm_le_of_vec M (by positivity) hall
  linarith

/-- `G` is a centered Gaussian matrix in the coordinates `ρ ~ Π N(0,v)` whose bilinear forms
have variance proxy `s‖x‖²‖y‖²`. -/
def IsGaussMatrix {κ : Type*} [Fintype κ] (v : ℝ≥0) (s : ℝ)
    (G : (κ → ℝ) → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x y : Fin n → ℂ, ∃ c : κ → ℂ, (∀ ρ, star y ⬝ᵥ (G ρ *ᵥ x) = ∑ k, (ρ k : ℂ) * c k) ∧
    (v : ℝ) * ∑ k, ‖c k‖ ^ 2 ≤ s * vecNorm x ^ 2 * vecNorm y ^ 2

theorem measure_norm_gt {κ : Type*} [Fintype κ] {v : ℝ≥0} {s : ℝ} (hs : 0 < s)
    {G : (κ → ℝ) → Matrix (Fin n) (Fin n) ℂ} (hG : IsGaussMatrix v s G) {r : ℝ} (hr : 0 ≤ r) :
    gaussPi κ v {ρ | 2 * r < ‖G ρ‖} ≤
      ((9 ^ (2 * n)) ^ 2 * 4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(r ^ 2 / (4 * s)))) := by
  obtain ⟨N, hcard, hN, hcov⟩ := exists_vec_net n
  have hsub : {ρ | 2 * r < ‖G ρ‖} ⊆
      ⋃ u ∈ N, ⋃ w ∈ N, {ρ | r < ‖star w ⬝ᵥ (G ρ *ᵥ u)‖} := by
    intro ρ hρ
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt] at hcon
    have := norm_le_of_net N hN hcov (G ρ) hr fun u hu w hw => hcon u hu w hw
    exact absurd hρ (not_lt.mpr this)
  have hterm : ∀ u ∈ N, ∀ w ∈ N, gaussPi κ v {ρ | r < ‖star w ⬝ᵥ (G ρ *ᵥ u)‖} ≤
      4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / (4 * s)))) := by
    intro u hu w hw
    obtain ⟨c, hc, hvc⟩ := hG u w
    have hset : {ρ | r < ‖star w ⬝ᵥ (G ρ *ᵥ u)‖} = {ρ | r < ‖∑ k, (ρ k : ℂ) * c k‖} := by
      ext ρ; simp [hc]
    rw [hset]
    refine measure_complex_linear_gt v c hs (hvc.trans ?_) hr
    have h1 := hN u hu; have h2 := hN w hw
    have h1' : vecNorm u ^ 2 ≤ 1 := by nlinarith [vecNorm_nonneg u]
    have h2' : vecNorm w ^ 2 ≤ 1 := by nlinarith [vecNorm_nonneg w]
    calc s * vecNorm u ^ 2 * vecNorm w ^ 2 ≤ s * 1 * 1 := by gcongr
      _ = s := by ring
  calc gaussPi κ v {ρ | 2 * r < ‖G ρ‖}
      ≤ gaussPi κ v (⋃ u ∈ N, ⋃ w ∈ N, {ρ | r < ‖star w ⬝ᵥ (G ρ *ᵥ u)‖}) := measure_mono hsub
    _ ≤ ∑ u ∈ N, gaussPi κ v (⋃ w ∈ N, {ρ | r < ‖star w ⬝ᵥ (G ρ *ᵥ u)‖}) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ N, ∑ w ∈ N, gaussPi κ v {ρ | r < ‖star w ⬝ᵥ (G ρ *ᵥ u)‖} :=
        Finset.sum_le_sum fun u _ => measure_biUnion_finset_le _ _
    _ ≤ ∑ u ∈ N, ∑ w ∈ N, 4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / (4 * s)))) :=
        Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun w hw => hterm u hu w hw
    _ = (N.card : ℝ≥0∞) ^ 2 * 4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / (4 * s)))) := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
        gcongr
        exact_mod_cast hcard

theorem measure_norm_gt_uniform {κ : Type*} [Fintype κ] {v : ℝ≥0} {τ : ℝ} (hτ : 0 < τ)
    (hn : 1 ≤ n) {G : (κ → ℝ) → Matrix (Fin n) (Fin n) ℂ} (hG : IsGaussMatrix v (τ / n) G)
    {r : ℝ} (hr : 0 ≤ r) (hr2 : 32 * τ * Real.log 9 ≤ r ^ 2) :
    gaussPi κ v {ρ | 2 * r < ‖G ρ‖} ≤ 4 * ENNReal.ofReal (Real.exp (-(r ^ 2 / (8 * τ)))) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : 0 < τ / n := by positivity
  have heq : ((9 ^ (2 * n)) ^ 2 * 4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(r ^ 2 / (4 * (τ / n))))) =
      4 * ENNReal.ofReal ((9 : ℝ) ^ (4 * n) * Real.exp (-(r ^ 2 / (4 * (τ / n))))) := by
    rw [ENNReal.ofReal_mul (by positivity), ← mul_assoc]
    congr 1
    rw [mul_comm (_ ^ 2 : ℝ≥0∞) 4, ENNReal.ofReal_pow (by norm_num), ← pow_mul]
    congr 2
    · simp
    · ring
  refine (measure_norm_gt hs hG hr).trans (heq.le.trans ?_)
  gcongr
  have h9 : (9 : ℝ) ^ (4 * n) = Real.exp (4 * n * Real.log 9) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]; push_cast; ring_nf
  rw [h9, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have e1 : r ^ 2 / (4 * (τ / n)) = n * (r ^ 2 / (4 * τ)) := by field_simp
  have e2 : r ^ 2 / (4 * τ) = 2 * (r ^ 2 / (8 * τ)) := by field_simp; ring
  have e3 : 4 * Real.log 9 ≤ r ^ 2 / (8 * τ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  rw [e1, e2]
  have h0 : 0 ≤ r ^ 2 / (8 * τ) := by positivity
  nlinarith

/-- **Uniform operator-norm moments of Gaussian matrices**: for variance proxy `τ/n`, every
`p ≥ 1` has a constant `C` independent of `n ≥ 1`, the coordinates and `G`. -/
theorem lintegral_norm_rpow_le {τ : ℝ} (hτ : 0 < τ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ (κ : Type) [Fintype κ] (v : ℝ≥0)
      (G : (κ → ℝ) → Matrix (Fin n) (Fin n) ℂ), Measurable G → IsGaussMatrix v (τ / n) G →
        ∫⁻ ρ, ‖G ρ‖ₑ ^ p ∂gaussPi κ v ≤ ENNReal.ofReal C := by
  set r₀ := Real.sqrt (32 * τ * Real.log 9)
  set b := 1 / (32 * τ)
  set K := 4 * Real.exp (b * (2 * r₀) ^ 2)
  have hb : 0 < b := by positivity
  have hint : IntegrableOn (fun t : ℝ => K * (t ^ (p - 1) * Real.exp (-b * t ^ 2))) (Set.Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq hb (by linarith)).const_mul K
  refine ⟨p * ∫ t in Set.Ioi 0, K * (t ^ (p - 1) * Real.exp (-b * t ^ 2)), ?_⟩
  intro n hn κ _ v G hGm hG
  have hp0 : 0 < p := by linarith
  have htail : ∀ t : ℝ, 0 < t → gaussPi κ v {ρ | t < ‖G ρ‖} ≤
      ENNReal.ofReal (K * Real.exp (-b * t ^ 2)) := by
    intro t ht
    by_cases h : t ≤ 2 * r₀
    · refine prob_le_one.trans ?_
      rw [ENNReal.one_le_ofReal]
      have : b * t ^ 2 ≤ b * (2 * r₀) ^ 2 := by gcongr
      have : 1 ≤ Real.exp (b * (2 * r₀) ^ 2 + -b * t ^ 2) := Real.one_le_exp (by linarith)
      rw [Real.exp_add] at this
      linarith [Real.exp_pos (-b * t ^ 2), Real.exp_pos (b * (2 * r₀) ^ 2)]
    · push Not at h
      have hr0 : 0 ≤ r₀ := Real.sqrt_nonneg _
      have hr : 0 ≤ t / 2 := by positivity
      have hr2 : 32 * τ * Real.log 9 ≤ (t / 2) ^ 2 := by
        have : r₀ ^ 2 = 32 * τ * Real.log 9 :=
          Real.sq_sqrt (by have := Real.log_pos (show (1 : ℝ) < 9 by norm_num); positivity)
        rw [← this]; nlinarith
      have := measure_norm_gt_uniform hτ hn hG hr hr2
      rw [show 2 * (t / 2) = t by ring] at this
      refine this.trans ?_
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have e : -((t / 2) ^ 2 / (8 * τ)) = -b * t ^ 2 := by simp only [b]; field_simp; ring
      rw [e]
      have : (4 : ℝ) ≤ K := by
        have := Real.one_le_exp (show 0 ≤ b * (2 * r₀) ^ 2 by positivity)
        simp only [K]; linarith
      nlinarith [Real.exp_pos (-b * t ^ 2)]
  have hlc := lintegral_rpow_eq_lintegral_meas_lt_mul (gaussPi κ v)
    (f := fun ρ => ‖G ρ‖) (ae_of_all _ fun _ => norm_nonneg _)
    (continuous_norm.measurable.comp hGm).aemeasurable hp0
  have hconv : ∫⁻ ρ, ‖G ρ‖ₑ ^ p ∂gaussPi κ v = ∫⁻ ρ, ENNReal.ofReal (‖G ρ‖ ^ p) ∂gaussPi κ v := by
    congr 1; ext ρ
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
  rw [hconv, hlc, ENNReal.ofReal_mul hp0.le]
  gcongr
  rw [ofReal_integral_eq_lintegral_ofReal hint ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun t (ht : 0 < t) => by
      have := Real.rpow_nonneg ht.le (p - 1)
      have : 0 ≤ K := by positivity
      positivity))]
  refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
  rw [show K * (t ^ (p - 1) * Real.exp (-b * t ^ 2)) =
      (K * Real.exp (-b * t ^ 2)) * t ^ (p - 1) by ring,
    ENNReal.ofReal_mul (by positivity)]
  gcongr
  exact htail t ht

end BlockBand.Transmission.PassiveLayer
