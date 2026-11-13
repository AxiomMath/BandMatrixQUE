module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The interval kernel at height `h`

Deterministic real analysis for the middle line of the interval bound.

* `pk η d = η/(d² + η²)` (`= Im (λ - e - iη)⁻¹` for `d = λ - e`); `kap h x y λ =
  π⁻¹(arctan((y-λ)/h) - arctan((x-λ)/h))`, and `integral_pk`: `∫_x^y pk h (λ - e) de = π kap`.
  So integrating `Im w^*G(e + ih)w` over the bottom side `[x, y]` of the rectangle gives the
  spectral sum `Σ_i |w^*u_i|² kap(λ_i)` exactly (the vertical and upper sides are not needed).
* `dyW h K d = h (Σ_{k ≤ K} pk (2^k h) d + pk 1 d)`: the dyadic endpoint weight. Its spectral sums
  are `h Σ_k Im w^*G(e + i2^kh)w + h Im w^*G(e + i)w`, controlled by the coarse law at the heights
  `2^kh ≤ 1` and `1` (positivity bounds each endpoint strip by `CNh`, with the logarithmic number
  `K + 2` of heights).
* `le_dyW`: every `ψ` with `ψ ≤ 1/2` and `ψ ≤ h/|d|` satisfies `ψ ≤ (2R² + 4) dyW h K d` on
  `|d| ≤ R` (`1 ≤ R`, `1 < 2^{K+1}h`).
* `indicator_sub_kap_le`: `|1_{[x,y]}(λ) - kap(λ)| ≤ (2R² + 4)(dyW(λ - x) + dyW(λ - y))` for all
  real `λ` when `y - x ≤ R` (inside the interval by the exact `arctan` identity, near outside by
  the same tail, far outside by the decay `kap ≤ (y - x)h/(π d²)`).
* `abs_mul_pk_le`: `|u| pk h u ≤ (2R² + 4) dyW h K u` on `|u| ≤ R` (the Lipschitz error of a
  smooth weight under the kernel).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open Real Set

/-- `pk η d = η/(d² + η²)`. -/
def pk (η d : ℝ) : ℝ := η / (d ^ 2 + η ^ 2)

/-- The interval kernel `kap h x y λ = π⁻¹(arctan((y-λ)/h) - arctan((x-λ)/h))`. -/
def kap (h x y lam : ℝ) : ℝ := (arctan ((y - lam) / h) - arctan ((x - lam) / h)) / π

/-- The endpoint tail `θ(d) = 1/2 - π⁻¹ arctan(|d|/h)`. -/
def kTail (h d : ℝ) : ℝ := 1 / 2 - arctan (|d| / h) / π

/-- The dyadic endpoint weight `h (Σ_{k ≤ K} pk (2^k h) d + pk 1 d)`. -/
def dyW (h : ℝ) (K : ℕ) (d : ℝ) : ℝ :=
  h * (∑ k ∈ Finset.range (K + 1), pk (2 ^ k * h) d + pk 1 d)

theorem pk_nonneg {η : ℝ} (hη : 0 ≤ η) (d : ℝ) : 0 ≤ pk η d := by
  unfold pk; positivity

theorem pk_neg (η d : ℝ) : pk η (-d) = pk η d := by unfold pk; ring

theorem dyW_nonneg {h : ℝ} (hh : 0 ≤ h) (K : ℕ) (d : ℝ) : 0 ≤ dyW h K d := by
  unfold dyW
  have : 0 ≤ ∑ k ∈ Finset.range (K + 1), pk (2 ^ k * h) d :=
    Finset.sum_nonneg fun k _ => pk_nonneg (by positivity) d
  have := pk_nonneg zero_le_one d
  positivity

theorem dyW_neg (h : ℝ) (K : ℕ) (d : ℝ) : dyW h K (-d) = dyW h K d := by
  unfold dyW; simp only [pk_neg]

theorem continuous_pk {η : ℝ} (hη : 0 < η) : Continuous (pk η) := by
  unfold pk
  refine continuous_const.div ((continuous_pow 2).add continuous_const) fun d => ?_
  positivity

/-- `∫_x^y pk h (λ - e) de = arctan((y-λ)/h) - arctan((x-λ)/h)`. -/
theorem integral_pk {h : ℝ} (hh : 0 < h) (lam x y : ℝ) :
    ∫ e in x..y, pk h (lam - e) = arctan ((y - lam) / h) - arctan ((x - lam) / h) := by
  have hderiv : ∀ e : ℝ, HasDerivAt (fun e => arctan ((e - lam) / h)) (pk h (lam - e)) e := by
    intro e
    have h1 : HasDerivAt (fun e : ℝ => (e - lam) / h) (1 / h) e := by
      simpa using ((hasDerivAt_id e).sub_const lam).div_const h
    refine ((hasDerivAt_arctan _).comp e h1).congr_deriv ?_
    unfold pk
    have h4 : 0 < (lam - e) ^ 2 + h ^ 2 := by positivity
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun e _ => hderiv e)]
  exact ((continuous_pk hh).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _

theorem kap_eq_integral {h : ℝ} (hh : 0 < h) (x y lam : ℝ) :
    kap h x y lam = (∫ e in x..y, pk h (lam - e)) / π := by
  rw [integral_pk hh]; rfl

theorem kap_nonneg {h : ℝ} (hh : 0 < h) {x y : ℝ} (hxy : x ≤ y) (lam : ℝ) : 0 ≤ kap h x y lam := by
  unfold kap
  apply div_nonneg _ pi_pos.le
  rw [sub_nonneg]
  exact arctan_mono (div_le_div_of_nonneg_right (by linarith) hh.le)

theorem kTail_le_half {h : ℝ} (hh : 0 < h) (d : ℝ) : kTail h d ≤ 1 / 2 := by
  unfold kTail
  have : 0 ≤ arctan (|d| / h) := arctan_nonneg.2 (by positivity)
  have := div_nonneg this pi_pos.le
  linarith

theorem kTail_le {h : ℝ} (hh : 0 < h) {d : ℝ} (hd : d ≠ 0) : kTail h d ≤ h / |d| := by
  have hd' : 0 < |d| := abs_pos.2 hd
  have e : kTail h d = arctan ((|d| / h)⁻¹) / π := by
    rw [arctan_inv_of_pos (by positivity)]
    unfold kTail
    field_simp
  rw [e, inv_div]
  have h1 : arctan (h / |d|) ≤ h / |d| := arctan_le_self (by positivity)
  have h2 : 0 ≤ h / |d| := by positivity
  rw [div_le_iff₀ pi_pos]
  have : h / |d| ≤ h / |d| * π := le_mul_of_one_le_right h2 (by linarith [two_le_pi])
  linarith

theorem kTail_neg (h d : ℝ) : kTail h (-d) = kTail h d := by unfold kTail; rw [abs_neg]

/-- `arctan(t/h) = π(1/2 - θ(t))` for `t ≥ 0`. -/
theorem arctan_eq_of_nonneg {h t : ℝ} (ht : 0 ≤ t) : arctan (t / h) = π * (1 / 2 - kTail h t) := by
  unfold kTail
  rw [abs_of_nonneg ht]
  field_simp
  ring

/-- `arctan(t/h) = -π(1/2 - θ(t))` for `t ≤ 0`. -/
theorem arctan_eq_of_nonpos {h t : ℝ} (ht : t ≤ 0) :
    arctan (t / h) = -(π * (1 / 2 - kTail h t)) := by
  have := arctan_eq_of_nonneg (h := h) (neg_nonneg.2 ht)
  rw [kTail_neg, neg_div, arctan_neg] at this
  linarith

/-- **The generic dyadic bound.** -/
theorem le_dyW {h R : ℝ} (hh : 0 < h) (hR : 1 ≤ R) {K : ℕ} (hK : 1 < 2 ^ (K + 1) * h)
    {d ψ : ℝ} (hd : |d| ≤ R) (hψ1 : ψ ≤ 1 / 2) (hψ2 : d ≠ 0 → ψ ≤ h / |d|) :
    ψ ≤ (2 * R ^ 2 + 4) * dyW h K d := by
  have hW0 := dyW_nonneg hh.le K d
  have hsum0 : ∀ k ∈ Finset.range (K + 1), 0 ≤ pk (2 ^ k * h) d :=
    fun k _ => pk_nonneg (by positivity) d
  have hterm : ∀ k ∈ Finset.range (K + 1), h * pk (2 ^ k * h) d ≤ dyW h K d := by
    intro k hk
    unfold dyW
    have h1 := Finset.single_le_sum hsum0 hk
    have h2 := pk_nonneg zero_le_one d
    nlinarith
  have hC : (1 : ℝ) ≤ 2 * R ^ 2 + 4 := by nlinarith
  rcases le_or_gt |d| h with h1 | h1
  · -- |d| ≤ h
    have := hterm 0 (by simp)
    simp only [pow_zero, one_mul] at this
    have hpk : 1 / 2 ≤ h * pk h d := by
      unfold pk
      have hd2 : d ^ 2 ≤ h ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg d) h1 2
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hd0 : d ≠ 0 := fun h0 => by rw [h0, abs_zero] at h1; linarith
  have hdpos : 0 < |d| := abs_pos.2 hd0
  have hψ := hψ2 hd0
  by_cases hex : ∃ k, k ≤ K ∧ |d| ≤ 2 ^ k * h
  · -- dyadic shell
    classical
    let P : ℕ → Prop := fun k => |d| ≤ 2 ^ k * h
    have hP : ∃ k, P k := ⟨hex.choose, hex.choose_spec.2⟩
    set k := Nat.find hP with hk
    have hkP : P k := Nat.find_spec hP
    have hkK : k ≤ K := (Nat.find_min' hP hex.choose_spec.2).trans hex.choose_spec.1
    have hk0 : k ≠ 0 := by
      intro h0
      have := hkP
      simp only [P, h0, pow_zero, one_mul] at this
      linarith
    have hprev : 2 ^ k * h < 2 * |d| := by
      have hlt : k - 1 < k := Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos
      have hn := Nat.find_min hP hlt
      simp only [P, not_le] at hn
      have e : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e]; nlinarith
    set η := 2 ^ k * h with hη
    have hηpos : 0 < η := by positivity
    have hterm' := hterm k (Finset.mem_range.2 (by omega))
    have hlow : h / (4 * |d|) ≤ h * pk η d := by
      unfold pk
      have hd2 : d ^ 2 ≤ η ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg d) hkP 2
      rw [div_le_iff₀ (by positivity), mul_div_assoc', div_mul_eq_mul_div,
        le_div_iff₀ (by positivity)]
      have h3 : d ^ 2 + η ^ 2 ≤ η * (4 * |d|) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 hh.le]
    have : h / |d| = 4 * (h / (4 * |d|)) := by field_simp
    nlinarith
  · -- far: |d| > 2^K h > 1/2
    push Not at hex
    have hfar := hex K le_rfl
    have hd2 : 1 < 2 * |d| := by
      have : (2 : ℝ) ^ (K + 1) * h = 2 * (2 ^ K * h) := by ring
      linarith
    have hψ' : ψ ≤ 2 * h := by
      refine hψ.trans ?_
      rw [div_le_iff₀ hdpos]; nlinarith
    have hlow : h / (R ^ 2 + 1) ≤ dyW h K d := by
      unfold dyW
      have hs := Finset.sum_nonneg hsum0
      have hp : 1 / (R ^ 2 + 1) ≤ pk 1 d := by
        unfold pk
        have : d ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg d) hd 2
        rw [one_pow]
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      have : h / (R ^ 2 + 1) = h * (1 / (R ^ 2 + 1)) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left (by linarith) hh.le
    have : 2 * h = 2 * (R ^ 2 + 1) * (h / (R ^ 2 + 1)) := by field_simp
    nlinarith

/-- **The interval-kernel error.** -/
theorem indicator_sub_kap_le {h R : ℝ} (hh : 0 < h) (hR : 1 ≤ R) {K : ℕ}
    (hK : 1 < 2 ^ (K + 1) * h) {x y : ℝ} (hxy : x ≤ y) (hyx : y - x ≤ R) (lam : ℝ) :
    |(if lam ∈ Icc x y then (1 : ℝ) else 0) - kap h x y lam| ≤
      (2 * R ^ 2 + 4) * (dyW h K (lam - x) + dyW h K (lam - y)) := by
  have hW1 := dyW_nonneg hh.le K (lam - x)
  have hW2 := dyW_nonneg hh.le K (lam - y)
  have hC0 : 0 ≤ 2 * R ^ 2 + 4 := by positivity
  have hθ : ∀ d, |d| ≤ R → kTail h d ≤ (2 * R ^ 2 + 4) * dyW h K d := fun d hd =>
    le_dyW hh hR hK hd (kTail_le_half hh d) (kTail_le hh)
  have hk0 := kap_nonneg hh hxy lam
  -- the far decay
  have hdecay : ∀ D : ℝ, 0 < D → (∀ e ∈ Icc x y, D ≤ |lam - e|) →
      kap h x y lam ≤ (y - x) * h / D ^ 2 := by
    intro D hD hDe
    rw [kap_eq_integral hh, div_le_iff₀ pi_pos]
    have hb : ∫ e in x..y, pk h (lam - e) ≤ ∫ _e in x..y, h / D ^ 2 := by
      apply intervalIntegral.integral_mono_on hxy
      · exact ((continuous_pk hh).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
      · exact intervalIntegrable_const
      · intro e he
        unfold pk
        have h1 : D ^ 2 ≤ (lam - e) ^ 2 := by
          rw [← sq_abs (lam - e)]; exact pow_le_pow_left₀ hD.le (hDe e he) 2
        exact div_le_div_of_nonneg_left hh.le (by positivity) (by nlinarith)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hb
    have : (y - x) * (h / D ^ 2) ≤ (y - x) * h / D ^ 2 * π := by
      rw [← mul_div_assoc]
      exact le_mul_of_one_le_right (by have := sub_nonneg.2 hxy; positivity)
        (by linarith [two_le_pi])
    linarith
  have hWfar : ∀ d, R < |d| → h / (2 * d ^ 2) ≤ dyW h K d := by
    intro d hd
    unfold dyW
    have hs := Finset.sum_nonneg fun k (_ : k ∈ Finset.range (K + 1)) =>
      pk_nonneg (η := 2 ^ k * h) (by positivity) d
    have hd1 : 1 ≤ d ^ 2 := by rw [← sq_abs]; nlinarith
    have hp : 1 / (2 * d ^ 2) ≤ pk 1 d := by
      unfold pk
      rw [one_pow]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have : h / (2 * d ^ 2) = h * (1 / (2 * d ^ 2)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hh.le
  have hT0 : ∀ d, 0 ≤ kTail h d := fun d => by
    unfold kTail; have := arctan_lt_pi_div_two (|d| / h)
    rw [sub_nonneg, div_le_iff₀ pi_pos]; linarith
  by_cases hin : lam ∈ Icc x y
  · simp only [hin, ↓reduceIte]
    have e : 1 - kap h x y lam = kTail h (lam - x) + kTail h (lam - y) := by
      unfold kap
      rw [arctan_eq_of_nonneg (by linarith [hin.2] : 0 ≤ y - lam),
        arctan_eq_of_nonpos (by linarith [hin.1] : x - lam ≤ 0)]
      rw [show lam - x = -(x - lam) by ring, kTail_neg, show lam - y = -(y - lam) by ring,
        kTail_neg]
      field_simp
      ring
    rw [e, abs_of_nonneg (add_nonneg (hT0 _) (hT0 _))]
    have h1 := hθ (lam - x) (by rw [abs_le]; constructor <;> linarith [hin.1, hin.2])
    have h2 := hθ (lam - y) (by rw [abs_le]; constructor <;> linarith [hin.1, hin.2])
    linarith
  · simp only [hin, ↓reduceIte, zero_sub, abs_neg, abs_of_nonneg hk0]
    simp only [mem_Icc, not_and_or, not_le] at hin
    rcases hin with hlt | hgt
    · -- λ < x
      have e : kap h x y lam = kTail h (lam - x) - kTail h (lam - y) := by
        unfold kap
        rw [arctan_eq_of_nonneg (by linarith : 0 ≤ y - lam),
          arctan_eq_of_nonneg (by linarith : 0 ≤ x - lam)]
        rw [show lam - x = -(x - lam) by ring, kTail_neg, show lam - y = -(y - lam) by ring,
          kTail_neg]
        field_simp
        ring
      have ht0 := hT0 (lam - y)
      rcases le_or_gt (x - lam) R with hn | hf
      · have := hθ (lam - x) (by rw [abs_le]; constructor <;> linarith)
        nlinarith
      · have hk := hdecay (x - lam) (by linarith) fun e he => by
          rw [abs_of_neg (by linarith [he.1])]; linarith [he.1]
        have hw := hWfar (lam - x) (by rw [abs_of_neg (by linarith)]; linarith)
        rw [show (lam - x) ^ 2 = (x - lam) ^ 2 by ring] at hw
        have hD : 0 < (x - lam) ^ 2 := by nlinarith
        have h3 : (y - x) * h / (x - lam) ^ 2 ≤ 2 * R * (h / (2 * (x - lam) ^ 2)) := by
          rw [mul_div_assoc', div_le_div_iff₀ hD (by positivity)]
          have : 0 ≤ h * (x - lam) ^ 2 := by positivity
          nlinarith
        nlinarith
    · -- λ > y
      have e : kap h x y lam = kTail h (lam - y) - kTail h (lam - x) := by
        unfold kap
        rw [arctan_eq_of_nonpos (by linarith : y - lam ≤ 0),
          arctan_eq_of_nonpos (by linarith : x - lam ≤ 0)]
        rw [show lam - x = -(x - lam) by ring, kTail_neg, show lam - y = -(y - lam) by ring,
          kTail_neg]
        field_simp
        ring
      have ht0 := hT0 (lam - x)
      rcases le_or_gt (lam - y) R with hn | hf
      · have := hθ (lam - y) (by rw [abs_le]; constructor <;> linarith)
        nlinarith
      · have hk := hdecay (lam - y) (by linarith) fun e he => by
          rw [abs_of_pos (by linarith [he.2])]; linarith [he.2]
        have hw := hWfar (lam - y) (by rw [abs_of_pos (by linarith)]; linarith)
        have hD : 0 < (lam - y) ^ 2 := by nlinarith
        have h3 : (y - x) * h / (lam - y) ^ 2 ≤ 2 * R * (h / (2 * (lam - y) ^ 2)) := by
          rw [mul_div_assoc', div_le_div_iff₀ hD (by positivity)]
          have : 0 ≤ h * (lam - y) ^ 2 := by positivity
          nlinarith
        nlinarith

/-- **The Lipschitz error under the kernel.** -/
theorem abs_mul_pk_le {h R : ℝ} (hh : 0 < h) (hR : 1 ≤ R) {K : ℕ} (hK : 1 < 2 ^ (K + 1) * h)
    {u : ℝ} (hu : |u| ≤ R) : |u| * pk h u ≤ (2 * R ^ 2 + 4) * dyW h K u := by
  refine le_dyW hh hR hK hu ?_ fun hu0 => ?_
  · unfold pk
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|u| - h), sq_abs u]
  · unfold pk
    have hpos : 0 < |u| := abs_pos.2 hu0
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hpos]
    nlinarith [sq_abs u, sq_nonneg h]

end BlockBand.Critical.RelativeVectors
