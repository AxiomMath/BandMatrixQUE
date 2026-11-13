module

public import BlockBand.Endpoints.Clock.RobinEntranceLaw
public import BlockBand.Layers.GinibreTails
public import BlockBand.Layers.Nets

/-!
# The Robin entrance lemma: the Robin phase interval and the Gaussian cutoff

We collect the elementary facts on the Robin phase `λ_θ` and the Gaussian cutoff of the far bond
used in the proof of the Robin entrance lemma.

## Results

* `boundaryZ_eq`, `etaZ_eq`, `re_boundaryZ_eq`: `z = -(1+b)E/2 + i(1-b)√(4-E²)/2` for `|E| ≤ 2`;
  `etaZ_bounds`: `κ/4 ≤ η ≤ 1`, `|Re z| ≤ 2` for `b ∈ [0,1/2]`, `E ∈ bulkInterval κ`.
* `robinLam b E θ = Re z + η tan((θ-π)/2)` (`= Re z - η cot(θ/2)`) and the closure
  relation `phase_mul_closure`: `e^{iθ}(z̄ - λ_θ) = z - λ_θ` for `θ ∈ (0, 2π)` (outgoing equals
  incoming minus `2iη` times the auxiliary amplitude, and incoming equals `e^{iθ}` times outgoing).
* `robinTheta b E λ = π + 2 arctan((λ - Re z)/η) ∈ (0, 2π)`: on `[θ(Λ₁), θ(Λ₂)]`,
  `λ_θ ∈ [Λ₁, Λ₂]` (`robinLam_mem_of_mem`) and `tan((θ-π)/2)` is in the corresponding range
  (`tan_mem_of_mem`); the interval length bound `robinTheta_sub_ge`
  (`θ(2Λ) - θ(Λ) ≥ 2(Λ/η)/(1 + ((2Λ + |Re z|)/η)²)`, mean value theorem for `arctan`, from
  `dθ/dλ = 2η/((λ - Re z)² + η²)`).
* `norm_robinInitial_le`: `‖λ⁻¹B₀B₀*‖ ≤ ‖B₀‖²/λ`; `ginibre_norm_tail`:
  `P(‖B₀‖ ≥ 7) ≤ e^{-W}` for `B₀ ~ Gin(b/W)`, `W ≥ 1`, `0 < b ≤ 1/2` (the net bound
  `ginibre_opNorm_tail_of_net` with the `1/4`-nets of `exists_sphere_net_euclidean`).
* `abs_integral_sub_le_of_good`: `|E φ - m| ≤ δ + M P(Gᶜ)` if `|φ - m| ≤ δ` on `G` and
  `|φ - m| ≤ M` everywhere.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Clock

open Real Filter Topology MeasureTheory
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open scoped Matrix Matrix.Norms.L2Operator ENNReal NNReal

namespace RobinEntrance

/-- `z = a⁻¹ + ba = (-(1+b)E/2) + i(1-b)√(4-E²)/2` for `|E| ≤ 2`. -/
theorem boundaryZ_eq {b E : ℝ} (hE0 : -2 ≤ E) (hE1 : E ≤ 2) :
    boundaryZ b E = ⟨-(1 + b) * E / 2, (1 - b) * Real.sqrt (4 - E ^ 2) / 2⟩ := by
  have h4 : 0 ≤ 4 - E ^ 2 := by nlinarith
  have hss : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := Real.sq_sqrt h4
  have hn : Complex.normSq (matchedA E) = 1 := by
    rw [Complex.normSq_apply]; simp only [matchedA]; nlinarith
  apply Complex.ext
  · simp only [boundaryZ, Complex.add_re, Complex.inv_re, hn, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [matchedA]; ring
  · simp only [boundaryZ, Complex.add_im, Complex.inv_im, hn, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    simp only [matchedA]; ring

theorem etaZ_eq {b E : ℝ} (hE0 : -2 ≤ E) (hE1 : E ≤ 2) :
    etaZ b E = (1 - b) * Real.sqrt (4 - E ^ 2) / 2 := by
  rw [etaZ, boundaryZ_eq hE0 hE1]

theorem re_boundaryZ_eq {b E : ℝ} (hE0 : -2 ≤ E) (hE1 : E ≤ 2) :
    (boundaryZ b E).re = -(1 + b) * E / 2 := by
  rw [boundaryZ_eq hE0 hE1]

/-- `λ_θ = Re z + η tan((θ - π)/2)` (`= Re z - η cot(θ/2)`). -/
def robinLam (b E θ : ℝ) : ℝ := (boundaryZ b E).re + etaZ b E * Real.tan ((θ - π) / 2)

/-- **The closure relation**: for `θ ∈ (0, 2π)`,
`e^{iθ}(z̄ - λ_θ) = z - λ_θ`. -/
theorem phase_mul_closure (b E : ℝ) {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
    phase θ * (star (boundaryZ b E) - robinLam b E θ) = boundaryZ b E - robinLam b E θ := by
  rw [robinLam]
  set u := (θ - π) / 2 with hu
  have hθ : θ = π + 2 * u := by rw [hu]; ring
  have hc : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by rw [hu]; linarith, by rw [hu]; linarith⟩
  set x := (boundaryZ b E).re
  set η := etaZ b E
  have hz : boundaryZ b E = ⟨x, η⟩ := rfl
  have ht : Real.tan u = Real.sin u / Real.cos u := Real.tan_eq_sin_div_cos u
  have hsc := Real.sin_sq_add_cos_sq u
  have hcos : Real.cos θ = -(Real.cos u ^ 2 - Real.sin u ^ 2) := by
    rw [hθ, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_two_mul]; nlinarith
  have hsin : Real.sin θ = -(2 * Real.sin u * Real.cos u) := by
    rw [hθ, Real.sin_add, Real.cos_pi, Real.sin_pi, Real.sin_two_mul]; ring
  rw [hz]
  apply Complex.ext
  · simp only [phase, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [hcos, hsin, ht]
    field_simp
    linear_combination (-(Real.sin u * η)) * hsc
  · simp only [phase, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [hcos, hsin, ht]
    field_simp
    linear_combination η * hsc

/-- `θ(λ) = π + 2 arctan((λ - Re z)/η)`: the phase with `λ_θ = λ`. -/
def robinTheta (b E lam : ℝ) : ℝ := π + 2 * Real.arctan ((lam - (boundaryZ b E).re) / etaZ b E)

theorem robinTheta_pos (b E lam : ℝ) : 0 < robinTheta b E lam := by
  have := Real.neg_pi_div_two_lt_arctan ((lam - (boundaryZ b E).re) / etaZ b E)
  unfold robinTheta; linarith

theorem robinTheta_lt (b E lam : ℝ) : robinTheta b E lam < 2 * π := by
  have := Real.arctan_lt_pi_div_two ((lam - (boundaryZ b E).re) / etaZ b E)
  unfold robinTheta; linarith

/-- On `[θ(Λ₁), θ(Λ₂)]` the half-angle tangent lies in `[(Λ₁ - Re z)/η, (Λ₂ - Re z)/η]`. -/
theorem tan_mem_of_mem {b E Λ₁ Λ₂ θ : ℝ}
    (hθ : θ ∈ Set.Icc (robinTheta b E Λ₁) (robinTheta b E Λ₂)) :
    (Λ₁ - (boundaryZ b E).re) / etaZ b E ≤ Real.tan ((θ - π) / 2) ∧
      Real.tan ((θ - π) / 2) ≤ (Λ₂ - (boundaryZ b E).re) / etaZ b E := by
  set v₁ := (Λ₁ - (boundaryZ b E).re) / etaZ b E
  set v₂ := (Λ₂ - (boundaryZ b E).re) / etaZ b E
  have hu1 : Real.arctan v₁ ≤ (θ - π) / 2 := by
    have := hθ.1; unfold robinTheta at this; linarith
  have hu2 : (θ - π) / 2 ≤ Real.arctan v₂ := by
    have := hθ.2; unfold robinTheta at this; linarith
  have hm := Real.strictMonoOn_tan.monotoneOn
  have hA1 : Real.arctan v₁ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hA2 : Real.arctan v₂ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩
  have hU : (θ - π) / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨lt_of_lt_of_le hA1.1 hu1, lt_of_le_of_lt hu2 hA2.2⟩
  refine ⟨?_, ?_⟩
  · have := hm hA1 hU hu1
    rwa [Real.tan_arctan] at this
  · have := hm hU hA2 hu2
    rwa [Real.tan_arctan] at this

/-- `λ_θ ∈ [Λ₁, Λ₂]` on `[θ(Λ₁), θ(Λ₂)]` (`η > 0`). -/
theorem robinLam_mem_of_mem {b E Λ₁ Λ₂ θ : ℝ} (hη : 0 < etaZ b E)
    (hθ : θ ∈ Set.Icc (robinTheta b E Λ₁) (robinTheta b E Λ₂)) :
    Λ₁ ≤ robinLam b E θ ∧ robinLam b E θ ≤ Λ₂ := by
  obtain ⟨h1, h2⟩ := tan_mem_of_mem hθ
  rw [div_le_iff₀ hη] at h1
  rw [le_div_iff₀ hη] at h2
  unfold robinLam
  constructor <;> nlinarith

/-- `arctan v₂ - arctan v₁ ≥ (v₂ - v₁)/(1 + V²)` for `v₁ < v₂`, `|v₁|, |v₂| ≤ V`. -/
theorem arctan_sub_ge {v₁ v₂ V : ℝ} (h12 : v₁ < v₂) (h1 : |v₁| ≤ V) (h2 : |v₂| ≤ V) :
    (v₂ - v₁) / (1 + V ^ 2) ≤ Real.arctan v₂ - Real.arctan v₁ := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.arctan (fun x => 1 / (1 + x ^ 2)) h12
    Real.continuous_arctan.continuousOn fun x _ => Real.hasDerivAt_arctan x
  have hcV : c ^ 2 ≤ V ^ 2 := by
    have hc1 : |c| ≤ V := abs_le.mpr ⟨by
      have := (abs_le.mp h1).1; linarith [hc.1], by have := (abs_le.mp h2).2; linarith [hc.2]⟩
    have := sq_abs c
    nlinarith [abs_nonneg c]
  have hpos : 0 < v₂ - v₁ := by linarith
  have key : Real.arctan v₂ - Real.arctan v₁ = (v₂ - v₁) * (1 / (1 + c ^ 2)) := by
    rw [hcd]; field_simp
  rw [key, div_eq_mul_one_div]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Length of the phase interval: `θ(2Λ) - θ(Λ) ≥ 2(Λ/η)/(1 + ((2Λ + |Re z|)/η)²)`. -/
theorem robinTheta_sub_ge {b E Λ : ℝ} (hη : 0 < etaZ b E) (hΛ : 0 < Λ) :
    2 * ((Λ / etaZ b E) / (1 + ((2 * Λ + |(boundaryZ b E).re|) / etaZ b E) ^ 2)) ≤
      robinTheta b E (2 * Λ) - robinTheta b E Λ := by
  set x := (boundaryZ b E).re
  set η := etaZ b E
  have hV1 : |(Λ - x) / η| ≤ (2 * Λ + |x|) / η := by
    rw [abs_div, abs_of_pos hη]
    exact div_le_div_of_nonneg_right (by
      have := abs_sub (Λ) x; rw [abs_of_pos hΛ] at this; linarith) hη.le
  have hV2 : |(2 * Λ - x) / η| ≤ (2 * Λ + |x|) / η := by
    rw [abs_div, abs_of_pos hη]
    exact div_le_div_of_nonneg_right (by
      have := abs_sub (2 * Λ) x; rw [abs_of_pos (by linarith : 0 < 2 * Λ)] at this; linarith)
      hη.le
  have h12 : (Λ - x) / η < (2 * Λ - x) / η := div_lt_div_of_pos_right (by linarith) hη
  have h := arctan_sub_ge h12 hV1 hV2
  have hd : (2 * Λ - x) / η - (Λ - x) / η = Λ / η := by field_simp; ring
  rw [hd] at h
  unfold robinTheta
  linarith

/-- Uniform bounds on compact parameter sets: for `b ∈ [0, 1/2]` and `E ∈ bulkInterval κ`,
`κ/4 ≤ η ≤ 1` and `|Re z| ≤ 2`. -/
theorem etaZ_bounds {b E κ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 2) (hκ : 0 < κ)
    (hE : E ∈ bulkInterval κ) :
    κ / 4 ≤ etaZ b E ∧ etaZ b E ≤ 1 ∧ |(boundaryZ b E).re| ≤ 2 := by
  have hE' : -2 + κ ≤ E ∧ E ≤ 2 - κ := hE
  have hE0 : -2 ≤ E := by linarith
  have hE1 : E ≤ 2 := by linarith
  rw [etaZ_eq hE0 hE1, re_boundaryZ_eq hE0 hE1]
  have h4 : 0 ≤ 4 - E ^ 2 := by nlinarith
  have hs0 := Real.sqrt_nonneg (4 - E ^ 2)
  have hss : Real.sqrt (4 - E ^ 2) ^ 2 = 4 - E ^ 2 := Real.sq_sqrt h4
  have hk : κ ^ 2 ≤ 4 - E ^ 2 := by nlinarith
  have hsk : κ ≤ Real.sqrt (4 - E ^ 2) := by
    rw [← Real.sqrt_sq hκ.le]; exact Real.sqrt_le_sqrt hk
  have hs2 : Real.sqrt (4 - E ^ 2) ≤ 2 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  rw [abs_le]; constructor <;> nlinarith

/-- `‖λ⁻¹ B B*‖ ≤ ‖B‖²/λ` (`λ > 0`, `ℓ²` operator norm). -/
theorem norm_robinInitial_le {W : ℕ} {lam : ℝ} (hlam : 0 < lam) (B : Matrix (Fin W) (Fin W) ℂ) :
    ‖robinInitial lam B‖ ≤ ‖B‖ ^ 2 / lam := by
  unfold robinInitial
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hlam]
  have h := norm_mul_le B Bᴴ
  rw [Matrix.l2_opNorm_conjTranspose] at h
  rw [div_eq_inv_mul, sq]
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hlam.le)

/-- **Gaussian norm cutoff for the far bond**: for `W ≥ 1` and `0 < b ≤ 1/2`, `P_{Gin(b/W)}(‖B‖ ≥ 7) ≤ e^{-W}` (`K = 7`). -/
theorem ginibre_norm_tail {W : ℕ} (hW : 0 < W) {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1 / 2) :
    ginibreMeasure (Fin W) (Fin W) (Real.toNNReal (b / W)) {B | 7 ≤ ‖B‖} ≤
      ENNReal.ofReal (Real.exp (-(W : ℝ))) := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hbW : 0 < b / W := div_pos hb0 hWr
  have ht : Real.toNNReal (b / W) ≠ 0 := (Real.toNNReal_pos.mpr hbW).ne'
  obtain ⟨N, hN1, hNc, hN⟩ := BlockBand.Layers.exists_sphere_net_euclidean (ι := Fin W)
    (ε := 1 / 4) (by norm_num) (by norm_num)
  have h := BlockBand.Layers.ginibre_opNorm_tail_of_net ht N N hN1 hN1 hN hN (a := 7)
    (by norm_num)
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have htv : ((Real.toNNReal (b / W) : ℝ≥0) : ℝ) = b / W := Real.coe_toNNReal _ hbW.le
  rw [htv]
  have hc : (N.card : ℝ) ≤ 12 ^ (2 * W) := by
    have : (3 : ℝ) / (1 / 4) = 12 := by norm_num
    rw [this, Fintype.card_fin] at hNc; exact hNc
  have h12 : (12 : ℝ) ≤ Real.exp 3 := by
    have h1 : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h3 := pow_lt_pow_left₀ h1 (by norm_num) (three_ne_zero)
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; norm_num at h3; linarith
  have hpow : (12 : ℝ) ^ (2 * W) ≤ Real.exp (6 * W) := by
    calc (12 : ℝ) ^ (2 * W) ≤ Real.exp 3 ^ (2 * W) := pow_le_pow_left₀ (by norm_num) h12 _
      _ = Real.exp (6 * W) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have hcard : (N.card : ℝ) * N.card ≤ Real.exp (12 * W) := by
    have h0 : (0 : ℝ) ≤ N.card := Nat.cast_nonneg _
    calc (N.card : ℝ) * N.card ≤ Real.exp (6 * W) * Real.exp (6 * W) :=
          mul_le_mul (hc.trans hpow) (hc.trans hpow) h0 (Real.exp_pos _).le
      _ = Real.exp (12 * W) := by rw [← Real.exp_add]; ring_nf
  have hexp : Real.exp (-(7 : ℝ) ^ 2 / (4 * (b / W))) ≤ Real.exp (-(13 * W)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have : 13 * (W : ℝ) * (4 * (b / W)) = 52 * b := by field_simp; norm_num
    rw [this]; nlinarith
  calc (N.card : ℝ) * N.card * Real.exp (-(7 : ℝ) ^ 2 / (4 * (b / W)))
      ≤ Real.exp (12 * W) * Real.exp (-(13 * W)) :=
        mul_le_mul hcard hexp (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (-(W : ℝ)) := by rw [← Real.exp_add]; ring_nf

/-- **Splitting an expectation into a good and a bad event.** -/
theorem abs_integral_sub_le_of_good {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {φ : α → ℝ} (hφ : Integrable φ μ) {m δ M : ℝ} (hδ : 0 ≤ δ)
    {G : Set α} (hG : MeasurableSet G) (hgood : ∀ x ∈ G, |φ x - m| ≤ δ)
    (hall : ∀ x, |φ x - m| ≤ M) :
    |∫ x, φ x ∂μ - m| ≤ δ + M * (μ Gᶜ).toReal := by
  have h1 : ∫ x, φ x ∂μ - m = ∫ x, (φ x - m) ∂μ := by
    rw [integral_sub hφ (integrable_const m), integral_const, probReal_univ, one_smul]
  have hb : Integrable (fun x => δ + M * Gᶜ.indicator (1 : α → ℝ) x) μ :=
    (integrable_const δ).add ((integrable_const (1 : ℝ)).indicator hG.compl |>.const_mul M)
  rw [h1]
  refine (abs_integral_le_integral_abs).trans ?_
  have hle : ∫ x, |φ x - m| ∂μ ≤ ∫ x, (δ + M * Gᶜ.indicator (1 : α → ℝ) x) ∂μ := by
    refine integral_mono (hφ.sub (integrable_const m)).abs hb fun x => ?_
    by_cases hx : x ∈ G
    · have : x ∉ Gᶜ := fun h => h hx
      simp only [Set.indicator_of_notMem this, mul_zero, add_zero]
      exact hgood x hx
    · rw [Set.indicator_of_mem (Set.mem_compl hx)]
      simp only [Pi.one_apply, mul_one]
      linarith [hall x]
  refine hle.trans (le_of_eq ?_)
  rw [integral_add (integrable_const δ) ?_, integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_indicator_one hG.compl]
  · rfl
  · exact ((integrable_const (1 : ℝ)).indicator hG.compl).const_mul M

end RobinEntrance

end BlockBand.Endpoints.Clock
