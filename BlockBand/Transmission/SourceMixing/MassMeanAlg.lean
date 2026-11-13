module

public import BlockBand.Transmission.SourceMixing.MatchedBasic

/-!
# Algebra for the `q/W`-exact mass mean

Scalar and matrix identities and inequalities used to bound the mean of the passive mass after
one fresh layer.

* `mm_ward`: the Ward identity of `M = (ζ - X)⁻¹`, `Im⟨M⟩ = -(Im ζ·Re⟨MMᴴ⟩ + Re⟨MᴴYM⟩)`
  (equivalently, `-Im m = (η - Im Ω)A_M + y_M`);
* `mm_inv_im`: `Im w⁻¹ = -|w⁻¹|² Im w`;
* `mm_trace_posSemidef`: the trace of a PSD matrix is real and nonnegative;
* `mm_passiveMass_le`: `q ≤ W/(4η)` (`T = 4ηQ = I - S*S ⪯ I`);
* `mm_F_le`: the scalar comparison `u·bh/(bhη + k_h u/W) ≤ Λ(q/(η(1+αq/W)) + C|h-1|q)`
  (with `s₁ = bh(η - Im Ω)/(bhη + k_h y_M)` and `k_h/(bhη) → α`);
* `mm_final`: the bookkeeping `(1+a)Λ(G + kq) ≤ G + Ceq`;
* `mm_re_s`, `mm_re_trace_le`, `mm_im_algebra`: `Re s₁` from the `s₁` equation, the crude
  trace bound, and the imaginary-part algebra `ι(1 - kA) = bhη + ky + O(ε)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.PassiveLayer
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The trace of a PSD matrix is a nonnegative real. -/
theorem mm_trace_posSemidef {n : Type*} [Fintype n] {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    0 ≤ P.trace.re ∧ P.trace = (P.trace.re : ℂ) := by
  have h := Complex.nonneg_iff.mp hP.trace_nonneg
  refine ⟨h.1, Complex.ext (by simp) ?_⟩
  simp only [Complex.ofReal_im]; exact h.2.symm

/-- `Im w⁻¹ = -|w⁻¹|² Im w`. -/
theorem mm_inv_im (w : ℂ) : (w⁻¹).im = -(w⁻¹ * conj w⁻¹).re * w.im := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.inv_im, Complex.normSq_inv]
  rcases eq_or_ne (Complex.normSq w) 0 with h | h
  · simp [h]
  · field_simp

/-- The Ward identity for `M = (ζ - X)⁻¹`: `Im⟨M⟩ = -(Im ζ·Re⟨MMᴴ⟩ + Re⟨MᴴYM⟩)`. -/
theorem mm_ward (X M : Matrix (Fin W) (Fin W) ℂ) (ζ : ℂ) (hNM : (ζ • 1 - X) * M = 1) :
    ((W : ℂ)⁻¹ * M.trace).im = -(ζ.im * ((W : ℂ)⁻¹ * (M * Mᴴ).trace).re +
      ((W : ℂ)⁻¹ * (Mᴴ * passiveY X * M).trace).re) := by
  set N := ζ • (1 : Matrix (Fin W) (Fin W) ℂ) - X
  have hMN : Mᴴ * Nᴴ = 1 := by rw [← conjTranspose_mul, hNM, conjTranspose_one]
  have hIm : matrixImaginaryPart N = ζ.im • 1 + passiveY X := by
    have h := matrixImaginaryPart_portPencil_general X ζ
    rw [portPencil] at h
    rw [h, passiveY]; abel
  have hdiff : M - Mᴴ = -((2 * Complex.I) • (Mᴴ * (ζ.im • 1 + passiveY X) * M)) := by
    have e1 : M - Mᴴ = Mᴴ * (Nᴴ - N) * M := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hMN, Matrix.one_mul, Matrix.mul_assoc, hNM,
        Matrix.mul_one]
    have e2 : Nᴴ - N = -(N - Nᴴ) := by abel
    rw [e1, e2, matrix_difference_eq_twoI_imaginaryPart, hIm]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  have htr := congrArg (fun A => (W : ℂ)⁻¹ * A.trace) hdiff
  simp only [trace_sub, trace_neg, trace_smul, Matrix.mul_add, Matrix.add_mul, trace_add,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_eq_mul] at htr
  rw [trace_conjTranspose, trace_mul_comm Mᴴ M] at htr
  have hW : ((W : ℂ)⁻¹).im = 0 := by simp
  have hWr : ∀ z : ℂ, ((W : ℂ)⁻¹ * z).re = (W : ℝ)⁻¹ * z.re := fun z => by
    simp [Complex.mul_re]
  have hWi : ∀ z : ℂ, ((W : ℂ)⁻¹ * z).im = (W : ℝ)⁻¹ * z.im := fun z => by
    simp [Complex.mul_im]
  have him := congrArg Complex.im htr
  rw [hWi, hWr, hWr, hWi] at *
  simp only [Complex.mul_im, Complex.mul_re, Complex.sub_im, Complex.star_def,
    Complex.conj_im, Complex.neg_im, Complex.add_im, Complex.add_re, Complex.real_smul,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
    Complex.im_ofNat] at him ⊢
  clear hW
  linear_combination (1 / 2 : ℝ) * him

/-- `q ≤ W/(4η)` for every `X` (`T = 4ηQ = I - S*S ⪯ I`). -/
theorem mm_passiveMass_le {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2)
    (X : Matrix (Fin W) (Fin W) ℂ) : passiveMass b E X ≤ W / (4 * etaZ b E) := by
  have hη := etaZ_pos b E hb h1 h2
  have hT := Bridge.passiveTransmission_eq_one_sub b E X
  have hS := (mm_trace_posSemidef (Matrix.posSemidef_conjTranspose_mul_self
    (Bridge.passiveS b E X))).1
  have htr := congrArg (fun A => A.trace.re) hT
  simp only [passiveTransmission, trace_smul, trace_sub, trace_one, Fintype.card_fin,
    smul_eq_mul, Complex.sub_re, Complex.natCast_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at htr
  rw [le_div_iff₀ (by positivity), passiveMass]
  nlinarith

/-- Scalar comparison of the `s₁` main term with `q/(1+αq/W)`. -/
theorem mm_F_le {η b h u q W Λ : ℝ} (hη : 0 < η) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hh : 1 / 2 ≤ h) (hu : 0 ≤ u) (hq : 0 ≤ q) (hW : 0 < W) (hqW : q ≤ W / (4 * η))
    (hΛ : 1 ≤ Λ) (huq : u ≤ Λ * q) :
    u * (b * h) / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) ≤
      Λ * (q / (η * (1 + (1 - b) ^ 2 / (b * η) * q / W)) +
        q * ((1 - 2 * b) / b * 2 * |h - 1|) / (4 * η ^ 3)) := by
  have hh0 : 0 < h := by linarith
  have hc : 0 ≤ 1 - 2 * b := by linarith
  set γ := ((1 - 2 * b) + b ^ 2 * h) / (b * h) with hγ
  set γ₀ := (1 - b) ^ 2 / b with hγ₀
  have hγ0 : 0 ≤ γ := by positivity
  have hγ₀0 : 0 ≤ γ₀ := by positivity
  have hbh : 0 < b * h := by positivity
  -- rewrite the left side as `u/(η + γu/W)`
  have eF : u * (b * h) / (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * (u / W)) =
      u / (η + γ * (u / W)) := by
    rw [hγ]; field_simp
  have eG : η * (1 + (1 - b) ^ 2 / (b * η) * q / W) = η + γ₀ * (q / W) := by
    rw [hγ₀]; field_simp
  rw [eF, eG]
  have hd : ∀ t, 0 ≤ t → 0 < η + γ * (t / W) := fun t ht => by positivity
  -- monotonicity in `u`, then `Λ ≥ 1`
  have m1 : u / (η + γ * (u / W)) ≤ Λ * q / (η + γ * (Λ * q / W)) := by
    rw [div_le_div_iff₀ (hd u hu) (hd _ (by positivity))]
    have : u * (γ * (Λ * q / W)) = Λ * q * (γ * (u / W)) := by ring
    nlinarith
  have m2 : Λ * q / (η + γ * (Λ * q / W)) ≤ Λ * (q / (η + γ * (q / W))) := by
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine div_le_div_of_nonneg_left hq (hd q hq) ?_
    have : q / W ≤ Λ * q / W := div_le_div_of_nonneg_right (by nlinarith) hW.le
    nlinarith
  -- the coefficient change `γ → γ₀`
  have hqW' : q / W ≤ 1 / (4 * η) := by
    rw [div_le_div_iff₀ hW (by positivity)]; rw [le_div_iff₀ (by positivity)] at hqW; linarith
  have hgg : |γ - γ₀| ≤ (1 - 2 * b) / b * 2 * |h - 1| := by
    have e : γ - γ₀ = (1 - 2 * b) / b * ((1 - h) / h) := by
      rw [hγ, hγ₀]; field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity), abs_div, abs_of_pos hh0, abs_sub_comm]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [div_le_iff₀ hh0]; nlinarith [abs_nonneg (h - 1)]
  have m3 : q / (η + γ * (q / W)) ≤ q / (η + γ₀ * (q / W)) +
      q * ((1 - 2 * b) / b * 2 * |h - 1|) / (4 * η ^ 3) := by
    have hd1 := hd q hq
    have hd2 : 0 < η + γ₀ * (q / W) := by positivity
    have e : q / (η + γ * (q / W)) - q / (η + γ₀ * (q / W)) =
        q * (q / W) * (γ₀ - γ) / ((η + γ * (q / W)) * (η + γ₀ * (q / W))) := by
      field_simp; ring
    have hprod : η ^ 2 ≤ (η + γ * (q / W)) * (η + γ₀ * (q / W)) := by
      have : 0 ≤ q / W := by positivity
      nlinarith [mul_nonneg hγ0 this, mul_nonneg hγ₀0 this,
        mul_nonneg (mul_nonneg hγ0 this) (mul_nonneg hγ₀0 this)]
    have hnum : q * (q / W) * (γ₀ - γ) ≤ q * (1 / (4 * η)) * ((1 - 2 * b) / b * 2 * |h - 1|) := by
      have : γ₀ - γ ≤ |γ - γ₀| := by rw [abs_sub_comm]; exact le_abs_self _
      have hqw0 : 0 ≤ q / W := by positivity
      calc q * (q / W) * (γ₀ - γ) ≤ q * (q / W) * |γ - γ₀| :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ q * (1 / (4 * η)) * ((1 - 2 * b) / b * 2 * |h - 1|) := by
            gcongr
    have hfin : q * (q / W) * (γ₀ - γ) / ((η + γ * (q / W)) * (η + γ₀ * (q / W))) ≤
        q * ((1 - 2 * b) / b * 2 * |h - 1|) / (4 * η ^ 3) := by
      rcases le_or_gt (q * (q / W) * (γ₀ - γ)) 0 with hn | hn
      · exact (div_nonpos_of_nonpos_of_nonneg hn (by positivity)).trans (by positivity)
      calc q * (q / W) * (γ₀ - γ) / ((η + γ * (q / W)) * (η + γ₀ * (q / W)))
          ≤ q * (q / W) * (γ₀ - γ) / η ^ 2 := div_le_div_of_nonneg_left hn.le (by positivity) hprod
        _ ≤ q * (1 / (4 * η)) * ((1 - 2 * b) / b * 2 * |h - 1|) / η ^ 2 :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = _ := by field_simp
    linarith
  calc u / (η + γ * (u / W)) ≤ Λ * (q / (η + γ * (q / W))) := m1.trans m2
    _ ≤ _ := mul_le_mul_of_nonneg_left m3 (by linarith)

/-- Bookkeeping: `(1+a)Λ(G + kq) ≤ G + Ceq` for `a ≤ Ae`, `Λ ≤ (1+Be)²`, `k ≤ Ke`, `e ≤ 1`. -/
theorem mm_final {G q a Λ k e A B K : ℝ} (hq : 0 ≤ q) (hG : 0 ≤ G) (hGq : G ≤ q) (he : 0 ≤ e)
    (he1 : e ≤ 1) (ha : 0 ≤ a) (ha' : a ≤ A * e) (hΛ : 1 ≤ Λ) (hΛ' : Λ ≤ (1 + B * e) ^ 2)
    (hk : 0 ≤ k) (hk' : k ≤ K * e) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (1 + a) * Λ * (G + k * q) ≤
      G + (A + 2 * B + B ^ 2 + A * (2 * B + B ^ 2) + (1 + A) * (1 + B) ^ 2 * K) * e * q := by
  have hBe : B * e ≤ B := by nlinarith
  have hAe : A * e ≤ A := by nlinarith
  have hP : (1 + a) * Λ ≤ 1 + (A + 2 * B + B ^ 2 + A * (2 * B + B ^ 2)) * e := by
    have h1 : (1 + a) * Λ ≤ (1 + A * e) * (1 + B * e) ^ 2 :=
      mul_le_mul (by linarith) hΛ' (by linarith) (by positivity)
    have h2 : (1 + B * e) ^ 2 ≤ 1 + (2 * B + B ^ 2) * e := by
      have hee : e ^ 2 ≤ e := by nlinarith
      have := mul_le_mul_of_nonneg_left hee (sq_nonneg B)
      nlinarith
    have h3 : (1 + A * e) * (1 + B * e) ^ 2 ≤ (1 + A * e) * (1 + (2 * B + B ^ 2) * e) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : A * e * ((2 * B + B ^ 2) * e) ≤ A * ((2 * B + B ^ 2) * e) := by
      have : 0 ≤ A * ((2 * B + B ^ 2) * e) := by positivity
      nlinarith
    nlinarith
  have hP' : (1 + a) * Λ ≤ (1 + A) * (1 + B) ^ 2 :=
    mul_le_mul (by linarith) (hΛ'.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2))
      (by linarith) (by positivity)
  have hkq : k * q ≤ K * e * q := mul_le_mul_of_nonneg_right hk' hq
  have hPpos : 0 ≤ (1 + a) * Λ := by positivity
  calc (1 + a) * Λ * (G + k * q) = (1 + a) * Λ * G + (1 + a) * Λ * (k * q) := by ring
    _ ≤ (1 + (A + 2 * B + B ^ 2 + A * (2 * B + B ^ 2)) * e) * G +
          (1 + A) * (1 + B) ^ 2 * (K * e * q) :=
        add_le_add (mul_le_mul_of_nonneg_right hP hG)
          (mul_le_mul hP' hkq (by positivity) (by positivity))
    _ ≤ G + (A + 2 * B + B ^ 2 + A * (2 * B + B ^ 2)) * e * q +
          (1 + A) * (1 + B) ^ 2 * (K * e * q) := by
        have : (A + 2 * B + B ^ 2 + A * (2 * B + B ^ 2)) * e * G ≤
            (A + 2 * B + B ^ 2 + A * (2 * B + B ^ 2)) * e * q :=
          mul_le_mul_of_nonneg_left hGq (by positivity)
        nlinarith
    _ = _ := by ring

/-- `Re s ≤ (bhι + |ι|ε₂ + C|E₁|)/D` from `|sL - bh| ≤ ε₂`, `ιL = D + E₁`, `|s| ≤ C`. -/
theorem mm_re_s {s : ℂ} {L D E₁ ι c ε₂ Cs : ℝ} (hsL : ‖s * L - c‖ ≤ ε₂)
    (hιL : ι * L = D + E₁) (hs : ‖s‖ ≤ Cs) (hD : 0 < D) :
    s.re ≤ (c * ι + (|ι| * ε₂ + Cs * |E₁|)) / D := by
  have e : s * D - c * ι = ι * (s * L - c) - s * E₁ := by
    have : (D : ℂ) = ι * L - E₁ := by exact_mod_cast (by linarith : D = ι * L - E₁)
    rw [this]; ring
  have hn : ‖s * D - c * ι‖ ≤ |ι| * ε₂ + Cs * |E₁| := by
    rw [e]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hsL (abs_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
  have hre : (s * D - c * ι).re = s.re * D - c * ι := by
    simp [Complex.mul_re]
  have := (Complex.re_le_norm _).trans hn
  rw [hre] at this
  rw [le_div_iff₀ hD]; linarith

/-- The crude bound `Re Tr(QZ) ≤ ‖Z‖q` for `Q ⪰ 0`. -/
theorem mm_re_trace_le {Q Z : Matrix (Fin W) (Fin W) ℂ} (hQ : Q.PosSemidef) :
    (Q * Z).trace.re ≤ ‖Z‖ * Q.trace.re := by
  rw [trace_mul_comm]
  exact (Complex.re_le_norm _).trans (norm_trace_mul_posSemidef_le hQ Z)

/-- The imaginary-part algebra: `ι(1 - kA) = bhη + ky + O(ε)`. -/
theorem mm_im_algebra {m₁ m₂ μ v : ℂ} {ι A y h η b ε : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (hh0 : 0 ≤ h) (hh : h ≤ 3 / 2)
    (hward : μ.im = -(ι * A + y)) (hι : ι = (1 - 2 * b) * (-m₁.im) + b * (-m₂.im))
    (hv : v.im = -h * (η - b * m₁.im)) (h1 : ‖m₁ - μ‖ ≤ ε) (h2 : ‖m₂ - v‖ ≤ ε) :
    |ι * (1 - ((1 - 2 * b) + b ^ 2 * h) * A) - (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * y)| ≤
      2 * ε := by
  have hc : 0 ≤ 1 - 2 * b := by linarith
  have e : ι * (1 - ((1 - 2 * b) + b ^ 2 * h) * A) - (b * h * η + ((1 - 2 * b) + b ^ 2 * h) * y) =
      (1 - 2 * b) * (-m₁.im + μ.im) + b * (-m₂.im + v.im) + b ^ 2 * h * (-m₁.im + μ.im) := by
    rw [hv, hward, hι]; ring
  have e1 : |-m₁.im + μ.im| ≤ ε := by
    have : -m₁.im + μ.im = -(m₁ - μ).im := by simp only [Complex.sub_im]; ring
    rw [this, abs_neg]; exact (Complex.abs_im_le_norm _).trans h1
  have e2 : |-m₂.im + v.im| ≤ ε := by
    have : -m₂.im + v.im = -(m₂ - v).im := by simp only [Complex.sub_im]; ring
    rw [this, abs_neg]; exact (Complex.abs_im_le_norm _).trans h2
  have hε : 0 ≤ ε := (abs_nonneg _).trans e1
  have hbh : b ^ 2 * h ≤ 1 := by nlinarith
  rw [e]
  calc |(1 - 2 * b) * (-m₁.im + μ.im) + b * (-m₂.im + v.im) + b ^ 2 * h * (-m₁.im + μ.im)|
      ≤ (1 - 2 * b) * |-m₁.im + μ.im| + b * |-m₂.im + v.im| + b ^ 2 * h * |-m₁.im + μ.im| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul, abs_of_nonneg hc]
        · rw [abs_mul, abs_of_nonneg hb0.le]
        · rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (1 - 2 * b) * ε + b * ε + 1 * ε := by gcongr
    _ ≤ 2 * ε := by nlinarith

end BlockBand.Transmission.SourceMixing
