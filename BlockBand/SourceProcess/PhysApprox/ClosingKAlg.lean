module

public import BlockBand.SourceProcess.PhysApprox.ClosingGramInt

/-!
# The closed `𝒦` as an analytic function of the phase

For a vector `u` put `F_u(z) = u*(𝒦_cl(z) - 𝒦)u` (`kForm`). Then
* `kForm_eq`: `F_u(z) = -(2iη z) (Vu)* (1 - zN)⁻¹ (Π𝕊V u)` (analytic where `1 - zN` is
  invertible; `F_u(0) = 0`);
* `im_kForm`: on `|z| = 1`, with the closing hypotheses, `Im F_u(z) = -η(‖V_cl u‖² - ‖Vu‖²)`
  (`CCᴴ = 1 + Z + Zᴴ`);
* `abs_im_kForm_le`: for `u = e_i + c e_k`, `|c| = 1`,
  `|Im F_u| ≤ η(2(a_i + a_k)(d_i + d_k) + (d_i + d_k)²)` (column norms `a`, `d` of `V`,
  `V_cl - V`);
* `polarization`: `4X_ik = F(1) - iF(i) - F(-1) + iF(-i)`, `F(c) = (e_i + ce_k)* X (e_i + ce_k)`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox

open Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Closing
open BlockBand.SourceProcess.ClosingLeak BlockBand.Transmission.Bridge

section Generic

variable {ρ c κ : Type*} [Fintype ρ] [Fintype c] [Fintype κ]

theorem re_star_dotProduct_comm (u v : ρ → ℂ) : (star v ⬝ᵥ u).re = (star u ⬝ᵥ v).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `u* (Vᴴ M) w = (Vu)* (M w)`. -/
theorem star_dotProduct_conjTranspose_mul (V : Matrix ρ c ℂ) (M : Matrix ρ κ ℂ) (u : c → ℂ)
    (w : κ → ℂ) : star u ⬝ᵥ ((Vᴴ * M) *ᵥ w) = star (V *ᵥ u) ⬝ᵥ (M *ᵥ w) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec]

theorem l2_add_le (u v : ρ → ℂ) : l2 (u + v) ≤ l2 u + l2 v := by
  rw [l2_eq_norm, l2_eq_norm, l2_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

theorem l2_smul (z : ℂ) (u : ρ → ℂ) : l2 (z • u) = ‖z‖ * l2 u := by
  rw [l2_eq_norm, l2_eq_norm, WithLp.toLp_smul, norm_smul]

end Generic

theorem star_single_one {ι : Type*} [DecidableEq ι] (i : ι) :
    star (Pi.single i 1 : ι → ℂ) = Pi.single i 1 := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The test vector `e_i + c e_k`. -/
def testVec {np : ℕ} (i k : Fin np) (c : ℂ) : Fin np → ℂ := Pi.single i 1 + c • Pi.single k 1

theorem quad_testVec {np : ℕ} (X : Matrix (Fin np) (Fin np) ℂ) (i k : Fin np) (c : ℂ) :
    star (testVec i k c) ⬝ᵥ (X *ᵥ testVec i k c) =
      X i i + c * X i k + star c * X k i + star c * c * X k k := by
  simp only [testVec, star_add, star_smul, star_single_one, mulVec_add, mulVec_smul,
    mulVec_single_one, add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul,
    single_one_dotProduct, smul_eq_mul, col_apply]
  ring

/-- **Polarization**: `4X_ik = F(1) - iF(i) - F(-1) + iF(-i)`. -/
theorem polarization {np : ℕ} (X : Matrix (Fin np) (Fin np) ℂ) (i k : Fin np) :
    4 * X i k = star (testVec i k 1) ⬝ᵥ (X *ᵥ testVec i k 1) -
      Complex.I * (star (testVec i k Complex.I) ⬝ᵥ (X *ᵥ testVec i k Complex.I)) -
      star (testVec i k (-1)) ⬝ᵥ (X *ᵥ testVec i k (-1)) +
      Complex.I * (star (testVec i k (-Complex.I)) ⬝ᵥ (X *ᵥ testVec i k (-Complex.I))) := by
  rw [quad_testVec, quad_testVec, quad_testVec, quad_testVec]
  simp only [star_one, star_neg, Complex.star_def, Complex.conj_I]
  linear_combination (2 * X i k - 2 * X k i) * Complex.I_sq

variable {W : ℕ}

/-- `F_u(z) = u*(𝒦_cl(z) - 𝒦)u`. -/
def kForm (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (W : ℕ) (x : ProbedPath W np)
    (u : Fin np → ℂ) (z : ℂ) : ℂ :=
  star u ⬝ᵥ ((closedK b E s T h τ m W z x - complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x) *ᵥ u)

/-- `F_u(z) = -(2iη z)(Vu)*(1 - zN)⁻¹(Π𝕊Vu)`. -/
theorem kForm_eq (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (u : Fin np → ℂ) (z : ℂ) :
    kForm b E s T h τ m W x u z = -(((2 * etaZ b E : ℝ) : ℂ) * Complex.I * z) *
      (star (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x *ᵥ u) ⬝ᵥ
        ((1 - z • physClosingN b E s T h W x.1)⁻¹ *ᵥ
          ((farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) *
            scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 *
            probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x) *ᵥ u))) := by
  rw [kForm, closedK, sub_sub_cancel_left, neg_mulVec, smul_mulVec, dotProduct_neg,
    dotProduct_smul, smul_eq_mul, neg_mul]
  congr 2
  rw [show (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᴴ * (1 - z • physClosingN b E s T h W x.1)⁻¹ *
      farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) *
      scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 * probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x =
      (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᴴ * ((1 - z • physClosingN b E s T h W x.1)⁻¹ *
      (farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1) *
      scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1 * probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)) by
    simp only [Matrix.mul_assoc], star_dotProduct_conjTranspose_mul, ← mulVec_mulVec]

/-- **`Im F_u(z) = -η(‖V_cl u‖² - ‖Vu‖²)`** on `|z| = 1`, under the closing hypotheses. -/
theorem im_kForm (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (x : ProbedPath W np) (z : ℂ)
    (hH : ClosingHyp b E h ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * T⌋₊ x.1 z) (u : Fin np → ℂ) :
    (kForm b E s T h τ m W x u z).im = -(etaZ b E) *
      (l2 (closedFrame b E s T h τ m W z x *ᵥ u) ^ 2 -
        l2 (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x *ᵥ u) ^ 2) := by
  set S := scatteringMatrix b E W ⌊(W : ℝ) * T⌋₊ x.1
  set A := farEmbed (omittedProj b E h W ⌊(W : ℝ) * s⌋₊ x.1)
  set Pi := farEmbed (closingPairing b E h W ⌊(W : ℝ) * s⌋₊ x.1)
  set V := probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x
  set C := physClosingMap b E s T h W x.1 z
  set Z := closingZ S A Pi z
  have hA2 : A * A = A := by rw [farEmbed_mul, omittedProj_mul_self]
  have hAH : Aᴴ = A := by rw [farEmbed_conjTranspose, omittedProj_conjTranspose]
  have hPi : Pi * Piᴴ = A := by
    rw [farEmbed_conjTranspose, farEmbed_mul, closingPairing_mul_conj b E h hH.hh]
  have hCC : C * Cᴴ = 1 + Z + Zᴴ :=
    closingMap_mul_conj hA2 hAH hPi hH.unitary hH.norm_one hH.unit
  -- the matrix form of `𝒦_cl - 𝒦`
  have hK : closedK b E s T h τ m W z x - complexSourceK b E W ⌊(W : ℝ) * T⌋₊ τ m x =
      -(((2 * etaZ b E : ℝ) : ℂ) * Complex.I) • (Vᴴ * Z * V) := by
    rw [closedK, sub_sub_cancel_left]
    change -((((2 * etaZ b E : ℝ) : ℂ) * Complex.I * z) • (Vᴴ *
        (1 - z • closingN S A Pi)⁻¹ * Pi * S * V)) = _
    rw [show Z = z • ((1 - z • closingN S A Pi)⁻¹ * (Pi * S)) from rfl, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, neg_mul, neg_smul]
    simp only [Matrix.mul_assoc]
  set w := V *ᵥ u
  have hF : kForm b E s T h τ m W x u z =
      -(((2 * etaZ b E : ℝ) : ℂ) * Complex.I) * (star w ⬝ᵥ (Z *ᵥ w)) := by
    rw [kForm, hK, neg_smul, neg_mulVec, smul_mulVec, dotProduct_neg, dotProduct_smul,
      smul_eq_mul, neg_mul, Matrix.mul_assoc, star_dotProduct_conjTranspose_mul,
      ← mulVec_mulVec]
  have hcl : l2 (closedFrame b E s T h τ m W z x *ᵥ u) ^ 2 =
      l2 w ^ 2 + 2 * (star w ⬝ᵥ (Z *ᵥ w)).re := by
    have e : closedFrame b E s T h τ m W z x *ᵥ u = Cᴴ *ᵥ w := by
      rw [closedFrame, ← mulVec_mulVec]
    rw [e, l2_mulVec_sq, conjTranspose_conjTranspose, hCC, add_mulVec, add_mulVec, one_mulVec,
      dotProduct_add, dotProduct_add, Complex.add_re, Complex.add_re, ← l2_sq]
    have h3 : (star w ⬝ᵥ (Zᴴ *ᵥ w)).re = (star w ⬝ᵥ (Z *ᵥ w)).re := by
      rw [dotProduct_mulVec, ← star_mulVec, re_star_dotProduct_comm]
    rw [h3]
    ring
  rw [hF, hcl]
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- **The imaginary part is controlled by the column norms** (`u = e_i + c e_k`, `|c| = 1`). -/
theorem abs_im_kForm_le (b E s T h : ℝ) {np : ℕ} (τ m : Fin np → ℝ) (x : ProbedPath W np)
    (z : ℂ) (hH : ClosingHyp b E h ⌊(W : ℝ) * s⌋₊ ⌊(W : ℝ) * T⌋₊ x.1 z) (i k : Fin np) {c : ℂ}
    (hc : ‖c‖ = 1) (hη : 0 ≤ etaZ b E) :
    |(kForm b E s T h τ m W x (testVec i k c) z).im| ≤ etaZ b E *
      (2 * (l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) +
          l2 ((probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k)) *
        (l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) +
          l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k)) +
      (l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ i) +
          l2 ((closedFrame b E s T h τ m W z x - probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x)ᵀ k)) ^
        2) := by
  set V := probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x
  set D := closedFrame b E s T h τ m W z x - V
  have hcol : ∀ M : Matrix (Fin 2 × Fin W) (Fin np) ℂ,
      l2 (M *ᵥ testVec i k c) ≤ l2 (Mᵀ i) + l2 (Mᵀ k) := by
    intro M
    have e : M *ᵥ testVec i k c = Mᵀ i + c • Mᵀ k := by
      rw [testVec, mulVec_add, mulVec_smul, mulVec_single_one, mulVec_single_one]
      rfl
    rw [e]
    refine (l2_add_le _ _).trans (le_of_eq ?_)
    rw [l2_smul, hc, one_mul]
  have hsplit : closedFrame b E s T h τ m W z x *ᵥ testVec i k c =
      V *ᵥ testVec i k c + D *ᵥ testVec i k c := by
    rw [← add_mulVec, add_sub_cancel]
  rw [im_kForm b E s T h τ m x z hH, hsplit, l2_add_sq]
  have hV : l2 (probeFrame b E W ⌊(W : ℝ) * T⌋₊ τ m x *ᵥ testVec i k c) =
      l2 (V *ᵥ testVec i k c) := rfl
  rw [hV]
  have hre := (Complex.abs_re_le_norm (star (V *ᵥ testVec i k c) ⬝ᵥ (D *ᵥ testVec i k c))).trans
    (norm_star_dotProduct_le _ _)
  have hre2 := abs_le.1 hre
  have ha := hcol V
  have hd := hcol D
  have ha0 := l2_nonneg (V *ᵥ testVec i k c)
  have hd0 := l2_nonneg (D *ᵥ testVec i k c)
  have hab : |2 * (star (V *ᵥ testVec i k c) ⬝ᵥ (D *ᵥ testVec i k c)).re +
      l2 (D *ᵥ testVec i k c) ^ 2| ≤
      2 * l2 (V *ᵥ testVec i k c) * l2 (D *ᵥ testVec i k c) + l2 (D *ᵥ testVec i k c) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hmono : 2 * l2 (V *ᵥ testVec i k c) * l2 (D *ᵥ testVec i k c) +
      l2 (D *ᵥ testVec i k c) ^ 2 ≤
      2 * (l2 (Vᵀ i) + l2 (Vᵀ k)) * (l2 (Dᵀ i) + l2 (Dᵀ k)) + (l2 (Dᵀ i) + l2 (Dᵀ k)) ^ 2 := by
    have := mul_le_mul ha hd hd0 (ha0.trans ha)
    nlinarith
  have hY := abs_le.1 (hab.trans hmono)
  rw [abs_le]
  constructor <;> nlinarith [hY.1, hY.2]

end BlockBand.SourceProcess.PhysApprox
