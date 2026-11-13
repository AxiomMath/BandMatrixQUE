module

public import BlockBand.Transmission.LawClauses.JetGap
public import BlockBand.Transmission.PassiveCovariance.WordReduction

/-!
# Deterministic core of `TransmissionLawContract.entryVariance`

* `passiveF_adj_mul_self`: `f*f = (I - T)/(4η²)` (from `R*R = c₀(R*-R) - Q/η`, `c₀² = -1/(4η²)`);
  hence `|u_i* f u_i|² ≤ (1 - t_i)/(4η²)`;
* `re_mainTensor_ge`: the leading tensor of the passive covariance lemma at
  `v = (u_i, u_j, u_j, u_i)` has real part `≥ (σ₊ - |σ₋|)/(4η²W)`. Indeed it is
  `(D₀/2W)(2 - t_i - t_j) + 2 Re(σ₋ f_ii f_jj)/W`, `2|f_ii f_jj| ≤ (2 - t_i - t_j)/(4η²)`,
  `D₀ = σ₊/(2η²)` and `2 - t_i - t_j ≥ 1`; the gap `σ₊ > |σ₋|` is `JetGap`;
* `bilinearCovariance_entry`: `E[(u_i*U⁰u_j)(u_j*U⁰u_i)] = E|u_i*U⁰u_j|²` (as a complex number)
  for every Hermitian-valued `U` (no integrability needed: `∫ (f : ℂ) = ↑∫ f`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawClauses

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.PassiveCovariance
open scoped ComplexConjugate ComplexOrder

/-- `v*M*u = conj(u*Mv)`. -/
theorem bilinear_conjTranspose {n : Type*} [Fintype n] (u v : n → ℂ) (M : Matrix n n ℂ) :
    bilinear v Mᴴ u = conj (bilinear u M v) := by
  rw [bilinear, bilinear, star_dotProduct, star_mulVec, conjTranspose_conjTranspose,
    ← dotProduct_mulVec]
  rfl

/-- For a Hermitian-valued `U`, the bilinear covariance at `(u, v, v, u)` is the real
`E|u*U⁰v|²`. -/
theorem bilinearCovariance_entry {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] (μ : Measure Ω)
    (U : Ω → Matrix n n ℂ) (hU : ∀ ω, (U ω).IsHermitian) (u v : n → ℂ) :
    bilinearCovariance μ U u v v u =
      ((∫ ω, ‖bilinear u (U ω - matrixExpect μ U) v‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have hE : (matrixExpect μ U).IsHermitian := by
    ext x y
    simp only [conjTranspose_apply, matrixExpect, Matrix.of_apply]
    rw [show star (∫ ω, U ω y x ∂μ) = conj (∫ ω, U ω y x ∂μ) from rfl, ← integral_conj]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      have := congrFun (congrFun (hU ω) x) y
      simpa [conjTranspose_apply] using this)
  rw [bilinearCovariance, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hH : (U ω - matrixExpect μ U)ᴴ = U ω - matrixExpect μ U := by
    rw [conjTranspose_sub, hU ω, hE]
  have hc : bilinear v (U ω - matrixExpect μ U) u = conj (bilinear u (U ω - matrixExpect μ U) v) := by
    conv_lhs => rw [← hH]
    exact bilinear_conjTranspose u v _
  simp only
  rw [hc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

section

variable {W : ℕ} {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)

include hb0 hb h1 h2 hY

/-- `f*f = (I - T)/(4η²)`, `f = R - c₀`. -/
theorem passiveF_adj_mul_self :
    (passiveF b E X)ᴴ * passiveF b E X =
      ((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹ • (1 - passiveTransmission b E X) := by
  have hR := adj_mul_resolvent hb0 hb h1 h2 hY
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hc := cZero_sq b E hη.ne'
  have hcc := conj_cZero b E
  have hη' : (etaZ b E : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hf : (passiveF b E X)ᴴ =
      (passiveResolvent b E X)ᴴ + cZero b E • (1 : Matrix (Fin W) (Fin W) ℂ) := by
    rw [passiveF, conjTranspose_sub, conjTranspose_smul, conjTranspose_one]
    change (passiveResolvent b E X)ᴴ - (conj (cZero b E)) • (1 : Matrix (Fin W) (Fin W) ℂ) = _
    rw [hcc, neg_smul, sub_neg_eq_add]
  rw [hf, passiveF, add_mul, mul_sub, mul_sub, hR, smul_mul_assoc, Matrix.one_mul,
    mul_smul_comm, Matrix.mul_one, smul_mul_assoc, Matrix.one_mul, smul_smul, ← sq, hc,
    passiveTransmission]
  have h4 : ((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹ * ((4 * etaZ b E : ℝ) : ℂ) = (etaZ b E : ℂ)⁻¹ := by
    push_cast; field_simp
  rw [smul_sub (((4 * etaZ b E ^ 2 : ℝ) : ℂ)⁻¹), smul_smul, h4]
  module

/-- `|u*fu|² ≤ (1 - t)/(4η²)` for a unit eigenvector `Tu = tu`. -/
theorem norm_bilinear_passiveF_sq_le (u : Fin W → ℂ) (t : ℝ) (hu : star u ⬝ᵥ u = 1)
    (hTu : passiveTransmission b E X *ᵥ u = (t : ℂ) • u) :
    ‖bilinear u (passiveF b E X) u‖ ^ 2 ≤ (1 - t) / (4 * etaZ b E ^ 2) := by
  set f := passiveF b E X
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hnu : vecNorm u = 1 := by
    have h := star_self_eq u
    rw [hu] at h
    have h' : vecNorm u ^ 2 = 1 := by exact_mod_cast h.symm
    have := vecNorm_nonneg u
    nlinarith
  have hcs : ‖bilinear u f u‖ ≤ vecNorm (f *ᵥ u) := by
    have := norm_star_dotProduct_le u (f *ᵥ u)
    rw [hnu, one_mul] at this; exact this
  have hsq : ((vecNorm (f *ᵥ u) ^ 2 : ℝ) : ℂ) = (((1 - t) / (4 * etaZ b E ^ 2) : ℝ) : ℂ) := by
    rw [← star_self_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      passiveF_adj_mul_self hb0 hb h1 h2 hY, smul_mulVec, sub_mulVec, one_mulVec, hTu,
      dotProduct_smul, dotProduct_sub, dotProduct_smul, hu]
    simp only [smul_eq_mul, mul_one]
    push_cast
    field_simp
  have hsq' : vecNorm (f *ᵥ u) ^ 2 = (1 - t) / (4 * etaZ b E ^ 2) := by exact_mod_cast hsq
  rw [← hsq']
  exact pow_le_pow_left₀ (norm_nonneg _) hcs 2

omit hb0 hb h1 h2 hY in
/-- `u*Tu = t` and `u*u = 1` evaluate the `I`, `I - T` letters. -/
theorem bilinear_one_sub_transmission (u : Fin W → ℂ) (t : ℝ) (hu : star u ⬝ᵥ u = 1)
    (hTu : passiveTransmission b E X *ᵥ u = (t : ℂ) • u) :
    bilinear u (1 - passiveTransmission b E X) u = ((1 - t : ℝ) : ℂ) := by
  rw [bilinear, sub_mulVec, one_mulVec, hTu, dotProduct_sub, dotProduct_smul, hu]
  simp

/-- **The leading tensor at `v = (u_i, u_j, u_j, u_i)` is `≥ (σ₊ - |σ₋|)/(4η²W)`** in real
part, for unit eigenvectors with `t_i, t_j ≤ 1/2`. -/
theorem re_mainTensor_ge (s : ℂ) (ui uj : Fin W → ℂ) (ti tj : ℝ)
    (hui : star ui ⬝ᵥ ui = 1) (huj : star uj ⬝ᵥ uj = 1)
    (hTi : passiveTransmission b E X *ᵥ ui = (ti : ℂ) • ui)
    (hTj : passiveTransmission b E X *ᵥ uj = (tj : ℂ) • uj) (hti : ti ≤ 1 / 2) (htj : tj ≤ 1 / 2)
    (hgap : ‖sigmaMinus b E s‖ ≤ sigmaPlus b) :
    (sigmaPlus b - ‖sigmaMinus b E s‖) / (4 * etaZ b E ^ 2) / W ≤
      (mainTensor b E s X ui uj uj ui).re := by
  have hη := etaZ_pos b E (by linarith) h1 h2
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have hD : transportD0 b E = sigmaPlus b / (2 * etaZ b E ^ 2) := by
    rw [sigmaPlus_eq b E hb0 h1 h2]; field_simp
  set f := passiveF b E X
  set σ := sigmaMinus b E s
  set Fi := bilinear ui f ui
  set Fj := bilinear uj f uj
  have hi := norm_bilinear_passiveF_sq_le hb0 hb h1 h2 hY ui ti hui hTi
  have hj := norm_bilinear_passiveF_sq_le hb0 hb h1 h2 hY uj tj huj hTj
  have h1i : bilinear ui (1 : Matrix (Fin W) (Fin W) ℂ) ui = 1 := by
    rw [bilinear, one_mulVec, hui]
  have h1j : bilinear uj (1 : Matrix (Fin W) (Fin W) ℂ) uj = 1 := by
    rw [bilinear, one_mulVec, huj]
  have hfHi : bilinear ui fᴴ ui = conj Fi := bilinear_conjTranspose ui ui f
  have hfHj : bilinear uj fᴴ uj = conj Fj := bilinear_conjTranspose uj uj f
  have hmain : mainTensor b E s X ui uj uj ui =
      (((transportD0 b E / (2 * W) : ℝ)) : ℂ) * (((1 - tj : ℝ) : ℂ) + ((1 - ti : ℝ) : ℂ)) +
        σ / W * (Fi * Fj) + conj σ / W * (conj Fi * conj Fj) := by
    simp only [mainTensor, crossedTensor, h1i, h1j, bilinear_conjTranspose,
      bilinear_one_sub_transmission ui ti hui hTi,
      bilinear_one_sub_transmission uj tj huj hTj, one_mul, mul_one]
    rfl
  have hre : (mainTensor b E s X ui uj uj ui).re =
      transportD0 b E / (2 * W) * ((1 - tj) + (1 - ti)) + 2 * (σ * (Fi * Fj)).re / W := by
    rw [hmain, ← Complex.ofReal_add]
    have hc : conj σ / (W : ℂ) * (conj Fi * conj Fj) = conj (σ / W * (Fi * Fj)) := by
      simp [map_mul, map_div₀]
    rw [hc, Complex.add_re, Complex.add_re, Complex.conj_re, Complex.re_ofReal_mul]
    have : (σ / (W : ℂ) * (Fi * Fj)).re = (σ * (Fi * Fj)).re / W := by
      rw [div_mul_eq_mul_div, ← Complex.ofReal_natCast, Complex.div_ofReal_re]
    rw [this]; simp only [Complex.ofReal_re]; ring
  rw [hre]
  -- `|Re(σFiFj)| ≤ |σ| |Fi| |Fj|` and `2|Fi||Fj| ≤ |Fi|² + |Fj|²`
  have hσF : -(‖σ‖ * (‖Fi‖ * ‖Fj‖)) ≤ (σ * (Fi * Fj)).re := by
    have := Complex.abs_re_le_norm (σ * (Fi * Fj))
    rw [norm_mul, norm_mul] at this
    linarith [abs_le.mp this]
  have hamgm : 2 * (‖Fi‖ * ‖Fj‖) ≤ ((1 - ti) + (1 - tj)) / (4 * etaZ b E ^ 2) := by
    have := sq_nonneg (‖Fi‖ - ‖Fj‖)
    have : ((1 - ti) + (1 - tj)) / (4 * etaZ b E ^ 2) =
        (1 - ti) / (4 * etaZ b E ^ 2) + (1 - tj) / (4 * etaZ b E ^ 2) := by ring
    nlinarith
  have hσ0 := norm_nonneg σ
  have h4 : 0 < 4 * etaZ b E ^ 2 := by positivity
  set S := (1 - ti) + (1 - tj)
  have hS : 1 ≤ S := by simp only [S]; linarith
  -- lower bound: `S (σ₊ - |σ|)/(4η²W)`
  have key : S * (sigmaPlus b - ‖σ‖) / (4 * etaZ b E ^ 2) ≤
      transportD0 b E / 2 * ((1 - tj) + (1 - ti)) + 2 * (σ * (Fi * Fj)).re := by
    rw [hD]
    have e1 : sigmaPlus b / (2 * etaZ b E ^ 2) / 2 * ((1 - tj) + (1 - ti)) =
        S * sigmaPlus b / (4 * etaZ b E ^ 2) := by simp only [S]; field_simp; ring
    rw [e1]
    have : ‖σ‖ * (2 * (‖Fi‖ * ‖Fj‖)) ≤ ‖σ‖ * (S / (4 * etaZ b E ^ 2)) :=
      mul_le_mul_of_nonneg_left hamgm hσ0
    have e2 : S * (sigmaPlus b - ‖σ‖) / (4 * etaZ b E ^ 2) =
        S * sigmaPlus b / (4 * etaZ b E ^ 2) - ‖σ‖ * (S / (4 * etaZ b E ^ 2)) := by ring
    rw [e2]; nlinarith
  have hgap0 : 0 ≤ (sigmaPlus b - ‖σ‖) / (4 * etaZ b E ^ 2) := div_nonneg (by linarith) h4.le
  have hS' : (sigmaPlus b - ‖σ‖) / (4 * etaZ b E ^ 2) ≤ S * (sigmaPlus b - ‖σ‖) / (4 * etaZ b E ^ 2) := by
    rw [mul_div_assoc]; nlinarith
  rcases hW0.eq_or_lt with hW | hW
  · rw [← hW]; simp
  · have := le_trans hS' key
    have e3 : transportD0 b E / (2 * W) * ((1 - tj) + (1 - ti)) + 2 * (σ * (Fi * Fj)).re / W =
        (transportD0 b E / 2 * ((1 - tj) + (1 - ti)) + 2 * (σ * (Fi * Fj)).re) / W := by
      field_simp
    rw [e3]
    exact div_le_div_of_nonneg_right this hW.le

end

end BlockBand.Transmission.LawClauses
