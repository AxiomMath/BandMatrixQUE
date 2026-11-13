module

public import BlockBand.SourceProcess.SmallLeak.Birth
public import BlockBand.SourceProcess.SmallLeak.GrowthCrude
public import BlockBand.SourceProcess.TagBirth.FreshTrace
public import BlockBand.Transmission.PassiveCovariance.ResolventBound

/-!
# One layer of the leakage with the newborn tag, in `lintegral` form

`leak_layer_step`: for a positive old `Q = R*R` and a birth weight `c ≥ 0`,
`∫⁻ Re Tr F(N*QN + c D₊*D₊) ≤ ℓ + (m/η)γ√g + ((m²+σ²)/(2η²))γg + c B g/(4η²)`,
with `B ≥ E(1 + ‖Δ‖/η)²` (`𝒢₁₁K = 1 + RΔ`, `birthFactor_norm_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.Transmission.PassiveLayer BlockBand.Transmission.PassiveCovariance
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ENNReal

variable {W : ℕ}

/-- `‖𝒢₁₁K‖ ≤ 1 + ‖Δ‖/η` for a passive old `X`. -/
theorem birthFactor_norm_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (passiveY (nearSchur (boundaryZ b E) XX)).PosSemidef) (f : LayerSample W .oneBlockOnePort) :
    ‖birthFactor b E XX f‖ ≤
      1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ / etaZ b E := by
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) h1 h2
  set X := nearSchur (boundaryZ b E) XX
  set R := passiveResolvent b E X
  have hK := (isUnit_iff_isUnit_det _).mp (TagBirth.isUnit_pencil hη hY)
  have hRK : R * (boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - X) = 1 :=
    Matrix.nonsing_inv_mul _ hK
  have e : birthFactor b E XX f = 1 + R * freshDelta b E X f := by
    have hg := TagBirth.g11_eq_resolvent_add hη hY f
    show g11 E (boundaryZ b E) X f * (boundaryZ b E • 1 - X) = _
    rw [hg, Matrix.add_mul, hRK, Matrix.mul_assoc, Matrix.mul_assoc, hRK, Matrix.mul_one]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hR : ‖R‖ ≤ (etaZ b E)⁻¹ := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have h1' : ‖(1 : Matrix (Fin W) (Fin W) ℂ)‖ ≤ 1 := norm_one_matrix_le
  have h2' := norm_mul_le R (freshDelta b E X f)
  have : ‖R‖ * ‖freshDelta b E X f‖ ≤ ‖freshDelta b E X f‖ / etaZ b E := by
    rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_right hR (norm_nonneg _)
  linarith

/-- **One layer of the leakage with the newborn tag.** -/
theorem leak_layer_step {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hY : (passiveY (nearSchur (boundaryZ b E) XX)).PosSemidef)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) (hA2 : A * A = A)
    {κ : Type*} [Fintype κ] (R : Matrix κ (Fin 2 × Fin W) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hΔ : ∀ x y, Integrable (fun f => freshDelta b E (nearSchur (boundaryZ b E) XX) f x y)
      (freshLaw W b))
    (hmeas : Measurable (freshDelta b E (nearSchur (boundaryZ b E) XX)))
    {m σ : ℝ} (hσ : 0 ≤ σ)
    (hm : ‖matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))‖ ≤ m)
    (hfl : ∀ u v : Fin W → ℂ, eLpNorm (fun f => bilinear u
      (freshDelta b E (nearSchur (boundaryZ b E) XX) f -
        matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))) v)
      (ENNReal.ofReal 2) (freshLaw W b) ≤ ENNReal.ofReal (σ * vecNorm u * vecNorm v))
    (hNi : Integrable (fun f => ‖freshTransport b E XX f‖ ^ 2) (freshLaw W b))
    {B : ℝ} (hBi : Integrable (fun f => (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ /
      etaZ b E) ^ 2) (freshLaw W b))
    (hB : ∫ f, (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ / etaZ b E) ^ 2
      ∂freshLaw W b ≤ B) :
    ∫⁻ f, ENNReal.ofReal (farEmbed A * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) *
        freshTransport b E XX f + ((c : ℝ) : ℂ) • ((freshD b E XX f)ᴴ * freshD b E XX f))).trace.re
        ∂freshLaw W b ≤
      ENNReal.ofReal ((farEmbed A * (Rᴴ * R) * farEmbed A).trace.re +
        m / etaZ b E * hsNorm R ^ 2 * Real.sqrt (fluxAt b E XX A) +
        (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * fluxAt b E XX A +
        c * B * fluxAt b E XX A / (4 * etaZ b E ^ 2)) := by
  have hη : 0 < etaZ b E := boundaryZ_im_pos (by linarith) h1 h2
  set μ := freshLaw W b
  set F := farEmbed A
  set g := fluxAt b E XX A
  set Δ := freshDelta b E (nearSchur (boundaryZ b E) XX)
  set X1 : LayerSample W .oneBlockOnePort → ℝ := fun f =>
    (F * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) * freshTransport b E XX f)).trace.re
  set Y1 : LayerSample W .oneBlockOnePort → ℝ := fun f =>
    (F * ((freshD b E XX f)ᴴ * freshD b E XX f)).trace.re
  have hF : Fᴴ = F := farEmbed_conjTranspose_of hA
  have hF2 : F * F = F := by rw [farEmbed_mul, hA2]
  have hg0 : 0 ≤ g := fluxAt_nonneg b E XX hA
  -- splitting
  have hsplit : ∀ f, (F * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) * freshTransport b E XX f +
      ((c : ℝ) : ℂ) • ((freshD b E XX f)ᴴ * freshD b E XX f))).trace.re = X1 f + c * Y1 f := by
    intro f
    simp only [X1, Y1, Matrix.mul_add, Matrix.trace_add, Complex.add_re, Matrix.mul_smul,
      Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  have hX0 : ∀ f, 0 ≤ X1 f := fun f => by
    have e : (F * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) * freshTransport b E XX f)).trace =
        ((R * freshTransport b E XX f * F)ᴴ * (R * freshTransport b E XX f * F)).trace := by
      calc _ = (F * (F * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) * freshTransport b E XX f))).trace :=
            by rw [← Matrix.mul_assoc F F, hF2]
        _ = (F * ((freshTransport b E XX f)ᴴ * (Rᴴ * R) * freshTransport b E XX f) * F).trace := by
            rw [Matrix.trace_mul_comm F]
        _ = _ := by simp only [Matrix.conjTranspose_mul, hF, Matrix.mul_assoc]
    show 0 ≤ (F * _).trace.re
    rw [e]; exact FullSource.trace_factor_re_nonneg _
  have hY0 : ∀ f, 0 ≤ Y1 f := fun f => by
    have hb := birth_leak_le hη XX f hA hA2
    have e : (F * ((freshD b E XX f)ᴴ * freshD b E XX f)).trace =
        ((freshD b E XX f * F)ᴴ * (freshD b E XX f * F)).trace := by
      calc _ = (F * (F * ((freshD b E XX f)ᴴ * freshD b E XX f))).trace := by
            rw [← Matrix.mul_assoc F F, hF2]
        _ = (F * ((freshD b E XX f)ᴴ * freshD b E XX f) * F).trace := by rw [Matrix.trace_mul_comm F]
        _ = _ := by simp only [Matrix.conjTranspose_mul, hF, Matrix.mul_assoc]
    show 0 ≤ (F * _).trace.re
    rw [e]; exact FullSource.trace_factor_re_nonneg _
  -- the transported old source
  have hX1i : Integrable X1 μ := by
    have hmX : Measurable X1 := by
      have hN := FullSource.measurable_freshTransport_comp (W := W) b E (XX := fun _ => XX)
        measurable_const measurable_id
      exact measurable_trace_re (measurable_matrix_mul' measurable_const
        (measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hN)
          measurable_const) hN))
    refine Integrable.mono' (hNi.mul_const (hsNorm R ^ 2)) hmX.aestronglyMeasurable
      (Filter.Eventually.of_forall fun f => ?_)
    rw [Real.norm_of_nonneg (hX0 f)]
    set N := freshTransport b E XX f
    have hle : X1 f ≤ ((R * N)ᴴ * (R * N)).trace.re := by
      have hp : ((R * N)ᴴ * (R * N)).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
      have := ClosingLeak.re_trace_proj_mul_le hF2 hF hp
      have e : (R * N)ᴴ * (R * N) = Nᴴ * (Rᴴ * R) * N := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      rw [e] at this ⊢; exact this
    rw [trace_conjTranspose_mul_self, Complex.ofReal_re] at hle
    have h3 : hsNorm (R * N) ≤ hsNorm R * ‖N‖ := by
      rw [← hsNorm_conjTranspose, Matrix.conjTranspose_mul, ← hsNorm_conjTranspose R]
      have := hsNorm_mul_le_opNorm Nᴴ Rᴴ
      rw [Matrix.l2_opNorm_conjTranspose] at this
      linarith [mul_comm ‖N‖ (hsNorm Rᴴ)]
    have h4 := pow_le_pow_left₀ (hsNorm_nonneg _) h3 2
    nlinarith [hsNorm_nonneg R, norm_nonneg N]
  have hX1 : ∫ f, X1 f ∂μ ≤ (F * (Rᴴ * R) * F).trace.re + m / etaZ b E * hsNorm R ^ 2 *
      Real.sqrt g + (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * g :=
    leak_fresh_mean hη hA hA2 R hΔ hmeas hσ hm hfl
  -- the newborn tag
  have hY1 : ∀ f, Y1 f ≤ (1 + ‖Δ f‖ / etaZ b E) ^ 2 / (4 * etaZ b E ^ 2) * g := fun f => by
    refine (birth_leak_le hη XX f hA hA2).trans (mul_le_mul_of_nonneg_right ?_ hg0)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (birthFactor_norm_le hb0 hb h1 h2 hY f) 2
  calc ∫⁻ f, ENNReal.ofReal _ ∂μ = ∫⁻ f, ENNReal.ofReal (X1 f + c * Y1 f) ∂μ := by
        congr 1; funext f; rw [hsplit f]
    _ ≤ ∫⁻ f, (ENNReal.ofReal (X1 f) + ENNReal.ofReal (c * (1 + ‖Δ f‖ / etaZ b E) ^ 2 /
          (4 * etaZ b E ^ 2) * g)) ∂μ := by
        refine lintegral_mono fun f => (ENNReal.ofReal_add_le).trans (add_le_add le_rfl
          (ENNReal.ofReal_le_ofReal ?_))
        have := mul_le_mul_of_nonneg_left (hY1 f) hc
        calc c * Y1 f ≤ c * ((1 + ‖Δ f‖ / etaZ b E) ^ 2 / (4 * etaZ b E ^ 2) * g) := this
          _ = _ := by ring
    _ = ENNReal.ofReal (∫ f, X1 f ∂μ) + ENNReal.ofReal (∫ f, c * (1 + ‖Δ f‖ / etaZ b E) ^ 2 /
          (4 * etaZ b E ^ 2) * g ∂μ) := by
        have hI2 : Integrable (fun f => c * (1 + ‖Δ f‖ / etaZ b E) ^ 2 / (4 * etaZ b E ^ 2) * g)
            μ := ((hBi.const_mul c).div_const _).mul_const g
        rw [lintegral_add_left' (hX1i.aemeasurable.ennreal_ofReal),
          ofReal_integral_eq_lintegral_ofReal hX1i (ae_of_all _ hX0),
          ofReal_integral_eq_lintegral_ofReal hI2 (ae_of_all _ fun f => by positivity)]
    _ ≤ ENNReal.ofReal ((F * (Rᴴ * R) * F).trace.re + m / etaZ b E * hsNorm R ^ 2 *
          Real.sqrt g + (m ^ 2 + σ ^ 2) / (2 * etaZ b E ^ 2) * hsNorm R ^ 2 * g) +
          ENNReal.ofReal (c * B * g / (4 * etaZ b E ^ 2)) := by
        refine add_le_add (ENNReal.ofReal_le_ofReal hX1) (ENNReal.ofReal_le_ofReal ?_)
        rw [integral_mul_const, integral_div, integral_const_mul]
        have := mul_le_mul_of_nonneg_left hB hc
        have h4 : 0 < 4 * etaZ b E ^ 2 := by positivity
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right h4]
        exact mul_le_mul_of_nonneg_right this hg0
    _ = _ := by
        have hℓ : 0 ≤ (F * (Rᴴ * R) * F).trace.re := by
          have : F * (Rᴴ * R) * F = (R * F)ᴴ * (R * F) := by
            simp only [Matrix.conjTranspose_mul, hF, Matrix.mul_assoc]
          rw [this]; exact FullSource.trace_factor_re_nonneg _
        have hm0 : 0 ≤ m := (norm_nonneg _).trans hm
        have hB0 : 0 ≤ B := (integral_nonneg fun f => sq_nonneg _).trans hB
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]

end BlockBand.SourceProcess.SmallLeak
