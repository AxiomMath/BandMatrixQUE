module

public import BlockBand.SourceProcess.ProjSeparator.FarHolds
public import BlockBand.SourceProcess.ProjSeparator.InjNearW2
public import BlockBand.SourceProcess.TagBirth.Ward
public import BlockBand.SourceProcess.ContractingWords.DeltaRefined

/-!
# The near injected trace: Ward scalar step and the mean of `⟨𝒢₁₁⟩`

* `ward_scalar_le`: `ηT = -Im t` gives `|W⁻¹T - d_*| ≤ η⁻¹|W⁻¹t - a|` (`d_*η = -Im a`);
* `trace_near_split`: `Tr(D*DP) = Tr(D*D) - Tr(D*D(I-P))`;
* `trace_g11_mean`: at a passive `X` with integrable `Δ` entries, `Tr𝒢₁₁` is integrable and
  `E Tr𝒢₁₁ = Tr R + Tr(R·EΔ·R)` (`𝒢₁₁ = R + RΔR`);
* `avg_g11_mean_le`: `|W⁻¹(Tr R + Tr(RMR)) - a| ≤ δ₀ + η⁻²‖M‖`;
* `measurable_trace_far`: measurability of `Tr(D*D(I-P))`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open BlockBand.SourceProcess.ContractingWords
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- **Ward scalar step**: `ηT = -Im t` gives `|W⁻¹T - d_*| ≤ η⁻¹|W⁻¹t - a|`. -/
theorem ward_scalar_le {b E : ℝ} (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) {T t : ℂ}
    (hT : ((etaZ b E : ℝ) : ℂ) * T = -((t.im : ℝ) : ℂ)) :
    ‖(W : ℂ)⁻¹ * T - (dStar b : ℂ)‖ ≤ (etaZ b E)⁻¹ * ‖(W : ℂ)⁻¹ * t - matchedA E‖ := by
  have hη : 0 < etaZ b E := etaZ_pos b E (by linarith) h1 h2
  have hηc : ((etaZ b E : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hTr : T = -((t.im : ℝ) : ℂ) / (etaZ b E : ℂ) := by
    rw [eq_div_iff hηc, mul_comm, hT]
  have hd := TagBirth.dStar_mul_eta (b := b) hb h1 h2
  have key : (W : ℂ)⁻¹ * T - (dStar b : ℂ) =
      ((-(etaZ b E)⁻¹ * ((W : ℂ)⁻¹ * t - matchedA E).im : ℝ) : ℂ) := by
    have him : ((W : ℂ)⁻¹ * t - matchedA E).im = (W : ℝ)⁻¹ * t.im - (matchedA E).im := by
      rw [Complex.sub_im, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.im_ofReal_mul]
    rw [him, hTr]
    have hd' : (dStar b : ℂ) = -((matchedA E).im : ℂ) / (etaZ b E : ℂ) := by
      rw [eq_div_iff hηc]; exact_mod_cast hd
    rw [hd']
    push_cast
    field_simp
    ring
  rw [key, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos hη]
  exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (inv_nonneg.mpr hη.le)

/-- `Tr(D*DP) = Tr(D*D) - Tr(D*D(I-P))`. -/
theorem trace_near_split (D : Matrix (Fin W) (Fin 2 × Fin W) ℂ) :
    (Dᴴ * D * nearProjection W).trace =
      (Dᴴ * D).trace - (Dᴴ * D * (1 - nearProjection W)).trace := by
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, sub_sub_cancel]

/-- **`E Tr𝒢₁₁ = Tr R + Tr(R·EΔ·R)`** at a passive `X`. -/
theorem trace_g11_mean {b E : ℝ} (hη : 0 < etaZ b E) {X : Matrix (Fin W) (Fin W) ℂ}
    (hY : (passiveY X).PosSemidef)
    (hD : ∀ i j, Integrable (fun ω => freshDelta b E X ω i j) (freshLaw W b)) :
    Integrable (fun ω => (g11 E (boundaryZ b E) X ω).trace) (freshLaw W b) ∧
      ∫ ω, (g11 E (boundaryZ b E) X ω).trace ∂freshLaw W b =
        (passiveResolvent b E X).trace + (passiveResolvent b E X *
          matrixExpect (freshLaw W b) (freshDelta b E X) * passiveResolvent b E X).trace := by
  set R := passiveResolvent b E X
  have e : (fun ω => (g11 E (boundaryZ b E) X ω).trace) = fun ω => R.trace +
      ∑ x, bilinear (Rᴴ *ᵥ Pi.single x 1) (freshDelta b E X ω) (R *ᵥ Pi.single x 1) := by
    funext ω
    rw [TagBirth.g11_eq_resolvent_add hη hY, Matrix.trace_add, TagBirth.trace_sandwich_eq]
  have hi : ∀ x : Fin W, Integrable (fun ω => bilinear (Rᴴ *ᵥ Pi.single x 1) (freshDelta b E X ω)
      (R *ᵥ Pi.single x 1)) (freshLaw W b) :=
    fun x => FullSource.integrable_bilinear _ hD _ _
  have hs : Integrable (fun ω => ∑ x, bilinear (Rᴴ *ᵥ Pi.single x 1) (freshDelta b E X ω)
      (R *ᵥ Pi.single x 1)) (freshLaw W b) := integrable_finsetSum _ fun x _ => hi x
  rw [e]
  refine ⟨(integrable_const _).add hs, ?_⟩
  rw [integral_add (integrable_const _) hs, integral_const, integral_finsetSum _ fun x _ => hi x,
    TagBirth.trace_sandwich_eq]
  simp only [probReal_univ, one_smul]
  congr 1
  exact Finset.sum_congr rfl fun x _ => FullSource.integral_bilinear _ hD _ _

/-- `|W⁻¹(Tr R + Tr(RMR)) - a| ≤ δ₀ + η⁻²‖M‖`. -/
theorem avg_g11_mean_le {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    (hW : 1 ≤ W) {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
    (M : Matrix (Fin W) (Fin W) ℂ) :
    ‖(W : ℂ)⁻¹ * ((passiveResolvent b E X).trace +
        (passiveResolvent b E X * M * passiveResolvent b E X).trace) - matchedA E‖ ≤
      jetDistance0 b E X + (etaZ b E)⁻¹ ^ 2 * ‖M‖ := by
  set R := passiveResolvent b E X
  have hR := norm_passiveResolvent_le hb0 hb h1 h2 hY
  have e : (W : ℂ)⁻¹ * (R.trace + (R * M * R).trace) - matchedA E =
      ((W : ℂ)⁻¹ * R.trace - matchedA E) + avgTr (R * M * R) := by
    rw [avgTr]; ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ((norm_avgTr_le hW _).trans ?_))
  calc ‖R * M * R‖ ≤ ‖R‖ * ‖M‖ * ‖R‖ :=
        (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right
          (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (etaZ b E)⁻¹ * ‖M‖ * (etaZ b E)⁻¹ := by
        have hη := etaZ_pos b E (by linarith) h1 h2
        have : 0 ≤ (etaZ b E)⁻¹ * ‖M‖ := by positivity
        gcongr
    _ = _ := by ring

theorem measurable_trace_far (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : LayerSample W .oneBlockOnePort =>
      ((freshD b E XX ω)ᴴ * freshD b E XX ω * (1 - nearProjection W)).trace := by
  have hc : Continuous fun M : Matrix (Fin W) (Fin 2 × Fin W) ℂ =>
      (Mᴴ * M * (1 - nearProjection W)).trace := by fun_prop
  exact hc.measurable.comp (FullSource.measurable_freshD_comp b E measurable_const measurable_id)

theorem measurable_trace_tot (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Measurable fun ω : LayerSample W .oneBlockOnePort =>
      ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace := by
  have hc : Continuous fun M : Matrix (Fin W) (Fin 2 × Fin W) ℂ => (Mᴴ * M).trace := by fun_prop
  exact hc.measurable.comp (FullSource.measurable_freshD_comp b E measurable_const measurable_id)

end BlockBand.SourceProcess.ProjSeparator
