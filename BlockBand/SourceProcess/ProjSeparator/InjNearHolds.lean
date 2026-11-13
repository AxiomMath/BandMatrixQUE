module

public import BlockBand.SourceProcess.ProjSeparator.InjNearAlg
public import BlockBand.SourceProcess.ContractingWords.WardRefined

/-!
# The near injected trace `InjNearMeanW2`

`injNearMeanW2_holds`: under `GaussianAbsorptionContract` and `GaussianLpGradient`, the near
injected trace satisfies `|W⁻¹E Tr(D*DP) − d_*| ≤ C(δ₀ + g/W + W⁻²)`, by the Ward identity and the
integrability of the far part. Measure `freshLaw W b`, Hermitian `𝕏`, `X = nearSchur z 𝕏`; `W₀`
from `b, κ`; uniform in `W ≥ W₀`, `E ∈ bulkInterval κ` and Hermitian `𝕏`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ProjSeparator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open BlockBand.Transmission.PassiveLayer BlockBand.SourceProcess.ContractingWords
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- The real arithmetic of `InjNearMeanW2`. -/
theorem inj_arith {e a δ m CM CF g w : ℝ} (he0 : 0 ≤ e) (hea : e ≤ a) (hδ : 0 ≤ δ) (hm0 : 0 ≤ m)
    (hm : m ≤ CM * (δ + w ^ 2)) (hCM : 0 ≤ CM) (hCF : 0 ≤ CF) (hg : 0 ≤ g) (hw : 0 ≤ w) :
    e * (δ + e ^ 2 * m) + w * (CF * g) ≤ (a + a ^ 3 * CM + CF) * (δ + g * w + w ^ 2) := by
  have ha0 : 0 ≤ a := he0.trans hea
  have h3 : e ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ he0 hea 3
  have t1 : e * δ ≤ a * δ := mul_le_mul_of_nonneg_right hea hδ
  have t2 : e ^ 3 * m ≤ a ^ 3 * (CM * (δ + w ^ 2)) :=
    mul_le_mul h3 hm hm0 (by positivity)
  have e1 : e * (δ + e ^ 2 * m) = e * δ + e ^ 3 * m := by ring
  rw [e1]
  have hgw : 0 ≤ g * w := mul_nonneg hg hw
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg w
  nlinarith [mul_nonneg ha0 hgw, mul_nonneg ha0 hw2, mul_nonneg (mul_nonneg (pow_nonneg ha0 3) hCM) hgw,
    mul_nonneg hCF hδ, mul_nonneg hCF hw2]

/-- **`InjNearMeanW2` from input hypotheses.** -/
theorem injNearMeanW2_holds (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient) :
    InjNearMeanW2 := by
  intro b hb0 hb κ hκ
  obtain ⟨CM, WM, hCM, hM⟩ := deltaMean_all hGA hLp b hb0 hb κ hκ
  obtain ⟨CI, WI, -, hI⟩ := FullSource.delta_integrable hGA b hb0 hb κ hκ
  obtain ⟨CF, WF, hCF, hF⟩ := injFarTrace_holds hGA b hb0 hb κ hκ
  obtain ⟨C2, W2, hC2, h2m⟩ := FullSource.delta_moments hGA b hb0 hb κ hκ 2 (by norm_num)
  set ηL := (1 - b) * κ / 4
  have hηL : 0 < ηL := by
    have : 0 < 1 - b := by linarith
    positivity
  refine ⟨ηL⁻¹ + ηL⁻¹ ^ 3 * CM + CF, max (max WM WI) (max (max WF W2) 1), by positivity, ?_⟩
  intro W hW E hE XX hXX X
  simp only [max_le_iff] at hW
  obtain ⟨⟨hWM, hWI⟩, ⟨hWF, hW2⟩, hW1⟩ := hW
  have hE1 : -2 < E := by have := hE.1; linarith
  have hE2 : E < 2 := by have := hE.2; linarith
  have hη := etaZ_pos b E (by linarith) hE1 hE2
  have hηge : ηL ≤ etaZ b E := FullSource.etaZ_ge hb0 hb hκ hE
  have hY : (passiveY X).PosSemidef := FullSource.nearSchur_passive hη hXX
  have hg0 : 0 ≤ conductanceOf (passiveTransmission b E X) :=
    FullSourceCovariance.conductance_nonneg b E hη.le hY
  set μ := freshLaw W b
  set η := etaZ b E
  set fT : LayerSample W .oneBlockOnePort → ℂ := fun ω => ((freshD b E XX ω)ᴴ * freshD b E XX ω).trace
  set fF : LayerSample W .oneBlockOnePort → ℂ :=
    fun ω => ((freshD b E XX ω)ᴴ * freshD b E XX ω * (1 - nearProjection W)).trace
  set t : LayerSample W .oneBlockOnePort → ℂ := fun ω => (g11 E (boundaryZ b E) X ω).trace
  obtain ⟨hD, -⟩ := hI W hWI E hE X hY
  obtain ⟨hti, htm⟩ := trace_g11_mean hη hY hD
  -- the Ward identity, a.s.
  have hae : ∀ᵐ ω ∂μ, fT ω = (((-(t ω).im / η : ℝ)) : ℂ) := by
    filter_upwards [ae_good W hb0 hW1] with ω hω
    have h := TagBirth.eta_trace_freshD b E hXX hη hω.1 hω.2
    have hηc : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    simp only [fT, t]
    rw [Complex.ofReal_div, Complex.ofReal_neg, eq_div_iff hηc, mul_comm]
    exact h
  have hti' : Integrable (fun ω => (((-(t ω).im / η : ℝ)) : ℂ)) μ :=
    ((hti.im.neg).div_const η).ofReal
  have hfT : Integrable fT μ := hti'.congr (hae.mono fun ω h => h.symm)
  have hIT : ((η : ℝ) : ℂ) * ∫ ω, fT ω ∂μ = -((((∫ ω, t ω ∂μ).im : ℝ)) : ℂ) := by
    rw [integral_congr_ae hae, integral_complex_ofReal, integral_div, integral_neg]
    have him := integral_im hti
    simp only [RCLike.im_to_complex] at him
    rw [him]
    have hηc : ((η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    push_cast
    field_simp
    rfl
  -- the far part is integrable
  obtain ⟨hint2, -⟩ := sq_moment_of_momBd hC2 (h2m W hW2 E hE X hY)
  set S := conductanceOf (passiveTransmission b E X) / (4 * η ^ 2)
  have hG : Integrable (fun ω => (2 + 2 * η⁻¹ ^ 2 * ‖freshDelta b E X ω‖ ^ 2) * S) μ :=
    ((integrable_const 2).add (hint2.const_mul (2 * η⁻¹ ^ 2))).mul_const S
  have hfF : Integrable fF μ := by
    refine hG.mono' (measurable_trace_far b E XX).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    refine (norm_trace_far_le hb0 hb hE1 hE2 hXX ω).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hx : 0 ≤ η⁻¹ * ‖freshDelta b E X ω‖ := by positivity
    nlinarith [sq_nonneg (η⁻¹ * ‖freshDelta b E X ω‖ - 1)]
  -- assemble
  have hsplit : ∫ y, ((freshD b E XX y)ᴴ * freshD b E XX y * nearProjection W).trace ∂μ =
      ∫ ω, fT ω ∂μ - ∫ ω, fF ω ∂μ := by
    rw [← integral_sub hfT hfF]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => trace_near_split _)
  rw [hsplit]
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW1
  have e : (W : ℂ)⁻¹ * (∫ ω, fT ω ∂μ - ∫ ω, fF ω ∂μ) - (dStar b : ℂ) =
      ((W : ℂ)⁻¹ * ∫ ω, fT ω ∂μ - (dStar b : ℂ)) - (W : ℂ)⁻¹ * ∫ ω, fF ω ∂μ := by ring
  rw [e]
  have hA := ward_scalar_le (W := W) hb hE1 hE2 hIT
  rw [htm] at hA
  have hB := avg_g11_mean_le hb0 hb hE1 hE2 hW1 hY (matrixExpect μ (freshDelta b E X))
  have hMb := hM W hWM E hE X hY
  have hFb := hF W hWF E hE XX hXX
  have hFar : ‖(W : ℂ)⁻¹ * ∫ ω, fF ω ∂μ‖ ≤ (W : ℝ)⁻¹ * (CF * conductanceOf
      (passiveTransmission b E X)) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hFb (by positivity)
  have hηi : η⁻¹ ≤ ηL⁻¹ := inv_anti₀ hηL hηge
  have har := inj_arith (inv_nonneg.mpr hη.le) hηi (norm_nonneg _ : 0 ≤ jetDistance0 b E X)
    (norm_nonneg _) hMb hCM hCF hg0 (by positivity : (0 : ℝ) ≤ (W : ℝ)⁻¹)
  have hgW : conductanceOf (passiveTransmission b E X) / W =
      conductanceOf (passiveTransmission b E X) * (W : ℝ)⁻¹ := div_eq_mul_inv _ _
  rw [hgW]
  refine (norm_sub_le _ _).trans ((add_le_add (hA.trans
    (mul_le_mul_of_nonneg_left hB (inv_nonneg.mpr hη.le))) hFar).trans har)

end BlockBand.SourceProcess.ProjSeparator
