module

public import BlockBand.SourceProcess.FullSource.MomentStep
public import BlockBand.SourceProcess.FullSource.Measurability

/-!
# The one-layer step of a transported tag

Fresh law `freshLaw W b`, deterministic Hermitian `𝕏`, `N = freshTransport b E 𝕏`,
`𝓔 = wardNoise b E 𝕏 = NN* - I`, and a deterministic factor `S` of the old tag `Y = S*S`.
With `t = W⁻¹Re Tr(S*S)` and `t₊ = W⁻¹Re Tr((SN)*(SN))` (the transported tag `N*YN`):
* `tagStep_moment`: `E t₊^n ≤ t^n(1 + nc + 2^n((c+σ₂)² + (c+σ_n)^n))` for integer `n ≥ 2`, when
  `‖E𝓔‖ ≤ c` and the centered bilinear entries of `𝓔` have `L^2`, `L^n` norms `≤ σ₂, σ_n`;
* `tagStep_crude`: `t₊ ≤ ‖N‖² t` (deterministic).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSource

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.Transmission.PassiveCovariance BlockBand.Transmission.PassiveLayer
open scoped ENNReal Matrix.Norms.L2Operator

theorem norm_entry_le_op {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    ‖M i j‖ ≤ ‖M‖ := by
  have h := norm_bilinear_le (Pi.single i 1) M (Pi.single j 1)
  have hv : ∀ k : ι, vecNorm (Pi.single k (1 : ℂ)) = 1 := fun k => by
    rw [vecNorm, Finset.sum_eq_single k (fun l _ hl => by simp [hl]) (by simp)]
    simp
  rw [hv, hv, mul_one, one_mul] at h
  refine le_of_eq_of_le ?_ h
  simp [bilinear, dotProduct, mulVec, Pi.single_apply]

theorem norm_mul_conjTranspose_le {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℂ) :
    ‖N * Nᴴ‖ ≤ ‖N‖ ^ 2 := by
  rw [sq]
  exact (Matrix.l2_opNorm_mul N Nᴴ).trans (le_of_eq (by rw [Matrix.l2_opNorm_conjTranspose]))

variable {W : ℕ}

/-- Entries of the Ward noise are integrable once `‖N‖ ∈ L²`. -/
theorem integrable_wardNoise_entry {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {C : ℝ} (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤
      ENNReal.ofReal C) (a c : Fin 2 × Fin W) :
    Integrable (fun ω => wardNoise b E XX ω a c) (freshLaw W b) := by
  have hm : Measurable fun ω => freshTransport b E XX ω :=
    measurable_freshTransport_comp b E measurable_const measurable_id
  have hmw : Measurable fun ω => wardNoise b E XX ω :=
    measurable_wardNoise_comp b E measurable_const measurable_id
  have hmem : MemLp (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) :=
    lt_of_le_of_lt hN ENNReal.ofReal_lt_top
  have hsq : Integrable (fun ω => ‖freshTransport b E XX ω‖ ^ 2) (freshLaw W b) := by
    have := hmem.integrable_norm_rpow'
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs] at this
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    rw [abs_of_nonneg (norm_nonneg _), Real.rpow_two]
  refine (hsq.add (integrable_const 1)).mono' hmw.eval_matrix.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  refine (norm_entry_le_op _ a c).trans ?_
  simp only [wardNoise]
  refine (norm_sub_le _ _).trans (add_le_add (norm_mul_conjTranspose_le _) ?_)
  exact norm_one_matrix_le

section Tag

variable {m : Type*} [Fintype m]

/-- The transported tag mass `t₊ = W⁻¹Re Tr((SN)*(SN))`. -/
def tagPlus (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) : ℝ :=
  (W : ℝ)⁻¹ * ((S * freshTransport b E XX ω)ᴴ * (S * freshTransport b E XX ω)).trace.re

theorem tagPlus_nonneg (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    0 ≤ tagPlus b E XX S ω :=
  mul_nonneg (by positivity) (trace_factor_re_nonneg _)

theorem tagPlus_eq (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    tagPlus b E XX S ω = (W : ℝ)⁻¹ * (Sᴴ * S).trace.re +
      (W : ℝ)⁻¹ * (Sᴴ * S * wardNoise b E XX ω).trace.re := by
  rw [tagPlus, trace_transport, Complex.add_re, mul_add, wardNoise]

/-- **Crude transport bound**: `t₊ ≤ ‖N‖² t`. -/
theorem tagStep_crude (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) (ω : LayerSample W .oneBlockOnePort) :
    tagPlus b E XX S ω ≤ ‖freshTransport b E XX ω‖ ^ 2 * ((W : ℝ)⁻¹ * (Sᴴ * S).trace.re) := by
  set N := freshTransport b E XX ω
  have h : ((S * N)ᴴ * (S * N)).trace.re ≤ ‖N‖ ^ 2 * (Sᴴ * S).trace.re := by
    have e : ((S * N)ᴴ * (S * N)).trace = (Sᴴ * S * (N * Nᴴ)).trace := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc]
    rw [e]
    exact (Complex.re_le_norm _).trans ((norm_trace_factor_le S _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_conjTranspose_le N) (trace_factor_re_nonneg S)))
  rw [tagPlus]
  have hW : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hW]

/-- **The one-layer moment step of a tag.** -/
theorem tagStep_moment {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (S : Matrix m (Fin 2 × Fin W) ℂ) {c σ₂ σn CN : ℝ} (hc0 : 0 ≤ c) (hσ₂ : 0 ≤ σ₂)
    (hσn : 0 ≤ σn) {n : ℕ} (hn : 2 ≤ n)
    (hc : ‖matrixExpect (freshLaw W b) (wardNoise b E XX)‖ ≤ c)
    (hfl₂ : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal 2) (freshLaw W b) ≤
        ENNReal.ofReal (σ₂ * vecNorm u * vecNorm v))
    (hfln : ∀ u v : Fin 2 × Fin W → ℂ, eLpNorm (fun ω => bilinear u (wardNoise b E XX ω -
      matrixExpect (freshLaw W b) (wardNoise b E XX)) v) (ENNReal.ofReal n) (freshLaw W b) ≤
        ENNReal.ofReal (σn * vecNorm u * vecNorm v))
    (hN : eLpNorm (fun ω => ‖freshTransport b E XX ω‖) 2 (freshLaw W b) ≤ ENNReal.ofReal CN) :
    Integrable (fun ω => tagPlus b E XX S ω ^ n) (freshLaw W b) ∧
      ∫ ω, tagPlus b E XX S ω ^ n ∂freshLaw W b ≤
        ((W : ℝ)⁻¹ * (Sᴴ * S).trace.re) ^ n *
          (1 + n * c + 2 ^ n * ((c + σ₂) ^ 2 + (c + σn) ^ n)) := by
  set μ := freshLaw W b
  set T := (Sᴴ * S).trace.re
  have hT : 0 ≤ T := trace_factor_re_nonneg S
  have hw : (0 : ℝ) ≤ (W : ℝ)⁻¹ := by positivity
  have hmw : Measurable fun ω => wardNoise b E XX ω :=
    measurable_wardNoise_comp b E measurable_const measurable_id
  have hint := integrable_wardNoise_entry (b := b) (E := E) XX hN
  obtain ⟨hm2, hmean, habs, hcen2⟩ := trace_noise (ν := μ) (wardNoise b E XX) hmw hint S hc
    (by norm_num) hσ₂ hfl₂
  obtain ⟨-, -, -, hcenn⟩ := trace_noise (ν := μ) (wardNoise b E XX) hmw hint S hc
    (by exact_mod_cast (show 1 ≤ n by omega)) hσn hfln
  set y : LayerSample W .oneBlockOnePort → ℝ := fun ω => (Sᴴ * S * wardNoise b E XX ω).trace.re
  set Y : LayerSample W .oneBlockOnePort → ℝ := fun ω => (W : ℝ)⁻¹ * y ω
  have hYm : AEStronglyMeasurable Y μ := hm2.const_mul _
  have hYmean : ∫ ω, Y ω ∂μ = (W : ℝ)⁻¹ * ∫ ω, y ω ∂μ := integral_const_mul _ _
  have hYabs : |∫ ω, Y ω ∂μ| ≤ c * ((W : ℝ)⁻¹ * T) := by
    rw [hYmean, abs_mul, abs_of_nonneg hw]
    nlinarith [mul_le_mul_of_nonneg_left habs hw]
  have hcen : ∀ q σ : ℝ, 0 ≤ σ →
      eLpNorm (fun ω => y ω - ∫ ω', y ω' ∂μ) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (σ * T) →
      eLpNorm (fun ω => Y ω - ∫ ω', Y ω' ∂μ) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (σ * ((W : ℝ)⁻¹ * T)) := by
    intro q σ hσ h
    have e : (fun ω => Y ω - ∫ ω', Y ω' ∂μ) = fun ω => (W : ℝ)⁻¹ * (y ω - ∫ ω', y ω' ∂μ) := by
      funext ω; simp only [Y, hYmean]; ring
    rw [e]
    have h' := (MomBd.const_mul (μ := μ) ⟨(hm2.sub aestronglyMeasurable_const), h⟩ hw).2
    refine h'.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  have hB2 := momBd_of_centered hYm (by norm_num) (by positivity) hYabs
    (hcen 2 σ₂ hσ₂ hcen2)
  have hBn := momBd_of_centered hYm (by exact_mod_cast (show 1 ≤ n by omega)) (by positivity)
    hYabs (hcen n σn hσn hcenn)
  have hpos : ∀ ω, 0 ≤ (W : ℝ)⁻¹ * T + Y ω := fun ω => by
    have := tagPlus_nonneg b E XX S ω
    rwa [tagPlus_eq] at this
  have hmean' : ∫ ω, Y ω ∂μ ≤ c * ((W : ℝ)⁻¹ * T) := (le_abs_self _).trans hYabs
  have hstep := integral_pow_step hYm (mul_nonneg hw hT) hc0 hσ₂ hσn hn hpos hmean'
    (hB2.of_le (by nlinarith [mul_nonneg hw hT])) (hBn.of_le (by nlinarith [mul_nonneg hw hT]))
  have e : (fun ω => tagPlus b E XX S ω ^ n) = fun ω => ((W : ℝ)⁻¹ * T + Y ω) ^ n := by
    funext ω; rw [tagPlus_eq]
  rw [e]
  exact hstep

end Tag

end BlockBand.SourceProcess.FullSource
