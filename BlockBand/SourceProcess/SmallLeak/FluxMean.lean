module

public import BlockBand.SourceProcess.SmallLeak.StepAlg
public import BlockBand.SourceProcess.CompleteSourceGap.MeanCases

/-!
# The one-layer mean bound of the omitted flux

At a deterministic Hermitian old two-port `𝕏` (scattering `𝕊`, unitary; `P' = 𝕊*P𝕊`) and a far
projection `F = farEmbed A`, the transported flux `g₊ = Re Tr F(N*(P'-P)N + P)F` (the exact
`J₊ = N*JN`, `J = P' - P`) satisfies
`E_f g₊ ≤ (1 + ‖EΔ‖/η) g`, `g = Re Tr FP'F` (`flux_fresh_mean`).
Proof: `flux_step_le` (`P' ⪯ 1`), linearity of the cross term in `Δ`, and
`|Re Tr V*(EΔ)*Y| ≤ ‖EΔ‖‖V‖₂‖Y‖₂` with `‖V‖₂ = ‖ιℝF‖₂ = √g/(2η)` and `‖ιP'F‖₂ ≤ √g`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.SmallLeak

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.FullSourceStops
open BlockBand.SourceProcess.CompleteSourceGap
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator ComplexConjugate

variable {W : ℕ}

/-!
## A random matrix entering linearly through `Δ*`
-/

section Lin

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {κ : Type*} [Fintype κ]

theorem trace_lin_eq (D : Matrix (Fin W) (Fin W) ℂ) (V Y : Matrix (Fin W) κ ℂ) :
    (Vᴴ * Dᴴ * Y).trace = ∑ k, ∑ y, ∑ x, conj (V x k) * conj (D y x) * Y y k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    RCLike.star_def, Finset.sum_mul]

theorem integral_trace_lin (D : Ω → Matrix (Fin W) (Fin W) ℂ)
    (hD : ∀ x y, Integrable (fun ω => D ω x y) μ) (V Y : Matrix (Fin W) κ ℂ) :
    Integrable (fun ω => (Vᴴ * (D ω)ᴴ * Y).trace.re) μ ∧
      ∫ ω, (Vᴴ * (D ω)ᴴ * Y).trace.re ∂μ = (Vᴴ * (matrixExpect μ D)ᴴ * Y).trace.re := by
  have hc : ∀ y x, Integrable (fun ω => conj (D ω y x)) μ := fun y x => by
    simpa using Complex.conjCLE.toContinuousLinearMap.integrable_comp (hD y x)
  have hi : ∀ k y x, Integrable (fun ω => conj (V x k) * conj (D ω y x) * Y y k) μ :=
    fun k y x => ((hc y x).const_mul _).mul_const _
  have hI : Integrable (fun ω => (Vᴴ * (D ω)ᴴ * Y).trace) μ := by
    simp only [trace_lin_eq]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun y _ =>
      integrable_finsetSum _ fun x _ => hi k y x
  refine ⟨hI.re, ?_⟩
  have hre := integral_re hI
  simp only [RCLike.re_to_complex] at hre
  rw [hre]
  congr 1
  simp only [trace_lin_eq]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun y _ =>
    integrable_finsetSum _ fun x _ => hi k y x]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun y _ => integrable_finsetSum _ fun x _ => hi k y x]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_finsetSum _ fun x _ => hi k y x]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_mul_const, integral_const_mul, integral_conj]
  rfl

end Lin

theorem hsNorm_smul {m n : Type*} [Fintype m] [Fintype n] (c : ℂ) (A : Matrix m n ℂ) :
    hsNorm (c • A) = ‖c‖ * hsNorm A := by
  rw [hsNorm, hsNorm]
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem abs_trace_lin_le {κ : Type*} [Fintype κ] (D : Matrix (Fin W) (Fin W) ℂ)
    (V Y : Matrix (Fin W) κ ℂ) : |(Vᴴ * Dᴴ * Y).trace.re| ≤ ‖D‖ * hsNorm V * hsNorm Y := by
  have e : Vᴴ * Dᴴ * Y = (D * V)ᴴ * Y := by rw [Matrix.conjTranspose_mul]
  rw [e]
  refine (Complex.abs_re_le_norm _).trans ((norm_trace_mul_le _ _).trans ?_)
  rw [hsNorm_conjTranspose]
  exact mul_le_mul_of_nonneg_right (hsNorm_mul_le_opNorm D V) (hsNorm_nonneg _)

/-!
## The deterministic layer
-/

theorem nearProjection_mul_nearSel_conj : nearProjection W * (nearSel W)ᴴ = (nearSel W)ᴴ := by
  rw [← FullSourceCovariance.nearSel_conj_mul_nearSel, Matrix.mul_assoc,
    nearSel_mul_conjTranspose, Matrix.mul_one]

theorem one_sub_nearProjection_psd : (1 - nearProjection W).PosSemidef := by
  have h1 : (1 - nearProjection W)ᴴ = 1 - nearProjection W := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, nearProjection_conjTranspose]
  have h2 : (1 - nearProjection W) * (1 - nearProjection W) = 1 - nearProjection W := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, nearProjection_mul_self]; simp
  have := Matrix.posSemidef_conjTranspose_mul_self (1 - nearProjection W)
  rwa [h1, h2] at this

theorem farEmbed_conjTranspose_of {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) :
    (farEmbed A)ᴴ = farEmbed A := by rw [farEmbed_conjTranspose, hA]

/-- `‖ιP'F‖₂² = g`, `g = Re Tr FP'F`. -/
theorem hsNorm_sq_nearOut {b E : ℝ} (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) :
    hsNorm (nearSel W * twoPortScattering b E XX * farEmbed A) ^ 2 =
      (farEmbed A * ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
        farEmbed A).trace.re := by
  have h := trace_conjTranspose_mul_self (nearSel W * twoPortScattering b E XX * farEmbed A)
  have e : (nearSel W * twoPortScattering b E XX * farEmbed A)ᴴ *
      (nearSel W * twoPortScattering b E XX * farEmbed A) = farEmbed A *
        ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX) *
          farEmbed A := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, farEmbed_conjTranspose_of hA,
      ← FullSourceCovariance.nearSel_conj_mul_nearSel]
    simp only [Matrix.mul_assoc]
  rw [e] at h
  rw [h, Complex.ofReal_re]

/-- `‖ι𝕊F‖₂ = 2η‖ιℝF‖₂`. -/
theorem hsNorm_nearScat_eq {b E : ℝ} (hη : 0 < etaZ b E)
    (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) (A : Matrix (Fin W) (Fin W) ℂ) :
    hsNorm (nearSel W * twoPortScattering b E XX * farEmbed A) =
      (2 * etaZ b E) * hsNorm (leakInput b E XX (farEmbed A)) := by
  have e : nearSel W * twoPortScattering b E XX * farEmbed A =
      (-(((2 * etaZ b E : ℝ) : ℂ) * Complex.I)) • leakInput b E XX (farEmbed A) := by
    rw [twoPortScattering, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, nearSel_mul_farEmbed,
      zero_sub, leakInput, Matrix.mul_smul, Matrix.smul_mul, neg_smul]
  rw [e, hsNorm_smul, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]

/-- **The one-layer mean bound of the omitted flux**: `E_f g₊ ≤ (1 + ‖EΔ‖/η) g`. -/
theorem flux_fresh_mean {b E : ℝ} (hη : 0 < etaZ b E)
    {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hXX : XX.IsHermitian)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A)
    (hΔ : ∀ x y, Integrable (fun f => freshDelta b E (nearSchur (boundaryZ b E) XX) f x y)
      (freshLaw W b)) :
    ∫ f, (farEmbed A * ((freshTransport b E XX f)ᴴ *
        ((twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX -
          nearProjection W) * freshTransport b E XX f + nearProjection W) * farEmbed A).trace.re
        ∂freshLaw W b ≤
      (1 + ‖matrixExpect (freshLaw W b) (freshDelta b E (nearSchur (boundaryZ b E) XX))‖ /
        etaZ b E) * (farEmbed A * ((twoPortScattering b E XX)ᴴ * nearProjection W *
          twoPortScattering b E XX) * farEmbed A).trace.re := by
  set S := twoPortScattering b E XX
  set P := nearProjection W
  set M := Sᴴ * P * S
  set F := farEmbed A
  set V := leakInput b E XX F
  set Δ := freshDelta b E (nearSchur (boundaryZ b E) XX)
  set g := (F * M * F).trace.re
  set Y := nearSel W * M * F
  have hS := twoPortScattering_unitary b E XX hXX (by simpa [etaZ] using hη)
  have hF : Fᴴ = F := farEmbed_conjTranspose_of hA
  have hPF : P * F = 0 := nearProjection_mul_farEmbed A
  have hPH : Pᴴ = P := nearProjection_conjTranspose
  have hFP : F * P = 0 := by
    have := congrArg Matrix.conjTranspose hPF
    rwa [Matrix.conjTranspose_mul, hF, hPH, Matrix.conjTranspose_zero] at this
  have hM : Mᴴ = M := by
    simp only [M, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPH,
      Matrix.mul_assoc]
  have hM1 : (1 - M).PosSemidef := by
    have h1 : 1 - M = Sᴴ * (1 - P) * S := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hS.1]
    rw [h1]; exact one_sub_nearProjection_psd.conjTranspose_mul_mul_same S
  -- the pointwise step
  have hpt : ∀ f, (F * ((freshTransport b E XX f)ᴴ * (M - P) * freshTransport b E XX f + P) *
      F).trace.re ≤ g + 2 * (Vᴴ * (Δ f)ᴴ * Y).trace.re := by
    intro f
    have hNF := freshTransport_mul_farEmbed b E XX f A
    have hPZ : P * ((nearSel W)ᴴ * (Δ f * V)) = (nearSel W)ᴴ * (Δ f * V) := by
      rw [← Matrix.mul_assoc, nearProjection_mul_nearSel_conj]
    have h := flux_step_le hNF hF hPF hPZ nearProjection_conjTranspose nearProjection_mul_self
      (by rw [hFP, Matrix.zero_mul]) hM hM1
    have e : ((nearSel W)ᴴ * (Δ f * V))ᴴ * M * F = Vᴴ * (Δ f)ᴴ * Y := by
      simp only [Y, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [e] at h
    exact h
  obtain ⟨hlinI, hlin⟩ := integral_trace_lin (μ := freshLaw W b) Δ hΔ V Y
  -- the norms
  set D := matrixExpect (freshLaw W b) Δ
  have hgsq : hsNorm (nearSel W * S * F) ^ 2 = g := hsNorm_sq_nearOut XX hA
  have hg0 : 0 ≤ g := by rw [← hgsq]; positivity
  have hP2 : P * P = P := nearProjection_mul_self
  have hMM : M * M = M := by
    show Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * S
    calc Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * (S * Sᴴ) * P * S := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * P * S := by rw [hS.2, Matrix.mul_one, Matrix.mul_assoc Sᴴ P P, hP2]
  have hMF : hsNorm (M * F) ^ 2 = g := by
    have h := trace_conjTranspose_mul_self (M * F)
    have e : (M * F)ᴴ * (M * F) = F * M * F := by
      rw [Matrix.conjTranspose_mul, hF, hM]
      calc F * M * (M * F) = F * (M * M) * F := by simp only [Matrix.mul_assoc]
        _ = F * M * F := by rw [hMM]
    rw [e] at h
    rw [show g = (F * M * F).trace.re from rfl, h, Complex.ofReal_re]
  have hY : hsNorm Y ≤ Real.sqrt g := by
    have h1 := hsNorm_mul_le_opNorm (nearSel W) (M * F)
    have hn : ‖nearSel W‖ ≤ 1 := norm_nearSel_le
    have e : Y = nearSel W * (M * F) := Matrix.mul_assoc _ _ _
    have h2 : hsNorm (M * F) = Real.sqrt g := by rw [← hMF, Real.sqrt_sq (hsNorm_nonneg _)]
    rw [e, ← h2]
    nlinarith [hsNorm_nonneg (M * F)]
  have hV : hsNorm V = Real.sqrt g / (2 * etaZ b E) := by
    have h1 : hsNorm (nearSel W * S * F) = (2 * etaZ b E) * hsNorm V := hsNorm_nearScat_eq hη XX A
    have hsg : Real.sqrt g = hsNorm (nearSel W * S * F) := by
      rw [← hgsq, Real.sqrt_sq (hsNorm_nonneg _)]
    rw [hsg, h1]
    field_simp
  have hsq : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt hg0
  have hlin_le : 2 * (Vᴴ * Dᴴ * Y).trace.re ≤ ‖D‖ / etaZ b E * g := by
    have h1 := (abs_le.mp (abs_trace_lin_le D V Y)).2
    have h2 : ‖D‖ * hsNorm V * hsNorm Y ≤ ‖D‖ * (Real.sqrt g / (2 * etaZ b E)) * Real.sqrt g := by
      rw [hV]; exact mul_le_mul_of_nonneg_left hY (by positivity)
    have h3 : ‖D‖ * (Real.sqrt g / (2 * etaZ b E)) * Real.sqrt g = ‖D‖ / etaZ b E * g / 2 := by
      conv_rhs => rw [← hsq]
      field_simp
    linarith
  by_cases hI : Integrable (fun f => (F * ((freshTransport b E XX f)ᴴ * (M - P) *
      freshTransport b E XX f + P) * F).trace.re) (freshLaw W b)
  · calc _ ≤ ∫ f, (g + 2 * (Vᴴ * (Δ f)ᴴ * Y).trace.re) ∂freshLaw W b :=
          integral_mono hI ((integrable_const g).add (hlinI.const_mul 2)) hpt
      _ = g + 2 * ∫ f, (Vᴴ * (Δ f)ᴴ * Y).trace.re ∂freshLaw W b := by
          rw [integral_add (integrable_const g) (hlinI.const_mul 2), integral_const_mul]
          simp
      _ = g + 2 * (Vᴴ * Dᴴ * Y).trace.re := by rw [hlin]
      _ ≤ (1 + ‖D‖ / etaZ b E) * g := by nlinarith
  · rw [integral_undef hI]
    exact mul_nonneg (by positivity) hg0

end BlockBand.SourceProcess.SmallLeak
