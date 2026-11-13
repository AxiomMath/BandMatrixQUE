module

public import BlockBand.SourceProcess.SmallLeak.LeakMean

/-!
# The transported omitted flux: definitions and the crude bound

At a Hermitian old two-port `𝕏` (scattering `𝕊`, `M = 𝕊*P𝕊`) and `F = farEmbed A`:
`fluxAt = Re Tr FMF` and `fluxNext f = Re Tr F(N*(M-P)N + P)F` (the next flux, by `J₊ = N*JN`).
Crude bound (`fluxNext_le`): `fluxNext ≤ (1 + ‖Δ‖/(2η))² fluxAt`.
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
open scoped Matrix ComplexOrder

section Frob
open scoped Matrix.Norms.Frobenius

theorem hsNorm_add_le' {m n : Type*} [Fintype m] [Fintype n] (A B : Matrix m n ℂ) :
    hsNorm (A + B) ≤ hsNorm A + hsNorm B := by
  rw [← frobenius_eq_hsNorm, ← frobenius_eq_hsNorm, ← frobenius_eq_hsNorm]
  exact norm_add_le A B

end Frob

open scoped Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `M = 𝕊*P𝕊` at a two-port. -/
def scatOut (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) :
    Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (twoPortScattering b E XX)ᴴ * nearProjection W * twoPortScattering b E XX

/-- The flux `Re Tr FMF`. -/
def fluxAt (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : Matrix (Fin W) (Fin W) ℂ) : ℝ :=
  (farEmbed A * scatOut b E XX * farEmbed A).trace.re

/-- The transported flux `Re Tr F(N*(M-P)N + P)F`. -/
def fluxNext (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : Matrix (Fin W) (Fin W) ℂ) (f : LayerSample W .oneBlockOnePort) : ℝ :=
  (farEmbed A * ((freshTransport b E XX f)ᴴ * (scatOut b E XX - nearProjection W) *
    freshTransport b E XX f + nearProjection W) * farEmbed A).trace.re

theorem fluxAt_nonneg (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A) : 0 ≤ fluxAt b E XX A := by
  have : hsNorm (nearSel W * twoPortScattering b E XX * farEmbed A) ^ 2 = fluxAt b E XX A :=
    hsNorm_sq_nearOut XX hA
  rw [← this]; positivity

theorem measurable_fluxNext (b E : ℝ) (XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ)
    (A : Matrix (Fin W) (Fin W) ℂ) : Measurable (fluxNext b E XX A) := by
  have hN := FullSource.measurable_freshTransport_comp (W := W) b E (XX := fun _ => XX)
    measurable_const measurable_id
  exact measurable_trace_re (measurable_matrix_mul' (measurable_matrix_mul' measurable_const
    ((measurable_matrix_mul' (measurable_matrix_mul' (measurable_matrix_conjTranspose' hN)
      measurable_const) hN).add measurable_const)) measurable_const)

theorem norm_le_one_of_proj {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : Mᴴ = M) (hM2 : M * M = M) : ‖M‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self M
  rw [hM, hM2] at h
  rcases (norm_nonneg M).eq_or_lt with h0 | h0
  · rw [← h0]; exact zero_le_one
  · nlinarith

/-- **The crude bound** `fluxNext ≤ (1 + ‖Δ‖/(2η))² fluxAt`. -/
theorem fluxNext_le {b E : ℝ} (hη : 0 < etaZ b E) {XX : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ}
    (hXX : XX.IsHermitian) {A : Matrix (Fin W) (Fin W) ℂ} (hA : Aᴴ = A)
    (f : LayerSample W .oneBlockOnePort) :
    fluxNext b E XX A f ≤
      (1 + ‖freshDelta b E (nearSchur (boundaryZ b E) XX) f‖ / (2 * etaZ b E)) ^ 2 *
        fluxAt b E XX A := by
  set S := twoPortScattering b E XX
  set P := nearProjection W
  set M := scatOut b E XX
  set F := farEmbed A
  set V := leakInput b E XX F
  set Δ := freshDelta b E (nearSchur (boundaryZ b E) XX) f
  set N := freshTransport b E XX f
  set Z := (nearSel W)ᴴ * (Δ * V)
  set g := fluxAt b E XX A
  have hS := twoPortScattering_unitary b E XX hXX (by simpa [etaZ] using hη)
  have hF : Fᴴ = F := farEmbed_conjTranspose_of hA
  have hPH : Pᴴ = P := nearProjection_conjTranspose
  have hP2 : P * P = P := nearProjection_mul_self
  have hPF : P * F = 0 := nearProjection_mul_farEmbed A
  have hFP : F * P = 0 := by
    have := congrArg Matrix.conjTranspose hPF
    rwa [Matrix.conjTranspose_mul, hF, hPH, Matrix.conjTranspose_zero] at this
  have hNF : N * F = F + Z := freshTransport_mul_farEmbed b E XX f A
  have hPZ : P * Z = Z := by rw [← Matrix.mul_assoc, nearProjection_mul_nearSel_conj]
  have hM : Mᴴ = M := by
    show (Sᴴ * P * S)ᴴ = Sᴴ * P * S
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hPH,
      Matrix.mul_assoc]
  have hMM : M * M = M := by
    show Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * S
    calc Sᴴ * P * S * (Sᴴ * P * S) = Sᴴ * P * (S * Sᴴ) * P * S := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * P * S := by rw [hS.2, Matrix.mul_one, Matrix.mul_assoc Sᴴ P P, hP2]
  -- the exact form
  have hFN : F * Nᴴ = (F + Z)ᴴ := by rw [← hNF, Matrix.conjTranspose_mul, hF]
  have e1 : F * (Nᴴ * (M - P) * N + P) * F =
      (M * (F + Z))ᴴ * (M * (F + Z)) - Zᴴ * Z := by
    have h1 : F * (Nᴴ * (M - P) * N + P) * F = (F + Z)ᴴ * M * (F + Z) -
        (F + Z)ᴴ * P * (F + Z) + F * P * F := by
      rw [← hFN, ← hNF]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_assoc]
    have h2 : (F + Z)ᴴ * P * (F + Z) = Zᴴ * Z := by
      have hPFZ : P * (F + Z) = Z := by rw [Matrix.mul_add, hPF, hPZ, zero_add]
      have : (F + Z)ᴴ * P * (F + Z) = (P * (F + Z))ᴴ * (P * (F + Z)) := by
        rw [Matrix.conjTranspose_mul, hPH]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc P P (F + Z), hP2]
      rw [this, hPFZ]
    have h3 : (F + Z)ᴴ * M * (F + Z) = (M * (F + Z))ᴴ * (M * (F + Z)) := by
      rw [Matrix.conjTranspose_mul, hM]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc M M (F + Z), hMM]
    rw [h1, h2, h3, hFP, Matrix.zero_mul, add_zero]
  have hle : fluxNext b E XX A f ≤ hsNorm (M * (F + Z)) ^ 2 := by
    show (F * (Nᴴ * (M - P) * N + P) * F).trace.re ≤ _
    rw [e1, Matrix.trace_sub, Complex.sub_re, trace_conjTranspose_mul_self,
      trace_conjTranspose_mul_self, Complex.ofReal_re, Complex.ofReal_re]
    have := hsNorm_nonneg Z
    nlinarith
  -- the norms
  have hg0 : 0 ≤ g := fluxAt_nonneg b E XX hA
  have hMF : hsNorm (M * F) = Real.sqrt g := by
    have h := trace_conjTranspose_mul_self (M * F)
    have e : (M * F)ᴴ * (M * F) = F * M * F := by
      rw [Matrix.conjTranspose_mul, hF, hM]
      calc F * M * (M * F) = F * (M * M) * F := by simp only [Matrix.mul_assoc]
        _ = F * M * F := by rw [hMM]
    rw [e] at h
    have h' : hsNorm (M * F) ^ 2 = g := by
      rw [show g = (F * M * F).trace.re from rfl, h, Complex.ofReal_re]
    rw [← h', Real.sqrt_sq (hsNorm_nonneg _)]
  have hV : hsNorm V = Real.sqrt g / (2 * etaZ b E) := hsNorm_leakInput hη XX hA
  have hZ : hsNorm Z ≤ ‖Δ‖ * (Real.sqrt g / (2 * etaZ b E)) := by
    have h1 := hsNorm_mul_le_opNorm (nearSel W)ᴴ (Δ * V)
    have h2 := hsNorm_mul_le_opNorm Δ V
    have hn : ‖(nearSel W)ᴴ‖ ≤ 1 := norm_nearSel_conj_le
    rw [hV] at h2
    nlinarith [hsNorm_nonneg (Δ * V)]
  have hMZ : hsNorm (M * Z) ≤ hsNorm Z := by
    have := hsNorm_mul_le_opNorm M Z
    have hn := norm_le_one_of_proj hM hMM
    nlinarith [hsNorm_nonneg Z]
  have hsum : hsNorm (M * (F + Z)) ≤ (1 + ‖Δ‖ / (2 * etaZ b E)) * Real.sqrt g := by
    rw [Matrix.mul_add]
    refine (hsNorm_add_le' (M * F) (M * Z)).trans ?_
    rw [hMF]
    have : ‖Δ‖ * (Real.sqrt g / (2 * etaZ b E)) = ‖Δ‖ / (2 * etaZ b E) * Real.sqrt g := by ring
    linarith
  refine hle.trans ?_
  have h0 := hsNorm_nonneg (M * (F + Z))
  calc hsNorm (M * (F + Z)) ^ 2 ≤ ((1 + ‖Δ‖ / (2 * etaZ b E)) * Real.sqrt g) ^ 2 :=
        pow_le_pow_left₀ h0 hsum 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hg0]

end BlockBand.SourceProcess.SmallLeak
