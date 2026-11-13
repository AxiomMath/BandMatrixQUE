module

public import BlockBand.SourceProcess.RankFree.NoiseAlgebra

/-!
# The rank-free drift of the coupled distance

For two constrained frames `V₁, V₂` (same near projection `P`, same signature `𝖣`) driven by
the same noise, with `X = ‖V₁ - V₂‖²`, `R = ‖V₁‖² + ‖V₂‖²` and `K_J = P₁' - P₂'`, the Itô drift of
`X` is `(D₀/2) ‖K_J‖² Re Tr(V₁ᴴ P V₂)` (every factor `Naux` cancels, `Tr(P₁'P₂') = Naux - ‖K_J‖²/2`),
and `‖K_J‖² ≤ 2RX`, `Re Tr(V₁ᴴPV₂) ≤ R/2` give the upper drift `D₀R²X/2`
(`distance_generator_le`). No dimension or rank enters.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.RankFree
open Matrix BlockBand.SourceProcess BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.SourceAlgebra BlockBand.SourceProcess.Stochastic.SourceSDE

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {ι c : Type*} [Fintype ι] [DecidableEq ι] [Fintype c]

omit [DecidableEq ι] in
/-- A signature does not increase the Frobenius norm: `‖A𝖣‖ ≤ ‖A‖`. -/
theorem norm_mul_signature_le {D : Matrix c c ℂ} (hD : IsSignature D) (A : Matrix ι c ℂ) :
    ‖A * D‖ ≤ ‖A‖ := by
  have hDH : Dᴴ = D := hD.1
  have hD4 : D * (D * (D * D)) = D * D := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD.2]
  have t1 : ((A * D)ᴴ * (A * D)).trace = (Aᴴ * (A * (D * D))).trace := by
    rw [conjTranspose_mul, hDH]
    have := trace_mul_comm D (Aᴴ * A * D)
    simp only [Matrix.mul_assoc] at this ⊢
    exact this
  have t2 : ((A * (D * D))ᴴ * (A * (D * D))).trace = (Aᴴ * (A * (D * D))).trace := by
    rw [conjTranspose_mul, conjTranspose_mul, hDH]
    have := trace_mul_comm (D * D) (Aᴴ * A * (D * D))
    simp only [Matrix.mul_assoc] at this ⊢
    rw [this, hD4]
  have e1 : ‖A * D‖ ^ 2 = reInner A (A * (D * D)) := by
    rw [← reInner_self, reInner_apply, reInner_apply, t1]
  have e2 : ‖A * (D * D)‖ ^ 2 = reInner A (A * (D * D)) := by
    rw [← reInner_self, reInner_apply, reInner_apply, t2]
  have h := two_re_trace_le A (A * (D * D))
  rw [← reInner_apply, e2.symm] at h
  have h2 : ‖A * D‖ ^ 2 ≤ ‖A‖ ^ 2 := by nlinarith [e1, e2]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

omit [DecidableEq ι] in
/-- `‖PV‖ ≤ ‖V‖` for a near projection. -/
theorem norm_near_sq_le {Naux : ℕ} {P : Matrix ι ι ℂ} (hP : IsNearProjection P Naux)
    (V : Matrix ι c ℂ) : ‖P * V‖ ^ 2 ≤ ‖V‖ ^ 2 := by
  have e : ‖P * V‖ ^ 2 = reInner V (P * V) := by
    rw [← reInner_self, reInner_apply, reInner_apply, conjTranspose_mul, hP.1, Matrix.mul_assoc,
      ← Matrix.mul_assoc P, hP.2.1]
  have h := two_re_trace_le V (P * V)
  rw [← reInner_apply, ← e] at h
  linarith

omit [DecidableEq ι] in
theorem reInner_sub_self (x y : Matrix ι c ℂ) :
    reInner (x - y) (x - y) = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * reInner x y := by
  simp only [map_sub, _root_.sub_apply, reInner_self, reInner_comm y x]
  ring

omit [DecidableEq ι] in
/-- `Tr(P₁ᴴP₂)` is real for Hermitian `P₁, P₂`. -/
theorem trace_herm_mul_im {P₁ P₂ : Matrix ι ι ℂ} (h₁ : P₁ᴴ = P₁) (h₂ : P₂ᴴ = P₂) :
    (P₁ᴴ * P₂).trace.im = 0 := by
  have h : star (P₁ᴴ * P₂).trace = (P₁ᴴ * P₂).trace := by
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, h₁, h₂,
      trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

/-- **Rank-free upper drift of the coupled distance.** -/
theorem distance_generator_le {D0 : ℝ} (hD0 : 0 ≤ D0) {Naux : ℕ} {P : Matrix ι ι ℂ}
    {D : Matrix c c ℂ} (hP : IsNearProjection P Naux) (hD : IsSignature D)
    {V₁ V₂ : Matrix ι c ℂ} (h₁ : TwoProjection P D V₁) (h₂ : TwoProjection P D V₂) :
    sdeGenerator (fun _ => sourceDrift D0 Naux P V₁ - sourceDrift D0 Naux P V₂)
        (fun a _ => sourceDiffusion D0 P D a V₁ - sourceDiffusion D0 P D a V₂)
        (fun W : Matrix ι c ℂ => ‖W‖ ^ 2) (V₁ - V₂) ≤
      D0 / 2 * (‖V₁‖ ^ 2 + ‖V₂‖ ^ 2) ^ 2 * ‖V₁ - V₂‖ ^ 2 := by
  set Δ := V₁ - V₂ with hΔ
  set P₁ := gramProjection P V₁ D
  set P₂ := gramProjection P V₂ D
  set T := (P₁ᴴ * P₂).trace
  set z := ((P * V₁)ᴴ * (P * V₂)).trace
  set R := ‖V₁‖ ^ 2 + ‖V₂‖ ^ 2
  have hb : sourceDrift D0 Naux P V₁ - sourceDrift D0 Naux P V₂ = sourceDrift D0 Naux P Δ := by
    simp only [sourceDrift, hΔ, Matrix.mul_sub, smul_sub]
  have hs1 : ∑ a, ‖sourceDiffusion D0 P D a V₁‖ ^ 2 = D0 / 2 * Naux * ‖P * V₁‖ ^ 2 := by
    simp_rw [← reInner_self, sourceDiffusion_eq']
    rw [sum_reInner_noise hD0, ← frob_sq_eq_trace, ← frob_sq_eq_trace, frob_sq_gramProjection hP h₁,
      ← Complex.ofReal_mul, Complex.ofReal_re, reInner_self]
    ring
  have hs2 : ∑ a, ‖sourceDiffusion D0 P D a V₂‖ ^ 2 = D0 / 2 * Naux * ‖P * V₂‖ ^ 2 := by
    simp_rw [← reInner_self, sourceDiffusion_eq']
    rw [sum_reInner_noise hD0, ← frob_sq_eq_trace, ← frob_sq_eq_trace, frob_sq_gramProjection hP h₂,
      ← Complex.ofReal_mul, Complex.ofReal_re, reInner_self]
    ring
  have hs12 : ∑ a, reInner (sourceDiffusion D0 P D a V₁) (sourceDiffusion D0 P D a V₂) =
      D0 / 2 * (T * z).re := by
    simp_rw [sourceDiffusion_eq']
    exact sum_reInner_noise hD0 _ _ _ _
  have hPΔ : ‖P * Δ‖ ^ 2 = ‖P * V₁‖ ^ 2 + ‖P * V₂‖ ^ 2 - 2 * z.re := by
    rw [← reInner_self, hΔ, Matrix.mul_sub, reInner_sub_self, reInner_apply]
  have hTim : T.im = 0 := trace_herm_mul_im h₁.1 h₂.1
  have hTz : (T * z).re = T.re * z.re := by rw [Complex.mul_re, hTim, zero_mul, sub_zero]
  have hK : ‖P₁ - P₂‖ ^ 2 = 2 * Naux - 2 * T.re := by
    rw [← reInner_self, reInner_sub_self, frob_sq_gramProjection hP h₁,
      frob_sq_gramProjection hP h₂, reInner_apply]
    ring
  have hKe : P₁ - P₂ = Δ * D * V₁ᴴ + V₂ * D * Δᴴ := by
    simp only [P₁, P₂, gramProjection, hΔ, conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hKb : ‖P₁ - P₂‖ ≤ ‖Δ‖ * ‖V₁‖ + ‖V₂‖ * ‖Δ‖ := by
    rw [hKe]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (frobenius_norm_mul _ _).trans ?_
      rw [frobenius_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (norm_mul_signature_le hD Δ) (norm_nonneg _)
    · refine (frobenius_norm_mul _ _).trans ?_
      rw [frobenius_norm_conjTranspose]
      exact mul_le_mul_of_nonneg_right (norm_mul_signature_le hD V₂) (norm_nonneg _)
  have hK2 : ‖P₁ - P₂‖ ^ 2 ≤ 2 * R * ‖Δ‖ ^ 2 := by
    have h0 : 0 ≤ ‖P₁ - P₂‖ := norm_nonneg _
    have h1 : ‖P₁ - P₂‖ ^ 2 ≤ (‖Δ‖ * ‖V₁‖ + ‖V₂‖ * ‖Δ‖) ^ 2 := pow_le_pow_left₀ h0 hKb 2
    nlinarith [sq_nonneg (‖V₁‖ - ‖V₂‖), sq_nonneg ‖Δ‖]
  have hz : 2 * z.re ≤ R := by
    have := two_re_trace_le (P * V₁) (P * V₂)
    linarith [norm_near_sq_le hP V₁, norm_near_sq_le hP V₂]
  rw [sdeGenerator_normSq]
  rw [hb, reInner_comm Δ, reInner_sourceDrift hP.1 hP.2.1]
  have hsum : ∑ a, reInner (sourceDiffusion D0 P D a V₁ - sourceDiffusion D0 P D a V₂)
      (sourceDiffusion D0 P D a V₁ - sourceDiffusion D0 P D a V₂) =
      D0 / 2 * Naux * ‖P * V₁‖ ^ 2 + D0 / 2 * Naux * ‖P * V₂‖ ^ 2 - 2 * (D0 / 2 * (T * z).re) := by
    simp only [reInner_sub_self, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      hs1, hs2, hs12]
  rw [hsum, hTz, hPΔ]
  have key : -(D0 * Naux / 4) * (‖P * V₁‖ ^ 2 + ‖P * V₂‖ ^ 2 - 2 * z.re) +
      -(D0 * Naux / 4) * (‖P * V₁‖ ^ 2 + ‖P * V₂‖ ^ 2 - 2 * z.re) +
      (D0 / 2 * Naux * ‖P * V₁‖ ^ 2 + D0 / 2 * Naux * ‖P * V₂‖ ^ 2 - 2 * (D0 / 2 * (T.re * z.re)))
      = D0 / 2 * ‖P₁ - P₂‖ ^ 2 * z.re := by
    rw [hK]; ring
  rw [key]
  have hk0 : 0 ≤ ‖P₁ - P₂‖ ^ 2 := sq_nonneg _
  have hR0 : 0 ≤ R := by positivity
  calc D0 / 2 * ‖P₁ - P₂‖ ^ 2 * z.re ≤ D0 / 2 * ‖P₁ - P₂‖ ^ 2 * (R / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ D0 / 2 * (2 * R * ‖Δ‖ ^ 2) * (R / 2) := by gcongr
    _ = D0 / 2 * R ^ 2 * ‖Δ‖ ^ 2 := by ring

end BlockBand.SourceProcess.RankFree
