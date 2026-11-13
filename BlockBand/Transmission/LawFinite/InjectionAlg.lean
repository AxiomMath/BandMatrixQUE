module

public import BlockBand.Transmission.LawFinite.InjectionNorms
public import BlockBand.Transmission.SourceMixing.MassMeanAlg
public import BlockBand.Transmission.PassiveCovariance.Step3
public import BlockBand.Transmission.PassiveCovariance.WordReduction

/-!
# Injection mean: deterministic algebra

* `injection_eq_conj`: `C = L'*R'*R'L'` pointwise (`L' = K'𝒢₁₂`, `R'K' = 1`), so
  `Tr C = Tr(R'*R'·L'L'*)`;
* `inj_trace_bound`: for `N ⪰ 0`, `EU = s KM KM* + Δ`:
  `|⟨N EU⟩ - ⟨N⟩| ≤ (‖Δ‖ + |Re s - 1|‖KM KM*‖ + ‖KM KM* - 1‖)⟨N⟩`, `⟨·⟩ = W⁻¹ Re Tr`;
* `inj_re_s`: `|Re s - 1| ≤ 2(ε' + (3/2)b|Im ω| + (9/4)q/W)/(bη)` from the scalar identity
  `Re s·(bhη + k u/W) ≈ bh(η - Im ω)` of `Generator.rf_sre`;
* `normTrace_adjR_sub_dStar_le`: `|⟨R*R⟩ - d_*| ≤ (δ₀ + q/W)/η`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.LawFinite

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission.PassiveLayer
open scoped ENNReal ComplexOrder Matrix.Norms.L2Operator

variable {W : ℕ}

/-- `C = L'*(R'*R')L'` at the absorbed input, for every sample. -/
theorem injection_eq_conj {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε)
    (ω : LayerSample W .oneBlockOnePort) :
    injection b E X ε ω = (freshL b E (absorbedInput X ε) ω)ᴴ *
      ((passiveResolvent b E (absorbedInput X ε))ᴴ * passiveResolvent b E (absorbedInput X ε)) *
        freshL b E (absorbedInput X ε) ω := by
  have hR := (PassiveCovariance.nearPencil_inverse hb0 hb h1 h2
    (passiveY_absorbedInput hY hε)).2
  rw [freshL_absorbedInput, injection]
  generalize freshG12 b E (absorbedInput X ε) ω = G
  generalize passiveResolvent b E (absorbedInput X ε) = R at hR ⊢
  generalize boundaryZ b E • (1 : Matrix (Fin W) (Fin W) ℂ) - absorbedInput X ε = K at hR ⊢
  have e : (K * G)ᴴ * (Rᴴ * R) * (K * G) = (R * K * G)ᴴ * (R * K * G) := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hR, Matrix.one_mul]

/-- `Re Tr C = Re Tr(R'*R'·L'L'*)`. -/
theorem trace_injection_eq {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
    {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef) {ε : ℝ} (hε : 0 ≤ ε)
    (ω : LayerSample W .oneBlockOnePort) :
    (injection b E X ε ω).trace =
      ((passiveResolvent b E (absorbedInput X ε))ᴴ * passiveResolvent b E (absorbedInput X ε) *
        freshU b E (absorbedInput X ε) ω).trace := by
  rw [injection_eq_conj hb0 hb h1 h2 hY hε, freshU]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **Trace pairing against a near-scalar mean.** -/
theorem inj_trace_bound {N U KM : Matrix (Fin W) (Fin W) ℂ} (s : ℂ) (hN : N.PosSemidef) :
    |(W : ℝ)⁻¹ * (N * U).trace.re - (W : ℝ)⁻¹ * N.trace.re| ≤
      (‖U - s • (KM * KMᴴ)‖ + |s.re - 1| * ‖KM * KMᴴ‖ + ‖KM * KMᴴ - 1‖) *
        ((W : ℝ)⁻¹ * N.trace.re) := by
  set P := KM * KMᴴ
  set Δ := U - s • P
  set t := N.trace.re
  have ht0 : 0 ≤ t := (SourceMixing.mm_trace_posSemidef hN).1
  have hTp : (KMᴴ * N * KM).PosSemidef := hN.conjTranspose_mul_mul_same KM
  have hTeq : (N * P).trace = (KMᴴ * N * KM).trace := by
    simp only [P]; rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  set T := (N * P).trace
  have hTr : T = (T.re : ℂ) := by rw [hTeq]; exact (SourceMixing.mm_trace_posSemidef hTp).2
  have hU : U = Δ + s • P := by simp only [Δ]; abel
  have hsplit : (N * U).trace.re = (N * Δ).trace.re + s.re * T.re := by
    rw [hU, Matrix.mul_add, trace_add, Matrix.mul_smul, trace_smul, Complex.add_re, smul_eq_mul,
      show (N * P).trace = ((N * P).trace.re : ℂ) from hTr, Complex.re_mul_ofReal]
  have hΔ : |(N * Δ).trace.re| ≤ ‖Δ‖ * t := by
    rw [trace_mul_comm]
    exact (Complex.abs_re_le_norm _).trans (PassiveCovariance.norm_trace_mul_posSemidef_le hN Δ)
  have hTP : |T.re - t| ≤ ‖P - 1‖ * t := by
    have e : T.re - t = ((P - 1) * N).trace.re := by
      simp only [T, t]
      rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re, trace_mul_comm]
    rw [e]
    exact (Complex.abs_re_le_norm _).trans
      (PassiveCovariance.norm_trace_mul_posSemidef_le hN (P - 1))
  have hT0 : |T.re| ≤ ‖P‖ * t := by
    have := PassiveCovariance.norm_trace_mul_posSemidef_le hN P
    rw [trace_mul_comm] at this
    exact (Complex.abs_re_le_norm _).trans this
  have hW0 : (0 : ℝ) ≤ (W : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have e : (W : ℝ)⁻¹ * (N * U).trace.re - (W : ℝ)⁻¹ * t =
      (W : ℝ)⁻¹ * ((N * Δ).trace.re + (s.re - 1) * T.re + (T.re - t)) := by
    rw [hsplit]; ring
  rw [e, abs_mul, abs_of_nonneg hW0]
  have hb : |(N * Δ).trace.re + (s.re - 1) * T.re + (T.re - t)| ≤
      (‖Δ‖ + |s.re - 1| * ‖P‖ + ‖P - 1‖) * t := by
    have h3 := abs_add_le ((N * Δ).trace.re + (s.re - 1) * T.re) (T.re - t)
    have h4 := abs_add_le ((N * Δ).trace.re) ((s.re - 1) * T.re)
    have h5 : |(s.re - 1) * T.re| ≤ |s.re - 1| * (‖P‖ * t) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hT0 (abs_nonneg _)
    nlinarith
  calc (W : ℝ)⁻¹ * |(N * Δ).trace.re + (s.re - 1) * T.re + (T.re - t)| ≤
        (W : ℝ)⁻¹ * ((‖Δ‖ + |s.re - 1| * ‖P‖ + ‖P - 1‖) * t) :=
        mul_le_mul_of_nonneg_left hb hW0
    _ = _ := by ring

/-- **`Re s ≈ 1`** from the scalar identity of `rf_sre`. -/
theorem inj_re_s {sre D b h η ωi u q W k ε' m : ℝ} (hb0 : 0 < b) (hη : 0 < η)
    (hD : D = b * h * η + k * (u / W)) (hDlo : b * (1 / 2) * η ≤ D) (hh : h ≤ 3 / 2)
    (hk0 : 0 ≤ k) (hk : k ≤ 1) (hu0 : 0 ≤ u) (huq : u ≤ 9 / 4 * q) (hW : 0 < W)
    (hs : |sre * D - b * h * (η - ωi)| ≤ ε') (hωi : |ωi| ≤ m) (hh0 : 0 ≤ h) :
    |sre - 1| ≤ 2 * (ε' + 3 / 2 * b * m + 9 / 4 * (q / W)) / (b * η) := by
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDlo
  have e : (sre - 1) * D = (sre * D - b * h * (η - ωi)) - b * h * ωi - k * (u / W) := by
    rw [hD]; ring
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hωi
  have hb1 : |b * h * ωi| ≤ 3 / 2 * b * m := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul (by nlinarith) hωi (abs_nonneg _) (by positivity)
  have huW : u / W ≤ 9 / 4 * (q / W) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right huq hW.le
  have hk1 : |k * (u / W)| ≤ 9 / 4 * (q / W) := by
    rw [abs_of_nonneg (by positivity)]
    calc k * (u / W) ≤ 1 * (u / W) := mul_le_mul_of_nonneg_right hk (by positivity)
      _ ≤ _ := by linarith
  have hnum : |(sre - 1) * D| ≤ ε' + 3 / 2 * b * m + 9 / 4 * (q / W) := by
    rw [e]
    have := abs_sub (sre * D - b * h * (η - ωi) - b * h * ωi) (k * (u / W))
    have := abs_sub (sre * D - b * h * (η - ωi)) (b * h * ωi)
    linarith
  rw [abs_mul, abs_of_pos hD0] at hnum
  rw [le_div_iff₀ (by positivity)]
  have h2 : |sre - 1| * (b * (1 / 2) * η) ≤ |sre - 1| * D :=
    mul_le_mul_of_nonneg_left hDlo (abs_nonneg _)
  nlinarith

section Passive

variable {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2)
  {X : Matrix (Fin W) (Fin W) ℂ} (hY : (passiveY X).PosSemidef)
include hb0 hb h1 h2 hY

/-- `|⟨R*R⟩ - d_*| ≤ (δ₀ + q/W)/η`. -/
theorem normTrace_adjR_sub_dStar_le (hW : W ≠ 0) :
    |(W : ℝ)⁻¹ * ((passiveResolvent b E X)ᴴ * passiveResolvent b E X).trace.re - dStar b| ≤
      (jetDistance0 b E X + passiveMass b E X / W) / etaZ b E := by
  have h := PassiveCovariance.normTrace_RRstar_sub_dStar_le hb0 hb h1 h2 hY hW
  rw [trace_mul_comm] at h
  refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans h)
  congr 1
  simp only [Complex.sub_re, Complex.ofReal_re]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

end Passive

end BlockBand.Transmission.LawFinite
