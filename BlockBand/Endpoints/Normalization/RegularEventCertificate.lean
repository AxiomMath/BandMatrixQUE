module

public import BlockBand.Internal.Contracts.CoareaPalm
public import BlockBand.Internal.Contracts.Layers
public import BlockBand.Palm.RegularityCertificate

/-!
# Regular prior event: the deterministic regularity certificate

The regularity certificate gives the fresh regularity on a fixed rectangle and `|m - μ| ≤ C|χ|`;
we restate it in the vocabulary of `FreshRegular` and `freshDyson`. The statements are
deterministic:
* `regularEvent_dyson_iff`, `regularEvent_freshDyson_eq`: the scalar root
  `CoareaPalm.freshDyson F s z` (classical choice of a positive-imaginary solution of
  `m = N⁻¹ Tr (F - z - s m)⁻¹`) equals every positive root of the certificate's spectral
  residual `certificateDysonResidual hF.eigenvalues s z` (`0 < s`, `0 ≤ Im z`, Hermitian `F`,
  `N > 0`), by `certificate_dyson_unique_nonnegative`. In particular it equals
  `certificateCanonicalDyson` wherever the latter is a positive root.
* `conj_matchedA_eq_reference`: `conj (Layers.matchedA e) = certificateSemicircleReference e`.
* `regularEvent_certificate` (main). Constants: fixed `0 < c < 1` (the fresh variance: `pairS p =
  min(b, 1-2b)` for the pair, `1-2b` for the block) and `κ > 0` (the bulk `bulkInterval κ`) first;
  then `ε, r₀, s₀, v₀, C > 0` with `FreshConstants c r₀ s₀ v₀`; then for every `N > 0`, every
  Hermitian `F : Matrix (Fin N) (Fin N) ℂ` (no norm bound) and every `e ∈ bulkInterval κ`, if
  `‖χ‖ ≤ ε` with `χ = certificateChi F c e (conj (matchedA e)) = N⁻¹ Tr (F - e - c μ)⁻¹ - μ`,
  `μ = conj a(e)`, then `FreshRegular F c e r₀ s₀ v₀` and
  `‖freshDyson F c e - conj (matchedA e)‖ ≤ C ‖χ‖`.

The certificate is `BlockBand.Palm.certificate_semicircle_full`; no contract is assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints.Normalization

open Matrix
open BlockBand.Palm
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open scoped ComplexConjugate

section Dyson

variable {N : ℕ}

/-- The normalized trace `N⁻¹ Tr (F - z)⁻¹` is the certificate matrix trace. -/
theorem regularEvent_trace_eq_certificateMatrixTrace (F : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    (N : ℂ)⁻¹ * (F - z • 1)⁻¹.trace = certificateMatrixTrace F z := by
  unfold certificateMatrixTrace certificateMatrixResolvent
  rw [Fintype.card_fin, div_eq_inv_mul]

/-- The `freshDyson` equation is the vanishing of the certificate spectral residual. -/
theorem regularEvent_dyson_iff (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) {s : ℝ}
    {z m : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < m.im) :
    m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace ↔
      certificateDysonResidual hF.eigenvalues s z m = 0 := by
  have ha : (z + (s : ℂ) * m).im ≠ 0 := by
    have : 0 < (z + (s : ℂ) * m).im := by
      simpa using add_pos_of_nonneg_of_pos hz (mul_pos hs hm)
    exact this.ne'
  rw [regularEvent_trace_eq_certificateMatrixTrace, certificateMatrixTrace_eq_average F hF ha,
    certificateDysonResidual_eq_zero_iff]

/-- A positive root of the certificate residual is the root `freshDyson`. -/
theorem regularEvent_freshDyson_eq (hN : 0 < N) (F : Matrix (Fin N) (Fin N) ℂ)
    (hF : F.IsHermitian) {s : ℝ} {z m : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < m.im)
    (hres : certificateDysonResidual hF.eigenvalues s z m = 0) : freshDyson F s z = m := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hex : ∃ m : ℂ, 0 < m.im ∧ m = (N : ℂ)⁻¹ * (F - (z + (s : ℂ) * m) • 1)⁻¹.trace :=
    ⟨m, hm, (regularEvent_dyson_iff F hF hs hz hm).2 hres⟩
  have hspec := Classical.choose_spec hex
  have hcho : freshDyson F s z = Classical.choose hex := by
    unfold freshDyson
    exact dite_eq_left_of_eq_true (eq_true hex)
  rw [hcho]
  exact certificate_dyson_unique_nonnegative hF.eigenvalues hs hz hspec.1 hm
    ((regularEvent_dyson_iff F hF hs hz hspec.1).1 hspec.2) hres

/-- A positive solution of the matrix trace equation is a zero of the spectral residual. -/
theorem regularEvent_residual_zero (F : Matrix (Fin N) (Fin N) ℂ) (hF : F.IsHermitian) {s : ℝ}
    {z m : ℂ} (hs : 0 < s) (hz : 0 ≤ z.im) (hm : 0 < m.im)
    (h : m = certificateMatrixTrace F (z + s * m)) :
    certificateDysonResidual hF.eigenvalues s z m = 0 := by
  rw [← regularEvent_dyson_iff F hF hs hz hm, regularEvent_trace_eq_certificateMatrixTrace]
  exact h

end Dyson

/-- `conj a(e)` is the certificate's semicircle reference `(-e + i√(4-e²))/2`. -/
theorem conj_matchedA_eq_reference (e : ℝ) :
    conj (matchedA e) = certificateSemicircleReference e := by
  apply Complex.ext
  · simp [matchedA, certificateSemicircleReference]
  · simp [matchedA, certificateSemicircleReference]
    ring

/-- **Regular prior event, deterministic step.** Fixed first: the fresh variance `0 < c < 1` and
the bulk parameter `κ > 0`. Then there are `ε, r₀, s₀, v₀, C` (`FreshConstants c r₀ s₀ v₀`,
`ε, C > 0`) such that for every `N > 0`, Hermitian `F : Matrix (Fin N) (Fin N) ℂ` (no norm
bound) and `e ∈ bulkInterval κ`: if the one-trace error `χ = certificateChi F c e (conj (matchedA e))`
has `‖χ‖ ≤ ε`, then `F` is fresh-regular on the rectangle `[c-s₀, c] × [e-r₀, e+r₀] × [0,1]`
and the root satisfies `‖freshDyson F c e - conj (matchedA e)‖ ≤ C ‖χ‖`.
Consumes only the proved `certificate_semicircle_full`.
-/
theorem regularEvent_certificate {c κ : ℝ} (hc : 0 < c) (hc1 : c < 1) (hκ : 0 < κ) :
    ∃ ε r₀ s₀ v₀ C : ℝ, 0 < ε ∧ 0 < C ∧ FreshConstants c r₀ s₀ v₀ ∧
      ∀ (N : ℕ), 0 < N → ∀ F : Matrix (Fin N) (Fin N) ℂ, F.IsHermitian →
      ∀ e ∈ bulkInterval κ, ‖certificateChi F c e (conj (matchedA e))‖ ≤ ε →
        FreshRegular F c e r₀ s₀ v₀ ∧
          ‖freshDyson F c e - conj (matchedA e)‖ ≤
            C * ‖certificateChi F c e (conj (matchedA e))‖ := by
  set θ : ℝ := min κ 2 with hθdef
  have hθ : 0 < θ := lt_min hκ (by norm_num)
  have hθ2 : θ ≤ 2 := min_le_right _ _
  obtain ⟨ε, r, s₀, v₀, C, hε, hr, hs₀, hs₀c, hv₀, hC, hall⟩ :=
    certificate_semicircle_full.{0} hc hc1 hθ hθ2
  refine ⟨ε, r, s₀, v₀, C, hε, hC, ⟨hc, hc1, hr, hs₀, hs₀c, hv₀⟩, ?_⟩
  intro N hN F hF e he hχ
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hE : |e| ≤ 2 - θ := by
    have h1 := he.1
    have h2 := he.2
    have hθκ : θ ≤ κ := min_le_left _ _
    exact abs_le.2 ⟨by linarith, by linarith⟩
  rw [conj_matchedA_eq_reference] at hχ ⊢
  obtain ⟨hrect, hdist, -, -⟩ := hall (Fin N) F hF e hE hχ
  refine ⟨?_, ?_⟩
  · intro s hs x hx η hη
    obtain ⟨heq, hlo, hhi⟩ := hrect s hs.1 hs.2 x hx η hη.1 hη.2
    have hspos : 0 < s := by linarith [hs.1]
    have hz : ((x : ℂ) + Complex.I * η) = (⟨x, η⟩ : ℂ) := by
      apply Complex.ext <;> simp
    have hzim : 0 ≤ ((x : ℂ) + Complex.I * η).im := by simpa using hη.1
    have hmpos : 0 < (certificateCanonicalDyson hF.eigenvalues s
        ((x : ℂ) + Complex.I * η)).im := lt_of_lt_of_le hv₀ hlo
    have hfd := regularEvent_freshDyson_eq hN F hF hspos hzim hmpos
      (regularEvent_residual_zero F hF hspos hzim hmpos heq)
    rw [← hz, hfd]
    exact ⟨hlo, hhi⟩
  · obtain ⟨heq, hlo, -⟩ := hrect c (by linarith) le_rfl e (by simp [hr.le]) 0 le_rfl zero_le_one
    have hz : ((e : ℂ) + Complex.I * ((0 : ℝ) : ℂ)) = (e : ℂ) := by simp
    rw [hz] at heq hlo
    have hzim : 0 ≤ (e : ℂ).im := by simp
    have hmpos : 0 < (certificateCanonicalDyson hF.eigenvalues c (e : ℂ)).im :=
      lt_of_lt_of_le hv₀ hlo
    have hfd := regularEvent_freshDyson_eq hN F hF hc hzim hmpos
      (regularEvent_residual_zero F hF hc hzim hmpos heq)
    rw [hfd]
    exact hdist

end BlockBand.Endpoints.Normalization
