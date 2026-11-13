module

public import BlockBand.Transmission.Generator.Interface
public import BlockBand.Transmission.SpectralGenerator
public import BlockBand.Transmission.Bridge.AlmostSure
public import BlockBand.Transmission.SourceMixing.MassUpdate

/-!
# Power sums of the transmission matrix: spectral bounds and measurability

* `trace_pow_mem`: for `0 ⪯ T ⪯ I` and `k ≥ 1`, `0 ≤ Re Tr T^k ≤ Re Tr T` (spectral theorem and
  `powerTrace_le_conductance`).
* `pathPower_mem`: almost surely `0 ≤ Tr T_r^k ≤ g_r ≤ W` (`k ≥ 1`), at every energy in `(-2,2)`.
* `measurable_pathPower_adapted`: `Tr T_r^k` is `growthSigma W r`-measurable.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open scoped ComplexOrder

/-- `Re Tr T^k = Σ λ_i^k` for Hermitian `T`. -/
theorem trace_pow_re_eq {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}
    (hT : T.IsHermitian) (k : ℕ) : (T ^ k).trace.re = ∑ i, hT.eigenvalues i ^ k := by
  have hs := hT.spectral_theorem
  have hk : T ^ k = (hT.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((hT.eigenvalues i : ℂ)) ^ k) * star (hT.eigenvectorUnitary : Matrix n n ℂ) := by
    conv_lhs => rw [hs]
    rw [← map_pow, diagonal_pow]
    rfl
  rw [hk, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- **`0 ≤ Tr T^k ≤ Tr T`** for `0 ⪯ T ⪯ I`, `k ≥ 1`. -/
theorem trace_pow_mem {n : Type*} [Fintype n] [DecidableEq n] {T : Matrix n n ℂ}
    (h0 : T.PosSemidef) (h1 : (1 - T).PosSemidef) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ (T ^ k).trace.re ∧ (T ^ k).trace.re ≤ T.trace.re := by
  have hT := h0.1
  have hev : ∀ i, 0 ≤ hT.eigenvalues i ∧ hT.eigenvalues i ≤ 1 := by
    intro i
    refine ⟨h0.eigenvalues_nonneg i, ?_⟩
    have he := hT.eigenvalues_eq i
    have hp := h1.re_dotProduct_nonneg (hT.eigenvectorBasis i)
    have hn : star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ (⇑(hT.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hT.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [sub_mulVec, one_mulVec, dotProduct_sub, hn, map_sub] at hp
    simp only [RCLike.one_re] at hp
    have : hT.eigenvalues i = RCLike.re (star (⇑(hT.eigenvectorBasis i)) ⬝ᵥ
        (T *ᵥ ⇑(hT.eigenvectorBasis i))) := he
    linarith
  have h1' := trace_pow_re_eq hT 1
  simp only [pow_one] at h1'
  rw [trace_pow_re_eq hT k, h1']
  simpa [powerTrace] using powerTrace_le_conductance (fun i => hT.eigenvalues i) hev k hk

variable {W : ℕ}

/-- Almost surely `0 ≤ Tr T_r^k ≤ g_r` and `g_r ≤ W` (`k ≥ 1`). -/
theorem pathPower_mem {b E : ℝ} (hb : b < 1) (hE1 : -2 < E) (hE2 : E < 2) :
    ∀ᵐ ω ∂growthPathLaw W b, ∀ k r : ℕ, 1 ≤ k →
      0 ≤ pathPower b E W k r ω ∧ pathPower b E W k r ω ≤ pathConductance b E W r ω ∧
        pathConductance b E W r ω ≤ W := by
  filter_upwards [Bridge.ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) hb hE1 hE2]
    with ω hω
  intro k r hk
  have h0 := Bridge.pathTransmission_posSemidef hω r
  have h1 := Bridge.one_sub_pathTransmission_posSemidef b E (fun _ => 0) W r ω
  obtain ⟨ha, hb'⟩ := trace_pow_mem h0 h1 k hk
  exact ⟨ha, hb', (Bridge.conductanceOf_pathTransmission_mem hω r).2⟩

/-- `X ↦ Re Tr T(X)^k` is measurable. -/
theorem measurable_trace_pow_transmission (b E : ℝ) (k : ℕ) :
    Measurable fun X : Matrix (Fin W) (Fin W) ℂ => ((passiveTransmission b E X) ^ k).trace.re := by
  have hc : Continuous fun Q : Matrix (Fin W) (Fin W) ℂ =>
      ((((4 * etaZ b E : ℝ)) : ℂ) • Q) ^ k |>.trace.re :=
    Complex.continuous_re.comp
      ((continuous_id.const_smul (((4 * etaZ b E : ℝ)) : ℂ)).pow k).matrix_trace
  exact hc.measurable.comp (SourceMixing.mu_measurable_passiveQ b E)

/-- **Adaptedness**: `Tr T_r^k` is `growthSigma W r`-measurable. -/
theorem measurable_pathPower_adapted (b E : ℝ) (k r : ℕ) :
    Measurable[growthSigma W r] (pathPower b E W k r) :=
  (measurable_trace_pow_transmission b E k).comp (Bridge.pathNearSchur_adapted b E _ W r)

theorem growthSigma_le (W r : ℕ) : growthSigma W r ≤ (inferInstance : MeasurableSpace (GrowthPath W)) :=
  Measurable.comap_le (by fun_prop)

theorem measurable_pathPower (b E : ℝ) (k r : ℕ) : Measurable (pathPower b E W k r) :=
  (measurable_pathPower_adapted b E k r).mono (growthSigma_le W r) le_rfl

end BlockBand.Transmission.Generator
