module

public import BlockBand.Transmission.Generator.LimitBasic
public import BlockBand.Transmission.Generator.Moments

/-!
# Bookkeeping for the limit martingale problem

* `lintegral_sq_le_of_abs_le`: `|f| ≤ c(|g₁| + |g₂|)` a.e. transfers second moments.
* `extendVec`, `ptVec`: the coordinates `(P_1(u), …, P_k(u))` as an fdd point family, and the
  identification of `A_k` read off them (`drift_extend_fin`, `drift_extend_lim`).
* `moment_pow_along`: the `ℕ`-power form of `pathPower_moment_along`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal

theorem lintegral_sq_le_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g₁ g₂ : α → ℝ} {c K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hg₁ : Measurable g₁) (h : ∀ᵐ x ∂μ, |f x| ≤ c * (|g₁ x| + |g₂ x|))
    (h₁ : ∫⁻ x, ‖g₁ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal K₁)
    (h₂ : ∫⁻ x, ‖g₂ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal K₂) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (2 * c ^ 2 * (K₁ + K₂)) := by
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (2 * c ^ 2) * (‖g₁ x‖ₑ ^ 2 + ‖g₂ x‖ₑ ^ 2) ∂μ := by
        refine lintegral_mono_ae (h.mono fun x hx => ?_)
        rw [enorm_sq_eq, enorm_sq_eq, enorm_sq_eq, ← ENNReal.ofReal_add (sq_nonneg _)
          (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ |f x| := abs_nonneg _
        have : f x ^ 2 ≤ (c * (|g₁ x| + |g₂ x|)) ^ 2 := by
          rw [← sq_abs (f x)]; exact pow_le_pow_left₀ h0 hx 2
        nlinarith [sq_abs (g₁ x), sq_abs (g₂ x), sq_nonneg (|g₁ x| - |g₂ x|), sq_nonneg c]
    _ = ENNReal.ofReal (2 * c ^ 2) * (∫⁻ x, ‖g₁ x‖ₑ ^ 2 ∂μ + ∫⁻ x, ‖g₂ x‖ₑ ^ 2 ∂μ) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (hg₁.enorm.pow_const 2)]
    _ ≤ ENNReal.ofReal (2 * c ^ 2) * (ENNReal.ofReal K₁ + ENNReal.ofReal K₂) := by gcongr
    _ = ENNReal.ofReal (2 * c ^ 2 * (K₁ + K₂)) := by
        rw [← ENNReal.ofReal_add hK₁ hK₂, ← ENNReal.ofReal_mul (by positivity)]

/-- Read `(x_0, …, x_{k-1})` as the power vector `P_j = x_{j-1}`, `1 ≤ j ≤ k`. -/
def extendVec (k : ℕ) (x : Fin k → ℝ) : ℕ → ℝ :=
  fun j => if h : 1 ≤ j ∧ j ≤ k then x ⟨j - 1, by omega⟩ else 0

theorem continuous_extendVec (k : ℕ) : Continuous (extendVec k) := by
  refine continuous_pi fun j => ?_
  by_cases h : 1 ≤ j ∧ j ≤ k
  · simp only [extendVec, h, and_self, ↓reduceDIte]; exact continuous_apply _
  · simp only [extendVec, h, ↓reduceDIte]; exact continuous_const

/-- The fdd points `(1,u), …, (k,u)`. -/
def ptVec (k : ℕ) (u : ℝ) : Fin k → ℕ × ℝ := fun l => (l.1 + 1, u)

theorem ptVec_pos {k : ℕ} {u : ℝ} (hu : 0 < u) : ∀ l, 1 ≤ (ptVec k u l).1 ∧ 0 < (ptVec k u l).2 :=
  fun _ => ⟨by simp [ptVec], hu⟩

theorem drift_extend_fin (D : ℝ) (k : ℕ) (b : ℝ) (e : ℕ → ℝ) (W : ℕ) (u : ℝ)
    (ω : GrowthPath W) :
    transmissionDrift D k (extendVec k (finVec b e W (ptVec k u) ω)) =
      transmissionDrift D k (pathPowers b (e W) W ⌊(W : ℝ) * u⌋₊ ω) := by
  refine transmissionDrift_congr D k fun j hj1 hj2 => ?_
  simp only [extendVec, hj1, hj2, and_self, ↓reduceDIte, finVec, ptVec, pathPowers]
  congr; omega

theorem drift_extend_lim {Ω : Type*} (D : ℝ) (k : ℕ) (Pk : ℕ → ℝ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    transmissionDrift D k (extendVec k (limVec Pk (ptVec k u) ω)) =
      transmissionDrift D k (fun i => Pk i u ω) ∧
    transmissionDrift D k (cutVec Pk u ω) = transmissionDrift D k (fun i => Pk i u ω) := by
  constructor
  · refine transmissionDrift_congr D k fun j hj1 hj2 => ?_
    simp only [extendVec, hj1, hj2, and_self, ↓reduceDIte, limVec, ptVec]
    congr; omega
  · exact transmissionDrift_congr D k fun j hj1 _ => by simp [cutVec, hj1]

/-- Second and fourth moments of `Tr T^k` along `e`, in `ℕ`-power form. -/
theorem moment_pow_along (hLU : TransmissionLengthUniformContract) {b : ℝ} (hb0 : 0 < b)
    (hb : b < 1 / 2) {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ}
    (he : IsMovingEnergy E Ce e) {ε : ℝ} (hε : 0 < ε) (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ t : ℝ, ε ≤ t → t ≤ T →
      ∀ k : ℕ, 1 ≤ k →
        ∫⁻ ω, ‖pathPower b (e W) W k ⌊(W : ℝ) * t⌋₊ ω‖ₑ ^ q ∂growthPathLaw W b ≤
          ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := pathPower_moment_along hLU hb0 hb hE1 hE2 he hε
    (p := (q : ℝ)) (by exact_mod_cast hq)
  refine ⟨C, hC0, fun T => ?_⟩
  obtain ⟨W₀, hW₀⟩ := hC T
  refine ⟨W₀, fun W hW t h1 h2 k hk => ?_⟩
  simpa [ENNReal.rpow_natCast] using hW₀ W hW t h1 h2 k hk

end BlockBand.Transmission.Generator
