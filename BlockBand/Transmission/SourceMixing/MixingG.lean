module

public import BlockBand.Transmission.SourceMixing.MixingErr
public import BlockBand.Transmission.SourceMixing.MassStatement
public import BlockBand.Transmission.LengthUniform.Jet
public import BlockBand.Transmission.PathJet.JetMoments

/-!
# One source-mixing quantity along the path

A nonnegative quantity `G ≤ Λq` satisfying the one-layer excess bound is `O(W^{-1/2})` in `L^p` at
every length `εW ≤ r ≤ TW` of the growth path, by the geometric recursion and the mass moments.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.SourceMixing

open MeasureTheory Matrix Filter
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements
open BlockBand.Transmission BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open scoped NNReal ENNReal ComplexOrder

/-- One mixing quantity along the path: `‖G(X_r)‖_p ≤ C₀ W^{-1/2}` for `εW ≤ r ≤ TW`. -/
theorem mx_G_final {b E : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (h1 : -2 < E) (h2 : E < 2) (s : ℂ)
    (G : (W : ℕ) → Matrix (Fin W) (Fin W) ℂ → ℝ) (hG : ∀ W, Measurable (G W))
    (hG0 : ∀ W X, 0 ≤ G W X) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hGq : ∀ (W : ℕ) (X : Matrix (Fin W) (Fin W) ℂ), (passiveY X).PosSemidef →
      G W X ≤ Λ * passiveMass b E X)
    {ρ : ℝ} (hρh : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) {p : ℝ} (hp : 1 ≤ p) {C C' : ℝ} {W₁ : ℕ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C')
    (hlayer : ∀ W : ℕ, W₁ ≤ W → ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => mx_excess (G W) ρ C b E s (X, ω)) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X))
    (hMass : MassMomentBound b E) (hJet : LengthUniform.PassiveJetMomentsUniform)
    (hs : IsStationaryJet b E s) {ε T : ℝ} (hε : 0 < ε) :
    ∃ (C₀ : ℝ) (W₀ : ℕ), 0 ≤ C₀ ∧ ∀ W : ℕ, W₀ ≤ W → ∀ r : ℕ, ε * W ≤ r → (r : ℝ) ≤ T * W →
      eLpNorm (fun ω => G W (pathX b E W r ω)) (ENNReal.ofReal p) (growthPathLaw W b) ≤
        ENNReal.ofReal (C₀ / Real.sqrt W) := by
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨K, hK0, hKT⟩ := hMass (2 * p) (by linarith)
  obtain ⟨Wq, hq⟩ := hKT T
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hE := PassiveLayer.mem_bulkInterval_min E
  obtain ⟨C₁, Cj, hJT⟩ := hJet b hb0 hb _ (2 * p) hκ (by linarith)
  obtain ⟨Wj, hj⟩ := hJT T
  obtain ⟨Wl₁, hl₁⟩ := LengthUniform.log_le_eps_mul C₁ (half_pos hε)
  obtain ⟨Wl₂, hl₂⟩ := LengthUniform.log_le_eps_mul (1 / Real.log (1 / ρ)) (half_pos hε)
  set D := max Cj 0
  set Kq := K * (1 + 2 / ε)
  have hKq : 0 ≤ Kq := by positivity
  set B := C * (2 * D * Kq + Kq ^ 2 + Kq) + C' * Kq
  have hB : 0 ≤ B := by positivity
  refine ⟨2 * (Λ * Kq) + B / (1 - ρ), max (max (max W₁ Wq) (max Wj Wl₁)) (max Wl₂ 1),
    by have : 0 < 1 - ρ := by linarith
       positivity, fun W hW r hr1 hr2 => ?_⟩
  simp only [max_le_iff] at hW
  obtain ⟨⟨⟨hW₁, hWq⟩, hWj, hWl₁⟩, hWl₂, hW1⟩ := hW
  set P := growthPathLaw W b
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hW0 : (0 : ℝ) < W := by linarith
  set r₀ := ⌈ε * W / 2⌉₊
  have hr₀a : ε * W / 2 ≤ r₀ := Nat.le_ceil _
  have hr₀b : (r₀ : ℝ) < ε * W / 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hr₀1 : 1 ≤ r₀ := Nat.one_le_iff_ne_zero.mpr (by
    intro h; rw [h] at hr₀a; simp at hr₀a; nlinarith [mul_pos hε hW0])
  have hr₀r : r₀ ≤ r := Nat.ceil_le.mpr (by nlinarith [mul_pos hε hW0])
  -- moments on `r₀ ≤ j ≤ TW`
  have hrange : ∀ j : ℕ, r₀ ≤ j → (j : ℝ) ≤ T * W →
      eLpNorm (fun ω => passiveMass b E (pathX b E W j ω)) (ENNReal.ofReal (2 * p)) P ≤
          ENNReal.ofReal Kq ∧
        eLpNorm (fun ω => jetDistance0 b E (pathX b E W j ω)) (ENNReal.ofReal (2 * p)) P ≤
          ENNReal.ofReal (D / W) ∧
        eLpNorm (fun ω => mx_jet1 b E s (pathX b E W j ω)) (ENNReal.ofReal (2 * p)) P ≤
          ENNReal.ofReal (D / W) := by
    intro j hj0 hjT
    have hjr : ε * W / 2 ≤ j := hr₀a.trans (by exact_mod_cast hj0)
    have hj1 : 1 ≤ j := hr₀1.trans hj0
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
    refine ⟨(hq W hWq j hj1 hjT).trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
    · have : (W : ℝ) / j ≤ 2 / ε := by
        rw [div_le_div_iff₀ hjpos hε]; nlinarith
      have := mul_le_mul_of_nonneg_left (add_le_add_left this 1) hK0
      simpa only [Kq, add_comm] using this
    have hlog : C₁ * Real.log W ≤ j := (hl₁ W hWl₁).trans (by linarith)
    have hJ := hj W hWj E hE s hs j hj1 hlog hjT
    have hae : (fun ω => PathJet.pathJet1 b E s W j ω) =ᵐ[P]
        fun ω => mx_jet1 b E s (pathX b E W j ω) :=
      PathJet.pathJet1_ae_eq (by linarith) h1 h2 s j
    rw [eLpNorm_congr_ae hae] at hJ
    have hDW : ENNReal.ofReal (Cj / W) ≤ ENNReal.ofReal (D / W) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_max_left _ _) hW0.le)
    exact ⟨(le_add_right le_rfl).trans (hJ.trans hDW), (le_add_left le_rfl).trans (hJ.trans hDW)⟩
  -- the start
  have hr₀T : (r₀ : ℝ) ≤ T * W := (by exact_mod_cast hr₀r : (r₀ : ℝ) ≤ r).trans hr2
  have hstart : eLpNorm (fun ω => G W (pathX b E W r₀ ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (Λ * Kq) := by
    have hpass : ∀ᵐ ω ∂P, (passiveY (pathX b E W r₀ ω)).PosSemidef := by
      filter_upwards [ae_passiveSample W (κ := fun _ => 0) (fun _ => le_rfl) (by linarith) h1 h2]
        with ω hP using pathNearSchur_passive hP r₀
    have hle : eLpNorm (fun ω => G W (pathX b E W r₀ ω)) (ENNReal.ofReal p) P ≤
        eLpNorm (fun ω => Λ * passiveMass b E (pathX b E W r₀ ω)) (ENNReal.ofReal p) P := by
      refine eLpNorm_mono_ae_real ((hG W).comp (PathJet.measurable_pathX b E r₀)).aestronglyMeasurable ?_
      filter_upwards [hpass] with ω hω
      rw [Real.norm_of_nonneg (hG0 _ _)]; exact hGq W _ hω
    refine hle.trans (mx_const_mul_le hΛ ?_)
    exact (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans
      (hrange r₀ le_rfl hr₀T).1
  have hrec := mx_rec (s := s) (C := C) hb h1 h2 hW1 (hG W) (hG0 W) hρ0 hρ1 hp
    (by positivity : 0 ≤ Λ * Kq) (by positivity : 0 ≤ B / Real.sqrt W) hr₀1 hr₀r hstart
    (fun j hj0 hjr => by
      have hjT : (j : ℝ) ≤ T * W := (by exact_mod_cast hjr.le : (j : ℝ) ≤ r).trans hr2
      obtain ⟨a, c, d⟩ := hrange j hj0 hjT
      exact mx_step_err (by linarith) h1 h2 hW1 hC hC' hp j (hG W) (hlayer W hW₁) hKq
        (le_max_right _ _) a c d)
  refine hrec.trans (ENNReal.ofReal_le_ofReal ?_)
  -- `ρ^{r-r₀} ≤ 2/W`
  have hpow : ρ ^ (r - r₀) ≤ 2 / W := by
    have h := PathJet.pow_le_two_div (W := W) (r := r - r₀ + 1) hρh hρ1 hW1 (by omega) (by
      rw [Nat.cast_add, Nat.cast_sub hr₀r, Nat.cast_one]
      have := hl₂ W hWl₂
      have : ε * W ≤ r := hr1
      linarith)
    simpa using h
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hs1 : Real.sqrt W ≤ W := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2W : 2 / (W : ℝ) ≤ 2 / Real.sqrt W := div_le_div_of_nonneg_left (by norm_num) hs0 hs1
  have h1ρ : 0 < 1 - ρ := by linarith
  have e : (2 * (Λ * Kq) + B / (1 - ρ)) / Real.sqrt W =
      2 / Real.sqrt W * (Λ * Kq) + B / Real.sqrt W / (1 - ρ) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_right (hpow.trans h2W) (by positivity : 0 ≤ Λ * Kq)
  linarith

end BlockBand.Transmission.SourceMixing
