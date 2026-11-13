module

public import BlockBand.Transmission.SourceMixing.MixingPath

/-!
# The forcing of the source-mixing recursions

The forcing term `C e(X_j) q_j + excess_j` of the geometric recursion for a source-mixing quantity
has `L^p` norm `O(W^{-1/2})`, given `L^{2p}` bounds on the mass and on the jet distances `δ₀, δ₁`.
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

variable {W : ℕ}

theorem mx_add_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g : Ω → ℝ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hf : eLpNorm f p μ ≤ ENNReal.ofReal a)
    (hg : eLpNorm g p μ ≤ ENNReal.ofReal c) :
    eLpNorm (fun ω => f ω + g ω) p μ ≤ ENNReal.ofReal (a + c) := by
  rw [ENNReal.ofReal_add ha hc]
  exact (eLpNorm_add_le (f := f) (g := g) hp).trans (add_le_add hf hg)

theorem mx_const_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ≥0∞}
    {f : Ω → ℝ} {a c : ℝ} (hc : 0 ≤ c) (hf : eLpNorm f p μ ≤ ENNReal.ofReal a) :
    eLpNorm (fun ω => c * f ω) p μ ≤ ENNReal.ofReal (c * a) := by
  have h := eLpNorm_const_smul c f p μ
  rw [show (c • f) = fun ω => c * f ω from rfl, Real.enorm_eq_ofReal hc] at h
  rw [h, ENNReal.ofReal_mul hc]
  exact mul_le_mul' le_rfl hf

theorem mx_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p : ℝ} (hp : 0 < p)
    {f g : Ω → ℝ} {a c : ℝ} (ha : 0 ≤ a) (hf : eLpNorm f (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal a)
    (hg : eLpNorm g (ENNReal.ofReal (2 * p)) μ ≤ ENNReal.ofReal c) :
    eLpNorm (fun ω => f ω * g ω) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (a * c) := by
  rw [ENNReal.ofReal_mul ha]
  exact (mx_eLpNorm_mul_le hp).trans (mul_le_mul' hf hg)

theorem mx_err_eq (b E : ℝ) (s : ℂ) (X : Matrix (Fin W) (Fin W) ℂ) :
    mx_err b E s X = jetDistance0 b E X * passiveMass b E X + mx_jet1 b E s X * passiveMass b E X +
      (W : ℝ)⁻¹ * (passiveMass b E X * passiveMass b E X) +
      (W : ℝ)⁻¹ ^ 2 * passiveMass b E X := by
  unfold mx_err; ring

/-- The forcing at one length `j` is `O(W^{-1/2})` in `L^p`. -/
theorem mx_step_err {b E : ℝ} (hb : b < 1) (h1 : -2 < E) (h2 : E < 2) (hW : 1 ≤ W)
    {G : Matrix (Fin W) (Fin W) ℂ → ℝ} {ρ C C' : ℝ} (hC : 0 ≤ C) (hC' : 0 ≤ C') {s : ℂ}
    {p : ℝ} (hp : 1 ≤ p) (j : ℕ) (hGm : Measurable G)
    (hlayer : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      eLpNorm (fun ω => mx_excess G ρ C b E s (X, ω)) (ENNReal.ofReal p) (freshLaw W b) ≤
        ENNReal.ofReal (C' / Real.sqrt W * passiveMass b E X))
    {K D : ℝ} (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hq : eLpNorm (fun ω => passiveMass b E (pathX b E W j ω)) (ENNReal.ofReal (2 * p))
      (growthPathLaw W b) ≤ ENNReal.ofReal K)
    (hδ0 : eLpNorm (fun ω => jetDistance0 b E (pathX b E W j ω)) (ENNReal.ofReal (2 * p))
      (growthPathLaw W b) ≤ ENNReal.ofReal (D / W))
    (hδ1 : eLpNorm (fun ω => mx_jet1 b E s (pathX b E W j ω)) (ENNReal.ofReal (2 * p))
      (growthPathLaw W b) ≤ ENNReal.ofReal (D / W)) :
    eLpNorm (fun ω => C * mx_err b E s (pathX b E W j ω) +
        mx_excess G ρ C b E s (pathX b E W j ω, freshSample W j ω)) (ENNReal.ofReal p)
        (growthPathLaw W b) ≤
      ENNReal.ofReal ((C * (2 * D * K + K ^ 2 + K) + C' * K) / Real.sqrt W) := by
  set P := growthPathLaw W b
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hW0 : (0 : ℝ) < W := by linarith
  have hDW : 0 ≤ D / W := by positivity
  have hWi : 0 ≤ (W : ℝ)⁻¹ := by positivity
  -- `‖q‖_p ≤ K`
  have hqp : eLpNorm (fun ω => passiveMass b E (pathX b E W j ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal K :=
    (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))).trans hq
  have t1 := mx_mul_le hp0 hDW hδ0 hq
  have t2 := mx_mul_le hp0 hDW hδ1 hq
  have t3 := mx_const_mul_le hWi (mx_mul_le hp0 hK hq hq)
  have t4 := mx_const_mul_le (sq_nonneg (W : ℝ)⁻¹) hqp
  have s12 := mx_add_le hp1 (by positivity) (by positivity) t1 t2
  have s123 := mx_add_le hp1 (by positivity) (by positivity) s12 t3
  have s1234 := mx_add_le hp1 (by positivity) (by positivity) s123 t4
  have hm := mx_const_mul_le hC s1234
  have hex := (mx_eLpNorm_path_le hb h1 h2 (measurable_mx_excess hGm ρ C b E s)
    (measurable_passiveMass b E) hp0 (by positivity) j hlayer).trans
    (mul_le_mul' le_rfl hqp)
  rw [← ENNReal.ofReal_mul (by positivity)] at hex
  have htot := mx_add_le hp1 (by positivity) (by positivity) hm hex
  simp only [← mx_err_eq] at htot
  refine htot.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the scalar inequality
  have hs1 : Real.sqrt W ≤ W := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hs0 : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
  have hinv : (W : ℝ)⁻¹ ≤ (Real.sqrt W)⁻¹ := inv_anti₀ hs0 hs1
  have hinv2 : (W : ℝ)⁻¹ ^ 2 ≤ (W : ℝ)⁻¹ := by
    rw [sq]; exact mul_le_of_le_one_left hWi (inv_le_one_of_one_le₀ hWr)
  have e1 : D / W * K = D * K * (W : ℝ)⁻¹ := by rw [div_eq_mul_inv]; ring
  rw [e1, div_eq_mul_inv _ (Real.sqrt W)]
  have hK2 : 0 ≤ K * K := mul_nonneg hK hK
  have hDK : 0 ≤ D * K := mul_nonneg hD hK
  have a1 : D * K * (W : ℝ)⁻¹ ≤ D * K * (Real.sqrt W)⁻¹ := mul_le_mul_of_nonneg_left hinv hDK
  have a2 : (W : ℝ)⁻¹ * (K * K) ≤ (Real.sqrt W)⁻¹ * (K * K) := mul_le_mul_of_nonneg_right hinv hK2
  have a3 : (W : ℝ)⁻¹ ^ 2 * K ≤ (Real.sqrt W)⁻¹ * K :=
    mul_le_mul_of_nonneg_right (hinv2.trans hinv) hK
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add a1 a1) a2) a3) hC
  have e : (C * (2 * D * K + K ^ 2 + K) + C' * K) * (Real.sqrt W)⁻¹ =
      C * (D * K * (Real.sqrt W)⁻¹ + D * K * (Real.sqrt W)⁻¹ + (Real.sqrt W)⁻¹ * (K * K) +
        (Real.sqrt W)⁻¹ * K) + C' * (Real.sqrt W)⁻¹ * K := by ring
  rw [div_eq_mul_inv, e]; linarith

end BlockBand.Transmission.SourceMixing
