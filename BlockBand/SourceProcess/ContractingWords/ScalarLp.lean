module

public import BlockBand.SourceProcess.ContractingWords.ScalarExp

/-!
# Mean and `L^r` size of `Π_p (m_p + D_p)`

`scalar_expansion`: for at most `d` centered factors `D_p` with `‖D_p‖_{(d+2)r} ≤ β` and constants
`|m_p| ≤ μ`, the product `Π_p (m_p + D_p)` is integrable, its mean is `Π_p m_p + O((dβ)²)` and its
deviation from `Π_p m_p` is `O(dβ)` in `L^r`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ContractingWords

open MeasureTheory Finset
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
theorem eLpNorm_le_of_le_real {f : Ω → ℂ} {g : Ω → ℝ} (hf : AEStronglyMeasurable f ν)
    (hfg : ∀ ω, ‖f ω‖ ≤ g ω) (p : ℝ≥0∞) : eLpNorm f p ν ≤ eLpNorm g p ν :=
  eLpNorm_mono_real hf fun ω => hfg ω

/-- `‖K(S^a + S^b)‖_{r'} ≤ K(B^a + B^b)` from the moments of `S`. -/
theorem eLpNorm_two_pow_le {P : Type*} [Fintype P] {d : ℕ} (hcard : Fintype.card P ≤ d)
    (D : P → Ω → ℂ) (hD : ∀ p, AEStronglyMeasurable (D p) ν) {Q β K : ℝ} (hQ : 1 ≤ Q)
    (hβ : 0 ≤ β) (hK : 0 ≤ K) (hDβ : ∀ p, eLpNorm (D p) (ENNReal.ofReal Q) ν ≤ ENNReal.ofReal β)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {r' : ℝ} (hr' : 1 ≤ r') (har : a * r' ≤ Q)
    (hbr : b * r' ≤ Q) :
    eLpNorm (fun ω => K * ((∑ i, ‖D i ω‖) ^ a + (∑ i, ‖D i ω‖) ^ b)) (ENNReal.ofReal r') ν ≤
      ENNReal.ofReal (K * ((d * β) ^ a + (d * β) ^ b)) := by
  have hSm : AEStronglyMeasurable (fun ω => ∑ i, ‖D i ω‖) ν :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hD i).norm
  have h1 := eLpNorm_sumNorm_pow_le hcard D hD hQ hβ hDβ a ha (by linarith) har
  have h2 := eLpNorm_sumNorm_pow_le hcard D hD hQ hβ hDβ b hb (by linarith) hbr
  have e : (fun ω => K * ((∑ i, ‖D i ω‖) ^ a + (∑ i, ‖D i ω‖) ^ b)) =
      K • ((fun ω => (∑ i, ‖D i ω‖) ^ a) + fun ω => (∑ i, ‖D i ω‖) ^ b) := by
    funext ω; simp [smul_eq_mul]
  rw [e, eLpNorm_const_smul]
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r' := by simpa using hr'
  calc ‖K‖ₑ * eLpNorm ((fun ω => (∑ i, ‖D i ω‖) ^ a) + fun ω => (∑ i, ‖D i ω‖) ^ b)
        (ENNReal.ofReal r') ν ≤ ‖K‖ₑ * (ENNReal.ofReal ((d * β) ^ a) +
          ENNReal.ofReal ((d * β) ^ b)) := by
        gcongr; exact (eLpNorm_add_le hr1).trans (add_le_add h1 h2)
    _ = ENNReal.ofReal (K * ((d * β) ^ a + (d * β) ^ b)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), Real.enorm_eq_ofReal hK,
          ← ENNReal.ofReal_mul hK]

/-- **The scalar expansion.** -/
theorem scalar_expansion {P : Type*} [Fintype P] [DecidableEq P] {d : ℕ}
    (hcard : Fintype.card P ≤ d) (m : P → ℂ) {μ : ℝ} (hμ : 0 ≤ μ) (hm : ∀ p, ‖m p‖ ≤ μ)
    (D : P → Ω → ℂ) (hD : ∀ p, AEStronglyMeasurable (D p) ν) (hD0 : ∀ p, ∫ ω, D p ω ∂ν = 0)
    {r β : ℝ} (hr : 1 ≤ r) (hβ : 0 ≤ β)
    (hDβ : ∀ p, eLpNorm (D p) (ENNReal.ofReal ((d + 2) * r)) ν ≤ ENNReal.ofReal β) :
    Integrable (fun ω => ∏ p, (m p + D p ω)) ν ∧
      ‖∫ ω, ∏ p, (m p + D p ω) ∂ν - ∏ p, m p‖ ≤
        2 ^ d * (1 + μ) ^ d * (d * β) ^ 2 * (1 + (d * β) ^ d) ∧
      eLpNorm (fun ω => ∏ p, (m p + D p ω) - ∏ p, m p) (ENNReal.ofReal r) ν ≤
        ENNReal.ofReal (2 ^ d * (1 + μ) ^ d * (d * β) * (1 + (d * β) ^ d)) := by
  set Q : ℝ := (d + 2) * r
  set K : ℝ := 2 ^ d * (1 + μ) ^ d
  set B : ℝ := d * β
  have hK : 0 ≤ K := by positivity
  have hB : 0 ≤ B := by positivity
  have hQ1 : 1 ≤ Q := by
    have : (2 : ℝ) ≤ d + 2 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    nlinarith
  have hdr : ∀ k : ℕ, k ≤ d + 2 → (k : ℝ) * 1 ≤ Q := fun k hk => by
    have : (k : ℝ) ≤ d + 2 := by exact_mod_cast hk
    nlinarith
  have hdr' : ∀ k : ℕ, k ≤ d + 2 → (k : ℝ) * r ≤ Q := fun k hk => by
    have : (k : ℝ) ≤ d + 2 := by exact_mod_cast hk
    nlinarith
  set S : Ω → ℝ := fun ω => ∑ i, ‖D i ω‖
  set V : Ω → ℂ := fun ω => ∏ p, (m p + D p ω)
  set L : Ω → ℂ := fun ω => ∑ i, D i ω * ∏ j ∈ univ.erase i, m j
  set F2 : Ω → ℂ := fun ω => V ω - ∏ p, m p - L ω
  have hVm : AEStronglyMeasurable V ν :=
    Finset.aestronglyMeasurable_fun_prod _ fun p _ => aestronglyMeasurable_const.add (hD p)
  have hDi : ∀ p, Integrable (D p) ν := fun p =>
    MemLp.integrable (q := ENNReal.ofReal Q) (by simpa using hQ1)
      ((hDβ p).trans_lt ENNReal.ofReal_lt_top)
  have hLi : Integrable L ν := integrable_finsetSum _ fun i _ => (hDi i).mul_const _
  have hL0 : ∫ ω, L ω ∂ν = 0 := by
    simp only [L]
    rw [integral_finsetSum _ fun i _ => (hDi i).mul_const _]
    exact sum_eq_zero fun i _ => by rw [integral_mul_const, hD0 i, zero_mul]
  have hF2m : AEStronglyMeasurable F2 ν := (hVm.sub aestronglyMeasurable_const).sub hLi.1
  -- pointwise bounds
  have hpt := fun ω => expand_bounds m (fun p => D p ω) univ
  have hw := fun ω k => weight_le m (fun p => D p ω) hcard hμ hm k
  have hF1 : ∀ ω, ‖V ω - ∏ p, m p‖ ≤ K * (S ω ^ 1 + S ω ^ (1 + d)) := fun ω =>
    (hpt ω).1.trans (by simpa [S, K] using hw ω 1)
  have hF2 : ∀ ω, ‖F2 ω‖ ≤ K * (S ω ^ 2 + S ω ^ (2 + d)) := fun ω =>
    (hpt ω).2.trans (hw ω 2)
  -- the `L¹` bound of `F2`
  have hF2L : eLpNorm F2 1 ν ≤ ENNReal.ofReal (K * (B ^ 2 + B ^ (2 + d))) := by
    refine (eLpNorm_le_of_le_real hF2m hF2 1).trans ?_
    have := eLpNorm_two_pow_le hcard D hD hQ1 hβ hK hDβ (a := 2) (b := 2 + d) (by norm_num)
      (by omega) le_rfl (hdr 2 (by omega)) (hdr (2 + d) (by omega))
    simpa using this
  have hF2i : Integrable F2 ν :=
    memLp_one_iff_integrable.mp (hF2L.trans_lt ENNReal.ofReal_lt_top)
  have hVi : Integrable V ν := by
    have : V = fun ω => F2 ω + ∏ p, m p + L ω := by funext ω; simp only [F2]; ring
    rw [this]; exact (hF2i.add (integrable_const _)).add hLi
  refine ⟨hVi, ?_, ?_⟩
  · have e : ∫ ω, V ω ∂ν - ∏ p, m p = ∫ ω, F2 ω ∂ν := by
      have h : ∫ ω, F2 ω ∂ν = ∫ ω, V ω ∂ν - ∏ p, m p - ∫ ω, L ω ∂ν := by
        have h1 := integral_sub (hVi.sub (integrable_const (∏ p, m p))) hLi
        have h2 := integral_sub hVi (integrable_const (∏ p, m p))
        rw [integral_const, probReal_univ, one_smul] at h2
        simp only [F2]
        rw [← h2]; exact h1
      rw [h, hL0, sub_zero]
    change ‖∫ ω, V ω ∂ν - ∏ p, m p‖ ≤ _
    rw [e]
    have h1 : ‖∫ ω, F2 ω ∂ν‖ ≤ (eLpNorm F2 1 ν).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hF2m]
      exact (norm_integral_le_lintegral_norm _).trans_eq (by
        congr 1; refine lintegral_congr fun ω => ?_; rw [ofReal_norm])
    refine h1.trans ((ENNReal.toReal_le_of_le_ofReal (by positivity) hF2L).trans (le_of_eq ?_))
    rw [pow_add]; ring
  · have hb := eLpNorm_two_pow_le hcard D hD hQ1 hβ hK hDβ (a := 1) (b := 1 + d) le_rfl
      (by omega) hr (hdr' 1 (by omega)) (hdr' (1 + d) (by omega))
    refine (eLpNorm_le_of_le_real (hVm.sub aestronglyMeasurable_const) hF1 _).trans
      (hb.trans (le_of_eq ?_))
    congr 1; rw [pow_add]; ring

end BlockBand.SourceProcess.ContractingWords
