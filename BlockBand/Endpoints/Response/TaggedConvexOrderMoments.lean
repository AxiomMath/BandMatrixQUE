module

public import BlockBand.Endpoints.Response.TaggedConvexOrderDefs
public import BlockBand.Endpoints.Response.TaggedConvexOrderGaussian
public import BlockBand.Endpoints.Sine.MicroscopicTagPort

/-!
# Uniform moments of the tagged response, and `M_W` as the average of the tags

Law: `probedClockLaw W b` (the path `growthPathLaw W b` with an independent `h ~ CN(0, I_{2W})`),
`Z_{n;k} = lmf_tagResponseClock b e W n k = h*Q_{n;k}h`, `Q_{n;k} = W⁻¹Y_{n;k}`.

* `tco_tagClock_eq_quadForm`, `tco_posSemidef_tagQ`: `Z_{n;k} = h*Q_{n;k}h` with `Q_{n;k} ⪰ 0`.
* `tco_tag_pow_bound` (`FullSourceMomentsEnergyUniformContract.tag` and the dimension-free
  Gaussian bound): for `b`, a bulk margin `κ > 0`, a length horizon `T` and `m ≥ 1`, there are
  `C, W₀` with `E Z_{n;k}^m ≤ C` for all `W ≥ W₀`, energies `e ∈ bulkInterval κ`, `n ≤ TW`, `k < n`.
* `tco_tag_centered_bound`: the same for `E|Z_{n;k} - d|^{2p}`.
* `tco_rescaledClock_eq_average`, `tco_rescaledClock_jensen`: `M_W = n⁻¹ Σ_{k<n} Z_{n;k}` and
  Jensen for this average.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Layers
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal ComplexOrder

/-!
## The tagged response as a positive quadratic form
-/

/-- `Q_{n;k} = W⁻¹ Y_{n;k}`. -/
def tco_tagQ (b e : ℝ) (W n k : ℕ) (ω : GrowthPath W) : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ :=
  (W : ℝ)⁻¹ • tagResponse b e W n k ω

theorem tco_quadForm_real_smul {ι : Type*} [Fintype ι] (r : ℝ) (Γ : Matrix ι ι ℂ) (q : ι → ℂ) :
    quadForm (r • Γ) q = r * quadForm Γ q := by
  unfold quadForm
  rw [smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

theorem tco_tagClock_eq_quadForm (b e : ℝ) (W n k : ℕ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    lmf_tagResponseClock b e W n k x = quadForm (tco_tagQ b e W n k x.1) x.2 := by
  unfold lmf_tagResponseClock tco_tagQ
  rw [tco_quadForm_real_smul]

theorem tco_posSemidef_tagProjection (W n k : ℕ) : (tagProjection W n k).PosSemidef := by
  unfold tagProjection
  rw [posSemidef_diagonal_iff]
  intro x
  split_ifs <;> simp

theorem tco_posSemidef_tagResponse (b e : ℝ) (W n k : ℕ) (ω : GrowthPath W) :
    (tagResponse b e W n k ω).PosSemidef := by
  unfold tagResponse
  exact (tco_posSemidef_tagProjection W n k).conjTranspose_mul_mul_same _

theorem tco_posSemidef_tagQ (b e : ℝ) (W n k : ℕ) (ω : GrowthPath W) :
    (tco_tagQ b e W n k ω).PosSemidef :=
  (tco_posSemidef_tagResponse b e W n k ω).smul (inv_nonneg.2 (Nat.cast_nonneg W))

theorem tco_quadForm_nonneg_of_posSemidef {ι : Type*} [Fintype ι] {Q : Matrix ι ι ℂ}
    (hQ : Q.PosSemidef) (q : ι → ℂ) : 0 ≤ quadForm Q q := by
  have h := hQ.dotProduct_mulVec_nonneg q
  unfold quadForm
  exact (Complex.nonneg_iff.1 h).1

theorem tco_tagClock_nonneg (b e : ℝ) (W n k : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) :
    0 ≤ lmf_tagResponseClock b e W n k x := by
  rw [tco_tagClock_eq_quadForm]
  exact tco_quadForm_nonneg_of_posSemidef (tco_posSemidef_tagQ b e W n k x.1) x.2

theorem tco_trace_tagQ_nonneg (b e : ℝ) (W n k : ℕ) (ω : GrowthPath W) :
    0 ≤ (tco_tagQ b e W n k ω).trace.re :=
  (Complex.nonneg_iff.1 (tco_posSemidef_tagQ b e W n k ω).trace_nonneg).1

/-!
## Measurability
-/

theorem tco_continuous_toBlocks₁₂ {m n : Type*} :
    Continuous (fun M : Matrix (m ⊕ n) (m ⊕ n) ℂ => M.toBlocks₁₂) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inl i))

theorem tco_measurable_tagResponse (b e : ℝ) (W n k : ℕ) :
    Measurable (fun ω : GrowthPath W => tagResponse b e W n k ω) := by
  have hF : Measurable (fun ω : GrowthPath W => fullInverse b e W n ω) :=
    measurable_fullInverse_of b W n (α := GrowthPath W) measurable_const measurable_id
  have hc : Continuous (fun G : Matrix (FullSite W n) (FullSite W n) ℂ =>
      (G.toBlocks₁₂)ᴴ * tagProjection W n k * G.toBlocks₁₂) :=
    ((tco_continuous_toBlocks₁₂.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
      tco_continuous_toBlocks₁₂
  exact hc.measurable.comp hF

theorem tco_continuous_quadForm {ι : Type*} [Fintype ι] :
    Continuous (fun p : Matrix ι ι ℂ × (ι → ℂ) => quadForm p.1 p.2) := by
  unfold quadForm
  refine Complex.continuous_re.comp ?_
  exact (continuous_star.comp continuous_snd).dotProduct
    (continuous_fst.matrix_mulVec continuous_snd)

theorem tco_measurable_tagClock (b e : ℝ) (W n k : ℕ) :
    Measurable (fun x : GrowthPath W × (Fin 2 × Fin W → ℂ) => lmf_tagResponseClock b e W n k x) := by
  unfold lmf_tagResponseClock
  exact measurable_const.mul (tco_continuous_quadForm.measurable.comp
    (((tco_measurable_tagResponse b e W n k).comp measurable_fst).prodMk measurable_snd))

/-!
## Uniform moments
-/

theorem tco_isProbabilityMeasure_growthPathLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (growthPathLaw W b) :=
  passDeriv_isProbabilityMeasure_growthPathLaw W b

theorem tco_isProbabilityMeasure_probedClockLaw (W : ℕ) (b : ℝ) :
    IsProbabilityMeasure (probedClockLaw W b) := by
  have := tco_isProbabilityMeasure_growthPathLaw W b
  have := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  unfold probedClockLaw; infer_instance

/-- Uniform moments of the tagged response (the full tag clock moments along compact bulk sets,
plus the Gaussian bound). -/
theorem tco_tag_pow_bound (hMom : FullSourceMomentsEnergyUniformContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (T : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ n : ℕ,
      (n : ℝ) ≤ T * W → ∀ k : ℕ, k < n →
        ∫⁻ x, ENNReal.ofReal (lmf_tagResponseClock b e W n k x ^ m) ∂probedClockLaw W b ≤
          ENNReal.ofReal C := by
  obtain ⟨c, hc0, hc⟩ := tco_lintegral_quadForm_pow_le m
  obtain ⟨Ct, W₀, hCt⟩ := hMom.tag b hb hb' κ 0 T m hκ (by exact_mod_cast hm)
  set C' : ℝ := max Ct 0
  refine ⟨c * C' ^ m, W₀, by positivity, ?_⟩
  intro W hW e he n hn k hk
  have hprob := tco_isProbabilityMeasure_circularVectorLaw (ι := Fin 2 × Fin W)
  have hgp := tco_isProbabilityMeasure_growthPathLaw W b
  have hmeas := tco_measurable_tagClock b e W n k
  have hTr := hCt W hW e he e (by simp [IsNearEnergy]) n hn k hk
  set f : GrowthPath W → ℂ := fun ω => (W : ℂ)⁻¹ * (tagResponse b e W n k ω).trace
  -- the trace of `Q` against the contract's `L^m` norm
  have htr : ∀ ω, ENNReal.ofReal ((tco_tagQ b e W n k ω).trace.re) ≤ ‖f ω‖ₑ := by
    intro ω
    have e1 : (tco_tagQ b e W n k ω).trace.re = (f ω).re := by
      simp only [tco_tagQ, f, trace_smul, Complex.real_smul, Complex.mul_re, Complex.inv_re,
        Complex.inv_im, Complex.natCast_re, Complex.natCast_im]
      push_cast
      simp
    rw [e1, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
  have hfm : AEStronglyMeasurable f (growthPathLaw W b) := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_const.mul (Continuous.measurable (continuous_id.matrix_trace) |>.comp
      (tco_measurable_tagResponse b e W n k))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hLm : ∫⁻ ω, ‖f ω‖ₑ ^ (m : ℝ) ∂growthPathLaw W b ≤ ENNReal.ofReal C' ^ (m : ℝ) := by
    rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hmpos]
    have h1 : eLpNorm f (ENNReal.ofReal (m : ℝ)) (growthPathLaw W b) =
        eLpNorm' f (m : ℝ) (growthPathLaw W b) := by
      rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_pos.2 hmpos).ne' ENNReal.ofReal_ne_top hfm,
        ENNReal.toReal_ofReal hmpos.le]
    rw [← h1]
    exact ENNReal.rpow_le_rpow (hTr.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      hmpos.le
  calc ∫⁻ x, ENNReal.ofReal (lmf_tagResponseClock b e W n k x ^ m) ∂probedClockLaw W b
      = ∫⁻ ω, ∫⁻ h, ENNReal.ofReal (lmf_tagResponseClock b e W n k (ω, h) ^ m)
          ∂circularVectorLaw (Fin 2 × Fin W) ∂growthPathLaw W b := by
        unfold probedClockLaw
        exact lintegral_prod _
          (ENNReal.measurable_ofReal.comp (hmeas.pow_const m)).aemeasurable
    _ ≤ ∫⁻ ω, ENNReal.ofReal (c * (tco_tagQ b e W n k ω).trace.re ^ m) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        simp_rw [tco_tagClock_eq_quadForm]
        exact hc (Fin 2 × Fin W) _ (tco_posSemidef_tagQ b e W n k ω)
    _ ≤ ∫⁻ ω, ENNReal.ofReal c * ‖f ω‖ₑ ^ (m : ℝ) ∂growthPathLaw W b := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_pow (tco_trace_tagQ_nonneg b e W n k ω),
          ← ENNReal.rpow_natCast]
        gcongr
        exact htr ω
    _ = ENNReal.ofReal c * ∫⁻ ω, ‖f ω‖ₑ ^ (m : ℝ) ∂growthPathLaw W b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal C' ^ (m : ℝ) := by gcongr
    _ = ENNReal.ofReal (c * C' ^ m) := by
        rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (le_max_right _ _),
          ← ENNReal.ofReal_mul hc0]

/-- Uniform centered moments `E|Z_{n;k} - d|^{2p} ≤ C`. -/
theorem tco_tag_centered_bound (hMom : FullSourceMomentsEnergyUniformContract) {b : ℝ}
    (hb : 0 < b) (hb' : b < 1 / 2) {κ : ℝ} (hκ : 0 < κ) (T : ℝ) {p : ℕ} (hp : 0 < p) :
    ∃ (C : ℝ) (W₀ : ℕ), 0 ≤ C ∧ ∀ W : ℕ, W₀ ≤ W → ∀ e ∈ bulkInterval κ, ∀ n : ℕ,
      (n : ℝ) ≤ T * W → ∀ k : ℕ, k < n →
        ∫⁻ x, ENNReal.ofReal (|lmf_tagResponseClock b e W n k x - dStar b| ^ (2 * p))
          ∂probedClockLaw W b ≤ ENNReal.ofReal C := by
  obtain ⟨C, W₀, hC0, hC⟩ := tco_tag_pow_bound hMom hb hb' hκ T (m := 2 * p) (by omega)
  have hd : 0 ≤ dStar b := by unfold dStar; have : 0 < 1 - b := by linarith
                              positivity
  refine ⟨2 ^ (2 * p) * (C + dStar b ^ (2 * p)), W₀, by positivity, ?_⟩
  intro W hW e he n hn k hk
  have hprob := tco_isProbabilityMeasure_probedClockLaw W b
  have hmeas := tco_measurable_tagClock b e W n k
  have hpt : ∀ x, ENNReal.ofReal (|lmf_tagResponseClock b e W n k x - dStar b| ^ (2 * p)) ≤
      ENNReal.ofReal (2 ^ (2 * p)) * (ENNReal.ofReal (lmf_tagResponseClock b e W n k x ^ (2 * p))
        + ENNReal.ofReal (dStar b ^ (2 * p))) := by
    intro x
    have hz := tco_tagClock_nonneg b e W n k x
    rw [← ENNReal.ofReal_add (pow_nonneg hz _) (pow_nonneg hd _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have habs : |lmf_tagResponseClock b e W n k x - dStar b| ≤
        lmf_tagResponseClock b e W n k x + dStar b := by
      rw [abs_le]; constructor <;> linarith
    exact (pow_le_pow_left₀ (abs_nonneg _) habs _).trans (tco_add_pow_le _ _ hz hd _)
  calc _ ≤ ∫⁻ x, ENNReal.ofReal (2 ^ (2 * p)) *
        (ENNReal.ofReal (lmf_tagResponseClock b e W n k x ^ (2 * p)) +
          ENNReal.ofReal (dStar b ^ (2 * p))) ∂probedClockLaw W b := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ (2 * p)) *
        (∫⁻ x, ENNReal.ofReal (lmf_tagResponseClock b e W n k x ^ (2 * p)) ∂probedClockLaw W b +
          ENNReal.ofReal (dStar b ^ (2 * p))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 ^ (2 * p)) * (ENNReal.ofReal C + ENNReal.ofReal (dStar b ^ (2 * p))) := by
        gcongr; exact hC W hW e he n hn k hk
    _ = ENNReal.ofReal (2 ^ (2 * p) * (C + dStar b ^ (2 * p))) := by
        rw [← ENNReal.ofReal_add hC0 (pow_nonneg hd _), ← ENNReal.ofReal_mul (by positivity)]

/-!
## `M_W` is the average of the tags
-/

theorem tco_sum_tagProjection (W n : ℕ) :
    ∑ k ∈ Finset.range n, tagProjection W n k = 1 := by
  ext x y
  rw [Matrix.sum_apply]
  unfold tagProjection
  simp only [diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    simp only [one_apply_eq, ite_true]
    have hx := x.1.isLt
    rw [Finset.sum_eq_single (n - 1 - x.1.val)]
    · have hc : n - 1 - x.1.val < n ∧ x.1.val = n - 1 - (n - 1 - x.1.val) :=
        ⟨by omega, by omega⟩
      exact ite_eq_left_of_eq_true _ _ (eq_true hc)
    · intro k hk hne
      have : ¬ (k < n ∧ x.1.val = n - 1 - k) := by
        rintro ⟨_, h⟩
        exact hne (by rw [Finset.mem_range] at hk; omega)
      exact ite_eq_right_of_eq_false _ _ (eq_false this)
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  · simp [hxy, one_apply_ne hxy]

theorem tco_fullClock_eq_sum (b e : ℝ) (W n : ℕ) (ω : GrowthPath W) :
    fullClock b e W n ω = ∑ k ∈ Finset.range n, tagResponse b e W n k ω := by
  unfold fullClock tagResponse
  set B := boundaryToInterior b e W n ω
  rw [show Bᴴ * B = Bᴴ * (∑ k ∈ Finset.range n, tagProjection W n k) * B by
    rw [tco_sum_tagProjection, Matrix.mul_one], Matrix.mul_sum, Matrix.sum_mul]

/-- `M_W = n⁻¹ Σ_{k<n} Z_{n;k}` (with `M_W = T_W/τ_W`). -/
theorem tco_rescaledClock_eq_average (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (x : GrowthPath (s.W j) × (Fin 2 × Fin (s.W j) → ℂ)) :
    rescaledClock b s j x = ((s.n j : ℝ))⁻¹ * ∑ k ∈ Finset.range (s.n j),
      lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) k x := by
  unfold rescaledClock lmf_tagResponseClock
  rw [tco_fullClock_eq_sum]
  have hq : quadForm (∑ k ∈ Finset.range (s.n j), tagResponse b (s.energy j) (s.W j) (s.n j) k x.1)
      x.2 = ∑ k ∈ Finset.range (s.n j),
        quadForm (tagResponse b (s.energy j) (s.W j) (s.n j) k x.1) x.2 := by
    unfold quadForm
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  rw [hq, ← Finset.mul_sum, div_eq_mul_inv, mul_inv, mul_comm, mul_assoc]

/-- Jensen for the spatial average: `E|M_W - d|^{2p} ≤ n⁻¹ Σ_{k<n} E|Z_{n;k} - d|^{2p}` (for
`n ≥ 1`). -/
theorem tco_rescaledClock_jensen (b : ℝ) {τ E : ℝ} (s : ClockSequence τ E) (j : ℕ)
    (hn : 0 < s.n j) (p : ℕ) :
    ∫⁻ x, ENNReal.ofReal (|rescaledClock b s j x - dStar b| ^ (2 * p))
        ∂probedClockLaw (s.W j) b ≤
      ((s.n j : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range (s.n j),
        ∫⁻ x, ENNReal.ofReal
            (|lmf_tagResponseClock b (s.energy j) (s.W j) (s.n j) k x - dStar b| ^ (2 * p))
          ∂probedClockLaw (s.W j) b := by
  set n := s.n j
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpt : ∀ x, ENNReal.ofReal (|rescaledClock b s j x - dStar b| ^ (2 * p)) ≤
      ((n : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range n, ENNReal.ofReal
        (|lmf_tagResponseClock b (s.energy j) (s.W j) n k x - dStar b| ^ (2 * p)) := by
    intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity),
      show ((n : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((n : ℝ)⁻¹) by
        rw [ENNReal.ofReal_inv_of_pos hnR, ENNReal.ofReal_natCast],
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hev : Even (2 * p) := even_two_mul p
    rw [hev.pow_abs, tco_rescaledClock_eq_average]
    have e1 : ((n : ℝ))⁻¹ * ∑ k ∈ Finset.range n,
        lmf_tagResponseClock b (s.energy j) (s.W j) n k x - dStar b =
        ∑ k ∈ Finset.range n, ((n : ℝ))⁻¹ *
          (lmf_tagResponseClock b (s.energy j) (s.W j) n k x - dStar b) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hnR.ne', one_mul]
    rw [e1]
    have hj := Real.pow_arith_mean_le_arith_mean_pow_of_even (Finset.range n)
      (fun _ => ((n : ℝ))⁻¹)
      (fun k => lmf_tagResponseClock b (s.energy j) (s.W j) n k x - dStar b)
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hnR.ne'])
      hev
    refine hj.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hev.pow_abs]
  calc _ ≤ ∫⁻ x, ((n : ℝ≥0∞))⁻¹ * ∑ k ∈ Finset.range n, ENNReal.ofReal
        (|lmf_tagResponseClock b (s.energy j) (s.W j) n k x - dStar b| ^ (2 * p))
          ∂probedClockLaw (s.W j) b := lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hn.ne')),
          lintegral_finsetSum']
        intro k _
        exact (ENNReal.measurable_ofReal.comp
          ((((tco_measurable_tagClock b _ _ _ k).sub_const _).abs).pow_const _)).aemeasurable

end BlockBand.Endpoints
