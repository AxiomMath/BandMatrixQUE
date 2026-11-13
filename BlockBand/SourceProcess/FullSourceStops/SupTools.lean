module

public import BlockBand.SourceProcess.FullSource.Conversion
public import BlockBand.SourceProcess.FullSource.TagFinal

/-!
# Elementary tools for supremum moments

* `exists_le_pow_of_le_iSup_pow`: a value `λ > 0` below the `m`-th power of a finite supremum is
  below the `m`-th power of one term;
* `iSup_pow_le_sum`: `(sup_{j ≤ N} f_j)^m ≤ Σ_{j ≤ N} f_j^m`;
* `lintegral_compl_indicator_le`: `∫_{Aᶜ} f ≤ (∫ f²)^{1/2} μ(Aᶜ)^{1/2}` (Cauchy–Schwarz);
* `rpow_le_one_add_pow`: `x^p ≤ 1 + x^n` for `0 ≤ p ≤ n`;
* `tagMass_eq_zero_of_le`: a tag vanishes before its birth (`j ≤ k`);
* `lintegral_tagMass_pow_le`: from the `L^q` bound of a tag to `E t^q`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceStops

open MeasureTheory Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.SourceProcess.FullSource
open BlockBand.Transmission.Bridge BlockBand.Transmission.PassiveCovariance
open scoped ENNReal

theorem iSup_le_eq_finset_sup (f : ℕ → ℝ≥0∞) (N : ℕ) :
    (⨆ (j : ℕ) (_ : j ≤ N), f j) = (Finset.range (N + 1)).sup f := by
  rw [Finset.sup_eq_iSup]
  congr 1; funext j
  have : (j ≤ N) = (j ∈ Finset.range (N + 1)) := by simp
  rw [this]

theorem exists_le_pow_of_le_iSup_pow (f : ℕ → ℝ≥0∞) (N m : ℕ) (hm : m ≠ 0) {lam : ℝ≥0∞}
    (hlam : 0 < lam) (h : lam ≤ (⨆ (j : ℕ) (_ : j ≤ N), f j) ^ m) :
    ∃ j, j ≤ N ∧ lam ≤ f j ^ m := by
  rw [iSup_le_eq_finset_sup] at h
  rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : ℝ≥0∞ => x ^ m)
    (fun _ _ hxy => pow_le_pow_left₀ bot_le hxy m) (by simp [hm])] at h
  obtain ⟨j, hj, hle⟩ := (Finset.le_sup_iff hlam).mp h
  exact ⟨j, Nat.lt_succ_iff.mp (Finset.mem_range.mp hj), hle⟩

theorem iSup_pow_le_sum (f : ℕ → ℝ≥0∞) (N m : ℕ) (hm : m ≠ 0) :
    (⨆ (j : ℕ) (_ : j ≤ N), f j) ^ m ≤ ∑ j ∈ Finset.range (N + 1), f j ^ m := by
  rw [iSup_le_eq_finset_sup, Finset.apply_sup_eq_sup_comp_of_linearOrder (fun x : ℝ≥0∞ => x ^ m)
    (fun _ _ hxy => pow_le_pow_left₀ bot_le hxy m) (by simp [hm])]
  exact Finset.sup_le fun j hj => Finset.single_le_sum (f := fun j => f j ^ m)
    (fun _ _ => bot_le) hj

theorem lintegral_compl_indicator_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A : Set Ω} (hA : MeasurableSet A) {f : Ω → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, Aᶜ.indicator f ω ∂μ ≤ (∫⁻ ω, f ω ^ 2 ∂μ) ^ (1 / 2 : ℝ) * μ Aᶜ ^ (1 / 2 : ℝ) := by
  have hg : Measurable (Aᶜ.indicator fun _ : Ω => (1 : ℝ≥0∞)) :=
    measurable_const.indicator hA.compl
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hg.aemeasurable hf.aemeasurable
  have e1 : (fun ω => Aᶜ.indicator f ω) = (Aᶜ.indicator fun _ => (1 : ℝ≥0∞)) * f := by
    funext ω; by_cases h : ω ∈ Aᶜ <;> simp [Set.indicator, h]
  have e2 : ∫⁻ ω, (Aᶜ.indicator fun _ => (1 : ℝ≥0∞)) ω ^ (2 : ℝ) ∂μ = μ Aᶜ := by
    rw [← lintegral_indicator_one hA.compl]
    congr 1; funext ω
    by_cases h : ω ∈ Aᶜ
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, ENNReal.one_rpow, Pi.one_apply]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  have e3 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂μ = ∫⁻ ω, f ω ^ 2 ∂μ := by
    congr 1; funext ω; rw [ENNReal.rpow_two]
  rw [e1]
  refine hH.trans (le_of_eq ?_)
  rw [e2, e3, mul_comm]

theorem rpow_le_one_add_pow (x : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p) {n : ℕ} (hpn : p ≤ n) :
    x ^ p ≤ 1 + x ^ n := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx hp).trans le_self_add
  · push Not at hx
    refine le_trans ?_ le_add_self
    rw [← ENNReal.rpow_natCast]
    exact ENNReal.rpow_le_rpow_of_exponent_le hx.le hpn

variable {W : ℕ}

theorem tagMass_eq_zero_of_le (b E : ℝ) {j k : ℕ} (hjk : j ≤ k) (ω : GrowthPath W) :
    tagMass b E W j k ω = 0 := by
  have hP : tagProjection W j k = 0 := by
    ext x y
    simp only [tagProjection, Matrix.diagonal_apply, Matrix.zero_apply]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)
  simp [tagMass, tagResponse, hP]

theorem lintegral_tagMass_pow_le (b E : ℝ) (j k q : ℕ) (hq : 1 ≤ q) {C : ℝ}
    (h : eLpNorm (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace)
      (ENNReal.ofReal (q : ℝ)) (growthPathLaw W b) ≤ ENNReal.ofReal C) :
    ∫⁻ ω, ENNReal.ofReal (tagMass b E W j k ω) ^ q ∂growthPathLaw W b ≤ ENNReal.ofReal C ^ q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : ENNReal.ofReal (q : ℝ) ≠ 0 := by simp; omega
  have hmeas : AEStronglyMeasurable (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace)
      (growthPathLaw W b) := by
    have : (fun ω => (W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace) = fun ω =>
        (W : ℂ)⁻¹ * ((pastS b E W j k (pastCoords W j ω))ᴴ *
          pastS b E W j k (pastCoords W j ω)).trace := by
      funext ω; rw [tagResponse_eq_factor]
    rw [this]
    have hS := (measurable_pastS (W := W) b E j k).comp (measurable_pastCoords W j)
    have hT := measurable_matrix_mul' (measurable_matrix_conjTranspose' hS) hS
    refine (measurable_const.mul ?_).aestronglyMeasurable
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.measurable_sum _ fun i _ => hT.eval_matrix
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne ENNReal.ofReal_ne_top hmeas,
    ENNReal.toReal_ofReal hq0.le] at h
  have e : ∀ ω, ‖(W : ℂ)⁻¹ * (tagResponse b E W j k ω).trace‖ₑ =
      ENNReal.ofReal (tagMass b E W j k ω) := fun ω => by
    rw [← ofReal_norm, norm_tag_eq]
  simp only [e] at h
  have h2 := ENNReal.rpow_le_rpow h hq0.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one,
    ENNReal.rpow_natCast] at h2
  refine le_trans (le_of_eq ?_) h2
  congr 1; funext ω; rw [ENNReal.rpow_natCast]

end BlockBand.SourceProcess.FullSourceStops
