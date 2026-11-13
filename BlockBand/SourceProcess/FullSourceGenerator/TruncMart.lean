module

public import BlockBand.SourceProcess.FullSourceGenerator.CondTools

/-!
# A maximal bound for the martingale part on one block

Real increments `d_i` (`G_{i+1}`-measurable, `d_i⁴` integrable) with conditional second moments
`E[d_i²|G_i] ≤ c + f_i`, `f_i ≥ 0` integrable. With `m_i = d_i - E[d_i|G_i]` and
`M_x = Σ_{i<x} m_i`, `block_tail`:
`P(max_{x ≤ n} |M_x| > λ) ≤ (8(cn + F)² + 8λ²F + 48D)/λ⁴`, `F = Σ_{i<n} E f_i`,
`D = Σ_{i<n} E d_i⁴`.

The proof stops `M` at its first exit from `[-λ, λ]` through the predictable events
`B_x = {|M_y| ≤ λ, y ≤ x}` (no stopping-time API): `M'_x = Σ_{i<x} 1_{B_i}m_i` has
`|M'_x| ≤ λ` on `B_x` and `max_{x≤n}|M_x| > λ ⇒ |M'_n| > λ`. Then
`E M'^4_{x+1} ≤ E M'^4_x + 8E[1_{B_x}M'^2_x m_x²] + 3E m_x⁴` (the cubic cross term vanishes),
`E[1_{B_x}M'^2_x m_x²] ≤ E[1_{B_x}M'^2_x E[d_x²|G_x]] ≤ cE M'^2_x + λ²E f_x`, and Markov.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.FullSourceGenerator

open MeasureTheory Set Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

theorem pow4_add_le (a b : ℝ) :
    (a + b) ^ 4 ≤ a ^ 4 + 4 * a ^ 3 * b + 8 * a ^ 2 * b ^ 2 + 3 * b ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (a - b))]

theorem sub_pow4_le (a b : ℝ) : (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg ((a + b) ^ 2), sq_nonneg (a ^ 2 - b ^ 2)]

theorem abs_le_one_add_pow4 (x : ℝ) : |x| ≤ 1 + x ^ 4 := by
  nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (x ^ 2 - 1), sq_nonneg (|x| - 1)]

theorem sq_le_one_add_pow4 (x : ℝ) : x ^ 2 ≤ 1 + x ^ 4 := by
  nlinarith [sq_nonneg (x ^ 2 - 1)]

/-- Integrability from `|f| ≤ 1 + g⁴`-type domination. -/
theorem integrable_pow_of_pow4 {f : Ω → ℝ} [IsFiniteMeasure μ] (hf : AEStronglyMeasurable f μ)
    (h4 : Integrable (fun ω => f ω ^ 4) μ) :
    Integrable f μ ∧ Integrable (fun ω => f ω ^ 2) μ := by
  refine ⟨integrable_of_norm_le hf ((integrable_const 1).add h4)
    (Filter.Eventually.of_forall fun ω => ?_), integrable_of_norm_le (hf.pow 2)
      ((integrable_const 1).add h4) (Filter.Eventually.of_forall fun ω => ?_)⟩
  · rw [Real.norm_eq_abs]; exact abs_le_one_add_pow4 _
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact sq_le_one_add_pow4 _

/-- **One step of the stopped martingale.** `M` is `G'`-measurable and `|M| ≤ λ` on the
`G'`-event `S`; the increment is `u = 1_S (d - E[d|G'])`. -/
theorem stopped_step [IsProbabilityMeasure μ] {G' : MeasurableSpace Ω} (hm : G' ≤ m0)
    {M : Ω → ℝ} (hM : StronglyMeasurable[G'] M) {S : Set Ω} (hS : MeasurableSet[G'] S)
    {lam : ℝ} (hlam : 0 ≤ lam) (hMS : ∀ ω ∈ S, |M ω| ≤ lam) (hM4 : Integrable (fun ω => M ω ^ 4) μ)
    {d f : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (hdm : AEStronglyMeasurable[m0] d μ)
    (hd4 : Integrable (fun ω => d ω ^ 4) μ) (hf0 : ∀ ω, 0 ≤ f ω) (hf : Integrable f μ)
    (hvar : μ[fun ω => d ω ^ 2 | G'] ≤ᵐ[μ] fun ω => c + f ω) :
    let u : Ω → ℝ := S.indicator fun ω => d ω - μ[d | G'] ω
    Integrable (fun ω => (M ω + u ω) ^ 4) μ ∧
    ∫ ω, (M ω + u ω) ^ 2 ∂μ ≤ ∫ ω, M ω ^ 2 ∂μ + (c + ∫ ω, f ω ∂μ) ∧
    ∫ ω, (M ω + u ω) ^ 4 ∂μ ≤ ∫ ω, M ω ^ 4 ∂μ +
      8 * (c * ∫ ω, M ω ^ 2 ∂μ + lam ^ 2 * ∫ ω, f ω ∂μ) + 48 * ∫ ω, d ω ^ 4 ∂μ := by
  intro u
  set g := μ[d | G'] with hg
  have hdi := integrable_pow_of_pow4 hdm hd4
  have hgm : StronglyMeasurable[G'] g := stronglyMeasurable_condExp
  have hg4 : Integrable (fun ω => g ω ^ 4) μ := integrable_condExp_pow hm (by decide) hdi.1 hd4
  set mm : Ω → ℝ := fun ω => d ω - g ω with hmmdef
  have hmm_m : AEStronglyMeasurable[m0] mm μ := hdm.sub (hgm.mono hm).aestronglyMeasurable
  have hmm4 : Integrable (fun ω => mm ω ^ 4) μ :=
    integrable_of_norm_le (hmm_m.pow 4) ((hd4.add hg4).const_mul 8)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
        exact sub_pow4_le _ _)
  have hmmi := integrable_pow_of_pow4 hmm_m hmm4
  have hmm4_le : ∫ ω, mm ω ^ 4 ∂μ ≤ 16 * ∫ ω, d ω ^ 4 ∂μ := by
    have h1 : ∫ ω, mm ω ^ 4 ∂μ ≤ ∫ ω, 8 * (d ω ^ 4 + g ω ^ 4) ∂μ :=
      integral_mono hmm4 ((hd4.add hg4).const_mul 8) fun ω => sub_pow4_le _ _
    rw [integral_const_mul, integral_add hd4 hg4] at h1
    have h2 := integral_condExp_pow_le hm (by decide : Even 4) hdi.1 hd4
    linarith
  have hS0 : MeasurableSet[m0] S := hm _ hS
  have hu_ind : ∀ ω, u ω = S.indicator mm ω := fun ω => rfl
  have hu4 : Integrable (fun ω => u ω ^ 4) μ :=
    (hmm4.indicator hS0).congr (Filter.Eventually.of_forall fun ω => by
      by_cases h : ω ∈ S <;> simp [hu_ind, h])
  have hu4_le : ∫ ω, u ω ^ 4 ∂μ ≤ ∫ ω, mm ω ^ 4 ∂μ := integral_mono hu4 hmm4 fun ω => by
    by_cases h : ω ∈ S <;> simp [hu_ind, h, Even.pow_nonneg (by decide : Even 4)]
  have hum : AEStronglyMeasurable[m0] u μ := hmm_m.indicator hS0
  have hui := integrable_pow_of_pow4 hum hu4
  have hMm : AEStronglyMeasurable[m0] M μ := (hM.mono hm).aestronglyMeasurable
  have hMi := integrable_pow_of_pow4 hMm hM4
  -- bounded `G'`-measurable weights
  have bnd : ∀ (k : ℕ), ∀ ω, ‖S.indicator (fun ω => M ω ^ k) ω‖ ≤ lam ^ k := fun k ω => by
    by_cases h : ω ∈ S
    · simp only [Set.indicator_of_mem h, norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hMS ω h) k
    · simp [Set.indicator_of_notMem h, pow_nonneg hlam]
  have Zm : ∀ k : ℕ, StronglyMeasurable[G'] (S.indicator fun ω => M ω ^ k) := fun k =>
    (hM.pow k).indicator hS
  have Zd : ∀ k : ℕ, Integrable (fun ω => S.indicator (fun ω => M ω ^ k) ω * d ω) μ := fun k =>
    hdi.1.bdd_mul ((Zm k).mono hm).aestronglyMeasurable (Filter.Eventually.of_forall (bnd k))
  have Zd2 : ∀ k : ℕ, Integrable (fun ω => S.indicator (fun ω => M ω ^ k) ω * d ω ^ 2) μ :=
    fun k => hdi.2.bdd_mul ((Zm k).mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (bnd k))
  have hMk_u : ∀ (k : ℕ) ω, M ω ^ k * u ω = S.indicator (fun ω => M ω ^ k) ω * mm ω :=
    fun k ω => by by_cases h : ω ∈ S <;> simp [hu_ind, h]
  have hMk_u2 : ∀ (k : ℕ) ω, M ω ^ k * u ω ^ 2 =
      S.indicator (fun ω => M ω ^ k) ω * (d ω - g ω) ^ 2 :=
    fun k ω => by by_cases h : ω ∈ S <;> simp [hu_ind, h, hmmdef]
  -- the vanishing cross terms
  have cross0 : ∀ k : ℕ, ∫ ω, M ω ^ k * u ω ∂μ = 0 := fun k => by
    simp_rw [hMk_u k]; exact integral_mul_sub_condExp hm (Zm k) (Zd k) hdi.1
  have crossI : ∀ k : ℕ, Integrable (fun ω => M ω ^ k * u ω) μ := fun k => by
    simp_rw [hMk_u k]
    exact hmmi.1.bdd_mul ((Zm k).mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (bnd k))
  have sqI : ∀ k : ℕ, Integrable (fun ω => M ω ^ k * u ω ^ 2) μ := fun k => by
    simp_rw [hMk_u2 k]
    exact hmmi.2.bdd_mul ((Zm k).mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (bnd k))
  have hcf : Integrable (fun ω => c + f ω) μ := (integrable_const c).add hf
  -- the variance terms
  have var : ∀ k : ℕ, Even k → ∫ ω, M ω ^ k * u ω ^ 2 ∂μ ≤
      ∫ ω, S.indicator (fun ω => M ω ^ k) ω * (c + f ω) ∂μ := fun k hk => by
    simp_rw [hMk_u2 k]
    have h0 : ∀ ω, 0 ≤ S.indicator (fun ω => M ω ^ k) ω := fun ω =>
      Set.indicator_nonneg (fun ω _ => hk.pow_nonneg _) ω
    have hC : ∀ ω, S.indicator (fun ω => M ω ^ k) ω ≤ lam ^ k := fun ω =>
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using bnd k ω)
    calc _ ≤ ∫ ω, S.indicator (fun ω => M ω ^ k) ω * d ω ^ 2 ∂μ :=
          integral_mul_sq_sub_condExp_le hm (Zm k) h0 hC hdm hdi.1 hdi.2
      _ = ∫ ω, S.indicator (fun ω => M ω ^ k) ω * μ[fun ω => d ω ^ 2 | G'] ω ∂μ :=
          (integral_mul_condExp hm (Zm k) (Zd2 k) hdi.2).symm
      _ ≤ _ := integral_mono_ae (integrable_mul_condExp (Zm k) (Zd2 k) hdi.2)
          (hcf.bdd_mul ((Zm k).mono hm).aestronglyMeasurable
            (Filter.Eventually.of_forall (bnd k)))
          (by filter_upwards [hvar] with ω hω; exact mul_le_mul_of_nonneg_left hω (h0 ω))
  have var0 : ∫ ω, u ω ^ 2 ∂μ ≤ c + ∫ ω, f ω ∂μ := by
    have h := var 0 (by decide)
    simp only [pow_zero, one_mul] at h
    refine h.trans ?_
    calc ∫ ω, S.indicator (fun _ => (1 : ℝ)) ω * (c + f ω) ∂μ ≤ ∫ ω, (c + f ω) ∂μ :=
          integral_mono ((hcf.bdd_mul (c := 1) (aestronglyMeasurable_const.indicator hS0)
            (Filter.Eventually.of_forall fun ω => by
              by_cases h : ω ∈ S <;> simp [h]))) hcf fun ω => by
            by_cases h : ω ∈ S <;> simp [h, add_nonneg hc (hf0 ω)]
      _ = c + ∫ ω, f ω ∂μ := by rw [integral_add (integrable_const c) hf]; simp
  have var2 : ∫ ω, M ω ^ 2 * u ω ^ 2 ∂μ ≤ c * ∫ ω, M ω ^ 2 ∂μ + lam ^ 2 * ∫ ω, f ω ∂μ := by
    refine (var 2 (by decide)).trans ?_
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hMi.2.const_mul c) (hf.const_mul _)]
    refine integral_mono (hcf.bdd_mul ((Zm 2).mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall (bnd 2))) ((hMi.2.const_mul c).add (hf.const_mul _))
      fun ω => ?_
    by_cases h : ω ∈ S
    · have hM2 : M ω ^ 2 ≤ lam ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hMS ω h) 2
      simp only [Set.indicator_of_mem h]
      nlinarith [hf0 ω, sq_nonneg (M ω)]
    · simp only [Set.indicator_of_notMem h, zero_mul]
      exact add_nonneg (mul_nonneg hc (sq_nonneg _)) (mul_nonneg (sq_nonneg _) (hf0 ω))
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_of_norm_le ((hMm.add hum).pow 4) ((hM4.add hu4).const_mul 8)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
    have := sub_pow4_le (M ω) (-u ω)
    simpa [sub_neg_eq_add, Even.neg_pow (by decide : Even 4)] using this
  · have e : ∫ ω, (M ω + u ω) ^ 2 ∂μ =
        ∫ ω, (M ω ^ 2 + 2 * (M ω ^ 1 * u ω) + u ω ^ 2) ∂μ := by
      congr 1; funext ω; ring
    have e2 : ∫ ω, (M ω ^ 2 + 2 * (M ω ^ 1 * u ω) + u ω ^ 2) ∂μ =
        ∫ ω, (M ω ^ 2 + 2 * (M ω ^ 1 * u ω)) ∂μ + ∫ ω, u ω ^ 2 ∂μ :=
      integral_add (hMi.2.add ((crossI 1).const_mul 2)) hui.2
    have e3 : ∫ ω, (M ω ^ 2 + 2 * (M ω ^ 1 * u ω)) ∂μ =
        ∫ ω, M ω ^ 2 ∂μ + ∫ ω, 2 * (M ω ^ 1 * u ω) ∂μ :=
      integral_add hMi.2 ((crossI 1).const_mul 2)
    rw [e, e2, e3, integral_const_mul, cross0 1]
    linarith
  · have e : ∫ ω, (M ω + u ω) ^ 4 ∂μ ≤
        ∫ ω, (M ω ^ 4 + 4 * (M ω ^ 3 * u ω) + 8 * (M ω ^ 2 * u ω ^ 2) + 3 * u ω ^ 4) ∂μ := by
      refine integral_mono ?_ (((hM4.add ((crossI 3).const_mul 4)).add
        ((sqI 2).const_mul 8)).add (hu4.const_mul 3)) fun ω => ?_
      · refine integrable_of_norm_le ((hMm.add hum).pow 4) ((hM4.add hu4).const_mul 8)
          (Filter.Eventually.of_forall fun ω => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (Even.pow_nonneg (by decide) _)]
        have := sub_pow4_le (M ω) (-u ω)
        simpa [sub_neg_eq_add, Even.neg_pow (by decide : Even 4)] using this
      · have := pow4_add_le (M ω) (u ω); simp only; linarith
    have e2 : ∫ ω, (M ω ^ 4 + 4 * (M ω ^ 3 * u ω) + 8 * (M ω ^ 2 * u ω ^ 2) + 3 * u ω ^ 4) ∂μ =
        ∫ ω, (M ω ^ 4 + 4 * (M ω ^ 3 * u ω) + 8 * (M ω ^ 2 * u ω ^ 2)) ∂μ +
          ∫ ω, 3 * u ω ^ 4 ∂μ :=
      integral_add ((hM4.add ((crossI 3).const_mul 4)).add ((sqI 2).const_mul 8))
        (hu4.const_mul 3)
    have e3 : ∫ ω, (M ω ^ 4 + 4 * (M ω ^ 3 * u ω) + 8 * (M ω ^ 2 * u ω ^ 2)) ∂μ =
        ∫ ω, (M ω ^ 4 + 4 * (M ω ^ 3 * u ω)) ∂μ + ∫ ω, 8 * (M ω ^ 2 * u ω ^ 2) ∂μ :=
      integral_add (hM4.add ((crossI 3).const_mul 4)) ((sqI 2).const_mul 8)
    have e4 : ∫ ω, (M ω ^ 4 + 4 * (M ω ^ 3 * u ω)) ∂μ =
        ∫ ω, M ω ^ 4 ∂μ + ∫ ω, 4 * (M ω ^ 3 * u ω) ∂μ :=
      integral_add hM4 ((crossI 3).const_mul 4)
    rw [e2, e3, e4, integral_const_mul, integral_const_mul, integral_const_mul, cross0 3] at e
    linarith

section Block

variable [IsProbabilityMeasure μ] (G : ℕ → MeasurableSpace Ω) (hG : ∀ i, G i ≤ m0)
  (hGmono : Monotone G)

include hG hGmono in
/-- **Maximal bound for the martingale part on one block.** -/
theorem block_tail (n : ℕ) (d f : ℕ → Ω → ℝ) (c lam : ℝ) (hc : 0 ≤ c) (hlam : 0 < lam)
    (hdm : ∀ i, StronglyMeasurable[G (i + 1)] (d i))
    (hd4 : ∀ i < n, Integrable (fun ω => d i ω ^ 4) μ)
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hf : ∀ i < n, Integrable (f i) μ)
    (hvar : ∀ i < n, μ[fun ω => d i ω ^ 2 | G i] ≤ᵐ[μ] fun ω => c + f i ω) :
    μ {ω | ∃ x ≤ n, lam < |∑ i ∈ range x, (d i ω - μ[d i | G i] ω)|} ≤
      ENNReal.ofReal ((8 * (c * n + ∑ i ∈ range n, ∫ ω, f i ω ∂μ) ^ 2 +
        8 * lam ^ 2 * ∑ i ∈ range n, ∫ ω, f i ω ∂μ +
          48 * ∑ i ∈ range n, ∫ ω, d i ω ^ 4 ∂μ) / lam ^ 4) := by
  -- notation
  set mm : ℕ → Ω → ℝ := fun i ω => d i ω - μ[d i | G i] ω with hmm
  set M : ℕ → Ω → ℝ := fun x ω => ∑ i ∈ range x, mm i ω with hM
  set B : ℕ → Set Ω := fun x => {ω | ∀ y ≤ x, |M y ω| ≤ lam} with hB
  set u : ℕ → Ω → ℝ := fun i => (B i).indicator (mm i) with hu
  set M' : ℕ → Ω → ℝ := fun x ω => ∑ i ∈ range x, u i ω with hM'
  set F : ℝ := ∑ i ∈ range n, ∫ ω, f i ω ∂μ
  -- measurability
  have hmm_m : ∀ i, StronglyMeasurable[G (i + 1)] (mm i) := fun i =>
    (hdm i).sub (stronglyMeasurable_condExp.mono (hGmono (Nat.le_succ i)))
  have hM_m : ∀ x, StronglyMeasurable[G x] (M x) := fun x =>
    Finset.stronglyMeasurable_fun_sum _ fun i hi =>
      (hmm_m i).mono (hGmono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
  have hB_m : ∀ x, MeasurableSet[G x] (B x) := fun x => by
    have : B x = ⋂ y ∈ Finset.range (x + 1), {ω | |M y ω| ≤ lam} := by
      ext ω; simp [hB]
    rw [this]
    refine Finset.measurableSet_biInter _ fun y hy => ?_
    have hy' : y ≤ x := Nat.lt_succ_iff.mp (Finset.mem_range.mp hy)
    exact measurableSet_le (continuous_abs.measurable.comp ((hM_m y).mono (hGmono hy')).measurable)
      measurable_const
  have hB_anti : ∀ {x y}, x ≤ y → B y ⊆ B x := fun hxy ω hω z hz => hω z (hz.trans hxy)
  have hu_m : ∀ i, StronglyMeasurable[G (i + 1)] (u i) := fun i =>
    (hmm_m i).indicator ((hGmono (Nat.le_succ i)) _ (hB_m i))
  have hM'_m : ∀ x, StronglyMeasurable[G x] (M' x) := fun x =>
    Finset.stronglyMeasurable_fun_sum _ fun i hi =>
      (hu_m i).mono (hGmono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
  -- `M' = M` on `B`
  have hM'eq : ∀ x ω, ω ∈ B x → M' x ω = M x ω := fun x ω hω => by
    refine Finset.sum_congr rfl fun i hi => ?_
    have : ω ∈ B i := hB_anti (Finset.mem_range.mp hi).le hω
    simp [hu, Set.indicator_of_mem this]
  have hM'B : ∀ x ω, ω ∈ B x → |M' x ω| ≤ lam := fun x ω hω => by
    rw [hM'eq x ω hω]; exact hω x le_rfl
  -- the exit inclusion
  have hincl : {ω | ∃ x ≤ n, lam < |M x ω|} ⊆ {ω | lam ^ 4 ≤ M' n ω ^ 4} := by
    intro ω ⟨x, hxn, hx⟩
    classical
    have hex : ∃ x, lam < |M x ω| := ⟨x, hx⟩
    set x₀ := Nat.find hex
    have hx₀ : lam < |M x₀ ω| := Nat.find_spec hex
    have hx₀n : x₀ ≤ n := (Nat.find_min' hex hx).trans hxn
    have hin : ∀ i < x₀, ω ∈ B i := fun i hi y hy =>
      not_lt.mp (Nat.find_min hex (lt_of_le_of_lt hy hi))
    have hout : ∀ i, x₀ ≤ i → ω ∉ B i := fun i hi hω => (not_lt.mpr (hω x₀ hi)) hx₀
    have hsum : M' n ω = M x₀ ω := by
      simp only [hM', hM]
      rw [← Finset.sum_range_add_sum_Ico _ hx₀n]
      have h2 : ∑ i ∈ Finset.Ico x₀ n, u i ω = 0 := Finset.sum_eq_zero fun i hi => by
        simp [hu, Set.indicator_of_notMem (hout i (Finset.mem_Ico.mp hi).1)]
      rw [h2, add_zero]
      exact Finset.sum_congr rfl fun i hi => by
        simp [hu, Set.indicator_of_mem (hin i (Finset.mem_range.mp hi))]
    have h4 : lam ^ 4 < M' n ω ^ 4 := by
      have h := pow_lt_pow_left₀ hx₀ hlam.le (by norm_num : (4 : ℕ) ≠ 0)
      rwa [Even.pow_abs (by decide : Even 4), ← hsum] at h
    exact h4.le
  -- the moment recursion
  have hF0 : ∀ x, 0 ≤ ∑ i ∈ range x, ∫ ω, f i ω ∂μ := fun x =>
    Finset.sum_nonneg fun i _ => integral_nonneg (hf0 i)
  have hFle : ∀ x ≤ n, ∑ i ∈ range x, ∫ ω, f i ω ∂μ ≤ F := fun x hx =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hx)
      fun i _ _ => integral_nonneg (hf0 i)
  have hstep : ∀ x, M' (x + 1) = fun ω => M' x ω + u x ω := fun x => by
    funext ω; simp [hM', Finset.sum_range_succ]
  have key : ∀ x ≤ n, Integrable (fun ω => M' x ω ^ 4) μ ∧
      ∫ ω, M' x ω ^ 2 ∂μ ≤ c * x + ∑ i ∈ range x, ∫ ω, f i ω ∂μ ∧
      ∫ ω, M' x ω ^ 4 ∂μ ≤ 8 * (c * x + F) ^ 2 + 8 * lam ^ 2 * ∑ i ∈ range x, ∫ ω, f i ω ∂μ +
        48 * ∑ i ∈ range x, ∫ ω, d i ω ^ 4 ∂μ := by
    intro x
    induction x with
    | zero =>
      intro _
      refine ⟨?_, ?_, ?_⟩
      · simp [hM']
      · simp [hM']
      · simp only [hM', Finset.range_zero, Finset.sum_empty]
        simp
        positivity
    | succ x ih =>
      intro hx
      have hxn : x < n := hx
      obtain ⟨hI4, h2, h4⟩ := ih hxn.le
      obtain ⟨hI4', h2', h4'⟩ := stopped_step (hG x) (hM'_m x) (hB_m x) hlam.le (hM'B x) hI4 hc
        ((hdm x).mono (hG _)).aestronglyMeasurable (hd4 x hxn) (hf0 x) (hf x hxn) (hvar x hxn)
      rw [hstep x]
      refine ⟨hI4', ?_, ?_⟩
      · rw [Finset.sum_range_succ]; push_cast
        exact h2'.trans (by linarith)
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]; push_cast
        have hFx := hFle x hxn.le
        have hFx0 := hF0 x
        have hI := integral_nonneg (μ := μ) fun ω => (sq_nonneg (M' x ω))
        refine h4'.trans ?_
        have hcF : 0 ≤ c * x + F := add_nonneg (mul_nonneg hc (Nat.cast_nonneg _)) (hF0 n)
        nlinarith [mul_le_mul_of_nonneg_left h2 hc]
  obtain ⟨hI4, -, h4⟩ := key n le_rfl
  have hmark : μ {ω | lam ^ 4 ≤ M' n ω ^ 4} ≤
      ENNReal.ofReal ((∫ ω, M' n ω ^ 4 ∂μ) / lam ^ 4) := by
    have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun ω =>
      Even.pow_nonneg (by decide : Even 4) (M' n ω)) hI4 (lam ^ 4)
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ (by positivity)]
    linarith
  calc μ {ω | ∃ x ≤ n, lam < |∑ i ∈ range x, (d i ω - μ[d i | G i] ω)|}
      ≤ μ {ω | lam ^ 4 ≤ M' n ω ^ 4} := measure_mono hincl
    _ ≤ _ := hmark.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right h4
        (by positivity)))

end Block

end BlockBand.SourceProcess.FullSourceGenerator
