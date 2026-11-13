module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalCrude

/-!
# The generic step under the closed law

Measure: `closedLaw b W np`; filtration `b3Sigma W j np`; alive set `b3Alive` (a.e. its Borel
version `b3AliveM`, a `b3Sigma W j`-event).
* `mem_kBox_iff`, `measurableSet_kBox_preimage`: the box event is measurable;
* `integrable_indicator_of_bound`, `integrable_indicator_of_pow4`,
  `integrable_indicator_mul_of_pow4`: integrability on the alive set from a.e. bounds and from
  finite fourth moments;
* **`genStep`**: at a generic cell, `‖∫ 1_{A_j} ψ Dh_j‖ₑ ≤ ‖φ‖ C_a (Σ_c e¹_j(c) + Σ e²_j(c, c'))
  + ∫⁻ 1_{A_j} ‖φ‖ (C (η³ + η⁴) + W⁻² C_Γ + W⁻¹ ε)`, with `e¹, e²` the summands of
  `b3SummedErr` (via `stepCE` and `genStep_pt`; the coefficients are truncated to the box).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2 BlockBand.SourceProcess.PhysApprox.B3.Modul
open scoped NNReal ENNReal

variable {K np : ℕ}

theorem mem_kBox_iff {B : ℝ} (hB : 0 ≤ B) (z : ZSt K np) : z ∈ kBox B ↔ ‖eZ z‖ ≤ B := by
  refine ⟨norm_eZ_le hB, fun h => ?_⟩
  rw [Prod.norm_def, Prod.norm_def] at h
  exact ⟨(pi_norm_le_iff_of_nonneg hB).1 ((le_max_left _ _).trans h),
    (pi_norm_le_iff_of_nonneg hB).1 ((le_max_left _ _).trans ((le_max_right _ _).trans h)),
    (pi_norm_le_iff_of_nonneg hB).1 ((le_max_right _ _).trans ((le_max_right _ _).trans h))⟩

theorem continuous_eZ : Continuous (eZ (K := K) (np := np)) :=
  (continuous_pi fun c => (ClosedLimit.continuous_gramEntry c).comp continuous_fst).prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      (continuous_pi fun c => (ClosedLimit.continuous_gramEntry c).comp
        (continuous_snd.comp continuous_snd)))

theorem measurableSet_kBox_preimage {Ω : Type*} {m : MeasurableSpace Ω} {B : ℝ} (hB : 0 ≤ B)
    {zH : Ω → ZSt K np} (hz : StronglyMeasurable[m] zH) :
    MeasurableSet[m] {y | zH y ∈ kBox B} := by
  have e : {y | zH y ∈ kBox B} = {y | ‖eZ (zH y)‖ ≤ B} := by
    ext y; exact mem_kBox_iff hB _
  rw [e]
  exact measurableSet_le ((continuous_norm.comp continuous_eZ).comp_stronglyMeasurable
    hz).measurable measurable_const

section Integrable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {A A' : Set Ω}

theorem integrable_indicator_of_bound (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A')
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (hC : ∀ᵐ y ∂μ, y ∈ A → ‖f y‖ ≤ C) :
    Integrable (A.indicator f) μ := by
  have hae : A.indicator f =ᵐ[μ] A'.indicator f := indicator_ae_eq_of_ae_eq_set hAA
  refine Integrable.of_bound ((hf.indicator hA').congr hae.symm) (max C 0) ?_
  filter_upwards [hC] with y hy
  by_cases h : y ∈ A
  · rw [Set.indicator_of_mem h]; exact (hy h).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem h, norm_zero]; exact le_max_right _ _

theorem integrable_indicator_of_dom (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A')
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ) {G : Ω → ℝ≥0∞}
    (hG : ∀ y ∈ A, ‖f y‖ₑ ≤ 1 + G y) (hGi : ∫⁻ y, A.indicator G y ∂μ < ⊤) :
    Integrable (A.indicator f) μ := by
  have hae : A.indicator f =ᵐ[μ] A'.indicator f := indicator_ae_eq_of_ae_eq_set hAA
  refine ⟨(hf.indicator hA').congr hae.symm, ?_⟩
  unfold HasFiniteIntegral
  have hpt : ∀ y, ‖A.indicator f y‖ₑ ≤ 1 + A.indicator G y := fun y => by
    by_cases h : y ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact hG y h
    · rw [Set.indicator_of_notMem h, enorm_zero]; exact zero_le
  calc ∫⁻ y, ‖A.indicator f y‖ₑ ∂μ ≤ ∫⁻ y, (1 + A.indicator G y) ∂μ := lintegral_mono hpt
    _ = μ univ + ∫⁻ y, A.indicator G y ∂μ := by
        rw [lintegral_add_left measurable_const, lintegral_const, one_mul]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨measure_lt_top μ univ, hGi⟩

theorem enorm_le_one_add_pow4 (w : ℂ) : ‖w‖ₑ ≤ 1 + ‖w‖ₑ ^ 4 := by
  rcases le_total ‖w‖ₑ 1 with h1 | h1
  · exact h1.trans le_self_add
  · refine le_trans ?_ le_add_self
    calc ‖w‖ₑ = ‖w‖ₑ ^ 1 := (pow_one _).symm
      _ ≤ ‖w‖ₑ ^ 4 := pow_le_pow_right₀ h1 (by norm_num)

theorem enorm_mul_le_pow4 (w w' : ℂ) : ‖w * w'‖ₑ ≤ 1 + (‖w‖ₑ ^ 4 + ‖w'‖ₑ ^ 4) := by
  have hx := norm_nonneg w
  have hy := norm_nonneg w'
  have hr : ‖w‖ * ‖w'‖ ≤ 1 + (‖w‖ ^ 4 + ‖w'‖ ^ 4) := by
    nlinarith [sq_nonneg (‖w‖ - ‖w'‖), sq_nonneg (‖w‖ ^ 2 - 1), sq_nonneg (‖w'‖ ^ 2 - 1)]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, norm_mul,
    ← ENNReal.ofReal_pow hx, ← ENNReal.ofReal_pow hy, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (pow_nonneg hx 4) (pow_nonneg hy 4),
    ← ENNReal.ofReal_add zero_le_one (by positivity)]
  exact ENNReal.ofReal_le_ofReal hr

theorem integrable_indicator_of_pow4 (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A')
    {f : Ω → ℂ} (hf : AEStronglyMeasurable f μ)
    (h4 : ∫⁻ y, A.indicator (fun y => ‖f y‖ₑ ^ 4) y ∂μ < ⊤) : Integrable (A.indicator f) μ :=
  integrable_indicator_of_dom hA' hAA hf (fun y _ => enorm_le_one_add_pow4 (f y)) h4

theorem integrable_indicator_mul_of_pow4 (hA' : MeasurableSet A') (hAA : A =ᵐ[μ] A')
    {f g : Ω → ℂ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hf4 : ∫⁻ y, A.indicator (fun y => ‖f y‖ₑ ^ 4) y ∂μ < ⊤)
    (hg4 : ∫⁻ y, A.indicator (fun y => ‖g y‖ₑ ^ 4) y ∂μ < ⊤) :
    Integrable (A.indicator fun y => f y * g y) μ := by
  refine integrable_indicator_of_dom hA' hAA (hf.mul hg)
    (G := fun y => ‖f y‖ₑ ^ 4 + ‖g y‖ₑ ^ 4) (fun y _ => enorm_mul_le_pow4 _ _) ?_
  have e : A.indicator (fun y => ‖f y‖ₑ ^ 4 + ‖g y‖ₑ ^ 4) =
      fun y => A.indicator (fun y => ‖f y‖ₑ ^ 4) y + A.indicator (fun y => ‖g y‖ₑ ^ 4) y := by
    funext y; by_cases h : y ∈ A <;> simp [h]
  have hm : AEMeasurable (A.indicator fun y => ‖f y‖ₑ ^ 4) μ :=
    ((hf.enorm.pow_const 4).indicator hA').congr (indicator_ae_eq_of_ae_eq_set hAA).symm
  rw [e, lintegral_add_left' hm]
  exact ENNReal.add_lt_top.2 ⟨hf4, hg4⟩

end Integrable

/-!
## The generic step
-/

section Generic

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} {a t : ℝ≥0} {R : ℝ}
  {r : ℕ} {i : Fin r → LIdx K np} {u : Fin r → ℝ≥0}
  {φ : BoundedContinuousFunction (Fin r → ℂ) ℝ}

theorem measurable_b3dX {j : ℕ} (hV : Measurable V) (c : CIdx K np) :
    Measurable (b3dX b E s h τ m W j V c) :=
  (measurable_b3X s h τ m hV c).sub (measurable_b3X s h τ m hV c)

/-- **The generic step under the closed law.** -/
theorem genStep (hCE : CondExpReplace) (td : TaylorData χ b E F Λ) (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) (hs : 0 ≤ s) (hτ : ∀ i, s < τ i) (hW : 1 ≤ W)
    (hVg : Measurable[growthSigma W (closeLen s W)] V) (hχ : Continuous χ) (hΛ : Continuous Λ)
    (hu : ∀ l, u l ≤ a) {j : ℕ} (hpj : limLenAll s W a < j) (hjq : j + 1 ≤ limLenAll s W t)
    (hnb : ¬ IsBirthStep τ W j)
    (hfe : ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W →
      FeasPath b E s h τ m W V y)
    {CJ BA CA Ca CΓ Crest Cβ ε : ℝ} (hR0 : 0 ≤ R) (hCJ0 : 0 ≤ CJ) (hBA0 : 0 ≤ BA)
    (hCa0 : 0 ≤ Ca)
    (hCJ : ∀ J ∈ jSet (K := K) b m, ∀ e, ‖gramEntry e J‖ ≤ CJ)
    (hBA : ∀ y, FeasPath b E s h τ m W V y → ∀ e,
      ‖genA χ b E s τ m (pG b E s h τ m W V) e (cellT s W a t j) y‖ ≤ BA)
    (hCA : ∀ e : GIdx K np, ∀ J ∈ jSet (K := K) b m, ∀ H : GSt K np,
      GramFeasible (srcSignature K (Fin np)) H → ‖lamA χ b E e (J, H - J)‖ ≤ CA)
    (hC : ∀ (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ),
      0 ≤ ℓ → (∀ e, ‖z.2.1 e‖ ≤ max (2 * (2 * R + CJ) + BA) CA) →
      (∀ e, ‖lamA χ b E e (J, z.1)‖ ≤ max (2 * (2 * R + CJ) + BA) CA) →
      ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ) →
      ‖F (nextZ χ b E J y' ℓ z) - F z - (td.a0 (J, z, ℓ) + ip1 (td.a1 (J, z, ℓ)) (dlt z.1 y') +
          ip2 (td.a2 (J, z, ℓ)) (sq2 (dlt z.1 y')))‖ ≤
        Crest * ((∑ c, ‖dlt z.1 y' c‖ + ℓ * max (2 * (2 * R + CJ) + BA) CA) ^ 3 +
          (∑ c, ‖dlt z.1 y' c‖ + ℓ * max (2 * (2 * R + CJ) + BA) CA) ^ 4))
    (hCa1 : ∀ c, ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ∀ ℓ ∈ Icc (0 : ℝ) 1, ‖td.a1 (J, z, ℓ) c‖ ≤ Ca)
    (hCa2 : ∀ c c', ∀ J ∈ jSet (K := K) b m,
      ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ∀ ℓ ∈ Icc (0 : ℝ) 1, ‖td.a2 (J, z, ℓ) c c'‖ ≤ Ca)
    (hCΓ : ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ‖td.Γ (J, z)‖ ≤ CΓ)
    (hUC : ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ∀ ξ : GIdx K np → ℂ, (∀ e, ‖ξ e‖ ≤ (W : ℝ)⁻¹ * max (2 * (2 * R + CJ) + BA) CA) →
        ‖Λ (J, (z.1, fun e => z.2.1 e - ξ e, z.2.2)) - Λ (J, z)‖ ≤ ε)
    (hCβ : ∀ G : GSt K np, GramFeasible (srcSignature K (Fin np)) G → trRe G < R →
      ∀ c c' : GIdx K np, ‖cDrift b E (Sum.inl c : CIdx K np) G‖ ≤ Cβ ∧
        ‖cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') G‖ ≤ Cβ)
    (h4 : ∀ c : GIdx K np, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
      (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np < ⊤)
    (hXi : Integrable ((b3Alive b E s h τ m R W j V).indicator
      (Dh χ b E s h τ m W V F Λ a t j)) (closedLaw b W np)) :
    ‖∫ y, (b3Alive b E s h τ m R W j V).indicator (fun y =>
        (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y) y
      ∂closedLaw b W np‖ₑ ≤
      ENNReal.ofReal (‖φ‖ * Ca) * ((∑ c : GIdx K np, ∫⁻ y,
          ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
            (closedLaw b W np)[(b3Alive b E s h τ m R W j V).indicator
              (b3dX b E s h τ m W j V (Sum.inl c)) | b3Sigma W j np] y -
            (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)) y‖ₑ
          ∂closedLaw b W np) +
        ∑ c : GIdx K np, ∑ c' : GIdx K np, ∫⁻ y,
          ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
            (closedLaw b W np)[(b3Alive b E s h τ m R W j V).indicator (fun y =>
              b3dX b E s h τ m W j V (Sum.inl c) y * b3dX b E s h τ m W j V (Sum.inl c') y) |
                b3Sigma W j np] y -
            (W : ℂ)⁻¹ * cCov b E (Sum.inl c) (Sum.inl c')
              (b3ClosedGramAt b E s h τ m W j V y)) y‖ₑ ∂closedLaw b W np) +
      ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator (fun y => ENNReal.ofReal (‖φ‖ *
        (Crest * ((∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ +
            (W : ℝ)⁻¹ * max (2 * (2 * R + CJ) + BA) CA) ^ 3 +
          (∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ +
            (W : ℝ)⁻¹ * max (2 * (2 * R + CJ) + BA) CA) ^ 4) +
          (W : ℝ)⁻¹ ^ 2 * CΓ + (W : ℝ)⁻¹ * ε))) y ∂closedLaw b W np := by
  set B₁ := 2 * (2 * R + CJ) + BA
  set B := max B₁ CA
  set J := b3JumpAt (K := K) b s τ m W j
  set w : ℝ := (W : ℝ)⁻¹
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hW)
  have hB₁ : 0 ≤ B₁ := by positivity
  have hV : Measurable V := hVg.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hcj : closeLen s W ≤ j := (closeLen_le_limLenAll (s := s) (W := W) a).trans hpj.le
  have hLj : limLenAll s W (cellT s W a t j) = j := limLenAll_cellT hs hW hpj.le (by omega)
  have hm := gen_sigma_le W j np
  have hA' := measurableSet_b3AliveM_past (b := b) (E := E) s h τ m R (i := j) hcj le_rfl hVg
  have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j V
  have hA'a : MeasurableSet (b3AliveM b E s h τ m R W j V) := hm _ hA'
  have hzH : StronglyMeasurable[b3Sigma W j np] (zHat χ b E s h τ m W V (cellT s W a t j)) :=
    sm_zHat_past hVg hχ hLj.le
  have hBx := measurableSet_kBox_preimage hB₁ hzH
  set Bx := {y | zHat χ b E s h τ m W V (cellT s W a t j) y ∈ kBox (K := K) (np := np) B₁}
  -- truncated coefficients
  set a1' : GIdx K np → ProbedPath W np × ℝ → ℂ := fun c => Bx.indicator fun y =>
    td.a1 (J, zHat χ b E s h τ m W V (cellT s W a t j) y, w) c
  set a2' : GIdx K np → GIdx K np → ProbedPath W np × ℝ → ℂ := fun c c' => Bx.indicator fun y =>
    td.a2 (J, zHat χ b E s h τ m W V (cellT s W a t j) y, w) c c'
  have hpair : StronglyMeasurable[b3Sigma W j np] fun y =>
      ((J, zHat χ b E s h τ m W V (cellT s W a t j) y, w) : GSt K np × ZSt K np × ℝ) :=
    stronglyMeasurable_const.prodMk (hzH.prodMk stronglyMeasurable_const)
  have ha1 : ∀ c, StronglyMeasurable[b3Sigma W j np] (a1' c) := fun c =>
    ((td.ca1 c).comp_stronglyMeasurable hpair).indicator hBx
  have ha2 : ∀ c c', StronglyMeasurable[b3Sigma W j np] (a2' c c') := fun c c' =>
    ((td.ca2 c c').comp_stronglyMeasurable hpair).indicator hBx
  have ha1b : ∀ c y, ‖a1' c y‖ ≤ Ca := fun c y => by
    by_cases hy : y ∈ Bx
    · simp only [a1', Set.indicator_of_mem hy]
      exact hCa1 c J (b3JumpAt_mem_jSet b s τ m W j) _ hy w ⟨hw0, hw1⟩
    · simp only [a1', Set.indicator_of_notMem hy, norm_zero]; exact hCa0
  have ha2b : ∀ c c' y, ‖a2' c c' y‖ ≤ Ca := fun c c' y => by
    by_cases hy : y ∈ Bx
    · simp only [a2', Set.indicator_of_mem hy]
      exact hCa2 c c' J (b3JumpAt_mem_jSet b s τ m W j) _ hy w ⟨hw0, hw1⟩
    · simp only [a2', Set.indicator_of_notMem hy, norm_zero]; exact hCa0
  -- the test
  have hψ : StronglyMeasurable[b3Sigma W j np] (pTest b E s h τ m W V i u φ) := by
    have h1 := measurable_pTest_past (b := b) (E := E) (h := h) (τ := τ) (m := m) hVg (j := j) i u
      (fun l =>
      (Nat.floor_mono (mul_le_mul_of_nonneg_left (by
        have : (u l : ℝ) ≤ a := hu l
        linarith) (Nat.cast_nonneg W))).trans hpj.le) φ
    let _ : MeasurableSpace (ProbedPath W np × ℝ) := b3Sigma W j np
    exact h1.stronglyMeasurable
  -- the increments and their targets
  have hδm : ∀ c : GIdx K np, AEStronglyMeasurable (b3dX b E s h τ m W j V (Sum.inl c))
      (closedLaw b W np) := fun c => (measurable_b3dX hV _).aestronglyMeasurable
  have hG : StronglyMeasurable[b3Sigma W j np] fun y => b3ClosedGramAt b E s h τ m W j V y :=
    sm_gram_past hVg hcj le_rfl
  have hcD : ∀ c : GIdx K np, Continuous fun G : GSt K np => cDrift b E (Sum.inl c : CIdx K np) G :=
    fun c => ClosedLimit.continuous_gramDriftEntry _ _ c
  have hcC : ∀ c c' : GIdx K np, Continuous fun G : GSt K np =>
      cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') G :=
    fun c c' => ClosedLimit.continuous_gramCovEntry _ _ c c'
  have hβ1s : ∀ c : GIdx K np, StronglyMeasurable[b3Sigma W j np] fun y =>
      (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y) := fun c =>
    stronglyMeasurable_const.mul ((hcD c).comp_stronglyMeasurable hG)
  have hβ2s : ∀ c c' : GIdx K np, StronglyMeasurable[b3Sigma W j np] fun y =>
      (W : ℂ)⁻¹ * cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y) :=
    fun c c' => stronglyMeasurable_const.mul ((hcC c c').comp_stronglyMeasurable hG)
  have hbnd : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j V →
      ∀ c c' : GIdx K np,
        ‖(W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)‖ ≤ w * Cβ ∧
        ‖(W : ℂ)⁻¹ * cCov b E (Sum.inl c) (Sum.inl c')
          (b3ClosedGramAt b E s h τ m W j V y)‖ ≤ w * Cβ := by
    filter_upwards [hfe] with y hy hA c c'
    have hb := hCβ _ (hy hA.1 j hcj) (hA.2 j hcj le_rfl) c c'
    have hn : ‖(W : ℂ)⁻¹‖ = w := by simp [w]
    rw [norm_mul, norm_mul, hn]
    exact ⟨mul_le_mul_of_nonneg_left hb.1 hw0, mul_le_mul_of_nonneg_left hb.2 hw0⟩
  have hβ1 : ∀ c : GIdx K np, Integrable ((b3Alive b E s h τ m R W j V).indicator fun y =>
      (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y))
      (closedLaw b W np) := fun c =>
    integrable_indicator_of_bound hA'a hAA ((hβ1s c).mono hm).aestronglyMeasurable
      (by filter_upwards [hbnd] with y hy hA using (hy hA c c).1)
  have hβ2 : ∀ c c' : GIdx K np, Integrable ((b3Alive b E s h τ m R W j V).indicator fun y =>
      (W : ℂ)⁻¹ * cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y))
      (closedLaw b W np) := fun c c' =>
    integrable_indicator_of_bound hA'a hAA ((hβ2s c c').mono hm).aestronglyMeasurable
      (by filter_upwards [hbnd] with y hy hA using (hy hA c c').2)
  -- the pointwise bound
  have hRt : ∀ᵐ y ∂closedLaw b W np, y ∈ b3Alive b E s h τ m R W j V →
      ‖Dh χ b E s h τ m W V F Λ a t j y - (∑ c, a1' c y *
          (b3dX b E s h τ m W j V (Sum.inl c) y -
            (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)) +
        ∑ c, ∑ c', a2' c c' y * (b3dX b E s h τ m W j V (Sum.inl c) y *
          b3dX b E s h τ m W j V (Sum.inl c') y - (W : ℂ)⁻¹ *
            cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y)))‖ ≤
        Crest * ((∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ + w * B) ^ 3 +
          (∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ + w * B) ^ 4) +
          w ^ 2 * CΓ + w * ε := by
    filter_upwards [hfe] with y hy hA
    have hfy := hy hA.1
    have hz : zHat χ b E s h τ m W V (cellT s W a t j) y ∈ kBox (K := K) (np := np) B₁ :=
      zHat_mem_kBox hR0 hCJ0 hBA0 hCJ hfy hA hLj.le (hBA y hfy)
    have hzB : y ∈ Bx := hz
    simp only [a1', a2', Set.indicator_of_mem hzB]
    have key := genStep_pt td hV hχ hΛ hs hτ hW hpj hjq hnb y (B := B) (C := Crest) (ε := ε)
      hC (fun e => (hz.2.1 e).trans (le_max_left _ _))
      (fun e => (hCA e J (b3JumpAt_mem_jSet b s τ m W j) _ (hfy j hcj)).trans
        (le_max_right _ _))
      (hUC J (b3JumpAt_mem_jSet b s τ m W j) _ hz)
    refine key.trans (add_le_add (add_le_add le_rfl ?_) le_rfl)
    have hn : ‖((((W : ℕ) : ℝ) : ℂ))⁻¹‖ = w := by simp [w]
    rw [norm_mul, norm_pow, hn]
    exact mul_le_mul_of_nonneg_left (hCΓ J (b3JumpAt_mem_jSet b s τ m W j) _ hz) (by positivity)
  exact stepCE hCE hm hA' hAA (fun c => b3dX b E s h τ m W j V (Sum.inl c))
    (fun c y => (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y))
    (fun c c' y => (W : ℂ)⁻¹ * cCov b E (Sum.inl c) (Sum.inl c')
      (b3ClosedGramAt b E s h τ m W j V y)) a1' a2' ha1 ha2 ha1b ha2b
    (pTest b E s h τ m W V i u φ) hψ (fun y => φ.norm_coe_le_norm _)
    (fun c => integrable_indicator_of_pow4 hA'a hAA (hδm c) (h4 c))
    (fun c c' => integrable_indicator_mul_of_pow4 hA'a hAA (hδm c) (hδm c') (h4 c) (h4 c'))
    hβ1 hβ2 (fun c => (hβ1s c).aestronglyMeasurable) (fun c c' => (hβ2s c c').aestronglyMeasurable)
    _ hXi _ hRt

end Generic

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
