module

public import BlockBand.Endpoints.Response.NearSchattenStoppedBounds

/-!
# Stopped telescoping of a summed one-step error bound

**Proved here** (abstract; no model input).
* `nssStopIdx j₂ σ = min(j₂, σ)` (as a natural number) and the telescoping identity
  `nss_sum_telescope`: on `{σ > j₁}`, `Σ_{j₁≤j<j₂} 1{j<σ}(f_{j+1} - f_j) = f_{j₂∧σ} - f_{j₁}`.
  The case `σ ≤ j₁` contributes nothing, so the uncontrolled exit at the start of the stop never
  enters.
* `nss_stopped_step`: `|E[1_A X] - E[1_A G]| ≤ E|1_A(E[1_A X | 𝓕] - G)|` for `A ∈ 𝓕`.
* `nss_telescope_bound`: a summed bound `Σ_j E|1_{A_j}(E_j[1_{A_j}ΔF_j] - G_j)| ≤ e` (the shape of
  `ContractingWordsContract.summed`) gives
  `E[1{σ>j₁}(Re F_{j₂∧σ} - Re F_{j₁})] - e ≤ Σ_{j₁≤j<j₂} E[1_{A_j} Re G_j]`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set Finset
open scoped ENNReal

/-- The stopped index `min(j₂, σ)` as a natural number. -/
def nssStopIdx (j₂ : ℕ) (σ : ℕ∞) : ℕ := (min (j₂ : ℕ∞) σ).toNat

theorem nss_stopIdx_cases (j₂ : ℕ) (σ : ℕ∞) :
    ((j₂ : ℕ∞) ≤ σ ∧ nssStopIdx j₂ σ = j₂) ∨
      (σ = (nssStopIdx j₂ σ : ℕ∞) ∧ nssStopIdx j₂ σ < j₂) := by
  unfold nssStopIdx
  rcases le_or_gt (j₂ : ℕ∞) σ with h | h
  · left; rw [min_eq_left h, ENat.toNat_natCast]; exact ⟨h, rfl⟩
  · right
    rw [min_eq_right h.le]
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt h)
    rw [ENat.toNat_natCast]
    exact ⟨rfl, by exact_mod_cast h⟩

theorem nss_stopIdx_le (j₂ : ℕ) (σ : ℕ∞) : nssStopIdx j₂ σ ≤ j₂ := by
  rcases nss_stopIdx_cases j₂ σ with ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem nss_le_stopIdx {j₁ j₂ : ℕ} {σ : ℕ∞} (h12 : j₁ ≤ j₂) (h1 : (j₁ : ℕ∞) < σ) :
    j₁ ≤ nssStopIdx j₂ σ := by
  rcases nss_stopIdx_cases j₂ σ with ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · rw [h] at h1; exact_mod_cast h1.le

theorem nss_lt_iff_lt_stopIdx {j j₂ : ℕ} {σ : ℕ∞} (hj : j < j₂) :
    (j : ℕ∞) < σ ↔ j < nssStopIdx j₂ σ := by
  rcases nss_stopIdx_cases j₂ σ with ⟨h, h'⟩ | ⟨h, -⟩
  · rw [h']
    exact ⟨fun _ => hj, fun _ => lt_of_lt_of_le (by exact_mod_cast hj) h⟩
  · conv_lhs => rw [h]
    exact_mod_cast Iff.rfl

theorem nss_sum_Ico_sub {G : Type*} [AddCommGroup G] (f : ℕ → G) {a c : ℕ} (h : a ≤ c) :
    ∑ j ∈ Finset.Ico a c, (f (j + 1) - f j) = f c - f a := by
  have e := Finset.sum_range_sub (fun k => f (a + k)) (c - a)
  simp only [← add_assoc, add_zero, Nat.add_sub_cancel' h] at e
  rw [Finset.sum_Ico_eq_sum_range, e]

/-- **Stopped telescoping**: on `{σ > j₁}`, `Σ_{j₁≤j<j₂} 1{j<σ}(f_{j+1} - f_j) = f_{j₂∧σ} - f_{j₁}`. -/
theorem nss_sum_telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) {j₁ j₂ : ℕ} {σ : ℕ∞}
    (h12 : j₁ ≤ j₂) (h1 : (j₁ : ℕ∞) < σ) :
    ∑ j ∈ Finset.Ico j₁ j₂, (if (j : ℕ∞) < σ then f (j + 1) - f j else 0) =
      f (nssStopIdx j₂ σ) - f j₁ := by
  have hs1 := nss_le_stopIdx h12 h1
  have hs2 := nss_stopIdx_le j₂ σ
  rw [← nss_sum_Ico_sub f hs1, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha, (nss_lt_iff_lt_stopIdx hb).1 hc⟩
  · rintro ⟨ha, hb⟩
    have hj : j < j₂ := lt_of_lt_of_le hb hs2
    exact ⟨⟨ha, hj⟩, (nss_lt_iff_lt_stopIdx hj).2 hb⟩

/-- Off `{σ > j₁}` the stopped increments vanish. -/
theorem nss_sum_telescope_dead {G : Type*} [AddCommGroup G] (f : ℕ → G) {j₁ j₂ : ℕ} {σ : ℕ∞}
    (h1 : ¬ (j₁ : ℕ∞) < σ) :
    ∑ j ∈ Finset.Ico j₁ j₂, (if (j : ℕ∞) < σ then f (j + 1) - f j else 0) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  have : ¬ (j : ℕ∞) < σ := fun h => h1 (lt_of_le_of_lt (by exact_mod_cast
    (Finset.mem_Ico.1 hj).1) h)
  simp [this]

theorem nss_re_indicator {Ω : Type*} (A : Set Ω) (f : Ω → ℂ) (ω : Ω) :
    (A.indicator f ω).re = A.indicator (fun ω => (f ω).re) ω := by
  by_cases h : ω ∈ A
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- **One stopped step** (tower property and pull-out on `A ∈ 𝓕`). -/
theorem nss_stopped_step {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) {μ : Measure[mΩ] Ω} [IsFiniteMeasure μ] {A : Set Ω} (hAm : MeasurableSet[m] A)
    {X G : Ω → ℂ} (hX : Integrable X μ) (hG : Integrable (A.indicator G) μ) :
    ‖∫ ω, A.indicator X ω ∂μ - ∫ ω, A.indicator G ω ∂μ‖ₑ ≤
      ∫⁻ ω, ‖A.indicator (fun ω => μ[A.indicator X | m] ω - G ω) ω‖ₑ ∂μ := by
  have hA : MeasurableSet[mΩ] A := hm _ hAm
  set cond := μ[A.indicator X | m]
  have hcond : ∫ ω, A.indicator cond ω ∂μ = ∫ ω, A.indicator X ω ∂μ := by
    have e1 : A.indicator cond =ᵐ[μ] μ[A.indicator (A.indicator X) | m] :=
      (condExp_indicator (hX.indicator hA) hAm).symm
    rw [integral_congr_ae e1, integral_condExp hm, Set.indicator_indicator, Set.inter_self]
  have icond : Integrable (A.indicator cond) μ := integrable_condExp.indicator hA
  rw [← hcond, ← integral_sub icond hG]
  refine (enorm_integral_le_lintegral_enorm _).trans_eq (lintegral_congr fun ω => ?_)
  by_cases h : ω ∈ A
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

/-- **Stopped telescoping of a summed one-step error bound.** -/
theorem nss_telescope_bound {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure[mΩ] Ω}
    [IsFiniteMeasure μ] (m : ℕ → MeasurableSpace Ω) (hm : ∀ j, m j ≤ mΩ) (σ : Ω → ℕ∞)
    (A : ℕ → Set Ω) (hAσ : ∀ j ω, ω ∈ A j ↔ (j : ℕ∞) < σ ω) (hAm : ∀ j, MeasurableSet[m j] (A j))
    {j₁ j₂ : ℕ} (h12 : j₁ ≤ j₂) (F G : ℕ → Ω → ℂ)
    (hF : ∀ j, j₁ ≤ j → j ≤ j₂ → Integrable (F j) μ)
    (hG : ∀ j ∈ Finset.Ico j₁ j₂, Integrable ((A j).indicator (G j)) μ) {e : ℝ} (he : 0 ≤ e)
    (hsum : ∑ j ∈ Finset.Ico j₁ j₂, ∫⁻ ω, ‖(A j).indicator (fun ω =>
        μ[(A j).indicator (fun ω => F (j + 1) ω - F j ω) | m j] ω - G j ω) ω‖ₑ ∂μ ≤
      ENNReal.ofReal e) :
    ∫ ω, (A j₁).indicator (fun ω => (F (nssStopIdx j₂ (σ ω)) ω).re - (F j₁ ω).re) ω ∂μ - e ≤
      ∑ j ∈ Finset.Ico j₁ j₂, ∫ ω, (A j).indicator (fun ω => (G j ω).re) ω ∂μ := by
  set X : ℕ → Ω → ℂ := fun j ω => F (j + 1) ω - F j ω
  have hX : ∀ j ∈ Finset.Ico j₁ j₂, Integrable (X j) μ := fun j hj => by
    have := Finset.mem_Ico.1 hj
    exact (hF (j + 1) (by omega) (by omega)).sub (hF j this.1 this.2.le)
  have hAX : ∀ j ∈ Finset.Ico j₁ j₂, Integrable ((A j).indicator (X j)) μ :=
    fun j hj => (hX j hj).indicator (hm j _ (hAm j))
  set Z : ℂ := ∑ j ∈ Finset.Ico j₁ j₂, (∫ ω, (A j).indicator (X j) ω ∂μ -
    ∫ ω, (A j).indicator (G j) ω ∂μ)
  have hZ : ‖Z‖ₑ ≤ ENNReal.ofReal e :=
    (enorm_sum_le _ _).trans ((Finset.sum_le_sum fun j hj =>
      nss_stopped_step (hm j) (hAm j) (hX j hj) (hG j hj)).trans hsum)
  have hZr : Z.re ≤ e := by
    have h1 : ‖Z‖ ≤ e := by
      rw [← ofReal_norm] at hZ
      exact (ENNReal.ofReal_le_ofReal_iff he).1 hZ
    exact (Complex.re_le_norm Z).trans h1
  have hre : Z.re = ∑ j ∈ Finset.Ico j₁ j₂, ∫ ω, (A j).indicator (fun ω => (X j ω).re) ω ∂μ -
      ∑ j ∈ Finset.Ico j₁ j₂, ∫ ω, (A j).indicator (fun ω => (G j ω).re) ω ∂μ := by
    simp only [Z, Complex.re_sum, Complex.sub_re, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      exact (integral_re (hAX j hj)).symm.trans
        (integral_congr_ae (Eventually.of_forall fun ω => nss_re_indicator _ _ ω))
    · refine Finset.sum_congr rfl fun j hj => ?_
      exact (integral_re (hG j hj)).symm.trans
        (integral_congr_ae (Eventually.of_forall fun ω => nss_re_indicator _ _ ω))
  have htel : ∑ j ∈ Finset.Ico j₁ j₂, ∫ ω, (A j).indicator (fun ω => (X j ω).re) ω ∂μ =
      ∫ ω, (A j₁).indicator (fun ω => (F (nssStopIdx j₂ (σ ω)) ω).re - (F j₁ ω).re) ω ∂μ := by
    rw [← integral_finsetSum _ fun j hj => (hAX j hj).re.congr
      (Eventually.of_forall fun ω => nss_re_indicator _ _ ω)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    have hind : ∀ j, (A j).indicator (fun ω => (X j ω).re) ω =
        if (j : ℕ∞) < σ ω then (F (j + 1) ω).re - (F j ω).re else 0 := fun j => by
      by_cases h : (j : ℕ∞) < σ ω
      · rw [Set.indicator_of_mem ((hAσ j ω).2 h), ite_eq_left h]; simp [X]
      · rw [Set.indicator_of_notMem (fun h' => h ((hAσ j ω).1 h')), ite_eq_right h]
    simp only [hind]
    by_cases h1 : (j₁ : ℕ∞) < σ ω
    · rw [Set.indicator_of_mem ((hAσ j₁ ω).2 h1)]
      exact nss_sum_telescope (fun j => (F j ω).re) h12 h1
    · rw [Set.indicator_of_notMem (fun h' => h1 ((hAσ j₁ ω).1 h'))]
      exact nss_sum_telescope_dead (fun j => (F j ω).re) h1
  linarith

/-- The stopped value `1{σ>j₁} F_{j₂∧σ}` is integrable when `F_{j₁}, …, F_{j₂}` are. -/
theorem nss_integrable_stopped {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure[mΩ] Ω}
    (σ : Ω → ℕ∞) (A : ℕ → Set Ω) (hAσ : ∀ j ω, ω ∈ A j ↔ (j : ℕ∞) < σ ω)
    (hA : ∀ j, MeasurableSet (A j)) {j₁ j₂ : ℕ} (h12 : j₁ ≤ j₂) (F : ℕ → Ω → ℂ)
    (hF : ∀ j, j₁ ≤ j → j ≤ j₂ → Integrable (F j) μ) :
    Integrable ((A j₁).indicator (fun ω => F (nssStopIdx j₂ (σ ω)) ω)) μ := by
  have hX : ∀ j ∈ Finset.Ico j₁ j₂,
      Integrable ((A j).indicator (fun ω => F (j + 1) ω - F j ω)) μ := fun j hj => by
    have := Finset.mem_Ico.1 hj
    exact ((hF (j + 1) (by omega) (by omega)).sub (hF j this.1 this.2.le)).indicator (hA j)
  refine (((hF j₁ le_rfl h12).indicator (hA j₁)).add (integrable_finsetSum _ hX)).congr
    (Eventually.of_forall fun ω => ?_)
  have hind : ∀ j, (A j).indicator (fun ω => F (j + 1) ω - F j ω) ω =
      if (j : ℕ∞) < σ ω then F (j + 1) ω - F j ω else 0 := fun j => by
    by_cases h : (j : ℕ∞) < σ ω
    · rw [Set.indicator_of_mem ((hAσ j ω).2 h), ite_eq_left h]
    · rw [Set.indicator_of_notMem (fun h' => h ((hAσ j ω).1 h')), ite_eq_right h]
  simp only [Pi.add_apply, hind]
  by_cases h1 : (j₁ : ℕ∞) < σ ω
  · rw [Set.indicator_of_mem ((hAσ j₁ ω).2 h1), Set.indicator_of_mem ((hAσ j₁ ω).2 h1),
      nss_sum_telescope (fun j => F j ω) h12 h1]
    abel
  · rw [Set.indicator_of_notMem (fun h' => h1 ((hAσ j₁ ω).1 h')),
      Set.indicator_of_notMem (fun h' => h1 ((hAσ j₁ ω).1 h')),
      nss_sum_telescope_dead (fun j => F j ω) h1, add_zero]

end BlockBand.Endpoints
