module

public import BlockBand.SourceProcess.ModelExist.BirthSort

/-!
# Measurability of the sorted birth vectors

With `𝓖₀`-measurable birth times, a measurable selection and a progressive `𝒢`:
* the sorting permutation and the sorted times are `𝓖₀`-measurable;
* the `l`-th birth vector `b_l = bV … l` is `𝓕_{T_l}`-measurable (`measurable_bV`, by induction along
  the sorted order, `T` nondecreasing);
* the vector of probe `m` is `𝓕_{θ_m}`-measurable (`measurable_probeV`): on the
  `𝓖₀`-event `{srt = π}` the time `T_{π⁻¹ m}` is `θ_m`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.ModelExist
open MeasureTheory Filter Set
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- `𝓖₀`-events are `𝓕_τ`-events. -/
theorem measurableSet_of_zero {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ) {A : Set Ω}
    (hA : MeasurableSet[𝓖 0] A) : MeasurableSet[hτ.measurableSpace] A :=
  ⟨le_iSup (fun t => 𝓖 t) 0 _ hA, fun i => (𝓖.mono zero_le _ hA).inter (hτ i)⟩

/-- On a `𝓖₀`-event where `τ = τ'`, `𝓕_{τ'}`-events are `𝓕_τ`-events. -/
theorem measurableSet_inter_of_eqOn {τ τ' : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hτ' : IsStoppingTime 𝓖 τ') {E : Set Ω} (hE : MeasurableSet[𝓖 0] E)
    (heq : ∀ ω ∈ E, τ ω = τ' ω) {S : Set Ω} (hS : MeasurableSet[hτ'.measurableSpace] S) :
    MeasurableSet[hτ.measurableSpace] (E ∩ S) := by
  refine ⟨(le_iSup (fun t => 𝓖 t) 0 _ hE).inter hS.1, fun i => ?_⟩
  have e : E ∩ S ∩ {ω | τ ω ≤ i} = E ∩ (S ∩ {ω | τ' ω ≤ i}) := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, heq ω h1 ▸ h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, (heq ω h1).symm ▸ h3⟩
  rw [e]
  exact (𝓖.mono zero_le _ hE).inter (hS.2 i)

theorem measurable_ite_of_eqOn {β : Type*} [MeasurableSpace β] {τ τ' : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) (hτ' : IsStoppingTime 𝓖 τ') {E : Set Ω} [DecidablePred (· ∈ E)]
    (hE : MeasurableSet[𝓖 0] E) (heq : ∀ ω ∈ E, τ ω = τ' ω) {g : Ω → β}
    (hg : Measurable[hτ'.measurableSpace] g) (b : β) :
    Measurable[hτ.measurableSpace] (fun ω => if ω ∈ E then g ω else b) := by
  intro A hA
  have e : (fun ω => if ω ∈ E then g ω else b) ⁻¹' A =
      (E ∩ g ⁻¹' A) ∪ (Eᶜ ∩ {_ω | b ∈ A}) := by
    ext ω
    by_cases h : ω ∈ E <;> simp [h]
  rw [e]
  exact (measurableSet_inter_of_eqOn hτ hτ' hE heq (hg hA)).union
    ((measurableSet_of_zero hτ hE).compl.inter (MeasurableSet.const _))

variable {c' : Type*} [Fintype c'] {n : ℕ} {θf : Fin n → Ω → ℝ≥0}

theorem measurableSet_srt_eq (hθ : ∀ m, Measurable[𝓖 0] (θf m)) (π0 : Equiv.Perm (Fin n)) :
    MeasurableSet[𝓖 0] {ω | srt θf ω = π0} := by
  have e : {ω | srt θf ω = π0} = (⋂ i, ⋂ j, {ω | i ≤ j → θf (π0 i) ω ≤ θf (π0 j) ω}) ∩
      ⋂ i, ⋂ j, {ω | i < j → θf (π0 i) ω = θf (π0 j) ω → π0 i < π0 j} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, srt]
    rw [eq_comm, Tuple.eq_sort_iff, Monotone]
    rfl
  rw [e]
  refine (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => ?_)
  · by_cases hij : i ≤ j
    · simpa [hij] using measurableSet_le (hθ (π0 i)) (hθ (π0 j))
    · simp [hij]
  · by_cases hij : i < j
    · by_cases hp : π0 i < π0 j
      · simp [hij, hp]
      · have h := (measurableSet_eq_fun (hθ (π0 i)) (hθ (π0 j))).compl
        simp only [hij, hp, true_implies, imp_false]
        exact h
    · simp [hij]

theorem measurable_sT (hθ : ∀ m, Measurable[𝓖 0] (θf m)) (l : Fin n) :
    Measurable[𝓖 0] (sT θf l) := by
  have e : sT θf l = fun ω => ∑ π0 : Equiv.Perm (Fin n),
      if srt θf ω = π0 then θf (π0 l) ω else 0 := by
    funext ω
    rw [Finset.sum_ite_eq]
    simp [sT]
  rw [e]
  exact Finset.measurable_fun_sum _ fun π0 _ =>
    Measurable.ite (measurableSet_srt_eq hθ π0) (hθ (π0 l)) measurable_const

theorem measurable_mono_zero {β : Type*} [MeasurableSpace β] {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {g : Ω → β} (hg : Measurable[𝓖 0] g) :
    Measurable[hτ.measurableSpace] g := fun _ hA => measurableSet_of_zero hτ (hg hA)

theorem measurable_vf_srt (hθ : ∀ m, Measurable[𝓖 0] (θf m)) (vf : Fin n → ℝ) (l : Fin n) :
    Measurable[𝓖 0] (fun ω => vf (srt θf ω l)) := by
  have e : (fun ω => vf (srt θf ω l)) = fun ω => ∑ π0 : Equiv.Perm (Fin n),
      if srt θf ω = π0 then vf (π0 l) else 0 := by
    funext ω
    rw [Finset.sum_ite_eq]
    simp
  rw [e]
  exact Finset.measurable_fun_sum _ fun π0 _ =>
    Measurable.ite (measurableSet_srt_eq hθ π0) measurable_const measurable_const

variable (sel : (Matrix c' c' ℂ × Matrix c' c' ℂ) × (Fin n → c' → ℂ) × ℝ → c' → ℂ)
  (𝒢 : ℝ≥0 → Ω → Matrix c' c' ℂ × Matrix c' c' ℂ) (vf : Fin n → ℝ)

omit [MeasurableSpace Ω] [Fintype c'] in
theorem measurable_update {m : MeasurableSpace Ω} {s : Ω → Fin n → c' → ℂ} {x : Ω → c' → ℂ}
    (hs : Measurable[m] s) (hx : Measurable[m] x) (i : Fin n) :
    Measurable[m] (fun ω => Function.update (s ω) i (x ω)) := by
  let _ := m
  refine Measurable.of_eval fun j => ?_
  by_cases h : j = i
  · subst h; simpa using hx
  · simp only [Function.update_of_ne h]
    exact (measurable_pi_apply j).comp hs

theorem measurable_stateV (hθ : ∀ m, Measurable[𝓖 0] (θf m)) (hsel : Measurable sel)
    (h𝒢 : IsStronglyProgressive 𝓖 𝒢) :
    ∀ m : ℕ, ∀ l : Fin n, m ≤ l.val + 1 →
      Measurable[(isStoppingTime_of_meas0 (measurable_sT hθ l)).measurableSpace]
        (stateV sel 𝒢 θf vf m)
  | 0, l, _ => measurable_const
  | m + 1, l, hm => by
    have ih := measurable_stateV hθ hsel h𝒢 m l (by omega)
    have : TopologicalSpace.PseudoMetrizableSpace (Matrix c' c' ℂ) :=
      inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (c' → c' → ℂ))
    have : SecondCountableTopology (Matrix c' c' ℂ) :=
      inferInstanceAs (SecondCountableTopology (c' → c' → ℂ))
    have : BorelSpace (Matrix c' c' ℂ × Matrix c' c' ℂ) := Prod.borelSpace
    rw [stateV]
    by_cases h : m < n
    · simp only [dite_eq_left h]
      have hT := isStoppingTime_of_meas0 (measurable_sT hθ ⟨m, h⟩)
      have hle : (isStoppingTime_of_meas0 (measurable_sT hθ ⟨m, h⟩)).measurableSpace ≤
          (isStoppingTime_of_meas0 (measurable_sT hθ l)).measurableSpace :=
        IsStoppingTime.measurableSpace_mono _ _ fun ω =>
          WithTop.coe_le_coe.2 (sT_mono θf ω (show (⟨m, h⟩ : Fin n) ≤ l from
            Fin.le_iff_val_le_val.2 (Nat.le_of_succ_le_succ hm)))
      have hG : Measurable[(isStoppingTime_of_meas0 (measurable_sT hθ ⟨m, h⟩)).measurableSpace]
          (fun ω => 𝒢 (sT θf ⟨m, h⟩ ω) ω) :=
        measurable_stoppedValue h𝒢 hT
      have hv := measurable_mono_zero (isStoppingTime_of_meas0 (measurable_sT hθ l))
        (measurable_vf_srt hθ vf ⟨m, h⟩)
      exact measurable_update ih (hsel.comp ((hG.mono hle le_rfl).prodMk (ih.prodMk hv)))
        ⟨m, h⟩
    · simpa only [dite_eq_right h] using ih

theorem measurable_bV (hθ : ∀ m, Measurable[𝓖 0] (θf m)) (hsel : Measurable sel)
    (h𝒢 : IsStronglyProgressive 𝓖 𝒢) (l : Fin n) :
    Measurable[(isStoppingTime_of_meas0 (measurable_sT hθ l)).measurableSpace]
      (bV sel 𝒢 θf vf l) := by
  have e : bV sel 𝒢 θf vf l = fun ω => stateV sel 𝒢 θf vf (l.val + 1) ω l := by
    funext ω
    have h := stateV_stable sel 𝒢 θf vf ω l (n - (l.val + 1))
    rw [show l.val + 1 + (n - (l.val + 1)) = n by omega] at h
    rw [bV, h]
  rw [e]
  exact (measurable_pi_apply l).comp (measurable_stateV sel 𝒢 vf hθ hsel h𝒢 (l.val + 1) l le_rfl)

/-- **The vector of probe `m` is `𝓕_{θ_m}`-measurable.** -/
theorem measurable_probeV (hθ : ∀ m, Measurable[𝓖 0] (θf m)) (hsel : Measurable sel)
    (h𝒢 : IsStronglyProgressive 𝓖 𝒢) (m : Fin n) :
    Measurable[(isStoppingTime_of_meas0 (hθ m)).measurableSpace] (probeV sel 𝒢 θf vf m) := by
  classical
  have e : probeV sel 𝒢 θf vf m = fun ω => ∑ π0 : Equiv.Perm (Fin n),
      if ω ∈ {ω | srt θf ω = π0} then bV sel 𝒢 θf vf (π0.symm m) ω else 0 := by
    funext ω
    simp only [mem_ofPred_eq]
    rw [Finset.sum_ite_eq]
    simp [probeV]
  rw [e]
  refine Finset.measurable_fun_sum _ fun π0 _ => measurable_ite_of_eqOn _
    (isStoppingTime_of_meas0 (measurable_sT hθ (π0.symm m))) (measurableSet_srt_eq hθ π0)
    (fun ω hω => ?_) (measurable_bV sel 𝒢 vf hθ hsel h𝒢 _) 0
  simp only [mem_ofPred_eq] at hω
  simp only [sT, hω, Equiv.apply_symm_apply]

end BlockBand.SourceProcess.ModelExist
