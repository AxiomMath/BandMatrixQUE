module

public import BlockBand.Density.Coupling

/-!
# Mean resolvent comparison on the coupled space

Law: `coupledLaw model model'` on `(H, K')` (ring law of any admissible `p` times an independent
short-ring law, `4 ≤ m < n`), `K = coupledShortMatrix (H, K')`, `z = e + iη`, `η > 0`. Only finitely
many Gaussian blocks enter the coupling difference; on the exceptional event the deterministic
bound `2/η` is used.

* `norm_couplingDefect_interior`, `norm_couplingDefect_le`: deterministic bounds on the coupling
  difference `V = couplingDefect`: off the end blocks `0, m-1` of the short ring, `V_{uv}` is
  `0` or an entry of `H` outside the band; on the end blocks it is bounded by entries of `H, K'`;
* `norm_integral_resolvent_sub_le`: if, for every end-block site `u`, `P(‖G^K_{x u}‖ > δ) ≤ β`,
  then `‖E G^H_{ιx,ιx} - E G^K_{xx}‖ ≤ η⁻¹ δ N_K N (2 + 2 N_K) + 2 η⁻¹ N_K β`
  (`N = nW`, `N_K = mW`);
* `norm_integral_resolvent_diag_sub_le`: if `P(‖G_{xx} - m‖ > t) ≤ β` and `‖m‖ ≤ 1`, then
  `‖E G_{xx} - m‖ ≤ t + (η⁻¹ + 1) β` under any physical law.
No further hypothesis: the event bounds are hypotheses of the statements, supplied by
`ShortRingLocalLaw` in `CouplingEstimate`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Density

open MeasureTheory

/-- `E f ≤ E g + M P(S)` from `f ≤ g + M 1_S` a.s. -/
theorem integral_le_add_indicator {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} {S : Set Ω} (hS : MeasurableSet S) (hf : Integrable f μ) (hg : Integrable g μ)
    [IsFiniteMeasure μ] (M : ℝ) (h : ∀ᵐ ω ∂μ, f ω ≤ g ω + S.indicator (fun _ => M) ω) :
    ∫ ω, f ω ∂μ ≤ ∫ ω, g ω ∂μ + μ.real S * M := by
  have hi : Integrable (S.indicator (fun _ : Ω => M)) μ := (integrable_const M).indicator hS
  refine (integral_mono_ae hf (hg.add hi) h).trans (le_of_eq ?_)
  rw [integral_add' hg hi, integral_indicator_const M hS, smul_eq_mul]

theorem card_site_eq (q : Parameters) : (Fintype.card q.Site : ℝ) = q.N := by
  simp [Parameters.N, Fintype.card_prod, ZMod.card]

section Defect

variable {p : Parameters} {m : ℕ} {hm : 4 ≤ m}

theorem mem_range_segmentEmbedding_iff (hmn : m < p.n) (v : p.Site) :
    (∃ v₀, segmentEmbedding p hm v₀ = v) ↔ v.1.val < m := by
  constructor
  · rintro ⟨v₀, rfl⟩
    rw [val_segmentEmbedding hmn]
    exact ZMod.val_lt (n := (shortParameters p m hm).n) v₀.1
  · intro h
    refine ⟨(((v.1.val : ℕ) : ZMod (shortParameters p m hm).n), v.2), ?_⟩
    apply Prod.ext
    · change (((((v.1.val : ℕ) : ZMod (shortParameters p m hm).n)).val : ℕ) : ZMod p.n) = v.1
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (show v.1.val < (shortParameters p m hm).n from h),
        ZMod.natCast_zmod_val]
    · rfl

theorem sum_ite_segment_of_mem (hmn : m < p.n) (f : (shortParameters p m hm).Site → ℂ)
    (v₀ : (shortParameters p m hm).Site) :
    (∑ v', if segmentEmbedding p hm v' = segmentEmbedding p hm v₀ then f v' else 0) = f v₀ := by
  simp [(segmentEmbedding_injective hmn).eq_iff]

theorem sum_ite_segment_of_not_mem (f : (shortParameters p m hm).Site → ℂ) {v : p.Site}
    (hv : ¬∃ v₀, segmentEmbedding p hm v₀ = v) :
    (∑ v', if segmentEmbedding p hm v' = v then f v' else 0) = 0 :=
  Finset.sum_eq_zero fun v' _ => by rw [ite_eq_right_iff]; exact fun h => (hv ⟨v', h⟩).elim

/-- Off the end blocks the coupling difference is an out-of-band entry of `H` or zero. -/
theorem norm_couplingDefect_interior (hmn : m < p.n)
    (ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix) (u : (shortParameters p m hm).Site)
    (hu : ¬(u.1.val = 0 ∨ u.1.val = m - 1)) (v : p.Site) :
    ‖couplingDefect (segmentEmbedding p hm) ω.1 (coupledShortMatrix ω) u v‖ ≤
      if p.entryVariance (segmentEmbedding p hm u) v = 0 then ‖ω.1 (segmentEmbedding p hm u) v‖
      else 0 := by
  unfold couplingDefect
  by_cases hv : ∃ v₀, segmentEmbedding p hm v₀ = v
  · obtain ⟨v₀, rfl⟩ := hv
    rw [sum_ite_segment_of_mem hmn]
    have hc : ¬closingBond p hm u v₀ := by unfold closingBond; omega
    simp only [coupledShortMatrix, hc, ite_false, sub_self, norm_zero]
    split_ifs <;> simp
  · rw [sum_ite_segment_of_not_mem _ hv, sub_zero]
    have hvm : m ≤ v.1.val := by
      by_contra h
      exact hv ((mem_range_segmentEmbedding_iff hmn v).mpr (by omega))
    have hj := val_segmentEmbedding hmn u
    have hju : u.1.val < m := ZMod.val_lt (n := (shortParameters p m hm).n) u.1
    have hvn : v.1.val < p.n := ZMod.val_lt v.1
    have hn1 : 1 < p.n := by omega
    have hc1 : ¬v.1 = (segmentEmbedding p hm u).1 := by
      intro h
      have := congrArg ZMod.val h
      omega
    have hc2 : ¬(v.1 = (segmentEmbedding p hm u).1 + 1 ∨ v.1 = (segmentEmbedding p hm u).1 - 1) := by
      rw [zmod_eq_add_one_iff hn1, zmod_eq_sub_one_iff hn1, hj,
        succ_mod_eq (hju.trans hmn), succ_mod_eq hvn]
      split_ifs <;> omega
    have h0 : p.entryVariance (segmentEmbedding p hm u) v = 0 := by
      simp only [Parameters.entryVariance, hc1, hc2, ite_false]
    simp [h0]

/-- On every row the coupling difference is bounded by entries of `H` and `K'`. -/
theorem norm_couplingDefect_le (hmn : m < p.n)
    (ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix) (u : (shortParameters p m hm).Site)
    (v : p.Site) :
    ‖couplingDefect (segmentEmbedding p hm) ω.1 (coupledShortMatrix ω) u v‖ ≤
      ‖ω.1 (segmentEmbedding p hm u) v‖ + ∑ v', ‖ω.2 u v'‖ := by
  have hsum : ∀ v', 0 ≤ ‖ω.2 u v'‖ := fun _ => norm_nonneg _
  unfold couplingDefect
  by_cases hv : ∃ v₀, segmentEmbedding p hm v₀ = v
  · obtain ⟨v₀, rfl⟩ := hv
    rw [sum_ite_segment_of_mem hmn]
    simp only [coupledShortMatrix]
    split_ifs
    · refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      exact Finset.single_le_sum (fun v' _ => hsum v') (Finset.mem_univ v₀)
    · rw [sub_self, norm_zero]
      exact add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun v' _ => hsum v')
  · rw [sum_ite_segment_of_not_mem _ hv, sub_zero]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun v' _ => hsum v')

end Defect

section Mean

variable {p : Parameters} {m : ℕ} {hm : 4 ≤ m}

/-- The end blocks `0` and `m - 1` of the short ring. -/
def endBlocks (p : Parameters) (m : ℕ) (hm : 4 ≤ m) : Finset (shortParameters p m hm).Site :=
  Finset.univ.filter fun u => u.1.val = 0 ∨ u.1.val = m - 1

/-- **Mean resolvent comparison**. Law: `coupledLaw model model'`. If for
every end-block site `u` the event `‖G^K_{x u}‖ > δ` has probability at most `β`, then
`‖E G^H_{ιx,ιx} - E G^K_{xx}‖ ≤ η⁻¹ δ N_K N (2 + 2N_K) + 2η⁻¹ N_K β`. -/
theorem norm_integral_resolvent_sub_le (hmn : m < p.n) (model : p.GaussianRingModel)
    (model' : (shortParameters p m hm).GaussianRingModel) (e : ℝ) {η : ℝ} (hη : 0 < η)
    (x : (shortParameters p m hm).Site) {δ β : ℝ} (hδ : 0 ≤ δ) (hβ : 0 ≤ β)
    (hbad : ∀ u ∈ endBlocks p m hm,
      (Measure.map coupledShortMatrix (coupledLaw model model'))
        {K | δ < ‖(K - ((e : ℂ) + (η : ℂ) * Complex.I) •
          (1 : (shortParameters p m hm).SiteMatrix))⁻¹ x u‖} ≤ ENNReal.ofReal β) :
    ‖(∫ H, (H - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : p.SiteMatrix))⁻¹
          (segmentEmbedding p hm x) (segmentEmbedding p hm x) ∂(model.law : Measure p.SiteMatrix)) -
        ∫ K, (K - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : (shortParameters p m hm).SiteMatrix))⁻¹ x x
          ∂(Measure.map coupledShortMatrix (coupledLaw model model'))‖ ≤
      η⁻¹ * δ * ((shortParameters p m hm).N * p.N * (2 + 2 * (shortParameters p m hm).N)) +
        2 * η⁻¹ * ((shortParameters p m hm).N * β) := by
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I
  set μ := coupledLaw model model'
  set F : p.SiteMatrix → ℂ := fun H => (H - z • (1 : p.SiteMatrix))⁻¹ (segmentEmbedding p hm x) (segmentEmbedding p hm x)
  set G : (shortParameters p m hm).SiteMatrix → (shortParameters p m hm).Site → ℂ := fun K u => (K - z • (1 : (shortParameters p m hm).SiteMatrix))⁻¹ x u
  have hFm : Measurable F := measurable_resolvent_apply z _ _
  have hGm : ∀ u, Measurable fun K => G K u := fun u => measurable_resolvent_apply z _ _
  have hΦ := measurable_coupledShortMatrix (p := p) (hm := hm)
  have hηi : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
  -- the two means on the coupled space
  have h1 : ∫ H, F H ∂(model.law : Measure p.SiteMatrix) = ∫ ω, F ω.1 ∂μ :=
    (integral_coupledLaw_fst model model' F).symm
  have h2 : ∫ K, G K x ∂(Measure.map coupledShortMatrix μ) = ∫ ω, G (coupledShortMatrix ω) x ∂μ :=
    integral_map hΦ.aemeasurable (hGm x).aestronglyMeasurable
  have hHerm : ∀ᵐ ω ∂μ, ω.1.IsHermitian ∧ ω.2.IsHermitian := by
    filter_upwards [ae_fst_isHermitian model model', ae_snd_isHermitian model model'] with ω h1 h2
    exact ⟨h1, h2⟩
  have hFi : Integrable (fun ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix => F ω.1) μ :=
    (integrable_const η⁻¹).mono' (hFm.comp measurable_fst).aestronglyMeasurable
      (by filter_upwards [hHerm] with ω hω using norm_resolvent_apply_le hω.1 e hη _ _)
  have hGi : Integrable (fun ω => G (coupledShortMatrix ω) x) μ :=
    (integrable_const η⁻¹).mono' ((hGm x).comp hΦ).aestronglyMeasurable
      (by filter_upwards [hHerm] with ω hω using
        norm_resolvent_apply_le (coupledShortMatrix_isHermitian hω.1 hω.2) e hη _ _)
  change ‖∫ H, F H ∂(model.law : Measure p.SiteMatrix) -
    ∫ K, G K x ∂(Measure.map coupledShortMatrix μ)‖ ≤ _
  rw [h1, h2, ← integral_sub hFi hGi]
  refine (norm_integral_le_integral_norm _).trans ?_
  -- the dominating functions
  set J : p.SiteMatrix × (shortParameters p m hm).SiteMatrix → ℝ := fun ω => ∑ u ∈ endBlocks p m hm, ∑ v,
    (‖ω.1 (segmentEmbedding p hm u) v‖ + ∑ v', ‖ω.2 u v'‖)
  set I : p.SiteMatrix × (shortParameters p m hm).SiteMatrix → ℝ := fun ω => ∑ u ∈ Finset.univ.filter
    (fun u : (shortParameters p m hm).Site => ¬(u.1.val = 0 ∨ u.1.val = m - 1)),
      ∑ v ∈ Finset.univ.filter (fun v => p.entryVariance (segmentEmbedding p hm u) v = 0), ‖ω.1 (segmentEmbedding p hm u) v‖
  set S : Set (p.SiteMatrix × (shortParameters p m hm).SiteMatrix) := coupledShortMatrix ⁻¹'
    (⋃ u ∈ endBlocks p m hm, {K | δ < ‖G K u‖})
  have hS : MeasurableSet S := hΦ (Finset.measurableSet_biUnion _ fun u _ =>
    measurableSet_lt measurable_const (hGm u).norm)
  have ha : ∀ a v, Integrable (fun ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix => ‖ω.1 a v‖) μ :=
    fun a v => (integrable_norm_entry p model a v).comp_fst _
  have hb : ∀ a v, Integrable (fun ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix => ‖ω.2 a v‖) μ :=
    fun a v => (integrable_norm_entry (shortParameters p m hm) model' a v).comp_snd _
  have hJu : ∀ u v, Integrable (fun ω : p.SiteMatrix × (shortParameters p m hm).SiteMatrix =>
      ‖ω.1 (segmentEmbedding p hm u) v‖ + ∑ v', ‖ω.2 u v'‖) μ :=
    fun u v => (ha _ _).add (integrable_finsetSum _ fun v' _ => hb _ _)
  have hJi : Integrable J μ :=
    integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => hJu u v
  have hIi : Integrable I μ :=
    integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => ha _ _
  have hfi : Integrable (fun ω => ‖F ω.1 - G (coupledShortMatrix ω) x‖) μ := (hFi.sub hGi).norm
  have hgi : Integrable (fun ω => η⁻¹ * δ * J ω + η⁻¹ * η⁻¹ * I ω) μ :=
    (hJi.const_mul _).add (hIi.const_mul _)
  have hpt : ∀ᵐ ω ∂μ, ‖F ω.1 - G (coupledShortMatrix ω) x‖ ≤
      (η⁻¹ * δ * J ω + η⁻¹ * η⁻¹ * I ω) + S.indicator (fun _ => 2 * η⁻¹) ω := by
    filter_upwards [hHerm] with ω hω
    have hK := coupledShortMatrix_isHermitian hω.1 hω.2
    have hJ0 : 0 ≤ J ω := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    have hI0 : 0 ≤ I ω := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    by_cases hω' : ω ∈ S
    · rw [Set.indicator_of_mem hω']
      have : ‖F ω.1 - G (coupledShortMatrix ω) x‖ ≤ 2 * η⁻¹ := by
        refine (norm_sub_le _ _).trans ?_
        have := norm_resolvent_apply_le hω.1 e hη (segmentEmbedding p hm x) (segmentEmbedding p hm x)
        have := norm_resolvent_apply_le hK e hη x x
        change ‖F ω.1‖ ≤ η⁻¹ at *
        linarith
      nlinarith [mul_nonneg (mul_nonneg hηi hδ) hJ0, mul_nonneg (mul_nonneg hηi hηi) hI0]
    · rw [Set.indicator_of_notMem hω', add_zero]
      have hgood : ∀ u ∈ endBlocks p m hm, ‖G (coupledShortMatrix ω) u‖ ≤ δ := by
        intro u hu
        by_contra hlt
        push Not at hlt
        exact hω' (Set.mem_preimage.mpr (Set.mem_biUnion hu hlt))
      have hP6 := norm_resolvent_sub_le_defect (segmentEmbedding_injective hmn) hω.1 hK e hη x
      refine hP6.trans ?_
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun u : (shortParameters p m hm).Site => u.1.val = 0 ∨ u.1.val = m - 1), mul_add]
      refine add_le_add ?_ ?_
      · rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hηi
        change _ ≤ δ * ∑ u ∈ endBlocks p m hm, ∑ v, (‖ω.1 (segmentEmbedding p hm u) v‖ + ∑ v', ‖ω.2 u v'‖)
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun u hu => ?_
        exact mul_le_mul (hgood u hu)
          (Finset.sum_le_sum fun v _ => norm_couplingDefect_le hmn ω u v)
          (Finset.sum_nonneg fun _ _ => norm_nonneg _) hδ
      · rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hηi
        change _ ≤ η⁻¹ * ∑ u ∈ Finset.univ.filter
          (fun u : (shortParameters p m hm).Site => ¬(u.1.val = 0 ∨ u.1.val = m - 1)),
            ∑ v ∈ Finset.univ.filter (fun v => p.entryVariance (segmentEmbedding p hm u) v = 0), ‖ω.1 (segmentEmbedding p hm u) v‖
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun u hu => ?_
        refine mul_le_mul (norm_resolvent_apply_le hK e hη x u) ?_
          (Finset.sum_nonneg fun _ _ => norm_nonneg _) hηi
        refine (Finset.sum_le_sum fun v _ =>
          norm_couplingDefect_interior hmn ω u (Finset.mem_filter.mp hu).2 v).trans
            (le_of_eq (Finset.sum_filter _ _).symm)
  -- the expectations
  have hI0 : ∫ ω, I ω ∂μ = 0 := by
    change ∫ ω, ∑ u ∈ Finset.univ.filter
      (fun u : (shortParameters p m hm).Site => ¬(u.1.val = 0 ∨ u.1.val = m - 1)),
        ∑ v ∈ Finset.univ.filter (fun v => p.entryVariance (segmentEmbedding p hm u) v = 0), ‖ω.1 (segmentEmbedding p hm u) v‖ ∂μ = 0
    rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => ha _ _]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [integral_finsetSum _ fun v _ => ha _ _]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [integral_coupledLaw_fst model model' (fun H => ‖H (segmentEmbedding p hm u) v‖)]
    exact integral_norm_entry_eq_zero p model (Finset.mem_filter.mp hv).2
  have hJ : ∫ ω, J ω ∂μ ≤ ((shortParameters p m hm).N : ℝ) * (p.N * (2 + 2 * (shortParameters p m hm).N)) := by
    have hcard : ((endBlocks p m hm).card : ℝ) ≤ (shortParameters p m hm).N := by
      rw [← card_site_eq (shortParameters p m hm)]
      exact_mod_cast Finset.card_le_univ _
    calc ∫ ω, J ω ∂μ ≤ ∑ u ∈ endBlocks p m hm, ∑ v : p.Site, (2 + 2 * ((shortParameters p m hm).N : ℝ)) := by
          change ∫ ω, ∑ u ∈ endBlocks p m hm, ∑ v, (‖ω.1 (segmentEmbedding p hm u) v‖ + ∑ v', ‖ω.2 u v'‖) ∂μ ≤ _
          rw [integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => hJu u v]
          refine Finset.sum_le_sum fun u _ => ?_
          rw [integral_finsetSum _ fun v _ => hJu u v]
          refine Finset.sum_le_sum fun v _ => ?_
          rw [integral_add (ha _ _) (integrable_finsetSum _ fun v' _ => hb _ _),
            integral_finsetSum _ fun v' _ => hb _ _]
          refine add_le_add ?_ ?_
          · rw [integral_coupledLaw_fst model model' (fun H => ‖H (segmentEmbedding p hm u) v‖)]
            exact integral_norm_entry_le_two p model _ _
          · calc ∑ v', ∫ ω, ‖ω.2 u v'‖ ∂μ ≤ ∑ _v' : (shortParameters p m hm).Site, (2 : ℝ) :=
                  Finset.sum_le_sum fun v' _ => by
                    rw [integral_coupledLaw_snd model model' (fun K => ‖K u v'‖)]
                    exact integral_norm_entry_le_two (shortParameters p m hm) model' _ _
              _ = 2 * (shortParameters p m hm).N := by
                  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_site_eq]; ring
      _ = ((endBlocks p m hm).card : ℝ) * (p.N * (2 + 2 * (shortParameters p m hm).N)) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul,
            card_site_eq]
      _ ≤ ((shortParameters p m hm).N : ℝ) * (p.N * (2 + 2 * (shortParameters p m hm).N)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  have hSr : μ.real S ≤ (shortParameters p m hm).N * β := by
    have hcard : ((endBlocks p m hm).card : ℝ) ≤ (shortParameters p m hm).N := by
      rw [← card_site_eq (shortParameters p m hm)]
      exact_mod_cast Finset.card_le_univ _
    have hmeas : μ S ≤ ENNReal.ofReal ((shortParameters p m hm).N * β) := by
      change μ (coupledShortMatrix ⁻¹' (⋃ u ∈ endBlocks p m hm, {K | δ < ‖G K u‖})) ≤ _
      rw [Set.preimage_iUnion₂]
      refine (measure_biUnion_finset_le _ _).trans ?_
      calc ∑ u ∈ endBlocks p m hm, μ (coupledShortMatrix ⁻¹' {K | δ < ‖G K u‖})
          ≤ ∑ _u ∈ endBlocks p m hm, ENNReal.ofReal β :=
            Finset.sum_le_sum fun u hu =>
              (Measure.le_map_apply hΦ.aemeasurable _).trans (hbad u hu)
        _ = ENNReal.ofReal (((endBlocks p m hm).card : ℝ) * β) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal ((shortParameters p m hm).N * β) :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hβ)
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hmeas
  have e1 := integral_le_add_indicator hS hfi hgi (2 * η⁻¹) hpt
  rw [integral_add (hJi.const_mul _) (hIi.const_mul _), integral_const_mul, integral_const_mul,
    hI0] at e1
  have e2 := mul_le_mul_of_nonneg_left hJ (mul_nonneg hηi hδ)
  have e3 := mul_le_mul_of_nonneg_right hSr (by positivity : (0 : ℝ) ≤ 2 * η⁻¹)
  have e4 : η⁻¹ * δ * (((shortParameters p m hm).N : ℝ) * (p.N * (2 + 2 * (shortParameters p m hm).N))) =
      η⁻¹ * δ * (((shortParameters p m hm).N : ℝ) * p.N * (2 + 2 * (shortParameters p m hm).N)) := by ring
  have e5 : ((shortParameters p m hm).N : ℝ) * β * (2 * η⁻¹) = 2 * η⁻¹ * ((shortParameters p m hm).N * β) := by ring
  linarith

/-- **Diagonal short-ring estimate in mean**: under any physical law of any `q`, if
`P(‖G_{xx}(z) - m‖ > t) ≤ β`, `‖m‖ ≤ 1`, then `‖E G_{xx}(z) - m‖ ≤ t + (η⁻¹ + 1) β`. -/
theorem norm_integral_resolvent_diag_sub_le (q : Parameters) (model : q.GaussianRingModel)
    (e : ℝ) {η : ℝ} (hη : 0 < η) (x : q.Site) (c : ℂ) (hc : ‖c‖ ≤ 1) {t β : ℝ} (ht : 0 ≤ t)
    (hβ : 0 ≤ β)
    (hbad : (model.law : Measure q.SiteMatrix)
      {K | t < ‖(K - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : q.SiteMatrix))⁻¹ x x - c‖} ≤
        ENNReal.ofReal β) :
    ‖(∫ K, (K - ((e : ℂ) + (η : ℂ) * Complex.I) • (1 : q.SiteMatrix))⁻¹ x x
        ∂(model.law : Measure q.SiteMatrix)) - c‖ ≤ t + (η⁻¹ + 1) * β := by
  set z : ℂ := (e : ℂ) + (η : ℂ) * Complex.I
  set P := (model.law : Measure q.SiteMatrix)
  have hGi := integrable_resolvent_apply q model e hη x x
  have hm : Measurable fun K : q.SiteMatrix => ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖ :=
    ((measurable_resolvent_apply z x x).sub measurable_const).norm
  have hS : MeasurableSet {K : q.SiteMatrix | t < ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖} :=
    measurableSet_lt measurable_const hm
  have hsub : (∫ K, (K - z • (1 : q.SiteMatrix))⁻¹ x x ∂P) - c =
      ∫ K, ((K - z • (1 : q.SiteMatrix))⁻¹ x x - c) ∂P := by
    rw [integral_sub hGi (integrable_const c), integral_const, probReal_univ, one_smul]
  rw [hsub]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hpt : ∀ᵐ K ∂P, ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖ ≤
      t + {K : q.SiteMatrix | t < ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖}.indicator
        (fun _ => η⁻¹ + 1) K := by
    filter_upwards [model.isPhysical.1] with K hK
    by_cases hKS : t < ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖
    · rw [Set.indicator_of_mem (show K ∈ {K : q.SiteMatrix |
        t < ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖} from hKS)]
      have := norm_resolvent_apply_le hK e hη x x
      have := norm_sub_le ((K - z • (1 : q.SiteMatrix))⁻¹ x x) c
      linarith
    · rw [Set.indicator_of_notMem (show K ∉ {K : q.SiteMatrix |
        t < ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖} from hKS), add_zero]
      exact not_lt.mp hKS
  have hfi : Integrable (fun K : q.SiteMatrix => ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖) P :=
    (hGi.sub (integrable_const c)).norm
  have e1 := integral_le_add_indicator hS hfi (integrable_const t) (η⁻¹ + 1) hpt
  rw [integral_const, probReal_univ, one_smul] at e1
  have e2 : P.real {K : q.SiteMatrix | t < ‖(K - z • (1 : q.SiteMatrix))⁻¹ x x - c‖} ≤ β :=
    ENNReal.toReal_le_of_le_ofReal hβ hbad
  have e3 := mul_le_mul_of_nonneg_right e2 (by positivity : (0 : ℝ) ≤ η⁻¹ + 1)
  linarith

end Mean

end BlockBand.Density
