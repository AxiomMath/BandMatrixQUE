module

public import BlockBand.SourceProcess.PhysApprox.B3Ident2KStopMain

/-!
# `CapIdentKStop` proved (assembly)

Measure: the candidate's `Q` (premises `CapIdentPremise`).

* `gridOf`, `sQ`: the grid made of `0`, the first `n + 1` enumerated good rationals and a dense
  non-birth grid.
* `min_gn_le`: `min(g_n, N) ≤ fGrid(obs)` pointwise, for every such grid.
* **`kStop_dominated`**: from `TransmissionLawContract`, `ComplexClosedSummed`,
  `ComplexClosedLindeberg` and `ComplexKStoppedMomentMax`, every candidate satisfies
  `IsKStopDominated`; the dominating function has `∫⁻ ≤ 2(2 + 2C_J² + 2C)/p`.
* **`capIdentKStop_holds : CapIdentKStop`**.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Ident2

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.CapLimit
open scoped NNReal ENNReal

/-- The grid: `0`, then `S`, then `d`. -/
def gridOf (n M : ℕ) (S : Fin (n + 1) → ℚ) (d : Fin M → ℚ) : Option (Fin (n + 1) ⊕ Fin M) → ℚ :=
  fun a => a.elim 0 (Sum.elim S d)

open scoped Classical in
/-- The first `n + 1` enumerated rationals, replaced by `0` when not good. -/
def sQ {np : ℕ} (s t : ℝ) (τ : Fin np → ℝ) (n : ℕ) : Fin (n + 1) → ℚ :=
  fun k => if goodQ s t τ (enumQ k) then enumQ k else 0

variable {K np : ℕ} {b E s h : ℝ} {τ m : Fin np → ℝ}
  {Ω' : Type} [MeasurableSpace Ω'] {tseq : Ω' → ℕ → ℝ}
  {G : ℝ≥0 → Ω' → GramState (SrcCol K (Fin np))} {Kc : ℝ≥0 → Ω' → Matrix (Fin np) (Fin np) ℂ}

omit [MeasurableSpace Ω'] in
theorem trOf_complexObs {α : Type} (r : α → ℚ) (ij : Fin np × Fin np) (ω : Ω') (c : α) :
    trOf (fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω) c =
      ((G ((r c : ℝ)).toNNReal ω).1.trace).re := by
  simp [trOf, gIdx, gTime, complexObs, gramEntry, Matrix.trace]

omit [MeasurableSpace Ω'] in
/-- **`min(g_n, N)` is below the grid functional.** -/
theorem min_gn_le (t L : ℝ) (ij : Fin np × Fin np) (n M : ℕ) (d : Fin M → ℚ)
    (hd0 : ∀ a, 0 ≤ d a) (N : ℕ) (ω : Ω') :
    min (gn E s t L τ m G Kc ij n ω) (N : ℝ≥0∞) ≤
      ENNReal.ofReal (fGrid L (gridOf n M (sQ s t τ n) d) N
        (fun a => (kJ E s τ m ((gridOf n M (sQ s t τ n) d a : ℝ)).toNNReal - kJ E s τ m 0)
          ij.1 ij.2) none
        (fun l => complexObs tseq G Kc (gIdx ij l) (gTime (gridOf n M (sQ s t τ n) d) l) ω)) := by
  classical
  set r := gridOf n M (sQ s t τ n) d
  set κ : Option (Fin (n + 1) ⊕ Fin M) → ℂ := fun a =>
    (kJ E s τ m ((r a : ℝ)).toNNReal - kJ E s τ m 0) ij.1 ij.2
  set X := fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun k => termQ E s t L τ m G Kc ij (enumQ k) ω)
  have hgn : gn E s t L τ m G Kc ij n ω = termQ E s t L τ m G Kc ij (enumQ k) ω := hkeq
  rw [hgn]
  unfold termQ
  split_ifs with hg
  swap
  · simp
  by_cases hal : ω ∈ aliveQ G L (enumQ k)
  swap
  · rw [Set.indicator_of_notMem hal]; simp
  rw [Set.indicator_of_mem hal]
  have hkn : k < n + 1 := Finset.mem_range.1 hk
  set a : Option (Fin (n + 1) ⊕ Fin M) := some (Sum.inl ⟨k, hkn⟩)
  have hra : r a = enumQ k := by simp [r, a, gridOf, sQ, hg]
  have hrn : ∀ c, (0 : ℚ) ≤ r c := by
    rintro (_ | (j | j))
    · simp [r, gridOf]
    · simp only [r, gridOf, Option.elim, Sum.elim_inl, sQ]
      split_ifs with hj
      · exact hj.1
      · exact le_rfl
    · exact hd0 j
  have hind : gridInd L r X a = 1 := Finset.prod_eq_one fun c hc => by
    have hc' : r c ≤ r a := (Finset.mem_filter.1 hc).2
    have hlt : trOf X c < L := by
      rw [trOf_complexObs]; exact hal (r c) (hrn c) (hra ▸ hc')
    simp [hlt]
  have e : X (Sum.inr a) - X (Sum.inr none) - κ a =
      kComp E s τ m Kc ij ((enumQ k : ℝ)).toNNReal ω := by
    show Kc ((r a : ℝ)).toNNReal ω ij.1 ij.2 - Kc ((r none : ℝ)).toNNReal ω ij.1 ij.2 -
      (kJ E s τ m ((r a : ℝ)).toNNReal - kJ E s τ m 0) ij.1 ij.2 = _
    have h0 : r none = 0 := rfl
    rw [hra, h0]
    simp only [kComp, kCompensated, Matrix.sub_apply, Rat.cast_zero, Real.toNNReal_zero]
    ring
  have hkt : kTerm N κ none X a = min (‖kComp E s τ m Kc ij ((enumQ k : ℝ)).toNNReal ω‖ ^ 2) N := by
    rw [kTerm, e]
  calc min (ENNReal.ofReal (‖kComp E s τ m Kc ij ((enumQ k : ℝ)).toNNReal ω‖ ^ 2)) (N : ℝ≥0∞)
      ≤ ENNReal.ofReal (min (‖kComp E s τ m Kc ij ((enumQ k : ℝ)).toNNReal ω‖ ^ 2) N) := by
        rcases le_total (‖kComp E s τ m Kc ij ((enumQ k : ℝ)).toNNReal ω‖ ^ 2) (N : ℝ)
          with hle | hle
        · rw [min_eq_left hle]; exact min_le_left _ _
        · rw [min_eq_right hle, ENNReal.ofReal_natCast]; exact min_le_right _ _
    _ = ENNReal.ofReal (gridInd L r X a * kTerm N κ none X a) := by rw [hind, one_mul, hkt]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
          (Finset.le_sup' (fun a => gridInd L r X a * kTerm N κ none X a) (Finset.mem_univ a))

omit [MeasurableSpace Ω'] in
theorem gn_mono (E s t L : ℝ) (τ m : Fin np → ℝ) (ij : Fin np × Fin np) :
    Monotone (gn (Ω' := Ω') E s t L τ m G Kc ij) := fun n₁ n₂ hn ω =>
  Finset.sup'_mono _ (Finset.range_mono (by omega)) _

omit [MeasurableSpace Ω'] in
theorem gE_eq_iSup (E s t L : ℝ) (τ m : Fin np → ℝ) (ij : Fin np × Fin np) (ω : Ω') :
    gE E s t L τ m G Kc ij ω = ⨆ n, gn E s t L τ m G Kc ij n ω := by
  refine le_antisymm (iSup_le fun k => le_iSup_of_le k ?_) (iSup_le fun n => ?_)
  · exact Finset.le_sup' (fun k => termQ E s t L τ m G Kc ij (enumQ k) ω)
      (Finset.self_mem_range_succ k)
  · exact Finset.sup'_le _ _ fun k _ => le_iSup (fun k => termQ E s t L τ m G Kc ij (enumQ k) ω) k

omit [MeasurableSpace Ω'] in
theorem termQ_ne_top (E s t L : ℝ) (τ m : Fin np → ℝ) (ij : Fin np × Fin np) (q : ℚ) (ω : Ω') :
    termQ E s t L τ m G Kc ij q ω ≠ ⊤ := by
  unfold termQ
  split_ifs
  · by_cases hω : ω ∈ aliveQ G L q
    · rw [Set.indicator_of_mem hω]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem hω]; exact ENNReal.zero_ne_top
  · exact ENNReal.zero_ne_top

omit [MeasurableSpace Ω'] in
theorem gn_ne_top (E s t L : ℝ) (τ m : Fin np → ℝ) (ij : Fin np × Fin np) (n : ℕ) (ω : Ω') :
    gn E s t L τ m G Kc ij n ω ≠ ⊤ := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.nonempty_range_add_one
    (fun k => termQ E s t L τ m G Kc ij (enumQ k) ω)
  have : gn E s t L τ m G Kc ij n ω = termQ E s t L τ m G Kc ij (enumQ k) ω := hk
  rw [this]
  exact termQ_ne_top E s t L τ m ij _ ω

/-- **The `𝒦` stop in the limit.** -/
theorem kStop_dominated (hTL : TransmissionLawContract) (hS : ComplexClosedSummed)
    (hL : ComplexClosedLindeberg) (hKM : ComplexKStoppedMomentMax) {T : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℝ → Ω → FiniteMeasure unitInterval}
    {φ : ℕ → ℕ} {Q : Measure Ω'}
    (hP : CapIdentPremise b E τ m T s h K Vs P μ φ Q tseq G Kc) :
    IsKStopDominated E s τ m Q G Kc := by
  intro L t ij
  obtain ⟨hD, hlim, hA, hne, hφ, ⟨hQ, htm, hGm, hKm, -, hkc⟩, hfdd⟩ := hP
  have := hQ
  obtain ⟨⟨hb0, hb, hE1, hE2, hinj, hτ0, hm, hτT⟩, hs, hτ, hh0, hh1, hVs⟩ := id hD
  have hb1 : b < 1 := by linarith
  have hobs := measurable_complexObs htm hGm hKm
  -- the horizon and the level
  set T' := max T (s + t + 1)
  have hD' : FrameDomain b E τ m T' s h K Vs :=
    ⟨⟨hb0, hb, hE1, hE2, hinj, hτ0, hm, fun j => (hτT j).trans_le (le_max_left _ _)⟩, hs, hτ,
      hh0, hh1, hVs⟩
  have hsT' : s ≤ T' := by
    have := le_max_right T (s + t + 1); have := t.2; linarith
  set R := L + ∑ i, dStar b * m i + 2
  obtain ⟨C0, hC0⟩ := hKM b E np τ m T' s h K Vs hD' R
  set C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  have hZ : ∀ᶠ n in atTop, ∫⁻ y, kMaxZ b E s h τ m R T' (φ n) (Vs (φ n)) ij y
      ∂closedLaw b (φ n) np ≤ ENNReal.ofReal C :=
    hφ.eventually (hC0.mono fun W hW => (hW ij).trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  -- the cap mass
  have := hlim.prob
  have := CapCond.isFiniteMeasure_entranceLaw P μ s
  set p := (entranceLaw P μ s (capSet K h)).toReal
  have hp : 0 < p := ENNReal.toReal_pos hne (measure_ne_top _ _)
  have hcap : ∀ᶠ n in atTop, growthPathLaw (φ n) b (physCapEventC b E s h K (φ n)) ≠ 0 ∧
      p / 2 ≤ (growthPathLaw (φ n) b (physCapEventC b E s h K (φ n))).toReal := by
    filter_upwards [hφ.eventually ((CapCond.tendsto_capProb hTL hb0 hb hE1 hE2 hlim hs hh0 K
      (hA K)).eventually (lt_mem_nhds (half_lt_self hp)))] with n hn
    exact ⟨(ENNReal.toReal_pos_iff.1 (lt_trans (half_pos hp) hn)).1.ne', hn.le⟩
  -- the birth part of `𝒦`
  obtain ⟨CK, hCK⟩ := exists_norm_kJ_le E s τ m
  set CJ := 2 * CK
  have hκ0 : ∀ v : ℝ≥0, ‖(kJ E s τ m v - kJ E s τ m 0) ij.1 ij.2‖ ≤ CJ := fun v => by
    rw [Matrix.sub_apply]
    exact (norm_sub_le _ _).trans (by linarith [hCK v ij.1 ij.2, hCK 0 ij.1 ij.2])
  set nc : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ)
  have hnc : 0 < nc := by
    have : 0 < Fintype.card (SrcCol K (Fin np)) := Fintype.card_pos_iff.2 ⟨Sum.inr ij.1⟩
    exact Nat.cast_pos.2 this
  set B0 := (2 + 2 * CJ ^ 2 + 2 * C) / (p / 2)
  have hB0 : 0 ≤ B0 := by positivity
  -- the key bound
  have key : ∀ (n N : ℕ) (ε : ℝ≥0), 0 < ε →
      ∫⁻ ω, min (gn E s t L τ m G Kc ij n ω) (N : ℝ≥0∞) ∂Q ≤ ENNReal.ofReal B0 + ε := by
    intro n N ε hε
    have hε' : (0 : ℝ) < ε := hε
    set θ : ℝ := ε * (p / 2) / (N * nc + 1)
    have hθ : 0 < θ := by positivity
    have hη : (0 : ℝ) < 1 / nc := by positivity
    have hmodc := fun col : SrcCol K (Fin np) =>
      Modul.modulusS hS hL hD' (Sum.inl (0, col, col)) le_rfl hsT' hη hθ
    choose δc hδc W₀c hW₀c using hmodc
    set δ := Finset.univ.inf' ⟨Sum.inr ij.1, Finset.mem_univ _⟩ δc
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun col _ => hδc col
    have hmod : ∀ᶠ n' in atTop, ∀ col, closedLaw b (φ n') np (modEvent b E s h τ m T' δ
        (1 / nc) (φ n') (Vs (φ n')) col) ≤ ENNReal.ofReal θ :=
      Filter.eventually_all.2 fun col => (hφ.eventually (eventually_ge_atTop (W₀c col))).mono
        fun n' hn' => (measure_mono (modEvent_mono (Finset.inf'_le _ (Finset.mem_univ col)) _
          col)).trans (hW₀c col _ hn')
    obtain ⟨M, d, hd, hdd⟩ := exists_grid s τ (t := (t : ℝ)) t.2 hδ
    set r := gridOf n M (sQ s t τ n) d
    have hd0 : ∀ a, 0 ≤ d a := fun a => by exact_mod_cast (hd a).1.le
    have hrt : ∀ a, 0 ≤ (r a : ℝ) ∧ (r a : ℝ) ≤ t ∧ ∀ j, s + (r a : ℝ) ≠ τ j := by
      rintro (_ | (k | a))
      · refine ⟨by simp [r, gridOf], by simp [r, gridOf], fun j => ?_⟩
        have h0 : (r none : ℝ) = 0 := by simp [r, gridOf]
        rw [h0, add_zero]; exact (hτ j).ne
      · simp only [r, gridOf, Option.elim, Sum.elim_inl, sQ]
        split_ifs with hg
        · exact ⟨by exact_mod_cast hg.1, hg.2.1, hg.2.2⟩
        · refine ⟨by simp, by simp, fun j => ?_⟩
          rw [Rat.cast_zero, add_zero]; exact (hτ j).ne
      · exact ⟨(hd a).1.le, (hd a).2.1, (hd a).2.2⟩
    have hrT : ∀ a, s + (r a : ℝ) ≤ T' := fun a => by
      have := le_max_right T (s + t + 1); have := (hrt a).2.1; linarith
    have hdense : ∀ x : ℝ, 0 ≤ x → (∃ a, x < r a) → ∃ c, (r c : ℝ) ≤ x ∧ x - δ ≤ r c := by
      rintro x hx ⟨a, ha⟩
      by_cases hxδ : x < δ
      · exact ⟨none, by simpa [r, gridOf] using hx, by simp [r, gridOf]; linarith⟩
      · obtain ⟨a', ha1, ha2⟩ := hdd x (not_lt.1 hxδ) (ha.le.trans (hrt a).2.1)
        exact ⟨some (Sum.inr a'), ha1, ha2⟩
    have hI := integral_fGrid_le hfdd hobs hb1 hm hs.le hτ (N := (N : ℝ)) (Nat.cast_nonneg N) hC
      hθ.le hp le_rfl (a₀ := none) rfl (fun a => (hrt a).1) hrT (fun a => (hrt a).2.2) hδ.le
      hdense (κ := fun a => (kJ E s τ m ((r a : ℝ)).toNNReal - kJ E s τ m 0) ij.1 ij.2)
      (fun a => hκ0 _) ij hcap hmod hZ
    have hf0 : ∀ ω, 0 ≤ fGrid L r N
        (fun a => (kJ E s τ m ((r a : ℝ)).toNNReal - kJ E s τ m 0) ij.1 ij.2) none
        (fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω) := fun ω =>
      (psiFun_nonneg (Nat.cast_nonneg N) 0 _).trans (psiFun_le_fGrid (Nat.cast_nonneg N) 0 _)
    calc ∫⁻ ω, min (gn E s t L τ m G Kc ij n ω) (N : ℝ≥0∞) ∂Q
        ≤ ∫⁻ ω, ENNReal.ofReal (fGrid L r N
            (fun a => (kJ E s τ m ((r a : ℝ)).toNNReal - kJ E s τ m 0) ij.1 ij.2) none
            (fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω)) ∂Q :=
          lintegral_mono fun ω => min_gn_le t L ij n M d hd0 N ω
      _ = ENNReal.ofReal (∫ ω, fGrid L r N
            (fun a => (kJ E s τ m ((r a : ℝ)).toNNReal - kJ E s τ m 0) ij.1 ij.2) none
            (fun l => complexObs tseq G Kc (gIdx ij l) (gTime r l) ω) ∂Q) :=
          (ofReal_integral_eq_lintegral_ofReal hI.1 (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (B0 + ε) := by
          refine ENNReal.ofReal_le_ofReal (hI.2.trans ?_)
          have e1 : (2 + 2 * CJ ^ 2 + N * nc * θ + 2 * C) / (p / 2) =
              B0 + N * nc * θ / (p / 2) := by simp only [B0]; ring
          have e2 : (N : ℝ) * nc * θ / (p / 2) = ε * ((N * nc) / (N * nc + 1)) := by
            simp only [θ]; field_simp
          have e3 : (N : ℝ) * nc / (N * nc + 1) ≤ 1 :=
            (div_le_one (by positivity)).2 (by linarith)
          rw [e1, e2]
          nlinarith [mul_le_mul_of_nonneg_left e3 hε'.le]
      _ = ENNReal.ofReal B0 + ε := by
          rw [ENNReal.ofReal_add hB0 hε'.le, ENNReal.ofReal_coe_nnreal]
  -- integrate
  have hgnm : ∀ n, Measurable (gn E s t L τ m G Kc ij n) := fun n =>
    Finset.measurable_range_sup'' fun k _ => measurable_termQ hobs hGm E s t L τ m ij _
  have hgn : ∀ n, ∫⁻ ω, gn E s t L τ m G Kc ij n ω ∂Q ≤ ENNReal.ofReal B0 := by
    intro n
    have e : ∀ ω, gn E s t L τ m G Kc ij n ω =
        ⨆ N : ℕ, min (gn E s t L τ m G Kc ij n ω) (N : ℝ≥0∞) := fun ω => by
      refine le_antisymm ?_ (iSup_le fun N => min_le_left _ _)
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (gn_ne_top E s t L τ m ij n ω)
      exact le_iSup_of_le N (le_min le_rfl hN.le)
    rw [lintegral_congr e, lintegral_iSup (fun N => (hgnm n).min measurable_const)
      (fun N₁ N₂ hN ω => min_le_min le_rfl (by exact_mod_cast hN))]
    exact iSup_le fun N => ENNReal.le_of_forall_pos_le_add fun ε hε _ => key n N ε hε
  have hgEm : Measurable (gE E s t L τ m G Kc ij) :=
    Measurable.iSup fun k => measurable_termQ hobs hGm E s t L τ m ij _
  have hgE : ∫⁻ ω, gE E s t L τ m G Kc ij ω ∂Q ≤ ENNReal.ofReal B0 := by
    simp_rw [gE_eq_iSup]
    rw [lintegral_iSup hgnm (gn_mono E s t L τ m ij)]
    exact iSup_le hgn
  have hfin : ∫⁻ ω, gE E s t L τ m G Kc ij ω ∂Q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgE
  refine ⟨fun ω => (gE E s t L τ m G Kc ij ω).toReal,
    integrable_toReal_of_lintegral_ne_top hgEm.aemeasurable hfin, ?_⟩
  filter_upwards [ae_lt_top hgEm hfin] with ω hω v hvt hvσ
  exact (ENNReal.ofReal_le_iff_le_toReal hω.ne).1
    (ofReal_le_gE E s τ m L t ij ω (hkc ω) v hvt hvσ)

/-- **`CapIdentKStop` holds.** -/
theorem capIdentKStop_holds : CapIdentKStop := by
  intro hTL hS _ hK hL b E np τ m T s h K Vs Ω mΩ P μ φ Ω' mΩ' Q tseq G Kc hP
  exact kStop_dominated hTL hS hL hK hP

end BlockBand.SourceProcess.PhysApprox.B3.Ident2
