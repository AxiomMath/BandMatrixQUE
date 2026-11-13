module

public import BlockBand.Transmission.Dual.GGlueProc
public import BlockBand.Transmission.Dual.GGlueFilt

/-!
# The glued filtration and the martingale clauses of the glued process

Setting of the glued process, with `σ(π') ≤ 𝓖₀` on the restart space.
* `comapFilt`, `martingale_comap`: the pull-back of a filtration and of its martingales
  (`P.map π'` is the first-stage law);
* `𝓕R`, `gFilt`: the first-stage filtration pulled back by `π'`, and the glued filtration
  `glueFilt` for `ρ = ρ₁ ∘ π'` and `θ = ρ.untopA`;
* `adapted_g`: the glued process is `gFilt`-adapted (`measurable_glueFilt_ite`; after `ρ` the
  truncated state is `unpad ∘ padPath` at the stopping time `(t − θ)⁺`);
* `dualMartingale_g_top`: the level-`(k+1)` martingale of the glued process is `M1 ∘ π'`, and
  `martingale_g_top` (`martingale_glue_pre`);
* `dualMartingale_g_low`: at a level `q' ≤ k` it is `1{ρ ≤ t} M'_{t−θ}` (`dualMartingale_shift`),
  and `martingale_g_low` (`martingale_glue_post`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-!
## Pull-back filtrations
-/

section Comap

variable {Ω Ω₁ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₁] {π' : Ω → Ω₁}

/-- The pull-back `t ↦ σ(π')`-version of a filtration. -/
def comapFilt (hπ : Measurable π') (𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) where
  seq t := (𝓖₁ t).comap π'
  mono' _ _ h := MeasurableSpace.comap_mono (𝓖₁.mono h)
  le' t := (MeasurableSpace.comap_mono (𝓖₁.le t)).trans hπ.comap_le

/-- Martingales pull back along `π'` to martingales under `P` for `comapFilt`. -/
theorem martingale_comap (hπ : Measurable π')
    {𝓖₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω₁)} {P : Measure Ω} [IsFiniteMeasure P]
    {M : ℝ≥0 → Ω₁ → ℝ} (hM : Martingale M 𝓖₁ (P.map π')) :
    Martingale (fun t ω => M t (π' ω)) (comapFilt hπ 𝓖₁) P := by
  refine martingale_of_setIntegral (fun t => ((hM.1 t).measurable.comp
    (comap_measurable (m := 𝓖₁ t) π')).stronglyMeasurable)
    (fun t => (hM.integrable t).comp_measurable hπ) fun s t hst A hA => ?_
  obtain ⟨B, hB, rfl⟩ := hA
  have hBm := 𝓖₁.le s _ hB
  rw [← setIntegral_map hBm (hM.integrable t).aestronglyMeasurable hπ.aemeasurable,
    ← setIntegral_map hBm (hM.integrable s).aestronglyMeasurable hπ.aemeasurable]
  exact (hM.setIntegral_eq hst hB).symm

end Comap

variable {k : ℕ} {D0 : ℝ}
variable {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin ((k + 1) + (k + 1)) → ℝ}

namespace B1R

variable (F : B1R D0 (k + 1) μ ξ)
variable {Ω : Type} [MeasurableSpace Ω] {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
  {P : Measure Ω} {π' : Ω → ΩR S (k + 1)} {N' : ℝ≥0 → Ω → ℕ} {X' Y' : ℝ≥0 → Ω → ℕ → ℝ}

theorem measurable_of_comap (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0) :
    Measurable π' := fun _ hs => 𝓖.le 0 _ (hcomap _ ⟨_, hs, rfl⟩)

omit [IsProbabilityMeasure μ] in
theorem le_𝓕R (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0) (t : ℝ≥0) :
    comapFilt (measurable_of_comap hcomap) (𝓖R μ (k + 1)) t ≤ 𝓖 0 :=
  (MeasurableSpace.comap_mono ((𝓖R μ (k + 1)).le t)).trans hcomap

theorem isStoppingTime_rho (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0)
    (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) :
    IsStoppingTime (comapFilt (measurable_of_comap hcomap) (𝓖R μ (k + 1)))
      (fun ω => F.rho1 (π' ω)) :=
  fun t => ⟨_, F.isStoppingTime_rho1 hD0 hξ hξc t, rfl⟩

theorem measurable_theta (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0)
    (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) :
    Measurable[𝓖 0] (F.theta π') :=
  ((F.measurable_rho1 hD0 hξ hξc).untopA.comp (comap_measurable π')).mono hcomap le_rfl

/-- **The glued filtration.** -/
abbrev gFilt (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0)
    (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) :=
  glueFilt (le_𝓕R hcomap) (F.isStoppingTime_rho hcomap hD0 hξ hξc)
    (F.measurable_theta hcomap hD0 hξ hξc)

/-!
## Adaptedness
-/

theorem measurable_shift_padPath (hD' : IsDualFrom P 𝓖 D0 k N' X' Y') {θ : Ω → ℝ≥0}
    (hθ : Measurable[𝓖 0] θ) (t : ℝ≥0) :
    Measurable[shiftFilt hθ t] fun ω => padPath k N' X' Y' (t - θ ω) ω :=
  measurable_stoppedValue (StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (hD'.measurable_padPath t).stronglyMeasurable) hD'.continuous_padPath)
    (isStoppingTime_shiftTime hθ t)

theorem measurable_sX (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1))
    (t : ℝ≥0) :
    Measurable[𝓖R μ (k + 1) t] (F.sX t) ∧ Measurable[𝓖R μ (k + 1) t] (F.sY t) :=
  ⟨measurable_toSeq.comp ((continuous_fst.comp (ofFlat (k + 1)).continuous).measurable.comp
      (F.measurable_Zs hD0 hξ hξc t)),
    measurable_toSeq.comp ((continuous_snd.comp (ofFlat (k + 1)).continuous).measurable.comp
      (F.measurable_Zs hD0 hξ hξc t))⟩

/-- **The glued process is adapted to the glued filtration.** -/
theorem adapted_g (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0)
    (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1))
    (hD' : IsDualFrom P 𝓖 D0 k N' X' Y') (t : ℝ≥0) :
    Measurable[F.gFilt hcomap hD0 hξ hξc t] (F.gN π' N' t) ∧
      Measurable[F.gFilt hcomap hD0 hξ hξc t] (F.gC π' N' F.sX X' t) ∧
      Measurable[F.gFilt hcomap hD0 hξ hξc t] (F.gC π' N' F.sY Y' t) := by
  have hθ := F.measurable_theta hcomap hD0 hξ hξc
  have hW := measurable_shift_padPath hD' hθ t
  have hu : ∀ ω, unpad k (padPath k N' X' Y' (t - F.theta π' ω) ω) =
      (N' (t - F.theta π' ω) ω, truncCoord (N' (t - F.theta π' ω) ω) (X' (t - F.theta π' ω) ω),
        truncCoord (N' (t - F.theta π' ω) ω) (Y' (t - F.theta π' ω) ω)) :=
    fun ω => hD'.unpad_padPath _ ω
  have h2N : Measurable[shiftFilt hθ t] fun ω => N' (t - F.theta π' ω) ω := by
    have := (measurable_fst.comp measurable_unpad).comp hW
    simpa only [Function.comp_def, hu] using this
  have h2X : Measurable[shiftFilt hθ t] fun ω =>
      truncCoord (N' (t - F.theta π' ω) ω) (X' (t - F.theta π' ω) ω) := by
    have := (measurable_snd.fst.comp measurable_unpad).comp hW
    simpa only [Function.comp_def, hu] using this
  have h2Y : Measurable[shiftFilt hθ t] fun ω =>
      truncCoord (N' (t - F.theta π' ω) ω) (Y' (t - F.theta π' ω) ω) := by
    have := (measurable_snd.snd.comp measurable_unpad).comp hW
    simpa only [Function.comp_def, hu] using this
  have h1 := F.measurable_sX hD0 hξ hξc t
  have hc := comap_measurable (m := 𝓖R μ (k + 1) t) π'
  exact ⟨measurable_glueFilt_ite _ _ hθ measurable_const h2N,
    measurable_glueFilt_ite _ _ hθ (h1.1.comp hc) h2X,
    measurable_glueFilt_ite _ _ hθ (h1.2.comp hc) h2Y⟩

/-!
## The top level
-/

omit [MeasurableSpace Ω] in
theorem gN_le (hlev : ∀ t ω, N' t ω ≤ k) (t : ℝ≥0) (ω : Ω) : F.gN π' N' t ω ≤ k + 1 := by
  unfold gN; split_ifs
  · exact le_rfl
  · exact (hlev _ ω).trans (Nat.le_succ k)

omit [MeasurableSpace Ω] in
theorem dualLift_g_top (hlev : ∀ t ω, N' t ω ≤ k) (g : DualCoord (k + 1) → ℝ) (t : ℝ≥0) (ω : Ω) :
    dualLift g (F.gN π' N' t ω) (F.gC π' N' F.sX X' t ω) (F.gC π' N' F.sY Y' t ω) =
      if (t : WithTop ℝ≥0) < F.rho1 (π' ω) then g (ofFlat (k + 1) (F.Zs t (π' ω))) else 0 := by
  by_cases h : (t : WithTop ℝ≥0) < F.rho1 (π' ω)
  · simp only [dualLift, F.gN_of_lt π' N' h, F.gC_of_lt π' N' _ _ h, F.dualCoordOf_sX, h,
      ↓reduceIte]
  · have h' := F.gN_of_le π' N' (not_lt.1 h)
    have hne : F.gN π' N' t ω ≠ k + 1 := by rw [h']; have := hlev (t - F.theta π' ω) ω; omega
    simp only [dualLift, hne, h, ↓reduceIte]

omit [MeasurableSpace Ω] in
/-- The level-`(k+1)` martingale of the glued process is the pulled-back first-stage
martingale. -/
theorem dualMartingale_g_top (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) (hlev : ∀ t ω, N' t ω ≤ k)
    (f : DualCoord (k + 1) → ℝ) (t : ℝ≥0) (ω : Ω) :
    dualMartingale D0 (k + 1) f (F.gN π' N') (F.gC π' N' F.sX X') (F.gC π' N' F.sY Y') t ω =
      F.M1 f t (π' ω) := by
  have hex : ∃ u ≤ t, F.gN π' N' u ω ≤ k + 1 := ⟨0, zero_le, F.gN_le hlev 0 ω⟩
  have hent : dualEntrance (F.gN π' N') (k + 1) ω = 0 := by
    have : {s | F.gN π' N' s ω ≤ k + 1} = univ := eq_univ_of_forall fun s => F.gN_le hlev s ω
    simp only [dualEntrance, this, csInf_univ]; rfl
  simp only [dualMartingale, dualEntranceValue, hex, ↓reduceIte, hent, F.dualLift_g_top hlev,
    WithTop.coe_zero, F.rho1_pos (π' ω), F.Zs_zero hξc, M1, flatT, flatGen]

theorem M1_stop (f : DualCoord (k + 1) → ℝ) {x : ΩR S (k + 1)} {s t : ℝ≥0} (hst : s ≤ t)
    (hs : F.rho1 x ≤ s) : F.M1 f t x = F.M1 f s x := by
  have h1 : ¬ (t : WithTop ℝ≥0) < F.rho1 x := not_lt.2 (hs.trans (WithTop.coe_le_coe.2 hst))
  have h2 : ¬ (s : WithTop ℝ≥0) < F.rho1 x := not_lt.2 hs
  simp only [M1, h1, h2, ↓reduceIte]
  congr 1
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
    (Ioc_subset_Ioc_right (NNReal.coe_le_coe.2 hst)) fun u hu => ?_
  have hsu : s < u.toNNReal := by
    have : (s : ℝ) < u := by
      by_contra h; exact hu.2 ⟨hu.1.1, not_lt.1 h⟩
    exact Real.lt_toNNReal_iff_coe_lt.2 this
  simp only [not_lt.2 (hs.trans (WithTop.coe_le_coe.2 hsu.le)), ↓reduceIte]

/-- **The level-`(k+1)` clause of the glued process.** -/
theorem martingale_g_top (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0)
    (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1))
    [IsProbabilityMeasure P] (hmap : P.map π' = PR μ (k + 1)) (hlev : ∀ t ω, N' t ω ≤ k)
    {f : DualCoord (k + 1) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ dualChamber (k + 1)) :
    Martingale (dualMartingale D0 (k + 1) f (F.gN π' N') (F.gC π' N' F.sX X')
      (F.gC π' N' F.sY Y')) (F.gFilt hcomap hD0 hξ hξc) P := by
  have hM := F.martingale_M1 hD0 hξ hξc hf hfc hfs
  rw [← hmap] at hM
  have e : dualMartingale D0 (k + 1) f (F.gN π' N') (F.gC π' N' F.sX X') (F.gC π' N' F.sY Y') =
      fun t ω => F.M1 f t (π' ω) :=
    funext fun t => funext fun ω => F.dualMartingale_g_top hξc hlev f t ω
  rw [e]
  exact martingale_glue_pre _ _ _ (martingale_comap (measurable_of_comap hcomap) hM)
    fun s t ω hst hs => F.M1_stop f hst hs

/-!
## The lower levels
-/

omit [MeasurableSpace Ω] in
theorem rho_le_entry {q' : ℕ} (hqk : q' ≤ k) (ω : Ω) :
    F.rho1 (π' ω) ≤ entryTime (fun t => F.gN π' N' t ω) q' :=
  le_iInf₂ fun u hu => not_lt.1 fun h => by
    have h' : F.gN π' N' u ω ≤ q' := hu
    rw [F.gN_of_lt π' N' h] at h'; omega

omit [MeasurableSpace Ω] in
theorem dualMartingale_trunc {q : ℕ} (f : DualCoord q → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) :
    dualMartingale D0 q f N (fun t ω => truncCoord (N t ω) (X t ω))
      (fun t ω => truncCoord (N t ω) (Y t ω)) = dualMartingale D0 q f N X Y := by
  funext t ω
  simp only [dualMartingale, dualEntranceValue, dualLift_trunc]

omit [MeasurableSpace Ω] in
/-- The level-`q'` martingale of the glued process (`q' ≤ k`) is the shifted restart one. -/
theorem dualMartingale_g_low (hξc : ∀ s, ξ s ∈ flatChamber (k + 1)) {ω : Ω}
    (hP : IsDeletionPath (fun t => N' t ω) (fun t => X' t ω) (fun t => Y' t ω))
    (h0 : N' 0 ω = k ∧ dualCoordOf k (X' 0 ω) (Y' 0 ω) = ofFlat k (F.surv (π' ω)))
    {q' : ℕ} (hqk : q' ≤ k) {f : DualCoord q' → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber q') (t : ℝ≥0) :
    dualMartingale D0 q' f (F.gN π' N') (F.gC π' N' F.sX X') (F.gC π' N' F.sY Y') t ω =
      if (t : WithTop ℝ≥0) < F.rho1 (π' ω) then 0
      else dualMartingale D0 q' f N' X' Y' (t - F.theta π' ω) ω := by
  have hG := F.isDeletionPath_g hξc hP h0
  have hle := F.rho_le_entry (π' := π') (N' := N') hqk ω
  by_cases ht : (t : WithTop ℝ≥0) < F.rho1 (π' ω)
  · simp only [ht, ↓reduceIte]
    exact dualMartingale_eq_zero_of_le_entry hG (ht.le.trans hle)
  · simp only [ht, ↓reduceIte]
    set r := F.theta π' ω
    have hr : (r : WithTop ℝ≥0) = F.rho1 (π' ω) :=
      coe_untopA_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (not_lt.1 ht))
    have hrt : r ≤ t := WithTop.coe_le_coe.1 (hr ▸ not_lt.1 ht)
    have hrs : ∀ s : ℝ≥0, F.rho1 (π' ω) ≤ r + s := fun s =>
      hr ▸ WithTop.coe_le_coe.2 le_self_add
    have hN : ∀ s, N' s ω = F.gN π' N' (r + s) ω := fun s => by
      rw [F.gN_of_le π' N' (hrs s), add_tsub_cancel_left]
    have hC : ∀ (Z : ℝ≥0 → ΩR S (k + 1) → ℕ → ℝ) (X'' : ℝ≥0 → Ω → ℕ → ℝ) (s : ℝ≥0),
        truncCoord (N' s ω) (X'' s ω) =
          truncCoord (F.gN π' N' (r + s) ω) (F.gC π' N' Z X'' (r + s) ω) := fun Z X'' s => by
      rw [F.gN_of_le π' N' (hrs s), F.gC_of_le π' N' X'' Z (hrs s), add_tsub_cancel_left,
        truncCoord_idem]
    have hsh := dualMartingale_shift (D0 := D0) hG hf hfc hfs (r := r) (hr ▸ hle)
      (N' := N') (X' := fun s ω => truncCoord (N' s ω) (X' s ω))
      (Y' := fun s ω => truncCoord (N' s ω) (Y' s ω)) (ω' := ω) hN (hC _ X') (hC _ Y') (t - r)
    have hzero : dualMartingale D0 q' f (F.gN π' N') (F.gC π' N' F.sX X') (F.gC π' N' F.sY Y')
        r ω = 0 := dualMartingale_eq_zero_of_le_entry hG (by rw [hr]; exact hle)
    rw [dualMartingale_trunc, add_tsub_cancel_of_le hrt, hzero, sub_zero] at hsh
    exact hsh.symm

/-- **The level-`q'` clauses of the glued process** (`1 ≤ q' ≤ k`). -/
theorem martingale_g_low (hcomap : MeasurableSpace.comap π' inferInstance ≤ 𝓖 0)
    (hD0 : 0 < D0) (hξ : Measurable ξ) (hξc : ∀ s, ξ s ∈ flatChamber (k + 1))
    (hD' : IsDualFrom P 𝓖 D0 k N' X' Y')
    (h0 : ∀ ω, N' 0 ω = k ∧ dualCoordOf k (X' 0 ω) (Y' 0 ω) = ofFlat k (F.surv (π' ω)))
    {q' : ℕ} (hq : 1 ≤ q') (hqk : q' ≤ k) {f : DualCoord q' → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ dualChamber q') :
    Martingale (dualMartingale D0 q' f (F.gN π' N') (F.gC π' N' F.sX X')
      (F.gC π' N' F.sY Y')) (F.gFilt hcomap hD0 hξ hξc) P := by
  have := hD'.prob
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by simp)
  have e : dualMartingale D0 q' f (F.gN π' N') (F.gC π' N' F.sX X') (F.gC π' N' F.sY Y') =
      fun (t : ℝ≥0) ω => if (t : WithTop ℝ≥0) < F.rho1 (π' ω) then 0
        else dualMartingale D0 q' f N' X' Y' (t - F.theta π' ω) ω :=
    funext fun t => funext fun ω =>
      F.dualMartingale_g_low hξc (hD'.paths ω) (h0 ω) hqk hf2 hfc hfs t
  rw [e]
  exact martingale_glue_post _ _ _ (hD'.martingale q' hq hqk f hf hfc hfs)
    (fun ω t => ((continuous_dualMartingale (hD'.paths ω) D0 hq hf2 hfc hfs).tendsto t).mono_left
      nhdsWithin_le_nhds)
    (abs_dualMartingale_le (D0 := D0) (N := N') (X := X') (Y := Y') hf2 hfc hfs)
    (fun ω => dualMartingale_eq_zero_of_le_entry (hD'.paths ω)
      (by rw [WithTop.coe_zero]; exact bot_le))

end B1R

end BlockBand.Transmission.Dual.G
