module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWMom
public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWTime
public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWMeasObs

/-!
# The prelimit process along one path

* `gramJ_zero`; `born_iff_of_ne`: off the birth cells the discrete births before
  `⌊W(s + r)⌋` are those with `τ_i − s ≤ r`; `jumps_eq_of_ne` (both jumps agree).
* **`stZKObs_eq_zeta`**: where the jumps agree, the drift-free state of `b3ObsAll` is `zeta`.
* `adm_stZKObs`: the states of `b3ObsAll` are admissible (any time).
* **`genObs_sub_eq`**: for `W ≥ 1` and off-birth endpoints where the jumps agree,
  `M(t') − M(t) = Σ_{n ≤ j < n'} dStep_j + err`, `|err| ≤ 2 C_Λ (2 + 2 np)/W`
  (KT's `norm_integral_sub_sum_le`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

open MeasureTheory Finset Filter Matrix
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal Topology NNReal

variable {W np K : ℕ}

theorem gramJ_zero {b s : ℝ} {τ m : Fin np → ℝ} (hτ : ∀ j, s < τ j) :
    gramJ (K := K) b s τ m 0 = 0 := by
  unfold gramJ birthJump
  refine Finset.sum_eq_zero fun j _ => ite_eq_right_iff.2 fun h' => absurd h' (not_le.2 (by
    simp only [NNReal.coe_zero]; linarith [hτ j]))

theorem limLenAll_zero (s : ℝ) (W : ℕ) : limLenAll s W 0 = closeLen s W := by
  simp [limLenAll]

/-- Off the birth cells, the discrete births before `⌊W(s + r)⌋` are those with `τ_i − s ≤ r`. -/
theorem born_iff_of_ne {s : ℝ} (hs : 0 ≤ s) {τ : Fin np → ℝ} (hsτ : ∀ j, s < τ j) {W : ℕ}
    (hW : 0 < W)
    {r : ℝ} (hr : 0 ≤ r) (hne : ∀ i, ⌊(W : ℝ) * (s + r)⌋₊ ≠ ⌊(W : ℝ) * τ i⌋₊) (i : Fin np) :
    ⌊(W : ℝ) * τ i⌋₊ ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * (s + r)⌋₊ ↔ τ i - s ≤ r := by
  have hW' : (0 : ℝ) < W := by exact_mod_cast hW
  have hlo : closeLen s W ≤ ⌊(W : ℝ) * τ i⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (hsτ i).le (Nat.cast_nonneg W))
  simp only [Finset.mem_Ico]
  rcases lt_or_gt_of_ne (hne i) with hlt | hgt
  · -- the birth cell is after the current one
    constructor
    · intro h; omega
    · intro h
      exfalso
      have h1 : (W : ℝ) * τ i ≤ (W : ℝ) * (s + r) := mul_le_mul_of_nonneg_left (by linarith) hW'.le
      have := Nat.floor_mono h1
      omega
  · constructor
    · intro _
      have h1 : ((⌊(W : ℝ) * τ i⌋₊ : ℕ) : ℝ) + 1 ≤ ⌊(W : ℝ) * (s + r)⌋₊ := by exact_mod_cast hgt
      have h2 := Nat.lt_floor_add_one ((W : ℝ) * τ i)
      have h3 := Nat.floor_le (mul_nonneg hW'.le (by linarith : 0 ≤ s + r))
      have : (W : ℝ) * τ i < (W : ℝ) * (s + r) := by linarith
      have := lt_of_mul_lt_mul_left this hW'.le
      linarith
    · intro _; exact ⟨hlo, hgt⟩

theorem jumps_eq_of_ne {b E s : ℝ} (hs : 0 ≤ s) {τ m : Fin np → ℝ} (hsτ : ∀ j, s < τ j) {W : ℕ}
    (hW : 0 < W)
    {r : ℝ} (hr : 0 ≤ r) (hne : ∀ i, ⌊(W : ℝ) * (s + r)⌋₊ ≠ ⌊(W : ℝ) * τ i⌋₊) :
    b3JumpAt (K := K) b s τ m W ⌊(W : ℝ) * (s + r)⌋₊ = gramJ b s τ m r.toNNReal ∧
      b3KJumpAt E s τ m W ⌊(W : ℝ) * (s + r)⌋₊ = kJ E s τ m r.toNNReal := by
  have hb := born_iff_of_ne hs hsτ hW hr hne
  have hc : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr
  constructor
  · rw [Fdd.b3JumpAt_eq_sum, gramJ, birthJump]
    exact Finset.sum_congr rfl fun i _ => by simp only [hb i, hc]
  · rw [Fdd.b3KJumpAt_eq_sum, kJ, kBirthJump]
    exact Finset.sum_congr rfl fun i _ => by simp only [hb i, hc]

section Obs

variable (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
  (Vs : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ)

theorem gOfObs_b3 (u : ℝ≥0) (y : ProbedPath W np × ℝ) :
    gOfObs (b3ObsAll b E s h τ m W Vs) u y =
      b3ClosedGramAt b E s h τ m W (limLenAll s W u) Vs y :=
  gramOfEntries_gramEntry _

theorem kOfObs_b3 (u : ℝ≥0) (y : ProbedPath W np × ℝ) :
    kOfObs (b3ObsAll b E s h τ m W Vs) u y = b3ClosedKAt b E s h τ m W (limLenAll s W u) y := by
  ext i k; rfl

/-- **Where the jumps agree, the state of `b3ObsAll` is the discrete state.** -/
theorem stZKObs_eq_zeta (hτ : ∀ j, s < τ j) (u : ℝ≥0) (y : ProbedPath W np × ℝ)
    (hG : b3JumpAt (K := K) b s τ m W (limLenAll s W u) = gramJ b s τ m u)
    (hK : b3KJumpAt E s τ m W (limLenAll s W u) = kJ E s τ m u) :
    stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) u y =
      zeta b E s h τ m W Vs (limLenAll s W u) y := by
  simp only [stZKObs, zeta, gOfObs_b3, kOfObs_b3, limLenAll_zero, gramJ_zero hτ, kJ_zero hτ,
    sub_zero, ← hG, ← hK]

/-- The states of `b3ObsAll` are admissible. -/
theorem adm_stZKObs (u : ℝ≥0) (y : ProbedPath W np × ℝ) :
    Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m)
      (stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) u y) := by
  have hC := cJump_nonneg b m
  have hn : (0 : ℝ) ≤ Fintype.card (SrcCol K (Fin np)) := Nat.cast_nonneg _
  have key : ∀ (G J : GSt K np), (∀ e, ‖gramEntry e G‖ ≤ trRe G) →
      (∀ e, ‖gramEntry e J‖ ≤ cJump b m) → ∀ e, ‖gramEntry e (G - J)‖ ≤
        |trRe (G - J)| + ((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m := by
    intro G J hG hJ e
    have h3 := abs_trRe_le J
    have h4 : ∑ k : SrcCol K (Fin np), ‖gramEntry ((0 : Fin 2), k, k) J‖ ≤
        (Fintype.card (SrcCol K (Fin np)) : ℝ) * cJump b m := by
      have := Finset.sum_le_card_nsmul (univ : Finset (SrcCol K (Fin np)))
        (fun k => ‖gramEntry ((0 : Fin 2), k, k) J‖) (cJump b m) (fun k _ => hJ _)
      simpa [nsmul_eq_mul] using this
    rw [gramEntry_sub', trRe_sub]
    refine (norm_sub_le _ _).trans ?_
    have h6 := le_abs_self (trRe G - trRe J)
    have h7 := le_abs_self (trRe J)
    linarith [hG e, hJ e]
  refine ⟨key _ _ (fun e => ?_) (norm_gramEntry_gramJ_le b s τ m u), key _ _ (fun e => ?_)
    (norm_gramEntry_gramJ_le b s τ m 0), fun a => rfl⟩
  · rw [gOfObs_b3]; exact norm_gramEntry_b3ClosedGramAt_le b E s h τ m W _ Vs y e
  · rw [gOfObs_b3]; exact norm_gramEntry_b3ClosedGramAt_le b E s h τ m W _ Vs y e

variable {b E s h τ m W Vs}

/-- The time-integral bound along one path (KT's `norm_integral_sub_sum_le`). -/
theorem norm_integral_lam_sub_le (hs : 0 ≤ s) (hτ : ∀ j, s < τ j) (hW : 0 < W)
    (hV : Measurable Vs) {Λ : GSt K np × ZK K np → ℂ} (hΛ : Continuous Λ) {CΛ : ℝ}
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z → ‖Λ (J, z)‖ ≤ CΛ)
    (y : ProbedPath W np × ℝ) (v : ℝ≥0) :
    ‖(∫ r in Set.Ioc (0 : ℝ) v, Λ (gramJ b s τ m r.toNNReal,
        stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) r.toNNReal y)) -
      ∑ j ∈ Finset.Ico (closeLen s W) (limLenAll s W v),
        Λ (b3JumpAt b s τ m W j, zeta b E s h τ m W Vs j y) / (W : ℂ)‖ ≤
      CΛ * (2 + 2 * np) / W := by
  have ho := measurable_uncurry_b3ObsAll_of_measurable (b := b) (E := E) (s := s) (h := h)
    (τ := τ) (m := m) hV
  have hfm : Measurable fun r : ℝ => Λ (gramJ b s τ m r.toNNReal,
      stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) r.toNNReal y) := by
    have hx : Measurable fun r : ℝ => Core.xv cK (b3ObsAll b E s h τ m W Vs) r.toNNReal y :=
      (Core.measurable_xv ho cK).comp (measurable_id.prodMk (measurable_const (a := y)))
    have h1 := (measurable_gL (b := b) (E := E) (s := s) (τ := τ) (m := m) hΛ).comp
      (measurable_real_toNNReal.prodMk (hx.prodMk
        (measurable_const (a := Core.xv cK (b3ObsAll b E s h τ m W Vs) 0 y))))
    have e : (fun r : ℝ => Λ (gramJ b s τ m r.toNNReal,
        stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) r.toNNReal y)) =
        (fun q : ℝ≥0 × (KCo K np → ℂ) × (KCo K np → ℂ) => gL b E s τ m Λ q.1 q.2.1 q.2.2) ∘
          (fun r : ℝ => (r.toNNReal, Core.xv cK (b3ObsAll b E s h τ m W Vs) r.toNNReal y,
            Core.xv cK (b3ObsAll b E s h τ m W Vs) 0 y)) := by
      funext r; simp only [Function.comp, gL, stZKObs_eq]
    rw [e]; exact h1
  refine norm_integral_sub_sum_le hW hs (fun i => ⌊(W : ℝ) * τ i⌋₊) hfm
    (fun r => hCΛ _ _ (norm_gramEntry_gramJ_le b s τ m _) (adm_stZKObs b E s h τ m W Vs _ y))
    (fun j => hCΛ _ _ (norm_gramEntry_b3JumpAt_le b s τ m W j) (adm_zeta b E s h τ m W Vs j y))
    (fun r hr hne => ?_) v v.2
  have hl : limLenAll s W r.toNNReal = ⌊(W : ℝ) * (s + r)⌋₊ := by
    simp [limLenAll, Real.coe_toNNReal r hr]
  obtain ⟨hG, hK⟩ := jumps_eq_of_ne (K := K) (b := b) (E := E) (m := m) hs hτ hW hr hne
  rw [stZKObs_eq_zeta b E s h τ m W Vs hτ r.toNNReal y (by rw [hl, hG]) (by rw [hl, hK]), hl, hG]

/-- **The prelimit increment is the sum of the steps, up to the time grid.** -/
theorem genObs_sub_eq (hs : 0 ≤ s) (hτ : ∀ j, s < τ j) (hW : 0 < W) (hV : Measurable Vs)
    {χ ξ : ℝ → ℝ} (hχ : ContDiff ℝ 3 χ) (hξ : ContDiff ℝ 3 ξ) (κ : KTest K np) {CΛ : ℝ}
    (hCΛ : ∀ (J : GSt K np) (z : ZK K np), (∀ e, ‖gramEntry e J‖ ≤ cJump b m) →
      Adm (((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m) z →
      ‖κ.lam χ ξ b E (J, z)‖ ≤ CΛ)
    {t t' : ℝ≥0} (htt : t ≤ t')
    (hGt : b3JumpAt (K := K) b s τ m W (limLenAll s W t) = gramJ b s τ m t)
    (hKt : b3KJumpAt E s τ m W (limLenAll s W t) = kJ E s τ m t)
    (hGt' : b3JumpAt (K := K) b s τ m W (limLenAll s W t') = gramJ b s τ m t')
    (hKt' : b3KJumpAt E s τ m W (limLenAll s W t') = kJ E s τ m t') (y : ProbedPath W np × ℝ) :
    ‖(genObs b E s τ m (b3ObsAll b E s h τ m W Vs) (κ.fn χ ξ) (κ.lam χ ξ b E) t' y -
        genObs b E s τ m (b3ObsAll b E s h τ m W Vs) (κ.fn χ ξ) (κ.lam χ ξ b E) t y) -
      ∑ j ∈ Finset.Ico (limLenAll s W t) (limLenAll s W t'), dStep b E s h τ m W Vs χ ξ κ j y‖ ≤
      2 * (CΛ * (2 + 2 * np) / W) := by
  obtain ⟨hχc, hχd, hχdd⟩ := cut_continuity hχ
  obtain ⟨hξc, hξd, hξdd⟩ := cut_continuity hξ
  have hΛ := κ.continuous_lam hχc hχd hχdd hξc hξd hξdd b E
  have h1 := norm_integral_lam_sub_le (E := E) (h := h) hs hτ hW hV hΛ hCΛ y t
  have h2 := norm_integral_lam_sub_le (E := E) (h := h) hs hτ hW hV hΛ hCΛ y t'
  have hn0 : closeLen s W ≤ limLenAll s W t := le_limLenAll s W t
  have hnn : limLenAll s W t ≤ limLenAll s W t' :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (by simpa using htt) (Nat.cast_nonneg W))
  set g : ℕ → ℂ := fun j => κ.lam χ ξ b E (b3JumpAt b s τ m W j, zeta b E s h τ m W Vs j y)
  have hsplit : ∑ j ∈ Finset.Ico (closeLen s W) (limLenAll s W t'), g j / (W : ℂ) =
      ∑ j ∈ Finset.Ico (closeLen s W) (limLenAll s W t), g j / (W : ℂ) +
        ∑ j ∈ Finset.Ico (limLenAll s W t) (limLenAll s W t'), g j / (W : ℂ) :=
    (Finset.sum_Ico_consecutive _ hn0 hnn).symm
  have htele : ∑ j ∈ Finset.Ico (limLenAll s W t) (limLenAll s W t'),
      dStep b E s h τ m W Vs χ ξ κ j y =
        κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W t') y) -
          κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W t) y) -
          ∑ j ∈ Finset.Ico (limLenAll s W t) (limLenAll s W t'), g j / (W : ℂ) := by
    have hd : ∀ j, dStep b E s h τ m W Vs χ ξ κ j y =
        (κ.fn χ ξ (zeta b E s h τ m W Vs (j + 1) y) - κ.fn χ ξ (zeta b E s h τ m W Vs j y)) -
          g j / (W : ℂ) := fun j => by simp only [dStep, g, div_eq_inv_mul]
    rw [Finset.sum_congr rfl fun j _ => hd j, Finset.sum_sub_distrib,
      sum_Ico_tele (fun j => κ.fn χ ξ (zeta b E s h τ m W Vs j y)) hnn]
  have hF : ∀ v : ℝ≥0, b3JumpAt (K := K) b s τ m W (limLenAll s W v) = gramJ b s τ m v →
      b3KJumpAt E s τ m W (limLenAll s W v) = kJ E s τ m v →
      κ.fn χ ξ (stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) v y) =
        κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W v) y) := fun v hG hK => by
    rw [stZKObs_eq_zeta b E s h τ m W Vs hτ v y hG hK]
  simp only [genObs]
  rw [hF t hGt hKt, hF t' hGt' hKt', htele]
  set I1 := ∫ r in Set.Ioc (0 : ℝ) t, κ.lam χ ξ b E (gramJ b s τ m r.toNNReal,
    stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) r.toNNReal y)
  set I2 := ∫ r in Set.Ioc (0 : ℝ) t', κ.lam χ ξ b E (gramJ b s τ m r.toNNReal,
    stZKObs b E s τ m (b3ObsAll b E s h τ m W Vs) r.toNNReal y)
  set S1 := ∑ j ∈ Finset.Ico (closeLen s W) (limLenAll s W t), g j / (W : ℂ)
  set S2 := ∑ j ∈ Finset.Ico (limLenAll s W t) (limLenAll s W t'), g j / (W : ℂ)
  rw [hsplit] at h2
  have e : κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W t') y) - I2 -
      (κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W t) y) - I1) -
      (κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W t') y) -
        κ.fn χ ξ (zeta b E s h τ m W Vs (limLenAll s W t) y) - S2) =
      (I1 - S1) - (I2 - (S1 + S2)) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

end Obs

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW
