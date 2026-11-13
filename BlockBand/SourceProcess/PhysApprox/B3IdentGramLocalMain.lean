module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalFix
public import BlockBand.SourceProcess.PhysApprox.GramMom.Main

/-!
# The local Gram passage at large `W`: `GramPassLocalLarge`

The endpoint constant is `R₀ = |R_χ| + C_T + 1`, with `C_T` bounding the traces of the jump values.

Measure: `closedLaw b W np`. Inputs: the antecedents of `GramPassLocalLarge`
(`ComplexClosedSummed`, `ComplexClosedLindeberg`), the Gram moment theorems
(`gramMomSumCube_holds`, `gramMomSingle_holds`, `condExpReplace_holds`) and finite-`W`
feasibility (`complexClosedFeasible_holds`).

* `eventually_not_birth`: a time off the birth times has a birth-free length for large `W`;
* **`gramPassLocalLarge_holds : GramPassLocalLarge`**: at the horizon `T_H = max T (s + t + 1)`,
  `fixedW_bound` bounds `‖pStopSum‖ₑ` by summed errors tending to `0` and deterministic terms
  tending to `C ε` (`ε` the moduli of uniform continuity of `F`, `Λ` on the boxes).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath BlockBand.SourceProcess.ClosedSum
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2
open scoped NNReal ENNReal

variable {K np : ℕ}

/-- **Off the birth times, the length is eventually birth-free.** -/
theorem eventually_not_birth {s : ℝ} (hs : 0 ≤ s) {τ : Fin np → ℝ} (hτ : ∀ i, 0 < τ i)
    {u : ℝ≥0} (hu : u ∉ birthTimes s τ) :
    ∀ᶠ W : ℕ in atTop, ¬ IsBirthStep τ W (limLenAll s W u) := by
  have hi : ∀ i, ∀ᶠ W : ℕ in atTop, ⌊(W : ℝ) * τ i⌋₊ ≠ limLenAll s W u := fun i => by
    have hne : s + (u : ℝ) ≠ τ i := fun h => hu ⟨i, h⟩
    have hd : 0 < |τ i - (s + u)| := abs_pos.2 (sub_ne_zero.2 hne.symm)
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / |τ i - (s + u)|)
    filter_upwards [eventually_ge_atTop N] with W hW heq
    have hWr : (N : ℝ) ≤ W := by exact_mod_cast hW
    have h1 : 1 < (W : ℝ) * |τ i - (s + u)| := by
      rw [div_lt_iff₀ hd] at hN; nlinarith
    have hx : 0 ≤ (W : ℝ) * τ i := mul_nonneg (Nat.cast_nonneg W) (hτ i).le
    have hy : 0 ≤ (W : ℝ) * (s + u) := mul_nonneg (Nat.cast_nonneg W) (by positivity)
    have a1 := Nat.floor_le hx
    have a2 := Nat.lt_floor_add_one ((W : ℝ) * τ i)
    have b1 := Nat.floor_le hy
    have b2 := Nat.lt_floor_add_one ((W : ℝ) * (s + u))
    unfold limLenAll at heq
    rw [heq] at a1 a2
    have : |(W : ℝ) * τ i - W * (s + u)| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg W)] at this
    linarith
  filter_upwards [eventually_all.2 hi] with W hW ⟨i, h⟩
  exact hW i h

/-- **`GramPassLocalLarge`.** -/
theorem gramPassLocalLarge_holds : GramPassLocalLarge := by
  intro _hTL hS _hT _hK hL b E np τ m T s h K Vs hD χ h3 hcs F Λ hp
  obtain ⟨hχc, hFc, hΛc, Rχ, hRχ, hFv, hΛv⟩ := hp.data h3 hcs
  obtain ⟨td⟩ := IsGenPair.taylorData h3 hcs hp
  obtain ⟨⟨_, hb2, hE1, hE2, -, hτ0, -, -⟩, hs0, hτ, -, -, hVs⟩ := id hD
  have hb : b < 1 := by linarith
  have hs : 0 ≤ s := hs0.le
  obtain ⟨CJ, hCJ0, hCJb⟩ := exists_jSet_bound (K := K) b m
  set nc : ℝ := (Fintype.card (SrcCol K (Fin np)) : ℝ)
  have hnc : 0 ≤ nc := Nat.cast_nonneg _
  have hCT : ∀ J ∈ jSet (K := K) b m, trRe J ≤ nc * CJ := fun J hJ =>
    (le_abs_self _).trans (hCJb J hJ).2
  refine ⟨|Rχ| + nc * CJ + 1, fun R hR a t hat ha ht r i u hu hub φ => ?_⟩
  have hRR : Rχ + nc * CJ < R := by linarith [le_abs_self Rχ]
  have hR0 : 0 ≤ R := by
    have : 0 ≤ nc * CJ := mul_nonneg hnc hCJ0
    linarith [abs_nonneg Rχ]
  have hCJ : ∀ J ∈ jSet (K := K) b m, ∀ e, ‖gramEntry e J‖ ≤ CJ := fun J hJ => (hCJb J hJ).1
  -- the constants
  obtain ⟨CA, hCA0, hCA⟩ := exists_bound_lamA (K := K) (b := b) (m := m) hχc hRχ E
  set BA := CA * t
  have hBA0 : 0 ≤ BA := by positivity
  set B₁ := 2 * (2 * R + CJ) + BA
  set B := max B₁ CA
  have hB₁ : 0 ≤ B₁ := by positivity
  have hB : 0 ≤ B := le_max_of_le_left hB₁
  obtain ⟨Crest, hCr0, hC⟩ := td.rest B hB
  have hca1 : ∀ c : GIdx K np, ∃ C : ℝ, ∀ J ∈ jSet (K := K) b m,
      ∀ q ∈ kBox (K := K) (np := np) B₁ ×ˢ Icc (0 : ℝ) 1, ‖td.a1 (J, q) c‖ ≤ C := fun c =>
    exists_bound_finite_compact (td.ca1 c) (jSet_finite b m)
      ((isCompact_kBox B₁).prod isCompact_Icc)
  have hca2 : ∀ c c' : GIdx K np, ∃ C : ℝ, ∀ J ∈ jSet (K := K) b m,
      ∀ q ∈ kBox (K := K) (np := np) B₁ ×ˢ Icc (0 : ℝ) 1, ‖td.a2 (J, q) c c'‖ ≤ C := fun c c' =>
    exists_bound_finite_compact (td.ca2 c c') (jSet_finite b m)
      ((isCompact_kBox B₁).prod isCompact_Icc)
  choose C1 hC1 using hca1
  choose C2 hC2 using hca2
  set Ca := ∑ c, |C1 c| + ∑ c, ∑ c', |C2 c c'|
  have hCa0 : 0 ≤ Ca := by positivity
  have hCa1 : ∀ c, ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) B₁,
      ∀ ℓ ∈ Icc (0 : ℝ) 1, ‖td.a1 (J, z, ℓ) c‖ ≤ Ca := fun c J hJ z hz ℓ hℓ => by
    refine (hC1 c J hJ (z, ℓ) ⟨hz, hℓ⟩).trans ((le_abs_self _).trans ?_)
    refine (Finset.single_le_sum (f := fun c => |C1 c|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ c)).trans (le_add_of_nonneg_right (by positivity))
  have hCa2 : ∀ c c', ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) B₁,
      ∀ ℓ ∈ Icc (0 : ℝ) 1, ‖td.a2 (J, z, ℓ) c c'‖ ≤ Ca := fun c c' J hJ z hz ℓ hℓ => by
    refine (hC2 c c' J hJ (z, ℓ) ⟨hz, hℓ⟩).trans ((le_abs_self _).trans ?_)
    refine le_trans ?_ (le_add_of_nonneg_left (by positivity))
    refine (Finset.single_le_sum (f := fun c' => |C2 c c'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ c')).trans ?_
    exact Finset.single_le_sum (f := fun c => ∑ c', |C2 c c'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c)
  obtain ⟨CΓ', hCΓ'⟩ := exists_bound_finite_compact td.cΓ (jSet_finite (K := K) b m)
    (isCompact_kBox (K := K) (np := np) B₁)
  set CΓ := max CΓ' 0
  have hCΓ0 : 0 ≤ CΓ := le_max_right _ _
  have hCΓ : ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) B₁, ‖td.Γ (J, z)‖ ≤ CΓ :=
    fun J hJ z hz => (hCΓ' J hJ z hz).trans (le_max_left _ _)
  have hβb : ∀ c c' : GIdx K np, ∃ C : ℝ, ∀ G ∈ {G : GSt K np | ∀ e : GIdx K np,
      ‖gramEntry e G‖ ≤ 2 * R}, ‖cDrift b E (Sum.inl c : CIdx K np) G‖ +
        ‖cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') G‖ ≤ C := fun c c' =>
    (isCompact_box (2 * R)).exists_bound_of_continuousOn
      (((ClosedLimit.continuous_gramDriftEntry _ _ c).norm.add
        (ClosedLimit.continuous_gramCovEntry _ _ c c').norm).continuousOn) |>.imp
      fun C hC G hG => (le_abs_self _).trans (by
        have := hC G hG
        rw [Real.norm_eq_abs] at this
        exact this)
  choose Cb hCb using hβb
  set Cβ := ∑ c, ∑ c', |Cb c c'|
  have hCβ : ∀ G : GSt K np, GramFeasible (srcSignature K (Fin np)) G → trRe G < R →
      ∀ c c' : GIdx K np, ‖cDrift b E (Sum.inl c : CIdx K np) G‖ ≤ Cβ ∧
        ‖cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') G‖ ≤ Cβ := fun G hG hGR c c' => by
    have hbox : G ∈ {G : GSt K np | ∀ e : GIdx K np, ‖gramEntry e G‖ ≤ 2 * R} := fun e =>
      (ModelExist.norm_gramEntry_le_of_feasible hG e).trans (by unfold trRe at hGR; linarith)
    have h1 := hCb c c' G hbox
    have h2 : |Cb c c'| ≤ Cβ := (Finset.single_le_sum (f := fun c' => |Cb c c'|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ c')).trans
      (Finset.single_le_sum (f := fun c => ∑ c', |Cb c c'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ c))
    have h3 := le_abs_self (Cb c c')
    exact ⟨by linarith [norm_nonneg (cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') G)],
      by linarith [norm_nonneg (cDrift b E (Sum.inl c : CIdx K np) G)]⟩
  obtain ⟨CH, -, hCHb⟩ := exists_uniform_bound (b := b) (E := E) (s := s) (τ := τ) (m := m)
    hχc hRχ hFc hΛc hFv hΛv t
  obtain ⟨CF, hCF0, hCFb⟩ := exists_bound_stateOf (K := K) (b := b) (m := m)
    (G := fun p : GSt K np × ZSt K np => F p.2) (hFc.comp continuous_snd)
    (fun p hp => hFv p.2 hp) BA
  obtain ⟨CL, hCL0, hCLb⟩ := exists_bound_stateOf (K := K) (b := b) (m := m) (G := Λ) hΛc hΛv BA
  -- the horizon
  set TH := max T (s + t + 1)
  have hD' := Fdd.frameDomain_mono hD (le_max_left T (s + t + 1))
  have hTH : s + t + 1 ≤ TH := le_max_right _ _
  -- pathwise bounds along feasible paths
  have hBA : ∀ (W : ℕ) (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) y,
      FeasPath b E s h τ m W V y → ∀ v ≤ t, ∀ e,
        ‖genA χ b E s τ m (pG b E s h τ m W V) e v y‖ ≤ BA := fun W V y hy v hv e =>
    norm_genA_le hCA0 hCA hy e (T₁ := t) (NNReal.coe_le_coe.2 hv)
  have hfeasu : ∀ (W : ℕ) (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) y,
      FeasPath b E s h τ m W V y → ∀ u : ℝ≥0,
        GramFeasible (srcSignature K (Fin np)) (pG b E s h τ m W V u y) := fun W V y hy u =>
    hy _ (closeLen_le_limLenAll _)
  have hCH : ∀ (W : ℕ) (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) y,
      FeasPath b E s h τ m W V y → ∀ v ≤ t, ‖pM χ b E s h τ m W V F Λ v y‖ ≤ CH :=
    fun W V y hy v hv => hCHb _ (pG b E s h τ m W V) y (hfeasu W V y hy) v hv
  have hCF : ∀ (W : ℕ) (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) y,
      FeasPath b E s h τ m W V y → ∀ v ≤ t,
        ‖F (stZ χ b E s τ m (pG b E s h τ m W V) v y)‖ ≤ CF ∧
          ‖F (zHat χ b E s h τ m W V v y)‖ ≤ CF := fun W V y hy v hv => by
    have hα := hBA W V y hy v hv
    refine ⟨?_, ?_⟩
    · rw [stZ_eq_stateOf]
      exact hCFb _ (gramJ_mem_jSet b s τ m 0) _ _ _ _ _ (hy _ (closeLen_le_limLenAll _))
        (hy _ (closeLen_le_limLenAll _)) (gramJ_mem_jSet b s τ m v) (gramJ_mem_jSet b s τ m 0) hα
    · rw [zHat_eq_stateOf]
      exact hCFb _ (gramJ_mem_jSet b s τ m 0) _ _ _ _ _ (hy _ (closeLen_le_limLenAll _))
        (hy _ (closeLen_le_limLenAll _)) (b3JumpAt_mem_jSet b s τ m W _)
        (gramJ_mem_jSet b s τ m 0) hα
  have hCL : ∀ (W : ℕ) (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) y,
      FeasPath b E s h τ m W V y → ∀ r ∈ Ioc (0 : ℝ) t,
        ‖lInt χ b E s h τ m W V Λ y r‖ ≤ CL := fun W V y hy r hr => by
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hr.2
    unfold lInt
    rw [stZ_eq_stateOf]
    exact hCLb _ (gramJ_mem_jSet b s τ m _) _ _ _ _ _ (hy _ (closeLen_le_limLenAll _))
      (hy _ (closeLen_le_limLenAll _)) (gramJ_mem_jSet b s τ m _) (gramJ_mem_jSet b s τ m 0)
      (hBA W V y hy _ hrt)
  -- the limit
  rw [tendsto_zero_iff_enorm_tendsto_zero, ENNReal.tendsto_nhds_zero]
  intro ε' hε'
  obtain ⟨ρ, hρ0, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hε'
  have hρ0' : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  set Φ := ‖φ‖
  set c0 := Φ * ((t + 2) + ((np : ℝ) + 2)) + 1
  have hc0 : 0 < c0 := by positivity
  set ε : ℝ := (ρ : ℝ) / (2 * c0)
  have hε : 0 < ε := by positivity
  obtain ⟨K₀, hK0, hFcl⟩ := exists_close_F (K := K) (np := np) hFc hB₁ hCF0 hε
  obtain ⟨δΛ, hδΛ, hΛcl⟩ := exists_close_Λ (K := K) (np := np) hΛc (b := b) (m := m) hB₁ hε
  set N : ℝ := (Fintype.card (GIdx K np) : ℝ)
  -- the deterministic terms
  set g1 : ℝ → ℝ := fun w => (t + 2) * (Φ * (Crest * (4 * w ^ 2 * B ^ 3 + 8 * w ^ 3 * B ^ 4) +
    (w * CΓ + ε)))
  set g2 : ℝ → ℝ := fun w => ((np : ℝ) + 2) * (Φ * (ε + K₀ * (N * CA * w) + CL * w))
  have hg1 : Tendsto (fun W : ℕ => g1 (W : ℝ)⁻¹) atTop (𝓝 (g1 0)) :=
    ((by fun_prop : Continuous g1).tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
  have hg2 : Tendsto (fun W : ℕ => g2 (W : ℝ)⁻¹) atTop (𝓝 (g2 0)) :=
    ((by fun_prop : Continuous g2).tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
  have hg10 : g1 0 = (t + 2) * (Φ * ε) := by simp [g1]
  have hg20 : g2 0 = ((np : ℝ) + 2) * (Φ * ε) := by simp [g2]
  have hL0 : g1 0 + g2 0 < ρ := by
    rw [hg10, hg20]
    have : ((t : ℝ) + 2) * (Φ * ε) + ((np : ℝ) + 2) * (Φ * ε) = (c0 - 1) * ε := by
      simp only [c0]; ring
    rw [this]
    have h1 : (c0 - 1) * ε < c0 * ε := by nlinarith
    have h2 : c0 * ε = (ρ : ℝ) / 2 := by simp only [ε]; field_simp
    linarith
  -- the summed errors
  have hSum := fun c c' : GIdx K np =>
    (hS b E np τ m TH s h K Vs hD' R).1 (Sum.inl c) (Sum.inl c')
  have hCube := fun c : GIdx K np => gramMomSumCube_holds hS hL b E np τ m TH s h K Vs hD' R c
  have hLind := fun c : GIdx K np => hL b E np τ m TH s h K Vs hD' R (Sum.inl c)
  have hpB : ∀ᶠ W : ℕ in atTop, limLenAll s W a ∈ nbSteps s TH τ W := by
    filter_upwards [eventually_not_birth hs hτ0 ha, eventually_ge_atTop 1] with W hW hW1
    refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨closeLen_le_limLenAll _, ?_⟩, hW⟩
    exact lt_of_le_of_lt (Nat.floor_mono (mul_le_mul_of_nonneg_left (by
      have : (a : ℝ) ≤ t := hat
      linarith) (Nat.cast_nonneg W))) (limLenAll_lt_floor hs hW1 hTH)
  have hSing := fun c : GIdx K np => gramMomSingle_holds hS hL b E np τ m TH s h K Vs hD' R c
    (fun W => limLenAll s W a) hpB
  -- the right-hand side and its limit
  set A1 : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal (Φ * Ca) *
    (∑ c : GIdx K np, b3SummedErr b E s TH h τ m R W (Vs W) (Sum.inl c) (Sum.inl c) +
      ∑ c : GIdx K np, ∑ c' : GIdx K np,
        b3SummedErr b E s TH h τ m R W (Vs W) (Sum.inl c) (Sum.inl c'))
  set A2 : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal (4 * Φ * Crest * N ^ 2) *
    ∑ c : GIdx K np, ∑ j ∈ nbSteps s TH τ W, ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np
  set A3 : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal (8 * Φ * Crest * N ^ 3) *
    ∑ c : GIdx K np, b3LindebergErr b E s TH h τ m R W (Vs W) (Sum.inl c)
  set A4 : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal (W * (t + 2) * (Φ * (Crest *
    (4 * ((W : ℝ)⁻¹ * B) ^ 3 + 8 * ((W : ℝ)⁻¹ * B) ^ 4) + ((W : ℝ)⁻¹ ^ 2 * CΓ +
      (W : ℝ)⁻¹ * ε))))
  set A5 : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal (((np : ℝ) + 2) * (Φ * (ε + K₀ * (N * CA *
    (W : ℝ)⁻¹) + CL * (W : ℝ)⁻¹)))
  set A6 : ℕ → ℝ≥0∞ := fun W => ENNReal.ofReal (2 * Φ * K₀) * ∑ c : GIdx K np,
    ((∫⁻ y, (b3Alive b E s h τ m R W (limLenAll s W a) (Vs W)).indicator (fun y =>
      ‖b3dX b E s h τ m W (limLenAll s W a) (Vs W) (Sum.inl c) y‖ₑ) y ∂closedLaw b W np) +
      b3SummedErr b E s TH h τ m R W (Vs W) (Sum.inl c) (Sum.inl c))
  have t1 : Tendsto A1 atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Φ * Ca))
      ((tendsto_finsetSum Finset.univ fun c _ => hSum c c).add
        (tendsto_finsetSum Finset.univ fun c _ => tendsto_finsetSum Finset.univ fun c' _ =>
          hSum c c')) (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have t2 : Tendsto A2 atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (4 * Φ * Crest * N ^ 2))
      (tendsto_finsetSum Finset.univ fun c _ => hCube c) (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have t3 : Tendsto A3 atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (8 * Φ * Crest * N ^ 3))
      (tendsto_finsetSum Finset.univ fun c _ => hLind c) (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have t4 : Tendsto A4 atTop (𝓝 (ENNReal.ofReal (g1 0))) := by
    refine ENNReal.tendsto_ofReal (hg1.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with W hW
    have hW0 : (W : ℝ) ≠ 0 := by positivity
    simp only [g1]
    field_simp
  have t5 : Tendsto A5 atTop (𝓝 (ENNReal.ofReal (g2 0))) := ENNReal.tendsto_ofReal hg2
  have t6 : Tendsto A6 atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * Φ * K₀))
      (tendsto_finsetSum Finset.univ fun c _ => (hSing c).add (hSum c c))
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have tall : Tendsto (fun W => A1 W + (A2 W + A3 W + A4 W) + (A5 W + A6 W)) atTop
      (𝓝 (0 + (0 + 0 + ENNReal.ofReal (g1 0)) + (ENNReal.ofReal (g2 0) + 0))) :=
    (t1.add ((t2.add t3).add t4)).add (t5.add t6)
  have hlt : (0 + (0 + 0 + ENNReal.ofReal (g1 0)) + (ENNReal.ofReal (g2 0) + 0) : ℝ≥0∞) <
      (ρ : ℝ≥0∞) := by
    have h1 : 0 ≤ g1 0 := by rw [hg10]; positivity
    have h2 : 0 ≤ g2 0 := by rw [hg20]; positivity
    simp only [zero_add, add_zero]
    rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff hρ0').2 hL0
  -- the eventual conditions
  have hwB : ∀ᶠ W : ℕ in atTop, (W : ℝ)⁻¹ * B ≤ δΛ := by
    have := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const B
    rw [zero_mul] at this
    exact (this.eventually (gt_mem_nhds hδΛ)).mono fun W hW => hW.le
  have h4ev : ∀ᶠ W : ℕ in atTop, ∀ j ∈ nbSteps s TH τ W, ∀ c : GIdx K np,
      ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np < ⊤ := by
    have hc : ∀ c : GIdx K np, ∀ᶠ W : ℕ in atTop,
        b3LindebergErr b E s TH h τ m R W (Vs W) (Sum.inl c) < 1 := fun c =>
      (hLind c).eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [eventually_all.2 hc] with W hW j hj c
    refine lt_of_le_of_lt ?_ ((hW c).trans ENNReal.one_lt_top)
    exact Finset.single_le_sum (f := fun j => ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np)
      (fun _ _ => zero_le) hj
  filter_upwards [eventually_ge_atTop 1, hVs,
    complexClosedFeasible_holds b E np τ m TH s h K Vs hD',
    eventually_not_birth hs hτ0 ha, eventually_not_birth hs hτ0 ht, hwB, h4ev,
    tall.eventually (gt_mem_nhds hlt)] with W hW1 hVW hfe hnbp hnbq hwBW h4W hR
  have key := fixedW_bound (i := i) (u := u) (φ := φ) (R := R) (T := TH)
    GramMom.condExpReplace_holds td hb hE1 hE2 hs hτ hW1 hVW.1 hχc hFc hΛc hat hu hTH hnbp
    hnbq hfe hFv hCT hRR hR0 hCJ0 hBA0 hCA0 hCa0 hCr0 hCΓ0 hCL0 hK0 hε.le hε.le hCJ
    (hBA W (Vs W)) hCA hC hCa1 hCa2 hCΓ
    (fun J hJ z hz ξ hξ => hΛcl J hJ z hz ξ fun e => (hξ e).trans hwBW) hCβ
    (hCH W (Vs W)) (hCF W (Vs W)) (hCL W (Vs W)) hFcl h4W
  exact key.trans (hR.le.trans hρ.le)

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
