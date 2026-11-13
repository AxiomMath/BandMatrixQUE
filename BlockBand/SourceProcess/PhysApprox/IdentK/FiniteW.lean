module

public import BlockBand.SourceProcess.PhysApprox.IdentK.FiniteWLim
public import BlockBand.SourceProcess.PhysApprox.B3StopTailMain

/-!
# The finite-`W` tested increments `KFiniteW`

Proof of `kFiniteW_holds`, for one test `κ`, off-birth times `t ≤ t'`, test times `u_l ≤ t` and a
bounded continuous `ψ`:

* **horizon**: the finite-`W` estimates are used at `T' = max T (s + t' + 1)`
  (`frameDomain_mono`; `ComplexSourceLawDomain` only bounds the birth times);
* constants independent of `W` and of the auxiliary level `R`: `C` (test, jet coefficients,
  Taylor remainder; `exists_tayB`), `C_Λ` (generator; `exists_lam_bound`);
* given `ε`, choose `θ`, then `R` from the stop tail `StopTail.complexClosedStopTail_of` at `T'`;
  at this fixed `R`, `enorm_capIncW_le` bounds `‖capIncW‖ₑ` by
  - the time-grid error `O(1/W)`;
  - `2 C_st ‖ψ‖ μ(bad) ≤ ε/4` (the stop is rarely reached);
  - the summed errors (`ComplexClosedSummed` at `T'` and `R`, → 0);
  - the cubic terms, `≤ η Q_W(R) + η⁻¹ L_W(R)`, with `Q_W(R)` bounded through the brackets
    and `L_W(R) → 0` (`ComplexClosedLindeberg`);
  - the births (`np` steps, birth errors → 0, `C_Λ / W`).

`ComplexClosedTight` and `ComplexKStoppedMomentMax` are not used.
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

/-- **The frame domain is monotone in the horizon.** -/
theorem frameDomain_mono {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T T' s h : ℝ} {K : ℕ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hF : FrameDomain b E τ m T s h K Vs) (hT : T ≤ T') : FrameDomain b E τ m T' s h K Vs := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, rest⟩ := hF
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, fun j => (h8 j).trans_le hT⟩, rest⟩

/-- At a fixed time off the births, eventually both discrete jumps are the limit jumps. -/
theorem eventually_jumps_eq {b E s : ℝ} (hs : 0 ≤ s) {np K : ℕ} {τ m : Fin np → ℝ}
    (hsτ : ∀ j, s < τ j) {u : ℝ≥0} (hu : u ∉ birthTimes s τ) :
    ∀ᶠ W : ℕ in atTop, b3JumpAt (K := K) b s τ m W (limLenAll s W u) = gramJ b s τ m u ∧
      b3KJumpAt E s τ m W (limLenAll s W u) = kJ E s τ m u := by
  have hu' : ∀ j, s + (u : ℝ) ≠ τ j := fun j hj => hu ⟨j, hj⟩
  filter_upwards [Fdd.eventually_born_iff hs hsτ hu'] with W hW
  constructor
  · rw [Fdd.b3JumpAt_eq_sum, gramJ, birthJump]
    exact Finset.sum_congr rfl fun i _ => by simp only [hW i]
  · rw [Fdd.b3KJumpAt_eq_sum, kJ, kBirthJump]
    exact Finset.sum_congr rfl fun i _ => by simp only [hW i]

/-!
## The steps between the two times are steps of the estimates at the horizon
-/

theorem subset_noBirth {s T : ℝ} {np : ℕ} (τ : Fin np → ℝ) {W : ℕ} {t t' : ℝ≥0}
    (hT : s + (t' : ℝ) ≤ T) :
    (Ico (limLenAll s W t) (limLenAll s W t')).filter (fun j => ¬ IsBirthStep τ W j) ⊆
      genNoBirthSteps s T τ W := fun j hj => by
  obtain ⟨hj1, hj2⟩ := mem_filter.1 hj
  obtain ⟨hj3, hj4⟩ := mem_Ico.1 hj1
  have h1 := le_limLenAll s W t
  have h2 : limLenAll s W t' ≤ ⌊(W : ℝ) * T⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg W))
  exact mem_filter.2 ⟨mem_Ico.2 ⟨h1.trans hj3, hj4.trans_le h2⟩, hj2⟩

theorem subset_birth {s T : ℝ} {np : ℕ} (τ : Fin np → ℝ) {W : ℕ} {t t' : ℝ≥0}
    (hT : s + (t' : ℝ) ≤ T) :
    (Ico (limLenAll s W t) (limLenAll s W t')).filter (fun j => IsBirthStep τ W j) ⊆
      genBirthSteps s T τ W := fun j hj => by
  obtain ⟨hj1, hj2⟩ := mem_filter.1 hj
  obtain ⟨hj3, hj4⟩ := mem_Ico.1 hj1
  have h1 := le_limLenAll s W t
  have h2 : limLenAll s W t' ≤ ⌊(W : ℝ) * T⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg W))
  exact mem_filter.2 ⟨mem_Ico.2 ⟨h1.trans hj3, hj4.trans_le h2⟩, hj2⟩

section Limits

variable {b E : ℝ} {np : ℕ} {τ m : Fin np → ℝ} {T s h : ℝ} {K : ℕ}
  {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}

/-- **The summed errors vanish.** -/
theorem tendsto_Tpin (hS : ComplexClosedSummed) (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ)
    {t t' : ℝ≥0} (hT : s + (t' : ℝ) ≤ T) :
    Tendsto (fun W => ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter
      (fun j => ¬ IsBirthStep τ W j), (∑ i, pinE1 b E s h τ m R W (Vs W) j i +
        ∑ i, ∑ i', pinE2 b E s h τ m R W (Vs W) j i i')) atTop (𝓝 0) := by
  set n : ℝ≥0∞ := (Fintype.card (BI K np) : ℝ≥0∞)
  have hlim : Tendsto (fun W => (n + n * n) * pinTot b E s T h τ m R W (Vs W)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := n + n * n) (tendsto_pinTot hS hF R)
      (Or.inr (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _,
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)⟩))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun W => ?_
  have hsub := subset_noBirth (W := W) (t := t) τ hT
  dsimp only
  rw [sum_add_distrib, sum_comm, sum_comm (s := (Ico (limLenAll s W t)
    (limLenAll s W t')).filter (fun j => ¬ IsBirthStep τ W j))]
  have h1 : ∑ i : BI K np, ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter
      (fun j => ¬ IsBirthStep τ W j), pinE1 b E s h τ m R W (Vs W) j i ≤
        ∑ _i : BI K np, pinTot b E s T h τ m R W (Vs W) :=
    sum_le_sum fun i _ => sum_pinE1_le b E s T h τ m R W (Vs W) hsub i
  have h2 : ∑ i : BI K np, ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter
      (fun j => ¬ IsBirthStep τ W j), ∑ i', pinE2 b E s h τ m R W (Vs W) j i i' ≤
        ∑ _i : BI K np, ∑ _i' : BI K np, pinTot b E s T h τ m R W (Vs W) :=
    sum_le_sum fun i _ => by
      rw [sum_comm]; exact sum_le_sum fun i' _ => sum_pinE2_le b E s T h τ m R W (Vs W) hsub i i'
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  simp only [sum_const, card_univ, nsmul_eq_mul, n]
  ring

/-- **The birth terms vanish.** -/
theorem tendsto_Tbir (hS : ComplexClosedSummed) (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ)
    {t t' : ℝ≥0} (hT : s + (t' : ℝ) ≤ T) (C CΛ : ℝ) :
    Tendsto (fun W => ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter
      (fun j => IsBirthStep τ W j), (ENNReal.ofReal (3 * C) *
        ∑ i : BI K np, genBirthStep b E s h τ m R W j (Vs W) (cOf i) +
          ENNReal.ofReal (CΛ / W))) atTop (𝓝 0) := by
  set n : ℝ≥0∞ := (Fintype.card (BI K np) : ℝ≥0∞)
  have hW : Tendsto (fun W : ℕ => ENNReal.ofReal (CΛ / W)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat CΛ)
    simpa using this
  have hlim : Tendsto (fun W => ENNReal.ofReal (3 * C) * (n * pinTot b E s T h τ m R W (Vs W)) +
      (np : ℝ≥0∞) * ENNReal.ofReal (CΛ / W)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (3 * C))
      (ENNReal.Tendsto.const_mul (a := n) (tendsto_pinTot hS hF R)
        (Or.inr (ENNReal.natCast_ne_top _)))
      (Or.inr ENNReal.ofReal_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := (np : ℝ≥0∞)) hW (Or.inr (by simp))
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    fun W => ?_
  have hsub := subset_birth (W := W) (t := t) τ hT
  dsimp only
  rw [sum_add_distrib, ← mul_sum, sum_comm, sum_const]
  refine add_le_add (mul_le_mul' le_rfl ?_) ?_
  · calc ∑ i : BI K np, ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter
          (fun j => IsBirthStep τ W j), genBirthStep b E s h τ m R W j (Vs W) (cOf i) ≤
        ∑ _i : BI K np, pinTot b E s T h τ m R W (Vs W) :=
          sum_le_sum fun i _ => sum_birth_le b E s T h τ m R W (Vs W) hsub (cOf i)
      _ = n * pinTot b E s T h τ m R W (Vs W) := by simp [n]
  · rw [nsmul_eq_mul]
    exact mul_le_mul' (by exact_mod_cast card_birth_le τ W _) le_rfl

/-- **The cubic Taylor terms vanish**: `≤ η Q_W(R) + η⁻¹ L_W(R)` with `Q_W(R)` bounded. -/
theorem tendsto_Tcub (hS : ComplexClosedSummed) (hL : ComplexClosedLindeberg)
    (hF : FrameDomain b E τ m T s h K Vs) (R : ℝ) {t t' : ℝ≥0} (htt : t ≤ t')
    (hT : s + (t' : ℝ) ≤ T) :
    Tendsto (fun W => ∑ j ∈ (Ico (limLenAll s W t) (limLenAll s W t')).filter
      (fun j => ¬ IsBirthStep τ W j), ∫⁻ y, (b3AliveM b E s h τ m R W j (Vs W)).indicator
        (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W (Vs W) j y) ^ 3)) y ∂closedLaw b W np)
      atTop (𝓝 0) := by
  obtain ⟨⟨-, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, hVs⟩ := id hF
  have hb1 : b < 1 := by linarith
  obtain ⟨CR, hCR0, hCR⟩ := exists_bound_coef (K := K) (np := np) b E R
  set nI : ℝ := (Fintype.card (BI K np) : ℝ)
  have hnI : 0 ≤ nI := Nat.cast_nonneg _
  set X : ℝ := CR * ((t' : ℝ) - t + 1)
  have hX : 0 ≤ X := mul_nonneg hCR0 (by have : (t : ℝ) ≤ t' := htt; linarith)
  set Qb : ℝ := nI * (nI * (X + 1))
  have hQb : 0 ≤ Qb := by positivity
  have hLind : ∀ c, Tendsto (fun W => b3LindebergErr b E s T h τ m R W (Vs W) c) atTop (𝓝 0) :=
    fun c => hL b E np τ m T s h K Vs hF R c
  have hL2 := Filter.eventually_all.2 fun c => genMem_eventually_memLp_of_lindeberg hF R c (hLind c)
  have hLtot : Tendsto (fun W => ENNReal.ofReal (nI ^ 3) * ∑ i : BI K np,
      b3LindebergErr b E s T h τ m R W (Vs W) (cOf i)) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (nI ^ 3))
      (tendsto_finsetSum (univ : Finset (BI K np)) fun i _ => hLind (cOf i))
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h1
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ⊤
  · exact Eventually.of_forall fun _ => hδt ▸ le_top
  set δr := δ.toReal
  have hδr : 0 < δr := ENNReal.toReal_pos hδ.ne' hδt
  set η : ℝ := δr / (2 * (Qb + 1))
  have hη : 0 < η := by positivity
  have hL0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal η⁻¹) hLtot
    (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hL0
  have hLev := ENNReal.tendsto_nhds_zero.1 hL0 (ENNReal.ofReal (δr / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  have hPev := ENNReal.tendsto_nhds_zero.1 (tendsto_pinTot hS hF R) 1 one_pos
  filter_upwards [eventually_ge_atTop 1, hVs, hL2, hLev, hPev] with W hW1 hVW hL2W hLW hPW
  have hW0 : 0 < W := hW1
  have hV' : Measurable (Vs W) :=
    hVW.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set S := (Ico (limLenAll s W t) (limLenAll s W t')).filter (fun j => ¬ IsBirthStep τ W j)
  have hsub : S ⊆ genNoBirthSteps s T τ W := subset_noBirth τ hT
  -- per-step bound
  have hstep : ∀ j ∈ S, ∫⁻ y, (b3AliveM b E s h τ m R W j (Vs W)).indicator
      (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W (Vs W) j y) ^ 3)) y ∂closedLaw b W np ≤
      ENNReal.ofReal η * (ENNReal.ofReal nI * ∑ i : BI K np,
        (ENNReal.ofReal (CR / W) + pinE2 b E s h τ m R W (Vs W) j i (sig i))) +
      ENNReal.ofReal η⁻¹ * (ENNReal.ofReal (nI ^ 3) * ∑ i : BI K np,
        ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
          (fun y => ‖b3dX b E s h τ m W j (Vs W) (cOf i) y‖ₑ ^ 4) y ∂closedLaw b W np) := by
    intro j hj
    have hjnb : ¬ IsBirthStep τ W j := (mem_filter.1 hj).2
    have hjs : closeLen s W ≤ j := (le_limLenAll s W t).trans (mem_Ico.1 (mem_filter.1 hj).1).1
    have c1 := lint_cube_le (μ := closedLaw b W np)
      (measurableSet_b3AliveM b E s h τ m R W j hV') (β := betaS b E s h τ m W (Vs W) j)
      (fun i => measurable_betaS hV' i) hη
    have c3 := lint_four_le (R := R) hb1 hE1 hE2 hV' hjnb (j := j) (b := b) (E := E) (s := s)
      (h := h) (τ := τ) (m := m)
    refine c1.trans (add_le_add (mul_le_mul' le_rfl (mul_le_mul' le_rfl
      (sum_le_sum fun i _ => ?_))) (mul_le_mul' le_rfl c3))
    exact lint_sq_le hb1 hE1 hE2 hVW.1 hjs hjnb (hL2W · j (hsub hj)) hCR0 hCR i
  refine (sum_le_sum hstep).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, sum_comm, sum_comm (s := S)]
  have hcard : (S.card : ℝ) * (CR / W) ≤ X := by
    have h1 : (S.card : ℝ) ≤ ((limLenAll s W t' - limLenAll s W t : ℕ) : ℝ) := by
      have := card_le_card (filter_subset (fun j => ¬ IsBirthStep τ W j)
        (Ico (limLenAll s W t) (limLenAll s W t')))
      rw [Nat.card_Ico] at this
      exact_mod_cast this
    have h2 := card_Ico_div_le hs.le hW0 htt
    have hW' : (0 : ℝ) < W := by exact_mod_cast hW0
    calc (S.card : ℝ) * (CR / W) = (S.card : ℝ) / W * CR := by ring
      _ ≤ ((t' : ℝ) - t + 1) * CR := mul_le_mul_of_nonneg_right
          ((div_le_div_of_nonneg_right h1 hW'.le).trans h2) hCR0
      _ = X := by ring
  have hA : ∀ i : BI K np, ∑ j ∈ S, (ENNReal.ofReal (CR / W) +
      pinE2 b E s h τ m R W (Vs W) j i (sig i)) ≤ ENNReal.ofReal X + 1 := fun i => by
    rw [sum_add_distrib, sum_const, nsmul_eq_mul]
    refine add_le_add ?_ ((sum_pinE2_le b E s T h τ m R W (Vs W) hsub i (sig i)).trans hPW)
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hcard
  have hB : ∀ i : BI K np, ∑ j ∈ S, ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
      (fun y => ‖b3dX b E s h τ m W j (Vs W) (cOf i) y‖ₑ ^ 4) y ∂closedLaw b W np ≤
        b3LindebergErr b E s T h τ m R W (Vs W) (cOf i) := fun i =>
    sum_le_sum_of_subset hsub
  have h1 : ENNReal.ofReal η * (ENNReal.ofReal nI * ∑ i : BI K np, ∑ j ∈ S,
      (ENNReal.ofReal (CR / W) + pinE2 b E s h τ m R W (Vs W) j i (sig i))) ≤
        ENNReal.ofReal (δr / 2) := by
    calc _ ≤ ENNReal.ofReal η * (ENNReal.ofReal nI * ∑ _i : BI K np,
          (ENNReal.ofReal X + 1)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl (sum_le_sum
            fun i _ => hA i))
      _ = ENNReal.ofReal (η * Qb) := by
          rw [sum_const, card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add hX zero_le_one, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul hnI, ← ENNReal.ofReal_mul hη.le]
      _ ≤ ENNReal.ofReal (δr / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : η * Qb = δr / 2 * (Qb / (Qb + 1)) := by
            simp only [η]; field_simp
          rw [this]
          exact mul_le_of_le_one_right (by positivity)
            ((div_le_one (by positivity)).2 (by linarith))
  have h2 : ENNReal.ofReal η⁻¹ * (ENNReal.ofReal (nI ^ 3) * ∑ i : BI K np, ∑ j ∈ S,
      ∫⁻ y, (b3Alive b E s h τ m R W j (Vs W)).indicator
        (fun y => ‖b3dX b E s h τ m W j (Vs W) (cOf i) y‖ₑ ^ 4) y ∂closedLaw b W np) ≤
        ENNReal.ofReal (δr / 2) :=
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl (sum_le_sum fun i _ => hB i))).trans hLW
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, ENNReal.ofReal_toReal hδt]

end Limits

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK.FW

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK

open MeasureTheory Finset Filter Matrix FW
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw BlockBand.SourceProcess.ComplexConstruct
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.SourceProcess.CapLimit
open scoped ComplexConjugate ENNReal Topology NNReal

/-- **`KFiniteW` holds** (drift-free tests): for every drift-free test, the cap-restricted
finite-`W` tested increment at off-birth times tends to `0`. -/
theorem kFiniteW_holds : KFiniteW := by
  intro _hTL hS _hTi _hKm hL b E np τ m T s h K Vs hFD χ ξ hχ hχs hξ hξs κ t t' htt ht ht' r i u
    hu _hub ψ
  obtain ⟨⟨-, hb, hE1, hE2, -, -, -, -⟩, hs, hsτ, -, -, hVs⟩ := id hFD
  have hb1 : b < 1 := by linarith
  set T' := max T (s + (t' : ℝ) + 1)
  have hT' : s + (t' : ℝ) ≤ T' := le_max_of_le_right (by linarith)
  have hFD' : FrameDomain b E τ m T' s h K Vs := frameDomain_mono hFD (le_max_left _ _)
  set D := ((Fintype.card (SrcCol K (Fin np)) : ℝ) + 1) * cJump b m
  have hD0 : 0 ≤ D := mul_nonneg (by positivity) (cJump_nonneg b m)
  obtain ⟨C, hC⟩ := exists_tayB hχ hχs hξ hξs κ hD0
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := exists_lam_bound hχ hχs hξ hξs b E κ (CJ := cJump b m) hD0
  have hC0 : 0 ≤ C := hC.1
  have htt' : (t : ℝ) ≤ t' := htt
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Kst : ℝ := ‖ψ‖ * (2 * (2 * C + ((t' : ℝ) - t + 1) * CΛ))
  have hKst : 0 ≤ Kst := by
    have : 0 ≤ (t' : ℝ) - t + 1 := by linarith
    positivity
  set θ : ℝ := ε / 4 / (Kst + 1)
  have hθ : 0 < θ := by positivity
  obtain ⟨R, hR⟩ := StopTail.complexClosedStopTail_of hS hL b E np τ m T' s h K Vs hFD' θ hθ
  -- the vanishing terms at the level `R`
  have hTp := tendsto_Tpin hS hFD' R (t := t) hT'
  have hTc := tendsto_Tcub hS hL hFD' R htt hT'
  have hTb := tendsto_Tbir hS hFD' R (t := t) hT' C CΛ
  have hTt : Tendsto (fun W : ℕ => ENNReal.ofReal (‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W)))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun W : ℕ => ‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W))) atTop (𝓝 0) := by
      have := ((tendsto_const_div_atTop_nhds_zero_nat (CΛ * (2 + 2 * np))).const_mul 2).const_mul
        ‖ψ‖
      simpa using this
    simpa using ENNReal.tendsto_ofReal h1
  have hG := ((hTt.add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖ψ‖ * C)) hTp
    (Or.inr ENNReal.ofReal_ne_top))).add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖ψ‖)
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hTc (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr ENNReal.ofReal_ne_top))).add (ENNReal.Tendsto.const_mul
        (a := ENNReal.ofReal ‖ψ‖) hTb (Or.inr ENNReal.ofReal_ne_top))
  simp only [mul_zero, add_zero] at hG
  have hGev := ENNReal.tendsto_nhds_zero.1 hG (ENNReal.ofReal (ε / 4))
    (ENNReal.ofReal_pos.2 (by positivity))
  have hLind : ∀ c, Tendsto (fun W => b3LindebergErr b E s T' h τ m R W (Vs W) c) atTop (𝓝 0) :=
    fun c => hL b E np τ m T' s h K Vs hFD' R c
  have hL2 := Filter.eventually_all.2 fun c =>
    genMem_eventually_memLp_of_lindeberg hFD' R c (hLind c)
  filter_upwards [eventually_ge_atTop 1, hVs, hL2, hR, hGev,
    eventually_jumps_eq (b := b) (E := E) (K := K) (m := m) hs.le hsτ ht,
    eventually_jumps_eq (b := b) (E := E) (K := K) (m := m) hs.le hsτ ht'] with
    W hW1 hVW hL2W hRW hGW ⟨hGt, hKt⟩ ⟨hGt', hKt'⟩
  have hW0 : 0 < W := hW1
  set n := limLenAll s W t
  set n' := limLenAll s W t'
  have hL2' : ∀ j ∈ Ico n n', ¬ IsBirthStep τ W j → ∀ c, MemLp
      ((b3Alive b E s h τ m R W j (Vs W)).indicator (b3dX b E s h τ m W j (Vs W) c)) 2
        (closedLaw b W np) := fun j hj hjb c =>
    hL2W c j (subset_noBirth τ hT' (mem_filter.2 ⟨hj, hjb⟩))
  have key := enorm_capIncW_le hb1 hE1 hE2 hs.le hsτ hW0 hVW.1 hχ hξ κ hC hCΛ0 hCΛ R htt hGt
    hKt hGt' hKt' i u hu ψ hL2'
  -- the stop term
  have hnT : n' ≤ ⌊(W : ℝ) * T'⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hT' (Nat.cast_nonneg W))
  have hbad : closedLaw b W np (badSet b E s h τ m R W n' (Vs W)) ≤ ENNReal.ofReal θ := by
    refine (measure_mono_ae ?_).trans hRW
    have hq : Measure.QuasiMeasurePreserving (fun y : ProbedPath W np × ℝ => y.1.1)
        (closedLaw b W np) (growthPathLaw W b) :=
      (Measure.quasiMeasurePreserving_fst (μ := growthPathLaw W b)).comp
        (Measure.quasiMeasurePreserving_fst (μ := probedPathLaw W np b))
    have hae := hq.preimage_ae_eq (ClosedIdent.physCapEvent_ae_eq hb1 hE1 hE2 s h K (W := W))
    filter_upwards [hae.mem_iff] with y hy
    intro hyb
    obtain ⟨hc, j, h1, h2, h3⟩ := hyb
    exact ⟨hy.2 hc, j, h1, h2.trans hnT, h3⟩
  have hcoef : ENNReal.ofReal (‖ψ‖ * (2 * (2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W)))) ≤
      ENNReal.ofReal Kst := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := card_Ico_div_le hs.le hW0 htt
    have h2 : ((n' - n : ℕ) : ℝ) * (CΛ / W) ≤ ((t' : ℝ) - t + 1) * CΛ := by
      calc ((n' - n : ℕ) : ℝ) * (CΛ / W) = ((n' - n : ℕ) : ℝ) / W * CΛ := by ring
        _ ≤ ((t' : ℝ) - t + 1) * CΛ := mul_le_mul_of_nonneg_right h1 hCΛ0
    exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  have hstop : ENNReal.ofReal (‖ψ‖ * (2 * (2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W)))) *
      closedLaw b W np (badSet b E s h τ m R W n' (Vs W)) ≤ ENNReal.ofReal (ε / 4) := by
    refine (mul_le_mul' hcoef hbad).trans ?_
    rw [← ENNReal.ofReal_mul hKst]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Kst * θ = ε / 4 * (Kst / (Kst + 1)) := by simp only [θ]; field_simp
    rw [this]
    exact mul_le_of_le_one_right (by positivity) ((div_le_one (by positivity)).2 (by linarith))
  -- assemble
  have hsplit : ∑ j ∈ (Ico n n').filter (fun j => ¬ IsBirthStep τ W j),
      (ENNReal.ofReal (‖ψ‖ * C) * (∑ i, pinE1 b E s h τ m R W (Vs W) j i +
        ∑ i, ∑ i', pinE2 b E s h τ m R W (Vs W) j i i') +
      ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal C * ∫⁻ y, (b3AliveM b E s h τ m R W j (Vs W)).indicator
        (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W (Vs W) j y) ^ 3)) y
          ∂closedLaw b W np)) =
      ENNReal.ofReal (‖ψ‖ * C) * ∑ j ∈ (Ico n n').filter (fun j => ¬ IsBirthStep τ W j),
        (∑ i, pinE1 b E s h τ m R W (Vs W) j i + ∑ i, ∑ i', pinE2 b E s h τ m R W (Vs W) j i i') +
      ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal C * ∑ j ∈ (Ico n n').filter
        (fun j => ¬ IsBirthStep τ W j), ∫⁻ y, (b3AliveM b E s h τ m R W j (Vs W)).indicator
          (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W (Vs W) j y) ^ 3)) y
            ∂closedLaw b W np) := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  have hsplit2 : ∑ j ∈ (Ico n n').filter (fun j => IsBirthStep τ W j),
      ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal (3 * C) *
        ∑ i : BI K np, genBirthStep b E s h τ m R W j (Vs W) (cOf i) +
          ENNReal.ofReal (CΛ / W)) =
      ENNReal.ofReal ‖ψ‖ * ∑ j ∈ (Ico n n').filter (fun j => IsBirthStep τ W j),
        (ENNReal.ofReal (3 * C) * ∑ i : BI K np, genBirthStep b E s h τ m R W j (Vs W) (cOf i) +
          ENNReal.ofReal (CΛ / W)) := (mul_sum _ _ _).symm
  rw [hsplit, hsplit2] at key
  have hfin : ‖capIncW b E s h τ m W (Vs W) (κ.fn χ ξ) (κ.lam χ ξ b E) i u ψ t t'‖ₑ ≤
      ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
    refine key.trans ?_
    calc _ = (ENNReal.ofReal (‖ψ‖ * (2 * (CΛ * (2 + 2 * np) / W))) +
          ENNReal.ofReal (‖ψ‖ * C) * ∑ j ∈ (Ico n n').filter (fun j => ¬ IsBirthStep τ W j),
            (∑ i, pinE1 b E s h τ m R W (Vs W) j i +
              ∑ i, ∑ i', pinE2 b E s h τ m R W (Vs W) j i i') +
          ENNReal.ofReal ‖ψ‖ * (ENNReal.ofReal C * ∑ j ∈ (Ico n n').filter
            (fun j => ¬ IsBirthStep τ W j), ∫⁻ y, (b3AliveM b E s h τ m R W j (Vs W)).indicator
              (fun y => ENNReal.ofReal (nrm (betaS b E s h τ m W (Vs W) j y) ^ 3)) y
                ∂closedLaw b W np) +
          ENNReal.ofReal ‖ψ‖ * ∑ j ∈ (Ico n n').filter (fun j => IsBirthStep τ W j),
            (ENNReal.ofReal (3 * C) *
              ∑ i : BI K np, genBirthStep b E s h τ m R W j (Vs W) (cOf i) +
                ENNReal.ofReal (CΛ / W))) +
          ENNReal.ofReal (‖ψ‖ * (2 * (2 * C + ((n' - n : ℕ) : ℝ) * (CΛ / W)))) *
            closedLaw b W np (badSet b E s h τ m R W n' (Vs W)) := by ring
      _ ≤ _ := add_le_add hGW hstop
  have hε4 : ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) = ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  rw [hε4, ← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  rw [dist_zero_right]
  linarith

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.IdentK
