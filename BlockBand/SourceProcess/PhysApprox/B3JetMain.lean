module

public import BlockBand.SourceProcess.PhysApprox.B3JetStep
public import BlockBand.SourceProcess.PhysApprox.B3Bridges
public import BlockBand.Transmission.LengthUniform.DeltaZero

/-!
# The closed `δ₀` jet in `L⁴` (`ClosedJetL4`, `ClosedJetHalf`)

For a closed input family `Xcl : ClosedInputFam`, the closed `δ₀` jet is proved in `L⁴` from
`GaussianAbsorptionContract` and `GaussianLpGradient` (through `passiveMeanStep_holds` and
`passiveFluctuationStep_holds`) and three properties of `Xcl`:

* `ClosedInputRegular Xcl`: at every step `n_s ≤ j < ⌊WT⌋`, `Xcl_j` is Borel, unchanged by
  `b3Ext W j` and a.e. passive (the first three clauses of `ClosedKStepForm`;
  `closedInputRegular_of_stepForm`). For `b3ClosedX` regularity reduces to passivity
  (`closedInputRegular_b3ClosedX`), proved as `closedInputPassive_b3ClosedX`; its recursion is
  `closedInputRecursion_b3ClosedX`;
* **`ClosedInputRecursion Xcl`** (exact algebra), stated as a hypothesis:
  `Xcl_{j+1} = freshSchur E Xcl_j F_j` a.e.: closing touches the far end only, so the near-end
  growth is the open one-port map;
* **`ClosedJetEntrance q Xcl`**, stated as a hypothesis: at one time `s' ∈ [s, min τ)`, for
  every radius `d > 0`, `μ(δ₀(Xcl_{⌊Ws'⌋}) > d) ≤ C/W^q`. Only a fixed radius is asked; the
  `W⁻¹` rate is produced by the recursion.

Proved here:
* **`closedJet_lintegral_le`**: `Regular + Recursion + Entrance q ⇒ E δ₀(Xcl_j)⁴ ≤ C/W^q` at
  every step after the first birth (`q ≤ 4`): geometric forgetting over the `≥ (min τ - s')W`
  layers between the entrance and the first birth, exits by Markov at `p = 6`;
* **`closedJetL4Fam_of`** (`q = 4`: `ClosedJetL4Fam`) and
  **`closedJetHalf_of`** (`q = 2`: `ClosedJetHalf`, from a weaker entrance);
* at the shared closed input: **`closedJetL4Fam_b3ClosedX`** (main theorem),
  `closedJetHalf_b3ClosedX`, and `closedKMeanInput_b3ClosedX` (through the closed-input bridge).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Jet

open MeasureTheory Filter Topology Matrix
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Transmission.Bridge BlockBand.Transmission.PathScalar
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.ClosedPath
open BlockBand.Transmission.PassiveLayer
open scoped ENNReal ComplexOrder

/-!
## The closed-input properties
-/

/-- **Regularity of a closed input family**: at every step `n_s ≤ j < ⌊WT⌋`, `Xcl_j` is Borel,
a function of the past at `j` and a.e. passive (the first three clauses of
`ClosedKStepForm`). -/
def ClosedInputRegular (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        Measurable (Xcl b E s h τ m W j) ∧
        (∀ y, Xcl b E s h τ m W j (b3Ext W j y) = Xcl b E s h τ m W j y) ∧
        ∀ᵐ y ∂closedLaw b W np, (passiveY (Xcl b E s h τ m W j y)).PosSemidef

/-- **Passivity of a closed input family** at every step `n_s ≤ j < ⌊WT⌋` (the third clause of
`ClosedInputRegular`). -/
def ClosedInputPassive (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
      ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊,
        ∀ᵐ y ∂closedLaw b W np, (passiveY (Xcl b E s h τ m W j y)).PosSemidef

/-- **`ClosedInputRecursion Xcl`: the closed one-port recursion** (on the far-closed path): for
`n_s ≤ j` and `j + 1 < ⌊WT⌋`, `Xcl_{j+1} = B_{j+1}*(A_j - E - Xcl_j)⁻¹B_{j+1}` a.e. Closing changes
only the far boundary, which is fixed after `n_s`. -/
def ClosedInputRecursion (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∀ᶠ W in atTop,
      ∀ j : ℕ, closeLen s W ≤ j → j + 1 < ⌊(W : ℝ) * T⌋₊ →
        ∀ᵐ y ∂closedLaw b W np, Xcl b E s h τ m W (j + 1) y =
          freshSchur E (Xcl b E s h τ m W j y) (freshSample W j y.1.1)

/-- **`ClosedJetEntrance q Xcl`: the closed path enters the scalar domain**. There is a time
`s ≤ s' < min τ` such that for every radius `d > 0`, eventually `μ(δ₀(Xcl_{⌊Ws'⌋}) > d) ≤ C/W^q`. -/
def ClosedJetEntrance (q : ℕ) (Xcl : ClosedInputFam) : Prop :=
  ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
    (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
    FrameDomain b E τ m T s h K Vs → ∃ s' : ℝ, s ≤ s' ∧ (∀ k, s' < τ k) ∧
      ∀ d : ℝ, 0 < d → ∃ C : ℝ, ∀ᶠ W in atTop,
        closedLaw b W np {y | d < jetDistance0 b E (Xcl b E s h τ m W ⌊(W : ℝ) * s'⌋₊ y)} ≤
          ENNReal.ofReal (C / (W : ℝ) ^ q)

theorem closedInputRegular_of_stepForm {Xcl : ClosedInputFam} (hF : ClosedKStepForm Xcl) :
    ClosedInputRegular Xcl := by
  intro b E np τ m T s h K Vs hD
  obtain ⟨Cf, hW⟩ := hF b E np τ m T s h K Vs hD 0
  filter_upwards [hW] with W hW j hj
  obtain ⟨h1, h2, h3, -⟩ := hW j hj
  exact ⟨h1, h2, h3⟩

theorem closedInputPassive_of_regular {Xcl : ClosedInputFam} (hR : ClosedInputRegular Xcl) :
    ClosedInputPassive Xcl := by
  intro b E np τ m T s h K Vs hD
  filter_upwards [hR b E np τ m T s h K Vs hD] with W hW j hj
  exact (hW j hj).2.2

/-- For the shared closed input `b3ClosedX`, regularity is passivity (measurability and
invariance are `measurable_b3ClosedX`, `b3ClosedX_b3Ext`). -/
theorem closedInputRegular_b3ClosedX (hP : ClosedInputPassive b3ClosedX) :
    ClosedInputRegular b3ClosedX := by
  intro b E np τ m T s h K Vs hD
  filter_upwards [hP b E np τ m T s h K Vs hD] with W hW j hj
  exact ⟨measurable_b3ClosedX b E s h τ m j,
    fun y => b3ClosedX_b3Ext (Finset.mem_Ico.1 hj).1 le_rfl y, hW j hj⟩

/-!
## Arithmetic
-/

theorem jet_pow_le {ρ x c u : ℝ} {n : ℕ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hu : u = 1 - ρ)
    (hx : 0 < x) (hc : 0 < c) (hn : x * c / 2 ≤ n) (hxc : 2 ≤ x * c) :
    ρ ^ n ≤ 2 / (x * c * u) := by
  have hn1 : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hu0 : 0 < u := by rw [hu]; linarith
  refine (pow_le_inv_mul hρ0 hρ1 hn1).trans ?_
  rw [← hu, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem jet_a_le {ρn x c u d₀ Cm C4 : ℝ} (hx : 1 ≤ x) (hc : 0 < c) (hu : 0 < u)
    (hd₀ : 0 < d₀) (hCm : 0 ≤ Cm) (hρ : ρn ≤ 2 / (x * c * u)) :
    ρn * (d₀ / 2) + (Cm / x ^ 2 + C4 / x) / u ≤ (d₀ / (c * u) + (Cm + C4) / u) / x := by
  have hx0 : 0 < x := by linarith
  have h1 : ρn * (d₀ / 2) ≤ d₀ / (c * u) / x := by
    calc ρn * (d₀ / 2) ≤ 2 / (x * c * u) * (d₀ / 2) := by gcongr
      _ = d₀ / (c * u) / x := by field_simp
  have h2 : Cm / x ^ 2 ≤ Cm / x :=
    div_le_div_of_nonneg_left hCm hx0 (by nlinarith)
  have h3 : (Cm / x ^ 2 + C4 / x) / u ≤ (Cm + C4) / u / x := by
    rw [div_div, mul_comm u x, ← div_div]
    gcongr
    rw [add_div]; linarith
  rw [add_div (d₀ / (c * u)) ((Cm + C4) / u) x]; linarith

theorem jet_total_le {a K M Ce n t6 x Tp : ℝ} {q : ℕ} (hq : q ≤ 4) (hx : 1 ≤ x) (ha0 : 0 ≤ a)
    (ha : a ≤ K / x) (hn0 : 0 ≤ n) (hn : n ≤ Tp * x)
    (ht6 : 0 ≤ t6) :
    a ^ 4 + M ^ 4 * (Ce / x ^ q + n * t6 / x ^ 6) ≤
      (K ^ 4 + M ^ 4 * (Ce + Tp * t6)) / x ^ q := by
  have hx0 : 0 < x := by linarith
  have hxq : 0 < x ^ q := by positivity
  have hK : 0 ≤ K := by
    have : 0 ≤ K / x := ha0.trans ha
    rwa [div_nonneg_iff, or_iff_left (by intro h; linarith [h.2]), and_iff_left hx0.le] at this
  have h1 : a ^ 4 ≤ K ^ 4 / x ^ q := by
    calc a ^ 4 ≤ (K / x) ^ 4 := pow_le_pow_left₀ ha0 ha 4
      _ = K ^ 4 * (1 / x ^ 4) := by rw [div_pow]; ring
      _ ≤ K ^ 4 * (1 / x ^ q) := by
          gcongr
      _ = K ^ 4 / x ^ q := by ring
  have h2 : n * t6 / x ^ 6 ≤ Tp * t6 / x ^ q := by
    have hTp : 0 ≤ Tp := by
      have := hn0.trans hn
      exact nonneg_of_mul_nonneg_left this hx0
    calc n * t6 / x ^ 6 ≤ Tp * x * t6 / x ^ 6 := by gcongr
      _ = Tp * t6 * (1 / x ^ 5) := by field_simp
      _ ≤ Tp * t6 * (1 / x ^ q) := by
          gcongr; omega
      _ = Tp * t6 / x ^ q := by ring
  have h3 : M ^ 4 * (Ce / x ^ q + n * t6 / x ^ 6) ≤ M ^ 4 * ((Ce + Tp * t6) / x ^ q) := by
    gcongr; rw [add_div]; linarith
  calc a ^ 4 + M ^ 4 * (Ce / x ^ q + n * t6 / x ^ 6)
      ≤ K ^ 4 / x ^ q + M ^ 4 * ((Ce + Tp * t6) / x ^ q) := add_le_add h1 h3
    _ = (K ^ 4 + M ^ 4 * (Ce + Tp * t6)) / x ^ q := by ring

/-!
## The closed jet
-/

/-- **The closed jet from the closed-input properties**: `E δ₀(Xcl_j)⁴ ≤ C/W^q` at every step
`n_s ≤ j < ⌊WT⌋` after the first birth, for `q ≤ 4`. -/
theorem closedJet_lintegral_le (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {Xcl : ClosedInputFam} (hReg : ClosedInputRegular Xcl) (hRec : ClosedInputRecursion Xcl)
    {q : ℕ} (hq : q ≤ 4) (hEnt : ClosedJetEntrance q Xcl) :
    ∀ (b E : ℝ) (np : ℕ) (τ m : Fin np → ℝ) (T s h : ℝ) (K : ℕ)
      (Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ),
      FrameDomain b E τ m T s h K Vs → ∃ C : ℝ, ∀ᶠ W in atTop,
        ∀ j ∈ Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊, (∃ k, ⌊(W : ℝ) * τ k⌋₊ ≤ j) →
          ∫⁻ y, ENNReal.ofReal (jetDistance0 b E (Xcl b E s h τ m W j y) ^ 4)
            ∂closedLaw b W np ≤ ENNReal.ofReal (C / (W : ℝ) ^ q) := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨⟨hb0, hb, hE1, hE2, -, -, -, -⟩, hs, -, -, -, -⟩ := id hF
  have hκ : 0 < min (2 + E) (2 - E) := lt_min (by linarith) (by linarith)
  have hEb : E ∈ bulkInterval (min (2 + E) (2 - E)) :=
    ⟨by have := min_le_left (2 + E) (2 - E); linarith,
      by have := min_le_right (2 + E) (2 - E); linarith⟩
  obtain ⟨d₀, ρ, Cm, Wm, hd₀, hρ0, hρ1, hCm, hmean⟩ :=
    passiveMeanStep_holds (passiveBounds_holds hGA hLp) b hb0 hb _ hκ
  obtain ⟨C4, W4, hC4, hfl4⟩ :=
    passiveFluctuationStep_holds hGA hLp b hb0 hb _ hκ 4 (by norm_num)
  obtain ⟨C6, W6, hC6, hfl6⟩ :=
    passiveFluctuationStep_holds hGA hLp b hb0 hb _ hκ 6 (by norm_num)
  obtain ⟨s', hss', hs'τ, hent⟩ := hEnt b E np τ m T s h K Vs hF
  obtain ⟨Ce, hCe⟩ := hent (d₀ / 2) (by positivity)
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ k, c ≤ τ k - s' := by
    by_cases hne : Nonempty (Fin np)
    · obtain ⟨k₀, hk₀⟩ := Finite.exists_min fun k => τ k - s'
      exact ⟨τ k₀ - s', by linarith [hs'τ k₀], hk₀⟩
    · exact ⟨1, one_pos, fun k => (hne ⟨k⟩).elim⟩
  set ρ' := max ρ (1 / 2) with hρ'
  have hρ'0 : 0 < ρ' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hρ'1 : ρ' < 1 := max_lt hρ1 (by norm_num)
  set u := 1 - ρ' with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  set t := (1 - ρ') * d₀ / 2 with ht
  set M := (etaZ b E)⁻¹ + 1 with hM
  have hM0 : 0 ≤ M := by
    have := (etaLow_pos (by linarith : b < 1) hκ).le.trans
      (etaLow_le (by linarith : b < 1) hκ hEb)
    positivity
  set Kc := d₀ / (c * u) + (Cm + C4) / u with hKc
  set Tp := max T 0 with hTp
  set t6 := t⁻¹ ^ 6 * C6 ^ 6 with ht6
  refine ⟨Kc ^ 4 + M ^ 4 * (max Ce 0 + Tp * t6), ?_⟩
  filter_upwards [hReg b E np τ m T s h K Vs hF, hRec b E np τ m T s h K Vs hF, hCe,
    eventually_ge_atTop (max (max Wm (max W4 W6)) (max 1 (max ⌈2 / c⌉₊ ⌈Cm / (u * d₀ / 2)⌉₊)))]
    with W hWreg hWrec hWent hWbig j hj ⟨k, hk⟩
  simp only [max_le_iff] at hWbig
  obtain ⟨⟨hWm, hW4, hW6⟩, hW1, hWc, hWC⟩ := hWbig
  have hx : (1 : ℝ) ≤ W := by exact_mod_cast hW1
  have hx0 : (0 : ℝ) < W := by linarith
  obtain ⟨hjs, hjT⟩ := Finset.mem_Ico.1 hj
  set j₀ := ⌊(W : ℝ) * s'⌋₊ with hj₀
  have hs'0 : 0 ≤ (W : ℝ) * s' := by have := hs.le.trans hss'; positivity
  have hj₀s : closeLen s W ≤ j₀ := Nat.floor_mono (by nlinarith)
  have hj₀k : j₀ ≤ ⌊(W : ℝ) * τ k⌋₊ := Nat.floor_mono (by nlinarith [hs'τ k])
  have hj₀j : j₀ ≤ j := hj₀k.trans hk
  -- the number of layers between the entrance and `j`
  have hnr : (W : ℝ) * c / 2 ≤ ((j - j₀ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj₀j]
    have h1 := Nat.lt_floor_add_one ((W : ℝ) * τ k)
    have h2 : (j₀ : ℝ) ≤ (W : ℝ) * s' := Nat.floor_le hs'0
    have h3 : ((⌊(W : ℝ) * τ k⌋₊ : ℕ) : ℝ) ≤ j := by exact_mod_cast hk
    have h4 : (W : ℝ) * c ≤ (W : ℝ) * (τ k - s') := mul_le_mul_of_nonneg_left (hc k) hx0.le
    have h5 : 2 ≤ (W : ℝ) * c := by
      have := (Nat.le_ceil (2 / c)).trans (by exact_mod_cast hWc : (⌈2 / c⌉₊ : ℝ) ≤ W)
      rw [div_le_iff₀ hc0] at this; linarith
    nlinarith
  have hxc : 2 ≤ (W : ℝ) * c := by
    have := (Nat.le_ceil (2 / c)).trans (by exact_mod_cast hWc : (⌈2 / c⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hc0] at this; linarith
  have hpow := jet_pow_le hρ'0 hρ'1 hu hx0 hc0 hnr hxc
  -- the domain condition `C/W² ≤ (1-ρ)d₀/2`
  have hWd : Cm / (W : ℝ) ^ 2 ≤ (1 - ρ') * d₀ / 2 := by
    have hud : 0 < u * d₀ / 2 := by positivity
    have h1 := (Nat.le_ceil (Cm / (u * d₀ / 2))).trans
      (by exact_mod_cast hWC : (⌈Cm / (u * d₀ / 2)⌉₊ : ℝ) ≤ W)
    rw [div_le_iff₀ hud] at h1
    rw [div_le_iff₀ (by positivity)]
    rw [← hu]; nlinarith
  have hmean' : ∀ X : Matrix (Fin W) (Fin W) ℂ, (passiveY X).PosSemidef →
      jetDistance0 b E X ≤ d₀ →
        ‖(∫ ω, freshPortTrace b E X ω ∂freshLaw W b) - matchedA E‖ ≤
          ρ' * jetDistance0 b E X + Cm / (W : ℝ) ^ 2 := fun X hX hd =>
    (hmean W hWm E hEb X hX hd).trans (by
      have h0 : 0 ≤ jetDistance0 b E X := norm_nonneg _
      gcongr
      exact le_max_left _ _)
  have key := lintegral_jet_four_le (np := np) hb0 hb hE1 hE2 hd₀ hρ'0.le hρ'1 hCm hC4 hC6 hWd
    hmean' (fun X hX => hfl4 W hW4 E hEb X hX) (fun X hX => hfl6 W hW6 E hEb X hX)
    (fun j => Xcl b E s h τ m W j) hj₀j
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨hj₀s.trans h1, lt_of_le_of_lt h2 hjT⟩)).1)
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨hj₀s.trans h1, lt_of_le_of_lt h2 hjT⟩)).2.1)
    (fun j' h1 h2 => (hWreg j' (Finset.mem_Ico.2 ⟨hj₀s.trans h1, lt_of_le_of_lt h2 hjT⟩)).2.2)
    (fun j' h1 h2 => hWrec j' (hj₀s.trans h1) (by omega))
  -- assemble
  have hCe' : closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} ≤
      ENNReal.ofReal (max Ce 0 / (W : ℝ) ^ q) :=
    hWent.trans (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
  set a := ρ' ^ (j - j₀) * (d₀ / 2) + (Cm / (W : ℝ) ^ 2 + C4 / W) / (1 - ρ') with ha
  have ha0 : 0 ≤ a := by rw [ha]; have := hu0; positivity
  have haK : a ≤ Kc / W := by
    rw [ha, ← hu]
    exact jet_a_le hx hc0 hu0 hd₀ hCm hpow
  have hnT : ((j - j₀ : ℕ) : ℝ) ≤ Tp * W := by
    have hT1 : 0 < ⌊(W : ℝ) * T⌋₊ := lt_of_le_of_lt (Nat.zero_le _) hjT
    have hWT : 0 ≤ (W : ℝ) * T := le_trans zero_le_one (Nat.floor_pos.1 hT1)
    have h1 : ((j - j₀ : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j j₀
    have h2 : (j : ℝ) ≤ ⌊(W : ℝ) * T⌋₊ := by exact_mod_cast hjT.le
    have h3 := Nat.floor_le hWT
    have h4 : (W : ℝ) * T ≤ Tp * W := by rw [mul_comm]; gcongr; exact le_max_left _ _
    linarith
  have ht6' : ((1 - ρ') * d₀ / 2)⁻¹ ^ 6 * (C6 / W) ^ 6 = t6 / (W : ℝ) ^ 6 := by
    rw [ht6, ht, div_pow]; ring
  have hfin := jet_total_le (a := a) (K := Kc) (M := M) (Ce := max Ce 0)
    (n := ((j - j₀ : ℕ) : ℝ)) (t6 := t6) (Tp := Tp) hq hx ha0 haK
    (Nat.cast_nonneg _) hnT (by rw [ht6]; positivity)
  refine key.trans ?_
  rw [ht6']
  calc ENNReal.ofReal (a ^ 4) + ENNReal.ofReal (M ^ 4) *
        (closedLaw b W np {y | d₀ / 2 < jetDistance0 b E (Xcl b E s h τ m W j₀ y)} +
          ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) * (t6 / (W : ℝ) ^ 6)))
      ≤ ENNReal.ofReal (a ^ 4) + ENNReal.ofReal (M ^ 4) *
          (ENNReal.ofReal (max Ce 0 / (W : ℝ) ^ q) +
            ENNReal.ofReal (((j - j₀ : ℕ) : ℝ) * t6 / (W : ℝ) ^ 6)) := by
        rw [mul_div_assoc]
        gcongr
        exact le_of_eq (by rw [ht6]; ring)
    _ = ENNReal.ofReal (a ^ 4 + M ^ 4 * (max Ce 0 / (W : ℝ) ^ q +
          ((j - j₀ : ℕ) : ℝ) * t6 / (W : ℝ) ^ 6)) := by
        have h6 : 0 ≤ ((j - j₀ : ℕ) : ℝ) * t6 / (W : ℝ) ^ 6 := by rw [ht6]; positivity
        rw [← ENNReal.ofReal_add (by positivity) h6, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfin

/-- **The closed `L⁴` jet family `ClosedJetL4Fam Xcl`** from the
closed-input properties (`q = 4`). -/
theorem closedJetL4Fam_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {Xcl : ClosedInputFam} (hReg : ClosedInputRegular Xcl) (hRec : ClosedInputRecursion Xcl)
    (hEnt : ClosedJetEntrance 4 Xcl) : ClosedJetL4Fam Xcl := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨C, hC⟩ := closedJet_lintegral_le hGA hLp hReg hRec le_rfl hEnt b E np τ m T s h K Vs hF
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW j hj ⟨k, hk⟩
  exact hW j hj ⟨k, hk.le⟩

/-- **`ClosedJetHalf`** from the closed-input properties with the weaker entrance
`q = 2`. -/
theorem closedJetHalf_of (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    {Xcl : ClosedInputFam} (hReg : ClosedInputRegular Xcl) (hRec : ClosedInputRecursion Xcl)
    (hEnt : ClosedJetEntrance 2 Xcl) : ClosedJetHalf Xcl := by
  intro b E np τ m T s h K Vs hF
  obtain ⟨C, hC⟩ := closedJet_lintegral_le hGA hLp hReg hRec (by norm_num) hEnt b E np τ m T s h
    K Vs hF
  refine ⟨C, ?_⟩
  filter_upwards [hC] with W hW j hj ⟨k, hk⟩
  exact hW j hj ⟨k, hk.le⟩

/-!
## The shared closed input `b3ClosedX`
-/

/-- **Main theorem: `ClosedJetL4Fam b3ClosedX`** from the contract hypotheses and the three
closed-input estimates (passivity and the one-port recursion of `b3ClosedX`, exact algebra; the
entrance). -/
theorem closedJetL4Fam_b3ClosedX (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hEnt : ClosedJetEntrance 4 b3ClosedX) : ClosedJetL4Fam b3ClosedX :=
  closedJetL4Fam_of hGA hLp (closedInputRegular_b3ClosedX hP) hRec hEnt

/-- **`ClosedJetHalf b3ClosedX`** with the weaker entrance `q = 2`. -/
theorem closedJetHalf_b3ClosedX (hGA : GaussianAbsorptionContract) (hLp : GaussianLpGradient)
    (hP : ClosedInputPassive b3ClosedX) (hRec : ClosedInputRecursion b3ClosedX)
    (hEnt : ClosedJetEntrance 2 b3ClosedX) : ClosedJetHalf b3ClosedX :=
  closedJetHalf_of hGA hLp (closedInputRegular_b3ClosedX hP) hRec hEnt

/-- **`ClosedKMeanInput`** with the shared closed input (through
`closedKMeanInput_of_b3ClosedX`). -/
theorem closedKMeanInput_b3ClosedX (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hS : ClosedKStepForm b3ClosedX)
    (hRec : ClosedInputRecursion b3ClosedX) (hEnt : ClosedJetEntrance 4 b3ClosedX) :
    ClosedKMeanInput :=
  closedKMeanInput_of_b3ClosedX hS (closedJetL4Fam_of hGA hLp
    (closedInputRegular_of_stepForm hS) hRec hEnt)

end BlockBand.SourceProcess.PhysApprox.B3.Jet
