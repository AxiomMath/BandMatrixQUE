module

public import BlockBand.Palm.MomentFlow.PropD6
public import BlockBand.Palm.MomentFlow.Tail6Fwd
public import BlockBand.Palm.MomentFlow.BridgeVersion

/-!
# Canonical `𝓛`-measurable full and short moment flows

`RegVersion` does not make a version measurable in `ω`. The flows are therefore built
canonically, as in `tail6_core`:

* `canonDatum F a c q ω ζ`: the jointly measurable version `momentVersion` at time `a`
  (`𝓛`-measurable, bounded by `momentLevel q ζ`), a.s. equal to `condMoment(a, ζ)`
  (`canonDatum_ae_eq`, via simple spectrum at time `a` from `ae_noCollision`).
* `gapSet F a c n`: all gaps on `[a,c]` are `≥ gapLevel n = 1/(n+1)`; `𝓛`-measurable, increasing,
  and a.s. `ω ∈ gapSet n` for some `n`.
* `fullC`, `shortC`: `truncForward` at gap level `1/(n+1)` with all pairs (`ℓ = N`) and
  with short pairs; on `gapSet n` they are the exact full and short moment flows from
  `canonDatum`, bounded by `overlapBound^r`, independent of `n`.
* `regVersion_eq_fullC`: every `RegVersion` agrees a.s. with `fullC` on `[a,c]`;
  `shortSol_eq_shortC`: every short solution from the same datum is `shortC`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission

variable {N : ℕ}

/-- Gap level `1/(n+1)`. -/
def gapLevel (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem gapLevel_pos (n : ℕ) : 0 < gapLevel n := by unfold gapLevel; positivity

theorem gapLevel_succ_le (n : ℕ) : gapLevel (n + 1) ≤ gapLevel n := by
  unfold gapLevel
  exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)

/-- All gaps on `[a,c]` are at least `1/(n+1)`. -/
def gapSet (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (n : ℕ) : Set (FlowSample N) :=
  {ω | ∀ x ∈ Icc a c, ∀ k m : Fin N, k ≠ m →
    gapLevel n ≤ |flowEigenvalue F a ω x k - flowEigenvalue F a ω x m|}

theorem measurableSet_gapSet {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (a c : ℝ)
    (n : ℕ) : MeasurableSet[pathSigma F a a c] (gapSet F a c n) :=
  measurableSet_gap F hF le_rfl le_rfl (gapLevel n)

theorem gapSet_mono (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (n : ℕ) :
    gapSet F a c n ⊆ gapSet F a c (n + 1) := fun _ hω x hx k m hkm =>
  (gapLevel_succ_le n).trans (hω x hx k m hkm)

theorem ae_exists_gapSet (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    ∀ᵐ ω ∂flowLaw N a, ∃ n, ω ∈ gapSet F a c n := by
  filter_upwards [ae_noCollision hDBM hF ha] with ω hω
  obtain ⟨n, hn⟩ := exists_gap_of_noCollision hF a hac ω
    fun x hx i j hij => hω.2 x hx.1 i j hij
  exact ⟨n, hn⟩

/-- With `ℓ = N` the short rates are the full rates. -/
theorem shortFlowRate_full (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (σ : ℝ) :
    shortFlowRate F a ω N σ = flowRate F a ω σ := by
  funext i j
  have h : labelDist i j < N := by
    unfold labelDist; have := i.isLt; have := j.isLt; omega
  simp [shortFlowRate, maskRate, h]

/-!
## The canonical datum
-/

/-- The `𝓛`-measurable datum at time `a`: the jointly measurable version of `condMoment`. -/
def canonDatum (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) :
    FlowSample N → Occ N → ℝ :=
  fun ω ζ => momentVersion F a a c q ζ a ω

theorem measurable_canonDatum (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ)
    (ζ : Occ N) : Measurable[pathSigma F a a c] fun ω => canonDatum F a c q ω ζ :=
  measurable_momentVersion_slice F a a c q ζ a

theorem abs_canonDatum_le (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ)
    {r : ℕ} {ζ : Occ N} (hζ : ζ ∈ sector N r) (ω : FlowSample N) :
    |canonDatum F a c q ω ζ| ≤ overlapBound N q ^ r := by
  have h := abs_momentVersion_le F a a c q ζ a ω
  unfold momentLevel at h
  rwa [mem_sector.1 hζ] at h

theorem canonDatum_ae_eq (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a : ℝ} (ha : 0 < a) (c : ℝ) (q : Fin N → ℂ) (ζ : Occ N) :
    (fun ω => canonDatum F a c q ω ζ) =ᵐ[flowLaw N a] condMoment F a c q a ζ := by
  refine (momentVersion_ae_eq F a a c q ζ a).trans (condExp_congr_ae ?_)
  filter_upwards [ae_noCollision hDBM hF ha] with ω hω
  have hH := BlockBand.Palm.GoodEvent.flowMatrix_isHermitian hF a hω.1 a
  exact clampedMoment_eq q ζ hH
    (hasSimpleSpectrum_of_injective hH fun i j hij => hω.2 a le_rfl i j hij)

/-!
## Canonical flows
-/

/-- Canonical full flow (all pairs, gap level `1/(n+1)`). -/
def fullC (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (r n : ℕ) (v : ℝ)
    (ω : FlowSample N) : Occ N → ℝ :=
  truncForward F a N (gapLevel n) a c r (canonDatum F a c q) v ω

/-- Canonical short flow (`|i-j| < ℓ`, gap level `1/(n+1)`). -/
def shortC (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ) (v : ℝ)
    (ω : FlowSample N) : Occ N → ℝ :=
  truncForward F a ℓ (gapLevel n) a c r (canonDatum F a c q) v ω

theorem measurable_fullC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (r n : ℕ) (v : ℝ) (ζ : Occ N) :
    Measurable[pathSigma F a a c] fun ω => fullC F a c q r n v ω ζ :=
  measurable_truncForward hF hN N (gapLevel_pos n) le_rfl hac le_rfl r
    (measurable_canonDatum F a c q) v ζ

theorem measurable_shortC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (v : ℝ) (ζ : Occ N) :
    Measurable[pathSigma F a a c] fun ω => shortC F a c q ℓ r n v ω ζ :=
  measurable_truncForward hF hN ℓ (gapLevel_pos n) le_rfl hac le_rfl r
    (measurable_canonDatum F a c q) v ζ

theorem continuous_fullC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a c : ℝ) (q : Fin N → ℂ) (r n : ℕ) (ω : FlowSample N) (ζ : Occ N) :
    Continuous fun v => fullC F a c q r n v ω ζ :=
  continuous_truncForward hF hN a N (gapLevel_pos n) a c r _ ω ζ

theorem continuous_shortC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ) (ω : FlowSample N) (ζ : Occ N) :
    Continuous fun v => shortC F a c q ℓ r n v ω ζ :=
  continuous_truncForward hF hN a ℓ (gapLevel_pos n) a c r _ ω ζ

theorem fullC_isSolution {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    IsMomentFlowSolution (flowRate F a ω) r a c (fun v => fullC F a c q r n v ω) ∧
      ∀ ζ ∈ sector N r, fullC F a c q r n a ω ζ = canonDatum F a c q ω ζ := by
  have h := truncForward_isSolution hF hN a N (gapLevel_pos n) hac r (canonDatum F a c q) ω hω
  have e : shortFlowRate F a ω N = flowRate F a ω := funext fun σ => shortFlowRate_full F a ω σ
  rw [e] at h
  exact h

theorem shortC_isSolution {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    IsMomentFlowSolution (shortFlowRate F a ω ℓ) r a c (fun v => shortC F a c q ℓ r n v ω) ∧
      ∀ ζ ∈ sector N r, shortC F a c q ℓ r n a ω ζ = canonDatum F a c q ω ζ :=
  truncForward_isSolution hF hN a ℓ (gapLevel_pos n) hac r (canonDatum F a c q) ω hω

theorem abs_fullC_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r, |fullC F a c q r n v ω ζ| ≤ overlapBound N q ^ r := by
  obtain ⟨hs, h0⟩ := fullC_isSolution hF hN hac q r n hω
  intro v hv ζ hζ
  have hb := flowMoment_bounds F a ω r hs (m := -(overlapBound N q ^ r))
    (M := overlapBound N q ^ r)
    (fun ξ hξ => by rw [h0 ξ hξ]; exact neg_le_of_abs_le (abs_canonDatum_le F a c q hξ ω))
    (fun ξ hξ => by rw [h0 ξ hξ]; exact le_of_abs_le (abs_canonDatum_le F a c q hξ ω)) v hv ζ hζ
  exact abs_le.2 hb

theorem abs_shortC_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r, |shortC F a c q ℓ r n v ω ζ| ≤ overlapBound N q ^ r := by
  obtain ⟨hs, h0⟩ := shortC_isSolution hF hN hac q ℓ r n hω
  intro v hv ζ hζ
  have hb := shortFlowMoment_bounds F a ω ℓ r hs (m := -(overlapBound N q ^ r))
    (M := overlapBound N q ^ r)
    (fun ξ hξ => by rw [h0 ξ hξ]; exact neg_le_of_abs_le (abs_canonDatum_le F a c q hξ ω))
    (fun ξ hξ => by rw [h0 ξ hξ]; exact le_of_abs_le (abs_canonDatum_le F a c q hξ ω)) v hv ζ hζ
  exact abs_le.2 hb

theorem fullC_succ {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r, fullC F a c q r (n + 1) v ω ζ = fullC F a c q r n v ω ζ := by
  obtain ⟨hs, h0⟩ := fullC_isSolution hF hN hac q r n hω
  obtain ⟨hs', h0'⟩ := fullC_isSolution hF hN hac q r (n + 1) (gapSet_mono F a c n hω)
  exact flowMoment_unique F a ω r hs' hs fun ζ hζ => by rw [h0 ζ hζ, h0' ζ hζ]

theorem shortC_succ {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r,
      shortC F a c q ℓ r (n + 1) v ω ζ = shortC F a c q ℓ r n v ω ζ := by
  obtain ⟨hs, h0⟩ := shortC_isSolution hF hN hac q ℓ r n hω
  obtain ⟨hs', h0'⟩ := shortC_isSolution hF hN hac q ℓ r (n + 1) (gapSet_mono F a c n hω)
  exact hs'.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hs
    fun ζ hζ => by rw [h0 ζ hζ, h0' ζ hζ]

/-- A regular version starts a.s. at the canonical datum. -/
theorem regVersion_start (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) {q : Fin N → ℂ} {r : ℕ}
    {Φ : ℝ → Occ N → FlowSample N → ℝ} (hΦ : RegVersion F a c q r Φ) :
    ∀ᵐ ω ∂flowLaw N a, ∀ ζ ∈ sector N r, Φ a ζ ω = canonDatum F a c q ω ζ := by
  have h : ∀ ζ : Occ N, ∀ᵐ ω ∂flowLaw N a, ζ ∈ sector N r → Φ a ζ ω = canonDatum F a c q ω ζ := by
    intro ζ
    by_cases hζ : ζ ∈ sector N r
    · filter_upwards [hΦ.1 a ⟨le_rfl, hac⟩ ζ hζ, canonDatum_ae_eq hDBM hF ha c q ζ] with ω h1 h2 _
      rw [h1, h2]
    · exact Eventually.of_forall fun _ h => absurd h hζ
  filter_upwards [ae_all_iff.2 h] with ω hω ζ hζ
  exact hω ζ hζ

/-- **Every regular version is a.s. the canonical full flow** on `[a,c]` (`flowMoment_unique`). -/
theorem regVersion_eq_fullC (hDBM : DysonBrownianMotion N) {F : Matrix (Fin N) (Fin N) ℂ}
    (hF : F.IsHermitian) (hN : 0 < N) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) {q : Fin N → ℂ}
    {r : ℕ} {Φ : ℝ → Occ N → FlowSample N → ℝ} (hΦ : RegVersion F a c q r Φ) :
    ∀ᵐ ω ∂flowLaw N a, (∀ ζ ∈ sector N r, Φ a ζ ω = canonDatum F a c q ω ζ) ∧
      IsMomentFlowSolution (flowRate F a ω) r a c (fun σ ξ => Φ σ ξ ω) ∧
      ∀ n, ω ∈ gapSet F a c n → ∀ σ ∈ Icc a c, ∀ ζ ∈ sector N r,
        Φ σ ζ ω = fullC F a c q r n σ ω ζ := by
  filter_upwards [regVersion_start hDBM hF ha hac hΦ, hΦ.2] with ω h0 hs
  refine ⟨h0, hs, fun n hn => ?_⟩
  obtain ⟨hs', h0'⟩ := fullC_isSolution hF hN hac q r n hn
  exact flowMoment_unique F a ω r hs hs' fun ζ hζ => by rw [h0 ζ hζ, h0' ζ hζ]

/-- **Every short solution from the canonical datum is the canonical short flow.** -/
theorem shortSol_eq_shortC {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) {h : ℝ → Occ N → ℝ} (hh : ShortSol F a c ω ℓ r h)
    (h0 : ∀ ζ ∈ sector N r, h a ζ = canonDatum F a c q ω ζ) :
    ∀ σ ∈ Icc a c, ∀ ζ ∈ sector N r, h σ ζ = shortC F a c q ℓ r n σ ω ζ := by
  obtain ⟨hs', h0'⟩ := shortC_isSolution hF hN hac q ℓ r n hω
  exact hh.eq_of_initial_eq (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j) hs'
    fun ζ hζ => by rw [h0 ζ hζ, h0' ζ hζ]

end BlockBand.Palm.MomentFlow
