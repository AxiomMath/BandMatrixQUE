module

public import BlockBand.Palm.MomentFlow.EventControl
public import BlockBand.Palm.MomentFlow.EventNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The overlap bound at a fixed time (`X_i ≤ C N^{4ε} q*Γq`)

At a fixed time `σ`, outside an event of probability `≤ N^{-D}`, every eigenvalue `λ_i(σ)` in the
bulk window has overlap `X_i = N|q* u_i(σ)|² ≤ C N^{4ε} q*Γq` (`overlap_event_fixed_time`), by
the overlap bound on an energy grid of spacing `N^{-1+4ε}` and `Γ(z) ≍ Γ`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Internal.Contracts.Inputs BlockBand.External BlockBand.Palm.CoarseRelative
open scoped ENNReal Matrix.Norms.L2Operator

variable {N : ℕ}

/-- `2 (1 + 1/√(π v₀)) · gammaCompConst`. -/
def overlapConst (c₀ r₀ s₀ v₀ : ℝ) : ℝ :=
  2 * (1 + 1 / Real.sqrt (Real.pi * v₀)) * gammaCompConst c₀ r₀ s₀ v₀

/-- The energy grid `E - r₀/2 + kη`, `0 ≤ k ≤ ⌈r₀/η⌉₊`. -/
def energyGrid (E r₀ η : ℝ) : Finset ℝ :=
  (Finset.range (⌈r₀ / η⌉₊ + 1)).image (fun k : ℕ => E - r₀ / 2 + k * η)

theorem energyGrid_cover {E r₀ η : ℝ} (hη : 0 < η) {lam : ℝ}
    (hl : |lam - E| ≤ r₀ / 2) : ∃ x ∈ energyGrid E r₀ η, |lam - x| ≤ η := by
  set t := (lam - (E - r₀ / 2)) / η
  have ht0 : 0 ≤ t := div_nonneg (by linarith [(abs_le.1 hl).1]) hη.le
  have htr : t ≤ r₀ / η := div_le_div_of_nonneg_right (by linarith [(abs_le.1 hl).2]) hη.le
  refine ⟨E - r₀ / 2 + (⌊t⌋₊ : ℝ) * η, Finset.mem_image.2 ⟨⌊t⌋₊, ?_, rfl⟩, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_of_le ((htr).trans (Nat.le_ceil _))
  · have h1 := Nat.floor_le ht0
    have h2 := Nat.lt_floor_add_one t
    have e : lam = E - r₀ / 2 + t * η := by simp only [t]; field_simp; ring
    rw [abs_le]
    constructor <;> nlinarith

theorem energyGrid_window {E r₀ η : ℝ} (hη : 0 < η) (hηr : η ≤ r₀ / 2) (hr : 0 < r₀) {x : ℝ}
    (hx : x ∈ energyGrid E r₀ η) : |x - E| ≤ r₀ := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  have hk' : (k : ℝ) ≤ r₀ / η + 1 := by
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have h2 : ((⌈r₀ / η⌉₊ : ℕ) : ℝ) < r₀ / η + 1 := Nat.ceil_lt_add_one (by positivity)
    exact le_trans (by exact_mod_cast this) h2.le
  have hkη : (k : ℝ) * η ≤ r₀ + η := by
    have := mul_le_mul_of_nonneg_right hk' hη.le
    rwa [add_mul, div_mul_cancel₀ _ hη.ne', one_mul] at this
  rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) k]

theorem energyGrid_card_le {E r₀ η : ℝ} (hη : 0 < η) (hr : 0 < r₀) :
    ((energyGrid E r₀ η).card : ℝ) ≤ r₀ / η + 2 := by
  have h1 : (energyGrid E r₀ η).card ≤ ⌈r₀ / η⌉₊ + 1 :=
    Finset.card_image_le.trans (by simp)
  have h2 : ((⌈r₀ / η⌉₊ : ℕ) : ℝ) < r₀ / η + 1 := Nat.ceil_lt_add_one (by positivity)
  have : ((energyGrid E r₀ η).card : ℝ) ≤ ((⌈r₀ / η⌉₊ + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at this
  linarith

theorem eventually_rpow_ge {p : ℝ} (hp : 0 < p) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ p :=
  ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

theorem eventually_rpow_le {p : ℝ} (hp : 0 < p) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-p) ≤ K :=
  (((tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop).eventually
    (gt_mem_nhds hK)).mono fun _ h => h.le

/-- **Overlap bound at a fixed time.** -/
theorem overlap_event_fixed_time (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification)
    {A c₀ r₀ s₀ v₀ : ℝ} (hK : FreshConstants c₀ r₀ s₀ v₀) {ε : ℝ} (hε : 0 < ε)
    (hε4 : ε < 1 / 4) (D : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (F : Matrix (Fin N) (Fin N) ℂ) (E : ℝ),
      FreshClass F A c₀ E r₀ s₀ v₀ → ∀ σ ∈ Icc (c₀ - s₀) c₀, ∀ a : ℝ, 0 ≤ a → a ≤ σ →
      ∀ q : Fin N → ℂ, ∃ Bad : Set (FlowSample N),
        flowLaw N a Bad ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) ∧
        ∀ ω ∉ Bad, ω.1.IsHermitian → HasSimpleSpectrum N (flowMatrix F a ω σ) →
          ∀ i : Fin N, |flowEigenvalue F a ω σ i - E| ≤ r₀ / 2 →
            flowOverlap F a q σ i ω ≤
              overlapConst c₀ r₀ s₀ v₀ * (N : ℝ) ^ (4 * ε) * quadForm (freshGamma F c₀ E) q := by
  have hK' := hK
  obtain ⟨hc0, hc1, hr0, hs0, hs0c, hv0⟩ := hK
  have hcs : 0 < c₀ - s₀ := by linarith
  set ρ0 := Real.sqrt (c₀ - s₀)
  have hρ0 : 0 < ρ0 := Real.sqrt_pos.2 hcs
  set κ := max A 0 + 1
  set D' := max D 0 + 2
  have hD' : 0 < D' := by positivity
  obtain ⟨N₁, hN₁, hloc⟩ := flowLaw_isotropicBad_freshM_le hELG hMDE κ ρ0⁻¹ ε ε D' hε hε hD'
  have h14 : 0 < 1 - 4 * ε := by linarith
  have ev : ∀ᶠ n : ℕ in atTop, N₁ ≤ n ∧ (1 : ℝ) ≤ n ∧
      (n : ℝ) ^ (-(1 - 4 * ε)) ≤ min 1 (r₀ / 2) ∧ Real.pi / v₀ ≤ (n : ℝ) ^ (3 * ε) ∧
      (2 + 2 / v₀ + r₀) / ρ0 ≤ (n : ℝ) ∧ r₀ + 2 ≤ (n : ℝ) := by
    refine (eventually_ge_atTop N₁).and ((tendsto_natCast_atTop_atTop.eventually_ge_atTop 1).and
      ((eventually_rpow_le h14 (lt_min one_pos (by linarith))).and
      ((eventually_rpow_ge (by linarith) _).and
      ((tendsto_natCast_atTop_atTop.eventually_ge_atTop _).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)))))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 ev
  refine ⟨N₀, fun N hN F E hC σ hσ a ha haσ q => ?_⟩
  obtain ⟨hNN₁, hN1, hηsmall, hdens, hnormN, hcardN⟩ := hN₀ N hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hNpos : 0 < N := by exact_mod_cast hNp
  have hσ0 : 0 < σ := by linarith [hσ.1]
  set η : ℝ := (N : ℝ) ^ (-(1 - 4 * ε))
  have hη : 0 < η := Real.rpow_pos_of_pos hNp _
  have hη1 : η ≤ 1 := hηsmall.trans (min_le_left _ _)
  have hηr : η ≤ r₀ / 2 := hηsmall.trans (min_le_right _ _)
  have hNη : (N : ℝ) * η = (N : ℝ) ^ (4 * ε) := by
    simp only [η]
    rw [← Real.rpow_one_add' hNp.le (by linarith)]
    congr 1; ring
  obtain ⟨M⟩ := exists_mdeBranch_eq_freshM hMDE hNpos hC.1 hσ0
  have hrpow_mono : ∀ {p r : ℝ}, p ≤ r → (N : ℝ) ^ p ≤ (N : ℝ) ^ r := fun h =>
    Real.rpow_le_rpow_of_exponent_le hN1 h
  -- the CEH hypotheses at each grid point
  have hFn : (Real.sqrt σ)⁻¹ * ‖F‖ ≤ ρ0⁻¹ * (N : ℝ) ^ κ :=
    (cehNormBound_uniform hC.2.1 hcs hσ.1).trans
      (mul_le_mul_of_nonneg_left (hrpow_mono (by simp only [κ]; linarith [le_max_left A 0]))
        (by positivity))
  have hdom : ∀ x ∈ energyGrid E r₀ η, CEH.InLocalLawDomain M κ ε ⟨x, η⟩ := by
    intro x hx
    have hxw := energyGrid_window hη hηr hr0 hx
    refine inLocalLawDomain_of_bulk hMDE hNpos hK' hC hσ hxw hη hη1 M ?_ ?_
    · show (N : ℝ) ^ ε ≤ (N : ℝ) * η * (v₀ / Real.pi)
      rw [hNη]
      have e : (N : ℝ) ^ (4 * ε) = (N : ℝ) ^ ε * (N : ℝ) ^ (3 * ε) := by
        rw [← Real.rpow_add hNp]; ring_nf
      rw [e]
      have hNe : 0 ≤ (N : ℝ) ^ ε := by positivity
      have : (N : ℝ) ^ ε * (Real.pi / v₀) * (v₀ / Real.pi) = (N : ℝ) ^ ε := by
        field_simp
      calc (N : ℝ) ^ ε = (N : ℝ) ^ ε * (Real.pi / v₀) * (v₀ / Real.pi) := this.symm
        _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (3 * ε) * (v₀ / Real.pi) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdens hNe) (by positivity)
    · have hz := norm_z_le hNpos hK' hC (z := ⟨x, η⟩) hxw hη.le hη1
      have hsq : ρ0 ≤ Real.sqrt σ := Real.sqrt_le_sqrt hσ.1
      have hm1 : (1 : ℝ) ≤ (N : ℝ) ^ max A 0 := Real.one_le_rpow hN1 (le_max_right _ _)
      have hmA : (N : ℝ) ^ A ≤ (N : ℝ) ^ max A 0 := hrpow_mono (le_max_left _ _)
      have hpow : (N : ℝ) ^ max A 0 * N ≤ (N : ℝ) ^ (κ + 1 / ε) := by
        have : (N : ℝ) ^ max A 0 * N = (N : ℝ) ^ (max A 0 + 1) := by
          rw [Real.rpow_add hNp, Real.rpow_one]
        rw [this]; exact hrpow_mono (by simp only [κ]; have := one_div_pos.2 hε; linarith)
      have hρN : 2 + 2 / v₀ + r₀ ≤ ρ0 * N := by
        rw [div_le_iff₀ hρ0] at hnormN; linarith
      calc ‖(⟨x, η⟩ : ℂ)‖ ≤ (N : ℝ) ^ A + 2 / v₀ + r₀ + 1 := hz
        _ ≤ (N : ℝ) ^ max A 0 * (2 + 2 / v₀ + r₀) := by
            have : 0 ≤ 2 / v₀ + r₀ + 1 := by positivity
            nlinarith
        _ ≤ (N : ℝ) ^ max A 0 * (ρ0 * N) :=
            mul_le_mul_of_nonneg_left hρN (by positivity)
        _ = ρ0 * ((N : ℝ) ^ max A 0 * N) := by ring
        _ ≤ Real.sqrt σ * (N : ℝ) ^ (κ + 1 / ε) :=
            mul_le_mul hsq hpow (by positivity) (Real.sqrt_nonneg _)
  have him : ∀ x ∈ energyGrid E r₀ η, 0 < (freshDyson F σ ⟨x, η⟩).im := by
    intro x hx
    have hxw := energyGrid_window hη hηr hr0 hx
    exact lt_of_lt_of_le hv0 (fresh_regular_bounds hC.2.2 hσ hxw hη.le hη1).1
  set badx : ℝ → Set (FlowSample N) := fun x => {ω | (N : ℝ) ^ ε *
      CEH.isotropicControl (freshM F σ ⟨x, η⟩) ⟨x, η⟩ q q <
      ‖star q ⬝ᵥ (((flowMatrix F a ω σ - (⟨x, η⟩ : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ -
        freshM F σ ⟨x, η⟩) *ᵥ q)‖}
  refine ⟨⋃ x ∈ energyGrid E r₀ η, badx x, ?_, ?_⟩
  · have hcard : ((energyGrid E r₀ η).card : ℝ) * (N : ℝ) ^ (-D') ≤ (N : ℝ) ^ (-D) := by
      have h1 := energyGrid_card_le (E := E) hη hr0
      have h2 : r₀ / η ≤ r₀ * N := by
        rw [div_le_iff₀ hη, mul_assoc, hNη]
        have : (1 : ℝ) ≤ (N : ℝ) ^ (4 * ε) := Real.one_le_rpow hN1 (by linarith)
        nlinarith
      have h3 : ((energyGrid E r₀ η).card : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two]; nlinarith
      calc ((energyGrid E r₀ η).card : ℝ) * (N : ℝ) ^ (-D')
          ≤ (N : ℝ) ^ (2 : ℝ) * (N : ℝ) ^ (-D') :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = (N : ℝ) ^ (-max D 0) := by rw [← Real.rpow_add hNp]; congr 1; simp only [D']; ring
        _ ≤ (N : ℝ) ^ (-D) := hrpow_mono (by linarith [le_max_left D 0])
    calc flowLaw N a (⋃ x ∈ energyGrid E r₀ η, badx x)
        ≤ ∑ x ∈ energyGrid E r₀ η, flowLaw N a (badx x) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _x ∈ energyGrid E r₀ η, ENNReal.ofReal ((N : ℝ) ^ (-D')) :=
          Finset.sum_le_sum fun x hx => hloc N hNN₁ a σ ha haσ hσ0 F hC.1 hFn M ⟨x, η⟩
            (hdom x hx) hη (him x hx) q q
      _ = ENNReal.ofReal (((energyGrid E r₀ η).card : ℝ) * (N : ℝ) ^ (-D')) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hcard
  · intro ω hω hH hs i hi
    obtain ⟨x, hxX, hix⟩ := energyGrid_cover hη hi
    have hxw := energyGrid_window hη hηr hr0 hxX
    have hnot : ω ∉ badx x := fun h' => hω (mem_biUnion hxX h')
    simp only [badx, Set.mem_ofPred_eq, not_lt] at hnot
    have hb := overlap_combined_le hK' hC hσ hxw hη hη1 hNpos q
      (flowMatrix_isHermitian hC.1 a hH σ) hs hnot i hix
    have hγ : 0 ≤ quadForm (freshGamma F c₀ E) q := by
      rw [freshGamma_quad_eq hC.1]
      exact mul_nonneg hc0.le (Finset.sum_nonneg fun _ _ => by positivity)
    have hKc : 0 ≤ gammaCompConst c₀ r₀ s₀ v₀ := by
      unfold gammaCompConst; simp only
      have : 0 < (c₀ - s₀) * v₀ := mul_pos hcs hv0
      positivity
    have hsqrt : Real.sqrt (Real.pi * v₀ * N * η) =
        Real.sqrt (Real.pi * v₀) * (N : ℝ) ^ (2 * ε) := by
      rw [mul_assoc, hNη, Real.sqrt_mul (by positivity)]
      congr 1
      rw [show (N : ℝ) ^ (4 * ε) = ((N : ℝ) ^ (2 * ε)) ^ 2 by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; norm_num; ring_nf]
      exact Real.sqrt_sq (by positivity)
    have hfac : 2 * N * η * (1 + (N : ℝ) ^ ε / Real.sqrt (Real.pi * v₀ * N * η)) ≤
        2 * (1 + 1 / Real.sqrt (Real.pi * v₀)) * (N : ℝ) ^ (4 * ε) := by
      rw [hsqrt, show 2 * (N : ℝ) * η = 2 * ((N : ℝ) * η) by ring, hNη]
      have hspv : 0 < Real.sqrt (Real.pi * v₀) := Real.sqrt_pos.2 (by positivity)
      have hle : (N : ℝ) ^ ε / (Real.sqrt (Real.pi * v₀) * (N : ℝ) ^ (2 * ε)) ≤
          1 / Real.sqrt (Real.pi * v₀) := by
        rw [div_le_div_iff₀ (by positivity) hspv]
        have : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (2 * ε) := hrpow_mono (by linarith)
        nlinarith
      have h4 : 0 ≤ (N : ℝ) ^ (4 * ε) := by positivity
      nlinarith
    calc flowOverlap F a q σ i ω
        ≤ 2 * N * η * (1 + (N : ℝ) ^ ε / Real.sqrt (Real.pi * v₀ * N * η)) *
          (gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q) := hb
      _ ≤ 2 * (1 + 1 / Real.sqrt (Real.pi * v₀)) * (N : ℝ) ^ (4 * ε) *
          (gammaCompConst c₀ r₀ s₀ v₀ * quadForm (freshGamma F c₀ E) q) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hKc hγ)
      _ = overlapConst c₀ r₀ s₀ v₀ * (N : ℝ) ^ (4 * ε) * quadForm (freshGamma F c₀ E) q := by
          unfold overlapConst; ring

end BlockBand.Palm.MomentFlow
