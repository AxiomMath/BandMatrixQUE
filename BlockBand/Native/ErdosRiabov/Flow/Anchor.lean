module

public import BlockBand.Native.ErdosRiabov.Flow.Scales

/-!
# The anchor time

Parts (a), (b) of the anchor-time lemma of the zigzag argument. Deterministic; no law.

`η♭ = (W/N)²` (`etaFlat`), `𝓛 = {t ∈ [0,1] : η_t ≥ η♭}` (`anchorSet`),
`t♭ = sup 𝓛` if `𝓛 ≠ ∅`, else `0`. Since `η_t = η_0 - t Im m` is affine and strictly decreasing,
`t♭` has the closed form `anchorTime` (`0` if `η_0 < η♭`, else `min 1 ((η_0 - η♭)/Im m)`), and
`anchorTime_isGreatest` shows it is the greatest element of `𝓛` when `𝓛 ≠ ∅`.
Only `Im z > 0`, `N, W ≥ 1` are used.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Flow

open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Adapters.ErdosRiabov (loc_eq_N)
open Set

/-- The delocalization threshold `η♭ = (W/N)²`. -/
def etaFlat (N W : ℕ) : ℝ := ((W : ℝ) / N) ^ 2

/-- `𝓛 = {t ∈ [0,1] : η_t ≥ η♭}`. -/
def anchorSet (z : ℂ) (N W : ℕ) : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ etaFlat N W ≤ vsHeight z t}

/-- The anchor time `t♭` (closed form of `sup 𝓛`, and `0` if `𝓛 = ∅`). -/
def anchorTime (z : ℂ) (N W : ℕ) : ℝ :=
  if vsHeight z 0 < etaFlat N W then 0
  else min 1 ((vsHeight z 0 - etaFlat N W) / (semicircleM z).im)

theorem etaFlat_pos {N W : ℕ} (hN : 0 < N) (hW : 0 < W) : 0 < etaFlat N W := by
  unfold etaFlat
  have : (0 : ℝ) < W := by exact_mod_cast hW
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- `η♭ ≤ 1/16` for rings with `m ≥ 4` blocks (`4W ≤ N`). -/
theorem etaFlat_le {N W : ℕ} (hN : 0 < N) (h4 : 4 * W ≤ N) : etaFlat N W ≤ 1 / 16 := by
  unfold etaFlat
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h4' : 4 * (W : ℝ) ≤ N := by exact_mod_cast h4
  have hq : (W : ℝ) / N ≤ 1 / 4 := by
    rw [div_le_iff₀ hN0]
    linarith
  have hq0 : 0 ≤ (W : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hN0.le
  nlinarith

theorem vsHeight_affine (z : ℂ) (t : ℝ) :
    vsHeight z t = vsHeight z 0 - t * (semicircleM z).im := by
  unfold vsHeight
  ring

/-- `η♭ ≤ η_t ↔ t ≤ (η_0 - η♭)/Im m` (`Im z > 0`). -/
theorem etaFlat_le_iff {z : ℂ} (hη : 0 < z.im) (N W : ℕ) (t : ℝ) :
    etaFlat N W ≤ vsHeight z t ↔ t ≤ (vsHeight z 0 - etaFlat N W) / (semicircleM z).im := by
  have hy := semicircleM_im_pos hη
  rw [le_div_iff₀ hy, vsHeight_affine z t]
  constructor <;> intro h <;> linarith

theorem anchorSet_nonempty_iff {z : ℂ} (hη : 0 < z.im) (N W : ℕ) :
    (anchorSet z N W).Nonempty ↔ etaFlat N W ≤ vsHeight z 0 := by
  have hy := semicircleM_im_pos hη
  constructor
  · rintro ⟨t, ⟨ht0, _⟩, ht⟩
    rw [vsHeight_affine z t] at ht
    nlinarith
  · intro h
    exact ⟨0, ⟨le_refl _, zero_le_one⟩, h⟩

/-- For `t ∈ [0,1]` and `𝓛 ≠ ∅`: `η♭ ≤ η_t ↔ t ≤ t♭`. -/
theorem etaFlat_le_iff_le_anchorTime {z : ℂ} (hη : 0 < z.im) {N W : ℕ}
    (hne : etaFlat N W ≤ vsHeight z 0) {t : ℝ} (ht1 : t ≤ 1) :
    etaFlat N W ≤ vsHeight z t ↔ t ≤ anchorTime z N W := by
  rw [anchorTime, ite_eq_right (not_lt.mpr hne), le_min_iff, etaFlat_le_iff hη]
  exact ⟨fun h => ⟨ht1, h⟩, fun h => h.2⟩

theorem anchorTime_mem {z : ℂ} (hη : 0 < z.im) (N W : ℕ) :
    0 ≤ anchorTime z N W ∧ anchorTime z N W ≤ 1 := by
  have hy := semicircleM_im_pos hη
  unfold anchorTime
  split_ifs with h
  · exact ⟨le_refl _, zero_le_one⟩
  · rw [not_lt] at h
    exact ⟨le_min zero_le_one (div_nonneg (by linarith) hy.le), min_le_left _ _⟩

/-- `t♭` is the greatest element of `𝓛` when `𝓛 ≠ ∅` (so `t♭ = sup 𝓛`), and `𝓛 = [0,t♭]`. -/
theorem anchorTime_isGreatest {z : ℂ} (hη : 0 < z.im) {N W : ℕ}
    (hne : (anchorSet z N W).Nonempty) :
    IsGreatest (anchorSet z N W) (anchorTime z N W) ∧
      anchorSet z N W = Icc 0 (anchorTime z N W) ∧ sSup (anchorSet z N W) = anchorTime z N W := by
  have hne' := (anchorSet_nonempty_iff hη N W).mp hne
  have hm := anchorTime_mem hη N W
  have hset : anchorSet z N W = Icc 0 (anchorTime z N W) := by
    ext t
    constructor
    · rintro ⟨⟨ht0, ht1⟩, ht⟩
      exact ⟨ht0, (etaFlat_le_iff_le_anchorTime hη hne' ht1).mp ht⟩
    · rintro ⟨ht0, ht⟩
      exact ⟨⟨ht0, ht.trans hm.2⟩,
        (etaFlat_le_iff_le_anchorTime hη hne' (ht.trans hm.2)).mpr ht⟩
  have hg : IsGreatest (anchorSet z N W) (anchorTime z N W) := by
    rw [hset]
    exact isGreatest_Icc hm.1
  exact ⟨hg, hset, hg.csSup_eq⟩

/-- Beyond the anchor (`t♭ < t ≤ 1`): `η_t < η♭` and `ℓ_t = N`. -/
theorem lt_etaFlat_of_anchorTime_lt {z : ℂ} (hη : 0 < z.im) {N W : ℕ} (hN : 0 < N) {t : ℝ}
    (ht : anchorTime z N W < t) (ht1 : t ≤ 1) :
    vsHeight z t < etaFlat N W ∧ localizationLength N W (vsHeight z t) = N := by
  have hy := semicircleM_im_pos hη
  have hlt : vsHeight z t < etaFlat N W := by
    by_cases h : vsHeight z 0 < etaFlat N W
    · have ht0 : 0 ≤ t := by
        have := (anchorTime_mem hη N W).1
        linarith
      rw [vsHeight_affine z t]
      nlinarith
    · rw [not_lt] at h
      by_contra hc
      rw [not_lt, etaFlat_le_iff_le_anchorTime hη h ht1] at hc
      linarith
  exact ⟨hlt, loc_eq_N hN (vsHeight_pos hη ht1) hlt.le⟩

/-- **Anchor time, part (a).** For `Im z > 0`, `N ≥ 1`, any `W`, `η♭ = (W/N)²`,
`𝓛 = anchorSet z N W`, `t♭ = anchorTime z N W ∈ [0,1]`: if `𝓛 ≠ ∅` then `𝓛 = [0,t♭]`,
`t♭ = sup 𝓛`, and for `t ∈ [0,t♭]`: `η_t ≥ η♭`, `ℓ_t = W/√η_t`, `ℓ_t²η_t = W²`; if `𝓛 = ∅` then
`t♭ = 0` and `η_t < η♭` for all `t ∈ [0,1]`; in both cases `η_t < η♭` and `ℓ_t = N` for
`t ∈ (t♭,1]`. Also `η♭ ≤ 1/16` if `4W ≤ N`. -/
theorem anchorTime_facts {z : ℂ} (hη : 0 < z.im) {N W : ℕ} (hN : 0 < N) :
    (0 ≤ anchorTime z N W ∧ anchorTime z N W ≤ 1) ∧
      ((anchorSet z N W).Nonempty →
        anchorSet z N W = Icc 0 (anchorTime z N W) ∧
          sSup (anchorSet z N W) = anchorTime z N W ∧
          ∀ t ∈ Icc 0 (anchorTime z N W), etaFlat N W ≤ vsHeight z t ∧
            localizationLength N W (vsHeight z t) = (W : ℝ) / Real.sqrt (vsHeight z t) ∧
            localizationLength N W (vsHeight z t) ^ 2 * vsHeight z t = (W : ℝ) ^ 2) ∧
      (anchorSet z N W = ∅ →
        anchorTime z N W = 0 ∧ ∀ t ∈ Icc (0 : ℝ) 1, vsHeight z t < etaFlat N W) ∧
      (∀ t, anchorTime z N W < t → t ≤ 1 →
        vsHeight z t < etaFlat N W ∧ localizationLength N W (vsHeight z t) = N) ∧
      (4 * W ≤ N → etaFlat N W ≤ 1 / 16) := by
  have hm := anchorTime_mem hη N W
  refine ⟨hm, fun hne => ?_, fun hemp => ?_,
    fun t ht ht1 => lt_etaFlat_of_anchorTime_lt hη hN ht ht1, etaFlat_le hN⟩
  · obtain ⟨_, hset, hsup⟩ := anchorTime_isGreatest hη hne
    refine ⟨hset, hsup, fun t ht => ?_⟩
    have hmem : t ∈ anchorSet z N W := hset ▸ ht
    have hηt := vsHeight_pos hη hmem.1.2
    exact ⟨hmem.2, loc_eq_W_div_sqrt hN hηt hmem.2, (loc_sq_mul hN hηt).2.mpr hmem.2⟩
  · have h0 : vsHeight z 0 < etaFlat N W := by
      by_contra hc
      rw [not_lt, ← anchorSet_nonempty_iff hη N W, hemp] at hc
      exact not_nonempty_empty hc
    refine ⟨by rw [anchorTime, ite_eq_left h0], fun t ht => ?_⟩
    have hy := semicircleM_im_pos hη
    rw [vsHeight_affine z t]
    nlinarith [ht.1]

/-- **Anchor time, part (b): height partition.** For `Im z > 0`, `N, W ≥ 1` and `0 ≤ s ≤ t ≤ 1`,
one of: **(1)** `η_t ≥ η♭`, `𝓛 ≠ ∅`, `t ≤ t♭`; **(2a)** `η_s ≤ η♭`, `ℓ_s = ℓ_t = N`,
`η_t ≤ η_s`; **(2b)** `η_t < η♭ < η_s`, `s < t♭ < t`, `η_{t♭} = η♭`, `ℓ_{t♭} = N`,
`ℓ_{t♭}²η_{t♭} = W²`, `ℓ_t = N`. -/
theorem anchorTime_partition {z : ℂ} (hη : 0 < z.im) {N W : ℕ} (hN : 0 < N) (hW : 0 < W)
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    (etaFlat N W ≤ vsHeight z t ∧ (anchorSet z N W).Nonempty ∧ t ≤ anchorTime z N W) ∨
      (vsHeight z s ≤ etaFlat N W ∧ localizationLength N W (vsHeight z s) = N ∧
        localizationLength N W (vsHeight z t) = N ∧ vsHeight z t ≤ vsHeight z s) ∨
      (vsHeight z t < etaFlat N W ∧ etaFlat N W < vsHeight z s ∧ s < anchorTime z N W ∧
        anchorTime z N W < t ∧ vsHeight z (anchorTime z N W) = etaFlat N W ∧
        localizationLength N W (vsHeight z (anchorTime z N W)) = N ∧
        localizationLength N W (vsHeight z (anchorTime z N W)) ^ 2 *
          vsHeight z (anchorTime z N W) = (W : ℝ) ^ 2 ∧
        localizationLength N W (vsHeight z t) = N) := by
  have hy := semicircleM_im_pos hη
  have hηt := vsHeight_pos hη ht1
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hts : vsHeight z t ≤ vsHeight z s := by
    rw [vsHeight_affine z t, vsHeight_affine z s]
    nlinarith
  by_cases h1 : etaFlat N W ≤ vsHeight z t
  · have hne : (anchorSet z N W).Nonempty := ⟨t, ⟨hs0.trans hst, ht1⟩, h1⟩
    have hne' := (anchorSet_nonempty_iff hη N W).mp hne
    exact Or.inl ⟨h1, hne, (etaFlat_le_iff_le_anchorTime hη hne' ht1).mp h1⟩
  rw [not_le] at h1
  by_cases h2 : vsHeight z s ≤ etaFlat N W
  · exact Or.inr (Or.inl ⟨h2, loc_eq_N hN hηs h2, loc_eq_N hN hηt (h1.le), hts⟩)
  rw [not_le] at h2
  right
  right
  have hne' : etaFlat N W ≤ vsHeight z 0 := by
    have : vsHeight z s ≤ vsHeight z 0 := by
      rw [vsHeight_affine z s]
      nlinarith
    linarith
  set τ := (vsHeight z 0 - etaFlat N W) / (semicircleM z).im with hτ
  have hsτ : s < τ := by
    rw [hτ, lt_div_iff₀ hy]
    rw [vsHeight_affine z s] at h2
    linarith
  have htτ : τ < t := by
    by_contra hc
    rw [not_lt] at hc
    have := (etaFlat_le_iff hη N W t).mpr hc
    linarith
  have hanc : anchorTime z N W = τ := by
    rw [anchorTime, ite_eq_right (not_lt.mpr hne'), min_eq_right (by linarith)]
  have hητ : vsHeight z τ = etaFlat N W := by
    rw [vsHeight_affine z τ, hτ]
    field_simp
    ring
  have hflat := etaFlat_pos hN hW
  refine ⟨h1, h2, by rw [hanc]; exact hsτ, by rw [hanc]; exact htτ, by rw [hanc, hητ], ?_, ?_,
    loc_eq_N hN hηt h1.le⟩
  · rw [hanc, hητ]
    exact loc_eq_N hN hflat le_rfl
  · rw [hanc, hητ]
    exact (loc_sq_mul hN hflat).2.mpr le_rfl

end BlockBand.Native.ErdosRiabov.Flow
