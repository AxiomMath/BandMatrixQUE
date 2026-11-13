module

public import BlockBand.Transmission.Dual.GB1R

/-!
# The glued first-stage path of a random-start family

* `zeta = sup_n e_n` (the chart explosion time, a `𝓖R`-stopping time: `measurableSet_zeta_le`);
* `norm_X_le`: `‖X_n‖ ≤ max(n, ‖X_n(0)‖)`, hence `e_lt_zeta` on a consistent path with finite `ζ`;
* `idx`, `Z` (the glued flat path, `Yf n` on `[0, e_n]`: `Z_eq`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual.G

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.Stochastic.NativeSDE BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

variable {q : ℕ} {D0 : ℝ}
variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : S → Fin (q + q) → ℝ}

namespace B1R

variable (F : B1R D0 q μ ξ)

/-- The exhaustion time `ζ = sup_n e_n`. -/
def zeta (ω : ΩR S q) : WithTop ℝ≥0 := ⨆ n, F.e n ω

theorem e_le_zeta (n : ℕ) (ω : ΩR S q) : F.e n ω ≤ F.zeta ω := le_iSup (fun n => F.e n ω) n

theorem X_eq_of_e_le (n : ℕ) {t m : ℝ≥0} {ω : ΩR S q} (hm : F.e n ω = m) (hmt : m ≤ t) :
    F.X n t ω = F.X n m ω := by
  rw [← (F.strong n).stopped t ω, stoppedProcess_eq_of_ge (by
    show (F.e n ω) ≤ (t : WithTop ℝ≥0); rw [hm]; exact WithTop.coe_le_coe.2 hmt)]
  show F.X n (exitTime (F.X n) (n : ℝ) ω).untopA ω = F.X n m ω
  rw [show exitTime (F.X n) (n : ℝ) ω = F.e n ω from rfl, hm]; rfl

theorem norm_X_le (n : ℕ) (t : ℝ≥0) (ω : ΩR S q) :
    ‖F.X n t ω‖ ≤ max (n : ℝ) ‖chartQInv q (ξ ω.1)‖ := by
  have key : ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ F.e n ω →
      ‖F.X n s ω‖ ≤ max (n : ℝ) ‖chartQInv q (ξ ω.1)‖ := by
    intro s hs
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h | h
    · rw [← h, (F.strong n).init ω]; exact le_max_right _ _
    · exact (norm_le_of_le_exitTimeOf ((F.strong n).continuous ω) h hs).trans (le_max_left _ _)
  by_cases ht : (t : WithTop ℝ≥0) ≤ F.e n ω
  · exact key t ht
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt (not_le.1 ht))
    have hmt : m ≤ t := by
      have := (not_le.1 ht).le; rw [← hm] at this; exact WithTop.coe_le_coe.1 this
    rw [F.X_eq_of_e_le n hm.symm hmt]
    exact key m (by rw [← hm])

/-- On a consistent path with finite `ζ`, every `e_n` is strictly before `ζ`. -/
theorem e_lt_zeta {ω : ΩR S q} (h : F.IsConsAt ω) (hζ : F.zeta ω < ⊤) (n : ℕ) :
    F.e n ω < F.zeta ω := by
  refine lt_of_le_of_ne (F.e_le_zeta n ω) fun heq => ?_
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 hζ.ne
  obtain ⟨k, hk⟩ := exists_nat_ge (max (n : ℝ) ‖chartQInv q (ξ ω.1)‖)
  have hnk : n ≤ k := by exact_mod_cast (le_max_left _ _).trans hk
  have hek : ∀ j, n ≤ j → F.e j ω = m := fun j hj => le_antisymm (hm ▸ F.e_le_zeta j ω)
    (hm ▸ heq ▸ (h n j hj).1)
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ ‖F.X (k + 1) m ω‖ :=
    le_norm_exitTimeOf ((F.strong (k + 1)).continuous ω) (hek (k + 1) (by omega))
  have h2 : F.X k m ω = F.X (k + 1) m ω :=
    (h k (k + 1) (by omega)).2 m (by rw [hek k hnk])
  have h3 := F.norm_X_le k m ω
  have h4 : max (k : ℝ) ‖chartQInv q (ξ ω.1)‖ = k := max_eq_left ((le_max_right _ _).trans hk)
  rw [h2, h4] at h3
  push_cast at h1
  linarith

theorem lt_zeta_of_le_e {ω : ΩR S q} (hc : F.IsConsAt ω) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : (t : WithTop ℝ≥0) < F.zeta ω := by
  by_cases hζ : F.zeta ω < ⊤
  · exact ht.trans_lt (F.e_lt_zeta hc hζ n)
  · rw [not_lt_top_iff.1 hζ]; exact WithTop.coe_lt_top t

open scoped Classical in
/-- The first index whose exit time is after `t` (`0` if none). -/
def idx (t : ℝ≥0) (ω : ΩR S q) : ℕ :=
  if h : ∃ n, (t : WithTop ℝ≥0) < F.e n ω then Nat.find h else 0

/-- The glued flat path. -/
def Z (t : ℝ≥0) (ω : ΩR S q) : Fin (q + q) → ℝ := F.Yf (F.idx t ω) t ω

theorem Z_mem (t : ℝ≥0) (ω : ΩR S q) : F.Z t ω ∈ flatChamber q := F.Yf_mem _ t ω

theorem Z_eq {ω : ΩR S q} (hc : F.IsConsAt ω) {n : ℕ} {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ F.e n ω) : F.Z t ω = F.Yf n t ω := by
  have hex : ∃ m, (t : WithTop ℝ≥0) < F.e m ω := lt_iSup_iff.1 (F.lt_zeta_of_le_e hc ht)
  have hspec := Nat.find_spec hex
  simp only [Z, idx, hex, dite_true]
  rcases le_total n (Nat.find hex) with h | h
  · exact F.Yf_eq_of_le hc h ht
  · exact (F.Yf_eq_of_le hc h hspec.le).symm

theorem Z_eq_zero {ω : ΩR S q} {t : ℝ≥0} (h : ¬∃ n, (t : WithTop ℝ≥0) < F.e n ω) :
    F.Z t ω = F.Yf 0 t ω := by
  simp only [Z, idx, h, dite_false]

theorem measurableSet_zeta_le (t : ℝ≥0) : MeasurableSet[𝓖R μ q t] {ω | F.zeta ω ≤ t} := by
  have : {ω | F.zeta ω ≤ t} = ⋂ n, {ω | F.e n ω ≤ t} := by
    ext ω; rw [mem_iInter]; exact iSup_le_iff (f := fun n => F.e n ω)
  rw [this]
  exact MeasurableSet.iInter fun n => (F.isStoppingTime_e n).measurableSet_le t

/-- `ζ` is a stopping time. -/
theorem isStoppingTime_zeta : IsStoppingTime (𝓖R μ q) F.zeta := F.measurableSet_zeta_le

end B1R

end BlockBand.Transmission.Dual.G
