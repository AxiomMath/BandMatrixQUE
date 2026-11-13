module

public import BlockBand.Transmission.Dual.UniqueReg
public import BlockBand.Transmission.Dual.PathLift

/-!
# Uniqueness in law: the front-padded flat state

For a level `n ≤ p` the front-padded flat state is
`(0^{p−n}, x₀ … x_{n−1}; 0^{p−n}, y₀ … y_{n−1}) ∈ ℝ^{p+p}` (`padState`).
* `continuous_padState`: along a deletion path with `n₀ ≤ p` it is continuous at **every**
  time (the deleted pair goes to `0` and the survivors slide one place to the right).
* `padState_mem_flatChamber_iff`: it lies in the flat chamber exactly at level `p`.
* `unpadAt_padState`: at a known level `n`, the truncated state is a coordinate projection of
  the padded state.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Dual

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath
open scoped NNReal ENNReal

variable {p : ℕ}

/-- Front padding of the first `n` entries of `x` to length `p`. -/
def padX (p n : ℕ) (x : ℕ → ℝ) : Fin p → ℝ :=
  fun j => if p - n ≤ (j : ℕ) then x (j - (p - n)) else 0

/-- The front-padded flat state. -/
def padState (p n : ℕ) (x y : ℕ → ℝ) : Fin (p + p) → ℝ :=
  Fin.append (padX p n x) (padX p n y)

theorem ofFlat_padState (n : ℕ) (x y : ℕ → ℝ) :
    ofFlat p (padState p n x y) = (padX p n x, padX p n y) :=
  Prod.ext (funext fun i => Fin.append_left _ _ i) (funext fun j => Fin.append_right _ _ j)

theorem padX_self (x : ℕ → ℝ) : padX p p x = fun j : Fin p => x j := by
  funext j; simp [padX]

theorem ofFlat_padState_self (x y : ℕ → ℝ) :
    ofFlat p (padState p p x y) = dualCoordOf p x y := by
  rw [ofFlat_padState, padX_self, padX_self]; rfl

theorem padX_trunc (n : ℕ) (x : ℕ → ℝ) : padX p n (truncCoord n x) = padX p n x := by
  funext j
  simp only [padX]
  split_ifs with h
  · exact truncCoord_of_lt x (by omega)
  · rfl

theorem padState_trunc (n : ℕ) (x y : ℕ → ℝ) :
    padState p n (truncCoord n x) (truncCoord n y) = padState p n x y := by
  simp [padState, padX_trunc]

/-- Unpadding at a known level `n`. -/
def unpadX (p n : ℕ) (w : Fin p → ℝ) : ℕ → ℝ :=
  fun i => if h : p - n + i < p ∧ i < n then w ⟨p - n + i, h.1⟩ else 0

/-- The truncated state read off the padded state at a known level `n`. -/
def unpadAt (p n : ℕ) (w : Fin (p + p) → ℝ) : DualState :=
  (n, unpadX p n ((ofFlat p w).1), unpadX p n ((ofFlat p w).2))

theorem unpadX_padX {n : ℕ} (hn : n ≤ p) (x : ℕ → ℝ) : unpadX p n (padX p n x) = truncCoord n x := by
  funext i
  simp only [unpadX, padX, truncCoord]
  by_cases hi : i < n
  · have h1 : p - n + i < p ∧ i < n := ⟨by omega, hi⟩
    have h2 : p - n ≤ p - n + i := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [Nat.add_sub_cancel_left]
    simp
  · have h1 : ¬(p - n + i < p ∧ i < n) := fun h => hi h.2
    rw [dite_eq_right_iff.2 fun h => absurd h h1]
    simp only [hi, ↓reduceIte]

theorem unpadAt_padState {n : ℕ} (hn : n ≤ p) (x y : ℕ → ℝ) :
    unpadAt p n (padState p n x y) = (n, truncCoord n x, truncCoord n y) := by
  simp [unpadAt, ofFlat_padState, unpadX_padX hn]

theorem measurable_unpadX (n : ℕ) : Measurable (unpadX p n) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [unpadX]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem measurable_unpadAt (n : ℕ) : Measurable (unpadAt p n) := by
  have h1 : Measurable fun w : Fin (p + p) → ℝ => (ofFlat p w).1 :=
    (continuous_fst.comp (ofFlat p).continuous).measurable
  have h2 : Measurable fun w : Fin (p + p) → ℝ => (ofFlat p w).2 :=
    (continuous_snd.comp (ofFlat p).continuous).measurable
  exact measurable_const.prodMk (((measurable_unpadX n).comp h1).prodMk
    ((measurable_unpadX n).comp h2))

/-- At a level below `p` the first flat coordinate is `0`, so the state is off the chamber. -/
theorem padState_notMem {n : ℕ} (hn : n < p) (x y : ℕ → ℝ) :
    padState p n x y ∉ flatChamber p := by
  intro h
  have h' : ofFlat p (padState p n x y) ∈ dualChamber p := h
  rw [ofFlat_padState] at h'
  have := h'.2.2.1 ⟨0, by omega⟩
  simp only [padX] at this
  have h0 : ¬ (p - n ≤ ((⟨0, by omega⟩ : Fin p) : ℕ)) := by simp; omega
  simp only [h0, ↓reduceIte] at this
  exact lt_irrefl _ this

theorem padState_mem_flatChamber_iff {n : ℕ} {x y : ℕ → ℝ} (hn : n ≤ p)
    (hc : dualCoordOf n x y ∈ dualChamber n) : padState p n x y ∈ flatChamber p ↔ n = p := by
  constructor
  · intro h
    by_contra hne
    exact padState_notMem (lt_of_le_of_ne hn hne) x y h
  · rintro rfl
    show ofFlat n (padState n n x y) ∈ dualChamber n
    rw [ofFlat_padState_self]; exact hc

/-!
## Continuity along deletion paths
-/

section Cont

variable {n : ℝ≥0 → ℕ} {z : ℝ≥0 → ℕ → ℝ}

theorem tendsto_padX_same {F : Filter ℝ≥0} {m : ℕ} {w : ℕ → ℝ} (hm : m ≤ p)
    (hev : ∀ᶠ u in F, n u = m) (hs : ∀ i, i < m → Tendsto (fun u => z u i) F (𝓝 (w i)))
    (j : Fin p) : Tendsto (fun u => padX p (n u) (z u) j) F (𝓝 (padX p m w j)) := by
  have e : (fun u => padX p (n u) (z u) j) =ᶠ[F] fun u => padX p m (z u) j := by
    filter_upwards [hev] with u hu; rw [hu]
  refine Tendsto.congr' e.symm ?_
  simp only [padX]
  split_ifs with h
  · exact hs _ (by omega)
  · exact tendsto_const_nhds

theorem tendsto_padX_jump {F : Filter ℝ≥0} {m : ℕ} {w : ℕ → ℝ} (hm : m + 1 ≤ p)
    (hev : ∀ᶠ u in F, n u = m + 1) (h0 : Tendsto (fun u => z u 0) F (𝓝 0))
    (hs : ∀ i, i < m → Tendsto (fun u => z u (i + 1)) F (𝓝 (w i))) (j : Fin p) :
    Tendsto (fun u => padX p (n u) (z u) j) F (𝓝 (padX p m w j)) := by
  have e : (fun u => padX p (n u) (z u) j) =ᶠ[F] fun u => padX p (m + 1) (z u) j := by
    filter_upwards [hev] with u hu; rw [hu]
  refine Tendsto.congr' e.symm ?_
  simp only [padX]
  by_cases h1 : p - (m + 1) ≤ (j : ℕ)
  · simp only [h1, ↓reduceIte]
    by_cases h2 : p - m ≤ (j : ℕ)
    · simp only [h2, ↓reduceIte]
      have e2 : (j : ℕ) - (p - (m + 1)) = (j - (p - m)) + 1 := by omega
      rw [e2]
      exact hs _ (by omega)
    · simp only [h2, ↓reduceIte]
      have e2 : (j : ℕ) - (p - (m + 1)) = 0 := by omega
      rw [e2]; exact h0
  · have h2 : ¬ p - m ≤ (j : ℕ) := by omega
    simp only [h1, h2, ↓reduceIte]
    exact tendsto_const_nhds

variable {x y : ℝ≥0 → ℕ → ℝ}

theorem tendsto_padState_right (hP : IsDeletionPath n x y) (hp : n 0 ≤ p) (t : ℝ≥0) :
    Tendsto (fun u => padState p (n u) (x u) (y u)) (𝓝[≥] t)
      (𝓝 (padState p (n t) (x t) (y t))) := by
  have hnt : n t ≤ p := (hP.antitone zero_le).trans hp
  obtain ⟨b, hb, hlev⟩ := exists_right_level hP t
  have hev : ∀ᶠ u in 𝓝[≥] t, n u = n t := by
    filter_upwards [Ico_mem_nhdsGE hb] with u hu using hlev u hu
  refine tendsto_pi_nhds.2 fun k => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · simp only [padState, Fin.append_left]
    exact tendsto_padX_same hnt hev (fun i hi => (tendsto_coord_right hP t hi).1) j
  · simp only [padState, Fin.append_right]
    exact tendsto_padX_same hnt hev (fun i hi => (tendsto_coord_right hP t hi).2) j

theorem tendsto_padState_left (hP : IsDeletionPath n x y) (hp : n 0 ≤ p) (t : ℝ≥0) :
    Tendsto (fun u => padState p (n u) (x u) (y u)) (𝓝[<] t)
      (𝓝 (padState p (n t) (x t) (y t))) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | ht
  · rw [← h, nhdsLT_zero_nnreal]; exact tendsto_bot
  obtain ⟨k, u₀, hu₀, hk⟩ := exists_left_level hP.antitone ht
  have hev : ∀ᶠ u in 𝓝[<] t, n u = k := by
    filter_upwards [Ico_mem_nhdsLT hu₀] with u hu using hk u hu
  have hkp : k ≤ p := (hk u₀ ⟨le_rfl, hu₀⟩) ▸ (hP.antitone zero_le).trans hp
  refine tendsto_pi_nhds.2 fun c => ?_
  by_cases hkt : k = n t
  · subst hkt
    have hs := fun i (hi : i < n t) => tendsto_coord_left_same hP hu₀ hk hi
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
    · simp only [padState, Fin.append_left]
      exact tendsto_padX_same hkp hev (fun i hi => (hs i hi).1) j
    · simp only [padState, Fin.append_right]
      exact tendsto_padX_same hkp hev (fun i hi => (hs i hi).2) j
  · obtain ⟨hk1, hx0, hy0, hs⟩ := left_jump hP hu₀ hk hkt
    rw [hk1] at hev hkp
    refine Fin.addCases (fun j => ?_) (fun j => ?_) c
    · simp only [padState, Fin.append_left]
      exact tendsto_padX_jump hkp hev hx0 (fun i hi => (hs i hi).1) j
    · simp only [padState, Fin.append_right]
      exact tendsto_padX_jump hkp hev hy0 (fun i hi => (hs i hi).2) j

/-- **The front-padded state is continuous** along a deletion path started at level `≤ p`. -/
theorem continuous_padState (hP : IsDeletionPath n x y) (hp : n 0 ≤ p) :
    Continuous fun t => padState p (n t) (x t) (y t) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  refine continuousAt_iff_continuous_left'_right'.2 ⟨tendsto_padState_left hP hp t, ?_⟩
  exact (tendsto_padState_right hP hp t).mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

end Cont

end BlockBand.Transmission.Dual
