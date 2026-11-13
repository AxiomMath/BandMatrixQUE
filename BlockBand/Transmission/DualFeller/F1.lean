module

public import BlockBand.Transmission.DualFeller.F1Aux

/-!
# Start continuity of the lifted `p = 1` dual

Proves `LiftStartContinuity D₀` for every `D₀ > 0`, with no further hypotheses.

Measure/domain: any `S : Type`, probability `μ`, driver space `LΩ S` with law `LP μ` and the
augmented filtration; any admissible starts `ξ, ξ'` and lifted families `F, F'` on it. The
constants `δ` depend only on `D₀, T, R, η`.

Choice of constants (`η < 1`; for `η ≥ 1` the bound is trivial): return level `a = η/3`, corner
level `ε = aη/48`, radius `n ≥ R + 1, 1/ε + 1, 2, e^K` with
`K = 8 g_{R+1} e^{D₀T/2}/(η ε)` (infinity: `measure_noHit_le`), pair Lyapunov constant `c`
on the `n`-ball (`exists_gen_pairDist_le`), pair tolerance `r` from the modulus of `π`
(`exists_proj_mod` with `ρ = min η (ε/2)`), and `δ = min(η/8, √(η e^{−cT} r/96))`.
Union bound over: the Ky Fan event (`≤ δ`), the null complements of `good₂`, the pair event
(`measure_pair_sup_le`, `≤ η/8`), the two escapes to infinity (`≤ η/8` each) and the four return
events (`measure_ret_le`, total `6ε/a = η/8`); off these, `pathwise` gives
`sup_{t≤T}‖Z̄_t − Z̄'_t‖ < η`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.Transmission.DualLift BlockBand.Transmission.Dual
open scoped NNReal ENNReal

/-- **Start continuity of the lift holds** (`LiftStartContinuity D₀`, `D₀ > 0`). -/
theorem liftStartContinuity_holds {D0 : ℝ} (hD0 : 0 < D0) : LiftStartContinuity D0 := by
  intro T R η hη
  by_cases hη1 : 1 ≤ η
  · refine ⟨1, one_pos, fun S _ μ _ ξ ξ' _ _ F F' _ => ?_⟩
    exact prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hη1)
  rw [not_le] at hη1
  set a : ℝ := η / 3 with hadef
  set ε : ℝ := a * η / 48 with hεdef
  have ha : 0 < a := by positivity
  have hε : 0 < ε := by positivity
  have hεa : ε < a := by rw [hεdef]; nlinarith
  have h2εa : 2 * ε < a := by rw [hεdef]; nlinarith
  set Bℓ : ℝ := (2 * (R + 1) ^ 2 + 1) * (1 + 2 * (R + 1) ^ 2) with hBℓ
  have hBℓ0 : 0 < Bℓ := by positivity
  set E' : ℝ := exp (-(D0 / 2) * T) with hE'
  have hE'0 : 0 < E' := exp_pos _
  set K : ℝ := 8 * Bℓ / (η * (E' * ε)) with hKdef
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max (R + 1) (1 / ε + 1)) (max 2 (exp K)))
  have hnR : R + 1 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnε : 1 / ε < n := by
    have := (le_max_right _ _).trans ((le_max_left _ _).trans hn); linarith
  have hn2 : (2 : ℝ) ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : (1 : ℝ) < n := by linarith
  have hnK : exp K ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hlogK : K ≤ Real.log (1 + n * n) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    nlinarith
  have hlog0 : 0 < Real.log (1 + n * n) := Real.log_pos (by nlinarith)
  obtain ⟨c, hc0, hc⟩ := exists_gen_pairDist_le hD0 (n : ℝ)
  obtain ⟨r, hr0, hmod⟩ := exists_proj_mod (n : ℝ) (lt_min hη (half_pos hε))
  set E : ℝ := exp (-c * T) with hE
  have hE0 : 0 < E := exp_pos _
  set δ : ℝ := min (η / 8) (√(η * E * r / 96)) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (Real.sqrt_pos.2 (by positivity))
  have hδ8 : δ ≤ η / 8 := min_le_left _ _
  have hδ2 : δ ^ 2 ≤ η * E * r / 96 :=
    (pow_le_pow_left₀ hδ.le (min_le_right _ _) 2).trans (Real.sq_sqrt (by positivity)).le
  refine ⟨δ, hδ, fun S _ μ _ ξ ξ' hξ hξ' F F' hD => ?_⟩
  set A : Set (LΩ S) := {ω | ‖ξ ω‖ ≤ R ∧ ‖ξ ω - ξ' ω‖ < δ} with hAdef
  have hA : MeasurableSet[L𝓖 μ 0] A :=
    (measurableSet_le hξ.meas.norm.measurable measurable_const).inter
      (measurableSet_lt (hξ.meas.sub hξ'.meas).norm.measurable measurable_const)
  have hA1 : ∀ ω ∈ A, ‖ξ' ω‖ < R + 1 := fun ω hω => by
    have h := norm_sub_le (ξ ω) (ξ ω - ξ' ω)
    rw [sub_sub_cancel] at h
    linarith [hω.1, hω.2]
  have hAn : ∀ ω ∈ A, ‖ξ ω‖ ≤ n ∧ ‖ξ' ω‖ ≤ n := fun ω hω =>
    ⟨by linarith [hω.1], by linarith [hA1 ω hω]⟩
  have hAB : ∀ ω ∈ A, pairDist (ξ ω, ξ' ω) ≤ 6 * δ ^ 2 := fun ω hω =>
    (pairDist_le_sq_norm _).trans (by
      have := pow_le_pow_left₀ (norm_nonneg _) hω.2.le 2; linarith)
  have hAst : A ⊆ LiftFamily.startBd (ξ := ξ) Bℓ := fun ω hω =>
    liftLyap_le_of_norm (hξ.mem ω) (by linarith [hω.1])
  have hAst' : A ⊆ LiftFamily.startBd (ξ := ξ') Bℓ := fun ω hω =>
    liftLyap_le_of_norm (hξ'.mem ω) (hA1 ω hω).le
  -- the bad events
  set X1 : Set (LΩ S) := {ω | δ ≤ ‖ξ ω - ξ' ω‖}
  set X4 : Set (LΩ S) := A ∩ {ω | ∃ t : ℝ≥0, t ≤ T ∧
    (t : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) ∧ r ≤ pairDist (F.X n t ω, F'.X n t ω)}
  set X5 : Set (LΩ S) := A ∩ F.good ∩ {ω | F.e n ω < F.hitS n ε ω ∧ F.e n ω < T}
  set X6 : Set (LΩ S) := A ∩ F'.good ∩ {ω | F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T}
  set X7 : Set (LΩ S) := A ∩ {ω | ω ∈ F.good ∧ ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T) ∧
    ω ∈ Ret F n ε a T}
  set X8 : Set (LΩ S) := A ∩ {ω | ω ∈ F.good ∧ ¬(F.e n ω < F.hitS n (2 * ε) ω ∧
    F.e n ω < T) ∧ ω ∈ Ret F n (2 * ε) a T}
  set X9 : Set (LΩ S) := A ∩ {ω | ω ∈ F'.good ∧ ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T) ∧
    ω ∈ Ret F' n ε a T}
  set X10 : Set (LΩ S) := A ∩ {ω | ω ∈ F'.good ∧ ¬(F'.e n ω < F'.hitS n (2 * ε) ω ∧
    F'.e n ω < T) ∧ ω ∈ Ret F' n (2 * ε) a T}
  have hsub : {ω | ‖ξ ω‖ ≤ R ∧ ∃ t : ℝ≥0, t ≤ T ∧ η ≤ ‖liftZbar F t ω - liftZbar F' t ω‖} ⊆
      X1 ∪ F.good₂ᶜ ∪ F'.good₂ᶜ ∪ X4 ∪ X5 ∪ X6 ∪ X7 ∪ X8 ∪ X9 ∪ X10 := by
    rintro ω ⟨hωR, t, htT, hηt⟩
    by_contra hc
    simp only [mem_union, not_or] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := hc
    have hωA : ω ∈ A := ⟨hωR, not_le.1 h1⟩
    have hω : ω ∈ F.good₂ := not_not.1 h2
    have hω' : ω ∈ F'.good₂ := not_not.1 h3
    have hg := (F.good₂_spec hω).1
    have hg' := (F'.good₂_spec hω').1
    have hP : ∀ s : ℝ≥0, s ≤ T → (s : WithTop ℝ≥0) ≤ min (F.e n ω) (F'.e n ω) →
        pairDist (F.X n s ω, F'.X n s ω) < r := fun s hs hse =>
      not_le.1 fun hle => h4 ⟨hωA, s, hs, hse, hle⟩
    have hI : ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T) := fun h => h5 ⟨⟨hωA, hg⟩, h⟩
    have hI' : ¬(F'.e n ω < F'.hitS n ε ω ∧ F'.e n ω < T) := fun h => h6 ⟨⟨hωA, hg'⟩, h⟩
    have hI₂ : ¬(F.e n ω < F.hitS n (2 * ε) ω ∧ F.e n ω < T) := fun h => by
      refine hI ⟨h.1.trans_le ?_, h.2⟩
      unfold LiftFamily.hitS hitLe
      exact le_iInf₂ fun s hs => iInf₂_le s (hs.trans (by linarith))
    have hI₂' : ¬(F'.e n ω < F'.hitS n (2 * ε) ω ∧ F'.e n ω < T) := fun h => by
      refine hI' ⟨h.1.trans_le ?_, h.2⟩
      unfold LiftFamily.hitS hitLe
      exact le_iInf₂ fun s hs => iInf₂_le s (hs.trans (by linarith))
    exact absurd (pathwise F F' hξ hξ' hω hω' ha (by rw [hadef]; linarith) (hAn ω hωA).1
      (hAn ω hωA).2 hmod hP hI hI' (fun h => h7 ⟨hωA, hg, hI, h⟩)
      (fun h => h8 ⟨hωA, hg, hI₂, h⟩) (fun h => h9 ⟨hωA, hg', hI', h⟩)
      (fun h => h10 ⟨hωA, hg', hI₂', h⟩) t htT) (not_lt.2 hηt)
  -- the bounds
  have b4 := measure_pair_sup_le F F' n hc0 hc hA hAn (B := 6 * δ ^ 2) (by positivity) hAB T hr0
  have b5 := le_ofReal_div_of_mul_le (by positivity)
    (F.measure_noHit_le hD0 hξ n hε hn1 hnε T hA fun ω hω => hAst hω)
  have b6 := le_ofReal_div_of_mul_le (by positivity)
    (F'.measure_noHit_le hD0 hξ' n hε hn1 hnε T hA fun ω hω => hAst' hω)
  have b7 := measure_ret_le F hD0 hξ (n := n) hε hεa T hAst
  have b8 := measure_ret_le F hD0 hξ (n := n) (by positivity) h2εa T hAst
  have b9 := measure_ret_le F' hD0 hξ' (n := n) hε hεa T hAst'
  have b10 := measure_ret_le F' hD0 hξ' (n := n) (by positivity) h2εa T hAst'
  have b2 : LP μ F.good₂ᶜ ≤ ENNReal.ofReal 0 := by rw [F.measure_good₂_compl hD0 hξ]; exact zero_le
  have b3 : LP μ F'.good₂ᶜ ≤ ENNReal.ofReal 0 := by
    rw [F'.measure_good₂_compl hD0 hξ']; exact zero_le
  -- the real arithmetic
  have hP4 : 2 / (E * ((6 * δ ^ 2)⁻¹ * r)) ≤ η / 8 := by
    have e : 2 / (E * ((6 * δ ^ 2)⁻¹ * r)) = 12 * δ ^ 2 / (E * r) := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  have hI5 : Bℓ / (E' * (ε * Real.log (1 + n * n))) ≤ η / 8 := by
    rw [div_le_iff₀ (by positivity)]
    have e : η / 8 * (E' * ε) * K = Bℓ := by rw [hKdef]; field_simp
    have := mul_le_mul_of_nonneg_left hlogK (by positivity : 0 ≤ η / 8 * (E' * ε))
    nlinarith
  have hq : ε / a = η / 48 := by rw [hεdef]; field_simp
  have hq2 : 2 * ε / a = η / 24 := by rw [mul_div_assoc, hq]; ring
  have u {X Y : Set (LΩ S)} {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
      (hX : LP μ X ≤ ENNReal.ofReal x) (hY : LP μ Y ≤ ENNReal.ofReal y) :
      LP μ (X ∪ Y) ≤ ENNReal.ofReal (x + y) :=
    (measure_union_le _ _).trans (add_ofReal_le hx hy hX hY)
  have hle := u (by positivity) (by positivity) (u (by positivity) (by positivity)
    (u (by positivity) (by positivity) (u (by positivity) (by positivity) (u (by positivity)
    (by positivity) (u (by positivity) (by positivity) (u (by positivity) (by positivity)
    (u (by positivity) le_rfl (u hδ.le le_rfl hD b2) b3) b4) b5) b6) b7) b8) b9) b10
  refine (measure_mono hsub).trans (hle.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [hq, hq2]
  linarith

end BlockBand.Transmission.DualFeller
