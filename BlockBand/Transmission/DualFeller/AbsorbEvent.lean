module

public import BlockBand.Transmission.DualFeller.Absorb

/-!
# The absorption-time bound for one lifted family

Setting of `absK` (one family `F`, start `ξ`). `AbsBad F n ε η T` is the set of good paths that
* do not exit the `n`-ball before both `hitS_n(ε)` and `T` (no escape);
* make no return of any `S^k` (`k ≥ n`) to level `1/2` in `[hitS_n(ε), T]` (`Ret`);
* still have `ζ ∧ T − hitS_n(ε) ∧ T ≥ η`.

**`measure_absBad_le`**: if `u ≤ c` on `{S ≤ ε}` (strip), `P(AbsBad) ≤ 18c/(D₀η)`.
Proof: `AbsBad ⊆ ⋃_k E_k`, with `E_k` the same event for the radius-`(n+k)` exit `e_{n+k}` in
place of `ζ = sup_k e_k` and `η/2` in place of `η`; the `E_k` increase (consistency of the
radii on `good`). On `E_k`, `S^{n+k} < 1/2` on `[hitS, e_{n+k} ∧ T]`, so `−L₁u ≥ D₀/9` there and
`K_{n+k} ≥ (D₀/9)(η/2)` (`le_absK`); Markov (`measure_absK_ge`) bounds `P(E_k)` uniformly in `k`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.DualFeller

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.Stochastic.NativeSDE
open BlockBand.Transmission.DualLift BlockBand.Transmission.Dual
  BlockBand.Transmission.Dual.Exists
open scoped NNReal ENNReal

theorem toNNReal_lt_of_lt_untopA {T : ℝ≥0} {x : WithTop ℝ≥0} {t : ℝ} (ht0 : 0 ≤ t)
    (h : t < (((min (T : WithTop ℝ≥0) x).untopA : ℝ≥0) : ℝ)) : (t.toNNReal : WithTop ℝ≥0) < x := by
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (min_coe_ne_top T x)
  rw [← hv, untopA_ofNN] at h
  have : t.toNNReal < v := (Real.toNNReal_lt_iff_lt_coe ht0).2 h
  exact (WithTop.coe_lt_coe.2 this).trans_le (hv ▸ min_le_right _ _)

theorem le_untopA_of_le {T : ℝ≥0} {x : WithTop ℝ≥0} {t : ℝ≥0} (htT : t ≤ T)
    (h : (t : WithTop ℝ≥0) ≤ x) : (t : ℝ) ≤ (((min (T : WithTop ℝ≥0) x).untopA : ℝ≥0) : ℝ) :=
  NNReal.coe_le_coe.2 ((WithTop.le_untopA_iff (min_coe_ne_top T x)).2
    (le_min (WithTop.coe_le_coe.2 htT) h))

theorem toNNReal_le_of_le_untopA {T : ℝ≥0} {x : WithTop ℝ≥0} {t : ℝ}
    (h : t ≤ (((min (T : WithTop ℝ≥0) x).untopA : ℝ≥0) : ℝ)) :
    (t.toNNReal : WithTop ℝ≥0) ≤ min (T : WithTop ℝ≥0) x := by
  obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (min_coe_ne_top T x)
  rw [← hv, untopA_ofNN] at h
  rw [← hv]
  exact WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 h)

variable {D0 : ℝ} {S : Type} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]
  {ξ : LΩ S → Fin 6 → ℝ} (F : LiftFamily μ D0 ξ)

/-- Good paths without escape and without return to `1/2` after `hitS_n(ε)`, whose lifetime
(capped at `T`) exceeds `hitS_n(ε) ∧ T` by at least `η`. -/
def AbsBad (n : ℕ) (ε η : ℝ) (T : ℝ≥0) : Set (LΩ S) :=
  {ω | ω ∈ F.good ∧ ¬(F.e n ω < F.hitS n ε ω ∧ F.e n ω < T) ∧ ω ∉ Ret F n ε (1 / 2) T ∧
    η ≤ (((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) - absStart F n ε T ω}

/-- The approximating events at the radius `n + k`. -/
def AbsBadK (n : ℕ) (ε η : ℝ) (T : ℝ≥0) (k : ℕ) : Set (LΩ S) :=
  {ω | ω ∈ F.good ∧ F.hitS n ε ω ≤ F.e n ω ∧ ω ∉ Ret F n ε (1 / 2) T ∧
    η / 2 ≤ (((min (T : WithTop ℝ≥0) (F.e (n + k) ω)).untopA : ℝ≥0) : ℝ) - absStart F n ε T ω}

theorem monotone_absBadK (n : ℕ) (ε η : ℝ) (T : ℝ≥0) : Monotone (AbsBadK F n ε η T) := by
  intro k k' hkk' ω ⟨hg, h1, h2, h3⟩
  exact ⟨hg, h1, h2, h3.trans (sub_le_sub_right (untopA_min_mono T
    ((F.good_spec hg).2 _ _ (by omega)).1) _)⟩

theorem absBad_subset (n : ℕ) {ε η : ℝ} (hη : 0 < η) (T : ℝ≥0) :
    AbsBad F n ε η T ⊆ ⋃ k, AbsBadK F n ε η T k := by
  rintro ω ⟨hg, hI, hR, hη'⟩
  have hzT := untopA_min_le T (F.zeta ω)
  have hhe : F.hitS n ε ω ≤ F.e n ω := by
    by_contra hc
    rw [not_le] at hc
    have hTe : (T : WithTop ℝ≥0) ≤ F.e n ω := not_lt.1 fun h => hI ⟨hc, h⟩
    have : absStart F n ε T ω = T := by
      unfold absStart; rw [min_eq_left (hTe.trans hc.le)]; rfl
    linarith
  set a := absStart F n ε T ω with ha
  have ha0 : 0 ≤ a := absStart_nonneg F n ε T ω
  have ht0 : 0 ≤ a + η / 2 := by positivity
  have hlt : a + η / 2 < (((min (T : WithTop ℝ≥0) (F.zeta ω)).untopA : ℝ≥0) : ℝ) := by linarith
  obtain ⟨j, hj⟩ := lt_iSup_iff.1 (toNNReal_lt_of_lt_untopA ht0 hlt)
  refine mem_iUnion.2 ⟨j, hg, hhe, hR, ?_⟩
  have hej : F.e j ω ≤ F.e (n + j) ω := ((F.good_spec hg).2 j (n + j) (by omega)).1
  have htT : (a + η / 2).toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 (by linarith)
  have := le_untopA_of_le htT (hj.le.trans hej)
  rw [Real.coe_toNNReal _ ht0] at this
  linarith

/-- On `AbsBadK`, the weighted time `K_{n+k}` is at least `(D₀/9)(η/2)` (a.s.). -/
theorem le_absK_of_absBadK (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {ε η : ℝ}
    (hη : 0 < η) (T : ℝ≥0) (k : ℕ) {ω : LΩ S} (hω : ω ∈ AbsBadK F n ε η T k)
    (hi : IntegrableOn (fun s : ℝ => absDrift F (n + k) s.toNNReal ω) (Ioc 0 T)) :
    D0 / 9 * (η / 2) ≤ absK F (n + k) ε T ω := by
  obtain ⟨hg, hhe, hR, h3⟩ := hω
  have hτ : F.hitS (n + k) ε ω = F.hitS n ε ω := F.hitS_eq_of_good hg (by omega) hhe
  have hst : absStart F (n + k) ε T ω = absStart F n ε T ω := by unfold absStart; rw [hτ]
  set a := absStart F n ε T ω with ha
  set b := (((min (T : WithTop ℝ≥0) (F.e (n + k) ω)).untopA : ℝ≥0) : ℝ) with hb
  have hbT : b ≤ T := untopA_min_le T _
  have ha0 : 0 ≤ a := absStart_nonneg F n ε T ω
  -- the clock starts at the hitting time itself
  have hhT : F.hitS n ε ω < T := by
    by_contra hc
    rw [not_lt] at hc
    have : a = T := by rw [ha]; unfold absStart; rw [min_eq_left hc]; rfl
    linarith
  obtain ⟨h₀, hh₀⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hhT)
  have ha₀ : a = h₀ := by
    rw [ha]; unfold absStart; rw [min_eq_right hhT.le, ← hh₀]; rfl
  have hc : ∀ s ∈ Icc (absStart F (n + k) ε T ω) b, D0 / 9 ≤ -absDrift F (n + k) s.toNNReal ω := by
    intro s hs
    rw [hst] at hs
    have hs0 : 0 ≤ s := ha0.trans hs.1
    have hse : (s.toNNReal : WithTop ℝ≥0) ≤ min (T : WithTop ℝ≥0) (F.e (n + k) ω) :=
      toNNReal_le_of_le_untopA hs.2
    have hsT : s.toNNReal ≤ T := WithTop.coe_le_coe.1 (hse.trans (min_le_left _ _))
    have hse' : (s.toNNReal : WithTop ℝ≥0) ≤ F.e (n + k) ω := hse.trans (min_le_right _ _)
    have hhs : F.hitS n ε ω ≤ s.toNNReal := by
      rw [← hh₀]
      refine WithTop.coe_le_coe.2 (Real.le_toNNReal_iff_coe_le hs0 |>.2 ?_)
      rw [← ha₀]; exact hs.1
    have hS := Sp_lt_of_not_ret F hg hR hsT hhs (n + k) hse'
    unfold absDrift switchOff
    simp only [hse', ↓reduceIte]
    exact le_neg_L₁_absLyap hD0.le (F.Yf_mem_strip hξ _ _ ω) hS
  have hab : absStart F (n + k) ε T ω ≤ b := by rw [hst]; linarith
  have := le_absK F (n + k) ε T hD0.le hξ hi hab hbT hc
  rw [hst] at this
  have hη2 : D0 / 9 * (η / 2) ≤ D0 / 9 * (b - a) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **Absorption-time bound for one family.** -/
theorem measure_absBad_le (hD0 : 0 < D0) (hξ : IsLiftStart μ ξ) (n : ℕ) {ε c η : ℝ}
    (hη : 0 < η) (hc0 : 0 ≤ c) (hc : ∀ y ∈ flatStrip, tot y ≤ ε → absLyap y ≤ c) (T : ℝ≥0) :
    LP μ (AbsBad F n ε η T) ≤ ENNReal.ofReal (18 * c / (D0 * η)) := by
  refine (measure_mono (absBad_subset F n hη T)).trans ?_
  rw [(monotone_absBadK F n ε η T).measure_iUnion]
  refine iSup_le fun k => ?_
  have hb : 0 < D0 / 9 * (η / 2) := by positivity
  have hae : AbsBadK F n ε η T k ≤ᵐ[LP μ] {ω | D0 / 9 * (η / 2) ≤ absK F (n + k) ε T ω} := by
    filter_upwards [ae_integrableOn_absDrift F hD0 hξ (n + k)] with ω hi hω
    exact le_absK_of_absBadK F hD0 hξ n hη T k hω (hi T)
  refine (measure_mono_ae hae).trans ((measure_absK_ge F hD0 hξ (n + k) ε T hc0 hc hb).trans
    (le_of_eq ?_))
  congr 1
  field_simp
  ring

end BlockBand.Transmission.DualFeller
