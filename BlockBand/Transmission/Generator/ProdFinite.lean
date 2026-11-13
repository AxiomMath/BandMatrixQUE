module

public import BlockBand.Transmission.Generator.ProdFixed
public import BlockBand.Transmission.Generator.ModAlong
public import BlockBand.Transmission.Generator.BrSum

/-!
# The finite-`W` tested product vanishes along every subsequence

**`prod_finite_tendsto hMT hGA hLp hP`**: along a moving energy, for past tests `Φ_n`
(`𝓕_{⌊W_ns⌋}`-measurable, `|Φ_n| ≤ B`) and `0 < s ≤ t`,
`E_n[Φ_n(M^W_kM^W_l - Σ_{⌊Ws⌋ ≤ r < ⌊Wt⌋} B_{kl}(P_r)/W)] → 0`.
Inputs: `prod_fixedW`; `powerDriftSummable_holds`, `powerBracketSummable_holds` on the window
`[s, t+1]`; `fourth_increment_bound` (`E Δ⁴ ≤ K/W²`, so `‖N‖₂` stays bounded); the length-uniform
conductance at `p = 4` (`‖A_k(P_r)/W‖₂ = O(1/W)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Transmission.Generator

open MeasureTheory Filter Finset Topology
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.TransmissionPath
open BlockBand.Internal.Contracts.TransmissionStatements BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

theorem tendsto_sum_toReal {ι : Type*} {S : ℕ → Finset ι} {f : ℕ → ι → ℝ≥0∞}
    (h : Tendsto (fun n => ∑ i ∈ S n, f n i) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i ∈ S n, (f n i).toReal) atTop (𝓝 0) := by
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at h'
  refine h'.congr' ?_
  filter_upwards [h.eventually (gt_mem_nhds zero_lt_one)] with n hn
  simp only [Function.comp_apply]
  exact ENNReal.toReal_sum fun i hi => ENNReal.sum_ne_top.mp (hn.trans ENNReal.one_lt_top).ne i hi

theorem sum_range_le_window {f : ℕ → ℝ} (hf : ∀ r, 0 ≤ f r) {W : ℕ} {s t t' : ℝ}
    (htt : t ≤ t') :
    ∑ u ∈ range (⌊(W : ℝ) * t⌋₊ - ⌊(W : ℝ) * s⌋₊), f (⌊(W : ℝ) * s⌋₊ + u) ≤
      ∑ r ∈ lengthWindow s t' W, f r := by
  have hW : (0 : ℝ) ≤ W := Nat.cast_nonneg _
  rw [← sum_Ico_eq_sum_range]
  exact sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl
    (Nat.floor_mono (mul_le_mul_of_nonneg_left htt hW))) fun r _ _ => hf r

theorem prod_real_le {β β' σk σk' σl σl' ν ν' ak al n c : ℝ} (hβ : β ≤ β') (hk0 : 0 ≤ σk)
    (hk : σk ≤ σk') (hl0 : 0 ≤ σl) (hl : σl ≤ σl') (hν0 : 0 ≤ ν) (hν : ν ≤ ν') (hak : 0 ≤ ak)
    (hal : 0 ≤ al) (hn : n * (ak * al) ≤ c) :
    β + (σk * σl + al * σk + ak * σl + n * (ak * al)) + ν * σl + σk * ν + σk * σl ≤
      β' + (σk' * σl' + al * σk' + ak * σl' + c) + ν' * σl' + σk' * ν' + σk' * σl' := by
  have h1 : σk * σl ≤ σk' * σl' := mul_le_mul hk hl hl0 (hk0.trans hk)
  have h2 : ν * σl ≤ ν' * σl' := mul_le_mul hν hl hl0 (hν0.trans hν)
  have h3 : σk * ν ≤ σk' * ν' := mul_le_mul hk hν hν0 (hk0.trans hk)
  have h4 : al * σk ≤ al * σk' := mul_le_mul_of_nonneg_left hk hal
  have h5 : ak * σl ≤ ak * σl' := mul_le_mul_of_nonneg_left hl hak
  linarith

/-- `√((x/W)²C) = x√C/W` for `x ≥ 0`. -/
theorem sqrt_sq_div_mul {x : ℝ} (C : ℝ) (hx : 0 ≤ x) (W : ℕ) :
    Real.sqrt ((x / W) ^ 2 * C) = x / W * Real.sqrt C := by
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hx (Nat.cast_nonneg _))]

/-- **The finite-`W` tested product vanishes.** -/
theorem prod_finite_tendsto (hMT : MatchedTracesContract) (hGA : GaussianAbsorptionContract)
    (hLp : GaussianLpGradient) (hP : GaussianPoincare) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) {Ce : ℝ} {e : ℕ → ℝ} (he : IsMovingEnergy E Ce e)
    {k l : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) {σ : ℕ → ℕ}
    (hσ : Tendsto σ atTop atTop) {B : ℝ} (hB0 : 0 ≤ B) (Φ : ∀ n, GrowthPath (σ n) → ℝ)
    (hΦ : ∀ n, Measurable[growthSigma (σ n) ⌊((σ n : ℕ) : ℝ) * s⌋₊] (Φ n))
    (hB : ∀ n ω, |Φ n ω| ≤ B) :
    Tendsto (fun n => ∫ ω, Φ n ω *
      (prodM b E (e (σ n)) (σ n) k ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω *
        prodM b E (e (σ n)) (σ n) l ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω -
        bracketSum b E (e (σ n)) (σ n) k l ⌊((σ n : ℕ) : ℝ) * s⌋₊ ⌊((σ n : ℕ) : ℝ) * t⌋₊ ω)
      ∂growthPathLaw (σ n) b) atTop (𝓝 0) := by
  obtain ⟨hκ, -⟩ := mem_bulk_min hE1 hE2
  set κ := min (2 + E) (2 - E) / 2
  have hκ2 : 0 < κ := by positivity
  set D := transportD0 b E
  have hD : 0 ≤ D := transportD0_nonneg hb0 hE1 hE2
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  obtain ⟨Kk, Wk, hKk, h4k⟩ := fourth_increment_bound hMT hGA hLp (κ := κ) (ε := s / 2)
    (T := t + 1) hb0 hb hκ2 (by positivity) (by linarith) k'
  obtain ⟨Kl, Wl, hKl, h4l⟩ := fourth_increment_bound hMT hGA hLp (κ := κ) (ε := s / 2)
    (T := t + 1) hb0 hb hκ2 (by positivity) (by linarith) l'
  set K4 := max Kk Kl
  obtain ⟨Cg, hgT⟩ := (LengthUniform.transmissionLengthUniform_holds hMT hGA hLp).conductance b
    hb0 hb κ (s / 2) ((4 : ℕ) : ℝ) hκ2 (by positivity) (by norm_num)
  obtain ⟨Wg, hg⟩ := hgT (t + 1)
  set Cg' := max Cg 0
  have hCg : 0 ≤ Cg' := le_max_right _ _
  have hDk := tendsto_sum_toReal ((powerDriftSummable_holds hMT hGA hLp hP b hb0 hb E hE1 hE2 Ce e
    he (k' + 1) (by omega) s (t + 1) hs (by linarith)).comp hσ)
  have hDl := tendsto_sum_toReal ((powerDriftSummable_holds hMT hGA hLp hP b hb0 hb E hE1 hE2 Ce e
    he (l' + 1) (by omega) s (t + 1) hs (by linarith)).comp hσ)
  have hBr := tendsto_sum_toReal ((powerBracketSummable_holds hMT hGA hLp hP b hb0 hb E hE1 hE2 Ce
    e he (k' + 1) (l' + 1) (by omega) (by omega) s (t + 1) hs (by linarith)).comp hσ)
  set ck : ℝ := D * ((k' + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt Cg'
  set cl : ℝ := D * ((l' + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt Cg'
  set c₁ : ℝ := (t - s + 1) * (ck * cl)
  set ν' : ℝ := Real.sqrt (1 + 320 * (t - s + 1) ^ 2 * K4)
  have hW0 : ∀ c : ℝ, Tendsto (fun n => c / ((σ n : ℕ) : ℝ)) atTop (𝓝 0) := fun c =>
    (tendsto_const_div_atTop_nhds_zero_nat c).comp hσ
  set βn : ℕ → ℝ := fun n => ∑ r ∈ lengthWindow s (t + 1) (σ n),
    (eLpNorm (bracketError b E (e (σ n)) (σ n) (k' + 1) (l' + 1) r) 1 (growthPathLaw (σ n) b)).toReal
  set σkn : ℕ → ℝ := fun n => ∑ r ∈ lengthWindow s (t + 1) (σ n),
    (eLpNorm (driftError b E (e (σ n)) (σ n) (k' + 1) r) 2 (growthPathLaw (σ n) b)).toReal
  set σln : ℕ → ℝ := fun n => ∑ r ∈ lengthWindow s (t + 1) (σ n),
    (eLpNorm (driftError b E (e (σ n)) (σ n) (l' + 1) r) 2 (growthPathLaw (σ n) b)).toReal
  have hR : Tendsto (fun n => B * (βn n + (σkn n * σln n + cl / ((σ n : ℕ) : ℝ) * σkn n +
      ck / ((σ n : ℕ) : ℝ) * σln n + c₁ / ((σ n : ℕ) : ℝ)) + ν' * σln n + σkn n * ν' +
      σkn n * σln n)) atTop (𝓝 0) := by
    have hν : Tendsto (fun _ : ℕ => ν') atTop (𝓝 ν') := tendsto_const_nhds
    have := ((hBr.add (((hDk.mul hDl).add ((hW0 cl).mul hDk)).add ((hW0 ck).mul hDl) |>.add
      (hW0 c₁))).add (hν.mul hDl) |>.add (hDk.mul hν) |>.add
      (hDk.mul hDl)).const_mul B
    simpa using this
  refine squeeze_zero_norm' ?_ hR
  filter_upwards [hσ.eventually_ge_atTop (max (max Wk Wl) (max Wg
    (max (EnergyUniform.windowWidth (min (2 + E) (2 - E)) Ce) ⌈2 / s⌉₊)))] with n hn
  simp only [max_le_iff] at hn
  obtain ⟨⟨hnk, hnl⟩, hng, hnw, hns⟩ := hn
  set W := σ n
  have hmem : e W ∈ bulkInterval κ := along_mem_bulk hE1 hE2 he hnw
  obtain ⟨he1, he2⟩ := bulk_bounds' hκ2 hmem
  have hWs : 2 / s ≤ (W : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hns)
  have hWpos : (0 : ℝ) < W := lt_of_lt_of_le (by positivity) hWs
  have hW0' : (0 : ℝ) ≤ W := hWpos.le
  have hsW : 2 ≤ s * W := by rw [div_le_iff₀ hs] at hWs; linarith
  set rs := ⌊(W : ℝ) * s⌋₊
  set rt := ⌊(W : ℝ) * t⌋₊
  have hrst : rs ≤ rt := Nat.floor_mono (mul_le_mul_of_nonneg_left hst hW0')
  have hrs1 : (W : ℝ) * s - 1 < rs := by
    have := Nat.lt_floor_add_one ((W : ℝ) * s); linarith
  have hrt : (rt : ℝ) ≤ W * t := Nat.floor_le (mul_nonneg hW0' (hs.le.trans hst))
  set m := rt - rs
  have hm : rs + m = rt := Nat.add_sub_cancel' hrst
  have hmR : (m : ℝ) = rt - rs := by rw [Nat.cast_sub hrst]
  have hrange : ∀ u < m, 1 ≤ rs + u ∧ s / 2 * W ≤ ((rs + u : ℕ) : ℝ) ∧
      ((rs + u : ℕ) : ℝ) ≤ (t + 1) * W := by
    intro u hu
    have hu' : ((rs + u : ℕ) : ℝ) < rt := by exact_mod_cast (show rs + u < rt by omega)
    have h0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
    push_cast at hu' ⊢
    refine ⟨?_, by nlinarith, by nlinarith⟩
    have : (1 : ℝ) < rs + 1 := by linarith
    exact_mod_cast (show (1 : ℝ) ≤ (rs : ℝ) + u by nlinarith)
  have H4k : ∀ u < m, ∫ ω, modInc (fun r => pathPower b (e W) W (k' + 1) r) (rs + u) ω ^ 4
      ∂growthPathLaw W b ≤ K4 / (W : ℝ) ^ 2 := fun u hu => by
    obtain ⟨r1, r2, r3⟩ := hrange u hu
    refine (h4k W hnk (e W) hmem _ r1 (by linarith) (by linarith)).trans ?_
    gcongr; exact le_max_left _ _
  have H4l : ∀ u < m, ∫ ω, modInc (fun r => pathPower b (e W) W (l' + 1) r) (rs + u) ω ^ 4
      ∂growthPathLaw W b ≤ K4 / (W : ℝ) ^ 2 := fun u hu => by
    obtain ⟨r1, r2, r3⟩ := hrange u hu
    refine (h4l W hnl (e W) hmem _ r1 (by linarith) (by linarith)).trans ?_
    gcongr; exact le_max_right _ _
  have Hg : ∀ u < m, ∫ ω, pathConductance b (e W) W (rs + u) ω ^ 4 ∂growthPathLaw W b ≤ Cg' :=
    fun u hu => by
    obtain ⟨-, r2, r3⟩ := hrange u hu
    refine integral_pow_le_of_lintegral (SourceMixing.measurable_pathConductance b (e W) _) ?_ 4
      hCg ((hg W hng (e W) hmem _ r2 r3).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    filter_upwards [pathPower_mem (W := W) (b := b) (by linarith) he1 he2] with ω hm
    obtain ⟨a0, a1, -⟩ := hm 1 (rs + u) le_rfl
    exact a0.trans a1
  have hfix := prod_fixedW (by linarith : b < 1) he1 he2 hD (by omega) (by omega) rs m (hΦ n) hB0
    (hB n) H4k H4l Hg
  simp only [hm] at hfix
  rw [Real.norm_eq_abs]
  refine hfix.trans (mul_le_mul_of_nonneg_left ?_ hB0)
  rw [sqrt_sq_div_mul Cg' (by positivity), sqrt_sq_div_mul Cg' (by positivity)]
  have e1 : D * ((k' + 1 : ℕ) : ℝ) ^ 2 / W * Real.sqrt Cg' = ck / W := by ring
  have e2 : D * ((l' + 1 : ℕ) : ℝ) ^ 2 / W * Real.sqrt Cg' = cl / W := by ring
  rw [e1, e2]
  have hck : 0 ≤ ck := by positivity
  have hcl : 0 ≤ cl := by positivity
  have hW1 : (1 : ℝ) ≤ W := Nat.one_le_cast.mpr (by exact_mod_cast hWpos)
  have hm1 : (m : ℝ) ≤ (t - s + 1) * W := by rw [hmR]; nlinarith [hrt, hrs1, hW1]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hq : (m : ℝ) / W ≤ t - s + 1 := by rw [div_le_iff₀ hWpos]; linarith
  have hq0 : 0 ≤ (m : ℝ) / W := by positivity
  have hK4 : 0 ≤ K4 := le_max_of_le_left hKk
  have hβ' : ∑ u ∈ range m, (eLpNorm (bracketError b E (e W) W (k' + 1) (l' + 1) (rs + u)) 1
      (growthPathLaw W b)).toReal ≤ βn n :=
    sum_range_le_window (W := W) (s := s) (t := t) (t' := t + 1)
      (f := fun r => (eLpNorm (bracketError b E (e W) W (k' + 1) (l' + 1) r) 1
        (growthPathLaw W b)).toReal) (fun r => ENNReal.toReal_nonneg) (by linarith)
  have hσk' : ∑ u ∈ range m, (eLpNorm (driftError b E (e W) W (k' + 1) (rs + u)) 2
      (growthPathLaw W b)).toReal ≤ σkn n :=
    sum_range_le_window (W := W) (s := s) (t := t) (t' := t + 1)
      (f := fun r => (eLpNorm (driftError b E (e W) W (k' + 1) r) 2
        (growthPathLaw W b)).toReal) (fun r => ENNReal.toReal_nonneg) (by linarith)
  have hσl' : ∑ u ∈ range m, (eLpNorm (driftError b E (e W) W (l' + 1) (rs + u)) 2
      (growthPathLaw W b)).toReal ≤ σln n :=
    sum_range_le_window (W := W) (s := s) (t := t) (t' := t + 1)
      (f := fun r => (eLpNorm (driftError b E (e W) W (l' + 1) r) 2
        (growthPathLaw W b)).toReal) (fun r => ENNReal.toReal_nonneg) (by linarith)
  have hν2 : Real.sqrt (1 + 320 * (m : ℝ) ^ 2 * (K4 / (W : ℝ) ^ 2)) ≤ ν' := by
    refine Real.sqrt_le_sqrt ?_
    have h1 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq 2) hK4
    have e3 : (m : ℝ) ^ 2 * (K4 / (W : ℝ) ^ 2) = ((m : ℝ) / W) ^ 2 * K4 := by
      field_simp
    calc 1 + 320 * (m : ℝ) ^ 2 * (K4 / (W : ℝ) ^ 2) = 1 + 320 * (((m : ℝ) / W) ^ 2 * K4) := by
          rw [← e3]; ring
      _ ≤ 1 + 320 * ((t - s + 1) ^ 2 * K4) := by gcongr
      _ = _ := by ring
  have hc₁ : (m : ℝ) * (ck / W * (cl / W)) ≤ c₁ / W := by
    calc (m : ℝ) * (ck / W * (cl / W)) = (m : ℝ) / W * (ck * cl) / W := by ring
      _ ≤ (t - s + 1) * (ck * cl) / W := by gcongr
      _ = c₁ / W := rfl
  exact prod_real_le hβ' (sum_nonneg fun _ _ => ENNReal.toReal_nonneg) hσk'
    (sum_nonneg fun _ _ => ENNReal.toReal_nonneg) hσl' (Real.sqrt_nonneg _) hν2 (by positivity)
    (by positivity) hc₁

end BlockBand.Transmission.Generator
