module

public import BlockBand.Window.Count.RefinedCountLocationTools
public import BlockBand.Window.Count.RefinedCountCount
public import BlockBand.Window.Count.RingFreshBlockLaw

/-!
# The refined count: location clause and assembly

For bulk ranks `α`, `‖λ_α - e_α‖_q ≤ C_q a_{n,W}/N`, deduced from the count clause; together they
give `RefinedCountStatement` (`refinedCount_holds`).

Proof (a multiscale form of the tail integration). Put `δ = πϑ/4`, `c = √(2δ)/(2π)`,
`s = a_{n,W}/N`, `X = λ_α - e_α`, `D_x = N_H(x) - N F_sc(x)`.
* `e_α ∈ bulkInterval 2δ` and `ρ_sc ≥ c` on `bulkInterval δ`, so for `0 < t ≤ δ`,
  `|X| > t` forces `|D_{e_α ± t}| ≥ cNt` at one sign (a.s., on the Hermitian set);
  hence `1 ≤ Y_t := (D_{e-t}/(cNt))² + (D_{e+t}/(cNt))²`.
* Pointwise `|X| ≤ s + s Σ_{k<⌊δ/s⌋} Y_{(k+1)s} + X²/(2λ) + (λ/2) Y_δ`, `λ = R²/s`.
* `‖Y_t‖_q ≤ 2 (C s/(c t))²` from the count clause at order `2q` on `bulkInterval δ`
  (`‖D‖_{2q} ≤ C a_{n,W}`), so the grid sum costs `≤ 4 (C/c)² s` (`Σ (k+1)⁻² ≤ 2`);
  `‖X²‖_q = ‖X‖_{2q}² ≤ R²` from `RankLocationContract.location` at order `2q` (the
  "uniform fixed moments" input, used only far from `e_α`); the last two terms cost
  `s/2 + R² (C/(cδ))² s`.
Dependencies: the count clause (here a hypothesis of `refinedCount_location_of_count`,
discharged by `refinedCount_count_of`) and `RankLocationContract.location`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Window.Count

open MeasureTheory
open BlockBand.Model.Construction BlockBand.Internal.Contracts.CoareaPalm
open BlockBand.Internal.Contracts.Layers BlockBand.Internal.Contracts.WindowAngular
open BlockBand.RankLocation BlockBand.Foundations.Spectral
open scoped ENNReal

theorem eLpNorm_const_mul_le_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {r B : ℝ} {p : ℝ≥0∞} (hr : 0 ≤ r) (h : eLpNorm f p μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => r * f ω) p μ ≤ ENNReal.ofReal (r * B) := by
  have : (fun ω => r * f ω) = r • f := rfl
  rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hr, ENNReal.ofReal_mul hr]
  gcongr

theorem eLpNorm_sq_le_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) {q B : ℝ}
    (hq : 1 ≤ q) (h : eLpNorm f (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => f ω ^ 2) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (max B 0 ^ 2) := by
  have h' := eLpNorm_le_of_sq_bound μ (fun ω => f ω ^ 2) (fun ω => ‖f ω‖) hf.norm
    (hf.pow 2) (fun ω => norm_nonneg _) hq zero_le_one le_rfl (le_max_right B 0)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, sq_abs, abs_of_nonneg (sq_nonneg _)]; linarith)
    (by rw [eLpNorm_norm f hf]; exact h.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  simpa using h'

theorem sum_range_inv_succ_sq_le (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / ((k : ℝ) + 1) ^ 2) ≤ 2 - 2 / ((K : ℝ) + 1) := by
  induction K with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have key : 1 / ((m : ℝ) + 1) ^ 2 ≤ 2 / ((m : ℝ) + 1) - 2 / ((m : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

set_option maxHeartbeats 1600000 in
/-- The location clause of the refined count, from the count clause. Physical law;
`b, T, ϑ ∈ (0,1/2), q ≥ 1` first, then `C_q`; for every admissible `p` with `p.b = b`,
`n ≤ TW`, every realization and every deterministic zero-based rank `α` with
`ϑ ≤ (α+1)/N ≤ 1 - ϑ`: `‖λ_α - e_α‖_q ≤ C_q a_{n,W}/N`. Inputs: the count clause of
the refined count (hypothesis `hcount`, used at order `2q` on `bulkInterval (πϑ/4)`) and
`RankLocationContract.location` (order `2q`). -/
theorem refinedCount_location_of_count
    (hcount : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ T : ℝ, 0 < κ → ∀ q : ℝ, 1 ≤ q →
      ∃ Cq : ℝ, ∀ (p : BlockBand.Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
      ∀ (model : p.GaussianRingModel) (e : ℝ), e ∈ bulkInterval κ →
        eLpNorm (fun H => (physicalCount p H e : ℝ) - p.N * semicircleCDF e)
            (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
          ENNReal.ofReal (Cq * countScale p.n p.W))
    (hRank : RankLocationContract) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ T ϑ : ℝ, 0 < ϑ → ϑ < 1 / 2 → ∀ q : ℝ, 1 ≤ q →
    ∃ Cq : ℝ, ∀ (p : BlockBand.Parameters), p.b = b → (p.n : ℝ) ≤ T * p.W →
    ∀ (model : p.GaussianRingModel) (α : Fin p.N), IsBulkRank p ϑ α →
      eLpNorm (fun H => physicalOrderedEigenvalue p H α - classicalLocation p α)
          (ENNReal.ofReal q) (model.law : Measure p.SiteMatrix) ≤
        ENNReal.ofReal (Cq * countScale p.n p.W / p.N) := by
  intro b hb hb' T ϑ hϑ hϑ' q hq
  set δ : ℝ := Real.pi * ϑ / 2 / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  set c : ℝ := Real.sqrt (2 * δ) / (2 * Real.pi) with hc
  have hc0 : 0 < c := div_pos (Real.sqrt_pos.mpr (by positivity)) (by positivity)
  obtain ⟨Cc, hCc⟩ := hcount b hb hb' δ T hδ0 (2 * q) (by linarith)
  obtain ⟨CR, hCR⟩ := hRank.location b hb hb' T ϑ hϑ hϑ' (2 * q) (by linarith)
  set Cc' := max Cc 0 with hCc'
  set R := max CR 1 with hR
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCc0 : 0 ≤ Cc' := le_max_right _ _
  refine ⟨2 + 4 * (Cc' / c) ^ 2 + R ^ 2 * (Cc' / (c * δ)) ^ 2, ?_⟩
  intro p hpb hpT model α hα
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix) with hμ
  set e := classicalLocation p α with he
  have heκ : e ∈ bulkInterval (Real.pi * ϑ / 2) := classicalLocation_mem_bulk p hϑ hα
  have hF : semicircleCDF e = ((α.val + 1 : ℕ) : ℝ) / p.N :=
    BlockBand.Window.Transfer.semicircleCDF_classicalLocation p α
  set N : ℝ := (p.N : ℝ) with hN
  have hN0 : 0 < N := Nat.cast_pos.mpr p.N_pos
  have hNF : N * semicircleCDF e = (α.val : ℝ) + 1 := by
    rw [hF]; push_cast; field_simp
  set a := countScale p.n p.W with ha
  have ha1 : 1 ≤ a := one_le_countScale p
  set s := a / N with hs
  have hs0 : 0 < s := div_pos (by linarith) hN0
  set X : p.SiteMatrix → ℝ := fun H => physicalOrderedEigenvalue p H α - e with hX
  have hXm : Measurable X := (measurable_physicalOrderedEigenvalue p α).sub_const _
  set D : ℝ → p.SiteMatrix → ℝ := fun x H => (physicalCount p H x : ℝ) - N * semicircleCDF x
    with hD
  have hDm : ∀ x, Measurable (D x) := fun x =>
    (measurable_negativeCount_real.comp (measurable_id.sub_const _)).sub_const _
  set Y : ℝ → p.SiteMatrix → ℝ := fun t H =>
    (1 / (c * N * t) * D (e - t) H) ^ 2 + (1 / (c * N * t) * D (e + t) H) ^ 2 with hY
  set lam := R ^ 2 / s with hlam
  have hlam0 : 0 < lam := by positivity
  have hmem : ∀ t, 0 ≤ t → t ≤ δ → e - t ∈ bulkInterval δ ∧ e + t ∈ bulkInterval δ := by
    intro t ht0 ht
    obtain ⟨h1, h2⟩ := heκ
    have h2δ : Real.pi * ϑ / 2 = 2 * δ := by rw [hδ]; ring
    rw [h2δ] at h1 h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have heδ : e ∈ bulkInterval δ := by simpa using (hmem 0 le_rfl hδ0.le).1
  -- the four pieces of the dominating function
  set G1 : p.SiteMatrix → ℝ := fun _ => s with hG1
  set G2 : p.SiteMatrix → ℝ :=
    ∑ k ∈ Finset.range ⌊δ / s⌋₊, fun H => s * Y ((k + 1) * s) H with hG2
  set G3 : p.SiteMatrix → ℝ := fun H => 1 / (2 * lam) * X H ^ 2 with hG3
  set G4 : p.SiteMatrix → ℝ := fun H => lam / 2 * Y δ H with hG4
  -- pointwise domination, almost surely (on the Hermitian set)
  have hpt : ∀ᵐ H ∂μ, ‖X H‖ ≤ (G1 + G2 + G3 + G4) H := by
    filter_upwards [model.isPhysical.1] with H hH
    have hYH : ∀ t, 0 < t → t ≤ δ → t < |X H| → 1 ≤ Y t H := by
      intro t ht0 htδ hlt
      obtain ⟨hm1, hm2⟩ := hmem t ht0.le htδ
      have hA : 0 < c * N * t := by positivity
      have hlow := semicircleCDF_sub_ge hδ0 hm1 heδ (by linarith)
      have hupp := semicircleCDF_sub_ge hδ0 heδ hm2 (by linarith)
      rw [← hc] at hlow hupp
      have hlower : (fun x => N * semicircleCDF x) (e - t) ≤
          ((physicalSpectralRank p α).val + 1 : ℝ) - c * N * t := by
        rw [physicalSpectralRank_val]
        have : N * (c * (e - (e - t))) ≤ N * (semicircleCDF e - semicircleCDF (e - t)) :=
          mul_le_mul_of_nonneg_left hlow hN0.le
        show N * semicircleCDF (e - t) ≤ _
        nlinarith
      have hupper : ((physicalSpectralRank p α).val + 1 : ℝ) + c * N * t ≤
          (fun x => N * semicircleCDF x) (e + t) := by
        rw [physicalSpectralRank_val]
        have : N * (c * (e + t - e)) ≤ N * (semicircleCDF (e + t) - semicircleCDF e) :=
          mul_le_mul_of_nonneg_left hupp hN0.le
        show _ ≤ N * semicircleCDF (e + t)
        nlinarith
      have hdev : t < |increasingEigenvalue hH (physicalSpectralRank p α) - e| := by
        rw [← physicalOrderedEigenvalue_eq p hH α]; exact hlt
      have key := rank_deviation_forces_count_discrepancy (increasingEigenvalue_monotone hH)
        (physicalSpectralRank p α) (fun x => N * semicircleCDF x) e t (c * N * t)
        hlower hupper hdev
      rw [← physicalCount_eq_countBelow p hH, ← physicalCount_eq_countBelow p hH] at key
      have hsq : ∀ d : ℝ, c * N * t ≤ |d| → 1 ≤ (1 / (c * N * t) * d) ^ 2 := by
        intro d hd
        rw [show (1 / (c * N * t) * d) ^ 2 = (|d| / (c * N * t)) ^ 2 by
          rw [div_pow, sq_abs]; ring]
        exact one_le_pow₀ ((one_le_div hA).mpr hd)
      show 1 ≤ (1 / (c * N * t) * D (e - t) H) ^ 2 + (1 / (c * N * t) * D (e + t) H) ^ 2
      rcases key with h | h
      · have h1 := hsq _ h
        have h2 := sq_nonneg (1 / (c * N * t) * D (e + t) H)
        exact le_add_of_le_of_nonneg h1 h2
      · have h1 := hsq _ h
        have h2 := sq_nonneg (1 / (c * N * t) * D (e - t) H)
        exact le_add_of_nonneg_of_le h2 h1
    have h := abs_le_multiscale (x := |X H|) hs0 hδ0 hlam0 (fun t => Y t H)
      (fun t => by positivity) hYH
    simp only [sq_abs] at h
    rw [Real.norm_eq_abs]
    simp only [hG1, hG2, hG3, hG4, Pi.add_apply, Finset.sum_apply]
    rw [← Finset.mul_sum]
    calc |X H| ≤ _ := h
      _ = _ := by ring
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hq
  -- `‖Y_t‖_q`
  have hYb : ∀ t, 0 < t → t ≤ δ →
      eLpNorm (Y t) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (2 * (Cc' * s / (c * t)) ^ 2) := by
    intro t ht0 htδ
    obtain ⟨hm1, hm2⟩ := hmem t ht0.le htδ
    have hA : 0 < c * N * t := by positivity
    have hone : ∀ x, x ∈ bulkInterval δ →
        eLpNorm (fun H => (1 / (c * N * t) * D x H) ^ 2) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal ((Cc' * s / (c * t)) ^ 2) := by
      intro x hx
      have h1 : eLpNorm (D x) (ENNReal.ofReal (2 * q)) μ ≤ ENNReal.ofReal (Cc * a) :=
        hCc p hpb hpT model x hx
      have h2 := eLpNorm_const_mul_le_ofReal μ (D x) (r := 1 / (c * N * t))
        (by positivity) h1
      have h3 := eLpNorm_sq_le_ofReal μ (fun H => 1 / (c * N * t) * D x H)
        (((hDm x).const_mul _).aestronglyMeasurable) hq h2
      refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
      apply pow_le_pow_left₀ (le_max_right _ _)
      apply max_le _ (by positivity)
      have heq : Cc' * s / (c * t) = 1 / (c * N * t) * (Cc' * a) := by
        rw [hs]; field_simp
      rw [heq]
      gcongr
      exact le_max_left _ _
    calc eLpNorm (Y t) (ENNReal.ofReal q) μ
        ≤ eLpNorm (fun H => (1 / (c * N * t) * D (e - t) H) ^ 2) (ENNReal.ofReal q) μ +
          eLpNorm (fun H => (1 / (c * N * t) * D (e + t) H) ^ 2) (ENNReal.ofReal q) μ :=
          eLpNorm_add_le (f := fun H => (1 / (c * N * t) * D (e - t) H) ^ 2)
            (g := fun H => (1 / (c * N * t) * D (e + t) H) ^ 2) hp1
      _ ≤ ENNReal.ofReal ((Cc' * s / (c * t)) ^ 2) + ENNReal.ofReal ((Cc' * s / (c * t)) ^ 2) :=
          add_le_add (hone _ hm1) (hone _ hm2)
      _ = ENNReal.ofReal (2 * (Cc' * s / (c * t)) ^ 2) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
  -- the four bounds
  have hb1 : eLpNorm G1 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal s := by
    rw [hG1, eLpNorm_const _ (by positivity) (IsProbabilityMeasure.ne_zero μ), measure_univ,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal hs0.le]
  have hb2 : eLpNorm G2 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (s * (4 * (Cc' / c) ^ 2)) := by
    rw [hG2]
    calc eLpNorm (∑ k ∈ Finset.range ⌊δ / s⌋₊, fun H => s * Y ((k + 1) * s) H)
          (ENNReal.ofReal q) μ
        ≤ ∑ k ∈ Finset.range ⌊δ / s⌋₊,
            eLpNorm (fun H => s * Y ((k + 1) * s) H) (ENNReal.ofReal q) μ :=
          eLpNorm_sum_le hp1
      _ ≤ ∑ k ∈ Finset.range ⌊δ / s⌋₊,
            ENNReal.ofReal (s * (2 * (Cc' / c) ^ 2 * (1 / ((k : ℝ) + 1) ^ 2))) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : ((k : ℝ) + 1) * s ≤ δ := by
            have h1 : k + 1 ≤ ⌊δ / s⌋₊ := Finset.mem_range.mp hk
            have h2 : ((k + 1 : ℕ) : ℝ) ≤ δ / s :=
              (Nat.cast_le.mpr h1).trans (Nat.floor_le (div_nonneg hδ0.le hs0.le))
            push_cast at h2
            rwa [le_div_iff₀ hs0] at h2
          have := eLpNorm_const_mul_le_ofReal μ (Y ((k + 1) * s)) hs0.le
            (hYb ((k + 1) * s) (by positivity) hk')
          refine this.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
          field_simp
      _ = ENNReal.ofReal (∑ k ∈ Finset.range ⌊δ / s⌋₊,
            s * (2 * (Cc' / c) ^ 2 * (1 / ((k : ℝ) + 1) ^ 2))) :=
          (ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity).symm
      _ ≤ ENNReal.ofReal (s * (4 * (Cc' / c) ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          have h1 := sum_range_inv_succ_sq_le ⌊δ / s⌋₊
          have h2 : 0 ≤ 2 / ((⌊δ / s⌋₊ : ℝ) + 1) := by positivity
          have h3 : 0 ≤ 2 * (Cc' / c) ^ 2 := by positivity
          have h4 : 2 * (Cc' / c) ^ 2 * ∑ k ∈ Finset.range ⌊δ / s⌋₊, 1 / ((k : ℝ) + 1) ^ 2 ≤
              2 * (Cc' / c) ^ 2 * 2 := mul_le_mul_of_nonneg_left (by linarith) h3
          have h5 := mul_le_mul_of_nonneg_left h4 hs0.le
          nlinarith
  have hXsq : eLpNorm (fun H => X H ^ 2) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (R ^ 2) := by
    have h1 : eLpNorm X (ENNReal.ofReal (2 * q)) μ ≤
        ENNReal.ofReal (CR / (p.n * Real.sqrt p.W)) := hCR p hpb hpT model .physical α hα
    have h2 := eLpNorm_sq_le_ofReal μ X hXm.aestronglyMeasurable hq h1
    refine h2.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_max_right _ _) ?_ 2))
    refine max_le ?_ hR0.le
    have hn : (4 : ℝ) ≤ p.n := by exact_mod_cast p.n_ge_four
    have hW : (1 : ℝ) ≤ Real.sqrt p.W := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast p.W_pos)
    have hnW : 1 ≤ (p.n : ℝ) * Real.sqrt p.W := by nlinarith
    rcases le_total CR 0 with hC | hC
    · exact (div_nonpos_of_nonpos_of_nonneg hC (by linarith)).trans hR0.le
    · exact (div_le_self hC hnW).trans (le_max_left _ _)
  have hb3 : eLpNorm G3 (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (1 / (2 * lam) * R ^ 2) :=
    eLpNorm_const_mul_le_ofReal μ (fun H => X H ^ 2) (by positivity) hXsq
  have hb4 : eLpNorm G4 (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (lam / 2 * (2 * (Cc' * s / (c * δ)) ^ 2)) :=
    eLpNorm_const_mul_le_ofReal μ (Y δ) (by positivity) (hYb δ hδ0 le_rfl)
  -- assembly
  change eLpNorm X (ENNReal.ofReal q) μ ≤ _
  have hsplit := eLpNorm_mono_ae_real (p := ENNReal.ofReal q) hXm.aestronglyMeasurable hpt
  have hsum : eLpNorm (G1 + G2 + G3 + G4) (ENNReal.ofReal q) μ ≤
      eLpNorm G1 (ENNReal.ofReal q) μ + eLpNorm G2 (ENNReal.ofReal q) μ +
        eLpNorm G3 (ENNReal.ofReal q) μ + eLpNorm G4 (ENNReal.ofReal q) μ := by
    calc _ ≤ eLpNorm (G1 + G2 + G3) (ENNReal.ofReal q) μ + eLpNorm G4 (ENNReal.ofReal q) μ :=
          eLpNorm_add_le hp1
      _ ≤ (eLpNorm (G1 + G2) (ENNReal.ofReal q) μ + eLpNorm G3 (ENNReal.ofReal q) μ) +
            eLpNorm G4 (ENNReal.ofReal q) μ := by gcongr; exact eLpNorm_add_le hp1
      _ ≤ _ := by gcongr; exact eLpNorm_add_le hp1
  have e1 : 0 ≤ s * (4 * (Cc' / c) ^ 2) :=
    mul_nonneg hs0.le (mul_nonneg (by norm_num) (sq_nonneg _))
  have e2 : 0 ≤ 1 / (2 * lam) * R ^ 2 :=
    mul_nonneg (div_nonneg zero_le_one (by linarith)) (sq_nonneg _)
  have e3 : 0 ≤ lam / 2 * (2 * (Cc' * s / (c * δ)) ^ 2) :=
    mul_nonneg (div_nonneg hlam0.le (by norm_num)) (mul_nonneg (by norm_num) (sq_nonneg _))
  calc eLpNorm X (ENNReal.ofReal q) μ ≤ _ := hsplit
    _ ≤ _ := hsum
    _ ≤ ENNReal.ofReal s + ENNReal.ofReal (s * (4 * (Cc' / c) ^ 2)) +
          ENNReal.ofReal (1 / (2 * lam) * R ^ 2) +
          ENNReal.ofReal (lam / 2 * (2 * (Cc' * s / (c * δ)) ^ 2)) := by gcongr
    _ = ENNReal.ofReal (s + s * (4 * (Cc' / c) ^ 2) + 1 / (2 * lam) * R ^ 2 +
          lam / 2 * (2 * (Cc' * s / (c * δ)) ^ 2)) := by
        rw [← ENNReal.ofReal_add hs0.le e1, ← ENNReal.ofReal_add (by positivity) e2,
          ← ENNReal.ofReal_add (by positivity) e3]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have f3 : 1 / (2 * lam) * R ^ 2 = s / 2 := by
          rw [hlam]; field_simp
        have f4 : lam / 2 * (2 * (Cc' * s / (c * δ)) ^ 2) =
            R ^ 2 * (Cc' / (c * δ)) ^ 2 * s := by
          rw [hlam]; field_simp
        rw [f3, f4, mul_div_assoc, ← hs]
        nlinarith

/-- **`RefinedCountStatement`**, both clauses, physical law.
Dependencies: `SharperFreshCountStatement`, `MatchedTracesContract`,
`RingCompensatedPhaseContract`, `RankLocationContract`, `FreshCountContract`.
The count clause is `refinedCount_count_of`; the location clause is
`refinedCount_location_of_count` applied to it and to `RankLocationContract`.
The fresh-block split is not a hypothesis: it is `ringFreshBlockSplitAE`
(Schur inertia a.s., transport to `Fin W`, law split).
-/
theorem refinedCount_holds
    (hSharp : SharperFreshCountStatement) (hMT : MatchedTracesContract)
    (hRing : RingCompensatedPhaseContract) (hRank : RankLocationContract)
    (hFresh : FreshCountContract) : RefinedCountStatement where
  count := refinedCount_count_of ringFreshBlockSplitAE hSharp hMT hRing hRank hFresh
  location := refinedCount_location_of_count
    (refinedCount_count_of ringFreshBlockSplitAE hSharp hMT hRing hRank hFresh) hRank

end BlockBand.Window.Count
