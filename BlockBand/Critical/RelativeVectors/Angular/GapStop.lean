module

public import BlockBand.Critical.RelativeVectors.Angular.Selection

/-!
# The gap stop: continuity, path measurability, restart identity, coupling bound

The gap stop `σ` is the infimum of the times `u` at which some eigenvalue gap of `H_{s+u}` is at
most `1/n`.

* `gap_gt_of_lt_gapStop`: before `σ` every gap of `H_{s+v}` exceeds `1/n`;
* `lt_gapStop_iff_rat`: `c < σ` iff for each pair there is `m` with all gaps `≥ 1/n + 1/(m+1)`
  at the rational times of `[0, c]` (closedness of the gap events);
* `stopIndex_shift`: on `{t < σ}`, `t + (u' ∧ σ^{(s+t)}) = (t + u') ∧ σ` (restart identity);
* `dysonCoupling_fresh_le`: before `σ` every coupling of increasing ranks is in `[0, n²/N]`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors.Angular

open MeasureTheory Matrix Set Filter Topology
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Foundations.Spectral BlockBand.Model.Construction BlockBand.Palm.MomentFlow
open scoped NNReal

variable {N : ℕ}

/-- Every `dysonEigenvalue` is continuous on all matrices (it is half an eigenvalue of the
Hermitian `H + Hᴴ`). -/
theorem continuous_dysonEigenvalue (i : Fin N) :
    Continuous fun H : Matrix (Fin N) (Fin N) ℂ => dysonEigenvalue N H i := by
  have hc : Continuous fun H : Matrix (Fin N) (Fin N) ℂ =>
      (⟨H + Hᴴ, Matrix.isHermitian_add_transpose_self H⟩ : HermitianMatrix (Fin N)) :=
    (continuous_id.add continuous_id.matrix_conjTranspose).subtype_mk _
  refine (((continuous_increasingEigenvalue
    (Fin.cast (Fintype.card_fin N).symm i.rev)).comp hc).div_const 2).congr fun H => ?_
  simp only [Function.comp_apply]
  rw [dysonEigenvalue_eq_fresh_add, freshEigenvalue,
    rawIncreasingEigenvalue_eq _ _ (Matrix.isHermitian_add_transpose_self H)]

/-- The gap of the pair `(i, j)` at real time `x` after `s`. -/
def gapFun {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ω : Ω)
    (i j : Fin N) (x : ℝ) : ℝ :=
  |dysonEigenvalue N (H (s + x.toNNReal) ω) i - dysonEigenvalue N (H (s + x.toNNReal) ω) j|

theorem continuous_gapFun {Ω : Type*} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ ω, Continuous fun t => H t ω) (s : ℝ≥0) (ω : Ω) (i j : Fin N) :
    Continuous (gapFun H s ω i j) := by
  have hp : Continuous fun x : ℝ => H (s + x.toNNReal) ω :=
    (hH ω).comp (continuous_const.add continuous_real_toNNReal)
  exact (((continuous_dysonEigenvalue i).comp hp).sub ((continuous_dysonEigenvalue j).comp hp)).abs

theorem gapFun_coe {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (ω : Ω)
    (i j : Fin N) (v : ℝ≥0) :
    gapFun H s ω i j v =
      |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| := by
  simp [gapFun]

/-- `w ≤ σ` iff every small-gap time is `≥ w`. -/
theorem coe_le_gapStop_iff {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (n : ℕ) (ω : Ω) (w : ℝ≥0) :
    (w : WithTop ℝ≥0) ≤ gapStop N H s n ω ↔ ∀ u : ℝ≥0, (∃ i j : Fin N, i ≠ j ∧
      |dysonEigenvalue N (H (s + u) ω) i - dysonEigenvalue N (H (s + u) ω) j| ≤ 1 / (n : ℝ)) →
        w ≤ u := by
  unfold gapStop
  rw [le_iInf₂_iff]
  simp only [WithTop.coe_le_coe]

theorem gapStop_le {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0) (n : ℕ)
    (ω : Ω) (u : ℝ≥0) (hu : ∃ i j : Fin N, i ≠ j ∧
      |dysonEigenvalue N (H (s + u) ω) i - dysonEigenvalue N (H (s + u) ω) j| ≤ 1 / (n : ℝ)) :
    gapStop N H s n ω ≤ u := by
  unfold gapStop
  exact iInf₂_le u hu

/-- Before the gap stop every gap exceeds `1/n`. -/
theorem gap_gt_of_lt_gapStop {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s : ℝ≥0)
    (n : ℕ) (ω : Ω) {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) < gapStop N H s n ω) {i j : Fin N}
    (hij : i ≠ j) :
    1 / (n : ℝ) < |dysonEigenvalue N (H (s + v) ω) i - dysonEigenvalue N (H (s + v) ω) j| := by
  by_contra hle
  push Not at hle
  exact absurd (gapStop_le H s n ω v ⟨i, j, hij, hle⟩) (not_le.2 hv)

/-- A continuous function `≥ δ` at the rationals of `[0,u]` is `≥ δ` on `[0,u]`. -/
theorem ge_on_Icc_of_rat' {φ : ℝ → ℝ} (hφ : Continuous φ) {u δ : ℝ} (hu : 0 ≤ u)
    (h : ∀ v : ℚ, 0 ≤ (v : ℝ) → (v : ℝ) ≤ u → δ ≤ φ v) : ∀ x ∈ Icc 0 u, δ ≤ φ x := by
  have hS : IsClosed {x : ℝ | δ ≤ φ x} := isClosed_le continuous_const hφ
  rcases hu.eq_or_lt with rfl | hpos
  · intro x hx
    have : x = ((0 : ℚ) : ℝ) := by simp; exact le_antisymm hx.2 hx.1
    rw [this]; exact h 0 (by simp) (by simp)
  · have hsub : Ioo 0 u ∩ range ((↑) : ℚ → ℝ) ⊆ {x : ℝ | δ ≤ φ x} := by
      rintro x ⟨hx, v, rfl⟩
      exact h v hx.1.le hx.2.le
    have h1 : Ioo (0 : ℝ) u ⊆ closure (Ioo 0 u ∩ range ((↑) : ℚ → ℝ)) :=
      Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo
    have h2 : Icc (0 : ℝ) u ⊆ {x : ℝ | δ ≤ φ x} := by
      rw [← closure_Ioo hpos.ne]
      exact closure_minimal (h1.trans (closure_minimal hsub hS)) hS
    exact fun x hx => h2 hx

/-- If all gaps exceed `1/n` on `[0, c]` then `c < σ` (the gap condition is open). -/
theorem lt_gapStop_of_gap {Ω : Type*} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ ω, Continuous fun t => H t ω) (s : ℝ≥0) (n : ℕ) (ω : Ω) (c : ℝ≥0)
    (h : ∀ v : ℝ≥0, v ≤ c → ∀ i j : Fin N, i ≠ j → 1 / (n : ℝ) < gapFun H s ω i j v) :
    (c : WithTop ℝ≥0) < gapStop N H s n ω := by
  set U : Set ℝ := ⋂ i : Fin N, ⋂ j : Fin N, {x : ℝ | i ≠ j → 1 / (n : ℝ) < gapFun H s ω i j x}
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using isOpen_lt continuous_const (continuous_gapFun hH s ω i j)
  have hc : (c : ℝ) ∈ U := by
    simp only [U, mem_iInter, mem_ofPred_eq]
    exact fun i j hij => h c le_rfl i j hij
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU c hc
  set e : ℝ≥0 := (ε / 2).toNNReal
  have he : (0 : ℝ) < e := by simp [e, hε]
  have hle : ((c + e : ℝ≥0) : WithTop ℝ≥0) ≤ gapStop N H s n ω := by
    rw [coe_le_gapStop_iff]
    rintro u ⟨i, j, hij, hu⟩
    by_contra hlt
    push Not at hlt
    rcases le_total u c with huc | hcu
    · exact absurd hu (not_le.2 (by simpa [gapFun_coe] using h u huc i j hij))
    · have hmem : (u : ℝ) ∈ Metric.ball (c : ℝ) ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        have h1 : (u : ℝ) < c + e := by exact_mod_cast hlt
        have h2 : (e : ℝ) ≤ ε / 2 := by simp [e, le_of_lt (half_pos hε)]
        constructor
        · have : (c : ℝ) ≤ u := by exact_mod_cast hcu
          linarith
        · linarith
      have := hball hmem
      simp only [U, mem_iInter, mem_ofPred_eq] at this
      exact absurd hu (not_le.2 (by simpa [gapFun_coe] using this i j hij))
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast (lt_add_iff_pos_right c).2 (by exact_mod_cast he)

/-- `c < σ` iff for each pair the gaps at rational times of `[0, c]` are `≥ 1/n + 1/(m+1)`. -/
theorem lt_gapStop_iff_rat {Ω : Type*} {H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    (hH : ∀ ω, Continuous fun t => H t ω) (s : ℝ≥0) (n : ℕ) (ω : Ω) (c : ℝ≥0) :
    (c : WithTop ℝ≥0) < gapStop N H s n ω ↔ ∀ i j : Fin N, i ≠ j → ∃ m : ℕ, ∀ q : ℚ,
      0 ≤ (q : ℝ) → (q : ℝ) ≤ c → 1 / (n : ℝ) + 1 / ((m : ℝ) + 1) ≤ gapFun H s ω i j q := by
  constructor
  · intro hc i j hij
    have hpos : ∀ x ∈ Icc (0 : ℝ) c, 1 / (n : ℝ) < gapFun H s ω i j x := by
      intro x hx
      have hv : ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0) < gapStop N H s n ω := by
        refine lt_of_le_of_lt ?_ hc
        exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hx.2
      simpa [gapFun] using gap_gt_of_lt_gapStop H s n ω hv hij
    obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := c)).exists_isMinOn
      ⟨0, le_rfl, c.2⟩ (continuous_gapFun hH s ω i j).continuousOn
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 (hpos x0 hx0))
    refine ⟨m, fun q hq0 hqc => ?_⟩
    have := hmin (show (q : ℝ) ∈ Icc (0 : ℝ) c from ⟨hq0, hqc⟩)
    simp only [mem_ofPred_eq] at this
    linarith
  · intro h
    refine lt_gapStop_of_gap hH s n ω c fun v hv i j hij => ?_
    obtain ⟨m, hm⟩ := h i j hij
    have := ge_on_Icc_of_rat' (continuous_gapFun hH s ω i j) c.2 hm v ⟨v.2, by exact_mod_cast hv⟩
    have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith

/-- Each eigenvalue at time `s + v` is measurable for the eigenvalue path σ-algebra after `s`. -/
theorem measurable_dysonEigenvalue_pathSigma {Ω : Type*} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (s v : ℝ≥0) :
    Measurable[BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G s]
      fun ω => dysonEigenvalue N (F ω + G (s + v) ω) :=
  Measurable.of_comap_le (le_iSup (fun v => MeasurableSpace.comap
    (fun ω => dysonEigenvalue N (F ω + G (s + v) ω)) inferInstance) v)

/-- `{c < σ}` is an event of the eigenvalue path after `s`. -/
theorem measurableSet_lt_gapStop {Ω : Type*} (F : Ω → Matrix (Fin N) (Fin N) ℂ)
    (G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ) (hG : ∀ ω, Continuous fun t => G t ω)
    (s : ℝ≥0) (n : ℕ) (c : ℝ≥0) :
    MeasurableSet[BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G s]
      {ω | (c : WithTop ℝ≥0) < gapStop N (fun t ω => F ω + G t ω) s n ω} := by
  have hH : ∀ ω, Continuous fun t => F ω + G t ω := fun ω => continuous_const.add (hG ω)
  have e : {ω | (c : WithTop ℝ≥0) < gapStop N (fun t ω => F ω + G t ω) s n ω} =
      ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i ≠ j), ⋃ m : ℕ, ⋂ q : ℚ,
        ⋂ (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ c), {ω | 1 / (n : ℝ) + 1 / ((m : ℝ) + 1) ≤
          gapFun (fun t ω => F ω + G t ω) s ω i j q} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, and_imp]
    exact lt_gapStop_iff_rat hH s n ω c
  rw [e]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter
    fun _ => MeasurableSet.iUnion fun m => MeasurableSet.iInter fun q =>
      MeasurableSet.iInter fun _ => ?_
  let _ : MeasurableSpace Ω :=
    BlockBand.Internal.Contracts.TransmissionAngular.eigenPathSigma N F G s
  have h : Measurable fun ω => dysonEigenvalue N (F ω + G (s + (q : ℝ).toNNReal) ω) :=
    measurable_dysonEigenvalue_pathSigma F G s _
  have hm : Measurable fun ω => gapFun (fun t ω => F ω + G t ω) s ω i j q :=
    (((measurable_pi_apply i).comp h).sub ((measurable_pi_apply j).comp h)).abs
  exact hm measurableSet_Ici

/-!
## The restart identity
-/

theorem coe_le_gapStop_shift_iff {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (s t : ℝ≥0) (n : ℕ) (ω : Ω) (ht : (t : WithTop ℝ≥0) < gapStop N H s n ω) (w : ℝ≥0) :
    (w : WithTop ℝ≥0) ≤ gapStop N H (s + t) n ω ↔
      ((t + w : ℝ≥0) : WithTop ℝ≥0) ≤ gapStop N H s n ω := by
  rw [coe_le_gapStop_iff, coe_le_gapStop_iff]
  constructor
  · intro h u hu
    have htu : t < u := by
      have := lt_of_lt_of_le ht (gapStop_le H s n ω u hu)
      exact_mod_cast this
    have e : s + u = s + t + (u - t) := by
      rw [add_assoc, add_tsub_cancel_of_le htu.le]
    have := h (u - t) (by rw [← e]; exact hu)
    calc t + w ≤ t + (u - t) := add_le_add_right this t
      _ = u := add_tsub_cancel_of_le htu.le
  · intro h u hu
    have := h (t + u) (by rw [← add_assoc]; exact hu)
    exact le_of_add_le_add_left this

/-- **Restart identity.** On `{t < σ}`: `t + (u' ∧ σ^{(s+t)}) = (t + u') ∧ σ`. -/
theorem stopIndex_shift {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (s t : ℝ≥0) (n : ℕ) (ω : Ω) (ht : (t : WithTop ℝ≥0) < gapStop N H s n ω) (u' : ℝ≥0) :
    t + (min (u' : WithTop ℝ≥0) (gapStop N H (s + t) n ω)).untopA =
      (min ((t + u' : ℝ≥0) : WithTop ℝ≥0) (gapStop N H s n ω)).untopA := by
  set a := min (u' : WithTop ℝ≥0) (gapStop N H (s + t) n ω)
  set b := min ((t + u' : ℝ≥0) : WithTop ℝ≥0) (gapStop N H s n ω)
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have hb : b ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  have key : ∀ w : ℝ≥0, (w : WithTop ℝ≥0) ≤ a ↔ ((t + w : ℝ≥0) : WithTop ℝ≥0) ≤ b := by
    intro w
    simp only [a, b, le_min_iff, coe_le_gapStop_shift_iff H s t n ω ht w, WithTop.coe_le_coe]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨add_le_add_right h1 t, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨le_of_add_le_add_left h1, h2⟩
  have htb : t ≤ b.untopA := by
    rw [WithTop.le_untopA_iff hb]
    simp only [b, le_min_iff, WithTop.coe_le_coe]
    exact ⟨le_self_add, ht.le⟩
  apply le_antisymm
  · rw [WithTop.le_untopA_iff hb, ← key, ← WithTop.le_untopA_iff ha]
  · have h1 : b.untopA - t ≤ a.untopA := by
      rw [WithTop.le_untopA_iff ha, key, add_tsub_cancel_of_le htb, ← WithTop.le_untopA_iff hb]
    rw [tsub_le_iff_left] at h1
    exact h1

/-!
## Couplings before the gap stop
-/

/-- Before the gap stop every coupling of increasing ranks `i < j` is in `[0, n²/N]`. -/
theorem dysonCoupling_fresh_le {Ω : Type*} (H : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ)
    (s : ℝ≥0) (n : ℕ) (ω : Ω) {v : ℝ≥0} (hv : (v : WithTop ℝ≥0) < gapStop N H s n ω)
    (hherm : (H (s + v) ω).IsHermitian) (hn : 0 < n) {i j : Fin N} (hij : i < j) :
    0 ≤ dysonCoupling N (fun ℓ => freshEigenvalue (H (s + v) ω) ℓ) i j ∧
      dysonCoupling N (fun ℓ => freshEigenvalue (H (s + v) ω) ℓ) i j ≤ (n : ℝ) ^ 2 / N := by
  have hne : i.rev ≠ j.rev := fun e => hij.ne (Fin.rev_injective e)
  have hgap := gap_gt_of_lt_gapStop H s n ω hv hne
  rw [dysonEigenvalue_rev hherm, dysonEigenvalue_rev hherm] at hgap
  set d := freshEigenvalue (H (s + v) ω) i - freshEigenvalue (H (s + v) ω) j
  have hN : (0 : ℝ) < N := by
    have : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_of_le_of_lt (Nat.zero_le j.val) j.2)
    exact_mod_cast this
  have hd2 : (1 / (n : ℝ)) ^ 2 < d ^ 2 := by
    have h0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    calc (1 / (n : ℝ)) ^ 2 < |d| ^ 2 := by gcongr
      _ = d ^ 2 := sq_abs d
  have hdpos : 0 < d ^ 2 := lt_of_le_of_lt (sq_nonneg _) hd2
  unfold dysonCoupling
  refine ⟨by positivity, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_le_div_iff₀ (by positivity) hN, one_mul]
  have : (1 / (n : ℝ)) ^ 2 * (n : ℝ) ^ 2 = 1 := by field_simp
  nlinarith [mul_lt_mul_of_pos_right hd2 (by positivity : (0 : ℝ) < (n : ℝ) ^ 2 * N)]

end BlockBand.Critical.RelativeVectors.Angular
