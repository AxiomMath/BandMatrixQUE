module

public import BlockBand.Palm.MomentFlow.FlatCommutator
public import BlockBand.Palm.MomentFlow.LongShortExcess
public import BlockBand.Palm.MomentFlow.FlatEnergy

/-!
# The continuous flattening excess

* `flatDatum F a c q W k₀ = Av_{ramp W k₀}(canonDatum)`, the flattened canonical datum.
* **`flatExcess`** `Y n v ω = Σ_{(k₀,ζ)} 1_{nearBulk k₀}(ω) (|fwdC(Av Φ(a))(v,ζ) - Av(shortC(v))(ζ)| - main)_+`
  over all centres and all `r`-configurations. It is `𝓛`-measurable, continuous in time, `≥ 0`,
  `≤ N^{r+1} · 2 overlapBound^r` on `gapSet n`, and independent of `n` there.
* `abs_avFlat_le`, `mlocB_le`: elementary bounds.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem abs_avFlat_le {aR f : Occ N → ℝ} {ζ : Occ N} {B : ℝ} (h0 : 0 ≤ aR ζ) (h1 : aR ζ ≤ 1)
    (hB : 1 ≤ B) (hf : |f ζ| ≤ B) : |avFlat aR f ζ| ≤ B := by
  unfold avFlat
  rw [abs_le] at hf ⊢
  constructor <;> nlinarith [hf.1, hf.2]

/-- `(C x^{4ε})^r + j + 1 ≤ (max(1,C)^r + 2) x^{4rε}`. -/
theorem mlocB_le {x ε Cst j : ℝ} {r : ℕ} (hx : 1 ≤ x) (hε : 0 ≤ ε) (hC : 0 ≤ Cst)
    (hj : j ≤ 1) :
    (Cst * x ^ (4 * ε)) ^ r + j + 1 ≤ (max 1 Cst ^ r + 2) * x ^ (4 * r * ε) := by
  have hx0 : 0 < x := by linarith
  have hy1 : 1 ≤ x ^ (4 * ε) := Real.one_le_rpow hx (by linarith)
  have hP : x ^ (4 * r * ε) = (x ^ (4 * ε)) ^ r := by
    rw [← Real.rpow_mul_natCast hx0.le]; ring_nf
  have hP1 : 1 ≤ x ^ (4 * r * ε) := by rw [hP]; exact one_le_pow₀ hy1
  have h1 : (Cst * x ^ (4 * ε)) ^ r ≤ max 1 Cst ^ r * x ^ (4 * r * ε) := by
    rw [hP, ← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hC (by linarith))
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)) _
  nlinarith

/-- The flattened canonical datum `Av_{ramp W k₀}(canonDatum)`. -/
def flatDatum (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (W : ℝ) (k₀ : Fin N) :
    FlowSample N → Occ N → ℝ :=
  fun ω ζ => avFlat (ramp W (k₀ : ℕ)) (canonDatum F a c q ω) ζ

/-- **The flattening excess.** -/
def flatExcess (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ)
    (E κ ρ W main v : ℝ) (ω : FlowSample N) : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin N)) ×ˢ sector N r,
    (nearBulk F a c E κ ρ p.1).indicator (fun ω =>
      max (|fwdC F a c ℓ r n (flatDatum F a c q W p.1) v ω p.2 -
        avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2| - main) 0) ω

theorem measurable_flatExcess {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W main v : ℝ) :
    Measurable[pathSigma F a a c] (flatExcess F a c q ℓ r n E κ ρ W main v) := by
  refine Finset.measurable_sum _ fun p _ => ?_
  have hd : ∀ ζ, Measurable[pathSigma F a a c] fun ω => flatDatum F a c q W p.1 ω ζ := fun ζ =>
    (measurable_const.mul (measurable_canonDatum F a c q ζ)).add measurable_const
  have h1 := measurable_fwdC hF hN hac ℓ r n hd v p.2
  have h2 : Measurable[pathSigma F a a c] fun ω =>
      avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2 :=
    (measurable_const.mul (measurable_shortC hF hN hac q ℓ r n v p.2)).add measurable_const
  exact (((continuous_abs.measurable.comp (h1.sub h2)).sub_const main).max
    measurable_const).indicator (measurableSet_nearBulk hF a c E κ ρ p.1)

theorem continuous_flatExcess {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W main : ℝ) (ω : FlowSample N) :
    Continuous fun v => flatExcess F a c q ℓ r n E κ ρ W main v ω := by
  refine continuous_finsetSum _ fun p _ => ?_
  by_cases hω : ω ∈ nearBulk F a c E κ ρ p.1
  · simp only [Set.indicator_of_mem hω]
    have h2 : Continuous fun v => avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2 :=
      (continuous_const.mul (continuous_shortC hF hN a c q ℓ r n ω p.2)).add continuous_const
    exact ((((continuous_fwdC hF hN a c ℓ r n _ ω p.2).sub h2).abs).sub continuous_const).max
      continuous_const
  · simp only [Set.indicator_of_notMem hω]
    exact continuous_const

theorem flatExcess_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a c : ℝ) (q : Fin N → ℂ) (ℓ r n : ℕ)
    (E κ ρ W main v : ℝ) (ω : FlowSample N) : 0 ≤ flatExcess F a c q ℓ r n E κ ρ W main v ω :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem term_le_flatExcess {F : Matrix (Fin N) (Fin N) ℂ} {a c : ℝ} {q : Fin N → ℂ} {ℓ r n : ℕ}
    {E κ ρ W main v : ℝ} {ω : FlowSample N} {k₀ : Fin N} {ζ : Occ N} (hζ : ζ ∈ sector N r)
    (hω : ω ∈ nearBulk F a c E κ ρ k₀) :
    max (|fwdC F a c ℓ r n (flatDatum F a c q W k₀) v ω ζ -
        avFlat (ramp W (k₀ : ℕ)) (shortC F a c q ℓ r n v ω) ζ| - main) 0 ≤
      flatExcess F a c q ℓ r n E κ ρ W main v ω := by
  have hp : (k₀, ζ) ∈ (Finset.univ : Finset (Fin N)) ×ˢ sector N r :=
    Finset.mem_product.2 ⟨Finset.mem_univ _, hζ⟩
  have h := Finset.single_le_sum (f := fun p : Fin N × Occ N => (nearBulk F a c E κ ρ p.1).indicator
    (fun ω => max (|fwdC F a c ℓ r n (flatDatum F a c q W p.1) v ω p.2 -
        avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2| - main) 0) ω)
    (fun _ _ => Set.indicator_nonneg (fun _ _ => le_max_right _ _) _) hp
  simp only [Set.indicator_of_mem hω] at h
  exact h

theorem fwdC_flatDatum_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) (W : ℝ) (k₀ : Fin N) (ℓ r n : ℕ)
    {ω : FlowSample N} (hω : ω ∈ gapSet F a c n) :
    ∀ v ∈ Icc a c, ∀ ζ ∈ sector N r,
      |fwdC F a c ℓ r n (flatDatum F a c q W k₀) v ω ζ| ≤ overlapBound N q ^ r := by
  have hB : 1 ≤ overlapBound N q ^ r := one_le_pow₀ (one_le_overlapBound q)
  have hd : ∀ ζ ∈ sector N r, |flatDatum F a c q W k₀ ω ζ| ≤ overlapBound N q ^ r := fun ζ hζ =>
    abs_avFlat_le (ramp_nonneg _ _ _) (ramp_le_one _ _ _) hB (abs_canonDatum_le F a c q hζ ω)
  intro v hv ζ hζ
  exact abs_le.2 (fwdC_bounds hF hN hac ℓ r n _ hω (fun ζ hζ => neg_le_of_abs_le (hd ζ hζ))
    (fun ζ hζ => le_of_abs_le (hd ζ hζ)) v hv ζ hζ)

theorem flatExcess_le {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N) {a c : ℝ}
    (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W : ℝ) {main : ℝ} (hmain : 0 ≤ main)
    {ω : FlowSample N} (hω : ω ∈ gapSet F a c n) {v : ℝ} (hv : v ∈ Icc a c) :
    flatExcess F a c q ℓ r n E κ ρ W main v ω ≤
      ((Finset.univ : Finset (Fin N)) ×ˢ sector N r).card * (2 * overlapBound N q ^ r) := by
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun p hp => ?_
  have hζ : p.2 ∈ sector N r := (Finset.mem_product.1 hp).2
  have hB : 1 ≤ overlapBound N q ^ r := one_le_pow₀ (one_le_overlapBound q)
  have h1 := fwdC_flatDatum_le hF hN hac q W p.1 ℓ r n hω v hv p.2 hζ
  have h2 : |avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2| ≤ overlapBound N q ^ r :=
    abs_avFlat_le (ramp_nonneg _ _ _) (ramp_le_one _ _ _) hB
      (abs_shortC_le hF hN hac q ℓ r n hω v hv p.2 hζ)
  have h3 : max (|fwdC F a c ℓ r n (flatDatum F a c q W p.1) v ω p.2 -
      avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2| - main) 0 ≤
      2 * overlapBound N q ^ r := by
    refine max_le ?_ (by linarith)
    have := abs_sub (fwdC F a c ℓ r n (flatDatum F a c q W p.1) v ω p.2)
      (avFlat (ramp W (p.1 : ℕ)) (shortC F a c q ℓ r n v ω) p.2)
    linarith
  by_cases hm : ω ∈ nearBulk F a c E κ ρ p.1
  · simp only [Set.indicator_of_mem hm]; exact h3
  · simp only [Set.indicator_of_notMem hm]; exact (le_max_right _ _).trans h3

theorem flatExcess_succ {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N) {a c : ℝ}
    (hac : a ≤ c) (q : Fin N → ℂ) (ℓ r n : ℕ) (E κ ρ W main : ℝ) {ω : FlowSample N}
    (hω : ω ∈ gapSet F a c n) {v : ℝ} (hv : v ∈ Icc a c) :
    flatExcess F a c q ℓ r (n + 1) E κ ρ W main v ω = flatExcess F a c q ℓ r n E κ ρ W main v ω := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have hζ : p.2 ∈ sector N r := (Finset.mem_product.1 hp).2
  by_cases hm : ω ∈ nearBulk F a c E κ ρ p.1
  · simp only [Set.indicator_of_mem hm]
    rw [fwdC_succ hF hN hac ℓ r n _ hω v hv p.2 hζ]
    have e : shortC F a c q ℓ r (n + 1) v ω = fun ζ =>
        if ζ ∈ sector N r then shortC F a c q ℓ r n v ω ζ else shortC F a c q ℓ r (n + 1) v ω ζ := by
      funext ζ; split_ifs with h
      · exact shortC_succ hF hN hac q ℓ r n hω v hv ζ h
      · rfl
    rw [e]; simp only [avFlat, hζ, ite_true]
  · simp only [Set.indicator_of_notMem hm]

end BlockBand.Palm.MomentFlow
