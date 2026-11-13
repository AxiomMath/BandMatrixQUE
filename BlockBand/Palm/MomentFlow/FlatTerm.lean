module

public import BlockBand.Palm.MomentFlow.FlatExcess

/-!
# One term of the flattening excess along one sample path

Pathwise and deterministic once its three inputs are given. These inputs are
the a priori local bound on the datum, the row tail (when `rampDist k₀ ζ ≤ 2W`), and the column
tails of the window configurations.

**`flat_term_bound`**:
`|fwdC(Av Φ(a))(v,ζ) - Av(shortC(v))(ζ)| ≤ (b+1)(2/W) rR + (B^r + 1) N^r x₁`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset
open BlockBand.Internal.Contracts.CoareaPalm

variable {N : ℕ}

theorem flat_term_bound {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) {ℓ r n : ℕ} {ω : FlowSample N}
    (hωG : ω ∈ gapSet F a c n) {W R : ℝ} (hW : 0 < W) (hR0 : 0 ≤ R) (hrRW : (r : ℝ) * R ≤ W)
    (k₀ : Fin N) {ζ : Occ N} (hζ : ζ ∈ sector N r) {v : ℝ} (hv : v ∈ Icc a c) {b x₁ : ℝ}
    (hb0 : 0 ≤ b) (hx₁ : 0 ≤ x₁)
    (hloc : (rampDist (k₀ : ℕ) ζ : ℝ) ≤ 2 * W → ∀ ζ' ∈ sector N r, ζ' ∈ occBall r R ζ →
      |canonDatum F a c q ω ζ'| ≤ b)
    (hrow : (rampDist (k₀ : ℕ) ζ : ℝ) ≤ 2 * W → ∃ w : ℝ → Occ N → ℝ,
      IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r a v w ∧
      (∀ ζ' ∈ sector N r, w v ζ' = deltaCfg ζ ζ') ∧
      ∑ ζ' ∈ sector N r \ occBall r R ζ, w a ζ' ≤ x₁)
    (hcol : ∀ η ∈ sector N r, (rampDist (k₀ : ℕ) η : ℝ) ≤ W → ∀ Φ : ℝ → Occ N → ℝ,
      IsMomentFlowSolution (shortFlowRate F a ω ℓ) r a v Φ →
      (∀ ζ' ∈ sector N r, Φ a ζ' = if ζ' = η then 1 else 0) →
      ∑ ζ' ∈ (sector N r).filter (fun ζ' => (r : ℝ) * R < (occDist η ζ' : ℝ)), Φ v ζ' ≤ x₁) :
    |fwdC F a c ℓ r n (flatDatum F a c q W k₀) v ω ζ -
        avFlat (ramp W (k₀ : ℕ)) (shortC F a c q ℓ r n v ω) ζ| ≤
      (b + 1) * (2 / W * ((r : ℝ) * R)) + (overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁) := by
  classical
  have hNr : (1 : ℝ) ≤ (N : ℝ) ^ r := one_le_pow₀ (by exact_mod_cast hN)
  have hOb1 : 1 ≤ overlapBound N q ^ r := one_le_pow₀ (one_le_overlapBound q)
  obtain ⟨hsH, h0H⟩ := shortC_isSolution hF hN hac q ℓ r n hωG
  obtain ⟨hsG, h0G⟩ := fwdC_isSolution hF hN hac ℓ r n (flatDatum F a c q W k₀) hωG
  have hG0 : ∀ ζ' ∈ sector N r, fwdC F a c ℓ r n (flatDatum F a c q W k₀) a ω ζ' =
      avFlat (ramp W (k₀ : ℕ)) (shortC F a c q ℓ r n a ω) ζ' := by
    intro ζ' hζ'; rw [h0G ζ' hζ']; simp only [flatDatum, avFlat, h0H ζ' hζ']
  have hf : ∀ ζ' ∈ sector N r, |shortC F a c q ℓ r n a ω ζ'| ≤ overlapBound N q ^ r :=
    fun ζ' hζ' => abs_shortC_le hF hN hac q ℓ r n hωG a ⟨le_rfl, hac⟩ ζ' hζ'
  have hmain0 : 0 ≤ (b + 1) * (2 / W * ((r : ℝ) * R)) := by positivity
  by_cases hA : (rampDist (k₀ : ℕ) ζ : ℝ) ≤ 2 * W
  · obtain ⟨w, hw, hwu, htail⟩ := hrow hA
    have hcomm := comm_inbulk hv.1 (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j)
      (fun x _ i j => shortFlowRate_symm F a ω ℓ x i j) hw hζ hwu (hsG.mono_right hv.2)
      (hsH.mono_right hv.2) hW (k₀ : ℕ) hG0 hR0 (M := overlapBound N q ^ r) (Mloc := b) hb0 hf
      (fun ζ' hζ' hζB _ => by rw [h0H ζ' hζ']; exact hloc hA ζ' hζ' hζB)
    have h2 : (overlapBound N q ^ r + 1) * ∑ ζ' ∈ sector N r \ occBall r R ζ, w a ζ' ≤
        (overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁) :=
      mul_le_mul_of_nonneg_left (htail.trans (le_mul_of_one_le_left hx₁ hNr)) (by linarith)
    linarith
  · have hA' : 2 * W < (rampDist (k₀ : ℕ) ζ : ℝ) := not_le.1 hA
    have hζ0 : ramp W (k₀ : ℕ) ζ = 0 := ramp_eq_zero hW (by linarith)
    set datD : Occ N → FlowSample N → Occ N → ℝ := fun η _ ζ' => if ζ' = η then 1 else 0
      with hdatD
    have hdD01 : ∀ η, ∀ ζ' ∈ sector N r, 0 ≤ datD η ω ζ' ∧ datD η ω ζ' ≤ 1 := by
      intro η ζ' _; simp only [hdatD]; split_ifs <;> norm_num
    have hnn : ∀ η, ∀ ζ' ∈ sector N r, 0 ≤ fwdC F a c ℓ r n (datD η) v ω ζ' := fun η ζ' hζ' =>
      (fwdC_bounds hF hN hac ℓ r n (datD η) hωG (fun ζ'' h => (hdD01 η ζ'' h).1)
        (fun ζ'' h => (hdD01 η ζ'' h).2) v hv ζ' hζ').1
    set S := (sector N r).filter fun η => (rampDist (k₀ : ℕ) η : ℝ) ≤ W with hSdef
    have hcomm := comm_far hv.1 (fun x _ i j _ => shortFlowRate_nonneg F a ω ℓ x i j)
      (hsG.mono_right hv.2) (H := fun σ => shortC F a c q ℓ r n σ ω) (k₀ : ℕ) hG0 hf S
      (Finset.filter_subset _ _) (fun ζ' hζ' hns => ramp_eq_zero hW (by
        have : ¬ ((rampDist (k₀ : ℕ) ζ' : ℝ) ≤ W) := fun h => hns (Finset.mem_filter.2 ⟨hζ', h⟩)
        linarith [not_le.1 this]))
      (Φ := fun η σ => fwdC F a c ℓ r n (datD η) σ ω)
      (fun η _ => (fwdC_isSolution hF hN hac ℓ r n (datD η) hωG).1.mono_right hv.2)
      (fun η _ ζ' hζ' => (fwdC_isSolution hF hN hac ℓ r n (datD η) hωG).2 ζ' hζ')
      hζ (fun η _ => hnn η ζ hζ) hζ0
    have hsum : ∑ η ∈ S, fwdC F a c ℓ r n (datD η) v ω ζ ≤ (N : ℝ) ^ r * x₁ := by
      calc ∑ η ∈ S, fwdC F a c ℓ r n (datD η) v ω ζ ≤ ∑ _η ∈ S, x₁ := by
            refine Finset.sum_le_sum fun η hη => ?_
            have hη' : η ∈ sector N r ∧ (rampDist (k₀ : ℕ) η : ℝ) ≤ W := Finset.mem_filter.1 hη
            obtain ⟨hsD, h0D⟩ := fwdC_isSolution hF hN hac ℓ r n (datD η) hωG
            have hfar : ζ ∈ (sector N r).filter (fun ζ' => (r : ℝ) * R < (occDist η ζ' : ℝ)) := by
              refine Finset.mem_filter.2 ⟨hζ, ?_⟩
              have h1 := rampDist_sub_le_occDist hη'.1 hζ (k₀ : ℕ)
              have h2 := neg_abs_le ((rampDist (k₀ : ℕ) η : ℝ) - rampDist (k₀ : ℕ) ζ)
              linarith [hη'.2]
            calc fwdC F a c ℓ r n (datD η) v ω ζ
                ≤ ∑ ζ' ∈ (sector N r).filter (fun ζ' => (r : ℝ) * R < (occDist η ζ' : ℝ)),
                    fwdC F a c ℓ r n (datD η) v ω ζ' :=
                  Finset.single_le_sum (fun ζ' h => hnn η ζ' (Finset.mem_filter.1 h).1) hfar
              _ ≤ x₁ := hcol η hη'.1 hη'.2 _ (hsD.mono_right hv.2) h0D
        _ = S.card * x₁ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (N : ℝ) ^ r * x₁ := by
            refine mul_le_mul_of_nonneg_right ?_ hx₁
            exact (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans
              (by exact_mod_cast card_sector_le (N := N) r)
    have h2 : (overlapBound N q ^ r + 1) * ∑ η ∈ S, fwdC F a c ℓ r n (datD η) v ω ζ ≤
        (overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁) :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    linarith

/-- **The excess at one deterministic time along one sample path**: off the row and column
events (supplied as `hrow`, `hcol` for bulk configurations), every term of `flatExcess` is
`≤ (B^r + 1) N^r x₁`. -/
theorem flatExcess_le_of_paths {F : Matrix (Fin N) (Fin N) ℂ} (hF : F.IsHermitian) (hN : 0 < N)
    {a c : ℝ} (hac : a ≤ c) (q : Fin N → ℂ) {ℓ r n : ℕ} {ω : FlowSample N}
    (hωG : ω ∈ gapSet F a c n) {E r₀ ρ W R b x₁ : ℝ} (hr₀ : 0 ≤ r₀) (hW : 0 < W) (hR0 : 0 ≤ R)
    (hrRW : (r : ℝ) * R ≤ W) (h2WR : 2 * W + r * R ≤ ρ) (hb0 : 0 ≤ b) (hx₁ : 0 ≤ x₁)
    {v : ℝ} (hv : v ∈ Icc a c) {Φ₀ : ℝ → Occ N → FlowSample N → ℝ}
    (h0 : ∀ ζ ∈ sector N r, Φ₀ a ζ ω = canonDatum F a c q ω ζ)
    (hml : ∀ ξ ∈ sector N r, ∀ σ ∈ Icc a c, 0 ≤ Φ₀ σ ξ ω ∧
      ((∀ k : Fin N, 0 < ξ k → ∀ σ' ∈ Icc a c, |flowEigenvalue F a ω σ' k - E| ≤ r₀ / 2) →
        Φ₀ σ ξ ω ≤ b))
    (hrow : ∀ ζ ∈ sector N r,
      (∀ v' ∈ Icc a v, ∀ k : Fin N, 0 < ζ k → |flowEigenvalue F a ω v' k - E| ≤ r₀ / 16) →
      ∃ w : ℝ → Occ N → ℝ, IsBackwardMomentFlow (shortFlowRate F a ω ℓ) r a v w ∧
        (∀ ζ' ∈ sector N r, w v ζ' = deltaCfg ζ ζ') ∧
        ∑ ζ' ∈ sector N r \ occBall r R ζ, w a ζ' ≤ x₁)
    (hcol : ∀ η ∈ sector N r,
      (∀ k : Fin N, 0 < η k → |flowEigenvalue F a ω a k - E| ≤ r₀ / 16) →
      ∀ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F a ω ℓ) r a v Φ →
      (∀ ζ' ∈ sector N r, Φ a ζ' = if ζ' = η then 1 else 0) →
      ∑ ζ' ∈ (sector N r).filter (fun ζ' => (r : ℝ) * R < (occDist η ζ' : ℝ)), Φ v ζ' ≤ x₁) :
    flatExcess F a c q ℓ r n E (r₀ / 16) ρ W ((b + 1) * (2 / W * ((r : ℝ) * R))) v ω ≤
      (((Finset.univ : Finset (Fin N)) ×ˢ sector N r).card : ℝ) *
        ((overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁)) := by
  have hr₀ : 0 ≤ (r : ℝ) * R := mul_nonneg (Nat.cast_nonneg r) hR0
  have hWρ : W ≤ ρ := by linarith
  have h2Wρ : 2 * W ≤ ρ := by linarith
  have hOb1 : (1 : ℝ) ≤ overlapBound N q ^ r := one_le_pow₀ (one_le_overlapBound q)
  have hOb : 0 ≤ (overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁) :=
    mul_nonneg (by linarith) (mul_nonneg (pow_nonneg (Nat.cast_nonneg N) r) hx₁)
  unfold flatExcess
  rw [← nsmul_eq_mul (((Finset.univ : Finset (Fin N)) ×ˢ sector N r).card)
    ((overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁))]
  refine Finset.sum_le_card_nsmul ((Finset.univ : Finset (Fin N)) ×ˢ sector N r) _
    ((overlapBound N q ^ r + 1) * ((N : ℝ) ^ r * x₁)) fun pp hpp => ?_
  have hζ : pp.2 ∈ sector N r := (Finset.mem_product.1 hpp).2
  by_cases hnb : ω ∈ nearBulk F a c E (r₀ / 16) ρ pp.1
  · simp only [Set.indicator_of_mem hnb]
    refine max_le (sub_le_iff_le_add'.2 (flat_term_bound hF hN hac q (ℓ := ℓ) hωG hW hR0 hrRW
      pp.1 hζ hv hb0 hx₁ (fun hA ζ' hζ' hζB => ?_) (fun hA => ?_)
      (fun η hη hηW Φ hΦ hΦ0 => ?_))) hOb
    · rw [← h0 ζ' hζ']
      have hrd : (rampDist (pp.1 : ℕ) ζ' : ℝ) ≤ ρ :=
        (rampDist_le_of_mem_occBall hζ hζB _).trans (by linarith)
      obtain ⟨hpos, hbd⟩ := hml ζ' hζ' a ⟨le_rfl, hac⟩
      rw [abs_of_nonneg hpos]
      exact hbd fun k hk σ' hσ' => (bulk_of_nearBulk hnb hrd k hk σ' hσ').trans (by linarith)
    · exact hrow pp.2 hζ fun v' hv' k hk =>
        bulk_of_nearBulk hnb (hA.trans h2Wρ) k hk v' ⟨hv'.1, hv'.2.trans hv.2⟩
    · exact hcol η hη (fun k hk => bulk_of_nearBulk hnb (hηW.trans hWρ) k hk a ⟨le_rfl, hac⟩)
        Φ hΦ hΦ0
  · simp only [Set.indicator_of_notMem hnb]; exact hOb

end BlockBand.Palm.MomentFlow
