module

public import BlockBand.Palm.MomentFlow.FlatTerm
public import BlockBand.Palm.MomentFlow.FlatClauses
public import BlockBand.Palm.MomentFlow.PropP6Holds

/-!
# `Flattening` holds, given row and column finite speed

The hypotheses are `MultiShortFiniteSpeed` and `MultiShortColumnSpeed`.

Clauses.
1. Rough bound: `mloc_uniform` at time `a` on the window, which lies in the bulk by `nearBulk`.
2. Energies: `energy_near_target`, followed by `eventually_energy_le`.
3. Commutator. Use canonical flows `G = fwdC(Av Φ(a))` and `H = shortC`, together with the excess
   `flatExcess` and `excess_core`. At each deterministic time and pair `(k₀, ζ)` there are two cases.
   If `rampDist k₀ ζ ≤ 2W`, apply `comm_inbulk` with the row tail of `tail6_multi` at radius
   `N^ε ℓ`, and `M_loc` on the `occDist` ball. Otherwise `ramp(ζ) = 0`, and `comm_far` applies with
   the column events of `MultiShortColumnSpeed`. The main term
   `(b+1)(2/W) r N^ε ℓ ≤ N^{(4r+2)ε} ℓ/w`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Palm.MomentFlow

open Set Finset MeasureTheory Filter
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Inputs
open BlockBand.Internal.Contracts.Transmission BlockBand.Palm.CoarseRelative

/-- `2C√τ + 2max(ℓ/N, (4K_w w + 1)/(c₁N)) ≤ (3 + 10K_w/c₁) w/N` for large `N`. -/
theorem eventually_energy_le (Ce : ℝ) {ce Kw : ℝ} (hce : 0 < ce) (hKw : 0 < Kw) :
    ∀ᶠ n : ℕ in atTop, 2 * (Ce * Real.sqrt (cmTau n)) +
        2 * max ((cmEll n : ℝ) / n) ((4 * (Kw * cmW n) + 1) / (ce * n)) ≤
      (3 + 10 * Kw / ce) * cmW n / n := by
  filter_upwards [eventually_const_mul_rpow_neg_le (2 * Ce) (by norm_num : (0 : ℝ) < 1 / 300)
      (by norm_num : (0 : ℝ) < 1),
    eventually_const_le_rpow (1 / Kw) (by norm_num : (0 : ℝ) < 1 - (1 / 100 : ℝ) / 6),
    eventually_ge_atTop 1] with n h1 h2 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set w := cmW n with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hn0 _
  have ewn : w / n = (n : ℝ) ^ (-(1 / 600 : ℝ)) := by
    rw [hw, cmW, div_eq_iff hn0.ne', ← Real.rpow_add_one hn0.ne']; norm_num
  have hsq : Real.sqrt (cmTau n) = (n : ℝ) ^ (-(1 / 300 : ℝ)) * (n : ℝ) ^ (-(1 / 600 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, cmTau, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]; norm_num
  have e1 : 2 * (Ce * Real.sqrt (cmTau n)) ≤ w / n := by
    rw [hsq, ewn]
    have hp : 0 < (n : ℝ) ^ (-(1 / 600 : ℝ)) := Real.rpow_pos_of_pos hn0 _
    nlinarith
  have e2 : (cmEll n : ℝ) / n ≤ w / n := by
    refine div_le_div_of_nonneg_right ((cmEll_le_rpow n).trans ?_) hn0.le
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hKww : 1 ≤ Kw * w := by
    have : 1 / Kw ≤ w := h2
    rw [div_le_iff₀ hKw] at this; linarith
  have e3 : (4 * (Kw * w) + 1) / (ce * n) ≤ 5 * Kw * w / (ce * n) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hA : 0 ≤ (cmEll n : ℝ) / n := by positivity
  have hB : 0 ≤ (4 * (Kw * w) + 1) / (ce * n) := by positivity
  have hmax : max ((cmEll n : ℝ) / n) ((4 * (Kw * w) + 1) / (ce * n)) ≤
      w / n + 5 * Kw * w / (ce * n) := by
    have : 0 ≤ 5 * Kw * w / (ce * n) := by positivity
    have : 0 ≤ w / n := by positivity
    exact max_le (by linarith) (by linarith)
  have e4 : (3 + 10 * Kw / ce) * w / n = 3 * (w / n) + 2 * (5 * Kw * w / (ce * n)) := by
    field_simp; ring
  rw [e4]; linarith

theorem flattening_holds (hMS : MultiShortFiniteSpeed) (hCol : MultiShortColumnSpeed)
    (hELG : ExternalLocalGUE) (hMDE : MDEBranchIdentification) (hLp : GaussianLpGradient)
    (hIBP : MultivariateGaussianIBP) (hDBM : ∀ N : ℕ, DysonBrownianMotion N) :
    Flattening := by
  classical
  intro A c₀ r₀ s₀ v₀ hK r hr M Kw hKw
  have hr₀ : 0 < r₀ := hK.2.2.1
  obtain ⟨ce, Ce, hce, -, hEn⟩ := energy_near_target hLp hIBP (A := A) hK Kw
  set C₂ : ℝ := 1 + (3 + 10 * Kw / ce) / Kw with hC₂
  have hC₂1 : 1 ≤ C₂ := by
    have : 0 ≤ (3 + 10 * Kw / ce) / Kw := by positivity
    linarith
  refine ⟨4 * r + 2, C₂, fun ε hε hε1 D => ?_⟩
  obtain ⟨Cst', hCst', hMl⟩ := mloc_uniform hELG hMDE hLp hDBM (A := A) hK hε (by linarith)
  obtain ⟨c', hc', hColD⟩ := hCol A c₀ r₀ s₀ v₀ hK r hr ε hε
  set Cq : ℝ := max 1 (1 / (v₀ * lowConst c₀ s₀ v₀)) with hCq
  set Dq : ℝ := max D 1 + 1 with hDq
  set Qo : ℝ := r * (1 + 2 * max A 1) + 1 with hQo
  set Q : ℝ := 2 * r + Qo + 1 with hQ
  set D₁ : ℝ := 2 * Dq + Q + r + 5 with hD₁
  set D' : ℝ := max D₁ (Qo + 3) with hD'
  set K₀ : ℝ := max 1 Cst' ^ r + 2 with hK₀
  obtain ⟨N₁, hN₁⟩ := hMl r D'
  obtain ⟨N₂, hN₂⟩ := hColD D₁
  obtain ⟨N₃, hN₃⟩ := tail6_multi hMS hDBM (A := A) hK hr hε D₁
  obtain ⟨N₄, hN₄⟩ := hEn D₁
  obtain ⟨N₅, hN₅⟩ := bulk_near_target hLp hIBP (A := A) hK (κ' := 1 / 1200) (by norm_num) D₁
  have hτ0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 100 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    ((hnat.eventually_ge_atTop 4).and ((hτ0.eventually (gt_mem_nhds hK.1)).and
      ((eventually_window_le (2 * Kw) r).and ((eventually_center_le M hr₀).and
      ((eventually_R_le_window hKw r).and
      ((eventually_exp_le_rpow hc' hε D₁).and
      ((eventually_const_le_rpow K₀ hε).and
      ((eventually_const_le_rpow (2 * r / Kw * K₀) hε).and
      ((hnat.eventually_ge_atTop (Cq ^ r)).and
      ((eventually_energy_le Ce hce hKw).and
      ((eventually_ge_atTop N₁).and ((eventually_ge_atTop N₂).and ((eventually_ge_atTop N₃).and
      ((eventually_ge_atTop N₄).and (eventually_ge_atTop N₅)))))))))))))))
  refine ⟨N₀, fun N hN F E hC q hq => ?_⟩
  obtain ⟨hN4, hτc, hwin, hcen, hRW, hexp, hK₀N, hK₀N', hCqN, hEnN, hn1, hn2, hn3, hn4, hn5⟩ :=
    hN₀ N hN
  have hF := hC.1
  have hNr : (0 : ℝ) < N := by linarith
  have hNpos : 0 < N := by exact_mod_cast hNr
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hτpos : 0 < cmTau N := Real.rpow_pos_of_pos hNr _
  have ha : 0 < c₀ - cmTau N := by unfold cmTau; linarith
  have hac : c₀ - cmTau N ≤ c₀ := by linarith
  have hτ1 : cmTau N ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  have hεN : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (1 / 1000 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hε1.le
  obtain ⟨Bml, hBmlm, hBmlμ, hBml⟩ := hN₁ N hn1 F E hC q hq
  obtain ⟨Ben, hBenm, hBenμ, hBen⟩ := hN₄ N hn4 F E hC
  obtain ⟨Bbk, hBbkm, hBbkμ, hBbk⟩ := hN₅ N hn5 F E hC
  have htl := hN₃ N hn3 F E hC
  by_cases hex : ∃ Φ₀ : ℝ → Occ N → FlowSample N → ℝ, RegVersion F (c₀ - cmTau N) c₀ q r Φ₀
  swap
  · exact ⟨∅, @MeasurableSet.empty _ (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀),
      by simp, fun Φ hΦ => absurd ⟨Φ, hΦ⟩ hex⟩
  obtain ⟨Φ₀, hΦ₀⟩ := hex
  -- scales and constants
  set W : ℝ := Kw * cmW N with hWdef
  have hW : 0 < W := mul_pos hKw (Real.rpow_pos_of_pos hNr _)
  set ρ : ℝ := (N : ℝ) ^ (1 - (1 / 1200 : ℝ)) with hρdef
  set R : ℝ := (N : ℝ) ^ ε * cmEll N with hRdef
  have hR0 : 0 ≤ R := by positivity
  have hRR : (r : ℝ) * R ≤ (r : ℝ) * ((N : ℝ) ^ (1 / 1000 : ℝ) * cmEll N) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hεN (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  have h2WR : 2 * W + r * R ≤ ρ := by
    have := hwin; simp only [hWdef] at this ⊢; nlinarith
  have hrRW : (r : ℝ) * R ≤ W := hRR.trans hRW
  have hrR0 : 0 ≤ (r : ℝ) * R := by positivity
  have h2Wρ : 2 * W ≤ ρ := by linarith
  have hWρ : W ≤ ρ := by have : 0 ≤ (r : ℝ) * R := by positivity
                         linarith
  set Ob : ℝ := overlapBound N q with hOb
  have hObpoly : Ob ^ r ≤ (N : ℝ) ^ Qo :=
    pow_le_poly hN1 (by linarith [one_le_overlapBound q]) (overlapBound_le_poly hNpos hK hC hq)
      hCqN
  have hOb1 : 1 ≤ Ob ^ r := one_le_pow₀ (one_le_overlapBound q)
  set j₂ : ℝ := Ob ^ r * (N : ℝ) ^ (-D') with hj₂def
  have hj₂ : j₂ ≤ 1 := (junk_le hN1 (c₂ := 1) one_pos hObpoly (le_max_right _ _)
    (by norm_num; linarith)).2
  have hj₂0 : 0 ≤ j₂ := mul_nonneg (by linarith) (Real.rpow_pos_of_pos hNr _).le
  set b : ℝ := (Cst' * (N : ℝ) ^ (4 * ε)) ^ r + j₂ with hbdef
  have hb0 : 0 ≤ b := by positivity
  have hbK : b + 1 ≤ K₀ * (N : ℝ) ^ (4 * r * ε) := mlocB_le hN1 hε.le hCst' hj₂
  set main : ℝ := (b + 1) * (2 / W * ((r : ℝ) * R)) with hmaindef
  have hmain0 : 0 ≤ main := by positivity
  set x₁ : ℝ := (N : ℝ) ^ (-D₁) with hx₁def
  have hx₁0 : 0 ≤ x₁ := (Real.rpow_pos_of_pos hNr _).le
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) ^ r := one_le_pow₀ hN1
  set δ₀ : ℝ := (Ob ^ r + 1) * ((N : ℝ) ^ r * x₁) with hδ₀def
  have hδ₀0 : 0 ≤ δ₀ := mul_nonneg (by linarith) (mul_nonneg (by linarith) hx₁0)
  set pairs : Finset (Fin N × Occ N) := (Finset.univ : Finset (Fin N)) ×ˢ sector N r
    with hpairs
  have hcard0 : (0 : ℝ) ≤ pairs.card := Nat.cast_nonneg _
  set δ : ℝ := (pairs.card : ℝ) * δ₀ with hδdef
  set p : ℝ := (3 + (sector N r).card + ((sector N r).card : ℝ)) * x₁ with hpdef
  set Kb : ℝ := (pairs.card : ℝ) * (2 * Ob ^ r) with hKbdef
  have hδ0 : 0 ≤ δ := mul_nonneg hcard0 hδ₀0
  have hp0 : 0 ≤ p := mul_nonneg (add_nonneg (add_nonneg (by norm_num) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)) hx₁0
  have hKb0 : 0 ≤ Kb := mul_nonneg hcard0 (by linarith)
  set Y : ℕ → ℝ → FlowSample N → ℝ := fun n v ω =>
    flatExcess F (c₀ - cmTau N) c₀ q (cmEll N) r n E (r₀ / 16) ρ W main v ω with hYdef
  set datD : Occ N → FlowSample N → Occ N → ℝ := fun η _ ζ => if ζ = η then 1 else 0
    with hdatD
  -- the row tails and the column events
  have htl' : ∀ v : ℝ, ∀ ζ : Occ N, ∃ B : Set (FlowSample N),
      MeasurableSet[pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀] B ∧
      flowLaw N (c₀ - cmTau N) B ≤ ENNReal.ofReal x₁ ∧
      (v ∈ Icc (c₀ - cmTau N) c₀ → ζ ∈ sector N r →
        ∀ᵐ ω ∂flowLaw N (c₀ - cmTau N), ω ∉ B →
          (∀ v' ∈ Icc (c₀ - cmTau N) v, ∀ k : Fin N, 0 < ζ k →
            |flowEigenvalue F (c₀ - cmTau N) ω v' k - E| ≤ r₀ / 16) →
          ∃ w : ℝ → Occ N → ℝ,
            IsBackwardMomentFlow (shortFlowRate F (c₀ - cmTau N) ω (cmEll N)) r (c₀ - cmTau N) v w ∧
            (∀ ζ' ∈ sector N r, w v ζ' = deltaCfg ζ ζ') ∧
            ∑ ζ' ∈ sector N r \ occBall r R ζ, w (c₀ - cmTau N) ζ' ≤ x₁) := by
    intro v ζ
    by_cases hv : v ∈ Icc (c₀ - cmTau N) c₀ ∧ ζ ∈ sector N r
    · obtain ⟨B, hB1, hB2, hB3⟩ := htl (c₀ - cmTau N) v le_rfl hv.1.1 hv.1.2 ζ hv.2
      refine ⟨B, hB1, hB2, fun _ _ => ?_⟩
      filter_upwards [hB3] with ω hω hωB hbk
      obtain ⟨w, hw, hwu, -, hterm⟩ := hω hωB hbk
      exact ⟨w, hw, hwu, hterm⟩
    · exact ⟨∅, @MeasurableSet.empty _ (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀),
        by simp, fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
  choose Btl hBtlm hBtlμ hBtl using htl'
  set Scol : ℝ → Occ N → Set (FlowSample N) := fun v η => {ω |
    (∀ k : Fin N, 0 < η k → |flowEigenvalue F (c₀ - cmTau N) ω (c₀ - cmTau N) k - E| ≤ r₀ / 16) ∧
    ∃ Φ : ℝ → Occ N → ℝ, IsMomentFlowSolution (shortFlowRate F (c₀ - cmTau N) ω (cmEll N)) r
        (c₀ - cmTau N) v Φ ∧
      (∀ ζ ∈ sector N r, Φ (c₀ - cmTau N) ζ = if ζ = η then 1 else 0) ∧
      Real.exp (-(c' * (N : ℝ) ^ ε)) <
        ∑ ζ ∈ (sector N r).filter (fun ζ => (r : ℝ) * R < (occDist η ζ : ℝ)), Φ v ζ}
    with hScol
  have hScolμ : ∀ v ∈ Icc (c₀ - cmTau N) c₀, ∀ η ∈ sector N r,
      flowLaw N (c₀ - cmTau N) (Scol v η) ≤ ENNReal.ofReal x₁ := fun v hv η hη =>
    hN₂ N hn2 F E hC (c₀ - cmTau N) v le_rfl hv.1 hv.2 η hη
  have hD'1 : ENNReal.ofReal ((N : ℝ) ^ (-D')) ≤ ENNReal.ofReal x₁ :=
    ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (neg_le_neg (le_max_left _ _)))
  -- per-time bound
  have hbad : ∀ n : ℕ, ∀ v ∈ Icc (c₀ - cmTau N) c₀,
      flowLaw N (c₀ - cmTau N) {ω | ω ∈ gapSet F (c₀ - cmTau N) c₀ n ∧ δ < Y n v ω} ≤
        ENNReal.ofReal p := by
    intro n v hv
    set U : Set (FlowSample N) := Bml ∪ (⋃ ζ ∈ sector N r, Btl v ζ) ∪
      ⋃ η ∈ sector N r, Scol v η with hUdef
    have hs1 : ∑ _ζ ∈ sector N r, ENNReal.ofReal x₁ =
        ENNReal.ofReal ((sector N r).card * x₁) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    have hs2 : ∑ _η ∈ sector N r, ENNReal.ofReal x₁ =
        ENNReal.ofReal ((sector N r).card * x₁) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    have hU : flowLaw N (c₀ - cmTau N) U ≤ ENNReal.ofReal p := by
      calc flowLaw N (c₀ - cmTau N) U
          ≤ flowLaw N (c₀ - cmTau N) Bml +
              ∑ ζ ∈ sector N r, flowLaw N (c₀ - cmTau N) (Btl v ζ) +
              ∑ η ∈ sector N r, flowLaw N (c₀ - cmTau N) (Scol v η) := by
            refine (measure_union_le _ _).trans (add_le_add ?_ (measure_biUnion_finset_le _ _))
            exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
        _ ≤ ENNReal.ofReal x₁ + ∑ _ζ ∈ sector N r, ENNReal.ofReal x₁ +
              ∑ _η ∈ sector N r, ENNReal.ofReal x₁ := by
            gcongr with ζ hζ η hη
            · exact hBmlμ.trans hD'1
            · exact hBtlμ v ζ
            · exact hScolμ v hv η hη
        _ ≤ ENNReal.ofReal p := by
            rw [hs1, ← ENNReal.ofReal_add hx₁0 (mul_nonneg (Nat.cast_nonneg _) hx₁0),
              ← ENNReal.ofReal_add (add_nonneg hx₁0 (mul_nonneg (Nat.cast_nonneg _) hx₁0))
                (mul_nonneg (Nat.cast_nonneg _) hx₁0)]
            refine ENNReal.ofReal_le_ofReal ?_
            have e : p = x₁ + (sector N r).card * x₁ + (sector N r).card * x₁ + 2 * x₁ := by
              rw [hpdef]; ring
            rw [e]; linarith
    refine le_trans (measure_mono_ae ?_) hU
    filter_upwards [hBml Φ₀ hΦ₀, regVersion_start (hDBM N) hF ha hac hΦ₀,
      (eventually_all_finset (sector N r)).2 fun ζ hζ => hBtl v ζ hv hζ] with ω hml h0 htlω
    intro hω
    obtain ⟨hωG, hδY⟩ := hω
    by_contra hωU
    have hωml : ω ∉ Bml := fun h => hωU (Or.inl (Or.inl h))
    have hωtl : ∀ ζ ∈ sector N r, ω ∉ Btl v ζ := fun ζ hζ h =>
      hωU (Or.inl (Or.inr (mem_iUnion₂.2 ⟨ζ, hζ, h⟩)))
    have hωS : ∀ η ∈ sector N r, ω ∉ Scol v η := fun η hη h =>
      hωU (Or.inr (mem_iUnion₂.2 ⟨η, hη, h⟩))
    have hYle : Y n v ω ≤ δ := flatExcess_le_of_paths hF hNpos hac q (ℓ := cmEll N) hωG
      hr₀.le hW hR0 hrRW h2WR hb0 hx₁0 hv h0 (hml hωml)
      (fun ζ hζ hbk => htlω ζ hζ (hωtl ζ hζ) hbk)
      (fun η hη hbk Φ hΦ hΦ0 => by
        by_contra hlt
        exact hωS η hη ⟨hbk, Φ, hΦ, hΦ0, lt_of_le_of_lt hexp (not_le.1 hlt)⟩)
    linarith
  -- one bad set for the excess
  have ht : 0 < (N : ℝ) ^ (-Dq) := Real.rpow_pos_of_pos hNr _
  obtain ⟨Bc, hBcm, hBcμ, hBc⟩ := excess_core (pathSigma F (c₀ - cmTau N) (c₀ - cmTau N) c₀)
    (pathSigma_le F (c₀ - cmTau N) (c₀ - cmTau N) c₀) (flowLaw N (c₀ - cmTau N)) hac
    (gapSet F (c₀ - cmTau N) c₀) (measurableSet_gapSet hF _ c₀) (gapSet_mono F _ c₀) Y
    (fun n v _ => measurable_flatExcess hF hNpos hac q (cmEll N) r n E (r₀ / 16) ρ W main v)
    (fun n ω => (continuous_flatExcess hF hNpos _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W main
      ω).continuousOn)
    (fun n ω _ v _ => flatExcess_nonneg F _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W main v ω)
    (fun n ω hω v hv => flatExcess_le hF hNpos hac q (cmEll N) r n E (r₀ / 16) ρ W hmain0 hω hv)
    (K := Kb) hKb0 hδ0 hp0 ht
    (fun n ω hω v hv => flatExcess_succ hF hNpos hac q (cmEll N) r n E (r₀ / 16) ρ W main hω hv)
    hbad
  -- arithmetic
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hQo0 : 0 ≤ Qo := by
    have : 0 ≤ max A 1 := le_trans zero_le_one (le_max_right _ _)
    rw [hQo]; positivity
  have hrp : ∀ k : ℕ, (N : ℝ) ^ k = (N : ℝ) ^ (k : ℝ) := fun k => (Real.rpow_natCast _ k).symm
  have hcp : (pairs.card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) + 1) := by
    have h1 : pairs.card = N * (sector N r).card := by
      rw [hpairs, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    have h2 : (pairs.card : ℝ) ≤ (N : ℝ) ^ (r + 1) := by
      rw [h1, pow_succ]; push_cast
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_sector_le (N := N) r)
        (Nat.cast_nonneg N)
    rw [hrp] at h2; exact_mod_cast h2
  have hcs : ((sector N r).card : ℝ) ≤ (N : ℝ) ^ ((r : ℝ) + 1) := by
    have h1 : ((sector N r).card : ℝ) ≤ (N : ℝ) ^ (r + 1) :=
      (by exact_mod_cast card_sector_le (N := N) r : ((sector N r).card : ℝ) ≤ (N : ℝ) ^ r).trans
        (pow_le_pow_right₀ hN1 (Nat.le_succ r))
    rw [hrp] at h1; exact_mod_cast h1
  have hyr : (N : ℝ) ^ r ≤ (N : ℝ) ^ (r : ℝ) := le_of_eq (hrp r)
  obtain ⟨hfin, hδD, hDD⟩ := flat_arith (τ' := c₀ - (c₀ - cmTau N)) (D := D) hN4 hOb1 hObpoly hr1
    (pow_nonneg hNr.le r) hyr (Nat.cast_nonneg _) hcp (Nat.cast_nonneg _) hcs (Nat.cast_nonneg _)
    hcs hQ hQo0 hD₁ (by have := le_max_right D 1; linarith)
    (by have := le_max_left D 1; linarith) (by linarith)
  refine ⟨Bc ∪ Bbk ∪ Bml ∪ Ben, ((hBcm.union hBbkm).union hBmlm).union hBenm, ?_, ?_⟩
  · have hst : 0 ≤ (c₀ - (c₀ - cmTau N)) * (δ + Kb * p) / (N : ℝ) ^ (-Dq) + p :=
      add_nonneg (div_nonneg (mul_nonneg (by linarith) (add_nonneg hδ0 (mul_nonneg hKb0 hp0)))
        ht.le) hp0
    calc flowLaw N (c₀ - cmTau N) (Bc ∪ Bbk ∪ Bml ∪ Ben)
        ≤ flowLaw N (c₀ - cmTau N) Bc + flowLaw N (c₀ - cmTau N) Bbk +
            flowLaw N (c₀ - cmTau N) Bml + flowLaw N (c₀ - cmTau N) Ben := by
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
          exact measure_union_le _ _
      _ ≤ ENNReal.ofReal ((c₀ - (c₀ - cmTau N)) * (δ + Kb * p) / (N : ℝ) ^ (-Dq) + p) +
            ENNReal.ofReal x₁ + ENNReal.ofReal x₁ + ENNReal.ofReal x₁ :=
          add_le_add (add_le_add (add_le_add hBcμ hBbkμ) (hBmlμ.trans hD'1)) hBenμ
      _ = ENNReal.ofReal ((c₀ - (c₀ - cmTau N)) * (δ + Kb * p) / (N : ℝ) ^ (-Dq) + p + x₁ +
            x₁ + x₁) := by
          rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hst hx₁0) hx₁0) hx₁0,
            ENNReal.ofReal_add (add_nonneg hst hx₁0) hx₁0, ENNReal.ofReal_add hst hx₁0]
      _ ≤ ENNReal.ofReal ((N : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal hfin
  · intro Φ hΦ
    filter_upwards [regVersion_eq_fullC (hDBM N) hF hNpos ha hac hΦ,
      ae_exists_gapSet (hDBM N) hF ha hac, hBml Φ hΦ] with ω hreg hgap hml hωB
    obtain ⟨n, hn⟩ := hgap
    obtain ⟨h0, -, -⟩ := hreg
    have hωc : ω ∉ Bc := fun h => hωB (Or.inl (Or.inl (Or.inl h)))
    have hωb : ω ∉ Bbk := fun h => hωB (Or.inl (Or.inl (Or.inr h)))
    have hωm : ω ∉ Bml := fun h => hωB (Or.inl (Or.inr h))
    have hωe : ω ∉ Ben := fun h => hωB (Or.inr h)
    obtain ⟨hint, hend⟩ := hBc ω hωc n hn
    refine ⟨fun u => Y n u ω, ⟨fun u _ => flatExcess_nonneg F _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W
      main u ω, (continuous_flatExcess hF hNpos _ c₀ q (cmEll N) r n E (r₀ / 16) ρ W main
      ω).intervalIntegrable _ _, hint.trans hDD, hend.trans hδD⟩, ?_⟩
    obtain ⟨hmain, hbN⟩ := flat_main_le (r := r) (ℓ := (cmEll N : ℝ)) hN1 hε hbK hK₀N hK₀N' hKw
      (Real.rpow_pos_of_pos hNr _) (Nat.cast_nonneg _) hC₂1
    exact flat_clauses hF hNpos hac q hn hr₀ hKw hce hWρ (main := main) h0 (hml hωm)
      (fun σ₀ hσ₀ k₀ hk₀ v hv k hk =>
        hBbk ω hωb k₀ k σ₀ hσ₀ (hk₀.trans hcen) (nearCfg_pos.1 hk) v hv)
      (fun σ₀ hσ₀ k₀ k hk₀ hd v hv =>
        (hBen ω hωe k₀ k σ₀ hσ₀ (hk₀.trans hcen) hd v hv).trans hEnN)
      hbN (show main ≤ _ from hmain) hC₂

end BlockBand.Palm.MomentFlow
