module

public import BlockBand.SourceProcess.PhysApprox.B3ModulMain
public import BlockBand.SourceProcess.PhysApprox.B3StopTailMain

/-!
# The closed complex modulus from time `s` on

`modulusS`: from `ComplexClosedSummed` and `ComplexClosedLindeberg`, the closed modulus of
continuity holds on `[t₁, T]` for every `s ≤ t₁ ≤ T`, including `t₁ = s`: on the cap event, the
births-removed coordinate `X_c - J_c` moves by more than `η` within `δ` with probability at most
`θ`, eventually in `W`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.Modul

open MeasureTheory ProbabilityTheory Filter Topology Matrix Finset
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.ComplexSourceLaw
open BlockBand.SourceProcess.Closing BlockBand.SourceProcess.Stochastic
open BlockBand.SourceProcess.ClosedLimit BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.ClosedSum BlockBand.Transmission.Bridge
open BlockBand.SourceProcess.ClosingAux
open ClosedSumProof (l1 swapE reMul)
open scoped ENNReal ComplexConjugate

variable {W np K : ℕ}

/-- **The closed modulus on `[t₁, T]` for `s ≤ t₁ ≤ T`** (`targetModulus_holds` with `t₁ = s`
allowed): the births-removed coordinate `X_c - J_c` moves by more than `η` within `δ` with
probability at most `θ` on the cap event, eventually in `W`. -/
theorem modulusS (hS : ComplexClosedSummed) (hL : ComplexClosedLindeberg)
    {b E : ℝ} {τ m : Fin np → ℝ} {T s h : ℝ}
    {Vs : (W : ℕ) → GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
    (hD : FrameDomain b E τ m T s h K Vs) (c : CIdx K np) {t₁ : ℝ} (ht₁ : s ≤ t₁)
    (ht₁T : t₁ ≤ T) {η θ : ℝ} (hη : 0 < η) (hθ : 0 < θ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      closedLaw b W np {y | y.1.1 ∈ physCapEventC b E s h K W ∧
        ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧ η <
          ‖b3X b E s h τ m W ⌊(W : ℝ) * t⌋₊ (Vs W) c y -
            cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t⌋₊) (b3KJumpAt E s τ m W ⌊(W : ℝ) * t⌋₊) -
            (b3X b E s h τ m W ⌊(W : ℝ) * t'⌋₊ (Vs W) c y -
              cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t'⌋₊)
                (b3KJumpAt E s τ m W ⌊(W : ℝ) * t'⌋₊))‖} ≤ ENNReal.ofReal θ := by
  have hF : ComplexClosedFourth := complexClosedFourth_iff_lindeberg.2 hL
  have hT : ComplexClosedStopTail := StopTail.complexClosedStopTail_of hS hL
  obtain ⟨hdom, hs0, -, -, -, hVs⟩ := id hD
  obtain ⟨hb0, hb, hE1, hE2, -, -, -, -⟩ := hdom
  have hb1 : b < 1 := by linarith
  have hfl : ∀ W : ℕ, closeLen s W ≤ ⌊(W : ℝ) * t₁⌋₊ ∧ ⌊(W : ℝ) * t₁⌋₊ ≤ ⌊(W : ℝ) * T⌋₊ :=
    fun W => ⟨Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁ (Nat.cast_nonneg _)),
      Nat.floor_mono (mul_le_mul_of_nonneg_left ht₁T (Nat.cast_nonneg _))⟩
  have ht0 : 0 ≤ t₁ := hs0.le.trans ht₁
  have hT0 : 0 < T := hs0.trans_le (ht₁.trans ht₁T)
  obtain ⟨R, hR⟩ := hT b E np τ m T s h K Vs hD (θ / 4) (by positivity)
  set Cb := driftCC b E K np R
  set Cc := covCC b E K np R
  have hCb0 : 0 ≤ Cb := driftCC_nonneg b E K np R
  have hCc0 : 0 ≤ Cc := covCC_nonneg b E K np R
  set lam := η / 16
  have hlam : 0 < lam := by positivity
  set δ := min (1 / 2) (min (η / (16 * (Cb + 1))) (θ * lam ^ 4 / (1024 * (Cc ^ 2 + 1) * (T + 1))))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ2 : δ ≤ 1 / 2 := min_le_left _ _
  have hδb : δ ≤ η / (16 * (Cb + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδc : δ ≤ θ * lam ^ 4 / (1024 * (Cc ^ 2 + 1) * (T + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  set A := (64 + 8 * lam ^ 2) / lam ^ 4 + 1 / lam + 1 / lam
  have hA0 : 0 ≤ A := by positivity
  set ε₀ := min 1 (θ / (8 * (A + 1)))
  have hε₀ : 0 < ε₀ := lt_min one_pos (by positivity)
  have hε₁ : ε₀ ≤ 1 := min_le_left _ _
  have hε₀A : ε₀ * A ≤ θ / 8 := by
    have h1 : ε₀ ≤ θ / (8 * (A + 1)) := min_le_right _ _
    have h2 : θ / (8 * (A + 1)) * A ≤ θ / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    exact (mul_le_mul_of_nonneg_right h1 hA0).trans h2
  have hSW := (ENNReal.tendsto_nhds_zero.mp ((hS b E np τ m T s h K Vs hD R).1 c c)) _
    (ENNReal.ofReal_pos.mpr hε₀)
  have hBW := (ENNReal.tendsto_nhds_zero.mp (tendsto_brErr hS hD R c)) _
    (ENNReal.ofReal_pos.mpr hε₀)
  have hFW := (ENNReal.tendsto_nhds_zero.mp (hF b E np τ m T s h K Vs hD R c)) _
    (ENNReal.ofReal_pos.mpr hε₀)
  have hWδ : ∀ᶠ W : ℕ in atTop, (1 : ℝ) ≤ W * δ := by
    filter_upwards [eventually_ge_atTop ⌈1 / δ⌉₊] with W hW
    have : (1 / δ : ℝ) ≤ W := (Nat.le_ceil _).trans (by exact_mod_cast hW)
    rwa [div_le_iff₀ hδ] at this
  obtain ⟨W₀, hW₀⟩ := eventually_atTop.mp
    (hVs.and (hR.and (hSW.and (hBW.and (hFW.and hWδ)))))
  refine ⟨δ, hδ, W₀, fun W hW => ?_⟩
  obtain ⟨hV, hRW, hSW', hBW', hFW', hWδ'⟩ := hW₀ W hW
  have hW0 : (0 : ℝ) < W := by
    by_contra hc
    have h0 : (W : ℝ) = 0 := le_antisymm (not_lt.mp hc) (Nat.cast_nonneg _)
    rw [h0, zero_mul] at hWδ'
    linarith
  have hVm : Measurable (Vs W) :=
    hV.1.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  set j₁ := ⌊(W : ℝ) * t₁⌋₊
  set L := ⌊(W : ℝ) * T⌋₊ - j₁
  set ℓ := ⌊(W : ℝ) * δ⌋₊ + 1
  set N := L / ℓ + 1
  have hℓ : 0 < ℓ := Nat.succ_pos _
  have hdm := Nat.div_add_mod L ℓ
  have hml := Nat.mod_lt L hℓ
  have hNL : L ≤ N * ℓ := by
    have e : N * ℓ = ℓ * (L / ℓ) + ℓ := by simp only [N]; ring
    omega
  have hNL2 : N * ℓ ≤ L + ℓ := by
    have e : N * ℓ = ℓ * (L / ℓ) + ℓ := by simp only [N]; ring
    omega
  have hjL : j₁ + L = ⌊(W : ℝ) * T⌋₊ := by have := (hfl W).2; omega
  have hℓR : (ℓ : ℝ) ≤ W * δ + 1 := by
    simp only [ℓ, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (mul_nonneg hW0.le hδ.le)]
  set thr := 3 * lam + ℓ * ((W : ℝ)⁻¹ * Cb) + lam + lam
  have hthr : thr ≤ η / 2 := by
    have h1 : (ℓ : ℝ) * (W : ℝ)⁻¹ ≤ 2 * δ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hW0]; linarith
    have h2 : 2 * δ * Cb ≤ η / 8 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (Cb + 1))).mp hδb
      nlinarith
    have h3 : (ℓ : ℝ) * ((W : ℝ)⁻¹ * Cb) ≤ 2 * δ * Cb := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hCb0
    simp only [thr, lam]; linarith
  -- the event inclusion
  set Z := zB b E s h τ m W (Vs W) c
  set stop := {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧ ∃ i,
    closeLen s W ≤ i ∧ i ≤ ⌊(W : ℝ) * T⌋₊ ∧
      R ≤ ((b3ClosedGramAt b E s h τ m W i (Vs W) y).1.trace).re}
  set mod : ℂ → Set (ProbedPath W np × ℝ) := fun u => {y | ∃ x y', x ≤ y' ∧ y' ≤ N * ℓ ∧
    y' ≤ x + ℓ ∧ thr < |wX Z u j₁ L y' y - wX Z u j₁ L x y|}
  have hincl : {y : ProbedPath W np × ℝ | y.1.1 ∈ physCapEventC b E s h K W ∧
      ∃ t ∈ Set.Icc t₁ T, ∃ t' ∈ Set.Icc t₁ T, |t - t'| ≤ δ ∧ η <
        ‖b3X b E s h τ m W ⌊(W : ℝ) * t⌋₊ (Vs W) c y -
          cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t⌋₊) (b3KJumpAt E s τ m W ⌊(W : ℝ) * t⌋₊) -
          (b3X b E s h τ m W ⌊(W : ℝ) * t'⌋₊ (Vs W) c y -
            cEntry c (b3JumpAt b s τ m W ⌊(W : ℝ) * t'⌋₊)
              (b3KJumpAt E s τ m W ⌊(W : ℝ) * t'⌋₊))‖} ⊆
      stop ∪ ((b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) ∩ mod 1) ∪
        (b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) ∩ mod (-Complex.I))) := by
    rintro y ⟨hcap, t, ht, t', ht', htt, hη'⟩
    by_cases hst : y ∈ stop
    · exact Or.inl hst
    right
    have hal : y ∈ b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) :=
      ⟨hcap, fun i hi1 hi2 => not_le.mp fun hR => hst ⟨hcap, i, hi1, hi2, hR⟩⟩
    rcases window_of_close Z y ht0 hδ.le (hfl W).2 hNL hthr ht ht' htt hη' with h1 | h1
    · exact Or.inl ⟨hal, h1⟩
    · exact Or.inr ⟨hal, h1⟩
  -- one part
  have hpart : ∀ u : ℂ, ‖u‖ = 1 → closedLaw b W np
      (b3Alive b E s h τ m R W ⌊(W : ℝ) * T⌋₊ (Vs W) ∩ mod u) ≤ ENNReal.ofReal (3 * θ / 8) := by
    intro u hu
    refine le_of_eq_of_le (measure_congr ((b3Alive_ae_eq hb1 hE1 hE2 s h τ m R W
      ⌊(W : ℝ) * T⌋₊ (Vs W)).inter (EventuallyEq.refl _ (mod u)))) ?_
    have hmod := window_modulus (closedLaw b W np) (fun j => b3Sigma W j np)
      (fun i => gen_sigma_le W i np) (fun i i' hii' => b3Sigma_mono hii')
      (fun j => b3AliveM b E s h τ m R W j (Vs W)) (fun j => b3dX b E s h τ m W j (Vs W) c)
      (fun j => partnerD b E s h τ m W j (Vs W) c) Z
      (fun j => cEntry c (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j))
      (fun j => IsBirthStep τ W j)
      (fun j y => cDrift b E c (b3ClosedGramAt b E s h τ m W j (Vs W) y))
      (fun j y => partnerP b E c (b3ClosedGramAt b E s h τ m W j (Vs W) y))
      (sc := (W : ℝ)⁻¹) (by positivity) hCb0 hCc0 (j₁ := j₁) (L := L)
      (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊)
      (fun k hk => Finset.mem_Ico.mpr ⟨by have := (hfl W).1; omega, by omega⟩)
      (fun k hk => measurableSet_b3AliveM_past s h τ m R
        (by have := (hfl W).1; omega) le_rfl hV.1)
      (fun k hk y hy => ⟨hy.1, fun i h1 h2 => hy.2 i h1 (by omega)⟩)
      (fun k hk => by
        have h1 : closeLen s W ≤ j₁ + k := by have := (hfl W).1; omega
        unfold b3dX
        exact ((measurable_b3X_past s h τ m (by omega) le_rfl hV.1 c).sub
          (measurable_b3X_past s h τ m h1 (Nat.le_succ _) hV.1 c)).stronglyMeasurable)
      (fun k hk y => partnerD_eq_star b E s h τ m W _ (Vs W) c y)
      (fun k hk y => zB_step b E s h τ m W (Vs W) c (by have := (hfl W).1; omega) y)
      (fun j hj => birth_eq_zero b E τ m hj c)
      (fun k hk => (measurable_cDrift_comp b E c
        (measurable_b3ClosedGramAt b E s h τ m W _ hVm)).aestronglyMeasurable)
      (fun k hk => (measurable_partnerP_comp b E c
        (measurable_b3ClosedGramAt b E s h τ m W _ hVm)).aestronglyMeasurable)
      (fun k hk y hy => by
        have hb := l1_b3Gram_le (by have := (hfl W).1; omega) hy
        exact norm_cDrift_le b E R c _ hb.1 hb.2)
      (fun k hk y hy => by
        have hb := l1_b3Gram_le (by have := (hfl W).1; omega) hy
        exact norm_partnerP_le b E R c _ hb.1 hb.2)
      hε₀.le hε₁
      ((errD_le hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans hSW')
      ((errF_le hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans hBW')
      ((errB_le hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans hSW')
      ((err4_eq hb1 hE1 hE2 s T h τ m R W (Vs W) c).trans_le hFW')
      N ℓ hℓ hNL hu hlam hlam hlam
    rw [hjL] at hmod
    refine hmod.trans (ENNReal.ofReal_le_ofReal ?_)
    have hNLR : ((N : ℝ) * ℓ) ≤ W * T + (W * δ + 1) := by
      have h1 : ((N * ℓ : ℕ) : ℝ) ≤ (L : ℝ) + ℓ := by exact_mod_cast hNL2
      have h2 : (L : ℝ) ≤ W * T := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans
        (Nat.floor_le (mul_nonneg hW0.le hT0.le))
      push_cast at h1; linarith
    have hc := ClosedSumProof.coeff_bound (Cc := Cc) hW0 hWδ' hT0 hNLR hδ2 (by positivity) hℓR
    have hb1' : 16 * ((W : ℝ)⁻¹ * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ / lam ^ 4 ≤ θ / 32 := by
      have hl4 : 0 < lam ^ 4 := by positivity
      rw [div_le_iff₀ hl4]
      have h1 : 16 * ((W : ℝ)⁻¹ * Cc) ^ 2 * ((N : ℝ) * ℓ) * ℓ ≤ 32 * Cc ^ 2 * (T + 1) * δ := by
        nlinarith
      have h2 : 32 * Cc ^ 2 * (T + 1) * δ ≤ θ / 32 * lam ^ 4 := by
        have := (le_div_iff₀ (by positivity : (0 : ℝ) < 1024 * (Cc ^ 2 + 1) * (T + 1))).mp hδc
        have hC : Cc ^ 2 ≤ Cc ^ 2 + 1 := by linarith
        have hδ0 := hδ.le
        nlinarith [mul_le_mul_of_nonneg_right hC (mul_nonneg (by linarith : (0 : ℝ) ≤ T + 1) hδ0)]
      linarith
    have : ε₀ * ((64 + 8 * lam ^ 2) / lam ^ 4 + 1 / lam + 1 / lam) ≤ θ / 8 := hε₀A
    linarith
  refine (measure_mono hincl).trans ((measure_union_le _ _).trans
    ((add_le_add hRW (measure_union_le _ _)).trans ?_))
  refine (add_le_add le_rfl (add_le_add (hpart 1 (by simp))
    (hpart (-Complex.I) (by simp)))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end BlockBand.SourceProcess.PhysApprox.B3.Modul
