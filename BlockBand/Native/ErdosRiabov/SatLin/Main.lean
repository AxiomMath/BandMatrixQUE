module

public import BlockBand.Native.ErdosRiabov.SatLin.Level

/-!
# The saturated master inequalities from the (LL) event bound

The saturated averaged master inequalities follow from the (LL) event bound at the `φ`-level, by
a union bound over a time grid and the slots.

* **`LLGridHyp`** (named hypothesis): the (LL) event over all `s ≤ T` at the level
  `B₂ = N^{ε'/4} φ^{av}_{k,T}`, for every `k = n+4 ≤ 8` and saturated `σ`, with failure
  probability `≤ N^{-D}` on `{T ≤ τ}`. This is the shape of `LLGrid.measure_not_circLLEvent_le`
  with an abstract `φ`-level; by `LLGrid.circLLEvent_mono` any level `≤ N^{ε'/4} φ` implies it.
* `prob_total_le`: the union bound `P(mod) + Σ_i P(E_iᶜ) + Σ_{j<M} Σ_i 4e^{-ρ²} ≤ N^{-D}/2`.
* **`satLinUnif_of_LL`**: `LLGridHyp → SatLinUnif` (the linear-term bound for all `s ∈ (0,T]`
  and all slots:
  `satLin_measure_le`, `slotBad_rotTo`, `satSlot_short`, `satSlot_long`, `bShort_le`,
  `bLong_le`, `side_*`).
* **`masterIneqSat_of_LL`**: `LLGridHyp → MI.MasterIneqSat`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.SatLin

open MeasureTheory Set Function
open BlockBand.External.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel
open BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.Psi
open BlockBand.Native.ErdosRiabov.Propagator
open BlockBand.Native.ErdosRiabov.Forcing
open BlockBand.Native.ErdosRiabov.QV
open BlockBand.Native.ErdosRiabov.Circ
open BlockBand.Native.ErdosRiabov.Stochastic
open BlockBand.Native.ErdosRiabov.MI (logL)
open BlockBand.Native.ErdosRiabov.Assembly (zigPsiData)
open BlockBand.Native.ErdosRiabov.ZigProof (zigTau)
open BlockBand.Native.ErdosRiabov.Apriori (aprPsiI aprPsiA aprLamM)
open BlockBand.SourceProcess.FiniteDriverIntegration
open scoped NNReal ENNReal ComplexConjugate

/-- **The (LL) event over all `s ≤ T` at the `φ`-level (named hypothesis).** For every `d` and
`D > 0` there is `N₀` such that for every ring `p` with `p.b = d.b`, `N ≥ N₀`, `ζ₀ < 1`,
`N^{1+ζ₀} ≤ W²`, every model, `z ∈ 𝒟`, `T ≤ 1`, `k = n+4 ≤ 8` and saturated `σ`:
`P(T ≤ τ ∧ x ∉ circLLEvent P σ τ (N^{ε'/4} φ^{av}_{k,T}) T) ≤ N^{-D}`
(`P = zigPsiData p d.D z`, `τ = zigTau p d z`). -/
def LLGridHyp : Prop :=
  ∀ (d : VSData) (D : ℝ), 0 < D → ∃ N₀ : ℕ,
    ∀ p : BlockBand.Parameters, p.b = d.b → N₀ ≤ p.n * p.W → d.zeta0 < 1 →
      ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2 →
      ∀ (model : p.GaussianRingModel) (z : ℂ),
        BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z →
        ∀ T : ℝ≥0, T ≤ 1 → ∀ {n : ℕ}, n + 4 ≤ 8 → ∀ σ : Fin (n + 2 + 2) → Bool,
          ¬ HasDesatFactor σ →
          driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
              {x | (T : WithTop ℝ≥0) ≤ zigTau p d z x ∧
                x ∉ circLLEvent (zigPsiData p d.D z) σ (zigTau p d z)
                  (((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) * phiT d p z T (n + 4)) T} ≤
            ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-D))

/-!
### The union bound in numbers
-/

/-- `P(mod) + Σ_i P(E_iᶜ) + Σ_{j<M} Σ_i g ≤ N^{-D}/2` from `P(mod), P(E_iᶜ) ≤ N^{-(D+4)}`,
`g ≤ 4 e^{-ρ²}`, `4 e^{-ρ²} ≤ N^{-(D+C+4)}`, `M ≤ 2 N^C`, `k ≤ 8`, `N ≥ 3`. -/
theorem prob_total_le {Nr D C e : ℝ} (hN3 : 3 ≤ Nr) (he0 : 0 ≤ e)
    (he : 4 * e ≤ Nr ^ (-(D + C + 4))) {M k : ℕ} (hM : (M : ℝ) ≤ 2 * Nr ^ C) (hk : k ≤ 8)
    {qm : ℝ≥0∞} (hqm : qm ≤ ENNReal.ofReal (Nr ^ (-(D + 4)))) (qE : Fin k → ℝ≥0∞)
    (hqE : ∀ i, qE i ≤ ENNReal.ofReal (Nr ^ (-(D + 4)))) (qg : ℕ → Fin k → ℝ≥0∞)
    (hqg : ∀ j < M, ∀ i, qg j i ≤ 4 * ENNReal.ofReal e) :
    qm + ∑ i, qE i + ∑ j ∈ Finset.range M, ∑ i, qg j i ≤ ENNReal.ofReal (Nr ^ (-D) / 2) := by
  have hN0 : 0 < Nr := by linarith
  set a := Nr ^ (-(D + 4))
  have ha0 : 0 ≤ a := Real.rpow_nonneg hN0.le _
  have hE : ∑ i, qE i ≤ ENNReal.ofReal (8 * a) := by
    refine (Finset.sum_le_sum fun i _ => hqE i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ha0)
  have hG : ∑ j ∈ Finset.range M, ∑ i, qg j i ≤ ENNReal.ofReal ((M : ℝ) * (8 * (4 * e))) := by
    have h1 : ∀ j ∈ Finset.range M, ∑ i, qg j i ≤ ENNReal.ofReal (8 * (4 * e)) := by
      intro j hj
      refine (Finset.sum_le_sum fun i _ => hqg j (Finset.mem_range.mp hj) i).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by exact_mod_cast hk)
        (by positivity))
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine (add_le_add (add_le_add hqm hE) hG).trans ?_
  rw [← ENNReal.ofReal_add ha0 (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- `M · 32 e ≤ 16 N^{-(D+4)}`
  have hNC : 0 ≤ Nr ^ C := Real.rpow_nonneg hN0.le _
  have h1 : (M : ℝ) * (8 * (4 * e)) ≤ 2 * Nr ^ C * (8 * Nr ^ (-(D + C + 4))) :=
    mul_le_mul hM (by linarith) (by positivity) (by positivity)
  have e1 : Nr ^ C * Nr ^ (-(D + C + 4)) = a := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have e2 : a = Nr ^ (-D) * (Nr ^ (4 : ℝ))⁻¹ := by
    simp only [a]
    rw [show -(D + 4) = -D + -(4 : ℝ) by ring, Real.rpow_add hN0, Real.rpow_neg hN0.le (4 : ℝ)]
  have h81 : (81 : ℝ) ≤ Nr ^ (4 : ℝ) := by
    calc (81 : ℝ) = 3 ^ (4 : ℝ) := by norm_num
      _ ≤ Nr ^ (4 : ℝ) := Real.rpow_le_rpow (by norm_num) hN3 (by norm_num)
  have hND : 0 ≤ Nr ^ (-D) := Real.rpow_nonneg hN0.le _
  have h25 : 25 * a ≤ Nr ^ (-D) / 2 := by
    rw [e2]
    have hpos : 0 < Nr ^ (4 : ℝ) := by linarith
    have : (Nr ^ (4 : ℝ))⁻¹ ≤ 1 / 81 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) h81
    nlinarith
  have : 2 * Nr ^ C * (8 * Nr ^ (-(D + C + 4))) = 16 * a := by rw [← e1]; ring
  linarith

/-!
### The level of the grid step against `satLevel`
-/

/-- `4 k b + 1 ≤ N^{ε'/2} φ` from `b ≤ A ℓ^{757} ρ² φ`, `(32 A + 1) ℓ^{757} ≤ ρ²`, `ρ² = N^{ε'/4}`,
`k ≤ 8`, `1 ≤ φ`. -/
theorem level_le {A ℓ7 ρ2 φ b Nε : ℝ} {k : ℕ} (hk : k ≤ 8) (hA : 0 ≤ A) (hℓ7 : 1 ≤ ℓ7)
    (hφ : 1 ≤ φ) (hb : b ≤ A * ℓ7 * ρ2 * φ) (hAρ : (32 * A + 1) * ℓ7 ≤ ρ2)
    (hNε : ρ2 * ρ2 = Nε) : 4 * (k : ℝ) * b + 1 ≤ Nε * φ := by
  have hk' : (k : ℝ) ≤ 8 := by exact_mod_cast hk
  have hρ1 : 1 ≤ ρ2 := by nlinarith
  have hφ0 : 0 ≤ φ := by linarith
  have hb' : 4 * (k : ℝ) * b ≤ 32 * (A * ℓ7 * ρ2 * φ) := by
    have h0 : 0 ≤ A * ℓ7 * ρ2 * φ := by
      have : 0 ≤ ℓ7 := by linarith
      have : 0 ≤ ρ2 := by linarith
      positivity
    rcases le_or_gt 0 b with hb0 | hb0
    · have := mul_le_mul hk' hb hb0 (by norm_num)
      nlinarith
    · have : 4 * (k : ℝ) * b ≤ 0 := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
        nlinarith
      linarith
  have h1 : 32 * (A * ℓ7 * ρ2 * φ) + 1 ≤ ((32 * A + 1) * ℓ7) * ρ2 * φ := by
    have : 1 ≤ ℓ7 * ρ2 * φ := by
      have := mul_le_mul hℓ7 hρ1 zero_le_one (by linarith)
      nlinarith
    nlinarith
  have h2 : ((32 * A + 1) * ℓ7) * ρ2 * φ ≤ ρ2 * ρ2 * φ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAρ (by linarith)) hφ0
  rw [← hNε]
  linarith

theorem rpow_eighth_sq {Nr ε : ℝ} (hN : 0 < Nr) :
    (Nr ^ (ε / 8)) ^ 2 = Nr ^ (ε / 4) ∧ Nr ^ (ε / 4) * Nr ^ (ε / 4) = Nr ^ (ε / 2) := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1; push_cast; ring
  · rw [← Real.rpow_add hN]
    congr 1; ring

/-- `⌈N^C⌉ ≤ 2 N^C` for `N ≥ 1`, `C ≥ 0`. -/
theorem ceil_le_two {Nr C : ℝ} (hN1 : 1 ≤ Nr) (hC : 0 ≤ C) : (⌈Nr ^ C⌉₊ : ℝ) ≤ 2 * Nr ^ C := by
  have h1 : 1 ≤ Nr ^ C := Real.one_le_rpow hN1 hC
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ Nr ^ C by linarith)
  linarith

/-- `P(T ≤ τ, x ∉ univ) = 0`. -/
theorem measure_not_univ_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (τ : Ω → WithTop ℝ≥0)
    (T : ℝ≥0) (q : ℝ≥0∞) : ν {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∉ (univ : Set Ω)} ≤ q := by
  have : {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∉ (univ : Set Ω)} = ∅ := by
    ext x; simp
  rw [this, measure_empty]
  exact bot_le

/-- The saturated linear event shrinks when the level grows. -/
theorem satEvent_mono {p : BlockBand.Parameters} (P : PsiData (p.n * p.W)) (hW : 0 < P.W)
    (hz : 0 < P.z.im) {k : ℕ} (σ : Fin k → Bool) (u : Fin k → Fin (p.n * p.W))
    (τ : RingSample p → WithTop ℝ≥0) (T : ℝ≥0) (hT1 : (T : ℝ) ≤ 1) {B B' : ℝ} (hBB : B ≤ B') :
    {x | (T : WithTop ℝ≥0) ≤ τ x ∧ ¬ ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
        ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
          (fun _ => conj (semicircleM P.z)) s) (fun y => P.avErr σ y s (Evol.pathH p x s)) u‖ ≤
        B' * (P.lEta s ^ Expo.lossBeta k * P.sAv u s)} ⊆
    {x | (T : WithTop ℝ≥0) ≤ τ x ∧ ¬ ∀ s ∈ Ioc (0 : ℝ) T, vsHeight P.z s *
        ‖propOp (vsTensorGen P.S (fun _ => semicircleM P.z)
          (fun _ => conj (semicircleM P.z)) s) (fun y => P.avErr σ y s (Evol.pathH p x s)) u‖ ≤
        B * (P.lEta s ^ Expo.lossBeta k * P.sAv u s)} := by
  have hN : 0 < p.n * p.W := Nat.mul_pos (by have := p.n_ge_four; omega) p.W_pos
  rintro x ⟨hτ, hno⟩
  refine ⟨hτ, fun hall => hno fun s hs => (hall s hs).trans ?_⟩
  have hs1 : s ≤ 1 := hs.2.trans hT1
  exact mul_le_mul_of_nonneg_right hBB (mul_nonneg (Real.rpow_nonneg
    (P.lEta_pos hN hW hz hs1).le _) (P.sAv_pos hN hW hz hs1 u).le)

/-!
### The two families
-/

section Cases

variable (d : VSData) {p : BlockBand.Parameters} (hpb : p.b = d.b)
  (hP6 : ((p.n * p.W : ℕ) : ℝ) ^ (1 + d.zeta0) ≤ (p.W : ℝ) ^ 2)
  (model : p.GaussianRingModel) {z : ℂ} (hz : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 z)
  (hN0 : Grid.zigN0 d ≤ ((p.n * p.W : ℕ) : ℝ)) (hN3 : (3 : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ))
  {D : ℝ} (T : ℝ≥0) (hT1 : T ≤ 1)
  (hmod : driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
    (Grid.modulusEvent p (LLGrid.llCg d)) ≤
      ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-(D + 4))))
  (htail : 4 * Real.exp (-(((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 8)) ^ 2) ≤
    ((p.n * p.W : ℕ) : ℝ) ^ (-(D + LLGrid.llCg d + 4)))
include hpb hP6 hz hN0 hN3 hT1 hmod htail

/-- **The saturated linear term, long chains (`k = n+4`), for all `s ∈ (0,T]`** (uniform in
`s`, summed over the slots): from the (LL) bound at the level `N^{ε'/4} φ_k` for every rotated
pattern and the absorption `(32 aLong + 1) ℓ^{757} ≤ N^{ε'/4}`,
`MI.SatLinBound … σ u T (N^{ε'/2} φ_k) (N^{-D}/2)`. -/
theorem satLinBound_long {n : ℕ} (hn : n + 4 ≤ 8) (σ : Fin (n + 2 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (n + 2 + 2) → Fin (p.n * p.W))
    (hLL : ∀ σ' : Fin (n + 2 + 2) → Bool, ¬ HasDesatFactor σ' →
      driverLaw (κ := Fin (ringDim p)) (model.law : Measure p.SiteMatrix)
          {x | (T : WithTop ℝ≥0) ≤ zigTau p d z x ∧
            x ∉ circLLEvent (zigPsiData p d.D z) σ' (zigTau p d z)
              (((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4) * phiT d p z T (n + 4)) T} ≤
        ENNReal.ofReal (((p.n * p.W : ℕ) : ℝ) ^ (-(D + 4))))
    (hA : (32 * aLong d n + 1) * logL (p.n * p.W) ^ 757 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4)) :
    MI.SatLinBound (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z)
      (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (n := n + 3) σ u T
      (satLevel d p z T (n + 4)) (((p.n * p.W : ℕ) : ℝ) ^ (-D) / 2) := by
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix)
  set P := zigPsiData p d.D z
  set Nr : ℝ := ((p.n * p.W : ℕ) : ℝ)
  set ρ : ℝ := Nr ^ (d.epsP / 8)
  set φ := phiT d p z T (n + 4)
  set B₂ := Nr ^ (d.epsP / 4) * φ
  set τ := tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))
  have hNpos : 0 < p.n * p.W := MI.mi_N_pos p
  have hN0' : (0 : ℝ) < Nr := by simp only [Nr]; exact_mod_cast hNpos
  have hz' : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z := hz
  have hzi := hz'.im_pos hNpos
  have hS : StochasticSymm P.S := Evol.stochasticSymm_ring p
  have hPH : Split.ProfileHyp P.S := ⟨hS.nonneg, hS.symm, hS.rowSum⟩
  have hD : 0 ≤ P.D := by show 0 ≤ d.D; linarith [d.D_ge_six]
  have hb : d.b = p.b := hpb.symm
  have hT1' : (T : ℝ) ≤ 1 := by exact_mod_cast hT1
  have hk1 : 1 ≤ n + 2 + 2 := by omega
  obtain ⟨hB2, hBL, -, -, -, -, -, -, -, -⟩ := Grid.zig_conditions d hN0 hz' hk1 hn
  obtain ⟨hq, hqE⟩ := side_factor d P rfl hz' hN0 hk1 hn
  have hfl := side_floor d P rfl rfl hz' hN0 hk1 hn u
  have herr := side_herr d P hz' hN0 hk1 hn
  obtain ⟨hρ2, hρ4⟩ := rpow_eighth_sq (ε := d.epsP) hN0'
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow (by linarith) (by have := d.epsP_pos; positivity)
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨-, -, hφ1⟩ := phiT_facts d hz hT1' (k := n + 4) (by omega) hn
  have hB₂0 : 0 ≤ B₂ := mul_nonneg (Real.rpow_nonneg hN0'.le _) (by linarith)
  obtain ⟨hAl0, hbl⟩ := bLong_le d hz hT1' hn hρ1 (B₂ := B₂) (by rw [hρ2])
  set b := bLong d P n B₂ T ρ
  have hb0 : 0 ≤ b := by
    have hN := hNpos
    have hX := (zig_scalars d hz hT1').2.1
    have hpsi := MI.mi_psi_ge d p
    have hpsi0 : ∀ n, 0 ≤ aprPsiI d (p.n * p.W) n ∧ 0 ≤ aprPsiA d (p.n * p.W) n := fun n =>
      ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
    have hγ1 : 0 ≤ 1 - Expo.lossBeta (n + 4) := by linarith [qv_beta_le_one (k := n + 4) hn]
    have h1 := MI.intF_nonneg d P rfl hz' hT1' hγ1
    have h2 : 0 ≤ bOne d P n T := by
      unfold bOne
      exact mul_nonneg (MI.avConst_nonneg d (by linarith [MI.aprLamM_one_le d hN])
        (MI.eMI_nonneg d hN _) _) (phiAvF_nonneg hpsi0 hX.le (zig_scalars d hz hT1').2.2.1.le _)
    have h3 := (qvPhiAv_pos (fun j => (hpsi j).1) (fun j => (hpsi0 j).2) (n + 4) hX).le
    have hCP := kernelActionConst_ge_one d
    have hCK := (vsCK_pos d).le
    have hCw : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
    have h4 := Real.sqrt_nonneg (qvC d * aprLamM d (p.n * p.W) ^ 3 *
      MI.intF d P (2 - 2 * Expo.lossBeta (n + 4)) T)
    simp only [b, bLong]
    positivity
  have hlev : 4 * ((n + 2 + 2 : ℕ) : ℝ) * b + 1 ≤ satLevel d p z T (n + 4) := by
    have hAρ : (32 * aLong d n + 1) * logL (p.n * p.W) ^ 757 ≤ ρ ^ 2 := by rw [hρ2]; exact hA
    have hNε : ρ ^ 2 * ρ ^ 2 = Nr ^ (d.epsP / 2) := by rw [hρ2, hρ4]
    have e : satLevel d p z T (n + 4) = Nr ^ (d.epsP / 2) * phiT d p z T (n + 4) := rfl
    rw [e]
    exact level_le (k := n + 2 + 2) hn hAl0 (one_le_pow₀ (MI.mi_logL_one (p := p))) hφ1 hbl
      hAρ hNε
  -- the rotated patterns and their (LL) events
  set σr : Fin (n + 2 + 2) → Fin (n + 2 + 2) → Bool := fun i l =>
    σ ((finRotate (n + 2 + 2) ^ ((i : ℕ) + 1)) l)
  have hσr : ∀ i, ¬ HasDesatFactor (σr i) := fun i =>
    MBound.not_hasDesatFactor_comp hσ ((i : ℕ) + 1)
  set E : Fin (n + 2 + 2) → Set (RingSample p) := fun i => circLLEvent P (σr i) τ B₂ T
  have h := satLin_measure_le μ P p.W_pos hz' hS hD hk1 hn σ u τ T hT1' hB2 hBL hfl hq hqE
    herr hb0 E
  unfold MI.SatLinBound
  refine (measure_mono (satEvent_mono P p.W_pos hzi σ u τ T hT1' hlev)).trans (h.trans ?_)
  set mh := VS.meshPow Nr (LLGrid.llCg d)
  refine prob_total_le hN3 (Real.exp_pos _).le htail
    (ceil_le_two (by linarith) (LLGrid.llCg_facts d).1.le) hn hmod
    (fun i => driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∉ E i})
    (fun i => hLL (σr i) (hσr i))
    (fun j i => driverLaw (κ := Fin (ringDim p)) μ
      {x | ((gridPt mh T j : ℝ≥0) : WithTop ℝ≥0) ≤ τ x ∧ x ∈ E i ∧
        slotBad P σ u b i (gridPt mh T j) x}) ?_
  intro j _ i
  have hs' : ((gridPt mh T j : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨(gridPt mh T j).2, (show ((gridPt mh T j : ℝ≥0) : ℝ) ≤ T by
      exact_mod_cast gridPt_le mh T j).trans hT1'⟩
  refine (measure_mono ?_).trans (satSlot_long μ d hb rfl rfl rfl hz' hP6 hT1' (gridPt_le mh T j)
    hn (σr i) (hσr i) (MBound.mbRotTo i u) hB₂0 hρ0)
  rintro x ⟨h1, h2, h3⟩
  exact ⟨h1, h2, (slotBad_rotTo P hPH hzi.ne' σ u b i hs' x).mp h3⟩

/-- **The saturated linear term, short chains (`k = 2`), for all `s ∈ (0,T]`** (uniform in `s`,
both slots): for `T > 0` and the absorption `(32 aShort + 1) ℓ^{757} ≤ N^{ε'/4}`,
`MI.SatLinBound … σ u T (N^{ε'/2} φ_2) (N^{-D}/2)`. -/
theorem satLinBound_short (hT0 : 0 < (T : ℝ)) (σ : Fin (0 + 2) → Bool)
    (hσ : ¬ HasDesatFactor σ) (u : Fin (0 + 2) → Fin (p.n * p.W))
    (hA : (32 * aShort d + 1) * logL (p.n * p.W) ^ 757 ≤ ((p.n * p.W : ℕ) : ℝ) ^ (d.epsP / 4)) :
    MI.SatLinBound (model.law : Measure p.SiteMatrix) (zigPsiData p d.D z)
      (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W)) (n := 1) σ u T
      (satLevel d p z T 2) (((p.n * p.W : ℕ) : ℝ) ^ (-D) / 2) := by
  set μ : Measure p.SiteMatrix := (model.law : Measure p.SiteMatrix)
  set P := zigPsiData p d.D z
  set Nr : ℝ := ((p.n * p.W : ℕ) : ℝ)
  set ρ : ℝ := Nr ^ (d.epsP / 8)
  set φ := phiT d p z T 2
  set τ := tau p P (aprPsiI d (p.n * p.W)) (aprPsiA d (p.n * p.W))
  have hNpos : 0 < p.n * p.W := MI.mi_N_pos p
  have hN0' : (0 : ℝ) < Nr := by simp only [Nr]; exact_mod_cast hNpos
  have hz' : BulkDomain (p.n * p.W) d.delta0 d.kappa d.C0 P.z := hz
  have hzi := hz'.im_pos hNpos
  have hS : StochasticSymm P.S := Evol.stochasticSymm_ring p
  have hPH : Split.ProfileHyp P.S := ⟨hS.nonneg, hS.symm, hS.rowSum⟩
  have hD : 0 ≤ P.D := by show 0 ≤ d.D; linarith [d.D_ge_six]
  have hb : d.b = p.b := hpb.symm
  have hT1' : (T : ℝ) ≤ 1 := by exact_mod_cast hT1
  have hk1 : 1 ≤ 0 + 2 := by omega
  have hk8 : 0 + 2 ≤ 8 := by omega
  obtain ⟨hB2, hBL, -, -, -, -, -, -, -, -⟩ := Grid.zig_conditions d hN0 hz' hk1 hk8
  obtain ⟨hq, hqE⟩ := side_factor d P rfl hz' hN0 hk1 hk8
  have hfl := side_floor d P rfl rfl hz' hN0 hk1 hk8 u
  have herr := side_herr d P hz' hN0 hk1 hk8
  obtain ⟨hρ2, hρ4⟩ := rpow_eighth_sq (ε := d.epsP) hN0'
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow (by linarith) (by have := d.epsP_pos; positivity)
  have hρ0 : 0 ≤ ρ := by linarith
  obtain ⟨-, -, hφ1⟩ := phiT_facts d hz hT1' (k := 2) (by norm_num) (by norm_num)
  have hbs := bShort_le d hz hT1' hρ1
  set b := bShort d P T ρ
  have hb0 : 0 ≤ b := by
    have hN := hNpos
    have hX := (zig_scalars d hz hT1').2.1
    have hpsi := MI.mi_psi_ge d p
    have hpsi0 : ∀ n, 0 ≤ aprPsiI d (p.n * p.W) n ∧ 0 ≤ aprPsiA d (p.n * p.W) n := fun n =>
      ⟨by linarith [(hpsi n).1], by linarith [(hpsi n).2]⟩
    have h1 := MI.intF_nonneg d P rfl hz' hT1' (γ := 0) le_rfl
    have h2 := MI.avConst_nonneg d (by linarith [MI.aprLamM_one_le d hN]) (MI.eMI_nonneg d hN 2)
      2 (LamM := aprLamM d (p.n * p.W))
    have h2' := phiAvF_nonneg hpsi0 hX.le (zig_scalars d hz hT1').2.2.1.le 2
      (psiI := aprPsiI d (p.n * p.W)) (psiA := aprPsiA d (p.n * p.W))
    have h3 := (qvPhiAv_pos (fun j => (hpsi j).1) (fun j => (hpsi0 j).2) 2 hX).le
    have hcR := cR_pos d
    have hCK := (vsCK_pos d).le
    have h4 := Real.sqrt_nonneg (qvC d * aprLamM d (p.n * p.W) ^ 3 * MI.intF d P 0 T)
    have h5 := (hpsi0 1).2
    simp only [b, bShort]
    positivity
  have hlev : 4 * ((0 + 2 : ℕ) : ℝ) * b + 1 ≤ satLevel d p z T 2 := by
    have hAρ : (32 * aShort d + 1) * logL (p.n * p.W) ^ 757 ≤ ρ ^ 2 := by rw [hρ2]; exact hA
    have hNε : ρ ^ 2 * ρ ^ 2 = Nr ^ (d.epsP / 2) := by rw [hρ2, hρ4]
    have e : satLevel d p z T 2 = Nr ^ (d.epsP / 2) * φ := rfl
    have hbl : b ≤ aShort d * logL (p.n * p.W) ^ 757 * ρ ^ 2 * φ := by
      refine hbs.trans ?_
      have h0 : 0 ≤ aShort d * logL (p.n * p.W) ^ 757 * φ := by
        have := aShort_nonneg d
        have := one_le_pow₀ (MI.mi_logL_one (p := p)) (n := 757)
        positivity
      have : ρ ≤ ρ ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this h0
      linarith
    rw [e]
    exact level_le (k := 0 + 2) hk8 (aShort_nonneg d) (one_le_pow₀ (MI.mi_logL_one (p := p))) hφ1
      hbl hAρ hNε
  set σr : Fin (0 + 2) → Fin (0 + 2) → Bool := fun i l =>
    σ ((finRotate (0 + 2) ^ ((i : ℕ) + 1)) l)
  have hσr : ∀ i, ¬ HasDesatFactor (σr i) := fun i =>
    MBound.not_hasDesatFactor_comp hσ ((i : ℕ) + 1)
  set E : Fin (0 + 2) → Set (RingSample p) := fun _ => univ
  have h := satLin_measure_le μ P p.W_pos hz' hS hD hk1 hk8 σ u τ T hT1' hB2 hBL hfl hq hqE
    herr hb0 E
  unfold MI.SatLinBound
  refine (measure_mono (satEvent_mono P p.W_pos hzi σ u τ T hT1' hlev)).trans (h.trans ?_)
  set mh := VS.meshPow Nr (LLGrid.llCg d)
  refine prob_total_le hN3 (Real.exp_pos _).le htail
    (ceil_le_two (by linarith) (LLGrid.llCg_facts d).1.le) hk8 hmod
    (fun i => driverLaw (κ := Fin (ringDim p)) μ {x | (T : WithTop ℝ≥0) ≤ τ x ∧ x ∉ E i})
    (fun i => measure_not_univ_le _ _ _ _)
    (fun j i => driverLaw (κ := Fin (ringDim p)) μ
      {x | ((gridPt mh T j : ℝ≥0) : WithTop ℝ≥0) ≤ τ x ∧ x ∈ E i ∧
        slotBad P σ u b i (gridPt mh T j) x}) ?_
  intro j _ i
  have hs' : ((gridPt mh T j : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨(gridPt mh T j).2, (show ((gridPt mh T j : ℝ≥0) : ℝ) ≤ T by
      exact_mod_cast gridPt_le mh T j).trans hT1'⟩
  have hpos : 0 < ((gridPt mh T j : ℝ≥0) : ℝ) := by
    have hmh : 0 < mh := Grid.meshPow_pos_dim p _
    unfold gridPt
    rw [NNReal.coe_min]
    refine lt_min ?_ hT0
    push_cast
    positivity
  refine (measure_mono ?_).trans (satSlot_short μ d hb rfl rfl rfl hz' hP6 hT1' (gridPt_le mh T j)
    hpos (σr i) (hσr i) (MBound.mbRotTo i u) hρ0)
  rintro x ⟨h1, -, h3⟩
  exact ⟨h1, (slotBad_rotTo P hPH hzi.ne' σ u b i hs' x).mp h3⟩

end Cases

/-!
### The assembly
-/

theorem aLong_nonneg (d : VSData) {n : ℕ} (hn : n + 4 ≤ 8) : 0 ≤ aLong d n := by
  have hγ1 : 0 ≤ 1 - Expo.lossBeta (n + 4) := by linarith [qv_beta_le_one (k := n + 4) hn]
  have hγ2 : 0 ≤ 2 - 2 * Expo.lossBeta (n + 4) := by linarith [qv_beta_le_one (k := n + 4) hn]
  have := MI.aInt_nonneg d hγ1; have := MI.aInt_nonneg d hγ2; have := MI.cAvZ_nonneg d
  have := MI.aLam_nonneg d; have := (qvC_pos d).le; have := (vsCK_pos d).le
  have := le_trans zero_le_one d.one_le_Cwc; have := kernelActionConst_ge_one d
  unfold aLong
  positivity

/-- The constant of the absorption of the levels: `32 (aShort + Σ_{n ≤ 4} aLong n) + 1`. -/
def aAll (d : VSData) : ℝ := 32 * (aShort d + ∑ n ∈ Finset.range 5, aLong d n) + 1

theorem aAll_facts (d : VSData) {n : ℕ} (hn : n + 4 ≤ 8) :
    0 ≤ aAll d ∧ 32 * aShort d + 1 ≤ aAll d ∧ 32 * aLong d n + 1 ≤ aAll d := by
  have hs := Finset.sum_nonneg fun j (hj : j ∈ Finset.range 5) =>
    aLong_nonneg d (n := j) (by have := Finset.mem_range.mp hj; omega)
  have h1 := Finset.single_le_sum (f := fun j => aLong d j)
    (fun j hj => aLong_nonneg d (n := j) (by have := Finset.mem_range.mp hj; omega))
    (Finset.mem_range.mpr (show n < 5 by omega))
  have h0 := aShort_nonneg d
  unfold aAll
  refine ⟨by positivity, by linarith, by linarith⟩

/-- **The saturated linear term for all `s ≤ T` and all slots, from the (LL) bound.**
`LLGridHyp → SatLinUnif`, with
`N₀ = max N₀^{LL}(D+4) ⌈max (max N₀^{mod}(D+4) (zigN0 d)) (max (absorbN0 aAll 757 (ε'/4))
(tailN0 (ε'/4) (D + C + 4) + 3))⌉`. The hypothesis `LLGridHyp` is proved as `llGridHyp_holds`.
-/
theorem satLinUnif_of_LL (h : LLGridHyp) : SatLinUnif := by
  intro d D hD
  set C := LLGrid.llCg d
  have hC := (LLGrid.llCg_facts d).1
  have hε := d.epsP_pos
  obtain ⟨N₁, hN₁⟩ := h d (D + 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := Grid.modulusEvent_whp hC (D + 4)
  set R : ℝ := max (max N₂ (Grid.zigN0 d))
    (max (MI.absorbN0 (aAll d) 757 (d.epsP / 4)) (MI.tailN0 (d.epsP / 4) (D + C + 4) + 3))
  refine ⟨max N₁ ⌈R⌉₊, fun p hpb hN hζ hband model z hz t ht n hn σ hσ u => ?_⟩
  set Nr : ℝ := ((p.n * p.W : ℕ) : ℝ)
  have hNR : R ≤ Nr := (Nat.le_ceil R).trans
    (show ((⌈R⌉₊ : ℕ) : ℝ) ≤ ((p.n * p.W : ℕ) : ℝ) by exact_mod_cast le_of_max_le_right hN)
  have hN2 : N₂ ≤ Nr := (le_max_left _ _ |>.trans (le_max_left _ _)).trans hNR
  have hN0 : Grid.zigN0 d ≤ Nr := (le_max_right _ _ |>.trans (le_max_left _ _)).trans hNR
  have hNA : MI.absorbN0 (aAll d) 757 (d.epsP / 4) ≤ Nr :=
    (le_max_left _ _ |>.trans (le_max_right _ _)).trans hNR
  have hNt : MI.tailN0 (d.epsP / 4) (D + C + 4) + 3 ≤ Nr :=
    (le_max_right _ _ |>.trans (le_max_right _ _)).trans hNR
  have hN3 : (3 : ℝ) ≤ Nr := by
    have := MI.tailN0_nonneg (d.epsP / 4) (D + C + 4); linarith
  have hN1nat : 1 ≤ p.n * p.W := MI.mi_N_pos p
  have hN0' : (0 : ℝ) < Nr := by linarith
  have hmod := hN₂ p (model.law : Measure p.SiteMatrix) hN2
  have htail : 4 * Real.exp (-(Nr ^ (d.epsP / 8)) ^ 2) ≤ Nr ^ (-(D + C + 4)) := by
    rw [(rpow_eighth_sq (ε := d.epsP) hN0').1]
    refine le_trans ?_ (MI.tail_le (ε := d.epsP / 4) (D := D + C + 4) (by positivity) hN1nat
      (by linarith))
    have h0 : 0 ≤ Nr ^ (d.epsP / 4) := Real.rpow_nonneg hN0'.le _
    have : Real.exp (-(Nr ^ (d.epsP / 4))) ≤ Real.exp (-(Nr ^ (d.epsP / 4) / 4)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hT1 : t ≤ 1 := ht
  -- the absorption of the levels
  have hAbs : aAll d * logL (p.n * p.W) ^ 757 ≤ Nr ^ (d.epsP / 4) := by
    have h0 := (aAll_facts d (n := 0) (by norm_num)).1
    have hl := one_le_pow₀ (MI.mi_logL_one (p := p)) (n := 757)
    have := MI.absorb_of_logL (by positivity) h0 le_rfl (by positivity) hNA
      (F := aAll d * logL (p.n * p.W) ^ 757) (M := 0)
    unfold MI.Absorb at this
    rw [mul_zero, add_zero] at this
    exact this
  by_cases ht0 : (t : ℝ) = 0
  · unfold MI.SatLinBound
    refine (measure_mono (t := ∅) fun x hx => hx.2 fun s hs => ?_).trans
      (by rw [measure_empty]; exact bot_le)
    exact absurd (hs.2.trans_eq ht0) (not_le.mpr hs.1)
  have ht0' : 0 < (t : ℝ) := lt_of_le_of_ne t.2 (Ne.symm ht0)
  have hl := one_le_pow₀ (MI.mi_logL_one (p := p)) (n := 757)
  rcases n with _ | _ | _ | m
  · exact absurd (MBound.hasDesatFactor_of_odd (by decide) σ) hσ
  · have hA : (32 * aShort d + 1) * logL (p.n * p.W) ^ 757 ≤ Nr ^ (d.epsP / 4) :=
      (mul_le_mul_of_nonneg_right (aAll_facts d (n := 0) (by norm_num)).2.1
        (by positivity)).trans hAbs
    exact satLinBound_short d hpb hband model hz hN0 hN3 t hT1 hmod htail ht0' σ hσ u hA
  · exact absurd (MBound.hasDesatFactor_of_odd (by decide) σ) hσ
  · have hm : m + 4 ≤ 8 := by omega
    have hA : (32 * aLong d m + 1) * logL (p.n * p.W) ^ 757 ≤ Nr ^ (d.epsP / 4) :=
      (mul_le_mul_of_nonneg_right (aAll_facts d hm).2.2 (by positivity)).trans hAbs
    exact satLinBound_long d hpb hband model hz hN0 hN3 t hT1 hmod htail hm σ hσ u
      (fun σ' hσ' => hN₁ p hpb (le_of_max_le_left hN) hζ hband model z hz t ht hm σ' hσ') hA

/-- **The saturated part of the master inequality from the (LL) event bound.**
`LLGridHyp → MI.MasterIneqSat` (`satLinUnif_of_LL`, `masterIneqSat_of_satLinUnif`); the
hypothesis `LLGridHyp` is proved as `llGridHyp_holds`.
-/
theorem masterIneqSat_of_LL (h : LLGridHyp) : MI.MasterIneqSat :=
  masterIneqSat_of_satLinUnif (satLinUnif_of_LL h)

/-- **`Inputs.ShortRingLocalLaw` from the (LL) event bound** (from `LLGridHyp`):
`MI.shortRingLocalLaw_of_masterIneqSat ∘ masterIneqSat_of_LL`.
-/
theorem shortRingLocalLaw_of_LL (h : LLGridHyp) :
    BlockBand.Internal.Contracts.Inputs.ShortRingLocalLaw :=
  MI.shortRingLocalLaw_of_masterIneqSat (masterIneqSat_of_LL h)

end BlockBand.Native.ErdosRiabov.SatLin
