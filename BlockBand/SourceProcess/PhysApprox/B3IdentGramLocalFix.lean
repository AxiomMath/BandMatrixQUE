module

public import BlockBand.SourceProcess.PhysApprox.B3IdentGramLocalAcct

/-!
# The local Gram bound at fixed `W`

Measure: `closedLaw b W np`. Horizon `T ≥ s + t + 1` for the summed errors.
* `dYh_cases`: on a special cell (`p`, `q`, or a birth step), `ΔŶ` is `0` on the last cell, the
  birth error `b3dX − b3BirthAt` on a birth step (`b3JumpAt_succ`), and `b3dX` on the first cell;
  so on such a cell the tested increment is bounded by a constant plus the first moments of `ΔŶ`;
* **`fixedW_bound`**: `‖pStopSum‖ₑ` is bounded by the summed drift/bracket/birth errors, the
  summed third and fourth moments, the first moment at `p`, and explicit deterministic terms.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local

open MeasureTheory ProbabilityTheory Filter Topology Matrix Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
open BlockBand.SourceProcess.Stochastic BlockBand.SourceProcess.ClosedLimit
open BlockBand.SourceProcess.ClosedPath
open BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Pass
open BlockBand.SourceProcess.PhysApprox.B3.Ident2 BlockBand.SourceProcess.PhysApprox.B3.Modul
open scoped NNReal ENNReal

variable {K np : ℕ}

section Fix

variable {χ : ℝ → ℝ} {b E s h : ℝ} {τ m : Fin np → ℝ} {W : ℕ}
  {V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ}
  {F : ZSt K np → ℂ} {Λ : GSt K np × ZSt K np → ℂ} {a t : ℝ≥0} {R : ℝ}
  {r : ℕ} {i : Fin r → LIdx K np} {u : Fin r → ℝ≥0}
  {φ : BoundedContinuousFunction (Fin r → ℂ) ℝ}

/-- The increment of `Ŷ` over the cell `j`. -/
def dYh (b E s h : ℝ) (τ m : Fin np → ℝ) (W : ℕ)
    (V : GrowthPath W → Matrix (Fin 2 × Fin W) (Fin K × Fin 2) ℂ) (a t : ℝ≥0) (j : ℕ)
    (c : GIdx K np) (y : ProbedPath W np × ℝ) : ℂ :=
  gramEntry c (yHat b E s h τ m W (limLenAll s W (cellT s W a t (j + 1))) V y) -
    gramEntry c (yHat b E s h τ m W (limLenAll s W (cellT s W a t j)) V y)

theorem measurable_dYh (hV : Measurable V) (j : ℕ) (c : GIdx K np) :
    Measurable (dYh b E s h τ m W V a t j c) := by
  have e : dYh b E s h τ m W V a t j c = fun y =>
      (gramEntry c (b3ClosedGramAt b E s h τ m W (limLenAll s W (cellT s W a t (j + 1))) V y) -
        gramEntry c (b3JumpAt (K := K) b s τ m W (limLenAll s W (cellT s W a t (j + 1))))) -
      (gramEntry c (b3ClosedGramAt b E s h τ m W (limLenAll s W (cellT s W a t j)) V y) -
        gramEntry c (b3JumpAt (K := K) b s τ m W (limLenAll s W (cellT s W a t j)))) := by
    funext y; simp only [dYh, yHat, gramEntry_sub']
  rw [e]
  exact ((((ClosedSumProof.measurable_gramEntry c).comp
      (measurable_b3ClosedGramAt b E s h τ m W _ hV)).sub_const _).sub
    (((ClosedSumProof.measurable_gramEntry c).comp
      (measurable_b3ClosedGramAt b E s h τ m W _ hV)).sub_const _))

/-- **`ΔŶ` on the special cells.** -/
theorem dYh_cases (hs : 0 ≤ s) (hW : 1 ≤ W) (hat : a ≤ t) {j : ℕ}
    (hpj : limLenAll s W a ≤ j) (hjq : j ≤ limLenAll s W t) (c : GIdx K np)
    (y : ProbedPath W np × ℝ) :
    (j = limLenAll s W t → dYh b E s h τ m W V a t j c y = 0) ∧
    (j + 1 ≤ limLenAll s W t → dYh b E s h τ m W V a t j c y =
      b3dX b E s h τ m W j V (Sum.inl c) y - gramEntry c (b3BirthAt (K := K) b τ m W j)) := by
  have hcj : closeLen s W ≤ j := (closeLen_le_limLenAll (s := s) (W := W) a).trans hpj
  have hLj : limLenAll s W (cellT s W a t j) = j := limLenAll_cellT hs hW hpj hjq
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · subst hq
    unfold dYh
    rw [cellT_last hW hat, hLj, sub_self]
  · have hL1 : limLenAll s W (cellT s W a t (j + 1)) = j + 1 :=
      limLenAll_cellT hs hW (by omega) hq
    unfold dYh
    rw [hLj, hL1]
    simp only [yHat, b3JumpAt_succ b s τ m hcj, gramEntry_sub', ClosedSumProof.gramEntry_add, b3dX,
      b3X, cEntry]
    ring

theorem limLenAll_lt_floor (hs : 0 ≤ s) (hW : 1 ≤ W) {T : ℝ} (hT : s + t + 1 ≤ T) :
    limLenAll s W t < ⌊(W : ℝ) * T⌋₊ := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : (W : ℝ) * (s + t) + 1 ≤ W * T := by nlinarith [t.2]
  have h2 : ((limLenAll s W t + 1 : ℕ) : ℝ) ≤ W * T := by
    push_cast; linarith [limLenAll_le_mul (W := W) hs t]
  have := Nat.le_floor h2
  omega

theorem card_Ico_le (hs : 0 ≤ s) (hW : 1 ≤ W) (hat : a ≤ t) :
    ((Finset.Ico (limLenAll s W a) (limLenAll s W t + 1)).card : ℝ) ≤ W * (t + 2) := by
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hpq : limLenAll s W a ≤ limLenAll s W t + 1 :=
    (Nat.floor_mono (mul_le_mul_of_nonneg_left (by
      have : (a : ℝ) ≤ t := hat
      linarith) (Nat.cast_nonneg W))).trans (Nat.le_succ _)
  rw [Nat.card_Ico, Nat.cast_sub hpq]
  have h1 := limLenAll_le_mul (W := W) hs t
  have h2 := lt_limLenAll_add_one (s := s) (W := W) a
  push_cast
  nlinarith [a.2, t.2]

/-- **The bound at fixed `W`.** -/
theorem fixedW_bound (hCE : CondExpReplace) (td : TaylorData χ b E F Λ) (hb : b < 1)
    (hE1 : -2 < E) (hE2 : E < 2) (hs : 0 ≤ s) (hτ : ∀ i, s < τ i) (hW : 1 ≤ W)
    (hVg : Measurable[growthSigma W (closeLen s W)] V) (hχ : Continuous χ) (hF : Continuous F)
    (hΛ : Continuous Λ) (hat : a ≤ t) (hu : ∀ l, u l ≤ a) {T : ℝ} (hT : s + t + 1 ≤ T)
    (hnbp : ¬ IsBirthStep τ W (limLenAll s W a)) (hnbq : ¬ IsBirthStep τ W (limLenAll s W t))
    (hfe : ∀ᵐ y ∂closedLaw b W np, y.1.1 ∈ physCapEventC b E s h K W →
      FeasPath b E s h τ m W V y)
    {Rχ CT CJ BA CA Ca CΓ Crest Cβ CH CF CL K₀ εF εΛ : ℝ}
    (hFv : ∀ z, F z ≠ 0 → |trRe z.1| ≤ Rχ ∧ |trRe z.2.2| ≤ Rχ)
    (hCT : ∀ J ∈ jSet (K := K) b m, trRe J ≤ CT) (hRR : Rχ + CT < R) (hR0 : 0 ≤ R)
    (hCJ0 : 0 ≤ CJ) (hBA0 : 0 ≤ BA) (hCA0 : 0 ≤ CA) (hCa0 : 0 ≤ Ca) (hCr0 : 0 ≤ Crest)
    (hCΓ0 : 0 ≤ CΓ) (hCL0 : 0 ≤ CL) (hK0 : 0 ≤ K₀) (hεF : 0 ≤ εF) (hεΛ : 0 ≤ εΛ)
    (hCJ : ∀ J ∈ jSet (K := K) b m, ∀ e, ‖gramEntry e J‖ ≤ CJ)
    (hBA : ∀ y, FeasPath b E s h τ m W V y → ∀ v ≤ t, ∀ e,
      ‖genA χ b E s τ m (pG b E s h τ m W V) e v y‖ ≤ BA)
    (hCA : ∀ e : GIdx K np, ∀ J ∈ jSet (K := K) b m, ∀ H : GSt K np,
      GramFeasible (srcSignature K (Fin np)) H → ‖lamA χ b E e (J, H - J)‖ ≤ CA)
    (hC : ∀ (J y' : GSt K np) (z : ZSt K np) (ℓ : ℝ),
      0 ≤ ℓ → (∀ e, ‖z.2.1 e‖ ≤ max (2 * (2 * R + CJ) + BA) CA) →
      (∀ e, ‖lamA χ b E e (J, z.1)‖ ≤ max (2 * (2 * R + CJ) + BA) CA) →
      ∑ k, dlt z.1 y' (0, k, k) = ((trRe y' - trRe z.1 : ℝ) : ℂ) →
      ‖F (nextZ χ b E J y' ℓ z) - F z - (td.a0 (J, z, ℓ) + ip1 (td.a1 (J, z, ℓ)) (dlt z.1 y') +
          ip2 (td.a2 (J, z, ℓ)) (sq2 (dlt z.1 y')))‖ ≤
        Crest * ((∑ c, ‖dlt z.1 y' c‖ + ℓ * max (2 * (2 * R + CJ) + BA) CA) ^ 3 +
          (∑ c, ‖dlt z.1 y' c‖ + ℓ * max (2 * (2 * R + CJ) + BA) CA) ^ 4))
    (hCa1 : ∀ c, ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ∀ ℓ ∈ Icc (0 : ℝ) 1, ‖td.a1 (J, z, ℓ) c‖ ≤ Ca)
    (hCa2 : ∀ c c', ∀ J ∈ jSet (K := K) b m,
      ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ∀ ℓ ∈ Icc (0 : ℝ) 1, ‖td.a2 (J, z, ℓ) c c'‖ ≤ Ca)
    (hCΓ : ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ‖td.Γ (J, z)‖ ≤ CΓ)
    (hUC : ∀ J ∈ jSet (K := K) b m, ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA),
      ∀ ξ : GIdx K np → ℂ, (∀ e, ‖ξ e‖ ≤ (W : ℝ)⁻¹ * max (2 * (2 * R + CJ) + BA) CA) →
        ‖Λ (J, (z.1, fun e => z.2.1 e - ξ e, z.2.2)) - Λ (J, z)‖ ≤ εΛ)
    (hCβ : ∀ G : GSt K np, GramFeasible (srcSignature K (Fin np)) G → trRe G < R →
      ∀ c c' : GIdx K np, ‖cDrift b E (Sum.inl c : CIdx K np) G‖ ≤ Cβ ∧
        ‖cCov b E (Sum.inl c : CIdx K np) (Sum.inl c') G‖ ≤ Cβ)
    (hCH : ∀ y, FeasPath b E s h τ m W V y → ∀ v ≤ t, ‖pM χ b E s h τ m W V F Λ v y‖ ≤ CH)
    (hCF : ∀ y, FeasPath b E s h τ m W V y → ∀ v ≤ t,
      ‖F (stZ χ b E s τ m (pG b E s h τ m W V) v y)‖ ≤ CF ∧
        ‖F (zHat χ b E s h τ m W V v y)‖ ≤ CF)
    (hCL : ∀ y, FeasPath b E s h τ m W V y → ∀ r ∈ Ioc (0 : ℝ) t,
      ‖lInt χ b E s h τ m W V Λ y r‖ ≤ CL)
    (hFc : ∀ z ∈ kBox (K := K) (np := np) (2 * (2 * R + CJ) + BA), ∀ z' : ZSt K np,
      ‖F z‖ ≤ CF → ‖F z'‖ ≤ CF → ‖F z' - F z‖ ≤ εF + K₀ * eDist z' z)
    (h4 : ∀ j ∈ nbSteps s T τ W, ∀ c : GIdx K np, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
      (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np < ⊤) :
    ‖pStopSum χ b E s h τ m W V F Λ R i u φ a t‖ₑ ≤
      ENNReal.ofReal (‖φ‖ * Ca) *
          (∑ c : GIdx K np, b3SummedErr b E s T h τ m R W V (Sum.inl c) (Sum.inl c) +
            ∑ c : GIdx K np, ∑ c' : GIdx K np,
              b3SummedErr b E s T h τ m R W V (Sum.inl c) (Sum.inl c')) +
        (ENNReal.ofReal (4 * ‖φ‖ * Crest * (Fintype.card (GIdx K np) : ℝ) ^ 2) *
            ∑ c : GIdx K np, ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
              (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np +
          ENNReal.ofReal (8 * ‖φ‖ * Crest * (Fintype.card (GIdx K np) : ℝ) ^ 3) *
            ∑ c : GIdx K np, b3LindebergErr b E s T h τ m R W V (Sum.inl c) +
          ENNReal.ofReal (W * (t + 2) * (‖φ‖ * (Crest * (4 * ((W : ℝ)⁻¹ *
            max (2 * (2 * R + CJ) + BA) CA) ^ 3 + 8 * ((W : ℝ)⁻¹ *
              max (2 * (2 * R + CJ) + BA) CA) ^ 4) + ((W : ℝ)⁻¹ ^ 2 * CΓ +
                (W : ℝ)⁻¹ * εΛ))))) +
        (ENNReal.ofReal ((np + 2) * (‖φ‖ * (εF + K₀ * ((Fintype.card (GIdx K np) : ℝ) * CA *
            (W : ℝ)⁻¹) + CL * (W : ℝ)⁻¹))) +
          ENNReal.ofReal (2 * ‖φ‖ * K₀) * ∑ c : GIdx K np,
            ((∫⁻ y, (b3Alive b E s h τ m R W (limLenAll s W a) V).indicator (fun y =>
              ‖b3dX b E s h τ m W (limLenAll s W a) V (Sum.inl c) y‖ₑ) y ∂closedLaw b W np) +
              b3SummedErr b E s T h τ m R W V (Sum.inl c) (Sum.inl c))) := by
  classical
  set p := limLenAll s W a
  set q := limLenAll s W t
  set Φ := ‖φ‖
  set N : ℝ := (Fintype.card (GIdx K np) : ℝ)
  set w : ℝ := (W : ℝ)⁻¹
  set B₁ := 2 * (2 * R + CJ) + BA
  set B := max B₁ CA
  have hΦ : 0 ≤ Φ := norm_nonneg _
  have hw0 : 0 ≤ w := by positivity
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hV : Measurable V := hVg.mono (BlockBand.Transmission.Generator.growthSigma_le W _) le_rfl
  have hpq : p ≤ q := Nat.floor_mono (mul_le_mul_of_nonneg_left (by
    have : (a : ℝ) ≤ t := hat
    linarith) (Nat.cast_nonneg W))
  have hcp : closeLen s W ≤ p := closeLen_le_limLenAll (s := s) (W := W) a
  have hqT := limLenAll_lt_floor hs hW hT
  have hint := fun j => integrable_D_Dh (R := R) (i := i) (u := u) (φ := φ) hb hE1 hE2 hVg hχ hF
    hΛ hat hCH hCF hfe j
  rw [pStopSum_eq hs hτ hW hat hnbp hnbq hFv hCT hRR (fun j => (hint j).1)
    (fun j => (hint j).2.2)]
  refine (enorm_sum_le _ _).trans ?_
  set P : ℕ → Prop := fun j => p < j ∧ j + 1 ≤ q ∧ ¬ IsBirthStep τ W j
  rw [← Finset.sum_filter_add_sum_filter_not _ P]
  set Gs := (Finset.Ico p (q + 1)).filter P
  set Ss := (Finset.Ico p (q + 1)).filter fun j => ¬ P j
  have hGsub : Gs ⊆ nbSteps s T τ W := fun j hj => by
    obtain ⟨-, hpj, hjq, hnb⟩ := Finset.mem_filter.1 hj
    exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, by omega⟩, hnb⟩
  -- the generic cells
  have hGen := sum_generic_le Gs
    (fun j => ‖∫ y, (b3Alive b E s h τ m R W j V).indicator (fun y =>
      (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y) y
        ∂closedLaw b W np‖ₑ)
    (fun j c => ∫⁻ y, ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j V).indicator
        (b3dX b E s h τ m W j V (Sum.inl c)) | b3Sigma W j np] y -
      (W : ℂ)⁻¹ * cDrift b E (Sum.inl c) (b3ClosedGramAt b E s h τ m W j V y)) y‖ₑ
        ∂closedLaw b W np)
    (fun j c c' => ∫⁻ y, ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
      (closedLaw b W np)[(b3Alive b E s h τ m R W j V).indicator (fun y =>
        b3dX b E s h τ m W j V (Sum.inl c) y * b3dX b E s h τ m W j V (Sum.inl c') y) |
          b3Sigma W j np] y -
      (W : ℂ)⁻¹ * cCov b E (Sum.inl c) (Sum.inl c') (b3ClosedGramAt b E s h τ m W j V y)) y‖ₑ
        ∂closedLaw b W np)
    (fun j c => ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
      (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np)
    (fun j c => ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
      (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 4) y ∂closedLaw b W np)
    (fun c => b3SummedErr b E s T h τ m R W V (Sum.inl c) (Sum.inl c))
    (fun c c' => b3SummedErr b E s T h τ m R W V (Sum.inl c) (Sum.inl c'))
    (fun c => ∑ j ∈ nbSteps s T τ W, ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
      (fun y => ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ₑ ^ 3) y ∂closedLaw b W np)
    (fun c => b3LindebergErr b E s T h τ m R W V (Sum.inl c))
    (ENNReal.ofReal (Φ * Ca)) (ENNReal.ofReal (4 * Φ * Crest * N ^ 2))
    (ENNReal.ofReal (8 * Φ * Crest * N ^ 3))
    (ENNReal.ofReal (Φ * (Crest * (4 * (w * B) ^ 3 + 8 * (w * B) ^ 4) + (w ^ 2 * CΓ + w * εΛ))))
    (fun j hj => by
      obtain ⟨-, hpj, hjq, hnb⟩ := Finset.mem_filter.1 hj
      have gs := genStep (i := i) (u := u) (φ := φ) hCE td hb hE1 hE2 hs hτ hW hVg hχ hΛ hu hpj
        hjq hnb hfe hR0 hCJ0 hBA0 hCa0 hCJ
        (fun y hy e => hBA y hy _ (cellT_le s W hat j) e) hCA hC hCa1 hCa2 hCΓ hUC hCβ
        (h4 j (hGsub hj)) (hint j).2.1
      refine gs.trans (add_le_add le_rfl ?_)
      have hA' := measurableSet_b3AliveM b E s h τ m R W j hV
      have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j V
      have e : (fun y => ENNReal.ofReal (‖φ‖ *
          (Crest * ((∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ +
              (W : ℝ)⁻¹ * max (2 * (2 * R + CJ) + BA) CA) ^ 3 +
            (∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ +
              (W : ℝ)⁻¹ * max (2 * (2 * R + CJ) + BA) CA) ^ 4) +
            (W : ℝ)⁻¹ ^ 2 * CΓ + (W : ℝ)⁻¹ * εΛ))) =
          fun y => ENNReal.ofReal (Φ * (Crest * ((∑ c : GIdx K np,
            ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ + w * B) ^ 3 +
            (∑ c : GIdx K np, ‖b3dX b E s h τ m W j V (Sum.inl c) y‖ + w * B) ^ 4) +
            (w ^ 2 * CΓ + w * εΛ))) := by
        funext y; rw [add_assoc]
      rw [e]
      exact lint_rest_le hA' hAA (fun c => measurable_b3dX hV (Sum.inl c)) hΦ hCr0
        (by positivity) (by positivity))
    (fun c => sum_drift_le hGsub (Sum.inl c) (Sum.inl c))
    (fun c c' => sum_bracket_le hGsub (Sum.inl c) (Sum.inl c'))
    (fun c => sum_cube_le hGsub c) (fun c => sum_lind_le hGsub (Sum.inl c))
  -- the special cells
  set Bs := (Finset.Ico (closeLen s W) ⌊(W : ℝ) * T⌋₊).filter (fun j => IsBirthStep τ W j)
  have hSpec := sum_special_le Ss
    (fun j => ‖∫ y, (b3Alive b E s h τ m R W j V).indicator (fun y =>
      (pTest b E s h τ m W V i u φ y : ℂ) * Dh χ b E s h τ m W V F Λ a t j y) y
        ∂closedLaw b W np‖ₑ)
    (fun j c => ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
      (fun y => ‖dYh b E s h τ m W V a t j c y‖ₑ) y ∂closedLaw b W np)
    (fun c => ∫⁻ y, (b3Alive b E s h τ m R W p V).indicator (fun y =>
      ‖b3dX b E s h τ m W p V (Sum.inl c) y‖ₑ) y ∂closedLaw b W np)
    (fun j c => ∫⁻ y, ‖(b3Alive b E s h τ m R W j V).indicator (fun y =>
      b3dX b E s h τ m W j V (Sum.inl c) y -
        cEntry (Sum.inl c) (b3BirthAt b τ m W j) (b3KBirthAt E τ m W j)) y‖ₑ ∂closedLaw b W np)
    Bs p (fun c => b3SummedErr b E s T h τ m R W V (Sum.inl c) (Sum.inl c))
    (ENNReal.ofReal (2 * Φ * K₀)) (ENNReal.ofReal (Φ * (εF + K₀ * (N * CA * w) + CL * w)))
    (fun j hj => by
      obtain ⟨hjI, -⟩ := Finset.mem_filter.1 hj
      obtain ⟨hpj, hjq⟩ := Finset.mem_Ico.1 hjI
      have hjq' : j ≤ q := Nat.lt_succ_iff.1 hjq
      have hLj : limLenAll s W (cellT s W a t j) = j := limLenAll_cellT hs hW hpj hjq'
      have hA' := measurableSet_b3AliveM b E s h τ m R W j hV
      have hAA := b3Alive_ae_eq hb hE1 hE2 s h τ m R W j V
      refine (crudeStep (φ := φ) j (X := fun y => εF + K₀ * (2 * ∑ c,
        ‖dYh b E s h τ m W V a t j c y‖ + N * CA * w) + CL * w) ?_).trans ?_
      · filter_upwards [hfe] with y hy hA
        have hfy := hy hA.1
        have hz := zHat_mem_kBox hR0 hCJ0 hBA0 hCJ hfy hA (le_of_eq hLj)
          (hBA y hfy _ (cellT_le s W hat j))
        have hc := crude_pt (a := a) (t := t) hV hχ hΛ j y (ε := εF) (K₀ := K₀) hCL0
          (hFc _ hz _ (hCF y hfy _ (cellT_le s W hat j)).2
            (hCF y hfy _ (cellT_le s W hat (j + 1))).2)
          (fun r hr => hCL y hfy r ⟨lt_of_le_of_lt (cellT s W a t j).2 hr.1,
            hr.2.trans (cellT_le s W hat (j + 1))⟩)
        have hed := eDist_zHat_le (χ := χ) (b := b) (E := E) (s := s) (h := h) (τ := τ) (m := m)
          (V := V) y (cellT s W a t j) (cellT s W a t (j + 1))
        have hA2 : ∑ e : GIdx K np, ‖genA χ b E s τ m (pG b E s h τ m W V) e
            (cellT s W a t (j + 1)) y - genA χ b E s τ m (pG b E s h τ m W V) e
              (cellT s W a t j) y‖ ≤ N * CA * w := by
          have hle : ∀ e : GIdx K np, ‖genA χ b E s τ m (pG b E s h τ m W V) e
              (cellT s W a t (j + 1)) y - genA χ b E s τ m (pG b E s h τ m W V) e
                (cellT s W a t j) y‖ ≤ CA * w := fun e =>
            (norm_genA_sub_le hV hχ hCA hfy e (cellT_mono s W a t (Nat.le_succ j))).trans
              (mul_le_mul_of_nonneg_left (by
                have := cellT_succ_sub_le s W a t j
                rwa [one_div] at this) hCA0)
          have := Finset.sum_le_card_nsmul (Finset.univ : Finset (GIdx K np)) _ (CA * w)
            fun e _ => hle e
          rw [Finset.card_univ, nsmul_eq_mul] at this
          linarith
        have hdY : ∀ c, dYh b E s h τ m W V a t j c y =
            gramEntry c (yHat b E s h τ m W (limLenAll s W (cellT s W a t (j + 1))) V y) -
              gramEntry c (yHat b E s h τ m W (limLenAll s W (cellT s W a t j)) V y) :=
          fun c => rfl
        simp only [← hdY] at hed
        calc ‖Dh χ b E s h τ m W V F Λ a t j y‖ ≤ εF + K₀ *
            eDist (zHat χ b E s h τ m W V (cellT s W a t (j + 1)) y)
              (zHat χ b E s h τ m W V (cellT s W a t j) y) + CL * w := hc
          _ ≤ _ := by gcongr; linarith
      · exact lint_crude_le hA' hAA (fun c => measurable_dYh hV j c) hΦ hεF hK0
          (by positivity) (by positivity))
    (fun j hj c => by
      obtain ⟨hjI, hnP⟩ := Finset.mem_filter.1 hj
      obtain ⟨hpj, hjq⟩ := Finset.mem_Ico.1 hjI
      have hjq' : j ≤ q := Nat.lt_succ_iff.1 hjq
      have hcs := dYh_cases (b := b) (E := E) (h := h) (τ := τ) (m := m) (V := V) hs hW hat hpj
        hjq' c
      by_cases hjq0 : j = q
      · have : ∫⁻ y, (b3Alive b E s h τ m R W j V).indicator
            (fun y => ‖dYh b E s h τ m W V a t j c y‖ₑ) y ∂closedLaw b W np = 0 := by
          refine lintegral_eq_zero_of_ae_eq_zero (ae_of_all _ fun y => ?_)
          by_cases hA : y ∈ b3Alive b E s h τ m R W j V
          · simp [Set.indicator_of_mem hA, (hcs y).1 hjq0]
          · simp [Set.indicator_of_notMem hA]
        rw [this]; exact zero_le
      have hj1 : j + 1 ≤ q := by omega
      by_cases hbj : IsBirthStep τ W j
      · have hjB : j ∈ Bs :=
          Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hcp.trans hpj, by omega⟩, hbj⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hjB)]
        refine le_add_left (le_of_eq (lintegral_congr fun y => ?_))
        rw [enorm_indicator_eq_indicator_enorm]
        by_cases hA : y ∈ b3Alive b E s h τ m R W j V
        · simp only [Set.indicator_of_mem hA, (hcs y).2 hj1, cEntry]
        · simp only [Set.indicator_of_notMem hA]
      · have hjp : j = p := by
          by_contra hne
          exact hnP ⟨lt_of_le_of_ne hpj (Ne.symm hne), hj1, hbj⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hjp)]
        refine le_add_right (le_of_eq (lintegral_congr fun y => ?_))
        subst hjp
        by_cases hA : y ∈ b3Alive b E s h τ m R W p V
        · have hz0 : gramEntry c (0 : GSt K np) = 0 := by unfold gramEntry; split_ifs <;> rfl
          simp only [Set.indicator_of_mem hA, (hcs y).2 hj1, b3BirthAt_eq_zero b hbj, hz0,
            sub_zero]
        · simp only [Set.indicator_of_notMem hA])
    (fun c => sum_birth_le (G := Bs) subset_rfl (Sum.inl c) (Sum.inl c))
  -- the counts
  have hcG : (Gs.card : ℝ) ≤ W * (t + 2) :=
    (Nat.cast_le.2 (Finset.card_le_card (Finset.filter_subset _ _))).trans (card_Ico_le hs hW hat)
  have hcS : (Ss.card : ℝ) ≤ np + 2 := by
    have hsub : Ss ⊆
        insert p (insert q (Finset.univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊)) := by
      intro j hj
      obtain ⟨hjI, hnP⟩ := Finset.mem_filter.1 hj
      obtain ⟨hpj, hjq⟩ := Finset.mem_Ico.1 hjI
      rcases eq_or_lt_of_le hpj with h1 | h1
      · exact Finset.mem_insert.2 (Or.inl h1.symm)
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.1 hjq) with h2 | h2
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.2 (Or.inl h2))
      have hb' : IsBirthStep τ W j := by
        by_contra hb'; exact hnP ⟨h1, by omega, hb'⟩
      obtain ⟨i0, hi0⟩ := hb'
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.2 ⟨i0, Finset.mem_univ _, hi0⟩))
    have hc1 : (Finset.univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊).card ≤ np :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    have hc2 : (insert p (insert q (Finset.univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊))).card ≤
        np + 2 := by
      have h1 := Finset.card_insert_le p
        (insert q (Finset.univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊))
      have h2 := Finset.card_insert_le q (Finset.univ.image fun i : Fin np => ⌊(W : ℝ) * τ i⌋₊)
      omega
    have h3 : Ss.card ≤ np + 2 := (Finset.card_le_card hsub).trans hc2
    exact_mod_cast h3
  have hK1 : 0 ≤ Φ * (Crest * (4 * (w * B) ^ 3 + 8 * (w * B) ^ 4) + (w ^ 2 * CΓ + w * εΛ)) := by
    positivity
  have hK2 : 0 ≤ Φ * (εF + K₀ * (N * CA * w) + CL * w) := by positivity
  have hD1 : (Gs.card : ℝ≥0∞) * ENNReal.ofReal (Φ * (Crest * (4 * (w * B) ^ 3 + 8 * (w * B) ^ 4) +
      (w ^ 2 * CΓ + w * εΛ))) ≤ ENNReal.ofReal (W * (t + 2) * (Φ * (Crest * (4 * (w * B) ^ 3 +
        8 * (w * B) ^ 4) + (w ^ 2 * CΓ + w * εΛ)))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcG hK1)
  have hD2 : (Ss.card : ℝ≥0∞) * ENNReal.ofReal (Φ * (εF + K₀ * (N * CA * w) + CL * w)) ≤
      ENNReal.ofReal ((np + 2) * (Φ * (εF + K₀ * (N * CA * w) + CL * w))) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcS hK2)
  refine (add_le_add hGen hSpec).trans ?_
  gcongr

end Fix

end BlockBand.SourceProcess.PhysApprox.B3.IdentGram.Local
