module

public import BlockBand.Native.ErdosRiabov.Prop.ThetaReg
public import BlockBand.Native.ErdosRiabov.Prop.Actions

/-!
# One-step regularized action

Setting: VS data `d`, `m ≥ 4`, `W ≥ 1`, `N = mW`, `S = shortRingProfile d.b m W`, `z ∈ 𝒟`,
`Θ̊^p_t = vsThetaRing S m (conj m) t p`, `η_r = vsHeight z r`, `Υ_r`, `ℓ_r = ℓ(η_r)`,
`L_r = ℓ_r η_r`, `0 ≤ s ≤ t ≤ 1`, `r ∈ {s, t}`, sites `p = x_{k-1}`, `u = x_k`, `q = x_{k+1}`,
`f(b) = √(Υ_s(p,b) Υ_r(b,q))`. Constant `C_reg = 2 C_K (C₁'')^{7/2} (1 + C_K/c_m)`
(`onestepConst d`, with `(C₁'')^{7/2}` written `(C₁'')³ √C₁''`).

Deterministic: no measure occurs. The parity hypothesis "`k ≥ 2` even" plays no role in the estimate and is not assumed.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.LemmaK
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open scoped BigOperators ComplexConjugate

/-- `C_reg = 2 C_K (C₁'')³ √C₁'' (1 + C_K/c_m)`. -/
def onestepConst (d : VSData) : ℝ :=
  2 * vsCK d * (d.C1pp ^ 3 * Real.sqrt d.C1pp) * (1 + vsCK d / d.cm)

/-- The right-hand side scale `η_s⁻¹ (ℓ_s ℓ_t η_t/W²) √(L_s/L_r) √(Υ_t(p,u) Υ_t(u,q))`. -/
def onestepScale (d : VSData) (m W : ℕ) (z : ℂ) (s t r : ℝ) (p u q : Fin (m * W)) : ℝ :=
  1 / vsHeight z s *
    (ErdosRiabov.localizationLength (m * W) W (vsHeight z s) *
      ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t / (W : ℝ) ^ 2) *
    Real.sqrt ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) /
      (ErdosRiabov.localizationLength (m * W) W (vsHeight z r) * vsHeight z r)) *
    Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) p u *
      polynomialControl (m * W) W d.D (vsHeight z t) u q)

theorem onestepScale_nonneg (d : VSData) (m W : ℕ) (z : ℂ) {s t r : ℝ}
    (hs : 0 < vsHeight z s) (ht : 0 < vsHeight z t) (p u q : Fin (m * W)) :
    0 ≤ onestepScale d m W z s t r p u q := by
  unfold onestepScale
  have h1 : 0 ≤ ErdosRiabov.localizationLength (m * W) W (vsHeight z s) :=
    le_min (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  have h2 : 0 ≤ ErdosRiabov.localizationLength (m * W) W (vsHeight z t) :=
    le_min (div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (Nat.cast_nonneg _)
  positivity

/-- `√(a b) ≤ (C/L_s) √(L_s/L_r)` if `0 ≤ a ≤ C/L_s`, `0 ≤ b ≤ C/L_r`. -/
private theorem onestep_sqrt_le {a b C Ls Lr : ℝ} (hb0 : 0 ≤ b) (hC : 0 ≤ C) (hLs : 0 < Ls)
    (hLr : 0 < Lr) (ha : a ≤ C / Ls) (hb : b ≤ C / Lr) :
    Real.sqrt (a * b) ≤ C / Ls * Real.sqrt (Ls / Lr) := by
  have hcs : 0 ≤ C / Ls := div_nonneg hC hLs.le
  calc Real.sqrt (a * b) ≤ Real.sqrt (C / Ls * (C / Lr)) :=
        Real.sqrt_le_sqrt (mul_le_mul ha hb hb0 hcs)
    _ = Real.sqrt (C / Ls * (C / Ls) * (Ls / Lr)) := by
        congr 1
        field_simp
    _ = C / Ls * Real.sqrt (Ls / Lr) := by
        rw [Real.sqrt_mul (mul_self_nonneg _), Real.sqrt_mul_self hcs]

/-- `λ ≤ √(x y)` if `λ ≤ x`, `λ ≤ y`, `λ ≥ 0`. -/
private theorem onestep_le_sqrt {l x y : ℝ} (hl : 0 ≤ l) (hx : l ≤ x) (hy : l ≤ y) :
    l ≤ Real.sqrt (x * y) := by
  rw [← Real.sqrt_mul_self hl]
  exact Real.sqrt_le_sqrt (mul_le_mul hx hy hl (hl.trans hx))

section Cases

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z) {s t r : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
  (ht1 : t ≤ 1) (hr : r = s ∨ r = t) (p u q : Fin (m * W))
include hm hW hz hs0 hst ht1 hr

/-- Case (1), `η♭ ≤ η_t` (ER Case 1): constant `2 C_K (C₁'')^{3/2}`. -/
private theorem onestep_case1 (h1 : etaFlat (m * W) W ≤ vsHeight z t) :
    ∑ b, ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t p u b‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      2 * vsCK d * (d.C1pp * Real.sqrt d.C1pp) * onestepScale d m W z s t r p u q := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have ht0 : 0 ≤ t := hs0.trans hst
  have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
  have hrt : r ≤ t := by rcases hr with h | h <;> linarith
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hηt := vsHeight_pos hη ht1
  have hηr := vsHeight_pos hη (hrt.trans ht1)
  have hreg := vsThetaRing_K2 d hm hW hz ht0 ht1 (Or.inl h1) p u
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hU8, -, -⟩ := ups_U2_U8_vs d hm hW hz hs0 hst ht1
  obtain ⟨-, -, -, -, -, -, hU4rt, -, -, -, -, -, -⟩ := ups_U2_U8_vs d hm hW hz hr0 hrt ht1
  obtain ⟨-, -, -, -, -, -, hU4tt, -, -, -, -, -, -⟩ := ups_U2_U8_vs d hm hW hz ht0 le_rfl ht1
  have hE1 := hU8 t (Or.inr rfl) p u
  have hE2 := hU8 r hr p q
  have hsq := (loc_sq_mul hN hηt).2.mpr h1
  have hpos : ∀ h : ℝ, 0 < h → ∀ x y, 0 ≤ polynomialControl (m * W) W d.D h x y :=
    fun h hh x y => (polynomialControl_pos hN hW d.D hh x y).le
  have hsym : ∀ h : ℝ, ∀ x y, polynomialControl (m * W) W d.D h x y =
      polynomialControl (m * W) W d.D h y x := fun h x y => polynomialControl_symm _ _ _ h x y
  have hls := loc_pos hN hW hηs
  have hlt := loc_pos hN hW hηt
  have hlr := loc_pos hN hW hηr
  unfold onestepScale
  set Ys := polynomialControl (m * W) W d.D (vsHeight z s) with hYs
  set Yt := polynomialControl (m * W) W d.D (vsHeight z t) with hYt
  set Yr := polynomialControl (m * W) W d.D (vsHeight z r) with hYr
  set ls := ErdosRiabov.localizationLength (m * W) W (vsHeight z s) with hlsd
  set lt := ErdosRiabov.localizationLength (m * W) W (vsHeight z t) with hltd
  set lr := ErdosRiabov.localizationLength (m * W) W (vsHeight z r) with hlrd
  set C1 := d.C1pp with hC1d
  set CK := vsCK d with hCKd
  have hC1 : 0 < C1 := lt_of_lt_of_le one_pos d.one_le_C1pp
  have hCK : 0 < CK := vsCK_pos d
  have hLs : 0 < ls * vsHeight z s := mul_pos hls hηs
  have hLt : 0 < lt * vsHeight z t := mul_pos hlt hηt
  have hLr : 0 < lr * vsHeight z r := mul_pos hlr hηr
  have hYs0 : ∀ x y, 0 ≤ Ys x y := hpos _ hηs
  have hYt0 : ∀ x y, 0 ≤ Yt x y := hpos _ hηt
  have hYr0 : ∀ x y, 0 ≤ Yr x y := hpos _ hηr
  have hsT : ∀ x y, Yt x y = Yt y x := fun x y => polynomialControl_symm _ _ _ _ x y
  have hsR : ∀ x y, Yr x y = Yr y x := fun x y => polynomialControl_symm _ _ _ _ x y
  set M1 := Real.sqrt (C1 / (lr * vsHeight z r) * Yt q u) with hM1
  have hw : ∀ b : Fin (m * W),
      0 ≤ min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt := fun b =>
    div_nonneg (le_min (by positivity) hlt.le) hlt.le
  -- pointwise bound
  have hb : ∀ b, ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z))
        t p u b‖ * Real.sqrt (Ys p b * Yr b q) ≤
      CK * (M1 * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
          Real.sqrt (Ys p b * Yt b u)) +
        Yt u p * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
          Real.sqrt (Ys p b * Yr b q))) := by
    intro b
    have hid : Yt u b * Real.sqrt (Ys p b * Yr b q) =
        Real.sqrt (Ys p b * Yt b u) * Real.sqrt (Yr q b * Yt b u) := by
      rw [← Real.sqrt_mul (mul_nonneg (hYs0 p b) (hYt0 b u)), hsT b u, hsR q b,
        show Ys p b * Yt u b * (Yr b q * Yt u b) = Ys p b * Yr b q * Yt u b * Yt u b by ring,
        prop_sqrt_mul_sq _ _ (hYt0 u b)]
    have hM : Real.sqrt (Yr q b * Yt b u) ≤ M1 := Real.sqrt_le_sqrt ((hU4rt q u).1 b)
    have hf0 := Real.sqrt_nonneg (Ys p b * Yr b q)
    have hg0 := Real.sqrt_nonneg (Ys p b * Yt b u)
    have hwb := hw b
    calc _ ≤ CK * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt) *
            (Yt u b + Yt u p) * Real.sqrt (Ys p b * Yr b q) :=
          mul_le_mul_of_nonneg_right (hreg b) hf0
      _ = CK * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
            (Yt u b * Real.sqrt (Ys p b * Yr b q)) +
          Yt u p * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
            Real.sqrt (Ys p b * Yr b q))) := by ring
      _ ≤ _ := by
          rw [hid]
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hCK.le
          calc min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
                (Real.sqrt (Ys p b * Yt b u) * Real.sqrt (Yr q b * Yt b u))
              ≤ min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
                (Real.sqrt (Ys p b * Yt b u) * M1) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hM hg0) hwb
            _ = _ := by ring
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hb b
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  refine hsum.trans ?_
  -- algebra
  set P := Yt p u * Yt u q with hP
  have hA1 : M1 * Real.sqrt (ls * vsHeight z s / (lt * vsHeight z t)) *
      Real.sqrt (lt * vsHeight z t * Yt p u) =
      Real.sqrt C1 * Real.sqrt (ls * vsHeight z s / (lr * vsHeight z r)) * Real.sqrt P := by
    rw [hM1, ← Real.sqrt_mul (mul_nonneg (div_nonneg hC1.le hLr.le) (hYt0 q u)),
      ← Real.sqrt_mul (mul_nonneg (mul_nonneg (div_nonneg hC1.le hLr.le) (hYt0 q u))
        (div_nonneg hLs.le hLt.le)),
      ← Real.sqrt_mul hC1.le, ← Real.sqrt_mul (mul_nonneg hC1.le (div_nonneg hLs.le hLr.le)),
      hP, hsT q u]
    congr 1
    field_simp
  have hA2 : Yt u p * Real.sqrt (lt * vsHeight z t * Yt p q) ≤ Real.sqrt C1 * Real.sqrt P := by
    have htri := (hU4tt u q).1 p
    have hup := hYt0 u p
    rw [← Real.sqrt_mul_self hup, ← Real.sqrt_mul (mul_self_nonneg _), ← Real.sqrt_mul hC1.le]
    refine Real.sqrt_le_sqrt ?_
    rw [hP, hsT p u]
    have h3 : lt * vsHeight z t * (Yt u p * Yt p q) ≤ C1 * Yt u q := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hLt] at htri
      linarith
    nlinarith
  have hE1' := mul_le_mul_of_nonneg_left hE1 (Real.sqrt_nonneg
    (C1 / (lr * vsHeight z r) * Yt q u))
  have hE2' := mul_le_mul_of_nonneg_left hE2 (hYt0 u p)
  have hratio : ls / lt = ls * lt * vsHeight z t / (W : ℝ) ^ 2 := by
    rw [← hsq]
    field_simp
  have hfac : 0 ≤ C1 / vsHeight z s * (ls / lt) := by positivity
  calc CK * (M1 * ∑ b, min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
          Real.sqrt (Ys p b * Yt b u) +
        Yt u p * ∑ b, min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lt / lt *
          Real.sqrt (Ys p b * Yr b q))
      ≤ CK * (M1 * (C1 / vsHeight z s * (ls / lt) *
            Real.sqrt (ls * vsHeight z s / (lt * vsHeight z t)) *
            Real.sqrt (lt * vsHeight z t * Yt p u)) +
          Yt u p * (C1 / vsHeight z s * (ls / lt) *
            Real.sqrt (ls * vsHeight z s / (lr * vsHeight z r)) *
            Real.sqrt (lt * vsHeight z t * Yt p q))) :=
        mul_le_mul_of_nonneg_left (add_le_add hE1' hE2') hCK.le
    _ = CK * (C1 / vsHeight z s * (ls / lt)) *
          (M1 * Real.sqrt (ls * vsHeight z s / (lt * vsHeight z t)) *
            Real.sqrt (lt * vsHeight z t * Yt p u) +
          Real.sqrt (ls * vsHeight z s / (lr * vsHeight z r)) *
            (Yt u p * Real.sqrt (lt * vsHeight z t * Yt p q))) := by ring
    _ ≤ CK * (C1 / vsHeight z s * (ls / lt)) *
          (Real.sqrt C1 * Real.sqrt (ls * vsHeight z s / (lr * vsHeight z r)) * Real.sqrt P +
          Real.sqrt (ls * vsHeight z s / (lr * vsHeight z r)) *
            (Real.sqrt C1 * Real.sqrt P)) := by
        rw [hA1]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hA2 (Real.sqrt_nonneg _))) (mul_nonneg hCK.le hfac)
    _ = _ := by rw [hratio]; ring

/-- Case (2a), `η_s ≤ η♭` (no anchor): constant `2 C_K (C₁'')²`. -/
private theorem onestep_case2a (h2 : vsHeight z s ≤ etaFlat (m * W) W) :
    ∑ b, ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t p u b‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      2 * vsCK d * d.C1pp ^ 2 * onestepScale d m W z s t r p u q := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have ht0 : 0 ≤ t := hs0.trans hst
  have hr0 : 0 ≤ r := by rcases hr with h | h <;> linarith
  have hrt : r ≤ t := by rcases hr with h | h <;> linarith
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hηt := vsHeight_pos hη ht1
  have hηr := vsHeight_pos hη (hrt.trans ht1)
  have hdec : ∀ a b : ℝ, a ≤ b → vsHeight z b ≤ vsHeight z a := fun a b hab => by
    rw [vsHeight_affine z a, vsHeight_affine z b]
    nlinarith [semicircleM_im_pos hη]
  have hsr : s ≤ r := by rcases hr with h | h <;> linarith
  have hrsm : vsHeight z r ≤ etaFlat (m * W) W := (hdec s r hsr).trans h2
  have htsm : vsHeight z t ≤ etaFlat (m * W) W := (hdec s t hst).trans h2
  have hlsN := loc_eq_N hN hηs h2
  have hltN := loc_eq_N hN hηt htsm
  have hlrN := loc_eq_N hN hηr hrsm
  have hK3 := (vsThetaRing_K3 d hm hW hz ht0 ht1).2.1 p u
  obtain ⟨hU2s, -⟩ := ups_U2_U8_vs d hm hW hz hs0 le_rfl (hst.trans ht1)
  obtain ⟨hU2r, -⟩ := ups_U2_U8_vs d hm hW hz hr0 le_rfl (hrt.trans ht1)
  obtain ⟨-, -, -, hU2t, -⟩ := ups_U2_U8_vs d hm hW hz ht0 le_rfl ht1
  have hlow := hU2t htsm
  unfold onestepScale
  set X := Real.sqrt ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) /
      (ErdosRiabov.localizationLength (m * W) W (vsHeight z r) * vsHeight z r)) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  set C1 := d.C1pp with hC1d
  set CK := vsCK d with hCKd
  have hC1 : 0 < C1 := lt_of_lt_of_le one_pos d.one_le_C1pp
  have hCK : 0 < CK := vsCK_pos d
  have hNr : (0 : ℝ) < ((m * W : ℕ) : ℝ) := by exact_mod_cast hN
  have hWr : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hf : ∀ b, Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
      polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      C1 / (((m * W : ℕ) : ℝ) * vsHeight z s) * X := by
    intro b
    have h := onestep_sqrt_le (polynomialControl_pos hN hW d.D hηr b q).le hC1.le
      (mul_pos (loc_pos hN hW hηs) hηs) (mul_pos (loc_pos hN hW hηr) hηr) (hU2s p b) (hU2r b q)
    rw [hlsN] at h
    rw [hX, hlsN]
    exact h
  have hsum : ∑ b, ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z)
        (conj (semicircleM z)) t p u b‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      ((m * W : ℕ) : ℝ) * (2 * CK * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 *
        (C1 / (((m * W : ℕ) : ℝ) * vsHeight z s) * X)) := by
    calc _ ≤ ∑ _b : Fin (m * W), 2 * CK * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 *
          (C1 / (((m * W : ℕ) : ℝ) * vsHeight z s) * X) :=
          Finset.sum_le_sum fun b _ => mul_le_mul (hK3 b) (hf b) (Real.sqrt_nonneg _)
            (by positivity)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine hsum.trans ?_
  set l := 1 / C1 * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) with hl
  have hl0 : 0 ≤ l := by positivity
  have hP := onestep_le_sqrt hl0 (hlow p u).1 (hlow u q).1
  rw [hlsN, hltN]
  have hcoef : 0 ≤ 2 * CK * C1 ^ 2 * (1 / vsHeight z s *
      (((m * W : ℕ) : ℝ) * ((m * W : ℕ) : ℝ) * vsHeight z t / (W : ℝ) ^ 2) * X) := by
    positivity
  calc ((m * W : ℕ) : ℝ) * (2 * CK * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 *
        (C1 / (((m * W : ℕ) : ℝ) * vsHeight z s) * X))
      = 2 * CK * C1 ^ 2 * (1 / vsHeight z s *
          (((m * W : ℕ) : ℝ) * ((m * W : ℕ) : ℝ) * vsHeight z t / (W : ℝ) ^ 2) * X) * l := by
        rw [hl]
        field_simp
    _ ≤ 2 * CK * C1 ^ 2 * (1 / vsHeight z s *
          (((m * W : ℕ) : ℝ) * ((m * W : ℕ) : ℝ) * vsHeight z t / (W : ℝ) ^ 2) * X) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) p u *
          polynomialControl (m * W) W d.D (vsHeight z t) u q) :=
        mul_le_mul_of_nonneg_left hP hcoef
    _ = _ := by ring

/-- Case (2b), `η_t < η♭ < η_s` (Erdős–Riabov's Case 2 at `τ = t♭ ∈ (s,t)`): constant
`C_reg`. -/
private theorem onestep_case2b
    (h2 : vsHeight z t < etaFlat (m * W) W ∧ etaFlat (m * W) W < vsHeight z s ∧
      s < anchorTime z (m * W) W ∧ anchorTime z (m * W) W < t ∧
      vsHeight z (anchorTime z (m * W) W) = etaFlat (m * W) W ∧
      ErdosRiabov.localizationLength (m * W) W (vsHeight z (anchorTime z (m * W) W)) =
        ((m * W : ℕ) : ℝ) ∧
      ErdosRiabov.localizationLength (m * W) W (vsHeight z (anchorTime z (m * W) W)) ^ 2 *
          vsHeight z (anchorTime z (m * W) W) = (W : ℝ) ^ 2 ∧
      ErdosRiabov.localizationLength (m * W) W (vsHeight z t) = ((m * W : ℕ) : ℝ)) :
    ∑ b, ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t p u b‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      onestepConst d * onestepScale d m W z s t r p u q := by
  obtain ⟨htf, hfs, hsτ, hτt, hητ, hlτ, hlτ2, hltN⟩ := h2
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have ht0 : 0 ≤ t := hs0.trans hst
  have hτ1 : anchorTime z (m * W) W ≤ 1 := hτt.le.trans ht1
  have hτ0 : 0 ≤ anchorTime z (m * W) W := hs0.trans hsτ.le
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hηt := vsHeight_pos hη ht1
  have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega : 3 ≤ m) hW
  obtain ⟨-, hd2, -, -, hd5, hd6, hd7⟩ :=
    anchor_decomp hS hN hW d.kappa_pos hz p hτt.le ht1
  obtain ⟨hK3t, -, hPit⟩ := vsThetaRing_K3 d hm hW hz ht0 ht1
  obtain ⟨hU2τ, -⟩ := ups_U2_U8_vs d hm hW hz hτ0 le_rfl hτ1
  obtain ⟨-, -, -, hU2t, -⟩ := ups_U2_U8_vs d hm hW hz ht0 le_rfl ht1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hU8, -, -⟩ :=
    ups_U2_U8_vs d hm hW hz hs0 hsτ.le hτ1
  have hregτ := vsThetaRing_K2 d hm hW hz hτ0 hτ1 (Or.inl hητ.ge) p
  set τ := anchorTime z (m * W) W with hτd
  have hητp := vsHeight_pos hη hτ1
  set S := shortRingProfile d.b m W with hSd
  set μ := semicircleM z with hμd
  set C1 := d.C1pp with hC1d
  set CK := vsCK d with hCKd
  set ls := ErdosRiabov.localizationLength (m * W) W (vsHeight z s) with hlsd
  set lτ := ErdosRiabov.localizationLength (m * W) W (vsHeight z τ) with hlτd
  set Ys := polynomialControl (m * W) W d.D (vsHeight z s) with hYs
  set Yτ := polynomialControl (m * W) W d.D (vsHeight z τ) with hYτ
  have hC1 : 0 < C1 := lt_of_lt_of_le one_pos d.one_le_C1pp
  have hCK : 0 < CK := vsCK_pos d
  have hcm := d.cm_pos
  have hNr : (0 : ℝ) < ((m * W : ℕ) : ℝ) := by exact_mod_cast hN
  have hWr : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hls := loc_pos hN hW hηs
  have hlτp : 0 < lτ := loc_pos hN hW hητp
  have hLs : 0 < ls * vsHeight z s := mul_pos hls hηs
  have hLτ : 0 < lτ * vsHeight z τ := mul_pos hlτp hητp
  have hYs0 : ∀ x y, 0 ≤ Ys x y := fun x y => (polynomialControl_pos hN hW d.D hηs x y).le
  have hYτ0 : ∀ x y, 0 ≤ Yτ x y := fun x y => (polynomialControl_pos hN hW d.D hητp x y).le
  set X := Real.sqrt (ls * vsHeight z s /
      (ErdosRiabov.localizationLength (m * W) W (vsHeight z r) * vsHeight z r)) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  -- Step 1: the weighted sum of `f`
  have hLτq : Real.sqrt (lτ * vsHeight z τ * Yτ p q) ≤ Real.sqrt C1 := by
    refine Real.sqrt_le_sqrt ?_
    have h := hU2τ p q
    rw [le_div_iff₀ hLτ] at h
    linarith
  have hW1 : ∑ b, min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ *
      Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      C1 * Real.sqrt C1 / vsHeight z s * (ls / lτ) * X := by
    rcases hr with rfl | rfl
    · refine (hU8 r (Or.inl rfl) p q).trans ?_
      have h0 : 0 ≤ C1 / vsHeight z r * (ls / lτ) * X := by positivity
      calc C1 / vsHeight z r * (ls / lτ) * X * Real.sqrt (lτ * vsHeight z τ * Yτ p q)
          ≤ C1 / vsHeight z r * (ls / lτ) * X * Real.sqrt C1 := mul_le_mul_of_nonneg_left hLτq h0
        _ = _ := by ring
    · have hprop : ∀ b, polynomialControl (m * W) W d.D (vsHeight z r) b q =
          vsHeight z τ / vsHeight z r * Yτ b q := fun b =>
        polynomialControl_deloc_prop_of_le d.D hητp hηt hητ.le htf.le b q
      have hc0 : 0 ≤ vsHeight z τ / vsHeight z r := by positivity
      have hfeq : ∀ b, Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) =
          Real.sqrt (vsHeight z τ / vsHeight z r) * Real.sqrt (Ys p b * Yτ b q) := fun b => by
        rw [hprop b, show Ys p b * (vsHeight z τ / vsHeight z r * Yτ b q) =
          vsHeight z τ / vsHeight z r * (Ys p b * Yτ b q) by ring, Real.sqrt_mul hc0]
      simp_rw [hfeq]
      have hE := hU8 τ (Or.inr rfl) p q
      calc ∑ b, min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ *
            (Real.sqrt (vsHeight z τ / vsHeight z r) * Real.sqrt (Ys p b * Yτ b q))
          = Real.sqrt (vsHeight z τ / vsHeight z r) *
              ∑ b, min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ *
                Real.sqrt (Ys p b * Yτ b q) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by ring
        _ ≤ Real.sqrt (vsHeight z τ / vsHeight z r) *
              (C1 / vsHeight z s * (ls / lτ) *
                Real.sqrt (ls * vsHeight z s / (lτ * vsHeight z τ)) * Real.sqrt C1) := by
            refine mul_le_mul_of_nonneg_left (hE.trans ?_) (Real.sqrt_nonneg _)
            exact mul_le_mul_of_nonneg_left hLτq (by positivity)
        _ = C1 * Real.sqrt C1 / vsHeight z s * (ls / lτ) *
              (Real.sqrt (vsHeight z τ / vsHeight z r) *
                Real.sqrt (ls * vsHeight z s / (lτ * vsHeight z τ))) := by ring
        _ = _ := by
            rw [← Real.sqrt_mul hc0, hX, hltN, hlτ]
            congr 2
            field_simp
  -- `B`: the bound at the anchor, uniform in the row
  set B := CK * (2 * C1 / (lτ * vsHeight z τ)) * (C1 * Real.sqrt C1 / vsHeight z s * (ls / lτ) * X)
    with hB
  have hrowB : ∀ c, ∑ b, ‖vsThetaRing S μ (conj μ) τ p c b‖ *
      Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤ B := by
    intro c
    have hpt : ∀ b, ‖vsThetaRing S μ (conj μ) τ p c b‖ ≤
        CK * (2 * C1 / (lτ * vsHeight z τ)) *
          (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ) := by
      intro b
      have hw : 0 ≤ min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ :=
        div_nonneg (le_min (by positivity) hlτp.le) hlτp.le
      refine (hregτ c b).trans ?_
      have h1 := hU2τ c b
      have h2 := hU2τ c p
      calc CK * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ) *
            (Yτ c b + Yτ c p)
          ≤ CK * (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ) *
            (C1 / (lτ * vsHeight z τ) + C1 / (lτ * vsHeight z τ)) :=
            mul_le_mul_of_nonneg_left (add_le_add h1 h2) (mul_nonneg hCK.le hw)
        _ = _ := by ring
    calc _ ≤ ∑ b, CK * (2 * C1 / (lτ * vsHeight z τ)) *
          (min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ *
            Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q)) :=
          Finset.sum_le_sum fun b _ => by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (hpt b) (Real.sqrt_nonneg _)
      _ = CK * (2 * C1 / (lτ * vsHeight z τ)) *
          ∑ b, min ((ErdosRiabov.cyclicDistance (m * W) b p : ℝ) + W) lτ / lτ *
            Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ B := mul_le_mul_of_nonneg_left hW1 (by positivity)
  have hB0 : 0 ≤ B := by positivity
  -- Step 2: the correction
  set κ0 : ℂ := (((μ).im / (((m * W : ℕ) : ℝ) * vsHeight z t) : ℝ) : ℂ) with hκ0
  have hentry : ∀ b, vsThetaRing S μ (conj μ) t p u b = vsThetaRing S μ (conj μ) τ p u b +
      ((t : ℂ) - τ) * ∑ c, (vsKernel S μ (conj μ) t u c - κ0) *
        vsThetaRing S μ (conj μ) τ p c b := by
    intro b
    rw [hd2]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.sub_apply, hPit]
  have htτ : 0 ≤ t - τ := by linarith
  set κ1 := CK * ((m * W : ℕ) : ℝ) / (W : ℝ) ^ 2 with hκ1
  have hpt2 : ∀ b, ‖vsThetaRing S μ (conj μ) t p u b‖ ≤ ‖vsThetaRing S μ (conj μ) τ p u b‖ +
      (t - τ) * ∑ c, κ1 * ‖vsThetaRing S μ (conj μ) τ p c b‖ := by
    intro b
    rw [hentry b]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul, show (t : ℂ) - τ = ((t - τ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg htτ]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun c _ => ?_)) htτ
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK3t u c) (norm_nonneg _)
  have hf0 : ∀ b, 0 ≤ Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) :=
    fun b => Real.sqrt_nonneg _
  have hstep3 : ∑ b, ‖vsThetaRing S μ (conj μ) t p u b‖ *
      Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      B * (1 + CK / d.cm) := by
    calc _ ≤ ∑ b, (‖vsThetaRing S μ (conj μ) τ p u b‖ +
          (t - τ) * ∑ c, κ1 * ‖vsThetaRing S μ (conj μ) τ p c b‖) *
          Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) :=
          Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_right (hpt2 b) (hf0 b)
      _ = ∑ b, ‖vsThetaRing S μ (conj μ) τ p u b‖ *
            Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) +
          (t - τ) * κ1 * ∑ c, ∑ b, ‖vsThetaRing S μ (conj μ) τ p c b‖ *
            Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q) := by
          rw [Finset.sum_comm (f := fun c b => ‖vsThetaRing S μ (conj μ) τ p c b‖ *
            Real.sqrt (Ys p b * polynomialControl (m * W) W d.D (vsHeight z r) b q)),
            Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [add_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          congr 1
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ B + (t - τ) * κ1 * ∑ _c : Fin (m * W), B :=
          add_le_add (hrowB u) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => hrowB c)
            (mul_nonneg htτ (by positivity)))
      _ = B * (1 + (t - τ) * (CK * (((m * W : ℕ) : ℝ) ^ 2 / (W : ℝ) ^ 2))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hκ1]
          ring
      _ ≤ B * (1 + CK / d.cm) := by
          refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hB0
          have h7 := hd7 (lt_of_lt_of_le hτt ht1)
          have h6 : t - τ ≤ vsHeight z τ / d.cm := hd6
          have hq : 0 ≤ ((m * W : ℕ) : ℝ) ^ 2 / (W : ℝ) ^ 2 := by positivity
          calc (t - τ) * (CK * (((m * W : ℕ) : ℝ) ^ 2 / (W : ℝ) ^ 2))
              ≤ vsHeight z τ / d.cm * (CK * (((m * W : ℕ) : ℝ) ^ 2 / (W : ℝ) ^ 2)) :=
                mul_le_mul_of_nonneg_right h6 (mul_nonneg hCK.le hq)
            _ = CK / d.cm * (vsHeight z τ * (((m * W : ℕ) : ℝ) ^ 2 / (W : ℝ) ^ 2)) := by ring
            _ ≤ CK / d.cm * 1 :=
                mul_le_mul_of_nonneg_left h7 (div_nonneg hCK.le hcm.le)
            _ = CK / d.cm := mul_one _
  refine hstep3.trans ?_
  -- Step 4: convert
  obtain ⟨hlow1, -⟩ := hU2t htf.le p u
  obtain ⟨hlow2, -⟩ := hU2t htf.le u q
  set l := 1 / C1 * (1 / (((m * W : ℕ) : ℝ) * vsHeight z t)) with hl
  have hl0 : 0 ≤ l := by positivity
  have hP := onestep_le_sqrt hl0 hlow1 hlow2
  unfold onestepScale onestepConst
  rw [← hCKd, ← hC1d, ← hlsd, ← hX, hltN]
  have hcoef : 0 ≤ 2 * CK * (C1 ^ 3 * Real.sqrt C1) * (1 + CK / d.cm) *
      (1 / vsHeight z s * (ls * ((m * W : ℕ) : ℝ) * vsHeight z t / (W : ℝ) ^ 2) * X) := by
    positivity
  have hW2 : (W : ℝ) ^ 2 = ((m * W : ℕ) : ℝ) ^ 2 * vsHeight z τ := by
    rw [← hlτ2, hlτ]
  calc B * (1 + CK / d.cm)
      = 2 * CK * (C1 ^ 3 * Real.sqrt C1) * (1 + CK / d.cm) *
          (1 / vsHeight z s * (ls * ((m * W : ℕ) : ℝ) * vsHeight z t / (W : ℝ) ^ 2) * X) * l := by
        rw [hB, hl, hW2, hlτ]
        field_simp
    _ ≤ 2 * CK * (C1 ^ 3 * Real.sqrt C1) * (1 + CK / d.cm) *
          (1 / vsHeight z s * (ls * ((m * W : ℕ) : ℝ) * vsHeight z t / (W : ℝ) ^ 2) * X) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) p u *
          polynomialControl (m * W) W d.D (vsHeight z t) u q) :=
        mul_le_mul_of_nonneg_left hP hcoef
    _ = _ := by ring

end Cases

/-- **One-step regularized action.**
For VS data `d`, `m ≥ 4`, `W ≥ 1`, `z ∈ 𝒟`, `0 ≤ s ≤ t ≤ 1`, `r ∈ {s,t}` and sites `p, u, q`
(`p = x_{k-1}`, `u = x_k`, `q = x_{k+1}`), with `f(b) = √(Υ_s(p,b)Υ_r(b,q))`:
`Σ_b |Θ̊^p_t(u,b)| f(b) ≤ C_reg η_s⁻¹ (ℓ_sℓ_tη_t/W²) √(L_s/L_r) √(Υ_t(p,u)Υ_t(u,q))`, and hence the
same bound for `|Σ_b Θ̊^p_t(u,b) f(b)|`; `C_reg = onestepConst d`. Proof by the height partition
(`anchorTime_partition`): Case (1) `η♭ ≤ η_t`, Case (2a) `η_s ≤ η♭`, Case (2b) `η_t < η♭ < η_s`. -/
theorem thetaringAction (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
    (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z) {s t r : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
    (ht1 : t ≤ 1) (hr : r = s ∨ r = t) (p u q : Fin (m * W)) :
    ∑ b, ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t p u b‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      onestepConst d * onestepScale d m W z s t r p u q ∧
    ‖∑ b, vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t p u b *
        (Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) : ℂ)‖ ≤
      onestepConst d * onestepScale d m W z s t r p u q := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hηt := vsHeight_pos hη ht1
  have hsc := onestepScale_nonneg d m W z (r := r) hηs hηt p u q
  have hC1 : 1 ≤ d.C1pp := d.one_le_C1pp
  have hsq1 : 1 ≤ Real.sqrt d.C1pp := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hC1
  have hCK := vsCK_pos d
  have hfac : 1 ≤ 1 + vsCK d / d.cm := by
    have := div_nonneg hCK.le d.cm_pos.le
    linarith
  have hc2 : d.C1pp ≤ d.C1pp ^ 2 := by nlinarith
  have hc3 : d.C1pp ^ 2 ≤ d.C1pp ^ 3 := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) hC1
  have hk1 : 2 * vsCK d * (d.C1pp * Real.sqrt d.C1pp) ≤ onestepConst d := by
    unfold onestepConst
    have h1 : d.C1pp * Real.sqrt d.C1pp ≤ d.C1pp ^ 3 * Real.sqrt d.C1pp :=
      mul_le_mul_of_nonneg_right (hc2.trans hc3) (by linarith)
    have h2 : 0 ≤ 2 * vsCK d * (d.C1pp ^ 3 * Real.sqrt d.C1pp) := by positivity
    nlinarith
  have hk2 : 2 * vsCK d * d.C1pp ^ 2 ≤ onestepConst d := by
    unfold onestepConst
    have h1 : d.C1pp ^ 2 ≤ d.C1pp ^ 3 * Real.sqrt d.C1pp :=
      hc3.trans (le_mul_of_one_le_right (by positivity) hsq1)
    have h2 : 0 ≤ 2 * vsCK d * (d.C1pp ^ 3 * Real.sqrt d.C1pp) := by positivity
    nlinarith
  have habs : ∑ b,
      ‖vsThetaRing (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t p u b‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) p b *
          polynomialControl (m * W) W d.D (vsHeight z r) b q) ≤
      onestepConst d * onestepScale d m W z s t r p u q := by
    rcases anchorTime_partition hη hN hW hs0 hst ht1 with h1 | h2a | h2b
    · exact (onestep_case1 d hm hW hz hs0 hst ht1 hr p u q h1.1).trans
        (mul_le_mul_of_nonneg_right hk1 hsc)
    · exact (onestep_case2a d hm hW hz hs0 hst ht1 hr p u q h2a.1).trans
        (mul_le_mul_of_nonneg_right hk2 hsc)
    · exact onestep_case2b d hm hW hz hs0 hst ht1 hr p u q h2b
  refine ⟨habs, (norm_sum_le _ _).trans (le_trans (le_of_eq ?_) habs)⟩
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

end BlockBand.Native.ErdosRiabov.Propagator
