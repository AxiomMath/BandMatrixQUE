module

public import BlockBand.Native.ErdosRiabov.Prop.GoodPropsCore
public import BlockBand.Native.ErdosRiabov.Prop.Actions
public import BlockBand.Native.ErdosRiabov.Prop.Glue

/-!
# Propagator estimates on the size functions

Setting: VS data `d`, `m ≥ 4`, `W ≥ 1`, `N = mW`, `S = shortRingProfile d.b m W`; a
`P : Psi.PsiData N` with `P.W = W`, `P.D = d.D`, `P.z ∈ 𝒟`; `0 ≤ s ≤ t ≤ 1`;
`L_r = P.lEta r = ℓ_r η_r`; `ρ = √(L_s/L_t) ≥ 1`. A factor is a `PropFactor`
(`sat` = `P̂ = vsPropagator S m (conj m)`, `desat` = `Q̂ = vsPropagator S m m`,
`desatConj` = `conj Q̂`, `ident` = `I = vsPropagator S 0 0`); `goodProp S z c s t` is
`⊗_j` of the factors `c j` (a `vsTensorProp`). `C_P = kernelActionConst d`,
`C_7 = 1 + C_K C₁''/c_m`. All bounds are for the entrywise absolute value `|U|`
(`Σ_y |U(x,y)| s(y)`), hence for `U` (`*_apply` forms).

* `goodProps_iso` (the isotropic propagator bound): chain length `k = n+2`, last factor `I` (the
  isotropic chain has `k-1` propagated sites; `s^iso_k` ignores the last site):
  `Σ_y |U(x,y)| s^iso_{k,s}(a,y,b) ≤ C_P^{k-1} √(L_t/L_s) s^iso_{k,t}(a,x,b)`.
* `goodProps_av` (the averaged propagator bound, `k = n+2`, last factor non-saturated):
  `Σ_y |U(x,y)| s^av_{k,s}(y) ≤ C_P^k (L_t/L_s) s^av_{k,t}(x)`.
* `goodProps_av_one` (`k = 1`, factor non-saturated): `≤ C_7 (L_t/L_s) s^av_{1,t}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.ErdosRiabov.Propagator

open BlockBand.External BlockBand.Internal.Contracts.Inputs BlockBand.Adapters.ErdosRiabov
open BlockBand.Native.ErdosRiabov.Kernel BlockBand.Native.ErdosRiabov.Flow
open BlockBand.Native.ErdosRiabov.LemmaK
open BlockBand.External.ErdosRiabov (semicircleM semicircleM_dyson norm_semicircleM_lt_one)
open Matrix
open scoped BigOperators ComplexConjugate

/-!
## Swapping the spectral arguments
-/

theorem vsKernel_swap {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (t : ℝ) :
    vsKernel S μ' μ t = vsKernel S μ μ' t := by
  unfold vsKernel vsY
  rw [mul_comm μ' μ]

theorem vsPropagator_swap {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (μ μ' : ℂ) (s t : ℝ) :
    vsPropagator S μ' μ s t = vsPropagator S μ μ' s t := by
  unfold vsPropagator vsY
  rw [mul_comm μ' μ]

theorem vsPropagator_zero {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (s t : ℝ) :
    vsPropagator S 0 0 s t = 1 := by
  unfold vsPropagator vsY
  simp

/-!
## Factors
-/

/-- The four factors of the Duhamel propagators. -/
inductive PropFactor
  | sat
  | desat
  | desatConj
  | ident
  deriving DecidableEq

/-- First spectral argument of a factor. -/
def PropFactor.mu1 (z : ℂ) : PropFactor → ℂ
  | .sat => semicircleM z
  | .desat => semicircleM z
  | .desatConj => conj (semicircleM z)
  | .ident => 0

/-- Second spectral argument of a factor. -/
def PropFactor.mu2 (z : ℂ) : PropFactor → ℂ
  | .sat => conj (semicircleM z)
  | .desat => semicircleM z
  | .desatConj => conj (semicircleM z)
  | .ident => 0

/-- The one-site propagator of a factor. -/
def goodPropFactor {N : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (c : PropFactor) (s t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  vsPropagator S (c.mu1 z) (c.mu2 z) s t

/-- The `k`-site propagator `⊗_j (factor c_j)` (a `vsTensorProp`). -/
def goodProp {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (c : Fin k → PropFactor)
    (s t : ℝ) : Matrix (Fin k → Fin N) (Fin k → Fin N) ℂ :=
  vsTensorProp S (fun j => (c j).mu1 z) (fun j => (c j).mu2 z) s t

/-- The entrywise norms of the factors. -/
def goodPropNorm {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (c : Fin k → PropFactor)
    (s t : ℝ) : Fin k → Matrix (Fin N) (Fin N) ℝ :=
  fun j u v => ‖goodPropFactor S z (c j) s t u v‖

theorem norm_goodProp {N k : ℕ} (S : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (c : Fin k → PropFactor)
    (s t : ℝ) (x y : Fin k → Fin N) :
    ‖goodProp S z c s t x y‖ = tensorR (goodPropNorm S z c s t) x y := by
  simp only [goodProp, vsTensorProp, tensorMat, tensorR, goodPropNorm, goodPropFactor, norm_prod]

/-!
## The core of (P3) and (K7) in `VSData` form
-/

section Core

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z)
include hm hW hz

/-- **Core of (P3)** (the general form of a step of `kernelActions`): any matrix `B` with
`|B(a,x)| ≤ δ_{ax} + (C_K/c_m) η_s Υ_0(a,x)` satisfies, for `r₁, r₂ ∈ [0,1]`,
`Σ_a |B(u,a)| √(Υ_{r₁}(x,a)Υ_{r₂}(a,y)) ≤ C_P √(Υ_{r₁}(x,u)Υ_{r₂}(u,y))`. -/
theorem kernelAction_P3_core {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) {r₁ r₂ : ℝ}
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1)
    (B : Fin (m * W) → Fin (m * W) → ℂ)
    (hB : ∀ a x, ‖B a x‖ ≤ (if a = x then 1 else 0) + vsCK d / d.cm * vsHeight z s *
      polynomialControl (m * W) W d.D (vsHeight z 0) a x) (u x y : Fin (m * W)) :
    ∑ a, ‖B u a‖ * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z r₁) x a *
        polynomialControl (m * W) W d.D (vsHeight z r₂) a y) ≤
      kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z r₁) x u *
        polynomialControl (m * W) W d.D (vsHeight z r₂) u y) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  obtain ⟨-, -, -, -, -, -, -, hU5a, -, -, -, -, -⟩ :=
    ups_U2_U8_vs d hm hW hz le_rfl hr₁0 hr₁1
  obtain ⟨-, -, -, -, -, -, -, hU5b, -, -, -, -, -⟩ :=
    ups_U2_U8_vs d hm hW hz le_rfl hr₂0 hr₂1
  set Υ := polynomialControl (m * W) W d.D with hΥdef
  have hsym : ∀ h x y, Υ h x y = Υ h y x := fun h x y => polynomialControl_symm _ _ _ h x y
  have hpos : ∀ r : ℝ, r ≤ 1 → ∀ x y, 0 ≤ Υ (vsHeight z r) x y := fun r hr x y =>
    (polynomialControl_pos hN hW d.D (vsHeight_pos hη hr) x y).le
  set K := vsCK d / d.cm with hKdef
  have hK : 0 ≤ K := div_nonneg (vsCK_pos d).le d.cm_pos.le
  have hCwc : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hsle0 : vsHeight z s ≤ vsHeight z 0 := by
    rw [vsHeight_affine z s, vsHeight_affine z 0]
    nlinarith [semicircleM_im_pos hη]
  have h0pos := vsHeight_pos hη (zero_le_one : (0 : ℝ) ≤ 1)
  set c0 := d.Cwc / vsHeight z 0 with hc0
  have hc00 : 0 ≤ c0 := div_nonneg hCwc h0pos.le
  have hsum : ∑ a, Υ (vsHeight z 0) u a *
      Real.sqrt (Υ (vsHeight z r₁) x a * Υ (vsHeight z r₂) a y) ≤
      c0 * Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) := by
    calc ∑ a, Υ (vsHeight z 0) u a *
          Real.sqrt (Υ (vsHeight z r₁) x a * Υ (vsHeight z r₂) a y)
        = ∑ a, Real.sqrt (Υ (vsHeight z 0) u a * Υ (vsHeight z r₁) a x) *
            Real.sqrt (Υ (vsHeight z 0) u a * Υ (vsHeight z r₂) a y) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Real.sqrt_mul (mul_nonneg (hpos 0 zero_le_one u a) (hpos r₁ hr₁1 a x)),
            hsym _ a x,
            show Υ (vsHeight z 0) u a * Υ (vsHeight z r₁) x a *
                (Υ (vsHeight z 0) u a * Υ (vsHeight z r₂) a y) =
              Υ (vsHeight z r₁) x a * Υ (vsHeight z r₂) a y * Υ (vsHeight z 0) u a *
                Υ (vsHeight z 0) u a by ring,
            prop_sqrt_mul_sq _ _ (hpos 0 zero_le_one u a)]
      _ ≤ Real.sqrt (∑ a, Υ (vsHeight z 0) u a * Υ (vsHeight z r₁) a x) *
            Real.sqrt (∑ a, Υ (vsHeight z 0) u a * Υ (vsHeight z r₂) a y) :=
          Real.sum_sqrt_mul_sqrt_le _
            (fun a => mul_nonneg (hpos 0 zero_le_one u a) (hpos r₁ hr₁1 a x))
            (fun a => mul_nonneg (hpos 0 zero_le_one u a) (hpos r₂ hr₂1 a y))
      _ ≤ Real.sqrt (c0 * Υ (vsHeight z r₁) u x) * Real.sqrt (c0 * Υ (vsHeight z r₂) u y) :=
          mul_le_mul (Real.sqrt_le_sqrt (hU5a u x)) (Real.sqrt_le_sqrt (hU5b u y))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = c0 * Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) := by
          rw [prop_sqrt_mul_const hc00 (hpos r₁ hr₁1 u x), hsym _ u x]
  have hmain := prop_sum_delta_le (B u) (fun a => Υ (vsHeight z 0) u a)
    (fun a => Real.sqrt (Υ (vsHeight z r₁) x a * Υ (vsHeight z r₂) a y)) u
    (fun a => Real.sqrt_nonneg _) (hB u)
  have hKs : 0 ≤ K * vsHeight z s := mul_nonneg hK hηs.le
  have hcc : K * vsHeight z s * c0 ≤ K * d.Cwc := by
    rw [hc0, mul_div_assoc', div_le_iff₀ h0pos]
    have := mul_le_mul_of_nonneg_left hsle0 (mul_nonneg hK hCwc)
    nlinarith
  have hsq0 := Real.sqrt_nonneg (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y)
  refine hmain.trans ?_
  calc Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) +
        K * vsHeight z s * ∑ a, Υ (vsHeight z 0) u a *
          Real.sqrt (Υ (vsHeight z r₁) x a * Υ (vsHeight z r₂) a y)
      ≤ Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) +
        K * vsHeight z s * (c0 * Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hKs)
    _ ≤ Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) +
        K * d.Cwc * Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) := by
        rw [← mul_assoc]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcc hsq0)
    _ = _ := by rw [kernelActionConst]; ring

/-- (K7) row sums at VS data `d`:
`Σ_x |T̂_t(a,x)| ≤ C_K C₁''/η_t` and
`Σ_x |Q̂_{s,t}(a,x)| ≤ 1 + C_K C₁''/c_m`.
-/
theorem lemmaK_K7_single_d {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
    (a : Fin (m * W)) :
    ∑ x, ‖vsKernel (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) t a x‖ ≤
      vsCK d * d.C1pp / vsHeight z t ∧
    ∑ x, ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (semicircleM z) s t a x‖ ≤
      1 + vsCK d * d.C1pp / d.cm := by
  obtain ⟨h1, -, h3⟩ := lemmaK_K7_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hm hW hz hs0 hst ht1 a
  exact ⟨h1, h3⟩

end Core

/-!
## Single-factor steps
-/

theorem kernelActionConst_ge_one (d : VSData) : 1 ≤ kernelActionConst d := by
  unfold kernelActionConst
  have := mul_nonneg (div_nonneg (vsCK_pos d).le d.cm_pos.le) (le_trans zero_le_one d.one_le_Cwc)
  linarith

section Steps

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t)
  (ht1 : t ≤ 1)
include hm hW hz hs0 hst ht1

/-- Entry bound of a non-saturated factor: `|F(a,x)| ≤ δ_{ax} + K η_s Υ_0(a,x)`. -/
theorem goodPropFactor_entry_nonsat {c : PropFactor} (hc : c ≠ .sat) (a x : Fin (m * W)) :
    ‖goodPropFactor (shortRingProfile d.b m W) z c s t a x‖ ≤
      (if a = x then 1 else 0) + vsCK d / d.cm * vsHeight z s *
        polynomialControl (m * W) W d.D (vsHeight z 0) a x := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  obtain ⟨-, hQ, -⟩ := lemmaK_K6_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hm hW hz hs0 hst ht1
  have hnn : 0 ≤ vsCK d / d.cm * vsHeight z s *
      polynomialControl (m * W) W d.D (vsHeight z 0) a x :=
    mul_nonneg (mul_nonneg (div_nonneg (vsCK_pos d).le d.cm_pos.le)
      (vsHeight_pos hη (hst.trans ht1)).le)
      (polynomialControl_pos hN hW d.D (vsHeight_pos hη zero_le_one) a x).le
  cases c with
  | sat => exact absurd rfl hc
  | desat => exact hQ a x
  | desatConj =>
    have hm1 := norm_semicircleM_lt_one hη.ne'
    have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega : 3 ≤ m) hW
    simp only [goodPropFactor, PropFactor.mu1, PropFactor.mu2]
    rw [vsPropagator_conj hS (norm_smul_lt_one hm1 hm1 (hs0.trans hst) ht1), Complex.norm_conj]
    exact hQ a x
  | ident =>
    simp only [goodPropFactor, PropFactor.mu1, PropFactor.mu2, vsPropagator_zero,
      Matrix.one_apply]
    split_ifs <;> simp <;> linarith

/-- Step A (`(s,s) → (t,t)`), every factor:
`Σ_a |F(u,a)| √(Υ_s(w,a)Υ_s(a,w')) ≤ C_P √(Υ_t(w,u)Υ_t(u,w'))`. -/
theorem goodProp_stepA (c : PropFactor) (u w w' : Fin (m * W)) :
    ∑ a, ‖goodPropFactor (shortRingProfile d.b m W) z c s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) w a *
          polynomialControl (m * W) W d.D (vsHeight z s) a w') ≤
      kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
        polynomialControl (m * W) W d.D (vsHeight z t) u w') := by
  have hs1 : s ≤ 1 := hst.trans ht1
  by_cases hc : c = .sat
  · subst hc
    exact (kernelActions d hm hW hz hs0 hst ht1 hs0 hs1 hs0 hs1).2.2.2.1 u w w'
  · have hN : 0 < m * W := Nat.mul_pos (by omega) hW
    have hη := hz.im_pos hN
    obtain ⟨-, -, -, -, hU3, -⟩ := ups_U2_U8_vs d hm hW hz hs0 hst ht1
    refine (kernelAction_P3_core d hm hW hz hs0 hst ht1 hs0 hs1 hs0 hs1 _
      (goodPropFactor_entry_nonsat d hm hW hz hs0 hst ht1 hc) u w w').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_)
      (le_trans zero_le_one (kernelActionConst_ge_one d))
    exact mul_le_mul (hU3 w u) (hU3 u w')
      (polynomialControl_pos hN hW d.D (vsHeight_pos hη hs1) u w').le
      (polynomialControl_pos hN hW d.D (vsHeight_pos hη ht1) w u).le

/-- Step B (`(t,s) → (t,t)`), every factor:
`Σ_a |F(u,a)| √(Υ_t(w,a)Υ_s(a,w')) ≤ C_P √(L_s/L_t) √(Υ_t(w,u)Υ_t(u,w'))`. -/
theorem goodProp_stepB (c : PropFactor) (u w w' : Fin (m * W)) :
    ∑ a, ‖goodPropFactor (shortRingProfile d.b m W) z c s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w a *
          polynomialControl (m * W) W d.D (vsHeight z s) a w') ≤
      kernelActionConst d *
        Real.sqrt ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) /
          (ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t)) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
          polynomialControl (m * W) W d.D (vsHeight z t) u w') := by
  have hs1 : s ≤ 1 := hst.trans ht1
  have ht0 : 0 ≤ t := hs0.trans hst
  by_cases hc : c = .sat
  · subst hc
    exact (kernelActions d hm hW hz hs0 hst ht1 hs0 hs1 hs0 hs1).2.2.2.2.2.2.1 u w w'
  · have hN : 0 < m * W := Nat.mul_pos (by omega) hW
    have hη := hz.im_pos hN
    obtain ⟨-, -, -, -, hU3, -⟩ := ups_U2_U8_vs d hm hW hz hs0 hst ht1
    have hηt := vsHeight_pos hη ht1
    have hηs := vsHeight_pos hη hs1
    have hts : vsHeight z t ≤ vsHeight z s := by
      rw [vsHeight_affine z t, vsHeight_affine z s]
      nlinarith [semicircleM_im_pos hη]
    have hLt := mul_pos (loc_pos hN hW hηt) hηt
    have hLst := loc_mul_mono (m * W) W hηt hts
    have hρ : 1 ≤ Real.sqrt ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) *
        vsHeight z s) / (ErdosRiabov.localizationLength (m * W) W (vsHeight z t) *
          vsHeight z t)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hLt]; linarith)
    have hCP := kernelActionConst_ge_one d
    refine (kernelAction_P3_core d hm hW hz hs0 hst ht1 ht0 ht1 hs0 hs1 _
      (goodPropFactor_entry_nonsat d hm hW hz hs0 hst ht1 hc) u w w').trans ?_
    have hsq : Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
        polynomialControl (m * W) W d.D (vsHeight z s) u w') ≤
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
          polynomialControl (m * W) W d.D (vsHeight z t) u w') :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hU3 u w')
        (polynomialControl_pos hN hW d.D hηt w u).le)
    have h0 := Real.sqrt_nonneg (polynomialControl (m * W) W d.D (vsHeight z t) w u *
      polynomialControl (m * W) W d.D (vsHeight z t) u w')
    calc _ ≤ kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
          polynomialControl (m * W) W d.D (vsHeight z t) u w') :=
          mul_le_mul_of_nonneg_left hsq (by linarith)
      _ ≤ _ := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h0 hρ) (by linarith)

/-- Step C (`(t,t) → (t,t)`), non-saturated factor:
`Σ_a |F(u,a)| √(Υ_t(w,a)Υ_t(a,w')) ≤ C_P √(Υ_t(w,u)Υ_t(u,w'))`. -/
theorem goodProp_stepC_nonsat {c : PropFactor} (hc : c ≠ .sat) (u w w' : Fin (m * W)) :
    ∑ a, ‖goodPropFactor (shortRingProfile d.b m W) z c s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w a *
          polynomialControl (m * W) W d.D (vsHeight z t) a w') ≤
      kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) w u *
        polynomialControl (m * W) W d.D (vsHeight z t) u w') :=
  kernelAction_P3_core d hm hW hz hs0 hst ht1 (hs0.trans hst) ht1 (hs0.trans hst) ht1 _
    (goodPropFactor_entry_nonsat d hm hW hz hs0 hst ht1 hc) u w w'

end Steps

/-!
## Exponent arithmetic
-/

private theorem goodProp_sqrt_div {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    Real.sqrt (X / Y) = X ^ (1 / 2 : ℝ) * Y ^ (-(1 / 2) : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.div_rpow hX.le hY.le, Real.rpow_neg hY.le, div_eq_mul_inv]

private theorem goodProp_pow_sqrt {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) (n : ℕ) :
    Real.sqrt (X / Y) ^ n = X ^ ((n : ℝ) / 2) * Y ^ (-((n : ℝ) / 2)) := by
  rw [goodProp_sqrt_div hX hY, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hX.le, ← Real.rpow_mul hY.le]
  congr 2 <;> ring

/-- `A^{-(n+1)/2} √(A/B)^n = √(B/A) B^{-(n+1)/2}`. -/
theorem goodProp_rpow_iso {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    A ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) * Real.sqrt (A / B) ^ n =
      Real.sqrt (B / A) * B ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) := by
  rw [goodProp_pow_sqrt hA hB, goodProp_sqrt_div hB hA, ← mul_assoc, ← Real.rpow_add hA,
    mul_comm (B ^ (1 / 2 : ℝ)), mul_assoc, ← Real.rpow_add hB]
  congr 2 <;> push_cast <;> ring

/-- `A^{-(n+2)/2} √(A/B)^n = (B/A) B^{-(n+2)/2}`. -/
theorem goodProp_rpow_av {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (n : ℕ) :
    A ^ (-((n + 2 : ℕ) : ℝ) / 2) * Real.sqrt (A / B) ^ n =
      B / A * B ^ (-((n + 2 : ℕ) : ℝ) / 2) := by
  rw [goodProp_pow_sqrt hA hB, ← mul_assoc, ← Real.rpow_add hA,
    show B / A * B ^ (-((n + 2 : ℕ) : ℝ) / 2) = A ^ (-1 : ℝ) * B ^ ((1 : ℝ) +
      (-((n + 2 : ℕ) : ℝ) / 2)) by
      rw [Real.rpow_add hB, Real.rpow_one, Real.rpow_neg_one]
      field_simp]
  congr 2 <;> push_cast <;> ring

/-!
## Propagator bounds on the size functions
-/

/-- Link heights after `m` steps: links `0, …, m` at time `t` (if `m ≥ 1`), the rest at `s`. -/
def linkTime (m : ℕ) (s t : ℝ) (i : ℕ) : ℝ := if 0 < m ∧ i ≤ m then t else s

section Psi

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) (P : Psi.PsiData (m * W))
  (hPW : P.W = W) (hPD : P.D = d.D) (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 P.z)
  {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1)
include hm hW hPW hPD hz hs0 hst ht1

/-- The interior iteration for any endpoints unchanged by interior updates (common part of
`goodProps_iso` and `goodProps_av`). -/
private theorem goodProps_interior {n : ℕ} (c : Fin (n + 2) → PropFactor)
    (ea eb : (Fin (n + 2) → Fin (m * W)) → Fin (m * W))
    (hea : ∀ (y : Fin (n + 2) → Fin (m * W)) (j : Fin (n + 2)) (e : Fin (m * W)),
      j.val + 1 < n + 2 → ea (Function.update y j e) = ea y)
    (heb : ∀ (y : Fin (n + 2) → Fin (m * W)) (j : Fin (n + 2)) (e : Fin (m * W)),
      j.val + 1 < n + 2 → eb (Function.update y j e) = eb y) (x : Fin (n + 2) → Fin (m * W)) :
    (tensorRSet (goodPropNorm (shortRingProfile d.b m W) P.z c s t) (slotsBelow (n + 2) (n + 1))
        *ᵥ fun y => Real.sqrt (linkProd (fun _ => P.ups s) (ea y) (eb y) y)) x ≤
      kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta s / P.lEta t) ^ n *
        Real.sqrt (linkProd (fun _ => P.ups t) (ea x) (eb x) x) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hu : ∀ r, P.ups r = polynomialControl (m * W) W d.D (vsHeight P.z r) := by
    intro r
    unfold Psi.PsiData.ups
    rw [hPW, hPD]
  have hl : ∀ r, P.lEta r =
      ErdosRiabov.localizationLength (m * W) W (vsHeight P.z r) * vsHeight P.z r := by
    intro r
    unfold Psi.PsiData.lEta
    rw [hPW]
  set Fn := goodPropNorm (shortRingProfile d.b m W) P.z c s t with hFn
  have hF0 : ∀ j u v, 0 ≤ Fn j u v := fun j u v => norm_nonneg _
  set V : ℕ → ℕ → Fin (m * W) → Fin (m * W) → ℝ := fun m' i => P.ups (linkTime m' s t i)
    with hV
  have hVn : ∀ m' i u w, 0 ≤ V m' i u w := by
    intro m' i u w
    rw [hV]
    dsimp only
    rw [hu]
    have hs1 : linkTime m' s t i ≤ 1 := by
      unfold linkTime
      split_ifs <;> linarith
    exact (polynomialControl_pos hN hW d.D (vsHeight_pos hη hs1) u w).le
  set ρ := Real.sqrt (P.lEta s / P.lEta t) with hρ
  set κ : ℕ → ℝ := fun i => if i = 0 then kernelActionConst d else kernelActionConst d * ρ
    with hκ
  have hCP := kernelActionConst_ge_one d
  have hκ0 : ∀ i, 0 ≤ κ i := by
    intro i
    rw [hκ]
    dsimp only
    split_ifs
    · linarith
    · exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hVV : ∀ m' i, i ≠ m' → i ≠ m' + 1 → V m' i = V (m' + 1) i := by
    intro m' i h1 h2
    rw [hV]
    dsimp only
    unfold linkTime
    congr 1
    by_cases hi : i < m'
    · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hstep : ∀ (m' : ℕ) (hm' : m' + 1 < n + 2) (x : Fin (n + 2) → Fin (m * W)),
      ∑ e, Fn ⟨m', by omega⟩ (x ⟨m', by omega⟩) e *
          Real.sqrt (V m' m' (Psi.isoPoint (ea x) (eb x) x m') e *
            V m' (m' + 1) e (Psi.isoPoint (ea x) (eb x) x (m' + 2))) ≤
        κ m' * Real.sqrt (V (m' + 1) m' (Psi.isoPoint (ea x) (eb x) x m') (x ⟨m', by omega⟩) *
          V (m' + 1) (m' + 1) (x ⟨m', by omega⟩) (Psi.isoPoint (ea x) (eb x) x (m' + 2))) := by
    intro m' hm' x
    have hb : V m' (m' + 1) = P.ups s := by
      rw [hV]; dsimp only; unfold linkTime; rw [ite_eq_right (by omega)]
    have hc1 : V (m' + 1) m' = P.ups t := by
      rw [hV]; dsimp only; unfold linkTime; rw [ite_eq_left ⟨by omega, by omega⟩]
    have hc2 : V (m' + 1) (m' + 1) = P.ups t := by
      rw [hV]; dsimp only; unfold linkTime; rw [ite_eq_left ⟨by omega, le_rfl⟩]
    rw [hb, hc1, hc2, hu, hu]
    rcases Nat.eq_zero_or_pos m' with h0 | hpos
    · subst h0
      have ha : V 0 0 = P.ups s := by
        rw [hV]; dsimp only; unfold linkTime; rw [ite_eq_right (by omega)]
      rw [ha, hu, hκ]
      dsimp only
      rw [ite_eq_left rfl]
      exact goodProp_stepA d hm hW hz hs0 hst ht1 _ _ _ _
    · have ha : V m' m' = P.ups t := by
        rw [hV]; dsimp only; unfold linkTime; rw [ite_eq_left ⟨hpos, le_rfl⟩]
      rw [ha, hu, hκ]
      dsimp only
      rw [ite_eq_right (by omega), hρ, hl s, hl t]
      exact goodProp_stepB d hm hW hz hs0 hst ht1 _ _ _ _
  have hit := tensorRSet_iter_le Fn hF0 V hVn ea eb hea heb κ hκ0 hVV hstep (n + 1)
    (by omega) x
  have hV0 : V 0 = fun _ => P.ups s := by
    funext i
    rw [hV]
    dsimp only
    unfold linkTime
    rw [ite_eq_right (by omega)]
  have hVt : linkProd (V (n + 1)) (ea x) (eb x) x = linkProd (fun _ => P.ups t) (ea x) (eb x) x :=
    linkProd_congr (fun i hi => by
      rw [hV]; dsimp only; unfold linkTime; rw [ite_eq_left ⟨by omega, by omega⟩]) _ _ x
  have hprod : ∏ i ∈ Finset.range (n + 1), κ i = kernelActionConst d ^ (n + 1) * ρ ^ n := by
    rw [Finset.prod_range_succ', hκ]
    dsimp only
    rw [ite_eq_left rfl, Finset.prod_congr rfl (fun i _ => ite_eq_right (Nat.succ_ne_zero i)),
      Finset.prod_const, Finset.card_range, mul_pow]
    ring
  rw [hV0, hVt, hprod] at hit
  exact hit

/-- Chain length `k = n+2`, factors `c` with last factor `I`: for all `a, b, x`,
`Σ_y |U(x,y)| s^iso_{k,s}(a,y,b) ≤ C_P^{k-1} √(L_t/L_s) s^iso_{k,t}(a,x,b)`,
`U = goodProp S P.z c s t`.
-/
theorem goodProps_iso {n : ℕ} (c : Fin (n + 2) → PropFactor)
    (hlast : c (Fin.last (n + 1)) = .ident) (a b : Fin (m * W))
    (x : Fin (n + 2) → Fin (m * W)) :
    ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sIso a b y s ≤
      kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta t / P.lEta s) * P.sIso a b x t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  obtain ⟨-, -, hLs, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW hs0 (hst.trans ht1)
  obtain ⟨-, -, hLt, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW (hs0.trans hst) ht1
  set Fn := goodPropNorm (shortRingProfile d.b m W) P.z c s t with hFn
  have huniv : (Finset.univ : Finset (Fin (n + 2))) =
      insert (Fin.last (n + 1)) (slotsBelow (n + 2) (n + 1)) := by
    ext j
    simp only [slotsBelow, Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
      Fin.ext_iff, Fin.val_last, true_iff]
    omega
  have hnot : Fin.last (n + 1) ∉ slotsBelow (n + 2) (n + 1) := by simp [slotsBelow]
  have hid : ∀ (h : (Fin (n + 2) → Fin (m * W)) → ℝ) (x : Fin (n + 2) → Fin (m * W)),
      (tensorRSet Fn {Fin.last (n + 1)} *ᵥ h) x = h x := by
    intro h x
    rw [mulVec_tensorRSet_single]
    unfold slotOp
    simp only [hFn, goodPropNorm, hlast, goodPropFactor, PropFactor.mu1, PropFactor.mu2,
      vsPropagator_zero, Matrix.one_apply, apply_ite, norm_one, norm_zero, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Function.update_eq_self]
  have hLHS : ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sIso a b y s =
      P.lEta s ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) *
        (tensorR Fn *ᵥ fun y => Real.sqrt (linkProd (fun _ => P.ups s) a b y)) x := by
    simp only [norm_goodProp, sIso_eq_linkProd, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hLHS, ← tensorRSet_univ, huniv, (tensorRSet_insert Fn hnot).1, ← Matrix.mulVec_mulVec,
    hid]
  have hint := goodProps_interior d hm hW P hPW hPD hz hs0 hst ht1 c (fun _ => a) (fun _ => b)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) x
  have hpow := goodProp_rpow_iso hLs hLt n
  have hcoef : 0 ≤ P.lEta s ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) := Real.rpow_nonneg hLs.le _
  calc P.lEta s ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) *
        (tensorRSet Fn (slotsBelow (n + 2) (n + 1)) *ᵥ
          fun y => Real.sqrt (linkProd (fun _ => P.ups s) a b y)) x
      ≤ P.lEta s ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) * (kernelActionConst d ^ (n + 1) *
          Real.sqrt (P.lEta s / P.lEta t) ^ n *
            Real.sqrt (linkProd (fun _ => P.ups t) a b x)) :=
        mul_le_mul_of_nonneg_left hint hcoef
    _ = kernelActionConst d ^ (n + 1) * (P.lEta s ^ (-(((n + 2 : ℕ) : ℝ) - 1) / 2) *
          Real.sqrt (P.lEta s / P.lEta t) ^ n) *
            Real.sqrt (linkProd (fun _ => P.ups t) a b x) := by ring
    _ = _ := by
        rw [hpow, sIso_eq_linkProd]
        push_cast
        ring

/-- **Good propagator bound, averaged chains.** Chain length `k = n+2`, factors `c` whose last
factor is non-saturated: for all `x`, `Σ_y |U(x,y)| s^av_{k,s}(y) ≤ C_P^k (L_t/L_s) s^av_{k,t}(x)`.
-/
theorem goodProps_av {n : ℕ} (c : Fin (n + 2) → PropFactor)
    (hlast : c (Fin.last (n + 1)) ≠ .sat) (x : Fin (n + 2) → Fin (m * W)) :
    ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s ≤
      kernelActionConst d ^ (n + 2) * (P.lEta t / P.lEta s) * P.sAv x t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  obtain ⟨-, -, hLs, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW hs0 (hst.trans ht1)
  obtain ⟨-, -, hLt, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW (hs0.trans hst) ht1
  have hu : ∀ r, P.ups r = polynomialControl (m * W) W d.D (vsHeight P.z r) := by
    intro r
    unfold Psi.PsiData.ups
    rw [hPW, hPD]
  set Fn := goodPropNorm (shortRingProfile d.b m W) P.z c s t with hFn
  have hF0 : ∀ j u v, 0 ≤ Fn j u v := fun j u v => norm_nonneg _
  have huniv : (Finset.univ : Finset (Fin (n + 2))) =
      insert (Fin.last (n + 1)) (slotsBelow (n + 2) (n + 1)) := by
    ext j
    simp only [slotsBelow, Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and,
      Fin.ext_iff, Fin.val_last, true_iff]
    omega
  have hnot : Fin.last (n + 1) ∉ slotsBelow (n + 2) (n + 1) := by simp [slotsBelow]
  set ea : (Fin (n + 2) → Fin (m * W)) → Fin (m * W) := fun y => y (Fin.last (n + 1)) with hea
  have hinv : ∀ (y : Fin (n + 2) → Fin (m * W)) (j : Fin (n + 2)) (e : Fin (m * W)),
      j.val + 1 < n + 2 → ea (Function.update y j e) = ea y := by
    intro y j e hj
    rw [hea]
    dsimp only
    rw [Function.update_of_ne]
    intro h
    subst h
    simp at hj
  have hLHS : ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s =
      P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) *
        (tensorR Fn *ᵥ fun y => Real.sqrt (linkProd (fun _ => P.ups s) (ea y) (ea y) y)) x := by
    simp only [norm_goodProp, sAv_eq_linkProd, Matrix.mulVec, dotProduct, Finset.mul_sum, hea]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hLHS, ← tensorRSet_univ, huniv, (tensorRSet_insert Fn hnot).1, ← Matrix.mulVec_mulVec,
    mulVec_tensorRSet_single]
  have hint := goodProps_interior d hm hW P hPW hPD hz hs0 hst ht1 c ea ea hinv hinv
  have hK0 : ∀ (y : Fin (n + 2) → Fin (m * W)) (e : Fin (m * W)),
      0 ≤ Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) e := fun y e => hF0 _ _ _
  have hlastStep := slotOp_sqrt_linkProd_last_le (K := fun y e =>
      Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) e) (V := fun _ => P.ups t)
    (V' := fun _ => P.ups t) (fun _ _ _ => rfl)
    (fun i u w => by rw [hu]; exact (polynomialControl_pos hN hW d.D
      (vsHeight_pos hη ht1) u w).le) x (κ := kernelActionConst d) (by
      simp only [hFn, goodPropNorm, hu]
      exact goodProp_stepC_nonsat d hm hW hz hs0 hst ht1 hlast _ _ _)
  have hcoef : 0 ≤ P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) := Real.rpow_nonneg hLs.le _
  have hC0 : 0 ≤ kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta s / P.lEta t) ^ n :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one (kernelActionConst_ge_one d)) _)
      (pow_nonneg (Real.sqrt_nonneg _) _)
  have hpow := goodProp_rpow_av hLs hLt n
  calc P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) *
        slotOp (Fin.last (n + 1)) (fun y e => Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) e)
          (tensorRSet Fn (slotsBelow (n + 2) (n + 1)) *ᵥ
            fun y => Real.sqrt (linkProd (fun _ => P.ups s) (ea y) (ea y) y)) x
      ≤ P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) *
        slotOp (Fin.last (n + 1)) (fun y e => Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) e)
          (fun y => kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta s / P.lEta t) ^ n *
            Real.sqrt (linkProd (fun _ => P.ups t) (ea y) (ea y) y)) x :=
        mul_le_mul_of_nonneg_left (slotOp_mono _ hK0 (fun y => hint y) x) hcoef
    _ = P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) *
        (kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta s / P.lEta t) ^ n *
          slotOp (Fin.last (n + 1)) (fun y e => Fn (Fin.last (n + 1)) (y (Fin.last (n + 1))) e)
            (fun y => Real.sqrt (linkProd (fun _ => P.ups t) (ea y) (ea y) y)) x) := by
        rw [slotOp_const_mul]
    _ ≤ P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) *
        (kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta s / P.lEta t) ^ n *
          (kernelActionConst d *
            Real.sqrt (linkProd (fun _ => P.ups t) (ea x) (ea x) x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlastStep hC0) hcoef
    _ = kernelActionConst d ^ (n + 2) * (P.lEta s ^ (-((n + 2 : ℕ) : ℝ) / 2) *
          Real.sqrt (P.lEta s / P.lEta t) ^ n) *
            Real.sqrt (linkProd (fun _ => P.ups t) (ea x) (ea x) x) := by ring
    _ = _ := by
        rw [hpow, sAv_eq_linkProd]
        ring

omit hPD in

/-- **Good propagator bound, averaged `k = 1`** (from (K7) with `η₀ ≥ c_m`): for a non-saturated
factor, `Σ_y |U(x,y)| s^av_{1,s}(y) ≤ C_7 (L_t/L_s) s^av_{1,t}(x)`, `C_7 = 1 + C_K C₁''/c_m`. -/
theorem goodProps_av_one (c : Fin 1 → PropFactor) (hc : c 0 ≠ .sat)
    (x : Fin 1 → Fin (m * W)) :
    ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s ≤
      (1 + vsCK d * d.C1pp / d.cm) * (P.lEta t / P.lEta s) * P.sAv x t := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have hWN : W ≤ m * W := Nat.le_mul_of_pos_left W (by omega)
  obtain ⟨-, -, hLs, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW hs0 (hst.trans ht1)
  obtain ⟨-, -, hLt, -⟩ := P.height_bounds hN hW hWN d.kappa_pos
    (by linarith [d.C0_ge_one]) hz hPW (hs0.trans hst) ht1
  have hsAv : ∀ (y : Fin 1 → Fin (m * W)) (r : ℝ), P.sAv y r = (P.lEta r)⁻¹ := by
    intro y r
    simp [Psi.PsiData.sAv]
  set Fn := goodPropNorm (shortRingProfile d.b m W) P.z c s t with hFn
  have huniv : (Finset.univ : Finset (Fin 1)) = insert 0 ∅ := by
    ext j
    simp [Fin.fin_one_eq_zero j]
  have hLHS : ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s =
      (P.lEta s)⁻¹ * (tensorR Fn *ᵥ fun _ => (1 : ℝ)) x := by
    simp only [norm_goodProp, hsAv, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hLHS, ← tensorRSet_univ, huniv, (tensorRSet_insert Fn (Finset.notMem_empty _)).1,
    tensorRSet_empty, Matrix.mul_one, mulVec_tensorRSet_single, hsAv]
  have hrow : ∑ e, Fn 0 (x 0) e ≤ 1 + vsCK d * d.C1pp / d.cm := by
    have h7 := (lemmaK_K7_single_d d hm hW hz hs0 hst ht1 (x 0)).2
    have hpos : 0 ≤ vsCK d * d.C1pp / d.cm :=
      div_nonneg (mul_nonneg (vsCK_pos d).le (le_trans zero_le_one d.one_le_C1pp)) d.cm_pos.le
    simp only [hFn, goodPropNorm, goodPropFactor]
    cases hc0 : c 0 with
    | sat => exact absurd hc0 hc
    | desat => exact h7
    | desatConj =>
      have hm1 := norm_semicircleM_lt_one hη.ne'
      have hS := shortRingProfile_stochasticSymm d.b_pos d.b_lt_half (by omega : 3 ≤ m) hW
      simp only [PropFactor.mu1, PropFactor.mu2]
      simp_rw [vsPropagator_conj hS (norm_smul_lt_one hm1 hm1 (hs0.trans hst) ht1),
        Complex.norm_conj]
      exact h7
    | ident =>
      simp only [PropFactor.mu1, PropFactor.mu2, vsPropagator_zero, Matrix.one_apply,
        apply_ite, norm_one, norm_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      linarith
  unfold slotOp
  simp only [mul_one]
  have hLs' : (P.lEta s)⁻¹ = (P.lEta t / P.lEta s) * (P.lEta t)⁻¹ := by
    field_simp
  rw [hLs', mul_comm ((P.lEta t / P.lEta s) * (P.lEta t)⁻¹)]
  calc (∑ e, Fn 0 (x 0) e) * (P.lEta t / P.lEta s * (P.lEta t)⁻¹)
      ≤ (1 + vsCK d * d.C1pp / d.cm) * (P.lEta t / P.lEta s * (P.lEta t)⁻¹) :=
        mul_le_mul_of_nonneg_right hrow (by positivity)
    _ = _ := by ring

/-- `goodProps_iso` for functions: if `|f(y)| ≤ φ s^iso_{k,s}(a,y,b)` then
`|U f(x)| ≤ C_P^{k-1} φ √(L_t/L_s) s^iso_{k,t}(a,x,b)` (`U = propOp (goodProp …)`). -/
theorem goodProps_iso_apply {n : ℕ} (c : Fin (n + 2) → PropFactor)
    (hlast : c (Fin.last (n + 1)) = .ident) (a b : Fin (m * W)) {φ : ℝ} (hφ : 0 ≤ φ)
    (f : (Fin (n + 2) → Fin (m * W)) → ℂ) (hf : ∀ y, ‖f y‖ ≤ φ * P.sIso a b y s)
    (x : Fin (n + 2) → Fin (m * W)) :
    ‖propOp (goodProp (shortRingProfile d.b m W) P.z c s t) f x‖ ≤
      kernelActionConst d ^ (n + 1) * φ * Real.sqrt (P.lEta t / P.lEta s) * P.sIso a b x t := by
  rw [propOp_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y * f y‖
      ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * (φ * P.sIso a b y s) :=
        Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hf y) (norm_nonneg _)
    _ = φ * ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sIso a b y s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ φ * (kernelActionConst d ^ (n + 1) * Real.sqrt (P.lEta t / P.lEta s) *
          P.sIso a b x t) :=
        mul_le_mul_of_nonneg_left (goodProps_iso d hm hW P hPW hPD hz hs0 hst ht1 c hlast a b x)
          hφ
    _ = _ := by ring

/-- `goodProps_av` for functions: if `|g(y)| ≤ φ s^av_{k,s}(y)` then
`|U g(x)| ≤ C_P^k φ (L_t/L_s) s^av_{k,t}(x)`. -/
theorem goodProps_av_apply {n : ℕ} (c : Fin (n + 2) → PropFactor)
    (hlast : c (Fin.last (n + 1)) ≠ .sat) {φ : ℝ} (hφ : 0 ≤ φ)
    (g : (Fin (n + 2) → Fin (m * W)) → ℂ) (hg : ∀ y, ‖g y‖ ≤ φ * P.sAv y s)
    (x : Fin (n + 2) → Fin (m * W)) :
    ‖propOp (goodProp (shortRingProfile d.b m W) P.z c s t) g x‖ ≤
      kernelActionConst d ^ (n + 2) * φ * (P.lEta t / P.lEta s) * P.sAv x t := by
  rw [propOp_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y * g y‖
      ≤ ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * (φ * P.sAv y s) :=
        Finset.sum_le_sum fun y _ => by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hg y) (norm_nonneg _)
    _ = φ * ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ φ * (kernelActionConst d ^ (n + 2) * (P.lEta t / P.lEta s) * P.sAv x t) :=
        mul_le_mul_of_nonneg_left (goodProps_av d hm hW P hPW hPD hz hs0 hst ht1 c hlast x) hφ
    _ = _ := by ring

omit hm hW hPW hPD hz hs0 hst ht1 in
/-- Cyclic invariance of `s^av_{n+2}`: `s^av(y ∘ (· + c)) = s^av(y)`. -/
theorem sAv_comp_addRight {n : ℕ} (c : Fin (n + 2)) (y : Fin (n + 2) → Fin (m * W)) (r : ℝ) :
    P.sAv (fun i => y (i + c)) r = P.sAv y r := by
  unfold Psi.PsiData.sAv
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  congr 2
  have hrot : ∀ i : Fin (n + 2), finRotate (n + 2) i = i + 1 := fun i => finRotate_apply i
  simp only [hrot]
  rw [← Equiv.prod_comp (Equiv.addRight c) (fun i => P.ups r (y i) (y (i + 1)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Equiv.coe_addRight]
  rw [add_right_comm]

/-- **Good propagator bound, averaged chains, any position** (rotate cyclically so that the
non-saturated factor is the last one): for chain length `k = n+2` and factors `c` with some
non-saturated factor `c j`, `Σ_y |U(x,y)| s^av_{k,s}(y) ≤ C_P^k (L_t/L_s) s^av_{k,t}(x)`. -/
theorem goodProps_av_any {n : ℕ} (c : Fin (n + 2) → PropFactor) (j : Fin (n + 2))
    (hj : c j ≠ .sat) (x : Fin (n + 2) → Fin (m * W)) :
    ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s ≤
      kernelActionConst d ^ (n + 2) * (P.lEta t / P.lEta s) * P.sAv x t := by
  set σ : Fin (n + 2) ≃ Fin (n + 2) := Equiv.addRight (j + 1) with hσ
  have hσl : σ (Fin.last (n + 1)) = j := by
    rw [hσ, Equiv.coe_addRight]
    show Fin.last (n + 1) + (j + 1) = j
    rw [add_comm j 1, ← add_assoc, Fin.last_add_one, zero_add]
  set c' : Fin (n + 2) → PropFactor := fun i => c (σ i) with hc'
  have hc'l : c' (Fin.last (n + 1)) ≠ .sat := by rw [hc']; dsimp only; rw [hσl]; exact hj
  have hnorm : ∀ x y : Fin (n + 2) → Fin (m * W),
      ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ =
        ‖goodProp (shortRingProfile d.b m W) P.z c' s t (fun i => x (σ i)) (fun i => y (σ i))‖ := by
    intro x y
    rw [norm_goodProp, norm_goodProp]
    unfold tensorR
    exact (Equiv.prod_comp σ (fun i => goodPropNorm (shortRingProfile d.b m W) P.z c s t i
      (x i) (y i))).symm
  set e : (Fin (n + 2) → Fin (m * W)) ≃ (Fin (n + 2) → Fin (m * W)) :=
    σ.symm.arrowCongr (Equiv.refl _) with he
  have happ : ∀ y : Fin (n + 2) → Fin (m * W), e y = fun i => y (σ i) := by
    intro y
    funext i
    simp [he, Equiv.arrowCongr_apply]
  have hsum : ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c s t x y‖ * P.sAv y s =
      ∑ y, ‖goodProp (shortRingProfile d.b m W) P.z c' s t (fun i => x (σ i)) y‖ *
        P.sAv y s := by
    refine Fintype.sum_equiv e _ _ fun y => ?_
    rw [happ, hnorm x y, hσ]
    simp only [Equiv.coe_addRight]
    rw [sAv_comp_addRight P (j + 1) y s]
  rw [hsum]
  refine (goodProps_av d hm hW P hPW hPD hz hs0 hst ht1 c' hc'l (fun i => x (σ i))).trans ?_
  rw [hσ]
  simp only [Equiv.coe_addRight]
  rw [sAv_comp_addRight P (j + 1) x t]

end Psi

end BlockBand.Native.ErdosRiabov.Propagator
