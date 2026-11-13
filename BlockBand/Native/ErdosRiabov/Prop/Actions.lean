module

public import BlockBand.Native.ErdosRiabov.Prop.Single

/-!
# One-variable kernel actions

Bounds on the one-site propagators `P̂_{s,t}`, `Q̂_{s,t}` and their actions on products of square
roots of the control `Υ` (`kernelActions`, items (P1)–(P5)): (P1) entry bounds
`|P̂(a,x)| ≤ δ_{ax} + (C_K/c_m) η_s Υ(a,x)` and reality and positivity of `P̂`; (P2) the action of
`P̂_{s,t}` from `Υ_s` to `Υ_t`; (P3) the action of `Q̂` and `conj Q̂` at arbitrary heights; (P4)
the mixed-time action with the factor `√(L_s/L_t)`; (P5) the action at time `t` with the factor
`η_s/η_t`.

Setting: VS data `d`, `m ≥ 4`, `W ≥ 1`, `N = mW`,
`S = shortRingProfile d.b m W`, `z ∈ 𝒟`, `m(z) = semicircleM z`, `η_r = vsHeight z r`,
`Υ_r = polynomialControl N W d.D η_r`, `L_r = ℓ(η_r) η_r`, `0 ≤ s ≤ t ≤ 1`;
`P̂_{s,t} = vsPropagator S m (conj m) s t`, `Q̂_{s,t} = vsPropagator S m m s t` (and
`conj Q̂ = vsPropagator S (conj m) (conj m) s t`). Constants: `K = C_K/c_m` (`vsCK d / d.cm`),
`C_P = 1 + K C_wc` (`kernelActionConst d`), `C_wc = d.Cwc = (C₁'')^{3/2}`. Entrywise absolute
values `‖P̂_{ua}‖` are used throughout (so the bounds hold for `|P̂|` as well; `P̂ ≥ 0`).
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

/-- The kernel-action constant `C_P = 1 + (C_K/c_m) C_wc`. -/
def kernelActionConst (d : VSData) : ℝ := 1 + vsCK d / d.cm * d.Cwc

/-!
## Helpers
-/

/-- `Σ_a |B_a| g_a ≤ g_u + c Σ_a V_a g_a` if `|B_a| ≤ δ_{ua} + c V_a`, `g ≥ 0`. -/
theorem prop_sum_delta_le {n : ℕ} (B : Fin n → ℂ) (V g : Fin n → ℝ) (u : Fin n) {c : ℝ}
    (hg : ∀ a, 0 ≤ g a) (hB : ∀ a, ‖B a‖ ≤ (if u = a then 1 else 0) + c * V a) :
    ∑ a, ‖B a‖ * g a ≤ g u + c * ∑ a, V a * g a := by
  calc ∑ a, ‖B a‖ * g a ≤ ∑ a, ((if u = a then 1 else 0) + c * V a) * g a :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hB a) (hg a)
    _ = g u + c * ∑ a, V a * g a := by
        simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum, mul_assoc]

/-- `√(A·B·C·C) = C √(A·B)` for `C ≥ 0`. -/
theorem prop_sqrt_mul_sq (A B : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    Real.sqrt (A * B * C * C) = C * Real.sqrt (A * B) := by
  rw [show A * B * C * C = (C * C) * (A * B) by ring, Real.sqrt_mul (mul_self_nonneg C),
    Real.sqrt_mul_self hC]

/-- `√(K a) √(K b) = K √(a b)` for `K, a ≥ 0`. -/
theorem prop_sqrt_mul_const {K a b : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) :
    Real.sqrt (K * a) * Real.sqrt (K * b) = K * Real.sqrt (a * b) := by
  rw [← Real.sqrt_mul (mul_nonneg hK ha), show K * a * (K * b) = (K * K) * (a * b) by ring,
    Real.sqrt_mul (mul_self_nonneg K), Real.sqrt_mul_self hK]

/-- `C_wc = C₁'' √C₁''`. -/
theorem vsData_Cwc_eq (d : VSData) : d.Cwc = d.C1pp * Real.sqrt d.C1pp := by
  have hC : 0 < d.C1pp := lt_of_lt_of_le one_pos d.one_le_C1pp
  rw [VSData.Cwc, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hC, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-!
## The kernel actions
-/

section Actions

variable (d : VSData) {m W : ℕ} (hm : 4 ≤ m) (hW : 0 < W) {z : ℂ}
  (hz : BulkDomain (m * W) d.delta0 d.kappa d.C0 z)
include hm hW hz

/-- For VS data `d`, `m ≥ 4`, `W ≥ 1`, `z ∈ 𝒟`, `0 ≤ s ≤ t ≤ 1`, `r₁, r₂ ∈ [0,1]`, all sites
(notation of the module header, `K = C_K/c_m`, `C_P = kernelActionConst d`):
(P1) `|P̂_{s,t}(a,x)| ≤ δ_{ax} + K η_s Υ_t(a,x)`, `|Q̂_{s,t}(a,x)| ≤ δ_{ax} + K η_s Υ_0(a,x)`,
`P̂_{s,t}` real and `≥ 0`;
(P2) `Σ_a |P̂_{s,t}(u,a)| √(Υ_s(x,a)Υ_s(a,y)) ≤ C_P √(Υ_t(x,u)Υ_t(u,y))`;
(P3) `Σ_a |Q̂_{s,t}(u,a)| √(Υ_{r₁}(x,a)Υ_{r₂}(a,y)) ≤ C_P √(Υ_{r₁}(x,u)Υ_{r₂}(u,y))`, and the
same for `conj Q̂`;
(P4) `Σ_a |P̂_{s,t}(u,a)| √(Υ_t(x,a)Υ_s(a,y)) ≤ C_P √(L_s/L_t) √(Υ_t(x,u)Υ_t(u,y))`;
(P5) `Σ_a |P̂_{s,t}(u,a)| √(Υ_t(x,a)Υ_t(a,y)) ≤ C_P (η_s/η_t) √(Υ_t(x,u)Υ_t(u,y))`.
-/
theorem kernelActions {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) {r₁ r₂ : ℝ}
    (hr₁0 : 0 ≤ r₁) (hr₁1 : r₁ ≤ 1) (hr₂0 : 0 ≤ r₂) (hr₂1 : r₂ ≤ 1) :
    -- (P1)
    (∀ a x,
      ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) s t a x‖ ≤
        (if a = x then 1 else 0) + vsCK d / d.cm * vsHeight z s *
          polynomialControl (m * W) W d.D (vsHeight z t) a x) ∧
    (∀ a x,
      ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (semicircleM z) s t a x‖ ≤
        (if a = x then 1 else 0) + vsCK d / d.cm * vsHeight z s *
          polynomialControl (m * W) W d.D (vsHeight z 0) a x) ∧
    (∀ a x,
      (vsPropagator (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) s t a x).im
        = 0 ∧
      0 ≤ (vsPropagator (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) s t
        a x).re) ∧
    -- (P2)
    (∀ u x y, ∑ a,
      ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z s) x a *
          polynomialControl (m * W) W d.D (vsHeight z s) a y) ≤
      kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x u *
        polynomialControl (m * W) W d.D (vsHeight z t) u y)) ∧
    -- (P3)
    (∀ u x y, ∑ a,
      ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (semicircleM z) s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z r₁) x a *
          polynomialControl (m * W) W d.D (vsHeight z r₂) a y) ≤
      kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z r₁) x u *
        polynomialControl (m * W) W d.D (vsHeight z r₂) u y)) ∧
    (∀ u x y, ∑ a,
      ‖vsPropagator (shortRingProfile d.b m W) (conj (semicircleM z)) (conj (semicircleM z))
          s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z r₁) x a *
          polynomialControl (m * W) W d.D (vsHeight z r₂) a y) ≤
      kernelActionConst d * Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z r₁) x u *
        polynomialControl (m * W) W d.D (vsHeight z r₂) u y)) ∧
    -- (P4)
    (∀ u x y, ∑ a,
      ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x a *
          polynomialControl (m * W) W d.D (vsHeight z s) a y) ≤
      kernelActionConst d *
        Real.sqrt ((ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s) /
          (ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t)) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x u *
          polynomialControl (m * W) W d.D (vsHeight z t) u y)) ∧
    -- (P5)
    (∀ u x y, ∑ a,
      ‖vsPropagator (shortRingProfile d.b m W) (semicircleM z) (conj (semicircleM z)) s t u a‖ *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x a *
          polynomialControl (m * W) W d.D (vsHeight z t) a y) ≤
      kernelActionConst d * (vsHeight z s / vsHeight z t) *
        Real.sqrt (polynomialControl (m * W) W d.D (vsHeight z t) x u *
          polynomialControl (m * W) W d.D (vsHeight z t) u y)) := by
  have hN : 0 < m * W := Nat.mul_pos (by omega) hW
  have hη := hz.im_pos hN
  have ht0 : 0 ≤ t := hs0.trans hst
  -- ups at the needed pairs of times
  obtain ⟨-, -, -, -, hU3st, -, hU4st, -, hU6st, -, -, -, -⟩ :=
    ups_U2_U8_vs d hm hW hz hs0 hst ht1
  obtain ⟨-, -, -, -, -, -, hU4tt, -, hU6tt, -, -, -, -⟩ :=
    ups_U2_U8_vs d hm hW hz ht0 le_rfl ht1
  set S := shortRingProfile d.b m W with hSdef
  set μ := semicircleM z with hμdef
  set Υ := polynomialControl (m * W) W d.D with hΥdef
  have hsym : ∀ h x y, Υ h x y = Υ h y x := fun h x y => polynomialControl_symm _ _ _ h x y
  have hpos : ∀ r : ℝ, r ≤ 1 → ∀ x y, 0 ≤ Υ (vsHeight z r) x y := fun r hr x y =>
    (polynomialControl_pos hN hW d.D (vsHeight_pos hη hr) x y).le
  obtain ⟨hP1, hQ1, hPr⟩ := lemmaK_K6_single d.b_pos d.b_lt_half d.delta0_pos d.kappa_pos
    d.C0_ge_one d.D_ge_six hm hW hz hs0 hst ht1
  set K := vsCK d / d.cm with hKdef
  have hK : 0 ≤ K := div_nonneg (vsCK_pos d).le d.cm_pos.le
  have hCwc : 0 ≤ d.Cwc := le_trans zero_le_one d.one_le_Cwc
  have hCP : 1 ≤ kernelActionConst d := by
    unfold kernelActionConst
    have := mul_nonneg hK hCwc
    linarith
  have hηt := vsHeight_pos hη ht1
  have hηs := vsHeight_pos hη (hst.trans ht1)
  have hts : vsHeight z t ≤ vsHeight z s := by
    rw [vsHeight_affine z t, vsHeight_affine z s]
    nlinarith [semicircleM_im_pos hη]
  have hsle0 : vsHeight z s ≤ vsHeight z 0 := by
    rw [vsHeight_affine z s, vsHeight_affine z 0]
    nlinarith [semicircleM_im_pos hη]
  have hcoef : K * vsHeight z s * (d.Cwc / vsHeight z s) = K * d.Cwc := by
    field_simp
  -- (P1) entry bounds
  have hP1' : ∀ a x, ‖vsPropagator S μ (conj μ) s t a x‖ ≤
      (if a = x then 1 else 0) + K * vsHeight z s * Υ (vsHeight z t) a x := hP1
  have hQ1' : ∀ a x, ‖vsPropagator S μ μ s t a x‖ ≤
      (if a = x then 1 else 0) + K * vsHeight z s * Υ (vsHeight z 0) a x := hQ1
  -- (P3) core, for any propagator with the `Q̂` entry bound
  have hP3core : ∀ B : Fin (m * W) → Fin (m * W) → ℂ,
      (∀ a x, ‖B a x‖ ≤ (if a = x then 1 else 0) + K * vsHeight z s * Υ (vsHeight z 0) a x) →
      ∀ u x y, ∑ a, ‖B u a‖ * Real.sqrt (Υ (vsHeight z r₁) x a * Υ (vsHeight z r₂) a y) ≤
        kernelActionConst d * Real.sqrt (Υ (vsHeight z r₁) x u * Υ (vsHeight z r₂) u y) := by
    intro B hB u x y
    obtain ⟨-, -, -, -, -, -, -, hU5a, -, -, -, -, -⟩ :=
      ups_U2_U8_vs d hm hW hz le_rfl hr₁0 hr₁1
    obtain ⟨-, -, -, -, -, -, -, hU5b, -, -, -, -, -⟩ :=
      ups_U2_U8_vs d hm hW hz le_rfl hr₂0 hr₂1
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
  refine ⟨hP1', hQ1', hPr, fun u x y => ?_, hP3core _ hQ1', ?_, fun u x y => ?_,
    fun u x y => ?_⟩
  · -- (P2)
    have hsum : ∑ a, Υ (vsHeight z t) u a *
        Real.sqrt (Υ (vsHeight z s) x a * Υ (vsHeight z s) a y) ≤
        d.Cwc / vsHeight z s * Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) := by
      have h6 := hU6st x y u u
      rw [hsym (vsHeight z t) y u] at h6
      refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_) h6
      rw [hsym (vsHeight z s) y a, hsym (vsHeight z t) a u,
        prop_sqrt_mul_sq _ _ (hpos t ht1 u a)]
    have hmain := prop_sum_delta_le (vsPropagator S μ (conj μ) s t u)
      (fun a => Υ (vsHeight z t) u a)
      (fun a => Real.sqrt (Υ (vsHeight z s) x a * Υ (vsHeight z s) a y)) u
      (fun a => Real.sqrt_nonneg _) (hP1' u)
    have hδ : Real.sqrt (Υ (vsHeight z s) x u * Υ (vsHeight z s) u y) ≤
        Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) :=
      Real.sqrt_le_sqrt (mul_le_mul (hU3st x u) (hU3st u y) (hpos s (hst.trans ht1) u y)
        (hpos t ht1 x u))
    have hKs : 0 ≤ K * vsHeight z s := mul_nonneg hK hηs.le
    refine hmain.trans ?_
    calc _ ≤ Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) +
          K * vsHeight z s * (d.Cwc / vsHeight z s *
            Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y)) :=
          add_le_add hδ (mul_le_mul_of_nonneg_left hsum hKs)
      _ = _ := by rw [← mul_assoc, hcoef, kernelActionConst]; ring
  · -- (P3), conjugate
    intro u x y
    have hconj : ∀ a x', ‖vsPropagator S (conj μ) (conj μ) s t a x'‖ =
        ‖vsPropagator S μ μ s t a x'‖ := fun a x' => by
      have hm1 := norm_semicircleM_lt_one hη.ne'
      rw [vsPropagator_conj (shortRingProfile_stochasticSymm d.b_pos d.b_lt_half
        (by omega : 3 ≤ m) hW) (norm_smul_lt_one hm1 hm1 ht0 ht1), Complex.norm_conj]
    have h := hP3core (vsPropagator S (conj μ) (conj μ) s t)
      (fun a x' => (hconj a x').trans_le (hQ1' a x')) u x y
    exact h
  · -- (P4)
    set Ls := ErdosRiabov.localizationLength (m * W) W (vsHeight z s) * vsHeight z s with hLs
    set Lt := ErdosRiabov.localizationLength (m * W) W (vsHeight z t) * vsHeight z t with hLt
    have hLt0 : 0 < Lt := mul_pos (loc_pos hN hW hηt) hηt
    have hLst : Lt ≤ Ls := loc_mul_mono (m * W) W hηt hts
    have hC1 : 0 < d.C1pp := lt_of_lt_of_le one_pos d.one_le_C1pp
    have hratio : 1 ≤ Real.sqrt (Ls / Lt) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hLt0]; linarith)
    set M := Real.sqrt (d.C1pp / Lt * Υ (vsHeight z t) u x) with hM
    have hsum : ∑ a, Υ (vsHeight z t) u a *
        Real.sqrt (Υ (vsHeight z t) x a * Υ (vsHeight z s) a y) ≤
        M * (d.C1pp / vsHeight z s * Real.sqrt (Ls * Υ (vsHeight z t) y u)) := by
      calc ∑ a, Υ (vsHeight z t) u a *
            Real.sqrt (Υ (vsHeight z t) x a * Υ (vsHeight z s) a y)
          = ∑ a, Real.sqrt (Υ (vsHeight z t) u a * Υ (vsHeight z t) a x) *
              Real.sqrt (Υ (vsHeight z s) y a * Υ (vsHeight z t) a u) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Real.sqrt_mul (mul_nonneg (hpos t ht1 u a) (hpos t ht1 a x)),
              hsym (vsHeight z t) a x, hsym (vsHeight z s) y a, hsym (vsHeight z t) a u,
              show Υ (vsHeight z t) u a * Υ (vsHeight z t) x a *
                  (Υ (vsHeight z s) a y * Υ (vsHeight z t) u a) =
                Υ (vsHeight z t) x a * Υ (vsHeight z s) a y * Υ (vsHeight z t) u a *
                  Υ (vsHeight z t) u a by ring,
              prop_sqrt_mul_sq _ _ (hpos t ht1 u a)]
        _ ≤ ∑ a, M * Real.sqrt (Υ (vsHeight z s) y a * Υ (vsHeight z t) a u) :=
            Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right
              (Real.sqrt_le_sqrt ((hU4tt u x).1 a)) (Real.sqrt_nonneg _)
        _ = M * ∑ a, Real.sqrt (Υ (vsHeight z s) y a * Υ (vsHeight z t) a u) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ M * (d.C1pp / vsHeight z s * Real.sqrt (Ls * Υ (vsHeight z t) y u)) :=
            mul_le_mul_of_nonneg_left (hU4st y u).2 (Real.sqrt_nonneg _)
    have hprod : M * Real.sqrt (Ls * Υ (vsHeight z t) y u) =
        Real.sqrt d.C1pp * Real.sqrt (Ls / Lt) *
          Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) := by
      rw [hM, ← Real.sqrt_mul (mul_nonneg (div_nonneg hC1.le hLt0.le) (hpos t ht1 u x)),
        ← Real.sqrt_mul hC1.le, ← Real.sqrt_mul (mul_nonneg hC1.le
          (div_nonneg (le_trans hLt0.le hLst) hLt0.le)), hsym (vsHeight z t) u x,
        hsym (vsHeight z t) y u]
      congr 1
      ring
    have hmain := prop_sum_delta_le (vsPropagator S μ (conj μ) s t u)
      (fun a => Υ (vsHeight z t) u a)
      (fun a => Real.sqrt (Υ (vsHeight z t) x a * Υ (vsHeight z s) a y)) u
      (fun a => Real.sqrt_nonneg _) (hP1' u)
    have hsq := Real.sqrt_nonneg (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y)
    have hδ : Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z s) u y) ≤
        Real.sqrt (Ls / Lt) * Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) := by
      refine le_trans ?_ (le_mul_of_one_le_left hsq hratio)
      exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hU3st u y) (hpos t ht1 x u))
    have hKs : 0 ≤ K * vsHeight z s := mul_nonneg hK hηs.le
    refine hmain.trans ?_
    calc _ ≤ Real.sqrt (Ls / Lt) * Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) +
          K * vsHeight z s *
            (M * (d.C1pp / vsHeight z s * Real.sqrt (Ls * Υ (vsHeight z t) y u))) :=
          add_le_add hδ (mul_le_mul_of_nonneg_left hsum hKs)
      _ = Real.sqrt (Ls / Lt) * Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) +
          K * (d.C1pp * Real.sqrt d.C1pp) * Real.sqrt (Ls / Lt) *
            Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) := by
          rw [show K * vsHeight z s * (M * (d.C1pp / vsHeight z s *
              Real.sqrt (Ls * Υ (vsHeight z t) y u))) =
            K * d.C1pp * (vsHeight z s / vsHeight z s) *
              (M * Real.sqrt (Ls * Υ (vsHeight z t) y u)) by ring,
            div_self hηs.ne', hprod]
          ring
      _ = _ := by rw [kernelActionConst, vsData_Cwc_eq]; ring
  · -- (P5)
    have hsum : ∑ a, Υ (vsHeight z t) u a *
        Real.sqrt (Υ (vsHeight z t) x a * Υ (vsHeight z t) a y) ≤
        d.Cwc / vsHeight z t * Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) := by
      have h6 := hU6tt x y u u
      rw [hsym (vsHeight z t) y u] at h6
      refine le_of_eq_of_le (Finset.sum_congr rfl fun a _ => ?_) h6
      rw [hsym (vsHeight z t) y a, hsym (vsHeight z t) a u,
        prop_sqrt_mul_sq _ _ (hpos t ht1 u a)]
    have hmain := prop_sum_delta_le (vsPropagator S μ (conj μ) s t u)
      (fun a => Υ (vsHeight z t) u a)
      (fun a => Real.sqrt (Υ (vsHeight z t) x a * Υ (vsHeight z t) a y)) u
      (fun a => Real.sqrt_nonneg _) (hP1' u)
    have hsq := Real.sqrt_nonneg (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y)
    have hr1 : 1 ≤ vsHeight z s / vsHeight z t := by rw [le_div_iff₀ hηt]; linarith
    have hKs : 0 ≤ K * vsHeight z s := mul_nonneg hK hηs.le
    refine hmain.trans ?_
    calc _ ≤ vsHeight z s / vsHeight z t *
            Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y) +
          K * vsHeight z s * (d.Cwc / vsHeight z t *
            Real.sqrt (Υ (vsHeight z t) x u * Υ (vsHeight z t) u y)) :=
          add_le_add (le_mul_of_one_le_left hsq hr1) (mul_le_mul_of_nonneg_left hsum hKs)
      _ = _ := by rw [kernelActionConst]; ring

end Actions

end BlockBand.Native.ErdosRiabov.Propagator
