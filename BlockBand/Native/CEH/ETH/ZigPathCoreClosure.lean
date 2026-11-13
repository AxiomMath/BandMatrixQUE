module

public import BlockBand.Native.CEH.ETH.ZigPathCoreX
public import BlockBand.Native.CEH.ETH.ZigPathCoreY
public import BlockBand.Native.CEH.ETH.ZigPathCoreZ

/-!
# CEH ETH, two-resolvent zig: the deterministic one-path closure

On one sample path where all the pathwise hypotheses hold, the coupled bootstrap for the
three processes `X`, `Y`, `Z` closes on all of `[0, s]`.

## Setting (`ZigPathCore`)

* `G : zpc_Geom`, `G.Valid`: `s ≥ 0`, `N > 0`, `η_i > 0`, `ρ_i > 0`, `c_i = π ρ_i`, a constant
  control `S > 0` (in the application `S = s₂(s) ≥ s₂(σ)`, by `sTwoAt_mono`).
  Heights `η_{i,t} = G.e_i t = η_i + c_i (s - t)`, `P_t = G.P t = η_{1,t} η_{2,t}`.
* Units `U_X(t) = √(ρ₁ρ₂) S / √(N P_t)`, `U_Y(t) = 1/(N P_t)`, `U_Z = ρ₁ρ₂ S²`;
  `ℓ₂ = 1/(c₁η₁) + 1/(c₂η₂)`, `gm = √(c₁η₁ c₂η₂)`; grid `h_ℓ = P_0/2^ℓ`.
* `p : zpc_Par`: `lam` (`N^{ξ/4}`), `θX = θY` (`N^{2ξ}`), `θZ` (`N^ξ`), `βZ` (`N^{ξ/2}`),
  `Tz` (`N^ζ`), `Lmax` (`≥ log(P_0/P_s)`), `Cm` (`C₅₆`), `Lg` (grid length).
* `D : zpc_Proc ι κ`: the processes; `h : zpc_Hyp G p D`: the pathwise hypotheses;
  `hS : zpc_Small G p`: the numeric hypotheses.

## Headline

`zpc_closure`: for `[Finite ι] [Finite κ]`, on all of `[0, s]`
* `‖X_k(t)‖ ≤ (1 + Lmax/2) K_X U_X(t)` and `‖X_k(t)‖ < θX U_X(t)`;
* `‖Y_j(t)‖ ≤ (1 + Lmax) K_Y U_Y(t)` and `‖Y_j(t)‖ < θY U_Y(t)`;
* `|Z(t)| ≤ βZ U_Z` and `|Z(t)| < θZ U_Z`.
`zpc_closure_endpoint`: `|Z(s)| ≤ βZ ρ₁ρ₂ S²` (with `S = s₂(s)`: `|Z_s| ≤ N^{ξ/2} ρ₁ρ₂ s₂(s)²`).
In the sibling module `ZigPathCoreWindow`: `zpc_small_of_ne`, the numeric hypotheses from their
window form, with `n_e ≤ N ρ_i η_i`
(`n_e = N^{ε_ρ}`): `gm ≥ π n_e/N`, `ℓ₂ ≤ 2N/(π n_e)`, `1/√(N c_i η_i) ≤ 1/√(π n_e)`.
`zpc_closure_rpow`, the headline with `lam = N^{ξ/4}`, `θX = θY = N^{2ξ}`, `θZ = N^ξ`,
`βZ = N^{ξ/2}`, `Tz = N^ζ` and the window-form numeric hypotheses.

## Martingale parameters (for the tails, `ZigTail`)

At grid level `ℓ ≤ Lg` (`h_ℓ = P_0/2^ℓ`), with `a = lam √b`, so `a²/(2b) = lam²/2`
(`= N^{ξ/2}/2` for `lam = N^{ξ/4}`; Freedman gives `2 exp(-N^{ξ/2}/2)` per event):
* `X` (Re and Im of each of the four constellations): `zpc_bX ℓ = θZ U_Z ℓ₂ / (N² h_ℓ)`,
  `zpc_aX ℓ = lam √(zpc_bX ℓ)`;
* `Y` (Re and Im of each constellation): `zpc_bY ℓ = 3 / (N² h_ℓ²)`, `zpc_aY ℓ = lam √(zpc_bY ℓ)`;
* `Z` (one level): `zpc_bZ = 2 θZ² U_Z² ℓ₂ / N`, `zpc_aZ = lam √zpc_bZ`.

## Sources of the hypotheses

Each field of the structure `zpc_Hyp` (defined in `ZigPathCore`; all on `[0, s]`) and the lemma
that discharges it in the application. The names in this list are field names, not declarations of
this file; the validity condition is `zpc_Geom.Valid`.

* `zpc_Geom.Valid`: positivity and `c_i = π ρ_i`: window data,
  `abs_im_normalizedTrace_eq_pi_mul_sourceDensity`; `S = s₂(s) > 0` when `A° ≠ 0` (for
  `A° = 0` the bad event is empty).
* `contX`, `contY`, `contZ`: continuity of the chain paths (continuity of the `flowResolvent`
  paths). `contCfX`, `contCfY`: continuity of `⟨M^I_σ⟩` (`continuousOn_ratCoeff`).
  `intDX`, `intDY`, `intDZ`: the drifts are continuous on `[0, s]`.
* `X0`, `Y0`: `R_{i,0} = M_i` and the deterministic approximation at `σ = 0`. `Z0`:
  `Z_0 = chainP` and `√chainP ≤ π √(ρ₁ρ₂) s₂(0)` (`sqrt_chain_le`), `s₂(0) ≤ S` (`sTwoAt_mono`).
* `decX`, `decY`: `isContinuousSemimartingale_avgRe2_flowResolvent`,
  `isContinuousSemimartingale_avgIm2_flowResolvent` (`B = 1`; path functions `ztl_mX`).
  `decZ`: `isContinuousSemimartingale_imChain_flowResolvent` (`ztl_mZ`).
* `cfX_le`, `cfY_le`: `norm_NTrace_twoResApprox_one_le_mde`.
* `driftX`: the drift (`B = 1`) and `hasDerivAt_NTrace_twoResApprox_mul`
  (`d⟨M^A⟩ = ⟨M^A⟩⟨M^I⟩`): the drift of `X` is
  `⟨M^I⟩X + ⟨M^A⟩Y + XY + W₁⟨R₁²AR₂⟩ + W₂⟨R₁AR₂²⟩`.
* `driftY`: the same with `A = 1`: `2⟨M^I⟩Y + Y² + W₁⟨R₁²R₂⟩ + W₂⟨R₁R₂²⟩`.
* `driftZ`: `fz_driftC_eq_ceh` and `bf_zDrift_four` (the tube part, with `|Im a| ≤ ‖a‖`), plus
  the cross terms `cross`.
* `MA_le`: `lemma56_window_bound` (`≤ C₅₆ √chainP`), `sqrt_chain_le`, `sTwoAt_mono`
  (`s₂(σ) ≤ s₂(s) = S`).
* `cross_le`: each factor of the four products is a combination with coefficients `¼` or `½`
  of the four chains `⟨R₁^a A R₂^b⟩ = X^{ab} + ⟨M^A_{ab}⟩` (`zcl_norm_cross_le`).
* `QX₁_le`, `QX₂_le`: `bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le`,
  `bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le`, all constellations
  (`bf_norm_normalizedTrace_bwImChain_conj_left/right`).
* `QY₁_le`, `QY₂_le`: `bw_norm_normalizedTrace_resolvent_sq_mul_resolvent_le_div`,
  `bw_norm_normalizedTrace_resolvent_mul_resolvent_sq_le_div`.
* `V₁_le`, `V₂_le` (and the middle form): `bw_norm_normalizedTrace_imChain_mul_resolvent_le`,
  `bw_norm_normalizedTrace_imChain_mid_resolvent_le`,
  `bf_norm_normalizedTrace_imChain_mid_conjTranspose_resolvent_le`.
* `W₁_le`, `W₂_le`, `imR₁_le`, `imR₂_le` (tube, `Tz = N^ζ`): `flowTube_holds_flowResolvent` at
  `z₁` and `z₂`, adjoints by conjugation.
* `TI_le₁`, `TI_le₂` (min form): `bf_norm_normalizedTrace_imaginaryPart_mul_le`
  (`|⟨Im R₁ Im R₂⟩| ≤ |⟨Im R₁⟩|/η₂`, and swapped by cyclicity) plus the tube.
* `brkXre_le`, `brkXim_le`: `bf_avgRe2_bracket_X_le`, `bf_avgIm2_bracket_X_le`.
  `brkYre_le`, `brkYim_le`: `bf_avgRe2_bracket_Y_le`, `bf_avgIm2_bracket_Y_le`.
  `brkZ_le`: `bf_avg_bracket_Z_le_sq`. `brk*_nonneg`: sums of squares.
* `martXre`, `martXim`, `martYre`, `martYim`, `martZ`: the martingale controls of `ZigTail`
  (`ztl_control_of_not_mem`), `∀ t ∈ Set.Icc 0 s, (∫ r in Set.Ioc 0 t, brk r) ≤ b ℓ →
  |m t| < a ℓ` with `a ℓ`, `b ℓ` as above, `ℓ ≤ Lg`.
* `zpc_Small`: numeric, discharged for `N ≥ N₀` (`zpc_small_of_ne`, `zpc_closure_rpow`) when
  `ζ < 2ξ` with a log margin, `2ξ < ε_ρ` and `ξ < 2ε_ρ/7`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open Set MeasureTheory intervalIntegral
open BlockBand.Native.CEH.Zig

variable {ι κ : Type*} {G : zpc_Geom} {p : zpc_Par} {D : zpc_Proc ι κ}

/-- `π² ≤ K_Z`. -/
theorem zpc_pi_sq_le_KZ (hG : G.Valid) (hS : zpc_Small G p) : Real.pi ^ 2 ≤ zpc_KZ G p := by
  have := hS.lam_nonneg
  have := hS.Tz_nonneg
  have := hS.θZ_pos
  have := hG.ell2_pos
  have := hG.N_pos
  have := hG.gm_pos
  have := hG.s_nonneg
  unfold zpc_KZ
  have : 0 ≤ p.lam * p.θZ * Real.sqrt (2 * G.ell2 / G.N) := by positivity
  have : 0 ≤ 3 * p.Tz * p.θZ * G.ell2 / G.N := by positivity
  have : 0 ≤ 8 * G.s * p.Cm ^ 2 * Real.pi ^ 2 := by positivity
  have : 0 ≤ 8 * p.θX ^ 2 / (G.N * G.gm) := by positivity
  linarith

/-- **The deterministic one-path closure of the coupled two-resolvent zig** (CEH §7.1 in
variance time). On all of `[0, s]`:
`‖X_k‖ ≤ (1 + Lmax/2) K_X U_X < θX U_X`, `‖Y_j‖ ≤ (1 + Lmax) K_Y U_Y < θY U_Y`,
`|Z| ≤ βZ U_Z < θZ U_Z`. -/
theorem zpc_closure [Finite ι] [Finite κ] (hG : G.Valid) (hS : zpc_Small G p)
    (h : zpc_Hyp G p D) :
    ∀ t ∈ Icc 0 G.s,
      (∀ k, ‖D.X k t‖ ≤ (1 + p.Lmax / 2) * zpc_KX G p * G.UX t ∧
        ‖D.X k t‖ < p.θX * G.UX t) ∧
      (∀ j, ‖D.Y j t‖ ≤ (1 + p.Lmax) * zpc_KY G p * G.UY t ∧
        ‖D.Y j t‖ < p.θY * G.UY t) ∧
      |D.Z t| ≤ p.βZ * G.UZ ∧ |D.Z t| < p.θZ * G.UZ := by
  set g : ι ⊕ (κ ⊕ Unit) → ℝ → ℝ :=
    Sum.elim (fun k t => ‖D.X k t‖) (Sum.elim (fun j t => ‖D.Y j t‖) fun _ t => |D.Z t|)
    with hg
  set θ : ι ⊕ (κ ⊕ Unit) → ℝ → ℝ :=
    Sum.elim (fun _ t => p.θX * G.UX t) (Sum.elim (fun _ t => p.θY * G.UY t)
      fun _ _ => p.θZ * G.UZ) with hθ
  set b : ι ⊕ (κ ⊕ Unit) → ℝ → ℝ :=
    Sum.elim (fun _ t => (1 + p.Lmax / 2) * zpc_KX G p * G.UX t)
      (Sum.elim (fun _ t => (1 + p.Lmax) * zpc_KY G p * G.UY t) fun _ _ => p.βZ * G.UZ)
    with hb
  have hUZ := hG.UZ_pos
  have hboot := multi_bootstrap_of_strict (g := g) (θ := θ) (b := b) (s := G.s)
    (by
      rintro (k | j | u)
      · exact (h.contX k).norm
      · exact (h.contY j).norm
      · exact continuous_abs.comp_continuousOn h.contZ)
    (by
      rintro (k | j | u)
      · exact continuousOn_const.mul hG.continuousOn_UX
      · exact continuousOn_const.mul hG.continuousOn_UY
      · exact continuousOn_const)
    (by
      rintro (k | j | u)
      · show ‖D.X k 0‖ < p.θX * G.UX 0
        rw [h.X0 k, norm_zero]
        exact mul_pos hS.θX_pos (hG.UX_pos hG.s_nonneg)
      · show ‖D.Y j 0‖ < p.θY * G.UY 0
        rw [h.Y0 j, norm_zero]
        exact mul_pos hS.θY_pos (hG.UY_pos hG.s_nonneg)
      · show |D.Z 0| < p.θZ * G.UZ
        refine h.Z0.trans_lt (mul_lt_mul_of_pos_right ?_ hUZ)
        exact ((zpc_pi_sq_le_KZ hG hS).trans hS.closeZ).trans_lt hS.βZ_lt)
    (by
      rintro (k | j | u) t ht
      · exact mul_lt_mul_of_pos_right hS.closeX (hG.UX_pos ht.2)
      · exact mul_lt_mul_of_pos_right hS.closeY (hG.UY_pos ht.2)
      · exact mul_lt_mul_of_pos_right hS.βZ_lt hUZ)
    (by
      intro T hT _ hle
      have hX : ∀ r ∈ Icc 0 T, ∀ k, ‖D.X k r‖ ≤ p.θX * G.UX r :=
        fun r hr k => hle (Sum.inl k) r hr
      have hY : ∀ r ∈ Icc 0 T, ∀ j, ‖D.Y j r‖ ≤ p.θY * G.UY r :=
        fun r hr j => hle (Sum.inr (Sum.inl j)) r hr
      have hZ : ∀ r ∈ Icc 0 T, |D.Z r| ≤ p.θZ * G.UZ :=
        fun r hr => hle (Sum.inr (Sum.inr ())) r hr
      rintro (k | j | u) t ht
      · exact zpc_stepX hG hS h hT hX hY hZ k t ht
      · exact zpc_stepY hG hS h hT hY j t ht
      · exact zpc_stepZ hG hS h hT hX hZ t ht)
  intro t ht
  exact ⟨fun k => hboot (Sum.inl k) t ht, fun j => hboot (Sum.inr (Sum.inl j)) t ht,
    (hboot (Sum.inr (Sum.inr ())) t ht).1, (hboot (Sum.inr (Sum.inr ())) t ht).2⟩

/-- **Endpoint**: `|Z(s)| ≤ βZ ρ₁ρ₂ S²`; with `S = s₂(s)`, `βZ = N^{ξ/2}`,
this is `|Z_s| ≤ N^{ξ/2} ρ₁ρ₂ s₂(s)²`. -/
theorem zpc_closure_endpoint [Finite ι] [Finite κ] (hG : G.Valid) (hS : zpc_Small G p)
    (h : zpc_Hyp G p D) : |D.Z G.s| ≤ p.βZ * (G.ρ₁ * G.ρ₂ * G.S ^ 2) :=
  (zpc_closure hG hS h G.s ⟨hG.s_nonneg, le_rfl⟩).2.2.1

end BlockBand.Native.CEH.ETH
