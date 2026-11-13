module

public import BlockBand.Native.CEH.ETH.ZigClosureProc

/-!
# CEH ETH: regularity, decompositions and initial values of the processes

The validity conditions of the zig data, and the fields of `zpc_Hyp` giving continuity,
integrability, initial values and semimartingale decompositions of the processes of the path core.
The statements hold on every sample path `ω`, for data with `d.Valid` (`N > 0`, `F` Hermitian, `G`
Hermitian with continuous paths and `G₀ = 0`, `Mᵢ` the MDE solution at `(s, F, zᵢ)`, `Im zᵢ > 0`,
`Im mᵢ > 0`, `s₂(s) > 0`, `Re⟨Γ₁AΓ₂Aᴴ⟩ ≥ 0`); the only measure is Lebesgue measure on `ℝ`.

* `zcl_Data.Valid.R₁_cz`, `zcl_Data.Valid.R₂_cz`: `R_i^{(false)} = (R_i^{(true)})ᴴ`;
  `zcl_Data.Valid.R₁_zero`, `zcl_Data.Valid.R₂_zero`: `R_i^{(b)}(0) = M_i^{(b)}`
  (`zgl_flowResolvent_zero`);
* the path-core fields `contX`, `contY`, `contZ`, `contCfX`, `contCfY`, `intDX`, `intDY`,
  `intDZ` (continuity of `pathR`, `zcl_continuousOn_pathR`, and of `⟨M^A_σ⟩`, `⟨M^I_σ⟩`,
  `zgl_continuousOn_NTrace_twoResApprox`);
* `X0`, `Y0` (`zgl_twoResApprox_zero`) and the decompositions `decX`, `decY` (the `ZigTail`
  path functions and the FTC `zgl_NTrace_twoResApprox_ftc`, `zgl_NTrace_twoResApprox_one_ftc`),
  `decZ` (`ztl_mZ` with the drift `Re fz_driftC`, `fz_re_driftC_eq_reTr`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open BlockBand.Internal.Contracts.Inputs (IsManuscriptMDE)
open BlockBand.External.CEH (normalizedTrace)
open scoped NNReal ENNReal ComplexConjugate

variable {Ω : Type} {N : ℕ}

namespace zcl_Data

/-- **Validity of the data** (all deterministic, or sure properties of `G`). -/
structure Valid (d : zcl_Data Ω N) : Prop where
  N_pos : 0 < N
  F_herm : d.F.IsHermitian
  G_herm : ∀ σ ω, (d.G σ ω).IsHermitian
  G_zero : ∀ ω, d.G 0 ω = 0
  G_cont : ∀ ω, Continuous fun t => d.G t ω
  mde₁ : IsManuscriptMDE (d.s : ℝ) ⟨d.F, F_herm⟩ d.z₁ d.M₁
  mde₂ : IsManuscriptMDE (d.s : ℝ) ⟨d.F, F_herm⟩ d.z₂ d.M₂
  z₁_pos : 0 < d.z₁.im
  z₂_pos : 0 < d.z₂.im
  m₁_pos : 0 < d.m₁.im
  m₂_pos : 0 < d.m₂.im
  S_pos : 0 < sTwoAt d.s d.M₁ d.M₂ d.A
  base_nonneg : 0 ≤ sTwoBase d.M₁ d.M₂ d.A

variable {d : zcl_Data Ω N}

namespace Valid

variable (hd : d.Valid)
include hd

theorem herm (σ : ℝ≥0) (ω : Ω) : (d.F + d.G σ ω).IsHermitian :=
  hd.F_herm.add (hd.G_herm σ ω)

theorem hm₁ : 0 ≤ d.z₁.im * d.m₁.im := (mul_pos hd.z₁_pos hd.m₁_pos).le

theorem hm₂ : 0 ≤ d.z₂.im * d.m₂.im := (mul_pos hd.z₂_pos hd.m₂_pos).le

theorem R₁_cz (b : Bool) (ω : Ω) (t : ℝ) :
    d.R₁ b ω t = if b then d.R₁ true ω t else (d.R₁ true ω t)ᴴ :=
  ztl_pathR_cz b d.z₁ d.m₁ d.s ω (hd.herm · ω) t

theorem R₂_cz (b : Bool) (ω : Ω) (t : ℝ) :
    d.R₂ b ω t = if b then d.R₂ true ω t else (d.R₂ true ω t)ᴴ :=
  ztl_pathR_cz b d.z₂ d.m₂ d.s ω (hd.herm · ω) t

theorem R₁_zero (b : Bool) (ω : Ω) : d.R₁ b ω 0 = d.Mc₁ b := by
  have h : d.R₁ true ω 0 = d.M₁ := by
    change flowResolvent d.F d.G d.z₁ d.m₁ d.s (0 : ℝ).toNNReal ω = d.M₁
    rw [Real.toNNReal_zero]
    exact zgl_flowResolvent_zero (F := ⟨d.F, hd.F_herm⟩) (hd.G_zero ω) hd.mde₁
  rw [hd.R₁_cz b ω 0, h]
  cases b <;> simp [Mc₁, zcl_ch]

theorem R₂_zero (b : Bool) (ω : Ω) : d.R₂ b ω 0 = d.Mc₂ b := by
  have h : d.R₂ true ω 0 = d.M₂ := by
    change flowResolvent d.F d.G d.z₂ d.m₂ d.s (0 : ℝ).toNNReal ω = d.M₂
    rw [Real.toNNReal_zero]
    exact zgl_flowResolvent_zero (F := ⟨d.F, hd.F_herm⟩) (hd.G_zero ω) hd.mde₂
  rw [hd.R₂_cz b ω 0, h]
  cases b <;> simp [Mc₂, zcl_ch]

theorem contR₁ (b : Bool) (ω : Ω) : ContinuousOn (d.R₁ b ω) (Icc 0 (d.s : ℝ)) :=
  zcl_continuousOn_pathR (hd.herm · ω) (hd.G_cont ω)
    (ztl_cz_im_ne_zero b hd.z₁_pos.ne') (ztl_cz_hm b hd.hm₁) d.s

theorem contR₂ (b : Bool) (ω : Ω) : ContinuousOn (d.R₂ b ω) (Icc 0 (d.s : ℝ)) :=
  zcl_continuousOn_pathR (hd.herm · ω) (hd.G_cont ω)
    (ztl_cz_im_ne_zero b hd.z₂_pos.ne') (ztl_cz_hm b hd.hm₂) d.s

theorem hden (k : Bool × Bool) :
    ∀ σ ∈ Icc (0 : ℝ) d.s, hybridDen σ (d.Mc₁ k.1) (d.Mc₂ k.2) ≠ 0 :=
  zgl_hybridDen_ne_zero_Icc hd.mde₁ hd.mde₂ hd.z₁_pos.ne' hd.z₂_pos.ne' d.s.2 _ _

theorem contμA (k : Bool × Bool) : ContinuousOn (d.μA k) (Icc 0 (d.s : ℝ)) :=
  zgl_continuousOn_NTrace_twoResApprox (hd.hden k) d.A

theorem contμI (k : Bool × Bool) : ContinuousOn (d.μI k) (Icc 0 (d.s : ℝ)) :=
  zgl_continuousOn_coeff (hd.hden k)

end Valid

end zcl_Data

/-!
## Continuity of functions of the two resolvents
-/

/-- Continuity on `[0, s]` of `r ↦ f(R₁ r, R₂ r)` for continuous `f`. -/
theorem zcl_continuousOn_pair {α : Type*} [TopologicalSpace α]
    {f : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ → α} (hf : Continuous f)
    {R₁ R₂ : ℝ → Matrix (Fin N) (Fin N) ℂ} {T : Set ℝ} (h₁ : ContinuousOn R₁ T)
    (h₂ : ContinuousOn R₂ T) : ContinuousOn (fun r => f (R₁ r, R₂ r)) T :=
  hf.comp_continuousOn (h₁.prodMk h₂)

theorem zcl_continuous_chain (A : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      normalizedTrace (p.1 * A * p.2) := by
  unfold normalizedTrace
  fun_prop

theorem zcl_continuous_drift (A : Matrix (Fin N) (Fin N) ℂ) (n₁ n₂ : ℂ) :
    Continuous fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      normalizedTrace (flowDrift2 p.1 p.2 A n₁ n₂) := by
  unfold flowDrift2 normalizedTrace
  fun_prop

theorem zcl_continuous_fz_chain (A : Matrix (Fin N) (Fin N) ℂ) :
    Continuous fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      (fz_chain p.1 p.2 A).re := by
  unfold fz_chain normalizedTrace External.CEH.imaginaryPart
  fun_prop

theorem zcl_continuous_fz_driftC (A : Matrix (Fin N) (Fin N) ℂ) (n₁ n₂ : ℂ) :
    Continuous fun p : Matrix (Fin N) (Fin N) ℂ × Matrix (Fin N) (Fin N) ℂ =>
      (fz_driftC p.1 p.2 A n₁ n₂).re := by
  unfold fz_driftC flowDrift2 normalizedTrace
  fun_prop

/-!
## The generic decomposition of a two-resolvent chain
-/

/-- **Decomposition of a chain along the flow** (+ FTC). For continuous sample paths
`R_i = pathR F G wᵢ nᵢ s ω` on `[0, s]`, any `A'`, and a deterministic `μ` with
`μ t = ⟨R₁(0) A' R₂(0)⟩ + ∫₀ᵗ g` (`g` continuous): for `t ∈ [0, s]`,
`⟨R₁(t) A' R₂(t)⟩ - μ t = ⟨m_Re(t), m_Im(t)⟩ + ∫₀ᵗ (⟨flowDrift2 R₁ R₂ A' n₁ n₂⟩ - g)`, where
`m_Re`, `m_Im` are the `ZigTail` path functions `ztl_mX` with `K = N⁻¹`, `-iN⁻¹`. -/
theorem zcl_dec_chain {F : Matrix (Fin N) (Fin N) ℂ} {G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ}
    {ω : Ω} {s : ℝ≥0} {w₁ n₁ w₂ n₂ : ℂ}
    (hc₁ : ContinuousOn (pathR F G w₁ n₁ s ω) (Icc 0 (s : ℝ)))
    (hc₂ : ContinuousOn (pathR F G w₂ n₂ s ω) (Icc 0 (s : ℝ)))
    (A' : Matrix (Fin N) (Fin N) ℂ) {μ g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 (s : ℝ)))
    (hμ : ∀ t ∈ Icc 0 (s : ℝ), μ t = normalizedTrace (pathR F G w₁ n₁ s ω 0 * A' *
      pathR F G w₂ n₂ s ω 0) + ∫ r in (0 : ℝ)..t, g r) :
    ∀ t ∈ Icc 0 (s : ℝ), normalizedTrace (pathR F G w₁ n₁ s ω t * A' *
        pathR F G w₂ n₂ s ω t) - μ t =
      (⟨ztl_mX F G w₁ n₁ w₂ n₂ s (ztl_evK true (ztl_avgK N)) A' ω t,
        ztl_mX F G w₁ n₁ w₂ n₂ s (ztl_evK false (ztl_avgK N)) A' ω t⟩ : ℂ) +
      ∫ r in (0 : ℝ)..t, (normalizedTrace (flowDrift2 (pathR F G w₁ n₁ s ω r)
        (pathR F G w₂ n₂ s ω r) A' n₁ n₂) - g r) := by
  intro t ht
  have hsub : Icc 0 t ⊆ Icc 0 (s : ℝ) := Icc_subset_Icc_right ht.2
  have hD : ContinuousOn (fun r => normalizedTrace (flowDrift2 (pathR F G w₁ n₁ s ω r)
      (pathR F G w₂ n₂ s ω r) A' n₁ n₂)) (Icc 0 t) :=
    (zcl_continuousOn_pair (zcl_continuous_drift A' n₁ n₂) hc₁ hc₂).mono hsub
  have hDi : IntegrableOn (fun r => normalizedTrace (flowDrift2 (pathR F G w₁ n₁ s ω r)
      (pathR F G w₂ n₂ s ω r) A' n₁ n₂)) (Ioc 0 t) :=
    hD.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hgi : IntegrableOn g (Ioc 0 t) :=
    (hg.mono hsub).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le ht.1, integral_sub hDi hgi, zcl_integral_Ioc_eq_mk hDi,
    hμ t ht, intervalIntegral.integral_of_le ht.1]
  simp only [ztl_mX, ztl_reTr_evK_avgK_true, ztl_reTr_evK_avgK_false]
  apply Complex.ext <;> simp only [Complex.sub_re, Complex.add_re, Complex.sub_im,
    Complex.add_im] <;> ring

namespace zcl_Data

variable {d : zcl_Data Ω N} (hd : d.Valid) (ω : Ω)
include hd

/-!
## The regularity and decomposition fields
-/

theorem contX (k : Bool × Bool) : ContinuousOn ((d.proc ω).X k) (Icc 0 d.geom.s) :=
  (zcl_continuousOn_pair (zcl_continuous_chain d.A) (hd.contR₁ k.1 ω)
    (hd.contR₂ k.2 ω)).sub (hd.contμA k)

theorem contY (k : Bool × Bool) : ContinuousOn ((d.proc ω).Y k) (Icc 0 d.geom.s) := by
  have h := (zcl_continuousOn_pair (zcl_continuous_chain (1 : Matrix (Fin N) (Fin N) ℂ))
    (hd.contR₁ k.1 ω) (hd.contR₂ k.2 ω)).sub (hd.contμI k)
  simp only [Matrix.mul_one] at h
  exact h

theorem contZ : ContinuousOn (d.proc ω).Z (Icc 0 d.geom.s) :=
  zcl_continuousOn_pair (zcl_continuous_fz_chain d.A) (hd.contR₁ true ω) (hd.contR₂ true ω)

theorem contCfX (k : Bool × Bool) : ContinuousOn ((d.proc ω).cfX k) (Icc 0 d.geom.s) :=
  hd.contμI k

theorem contCfY (k : Bool × Bool) : ContinuousOn ((d.proc ω).cfY k) (Icc 0 d.geom.s) :=
  hd.contμI k

theorem intDX (k : Bool × Bool) : IntervalIntegrable ((d.proc ω).DX k) volume 0 d.geom.s :=
  ((zcl_continuousOn_pair (zcl_continuous_drift d.A _ _) (hd.contR₁ k.1 ω)
    (hd.contR₂ k.2 ω)).sub ((hd.contμA k).mul (hd.contμI k))).intervalIntegrable_of_Icc
    d.s.2

theorem intDY (k : Bool × Bool) : IntervalIntegrable ((d.proc ω).DY k) volume 0 d.geom.s :=
  ((zcl_continuousOn_pair (zcl_continuous_drift 1 _ _) (hd.contR₁ k.1 ω)
    (hd.contR₂ k.2 ω)).sub ((hd.contμI k).mul (hd.contμI k))).intervalIntegrable_of_Icc
    d.s.2

theorem intDZ : IntervalIntegrable (d.proc ω).DZ volume 0 d.geom.s :=
  (zcl_continuousOn_pair (zcl_continuous_fz_driftC d.A d.m₁ d.m₂) (hd.contR₁ true ω)
    (hd.contR₂ true ω)).intervalIntegrable_of_Icc d.s.2

theorem X0 (k : Bool × Bool) : (d.proc ω).X k 0 = 0 := by
  change normalizedTrace (d.R₁ k.1 ω 0 * d.A * d.R₂ k.2 ω 0) -
    NTrace (twoResApprox 0 (d.Mc₁ k.1) d.A (d.Mc₂ k.2)) = 0
  rw [hd.R₁_zero, hd.R₂_zero, zgl_twoResApprox_zero, sub_eq_zero]
  rfl

theorem Y0 (k : Bool × Bool) : (d.proc ω).Y k 0 = 0 := by
  change normalizedTrace (d.R₁ k.1 ω 0 * d.R₂ k.2 ω 0) -
    NTrace (twoResApprox 0 (d.Mc₁ k.1) 1 (d.Mc₂ k.2)) = 0
  rw [hd.R₁_zero, hd.R₂_zero, zgl_twoResApprox_zero, Matrix.mul_one, sub_eq_zero]
  rfl

theorem decX (k : Bool × Bool) : ∀ t ∈ Icc 0 d.geom.s,
    (d.proc ω).X k t = (d.proc ω).MX k t + ∫ r in (0 : ℝ)..t, (d.proc ω).DX k r := by
  have h := zcl_dec_chain (hd.contR₁ k.1 ω) (hd.contR₂ k.2 ω) d.A
    ((hd.contμA k).mul (hd.contμI k)) (μ := d.μA k) (fun t ht => by
      change d.μA k t = normalizedTrace (d.R₁ k.1 ω 0 * d.A * d.R₂ k.2 ω 0) + _
      rw [hd.R₁_zero, hd.R₂_zero]
      exact zgl_NTrace_twoResApprox_ftc (hd.hden k) t ht)
  intro t ht
  exact h t ht

theorem decY (k : Bool × Bool) : ∀ t ∈ Icc 0 d.geom.s,
    (d.proc ω).Y k t = (d.proc ω).MY k t + ∫ r in (0 : ℝ)..t, (d.proc ω).DY k r := by
  have h := zcl_dec_chain (hd.contR₁ k.1 ω) (hd.contR₂ k.2 ω) 1
    ((hd.contμI k).mul (hd.contμI k)) (μ := d.μI k) (fun t ht => by
      change d.μI k t = normalizedTrace (d.R₁ k.1 ω 0 * 1 * d.R₂ k.2 ω 0) + _
      rw [hd.R₁_zero, hd.R₂_zero, Matrix.mul_one]
      exact zgl_NTrace_twoResApprox_one_ftc (hd.hden k) t ht)
  intro t ht
  have h' := h t ht
  simp only [Matrix.mul_one] at h'
  exact h'

omit hd in
theorem decZ : ∀ t ∈ Icc 0 d.geom.s,
    (d.proc ω).Z t = (d.proc ω).Z 0 + (d.proc ω).MZ t +
      ∫ r in (0 : ℝ)..t, (d.proc ω).DZ r := by
  intro t ht
  rw [intervalIntegral.integral_of_le ht.1]
  change d.Zp ω t = d.Zp ω 0 + ztl_mZ d.F d.G d.z₁ d.m₁ d.z₂ d.m₂ d.s d.A ω t +
    ∫ r in Ioc 0 t, (fz_driftC (d.R₁ true ω r) (d.R₂ true ω r) d.A d.m₁ d.m₂).re
  simp only [fz_re_driftC_eq_reTr, zcl_Data.R₁, zcl_Data.R₂, ztl_cz, ↓reduceIte]
  unfold ztl_mZ Zp fz_chain
  simp only [zcl_Data.R₁, zcl_Data.R₂, ztl_cz, ↓reduceIte]
  ring

end zcl_Data

end BlockBand.Native.CEH.ETH
