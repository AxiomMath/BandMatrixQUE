module

public import BlockBand.Native.CEH.ETH.ZigClosureBase

/-!
# CEH ETH: the processes of the path core along the flow

The data of one zig at fixed spectral parameters, the geometry it induces, and the processes of the
path core built from the flow resolvents.

**Data** (`zcl_Data`): `F`, the Brownian motion `G`, the horizon `s : ℝ≥0`, the points `z₁, z₂`,
the MDE solutions `M₁, M₂` (`mᵢ = ⟨Mᵢ⟩`) and the observable `A`. Constellations are indexed by
`(b₁, b₂) : Bool × Bool` (`true`: `Rᵢ`, `false`: `Rᵢᴴ = R(z̄ᵢ, m̄ᵢ)`, via `ztl_cz`), with the
deterministic approximations at `Mᵢ^{(bᵢ)} = chooseAdjoint (zcl_ch bᵢ) Mᵢ`.

**Geometry** (`zcl_Data.geom`): `s`, `N`, `ηᵢ = Im zᵢ`, `cᵢ = Im mᵢ`, `ρᵢ = cehDensityOf Mᵢ`,
`S = s₂(s) = sTwoAt s M₁ M₂ A`.

**Processes** (`zcl_Data.proc ω`), for `k = (b₁, b₂)` and `R_i' = pathR … (ztl_cz bᵢ zᵢ)
(ztl_cz bᵢ mᵢ) s ω`:
* `X k = ⟨R₁' A R₂'⟩ - ⟨M^A_σ⟩`, `Y k = ⟨R₁' R₂'⟩ - ⟨M^I_σ⟩`; martingale parts: the complex
  numbers with real and imaginary parts the `ZigTail` path functions `ztl_mX` (`K = N⁻¹`, `-iN⁻¹`);
  drifts: `⟨flowDrift2 R₁' R₂' A m₁' m₂'⟩ - ⟨M^A⟩⟨M^I⟩` (resp. `A = 1`, `- ⟨M^I⟩²`);
  brackets: `ztl_brkX`.
* `Z = Re⟨Im R₁ A Im R₂ Aᴴ⟩` (upper constellation), martingale part `ztl_mZ`, drift
  `Re (fz_driftC R₁ R₂ A m₁ m₂)` (the four-chain form of `ZigTail`), bracket `ztl_brkZ`.
* `W_i = ⟨R_i⟩ - m_i`, `imR_i = |Im⟨R_i⟩|`, `TI = |⟨Im R₁ Im R₂⟩|`, `cross = zgl_cross R₁ R₂ A`,
  and `V_i = |Z|/η_{i,σ}` (the right-hand side of the bounds `V₁_le`, `V₂_le` of `zpc_Hyp`, so
  that these fields hold with equality).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Native.CEH.ETH

open MeasureTheory Matrix Set
open CEHNative.BlockBand CEHNative.BlockBand.External.CEH
open BlockBand.Native.CEH.Flow BlockBand.Native.CEH.Zig BlockBand.Native.CEH.LocalLaw
open scoped NNReal ENNReal ComplexConjugate

/-- `true ↦ plain`, `false ↦ adjoint`. -/
def zcl_ch (b : Bool) : AdjointChoice := if b then .plain else .adjoint

/-- The data of one zig at fixed spectral parameters. -/
structure zcl_Data (Ω : Type) (N : ℕ) where
  F : Matrix (Fin N) (Fin N) ℂ
  G : ℝ≥0 → Ω → Matrix (Fin N) (Fin N) ℂ
  s : ℝ≥0
  z₁ : ℂ
  z₂ : ℂ
  M₁ : Matrix (Fin N) (Fin N) ℂ
  M₂ : Matrix (Fin N) (Fin N) ℂ
  A : Matrix (Fin N) (Fin N) ℂ

namespace zcl_Data

variable {Ω : Type} {N : ℕ} (d : zcl_Data Ω N)

/-- `m₁ = ⟨M₁⟩`. -/
def m₁ : ℂ := BlockBand.External.CEH.normalizedTrace d.M₁

/-- `m₂ = ⟨M₂⟩`. -/
def m₂ : ℂ := BlockBand.External.CEH.normalizedTrace d.M₂

/-- The sample path of `R₁` in constellation `b`. -/
def R₁ (b : Bool) (ω : Ω) : ℝ → Matrix (Fin N) (Fin N) ℂ :=
  pathR d.F d.G (ztl_cz b d.z₁) (ztl_cz b d.m₁) d.s ω

/-- The sample path of `R₂` in constellation `b`. -/
def R₂ (b : Bool) (ω : Ω) : ℝ → Matrix (Fin N) (Fin N) ℂ :=
  pathR d.F d.G (ztl_cz b d.z₂) (ztl_cz b d.m₂) d.s ω

/-- `M₁^{(b)}`. -/
def Mc₁ (b : Bool) : Matrix (Fin N) (Fin N) ℂ := chooseAdjoint (zcl_ch b) d.M₁

/-- `M₂^{(b)}`. -/
def Mc₂ (b : Bool) : Matrix (Fin N) (Fin N) ℂ := chooseAdjoint (zcl_ch b) d.M₂

/-- `⟨M^A_σ⟩` in constellation `k`. -/
def μA (k : Bool × Bool) (r : ℝ) : ℂ := NTrace (twoResApprox r (d.Mc₁ k.1) d.A (d.Mc₂ k.2))

/-- `⟨M^I_σ⟩` in constellation `k`. -/
def μI (k : Bool × Bool) (r : ℝ) : ℂ := NTrace (twoResApprox r (d.Mc₁ k.1) 1 (d.Mc₂ k.2))

/-- The geometry of the path core: `ηᵢ = Im zᵢ`, `cᵢ = Im mᵢ`, `ρᵢ = cehDensityOf Mᵢ`,
`S = s₂(s)`. -/
def geom : zpc_Geom where
  s := d.s
  N := N
  η₁ := d.z₁.im
  η₂ := d.z₂.im
  c₁ := d.m₁.im
  c₂ := d.m₂.im
  ρ₁ := cehDensityOf d.M₁
  ρ₂ := cehDensityOf d.M₂
  S := sTwoAt d.s d.M₁ d.M₂ d.A

/-- The `Z` process `Re⟨Im R₁ A Im R₂ Aᴴ⟩`. -/
def Zp (ω : Ω) (r : ℝ) : ℝ := (fz_chain (d.R₁ true ω r) (d.R₂ true ω r) d.A).re

/-- **The processes of the path core** on the sample path `ω`. -/
def proc (ω : Ω) : zpc_Proc (Bool × Bool) (Bool × Bool) where
  X k r := BlockBand.External.CEH.normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r) -
    d.μA k r
  MX k t := ⟨ztl_mX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK true (ztl_avgK N)) d.A ω t,
    ztl_mX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK false (ztl_avgK N)) d.A ω t⟩
  DX k r := BlockBand.External.CEH.normalizedTrace (flowDrift2 (d.R₁ k.1 ω r) (d.R₂ k.2 ω r)
      d.A (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.m₂)) - d.μA k r * d.μI k r
  cfX k r := d.μI k r
  MA k r := d.μA k r
  QX₁ k r := BlockBand.External.CEH.normalizedTrace (d.R₁ k.1 ω r * d.R₁ k.1 ω r * d.A *
    d.R₂ k.2 ω r)
  QX₂ k r := BlockBand.External.CEH.normalizedTrace (d.R₁ k.1 ω r * d.A * d.R₂ k.2 ω r *
    d.R₂ k.2 ω r)
  brkXre k r := ztl_brkX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK true (ztl_avgK N)) d.A ω r
  brkXim k r := ztl_brkX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK false (ztl_avgK N)) d.A ω r
  yX := id
  Y k r := BlockBand.External.CEH.normalizedTrace (d.R₁ k.1 ω r * d.R₂ k.2 ω r) - d.μI k r
  MY k t := ⟨ztl_mX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK true (ztl_avgK N)) 1 ω t,
    ztl_mX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK false (ztl_avgK N)) 1 ω t⟩
  DY k r := BlockBand.External.CEH.normalizedTrace (flowDrift2 (d.R₁ k.1 ω r) (d.R₂ k.2 ω r)
      1 (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.m₂)) - d.μI k r * d.μI k r
  cfY k r := d.μI k r
  QY₁ k r := BlockBand.External.CEH.normalizedTrace (d.R₁ k.1 ω r * d.R₁ k.1 ω r *
    d.R₂ k.2 ω r)
  QY₂ k r := BlockBand.External.CEH.normalizedTrace (d.R₁ k.1 ω r * d.R₂ k.2 ω r *
    d.R₂ k.2 ω r)
  brkYre k r := ztl_brkX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK true (ztl_avgK N)) 1 ω r
  brkYim k r := ztl_brkX d.F d.G (ztl_cz k.1 d.z₁) (ztl_cz k.1 d.m₁) (ztl_cz k.2 d.z₂)
      (ztl_cz k.2 d.m₂) d.s (ztl_evK false (ztl_avgK N)) 1 ω r
  Z r := d.Zp ω r
  MZ t := ztl_mZ d.F d.G d.z₁ d.m₁ d.z₂ d.m₂ d.s d.A ω t
  DZ r := (fz_driftC (d.R₁ true ω r) (d.R₂ true ω r) d.A d.m₁ d.m₂).re
  brkZ r := ztl_brkZ d.F d.G d.z₁ d.m₁ d.z₂ d.m₂ d.s d.A ω r
  V₁ r := ((|d.Zp ω r| / d.geom.e₁ r : ℝ) : ℂ)
  V₂ r := ((|d.Zp ω r| / d.geom.e₂ r : ℝ) : ℂ)
  cross r := zgl_cross (d.R₁ true ω r) (d.R₂ true ω r) d.A
  W₁ r := BlockBand.External.CEH.normalizedTrace (d.R₁ true ω r) - d.m₁
  W₂ r := BlockBand.External.CEH.normalizedTrace (d.R₂ true ω r) - d.m₂
  imR₁ r := |(BlockBand.External.CEH.normalizedTrace (d.R₁ true ω r)).im|
  imR₂ r := |(BlockBand.External.CEH.normalizedTrace (d.R₂ true ω r)).im|
  TI r := ‖BlockBand.External.CEH.normalizedTrace
    (BlockBand.External.CEH.imaginaryPart (d.R₁ true ω r) *
      BlockBand.External.CEH.imaginaryPart (d.R₂ true ω r))‖

end zcl_Data

end BlockBand.Native.CEH.ETH
