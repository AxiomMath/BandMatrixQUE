module

public import BlockBand.Internal.Contracts.ClocksCommonPort
public import BlockBand.Asymptotics.CriticalSequence

/-!
# Definitions for the physical microscopic tag comparison

* `tagClock`: `Z_{r;K} = W⁻¹ h*Y_{r;K}h`;
* `meanClock`: `M_r = (rW)⁻¹ h*Y^{int}h`, `Y^{int} = Σ_j Y_{r;j}`;
* `pathTagExpect`: `E_{path,h,K} Φ(Z_{r;K}/M_r)` at the real energy `e`, `K` uniform on the
  `r` interior positions (the average `r⁻¹ Σ_K`).
* `physicalTagSide`: `E Σ_α w(u_α) Φ(n p_{αk})` under the exact physical law `model.law`,
  `u_α = Nρ(E)(λ_α - E)` (`Clocks.microCoord`), `p_{αk}` the block mass of the `α`-th
  eigenvector (zero-based increasing ranks; every rank, with multiplicity).
* `pathTagSide`: `∫ w(u) E_{path,h,K} Φ(Z_{r;K}/M_r)(e(u)) du`, `e(u) = E + u/(Nρ(E))`
  (`Clocks.microEnergy`).

Conventions. `Φ ∈ C_b([0,∞))` is `Set.Ici 0 →ᵇ ℝ`, evaluated at the clamp `projIci 0`
(the arguments are nonnegative, so the clamp changes nothing). On the null event
`M_r = 0` Lean's `x / 0 = 0` assigns the ratio `0`. Lean's totalized matrix inverse is used for
`G_lead` (it is `0` on the null pole set).

Statement (`MicroscopicTagComparisonStatement`). For fixed `b`, bulk `E`, smooth compactly
supported (signed) `w`, `Φ ∈ C_b([0,∞))`, every `τ > 0` (in particular every `τ ∈ (0,T₀]`),
every critical sequence `n/W → τ` and every sequence of exact physical models: for every
`ε > 0`, eventually, for every physical block `k` of the ring,
`|E Σ_α w(u_α)Φ(n p_{αk}) - ∫ w(u) E_{path,h,K}Φ(Z_{r;K}/M_r)(e(u)) du| ≤ ε`
(uniform in the physical tag). The critical limit is taken before any trace or small-denominator
cutoff is removed; this concerns the proof, and no cutoff appears in the statement.

`MicroscopicTagLeadComparison` is the comparison stated before the ports are removed; see its
docstring.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology
open BlockBand.Model.Construction
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.Clocks
open scoped BoundedContinuousFunction

/-!
## The matched-lead clocks
-/

/-- `h*Y^{int}h = Σ_{j<r} ‖P_jUh‖²`, the interior clock of the matched-lead path. -/
def interiorLeadMass (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ∑ i : Fin r, leadPositionMass b e W r x.1 x.2 (Sum.inl i)

/-- `h*Y^{port}h = ‖P_{ports}Uh‖²`, the clock of the two auxiliary ports. -/
def portLeadMass (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ∑ j : Fin 2, leadPositionMass b e W r x.1 x.2 (Sum.inr j)

/-- `Z_{r;K} = W⁻¹ h*Y_{r;K}h`. -/
def tagClock (b e : ℝ) (W r : ℕ) (K : Fin r) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (W : ℝ)⁻¹ * leadPositionMass b e W r x.1 x.2 (Sum.inl K)

/-- `M_r = (rW)⁻¹ h*Y^{int}h`. -/
def meanClock (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ((r : ℝ) * W)⁻¹ * interiorLeadMass b e W r x

/-- `E_{path,h,K} Φ(Z_{r;K}/M_r)` at real energy `e`: path prior `growthPathLaw W b`,
independent `h ~ CN(0, I_{2W})`, `K` uniform on the `r` interior positions. -/
def pathTagExpect (b e : ℝ) (W r : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : ℝ :=
  ∫ x, (r : ℝ)⁻¹ * ∑ K : Fin r, Φ (Set.projIci 0 (tagClock b e W r K x / meanClock b e W r x))
    ∂probedClockLaw W b

/-!
## The two sides of the microscopic tag comparison
-/

/-- The physical side `E Σ_α w(u_α) Φ(n p_{αk})`, exact physical law, `u_α = Nρ(E)(λ_α - E)`. -/
def physicalTagSide (p : Parameters) (model : p.GaussianRingModel) (E : ℝ) (w : ℝ → ℝ)
    (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) (k : ZMod p.n) : ℝ :=
  ∫ H, ∑ α : Fin p.N, w (microCoord p E (physicalOrderedEigenvalue p H α)) *
      Φ (Set.projIci 0 ((p.n : ℝ) * physicalOrderedBlockMass p H α k))
    ∂(model.law : Measure p.SiteMatrix)

/-- The path side `∫ w(u) E_{path,h,K} Φ(Z_{r;K}/M_r)(e(u)) du`, `r = n - 3`. -/
def pathTagSide (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : ℝ :=
  ∫ u, w u * pathTagExpect p.b (microEnergy p E u) p.W (p.n - 3) Φ

/-- The microscopic tag comparison. Law: the exact physical law on the left; on the right the
independent matched-lead path prior `growthPathLaw W b` (path of `r = n - 3` blocks), independent
`h ~ CN(0, I_{2W})`, independent uniform `K`. Fixed first: `0 < b < 1/2`, the bulk energy
`-2 < E < 2`, a smooth compactly supported (possibly signed) `w`, `Φ ∈ C_b([0,∞))`, then `τ > 0`,
a critical sequence `n_j/W_j → τ` and models. Conclusion: for every `ε > 0`, eventually in `j`,
for every block `k` (uniformity in the physical tag),
`|E Σ_α w(u_α)Φ(n p_{αk}) - ∫ w(u) E Φ(Z_{r;K}/M_r)(e(u)) du| ≤ ε`. -/
def MicroscopicTagComparisonStatement : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → HasCompactSupport w →
    ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, ∀ τ : ℝ, 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
        |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
            pathTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε

/-!
## The lead comparison
-/

/-- The total mass `h*Y^{all}h` of the response on the `n - 1` old and auxiliary positions. -/
def totalLeadMass (b e : ℝ) (W r : ℕ) (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  ∑ y : Fin r ⊕ Fin 2, leadPositionMass b e W r x.1 x.2 y

/-- The averaged tag test on the matched-lead path: the `n` ring positions are the `r = n - 3`
interior positions, the two auxiliary ports and the removed block `0`, which carries mass zero;
`n⁻¹ [Φ(0) + Σ_{y ∈ Fin r ⊕ Fin 2} Φ(n h*Y_yh / h*Y^{all}h)]`. -/
def leadAveragedTest (b e : ℝ) (n W : ℕ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ)
    (x : GrowthPath W × (Fin 2 × Fin W → ℂ)) : ℝ :=
  (n : ℝ)⁻¹ * (Φ (Set.projIci 0 0) + ∑ y : Fin (n - 3) ⊕ Fin 2,
    Φ (Set.projIci 0 ((n : ℝ) * leadPositionMass b e W (n - 3) x.1 x.2 y /
      totalLeadMass b e W (n - 3) x)))

/-- `∫ w(u) E_{path,h}[leadAveragedTest](e(u)) du`. -/
def leadTagSide (p : Parameters) (E : ℝ) (w : ℝ → ℝ) (Φ : Set.Ici (0 : ℝ) →ᵇ ℝ) : ℝ :=
  ∫ u, w u * ∫ x, leadAveragedTest p.b (microEnergy p E u) p.n p.W Φ x ∂probedClockLaw p.W p.b

/-- The lead comparison, an intermediate step of the proof of the microscopic tag comparison. For
a nonnegative smooth compactly supported `w` and a bounded Lipschitz `Φ` (it suffices first to
take a nonnegative `w` of integral one and a bounded Lipschitz `Φ`; the normalization `∫ w = 1` is
immaterial since both sides are linear in `w`), uniformly in the physical tag `k`,
`E Σ_α w(u_α)Φ(n p_{αk}) - ∫ w(u) E_{path,h} n⁻¹[Φ(0) + Σ_y Φ(n h*Y_yh / h*Y^{all}h)](e(u)) du → 0`,
`y` over the `n - 1` old and auxiliary positions of the matched-lead path, `Lg` already replaced
by `h` (the scalar `γ` cancels from every ratio). -/
def MicroscopicTagLeadComparison : Prop :=
  ∀ (b : ℝ) (hb : 0 < b) (hb' : b < 1 / 2) (E : ℝ), -2 < E → E < 2 →
    ∀ w : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w → HasCompactSupport w → (∀ u, 0 ≤ w u) →
    ∀ Φ : Set.Ici (0 : ℝ) →ᵇ ℝ, (∃ L : NNReal, LipschitzWith L Φ) →
    ∀ τ : ℝ, 0 < τ → ∀ (s : CriticalSequence τ)
      (R : ∀ j, (s.parameters b hb hb' j).GaussianRingModel),
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k : ZMod (s.parameters b hb hb' j).n,
        |physicalTagSide (s.parameters b hb hb' j) (R j) E w Φ k -
            leadTagSide (s.parameters b hb hb' j) E w Φ| ≤ ε

end BlockBand.Endpoints
